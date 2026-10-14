-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0277
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:55:01.513842+00:00
-- url     : https://prove2.me/submissions/5ee3dd59-c504-4a40-834e-87ea750a8e3b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 49640291 ≤ n < 49820147 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 49641541 1250 49640291 49640309
    0x1050403061803080a1a01080c0d060906050a08030705030f03060a03060e070302010f02071d0705120106081527040501020906180a09050402030613170a020c13061d040804 75
    0x8a108466828800d003002d28611a40d5440255594403807010f06940e65070b5000181c01880c0000c0d90101d602404040c2c1d84202100d0343d0710709061800141c00c0c180c80d19540100082651000188100e060001010001c0c241c0600254941000c59450706e60340c0c481c0400041c40320700003202207034031f503920881040000c6410540c140000600d00744029190202440304038040741c44460754020b102d0020072201e0846038803404004040e42c91021000c1c110342c0003800101044820404840010700c60032441e8040c0100ea512003100c1c2c50010901b607503121070710010a1064440709da06590119001480701c00e0941e001c1c4036524a41c841d0318040c1e01902840e90601c1d030000c400b040f0407000107203a401c10780008404440f2800e506945850a03400c0300d80540d07000e90181c10050009140d03c2000007100c8680c0d100c0c0100d0042c01d4000302d481c03e006d80114880e0401038103e0400c3c0100c514003c2074030706000c0a44034080081501d46065244440303035031141005000e08103000a41801044401d940050030804 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 49642791 1250 49641541 49641551
    0x15050a0801140708010f030803040204090c030f0308250c020f030d0c031d0307060c210c030f02280201140301030305030108070b040b0904020c0a0203070801020d0606030e030f090105040306 83
    0x1140030303168180d41044982c00c6031001a025501ca02d4102e4121444a01c00004003402d40d21150003e0340020401d81c0c0003a03c1d101090001500340441400550280c10411140b200c2c034a402402400094031a00d0350744450684900624a048030412140680d410445a01c3d1034900c049104800c60080c2d003039041c0940b90722801915044030880c882c50b882070f600e03004240c002e150306403240d5000d4807449405900c090014441d540c001d01301d00c41054021980e1448580742d125080e0b2079442c90440000000f00c1501c0ca000405401c02c90040c2c42c11043d00140c04c000350038121300c1c58503a800c3d451310f590904115028800b035901840100150f40b098030b2203990f59613100e040240c159402845104a03602c9426000074052140405940c1a00c1c21071703490710704d000030807810070029412454048a00d405911460f100603902080800c004004980c00503842c0e01450344188121091544000c2c18541007140c1078400910200803034440381c07075007546662245100310040759207008540008100740d140c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 49644041 1250 49642791 49642799
    0x1140102190b060a12080405060a0908010204030507140103020304020f101403010806160815010804082104030e010e060912011113140114030402090910140603070f0b0d15050a 77
    0x1c1c40030345200b08404d031032580d5525075681c000d030a4480c0340240905001010b21080c821440c0000c001c010366442032502e840100e031980c03a440e08aa115034011900c9604c502000c000c240c00030400003200310001d080450551a094000c10050040b54031110300c01c162410721000c84602a81c2c2d150700020004403019104d40e143c0201c15602d10013600c21a881036803484241445901c1004000c0c03094060480c1c40c0d6031464031030015258110060702c225422201449007520440c41c1002a450a5081c0701c603220150409040c098070301c4001100031810014001020070054444804071600c002c1e041d50314000003403c0c03452090040c00250711075004030a0000300d0104a07170141c0c2c03400064800004a244548020b4801500c119138012444103c5c584180005005450b201c4201030740420041c0690709840d400401e40d0781120a01c0c1c40c24100008070609028940c1410000c2c2d4000e0041e00c2c1320245040d0800c120090140100704c04203245030f843e0300c1522441d10000a0768001080050001c1c4003880c2c071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 49645291 1250 49644041 49644053
    0x60e0f0a0f0b16020712020d06090302241003020108060613030302030301090f0c0f120608070f230603060d0c08030412060b040501031104091a0a02030126060114010219 74
    0x18101042d541903240c40c1c00701c1e110050701d1801c60102c20998004059032032800300ca40b90a02070f40c8005a034080550310419002c40c00034000c0d607001d648a64060a4242c41c08028101100d4003d800c00c1c4040c5a51420003010220560140007540d409082c1110300307680d801700144103442145225548251540c0c0c0c00810190000301031416216190b42c01d0002c035048500b100d0450319a1003104000400c00403080804500130000030f408021101004a11a5182d0318541e03c1c2a07600d80c002485d4038a815410007143c0318502003c201c0106e0350014a648102590000e481408040c1c01144a140924084007c124403001840024001d010950792510342d26021004802c4003074006031946810f15104441501d020310401c2c0c140c1c0e0303204260071280a8507009000c01082040c1049130300f5030100c4280c2c45c861951218681c450b0301c80400150382c940c14183c1080c840000d81407640b800410449084280c010007003100b41c107561003059060044411480102d1a080c02d030780b501d15118100030510f81c24407030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 49646541 1250 49645291 49645313
    0x1303020d0c02040f090c15170403080402030a210e0301020306152104050115120f080307030f06030c0512070303050d020d0204230a0512070e09010917070302070902070b04060e0f0a 79
    0x50804040d010404c047c0c501600c5d42125075036007e00d03401c961000240000c1c05601415002800a401c840100170240d0b1510130070b40d0b4501160341500b400d0751041c00000c0e8400074a01c1c52001c00d9009506500740b8070b02003050001c0142204511001c04100f1403041c210003000c155000303940c02441c003000c1c1004c0c01e02600801e0304030560100c04000f01e00100f010050544030340402940560105062429500c4071012600301400203004c254540790718503080115401a00082c0d0b008000e4050071515140070400e4040c108810003405402134102003003c03940010946a000d11600c1004d80ea0b03410820610000348038a801c980401c007200008480742442c030b203c05d115400c030b054441c4d00d601600c13082006010078060404540b26400ba003c24050b03504811103403030b042080c0d20004111800655640c440c5100b41c4d1540ca010000082030400505504015030b4000b8800a8400c46c0741403400c2d104c196070b032440100040d04094940000098254013001003021805403c0e040d141003985c6440c003210451 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 49647791 1250 49646541 49646549
    0x6060c160509101508071e1101060815010306020f0702060d09061401050f040e0703051f0609091203091a0c04090f0527030403020303120f1303020d0c02040f090c 71
    0x400c80c4002075110103260b43e15405507001d460311a20072074050790301110344000007407030700d81005140d80c0c500f840300d1040908043c0c20f01240e2a03d02d401d000008907203007155855408068194825180c94241101c2410801d054076004080966107401c1d0301c0e0708280620480b41b0094001000003000410683c040e0b100490551103524140b1110b1007125000c0b107925428041c10303030722001c2a8285c01040c64103501c400c598036201d0381543c40140e525105d4a051000302c070001c1e16040101c00003d4440c212a11a50010f05000c60b000c020000350f684030b0035201c0c000145084107266072648910306000403ea0207841200320701a01600fa0b280050740c90700260064410220802d00301141d1080c0031700d00b80201849021182c150340c8000d000780146080d100350b00ca10001c4140410070000c005a1400d000806501107406461130043c2042131450a00c45001001c44141c8540342443c1000a60b0202d809082650303680741c00800d28490340001401884d42d40340b048409850048050204042d0386003a00c111 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 49649041 1250 49647791 49647799
    0x21210031110081512010204090903080901050403050f0304030e0a09020c0f010207020f060f0f0a030902010807020d020a030f02030d060e01050109170309130b03010c08151002030d0506060c1605 85
    0x391600100b4001612014440007000c24010800107214010b03c0c1003c401410740217103803c031a800703c0d04186089034401d1700304000290300d62884805050b00010410b80110541008102c00e140c107803001003890007860920701c1c0b0500c000000c142454442c0c0d52007032890704000c00c11083d21ba0780c0e149100080d4800545607850703000354040c0c501c1c400818402e803240c154018000d100c00500340c0f0100952540011002c1400801c14081104407400e040d010b8022146903480c0001d040e910350001503e2404021328480131580189a40c01400794041104078a031a8142090715036007410a40c164198060080b417a41828603050000500d03070a000c1c4802d040740c000f81c0b14120001c0e00e03410320007010403e4400c461401d41c01000000305600b000c1d00201c042c0c80f18007000003a01c06005002a0035540400042d41c0043c00d04010700142c151000c40300e00855a04440c0016100c00e180e0019450f4013071000c00e68034807962500092419220041125040d001800c2540c450090003422218502031a0107880c0c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 49650291 1250 49649041 49649063
    0x3061104050306090d142802032205040609020306030a110103060b07030306090f06050312071a0f190c021005130f15050106030902060d0f0b03030a0201060e0f0f0402060d02121003 79
    0x400182c2c00300b21100076484280b001c0244000071f102c071921020785c54038032003184010410042030781841c03600d1002402044003441c104514020130170054560710b0700700300c400d04c3c030420a0145694002610054090b80140e400d41088001001a001482a83d00400c01003000241d4507003010741c15800f002c2a81c1011100300078a56211551008594090003480d4040d03000030402046480c3c280041e0400c1031180d02004011044142d240340385610035125038110311509003d00030b211a581d16102d2140c80000810845c0b00c014000c000e544045a0409505069840000c14080c02c01088000d055680208400b10001001e203000300c6403498090030f101e102490000085116032003805080c1080780c004000c41e0030711480302c01400081c50303100340a08a0681c2c07400e6801c0252030505c0501818606600005002468400b070a42c4008004044034501d0005100300400007038034020154000342c06840311500e81080301d140d14001d1084d40d41c1ca11400818034100400450085004030941c2c1c07154500d108 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 49651541 1250 49650291 49650317
    0x6010f03030c0b0405071a04080d0305060108060f01030f021204050607090f0e0c07060606050306211915021201050a15020c06090d021c02040e150103061104050306090d 74
    0x1220508900000340000c190b9103101000c907040b50f90312a04a40240280c5203019506c04c02103403445404e100002007400c006c00c0410045109000381a5285a2414244401d01c0c010000801c01c80700100721501c14010003514441d607034482c0d80b0403110301020380e0045542d034445c0c50420a1003c2c085404681c0d0380716180014120901c101c0c4008101c0f41030700000c1510030300b07280300b11070600001091500c4204040c44400d01080d0240204401808107488041d643d0900100b406401c610296200c43c0100c0e8001c15400c0f62040064a122400b8820940810010b868900030030f425258402104460740046048014840d400c20b1290488004aa040c500346948003420031003144103150703401c05078000b00000001401c4c403100034039440c10010000380100781c0780d50008071064107100c90031500b06002220481103041510685111101800081c0310a5808036800d400c6030b01c0500000307081c3da031110100004e000814003544c000c0c0000a05072046450b04001443e555503182550400044d0719880400c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 49652791 1250 49651541 49651559
    0xe0f060a0b1203040e0402010309030c05031b01060b210408090a0f0f050d081e090a0303050903010b04020708070f0f0b0a09060b010302041a0c070b04171c0e0d0609140a050601 77
    0x4e0210780b40800901e0312565150015802402caa080541c2800100411a40060418401411940c8000700c407401c5024481071035030300f1100c3c103401000c0c40300c40411042e0280600c0008404900e01c24099500d01355032072340341c0b40b076040c002c0c200c000d030300041100350215040318030003c04015100c3e0359a0307034030b02650384030100b006c941c400002c081c1040408100d01c0b2450140d040705000d11180c2d0030340d01c1e4608100788000c00e0380650940d00a90014030089a01115498280100059200100c03015810203009458102c03d500c50014014000c00400c100c600400c2030b04000e00b4401f541240742840780d071910020b41c4010700700312241190f02614001700329241d58000e20075034080d07030f448242380c21001070070781051503441d80221003107811881548000569004214005c0000c2d000007451400944941650705240400e92888000610142c04142d00103030760100101406c1c07030044505150a484a05044000748074030900075144020280d50304184440020340b200115201b00101ca45c541c0c2d82b8020780c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 49654041 1250 49652791 49652797
    0x7030305071b1101090b1606051305060f090708010218010f090b0a030209010201020c0d03090210030c080708060f090403031e0905060705090a0909030c0209090d0207090e0f060a0b1203 81
    0x4082c9800c0201040010407600d4520343c00407101030500c4404c10b074a64414440715080b5840c018003511a41d9221000c01a407070080940054056141c180e0300d4201e6920076449440c0106440024881000081e964003402c0000200030041e0f031008540d2202c103d0f02c1102d0341e0b0040303151140803c810032171140704c1500c40c81e0210215545c01c00d02d0750a2420341c0c0e0049021b90b0110842c0307030448d1b400b48002d84051006000c2c0c5d001c141d0143d1400140001c003881440070b076103540e41e42d01050614080300308c3c0800d9000f40311250b1040c91860404c1d80b0741c2c0c91800040881714401c0c259070700640800c04020825816500801a8a018048502002c0038540448050b1955402c00030b159400101c08244903d0251000c3c00410f240205414000c40d1526036100032110109005e0300003d4115000b1015410a030384450303040308202e409080000c441280113540d80d43c29109491500ea6108042e101c00c0f80e09010707441c1d00d002032006480b51800c107066410050500300030070074420500d12207190101b010000032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 49655291 1250 49654041 49654067
    0x70c060206060f040c030605090f090601050d050a06050601090803130608090d050f07110d05010209010311090d0b0604060f0e0406060e0403090e090a060204060f0801090507021009060f050108030703030507 90
    0xc40054443c041800041c1034059100018152180000b094645c2c0d00121944260140d8400380780626000b2002460400107030b100034029018140c50001082012460b111203640000c07000c11903465102c0100d0f0a038049034840310150101140700c0c0348403241e0f006110300301d550554403c5081d07180c540901d03403102a210f41c417401040041148100445c1c06201410f0014004c4900424400182000c00c6410b0034481d0121100d0754001240300d5550382521841071a41209101b5a00342041040882c810b8002c40308090250140d072400946a50303212f03040000600b008040325826155500741400003140161001c032030f81c0b41130070300c00310301c0c40c500a4801e4403c41c2c265441005240c94614031a00078403000d401c0c28441d006201c00c0101181041c0000c0000f8031041e030783c0070104100031000500b20001a040a40d1450510092140465002a0380058440d40900002c1c0000c0a45411401010400c448003119801e203400061f0840c8040b000d010b14900039101440665125002152240c0482c40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 49656541 1250 49655291 49655299
    0x20d0605161e120b03010e03030403030c0801180203130212070e06090c19050405190e090a20030703020306010609030203060f0609010b0903010f060b1b030423010c08030c070c06020606 81
    0x15940342c04a206080b0261100030103400040c42041c010003003429212030352604100c40d80b00105201c03c06074148581140c00c0030302c1c45c0200351541052001c0d41102032482d2440071031138011012035030030780884034901041a4010091400e0300c8241020544850140c45411411840d0400003078050800401140c428060f141e03995160903940c86000c4081d8000350040f1040010900c0013049903128044880c0245602c0c0400d1320b02a0b140c5000b48070440e000908185994010074203800028290041c010700d02040701c00380410810341032000c01d00d041c000d40e001035030601c5000f00006415030011804005e581c001c2d802d45445603900c0c00b140c0c20343e442c295031154102e52800c0040090361a180f0140c042c15800400115081c1050320904080e02e43d540c01c480300440c40094000001004904000c043d80341110107507040c2858100003814409100e003018942da202c000320595968032030544010301a602110080c2c07a8100400c50b412030390041d40007107820702e40741400410011300016040744107000041c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 49657791 1250 49656541 49656587
    0x61706060405220c150f020d03240909050c030615100309080a08010501120b0303030c09030109050709020702010f030b03030d0e01020f0406020c040513080d05090703020d060516 78
    0x6020301c4010000104202008521840d440718040710040450328450300603006020000d0070b000410b00d500098003800d07414400520071070724000b600072507010006420303820002569140303c8c8600c006503420600b054a468040302c004501c1d84aa54030031304c3c00902030021141103104110502d5500c2105641c001c61500781c010000c2c46500d04480f07040d401031100e2402080c254102c0e907840d04150040700f41200070540c100018007540d6401421407000141d0000103020030710b44807003c2520ba202c0038042d902140e6000880900e070fa1030941200c507219910104583c000c55480c8107010007034101c5c0c5002ca000402c1c900795080320714402d000b0b041d00b081d4028007440c504000c130a500001094940b50892280d502031204000442207400504002c00e0b15402501c41c240c0d00e60100021208000c00312020341285441c4500440e081100791380000b083c214000500781c860401ca0742c54500284d100940c0040c030350301140c082007141c1d00160300655260000382c0784a8035500040e80c1d4403202c0c20025000c01c80382 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 49659041 1250 49657791 49657801
    0xc040302030304090b0301150303110c0312090d020604030206070b01091103071d130c1205010b13030305070302120f09180912070c0509040b011a03060102070608041b0305060604061706 81
    0x2540c441042c05c1801000060a1003009014a10622155106802240300c1009156481005010703503180032004034040e02a4401480540c840e900a00f00c0f100d010300e40c00301c4000119201e1504807000303107800400c690b44601e4603103400c2c41da0b26002d004100a41b820601c00904080240b01540d0040245440f94450703060b40b01c49801007880004031295011078050121408144c2c40e201e020f50303009107a031722a540c103410b03200208240c40060348203500e03200301080102c010518540c1707184180c13541440e015580d1010b50600702e140c030315041c40c43d04541c400000c4002c804c1000d4001408012030560f03040d40110754000c200c2e6a0640111707003603451500081108409404140d0041c88013521449175070780103580b50804241030b50740031a812240302030b441c1c00600070041b00e40000c400b6001505c0e001465840c150700001d45900403449400144101140802c04129114403c0b4031441ca54850304c020b5140d590034440d940d0300d400e40358240107a10303180f00820200420070210801d011740c03a0040180b504c907 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 49660291 1250 49659041 49659059
    0x180a08040906170c1509040b0a0b030a0b0604030f0b071107230102160302040b04090803090a030305100b040501030911060c25031106030403110a06050103051506090415060b1209060c040302030304 86
    0x40307030803560b00c00d40c4c45014980302d0b074030300c270860700900030b00201d4940340d2511403001c0c2c0468018840580c49144107020810004520342554085194800e20b102c80c0d0b070b181c0301010303503542c8000b030100c0e11a40500b4401142c66003882c0c60040d080d00c4c01d000d6010b040d001803401643c4400880c10724401c1d9607410b20050015081981080f2194100500b0000708003002d6152640190410380e06440d9a4005401350000c1c15414003a840c2c006074885a9012020700d0503249050612039031043c1d17814141c85003454018000041d1040c0d6241002910595030340684080d025110381c0c03503800d4010f03842c5102141c041440f20107140c080540c0c0d8000c45a41e651050201041700302d82005008504104c1c5010400140450500020261502c0745501207059411407800e5820206c552900140d0040c003201044055035070007100c01d802a802c04000c0d40f4000c0000000e2025000b10303007002d02292400601c403003410415045080c402e04010003598180c1d200c020300c0c1012841203100107541544148814010528 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 49661541 1250 49660291 49660297
    0x14060417040b0d11091503040611190305070306050a031212020a0507020f060f04060c0c09020304031209020d0816031101020702031e01140a06050102060f0c03180a08040906170c15 79
    0x30b07070722014100a841c0300011207041b580090016800008414042042481c0c00741c0300c0946202104c0038100a9201e4140681c41880c0360614101611030020801d10342c0240d01100140202078041c0f0b225944030b00f04000a800504c010380c00246500050405a401e6442601e2403030400d5920b99181813202e80030003404141a0388401c0e4860010805048540d42c4000240000c082c261902015150681040148819070358007000d041d5004000700f1000907400500003894602c520000250310750350f400480c8480101500082003010f001a450244044445078010070303d00c00da45401d04584a940340a00340d00920400035015071000c03030802400c288061180440640900c00002e80c01180304a50401103000d441e030402865860364107020951341400220b40c03180d03028040d80300c02d0400c1c3d000d4807040e100c02400d1350003840420507c284860402e009044103d03401540641e00d45444070024001840346103e16031407035003044070140c00c1c1c52020844400042d00100144203808400765070a00701d038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 49662791 1250 49661541 49661561
    0x60105060d061502010c1202070215222409030803010e0c13060302120105180604020c0106050301050f07030c020f06010312030e031b060717010909060914060417040b0d 74
    0x142c40e144080741c03080e803510300b00780718054030b900220704c0001101010b02200ea41c44401008180104952405601e0300c3d801545204980e0703015a41c3e038100144026806001640d0410302c800445c40001101004091790104010805450071038000e00ca03801651445410711008151a2003071004001c800f40e06444103922601601d0b50618101c0c5142c0c1500700840a5003054011035408101c0142d072510380c200460140106407550134801188440007941008010031107481640c0009118000250a403c6003005100c090000d00c002c2c203141e040d03200e504500300c4020b40001c0c5440842d0804a1000500390500d0b01410301500a0b03134203686405490420200f130a07014151900c50400c03032100100010074894034181d120f40b04900001c40400e0401070701800da1010006604410407804020842303490444450840008600c0c51625046002e070907150340180820f400b82400762102000800d26512842c4a0f090302c0c00b02c09005549440c0d0b50280d8080d240040805210310701c95600e05a0200b4410 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 49664041 1250 49662791 49662817
    0x1180b040201020a0c1e060509010c12021606090302130513291303080106080105370305030307030608030307050304020f0d060e0c03010b040e030702060a050d060f15030501060206010506 82
    0x451301c284c40b5400703601c0e5503030300c01c005105558864040444c003480b43c00300a08008d281541c50054040f000a00840094801070a000403408010502074000c00003529111540e448151880382d4408000d400458030340300a90254415001c0f6620510b41ca01c50030348144111100589402801d44440030814801001c0220001c1d400004480c02032000c4820707071080c000c50304007407915402494001c0c60318806a100074240410030b401800f25941e00f621554280303035003400c03843c0181103e4a041d160019503074202010016440300c0841400004001903206080a8a00b8800f0380e41e44c1603081d9982c030049440340d001174401e1010034010b147c82c0c00c1030740900030010100e5140202a0700e800c0101d4107140090304072030317111842c1200c0b00d0078280190340112104032010051403400d89001c5850782b00301c24009214400020341028400d004506a9108003a1031404020254482550b10414140c90050002c1d90b20500100e51040d442409164142c5249602904040e440e11003445100d030050030b030550320 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 49665291 1250 49664041 49664053
    0xb04150209030303040803041104050105091f1505040614070b04020907030e011a040b030606060304030f02070f0807060912050a0b0c07150501050a05010c0819030228030b0301180b04020102 83
    0x10b950400203940542d0260245540d2810917241c00e842c2d01c84108450360056081c20b00401c242d40e81d00a0b40e5600841040c10f0081d0380031403001013440701d4402e40010008405091a01550130340c40b00c06041640d1240d15008148520b1440c0d54219000f603480c01011036180c0d10025005090000500382c101c500c1d400d0109034905044841402d446002014815114500001c14403034a00f9004142c2c0841c81600906400d040c850045000c1e4400100040c0c244100001c40c07158081c0308020302c8008004500d0f0510070141c403045a10b0b22004d15214003400100b60300c0000c20a9004041c1c000406503000000340195107040d42d0764010680300900c10020394000344241000300e00c1e006081c3c00b4205095600143c550b060108100c4802ca0503084203040040c001c10100c0081c401c2d404444c6024009a58111408070440040780640710302d0040c0a982184152400e403035007541100c140c00d503403154900307101071a940c0c002d00d402c0302d00032100c69041c1d1125094040201d004016520f81190040c070540304 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 49666541 1250 49665291 49665307
    0x201050d0903080a2313020a030f03091a160201030c051b060117011107030c020d0204140603100c09090216050303040c0806070905090f180106090b040b030a0b041502 73
    0x8880341d010082d40869126000c00095554900c6101c3c0a0f440c1c21140c142200c1200140e90180d10004101c001a003554511103030555580c0e6060000031903020710012070b42d80107898000c01454485c4141d0680b080210682c42c0d0f505003041c1540c10390300700b285490402c0140c43d0011809040303400b20031018841c00f00030410380c203409640d44a019001100050603654034051504070766000c940c40302005645400c0c261510031200201700d8085681514110340040c52034000911074007840000298418685422406490401111644180d600301c0c1500c0f10307502855251800e070342e0030001000010740000d80500003032109501401803141140380c0c0941d00341c0c075503545c00d00d5684195416500c0d12061802000005420040150303c008a0b15011003140d140c4004504103072000727090030181f00c078004001401000e00d20702d090342d6056140000e000c407550b244041c40042100d050302d6401541003030b52008480c01e0004a14000640c08000c43c0081c1c3e895889140800801100ca02425502044200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 49667791 1250 49666541 49666567
    0x21908060106020d0e0306010509040813050d0b150102060405030a0516020303040f29190e0306100510090e1612020f0d060e070c02040b040e070e010501090602061b07020105 76
    0x40c00b070000740e00148403090704580301800b46811010180d2003030340007100500454407405000b03504560b202c103159031503442e80b951000840d010342e00042c0e000070311a840401400b0001c2c1c0440c1c0542070013400304c0d0750001c041004903100d540c00c41e00588203900400940035020b01c11401800c42210481c28031842040c4c0d540000c4c11603015134005600a44280c1050119142203a140c00000e080c8c9000c0750064950b40a5500c00e5008454159802c9500c101030505258007590801000080040c20b481c640e14080780004807006030740c0181801030f000c00c2e040c05995030142d01c043c07003a00e00c2c0ca0000e1070345584d11004041181548030400080050b031a00c2c1028441d00c0707001900300e06926490440e102e00010f8030900440784954840c1468620340350034403018982192100020329019500801d0144401000c20040d22443c5050309040c81684800588d5034140c155060580714241d8070360345010b540c0c00c0c049907940000d0b103c910141e410f60400807120010940208078492040c1044c50030420801c0d002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 49669041 1250 49667791 49667803
    0xd1709150903180d0f020f0d020603041212020903060f04110a03080408061b09040b040b030304140405060103090506070e030a12020109030201060f080703021e030a03120c1407021908 80
    0x1409590b1012452958400207401c0c402203000044e540f10406604544541010b04c45041e0042e015003074004101030340c0d1300c6580610403001e402424055403400d03e440d00000b012410b88101000800c0040c10100d1103060b8000c41c0e5160360001d0003803070f081c1c88030309070422217000c0580204c1d0500b4844502c40c80035200c407002040118054160103485d14580080603052a80083c01c0c0614000c440144200d995a00c41c29035041040c203981c00503918507494003240041150102c0d55074503104c04240010004042c480000b001d11007034030244030949400c8019400c1d0f60001e01b000340950040000541000e1140728901400d50005040300e030950350036200c0e0390441c0c0403022010f0060351150206024107409005e0b146c014281603403842841880d000083e40c58500740d0200911a02c4480501e058040503d2180d62900c100181541d1300069030380340140c9440d10f06c5007006400e0341003107100d40c03c10703000e031807000c0c0f5464908090900d001156170030006145000072100280700080c1d6000f09a0003010402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 49670291 1250 49669041 49669051
    0x13e0706090b0702120301060507060e07081209150c03070f0f020a060c0b07020f0705370e1f0e0612070305250f120503040308070305030f07020d170915 67
    0x10310050b9052a03440213080c03154904081005101c20001008069032103021a20095040400040e41c45c0011195130300385409903010315103501c1148209810102c0e040001e000b15a82103070b050088a080c85154401d0340140c0b003081586400034496140410307414120b1a00e454815000b50380c0c0e83c800365000550124060308518000340382d00480131300700301e5000c4080b90064441c0c0024000d10079000695a07403880c5900460380280b2101415a020703800b00400380307140c0c0039100c20740b00700c0e4580d4005600c1e1a1010344116000c1414038004520f000c03011428400d1645140200064850304121043c0203846000d4501c0d81c001180720480007914500b40320302e501441c46000500000040d4080280d4440340316006c150320468100410081203020010b2402110b005e20703890386410304982013060a500561b440501800380c0090103208050784500154487e0304103000030b9038151509502242d84139505001e80c8081081042c41281044510700c00a40c400340c000c048035a1804802e920100216040e21 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 49671541 1250 49670291 49670303
    0x20a060504051b1c0314090307090218060c0706030203040309080f15061c0f03030e03030c0702030d09051e040605060703080f01060f0207060c170714013e070609 71
    0x200389000b22003a100441e81000300c64100c541310000340700807100450720f078000301484003401c01c5c0d5a0b00e20b01c003c1614200c20f0000c003038800c0e20342d03600100b1001c6e510071010720002001d1082c0300360107442c0440c00d417031980812100801c2000d0810400390025400a4420780c10302030001400914030600308804d01c01c0308101380281c041c41e480544444607800c406840180324500315000c50303600700e1481c0c1c40c102040703030003805c1c81da50b04035282405e50040045001880f4540800410003c1c1000c00303c0042007100d1082d01216156654844222400e0b001130040b40e600a0000c0d00b49006142c8012180d0041c107001803001400c0c2c4e903034030f001500783d81c0140b00840109010b8000c11090804844920780104441e09040c40e5840d40d20340d009440700e0280c00b9000c148119004940c1c184100e002407800d0300040381074241e80d100054104540c0c031021a800055956091100400314107405400c0c3e9030a183c4000703c102613002103102650100b985100e400713910002e00384200c06c0411914080d80c0d21040c0180 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 49672791 1250 49671541 49671553
    0x40b09011503060f11030105030c09040f08220806011406091207090b1e01050313030903061805010507030636060b040f09020406120b1809010c021e03040e07020a06050405 75
    0x1001540d855110110b40302e8011b0004001a84020a400404040450f51400180e44d5841c164070400e5942c1d001810b035103c045594010441c50040161481c2d103010001030040c1d03620940940d41c0c803424000c00310031b809160580aa203081c514060648150010300765600441c039021514605111a4455150307280c0340c4200418504216412079101c0e071501458511711104580064800d200141c54aa40d152500c10340034240761003080b401c00074640c801e1042c011443d0090401e800021b01117015501540303081c0100c1e50160103440b07070f1011200035000e600350184051842d040700840300c1844401502c00714410541c072131742c544a1040031301520f041503a1102d0911281c0d07070380010380350080d5400d180304001c14400340343c20034105000010341141c007083c818810800714401403000c0300c00328040082c91080c00303141c08064000d20280710300360303003240c40454031058001014907241003007400b5a0010001801507040b48510903900c031030b260040f1007402c0640d650f24000c1b924211000d0313465030466 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 49674041 1250 49672791 49672811
    0x50409080c0d08150402090f010c03090305030d06031a071e020f01050a0501060201291c02090406050609160509040509010204150e010f030501050f130b0301020c0f0d1106040b0901150306 82
    0x400da201c141c920140d03170441c24850041e01040c0d490f01545038007414400c2036038440c410036100d068100051a4440c00b9691034110101e80503003d04882d02003140c104104580901d61a00c00d00341d9684500c1c261390302c03140d46e0f004d1034000701d009100031403600007180140040c1540c102c200b40621401010322000004903985420002802c44000301c5000303a40071142c03070303e010309042807094945905808175080d00c0b90740e0b00d64030286e41c00e442446000f5084040203081005220650340042c4c0b00c2c040a440700310303407507603001d103d16054400140c020011610500131030300c1d10b081a80c0056403103074815000500e42030725400380c130140325100041503000414001c1c1030a580e5a1014448040c0c04103810103101c00d504040000d21500e0034075100381d0148210485105030700e196a0002125070703901800031540c035800c03c90100c0c1c41c0c00e60410803260a100c2c00e061050010310640c5060303031850740303d0041d04040d19242e590694500e400303404106030390740710002000700043e4101110001c51154200003408064 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 49675291 1250 49674041 49674061
    0x19081b0a02071503060e0c1c06051003020706270309080c0a0909020d1b14090405060c070507080d03060303020c01020d050406050702031005010905040308130c050409080c0d08 77
    0x20461050140002400146119500062403800f5140f50050041c0d400450a0003140201415405152074400301818455007a045000400785078810401002c4402500b405900c2a51100e1141a80105002905a1141d4840e03030141902ca44100b401250703a00f044003d44051060048400201d0b411034180b0b4001c1540040c070181c01000000b01400d1040320600c0000c101124070b1040410395501e41c4200b0045589810403121100c2c0e0080340031a1039051241383c0c114a41c5280146c04188070384c0c2072071410600c0c1c131402441c46103038444000c1c205540c4849100302103400400d4211020300c1014408a01e0b030400340190140c015050f81c00180e51071075428000e240c6080004503a0540d00316125140307100781d11404031001d590090400035074600c1107202089c90984903001130303c501850000007040610b4560480b0740602e0013666407040c1622054400103800c0f48045000341064010002007040382000c0e0005800540034501c558100001060814108000c02c0120000585518100281d602d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 49676541 1250 49675291 49675321
    0x309120203030f0703140103021002030d050108010203060a080a050d05091915091508060907050d06080c120303100504050c0408060411011103040605030c0c01020408030d050103030305060f030607030b01051908 92
    0x4285c90144094540d0340184507103560b040c04040e00030b840718804092441c0c02003048524101c0e001c00c00704501d6035a8255a03000b5041642c0c914172420b0084000603400400160a0088a8010f8007070802e0607025101034032560b001542403500040350700d1000c2d01384140260720074010034218007010849101d5400050198910390000c0c86c2400c2404480b1802541c441d000c030387e000c1401e03942401c040c0c5525600359614041d0354005a0160708002021840640118440700350301029940410441c00c42c43e0016124002110350760308020311802c1c100a540307001c1e000710b40c010b04620005031409031501c40c2541044411202611090007410102001f03590000603080005d4116024609050502c1c40080c00b030702c0082e1200115078008140401c03814000e504a4004103020340c200e0b0b07551003c0d09000405080244001d401081c40c141c0011103034244251008140c020040242c0400e43e0384070000d40041105400d100d04004040c000c0320030145150002440c41d100c4d68641d080075140407210145499 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 49677791 1250 49676541 49676551
    0x70807021512060111100617060a0b060d15121406060301061503051807060f11010504080d1802420406081306020424020f0d0f0309120203030f 63
    0x2500402800248a40094074a50880802d05e8252035610319241e2181c9482c001c0f8680620f414a801800920310349a07105440340c03d030030141030300d00c25680c010130903045406800c21035070051800c015041d15480164031844104a049081c3e114568461607000260a01640120b0b0100c110810850040c1000c0054541c00b0008500900ca041d04024029000003030703014030041070640b00c0003c2819003802001c1059000007100c202c8039440d80d00e100003040c003288000c201000c181180d00a41607454180a405c1c03059070000c0c401ca00d00130740da48001006000c809185c00f1440a100c08003001685e070400e03c0380d401c00729130302c0c070301d29200000c0010380e403140d0301c8032000041908283c405030700300700081c060b20b0440d40e450421001c40d0f55100801c1200b000e2034a40202102e200080108440c00400a916011005005850f50385000500240d07502d0f2005031281c03110791310102906840c00d106001c9417110007114540818015165a9809180c2c0040c05030000942c00c080100100c04910f4141a0b5000b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 49679041 1250 49677791 49677829
    0x603170918040302070605070203010e01020f03040311060601020a021509040905100c020601030209060904021206040602040911210c0f070f020405060d11010e010302091f0e040903050412060e0307080702 89
    0xb4241030381c000e0b40e40c0d04148141020300402141e144150754080d881a00c4800100e002076503150f5041c410030801d9401103c01310049403291030b100709510b81c0081d1041c030031403040e00105030000fa103400b084501800602140d0800c1c20070045461291194080c0b9440d03680b164004204034005244c030401544c1d0300c02c0d440e03001c65100710010405661800e0300c40d0f40056090b50700c0a140c2d101ca0020614000081d807522750144107000500c800c11516600801c00c459801d4010400d100d08804d401c0070a00c0742e034161456465409030b20f02441401c0c1030305030350080e4114054030310300000110800200d410100c000e0f039120881040080a40c10301d8083c05501141c11a80035417454110741c0ca038840b450b0000c5003981001781c81c500290f001e0740a541120400c0da0002c10050001103902060040302c0022003a400001d0790584604000781000e00406442a515440d11b030f09003400d0403121940c1060f01002075403444d8552a50388a615414401050310a00402c0c0540d501c00c014014415000b031003684054070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 49680291 1250 49679041 49679089
    0xd030b03060406020f0415050403020a0905010e0412091206060f0f0506040311010c0602040e041208090307110f0d030504060f0f0906030906090b09070501260f0a06031709 75
    0xa03680215030158801e500080058448000203200340b40c0d4041e0360131005050755000b0445541980180c09070040303920894514010a85400d040000e4410030301c40c3c81c21403405000850b000a0701d0240080c0c483c46980780c4600308a980d0200144290201c14007510314584c1c401c42400046103064214001e41940c03903e20940d2468040801c280b84602d00c005040c1c0000d00d02c40c4e003441c0e88194480071440c1e400078002d644031600c818600380d8400d400c1e03404503000f80c484440d0411860181c461144180520b5024608002490725203075070300d524000040754000d1302c95240c407800360f442c08101c0200c68025070303c040d140d50400302c1c060008511031003110b00344188040701100c5a0340c01240320342694003c0c600440c20300e4030b62130721038040c02c0c52501c010b10850001c41048850140042d106045417001d0b030f6031401800b89410707030307003240702c45000860001c00824000803201c0da00b0101642e00402507000c001651071362500c5900e4080a4980c05140c5076400151984192800700ca400c0d011003226400460 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 49681541 1250 49680291 49680311
    0x70510091203050903010623011805040e0a050a050d18030804090b060c0703030e15030c0a0806120609010c11010c0207090f02040f0306021e0f030402010e04020c011802030d03 77
    0x141115601c1105640d040d10200c100805220b02e0607104410b5001c0d000b80282d5807150000c00402000c15134a08800600b50b26214940d84518003a1001c0c0c400d000949000e541004144009406240600142e80c46180b840f98000b640800c0724901d0140610081d01020803068401410100c045101c200201da05000a1020500726421101262351412000940c000c1c03000c040b03504c0740a01c400d41d84090046007000800e0540050514245c543d04485901c1d035420070700e501c003050380425035800d600403500380040d4110070301800016400410040a44d14600c40781d0f0201450300c1c0b4119039400c035903511058400c0034030360807045000c26942108005c3c4031450b1560f80003540c0f600e0703610552401c40e89407628a0000403c40e4121000f43c10250034601800ea142d0038003002035842070308400204450f8100391450b950b1004140d0b000a072281c41c40c0f9286403916001160400030304808144e00a600f0440c1c0c1011000901c0759458840b500d9186407041030700745c0105400c0015202095083c107003424503101c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 49682791 1250 49681541 49681547
    0x20303040b0f0a0902060c0d03050601020102130302060a0201060f09020d1103071205071101020c01020306091308030c0711040e0d08070206060a030b0c070c121509020a05040506040e010204120302070510 89
    0x950300004140c035070b18450355000c094001610306208065080310f0300165101490303801051001000c0d40d180c0303040c41103484400c012401c034880c1c032a2549225100c0c040500c014034044005100b2140e02d0b20001c208075880300302c00d00b4021071076404000501d41c0010000c0344908507020300d903a401411020682035141040c80540300c0700f400c50f90001c401c6c0d6540c0c00501c03035500400c0303900c141c2040a030003192141b12184000f4000c0d40f090320032900c190042000035250307101c44040701030215448144542103407180201c8128a80102004841c03440c010744203140c40d07450b07504c1420f18200c00c0354001d102d075a40c1010083e01d405400340806045400200400805450700240c0001301c0b07078464001002a034030002c07820101e00944070020125400c1e6480010f00850074512981051b0207200d580d144c00c1410241745044900101000b50407075a404420042460254401e90f030062000e400841e004400340d10726400c9034003d41110181800d2480c000c0c06050b410050900a0142a1a10481144032034405 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 49684041 1250 49682791 49682813
    0x5010504110f0d1b020304051908030406350415060f1401050c0304060201050f0f0403141b1005070e09010806011e21021e1f02010e06150a0602030304 66
    0x8030560303000080f44020010180d110070070044948100000a15090740006d40365482440381920503000c429444107001d6012008100b161541b2004624161615505950410911a0300e52080c808101440c940e45a103017a404c00032503402c2c8081d03209140520344060302001221800c07802c1403400d03000b4048040c4072100001a601007108030303800d1400078401212244907102a403900780c00041800940c090701500420b000e00c480c1964698207940c0c00c0f52410031910126030240c00600748043c402d419403004c60040c2001c0c00303503891010351207150006031403512100300000a00645d4079010440003990040700080c080c90110344290f00c551400c640107694801c18003039420340710452088624030812000d502c0c1c00138650641000b03440f296001d40407000b032a0303103034041e8094a403503029003030341c2c440928024107200340090031201007603000c840328501c2c5075114111409666039203621080908040108501c94110403151000d4540036006000f08500c003a8130800540d40140f00340b00c0056507004072 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 49685291 1250 49684041 49684057
    0x102090f01030b032505010f110d0e060c0604030906020105070207030b040b0a02090a060906140301051c0c0f09020d0e0f070b0306060403120203070614070c0204050a200403060501050411 82
    0x209040000e540001c5c1400b080c000012410304260340840800d07104140c111040300c800362141c1c194591424030542d4246101d00b6001c0454011480005039a806010301e24080240601428100449961010304e80300d026207042d00840c030341c9202045055424000e20343e011000d440a03046d51880c655440050810190000300344900800004100c0011075068030140b503802000c00429036511000902070051700e0040b8000984c0004ca290154030401e4100c030b040b00c0000c0c0001d40125007040f41c440142081032400c681384908a4400107540008414103409040320450040e034074041400071404036038803061140313015001400e41c483c20100100c1c1030411109910590380d41ca1b641c40001402a2103643c00081c440410700c1d50031b244081c0e001019001d050321881042000307486480c2d903006101d00c11105180060036540c1500b0050900340c02c260307007200d609500401c0300e1442c940f6036203c0e061406102480ca2802042c10000e003c01c030700503580142001d403010003040041c2c0021b400148500a1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 49686541 1250 49685291 49685297
    0x809030c01021c14190c051014071115092805030f0c01061a040e06030610090b06040302030a0b040308010f0506030601030c05120c040503240a09030207030f0b040b0106020102090f01 80
    0x131030281c00164a5040f0f40c0d0100b2400f007070300207607920380d00007405680c0b030500207407114480d00d254580e041d96240300e00c01c0041c07400740002040c1d6a83e540111481e9604811412040c0502c02e50703420309900002c1c00601410340305c0c001c5d0004802e09407000380c941200c0da01c40ca00e1803c1c052082004204007004a03220090940b025030381e1307281044030450141c4101d500800f0034088104d44100c6a03044007000d0402d80d501144c600d80591070710010140e07100b1060b01c0300c6103403122010b0100255026036125224201020303107607500f81030340c81d00042d0a004c21070005854080b1a6010401019403018403030b4058020151043d02a6080001080050100a101074145943d43d481000304070b002c0c406440c01e1601c1c000d20180c051418000a03400c0380c020f0310034640a44512041c03040d1520211030250b0003a4608040080240d50380e4907094094090000103406500903c0c40c04404602c0b114080000940518001505801c107444c00c4040741c00168824000c59105100e2903c1541d10304480b8030401c1e009107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 49687791 1250 49686541 49686557
    0x11404170717060f15090f310308070801060912140105070c120905030a0602030a061205010203060109090504120810170a1202070302010909090309120809030c01021c 73
    0x44650745011100c0e00300e0b448001c4064200d602864000440600c60400140c010400f500c50220311700c141c444900190b0b0788a800300c0c00007445003090a4031140d010303041d07000e0002642044400000302d030b402c0300882e50300e0510059520f4103040d04048515000080c40c5043c006640c0f401c8001041b080709805203031300b2005041c04c070405105800000b0503008241d400200a1070514103c040d040c103025440032240090500c54480c051801081410200d0704060007520282e04503980d103000a5100425a420281c3d43c4c0201103900041921000740140c8160001607607801d101c0005000e0b4080e0380e111002441c04e101c1044001a001745404086240c1410a0402912041810048210260070404030360500c074400391a01c640c001892104130380204a95100c030420490101c0c0c0301d40090001902003a208a0104200d41455000943c018003034504030b0900c41d1103502010024a14a109031144080802c0e54401480c0a1005128115090004004500c107010f40c0d9000c01724581da102c001d010b506 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 49689041 1250 49687791 49687829
    0x306031506040b0a14010f03150e060607062f03060609060a09080609070f0806060d0f060e150a0e070303080703020c01110d050106080a06060207050609010e090414010b011404 77
    0x6402c03ca20421004241d4203150391500d01503083c031180c400c62103000072160b01400000600034401c95040190b410b0080b5005400c2020000012601521840e00014101301c0d0f000456028032408100c00b9100b804075400458001c2e4410720203086c0c221b00c01e03290307104000b0711416655404c1211032400c42034034101c0e01c8401c82c035001d880500e980d511441580c0a08002c11812a40126010081d280010061103045071107030f1705c680c0c2c2c412040700e04a400204a4041c000030401c1c481848810303d00c0b8180c0072035041001340450381441c1c05030340301010401c2004280801076003540181144481200020072040d455a24000ccc41404080d010300149a0700141426451200790000c1c98582d0504264503952072065107201c0c02070901340324030000a01b407540032540c54101400b6483c00c40381c0f642d004241241c00d201c00c00c26503900844100b810700181030315a00c80307a250030820510650140e04100340c0d90481d040100d094a91003000702d030403c4400021114940c0100e400c2c0c1e001c0c0c402c141101400c003500c0b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 49690291 1250 49689041 49689049
    0x70b0f0117150717010e07030e030301080c150f04080a020f060316030209060d0603050a03030c080903040504021c1508060c0403080d0b030304030215031509010e070f03020d09050109020a0b0306031506 88
    0x2140b103c040c03140c131100041100646a6400c5000d03d101350b50030080407100c00c034450f459000a00a0b90025005040d1428483c940b0001441132418500810f520f00380e004514102d0543c0268170903211900104003501c25440c0111280600704821f68440c2e10b5403070702954620014031000082814150f02080710102600e42d80300f500c1c02c4194207002000025128146140e5400308840124006420030803190f040030301c00e0107518060782e00c0784000c5003054108410800070750041860381c003a120512542c00c00360689400380c0c1da0441144890080e03132509004039582044401040321059035000c0104000061586080303070409170141400040d02654200045d086200d140e2000e98840f809110761410758404400442c015800068401c0044003c0801c0c40030803c024030401c003200b400100001e0141d0300507641007044c1c11007850010b00d000b807007400b0b203401c440c4a584240c642c0d81d551040c4508509100c1c401c000031700710307041005045207060000640c0d5258124900640c0c802e456000c2001525 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 49691541 1250 49690291 49690307
    0x80d03090819020303010e0603070e0f04080d1e1a0a05060c0106080d05030f100302010f08090109050d021b0904081b1614030105070804210c08070b0f01171507 70
    0x544511504030800d02c0100960320f81081c02a039030440c40750b4004c41c1091500240c04e80450351450303262601aa6510f030b10590340100100250764035101000b80e182450803d102e04c0c41d00c00030000303074480c0b404002d50100d411910300309a8441520014040004140e035400e0140302101d4040300c0046d600c6c01d00c404480d0244c00303a03520030440741c45011040c2c00a5078024000d54441d01900c078040002c1d42c0e6000d49150301138028032000e400b148100416138540340c400c001c1c06a2204002001082086196403824502198421100300607005458000d8028080e030080c0b03c9810422102d0690034102601e0300310a80c442e218108180651000000400401c14417001001c6021340c0c040c24107059986d0800255600c040320703441c2c400d510304400614154081c1c4861070051350000c107a081819003007024001e40c0d08000b110001400503401c01200020070040c018a0201c0c4030345012403086c140208408884031040c1c01004209001720b10454400c1000505c080d805205460a5174440d00c807030000340c1e1060 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 49692791 1250 49691541 49691557
    0x6100c0501020f0a112e02090a06030b0406050111070603090c08010218040f05041a0712050c0a0e01050c0a080a0c060c02160b16110f030a030815010504080d030908 72
    0x2500100c2d003030700c4103441040031303100c4500251100310382101030f05a11502c07412281344410403510520f6803140c131281c000c00030f60302d5106001401407600283d0340008482c5825980081e0000f501d407603c6140f182014058440202401e0030220115151188130646420140c002c0000300350ba65221a0305000c0300312200b20040107040021540d41002c07230702e5aa04a034420f801e00c1d0040307040000070715000e5000d1007568810340c2c200307501c60034450322a498403c400c100580400308100b01c2030001c83c0750603004d00c522800342c06031910440e902c42d520003014100450b0407808a06000d410f00104000c5500460b10728000703540800c3c1940c3d110904034041c1c07402403120030003a049601c1c0c070038118040e5800040042c02c40e03211050360035a059440c004c0203420f02c903000201c02c0154404443c1300001d81c801c4541e080b108002801548903641180c0824501310b5124000d034002104101800030102d0303130582d80c9074004801e2070300c24905410150456500c1c03c104210000305136807008440d09021108050311103003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 49694041 1250 49692791 49692793
    0x90f0f0a0b0904050127090c0f060306030614010510030c020106030f1505100503030a03090510050c03040308060316030f021801230607020904020114040902070305070b09010603020906100c05 84
    0x565100e000710605038002c400c2160107140350200205904107214084400c2110b4014090440c1401018010203820081c4088801d0200240301051840b10700d0803a10162030140d500090017855810131009999015181c203040006080044c00301d45c0f1000012001d03204641008100e520040340c08900410065001800700717a440c0c0160310410003400c06a036036a20a014050201d0f80310030702d020380031030007d205581d856801081403007100c40c01303504000011030051040c0e42104d4900c2014006903002250b51125100b000002c2000b003503081149690440000c0d0001c003000031614203101100c00280c00b0151100c250000b4000843d66010a004040a180540c00a103942d54640860700c2c178542802504000940b04007020040c03c0c18801d440e0ba10f9001070400169807110b400640b1880420151202900f0041202140d0800035000401001d03200303950780365507180e00b4140b49900c448045d060a4150741003000400259517460440354020700100d41d540641003d1003070650302504400c000401c6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 49695291 1250 49694041 49694059
    0x40209090f10050a0e06191a0909010c020d0e0d080d1808040906080f1c0507060e15070c050c01050f0d091a0105060c03040e040807020301020c06071209020303090f0f 73
    0x60b0b264a40200380202500c400500051040b0000c0b00d4a49500301d400d0300742612646042002d0102c03039000100d4045040b241e6150396845d08010400d80141103887c5903031070f0b460702864112680e0401418114a015141012130760700900006040d0001d0310754083c241c00740100d00e80f41104c0380c1c0d82c4609207111b14208580e0400b2010700d818600740d0002d00c00d800c41c55140a200060059000c140701c171000840c0d8010b401030702c48424a43c040c1068014603d000c101c428010b5a000400d0341c481d9481807040e0100809207156401c00303a051f0b48030002e1201c0100305071000660001800002c0c04d4172421003d09000b511076030141506070395030050040c407013440ca06010740754050000c1150040526a107244901d981680c0359000e009480c0310300c0c03048410b6a8006c04c0104908010140b0323441c0c219220f40c0d0001d00c0c1039803e400007400e81c1c02c40a0743c080c1e541c001805020040f508203c401e100141c0c100c0042c040c0c4007440d000643c407802428a0140251041c446c07084240d9201505003c1080c801003020b01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 49696541 1250 49695291 49695313
    0x10e010618051909050903071a0403020109080f1305040c1205070302090d06060807060512010311031014060406050102010c0203040302060f0c0604030207090e0304050a060507020120010c020c0603040b040209090f 93
    0x140f6400503208071251103142c400070540c210004000c503a00a030300241d11100c0d00b680c0420f08480341e10000c2c8183e045541e107108210001b8495001060202e20070640340f03840305900e18820003d0441c41d40b203107101307900e44840c0d490815044007110345420541e0100241d45c7d500d408040d006803180044460f40007484100d04400c100d01075110909480c3c000b8100d40e0a1900e403101981c0300e125076006080c0e0740e1a020700400002d8814003448545410240035a400004140440750a48003241102c502c0102c1050810200d410280316440050100b48000c2c001141e0f4280081d459110f14040640207550004c1c15a80622001c0c0845450b000701000b100c0b0b20380b8060800940740c2c0360b2409481005400c00301036904100d400804c0d00c00307560300100305901c42c4c2c3c0f074040141d030300794050042241800002624584480810880344240c041e041001181d011030782200241050303c101d166500c519814010701c00802c030b15000c0e4503441603040c0c030501c1c0c141d112251034030314002480440c0052446961015a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 49697791 1250 49696541 49696579
    0x10509030a02061605220306050a0c0216050121020702030a240902090106050703110d020d020c01050301300606081609020a02100b040e06011d0f010e01061805 70
    0x5100751541e082d03402980351040800d00f11300403030400d4800100e0501c0000c1c40c4000346049002014440c0104040250340e0f41d54040c1901c00840b402800d0315900e5a8401c2d0301501032000302890560603422070ba00e6814040041d00d03c60f80c05c2c8800107038450400740c0c01c010400980c1281d00460b001400c94484030b240c1d113002d03103280e41d03c035482c2c01c5c0c00100b0544203c503022080c001c1151040c5e005201401c10381c24018200c030f440e00003190980030060130030200d0000e18010710604103554660b501a00ca180902d00005e0310300011400c00604210041004102c5c0c10304240085045802561484402181403004402c5031010000042c1100e0701d4204001818440010f824248800b0354944142c0560303541c209104034000c0201c0071008d85c006480b4440c18040943c40741444600040c80010507100c040c0a0915100c000d800c102c2e031002c6501c2c1034519507001c110010f50301040101c2c40d11050343c1068009100c100c4c041c4100014451403507070500e400200c400650001d444040c0500c004030101c0300740b103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 49699041 1250 49697791 49697797
    0x31207060614060307050a03020304020a170c0901170705040c0203091815010e030604060b13021204020f040605030717070b0f07030e0a060f110106050301060602031c09030804080d0b0301050903 85
    0x350248902c044029010760818105483c810b4140c0d0b11100d0a20510890a4000e544003c0c4126846031050401081c503400c881c7c81440d548110200420741041d04070148400c050042e088044202180c120003817011200103004000c2d6082900c002c01c141100500c141e02d107028400c40c90340e2003441c11250100c1110180c54880c458805e421204900e041c15000640d031641e0b80c0122160190018000240460900c1e00b07d204148006008505c00002c414103071001c90308841d01d007450100859041c40158a005400b282000ea8215000c00071103107040d00299071825a8030480c0b44500ba5260903180814040c00100c0c02410b4928095558002d81d4500703020700e912070315044001c0745100d40016800c0c101655840290742042d107610100601d0407805540d1f00f038400d1280d4200d0364031940042025207081c0036290040c8444c0d0021038540d20101000c3c071420340c45900f02e1503024540007a40c004280e005ca21103070000e07001000e041e607ea429401c1003001d4111000c42a0b0035609000c1031215400d000001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 49700291 1250 49699041 49699049
    0x7140114070e010806060a0e13020a0507020103060e0c0318010207060c0c021f02100b0a080307050a0209150607020d050f0703080d0e06010b3103030905042a0503060312070606 77
    0x26075804010084019034942130b040c0c0e034094002c5802d0094588050040c18402041400140040802c1300d04c1c981d42001e985c0031020050014002017914021960580110005000016521801c92a080043c40340c1400000c1c0342d0034980320f60845034000c1231400c0d81100c80464108406100c4145180c2d0050550741800030100d01990108d09401454148681400c44000035980580750508150306020b0141401c9044c05501c50040e030360008450070100001c00301b4910550240103864500c2c0104603403040c00070181c42000340b0010084502c0d03501e02080722919641150038070001c0035641061460044542140a65841360b00c501009001201c0040c081d54043c141090192500c080c5c82e40e61100820720481113020024000203001ca0411000c0300f01000d1003d01048141c9071040c9126500c0b0040d5006134045a007400e414000d5052900030101c9450080001c040b002c0d6540b02440905c03480100342504100000c00429880d0303070709100301c00311034501c240b030203446a0300c1d81400c200a0010f885 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 49701541 1250 49700291 49700297
    0x21021c0905250915140d120f0215041209121a1005030604060b1009050307030f0609081305040f090203030a0804210518010305010806040305130f0b0d0501081209060714011407 77
    0xb90242d00c80c0b400d1401d030f454071b550001e44040480c0c0000c000769441c07c0c11041d0306055005a400b100906006903004c41e124a0041040002080e2119405440056207410650025426410150105000c240840f00c034084140e00d0500c2a036541c2444180c10401d60815070f41405280c041c007090010030b4004820780da00403903003c0b0301d48540040c02d5075620410702c900c1d038164210400c1040071400140114615030b014078004a1800201d9031400f03440e84c07101c0b5101a410301994414003043c10705106030240205080b00030004110250002543c0740502e00315141000a0000018108084071072004260403a100e802c002e052102c0202400640203030311400854240101c48407070541c40b03030180b6412100350801034003294841d40c504482c2030f80294456001e40c101c0220006c4c8081c81d40607020004c00354040d0980e01c9850b2103803140151001a0300c10401a030001040110120031803084503d4504111100c07035032603020745801d01c2540400328504e0240d5203084010788446016800b5588288040d80d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 49702791 1250 49701541 49701569
    0x204080610062309120f150a02041d04030201110d020901030e0102030c030121050703030c0201121b050702190e06030d03090503030f0721021c0905250915 68
    0x10408442140e1400c02207001c0d98819540c00c0b0f100246580181805840a401c0666445040324a2440c0c80010488980079034001140c811001c1060318045800c00d0b4420001e600d003a10b84615440c0c25480c00c0407410007450074401007010103000b5407108401d05211910329484501138181c0c01e00a40101c080940170904180100d42425010b00c08c5a2160000c440344505690800030b1a22000412450170525031403255103e074046a400c001e030f500110700c2542c0d502c800c008a0320004040c0030030040d411010b1828040a502d90b6905d102803e00840316500d402500c40d070450000031801d0f0394001c00100450005107000c5075058000c142d191062005508840b00c09171103010840440b0322003940600603404c24008101d40c15540d10400e5000003181c90044881d0051080360306001c030108414141040c0e000404100ca804401005aa011100d8004015000258035503075100d0401c004070b1100b000d002002c100d9200002c080c00030207850200d0b000c202c90210006201003241d0a8014003525520354 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 49704041 1250 49702791 49702799
    0x10507031808070807080408030f07060e010203040309050913060509060402030c03061006050318011d0d110a170f030106020f010f0b061b0f010207030504030b0c0406020a080d0f0204080610 83
    0x201c031041540c01d42c000469441e00d80c076611186010380220780211120201048009121035040014028910700b5818032680c403000c518050f01210031440180040f039005004100200f03407c803001a0444030103488860040e680c801c03030309801e624a00b400402d6646424213020960300c001030910301c07481c400d40481d04800d03401c1d07040541c0c9010450b4030910700c0d10307028402e00500348901c020315088005400c0385848100508001b5094841c61604246c0010070034880031910003041088091001b11401c4c18580c003e4998400b43d16200c1e11000940440303014504201100d070f20104a03442180700a22098480d61680002501c0302643c00c10a82e156083c8107032030216007000e00c0303250405071000f001d403440c0c540c0c140140c80b01220b10041035809801080c1c90f00300050420300080208501c6544c82c5d035039580c11842c00000d040005031200c01384080c20f00040c040703550009105241d45030812803d54441400100c0540a40000140c0d805400d00114000801040c0024428020700b120301c0005011621 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 49705291 1250 49704041 49704071
    0xd050a1805250f090b03010207080d021201090213060810081c02010507020c0901051c1226070c151107030f0e0904050c060717040f0f06030504050c0108090a060e01050703 75
    0x203603002e40e03034001840f01020040d03c001d80e80300c040c01c8140900050b0078011141c85000c1c0c545c20005104910360380009290b82c10b00c480b001154003400000c8011814407201e40c4003207030040d07520b0041e80140802000415a12460f0103020b04c01080d801e000c64451980d81c01c5107504003600c000c0c1c058095070030040410003072400850202c04005010704039072060782c641400c0003903048001c0788140200300008040c3c4045041d81c00c4482a910325a2034142240408003040c000c0881a01582d840c130302c103d4400d2020741644410000140e54000d00d001010754881d01b00300000740100c5000b0f03c0c1403030000400c1810160040c02c4c054100c4115220313170115446000a024849600b02c40080035508208889045880c00001400c281c600403114504000c44206000240d9402904030003005440d03040100222080d21280300043c4c03e46d840c06010a042c1f998640341c0e0391200740c2c0c101e414401c50000040c1807610803c6140000d0b50802070510800904858442c028141607602c2d00000381080014040091 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 49706541 1250 49705291 49705363
    0x20604090209010f0f0c11060d1b020705060301050d0807020303120a0504060f05100306020a110f010209090919120c0204090b07021c020312060301150b030108060106030608030d050a1805 82
    0x56292510b550a8082c0c6d912290400d4180d05052342c803140070b01210140611a01c25003542a421050840b0784520031a0043d1410310b0a074803440c8106800c00041c4103948915450303844050b030096006440d2106840041c0c1180a104205034070708101004024140043d0382040380101d00810080152107004901072090b2041103811113020029402c003000011407660003018015454a0000880c21f0f1003050141010035060551301350b40c4d0041013520780c6140c00c91000d508110341400400c0c0940310f0305081c51240008010240007d015212181c01880c02880102e04031a801003080040078218a0411440c030400c0d03801c18010311032842488990035071020a5010039919800131401d1125603481440100c5009001607015501e8043ca41e030726203001d01c0303554041d103081f0811546a6040150072403610700c050303000104241c1400c0302009001d0012003100c1c0303000e07007000c00031907541c1d83c01c00e103080a85501c085003201403000c8030011007440000f00d600f240a03101c07100b92100084080321829180c1c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 49707791 1250 49706541 49706567
    0x309040b120a030807030204050a14040f0209130905071503051b2106040e03120108010b0103020310030201050309070e0a2c071214070e2e0909060603020604090209010f 74
    0x750001c0c0d00140030034010505130b0b03400b10141c0b80161405485a002c41d07010302895101401e103405030301c21001146040d014820800042c031100b1810b0111002c000f9008000d9070411040d1150740d6669103050060078424038005d49808851043d04044d0004024010127044580c10142e1000107800c1804600010031504264070029104090000c000000b001c180b0b000350503194801e503650008000e0036070030f001409510032a1511030703203c0d6151200d51402c0d1510800c0450401d40b0401c00c1020786c0c0f001c0c2ca40d000540e0303028644162a6a18185032910300507e0f90050038030600480308115042c070081c0c0042c41040312004481380e05850b0715480c0b42400c3c0c41e80d405107400b600440d5050207400620031407100d06030f004500104214801a090314141840b9401c803410b03403041d05017000107844908084060a000788000980d403d582d2007040780c07400030f050040900c466110483d21040c4041504041c0c05540c008101d00e90f03440d9244035500007544521000c40c01700d041140e11038401801800c042581d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 49709041 1250 49707791 49707793
    0x72303190201050d0b0409120302070b0108060402030601091109130f0609110706110f0a05190507020306070819020f0d060509090a080706090f0c031b060504050915060703020309040b12 81
    0x12607103684280e8040c101d600c170059081940d40113081d010403d031805021001c0c800ea140141d4400f01403c0c50800b226050f04412125848002030100686001803414115048070f0400103105600c44030b600001d116180d02c15910800303000d1703c01c0444c0c00581c05074140450302002040315a80d5084144140c2d9103484903407802c10818440300020600340e40100d000c104003001c68914103100030b80300742c0e03540d009404020300040f40800c43c420440141c0c2a00c0440001c14208182881241d50000e5510b00009184c0410042c0701404100c000b901001c000d0b01c2007841380410740d00c075581d031100c550303941d0000b041d07219a0364100400062541024140c00c0e0042001d840a09824510b6403208103e41d400170008560140c0c0d5804104003185010b010030401070301c1480402450382c514209004450402401e1003078400c0c80f003400b006160b8000c41210119003050318200e1240d91901c6071041c81c0700e041c803a8250001000035009080603408002013030710f48012a400c08c500d11003101400030500301c22a1219271 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 49710291 1250 49709041 49709047
    0x12120b0603150a050306010b25050d030e010615021006060c02010c030c1a0c0310140a09050c0408030408030c01060f060504270606020f010e010b01080c0c07230319020105 75
    0x407002203802c000700501c501411840c60503560381c0200c0e15008099004254105000c1142c0b981d80040c0e40c05541000000d400002c410250f60300c550743c035811a0702e0301c1c0c03041c9955090140340702c08080d0007040040c40398800c01c400e28080720300041c4d15130160728249076040f4034048011403114011041900b01d00e4042c0c0d6144201c51041d5020f40c0c540c84919001c0d00e05540c4800079000408108590b00c5c4142041c40c00c4603201c1c00c010314004018410b50b04600f0708584002101e201c5034546000040c01c030f130b202150100b0945c46081c1000760900c41d070303000080c3c0e9000018001c1703039a61001000700300085081000300200d40d0303205c08044c21220321340117040000d001004100254030814403115421011040034044018a00f4142002c40300158400e5001d40c01c01500d080c0707407400078400d90a660b06038000a01034a064400001c209241c02031024041e40310210701c0403c02901001468094186c0e04907900703070105c08803045d50510f0701c403802051103803103010440b1301111042454420500e5040e118603003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 49711541 1250 49710291 49710301
    0x10602010c0210090b0f091903050d18020105030a0f1d010902100e0907030c020c030d0809010c03180303110c06040317060402071a06011101060b0909180d050304081612120b0603 78
    0x506d500b03000d002c4410600c540c00312298211000d0030386020140c8039468a6036a0ba00c102c41d524150380a450608107141d035078450810150341c005044941c4100594000201c044880102c100203002d6022501100310300000d808024941c1507102003d218003c44e01001ca06640103811142034429221468110318180c0100c0c000038040d0708540c003210242d00542d80b0f2075540c600440d1501904d101caa00c00141d500c001d209000b5000e2103010500c0c4014502404103d0b1902422016004868130040415070368004900060840c2c00581c3e00900c4000c003a1001ca080a060040c900e54041c04000764500d805008100503252a00c00c80303010b144e20507950810710340158926a0400700c01840b01c1d05014030b84200040c9200c0a100343c0000e0490034000a84881007034040c40041800180f4220031a2858041509080b030f000807001c150010074070303100b03a40780d0351854160003e01807030000e40080b001400800b020041e02d5031b458070800503903645490b101004004400233881402085641044040000c11 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 49712791 1250 49711541 49711561
    0xc0f1e06050d0f14190501050109060c020603090304030f06091101030b03100e0304050604090e16060c08070201090312030203161b0b101d090c030706091e0302040203010602010c0210090b 82
    0x1042d682c20f8400040c9200c0c0200d600700ca0007411079a8181500c40554491140001c0303100e00c1c0d000d42000e1078414512800c000d4081d01c2402d2114010b8852000480000c01031a410012a0045c580c003c1a400b0400d01c43c0c94040c0140c4401c0d4030031904485401c400f1190355200f4071400311620030040091050080003881f003c0280301c07010401155005c1004080303080e4403080700070b00041400781c0c1c0c0011104040400c1301e0400d25203032403107031403051100400c2204644c4103403500001500041c3c4c042e84d50380d10f440103231403404440d800208451b4404040000075609940035510500d8101b585050501556004540d14500090800399907420010110041355091017065442150000700320601512000b03044100018a80c2c000b0114070b9030401c00840e502c0604c00914030b140b096000344000d6040c43d0018003410b950340144140e5040441000e800c10320442c010300011b40d0040c000b1540d07941c64000081c082d1a01c08400c1c400f502c60089030441600941c0f04840c0c0b02504400703408455290b0320881 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 49714041 1250 49712791 49712801
    0xa080406020702040b091008010e0c090106120f0908030106030c0804020604060c02040b0405160906020304030c050105030402010c02040c080612061b0f0d0c05030f0a15050411070c0f1e06050d 84
    0x2c3c4c0c3c000e551401c180c0c2a58558207020350007070555003000c04042c1e1510009600395411a00e800c140d07a00010340281d4240c503442d00a9055985508100d11154886d1074440700900d0480180b0140c0c43c1898441700600080000660580d1002d0307a082c00421142c2c1e03420b986203001550029000071080104010f4588500c84000030188020001b00d80d1003080e0340098103454081d01c1045452100c005050844c03500172030b154009014078009541858076544640c00d841e41e90348516418010f0000001c2c04581c8905c1c6100c02c02540100308001e0713420724082c0142802c004a036014050b80d1030701c90039143c034640056100d1141e0a040102140004414030660a5400c02d04591940c000706004ca03424005071400781e20000091540c9032900d0b03140058400000b154064092144545070444da52112000041408281d410907240882ca00b01003c15200340307846251005015440d500704041125030501031030b00c1c12181c0542038000400c2c8480008480100382e4410200071640030480f0b21142d000d1034220b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 49715291 1250 49714041 49714043
    0xa03020405040603050c040b030d0503131401020a0e01030b120c0d03050403050703082101030b0610020733020106050102060703180b130302060108010b03120715110403030908030a0804060207 84
    0x5400c0c40d5480d0049000da6503650001c880c2a0040301c1000b406082c144100c442013007080300201540c0300030707100c050654840944120381846d401c41110080c070101181e50710703900103040001c5644071050500144440c0080004074002810010209000c4c54030004403070a0f00c0110307000d00841102401040782500000004400784101844000041403042c0103d100541c01121041d80c1c4101144280c0e100c04040358640000e101d0b8140140040307404407040c2607000c0070a840c00284160740410a03490051150700c030036800010b140d128400e4100c440300403001146415480744035000d05010a074203a4100d401502c1c0141c1c0075030300042a8070f100341c201142c0b1403022a15900800c2645e142c4c0404040116150303000046035010020416030b0401c11580100ba044d0005c00220009c0c8000035140d44c10703881202130424000c54000b00303221082d1511180c0d65480f103810030440f4004000f51807160050310042e004580404000650340ca00070048400381189035445103481c2e40c440d0380728030080d000550 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 49716541 1250 49715291 49715297
    0x150304020108060a061205100f030b041208040b0705180603072f030306100c060f091407060f0c03020309030109050c1005030c0a03020a1206090506130221040203120f120f060a03080a 80
    0x700027048441150104080d40c090b403039206461506042408490107862441010800c1c00e0b41007101103102116055040302c540d00d04239645948071714501c0c1030040301a041c282d100e0b10000c02e000c02c594001c111303040008080e04154075035505608446882c2c071640390307520801d034108000007400341c6400c449644081d00e29080010903245d031a150a000c8501c0e49d1400e00500350340d010310100384464410140881641c6000030061142000c40003441c45072204458418061081a500c08050003881901c9503070401a00070030584245081081e510001d048040340500030000891410754800e10459200c1e0004000b402d16000f40200210000c0d400480d4000030840c2c031481410a50742c1c0ca000703a000070500da010200c0c26041039000c00c40c1c0240b40354100010544100b00080070101e00c89424503070300c154020752260b80d540b5800824103040d00300340428045c510000b141080e0b145804081c12010100704055807a6036144030130200c2403201925050790000c4005010000201000010002580c07946 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 49717791 1250 49716541 49716571
    0xd030903080a02070906080c010207030308060402210402010311070c06080a0905010c110c04020a0e090c04240801120213091401180506150d0b04080702150304020108060a061205 78
    0x81c68074003041c1c100742d00b80801078102c03540801c10501c042c00f80303801410442c80174089820741440084d40d14001032000405005036000064410341c4c496040d1400c1c4541c00c96010b260600c40905c162401c0400c5404a01091600c42c1624085801100ba00e000c198004400f144450815400343d6140c50010304000b40685c540d104100050002c3c0540354224032252902180d0344e0300c00f14410f003490000c102c0580100e205020080f074041d03101c500040340e11000d840040d0592203402044042d0320454014900e403d04503030680e05482c04031500d14000750500d0380e4504169807074682580368030081420280d40301e002001b21807801419603002809032449507041d142041c480e041100d081d030310100c54041c0820b841511000c14000301307001c03079544038806001c051a207015860004040510104000d0950001000007d040107000400c84480940040c080b00740001850392040711a80115803c9001480a0002c2105424180201c1c810307100caa8440c0c030000094240c0c0440104001880d216000c0000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 49719041 1250 49717791 49717793
    0x50907051c020a0c0c09230402060f070b0403090b0702090a0203090a02120c090121080c120d050117010504080d020a0c0c0605030403020714060706090302010b0429010203090f0d030903 81
    0x244010800803e843e201d07500354500b0340c02d1000800106500402d1118140010508500610240d4200079554500380e60044e0f1a1030000c11403070300507440360920303031000051600d0900c10410b080600c56480395484040301c640b070301d040302041c2c040c0c100003c0d00480e075a00402d42c1c4111030b4028582c0084120100c82d240c400640004d85d801e989844074a030f207504000b000301c965042000495016040080d0840350b42d04242c9800c10b10030f105040003402860011074801d901350010b20045200f0000340c821141c80f03440c040d22180080ca428401c42d540b031502c04d084524071100600803e4070498006a90074141144401404040e5014085c4801003229082003280059259020400542511790f5900c0d281d04d81458040c0c5032003c990011228503010b6010184c1590f1100c0499007800e6201c2c80100c1c00810602d41a40584501c4008960242c10f00d11000d01c5103c10f110b82070342d885000010076814100c1000166164452840301d290465001c502c0f00d92107041c00042032101030b120740b0b0802102596 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 49720291 1250 49719041 49719097
    0x20c121c09080d0c030e0d02010e0606060a090f0905061c050604030e030307020d080d05060d051015081009051908070206090a03080a03060807060509180601090f0b030a0c030605090705 81
    0x1c1c00b90b04c100400e98038440342400c000100103005807104603000070040ca001102446640751703801840688254000035103044090711078075400303005000d5445000c9845440d01a1480500011180320b405031fa181c000d80c1840c164131300f40c0719080035001006802507880e035840131501401c1c01280076405110030401c010050319200c1c808030109015680e126103d003035204214056880141607280300e90501084180490380204036040010b90041c00000c020007010303111002c0036241c3d44010150300500d142038400708401c4d046801d0751849a0150741d0300b00c09031441254018440324014111034028884c0500600b0140c00500c42e050005003070b544043d0f50b030f07030303650356503600c045d0301800000e03125a401c11180070308000c142d01810180c117026090200d03040114110100c02c0c420949a03514810100d40c0b40c0e400307650288050249800705c48501a21140742c508590700980700150b21074540300401035000d00c6440b80c041510401001791129840380641107515400c100114201810350041805999074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 49721541 1250 49720291 49720301
    0x507050c10060e0c1e0c0c2806081303050c010b061b060601020a1a041a0c040e060915010f02010f0f05150d02010210111b01020c121c09080d 62
    0x30341c1c01c2001ca480341c10070150091200004d003001c00848010b0207501000b0031741e07500401007002809043c4d5140c40c04100703443d01d0500610f002541284038441c02d185032070012066401100e4226130128905076540500725050501229210ba070300e0f1030481542d00027445403009099154100300049102618000002c1d482d81c095a00517411a0800001c2e1103503150034001c096000c03900f4005031046a2180d11043c002c01d4281404c0044c83c1c1d9044001010008644041003980f54000d0a504d0306151603580030200e580a4000e5240d044e40100000e1480e292420803284100009040411841c0b100e200658001d02e00d80b61280035952a003690900d048040d200d0000c20a42101c1c010035039081800d0038189240441f000c1a00a003000800040541d8001511508000c110f1038001084010044644100d0045213425050000354129040441034150060688140480305640c901e00105020560611400c9003030994034000004d40740700c00d1420360103006030600407441075180c801e88441e5941154 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 49722791 1250 49721541 49721563
    0x105091201051018050103030516150903020105090f0c030703023304090c0804170a170903040504060e0124050405040905010c0e0f0901120204090203060a0e060f010b0a030507050c 79
    0x200c007000c008520f81c0541300103104880c8201088994111740703004000e44120060b100d602d0011002140c00c000b5070b80c4510102d00c0e82d0b800100400c01d1a86002406000e0503103660001d44140a442c00090f14086040d0b2032414004004151062543e402c0c41340d00d0b5026440c801e2004442140e42c411810408145080c520742c0d50401d03561141001446400c45011442c1030b005c1081c0c920401000801f10f00c0d9800d20381e44803858240c0c6504100d0400c81d40d44070b800c070406010b0380d00318080c8805020008081e000f030301c0f4111828088180c6403440120f109000340f2802901d2000c5c4402010240982d642c2c8940b00250381c58514a41a114804541900d428100849040e95180048070003503a0140c84002060b00c11542d1050009501c40001d44401060007410301c180c0c0b0441307414085682d20352051801c00e501078159641d61074410018401452007202c40c01c6540070340300009a9034a03441c0c3c0042c0c140e07224020540d05029440504a0003040020251303c20f00204100e00b00c40001d0400282c243d034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 49724041 1250 49722791 49722811
    0x20f031f0e210a080f2403010b0a0b04030c0608040302030a180312080f070201050601020d11010207020405040804030302070501020d050417100e030405031b0303030105010f0306090203040c0305060601090311010509120105 97
    0x801150344002d200340780c000c04440c41700940794144003130041040114401040c1c0d032090044860000c03030010740148007010180e58803400c503040002d8880c03400409001104c0c02115101c2c11343c0e50b504000e89502c40c04613001001a0400c2000f1105513000340d2a518075500d215800c800440e4403581c1e80007160703204029a20105070320703d0820000384034802c2c0c1c0d03a9002407503200038401d50600c0c0c0f001075566481180c690041c413605804414030094254181d4058070b800400900c8103040c64240040d05a00501080e0018054854086059400002ca504e1002000c1e60b60b1460325107041070417513042929000c20b15680c09171700ca075110401d196008100c03228000c000510b588034a000704140c500100c20720302c003255948000c07800c0d041d41e401105481c1141c1080c04c000d094080c2c801c1d0201e0003001c080c0c2000c04014408014401480000c004d080184c03403090045880903100c1c9401034860f101984802007100e5503420003010203501c101c0280404040c003504c0594050300036940b080c00c0d2002110b00c246c41d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 49725291 1250 49724041 49724047
    0x120c0304060c0207030b18010b030313181104050d02030118030e010e0f03030301060f021e0604020f0d020306010b0a020f030316020c0a0b092713020f031f0e21 70
    0x80c0705240c4202c288480983c0020906245142e03250509480b00828003a48000c0da5100d07542140c500b90041410004000d094070b80e40d0015800001080743d0302e004421490f00118401e003402103007841210803540c0d0603501c59051610301000c0050342c1010032012a003554940300c0c012543d02a0464441c145403003a05c40303418200b010340004000f00748076030056116018415111b0031a44001c021281580c1c0149001000c81c039000005a240080d103e43d002e401c5078400c1e5901c1d450f5440403600303901991080340c84ad8441403e120400c0760400070040007030341c95044400100011418400281801c41e01401500c908081480d4054259081103500036628112100c402e030660b41d0500c0b006000f541308680000102d411b25103800100e003e42c0404a003e980040c03a9201c0c2003ea00c17510700c551440c03040e0140e1171480c0101001c1454100410304a000d025120100c1e190f51074045040b50b00603140d0345030301c40c5500c5034007400805009070030480c024601a00c184401400c4031400243c3c90324070000207640d6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 49726541 1250 49725291 49725293
    0x613090b060403030c020f180403050307031103010506182202070501050901050907030f02310608340e09030c1b1c02030709050112060e010b01140f120c0304 69
    0x240d40c0d90400c0140726441c1000144002608404a181c00c250140c1d4010020103d2101141c10162000398031240000c0c90420041010390040085100b0b40040e90300f484000d04600c240c0741280000e024090f0700c02d005100145100c0045505440d00d07500c014818000c905225500546030215030300c042540d20703000960070f824010240a1103807c001e0410007046181307006a5100c0d2245561b000c0140b6007140401100159504d0103101000e1804204c041500d03519404035482c07800c01c4070452214003504082b00003c0303c200100e0794206485001d0f0f5880400d10f030070310f805442c1c201d03000d8440340c03000781c2c585005c40c221503900541c40c4a040034000450703546c100780c050716207407001a500d10130400d50102c810340019111030680300a184001d003e40140d560300d502c00242040500c0d04154841454000000fa02c1a11814112110750203400c0403c49014051001c0f8240d480ca42c2c00f840c041000420f24044040c08440181112401025200e0070030f8111401e0080382070f000d0f00d00d11011940401400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 49727791 1250 49726541 49726559
    0x3110d0209031218120c090f060108060d020907051b030c030307140c0705040504050a02030a0c0512070803040b070c030b0708010504051602070905100306050915011706010b09010c020613 82
    0x120140160f4051941450440310503100e06000750600760340100f40c90001008221030400217030640c080f00030070901303075841d12030808261100700325655070001e0300c4131000c9503082c00c0c440710504030030b40c02402c075010a6841250070340d250b034804210001008a03c14014220070018005041c1c01c581003400787d036907070038401002040300303004254402c3c07003000420503c016020300049440c00c44006031804030701550360f410468203000c1d160102a40601079250740780100886555028140c40b42110200500c40b005180e403503030340d009400381183c1540108014481c00182c40058002e40e8820308200350580c1d220b82d20449490001e07164540440e0404006102d0b9150a00070f03a9408195040f20158203030070110000c0d40e0381203500c42c0d10500f940e100041020f80300c4214800002e50342140c0180450300380341a582c0d0b6503c00c404044603020030b0002c00450b24081015800d102460000c4c001c099690134004154516800743d900c980c184214100958016100d02003c0c1c0342c0b10108100c41300d4103030720f424001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 49729041 1250 49727791 49727803
    0x616110f190e0702061014060d05091f020a021b061e0406080c18190b07050a02040f0605030604140703150515030f030d09020d06020403230105010b071203110d020903 73
    0xf60081d500400100711046221416200446000c41c0c800b0760000d114001062203842088040d68100b030a10040040200c000038010010600c00005030000110700e000700012801031149540058000395005040a404001646040540144110f2070010185030b00c0401c201400f101a85281c4041820840e2a400c6140b15900100f25210a0300d0014944071107081d40c129103d08a209000c402e89811141d480d6a040c500540308400c0d8440d85d41f0940d050055450b5000c51049108604000c00d000d0710100500802085a0001e0010f088584955841e0b03660350100c9400703d21030744290f00d40040400d01010041442562440d00011141059440010f080c054040094000c1d4803607200301162143c0041103444000e0004000100090544005807800c10b103201d015010307030700100f00801442131101c40c841c880002102012100b101194803d400d0700c000b48908081001c0c140074074000305828507842640ca80301854002400e80c1400b448564a40051040b0342142d075010030340e0081c0741810848 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 49730291 1250 49729041 49729051
    0x6030f160f15090303050a020c030f0102040503010f1a010507030512010621110a0f03060302060c010507080a0504020102061b0d050906010503210d020f04090501060513050616110f190e 81
    0x5240811500010280030380e02c0038130008041000019080d00481d10034041c0c685448401801c1d64400311228550a01030342080c010b41c0e00c01d52078250302034055052482440122040c882c5107020700f410714001540c240d0060f0209405006d4100232100a048518042a020300000d845400142c20302e280c4070b00c1201110800741018600c0c095844421021041c1940c00b0240c0310324102480205098003200502002d50000303400000202d0010f00080040d000280b146250380c2d1511800e58500c1300003402c3c0c3c0c006480c06030158100c1c40c0030600c40c8000d15200c441c06c8849000040c40d01d071001c1922801c6400460724511660400c00040c025880d041c802d0114441501c8038a102000d086001d002081c030070503841407001c03580012002c01d51420304080d1001032074101010001ba40c1c0d00c0c017029213507a101484000c0340c20810701c0c010515181c0f100a8846510740c0d0011860142d00903501d0942c1d440c0140c000c160b00511510740103129545001d10303050320310381060082901528080440314005400f0305 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 49731541 1250 49730291 49730309
    0x11010207090204150807032f04050a08070603051e190207020d1214130b0306011e0201020702010e060a020a02010c140a050c09100302130207080405060708190f0c02060306030f160f 79
    0xc011096800440019281c801411b502301031010a441000e11552084c5e03401140c025604180000d17402d0404200001110030342d842c20300541d56248040a0b041b00c44040c910440e1880c040410662041e2500c8002043c0b81007400601d80b05841d0000740c640d1200741030842d011040c0b11a00e0b50503907802420001e0107081c1441d01e078203140140c4d0051201062034098144000c1010000441310380c421080340098440e11945040001084400207010394848041a1b01249001003805024100360b0120f903458000c03039000c3d000c42034155004454a00b20b200c02542c4292075a6052040740000703021000d20148104010b0003510042c0c01400140f1100814000c0030714410315003040940c86845110003586d18140c80180d54150514050710b40c0d00071b9401040d00540c01042d02010414000c00070803800c061004083e14141c0c42c28403c440c0d40b41c84510701d800140047d0060ba0060810740d000d1504014010151040b0502c2045081d16081c0d05c03500300142e810f803a480401c90089040704c2c0c0c0000e04940c031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 49732791 1250 49731541 49731551
    0xc0d05030c0a270305150105010507120309030207030b011e12020603070c080705010c05040602060f0115030e03040513020909011a1902010e0a0501061706090a1101020709020415080703 81
    0x8540706090191940e44001d21454003182c403481c09003512044480038029281c1102c840c2c8a041140da1140c28100d00060704118000105896014500360f03041207900c050310680170704107003034101d01038010b0800840c2035104404000c40051154807450f4080c01d4142c0c4103141003c4059900c2d1194003440e031020034007091117007a20300540c0b40c5d002101c0d403100302ca040c041700c3c8080c00e10305801c0a01c41c00d40094055442c1c9000c401086030310000034130443d0220390899500d6110310600300b08240c000c0c441c480d10802c1c49445461598000d40200001b020800c080d80e0515943d1404a501403e070031440a0501c0c2c0d000a200740245405072010f0302401610b140032908140b05a00408240708030000c4060250ba10407038a0880f600c01d400140c600292801900d11810140c0303481800790004c2e008480b140c14001203000e808100000310503200f01c01880c000d00c2c50001c07640301d520041c031804244904500440c000402c2c040c5a900052000300201d41081d0082e4070400801412100b000d01401e08043c240 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 49734041 1250 49732791 49732801
    0x60e1b0604050d03050a090e04050604140606180a02040b04090506150a020615040914010506040e0d090506030702070e070c0b13080706110c1207050c090106050f030a0906110c0d0503 80
    0x4800c85460300c0d94507045c29903650010725815241410310b0f1788100818075415007004104000405d80c94001c521078003829100c06d03c03401c0078980303880c1c3c03c03a03111350080744c0e800f16920b100e403c070503140741c020040c1c0e18014030300390b00c502c001c9282d5400b6410510301981c465083c060b040c2000007108019141c01449241004110f81d0002c2d12400007900c901240c02d0070003d4a501655164444085603601440c8107080201c403d000d240a05400c8a41610580c03424000c5c424042020444440c1c10140d5038981c62250b040400b0082940c0010340210b0841c490594045905080c40403901d00810700c6450300300d615695490f01070001d010003045248074070345d50300101d4002013448044d00d45c4154824070201e0340300400c03000c490304d0340540c000110851103414041c4603052000f5004180d800d000354240d40e030303005091040c4912a08284507940008408020b2030302c1e1400098080d6070803040044020a50401903107a4805075078001d15841c80f50f41d4001440100d41d00108a68240070b80e0310705180c3c3c258642 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 49735291 1250 49734041 49734049
    0x503030a02060c0c030f030103030e040e010501050109091e090804090c0f0813060f0203070c060b090c03040209130210030204060e010201050118020a020c1305091b0604030618060e1b060405 83
    0x10140ca900614080810f2600c60300744240159144002031100c5547c0f20b45c0d4070b04004201228071402140103520384040549c80c0300040c0a06c605940041c1c50f01d80d48a0f240802d0750004100d0b0354070f20700350340400d000d4500c04440c250244c00b010783c1c050282070b9201c9061400708000c0365070340d407645402d01020102064440d60001e1110b030303005141d8032117441c1440341810302c04e018069215030000500d10000402ca099a00031061140c0d443c0903090030001c408140e014019048026600c3c0855401e0a00004006191001c0d256074801105c4102000046d0143c0c0444c407055006c44109011a40109050003d55841500c01021500c240300070720055150030030356112048048081d40000d0740005101041a0003040b242070110300107403942c0c4c400311040e002d8000034007003074480c07440a004288060340340c40c00404000e94610001003145103480e20b180e03030314401028035008401600004c0a0b102000c144988101401001102c01601076400c01c80341d0100821500c40314644128014402842651a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 49736541 1250 49735291 49735303
    0x110604020f06030403020a0b09030a0e1503060607020a030501020d0203040b0a090f02040e01020f030901020706060503070e27240106090b0409051f090605010e0a150e01110d0206010f0503030a02 85
    0x400342c4020b9602d803030b40d0900302e091088800002e0301d80e4140909008801c080000104400300d12951000502800c4a003040302e00050f0b002084000202071010900c28a008801005d04a200500700c8180c01d980e50389250076a0091603840e41d8895000c420042800550000e0a522101164040000090940c2d915030419641c00020740241e9441407511094a0250b040b80d8185c1c6040402c9a200d00e010301b4024040c2d40000c81c00c451403400c002c800203c1e420000786d42400c0d82d107000000f45680e602c1d6210070090020350f441c1c0c15402c9120b20900c504110040c00703201a0b440841c0407803404c05417256441804d060060b4802010021040420402c0e4110141590140ca400507008980b42d19880c90703605030505040c19203000b019189000040c694441d520000031210282c9552b48102034001c1040020284c40c803c000f129030120f071100d11001d110304040900c850b41410403400303081529010a01e800c010500e20710159010100522041c00c1284201005040c1140150b20700400d4003c000d440324 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 49737791 1250 49736541 49736569
    0x30f0b010c1104060f12020a090b0607121209060213080c0310090501060302150c0601050402040f0303051c0501090c08010902070f0f1a0411090703060302030c0d03110d0c0311060402 80
    0x440071500d014995959604010000c201c045c0d9503d00f5541c1700c0700d169004162000003248151034000f40003031200e00301d009020382c1c110020404c60920b04281c480b0218024401101e004000d002002010116100d101e05800f580c090140141c40c0d0304007650f80802180c1c2a0810242c07584000e424070f41a41c0c00285515258200e240302083c803001c140740c00d5002d0071a94200a42c8940c24100303c0358031503406000707041141c100404460050b607a56050100f00d00c100e0146503030b1017480441c1400424010380c0200600003003c10140000c02280e1251030407160280c00400c0c07500d4580c0d880c4078000c0e83c03080e05107014249090045162030201e0b501c14510318030805004040f0614103031181d0078000c1c419030103404461505000051403603d403420b413809245101102e40300b4041e56010407a503038400d00c01e0344e090b00e40c090028640e150002d0100314641400240460800c0254030b07074510f2015083c0300440120049844c2c1c40708900c1c042c40d0241c50800082003c10959104004010244c0d44600001c1058 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 49739041 1250 49737791 49737803
    0x8011a0d1119020601090b010507142506030c03020301050f0409051c020c0a080a0201080106031113120618081e160525180e070810050601030f0b010c 66
    0xe500055900c502618291080d1521400045125080b4a1103100b2440c1c1416a43e400e5445903a03d03a02d504048400d03140319117002840501c9000001401d000c4101c0130f0286e6074045519944022074428011810b45d813208000c0032040f4001c04c2001c1d054003e0a1220b1110304040d4110360405000c40d0407415071041ea28482c54075840303101c00303000050010720104a00300421141201400c2c2010750380c0c3c1c00c0741d8613103801012081c13000204e8280205800d00416030595030101c259183c5a03084001d005070f40014030344aa01003007107680346084103030740c60b008113100a00b0b614800c1c3e160412804887d05c1d8171080402098820300300c8000b66090045540e00c0051042e000b401040781c104d800c0c180c0c025100f8003035178045820720ba102032100004110202e40c4c516042101700000d01c045105650b80a4800d4944280d180c0c07001310710ba0011a0424070310f0f141030384101d503451591041c1d218174003100c10942000042da04c1b014000c0a507454018450111000401880110b2241c00001d0190b03110a1015000f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 49740291 1250 49739041 49739047
    0x603020903100b0105090a0e041b03020f040c020c1903060e031914130306141503030703031a030304180b1503040219080f240103051507020a06061202040b0108011a 72
    0x1131303014009071424284081c0000c1001600e42441c219039400550b400d8030001815422040c81c0001d02c0c0070b90060f0b80c1c0c0035209400f50064482400064207455001c0b10940c020070005040ca0f8135641c01e021700035030f10381e10300d001c200b0714605103042243c2c1416440400e60b002004580e9401c5030795011850590880e20f04405c0802d03000c0e040d007009000b4154a04088200e05c6400024040350350402d030201c0c000304500a000740c581c81c1e0741000a10f4030040668060b0002c0c401000880d00980c000c0340b50005821740d5001560321280003c0c21607110380c107c1004284422410031501c61a48102030714100c0c15278245070700c922864614800c5d40001440213120740c1c2c80d01d60401c00782088414000040c0580000c548081c0c80304025981c0383d8120f00d07602045110303a41250b03000d441c0211450707412243c1110241189060340b0f41c811515010043c5144e00398850080d034031001481600c00e20f0300420249069200c03108062041000391040f0360000c90401445c40c00502103003031041040410007000c09200340e5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 49741541 1250 49740291 49740311
    0x9080f150403090e01150806011701090905010f0c020a0b01060207030b0a020306030a06060e090c0f0f040207080705070801140609040506060909011d01050f0c0a0509090a0603050a0f0c060302090310 87
    0x14041c3c1c1c41c0d04403030312500341c01c0c000054541d00e031072000e852020030b84c507074405956a04004595950600784044441e4544400401850a035a44000c0c916401003002003800c1107101411015503451101410060b84007208120070721440e0340300e0b54094807581c0b01402030b151458440c11503200c00a05543c6082da13001000c07400700e507010048844016400041840503560703480041c000a801224109154000c004a15010345000150382d103151314001c0c2004603005140d0113100082d008441e0440b8200010080352000c01c3c420000d80d03000704044000490004107601c4803044555010b04094001d0011509200000d800492065400041035405221a940303030107155001d4001c2269a10b0107003001d00313000da071017103042d00841d1050ba0501c080040a844c1e502404025200d0030385d85100080041c002c1c42c07214500003541640045c3d190070040745141e00c03038652b6070405a144c01d044a5042c0e450210070200305401c00703184010110341c1011030a1800e500c2c0403a442c0c40300648003100c401e580b01d000340 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 49742791 1250 49741541 49741547
    0x306010c0f0c0f06020309030714150705060603010b10080a1e09030809010e03070305120402190b0306010305060f0a05010c02061201060c0606050312040501030f0b031c09080f150403 80
    0x418068211000d052801c103242449000315070140101d6001490b0302c00041100c0e400001200c07a03081002c0c0c001d1007480e142000c0c158586042100180e48a0394044e00c210b20f08410b840980b0352103010303c002e0040c03030801c401054219828039100c24091140f59451083c05234005040940c054105800807034144076510b030458500700020301c45034109183c20090818558085200c51043c2a941c00030000c01c65400322080da81c2c0629a00100014810000d44051000894005070020f102030000300c00c41310000e00641c1041240c0c1c0219021940c0031042201035a418021180c00c0101983c2114505180c500400d030181c1090180e107041c41544000c1c1c3e021910b03148101d170f5491603000c0807400e195031205002402d86c015014241d84060809501007130720714010980415600c07000400d030707141c94076000042d0702034141800c01c1c903c01c6650741c02c030524686040c0170f1030820000c01c03403000e07640c2ca2034114042c0040313480e034008407107030303845410040d4261200107404500f020365180368000503551440d0403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 49744041 1250 49742791 49742807
    0xe0d390f02040c0c051509120a0c0204020703080402041a0604050127030506090d0801080c150d1b030612020603010308091f0c0c08010e1b0d0b0c070611160206030601 73
    0x80d00585011260900d6076405020100c040380300b1070035034000b1071514840055400e010f6804007c15008100342c516001c0000d401000344030044d00700040c07a4a426000281284c00080d4181c0c0810f0100e42004110310345403144000b1140a540f1030003090880c1c0011440500503801072a062100075014110306a5103404218050040d280442e1043ca803a0b04d0310a44842d000e640203811881070051100307040703000360300c094182c504001c01404030800d65004c00001ca030303c090f08420426020010b00d48807ca99002d4059000e10030245481d03041d2521400170200d911070740c01030b1140e0446920100041c0d881d035040b01d04407030f04004465200c044040014501221648113040c10b20102c0483c031503401d07007001c132840c82036015094000c0c80a03994a96a82038400c1c500001829800603840e0856582601c2c81e00030801202a180214811413030b520340c810640d0640e4001c1400c8408507507a0f0401c0064003c404041414806540c18500c100724100000002e115009100d03c1e03000c40050f14507407050b44a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 49745291 1250 49744041 49744043
    0x20901030b13020702030106050102120313030509040e060105011d181b07050c01020c010905180a1523030c0108010911090603070507150e07030602030a0204090e0d390f 74
    0x200c16000ba41d25010025880104224040c0d4241400082c00d50b0002c10417030825a00482100c1c907540c3e91f03100c0c00c540540544000c41c01c1c800d0078804c0800c02e445071f01c12040d084082c2001030406504081c00035021040f6a818110103010681c200324558807054a081969600c3d920340c0191629813070000710030326407200d0f0b0f01c400d20b40e00403d041007072020006420508001c2a02995080040d100044803622070901880707800154131030602c1000c03028060b8655004016100001744019940d404003010302480c0e1100b81a00c1c0c02121101d43e5429405454083d03200481c0100034040c0080006050701c88141305d02d0305002d6498800441e447c840740110f40340e0220040400e43e69181a070b82c064032503044142c0541345004508a5441050380b82d20030550b0082501d001807a1181c40d40e0380b104007951009084000c815020320000600d01c10b1400385120b00c413036000c0a031441c590700c00002000031105039040c010031405042c101c1d800b00100322084408100c140d030408036015285c10007041c03c80c10294 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 49746541 1250 49745291 49745299
    0x705030309180a0204090c0504090605010926010f0c030c0905030102040e011208040302090406060608090607050405040c020304120804030201020607031503080d0b030d03020316020304031109070c14030a140a12020901030b 97
    0x2280511158004014025280003401c201305032f6454900441d030340030040c040d80e203101847c1038507040060040d41d00d840c007900d00381d800840c8141c1e4a20a4405968051600300c0100742c941805500c0d0b96000030b03a0078050081a0000c60502c0c0c94000302c8111024103102e0241440c04141c400001d0120f02002c9401a6402800070b803210709291034103400074989403042e100000e945902058103204c1c0854420b000f00403540e511800d0504110070080201130488501c8154402000700003054407410250b42800390103540010307143d620354000a41001d4009000200301480c0440f900c034074880203a46601603a0300444448c1c3c46000050000d0000c1c1152a10719915100301800c14420300e41c942c00441c45051254403210032401c2d140303026a928007980c04014480e056801040b00c1505003520441d501050614144001254036100c81040d80001080051140c0001841c10000c85d000000340b0340b400714003a0540d282c0400400001d080038402d601066800e500061494201d81c4250031441001d00300070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 49747791 1250 49746541 49746551
    0x80406080604060605070201021209040603020a0312020105130b011404111308070f0302130e0a0b090609010c0806010e120f0316060506010302030f01180207080307020f0705030309180a020409 84
    0x40058000030045800c984141d00340ba0022030f01611400c140c6103103581c1a0010014070300980740144268100b4040743c0c3c0c009035104c04c0000542c0d1242d54074401180150380d0910203000c2e16800900f9610001c0041c041da1074102144030003d40c1c00700e0128116444600701ca41c00c12004070000340500322a441600c208100480e050620940d43c003212421213252000301e0346491b540b146a00e580500d54400603612600c0303418991401c0c20360f03400c1403008000c02016582001c11070764840301104029104900b02c0d0384080308110950000348209901c0388910308002c17005140280008002400310038440307004500e40014030300c24640c104000300003076400c0016070b511140340440c0c450103c1d40c03000042d50b1107070800d0003185065000380708590244180d042c01d107642e41e090070300c407400003000d02c881300088030341c00c0003404040b59040300070f14060021580500032400d520300065143c001240c119900c01e40080010318005e40c2c0301e030504080a240214440c101c1da40f5642e481000740200c3c0e1103011250f0030a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 49749041 1250 49747791 49747799
    0xe01030f0606110709050717060d0204060f0306050a0203010e060d0f0b070507170a1407110603040305090316080309011107030b01080102070b0108120d270b150405040c140d0804 78
    0x41c401c0843c0300ba81d000316516142d40c1d040d0541583c0040e1028000302e5201c80c144204994036038069644020042d100040c0c900269011404807007403a44000310440e0301030824010020301c0d0107100e03042000500198119410304986040b500380140c0500c0c42042e00c07001000800100702c0c081c04180f608100e0501d040c1c61700c184007500d59400840101c1d18002400940c045020910b816030b200d0f2060741e52001c420305c1e9a441e02c2c10980e404404281c81c041405070307d8160035640c00000310303ca14070a640e4103032070310012401d00d494a4040300c03c640c2c140f50f07658010f0001c844000242e40c4060002d2a0005544126045250900c12590000382c00389135188004200010150002c04186125900c041d2a03a039072804841d031240160521050400b0702000000340c1c000e07561300002e41042d015020041141c048151f2180004444102101c510911900b00000f00c500c3c500003484c0004103a60030700581c6803035a17980e460030302c1030b016072859545034607200f8a1a03214a00d0842407079034002e100507501d50311 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 49750291 1250 49749041 49749047
    0xe0d0801080c030604120e0a081204030204060803160818040504050a02030d080c0301030b25090303020d030b0f04050a06050904110301050c07050d0f02011b030212010b04150e01030f0606 82
    0xd015100c0301e8421180c000030941400280c03a44100d80142d0b034200c0c40504003100319000c0c20220340941d8090b03070074903010640c4002070200c030025640c1103251a030f0f41c514520510065038544e90240c14103420a01c040c4c6500c5006601c100855607121040d60f07560182018a404046d2046079103941151411b01004100500081c1c0ea9104600031070840d030000440364412950190125154104c1c2001440100001003224258541101000c4c88500d604a541003101410480c0090b8401c0085d5a000042003419018005034203816064507041c0b002c8824980031501060324510b410340074555480000b0a121080d52000c005464020074210083c1401c2c1490402d418000c0c0c0280e20a501e0b000210f800da0f04013030203e61f00607500074090040150340020584400c4101d2942c1404e6548030b02424022408000710703407c803071045071001611a002c6040040c54084160000c41b13040004000910031514403180c520402a00d9150004541020000480c0074003000d1448121141c1490f00118249030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 49751541 1250 49750291 49750307
    0xe0118060804060b0d031202090a050907021e0f0307030c020a0e070c0606080c0f060315030f07030c050907020309090426030117011a040911120601050910050a0b09040e0d 75
    0x2000d500140411010b04080103c0038940740c00c0200440c0d05070307d800d4029950368000e000a040300410426002c0d5548010403074203003080703d4500040c1c00508004012041008108041403400c10007884009540114142e0303034424a02e014050207500b0f1402e400f15a5616201c0028140042c042d00540c144503001400325080100b0898055040000101300fa0038002000e6110090003082483c2074000b00091068660014100f8080240c1c4c039084000f40d51010020038041410310f90040415078a14205100007200e1908410306c0380310514144940c4030390000507241459030413148000151a00c0c5450f90014503c014000c002c0745d0fa01e140f81b42c0c10140800507504807080d0b02c24103c0c110046504003400c07500c00030740912003505040942511801c141d130140c0701e81841880d0b98405d03000d00000243e00049804280b5026a00410040c01a41404254070350444405020129a02c2c200b00c000307140000305004d000c803803c00c0071030b40d40c01c0e40d81c413500030102d00c20758a001c0d00d001c0c0351260801403c00b2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 49752791 1250 49751541 49751543
    0x30c060e060c010f020a0f050315010c05010f0606120605030a02090a05090f0f03120c13140a0801050c030610080910050606040902160204050606120103080a0507140c0307050405010b09010e0118060804 88
    0x54401a1f898004074003603c21a481031040074403090a07000a000150388043c403e0800303981c075658800d031032114a4294402c00e801b4094540760507002100c1210360006880c0c0b2900041d019400c001841401616000841c0c0e4005034425404140c9907181c8044c0c03450100c4400c408503251280510f0028601c0002c0010101c9852320902580c2966800d010f40c950752003200e01680c90340c41e840e1010001c940881c00043c0040304014102c0c50354694a40b1502d0941720241c2c1c5040418070008288082464528142d074251a2079050161030380c1b4042c61907944607100f2440d0f0f021603a803180c002502c1d80c1c0d501001c4401030f12680701d00715260b0b40603084c010a0a00d000c1c80480c02a4900004140c03203160000540e461060014548202607083d5901c0c403030f054014854001c103100041c8904000501070303e160054800c0502e000341175204007213003018500744465000c0703801689024010f11111007403e0484000e13a10a00306001305021a600403039103c2450a0900030b8011280804210281c0c4500614003075 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 49754041 1250 49752791 49752797
    0x2101030314040602100902060c030a05030108060105040e0d0309061103040803040309090e070302010c0602040b0c030c0d050a0912050a0b0115080c0a0e010f0c0b0a020403030807020601030c060e060c010f020a 91
    0x15440c80d4144040741c0c032850050b4800f603808400c0540441d4100d030001301019202402803418a0404038a0074559000805031a010079004001072001000c1044128010001201d092162500000c0c1d1561180341c2010568209900c86010000341b180b0b980041422003803001000780c4c2d9207001d0070001034035001518111300242c00c0e8940002c615001e4011211041ca8610180080920b5507006541d49190b071078044440c16000c0c8000200104000e010f80070381e503070500c0a165101303080103400d814441d030b00002d0703001d000d01849140b070300640c407454034002d8449207030140c038074001642803103841c009110400504c03100381e603400880c0326441e200c50b5584031422610f85038815245c6059042241c0a090300e031100088075641d124015621074861503070061004e040000e00c208290310b5440034030404981d0310300e181da0006002c20405a00c06400d82c0e0110031407010b0301d004d505503515100c0d4009079100b04000c004a40000c03100581c1ca52003220103140f140702c002c002a520060401000e500004014408 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 49755291 1250 49754041 49754057
    0x608040b18030d0903030b0301050109020903072903060f0409060c030c05090d110118030f03082d0a0e161401080403020c01050703090503010c0c060f0c0206040605060621010303 78
    0x5424030806160741c50709404005141402c1008040314001c208050055003016102c0d03401d040a41c400780f140c14040c090722400940d440960704245850040250300ca100c1e0105661414001102c200c0b51a036000b03400c1010355a900d84403000040c0c60704561180c0c0303a0780300380b81104060402c0746a500c450201c40007508d00f40800e141c1d200d01502c6a0240c0014590000c04c42a40100000c8610303003c03015081c0c0504103d558102440c5a115913103016810454000705809000014960000d400c194059a010a041054103011114400b90812045501c50301c05045001c40c0f07400001d500712820b110560011281c111044104000c2c20340d000348180d00c80795001c0c01c580b0030030f035101d2a401da108940603002050703016080801100c1c80e502401050f0100b211f0354102289503542030140d42001c101550720907440c25424100201107850f20510f07592240c1c9005c00f0000119000f10700280d1013600800c0c0014075a9815001c00c0e1302e8810303041c00d1040580a105903801c0c50000b0414507040e00d000b80c2e91840 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 49756541 1250 49755291 49755301
    0x605061002151008030712020106050a0518060f06120a0b0d020108070804030c0c0611070603020a0c110d0204050106020a0506060109030f0209100f080109171912020708040608040b 79
    0x1144450303650030540140c00c91520400406000c00010350032116000d4603a030003a50390b4a066055400c00c0c50304803481c0c0f031400c0b034900f0300903424021b250103440700316200c2d5103c524060000b440e1070a00a40200c000c28500001042d80d034580c881080e101c50007400f0681d0321500c0303c520707a52424044980c1000c06142c00c03a418103d05010281036482d6034181c4812901b0f0b00c0d0b0160175038024900a03c00c8080040d060341d90800622004c1515004080c1c54070b030303500c00c030304400705440c02c092a54014500b0075205001840555900848640754950094441c0300006511804642d4500d441c0b14041d400600f40700c0001495640058810b6450f0701900c103031005a2204001101d0400580c40041c060307941c0000c9030000f41c81d141c0d12280c0c0018940c8040440241c6c0c6112001852185078801070560f50b441e603814050011401000c00441000c1000724605010403481d0075000950340c6e103000400039102c03034050032010b6650468210310381100407640ca40d40d903080c0080c010a02100e044400710a03501c04a8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 49757791 1250 49756541 49756549
    0xa02030f0105042a0302030307080a030e0d080a021e040e0103300e0301020d052403070e010603021c020f040303090512060123091306110c07060c03141303060506 71
    0x14040e80d4404405029030300141e41c401e813010f103032003801d11070f00d000043c0001c0107039402c100806440d44200c01080d101c04816034040c00703d07881540ca040568100c0d010013902d80e036110402652003c84210010f0304c807466103444581c05400340c0304000002c800001d0128640300c406101a04a0788110000e003c9841102d03000340f80107a030700701600030841c60751800c0c00c04c15011f83c811807100341019000504101c1440e4915080d220305880304070040056205042c0c0130750a00a120360085429002002250310380341c040d6240541c14400e8004055022038000e04107a50002010000d4803c61400c2d034507554100c0c2e810a9550144c031007100070403509240050103051440a00c82441c01c4200640032030b80c604043c1c1d82c810a41800d141c00e0300340d9600d8400301a41c0d241071819019024032103141898101d5840c02c0c0045070600041c41d850441c00740181d020010307000446109071100e902e4000d20b17035541c03403409440d80d00c41030005140e80c03500071900300d0106034801c100c17408aa0098405018035141c1e04244 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 49759041 1250 49757791 49757801
    0x509070b0c1b0414040b090d1d0d05030c0703150506040b061c15060509030d050403020a170a060f0507140901091e0e01030302030a1101050f06130b0307080a02030f01 73
    0x40310360440440400490302001459020240203800814810302d604000c03422450125000c0720a01c9020b1b051000b010340c2042415501c07070850500300c03030004c01a04110400003c1c1c0f840c171486240c500307041004000080c000d41710002020404c0301d50790b035102c0c94800c18002c840c002d074081a5107490700042040c6014018274601c603034090010740c9080c0140c03c100101d01640b146803000341d6100d1005444000c0d101d208800200400e03907469440707000c07403000c141c00c01c002c3c0f16050303040107000d11007400540d98060040044450850340c00c00d5043d01241200e0801c1c00d000e10181603075260248100b0b000f141504075521800e103950b102c14850442e11034403490303402610040f60001b010417105100040407920b84100180c1c48044024800d0341c0c8907800030904100742c100300c005800210394481c45170780008030705030760034485002880a894847d07141442813000809141c402e501c0c09890070303200c1e416944603803c1608040d050301c02d25901c441245695201d02c0604a000b40714284036603001a0045c440c0d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 49760291 1250 49759041 49759057
    0x30708160c02060706020a020a05100f05010906050f091f09060e06100206011202150406020a14030901050d1e06060e03121201050f010207120b040605240105031005130509070b 77
    0x3e403800d20b40c8a0f242d500c000c2d084a86c03c0c0381984251140c420210304200f100281d012844c107008242d02d00350201007025204180d1103195100c2c1400003e01c200d60ba10300c45041145001c0e200030b682581e5075a011145e100c080f001c00b81c80202c6190004c07038600001e0704100160741140c1c0490301941c031a034040c00316950030009080010380190f0010300002d5020042a01040d000504440f42c54406141c0000558801e40c00301000d41d200714036031420407415080e06d031440303640310b4084d6080c80d04400001c1c1842c8207240d00500b61640d20f500160002c401d0078a0420480002030003000103a0701e0300da01038094074440007004d10070321a0b000310110b00c07800e040880303003402c0480045a840ba445c280c1440740b018520f45003a4194001c40c0300201d107540d015080c5001c1e550045200e5941406c003410305000715035014110101c5d54017104030138852444c07034240c4400000405c1c6001950f070755860440c0b1450440c141c0000f580050903c4400341c202141c4d820082c080c1d005070f0160361800d99030399007900c0540b0907030700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 49761541 1250 49760291 49760299
    0x106050424150203090909100b0d11040b13051501120603020a03110109080313060e040506010813020616030c0614061c06020f040306090b0601030507050f031803030708160c02 77
    0x4402e201101503075aa03400701202600440b410b15508200081d00b01008880b00703803559000d0303a0b1040c40781009018458510a05869000b4214500c2d2607a180d4000a00e80b218000d42d00c4010515030f0303854488110880e9910b0740020405403c24048a10118002c0151a0b001a40e040211a80e164951148400301c80e03004001005c1181385030f40b83d05500300351010090600540520008401c20180300038200b1030186012a2421810110082c1ca103103902c03c0180d000e51719100801c0050b03600305449903084041300f0210309201178107200107000b81c41444001c401d44210100e200b42015004640008010310800c014403003180d10750402c0590780c5080f0342c0168040c600341d514049140300d5400752450103020703000161410506294202503030340194011103841c1d40d102042c0040c011401129904010300f403034140318904101030003c041c0c1c01002e0a8041803080003010445986070304464082644800d015251240380202d0301514207201207440a038020030155010f00c81e50b20444401407082d50080c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 49762791 1250 49761541 49761611
    0xf020f01030b0d0b0c0d0212010e0c04060815030a14070f17060105011107030605070c120e0108070f0203040909061e020405030a1101030b12030a0f1b0204151701060504 74
    0x34498030070019018017402034034141009441000b025a000424500c800841d0141965152042c9c0030b41999005100030401c803024403003889401d40c4011030517084404542c20740ea0043c0b10b200028101200000700402020001a142c5562107010809a00300c646860642048699444a03c400e581e80482000c10907004180180100e6000d0500002c000314036000b1141007035242c1ea109012034a0075030b4460049541a804001004040c4649540e60203440c901001b050800d8070018140324400b801480c1030000c8510503404062003001654000c28091100788075160213420107900030031120814100007642040c0c074060180d0316000300c50480340302400070912220642c41e00021100b01d0801d1a0406440340300f826182d544e80303441e20040c003107410055030b0303074060010004e0010600b4591400c2070000c03252140584504403141c220710603030140c42c0441c1a4901c811101030b038400c607410224903c4e8600040010203401507220505481e02620200b15041c5c5072040300780c02c581c42d90090403800c03201c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 49764041 1250 49762791 49762793
    0xc0e0109050607030813080d05041103010c08040b092a0f0303030103030c15140403030b040c0216030f0302120d0609050606040b0702040b0f030118020a0b03070203030f090a020d0f020f01030b0d 85
    0x4101d443d40c4041928142c16403000380341e8400c1c038650700030b043d21044541c9460900ac148003940084208441301180204828070130010080c00341100284082e0480340c072000001e8860700c0030b11000c5a17001c8901ca003c3c1902d00c0040007510701c044001e8603d8060701170b8510a5500b070034000101c0f416aa0141c41c0c0d00f140344a1580e84d0340c004000112000c207010384804072001d03c10001d03114940914401d07103010503603200c1c04081c8011200c2c8506041e0071580403417032113801203812541c0c000c1542e03002003e1844000c86418243c5c07401d01004400e144100000403d000c2c0d2000d41e034018410307580300b100c05101c261164010070081d401180500c0c1c4482204200100052170f16501600806801a1040f0050074420000074215080314a1300704031074400d503140302c0452410305403d0016041003101c0341d055051140000b562404001c04549400070098081000e0b540f08016200c4002d40c02401c0304015100ea182c080c41c0481e426608a000e01d140c0c1d07031603048070743c002d0041c400d07101c4020748511106219 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 49765291 1250 49764041 49764047
    0x1e0a151415010309120302030403180b040501030e0f0f060f090106060f300204030b0912090d0302120409090312050402060a0f03091b08070803030402090a0b061207030c0e010905060703 81
    0x100310300d41e5050540d14810705001a00030b03800808880c4141d100107840749024140944150045521301440340d441c1c50060214800702015982580c40a2a000402c11036041c4000d18044098440902d80c1c0b04801d43c6e4480c1c03810001d4400d104025503000d81e1ba25480312003106090351500c2c0078000210f0341c0500080c107458841c00700707130b45025005841c104c981c2542d1203d2101554031200a003e0f6250006418414820000f11090b00089214000c0803942c01000035107581d0b0191f03c0410b48981c002030209000d05100308844010b28200315950b0703548a54807600c040091040d0202140482d480409407000a00c40344a074a1003036401926039844c24071030030303001c80d110700c030340043c0800741030713503288444040349603030400510b90700f22681460703109814468110300d840300170fa1000b60b0a074010801c000c010703100e414081e500107503050400b0500c88031400004880c0c1c01040d03070b6442a8514801000b08890785508144800960350310303071040c2c05201000448400c0d03481d00a580d0050070401203800000d00c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 49766541 1250 49765291 49765321
    0x3050c1206070c1202160f14030c030606270a0f0c020f0604080c030d060b040602060112080405040c0e0603040302070306061d0115050418060806010e0f07080402031e0a1514 76
    0x2000d4410751b000c00d800303642c8100072211306030840e03203900c085c0c15000d01202c010f1441119612404500030708401c1d04240000313a40b41402071035540a180f4a9403000c41d4000d2207a41c00b4284551444a030145140c00c8005800520b44515201101810040c0c1109085d0000c03696000c02d0300b41c00050101c60f60350b51520151940b00c84a00d1280380b1041240c1a0b00d01d00c1d0b40b14510152120b261080c1d81c85180000091402c00e0603005101d0401c4113030128400a0201811141140d0f8107840100e0410310f140001d403000c0c00b40c0b403041c0c1d8009030700004000402d6070100756003080d80d1007134200300851a120396590745601c1542c0b65090a00c5d0850300103201e0401c00c94116100d0312414030700030745043d8a6200550b80d02c07015440c0680b180342c580c5001d1000800910041c0c0c05440d01d84460002d80c40c246100e000c07002409894002400341440200f01075440921884c1f605005c10481c414800031402c0c44035589080d10301e82900c0c04d0500e0140e4107292a00c500440d030304043c1d0030130203141c7c0c2e4075041d42480c5000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 49767791 1250 49766541 49766573
    0x80702010f0504080109030908150112060b040212190c03020903030702060313050312010801050606071109070212180312160b0711010c1706100f030c11030403050c1206070c 76
    0xb00040c800011240c100b401801d00040c031a0b6030f50102c0605d001e000524145165030b10003120301d0323040700520910812455000070142c1189001c2144200040450700a2003003085011100100504208054203130003603001d2080e8144800300681151400121304034010020869816007007001460301510b0100081c5400c81145141240507404079030f9000d140d0780c0300d1054012810300c1080100b00020080c1300365540104207480f80d80c60f128141d51801500501011618454001d80c800308500ba8804c20090070320060030380d0717815907a441c0d004205080c2010001002e10030b1041c400705008801e480015181154007614440c400300c2141d541e50003524034024481420028041d000407491102405191811002038980b10181c910345950180c030940000c007141c0c014000070a048144642c0141010144069460006a08001c0c408100da600c06d005040d101c05110114011040c00800303c5d4000e9030720000c0380c41a1034182904503040d120401140c100010038601ca0b0714501240750100c05800750 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 49769041 1250 49767791 49767797
    0xb0705090f040603030e01020d020a0209041719020304090f140a05130b1015020c0102100c03020408030c060114090103050c010c080d0e0601030506130503090d17030906150a03080702010f 82
    0x1c40c0ea0240410201d8819074800d800103612010300e1002540c06011a00d452802407020704910601130700496902d900250000b0f001451811283c28548603030320580e28020f0092541050100c1071102c029900e42240c02a890524038260360a10008a580f01e50391039401452540f05103a620255900300610b0028168900c080c141c140b8040003400301803003648240c401c86803840d180c1c0d0429842c4c204c0e2008411b040390a55002c110000f51030b80e000110303c10111002c80d80481e9240c101c003c220702900865010081610020413841e0700103c01043d101e05071007601200a0201d1548401c1203401d95082c4030162054001061031442548250444e4080501440b00319140c55841c1083c80c0c00c44000c0e1131122920340103a40140100003082c00855042041d820341980105210340b10f07607440e4400c0405043c841c000ca070b14a80c0403c50714551702c41581c4c1c0c2d031221540e282c4c038205662544a82d001c4642c0040d00b1410740701e4804500e802c80715401900d402c40646824807a0300e50064800c3e41300f0b16842028 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 49770291 1250 49769041 49769059
    0x108010b0a0506070321020309060109050106080a05090718050f060f0607080c01061d04030201060b090109050f12030408030309061f03061509020309030403051c020607080a14010b091c0b070509 85
    0x200d0350881b002c980144600745006a90f481c121025606005040e0441d04455051a004000860b80850215000050510001415182e41c1007891804089500452043e0100960801c2141c129406107110303d132012100c44071540c900c4104200c2c400c80c2e05030154001e00520900000c5907004000d05214801c4000000d90651528649800c1d24440140d0400030000e100c00c01040560a0048000a00581185074248160170b4006030050016000d0706000c2c0306041d4000c01555201662142c84c07030703034950540381c0c2c65464892031502da40c0216602c0c0c00905c2040c01207040d070710001c00c940e0300078118100718101701070843d034900000d8007005030a03602058030340f8400300b44034a1a200450141c5402c0c001555030302d16501d401400d02c60304013006039680f10158002c030300170f90300802c0382a4802594a000815a914444040014003060559803010b05003c000414200201001420486d00459040c1c02a40c5601a001d8425070700580003072400c0700303010100c0c0c400743c0148003a0048010003820566 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 49771541 1250 49770291 49770317
    0x7091b0f050f18040c030506090112020103020409050709030c06022a030a050d120605010809030a0507020d080a0806011209110f0a08191a100302151605150108010b0a05060703 77
    0xa403940100301049200000c00f22550100d02e09885035403d1481603040a01c1a032074880300050b8402414403a8255149112821108580c886c0d4100c50151200350410442ea003011440200004442d000031201c4032000500450740b103000180f0b410340c458205000e48004456401310900d550140c1170400d0b014401c003030320480011414090160300d000d031940e9006a006000c0c400609582180e8005410f01c03d4480c1403046840010007120580c00241c10b000e5511100c51011401d543c0070740001920501000c075035280b056a0080f096170040344240d0ba102002c200e00b409031821501c0303401707000f40b102c5031340002e10201d030034041c1100c04541001041c044d071085e668858070b0b04188040f03011081d440c540411060401500c0710306d0004000d21158543c00d1481d00c2e041c1a050907040e0300020788500024104c0e031003c51406000c89240c8541c1c4141c128000e1510700e409d650b1211030403500c40e02448130134008180f0000520a00e858000000c00400760745240c903040c4205544026070540400104102d400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 49772791 1250 49771541 49771567
    0x20a0506071a070e0303071e02090405030a030f0b0102061303090803040b040f1a03010e0c070c18050702061e10030b010e0a0608011109060c0c09010801090507091b0f05 74
    0x70090300e0248800500100c0380e030702102e955680080214091280c2c0060024240e2800415505080d9000c026a01c9035008000310704584c400c8010000e5000101c1e20811003006800700c090480422130b900c043c400e000b4000501c3d41a210340c00300309801a48000c1c0050309a8209041421503d070280c2020b81701c1c1a11480d2840c01c5601a0b0000d464007000010200840c04415480d04014203011010300d41c94582c481c44050385120610600740c550340a000410031254088040791500c030380c001c03a0400d8a654594440041500c0361003100016450301c00042c0c1c05a0000c900244240c40080d421900341c040c0810504005e00e000c3c0c403c180016001d000400050360200b009400f80160300042001c074504607400324261195600125626418410381960948483d416207055406c2214565202d014002080789059050003031a41d0100e2848000505140103501c12010705002e8816603088a80f60056042507030007100c4440d030070000003880055070b42c0c4948440510303524145050b0f86000d501c8a00c2c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 49774041 1250 49772791 49772797
    0x30e060a02070302120a080304120e0604120303051b160809030f060402100c030f050f070606090501180218010f0203070b04081201060e090109023001050910120f020a0506 75
    0x40c025900c90071080c000e44c50311456400480c000c1000514222802d036a4151807400003800013020302041907030040e055030043d00040c40000000c1d26882d11690354651941320000045003e601103441c6c040400d84500741441101002c00304021014034002c5034404500a5800029042c2c0d1401400c1c06000da003980d003071069110001400f0024542410f00f80100100d1a140b03200a205005640036168002500601d20748007c00c883c2c2001a12200d1400311a40d2074468440d00612079842d1400201d203816103640107070b06842003410440100070304454020100c5c810399030318800c442d00b4542507100940c17207401c02020429952069a080c108282d41d0001d1945095404a170a14404550030078040002c40701140148414600120030f81c8101011807140030060080041e40c640000f00348440101c840c840c2541820260070020aa1100c1700701d1012620302030040501c80e000c1180032940c40d545115451050300e03100c1c08011558503090780c0f40310032819820003c903009204140d0015181d45c8110113 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 49775291 1250 49774041 49774057
    0x1090203120a0311040b0c010e030304110f0a1518050f0306150406030f08040518061c05030f04060206060a051002030409020309010b0d080d0b011d040e010b041e050f040b0c07030e06 80
    0x10507903c40507c10f9070a400e40314100c036810519032052041101080c072084244c131204900750755000c1183c8519022900111040e0002103152080706200300c070b42540710542e52038600304061034013036640e215020010348541515585600da0302010110313810040075141110b1b0b20b403000b0000178000e942d0355140302081510343d1041d112414041000c00490400b003540400c101c100c038004009600e84840060407201307405e080c941d21441840124810010200200c801c42d0f15602070a91302c80b940d52600a594a1007182c40502803901c0100c0000d0604104540491440b01070700034505003814581c0340d80094000500c00c5c420766480f011050843d484a4040104c0d15010701d000603950f1802d40704030710650709c4003003200b030412807013a0402100e8001950250910b0000300c0b000308200f104100040e024007001181d607584079140112401292801240244100a801e03400744900e40e20b00064032700c1c1c20b07400c40c0c008d0052034081c13000030455403440c070013448024442e05050700a010007101044503030301302c584 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 49776541 1250 49775291 49775309
    0x80a150b0301030c06030605060712020111030901060f08030301030c0b07030212162306060607060609111e04080c010f03180309080c0904050d0302030618161101090203120a031104 79
    0x100500601455801d0640500624203007801f045150102091880c0700386076001c0c000c0d102c00b6000d000d88074400e401c0000856403110f8044e4880c2000d0304440d000300a941f02c0c4500360440030400040030080402640d04036900146900380756443c000342e00c0c00e96402488100c04501802e00344028510542020f00307500700c2d54031120011105589860b1407081800400003c0d402c00748035918221240010b94142c0c4900700382d0703411746c440c0460301d40100a0180c0c1d402040b24181040d100e005000f10001c080d0070083c0600003020319900d03020700e51800038403c0d40101c029640280402034440d501650541400045914000403e1200e0f500315041c18107001c03c0843c00565180410001c8240c10400510072a0084031009040d04007a84d80690325140945402c084c940c01000003030803a030703410490760401c85440c40d1100c0d4514001d2030b041e144001c2000000d000c950a00003c08030500b05109405000b41e003c0d004000c0003001d80d0070f4501035080349864204254075403400041000100c4c2c050700007401108 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 49777791 1250 49776541 49776547
    0x1201060801150c021509010e040203040803061914090c0c031603090603020c150903160f1203060e0414030409060305010207020f0f01210f0c0c030e0f0d03080a150b 72
    0xc10901e50200c0b600154100102039032884050b0783d503000407021516007501502d64505070b0383e0040c0e4168052850441e40300c0c0c804000c00040c4241140294460a0200c441c0071004e495074140b060000028020845100048007035802030f030900f0300c1c02ea60000034451145041603940c04445107543d20101c041e6a5601c1c000c2e00c88020550000390303100140ca810b0405504122030300a640c0d540d240d40c0d8450125100700600814111441401121024039900802c01d5003520141090b4602080d43c103411511134043c3d00b008116584281300c2c1c0c00c00d40c3d224443c036601c01d07111610350300408a1480c8118682d0b0108001c00911540181b15400c01144940000740c0c44400034010045035403003503019140143ea102034503283d140e9110105e2960b03608104c10200149806503a0b90006000841d000d9908500d45003850315020f8220348241c0d0740301d02c65625901400940c405200a4010022000b80c0014481950000007800341130300550100c2c01190000f10740c8848100217410b1601980120705190b000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 49779041 1250 49777791 49777799
    0x70803043e0a05030102040602031602150c07060e0d12030c090806070e040621120c020307090605040509150a02070203010b090403080412050307021b031f020405031b100c020102031201060801 84
    0xd09048001c00b0101d008501f802e103041c1d4040d480f4810030720180d01f24942080c0003000c540d100e503220311a094160301c0321516281884445640e0700c2003801070102055102c014070600c1d142002c000306c40c0d19803000000e0848040c918040e0041e151111402083c88007110011409100c10440365104084503603c802e036a14400050008480154010160403c0c03010414403484c00d641c100380f800389522820320401040c0e00c0c001100c296030810170080d0f15000e400000240340006811441c140c5100316020805038840120091b600c00c96002071084003141c91000803180e1a150340584015400500080b940e07903030000014540c40c00c102c80440c0891000d00a01c02808041220325820380050f041c058a1400c2030500a9521fa01c002224448154403840107000b0707881c11702034450031a51814044044c5400c1d440107001940242c01854001d10912944c10911200c0c078002040c1c452b07026102600c981d8148008491107a540305081e03040d840104161040424520b0141d8000c0c007480d03407902455414 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 49780291 1250 49779041 49779049
    0x5130f0309050f0a03050a020f01120f02210f07031107080403050303091606050304080d061205010e01050a06031104050c0c030a1e0c03020d0f0207090c050301030c0506070803043e 79
    0x2180c00c55405130041c2c41c41070000840001311800705580440c0c00b00b5001d82d504004a17041001c400404680c2070403c0070340f104820440d000303801007440030303040480d045040006200003c10110b8105503e02c0e07140c000318a00f1406544000d6440003040d160601d410249d0b00d510b00b00740e10503402100c160340300004000555200b8072100703442c0501e004902d1501031500100501d40e01000d04040c116000000e055103500503141d100100805654100841138620782c18014000d1614841c072100da942800005180d0a4480c410082600c0d03100b0422807038101c1350b40030700c0002c250080800d201c08108000c9020040c400b0070181c00002210b0303a954101d0080e00085182e01d0030681c550005000207100d54500017a0041a42c89210116281c80c06e01d031403041e0000c91422407107502c50350203207280611554005600030001c6050301e00640d0343c050744c140e60b2010b00c541403140a034094180c0d0f40500104000900803518804600101030b03000003800040600a5030640114050326050301b807400c942d0006042c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 49781541 1250 49780291 49780309
    0x1b041508180604020a06030b010e0a08030a030e0c03100f090203070b031801020a120203070c0213021201050a06051209030706060b0c0f0a020102030405040b030a120203130906030c030605130f030905 87
    0x9280002e000d440c140359020030303292a09401044241078640d0800c0c04141d10400217082000b40080010200070b55034800107449620002e2400002414003000302d60241000490310740c080b2025000b0540324185645107402882c0c1903500001060301c401006000d654100001c00180642d101070725528202522140701800c4c012519007896401030100b080042d81200031041d07403a03803210303001d41c0d07075504d101040341c1c2d800c841200254046114125240d01c0380c141d031701401c0c0426a003a62900c507039883c0c2c070821440310003c0c400e4dc0c00203201007003007001d0004a0480c158000304030b14210b90030401d4a50b515001c0c0c400c281c01080441c20045241400c20800300f00c15006480a80050000b403070740c0da00000c2d00c85c40b42e0700405024603101c4030200c45071303101000b100011a03086001034601044075a4000d490303510885803507908450900b0080340318a018400d94086030342c400c4001440610703594840f80501030042c50612170414001307510740071802c084c0700b114881d40702c1d94400100c0c0e401c050400641311 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 49782791 1250 49781541 49781581
    0x717071d0601050f0306040e010509030901030608010509101508011e050106080f1621090b010b160b060d05011e05011d04230703050105040203070603050c031b041508 73
    0xc0303080300034040d09903000811a10141084440d841e43d80c2d407440d01103806088501882e182940c80c20781000088640403000d045642d600360307414000313155a8150075080e2402a90040d00326080328202907044c001c0c2d94068910505100003030355155950740c007403600b150f607100450610b00d40d10031007080115100d8407130300703000d017142d07042c682c0c280e013014030b440c400e4840000c01d83c1300c980c1d07039031502c0003903440c003d62000c074009445142e4000b0700016000711002405040c0c808580c0040494000b00e55101c100003a18040100c10000440c130b400e603601e441d6201a03010382501c0c4c00260584006000c201c0031300446d003048244034950140d04042c4c0c0502c4c402c0b514168407034198400e901280c140100000290650415040f90700c0001d40034059810f04505030b01c0b500c0032080b900c900c1100004210041d00028480c3e80214152040309923540c2054099070402c0792614540541000054170441c00702002d00412201138041c24182512449840004000f16054401141c80c44080050400d01032258180b60 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 49784041 1250 49782791 49782839
    0x70e070509012a1104020d06091a10020a12030b0d030203030f0c031302040b0301060e01030c060206090d0c1407030b071706150304120e0402070f0302010b0927071707 73
    0x5000020307626050f41c00e030314006002050b0151545403558581c1c0584459002040341048401c1c2d03905440741c004c20807001c00d01c4030005d11140b980c1080c584901404a1b80221740c0280081c6034040d03a442d8007440540c08001d052641e15020714419441d00104e80e10480e00c02c0d001582d481c1030911206003910002009580707180410004c00c40b0801d00c805609102560503500440c240100c100003902500e05500148031010303a8000000c203000300080700070100c590580980d60141c035080c4a0075101e515002140c0080b8031640081d40018074080c0b01d400d0411009402c3d9035041351642c0c1c07a0500b4060036144000003800780c0d2246901c4002d860601c2d600020111030004111054800c07580d05400014400b03020008014030b40b00d255030041c50015a880401030045540340b4003850483e201054690003600158644180c03446107080c441c0020340148183c0c40844034000c590601550070291402868030b517801554800108500042407800f103e4106002404601e4246110029403d003507088039552 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 49785291 1250 49784041 49784087
    0xe090f0a1505060d080904091a160801061d09040204020c0604030815010507050d03020903100207030210060504090f02040b040e1c11070303080c13032906030a0803010e09070e07050901 81
    0x4881d40b088a01d100411f81f40814840602d00740802c5420b0480e94000010103a1030800c6401075905070000f5180900751603c41159888038400c45001030b6030307038468950442800300c0c2c03072080c074100c18a031f03900c98402003000d4644411040c016080000990781200822060028402011491002980750075400c0c40c00c0390400c1100e440d0b90799240f01c402203804c2410b03400980d8a05507102400481a002449041590f40d80790b00d1a001796601c59504000140724904100821140303068020b500b055034203d241d0100c0444c0c10b4081000400324a05120fa01554884900d425101d00b40180102c031040b0180c14010742c1003444000d058403040520185542c0c210303600074000203402c20951600301300c402c2803003034982070f120020398079003038650f08058031028a042000401c41104072505c00a0042c0243c02a41a16940c0c18140d0b1200c490400402d1070078207000500c009040e010f6610713802020314044030103596a400045070749030b5059407158000b036400600301019580080201e000d1080c41008155 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 49786541 1250 49785291 49785293
    0x4060e030c120a020109050a0b07020105060105090d03080702010f061d0108010b060406030e031e0315040e0703020103091a041a091c050901090e0a0b03120301050306010e090f0a1505060d 82
    0x146405442c0000501507801061103400c40303100754030008440382e01c401164501d181c14241a004d480c0115000760040d82070000103a507552203041924440403001d0204c20302c2420558080d5442c010062200d000c5646c3c8400400fa10036242c02120001d00c0e007401c5c40ba00d030880b102c440c400ea0040582080b9401d81c10440d804e00d80e41c83d05000c84040742d80520303000030506100030510741140302c0c0308a0700e022010400390f141144404000110700035100644003401c440f22804c2884107aa1004403042c0881d0050403040000d0350007900545000c62048810b0360710710a104008400c0e103441a6426114280c500d186c1d000319050780110340b038200340144020000001d4260f55100300402d64480d4104104004c10400200d9004040d648081e044148042055180800300c0300e0051112071102c40c1700b48200c070707440200310000008a9061300c402030041c0c03203503030300700140b481400c04003400680182c4100250712007000821b2006404051040c002c202c2c18240b4005030002b540c001800803803040c000592800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 49787791 1250 49786541 49786543
    0x305030f0c09090c0301050906031c03020a03020c0a030c03120608060402040e030d0905010e15041a1909110114190f0e03010509060907061805060906071a04060e030c 73
    0x3984000200d120380080d54520500d4901d5001d21480c00e504400c1c0b003000d1080c0602c406010b1030698100b074034600417595400d410180d42c0c00c841600c900340c480c0b4024070300301202d119400502101180341000362905240c0d40103d880e21745001e00503000600e4264a01080641c0403c007405202d080c4030060280318102006e0944516020704002c7c4a0340c4d41b40142c507005035081c415180120304c5058104070106039030030890302800100800c1c00c0d0340e001b200e481e42400d1503941c424030f00494200c1d8152400325845014605140c0d8007601905c00d10081e00b20020b004901ca0090714250b512132400301c04003211000014298134030754a102d41e0640b406016100300200545c0c50030010840d1740c40c21400c0c6460301d20b41501c5051a00038010b4040d42040300b00005e0007000110f1a001c0c4c6103003402c40724101e42d10001292921806031540192280007541049103152200242040b40300003085241f030241160740c0c0305c0f018002ea0340d80782031002001d003c220600980c1d1044405401c0c0d407002440c03802e11429191 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 49789041 1250 49787791 49787797
    0x60f0c040e0604061706010608010b070308130f0b0a02090102061003120e0103020d0207030201021213051c181e0902040506041e0b04080307050105010501090e060d0312050c071407030305 82
    0x700c541041c1d40014a00340da0b550001402046086000521a4a000e003081c0c1c0303409003400b4903004108240c3c00003030000c42040454400c5a05690b5040403500e9640010002c1c1a12050903601e0f030b81440001008244c80c60f9986018030425840182d0b1940d51400290804200030030fa08841c510840c4204041041103056070300300d010900d0107000d40801e40d00140c0090154480401080d071011404808254055000b028542c20141000c0c13056038962402c0300100201040040094211121400100c3c2002131300c40030700744940c18400f5180701d400302c125271310400c154400d2010100c03038091052410640e1a290380500400d610079403626061401068491040f8410b03c860002281101c420b00c041400860014204d0045026652980c9016150b503c1e081000c05660300d529007000002c0540c0154011021500100c121a8a583d1003000b00802040004803c2d004d00030401d08034030411a40340308061003500c002d4001611341d001410f0100690300f0f500400612603000c1e880600129400c1000e0f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 49790291 1250 49789041 49789049
    0xe070501080a050612010f09110402031b16061401031509051f0209060301030b0106080c0a1d010c0c1701060603050603060117031606020d05090307020906090601090e0103060e060f0c04 81
    0x2c00304903504e506000c1007400c8505c4069019952800328403565212040d00490003141c000d40560000542ca0802c220403484151124402c0d0459a104030500803082c038090301070b91030303040039103001800240c480e0000d8441c43c0f0010007182561600520410a1840d040940c1c3d1410f01000c01c07a131041a0f5440b03035180e05004141d8410441c400342003a03580d0031501101d0001d00041c05050f100d5a592805107503c40081c003520012a08c00d00008a50386694001d885181c1c1595035a10103030380303102403170100380c0c00361220282c10011030440300b8002c070714078510b4440103250b80721142c0341e11002c2408050846070300b0f410400030581400244a9580c0d8002400380c191580c020300d080c42d41205113405459803040746094180012104221018021541c2c082c0034913490000b014800c0c2c0d942c220211380c0b01e02c41c61000940c0944e66030085892410009100c991040040c1043c28410740c603211074400d0440f09134811204140c44003480c106008c0140005500540d051820f40c1590605001c0c04d0124029401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 49791541 1250 49790291 49790311
    0xf081312050a031404050d1505090f07030204051009050405150612281401050106020d08010510080603120d0509011401120305070c0f030302031b06060105040b07060b180a0e07050108 80
    0x413194200f0b84510040310006c0c070004080d181e08110701d10305000380040c04003590840c64a0080022010840850701e20005024803001d800040e00710b5003004010003014102200c0c0d0041d5040c081031009035446194011030040d002405113003c141c00d001c04c00c8000401490250110025041010000250a003c0a000c22200c486c0c0101840b29520260031030400240c039140c0c0000c1890700409066000703034166550b95003a00c3c840c05c480001900e58540a20600d80c0200031043c1c040030b1180300e10301c200d411880c01000c1d40c0c4151482c240d422015004038145014a503600c40038060591000d1042602e4060032803482c0f8aa0740c5000d8048030182d10800f406007e00100284120801564a80031000341a81c0350540350150b0b180e040c02940d0340c000200c4022850380309251244001c0d03000410b20300c1808160749042c42d1a040045c8144d66821100040b9000b0f6142c8500081c03030350f60a204542250840500d0303038058541081c4080c00c1c0e91100341c10541030b07049414184401e0b40c1c41134200c1c2d0f00042c240 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 49792791 1250 49791541 49791557
    0x9060f0705030906070c140613060c1119050103050610020a0b100e0705040501020609210c07080303070c0c06080105030d03020313021003150801021312020109030f081312050a03 78
    0x70800c2400c40c40792401107544042d0008000041129180301001a5942c260603d1402c190802c01d1040a12070b0300c00d403d1944110107000c10159209900c1102014070466200007154080f2000c5101552a41240059045003860a024650b414403515034040c8040390800d005588031031011751280c1c9800381c06001c8080210000b1040e00011407408000c020b40703080c40015180500d0003c046820600130240103010f0080800c2c040d03280000c00e0082c2000350304401851007800411211180c4c000c2c01c03004a0743c05940d100140f20603040c005188200b0047d00c0d0364410119a10b020300c000300250304881d00b84003d000c0144201c2d240001d924182c01404e060040e940e4480c10107100c0b140d043c1e650029802580c0204c41ca601c1a40741d0403103550f0201d045c1040c42c0298403020002c0c00e034000c007a440c0004003146c5004000b0200c201c50b180f0f12803401814001d9801d5126103d0703e2018945ca4016a561035000404a001c2220840340c43c0c01420840d030911980c1d000766440c01c0e100c854000020f02040208 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 49794041 1250 49792791 49792793
    0x8120708040b0a0c050708010f0b0301090b06060a09170105040302011b090b03130501090f031101090503030c03150d0c030309090624030209120a051c090614070f080306030606040209060f07 83
    0x40791055030564103d02241c1840365280c4a2901030400366009d030f07880504082d4682150304050103a1801290721010342d03d165520034061000a8210450f40020000300c80c100140700b11050300a404c10407024000400c0748d241c1428080e081d14180c1401901642107400c404400316440318081042c2c602d800740c115540d480d1046030b03c000106445000d4815460300600e802002019081b000740f9500c01e80b103409400c01c103440e2880c200c035440040644241c0081001034201c140050080d0352000c1d042c024191004180404503546006040c0f0407203e4609184043c01455007240c204d00c000c04249105021080c1001e0007c01c94440054400d03a6070000040c03118005806030301602c0d90010040d0000d0a441103804c90240d0743c040b8010251f03120700403003440105034070654846410700480d5441705041107203421001c03904421220248010b42c0b809100440000c3c910314000d40000e4080e01405031a070600d0000c1604201000c1c1c0740034840c0d44100140d60b070682f2424143e41c944480c0a40090300c0350a1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 49795291 1250 49794041 49794047
    0x120a02040308040b070c0e070203040e0c0408120714031306110114150405010f050306180124030506090106060e040f020417030301080d0509010903060b010c020d060608120708040b0a 80
    0x2035508002c010707041c00302d004180d48074600080d0006034000d00c50448a69a1441041103e00050b02d030500160410031090062842e5458aa42c200a561424524150341ca00c10507040200d01803089903890b1000031501c3c180042c0e138401c0811010b54401540c40c1c00300c00030030381420a80b14801d0106100300c1d050032020981080d4002c0e4114150800c4441c400c0c5400c41c004484400c15240300c40c410381c9428004101c0081010090080d2007010b402440b181d1241c42c0f0f01c00201158903c0324070f09648549007402200c070b440001d8038450b200e030700314102040e00307600d005407c0510080a00440d07a1410700c0803c1455848800b03100c1919083d540041d2400800210740007a1040e80c20910650126803034410300703060004011812150204152540350200420864071849103602c4640040c3d01c0c00d8060001c52010b50010a0154050402000a41035035003c24010425140c00b5500c250752012308121455003804002150f01d0390700300d02458511156a4004140501e00031810300030000b14103c0200c80c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 49796541 1250 49795291 49795297
    0x10030617070f171c02060a0e0102090603060909120703050a080604052e05120f010606020a03120209040209040507080108010b0a06090e0c090303040b04080705120d0e041811030c15120a02 82
    0x1e404002c404d000c000d50704040e41d42c05058034090700c4149032050f0404400d0040c400e0750340080e030042c1722a16581350312007000b1400e400505041900e000d012007900c0342e11a08001032050612030703103d40392030701c04144010b8001d1070000c212901450820007005000b0f03890a020205030400b1002040600c07460702e6070300d242e5038030a400054000850480e180d00c1c0f070800107010910050820002d110868403010120707191040d1079001004150049120040c480da150060000240c01400050504a80100140698800b0780714040462003202c010b00c00d42c4028041e0051100068440c0c004c8a0300e0100c00030309140503803084440f001845c80100b061401304000f100c0032403100600301e907101c40c1c650100400c1644184a0342c01b0307070303c078240300001c0ba401c01c0c0c0c07165108082c075540540350445008005443c0c03842c90482e481d0b40540e4411504001070407210a10300114018502082586451410b0500c0c18402c0544280710b1031380d5224060084c2a40700c1201c607042d02c2e00c840e20000d80c650f1101540a40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 49797791 1250 49796541 49796563
    0xa1d06061e04060314060c090108010b0901260a06060e0105070b060a08070e180c011e021501081e060606091207090f1b03060812160210030617070f17 66
    0x240c20b007072000041c0701902c410850485c0c401c00c1a110030b9207038021076800903c0f4114019000c0b80010780101303c402a0302014000c1c20300107050288030032098060310220700c100000744d00101c04801007403000030300c000d1249002910040c2441c1000010071000030f000c40c024081c000303041c640740dd400510940c4039114260b000307002d5281160901070700e502002408035401c651050300c01c80d800e0b0ba222591f202c00940d43c2d9070400c06031203400c84034103201d024010500d41d440c14141036201d0a1550000f01514011184c0200043d2000e002c08a5030444681c0b01401960120340440e4406800e014056550008880752650100c440101104440c0601424000664000751244e4a07000e10707030315540301742e40054102003c1141500c4440509240c181c040310207500850035540d00040c40c3c224000b50000040608d81821020001c00744125400103e2840f102c4c1d29140c000707500c07650200321203845000200d04c070481210182010908062440003c00d94511030008580880e80c0c144200d89020310487d1307041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 49799041 1250 49797791 49797799
    0x20d0b090a1d010606090302040903030b0d0302010b0f150909090a1208040b070804050615030102130f06021204080a060c03020f0307030b010e010207030c0b09011106010801050a1d06061e 82
    0x140c40d007080c0c01c10040c6040a65080030741c5003100d840044003010311034281642c656460314541c42d41141c00b4400240095007046003071590360041d0207007543d205511120014070070341c008a030711070002c004c2c4440f1180220266000307410414036144800d641c4400d49400090a40344104180d48040c883d501d850310810002d040a0700d0071a407000c0a9a0000760b442c070490183c2c0d0b9610040c0c0724280308072031126049401526a400030b2011414803e00102d002501c07540060000d8180001a5401d00c131001032a80400400322086034104010341c0c05009188408419903d074500301850084410b4540000701c1d030050500741e45002e4149058000e6065490f0344d030710302214503100d26220700090014502c804080b80800d044150100c030325032001400c1800d40c1d5201c40745080b0030b0b2a0484c4100280c000902e6103040c802550519403a1010030850207000f402c1210020800d42810a043e02c11034031807010400888034016000b0001240001d4416001a01030303070318946954801d60110b045880301c0200301c1d80 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 49800291 1250 49799041 49799059
    0x1091a090c0304061401120f02040b030f0601030605070305040f030c030903080c0a0605010503060709030b04111002070e1b09062b0c12020301080a0b040c1e06030e0f060a020d0b 78
    0x1ca800320301441c82503114104c1003180fa1108840d110348440301348505c080400901070102c0000d0401440341940c288040c00226a14980400190038030034101d94007042c1d544a0001001400000d004582d0050b01c181800c014504203074950390903039900584090706106035100340ca41014072070841c442c000d40c0c114045588400440c84680e40710381042c4820740d200c0e4208400070035240b80100702d25000319425242d030310700f540c41c1d030303403100d1912000078001d4a201c0700311b18200e001038541071604421109507a0251059908005c069003810f0406070080709200001104c443d884514081181e2a20342e0403540ba50b250300100304011420590b140c000304480342c10411141e0290aa0f410035200381c071060b11861064882139103102c04a02007481030300065031200b400f003408a116840303482d400900640c401d03451540c8621004804400321480d001c0c00715940d18080008503454800c0c00051324825000d0110001401400e07690740801401522800c2c1e40083c04e0078140f8070591007001d50880140000c00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 49801541 1250 49800291 49800301
    0x30307050c060a0507120f020403060203040506061207080d0e0d0c080120030c070816050105280207151a0a0305030a110d0c0f02040207021e010908030c0601091a09 72
    0x40550042200c0444030b108180c0031840c000690b00400344a80815540d108562801641c040d000e800203d007880e0b021a4200408400318601c0c0c002140f040f4012001001c0d641001c03002d00440d245400c080310b8280c1c00100701030000840c007290002411000d460185480080b500000d1203581340260002c004804000380000c0381700040d04111a00b945a1400018000b0480c1e032160007803008640300c081400082002500140d650070241841c1c450312011518074480320b903201ca086a50681d0303200b2290403080e2004020004c144105001e01c040a941541400255039805001900111442c1c0c3c1e5075031a4a40440d65003070030221f0784d2040c84020505810340d5600d050094482c0c0c00894080001910b5002d2210345040c000780b03038003c052035540c40e110b103004243c0314107280e103501880890307104c0e400300b00010160390b0b03c0c01021079080101006c400002d1326100003510300450b560100c000c0350024090302c2d0f031400b40401e10078112410124081451144500741c3c40603c40030135180c075400903082045c01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 49802791 1250 49801541 49801547
    0x51c0b13050103110d0203151f080705040b0609060306150d0f0b090105030109030210020a051303030e03060708012603040e0106051e072a0b0408010c08010909080f0f0903030307 78
    0x181c12039000c0c00586a007081340009008160814610194050384000010040740b44508811071f80b0100d049187d883c41e0320f102e002e100f4400120750100c0d040368001201404075250905c101a000e103011640103140c281040702003091800020b0010f0320a042c80c02266858084500031240400500d4604120a103480601c1d040200300840e1001e008688240022800d82414424950240d4154000b020312801c01407011002e98041c0100008000040c00341c024008003081410000d1840790701c03900707440b40046050601c0c04da0000c048004101d1042c0c0108815441c101d0028440c5c0d00480030041c40b01944600240313940b0a0340e00050b0f04008040000500340e6114002d0034807070014061152604400c042e00381064012024044d10b0710660701d4407164480c040e4070760315a800300c048407040341c440c3d40c0c1e01408070301e50040e5110030385694454012045643d8480326240c09494245410000e01c00e16032030346059801031501d012030204000403a1042d88248000351401510018102c0e41e59140c000c03401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 49804041 1250 49802791 49802801
    0x90d02060d02071b06050f0a02031908072304140d050303040b01050315040818040e06070207060e04050c07030507020105040314070608070f0c02010518090a0209030f0607051c0b13 79
    0x591306008078504004840180e030054200f100c10b0390b5076240c100b143c1c040c207940300342c4c2c010250403007035110030001d441c5058110102035501c0c1c0c8054135201100c0c0340c003041c00f5001c00054100c0802ea0440a01e03c142840c1d0382c00242c0303040c1c540f4010500d41c041010340c042204e09000c50400703002440007008000c100301c040d1840606890058080d01c00c3c20450a55142c4030b8481950020b108602c01d000b840785107050351440c02880301004001080f030b070207188000d5091100596100f00160400701003840302c5030700304880090301801514100f00501d000d40c0103002500800500070b0402c2400070745501560310503410750b0041d642021044811003034084540d40e03074812a101d0341000c00c03226000910020300a24540a11250980b81c00ea20384081d6401114036038003205046a40c450b00703040e106010b407124000c0a10458001d4801a80c44580d6001c261500902ca41119103d503c03240070007004a0b8840180d901c4200400404265401d004213403001404001100c6074002070703c002c0800003840c06800c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 49805291 1250 49804041 49804043
    0x70804080303060a150215060a03020909160b070b0a09030e060c010516091d09120a110106080a05151504050c09190f050d110a030503070605090c15090d02060d0207 72
    0x60301c00f0341a03443c00010000181005d010740960020341c005121030000390105030340224003c05500d1015100d5000035180ca40684801105a00480c107a03090002a203a401024044124604d400c0104554407080e00c064001c04002c020f9031260400000c040c010404140c09032070060403a6110100100414000d0004442c40c80c8080d03261035010402038010a01c2d0810358540c1d4086101c10820502c15019805c800381035059207110302420341c0507203030404010745021348242d5601c0301c0329a0440d18041c00c0d50703d0742d000001541c0240c0c4100001640028a00111007040b03070700e0400320342d500c1c178009440340d2000311040d40090400042140c01c00c580002460807020485002d10f10145101404860014a00400e03d5001c00300344144403078500241800c140c0c070711945d000083e80e4051000310b44148000d600480301c95001041140070000c03140641c130340c8040c500c0000c008002c007100c00201145034145a915100c8800a01c200d02c0fa00c0c0e900307003c100640c0141c07500b591109007503000b0009502c0000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 49806541 1250 49805291 49805299
    0x403060c1d040603020d06020319060f061403160c03050702060d140a0c05160503040503010606020f100516030e030d0518010e01020f0304060b190303020a060e031309020f07080408030306 82
    0xc01c601c070914161140d04107490f006001d0b8000042d541da1404000d500c0030b4038084035200c4041c00f1140c8a0000d0013040064404840320307001191600001038840c86a0000f0752100c0c0d0b00500812180c0c01c1442007106052400789409108906107040995440c454620081c0d00544009600b140d0304006800c00b42000b0011000c0804a5481e42d62007021610400c8109001600400078030b041000b52400303c5180c0d81c0614207603407809035107c0000c0c3c00c48840d5441400960000032401c5071b0a0300510554449200e00c04081c0201c1c9803184156140485101c0810b0615641c0c8003403104142c010400e0765081034038078008100c0390528040c1e0803040140452040c100d0740c00c040c0b0500c900003041c020786580407070b0fa00c48a030641d00c40380e503540041c1c1686101d061f0072035005171f807009581400940c03500c011800383d006046801001d007450760649189030b0182c0700d1a03004004082c003964054110f501111600000140c6407800c50b5102542440384c224043c101510200d00428080c001000450045208417 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 49807791 1250 49806541 49806587
    0x5030301060908030c0d0e0a080708070302040509060702120a0302040b12090c1503011415030a021908041109040303020d0204030510060603110f030901060e16020d0809120903030403060c 82
    0x1100310366901c252810400317590804c64031020018029150104044d2000b0581c441480d200c104803850081d031544003c075075501c68101001941000e2040c640c01c02500340107440540703800000603655180e040588100c1d20400108080094440d90541e80544030007891139075036907401480010900700684078601c2c2c0d4044c1003103048062400719005181d01144044480c10b40e841c0901c4594918648040035800c03079800d91461103207541c0c8000540c45914003170b0005840700000c901c1c607940f034007001240c003003440614010b100200f100c01e4500740d03d4000c01c440c000542e944501d42240640142c1040c8035030140042004000c10101140306005044840030030000c0755510101213041d50361140c68001000d1042007541c0f440c0000400031580312001030008100241d0390400044d41081c111000754200d030302e01c0d54040703003e82d044c8003281c0b1568841c0740510603420902040c03502d40c1240310b002d50403070b4000140003c2a850038030940d40250740001003007090400d040009041006811f007203886e09040300c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 49809041 1250 49807791 49807799
    0x6041503060b1f0e040225030f080604090803060d050106080706050915040b031311030304030606091a010509120a02090103030c030801060804050c04020a030f06080c040c080906060103090816050303010609 90
    0x6222154682c210350f503898980a2a84040c04007c0d0b0142c0041c0e031050044010300180d012020100b40e00040c82a07582c940c40300848840100340d00000b4107042d101d00d0030702540c00045244441904c2d080502125800600181c62410038014101a4840d1902d4080e00e40c0002e03945802c01c0c0688090101a00c01403210540d42d01c02d01101c0c40341340151100030700f0620208042c00c41340742c0340c4002c80d84140c04003c03c803003200d0002441c48d00198000c840d280c1c1c40b0300080c0402c00c02c9002d040c99000b0400500c031042600c0c42c0c0041c0141c0070345000c850180d100070f1f4000707620400030480101c030260050602e001c5544c40703003801404240c00580a802142e0160300000d1428401e100c4ac074401c41e040000b41100f0381c1c0c04c01c1000085e62100c01100c0c10140c4441441d41c00310018441d0400901d8404024030402151724103010640d0076007a8100240310140040104082d40483e0159003c502441c00107000c6282e8a4a002d03907000b0ba641d0510002c51040304a010010000000d41c10b8504540703443e8001039031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 49810291 1250 49809041 49809079
    0x40b0703090c0f0510021606050a02070905010b07021002010903020d0302031e0108060603010b03070608070c03050903030d09020a0503010b090613061a04050102010501240305091906060e07030603051506041503060b 94
    0x1f040d0300044910031000003c01105100c0c0700608100308041c03042d00c040654504d10f14081c0c1d0001c2c0c2121040550000b0120210301c2c0c46104421005171900080c88000c142d614041d4480e55200d0f80c110600d0b400200282c000b00c40b261011050002c90706942920356100c48000750343d9101280c10b907020750303e812640d140324900000c1c0c030001c440031a03031000b50b00e40c2d5000703048a0380d4615203003c8062010601c180074280e6030600181ca5a0b00d50f8a0300090404442e0040107070040c51039200c28041d900d0100d509200d84c46071000e050340002c0523102001180f00002c402e4001307000396489031101d10304615180b00b03c42c1240e8000d10481e0401da009102d2a44c0300d048911034042000f03480c50003406000a05a41035009421080c0d0060342e50080c0c640441096072070f4160449400c904840c9140d40344000e01c006c4c4810107100f40c024102c5e1174100881c5086650b8240c0d03401c8607401441003400900001066650b95030088800b074440c00d20034400050f0f6a15042014040c98031740b052040c01d03500218084520 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 49811541 1250 49810291 49810303
    0xb18040203101809020a030506091501080d0c05100203010f1706010506090d1110050406020f01050601090e0411040f090201030b041a0f06190e0a0609050306040b0703090c0f051002 79
    0xc102802c034020507240039210030080840c01c50b01507074280c80c2c450400c0580c0e50208114015405080501500d2805989080c18440d0309258550322001e018014003040c5e44c000b8484421410320304060444101c0c504289181130003141c1e400ca00a8000000072400042c01c1d0703500011190140d00030119207031000706194a03980c3c00d00a89400c00800c0c0f081c0205440c1850f884602340c0e01481d90f40301c080c0301200c040b8140780501c00024012810028042003010b44c10440d096a065400c0d008000c0c074181500028805800e5118803031001d114000800c0c1071240d95507542c2c0f2000001401005898040200d101c081d0000c071209a01207450907900c421181814040c401c0051100c010149001740b02c0130800c900c0214800e07070355801c000c0c103110540c0c00110644594040d4445a01c1c5c0c1808000020100050301e0f01c5074208404003d0041010041a280082c00a42080d40301e0503044c21a80c4082e0120002c003205800541806c5125200041d01c142c8a58250280e031820368213185c1403202040b0580c2c2d60a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 49812791 1250 49811541 49811551
    0x20f01020a020c0d060b0a0902090324040b0910061e0602060415020a110307112103040605030c07050d090e0109061d0601021c1107051005190909060b18040203 70
    0x20700240d400c8655482c103928140d5007281704a00004071903400034003240e214015a001407441c10b9000846038101c0c1f80403c60001300070210250128140e0300120441005040580014150f04c1c0e00380104042030802e220244031515507030010403001e50380d581c0f000b00d20289120040403190303c06401180051001ca4500e11603604015056044002182e81c01c00a500c810078480800c11a0003000c14980350274002000c405000e140c2e1042d181428004000f00c210389490350ba404082c43c941c075061030300303000701c150b4085640f40d0031701035140d84e0340032221000e038415442c0003442401281000520140c0000c1c0c0d603010343d0b402c0140359041c0da80f41d84110003124050700404402c0705d440708054071035071044498264001c1042c415550064054500b8941960521140c1404101440389588a054040104034010001180d0740c00451640fa680034100f0b1140ca0a418411070003201c034514494002c0a880d0020260f90004000b040c0c0d503820440860b4010401d00d0b407020107104c0c40d100345403401c0e00a4034040c07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 49814041 1250 49812791 49812793
    0x30f151103010b18010521040606091415191d010503010e030d02070611120f090c0904030f0c051e07090b0105030f130203120d0c0801060e01050a0207080f07030201020f01020a02 78
    0xc07084c2d211107001d03860004040a0304116040040003000c150041180303810b004018034480315800c2c103203088026100c1f55004084441e1400302c50708415505441c106401c0a01f2101c864020401e241c08550803203e071041c418078a80f03111200007209600c04a0300d540c80d40080d9525612640c88008150a9440e6041030a846602c10b104000c0c4039085640200045413007600c0011312040c1621040300c15802480c1c152150a01400400451012100500e41e0000154026100006c0e1041c0054100d400c060005410404204c070384200240c0203a84801e0f40c80c1c2c004048070b80c19000d0b4034921000b42910030107644103004030980042c000b03c0074002c100050f001615168195555601402c2c00e0110091101c2d04654090140c4000b680303040c13000303490701e10308849187d44c0c0d150070051440903101c01d0790707040f0104102140104040c03580070300000700002c1e0034a401a901d0b080040f04030b140600701e807c00512405144c081c2ca00003000001c42e03400701e9100303800b42d58a81a400c60302c28203c0c050140f0407009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 49815291 1250 49814041 49814047
    0x60405070504090c051207030204030c060212040b07050c030f0d0e01090503031b10020c01050f060d111012020415020609030705060a0b0406030f0b07090b070c14010207030f151103010b 81
    0x1443c03500103c1140c512880c2141c20080440e407643e600f20301c00e840501c00f0035070004050040c02681c01c800c40150007107000a2415682d64880c000e42c5200b544201d8010b0b030800701d10002000390501c01000010402811074580d0191801034545a29075002c094001c100c0135201e54415502a0a00c18110f440027006142000004840800420800e0449080b9400742d440450050042d6101801840f100300c000000c8078a09850045c0c4020800340c02c0e01c0c400c000c86400d0000080f100700c40b010541406885446a54055090179940c469400341a000714130700100303001ca42c1d07100740c038200c40d1001c00d0340c0e08071070b940e486000300d09443c1e20410724043d006802c40c10000b0300d2654560000c03400070001500004066541c1c0c0c607481d40d10303420110200c0d10342451000b884403031680800d00d0400341118803650342c941145d41d86c8600f480d0541f4450070100c2008001c0c1490b241c0e001780200ca00440e0026081280341915180ca010b4082c000700c88130303600f203141c0002c1c041d1a00c1c212042d0b0b4181d514030341160703107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 49816541 1250 49815291 49815299
    0xd0c080607141b0f0a05030d0b040e030a141b010b0907140a081003060606030203060108160c0b040f0210080f0c03040308060d0212030c160905070903021207080d0c0506060405070504 80
    0x240d07480c0c042403410003403184414038410344d0000c0142200d45800b94000d5621107281c1c209041c140e03440526140c0c4250b061054405038880088229503520b030716030400c401940030240100b480d40c0120b0306900c1032007210300c140701802401900f0200c00f4003001c94003446603540780304041c3c230044840703a400004080c05210124605004100d5190002c040c04a915000359503030b0f980c00141c6103513401540c00207402209000c040d5070058801d0350845001c4402512004911100900302144c0c420007601004810002c1402e0058100e150810030350081e0009a000c544000040d042b00b50599481100d503240c000041c00355580e03007040c2c0b4000c42c0d240da107a410031b8070f900d020019001c05010082c0d07442140344607000202d02041008111040070301001c0d0586034403c3c2c413500c503a0704107a071215401c03e080c8070030000040e0303106c44141d09481d0b0480e82c40d0491103000b1880303890000590848509885807101c00d4513035941004500c034020344590121422a51040140015035005440c800c010030300a00c4180 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 49817791 1250 49816541 49816567
    0x203010e010b0a02030c060c27060d0b010306051f1205041205091915090501020106030c050d050709050705030a0b030a030804060203150405040c030b010b040b091c020d0c08060714 79
    0x2651403c0e441220f00301111600c0761800d003502901d10440401c0700150f050001021181d20085c50201c000c9608005116000424000d11590404000081e130b038415080031a07002ea0f1000c809800c001d0581403c02d2a03030230343d10310103641400d2017a01055404004461950160080602c2594071100c409014140c4001c1520319402035080303590300400c41710301800e114003503818400060010b603101c0161340c0c449001c00741c102e84881d0041030440e41450000c0c00407070801d80101c1304a410540d04030100c11300741d061103403c1010580150720303100d0905060100c51075110300a14015012504200b109400710b404060380c0d44400c03000200420a41c000081c0401c9040d4051a400540901000001014840002c048030b00c04c1720704a660184140e001e00521290210007400751402211092400c0d003822100300d200d0151107220782c8140305201c1c0300d502d0285503010400041e0b40c06014520a801a49054000030345103000e807031054440c0d0b40000765064418008490410000070405191546158201d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 49819041 1250 49817791 49817797
    0xc0115120b040c0e09010b0111010b062a03070b010609050103060303020d0c03090812071a06180601050d141603021608070602190f0801060c021f02150a090b09010203010e010b 77
    0x140d40045002c0d40000e01c002e10114500d20407105c007000000c03420007401c0054992014031074040c9113a85000118059a207413402140c402100e04070004120100c5082e0180344c5c103801012030340e0240004102c000406c800680000c0c1a00c030144ca030740d1056500d800044080303c15a120240050b44244144a003442c010950128118001d20340a01096283d0b0006031400c030340d41d031512030002c00004600080c0120348031015450204620700b24518100600040c2216561170700100e1190707103d0010030801e82c0100c0440340d0401030001d040c4002e030041941524500003c440c40401044580e0f00700b62007038424400c42c0c165140500c580101c012264607030400c150012102112050b508021840206142c400124000b00b019611045c81c20013900c4014031865060703002d0018040c18903096001665010003007803400c01c2512100c44107d0905008070f10741200110f0003007110600030188038104110b0703008114080d0060003020810744505061a0807403009103d42e5014802242c0103100c450028001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 49820147 1106 49819041 49819043
    0x30f0705040b1203070201050c0c0a15020c0904032a0f05031e0a050702120a1713060801080c010f02070f0e010315090b0f070917030c0115120b04 64
    0x14603130341c1c000c00c14000e0510101040700f4800f18810858101c15000c01081c050189a0b20510794080710452040c490040c05610071410480c1000d51030140281e500d542c8202c10b140c024507401180c175940c40d00700c84410b610143c3e2080415030020320984440d0040c0d016503030303c2e16032003241925212909100d03800250f0a000c0314801c103400c01c0c240d805140e01900c40d0f218417001e01d401581000203040008240c0003070852507040c98015a0003402d07442c02c032042440c2c0781c541c896105940c4600244213a201d16400107213006074951282501544942d2280111a0903988914404042040c02d800c080c0d41032003090f004005100710866148207010304e0321402c025080540c2c03161061540b00400754140c6000a0740410040c510581211004007241101154400c800b00d0174603860794429005480340b582040184503403000307000b854100711440d42c090500380d00d151f56950042010b000b00 = true := by decide +kernel

theorem cover : BRFrame.Cov 49640291 49820147 := by
  have h0 := BRFrame.cov_init 49640291
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49640291 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 49640291 ≤ n) (h2 : n < 49820147) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
