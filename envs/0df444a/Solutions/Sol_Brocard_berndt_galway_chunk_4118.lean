-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4118
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:37:10.676324+00:00
-- url     : https://prove2.me/submissions/14036ea4-410d-432b-b280-83d7d8dbafb1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 740467625 ≤ n < 740647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 740468875 1250 740467625 740467687
    0x603060d080a02070f1a09120f0106080a1401020406020c060f0702130f1b0f050d1103010303090e01060c0809040506030c040e010615180501181d0a110c12 68
    0x90b000103580e501803401101005031910000140c851859038034000e10660180065007003103540360601c0045002a842c0d944203007c2c1c00a00041301900740301c6c40c002400920010032171201241043c00c0810403032101d0018a0f40100300610255800041d203185c80801030303d4950ba41c2015422080301806100c4000794006014801d80d160071184d074000300e80780340d000d02041001c942402c003000741200c245013455020400340303414828000c0c014405000840500480800c407005003180750707c00c542c4244c00440101e049220b09000c0608003000543c0508454148480405180e459400c2103020701d01260340300342e4451000401c0d03600d0902c151303080c4a43c040c0c81400910540301c105030213024603000d00d084038229009070b6000c0c0da11038183c5108103e02c10031084070090900c0c00456582d80c4200410003c2030402000052107044440d0700f603071a001c0280040024145070710384505443c15951401c0e1004014012003c0b94100499802c04403091034081c0e6079030701f0080d49000840c43c403608044001200b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 740470125 1250 740468875 740468887
    0x102030c19020f0913020906040b04050c0a0e100c080f0412030e0405060d0309260d030902360907080706030f0501050123090607060203011d240603060d08 68
    0xe9014085078a10310072180c46812903001002e11a42600850f844c0c84051801441031002d42003209900350000809840400c0b09031070800454103892050b580084050800588801c181d41d10041c202d03240781e02281c00266600e1184001008240c210314050094100003860b240398903e041c04642c000c068222080408040c20b04015110240050605000350f00700310000c1d98920b070914002c04841c2d41f580315006d034182041c072031412949054034404030300240003101c10700d0050100321000001d12190340c007007006001d500c10702000700300100a0305140b20341c01c1c240540340c00c01034003640c1d44603502c00f040c450a503039901d44181c540740c0581d11011090180d135201060300c40c3c0c0340e00101c0201d5032141c0c050050303981e110011201590803083d1108035414410040100c4034010300280b0b1903031402007815045c2007860315140100c0e442a88030307645000c01000b100000301340045160354804024200000301c0c02c40188034000140407400707450720440d8008005119036450a45e44d40103980c02900146c1c840c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 740471375 1250 740470125 740470153
    0x30b04090503032e210807080309150103211404080a050c100207050607030e0603010b040806060f0319030504181d0106080c0d081b1b0f090f060102030c 67
    0x1520503a00944841d10740507410240042243c0c0101d044d000e126500503c140c50000ca400d9814100042003101002c0d100d0302c240412071201c00b90980d00c0c0511000740d5039040501c401b9280151410703503541c070800024010004184200c906441c42e59064154020b05850070714100d0701504107078041200b207440481c1c00300d9035103000a80b580000d4030031000c450040201c1420010854407080d0b9680060f0b111400030700541c01c05401404d03000d8840d04140c6125000b4500080b556007098000e09100c407800704013049504c4082020580141003514030440c1d0741b03071020202c4d031a100041118080b01c80c181c000001010701c07500031500100340d502c60f0254a10705040c9024068001255117903500460700814002d07540042c4a01c40441b26498011700608a0306424405901d101e010180c610950a01094500301c6000c108640b82c000000301070103100070640b105003100007007034144c1c502803609882210b4084d100c00000c1c6402c00640d44150505d5903c14004178594800c1e034203524694060201040418 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 740472625 1250 740471375 740471377
    0x110906120105240301110405120f0706032703120203060112050a09030201150605030118020405040903030c1d0a0e060d1a040c051005090d14011404060b0d0309030b0601030b04090503 80
    0xc000700d1016006400000e204240c00c0c0c4071b01501001803032200704010021441c040c6040201a4003da00b52032103050079030000c03420050b2550004000ca43c40d13401801c201030440103007a0422059501c10107500e00c82c0d4400801141103650840181a030020104280c0e80c0190402d2038009003040050100745402c03010103010f030007040d408401541c240800380500300303000000d40303042c1d0b0019500c9a095030720301f034201d10b0802035018144010341d9007000041a541c031640203200186003c0d0b100410000460f180060001241403404551500c03a20300703c3d282980c0d11704120007243c1d4a51615180e507180c480014415a04001000f0181440004403540a000d9000178500c00e0340105008046a40d6410522014400c940708100000e001003041d14007515000043e0340704540034011182440c0d00d20101a82103071000440c1d201c62501100422081084c140600d80e8042c1054070810301c944020394001d07101c00450300004240c9880a800100507910990011140310381c020b00a0118144909261343c50f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 740473875 1250 740472625 740472661
    0xf060911210405060f0a321f031103031312111921410a3905030105090106080c0d0201091a1312110906120105 49
    0x565494030305048441011250700c0c030680d08103002d480759a5900d0302c900080c28008060310041c90340d966800102a81a0404c030f040c00c0c0c80503200f41e0000d03407210b00040c3d003002c000340030130841a41004a0707207004075207083d000100ca41c0710014010b0b0b0960003000030b086003e10740c0e071184007000404001800d040024040ba80040c003c2d80c004c0e0030304002000380120007071100600402c482c071905007000b0401c1c89034008406003d5040100628000c0d43e41c40c0303481000c600b0692124215058108030b1036000303100c0310000d2440c0f240510340d000e202c04500d26403900d508804c0500084103101008600403800d800c01c040c400543c8501e0110f03006020222010750a1500a4030b009610300300000b036036400f051003a03030305a951300c0c0c0091101c03052400c20802d40140100c000c0b41045040b1000161076440940c00c84c52030000050020f4940044902c1701902d4100c56000801614441007001c0100e034032050b0f400001a82662451074503601c240104640076021a01c06030250310700001c0107600c1e4505c0f204400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 740475125 1250 740473875 740473897
    0x509040f120f080c0703020a0f0503030603120415111006030b0403080c130e1302120c15070b0a0f1d0d0e030a02090a050603240613020415030f060911 66
    0x3041c80200d5030480d034030342c2d1942c040004580440042000140c241010f014014441d00c102c0391132004954891546103034422003141d1550010040c0191480c041c001031050040701c010b070710705080c41c00c01d0703948481000380100010f001c1c80150040401c0010300200c080024540b1044c07000c3c507641d107440100d1090881d0b0550024031f0f0b40c00400c0840602d602241c6075074020001001002d13060480c507030041100540900c01400d642c81d14040140c591612554210801c0d401404902c2c4a00b400c0c0000b02c0740003246440103c008011100004140001d01e03600014840000a00c42d02c851204c9801420b20700043d600d54681035510900c9031b0000100095070342c805075182a121a4294141540d0304c6198a000354064050b0300041c5031040150f1140b03500c10720013000c940c03020103054001c80007031039a004100500081c03401080864203207800e84009100c044030045240600d0b0030074400c2c4202c402411a01015143d00c03020802c01c4c9250060000350602c810100140e18051482a40035801210f00c0a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 740476375 1250 740475125 740475143
    0x11d060a05161d061608070605060f0a0312300c02120d050447040c050111070308031303030b0a0f05090912040303030203070e03062a040509040f 64
    0x35141c8201080484091580c3c1e100c52207100c0c42c0d00403502c000304083c041640c0110090009180b1801d01211444180303001c0d2011694801d035508012066403002000703030b03008407410461000306031101a000e01c1169000101c035440f810341701000b16041240c0e090715007000910907440d13503840b2031900a0003480f07412030b510030090302c0300d6200181d0b1107254407420445c8509041c4900010502079821482d805403142c0110340900c0300080c2c204900c1400420024010000d184d108240c00c600700c8008001050031960b007451368501607540e410104014001c0a040081c007901c220030120301002481e018542c8100a1a2a03280400f080441c01c80100c2040c1c0000b81400c10300c3c40c2d02d080c070034100b100391041245500d81550602c0180300e007a000103883c5680078850484800f8003c8004c4000c0c0010310f00c2607501503a00d0409440042005654a07055031003504084188201c2d1280080d05119001142e0038070640b40150100c0240d9031f000b142d10860300562050304020400a500d6080450345100351402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 740477625 1250 740476375 740476381
    0x614030a0227120f0d0f0c1703040c0608010305100e240601230301050918030c0d110c100305091e0706090b032202130c1107060c030e090603011d060a05 67
    0x5103a0750b0b0613030381162009030801d41072501032520401a8510031040b0341044102c130405980d50180d04801308d4070a0318008004014001013160400920b4002d0942c0e03d00302d0b00c29411070b11020780300d410000640c044c1d15903880e542d550181d0244450082820043c4503202c0910301218001e620301c1c8112070150001e03444403801c81c060001028644000190424014156821b20040c0840c1c0760000e840951207015080d10400a001e040004001d0361030401c0c064100f540600740060840384280030340c102542c120b40b03528500340e11514143c6d031104940b0b25020079281c5441440030705040079540584070280303800355420f01c820b10000340138007220340c0e0341d60302008960703034450702e141c6804151095048030807981d821000702d0342c0e0201d440c891180010804002500140c039a002116245107006000c02ea802c18554071080c0c041c0506c600a1180c0d0031300244807480b90750300401003100349505600c00c8480c0c2000c111103031401d6000f5080c0c0c8a403c1140c080c60340c1c00103000740c0d89510171100800c04904143c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 740478875 1250 740477625 740477659
    0x1020c030109050c120c0303030c0903010612030503040b04020103021902061b071205030a27050705030102090a0b0d060f06110c1503070503180607090f0b03010614030a0227 76
    0x11041c0c0c2d81d4024000e010030260420801440c002c1c944282210b91144038107100c1e0a58043c00114001c21100c205255a540214181030030350b1100d51000700b0b45621504c030303500400e4011003142e9220754004007a919582e41c41c40143c001703000300d1000700049040c02d6100300f082c1e60005015401000f0400b0016214113050784a95494420307000f008100994204e48030a405d401840a95048a10210042030f03640381201e003040320040c0c500d03030303144043c9403442c203d41800000e201c90b1000c0c2030140d0080d403903c1403007070100e01a080c1500c80c43c4041c0c0c0e0001860040701503a9401341000c0e1101da4980034503142e460382d004081c22500743e0760601900a41c203107007031140380c422411035401c600c81032100d0550342c80980503201c54000815840705003915007a00c1d80d0200d001d0003043e100b00c80c50b88503462400d041082a0360814460707045603220400405c0144212a00b08480410a409403020103a0b40d075600040d09020740210034012610841000f50007800c107881802350b540a0030190b600814101e099030b4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 740480125 1250 740478875 740478881
    0x10915060305191a090c06132d14130f09020108010b03040b0414031e0d061a090f2d04050603030313031b020d0c080c0a06020d0e151801020c0301 64
    0x21004041341007111810254220113003a140d48600b80c442a50480b13000840420640c1c0d20080103ea91840150001d021011003001000c5200205180074071450003242e071404102c405600920301114010801002e580d039480f100c40d18000c2c50b808003030200c0c5544c14401c902a103030003881240800d0603d000421210a0070090300e109507000340c004a115202c03501d40c0100740100c6215940180020003046035250040220b5003020005041c619070380311030300b1200d0b03c200d070303c50b070000e196062a00e0001c0c1c01c544124416a813181400300d0350000c100c9403e000041c11200240b000e5001c0d1502042000e080264644407003940c240240c40501c001c1d6039510804d13440b4801110080b107400740100041c0c004c01d104d2100e4950080305c040c0c0c4540e0078075864000405d200146002114090001101400100e005001c076502a0b01d06491501e0141e013003500194490220301105410020749195640c0d20b40d88421410380b81d00000000c4d981d035a016503030001420300111040798058402c503810b20015040501c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 740481375 1250 740480125 740480173
    0x4081501120f02130b19030201120b030a120309120801060f0918090203241501091a030c0d05010617010803030c0f0d022101090b0108040b1503010915060305 69
    0x1e41402c500b402c01d0b82000104440104901a665a40e140350140707911002e260305082c26000d250140007a00d50f1000410b042449914420a1800e1a0314014240c5000074010071456000160721410140503a0441c000d000c000e0014001c1010340d0008054150405039850581e081c82e0b9582070b501503403000a881403081807180c0c514141c21410f2640307040c0301d15400701c20700c2440282a10401d280e5860018172500c2204100d81d0801581d10510200c5e800004803031521005c2800c044000d54034007039540d001049204484c050200b000000a03826610380c000b03d0b581c100484000b0041941c448100070590004418050010300201c0004141c83e00c000040d244640c1030008403d1410100980c02d080030b4000d101f10a40c0641c00b0302482c0e110b8446500c028925240ea105515850742c501803440e03050764144941c06050202c0f01c030500c40421034100d00300d907001c034608181d102035a01d05008030f40100140300e0041e000140f5042d9041d07030380241d60044001c90380a60304490484d00c0a40c07034088032907068 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 740482625 1250 740481375 740481383
    0x190f0b07051c0209040e01050108150f011a0c0307060612020405101505070203070510030203060316060804080307170f07090515160213020f0703200607080c0f0408150112 75
    0x100c2c1c4140500b0b00c650000c0045030005407006c11000074112045081d90400e8015404642140034440d1141d441d0451055000003124411592545445020054840e200e5402c400d010400a03401c00c2c0500c0c1082100c0780c40d548120100480c954400c6940107641c40303503808030322685c00c06002c01d41000003101a10183d400321010349912803101d10055995900c00042207806000b041000281c2e540d40c02d2642e506a115a240507a80f450310074109424218549119214807124060900c50345500c0020303154085d5124400560b2921818019900100b01900ca5180c964990b001c1000d144024a065406581c4644501d10015150701c1002043c1c10988402c42107840148070150840350060a6030f140e45001a06984141c82405d01032341c01d90344178a0103001e55140c0007a011040651018401c030000b5045a2188c0308851041103994a544000e0045030403ca114000726400300c450004880c480c0d02d00700320556650b030fa41c03410a612038148401c0c40001d00c602c00000924001c2c54290b1801260b40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 740483875 1250 740482625 740482657
    0x3110f01020c01120906051015050c0307020603040c0905070f0e030f150c130603020a02070b03060f040c021c0804050124060f0e0a03050604020910050a03020d0203190f0b0705 77
    0x1c8900440c1c4101c40300039011103458461400002003001480b406000d000c0c0750a92011031403c000d0312001c00b18030300c040c0727a0410408014011a0900200544050540c12901030307651352900d0902102c00c030000e8010008003407410b814881400d400c1304c610202005c182d181d01034400b1200302015200c6200f1141600740b50007ca110420000d0703009800c0754401d105613802800e0404600010b00003240d150020004030307a0006081039000e0701001410020100000c209103103142c10f40c0400c1c0c40c04c1d41540018007854943e420032112600900080c00b100c0c1c02408400c05009c40514020280c8a094030300b95450351900c13591143c84c107907a003c03a20b15000d03240a2400a6131902c0700c116100000b1460000c1086154410580720b56103101c030303100c000c40c0108002c20150030140104800c00c10090000900318001d03240400554a0f0000204100c1c0d804a45809403400d890022a044c800e50303c80c1e00d4005c00b0b418514008000081c880c0c1c036511030044041d1466642c403400152070b5072048402010034684 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 740485125 1250 740483875 740483893
    0x51f18200f13150503040c08010c0e060c011e0b0901050409080a1d15042d06140d0207060518030310120807020409050f0c01021203010311010c0807060603110f0102 72
    0x807425004000c440e00b5286800709903542c480c281180b07925001c1060780080c50020501007440680e00c501406003012030020403c44c62540d8002c1c0a22410701c40300b900444011950b851600800e600503403001d144040361401400c542da030b02000500748a25401e00c1800d02000125240c20180309280c1c1d00c0e940880014546414518140c455504560f0308468003a0024011185a19003801000180c00d5548916071070780e040441c030150a030354199001003009903000b61740407103a03040300c00f507070440c0c5082c104140c5803040c0480185c694400d1310f055070b080c1800001d0180c00c10089610851260783d912440044607080c01c4040c68403403009179070760200000c8055040c0f0403000c95124024007030348039442c505d242549030780c00b0400780c1d5043d00c815112034014038080041d218040c400714010752004d201400813190071480c00e00c118001800058041c2103c40d00000c000c1e40103140010003075400403c072030b0311004e942c41c002000d4040d07400b045070000201d05144002c2d040c0050180304009050300a855403d03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 740486375 1250 740485125 740485147
    0x7091d0309060a1116031a060f01090501200a050a050607081302060a090e100f06050f040911071725050d120f0c030914120d051f1820 59
    0x7404000d020b8604d40070305610075039080300c0c0000002c0254821090303405268100b1110040810008002c0c50040d1040a6515450b0381e0111244050fa2800d0808010b80000ca8404900f01d1150610f4080f0b140f0a9902400501800191314503005115104a1702a50b88941c400c40d0079a8007940e512002d00d840d225901d005103000382c05080d0264280c41c1420b03201d940c42c07203c500f1410302a01d1034485604c0045040c851001e201080303e014260300d06200e072801c0003004200c04144510300c1a1004982d540c80d0484120b410003089034540c0e078015a2218031025620740c4c40a80360700081070b010315400904c07106a00c0007806941c1092458000c80a00341c002d4500d08243d4000a0400044a00d1980c4e80c0c0c040660320750501c60781f4410362880d5800260071103646400030301e40d0541c040c00050341d807206400c2c1050490381c80481c0c4071502c060038081340c1916645105c90b0012213941002000001080000c95082480104148800da1001c82031083e0014035641d45040904405c0394201d01b20108940100301c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 740487625 1250 740486375 740486387
    0x1061404090c1404140301060506030606071e080708030702010b010806180714030c04081504050d11030903030318010f060b040620030c010501030210110d0c03050c07091d0309060a 79
    0xc2403107030424801c2400c03c0650f12030a41d2107a004186001c070800103014050600340f1407003002e01f20580c1d40c00e285040c07001c0001c409010304100140460141c400c41c05031100c244000340c1149a006a105803902c10303510340048107410485240b00158030b485552040c80d1f1045008900070040071b400022130707a11840e2150f41c1044018008400d01c002003040c9581140c00754003c510038070104010366103903824981c4842c282030241c0d400c001d0b2404802e0034400414000720301244202c40d0f43c01e1040c0f245c0b00d00c030a82411806a400140d505000c044100203503004008000c443c1c0d00e403050020040500110300c20b0080b100c1c00c0c0030385080e5800500041c403080d8040c088442c2503a1584900010740c0141c1c0c0240351642d40301c40030000140e51a1001001103041c0f8061640806880b800c002410300c113492b5050340d1f034818031120b240400500c619203c0c01d050080c2d04039407030000708106a918aa84800700d1002070720054114402401c400c10381001c0308a000f2094400484005003018a0035800700000c80315 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 740488875 1250 740487625 740487641
    0x8070f080412180f0503010b06040e0c0a0207030b0c0405040b01020d020d0f0309080d0605150705030d181b08070602150a0c02120a0905132c100e150106140409 70
    0xb07001820603c032418600f140e407144010444403603101d0066003031800f1315080d0740c200e000c81e03802020140000d20030141c0f030004155111b40192005070310723464042422850007480350b0003e442901e0365030074400148110001441581d405075403d100b001c01c21801241e45211b2004c4200040e0482042e16070254492080b0100b070250515005c0740c1d00007240c40d02000ca0344459450071481d540d5100410440c101400780640c40c600404180341800320544886449109101c002ca2100d40d90348115503001c0d1000c00014030041d0030079400c4951035440803007541004528041c00801303200c2d99000040c0383e0303c001014280f04045044401241d01c80255080281c1810404807055000c1d00014040102103040540051609551186034207440e0405200c00c0392070340c1c030106103044d04010b81c250f42245807244010101e103116001c035200410b5109001e04043c905c280045049051081d10004400005002441240d10320110415a6a07a00e0241c0e410760414034034a0002200340010841c00341540d1100388 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 740490125 1250 740488875 740488877
    0x12402061f05031e0f0d12020706090807050105070e040e0307110d121d0a050f0d06090b0a020d0b270414031923030c0d0e100203040308070f080412 65
    0x1003001d45450000e800d01501084581c0150038034481c0c0402004c0400000281180c07840103018070310006c040051400f10003444449140e17400044034020041a40d010500c603580020b20345481c3d845905d049400b03403400352516000940d0844923100c075480c25204042d941c481c084020b601d404039503a00c1c0800c6601c00d07400f10b540706400a003e400031916000d10310001788a01e03620178504a8400080b56001414045024040d0702c0c10b070814003440e2110f051032203020344100d40d101d100204519041001d80348017400102181e002405201900d1060b40151641030000482880803600d41c9081c00010400b090746401e0300307411608010480d103141e0000c10340160051038040c0c83e1000211415203107600140f68000b00340d40500101d0500c0d80e00c94000b0380400a4510038605a00c500145544280006000b2103c4550b0000d800791703502c034103680101c1c0e1021160003a12040d4000c803507880c001350402c540540c0400d084c00001800c0301c2c840c2440349401486900d0702d080585a80d201c50b0803203148900303448 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 740491375 1250 740490125 740490181
    0x906040e0304120c05190608010612022a0d0c0c06050702060c0106031b0902030912130e0a020901030b03032d0c15041529010c1a01240206 61
    0x850f410601c141c1400039a80603074896140c0714035007000d000c801240402c26420301c10300b0003014401140e010245604442c42c0d8603020610041807034840009116400c0062002c0368007000709410050700b1030340f250900303541c141038400c0c891303080300d058034403450b0090300030249070071884188402801480034164150000d81071904250000080c24210b800340c2d00250364200e900c0f60240503a0904207440c0740035040c04c001c1076046003842c500b0b0030f54510b884105128086008a038040c50700114400306001441031900f0120f490130504201002503011141c450b000908040c5801c986d03040010458125080007400d01c440070b0009031894200c141a085442058601008590703940c04003080303050358040300040315030000d0516161072100d5a02c034102c0c8102d044c1c06c0001c00240045040c1076000046126482c1400c64004100129003034900c90600070000703413490f900708005426140180307050752000f0070800e5042c400032450f503030003906030222940164010b07070000b021598020901954043d0b140014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 740492625 1250 740491375 740491379
    0xb0a060f08030702150f070b0601050c012f0a08012102060c030c010507020c211e0d030f020306101d030d11160501050301050904031e27050906040e0304 67
    0xd0350400d042988510300c19030002c2516415403400900030003019131020b012a01e0803d251010100d0740c000c04d500988a8080f810002e2070070b0740150b040343c65002508008002580c41031440d240004002d01200152400c03146840005038054000ca907801c3c4c4090f115031405078a00100302c4914030740c0c0c4d041c104400c6c016148160041c0c607103e0140c6500502503002d551280040a481401c40d100180308104560150f020075442d41c407405a00000d000560207840034041e08809001d14002d280008003a402c030405c1640c00003000c0c04036004016150985e81070150303c0001802000f640070542d200c50b0701843c0b0042001c03815004103400005007140714a1000e0f101d02c4580064100680c481405010038641d42103100245400e0103844100301c003414140d44501c0c10280020a5070005014007030042c86200e010a007454081d10b0320340510400c0100e11a0b0038803006a00030720840c0c41c0c0303a01440031180c24030503e0564810500d640d0a403100a001e45a4541d540410000500f08614001020b40820080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 740493875 1250 740492625 740492639
    0x6040b0d09021021141816080106051c03020c040b03011404051b040608150702030412030e13140402061c060b04030b070804030f05030a18150f180b0a06 67
    0x44041c0042c3c42d03203461118041004940c2d50707111100302a103200c0c5182503032151441c1c291082c5107410220300d03405050140da8050380030b450100611032800c80c10005003c0001c8690054000380e050798000c0e5601000201d185d0b80030600c0b20035883c801405600900340001c29400c2580c401421004000c0021038040c40712244140b0750b10301603c023602c41390004560310b64800b007020f014034050042a1001c00c10b50380340c150056201d40758101c44005001c6640b0110715000d1081007618003030003000342254100c05281c9005840320004801b0280a014105040045540075200b070800700d00800003c3c40c1ca595a0340e08111203607004031407030300340d020303a251001d1b8541c1241d10070760002c1e007003a07009a6500c50031418920380b442c2000303190008001c550410003000980c02406603502c038140c0d0402a80729100d40b450340740034110000703d0b406c01d080101561024005402c2d1204484000201c00b0401c01000080180581707006601d080107000c404c2019400160a21081c2d5a02880b0180006001602d0b254 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 740495125 1250 740493875 740493889
    0x40305160b0105030105060109030c0308030619060306140616110102010e030a02010b0f03030f0f090d1a070809070602031615020c0a030801080d0905090402010c0b090d0305011406040b0d0902 84
    0x103030940d01c0401c0a4010b20a80c102489844d801000900b40062100d2550384e40101300205408028100c250201c0811215160748800101e140c0300303c80100032998940c40010001c10303042c8070310070303898031850088403040c201002111449100c49292241824240e11200d050034603200915045650f510b000c0083c980050007d44103a10495002080d01c03000c44040140b0000303078500c9188a900100302c0002d03029020802c03600d4510424003900d85420b040d4000030300d545540100a13000350400c00902c101031443d4000d0a00c00c0696499401d8192241040540e6031422801880d000da4810003200c0d01d00915010300c00c3c0014420304c001110070001c00d066909a82195a001e0340c0ca6101c544460105900310303801c280075088110042150704003407140148010068429617000352515404103056900c00c8a40c1642c1c25044441940a03060403000c06643e00750a403048000030b4500380c004508821106100d01ca20003005080310b0505d130500d0b03c880d00f141c0c00342c81207026240e600c0038000016150b41d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 740496375 1250 740495125 740495167
    0xc041a090112230a050c0405010809010e0613140a1509080405030f06010501120203090c1c02041a100804021f09270e06060310021c060b0315030a0b040209040305 71
    0x140e00c0c2684041010f40103548940c05894803000c0b5061000300048084041c042d00c046500901c2d06507c95241d1440403801000d0f25104a0400e004490800907034410003414000d10782d22802003c10340c2c3c3d140c400c51586071240d922005180585020399003e918003503812600071107011f4400103180c10794070000203250a10803070f000c0b402900140010401580c02041c80c15044152480661461030258925a00c8a40162070b85200da0349907007160181009051180b00350540c00340040024908898030a2101002c000c0f80c503100d0786480440340542403003034003c507009943c0070f0907445128008111a811400c010040401004440c060001c1e249034036060041002d0f008919030f17807454203c10740f4442959441c0a490800307500100500500c0d03140000d02140724030b0301c0d420058a591903039521300034503c0358000c0d003082203040c40d001107524011800114004c03580e01c0c4920559042040516071906441c44000d090480b80714001005420210880d96025201e0302e00705152880344800450010800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 740497625 1250 740496375 740496401
    0x1c020919080f0c0603071e0c0615050a120c03020d050a170c0c0d02030a0303051b0c1b0307030b1602031b010b12120f0d0b0a08150c041a090112 63
    0x40010740c2c189003002d1103041c04004040d030304c4510754503040101130f003100b6201d150514012990401d801140b4414089060900c3d406182801004032088841d0321f0740509001d401d02c1014508000644d00c0709280c80312840b0b41d48004003640c401d2958003000010b02010070140c45e80c3c013400054000245240d8869036000307206c0c1904984501c900035201d45031005141145018890300b88104016940020303603186c14a91501d00486c0550b00c0640b14429118580050b254686e0007040c0401891404120303028004210b80040c207800004070101640d49a040c800a8805a184004181000e85140351049510914012280b5000f00e0003424100508500e41c0100e0300e96569280041c0c91500640c0c45500614010007420301d00e40100140e0b07164400d200011218000001c1c0082450780d141e00484003030701004003100c1d141c55030b40200503298400142481c8064a121000030084100501554241c0d20101c00d0310440c11510880c40686500100c1d0060511180b03010442d900c0805e4028402c2074120 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 740498875 1250 740497625 740497633
    0x111101508012301050d0b130201030623041413031d03060c091305160f2601030b010902070302031608120109271e031404060e0108010602031c02091908 67
    0x110024883e4a050681240740300340768020320340c030110355112505a00f1405000030120001030f84c5c030050b00104101d5002d02400070f0140d002da160f0309080c0c801009001003e66081c80a5245651414900c074022929200103955000340035001c02c0c8103480711441415020440e000400f0014002807074000122106851902c00146030052400c0000380900e05440c03013a01405103040070301d001e01c1142d5158070f10504010780400c40582070342c8620015812021551850300c0f450808407180321107d00700b4003051320004603903000065a00380c80d1007291070240e003540c060340c1000586580301e01d145030490fa05858030081484404010030300034040d18000c03d000040003680e0385042c2200300400d496913203451441414012590041110558030f00618180f0100140030480d4500c0e05649007240007001801e00c070000b00d80880c5047e00607032203011040c4262581c6015a030b8801c401c82e03880c0301d0040c0020201c0d02070010140350044c5074000e0000c80c0001841902d080e0a80491400e150955034050312070350340 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 740500125 1250 740498875 740498921
    0x604080702490309050f0303040504061410090806060d0303110d0c08070c200d120c020a120320030d14010e0117060f0a1e05040b06011110150801 64
    0x2520464030703a40c5440520801e842e184644000c0d160b00010b10502d80120304110080d41c4a0741c0038030460703010307100040003000403a450b000418281c071040b000050140d0244404c8103141030084005600702d685c0c0d90000c2005035101d009024156403004c4048040c1611020030080380705249020384142d0101440000c1d03001d0010100602c0480060300d4071003807050070807680300403503400b000f01030307401032100100303940400280042904820003080c054900b2404509201741c0c1d6500c070440c042c403103000f2600003100320349400c2c24205144403c0c1c00140810340170700c0c03a258813941001c4a0413511050205490519144041034015074000402c00c03004c00070b010006010b44c2d800d02e0421805410402105620006204440755403160060a00c91001a003c400649009800d8000e1160881e01c0307a1800300c030819095940018050542d41120b442c0408400541c8075441100c040d14031900050080c50300f140040494001880384500c2c40820800060010608510900404440d0541400390364030043d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 740501375 1250 740500125 740500219
    0x302060a0c0f0f0c2604140402040518070c050d030c02150702120c240105030606010810170c06030c0c0f0d05090112090f03020f0c010c050604080702 66
    0x384903909024180720081d09504540c036484407580c0003841e62410110400a26403e1421000a074060030f192141c081c0340c44810285444030150044070580c030008100031f034205c820041a40518011180c102401e003c020911a035590001c9410440c1400c00024510309526080c0c1080e080c00d14039004203848880c203030304456040010304440004580541c4090901160007034580c45c104024418006000c030f0340c5904400280b003442c02c1c4005005840002c450408c5109402c050b09101c1d003440ba0040000140c90b41d401039001c64170401c6880f5030703009480d0070141680c998000c584511446880340310b84d588129100c460081d40201040c00f4042c1d2601c1032400c0c0b1600d00301c1d49810300c40e02c070b0b0081d02000e0b038801d40040513600922000d00f0000c0118036850000310003049950406094803403043c95000c1030507000f080140c902d109030000e66280084110041d55002d640c2a001400d550101002402291903080a0701c1aa440200000131903141074008402c0803007880520f082d43e10400400150b04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 740502625 1250 740501375 740501381
    0x6010309021909053921070201061701020703080a151a0c070501051201140d0210030c080a06050a0e0702030f0c15240121060b0714060112060c120501030302060a 71
    0x1034144172061240c4103804940700b1460305408118074242d00340800e040b550070710a40100c4800c0700c5914514443d528128600034081c0950340320341d1034443c24030074030742074800b8060007100c0401d070701900c1d020707859252003040342d0017420040710060802041c1c0c0d40108980e1807910044032107007407400f141901c411801e07001c1400c05e00d9540c445230510800f000200341d04004801c3d10780c11134a0084104031900c030708402041710780d00d254100950018180e8404844280c0680c08900c2c0401d2981e5180400e0f500d0401c407000b12140c502032640d11901d05282004030b0b1400321a03444e40284a407041d6420301681c035a2140582e00610401126900301000164001140b407202550111a403803140e01c0504052107100d2070070940c18034007410840300c00060500401048804802a00030403070400946594080c040780d240c100c40c0046807003082e0b03965400c1c00708000164844c1030381c0e03003a003d10504071081d40e0781500900c01040300100b40502c0301744020055208ac0304e01030081d4080c3e00508100e14000040c2c0d400c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 740503875 1250 740502625 740502661
    0x608030a05210118020a0e090f09010b0105040501020a11030111072d0c031101090308040b0d0b1206191103270d020607050f0d0c05040609080102120601030902190905 73
    0x9020b900c0010014558024542090641c00d1000140d0f20400c5d003d08855460b514058039801c8801c2c501400606001144140e10504140008024000a16004444070711481c030400d801680030700341c0580810425030005408000040c0009401c0010741c010010581041101365142d0320407540d0084400240c0c1c0000304988103e0f0200c0c214000c540e502d07a032003e2054000a0f201814040030b28109034041c141c102c005d0340e040701034146c0721961240540d080385d00c10006440b00b42c0c10f0030b045a6150620400700715405e411071024015960f00c4208040580002904664400d131300c80303c0c11203280c0e02150065009210643d80c8100e203155070300020f011909641e62400b85e81e444001c0c15180642c0c04140ca54000d0081d2078815600d8290351000c0d41c050150300310f0001e03414a4000740c2c03003d260308070380103108a0310b064442c44441380c0e6a000300c508074002c0228000340c01c081240003500a610070350044101078401003000ca008030a03010b003a6015210b98000c145400d68500500184c4440510342400c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 740505125 1250 740503875 740503927
    0x60f0603060f090b030309120c010201141303050c12040308090103141302120a0c090501050f0916081009091208100b270d1a070504050907120608030a05 67
    0x80e6071404406244001d043c2c840c2c1d4508a41e00d0000000320343e003e204544440400030080f41c601728284d01e070075440d402010710181c00340d031174281110160040c580d034061240c0702da8012000e07051101e0b2019900383d482444010500d0242c142c2940d0400c4044000c4c0000d14001c160550325000d0b0400050101c82c01c0382d10002e1701d98412000c02c00c1c11f4410300d14030740b4140e0f8103a401081546043c3d4040d458000703c40300044c800e0502d1003001c200c80105030302180c100e403000c0f81c200803220112410301501e00425034902083c039441c08100705e101e07802184607036082039000701300394030196481d41c04500300d842001c002c49a0102181c810748205038050a40d0f82c10805200380c01000b940741800c040b4451052610b07810041c2c8125440f4810300780c5204840d8401000035180c400303010f520b840d180024a50301c090840b000c3c1103200c040340d51684100c1c00e46040c0d0f50007034185042900d581d03a05a8140005640c0031030b1050b1610408a404d1702d003440078266164140c0c90b520745030032508112034001c501c4000400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 740506375 1250 740505125 740505131
    0x52518090902030c01110316060f0606030e0303152101020d0f110405010c150212040b070804170d0603051204030501060b0309060f0a0e03030708060906040b060318031606060f0603 79
    0x440566030210711015900344c2400c0c62001102c03034882c940e0550068400c070918250003101d11000740400740e00f09005090003000c0c108a0591960000d4007102c102040c8070070b0b41da005000054910700440c0843c0500e400003060400321100ea507040f0b000c003c51200034068140d4022802d840f8900041c0100e903016042003c00f4041c94419100380940c41c05140f0035a41005517941e000c105205080354400d801d2406110f003952b4814411040c54880038040c1c50889001e54008009072503280b09a40c0d140c0101d0b407180f01c0210403241c000d6032400b1130700300304448004a9561040040010020028090f41454001c07290340c555146050041c2100c0c0140e1010400e03050070410044c0418000c2241a40b050903591595010f440e81150440205a0f02c890402144030000c2801003050708851124403904c0c0031501c4d81c16903600c003c103102c01c0c0c420800c0e1485e00000d05001044c841d04410b4520250340d401b020032641419a100c04030f588586178103005458541d5100010700c0552410503031403015100b941018 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 740507625 1250 740506375 740506391
    0x21905091503030d021606110a092102090601050904060905060f06041505130305010204031a01080307030903230a080c15010b04030204090312092003010c0e0405251809 74
    0x3194803446400d021110503640040c0d410310b020051348007552090f4210701e04008c4071000164140599001070180c0020540400000070785413034094144c3c092101c0859841c03420b1000d50f00b800980003000e00080e0511806004046075030304c99108102c000d00111802182c242004024884441002c50700c0707901550341007006000050b400b0215083d1420640351080c0d446140d104002c1c0182c00503040204035500019001041c403031111075815800c004801d0704c0820340d036201a040da6030f104540008012849903a002c1001c124a401042810312401e1030400060680780102804d01c900424101d07101400818404c406a00400101d9003031290851484859410b0a0800d0118015480028416510303204000c0c2018400d070081801c0c42100c0c001440360320b00398500341da03103c02c10b01300040e451285282900e10a00c1d0501030b401c1c0c680d4442e00c0d005003888241c0305100280138001c120068103421281000c418001168000c00756055a945000d000c00040707003160142c50f4038ae449180110300306060 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 740508875 1250 740507625 740507629
    0x30b030312130209180c0a031a0408040902121501020601121202033a0b0a050603090703020a1203030e160605130905010906061115060d0c030219050915 67
    0x4544511880781800512550303480e6080d5040c11110000a401103d460207002010101103810345680b403031039060701c4c05003c5036400e1000100ca81c1c40054515900f414441007540d1801034071a40240c05452038500e0b107500c0307103844010fa80c00151680d100006c40070400c100d80c2d500a001c030391000800d101501321540341c4030540340403a100e954060300c0341400000c4001820300800894a110382c449402c4ca85240130003041601d4400417180c2e5803805004544050003484180c0305000040c50000c0002e14998242001c1c0b180d00d0b0801015407501e8801c560020000d40d0341c06068000034058040303046a281420724004042d20348001c8100c080d6480840070039400c1d4850102c0c203003514010715289841e840c3d220b05050f40e5010030b92190090358034002c0045071110fa540c003d841030311200e03205c2030322408248000e580d40c1d007074070a000400c010048011030140d207440000092464040c001d08001241c4a40018000004081c2140d8503910142810016800c1c015401a4041400f5415810300b15590b40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 740510125 1250 740508875 740508877
    0x20070515090631031112010903200c0306011202120d02030301060309021305070203042c2224050a0207120305130506040c0e0603030c03041509170d0f030b0303 70
    0x1d80582421204900d641031942900c3c02c2e0810100489802c030000b5502e0902c06401d0311021404c07409508013a6440318a030205008aa108552564800c500c0e1380071851005000c074000d0441a4407405201400040e6036401c002d080e0184c1303c84415440029424410071190028494010072a034000c86210300216401009803030441e000c9080104140f085440058820105200e080c4c0c0300524080130b020b0502d50000180c810744042c4000000c44042c9200c201c1c804080481a0841980d11000000c0d20480007412a0600442d2024041007018066807014243c07442804010b20608481071306101c00c001d02d0040342d41204100c001103140945a071188822021001480030605440d2008103031034140d000ba1110030140c2201c00c1c1c1e041ea0802c0e1500440340411442006c84122080022828038a8003000f00c4a1412880b03008602c1c20303290800340b003145026036540d01d0a00c01550400a61011911101c042c0304001303001502552b039403043c0191014112642c0031040628050400300c00b80c1f4000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 740511375 1250 740510125 740510137
    0x121e05070b06060d090303050a0c020109020306060f041523010e01120b03030f0403050a15060602030a03090519050d020d0f1d040905120c06070e060f0a200705150906 73
    0x89001c10480c0d803044041410303407044850a000040ca844008002d1503490740c091070240c0740c0500305000e080384a1400700c0c2038031000200650f16070010b03404100a0b00d000030200c0c00441015101261507030248140f0490a40340c2d0b40807040e0401503903d807220f040a8000c09401560003428020a18224040000c0c600e0580c098401166556004110b04a640420a582c2c400304500d102c0c56456031a454130355140c1d100720404580106101242741001c0341c0390700400c01502e119500450518820080840180c5246c80007030b602d80c0244121200c000440e1304011440328003d0006048498549000900d400c4910a800c02000114814600310952200e1207a003d05240e0440c03403803c40c2c5600003d8010842ca02c0024010310030140c107014064806005400402c03407040989403542d41d280015a81c00740c0000406078010001c03c401e9140b503c4c000080d01c2c5840152a203c07080d070049002e0944070604600384210325174401c280811003480e00100d610802190f41207641d0170403030860b02040c1140566 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 740512625 1250 740511375 740511383
    0x1706091b030a0e0d0c02090919030f0c0c060c0b07030506011d03030c030d1b0203190c0320031305043c2a0503070e01030509030d0504121e0507 63
    0x1001c1003210071590440714180b0f0400e401e4841c078060240c409058001110001c034016000e95001070040180451003910308018100307042c44041c0f0302c5d60102c2d60036040d051303a18144001e055800d004582c082d02c104029004075102e29502144a00b230040f0381000090500c0109810b100c1044291390384400c0803220105582c107511a00018840060f05500850004203082d20020400200c1e200b240c0e00300207000014507042a480c04407400c0202d0b00e0b03100b00070150034004403910200600700c2c070643c04100803501a24041c0031058400700d02c00c3e05c0082001c20070500d6403010400c5140741c949190008014101206c0070040144807400c0c2c418800c02c09001d41c10350701140c161071404030441080203807001002a004200f000381c0b2001040403403c80d954003880d0f8203401100e00903541c1c094002c6901907041e42d10303000c048070301d101d00440180000408401c19800b043c00318041103151402150301980c8a900c20010b5000c5001000b00020b50740038080745401c40d80c0c1c03400308500e078000d0308980c8c03c5900 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 740513875 1250 740512625 740512627
    0x40b15030a021b03030114060408060c071109090d02070f1202040c020102090d050d030609060506070609050718060e07050f1b07031205130626040f0b0103031706091b 73
    0x407916498020302620402100711079000c000c8442c040c00200c002e505982c8030710710103043c034581c1e4428050305011343e00680c0340ca43e02203004102201e0003113000d80308841c03250028448106000340410b810102c1510115042d41c824050031802980500c500d4015120851801068a1400c01100041144040040d004a943e0525154614802e40480d92190005810180c4813500742c0350640d80c9505048009002a15064020a40e00c1103406000100c441c010400c074100710345901c400009009403e400c8400c1d12030608002000d10703000d80d003a091f241c5800d900103580ca00e451003050a15400402c14000c0240c200b00c1300039561000000d41d0b00c414807040440b06c1c0c41e10088200b42c941040c0341c00c05020141103943c08130b03840d42c0c040d00070714099400c00840780c0101e03603640301a5103000180320000c4c40c003100151203203c0c1e1a070382000580d000d0702070b04491041210035260601c030542c00717070801ea0004843c40d07450001c0220744000700b908500c00380d46c1d2950341d1401e50310200040380380491812400304 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 740515125 1250 740513875 740513881
    0x6031b0c030c0607050403150506060f0913060909050709020405060703050c2d100e1f110d02070c060c03021903020f060a0f1109060a081f0603020711040b1503 70
    0xc2007081e2000540712000300d51480c2445440a04690003d200c01c5403c0c001258106a4001d028080c21340241c002601642c10007081103038030305542d000404880e421003810407900e214003900b4040c0f14001c0c06400d800081c0b040300c038101b05041c20480e4000c1842280104000c02c11a11454207c6000ca0b8041c0341003034a0345d1854402d103003040d4040c4a000640e10407064501c0340c40408415038210441020115084030304448841415103e5540403070340b01e5080301e83c44070501d0032404041e51412408c100c0000317410f034201403c0c9000c0e4104040ca100107580c00300ba000c003084459081c04020b0581410715101c007045a075002540c80401e00d0700000460054500f00c003c040c000c0200c406051950416501140b5100b890781004094902da00c24610b4102601d012614452038110340440340c0c0984400d10f86408600184e9804001501100d0060301c40500766900203003095405003d0700966501582c2c9810700d04142c6c0c68501c1e50220035201c1d901d8540022007540d01d03a8650400e40e55400344094480d9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 740516375 1250 740515125 740515147
    0x30201030b03151e060f010906052b0c02010c1d040f0605030607180605094501030b10120b2707180c1d061e12010506031b 54
    0x21448042d02080c86214003d004041140c0c06032800c66003113a000e00403a6607552800c0000d0305001104a6002c2040c000c003d0012500c101c004110104580e014000320045242020085030744044a403100c25075241001e50a242e8203014910f60500e80e0700d8210040721f07511400d40c14071102210684d10550ba911402ca141d03101303a400c000300030000202600c80a10b800d00001c0c200e181030881c0c03584010038829012907442d000c0d20680b90301000262204101042d20840322180800c40501d504540c00b41d500e120b8440782a05020144ea10480e4803424629403440c5000c10100201400d41480403441040600800c400300841400c06504180031454a403150030301840764404c0d0400382c400f0041d02c003600c02441c1000007000c00032540490708a51146078240c107a001194486980382001465100c84c04d18500c2c22403040c8064100c0007000316103042c103c1e54041d11500381c4c081418600e1400031605a00307a180250701c0c1c0e8014803041d940c2e00e1031850202e00070181840725240f04400b0b4407020030721514107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 740517625 1250 740516375 740516383
    0xc02072c01060e0a09050108101a030d0c120302031603050703060515070203060c3604020301140f0f0303031b0417060f0c07032001090b1008010e16030201030b03 71
    0x201580d038862495586803000103112401180805000d034905410004090100d07200d80380c12107820101a0910994054109002d0448c1c0c2c0300444410070b06115008159400b0311520b45012940d40b00c2a5070b5403407a19241000e684200c0600e41854814010810030240c120955070001006103400196903540d003100358000d00803504900d802912688400c11111040b03802008414000c42c01c460440d40c84543c00c113035604c50942602880800c0201c124001d100c250048041401040718140c500e55420021404a80099100141310b1146c09080b0000e1305240a00402405043c3c51050301014400c01180e030700d100103414a400f0980d02e00d49802206202e0084d1409000e40c100c3c04082d44408409044d03640500755114408030342c001001c00c002c204003074102d0380b42d9a85a19031200e800d90000310720311076205440700003040b9500d42d02148002448141464468502c00902c0c1c08260f080401304c90845151385590a0b455101d01001840040b40b40040400c0b0b960920340070841d4502500801c1c20 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 740518875 1250 740517625 740517689
    0xa110f0714010f02040501020f0a0f06021b0f06011401021c14250c0618030201200f01050907060903170711181b0901080a3b0d030c0207 60
    0x207552902c8801c00c88008150010070403240245d080305e40a01b122680c8030344540244400501c05038402c03070541c00041e0581c01902c05490501c2100c00250b0a4180ca60304105a440d01105a500408010f22076015810381380103a400c8280300030705444400d402d441c260307084400d0004003480100c00038940d00118210440f9445203120301e180c1d0340c046c200744000c00460641d010444405600403c04248648908000f484440c10941050101c0d8916001541c10070340d403c85107142520b0000004400312810010300285030441c000001e0072b0b180000c01d071820040c09800240c100320302740760308102040350004084042c4040510369a9101054609102c1da01070182c1a19001040716189418100e015001180f20351800d00c00c5203106080000c0c47d0685110f45810203011a08200101344660919400820707110154072035803411400341300c06030100740c40e519a0503904290360240b803c044a0203120b150344410481c10248121203c1c0200070f512094607005601541464081510381e1030004400e00c50 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 740520125 1250 740518875 740518913
    0xe010e03011e0212060102031317010636051e060a080618100207030906120e1207060f05060f15280e030703020906150c0717060a110f07 60
    0x2a801c0d480b000d50000394001040c044908000500099400d50012040720b00c2c69000c900241c0006042c41c0d40c0c81c0c828030344211081c029658070b03c0080b500084500c070449690f601c07802e071024504080c001ca0074581c41400307410b002c07040c203101c14481051014507038490f40503190180c00d06950f0354440400d134020b610751312048047c4a141c0c03e215407100c04031040809012440241c03852219085202c800744d100307840c0000d000603803440341084450320420301088803210800e80418000903c0c030445140540c104140c10259000090813000c00c4084d215030a401c61008406115600d8a10300040009194000b00750140d00c1e0075584403195412401103d00440e040a0700c0e09050042003015000f4001d204420700101d114059550702c246000586681100e40c014403203020b55030380b00180134200102803003000c66440c2c02d01c04080296000d005202c0503000000761800c0e00304048481310310745036024240001c0b0501e0000c003400c0d408290021201c070004111401642c407a86031411040000258a181c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 740521375 1250 740520125 740520161
    0x90b011809020904120f020a03090e071b031806030b15070201170123040912050a02030702090411090105060a0503060607020d1b031407060e100201061e1d04030e010e0301 75
    0x201c104580d122941008076034070b0340d482c101800c030b041b0166654000c140000e8042070007050100616104070840315442600b5250524403a84c1801c2c1040329108001003c40100310f0341004900c25282d441c541c24000d05403840c0501108440802040b80244128503449480034001286001d59020323440750001036030b078252100a1580d41d0b00c00050140c20b81e0318240290a012504500a0b15023402161851500054142c0000589100940f810b9001210381000c1d8082801861b01503520078040f14070460284240071802d00d00c42c0c042004054050304410301c00c1006000c0074812680c00300580768040004e952060b524242400050030301055110010301108001d0140b00444179154010011a0f20070700b079100c03900700b00350a00d41d15103131a40078440c002642a242c005145c41d1008a88a5006403400009070040e11303441102108003030780044030a20350080c0d00030400a0400c50443c29480d03040d00000c043d90400c0d65000300420603100c2c18030304220310312540c008207503400c0d480184034917580c2d00c0070703 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 740522625 1250 740521375 740521381
    0x50d0501021b01020403020301060b07080a0305190204170d0207030804030303020a0e1e0306160f121d1b01180b1e0c0a050c03060403050319020903160315090b0118090209 75
    0x818041c5d0310602049000c0c0d400c0800001c0c40c1010300e0181c0d0b40f4280d011213100e050132001c4900310002c103070041002298400300007200e000c883c180d100810141040038090444845000c0e9a1032410f2070902c4444110741c0804002c0003c1102c84042d2016607906140c0540e407a031030311404850140c034030031641d45e01180d141c0e850ba4040c14401c20140c1340d030310154255402640da040c1e81c4c900b20113000203148082546142c84070042449950200307407001c80003c000595543e401e00c01c03c00305803160300108a9500900810601d2110300c40b0024507034409183c009200b0007000f1000b10b05034958071030440104008038107034110a5083c9904a0f107003801481042d01c0345c90395111140e41d41c00002d42a200c5014800d0425420b04000c10354601c9907805440d041d286840c4c0c80c5a480d02c0e84500005500160f0303080c00004426581401072040303e5600c021250f19090031800d1100b586e1603c01003a0040c240b0b0010300d040060b00c5002101c0c1180c03640c0340401c04583d40720300038501418198600a40c0301d180c0303a0070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 740523875 1250 740522625 740522677
    0x903150905010b01030b0307090e121801081f060e010c060c0513050306060307260714040608011b0509010903050307081e070f0b0709170703031404030c050d050102 72
    0x30695440c0158000d0055007071400056084400340c00321031b900350f081031100b8000e00d002c47d04280030143c200b800311540180315a184a40b09d030003800f203a021502407090000f01643e0300c0710380b26400240c5000ca2880205004003c11607510551040740244510909117080b0f9a0040c1541a4201d8001405008107074680c40000c02c0b039400198150080451020f011501d0305000520324418038005c0d00400312a402e004864001030b004401c3c5d2412421040d1850f60204000d01c1200c00509440c0201804002080200015901541c00030b01d00e03689401e1541b00c0c5101203890109a6142c0741c02e01070b50392070095004a50796030b5150400707000e511001466104004100300104540d00d004080b03084c4690524030031901a1107904005041c200c0c141040c070b804500c4003010a5040003490401c14a09503441a0904144040761403541894100d41810001d264100000007000f4072800b40c160b10705030965951300000d0030540502d0f03015002c2c60410f4130402900f50304039542140742020001c1a007814940d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 740525125 1250 740523875 740523881
    0x100e13050a030909150f09090206042304180201021b0103110f03090106080601080703110d0f080306240406050d0f18150209151c050c0703030b0d0201050f0a090315 72
    0xc2840c0b026071500e0041502011458424000d130b614035440c07100c9003450030340068050010b03a102072ba4040420040062010f10443c4200e1000410454002101807010104811110780300c0080b01100d43c09920200140c0e40452400f0322101030030240c00306110761000483c0248070b0030300303004000d810004229040c907645402851040090200a02c20a41c54044880e1185000c1c801c0719041c2d03100d00300a10000c1d064000300c0b103803a9406801c411090045842d0003861003482d4206440810000041c40114100351502d110200c05050724032282c2e041104000440d48114800c0c40304000d800300c0d01c0d0300c1940e201c1d044490300d1070b07000100348100c0d044068001070503204110102c030f100300040c03400300c19000f540c001c2c0c44084400030320000d0a094140e486005507480400751078105e07400d4481e141035030b080704d11031540a8a5208039050300d0b45000d190241c101c814140c0c03206d201d400840318000c0140c0e800f5048501000000c51303401e490b403c0005047d04e9807221504001c00c8603820b6640d961061503168 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 740526375 1250 740525125 740525129
    0x30f03050c2a032a032d1204080a080a060308090103181a0709061806140d0f1b11060c070507030b0403180504090f02100512010905041a100e13050a0309 67
    0xc80803404c0c2c00320407000319502d205000c4d03e900c203001d0588900000074900c3c45416000c04140900038609502003c0c02c220b0107204031011602160082442410503500c0010240d01000400c003c00c48541151a017050600079011214109500d5010081124840a03025003d16600000c8041c3d007036041c0310181484001102d0500000700c4081000458502c00c0c401d04920140d400c0b140015079080000840b980241040100d544006c01c04c603201482260384501c2407294803004001451401c1d85444440091b0002a010b080120340c107204034111030040b45098001c00803008007643c0d2641c501e003142c00c02c3c0f00b41d403015003220f80c908100010305421886512040a44040c001c444540b6581040700300c441c24180a406060103011082c0141403036408c0564100260521508000031005281c1c18910b09803c40d021701500c580a0001b0001c40b10261502c80494102c54481440d0658051003494400d22400c6500c24030f49001c51003d16407954101806d036042015500800c074a401c01034003401d414 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 740527625 1250 740526375 740526427
    0x30309010c0305250c030c14100c1d0d14121206040509101a041a12120f0315060307020c0102210d0f0b0d030903030f03050c2a03 57
    0x10b001800c4c5945404030401640307507014082e10040701d0711504842d6400300050403018880851100030200b42ea41c1c16540708041a4401440342d000f4200c040700c2656051034410080c40b00d1207449020307903200e000319001018021764004407064018200f20f01d8094800d0344e46941c0f0700a185030300b0001d00400c0010003900b0320008045c041c3e621500300b4082252800c0b240c410321070700294000040c5d005d207a0070441511a00c0101c0040e401b650600180c112400f034440f100011000c9580760b044c40c141000c84d5003500085d54041c003940640f420300364145224566041c0c20109000000407407281c03100d01a01225100070713103040d4491524190181d600d00b4040c482e103002d88203001c400e104404581c0b8a90f0000c4c09651011818155608880740107841d851005584080c2c544d40d41521035211070344141242c9010340c1c5e030180d1301840c0d0f08024050003008001c4208040c10b003000c12148254400440d800c50740c1880c0b1900511910740b940d484240c500d410120143c0c0130008825650103030718040307031030845e0031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 740528875 1250 740527625 740527631
    0x1806020301152303061306271508070302010525061409010c0e010e010e06072405070e2211180609090106030504081608340b070e03030309010c03 64
    0x1d059a0f031200c0032071481d1030f0b0719110041000030b04904001c542e80400c5a03004c000828079030303102c410540903d10b0312072142c040d140720510f5200740c60300d141c011168116140060100e80500741245192603481a000c0a811b02c100040d41c1820100f6086140c18441d800182c1c0f880d560b17200e86400c030054501c0007204150082c9040119010501c10301c1044155035558541821320005400191007819001542905010810308201e084c2d4964074001d004240c842c600349110711401546202c541100c400c08081d0746880c010400c101c45030080d64180004030100c0780703800b03040c44102081e07008001d4050051041130605903003001d40344400c009000114692901482011591401d128090150380e409030b90000d810700040149a009504c41034020b400740b0106031a000604410341201c005800c01120704078000500c0c4000c6405010300354544804407a84814442d0390032050045440c01104003400340344903080844c8080e405441662840b02c005015a038036841c1000095000f008041d8030f842c04242 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 740530125 1250 740528875 740528897
    0x30709020433121a0301060305030a02010c0906090605030c2802190206030402040b060408120703020606090106120515042f0906030414010b0901170708030c03040504180602030115 79
    0x745052207040c42211540c80340f00c00e4910720032140103811010700006007055041014040e81d2030038002c41d00603600543c015a03480c04400780c020708480f40e0115400c01c010102d202806010781c48801070003129014a06a9180e440d10f00d80011a48241450a0910804040130001c654401d1103c070603c0310b40c940903520158021204035203400b0714007100a41c000c0c4101f000800601e0a5441131891190241c00b013400c0c6a1a1410303185071002c00100e03c505558041403500030503504100040d44914240c540c0401540340c80c030082c4c00710340c250988285817a1500000bc1c10280c00007021902c0e03610040080c0107050141000e1f248080c40980c039243ca0328016140d0007014500c690484a01d614042c10076803840e40e03151100a9020502c81440859540f1000b04041aa480242c004d000c1c29491195802c005040e42c10303a031400c00907510229058009102c0701102080100c1910110b0b2000d44021a070002818032400d20498046401040948040000b107580040c50419110084060300da0740d910b03003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 740531375 1250 740530125 740530199
    0x1201031a07080c0706240f0e0105010207060c030e01020c060a03090611030717130b040b0910050609130212030703020309100509030d0e040b0a03051011070506070e0307090204 77
    0x2000310790410030f864003000381400141c0b443c3d00c446058908111801404100a0442d0740300700c0c1c0030782c07043d039640c03034030031001d001d0404030890300d03170041c02c090005011462070300300f003c2c000c4012101e01900340004001c2101ea2a4000d000603541903034020401c5980d01c02c50170001e0000d022001041d82e4941c40c1c5a02c481d0045600800c5a00a203140c1c0c48005500030f03a008000d01703101c8002d0003200c07104400036225002404c0141940d014510070100f4090910301400e4440c0f800d051074000483d82400c280c1406296107079a100c080d0000010854440d44a0041c0085646403910920036a0940302c0021f1440a03d5030120140c1110103044844003944190440b00f00c406015a02040707a068005040b4103000318040c510380340716000060004628400300b0f82c0001c02c5120694415101500300489040c10700203613214540c68070904070700d15402c050040c3c03105035039894010054401e002070045403668607902040410010489020300390360700c030380740c24503041c5610030000d581c0b01c1c1803c3c0c208404088 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 740532625 1250 740531375 740531387
    0x2011805060c030c0c0f1515010c0b0705070f0f062a2f010f110f040302100314070e010905121917070b0615071e03051201031a07 57
    0x100360000010000c40d16542003042c9a42d2018001d002011000c0043d010042e00034415904401c510300060011845002c480134a8204001c0041041508010002c240f580c1c2203040850682c3e0448580145555a40815a001c2c820a40702030420003038100c5240400002c042030302e01e200d101e8441403100124101030344900134503a500c005504c032540ea0502c6011071180c0b100902c05085040141200f00e00ba0a0000303c8814500804a059466a0b00882c4060b00c0c0e010b0510554003950340e0074905400c11003080104d00076800001c0c80b4080f00d24910b01124400d070804004503c07a41c000400e10304090101030032509001c490a4023140c4441000911817400c20a016581200c0802600311f01c140110401900c2c0c003a05001c42d00b41580c6002d11000080f0407029080051141c50f0844c3d840c100344041244002c880e44030310303c00c407400b04401000a610015110745402c08800703d0b4000301c2152800b03036840c4c010800303002c45407410500000f05010050b00c0700e4246455820300280c05442e40340c812256 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 740533875 1250 740532625 740532671
    0x712050d02060714090102120301090c080106020304080a020f042d06080604020d0f02030a1b050901210209040309080d030204090f050907063e0f010603030f0804060209150a0201 78
    0x1040c84140c3c403000321002e0744d00070200c0c40c1d41441924202c404070010000c070790f0030a80286030601e0751040129070294000c08113a001d4502c500003182090314104919556640e1100028091801012890300d0b80e00c66401c040e0180303039400201d98041865a15840c18503a02440c543c1c1c0f040e0811a000803000d1001c01c0d81ea0003103030060001c2c004d54000ea180c40002c5520820101c0e050320480949001040702c6100070900034503002e440c4139465151500b080840e11041e008015081940000b684184103c820303030359103466066482540350740c3c840c101034034228000c1c0d02107103060048110890409030b05d036006100380c0b90320070f1082014070140d030745443c101c440894030702e1642e500c1141d043c48058005d28440286401080b60b03680e0152046420100035513044151a40841b030700f82c0b140c90012000c0c090fa507882ca034080c00802c455484c44e14010080f51004065409008004021400b4410180c04480100101038001da40d00c1d01c01c0d40300d4810a910010b07008005510f00710940d203008009030070f0001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 740535125 1250 740533875 740533877
    0xd05071104110c0610141807030b060705010e01051b2b0b18090f0f07060305070c0503070b060a2102060a09030b0c090102010606090b0a0e0109080712050d020607 71
    0x1091036449040c0801480c910600d1440500305200a0071400d01c1048a00d2240da02118441c4029107800f520703014a950314042e603840b40740c002c0142484d0385001a5103640c4401d1700e10b008142d60720001c001c13400707501ca240700c058525401c00000d40803100d01508030038040c06141580580320745403c8500d00f0b032405407c400100400c003504203140141007950200b402060840c5001515140510004140b1003a91070881c0100c0ca04008200d540c01c01400a03100300c1c80d0318000790840c401581d50194a030120f07801035809055590011501c001e115402210205621500701c954941e414101201c56010889425106012030000402c40190b603000d1a2003601781402c0b9030f200c40015030b0800040340c02c4408500100284420000042803041c16040c1c00f41055480181d0750307005100c002400e681080c0c00803414854484010000344801100f200d131441c6052400d50240250000101d4549140e40e110208034410b190010072423031400e078000141507200320704960a000d4084805c1c0c0c0c0310401212100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 740536375 1250 740535125 740535143
    0x1214100c050a111e0c030f0c090a0c1803060509062802030613060f1a160209090a050102030901060f09050f0708182e050108060a020f0903030d0b030d0507 68
    0x80d035800340700f400036522a408207442614102c840344c41c205001d8002118403941c48207080d0b4480d03040c140714056401d89803030050145000319002040713060708054068004a69aa005058818401d200400a20101038a400b0450390f581c1040d0010741800c4d07402070380d2070181c800030031000d0084082c03890203103031040d0019502222403182d0900a42008041c550400249074407a00c280d55a4403c3c02d014020050000c0082d60810040202007114040e440e03e50382400c000c0341d0080340d040801850b0499045401220315a2110805810060303032050052484d80040103001503143c042d000742c81034035180110a0715159442c0700c200c0907582e090710030a1080b03041901013113280e0311445c42c480e80301007400283e518a00c28813598600c1c040c2d032810a44000c040d044c040700c13947e03182c04100304e00c101401c0d10148115410290090348401020700081d016507400180c9504401e680419510003400013025262101d0792406048050303c0c00b0b499052180c00742005a5080c83d004030305682105811060701 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 740537625 1250 740536375 740536387
    0x91b0602071a131e120b0133030b010f180e0702071502030702040b0d150f0e0106120308010e0c0a030207060603150609050a0c050306191214100c05 65
    0x6000c140510910081e21101004410f0348207400f000e00c14010540038080344100d803451041c5460088194004800b66000c501c090004941e04001b0181912032668002c40b2604400190107030303038120856481c03034602050500d02c0d04e0517055805049250400c3c0ca40a142c083c01c03031002c4855404004890000040254090000300030002026038400c135076004a444903615164190140d9544680c0c2d500140d000103aa0700850034103020340280c10310b043d506909804500d03a1030310b5040206410414001d50340310380b11840c0c0260f60300700f80349044000008000050715060418000596403406902141490000040709608940f0091080c80d00c681d08501741583c98000300d001e50301c56502510740030740350b001c0840410450f45074028414119680003d2951400c070725501641e4008200c60419440d29040700260354210048a0340404112000f600d65402c0c00c0030100b1640198005203654214101c3c00070420160500e941c80703d4107288125045104000328000a60380d034048140c0018000b8404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 740538875 1250 740537625 740537639
    0x1081302060c031201050a120302060a0f020409090c090b030303071407080d0509060601030c0801080c0607050709052e0302061c06050306070c0b0907120212031c091b060207 76
    0x400410344014101e0b80b40084190000d4916000312030440c6800824070010080c40c50708228200040240c000d0000300c02c0134985020b0b466060041c00603684949503c41e1000d034501c254100c402404022400b00304054090070305e4101800c050044103049440c001014100f89000025a48180b000d9030343c4000e04c14110300e0901041e0025182110403d6084c45141000c0840e4040c003482800200010000fa00c4c00c20300050a5840c010807100c1030002c50b2005110003440411203800c84502582e400d6501c94403490401c0c64500d184d80421315049c6002d080c08000d88960300403070344940d640c20f02983c2c2c2441009490002c0f00261100035400441042503442d0000c500d520400c100c50b1a070000151584e8600109080c1702d012250400000c07100030010b420042000b140c3e41d04801c11070010803c1c1303030401c1103540e009814404080d21400c080140e1031000a010011a0000701c1c80941c010610562102010054040e800c002c58401400482c050a0882805400300464500303900400f48680b034001c0c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 740540125 1250 740538875 740538901
    0xc171810120603060911180a090c05040e010207020a080706020a02100c0b07020c10090e130203072304050601030b0d150e0a0c06030608030c0703150605090a0e010501060c020108 78
    0x1500c428050600e680254441842c86804011405414041025800741c80c1c02c40c0c09105812043e07110320700c0140322103100d8039450180c43c3d0100d440400050b21482c5070030011034908080c0e125a5125090a5180e410050306401030020148242e880410254642030030a0311340083d806a5030060303121080d824054a804450003c40c4034a605110b03120020580b06c0d0348c01040100da083e80541d1040070912083e081c141d0409a040d0380a103410740da41420321441074030f0150084c00b2600300f9850b072076591056690130710044008004074101c810381c01c0a845020300d0b07055a50a2502c0c46585400005941035009005907045004020880c055840c5540d81d950281003401c4442500c01d0703942c0c2d1b103100451100b040310141d105c0c041c481d40884a4600b04005040ea28180c000003c2d0303030000c0c401140e80020015148040c2d035071210202c0041344210b10b440c1c00601550744030642c050b14803420f0105d40794035a4451000651103400034030442e07894140c00c0d0b8240710080e134000d0004c0c01c0f00e400280c042c0c00b12a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 740541375 1250 740540125 740540149
    0xc0d0e010e090a14090f07030f080c0d0807090e0c071403040801020d0902040f060317030702160b18011d090a0b030312150d2d0203030a0c1718 63
    0x1040100c0d00e06880d034007040580303000f22040d504150b03551518915031810628015400341c0b0503c010000401081c1c18070742c40e04001d10004001c541210002e00030045100c00b13035140740041c2c00469a00500c0c05800500144040e070342140860750f207080128051a00064103031107480300412151504280d1350315000b10140d1290b401040e8001408082000582800140300a0301780040200f82070303519004200445000303020395581140f402c0740400000d1400c03075206c02001c680456440e1259a800400c0c0e090650810300c81c407060380c07180d00228412202d0809000d4880703080515a540700140c00c0103484c854180c0a41079089001600006031910b070032248540d0240e40100e001c1940c442120200303146030401003110705450035040030010801c400109400c3d8111048030604034284103034644400c002c851007668010350700d0060207420188101004491a190702500300ca548501c210310040c402c151800c07003113410004080300f42c00340424441c03d94840b0440d145450300302c031091600300020000301d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 740542625 1250 740541375 740541377
    0x90504120509030c0603151c020102210408061303020d02010c0210180203010921020106180218030f0616080610110a0b0a021213200d0f05100e030c0d0e01 68
    0xd1300300c41c10151540406940070381c100300490042c0681500801c04400301c420f204000401c1030b80314000141c0c2c0d00080d0714680404010f9445002203580401e415544940d400c629024400c9a0030300c00b400700006619100d2502a42c25240d030344102c85030483c02d880c402d4984100603417080c00b813000c05103010750281c3d84284441c9041b5200360b100b603010070b081d5012401b050b01c2106040c1000705168010350384a00d60001c0d03510003044010f00f00940c4045400004490303040156004c20fa10700444000c10349024004402001c8070804004840304946d200c10840e502a40b0050b0304143d038445074002c02c09140101d03030081c800121505035007821a04c1c48010000c4c130216111b00040312021400182890380a083c4446001d6034400d010380f0b18020000d006000144640d034595003003030108010740918043d03000003203d0300c0c0c0e011180e40d000903032038040b10300007902c03410324107188004022001a1840648030046c0c800d2000c171f00100c550726100d00070441d541481d60841c602080c0e82e41d1145110b101c1041c01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 740543875 1250 740542625 740542633
    0x5040f1e020d0b0c07060e0c0301154e031d01050d0203040602190e01030b010923032a10091503050603030f0703210506030a2d0b1009050412050903 65
    0x1b41c5a00c0300703540c24041e07412425045881846801c5c1400e00403100070a5600c0b00d0710150514000e030421078040105c6840000c442e84c038110481e42c85184c0d41e5000504030814041c010500a00c41c80364251703050071802c50106520000e0700701107814900085400c080140c440720b0600c0d0807440c0b280047c1d80005d0048075038540c20442c0721104200d00d07880304e213501d0781a81c600e425940d8260014048078441c118160510900d0ba50400c046c15840c1c3c0000d8050341c0580a00c0c1c0f0015a06010a2900d0b004049502143c40a48902c450326811103000308103101c422180c10450b03045030482900d0064075805900c2d0080c42d10001000d40600a4100d00d81040c03005d41228034080e40c5644013180707600800000c50025800c030344c0340c1045081c141e9640b200000c07240b1007004507080c8100000c2d81d843c1c01e00001003100c4111200c0102e244c0e58403001c50308503040f10751034444041716454130828103002114a0440b0900e1b483c00030407290942c2c41114852a03224a00d0020400b0b15441640c2e141c03c10010300340c0c5440303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 740545125 1250 740543875 740543887
    0x6050109060c05011404080a1103250c0503030f0918010605030c0c070e01121401151a07061109031015230d05010b150c07090209010c0605040f1e020d0b0c 68
    0x50030b40c6007030b11450017091f00c2515500d02a4005000d00010006003509910a110307003000449040c5041c0e0401d00b2403848110212018901050025401d40c0403540c1800040307940d0100004003401015a100101c42044846858000d003502c2038100f8029000014030a000064a283c40140140390001141003105c404c11359400b00e41c80040000d800c402d02c000d8841e58814104006001e406041c1601900280b07c500e2207240c5150b0501d080d485a028a03080003000e2800200c0c4402c2100c002c981c01a109005007010781103081d441d1751203000198000c0c8199001900e1740d409520555010300030b440d0800c0410341c900614400c1160b02007c0c2c0071000d48a20a0f040c0099840503048200395228070700100740001c0d10010441001070740304902c48103040801960400310408104107044d100004401611081141c0040b100280b100c80024940c1f464101448144014101402c40c0a071096002c8045012008030904400412050007034004055038940030000d00480c45c0c480d8000d0001c40c00030f003800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 740546375 1250 740545125 740545151
    0x141b070f060504060b09090628060b040803070b160e0411040806090d0908070315020309010213060207080d030207150b3601090c023f03100906050109060c0501 70
    0x1400946045501355510a050521401c1c0b491007154414004005054903203828244003001c04403d10860080740b0380603070a0b0b22103100c50b0b40800d0140071002c0c02c142c0ca99807260880c1d69241d02021080c0ca4103800140090108001d0017189020f2407240e44c2c2c0d40007030402a5040c040606402e102103c03000b0400d100c00300d49500c080055030710913490b170801003000d03080a40024180306000d0300124002d0b0440d000a0000c601c2c869480041102009401641e039030b15200c140c1c1c020b002c1d4410b4104440c0d910400021a0703139002848000b039414107402d42d42d90501d284e5055080f0300c16040010203664078402c85480d1414035501080030700d24050243c03c0550500041c403c1c40348655030300d209030f03810034036240d0100302d0541c06118094009000204a1982211070103990740c20507403035000d071500c01446846006044010b83c0400001d0403400c0a0103103001055804803504110380890070381e003020000180a2816000d030781c04031071040c0c450803c040c0c01c01c032084500841c0004281c5280d0749415602e2120 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 740547625 1250 740546375 740546381
    0x3080a24063002120606040506120406110a02030301030309050a0617040f020406090e0f0105060a1a0405060f090102010f060b0f1b0a0b0414070503120901020f100f141b070f06 77
    0x2500402c0300681e01d5540034190050588003900301c600460040c070007400240c40b14030480f210076640403c20009a651843c0a2018000600f0580c10610740031496220007500040a14182c1c1e02c0b0f51551049951140d06001c98031700c1c14400c1d030b000100040c15903035100d0030b114480c580190003032081058401680c0c0100701911103607441008505d55502c4000740d442824051054107060220082c032141c10914005004000e0714002c041c04232510010405034603021904031030091030b000c0c100580703501c008000d904040c0c1081c120540594201904d01440241503c91141034405900850b41000400c080d0b440d80e0703811001c070869480132805040300380f40d0410010064220b1084144040b5860300340380600d11494810011078070355100c11010711256601040812100d0380500420b80c542216100407880e080c203050365010300d4001c0d1142c0888800d840d4215484100e1000000c0c4601c401319550310b891014200d0300281085100c1c5402c0010001040045c48060b002e003000203028007030b03500c0304011 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 740548875 1250 740547625 740547707
    0x2010e060106091e18110d0c08060405090a0c17010e03040f080d210f1e05040209091b090406090209070c1a06010c02012a03080a2406 59
    0x3040c0080410071102141000021130003c43c2c0184a031114642a00510403400045940ba070b0746844400020340d940443c0705070740b10340081001c18016400c0e140406080d542090782d041d4000c9090400184103d14001002e008840d40030300d00d480d100380341c43c05a14003401c203c45903020755500c0360301100b4280000c0004e40080d10a40320041c05040c6000c24180c6041c04545800060118010b20320342d00b0604075016a140748100d41d00428501c40d400c24441c002e000c0c880e80e101c0c000001070700b20518030500e680a1031080d0301c00c0d0340c41c0f100b0b41c035007411040c0c0c1e41007618045600f40c40e41900302c0007a414008481c1e03400078403850004c81c61030015400244012002c51b03107480015604420402070002d003042694128140d04600d8031f441c14801d000914102d402d0070f010b414000c40e400620100f40320a4a128aa403c840032074000750072040c5002441c018080e02c0b140c007104c0c105980506800000049003a240c0411400c4c0355060380341001c10707210760111241210084028003180d0010351041d8907442c0d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 740550125 1250 740548875 740548877
    0x9071a190e06070624051003021602120606010201060e060a2607061d1503010e1315020913050f1b0f121807030201020d120603080f030f01060e090a0c02010e060106 72
    0x86040038440b60884115032001280010601448100181e856030700300040d41f90503902e00980e45030380500242d1032149a04000035000341052940c030380c3c42000801c210b400340601b40d000b44009641e6070116440c401d806c0d200d041d4070480038501007200300b4039100c02c9201c4103020060110400c511880d40c504000c880d0f0b10450100d4240310003024219540d01e20041c0382d0408560f24040c1c85440c3c07688425500050080d40b41c4030010002244420f44a511000741c017550010150b01c031301111041c5540039401842c9141d000c0c80b0b407641c588150303a500380185407160701592400c1410355a1451075200001c0014401c64035484200182c054489402004240c64102d9421519090130450f142d110384000141014005801200702400141ea011640c40c11203001d900e0000d82e1008400d203c400100101e0740000c06000340015032207451440384002c0d501c50000790f80100f010b03030b988031400c2e15000c40d81150316610814140000b500880d031644442c2400c14a4400003d41d866444c07207040c680a000e0f00410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 740551375 1250 740550125 740550131
    0x1e08030a0903050708031c020307110106060522050d08030402131b0f1106011401020f06010e0a0e060411060f12040b0109050106020f1225030809071a190e060706 71
    0x2c810701c4401c0002d000100f030b1240c0110305e440e229960203060303094096542c0a50384c0e0000081441c403441240d036502c0080c2c0c540003c0003c1741d907401c0054a540d01080f07100340160701a00c1000c0c07030440d07442c0c0c6140403074178080c041c500380d0003595450342d0071544010402c9034000d5240795000c88002461080c50546486134508010502c03800d1006441e48400407414010489410b040e400b0001003ca00141110310b44000402d0001d84580180c0c14403041041040080c411745000040000001540038040c480382142001411420348106480c1c000803103020313011902600e18401c540c144040200842000d45e0f0000d8145403403200250340415041c0d50030303165a1143c000611022400d40b203124010100e0340000c1004101e940c400d6511842d1042c60301c4410040810403400070058200c1001c0c0c50007107a40110801c440030f29010300340000a5400ac038640c842c0c01c00114511258135200041d10400d040300d02d0500282c5c0c00f428610381010080c170010410000d046441c203884640113061542d20402c004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 740552625 1250 740551375 740551379
    0x9080d020315060304030c0f02120f03040e0c1612090e09060f0a06080d08061807020706030b010503010f12050c060a031d011404080a0201061215050604050403091e08030a09 76
    0x882941c02d0003074806100d02020400e0100003500226840c15441d4800480c2c000200d0310b0001854608140590180340c7c0180d40485400c1e520200c0100142c40c01a03030545044d40311a0014181c3d0302600742e0916040404001100200d0102040540400c1041c035112520f15140c2e00e1148030380f0000e0b01c94200580c014014070001c180d98045884c2d00503402001007203000d03d40065656510811820b01c000c2c0b00f00741020603d00c4d160345004909450000781c0f00f09082c140399600a548030030b80d20840c0d00280c42c0101048181d071003401128101c1e140888039005c0c1a04000c03404074050440101241c191095109101344c075103500c006011140003e490001e002d072614180381c5840b2429800030140c591514070714403410041031250b2900540c1200c4910340b2142d40000980c0102030a800c4032000e096852196010480d041c010103529401d6200d0502c80d580b120000e100c26154241c170000d0200301c1b46c910030f200403074100f030a02c900310008520400c01555a04219425a030046619000052100b001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 740553875 1250 740552625 740552641
    0x304031209080405040e0a0501020403050f0d0311030f0c07020a0902091201050903122703030403091e180212040b06180c0306040c0905090f01031b0501050f03070309080d0203 77
    0x140310104000940c144488a010742d180a001e02c214003ca501c2960758140100c030b441020482e41004a030302c00b00071981c0325100e00b082035135204013542003c0ca07403092104815081348280252200111510780050640e11411510002c10a00030408070b80391006210110259807811000c3c1c004048224005131b0303071803050080c44102000c9070780c18009a8103060034020300c0740000007112181402d0420400c40e603103805121109408001c40d694800300c034a0008545640c0d8040001d50141d1f10a450b121209946e6211116824142e0390b03a808010b42c00784000c02a4410007007018203c0c00c0b4090b801031030082d5459030711001e84000c0d60141c0d050303070301001085424180708482100c4801c128401108501e1f000082505a100c01003146000c0c0342c903011384242c9035000d40310359401f411008040d1043c0d46410314152140a2091200351150364624881c01815000040d8000035558107075a07007442c00395404a00c840307030b504c050300c01c400305a500d545000100311841c0140001c65a01c00000d03941c2d0400c0f070f403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 740555125 1250 740553875 740553887
    0x5010c0e010e0307031509081318140906040311120a050409201b100c02030d0f1503020d0c080a08070b0906060a050d02181503061506030f090a05010908030403 70
    0x4502d5000e41c2c4449018808101541d1500b5100b95905c1d4000c1010f403d00d10b4400c0c01802a1300c554140c1031307901c160101700100c0701c020004c4100d801c144100412001000a0003941a0a50301d010080c1c00c00d0020901192040c520503070701c1243d4004440d0f941c0e48151803210305503c000400000500049001c3c840c0c160380e8000c001d88a036003021089400d24680f110144a445500b41c2c00707003a41c41507584148400030074001c00000b0944e561040001c450f83c020042d441c0d0f40f21501c6002618a450900812210141304490b074441c41003a202d40c1042c110342c00e01a5a08200c80b054560800040c030001e421001003002055143c416044c40d6241c03035242c5881c40860030003034030b1400030b0340110080003400e403100140c010844104454800d041c404c0c2c1e00116105c1e07031840341d2a0800c10140001c1100d82c5800d150041c18155041d030888081d03942e46504404055690450b090b8000030030008034010503d0b03041a990810610700556200c0c21141c4e849070f084075010b01040712054004420001450b4000e1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 740556375 1250 740555125 740555147
    0xc060b01051201122111100507020c01050d0603050a0f0308060d0c051003020706110c15060108070f0509030a0605060f010206090a060b0114070c03113a0f0f051c0207051c05010c0e01 80
    0xb0300235400c1800c1d001c1c0d2903000049103a81006404240001c410315243c001400864100b000d4072034486c500e040100c5000381d0000c00382c0c0400d041c000460f455080c44c1d05035060803a004580d80510320300300700170800040c410181010406800784060004205144281c8000008034413040351f840082c04002c5090549650860300380031041380c00c105031640c0100c1c00b80d903c9440c0c2c0c9000c400418401409803114003401503070075003502c50f80038850100304032903200d85d0184000710b5000502c00401401240d4403038003200e000d01c0701d4000c1c22070b0f4000a000b40d0401440002c050420751445464a409212540c00c5a103095440c01c48407070b000c00070700106000c03889a416003581d03003d15804c0d10318a0f406140002c40d80b101c0c01007695120f456021510410740c01040c0741c2c80090307050750000c0f80c00c0c510400724a419098520f40101d060400820800807400c2d400010650003401496141204000000c0a61100e0190303010a980d00c0d0740000fa021721550807440e100303499041013207500c240010907001c046 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 740557625 1250 740556375 740556403
    0x209070f09140a030605070903140a0201120b060712180509160f02120a02030408010e0c0d0b100302091617130b0a090c060c060b01051201122111 64
    0xa054840c0680c4030318400c0070358411080390021100080d02140b031140e81940054006840c14052181c1c01780d011510f4800c59020701504201c04010308081038072084e200100074082a20031810021503c4980c02440742c0a0b00105a9420858940c6410240900e00c2c0600380c005107840150041030708030b40c0d0403007000d00415580c1740094a002840409001c114034041e105101c3c108001c01c803514420407c20203290b02e43e9103009c0d2545104003010395a60414000c52206500740300c014208140c2c00542036000700b400804100c160701254a4403803a01c00d001e06503400050702c00d0320100158407a450300c64040c00049000074622000000018001d200401e0b040c0c1d00e0031308440038040300c0c504c4669441d520310303005805075800c1d0310768270301c903070000d007450403008007407042c101000241260040040740285001755018404420110011500d5210710800094503114802c01400610010300c00e10810301d100380d1488114801d058500c81c082c040c06d180b048001480302c9901c1c50380000502c0301148022107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 740558875 1250 740557625 740557637
    0xc020d0c0602040510170a0902150309160f0306050a02251e080909160e01050a0309050a05070e010f030f060504050109021e0a06050705070e071205011508071e03181e020907 76
    0x503276800600b0f290a40640b6a8a401001c070202d500c0f99814013042084051507000d4120303090b0b440c0c9020800e50340d61301c02aa0101c3c23901c400209801010f0080702c41441d4441941d801402c031100c1e0301d00c6c0b0131411540c15903c4803c0d02d041240842c01d140c0480721920b004444698540c291002040300e5844014074805103075032140401d100c0c2e20b8020951100ca10000d080854680c28030080440c0140000980540320b841594060810710001203081020b407015804070b0842607072030381c01052030082a4440100041e50030b00380c40c408640701e0b50200703411501ca0307000032a1159454001a00220b2440c82500020f0000f01e4201002c3c64071829130707002088541001ca003421030a8441c83e81311030140c403610b070554100f407000518035442114811404148800c042246585600700441080b041c50308600105000c08085201c1c41e001e903445c4850041302d41c480b08150361913050100c1c05400100d0b42034030702940001c5c01500007403100124010740c801106520301c01540038010000754010240c000800e02c86 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 740560125 1250 740558875 740558891
    0x12060b04090b07050c03093a050a03050a11011a010e0f0105090d02041407170105060c030d0b04112115090c1602060c0d02100c020d0c0602040510170a 66
    0x4028070903a98040282c0c00c0045d12940b00e0074081c1e086210701c1044c2940a1505812020641042c103071290440d04134200c803603107010706c020388031102d2081c40c040a03103558814880103000a06c504010501600c0614080015510751050f0900352200403d003030310b040140103114070003549c0c01800c80080c101c003107035418070006020001814900c20b81004500070b4500d0192a81591529000383d040403410140011440c90441c3c001840841c0d59031091511401c1c000000905103080d0302038405030907583d400366140000c0720400e50300400101c0c6410750000d489428104541c480d56001e0504201c01042007421a031441e805040c01c104000c114070b110700ca04485007202c0e5140c5d0f04580340d000b2003824160790742d02c0c03040e030546071100070105009501c200001650000e050020644100d858015000c8401c409421401d280665200c1c81141005074004c620075269070b4400c01507064a9401840014600764540010620510354101c000005c00c035103440c001c014940c00104a0342c003880c000000c00c0595 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 740561375 1250 740560125 740560133
    0x90304050607150222030b0112170c160902070b130c051909181a090d0c03050909010f05090a0c0815040e0a03111203060f060a090b0412060b0409 64
    0x1c01003000140490010300b0071074183e0a080ea0445035002000030148400304c103a007000c4194950340f0301080f0350360f81480d40001141c00280c20351400d007a60058500048019403900407000b0340103007100c40c0d440d21030805103903c5500320307036113200c0a808640005030740c800c45414901c0392828013520a1203840c07948880c101c00b00b2502c1c0c5150069490860311008150f40f13504d00704640325690f03041260b02c00c1ca4940c400203041d4000c0003d840d058400c00c040d11079814103401035010707044100c0304080c0725005801d20b01162440350318510a41840707800c1c000c1c00c00031000702107607201c00300f6000b1a40381d5a0014050280b854030500035030744044194020301100442c001d0040c60080040e20f401107649650b000306103190b5031030300701c000e003181c0600484d03002c00650304008201000d10400c1d08190301171440643c4050b4080c4085070b124501c040c21405094460405100080d4000c56450302006044140402e0781800b0344006d200603c1003c41c4d000581c00745007003800445554601c2907104901d0415000005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 740562625 1250 740561375 740561377
    0xe0610060309240b01030f050609011802042402010e070305070b030601030204050310090201030501061107050607020118060320071a0405011805070e0606130905061c12080903040506 80
    0x244180786000b0800501610b406070080b04100e984100d0400181c03ca80350046a035400100c8211090380c05000e40d0826182e00d030f003158070980340140c0001060005105480c4003211205c0041100c0e0401403030159078400d5004000c81a141c40c4104440e984031005c5010f509008803580560758001400c420341c030b1903039860754803003c0b8403580300d900d9004800904240e0003981903034020b10300601510110401035a2040c01428020012400710b440c0c0400480c10700d00c40d044407009002103030004c3c240356081a08201541c0c021043c102d04000d03041c01d50704440680d4081c03640040415440100c0d954003d00c1ca076100e0224500ca011060b030909110a6001c1011501055410804440c0606140d03d460500501410f00402d81d00307010303502603a1041c1002170000d03481c002c4075259009d140c016101d071000c1001a20800c1d0b25041169a480c10911005800350300c640d41115001b00089070001c4902d211010111082000340d42221140c18440300c0a502300700000d502442c1803000d503141c2030070503000038a6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 740563875 1250 740562625 740562629
    0x10050706050601031404060207061505010906030504111206011a070206031609090203310f080f070203120301090e01050103050718090602030a0902030d0c0f141c120e0610 75
    0x812916007011a41e0303039009a01c00c2c21310b00c1010003500c4c02c0c0e1800d400d15001a44c0185800c540e8946002c038840e654003e02c41004040d038070140e484041080c03070003900302c0207001d000d0400c0d00c858043e15500c559650b0b50721543c110f65507146000c0e1403150f00d0410080c1c40400030122060140804204181c010317034032001241c5c1e100c45400380c01c0e03400209240341140c074000c03280c002501d050710010502440c014903101000d9078034450ba00c0781200718064940b500102e859010001d00c600300003800d40000400d203401030454542c0e294990384c00d0100c540c0001c2d2a12a00103c002001e6400000601c40ca200ca40a00f50500e9090303c002d000c00e5156546059070b9180600c2810740e24003420000c40070603121303904a0204c840d00044d0940d201c3c140305101c40000c21621070202c0c4a44208003407113076a02d0040741d80c180e8594002c480d00c0103004030381c1c6480810301c44c050101184e9000f01c1e00c501d20700592400f14007800d03548541d115400408540e482104640d0401c43e803225075840b1004028600b418625140c2c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 740565125 1250 740563875 740563883
    0x3010b0403080318120306040c0512040b0603160f0501120b331321030f1803050307060f0f110403060b010c0b1e0c0a020307030e0f03010903110c100507 67
    0x260b031380d0b11808103036202e80e0307541503001c00c501414007030b501400c110a02441c02248100c4042008040c0402c00707507014400c840d031440c40c02d0081c1000902042c1700f0700440741d11640c06003d0396409410203104242041e0650000a1025456030046c826543e0000020152116400d01084031041003000036081d004501d0000301d80d03041d607840340750071071504114a180c0311017240c6030151110081c18022240711501d0103103e000e000c104c11400b00400100001011075174140d00c605a41d50010b10701254103c0f41051050603001804000000140082008140160240354001240e284183c1b002040d1400c24104180d00c1e41005152845085250102d60860f40e0203940092450034450040e101c0c003018580c050038103046401000f800c4071804486020903000b030881070206070b454440200080c0611207070718005900c00d11001002070f015201400702c0c180001d2010f41d407100b001c000a82514400901200028128194281c65103010030460750071400880c0c0d0800400301d40d0304020b00c035014448010f4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 740566375 1250 740565125 740565127
    0x50105091c020a0f14090705090a120305070c1e081c0e1306031415150904060f020f07020118080a0f0f020d030c020306090c0108060123040f180203010b040308 70
    0x190440d5250f6000d0350040080c0d41851490b940d407400f403c048001c84c2c0880d68003402e2990002040030b880740045036804500103000220940c20321201c140c86025a40044092000410224010550380602c401c002c14521242c3d81540320f04000c045400f0b9480c0d44240e0f0f49034030092450320440c1c041001d0700d0b00c210f200c0c503020084080c40c0001500c3c0320800c01c0300040803440c1420220500c00c01002a00d9070721300080440b021a000111040154081115a80c0680b6003041009201d45400e40f1040d402a0041c44082410206140c24030100e0744800359087c42400006950811540c00590404c00359a00d04c0450903000c0c2f9100200340c0318000d44900034401050040b400c020051034008806205801034006040c5ca465440c0141c000e84802c0401d1340f09200e0b103400a2a00030f4001403000340c4400c1030350f070a404c94807031400644100c0c00a40a0048401d6038500005070b0039558030140000382040b9015504a910340340c81e681c40800300d01c05003400f00b4010001132104201080894089030782c008203003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 740567625 1250 740566375 740566429
    0x303270c2b02040e030909071b0b041b15120608030d051003140d17070c35071406070504060c0f0803180106090c0804021e100207090605010509 63
    0x303078000030010095200c1c2c40d19481c8070040d100000078000e1100309440903103598540700b00586080403620841840c10350300c090740070005401c0004d12604144121010798000100c016004020b48050704a4141c2051100e005006140e2000d80706103ca0f07a078002c10009107007000007881d01c0307102e602d84004925445002007480c0304000c10704407000b03503003000403110b004440348030307050b22a0100c040450026282040c90341e00140e428420713074016805511400c41c2c4e0581943e400841c81542e04194000503403d648070150b0302615510441101d81041400390743d8200362a0200460481003c04001c950101080103412500842200c00f6115507080844402c8040d00e440b003074100c1c0c03d030300041012a010080c03111480503150310101c5900004000d00c11544c4034045101240d817441407460000758490046009410a01070456519896000482e082408030340840c5207110b2141c0c072400164002c013400c200245062098002900003440c16925000c0c4e44400a04031484403698200c14001004603 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 740568875 1250 740567625 740567689
    0x90c030f05070f0b0901020129040924020304020306070305041a10031203090606080c0a170a05061806060a0b0a05402903090703050303270c 62
    0x190b5004120749190b40100030344809482070944c00c41c2d1a9039001d0740c00c1c58400240d0001c91480360100100120b10008250041e07010400508407201003035950300b0704a5200300920401d0204000c0d869201400541d5a09113481450b03d400340c000c007520105440c002c103020002e00c8040d5480d59254030fa040b5500d454856003205a0807018a9000510242d070300314480389800e1701900f140310801c4c0a00070806c9007507961400141c5494540b110a40d12803080b9900b1711840448040104803c00e0f81d40440e6800d01c2265203071441c20701d0590750040c02d03003034210142491600c1080f0300c592011084d1900c80700503183c2048104640501d01c03444081c00740110381050f1108591402c540c80c540100c410307100c0c1071003500f00f60034050500b050455510b0b441c02004102002203440c0c1581a07207a45080e08860304a0000c013a52540000c2c01010440c050b2610010210310200083c5010351070368008020001c8800750008100480342c0d502c0440c6401c080e580120b281d41e8224100d500303442083c40022000517100f8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 740570125 1250 740568875 740568883
    0x503090d080f1303050c01230d0204081b12150c0904090b010f23150906130f090f05041a0601020f10020403060b0a03050a03230c01050a0f090c030f05 66
    0x40b5140c800c500c049009a14a0010703031034401224050425a16240c03280001142c00b010051019020350455582110310b01094500070540c803413071443c0050610741c6a100d01030510517030805046944901c002c4012640ca09911143c03031500c0384030014040c0241c0c4e003812000d590dc004050802e2441c020070f185802c2d0315a40c0158902944c4034260049941e10f580710002c04802038000c440d4440722200039581000c0070301440c031060b020020608400b1002d0880c82030000d5000c04000c0350400018031000c207603150045081000f0300300fa048003141180c185412041141c500700c0044141501303180620011070455045403508038060600764500303507036100041c0e14010b003449078025684500c15228001d00d90580c0500241c0703104410900c0704170321140802c070b20301105000240250708240800170011303005e03000c42c20804d94403e080c01c7c0781c403d04604103e15038119014034501651948200460910540b080d100031040c2c560003081400807544851695018030701000b07102e501d441c10b4000034094104 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 740571375 1250 740570125 740570137
    0x190b010e18060f090d020106030c05131e0c0e04180b1005030a0615060f080708040c15020307261e09030313140607200a0302040f0e10090503090d08 65
    0x401c6446030309010f031485807607150450340c4036410b0265401401d022841805540100c83e008a06010f1460800d002c0190300081000d0300d031003456880d0085030515030103003d0304011a2020000080c840c51440c809080c2c1c0804080b00d82c03050b4175140007041d414508491507102142c01110f8040700e50b4641c0c065400341e00140c1c20182e81032041202120800045030001448262400310300c6600ca80d4482060343c031114640d1104000c104683c000507a070034130444030107502a0141c88000f426554a00c203822005031031240210060b017000405400740700c085501494110800301c900c0d40b01d40caa18408030914004e00c1d0410040340351000a9840400303200040d03601644006090f40c5d40c481e942c2d110000c4041180c8a81d03240342c20b107107039901c040d031402c0070944400a4000c0b030310034004080e0720b01d03401d445510380c100c10350710000042c80400540c8031445001d01e500d082c0c001c000380d441940340c04a40707071800103020009054240388400c1c0002e0004401e6501030001030395010b0400207580b40c1201140298 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 740572625 1250 740571375 740571421
    0x6161b02040f060504180f1401061e150908070902090d060f060e0a0506060d2c07090b0d051c1b050a02010e040e2802060f0c190b010e 59
    0x1001c8030b0003032081568070000459030704460803c4000608801e048102000c640042d1100c0b04207000140030550600e40c500300540e0000c00012950b495100d00860810358030340c54031401d241007005001920b02801c1c501c42c049454204090f00618000f1026500c1c501401400212900410303d29182e440303007840c86a400354040028014400130302e2464006000b03e114202284003a0350100b4030042e0b4500c1228010580035040d145014005003201d4050801080c42d80074074a048c1032000e080c1035029140e46010b801c1000900300d02803402c1003640c280c820180c1d00314402c0350200325040006500042820520b20541a02c5190324588502595500810040000340884000340001013080120b285100207100340c07554603240c4a100c0a0004552890318030346195480f1500c14100440150b5400d41481032500307031221249502ea0110b81d1a4100c580e120b00c4400010806144c914018029000e800b082101e80001e40701c131f25101d00340080c030107108010001d00c400d40480c0ba07040500c000784200c1000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 740573875 1250 740572625 740572631
    0xc210403150903140f030a05180114090c010e0607060509120304050c01230313140a03082401091e0f0303080901200d11090a0e0f01050306161b0204 65
    0x10080074000905100b240881c0000c95a2049065030107130103065807840210156100d08540d505590b59000b0080036045c901d1603030802d202c080d150030b130034000c900403240610102c0308182060241113250424441d50349050000030003507949540c0711107094030308840c0c001d48089556210050018141100e905241100b05000010030050000c0041d144208070400e0341c808821071200001c65501521150707190032104010004940710503000d011840711503001e40b2031a1400d195420000b45000000ca9086000c00d00382400c02031000b40c0006880900c1801c1c0c5003029081d125400000c1190800d8041c001c84284030701030f040c6e0034026445004001c2c04644c0300001c4010340300c0c103000e410b4540840b0700b18420b600340840000f044030501c801c4a00100320360f9840342040854dc4080d0043e080c0035a10258000050151410301c1c5d45050b5804001d100030f0f03031000c4460808002e041c1002c80141c0125020b50700500c00c3c0001500315000700a1340901c02d14104002040c480e8a01020009501010790f029003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 740575125 1250 740573875 740573903
    0x12020d0612300c080f0702030a0c08060106080709060f03060506030712050c0405030a0308040f02150c0606040903120207020105090d0605040311031207031e0507081609080c090402010504091103010e0c0c210403 92
    0x3c030341030ad0201611030341000c440c541daa9452088420725000c85a00000408203841085061300034105409a0403040c18045251030715040420b440e504112049400039800d2982c0202100d00c5114031030304000b014261518060401012a617111b41114005081001110004003841070304403016102c45e82c000c3c082100c110f04001b112042d40c00c626911030840c05030801007a0f60b4909481401d280d00c1d499160780b5802030200018100035000060180e05003c020041180f595881c00c03150b000b0350388590800101c0781803a0034010015049886030401e1584208103a5104001280100b030703100880d4a004038081c0c403e40301241004018600d81d000044c1030000b404030081d00120014825030760046004540c0c01070038000c448a03540e51080280326040414500c0703041c200755007115403260045c103026182aa98045100840d848840240c040d94030210050182e88800300c41303160412407150845041c6070001c3d0384244c0b14941196080300e0500d0004c00c035020f544c0b00809507030007180c0100c0c40f200c040c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 740576375 1250 740575125 740575133
    0x906120f1c020c0117071103190e030a0c12080403020d0606090b10091518030803011406030105100309060f021308061612020d0612300c080f0702030a 66
    0x100700d00c145200ca10503005481c80e0a10720000f2044501141655004000b40a002e8050311520014000740c04112039846c0405410b0320400c0181040513820303074024010000e5441c020840c4c0514000c07582b003a0004004070b808603168174810000d40d00c50303a42450403000c540c9003440c801e00c901c2c1d100941216444040740144400b0364460000c03228682414441e500241c01000201d48640e4480340108082c04024014980c006811007110710701400c1031000100d01410048070300040e031b03004480002e000001031000502e29240c0180881c016100e0070704550405000820058400100c0004c0543c4d400c0d902080c08043e13000f0f0700c07010180300811981c0718035080d50312954202501841c3d5082c4140004030b03a0300125100a1114041d0a07541e24080c0003d80d80b010003e51300510b8014221501d541c00856010506e440701039410380b14101703010545241c0d04210414110070300581208050710524441c3c0c150704031460300101640859110755031202040345900354000c01001a405104000d0450700b00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 740577625 1250 740576375 740576383
    0xf0201141e070302091507111903051002030411010f12050903070209060609090103200604060f02010b121b150301140913030e0d03121103060406060309050a020906120f 74
    0x20304000004810a0b40e03900419816840340120040c1c03c80340045144404080135800741c02c2c0184140511504403180c5070010b0f2945460440500c000b0b40c09200410401c031b01004002084405020294107501c2c20f41c84142900403a071460b00d0612408001580c0028800c2d40c03089007100e5211001c001904200032484c2d03032900500d00881c02000e00101007000c40c500f820a48803a5500106030720305e42d0b0f0841d42c0f42007140c0c0341c0a0103040c1c0480c40c4440b1801d10359544010f0000341c00141e0b01d452034450f141078000d0039240d105400c14004c804003000250a401e000c902c4600701da2100d16002100550040815518240c00320580e0607407401000200b05010300b01c0d002c0ca45114225581c11864513041e00b03208a1403c5513400a000c90119101a00c05003055400c1003802c80c0a41014071044045600b141c0170741e880c01c00002401c1d8030001c200070461a26114180150041e468100810b17113448d0b481590b5009110b0000c2e1050b900080000d22a556944410042a0500e420768496036138880003603030f039 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 740578875 1250 740577625 740577661
    0x100f02210c0c010201051003110307030605040b0f180a080c1014061503091f0b0d1b080f060606090a0302030304031b050607050d120e0d050304050d0302040e04030f020114 75
    0x4a801041d1600042c2d42c41402401e000707003a0000d1405105156a07511010741035941c9005425004500780000801d200c1d00c511441680660789415040c608602b408100c0200188120404443e04255048259000400820f0b46501095460b40c0300c803a02e0302c15141c0049007038890740e80c605201d0001e21007880300002a00890081c3e03981855a55070390040220b5005c201e900451a6001c401d03500c64945130801c0251406040450000b184c58a200215680000c0c0b12010b40c1e61305605407544405521000420006048a074060f00c07001100d890490345640025024910400010560344065611101200e00a41d40103040fa90b460359070340345c51041d0180140140e1000400f1000c00a5035007407030750132610081d0340310000d0034445201420a4482549803200c4c3c126540c2d403500d89242103d02001644071400c5191903103501c03454140740451074086801d83c0202058018001080f00091100005801a80c1802c041c1058038403050101e0042990055405882203607109001810880c0180911 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 740580125 1250 740578875 740578897
    0xe09180d031b02031c3b0d05090f0405061f2c1309150c020c031c081b13121203110409090501150b1b0c100f0221 50
    0x1021a0b4038141642c50340144051140411650f4100e45100051580004059002040c1d040782c440e208401b05024524003040c010f41d10728030b0b07050341c1c0c140a03001c11003039002e00c80714a401842c2c0a0400089400c0881e06041c45002c0d80e00c4501080480c0d0300c0880482143c030811007103c000600341c40c002400c524409421112507220b1803074001e003009012007206403540e0060104001d007440141c07814020f103604007050380d0b141c020488500840740c00b4050780d03107252481d03401042030340748410800d402e109118800760146c9510880c003512341034200251a6000240714a0070f403100f184003040c03180f60b104404c8030f0820081c007058003155010700c0c40807d107200ca0160788501200c00c00290203404540000003884505082400100303e036140302d420002030a4031590000c221100030034407921501a864102c10403a6502044c50040d1196003032002d15000d00300030041c040000f9020200d03416100e104540c10410600414030b51030180200807940789000303a6000008040c00006064000d80c100410442c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 740581375 1250 740580125 740580161
    0x90a06020a02061c020702040e01060f0914180307080c0d20060a0c02030c010f060504230c030c16050c090705040f140f090f090705010804030e09180d03 67
    0x46166480003603003965081e8041c0103d49042c019004000d4820501940405010f03005c100110058541d8000e080039103403000300100c0e004d800c0c03184e0103800e800030360030160f0518500000070035035050040c109070f002102d040c047d8560b4080740400304d04500c0344c0080038015110000c2c0a00149078001981884100d059440c2c0070701c045801d850101510000b810203000f0b90004000c990014016884058103c01c0c9004992600c030101c0718450954084c00196510b0580d109001c2120f4200b50003039a103803080300d80c17400300d840742c0134410070b200c244020700046860100400000c130300306503183c101c0c0e0203480c1080310070040e4040ca1501607669011090124042c21007000030411684c084c07800e480070b94425510110300d46080402104c0541c0c02d807040b1aa0005a0f1002a0501d896024641d801210342150500f81403606989041c503201c100c1e4403240c10858030b0810080802d601800600b607840d42140c0e22407a13a02d030301c00083c01098811030141780b18040d981200004640582c082940d00c80920800d03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 740582625 1250 740581375 740581379
    0x3020603310b15061902010e070909020102030f0304080d020c0f1b030d0e030115080706090602070f0509040c090e0102070308010905040b192a0e0301061406070602040911090a 77
    0x4201c03080c88800d0001c12a240300300c0410320a52000c590a1941000903100c5820403c0f20198034945030a041084005030755208580b4841c480300740090806841082420310480c14030b135000035543c1c0700d0002c204124800c08808a81080042c03011540c541e40802c00030f46d15140e8404040d0f4130b80c4481402c109152080c0c3c5000074480504850300c548030351004001c0c1c02515400d0b10b0594411714103005255141d5641d0f00c501f0941009001d450300a41031080c0100009130401c02d0280210380c06400400a40d80092010401f40001d08849c2d402c0d00d0b420b8035101076640f182d207440003403080103070081c89505d42080b1108072110300540c00340910900a030f42d490131a0343d0b2800140c0850340240d0303010b03040c110000001000d0040c41c5644140b0201d1580c23000440c224084c4201c42d201c01d11020000e602202100c030000d0f1560300c49113140408070100c000304491840d20508524503440e03480c10600a107808580d2905018451703055500030103440406000050b18070324458200c0e4030030000e03030b44607002240c40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 740583875 1250 740582625 740582701
    0x303050708071e030f09151509060b092115071b0c030308090f01050907050901091e1a030a0b09150702060402011b02030d030903020d0c080d020c0703020603 69
    0x210340d100400f001c00c030405859050000b280a8120041002c2950340c444080030002580b42030807884020031150001040b00d644ea4101030b42c0c840b941d114030851401c0840a101c8800d0010840d00d48940850f043c0390200d142001c0c58011814070401a445405004005082840d209031810300c90301c5c3c41d5031082100800600001080109004054903c280c001002d2002901a580c15608060148119207220791121041800c2d200102c4071b0300c900342c2010004111904040e0801c1d03002d0040d9440c14003181c148241d003041007071890505c5400543d100d86090300c020160901142d10f0160140c19201000201d09000788000d07005e031040740f03180c4030b112070a04003a0482e0701c0c054042c20941d409404030361502d0b0011a50702d905c0000c884414901079440000680d0100300950700c405e06038502003140350705810083d05055015010209122000082c0c40c00200c043c0201d4032134000c04803005844044480c400c901d44025a08020340004001050200f01004180e10440000c059081d0740c03a03039242094 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 740585125 1250 740583875 740583887
    0x3080718060e0616080a0504030302011406031908131e080106030f0f0206090a0810050604052e080a080c0601140d020402210a0f0b030606060a2307030305070807 71
    0x1c5003500040400280900c0303032400300c00800c850113501505140c2c4104688034034803682c1c000360101000c11030000701003081540a01558504440ca0300075000c07240341c60b8000c41d484010f03071000502400e412090391010000315030b087c0c491084118003603140c0c140e00c0d070b810041c000c0c100c4800c41210014a20380091004014028001500d40c890417040c5c00012503501c04044060404c406c070b074042d1080c0848070194891079141c03c000d1000c8801070500c1d410148508084420140407907002d075046c0b40c104030842c0008000044070118015030100840800d1040f07050000081d00b040e0010b0056155003028400e0007800340064558000645801c3e0741d0b99a100c01c1c141d003103100c9298020342805034880151501d0303030103096440240003100d503103044a2444811000d03030450300510f00d50381d10035201030203d6142c03060703030324642081d4010005030030300000050175030188804480821003e11f800c20a880b0070300c1816070003500c403004215100e5482d407078041c002d800c0848684d40010081000581003d100e84 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 740586375 1250 740585125 740585129
    0x60e04292a1e0f090409060227090c0a02010f050f01060f020f0c120a0213290d0605070917010606080a1a0105030603120d090c05090c091c02090403080718 68
    0x10404070340449100e98000d030540c10030040c0b001c4002e010b00c0240135030340300c80c002c0c0303105c4034800e00c07005907194841011450400e209020281a840c604030780b0380800d0315400c0c00e4507005008404000c4d15840500c034120701600c00601412881401c002c203210b4020928040b85040c3c0d8141d0b140c08010004000e8120f80c0c5150802901d081030b0f0000094140d203040c50a5403c0400d81d001040c5c854203030458010444404141c146500e41e40d50f00e640c0713600c0e103070076100344030718500844c0c101900c4012031040007071920701003c01c000d0300c8555920042004240905000b00041905070501c5028480150000d0300a0a85206800105a0000024500240710b106134440c4a03280803c4c102050032103001110a80c02c000c008035098410380390325285e40741c45040600321034803103140003040030480c41c80c0401a400039075101e98021080842442030b460030120030b5481008040c0c81040300007400302c034000001516003402a400103141303018031061561240400c0d02c030307011640f00c01e5860040c003005003030201d0480c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 740587625 1250 740586375 740586397
    0x20405150c1c080f060a0b0a08010603291207080d080604061703070f1509230304050901031709060d140903040510110304031e0c0504060e04292a 64
    0xc0c41c15001d004d001ea00301d040030f007030384440540f600448500e41d03000041c0c90300804d03007003001002116414064141000301d040000c900c9500c41c40a18064060f45003561840340c0500d43d1000309129003088514018003148045031140800d14001800800b025140075005c5d6041410104008a00400e101105e0480c140214034140c0030740c9480300d01c004801c02c00c0f01d00044a03000c503281200c0c2c074020b442103580644d42082c00a01e0480500320501d0843e8008102500244401c00403030b6504c200803030440e034000c062100d1003190700c404440144100f20000e50b000f00045105202110154040c55902d102544610000d80714928295171b2801184152503110850140345c8a07010b20030b0714170900c82080401202c3c2002d407241e5441c200511484803441c5060782400300030060248100082004000681e0100002c60801c01c40c5414640000d2000d804107070302070298040080e0710580301028100314841c003011400c050900003c1c04601300507420741d00319031035200120550341d44c0c2240d50720110 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 740588875 1250 740587625 740587637
    0x6071a090705090c07021f02030408150c0a050a260a050601020703081b0c0a0308130b0403170c16091a01031e271b1409010b0d020405150c1c 62
    0xa001c0d0b0074401a400351710120b03000302100d4a200c005a201078011034207041180c020b982c445041074040751500742c90742c2c1400d1039140103005204100300103004842540f025031501982d6448103402c00d940690750030005440b69030500503107a40424a8500c418002c440038001840291521401240e44010a01004c1c1280038100081c012035660355401c0540e03c082d0105941e1040000c0c000100308200c03690060310fa4020010301c01d40c140c1140074444c005859050707410b078141030a648a01062070b5268586110214001034580f096480030062401050102070994425035245c09480c0003034079800c41c907000004404440e28036a50301074000c0c1022034904181c7d9885081d4008600300141504182d4120050034289021102d00c4000f10305241d128010050255051500d9070301c040b00e40d065a100000007403280f42c444200e90744800c0300d181113941c5181055110454080204020b1003187d00107584038066403483c0c400a440769000e0429860900d050310340c0d00c0103c03944451419540801c240007e51 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 740590125 1250 740588875 740588881
    0x1d04061b0806091302090112060e0a031205190504060911060f07060507171e0708090a1b0510020a0221150408070206180a080d020c060706090206071a09070509 70
    0x10401002a4130240c000001d00071141c82e600402c0c40f0180c01e07000b4401e0001002041c0c400c0c0609400b681c0054445100101041d00a544008013004582c80c2d445091a4440b000b02c0c0c0c281ca5000008400ca20318490104200e050518001d0300170071101d18210b4880c071348280003030820718001d01642e070810019080289081626502d140050100a04550900c007028800132951208030303417030603c0b90546c83e038000101214903401c01021003000348031030304000c01d001c03c112210701d001c00c0c81c002c81075102c4c4013110392a000e00010701d13141a1a82040390040610010f48120950006030b908080b4002e807564507100b001451281c4110800c0018030711203510104003006014031803920554064020a10141003038050740c0094030b0340e4807909450348601580c00000d0900c0c9082041030009189050040c0b14a01e12070001030b440300070617a0018403882d408940b403002e02c1000e4002c141c1031035008050580e02c1500d031038820b540642051208a0144907036000440c0306500044610030348100902d9140705079 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 740591375 1250 740590125 740590129
    0xe01090614090402071a0414070803041802070606081f051f060c06061a0414010f0906030b010504050307170712020102060c09130e0d0219020d0b0705041d04061b0806 73
    0x140c08a034040307810780540d0312902942402c4041c40c2c0c1c0641d08c518116007816056015081c580304058000e2111500100020401380445e94103140640c5800c01e40961202c0881c100b42d401424a5401024075001c0c00016200d100c5142d2000031001044c200100901e0700c9403180c07901c3e140112002d46403c0081d1010034001c02d400f810000c07090724410040826155142e2042000b14502c0c5124100c1c511008602030100c940d254801c99000c090a2810080310030419800030a5038032036110701014140c7d9811400d07110391007281214040d2401400301c0305d0540da28500b02000008902000040740164a00898007403032412202c42050740590040845031100b0501003000e5000703402c0f032507100307401d4200740f603006100d0300884003141c014802418400058007006801c024080c1d903d8002034017024141d2005a072900b00c000240ca0f081450384016aa50280a81e2148a2900070040c01600e0020215801002e40c60300ca128500c600000d02c210205201c1050b46400c41c90302c8000410714240002e40b00d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 740592625 1250 740591375 740591377
    0x1060e071d0918190f02010908190206160b10150f02120d06031a01080610050d06020904110304051c050a053c071b050a030609050114070e01090614090402 68
    0x1d08490580f138004002c20007100e88006541e07070803034401d440a90010107568020400c0401000030202516020401c028100d40c501800003000b4802c1d400401c0301480b2102010b24510542e40c0804526120305002c4006940d03048035120340745e81309000754846c0c40100d204480007101103810341c0092200c1d1915000d4030030f9682265116944c45582c2c0d600000100e94001c0081c060243e110120a0300b950402e0006070070a140100800c20340740e0103c104011944409880c40300b1150414001600c1e010f0600005000d88401044c129102c24084140401e000303001c220189144149070218040d44030111054039117002e9048208003180045c0324070f01c10910510003012a05c110011104002e065810a844040881039440514550040f8240d400c110030719140c08020b0f00309041c9181c44619090000d0140103890200030005612004022304010094004031801100740180324598500100020140140240c0945c0003030480440003400f64003030054000f050020910071890860401c0a000103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 740593875 1250 740592625 740592661
    0x6190c02031c080703052409090a06150626010e04051006180e161a07060203010b2101150507050f03030c2205060414060c01060e071d09 60
    0x150207001403070740d04180d48825458000c00b182d00c941c501400e03c2c000090891300014410f020032a003c0d0101151038204800e25000c900301141c40c206650307a11080e850070600a008020105811314070030981e0341d04000001801e84c0c001d55500032110000038010904001158500c030b4580140e080140040716828100607071003030148040b541d000014011542c01ca402c5980f06803501120080f629500340e80701d00490122074148401003181c0705049a20310a0340409100d1701400020a00c20641301000c50015a8402a000b00b000c540700c2d0794a03425440b00740d000403c0c12141c038410040b4200014410120981621354040101c0b2000ba0a410305071b8150703005400580e4030b4030451240d0264040c0c200021481045c90840c51a19005409203c41c04042c21010303400340e10240c0c50042c0107039166201518207d4038000e03201c060030322122011070b1140c4550804045c1d0ba5007494004215140301d070303655034098801542c41004c00000041a0820507101000d101c2d8010420000310b0f5140404844c0445 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 740595125 1250 740593875 740593879
    0x8040306050a0b030f0d1808060a1d030412060b04050906180a02061324080c0706110a0e0f040b06090f0103060e070e010305070503012909060708030a050606190c02 72
    0x120319208000003172814410226244003540000d030044001a400429620b80418001e02800d0300ca041c04102501c480c0000c00315540141d0740e0391040280c04080c51400c3c050f00c41c030800d4903580c58407940308800e2000385002c142c6c0c01a0038038152100500b4280300ba1449403071620f0290480d52501c0035150b209120300d50005400e4032a081d03806007d0781e80c040040c0b1b47c040c64038590700d9400d8544015508009400032a00c1c14959460304002d030115044414558050340a188541e5034144504d4508020804554144014400482c0d14500e20750031802946e4521000c0743c990401d004011b04210a885c0c04417003031a0071150500c4064500c1c2081484803010b603205040c040b174000c3e26000442d913803507421a81c075000503d000107001300c65605842103640141c09403400a01d15810004443e0886181e18103440a02c0ea5840450b0318a00c03186040d2440600010000d41d69003e29003800d4045070000d079001c000f903030710b13144c00709525160a1045441c00c0301d40d081d40601841d007482041d40d10800180301a0303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 740596375 1250 740595125 740595131
    0x50d0f020d1112130e0112032a060203070e010212040b040e06040b090708070f0f1e02070308030c0714010507020a08130e0406050a18081b0f0f150f010308040306050a 73
    0x380c1000903c40240804414100e008280740303241401605180c4c4045c0c0c88440c810141c11002400310b07a01c00c11a0360f080d035402c5822148071f1042690203403481040003001c0c7c4164030120070b00c24140c1d4490a90782d0b90340c1e426822141c015500f105140050700c82ca10501107403142c00c020801800c0c02d00404964089070082c400108600950046400c1d440d040b0303103c20002c1d4051080116240d040347c14440c40c50124540100c11440041c005483d03050100c40221408100803000c07824503108009400c0034562100150f03440e410101c519040581100a00315101c5000e8050798940603c14400e540c03143c001a0300170001c0031400d0f2107100c01a40000359650502c494070002080c2c400d440031286015503c600c00008091410305908c00c1140d43c1845107440440101c40319001080010064503001412240c0100082d02c42c034406a14129181103034000a00408052282101c40442c03070b03c400900728906a40240d8522165010350842400000c2800c6002e01050010481c5980600e6220102d02400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 740597625 1250 740596375 740596393
    0x110a0806102003070c060819021201051203070204060305010605010e01030e060708040528020f041a01120b0d0507050102120408060c1c05102103021005100f030f050d0f020d11 77
    0x10104100150003030700c00324842a0078440c8c182c200f00000014070000d01811420031080c80d098007042001031194a100d03c00ca0001410901c00906c125848254014401c2009655078030f03025000c0e140510441c2d0105464280b02c140650180c0101c0c01702400d080c1c060300c078036541d6141c260380c0130380081c00582d650701c00c8040d10314120940d0406903040d2100d1644034041c0340c03082c2c410030240000081846010314280450303c44140200c4607030600910003406c140480c41d049103d0781005042802e840d03503201300200305101c18044085115001d40b1070a90a03541180c0034400801000c0c4258070406c0b06581c000000110007004500c05049244440d01c0f00031a100e07100a154020340700e05803070048007824058000c11840b40310b0b00100400c1c203810b055a042041c1242c40203915510900c6051480a44030781c0043c0130f180504140703c1c00f40482035001800ca60b01c0b414108000b100e44041100d0350b214070081d40a640780280b01c0f2281c20441c030b81c0144483d240030b8004a91503c1c825449150521502c41f01b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 740598875 1250 740597625 740597633
    0xf0c0305030418060f05090f04020f0d0b01090e030301261011090a1401050403060203130c031a071b020d060b03031b01050a09020a12080d110a080610200307 69
    0x4100400e407580003500e04503422002c03d0103c1e50194401124808008000c109a0300d88500c0c0d150321000040000c2c4243d46c442c0045416141c091381060f9210b0081c282a0041042c0c59210364140e03415004200300c1c941c84102071964a11080c026129018443c3c00c0819840c81030150a202203401030b0151402402c0d038040d00c6090350001c40c01007848030700c0030074080410308001840000518013404454000c10b59540060120310644c040602a1600000081c0090b0310380012015021ba1008182c5065a40da007083c920301100c03000301407480341c20500480c1005101d00d9111032034000c151401c259250703c0360700b000194950300c1c2c021a03002c0d03110f411400e41954103201908510014803140303010303c58074607000d81c2120130040c007002c4410b1a1082d40405070311010402000e80d81c0c910204040c601c82818150014000d8024004c001e03414a8241c00365400994098000600c2c01c0d00c41102e540c840108210544244444c0076002481000d841203110310010540150f030f9103142c2c192485d05c0c0c0180c032 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 740600125 1250 740598875 740598877
    0x70516080a0215070506040c141f030f140c0307080c0307020c06091f0f0210061802071e030320072a171c080405030904020f16050106060f1b0f0c030503 67
    0x3e023520400038040c420001d500d00800c0071078400c002100d0984900d81c0c020440c568a1013044080d80030150b0300c11001c100d500881d071140442e880024003200c918500610700c0441913004407a5140094500c1021420404403c0c041d64080e010540103050f45403044814421a600828941e42c0c0c0004510602b0701c0c3c161041c2201d00060300340f0795501c4c1c0031b4801041c010349004042d50000f0125440d00703104001180b8105101c0c1104401c1d001c0243e610340c102e0800b103c201c0030b080541c10407402241d00c11410180c00d6444030145140c0c0080d41030610020700c3e00c2c621075000d80c800190048600c070102912600001960300714940352aaa6000250b8580100700e003d1549503402c144036910011400034106d5114047c3c2501d4000c506d0018041d00d85a0b40310350303c0340940340583d40036070307000309454203c04002400d47e05045a0318111002d10192418018042c10442c4500000f081e11141c102001a10079842a1115488483c049041000340d90f50b91303504000b0200d080c3d81212040c20b02100182d07080c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 740601375 1250 740600125 740600131
    0x6020d0f02130e0612061303110303010603060f0b04180e12040e0901060f150f020c120309040509010605010e090c09040c051e0412080c070911070516080a0215070506 73
    0x902e028024249100140410030140c545446202480030303556002c8800500682d009200d0f440c8250080300901c0d040e9a180d05040101c0c1203408088004608203515a2000080f9045175007c20501c60395040e5142d118421030054041680700203a411a4501c40758114149040f100782c107c0708050036001d50800d050b00582c1041c00100803000070302c08004002d000d40c03409003003a4107036a0101450280700500b0002c09641c00014400c00782e07840b0300954020710001040b00c0c0090208100c41083c0f664541d01c07036200341d1405106500e4800414510401441500103403541a150050300c1c2441004000010100400f100c64064041000641544446c00303040c0c0c2c0000701c1e44640d611441c11800d01422068000d036800d41c00642800100029000407a0b0312400d280c100310141d5030703440c10680c05070070301d40d0039000301c01e042e03003030005c202400000341340107001c1c4a010b80305548040d21401414010007203d442040041d80c004c076280405460208500000c0c170700610f20091801d002030b541c450510b0412 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 740602625 1250 740601375 740601397
    0xe0d0204110a110609030913390305091f0e01020a0306150806030307031218140c01030209060f0306060721140304020123090910080c01050c0a06020d0f02 68
    0xb060880c2c019402c51000c101d02540000540958641301410769928025400c07818072803048003003044542491a84443ca03401400000044910080c0c94243c400340112003124105c3e02511540c14216840303480341c28003072000340780900074600c041031102c0d08103408880c13100f1030300d60760711240700159070244014040d0001070341300031070510700d03094500c050382c95410500c030107014004040040682d0040111241980d042c1080241004803648444c0200321203e400d07001d490042d0709150500013504801e449140e03004040f60b60407841040114160b01030140481d03006581405203c03281104040616480300b40030f40318500303111140d00d607420a1400400c10180c032442941c650b1280c250702910003d605191034544034954100f5074002009034443c0203c0b200d200050f00d8240c2c0724202c03100100c071900d201c000c240e98140d040214440072041454407841519205e00102c0c80411f50140082d140d2a10175403001c4c101503459501d4500203540070404d1401407503a01c55031262582c1c5c1600c06001d108100c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 740603875 1250 740602625 740602627
    0x30f0809030c0709090c0807060507030c0809030303091006050f01050f0309120d020a090906061d040615020610050306040b04110a0504020f0a02010c0e0f0103180501090b040302070902190e0d020411 87
    0x503410200d80c2c0d1b00454110309015000320b503040c01610b4204080312900c035410315010000850314240740c0000e006d907a0000307502d0b01001040c44440d001c0007410909a042091003002400e9440c01041400f03201209d00a011135810300107515170b10f0041c8e000e5a482503286050f40d02c00d00d903c0301010015884002d1003407000382d000c110802740701e510410031000f8016481081008500301240070b080d40004d19034229884a20258000d42901c40c1c0e0040d00040100c104241151000c500c5c019459a40803203c0c2d00c0c40c28040100000c440c5400200d00d4012500008803040a482d0740c0c079411f2190680c01000385d00200403100c001041d0b103a078401010040504800e540e01c4000c012002130a41e0190b08600003002510031130f4460664031460407180c0710130242400142e40309108000c901a03500d1090142070340d440d0829160a00244841443c4613912070360036074000360344440b102022401005c1181c0741c0d02e120324080d9494103010300c145000315100280408480302503079000405880d001985c202c0c2d40030b4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 740605125 1250 740603875 740603891
    0x1113030b0106120513080c150a02070b15090402130902150408160315090203211209010509060f0402060d0606020c030f0118080906040b0307091809030f0809030c0709 73
    0x40d001800c00f108008101042c4140e01308502d5001665550f6071000d4080e40c000524103a2148082001030481d90700103003490a01e203026042c45000350800441541d001e4a24800a40344d00f01c0001c01c0d42d00284014441c0107543c48a40034841d00641e044000000c85a1b10841c450159a910140034043c0d244405080d0307840d810b122580d0300307003e504d90750316103c101c17098000d00000c0c1c0c8002015450f22100303c000a0706070802d000007450160160b9130104e091700300e0050042001d1025008110f078122414000807a5114015264225001180d05500d0354024030081810f9017003445850b40c04c180020140350420000628045c00ca84295000c10050382c040300d44003450f800d044c4140f101310010707070008124400d00c02ca13a044881d0032084004000e0640012041207a984680a0320080c10742c038640e040c1c80c0e02c0c002d1805001c50310a40590f125094547c840000c848a42d40640211280d06644501503864080000d460b58400640000e4013400107000b144480c64041041d40000d003501100401c42203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 740606375 1250 740605125 740605127
    0x6070513240923060a09050909010c14030c030109020d0b0612010611030906030f060a030f0602030910050402100e12010c09031a010b0a0e0d0206070615051f031113030b0106 76
    0x90700c2070780180002e00f0500d5030240350054012400c216107900742e1314280d48038910700c2c0031075085d8201e40200c3d034024040f030140032060005601100f040d40710350300c850302030f00c081e90398070750711800100c8020302d200000b000180089045500941076408045601290000f00500002c540d80c00c040c2c00c2d11580754041d801006602c0d800080750b446400c484014526001c0044045040b5100041c00c1000380003c0c0004607420b5140c0300c808000850300301c41002c10066a900e0a01c020b580141c07548181c5100b40d013401304800d5900d1188500a030f07801010f60700c07551a50101612403048a812950344402030705403007181040c0038040c4100706841ea95075943c01d00e007503203400e4640112a40d010303854444030600610880d00003a00700c0d00c2c0c0206608041b0507140c0308000003680f010050000940010021814800b00703d080d401c4003507240080544640030319295010f00c0f54110341d03800c094400420058003401000e0180d4400800b0b2030091400a107022241c50810345020001d074003c940c40c9c410080100581 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 740607625 1250 740606375 740606387
    0x30305041b060c06020c0f0a030804050705010e1c1713050a0b07020102030919030609060204090c11071401090b0316080903090901150c0501050c0d0e0309030607051324 74
    0x100d110100607205050810800422102c032243c40185503507030000f4111100300041001e44c400460700d40448840d4000d0b4a801041c038032042d2021210f030303c00c000001c1100d600880d2001c464000142c9901c109200300e801c0d424110079252801d0b120700916101c2030080c20210f400078040424009140e15000d031031300c0c0a100b80c0c2c80240c2e20000c0da114040c4101c0300140ea01000f118000c5001b00d508001149a00303154442c46d442c17651004005078a070600c0700307080111540241c000c941d40b660b802c1001c01d0102d0001e481504003001d2080c0f06421069007800384d11000010300300c1c114810b03d800c90a1a48443e402207142d482514032400250403010508020350b4012031890380040e58030701460a101c1108c01185000380103002c1c0040000d020607020303040d80d118212004c20b454015000784800e041548041645500c101c54607040b030390601511800741c42001089522030440a8000c00c01d0b039172184800c031416000a1540d02240d0240d0030b001441c84118503844580c60b602d10039006c200c81039003802502c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 740608875 1250 740607625 740607653
    0xf0f240904031e2307080c0d09030b090c2101060b0c0a11061206010f030905151b04032006040807092403121409030106170f032a010204050603010303030504 69
    0x4201d811810700138032104605407400741c10b42e08801c05465601a02d04100607026003030001c0f225208001c44000300d2988440350408882c050740303c002c1680c03101d001ca65100c40006007825081a0110782000440c035020800c0640041664000140c1e6902c07014010790341e91081c1c02030405a030111100c0e03014800300001040e5400300854201d442c01d403203402d440d480004c0003440103041c040c080784011038240c040d80103c0d01041c0c0c40070940780140345005022240343c80c1541c00e4040704401404d5056950142030448090340e402c1340030021541c0f891000d007400c86807001c28180d0000014800010384200c1084107801a0003941004a0312018925081944511a01c4120140000b42c42c080000c1040494003012203841d1340b0380700a040403282e822281c0c620401000640661910b040042c401b0903c1c0301c03510020042100b92032040071a0190240c0c0e0780541610740742030007090090543c40f59030210b0303860301c2d5810441c009424559114000740e8941c000b41c1c019800300381c8a800f00b00820202a070303002c035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 740610125 1250 740608875 740608877
    0x90b2802010b180712060e10050102010b1c0507030b0415050601090302010e011209020a0b0711060c25030506160f140d0b06070b0406140f0f240904031e 67
    0xb40924600009401000d02e12150100300b0031003002c1480d061080404c0c030024810008144941c5686070f4200460803022500360914008485c07000c0307410f6206009120940000810401003001c1501a90310702078070700c100c200c4d070034410000c0000010b4028113549114500400ca2111680300130040c0e101a1b4400400c0b590421001f0320b003d10050780c000012440040c020301e00300c00b5000440c44d50f14010000124069030008400c0030024409160400402c00c00344108140074040310720b2000d001d02d501410050480c1504440758200c03100c8061070b00c102500d109215070100d80740c1d0301c3d114235003052001d40d840a40075011240104403950070403052220780000f494100780e0a0010040b229181c0a18443c9210040c0c4401598140395203081c285e5800580000c0c46403c1400c140c0b03410300040c420103c0881c0311141000005052400220000303108000c610030060f05031340c60074410f2030312446000c641c0c460401d442c801e415494842c1e06e1380750b00c2103229031182e048007e00c0288034240c1d52081041c181c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 740611375 1250 740610125 740610131
    0x6180402030a03050d240612060e01290c012a08070305090f0102031302190602060106081003061401050406140616020406080a0605100b0a020c0d0201090b280201 71
    0x20050300c00041502c01190946000c81c0c8070941d00140740302402500c1261513401c0010f07038401005810000c0c2120488406031200300c520fa8079a80a00191400c51142d40d0043d401c4d0001000301030b01d005d10880e4009004a11507498500c40c00e02d003000c1e40c0000241e034407642e548091a054108000702101141042030200b0407183c00c032900d00810820303005140c81c0805480e000860501c600402018503801054002951a0701d4104102009101041002e91080090245180c19002e480c68078105840c0240d0150955a0030090190f42e140c201406014404005060000c003040c480c0c4039050803d80104402c2c841035140c401017005a5103280c12001e0b84030b6281c20110150742d100c0007110b051001707050704448085010300008004000341da1017020a802141807100401440d6403000b449000c41030300c4801120b46844c440009030151306401009a030050005000e02c2c42d0000103907203098414036000308038036140e038021902c40e005480501c101c9416600502540c002000491450403800c0c8020 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 740612625 1250 740611375 740611381
    0x30916140916090f06180b070b010e100b07080d050a060602070e09030d0c11011b08060103020c0a02061c0b030d05071704081b0f0a36050705030618 65
    0x2840e9148040d1801440d44400c991a880881c02050b543c0000d00300100141225a80c0700400b40003031415551014050031944030201c1c000550005440301c00340c20441011290703082482030f002c1c2d40400b0340b10040f40080701000051001c0068028540648103540e040d4070ba02c0b09020080c251040034018044aa00301001800704941c0003801404031140d030301c0c401c2c600d03440b560700450030b601c03c1861600b0714a00f03220084103c241c012045000c0e802000008110110301a091304070a80c1503807a213540010040804940558402c0e0041e00c0d01003100740a41d0042946540011480e41c000007c2081d07442e290b01c9509041101c2d40b080c1101a50250050043c1c4011040300405c2c0e803040c82d600038200c05905d854110088125002c0c0c50241c0904403c40d00801c00045044040194044070244950306101c007491046c00c040d00d406088950f0740300303480d10b0154503842c000341008200d54607456407a45240c40000818441c01780320700482c800d0701e4803942c2c1c0c201034060049150340c404d282c1c016041601c0038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 740613875 1250 740612625 740612629
    0x522121e02060f18180601120c090509090f0a0c1404050606070b090f07030c0e0c27012105040c05010801121b0305030c0609010608010e1002030a0b0603091614 70
    0x12180100c600d0307070f2141d646120180c0d198008000c9040c40d1070b04001c1d25906840900d14960b01e09024140903203541c03001403868040801907655030900000003400340c15041025042400c00700384c02101ca032050b01d010200c8607a04a16000010109403503411217008100310449440380c009011401c00d40d014000d61401c0ca000c00d4903881103140003012480d00200180300b584085c0b100103000002482550100382d6642400c00c1c20f10307040e000c3e41901d4642100030540f028941421200070300102a0800c424086540105c0c1c05981102c640c0c40c148610401c04120191000c42140140341c5c41c400005080e051506120080c501180c2082c1d041c400d9650046c0314110301443e45201083e40040c5060303414145440517428000c40358070041076448040350314003685c01d01056040c81226080000c01c40300e0742c0e800717940742621048128120030707400050001d554884990005c3da40103020b03c4001c2078154030800800d0700c4c0d030310485044da09600b042c5c1c50540c0340c44c0e14001180042c84120a460220050000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 740615125 1250 740613875 740613877
    0x1a010e043b0a0309180207050a020d02040204090f020301031502072d0b01030b0702102007060b06030c1201050904020109050405060d0503130609150c030522121e0206 73
    0x55516481c009001d4902169003422072554a801c94800355488103482c1e01c1c01400c40354590041d8064501c40010030150040a80b0a4416498001d4002c0c03030144d1054007131011290070308409a800c0f079000c110208180c01280501030490b1102c072001a500e40c5076051010010030f0a003402802c060042001e480800e004507000c4004000c07030181c2c003103801440c030b0a60340030408444009160300c854400000c01d000c68601801e1003603009400340d680250a4440d42c0c003c84220501d010303c130790007010342c00c0c0350010000081c0581c2c0e84540030008500790114001802600101d510519000000600b4111408031078071803030050030183c40c907080703604041d4000380c450304880c02100e005554440008140f0380c1c3d0910211141508202920b6540c1c001e4901260090082d01804001c00c0a550000620001903c10b940d0310f50f08591382d44810102e203a0b000c913000c0d44145446003980c0d40d420700451a840c43c01c0c10f120018080e880f4544203004e511300c2d1811a0b124101800c2410b01c00b0101c141e000360f140c0038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 740616375 1250 740615125 740615171
    0x2011206141003140c041e05010f050d0905070f150f0503010302270a1505060c0a0201050918010608011d15010e04090b0408040603140403091202131a010e04 69
    0x11551001d4080c0b40c0c00c00c90090074200040002d1401d040e090050550b6900010403c1da02c0c4102080000003280d00000256040392007098001501900302100591250000c2c4c252181c0042011804200301c0d00e03217601e441002d40011244860340802003111010401140d031040c100f5080408107000c0241c000b800741c0c08140b01c080c3c0240484078400c2050004002202071b00f182503568a485030802e40785010082104420f0360402da258120081824641030058030721054082005201c41d01c031990045981d07400c01041e20342c0050b0402c0d032030b00710141801f50300d501030f014554815840e1340c548000c1c58000300340840003200c403040c0c1c00140030f54940128900000c0d00028200728404c01c01c0c000205004081c410740160416041105001c00c0005100c010821210140e070148407522043c0c07010a140141038500401044281400f002180e0540c0c688540c5a40010900c038884070401e40700b8001d45025621020305041101d450300a650b0300032540d849001c3e41035400308070000645100d503900401308 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 740617625 1250 740616375 740616379
    0xb090907121e150b1e0303040306150b0304060c02070e07020606090916181b0519050f070f0c060809030417030c1f290f0409060203090a0201120614 65
    0x1c00744400d00039200c80d8080e08540c0c1d003c0c3d520200385240c0c01070348009200c180c0050b88205d900301410107684c1602c00c085181882e00402035880c0525503550b46009000030101c56011041c080b4002491054140103140720300d00071342c00800c0c01510000700900301005c80c0c1140d0f16200207402482441580019000c0c0e0100090720500c10355100c40000500c0d0001c4030241400f110b904401c0480e11040d9240b03a040c0411102e4014400301c0c041e00102e100000980490b403000400501106051542c880899045c00d0314504081e842e0542c2c2080f90005584100c0f001c1c0ca19640b0b2420010811040440c41c03402010b803460161164100311481540b20f102d548035600000d58280b00034440010144103e504c0c15130204200e410688d4850840c0b0003944045586450152038400031030914413100341a644d1401a07440c0403111075460718100f11441d03c54100300d40d0066903d20403031000038031910045016055080081c840f07025184001804420700d0240303110a64200902008041c00c04121406013140c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 740618875 1250 740617625 740617643
    0x90f0b040204062115270c0f0305091c0c0c15080117060108060a02070c0e07200f030d051e150a12020319150f020414010e1003180c090b09090712 64
    0x5200c645185546c0d08052008003c5c07901e12601079040e041046511240541d4805100c10759500201c19210380706140c008914185417207081c41c0703240c49820340d401c1c000d220700e21502c07005455101013004080440034080100c1c4540005010701c0700404981c484003400000100450341c1449115921088080d0007008a61340115603402006854445c45002d808941c2c612a003d01d000c0400078240310044000c10f5860402d080c0301c880c09a03000c07500300750104904c0000c601e000d0038196624000c0100420700341000620072120862880348550060088a05001e008021a207507010003061181c1944522441c0800c0f140f8500103840100341c1d0041c4820302580074090138003500b404402c0c0500c20002c2c1411500c1d01a10100c400b03820f9000c2d0098030020010038600041000040d45e07100e0500280f950b20041d515460100944250080d4180c1001150701404001e40c80e0385409008400d82c201c0c00d0440d440c2c0c0ca42d24924101500b0643d401200c950041c08090720f090440e00044490b0b03080a400482 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 740620125 1250 740618875 740618909
    0x80d020a23091e0a031505040b0709030507060c060605031014062d03010605100206010f060e030a0605101a03161e03020307200c03150907090f0b040204062115 70
    0x5030341c80d04d200080d600800442034654040b03031a01d00602c01103030102d808030032060100b4030f014411112402036a0b071010040040c1070402006a4480980c10310403910151100004141504c05009131380c00808100c1c070100f400e81c80d40584400c580d00040a480c041c0c810019203070030640020078a5840415001c0007c000d24045501281c054042a04010f820006224042c20001d50016459040303613000c80e1100d5084e600d91608892109150200b1645988800c00c1080465120780c0150781042d280c260700c10707005607140f80c2003c503261a9103c120b44041d011082001d49504036045041041c120f01e0b00003c0501160034065100320904100c00400d82d02100081c2e520340121180807200d00c404034410781d5030341105045a951000d1000e845e02a01440200310f0600400f41c600e01d0080d0f20b86001b80000b03070708025809000b030dc0c803504500a8513403580c20448190b110f070300c01000a4112a030b2440000e480303070101050415a07284091501c58a0400038034040314000030f10500340c804c0108842c00b652 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 740621375 1250 740620125 740620129
    0xd0203010905010603081b0105061e0d1205180d0c0b07060b0a0f181b18030b0f09061008060408071b08011d03070f020d080d020a23091e 60
    0x8180010300030070320b44c0b0308035010052003001005070601c40714008002410b100c031035582d03900f81c95040e0340b450741010544007500807a442d002c030400c01d100d4018022503552303c20742e01c4103114440045003c8021920000d0a004082804407000402081c103840d6031407442c1c5143d9030542d034154203201b413000341400420420100095508002e0070720000030407807034869440e480b50180d82c010500c140241e00003a404042054086401840d514880c01d28400b10a100040750568600500080083d401c13462058044001101c900f4002e02400340c82c1000d098600d40510200e02e4000050200d0303071030688032181001040400a04264002d51003640703d40c864002d0315041d04900204540091080d8800d00003040b075000c1548580c1d0741e810b80000c2c0700c0c0118aa001196240d10440724040c0400454521440260a00f9072152000501c03480030030780303010485403c0300c1c207d800864a40d40010159800d11030303400c501403852104140142e40191500340b40c000060001307000c101a1142465003405010166 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 740622625 1250 740621375 740621381
    0xc0411130b0903070509390307051b0c0904020f12031303120507080d181a0402040c0c020f041a130506010f140306150d0603030201140a050c040e15041a0916020c0d020301 75
    0x3000501c0c072482d459080124000d80650009500c02d6607000502f01c0e1005012400908a500320320007815030700b02c41e00c5035001d00030400d480304400d070342100d250130301e900c00280d04000a00340d0785034480c0011002820b520b0a610501581c1608004000080c0044d00c081810202141d03403843c5c00c20000500f01d1080e0b1005581503007040c0c0041e0050b6074041d9020000518105e02602c070341d20032903040000009100c400e941c00c0208480103034004e911a504102207003443e512404030320181c4032009440724034120000341c040d28103d00038401e8a44840600085580280400c2845041801d2150101c1007055581c011404010900307071141c0c82c000c06421a83c001c070300480307080040c2e0f0001808159240d041c041d0181500700d0880942c0c0c0c09440015100038824803c5600441075200800c6c50a460031401601c40d8402406da240301060001c030440103550390b4441c1d0003402c0315070269242c41d03000e044100100d2050050040c0302c52070101c021881890341c041480d40c40f03070204449400101c191800402c4c01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 740623875 1250 740622625 740622721
    0x120f0a0e09010602010c03050105090114010804080405090907090c03140f100306150602060a06080d18081c0305070e0108010b0a122d0e0c0411130b0903070509 70
    0x1d14080c001056860303064011090620300c60b181402181d03640c200b4840410000d1050751203603601c045001d50158442c01e2002e421a004810582c145500c035000140c03050410703900c185059010300000c00000c08075000b4090810311505041048024280400c025044000c12402802d4140f40014506092084003100070b560445010010851020f52800000140e0701944015205400018030204070501a07102910440009030218622105003a101d40d85004224041049030060200d013000c8200700d0181d401d440da16407010311480410015003100d10141c01803007003185d5203003c00c40a0760402e00c6141150300d804142ea90791180a40d040380c00d601040c01040d1524103002c00000b07030000000410801c0d504410b0000d2a108010006000f151402d002c01c120503045000f1018040c602030340000d1110315404000380c50b10520075901d104140c0c007a0000300e001c0d074002c50040100d080801000780038000c240c0701560787c0e0a0000580320905114603590450b404010810620310100101d1058 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 740625125 1250 740623875 740623879
    0x4060905010e03030a1107170a020a080f091003050f07110a140a05060f010812030c090607050105041509211e0206160806130c140706090212120f0a0e 66
    0x46010200c1c5002c5440740d0041e10048011030400c01c000044d00c502c0c42c125030085610000500c0004800710016210303800540e460b0056008140c1004041800309004103c50900c8005955035000107000b0131000501c0c1b8401c40c4200340c50501013164060035105080d40000031410b0044654000c17011951405001c0d0034001c003174211980503078110400014104c0c810314410001c0d2a00d0340d880300c00c11542c2d00000d1042043e168042d040d000030b0500b9400040d90444091f0028500e003044d20008281d05a00c0360750101d03000d130b54580800080c80b00c1403a20104100044105000411207074407855402d6820b03444207801050003950300c0011034002c1294a43c413003c10030b4011014010f00c28080d45400048500140d40000000600b1740140b0480009102e002c0090118410b528821920b030000e20903111172405025084841642200010025040c068420341010442d80814811712211104031181c0031001d52122039108a009514401d8509680c80041c1081c6c50319146a000c40300350320203c0003070b031b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 740626375 1250 740625125 740625131
    0x3090602130f0f050102031314180103051509070b2205041b08060103021e03072c040e0d080c030a06121208070e13020c030408060112150501060e090406090501 70
    0xa682c481000c403031030485030781d48100c0d0609540d510041e0780308c0c4540e401844881c240c0c8041800108030b06600007002c04405000c042562513405075000324090207820540e8168072011000d1007800d5000b41c02540400c03050013504042d854180c010786d00b8040d00c08010010454803c042c0d126104810034500100300c02407017072005800209114003d5074060000400040c00360000445550090084402132420b0031544802c0504880010a1039000900f0780301c1000104444481800700c40310b000710300100c075280281c038068001c0d000c001c100c1c0c0f001c14a009494001500417023081c6d07000031005500c41d426003400d655070350321b844804004204641003d900100910701a81c20b21850035416000c0119549030040d2a0b15401000c0ea001000d90400c41e07032251001400420710005c83d0041d02c0ca0144c0c100449080c43c1c0c9900d45181001003d0b003001c80661014a1104244598580010002d006402e030800c000e505009c0018810f280c1440594001c85080c4041801c024640d0311400c031498100c0020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 740627625 1250 740626375 740626379
    0x60d020f07020a1509290a1101330f0509040503040e0c0d0605060711120109050106031406180d03020f0c0a03030f0c030c050d05060f030601060309050105010b0c0d0309060213 77
    0x4040130060601c1c2c0714002401c5804041a1240d900344c040c840316042080410444510401d00034165000c81a002e080140360707940041c119009001d0f1080380580c05c0241140e10810b042184000000c07500e100c0d40c03c855501c0708200710401c1c1d0010405440c0305882801050307a4030b0030150300d1403189900c0002401c0791281045040e400301c01c040e100d1500e1300c03001030100a41d64400c2144900035510040c08000c1400c1d15100907203411181704049403960b0001043d1070a4980720340307003118155881a14440c00c1c25200380d6404070103100340c96001c0101e450b040404281d10f41d4065441c130012200b8410325500062070301910103040140c0b8a44101e0304121407180c0c4440c6401000b070401d62410501076401d0029581100c0d0003401a00c2503d075440c1c0ea59130601503a80b000c00041c000144c5003d0b0031165956030741e0142c8d102841400d004e42041d4a010a51600c949409801c480c0141c0c4184000d14050140007003200002c6558191681180b0f000320b0314058508140c4001c0c85851165401c4445034400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 740628875 1250 740627625 740627639
    0x190807060306060813051c11150f0a0612080903070b0309030a020d08070e061e0f070b0f0106050d020a0e06030a0f0f06030305030f0c070f0b010801051005060d020f07020a 75
    0x8a80300f40d6000c0d60700c0c011030342c840c0760301d0f04a0961502c40082264010700400e0704016000406038540c0040d40c07400c03c010b00c0b4a058440c2c1440ea910044241d00c00b010020459012860404603400407070b03084003000040e140901c50f010f03892032410010300c10400001d005000350303410012034001c3d18401325040d9690901904943d03607a4800080d4101601542641101c883d0240c44c04034131030300c032039290b00d00719103d80c2c02001115400b07211b84600d00d0390b2540b0600c0c42c80c040d90025005449015901555035001c0d404d002410601c01071400d013041e08103100500c0843c0d030000c2034a01b84094003c0168031184041c500703070340d0400c15071912030308030a022041080e402a0b40e0440c40030040400c0c4100503050443c100b00082d580e047c000030703000c10010800300308a81e0209800c0c550105c1c450603841d00388a01a541d0400c0c000704814250ba03441d55070740051010301d0b0288502504070a0642406445034075006c0410310a0044450302c404042c0d0110700d1b9480c0e40051402c6456483d0300502c0421965141e800c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 740630125 1250 740628875 740628881
    0x2402030f0108100603111003020c030304050a03090b09100e1807051b03030c031b0403051618090f020f0307030f080d0b010c1e060908161104110301051908070603 71
    0x4030302e00e810700c9900006102c0b154940b051105030383e00a503610741185110350500038140a2000a801016401c200341840c5c100b040c0040c50085104002810025001d805c004103901c0d030340c3d000311801900070081d40003590f403180386c0d8141c41c1e2418202070342c05403c2640058070503030032100c0d44100c0080c14001c100c0c80d6948a0010500922170310040c08002204150190382ca02080359024103418040001c203010500806120000c2e00000302c13850b00c0d06459658181c01e1040c2e003440da40c03084a0080c0c05016010030014000f4880d400041d0420002c00355071580d502c0d541c0c0342903010340128418a0304007021349082c40031201954001e584000e05c52001d00c0e09900c01c0d0301501440c1c109501e0f10720891142e6101c0e40c10043c0c40d42d000755469150070340750301c6110202c41400c00304460190b0340e401e071000002d02c403101515460081054041c044821801d080864660f152003c91040385404000040307000007a09403410364600b62100703003003249810110056214560081c4410307110f00c0d1000500300758950 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 740631375 1250 740630125 740630129
    0xc270a091e05011d06060609030f12070c0b030f150609060c031c0902102d1706221d12071b0f03110301060519050a0e0f042402030f01 59
    0x40000c0003004e2880008030300c402c4a02e1183c0f4040d800c14000f10708a850310318082c118206004095a55565101e08031503c0c2c2080026180103416000caa21010f00982e50000b03001000d4034400d0f0340ca5403074403c020340c1c8189401801c541c0c1070501103140d40f0031601d1764003d603400764001511184da01c3c001400e50036540e80201404400f11401500c0c1c041e080070040c080e0000385503000e40341d40d80420700c940041e20b41c071403c2d040c2d2024903441000c0a0000c405401c08481c022025070726941001c030440b58006084440051586000701c48130315000040180c0000008032862100b0000a00c10b03910003150503c0e55224a0040c856226440c100c1c03071001007510041c45c015200d140a098100700030051a0030304e1025118590003003d2060080022928408411116180040c0001100340d1190300094204010042d803101d824801c5605000d00c0c1449588007001d008595038021452902c0b0340d000442601c000d00060104040c0003140000a5662550301e030701e4940510700790340b40d15007a01c80c0801d40d50700b4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 740632625 1250 740631375 740631383
    0x2100504170a05030316030213030f0302061b1602030f070b0c06071103191e2a080a0f0c140109060b100c020f0f0d11030c270a091e 58
    0x22070060841c0c8000050440b8045520401860035507956801000c0b0b6007442042c50414942c0802c403c04124282000c0b85000e1881401c02100c4104141030003407414100410484440c2c0c200c1401e4044088510165248210145204410142c0b1480408c0c02c041506000103424031481001207441c4072507a01801e103500c01c2c40121070f26941c0d8000d04468040e4003503c00f080c150420040c10007108a2803840410602c1f19003000c02007414032a0030840302110012182d80000c43c82188650040200c1c0500301802054448015030311441303899003a0343d4070454900c0f50501080c01005c2c90740a009002100c40d95820000c201a028440c0580502030400c18004482035843c0090150306441c0103002044816442d07500d401840750541d003801001c51411907800e030b200c18031004201d02a500c003d0743c80c80d05442410b100da600c081c00c0702418680509468460b104040040c1e110503419120342e40c503104030001541c5203a4a441e07036401c400082403801000b8000d079400c182150ba801e070024074070b000c0c036601c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 740633875 1250 740632625 740632649
    0x718020c06153303061210050601020d020d0923030d0504031106070b13140d02030c0705060a050d0f0f09120806090933070c05240703150302100504 65
    0x10081d0303c40c02d4511401094a50209010115800400344801841d84001c000d042040c0e18402401128600b240612031401c0c03864540040103400c0d64148000207250015000038403120055000180500525004910740319191a01c140410107884094110350400681916000714269500400c10340c043c1c00300b541c500554130000c030504c0c18084110746006030405102c0d0216100d0300c40401ca01444c0003410380d1203540e05814140c1d544400d01400a22250036001147c0d42d54414844608200496100d644151001e000803448107401004960340d090541d50002000e0b0351382c44417003000b40101480840c0007840c00c0050310030000340441c1015a281c1ea038480b01c1c926070b901002c00a1b058002c58811055030070803049040110300d0050000c0e10ba0b2009001a5100d404101250a0341d0100b100d4600000301e01c0410002800f805200581c804119903041542c103041c03090001c1840f460140c02c0104260b80d034407407000c00c1c0d2001240b000144d1b900908513031880203030540040041d0042e01854141c050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 740635125 1250 740633875 740633899
    0x14030c0f12040b0a0903060221090601031a070201090b0a020714071a0c030f030f0103031209120f0e12010f0b01020f07060e010c050f1c020606030718020c0615 70
    0x40060120040700039191a9807030726090407000a469048490318405101c40c0080c04000980140003900030345500800c40340c0181e89034491400c9a40c00503240082d981c008500600104134a04060f02d45a0504040c0081c2521021000c81c0103245001c0050b25500303082c0d05000c0201d5054005001c1c0034015100d1020500402c00400c0e100e41c410b104628050f0034034004100c6008101020300107007410001528100951051000050b40c001c443d40e00c80c494419005008141d004604821803120b80c080c10001c0c1f142c241d032090b400c801c80311f0014041c41030324204142c9191184000b410403460143c4080b242003800c41c2541e019180d845a00a040d6041039103c403c107500c0020b001a0000c0d02100919280c0c3c03405c0350955114514100044c10003484406500c0402ca040013000c00340c80400009204101900c0013100444040400410464101c442888050b6a0014410041d20038030725586000c640c1c080a814002d12a81c0c02c83c4826004000030007112200b007182c0a90600d1027911850040c0d2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 740636375 1250 740635125 740635153
    0x50c070906080d5705010b0301110f040b09040204090228020a0b0c0a0306030c0f03050d0c08030a0507110d0e0307170715020a06020c030702040f1811060714030c 71
    0x9070881043d0604100058507110704100e01310300711010007070580000c507213507030103451800c446016218281c030780d130f911800350080d00d00b424411202080b07c20340c149401c04154480091441c4210300c94040c0d400000b1a00422039510b0b41d048600a2101c00c00c11517940703403040c1070103244414413608a0820245c140756954a2400801c40394034031a440300d419401d40e600c4407100e28154000710300c0141010b035038a07804400a20b941c1d0381e00000c0d0051302d0000080d50703e1840c005241c42d48402c10201084080c103603550020310b01d001605d07084411428040f400e40d42d4821700700c421003510903010b030443c8500050800519000407401800e000f0a405403061140c0300c00046941500a2054241941c0010b5040200c03001502c440c1441d6903d900c140c036607000c044c0c2c0b01c100a9822145000380a6007000078140110318183c85510301354000c0310301c14860541c08034401b4128640000d005031200500703940200c0c00360703150305c1180e207110341c0403800e0030105c9119071a2541d40c0d04141b14812441c804d00d50058410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 740637625 1250 740636375 740636417
    0x705060a0f030207050109080304051b03190303020702180c04081b06092205040309090b0d0c230a26011a0d060e0f011a0d080a050c070906080d 63
    0x91030158466501d4a100220300b24001d600c03140303082d0303401c0d540c2e0b1911800082d4550000c5001c2c90080c4010f00b407410190b140c10240040968441e40b10b5400081508c00b18403070f00b00e00440041e018140146c94070400c0c0085039410011101c1c0410214100d010804071400c1c10015000f900c0c040021510712103407512500c866880200081e590001040c80f59145600e07000000004400c25810301c0c0d203440d04240c100354281e032070035102103010400b16082800804901d201d003c080040450b0a5480341d50703c0d4403090400c002030300030342101401d4138400960f50460b00d51003003513001780600b48622035692185100c002815404403c0500340880114040007401400381043c208444a001056503017030004000c00b00d6000c0c40c00301c4550b52582c8500300045028800e0440c840d5201002190700c208410005410103c07080815104a810111445c0450320b003a0a56554041344d040150b541d940c00c0003010320f08402030307003c0c0c0320040c00c115000c00c4940c00480d07080d010342c05649501c441544214600845 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 740638875 1250 740637625 740637637
    0x919060b0c0c09190c09031b03021008040b1602030c1504110d35070f1e0506010b09010509060a05041806060804030e0a170a0507080c090a090c0e1305070506 69
    0x80150913a05000380e078422035022811a24190400c40d0466075603545002400760508480741e403940d41258100254100036100d2100c170909480c103030520745050341d9064251a03000d810580709a915181c00703e03aa900810031544030b40b10342c104643c160803610715200403081c07080300e0480b5142c448160446140c10004a12944e056010009920800f0300c0381d1080f100d0142a10500d0542440c0c6d1110f801c0e4000e0b1400405000b03004070344008018905041404850720b98103000081079042c40183c8002c0381c0b010a099066540c0d481280e56200002801205d040c007540209982c040300018030301d01d0403600f02c4020400c03152821604a90040301042d6041111140c1c420030020801000000c2c000178410604400051001030a00381c80c2600c481c184010012001e2000c43e0030b0744910380708030a1000c10015000103207030103070040c03528040d004085400300b10302400100b126519160003400b00603c808420026080e034035a00d0400313292101c202888868220003d84840c001c07044c003c80d0a0500e40d0403512 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 740640125 1250 740638875 740638891
    0x8121902160b09190306050403110c0f0103051302041103010e070507080307030c21091a0105031e070e070806040c090e1306021201030503220f050919060b0c0c09 71
    0xd0a5103481110b1002d64042580750354000002012601381c20700c1071600300701860254100195034901850040c0ca03010b040b001c80c00b1590301181008060360764800c1c0681001c00d007171074081a9078480e6144402030b030030f040e80020b5000b07040c06112034443c4d40041c0a14100c4a16860b01240e9841c1c03850281c0e201c3c851600c0c003406105c07040000529080c001c1d0041c0798200358518010608880c4107121080d044000e001c03156100341c031240e1101c02d000d4040850700c0c0310a0b000101950551500c40000c0d034502600c5a007680030142070320342d000940001e00202c8018906594141410700e803103500107010710821074055115a15148040c60f100d48100c2c03035803094402c102501c040e0754035078044080d03503a020201c003200c040d5000c00c8210342400040704220700031441200110b4407600105c600800034240d201d000c0b0207041188104001c1c03100e4000c0e08100b140d10584603c1e207c1d444030000d5185484ca0f808600b5403103410500000b5407412224000c00300f216005091b503903480d01c08410400300402c2910900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 740641375 1250 740640125 740640163
    0x303220503120c09040c230f120c0c06010e060907050a12020f07050a1a061f051c1409010c0207050f280b0705010b0414040f03020708121902 62
    0x742c00c81d08a82c2c4050f084a00104550300300701e10100060b0a68401206000004000701c80031004941e00341d41501d4035140c1010400d050442c00c0c40078034100c0c050981c01d6802124003101003041d4540e00000ca45034614400b0a4030b04c59a11140c1c1d5844503034040e61400d0007950884001045544150251052050595103c500c02583c10100381c002c0d4102540451304403004000e50f40015408004071407030148540c01c415000c600c0440010a18403000780181e02826020000c0b200320461500072440d0a8201e0038078035120621944540300101d1a01400e0030380c185000c401549404105600620840040d4001d0050070300f0544100c0e142d00c450f12595030030110b02064000c90345001f10340d0010b21a038803090040d00c00c3d00f149003001030440b03543c0800c0c000140000c05100740b060a0060300c21107d402c0d5418824503c1c4000c44002c02d2100401c0940110f200e0000642058428840d04000380981c1d004c40d551800000e200403219484400f00e0b60014840b50741c00d024944c00840c10701001d0141081d66 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 740642625 1250 740641375 740641387
    0x9180204410f070518031905010b030c0312070611040b16060b061312150212011802070f0f050a0b15010e030109170a1e0c030e0306040228030b090303220503 69
    0x101700a880c5102c0c0380c503498040c0c124072544846981e404280810301580010032443e104501385400c02200c0703d0300a0198000c901e01d8004001e80d882190f91441d0301a400150300e0315640b01c54201c0d40515000341514072000030345101302800e201d0140f0b0405000d49020003000a00c842001414894903004504071100280b041051700c459a11840c507440c00707146100d003205909404401281c0c8022007610160107442c0c01403000000500601303a108201441c214580203140d140e164009851f144003d06103e5444604020488103200e0030440c4c0344c1c0162003030414103106134111088903041203454001444503605074007902d4140103c1c080710307410040c01c421045280341100c01035409021b52200380251010319010300c400c10381d502c041e1041e4595484203c0c40ea203150051034444410b1a05110b0790002c01804056940e00c2000800b01d550282c90001070340c0020002c07a01000319030320107065010240c0410015031804401144160445100d9000b01ca040350481d1811910505000e40142d10510403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 740643875 1250 740642625 740642647
    0x30c05030c1912050f01020c060106081303020c060a02030c0a030201020912060c1204210c06060b130605160804030809030610080a0206032203090e0109180204410f0705 74
    0xf920f030094050010740b51007400a1090310b017664030078500804640d001000400846900144a0340c000c1a2442d0f00c0d440c1800944000759100d2400315003c0c0325880008000000314000c1080395110406403055030418070850a0180c001c0d040310171200d011b02da90f000d03542640e020110f84140f240c180300b8001420705d0843c3c0d13405290f0040040045601e85200300c1508a104180e0080c1c5010f458035540300c4440100a04d05901551000e500030b218450043c0080700704101ca00015406640b21840c1c40340c1c45517484e5981403010200d42e000038104090008001c024000c100b0000d103070701441602111a41d403140c214410b10449203106403025a000b14030138400500d0224011038002c0102300d4444051082402c24a4070b100c1cbd2010110082002c6540c10007199041e104040e0042c6000001040075040180f8070100c440500075000384a5a40e0301032600c1415507010300300c041920314072510080c010b4503060007a281c440c90104d40000450000000b802a003441108030710807612640e90030705000c5c0d506c031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 740645125 1250 740643875 740643899
    0x4270e160807050a150e090a06140409021008090726012003070e030705120604020a08120f0c011104031b15090b0a090e100e06060301050d1e0c030c05030c19 69
    0x251482007046e0002c1c0501301d0b40d1880f9803140201741a01002074514a0542d604000306c54013991140a90b083c0f0100074090380e1844401c0517203106900780004259514140d880c01c100b4a41c20030445071007203016000a1a0029085110400044008005104101414042d5103812884d0460044010000100c0f440d2041180700648171014080742e02260302c850000303111580680e03a04c200796000d94100000d61411308d200100400d41c640c00340c6282d040345605010b01d1310a0010b504001070002406a0081000754040b480742d003158008030391519220f1074220000c4510f410210340610b400c040102c0c443d10801140350108405484094500b407030b0106411554011030803902c1484041c0c0703800501d0400c0704814600c21445003030b00400311030508c43d00c56440540a0f1030315020f85000c0c4018401c03900d54041420b150364000c010743c00614620718901c484800c2d40302c4010401400340c1000010041c2c058444010354100b24103581ca264804000d0001c04c543e02d804460007490086820000450162 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 740646375 1250 740645125 740645159
    0x51f0c06020c030a05030604050f060603071803020d03021c03020906180409061d071d180a0c08030d06060201050714030a06230f0d03020304270e160807050a 69
    0x11000740c10181c15541e2107003183c100361080d40109800104101c13413480c1c80e1080651021009034541da1500b07000011801c00c0c000240788000380840500b060010182d03e0015400441d03005200468503e014134000b52202c4105084030915211109075081d118024029034102c0040031b4082c41c28025940d40b5810000a070800f00d0750010341d50811000884c069000b24109200f106101d400c0881c40c0002c0c99240501c50362001c0400c88880c2c1040c1c0c111032595001c5034000083d0072150340c02008403104a418414500340040405500200003e82c804000c00600f220052010080000c95a01c40c416420390f2401c4641100142003401c010070422010009190041c415800000f0542d484440b20810481d62400c40307020000c452200466a290030760641084040544208540d00039617500a50380740503170300803401c00c543d4100314902003407070070b10000190304900310050050481d83c1000d1a00c484844540303020b00841c41e20081890380c0000f83c1b4400f10340700038110301407541c544294000c1c0403c2c16 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 740647482 1107 740646375 740646383
    0x3180f040b0f09090c031b030610080a12020313230d030801090203040f061b0305060a1a0c0106260c012d020a0b071107051f0c 56
    0xb0ba404540c0350070015100d200054442410aa003440c40c03000d140e6400d8071a264442108408050354049150002c1d020740350140c844549186000d00710380102c00c140e901c00d43c403000c002062a400c1801d42083c0388152824686020412540040c0c0d03580302da14075003060054010840440349010b1240c480448100311241c6450b80c000e000c1c030b4014490b48850301c0d400300004050184a001c4462090340c40b640c10400d4004221070204013202c00b5080c800044d05d00030000f035040c2400c0304908191218003100030324141110607000300ca030703200d518030001a54880400061078012241c001c1c1c403d4421401110807254a07401852a03c1c13082d5908034108200070700200c0c0142000c0140b08104450a00a1030034150f5080e801d83c41c154000000412000020040042031640406007800c0402940700307440d401690341003000f4182011949101c1d107400344400146003280105c080700000c0d0301c9 = true := by decide +kernel

theorem cover : BRFrame.Cov 740467625 740647482 := by
  have h0 := BRFrame.cov_init 740467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 740467625 ≤ n) (h2 : n < 740647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
