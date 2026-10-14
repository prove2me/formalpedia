-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2206
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:59:34.362357+00:00
-- url     : https://prove2.me/submissions/8296b291-8f45-4862-98d3-bbc28af2e998

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 396582733 ≤ n < 396762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 396583983 1250 396582733 396582737
    0x91208070f1a011514090406030804030b071206034407050f030c0c091504090c151d01030f2003060915091303030e010626060906040303050c0415 64
    0x248a400c084148055600e024101c05181c50955213030303034580500b0412102d80340708203905011940d0a01591241c06c91005036602411481c2c85660368544403150500c1a1902000f00b910807106141c00c0c0420b110344811650020070003c490011409980062a441c8000c0c024902a10840540c160312044941c100c1884000603190385000500b40f2071300f02000c3c11a01d0000340c204201a801d80320001072612090402101c401c1d03900e0702c84041c07881c0c87d1455840030316081070601070804284607c29001a04403003002110649540c1082d00c100d4000050038140440c0c01c95504c100c1c050b65220fa8092011680180000564100101c0030030100b40b54071880d18015040c0003040141904000421035000307180024407118050b00d520005201c04002070a48800c06441d10100c000d040c403c0d0803c1301034090b40c070000c000350354039010000c1051203420301840102d102d07100312100315000020024460990748000d0601e90310785982c220040c00c006803000107140000c2c030020600c1c6c18900e061400e10b00c1a5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 396585233 1250 396583983 396584003
    0x4060b04050f030118110607060c0e0103180b04030e030309030114090c150a0e0f04020d09050f0f03030c0307180816090b011d030f011103060301050115091208070f 72
    0x110040002202e0800300d00390007a410004010700d0b1811902041040130b6108810011001640300030508500405101500c0181010442c484058100004000100c42a601840491514100f40350480d003400c0c401001c00510500081c04284200c0d100a140729004003a02d252800d4100000d0a503070304004a4801c80d10300da424007424a504000f2240942c0055441d0000c1420451800d007160085041580c20700000510b1200d4503a6046594410030200502c110345501c05804560000e0429071000c50b40303440351011040c05560005016680031704c40c075006500d90340d101000f9000580015000f07130305200d01d41e12790800c90545103001d03d02604401c00242050040d0306841804a220707544424805032400342e452000d640d201600301c00405501202042203542032011915003110910000310035440d0010300c05a84401c0f400443c0a001c040b0b000340b10903622241d20301c000f041c80c0608000881c01042003000b556100025102c0c00d01d0142915a00b04180c1c2c2e2600d0518003052031046a08110f0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 396586483 1250 396585233 396585239
    0x1002061816170606030d090e0a020d0e010902010f0503060310180203030403080a02060601051e031e240f03060105090702012405040c0903020a06050706060f03030c02101805061804060b04 82
    0x2040000e01c4c0e010708218010440300c84030700d4014000e810a0b001d04510780102c14000740911000c7e80403503203540b00c0804100158003c0740302c814020f1650030005ca00046000c044010194490b0b42601e0050b9001400381c4110a00ea14010740206100780403a01c0006600c20190b015039000d00c00b500046024641281c0c0e26921000b0090400000400040c11b202c020700c5024a01d201c00d800000f44000d04621155a80c2c0720844142d085610a10030780c0003a880c1c500421058500185003ca80c0503121810301d40c0603441c2c2410040c0c81c609070140640c042c1e106100400c428545403020580100040c0000900c200d21410040741c00d6450300b960050390560b04008115600380317413040400c5e101c1c6515025450074110781c006050f201042c03007640100600800c0b10410300016a010b00c1c024030f00d1740e6003100320319560715001e404280504416489600144102e0341841d0017500d84c02c1c0e00c824046055442c2e90b0805041200a030001040311041440061740851a030311641b04000c0030b003011002058490345 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 396587733 1250 396586483 396586529
    0x4030203031b070512030a020c0703050106060314040b1519061707080910020a1b0b01090b060301030b0109052d061318020d020301180f0606051002061816 68
    0x2030009242e003041c11007044001e0201d840880c824040e00600001640d03a500e440303c03482c01030702400d0708103411401a82000010854158030150895910351410f00c03c8280d08184810040c000b20b4000d800e075400c42d0006440c280c0806050302c1609001800c200d049004e50a0329201c1520541010010541d5413498900490304d0610b46d0307500c5162803410300303071710314203038007950344405a00500155254001c640306a4180c0592141030304842e020080204070481400d000120030750038403559401510300394036440c0d2400d01004480c143c9420420fe01d00030307481c0658403002044000d20b40b420040214000e141100001840482207001401342c50030281070603003c000c51000304084403000f15280c04005159a80c4155610260030b40441f421100f4a02c18008a4050704c182c803050303050740402d4500d500400c1150020781c01c03c9070007404100300c015141c8050207424400c41c4011001f503400380000910504905483c80414890841961181000182c425600c00140e070080d0150f0b40000c8510040741c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 396588983 1250 396587733 396587761
    0x20102031e120112150c1e03020306090c0702060406050f1318050f090705010e130507020609120708040506030402040902090a020a0305060406032102010e06010b2d09060d0e060403020303 82
    0xc55840d20b504601e8135265940c01d1040402c1207082c50b801d48481c90040c032180107800c0c0708650712441007000130007440a10f00a00035070080710400d01c220148404030358606854070503103071050342c060445450241480030544040c0c0005032001d085caa0104217442d1091001307900c4000a01c0d8032000d419420810031348100c26207100034200c1c16240705010801c000104002400003c980f02820140c00380b851a00104a8200d6018012140b080c203040034070034555800600d0510585183c2e003503c0c10341c59600010b80350b80c804c4600103000108284414081460304400031a04a0710043c0001150300256021130310003d82140d54250a543c00300c2c0c010000b540600619900c0b0f001110100804be040d950351068990740c2d204401c02c1348000640020040e8001d42c4603060035180d04044501070b41c3c3d120323460034180d4400e014220b404903c0c001003410803071111200407280000700007290b007010516000c0c88890f8101c08903440d901a02c50341004202002400400e000380d0180d806180d6a10301000045154 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 396590233 1250 396588983 396588989
    0x13122a0c050103050a1a0111030708030906160203030f19020909101811030a02090319050d120b030604080d090c0e010e0601020a1a040201210e0105090307021804020102031e1201 78
    0x4a083c000202e442040300e2800e05000102400c2003808c04200301c488a2441c01000f500400040000003407040e13241e800994941703c0c5051162030b140d200d440006c12a1203002c25603950151107a10000f14040c03200409856021000000006080ca40f181c000036a102006139104105014034504c140122585424810304a208aa20500414901ea201c0b1207162000400c0382e80000d1780810360030782c540e0b024480101011100680c40d542107000303080075a00d50900402500c0840c0010a0405014181d40106c441500c80203016040d41c1d511070b03d8010880e4401003680040541d0b0701191800500b81c08241e001074401c45a1102640d8101454100b20440c05054541035500c0b5014040000d1548034460000b020a21034200c013a444038401170f9544802e004d060019540780c0e096001c44000700b580044003240040000340429107074421030a44132703c21100e0107500101071071003d0003003521694100d40c10503c10310487c2d103440c0500800b2040b080001c085016610400280c00902e90020400c0f1409 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 396591483 1250 396590233 396590251
    0x190905090a061809170301030803010e0a0b01020a02011815020303011a041505071b060507030905010e030c2e02490309140f0613122a0c05010305 64
    0x2109050a0038a41003100036100040303c44d844040310070130011280c4040c500480c903001401c0d125616031400303141c145c2013401040c41c2d003045400040e110141074020110b1070001a0003800c031300030240d00119054862105190f810540881c0d000800f0f0220502450101d655680a180c5950600384110509e4480e090a030040000601c010f000c403043e03050780318000c43c0c59410300c06c1d0b03507806e1b030304c0c0c03544207400854242c0c0d41240d484c1e000001c4240c2c001c4000c211641c8255996a00310781c9034001034503140540c48016416500118074041581000c844180380c400179204207100740003030410882d400d4000448084010380011107140c4000305800340f561402c070f60a000e04140d0b103000014200c1e049000b5601c0c040c014070980a542500c50099219060164100c801c040b111010040d8040c1d903005171603010002e0b48a45000141d0800303402001c0000c50b80d018400ba1095250000121200580d803009207c1c0050b8031010101c601190302500c403650f07031064911442291402001504940c00240b0740780c5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 396592733 1250 396591483 396591491
    0x1c110303040f0b0a02190f0614040c0506070305070605010b120f0f060607060902030a140c0a031a06011826010507090611010908040902040e071404030b0c190905090a 73
    0x6282c044510007003612100c0e070095880c1c8a042c0701c2249004c0c40c0c003850b14101741414503032105003c071a80b041c144403402004140007050b0307180641003640104807400780c0104050a024001490204020701c80e003402460154240125030b15a10101c034403c1e88209850917000a805070200303036141c1900d0740300c4100c4d02c80328820b1500d02042c0300290340041c011403051100081c910300300901036000382443c036006022241808118a0310703201c4a0803940d4010340900c03904492601a00d06043c0d81010b4903403000301c039480441c882c443d1003400c01010f0001030610148619031005a40304060131801840c80d0705c4043c81c0d00c502c042003592040120300e2a10a41c0c2d05020801641a4004c0d80c000100c0344c051900c2140441000c4800780140310101005040140000e00010005820f4010307000f551806800d60003d501d54101c181c52001c86d0804080219200740820800700f4100701c081c5500001f98100346d4a44400c0005d001001440d040350074020a00342c404c240241d041402040382d1046503000204 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 396593983 1250 396592733 396592739
    0x2303090615270403030e010e06060415063c03050717130201111009050c030607020309090a02160f0302031801081b0c0c100f030506040212070507050c1c11030304 71
    0x102d6881105400004a266640c08a02010310950101c055055200001c000e0747d901c5490039501d440003590a10701ca035003803024140858507064100f80485030750341c0321aa191761450340708011410000d8180c2c081c0507554543c1a99003001d400c100320302c1c0c0119640005151070460405010441d03003210640c4001814000c0000c00d00e103500340c0707001035502402d0084000c0305060560345402e1050030201c0365541010418000c00600007408880f1031001c8045c1c60301c556404200700e80c1c0b0300560681c41e6001c01810081102c3c0c4071a940101783c4080a9840340c2031303540203500c6440f00c1070100e00d402c4005900c0002c0702108110402c0700300c4000340d000d01e0031040c242084000700a8030300d011070001e14a280c00007140705140c0e801304402a24240041e0025181110018028000e0b007944007100010904000015042d450284200e82c8044450141d807206512503101c00c0740c4079009090100d88034800d040c1c0212150351401c0e100c803600076200c4240303c0440031034a0041401540d070151103010742d10501c024 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 396595233 1250 396593983 396594019
    0x15090c0901030b0a0912020f07211b0306021804050610050a050d0b130c18060c15090204050903031603110d050709090516032a2303090615 61
    0x8107045940128203007030f1944940900300001c010030800140300240d840b0410b0603058020884101d221210015a41d050b644d0710741c1914514569010301900d0764429a0301c0d00090004100703050301c1d88a641050021079100e50b00c10b07040780c0c01000494036031801300c48480018039150080592040064640d00c00d03030b00050b60090828019800c43c8810b002020a62684000c2ca5510181803180020250342403000d81600b664001c00b40b07240720600050148065001c55104082040c0465003241e640140300c1d0481d0b11003a002030782142240349030b581c440c07014102582d624007400b806184144050340e5130741010f50500f0741215110f44002c00380b41c1882c00e054180b080b050140c420140c0c480e1404509903275902001c03509185181c1000007078600d000148006041e181010400034925070b03d0422400311002141ca2001c2d030542c500e510001a0103851800f002c1c411101400701220000080c100c0103c00c001c11045074004440d403050301e600940030060340b103007500d0306034402c10303c15203858190051100d10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 396596483 1250 396595233 396595249
    0xb0102030712030b0f0307033e0409080c0109120912021c05010209120105040204060b040b0d150b042702130902030402131803021203011401080415020c15090c 70
    0x2203090503507030001c215003030f10717094400034400308000c09680e0556241d00d80502c0003180c42e61510a41d82190b001500030545800b9680e040400d002c2d2000c60003c02041040040e0150400c1101e06c1c400501402c0c1c1d0048007401180d0080388282c9141021a42c0480300505500446c0c1c01040500c000380c0443c0056140c04801c403482d6501244c60807940728050404a019100f502011030304005075040c902c00f40101076014a0249108503428800c480e903800d5001150301603800b610088900c204041140300c00680e01809207621244814054641d842d0010802a08554086050004619502e2100340c65480d00030901d0f1180340c004501f40b0565424016001d2864020807610940c008003040541d40d9000c00114001c0648400b88442c414007503d50801c0620320200300d002d44a80140143c0f8114180141d0b416140340020544400c20b02c1c40046440c0000903000341e400ca00030440c0c04043c40110300060012201d10002000c103100540301100400d40010842241a002264030701c59903614081 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 396597733 1250 396596483 396596513
    0x9010e04150b010f030f0b031501030510110a0804030201060b032701020a051603030b0a09020c0c041b140f030403050426070b0714011508010b04020c060403140c15010302040b01020307 81
    0x85d0000c0c001e1204016a00103100322410198144101c00380703440000300410845059078429825549805080c4019106450101100030000d00b001e001f8084800c0c45030080b294841d000703100204030659540700c03020a9070300a88074481464048414003604041801c442103004c0e00000085251030701c100b03802002400f841402406030042ca0b4040020b051294018140c5030000400002003690b840c1319510080d8041c1d808400346000c1e80040700007600c1d05100781022002c1002e03040c0009000010201e4095182c05614681548240507501c4503c0261024520407842600d650740e442c0e05180c020344e202c10301501801008803401d8420700d20340b0b40220f1040d007145c0c2211030842d2100c1e400d261410403e800501d000803503610b011890b6148040d8500180101c41826008000e06580300b4140002d92003910130071b010a0740440c02080000e0f1051a880c0301c8504601c041c0380c2494900e241703640c02c1035540c0c0100055180074600510561800784180c01d8421401d000862034004c80c2e270380307030000040c802c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 396598983 1250 396597733 396597737
    0x3050a260c070804090203070c0309080a170a020a15050103030e09070c17041203030f050709050a14060c0303072105071b170a0203032a040b07080909010e04150b010f 73
    0x4039040b02040b46043c02d94002e01081e0360207648900d880c0c9402803128205100660008100c2500043d45400118482c40c02c0c0e601f20002d150510070700c4140704026803040b10404214032900c202c0744007003504036503406100091030170081a15455410b004211401c004022886047c6032802d100300560401065203038541e00994980404400e000b80b041640110b40c042e001c00000e45400c0302c101a07160340039034210304052000300140d403240c01c0200ca01242c94003032190020380c07103407003880750070800c0d03401d00d0f03014500402c40c2c0d00d4105075004490640e00103441c0b03600482c1090b21510409000e40e03003002e41d00d0201c030760108000e1030000d0000701000d00700c51041e1004100e8883c1181400b000781c615101e2022234440569840f004044001e40d240d20444d111440e03a0601500483c028081c42c80c840c40c219030b4014024145810104d000710158000141210400000c02180c0c1c1141c44403404036000b0208074900000302d2610b4100b68000d201c9041200b8070151509124920301d83e00300c0d540b114040564 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 396600233 1250 396598983 396598987
    0x40c0905031b09040f1109090f010501141005070c0504140a060504180b100b0c0d021603030206190209040501090b03010e1501270e010203010f0e0708060409050a0c0303050a260c 78
    0x9801d06c40b1124407001d2001e0b40001400003089200da50020f440034549080e4002006543e2340c0e001101014003101000b0340c1c1c8240c403240a010703854482c0d405810250b004110044680341d940300020101d609010b003d2500014520820107600003038898103008040540e0305020300d46c0c10b0005c2000802c20031900070320115002001c610840c2c40001a03101900c680844580d440e01440c0302d152340d9881490400005104440c00314640c82910440c1d4000c4942c1038004380034607126082c0c0e4449400c000303c5450743c07143e420312900340141d446005035402032151940001d4010790301d105241c203448a0b091020300390f62284034000d4842003844002411146003000402c1c0c82c1010300c00c80e080301c9400700d600b03282150801c0c1280c548150190b00541c101c40000f21f40e8221140d86130010300c802318044070100c0c0031410741000641c041c1026000000d410303109400741c4030201e21594500c0a50701c1940c00c15000201d01150000c00f80d90820000f50607400b05100c034140c80c04a01c5c07244000108001c2480c5880140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 396601483 1250 396600233 396600263
    0x603060409150e0f1b0a150c08070b1b07050c04110c07090c0f080106050d0903172802040806011406210708010b0c0c0f0609040c0905031b0904 63
    0x4007407038050004249000f0b0104034040d10740260344480102600400d03008442c40b42454520310b500d400c0510303401078200403c1307604d0108008001d81c0e41840b41303014400d059504078006443d580041101c00c0c403440003030600e41080c0c440d61004850728a0300400f450700421000f0301090001407100c1c1c81510403500841d604001400f00e2801e40918840058207206040c0c0210742078050b0f40040300e6a080507914200711401d214000c541c074000c20712800c1c0200386e0810841c3c1d405c7c0345035081440b44500904000013081d049108e08450180100c6140200c10048825110100aa00480343c0c0c0d03500000015400c00d824480403a88940045c172406074803407600a503010541d1504015540001e460041c01c414440c03050f4510700e0014400c0360302c84005121034001148c10103028054035820a800001000244002018001c00841c601d49070395000c40b00344240340480d0703640c0c007034102e45a0700c0c1d42c0c40041c8149028185840e101070307554500407510210548020a480341c4060581c083c0d00400c820102d040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 396602733 1250 396601483 396601493
    0x8071a12091603080d14071d06160503030906070504060203090405180a051b090f070e0111010f2a02030a0804060e010203010e1801060b0405010f09080109121205060603060409 77
    0x1600b0020000078208035100109100e101030103001440700180043c8144244001c4180c107614044034124003007522180c02285111b41e1146100450038094015881c02c5070305480c144007500b510310101c416601c000100000c40d0400e00c0740d15040b03071150030300b14206420440c002e0b440340035401d000790007117654100044451405615460b91164004181c8541418904003980c031101d480400d400780380c5c0c840541321107504100c2d4400f40718030a4001404c0c1a030b20307003c00881e844d131590b51406040051030030031500b14010038840d40300c400d1120480058101d40d105540c0c42201c416401c8604c0140445003a054080c0d008401c40c1c0c0d00c41c10718944155103981e203107021b10080c40f140200140541c4084004110030684541c0180903450030314000212280b040501030a944050254603501c2c4000d0004014030350003080a000d410b80c2d142005003481d600c900c545c0f82100d09441050725004e02c1002e0204d290b54100115405400c8280e80600840c80c041c00410034520000d08a203004903925211b48003401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 396603983 1250 396602733 396602743
    0x61401090825032001080c090a0306180b0f060109080a05030f0903070f060e0a0509040203101a04090803100e15010c0317070809010b04200c010e0709020408071a1209 73
    0x550040d0f030300f0981d001400740c024030384d44080c500c41d0116030b44c0400b20310400742c40810ba9218480081402c0324090540c2d5401e0042c040c003410140007008905c0040c0c0020f074501c00390300d128150614282c25286040c2000403c03100550348201e880790003000b403070000706030044200c4651801803001c50340c2d9134402d0b401003071400c200c44e032001c56107015425010458503400f000c292142802180c0b1446103c1d101d030100112004140c8000703505070700c060401209050507410811030400380491205421501070081820341e2102281102c09180000c02c100a05030000d0070540030300030419034a185403801038449600403074030301c50f41414002600807140c2003511030854410f84000801461a140c00c003040060181c54081da516405075007000c02c60380301c03420603100c1c40340c800c0505100e000c41002c0134480708441d41d000d070262407059500d0320024049610f0070400c140042441d800c0050351280343c0007890781040016000800080c0b145450103940d0311403041504c09118001c5055445034450880251500c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 396605233 1250 396603983 396603989
    0xa020f01110a0b06030c0117060409021f03020c0f07030c06140708190e04020307050d020706060b070f11240a09050a150314060105040e0414010f061401090825 70
    0x25100e03102c80001001101035a160113444d00380c00f01e481d030241001c019036070745140c3e0800780c1d00042e180700010554035054104640d9140007a02160403d10310352211403802154140140100b07030000740a8411100c1040000e00340300106010341461425582c1d01940c8204521603c41008000010760b4140102c0c2012598200d600001166550601007d108042204101d00c500427560440341004a42410300031244505c2d8541c3d10207140056455900e0029000000182c0c3e8080e0b50302c2c00401c1444101e0006d01d03805025405800301c0c041685000e0980c0d00000c0099800348030351481e09403c0400c8441c5000c00075004014942d260224042c0c100d542c01c1c0340d64050b5500c550303111400100300442d02c5080e02140b09556040c00011a06000506101ca00307440c80f60015804000030480e811300362035541c1c1c0107482807900d07a0000456070072050940e041076402201c0903a48071001c000b052540056081e0000c000e082c40a02546000740c099200c4000b1000c0150030f000c0003900e0083d0341000351140c03002d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 396606483 1250 396605233 396605267
    0x1f05250f0f170d05011409070915170108011d0a170c0102220602070f052b0b0a06150305161101111b0d050c0c010302130b0315010318050a020f01 64
    0x300c3c0c0615030140050f1500b881006840703490080c2820311814003011291140e1501e84654440f04d207400d40521010b032150b411031041090b465444080981030038980c2c1d0080c0220350002c6618102240038141c080c0d00c17004050311340d5201003421000146070340042089201000e003030541728660a50164060700c100860101031201501c03c61402884003400d80080d0b4009a0849151070303124003111140e02500d0007185d50044540301326051500503a80404140101c070f150901c0c480215035030b0143c2100064a50f0418076454103018401c1d091004280e18480c881d6180c140803d0070640304130204011000384100800c64401c0c803940702c505e000d4101101400300700e00103a030703075140440c0c0400b0141030000e542c401074014480c0219000d40704405841000318200081c003640b10b030480c01540258081d1000c1c1c0114410440002000040780c0051441381101030a406841a44540014201c803410400c03e5410100d0111a201180d0005105c1c01401d41c192550b0040300020001a19000200185511 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 396607733 1250 396606483 396606487
    0xb060f0c010c0e0409200a030c15020d08061c020f03030406020c090603062e180b0a0603110405060d02220312090510030203061f05250f0f17 62
    0xc5490055000800c01c811680c0c401001064540400080d201000e001400c40b039a050700342101d00c100c1003038240025070010103421115590b6079403c04c0d03009070f50f8041c0b891064080074146c03074690180404e00d140301e03040c501002c0c540b80020010344804041e1544000d40c40001c110300086454400200204072030003002c0740d444684c2c609009594141060403240980480d0000c601035050019030320303000b00340c084a0311180034040b108002602c02c0421100b020002c8550700084c580311814a50310001c95414804134002034203805001c080b0000340c0c04101018609080c1e0a075007950341042c2c600b9580111211607a4004201180d001380c05000c1110030303081e1301d14413a1040c0f180d20402c21011240308142c0d10f40b022405020954800c0480d10400b81c00ca2010680030440d103100303500441d4415402000c0702441a0340a410f884115a03d0240c5130100700700241181d041d60f0342181d8601001c007500301e0100507100c541d4a980510f42116401881c4020003135a210030442d0342d607030000981c018105059 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 396608983 1250 396607733 396607747
    0x6080f10090f021308122212140105090f0615060d050c1903020309060a0f24210206070206070c0306021207030615021b010917010e010b1903060b060f 66
    0x44000c0d4000c20880d00d440c5920710000807406004206c000040800204042c1803500d13031200f130441120380c0340c2045085082d441011403c07040c1c40c90a5034001e0b005052060b030404459004a0071610050070440580c1e00c9811014031140d4000b03842c1d5402101c41000e10340440015001c40c46d503015041520050500748020007554844600181101c1302c101c2c50f44101018508400b42c00301c4c4400d44000210740c10100000301c0301c0d829500142c4060348186800502c03e02c245100d00741c0d415441682c803a0820400384d00f00184207154500d4400080095030800c1e40e41c4450340020200c0c40740c1c500080c080c110101d829018131003a00386071001140c000b0300c103542d940d2210001c051303c03000440350a00813a01d00380d00490200c0264041141801c40e0b0f07002450290410b00c81785d0300c10441c500010741007040850b801b08075800d0001d4951007082a4000110300030310b20504590035540346004560040340424038140aa0390544c45040440341c0112001640b09090408140c4604c240c00350507100701d800040b00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 396610233 1250 396608983 396609011
    0xf160e010c05071517070509011d0d0614010f08070e0405150a0e0114190b041e0506030c0f0a0603020f130b090f04060f030221070621020406080f1009 66
    0x48180070607996481d0051721010080a07a512050366880c001030018440c038055540103c403181e414a06020a100c115a03403040020001032400008540c2c082e158603550580341007181d000d078058003445540740034003401c7c0003a84d65950390034840d403000026003002080911406018004545400c00345019141c40c00c0c81c2c03000003502c90308082c800558a1301200c3e4405141c05c000c064020b005507640718084107a40104000684000ca4843e98050350310924001c509000740c034140300c81038840502003401c4c0f82c002c0400d4240200802d80718004c1d17040308650b510035907401c1500350956a1a090040c0c4508440b140b051081c080c5006100c8100045000402c13403445c0e80b4090700f500d0b142206e0403544c0761618014403050f10401d10880e991200c400704c0c24401031174200036842c0c0d2001e01e0f5207074001c40240c41c100e15140c0a9941d114102040926045440c881601f400d803460600848100f54501072800c0801000714038005c001101040c2001302080300c69280d041c1041c000d00030900300303003c0c4031812542 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 396611483 1250 396610233 396610259
    0xf190203070c140f01030c030f1a040608030405220b0a0605041716120f08030f010501020601120503190c0b160e1c030f1101060e0109050f160e010c0507 67
    0x1050340d802502d407800055041d109840440c4600024268040348000003005401601c20520003200340368450381408241c416510030b201f020f80c440b6110591150160040c80b003210002d8203e92000d070000c11091045460b2100e040103003600800e100c140c0d01150410610060403000741050307007c3c0c0c1e04400001c21a5001015109443d00640b0109400d40c908849558482c1551030100c11101540f4041102c2001c80751007400030703070042040c80b072030b04140d039243c01c02ea6104a0b81d107000741d204007005100315641085030602500c80c100003555440e500c0c3d20fa8580d0303802000c0c6441443c42d0500901c0028a120341845800da03a030009645955081045c0f50345c407000c610f024500009242c000c0001302c0d07450050002440d0721001000300043c40d4054400710350b0400310700002014070191400c40700480400b44030740801400140d454a0403941821116006d4070fa01070141b0804805803070500c07400305c100b086002445492420155940e251600060b5480d40707052201810f02d00400d840000c41031940f8603 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 396612733 1250 396611483 396611497
    0x60319030216090903080c0d061205030406080c0a050304081303061b11160b0f1b0604030212040e070305150a031a070212030c0906070b04050102090909071a0f190203 73
    0x71109000b140c0300c51a0740c00b1925004006400200200c01050340c0c1e00c41a0002c10b01100d4100e004600c0c50780b90717606c01400c0308a00e01c040702d0300c2e0f02c006020409a580140c030507030480c1d000c440d420b10b841010b0200403e14007000c0c001030259800018a001042071006450004690005c000d20800280c0203134081140c80a0305404082544c151482d10111400700d00c04101d4084040345028060a0400403c07050b0400f103607171028110204105984070700c165071842c0e41c2c440482c0083c2242d141c1031400030304180c2010360114900c20288014060000040c20342540300c2514500015140d80705840c1d007040b000026012030700b0940301c040c08003c1c001d501041c84491742d03581803031602c2510b4a41d801c99a440700c1401c4244031440a102040245141400071316003014010302d014108a680e450304204201d041c1c4040320039070342c001f41d212100e06000c24055030015034000a0640d0074502510700c044100840001301c030803e000141e00b04202980410380301c50301244461103400285418002c0d40d00d6002c04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 396613983 1250 396612733 396612763
    0x13060c0b0106090503100b0d020a0b0711060f040b0a031119030b0603040c0510050c070b0d0c020f0601090f060b040602011e0b010903151415010f0206040203060705030603190302 78
    0x103000420b00c0307405400c018040b00d50260040c43c90210b480d01c9107000f0014012125440b032000d035a100050b0350ba407045e40c0040c0100c8078a040d550106d6203007003100044a04c145038054801441013500600842d825142251480b05400b5910b43c0c164804900800b03d5004c2d07441c405030081404a01e10140c814040c01d00700281c5c0b420071042c0140300c1000024001214000d10600000b80705101a06003455611100005030a000741450303105002a400e000490300102c42041000c9150100b5080034020704080e10005d0020345180503803140035a40b150750502801c07103d1511a42c04025031030352540b041000700480e84034643c03190b0701c5950003400382c044001c003100b142c400d12040030400c5500d0b11612000c444161a002d82c41032a580d00c1c415840c40000301d040505035078107040b915510749035861512500505685050780340e8050000351000f90105003440c1154002d07401c000050b00c0010b0529008026404c141e5181c0d910036001070310340000140d1441d524100f00c0400400c05400250300701c0351100e81 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 396615233 1250 396613983 396614003
    0x2090a08071a03100b130305030a0c06060506190807020304080114010905060901140904021f09050a080d02060f060d080703031e0216060b1c0c080d0e010f120213060c 73
    0x8940c02d1481d41c00242da0396a00183e86250810540300203000800342c81c0c0e49400a140c150f5a00d444490654000d48080c070b0100e03050407800401c0103c188a140080c0c20304a90060600d100032201016082e2840b1906040c003042c83d010481c0a070080094600070005c1c20024040301410000e41c0115440a07c10011910b060001042c40740c9071444909060350070300c0d05a007009500c02c008008241c4006801070307802c41401c800c0104124a100c40b503505040282e2101142c241c1f4007803c0c009070184139842000039070407a80d9040401503010801e15002018070402c04142c1e110800052190f1174a004014120070001428008054040d0003580001e01c1036810040d4815041440c00c00768440c11102e854910700704400500040e225174071074080108040d04c0b007410300303541c0e00040c912601346800c10340d105160803100b00b08400c1d04000104070344178a8a010401065036000181804100300d140d0741c00e0002000308541c01d21142c0e81510745c40d4248440d04450306070380300400780c480000a0801e071010004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 396616483 1250 396615233 396615269
    0x3281203050402030a080702010e120a05060a18030311120f1b040501050901120b0301060611010b0303070b0f0a02070b0a060323061801020d1b0215040201020a060c0302090a0807 78
    0x2880340c1c40c400e64001d00649000704440e951001d280d845000228140b152004d9414942d480c3e00d07018492601100006280d41c0442d070524600e04140241411012824080801c1d4410740c00316200405c150325090101d00d01c407004554040c64001c850512920003800360421074400011401280922615003080241043c14060405079100358000c1901140b4100410a9254402e030451400301607900000280c1041800020b400c0d1041540800d000422942c3d11001c3c988080c842c0506c40c02e4110011460301c2e02c2075841e810780240080801d207403d600440010100b002640454440035442091804103145c100f0f40d0500400701400141c17009540e00c0c0442c8400c5404142d940c6403441c1030300042c00a0f903210300760174a0750254048201d409540038404204818240c1c016248101c520703400c5402c070b289800c83d00900e04040c00c014585e40c41c0b100001d000c0940d801095000d00b1580250b800724151101b28003c0d8040e00c030b5009110381001041c1400030300d886010500c1c1d0107540b6448030039510f0140c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 396617733 1250 396616483 396616487
    0x3090605040803040314010f0c020105010f0b070c030209040206120f04150c1202090303390307032a241506141e07030503060a0f0e0403030b032812 65
    0x7540103800440e0710030003040c40400c400042c07070310800314950000300ea46440505c0a0058440c00c8000e40050f1303440d00c0c0140000311041802030041c0810724841030034441d03603848001d010266407001a000d29441d0000c2010764982000312440c4030000340041600d428854404031020004031000d07121403c0c40088900c141140b4003407982071000954520f0f820034440240c1000a6002849041e4103100800c4030610320006100c0b030748610650340d06030040601000f8207c2e400741f250701c80c00d4400307604100600400260410310125001003040c00c00364488107440754500002c0c1d1480b101820807000d02800c1041c004540d42015040c1030281e00030f1100c0d1a01c03040b5004071007035600980c2c0100d1042c0007203030380401e2001c0240c02c80340d403140c00050010240520321000f40d4031409083c0c00180c000410090f403070408021040c0141904441922424608440c00550202c0078100404141c0c4925440c04240c0c0d04014100320710341848040219040d114510401e0000e5401086401103207078445418903074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 396618983 1250 396617733 396617737
    0x2010605060702060d0c020f071d0106020f03030a020f04030b0109021b0f250b0a18060513050103021308010e010911030c061c140106171522060504050703060303090605 74
    0x1507000d04100c0c10705c10394030101d2000d4a4145800400c41c4514851405529400c0142c50010452041b4501140101550358803c052050304098117550012140c4609040000212035101d2501c600c0180c03221010a052102845180e00181400d103210001294000e241c0c1d00610201c460a510048003800c1c00345030340e440c0c200042003200603400c13009a21000380200c0c0d40c000b40e060386810440820544a042c6014160800a000c100081c034051105026814600d1920701520203800c0180c10024810030000e030400301c6010303d40c105034002c900765600150703503810750029000c000000c3c4a50440690300d64001c1c0105e003400d50340c095a6030403050860030089a658480380000c0c0c4480d240135401201d030b600341c00c041c26217030398120341c0c5244248c2d441d4000c996107030190102e0341c1c502140c520501c0d203001600001820781ca40000c14920341d441c030703a40e49481240c00b854203003d60041c0b2691610400c0300800311175000a8005007001c0070042000d515500c5401500d100343c88000006031102c60460f10340c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 396620233 1250 396618983 396618997
    0x40c0918020903031b3a120e010c050315150d020c0709060f05010915210b0303030406020d0c020d020303060906120f010614010509010e090703141003030201060506 72
    0x594655003000380524500d80042480c140050100ca262207000003001121042c2850741109a4001030405c03050744142e08111345860180106032031580c60360380605811000401d88440c2442503190700300454012607080705505c01460402001040703d940d9018140c0d038003c84a0b00304800d054900350070146032100c07a400d516400e9120341810003440481e044025448009146198483d501c40040c103043c1034040d10f0003800c8041d4032018450f1030074001500c2440c040d00304064252802001c602c0d116030004c4c00c0341c100011403400e14450b007000e1018000034100c90700301c16050f020002c03c0000348002d41d00103040b4500140390410154901500403a1200301301106000181c20402c0400c105281041d0900c1d00440d000309420000422103810a1501840051041282c1d448800400c00c90303290351030303440360800282402d9140c814803d00013070010486402c901d108014040104100c070b4402da100d280d82501b180e40300344480c01c201000d40e5403000300b07100440c01503003403150102e003a041c8070083d1211 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 396621483 1250 396620233 396620249
    0x51009091e06020c1e010f0506031b12070b0c07060801030309032a12020108011401050a0c14070b13080a0f111f0e12030702060f0d09061a040c09 64
    0x401a41040710304440c1e80c490405640c0282c0a01440c0b41d0010180806074140280b030070280020403158400721b0075540f034082200f014a18000820805840110b402100c134100740244800d0800b0140010300f901c50442400700b03003845294030120301c00d4404401082d1410140c2c2c12074203095515001224081001d00004001503050354042000601041290108402000884190f01150b000810b41c1d60281d610000c101103110a4040c04d550300049482c1c054400010412040760110340041c004c0e10401c40c0074010040d030780c0512010b021b5004c0e50054100d42d0f500644108568800340c0324960b4101d5281e0516000319017400003610440055501001075000220748217101558603407181c1d14000801094100d600302d600848600a0020071b00c10684007038486d41c0c0140711500600c6240e40d50100c81c40c0140d03200300840e2002d40d441805440b5210046842143e848000c6070000001d040000001041d141c24a00c0f4a006a498201018040707441605e00304002604401c040740e030390600e4822400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 396622733 1250 396621483 396621503
    0xa050f0f120a02071a09040b0a03120c0302070e0c070b0a15050103020903010e0601060305011509030f020d0f05030a030609050f060a09050601092102030106080313141206070305100909 81
    0x521801c441c01800c0740d4282c0e03005071080e0507030341c0c181817100b007a4228002030101c00000780126245000d200d00c0c0040f040036160030820a055644251602c1202039404e0180000e00782c2c04001c1510070010840a80850034000c40603003002800203405800401041b80c07601200030000e0404000b1340702d0034850341da102d20218110b925240064001394455610a6015501d60900751a4421308128042c020b01d02c50341c0c0020321390315044942d8400d48800c01501c00b002030480c82000402d1070128481e81994042354a0005401c0c0f510f0400c00c0c5500340c0d84001c049000104842000c550581c0c840030071200d070300300f0501a60b61001c90311202488103da032540d0001409030b003030001003000e40c0301950003841814150001c584908600007101d514403588414000054107040c114282801042c000703145c0070b002141010100180d8460b80c2200d801040c040215250600f01241d0700e050b10704100d48110415120705042c1a0002405046e00700c409001d00003410b0b0000542c0007051140702526904407072845 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 396623983 1250 396622733 396622753
    0xc080607021b0613030b090609010b0f15030c1317070e0603191103010f021806090a0e0901090807062004050d1412040608040516030c1401030906020c0a050f0f 70
    0x8071003600300d44000d520342100b204d40030000a12808100380034011800044c075092038420005829910075000c03481c003034141da01411680c0c1d1070742011400c6c911942101507849a072502c880307212a000c1c80c8080d0001c02840c2c2c10019042001014125525036603800f61101e85440d5884402c0c0e0f0300f4181c600710340650140c1045025a04010458a06c651182020032907403400040000c0c25600701601c1a909142c1c000748881c01200000f441400207003040c1d40c22420880c41c2c40000e0740c0c005251045090740501307240090f040600c2903000540f1203900000c8544c0302d0790f0b142415001010f802e414540324082e040800d070030b5020310790142d40c21540c0c0202014240140c43d5210030032084a0300c0020054460b82d4ad051000c90b14036000360018184035541c1c8141c0e0300d06814030380d15201e241204034042544030f150a00200d1a81342c40c0000f907030350f030614800d11071025400480040691080c0a00f030750344081214000f0440105100c034440e8001c01c1120b00c1c020300c01c103880d40c407146032008100e040d034007420101c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 396625233 1250 396623983 396623989
    0x60506040203010f14030f0f0f010e0115051002030702040606080402040e0606030d0f09080706110615100c02030c0406030813140904020d0f060f06050a080d2304120c080607021b 78
    0x74045c004005015158a400c0083c0401d1402242104011f8160801280c200d2111400d00c2101c803906101c0c402030010441d0308910b030382607032260b000d07050254032903c0003251078034001c000f01c4043d00c1e4041d2040100e50b5813200c000308502e41c290b034124071132070400100c114200f000140c12802500e008024040070480a14256070b03a03035030b03400703070f030b0184030380600c00068a140c2070084600170711107074444070461a99008010b0070f151005000fa42c003030303c03800950080d0f5151105500088803407410111076603001800000d10b04071400980d10303030250621101004021100c0050000030b00d200030f00303e10860b1951010400312440c22020b0ba000008000050098600045100d24860260b80c1c108880c1020b070b04c80100b90352610061100d0300b503e0306000c02c030320f040c0b142405004015060182500b01c034100da0040c001400020352609407244200109444107462048a004100144803201700040c0c601d884c103100d2809202d2400d00d40543c0d400070300010f001081a00802c0c12600451f290302c0040020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 396626483 1250 396625233 396625259
    0x40201110d27080f01020c0d080106090510141902010b0d0209060402030c0702060c0303011a07020d030f140c060406060e090a0b04060b040203070816110d030b030a050102040b07060506040203010f 86
    0x80c10410001d502d0000810820a00114048010fa03000242c1d4407090502141c0c07400c000c40150400704041403004100090b8001d000c81c05a4008031400d141c050703802c840032a548040e6a0303035080011030001d40c0036008104224140071142803078000b8800381615408005898618000180d0044250b10009403a86002d90045030302008121070141440d5035a004541180c0020840901d036074000801845280787d80d401d0401c00c00380c101010f520780301117680800d1050314280300003014041c01c405102090381c01641646032a038175400007240c40c0d6520702c0320340e96102d400380c038140c5a035440c144001c104100310720451813140b242d40008040b00c6d94a6034030361151020040c001c1d031324541e94602c0c180b0750b6629030000314010306031a82c9034403007420952022038104014010320400e10080d000000500d24011542406145c801d0500003241c0d140d160101e418046041001001544005004a03041c0c1c00311015004150003000108007694030b42081c00201c0c4028082e00b6031201000000700402e0f2190380d4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 396627733 1250 396626483 396626537
    0x9030313032a0b01140604150c020d082706090609090a14010308070b0a050601081b0f030405070e010b28050702040f020a0f03053c01080105040201110d 67
    0x40c0007a8030181c24440102c1001400800b202c1c90300c1200010458105a141c0d007580003002140d04520703261400f8511503a9a290310003907001c0c010b241900c84199682c4135080300b4501d420400d201e95400e1129002d4405650800b58456062401118000c640c10f0007000d603010b140001e0700083c940302d0048100002d428009010448860b26451851030b00480380d680e03c1c3c0218803071022203440d0081c0c0d240c032841c8040f00400701c1603000d10f070104014280c0e03130108070380f5006021031038051909102040b00c44041e00c5101c2c0345030041030300042440b04011001034031500315818001840e0740c603629a94260040d1181d0950501c0e440c0d0001201060441030340441c01c4c0016213801c10924004881e030120341980d440c0ca640000455011900c010740380d40004a000e684038281c40c0c20851882c140c1d094240701c04100c1103140800089680f1002511041403c1c105400c04c006a038004c00c0d0b9646007000d020305002ca4049002514105096001403030024541d50011404d07101c0b4980364842d40c5080ca2040701c009 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 396628983 1250 396627733 396627767
    0x415020c0708010614010e011b08031008240606030925050d0b09011a060d0b04142d070f08040501150810110403020604060513031a0a050903031303 65
    0x8074001035420740c2480384c0c400070108601010842100b000c00902a10030704007040b410720400066180604c43ca1201803591541e203d0411921398030707040034030500e1f14640d40214542d2b206424040f4402d40340c400183d001c20520102c280c0d03403a40d03200c4c140800b42c00103440b10b48465021038110b0001501c0381c0031008461207110215208503a40380005814581007450036181102110705125aa0780c0a000c0c00e412495185000705c41052000c0c0401c1283c891001c47d0500c055540c0689600c56171075401605003811460503203989030410203442c844585040301c0b0042e848003201c00740c000402100d20b074179115a62a07195180d4291800d0000d60300300c0e100030f208035240d541e0b070f1802401040003000258080c20402d0020314412103665076140c101e5000e0008154250028401040180d0718401158107880c0c641c540f40303455014044c2c64600504080c0c0004200241d51084001c420200b000c2c02132061154001c14811600ca070441e0301d4492105a6455840040072482032012901611101c0309050302c807 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 396630233 1250 396628983 396628993
    0x50d0b0a030f030f0518060706060f080708070e2e030203070b0c0705031516030f020f0702011e02060112031e020601170705012309031005090f060415020c 68
    0x190015150901a80080390008a80000503003419403000140c00c1c0f80c401c1d800d0143c5031020b4030003160313460009150b0047c070407100020004100076854101c0d000629580803081c01c00ca4844121945442a0b130140a0041c41510000120b00303016001150040c2e0310402e9400648800c14074001034010894860318aa0480400010058801304540c1d0010110300007255200c2c0d4a00d0381031410711016a00152192748003903440c194201c1c0729102c2c15044243e044405103c040b58100c1a00a0300c1c40350812050a4408941084445013003002040e40c40d100766203200748600502d044460070441d5040990050307100c03c00500c14155188112140c1074045d04219194401c45e14014190300c8254183c14010b8100400402c2003c881304444250104000c02a040c66402d00000a184d8441b1004400c8118588940358030040310400880320041006400c1d10000001da0306400058a000c0d60390f03056601c101c00790780491410101d03050f4015a0721000e1f00c0e00120034440400701a40020f16403406901a03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 396631483 1250 396630233 396630251
    0x60207170a02010b03030705070e070c1502120a0218040203150a17060117030306090604060e1003140a0515070215100f061b030f02070504020a050d06060e060703050d 73
    0x180310800c140c0034508800150340e580388804001d0075030718550b40c0240640c2c81403048000083d804101101036a17500040140990740d2200121071601c0c8040020b4420424200001080e0300c29030028074900d05003080389a4651103d203000c1d0101e200d44241a1080704081e006140140b5180c0c0080d60440b4900124042c0ca145880000f43c464005901c02070001e1100b210300a90800e080c48014018002800080040207108048544910008001610890208000406c03c2d5100c0d0b1100c00509030295611145241c0b118080500c0c9091380030030307247c01504140d400b60810380012040030399a03108014041e0349000b048824001100a0020070944c0280d0000501854400545511a020081c2c26000e05490455a248501c0e901d80000040241e0300801506403001c803684940450740c5843c05116450b5240412800c10100350082a40280009a24a1041e501401800190100070000c1001964407041650b501a440f17042d1504940d051101c2404a40140c001e4120030002d004082140c43c0c0d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 396632733 1250 396631483 396631493
    0x305070905060c3403060915050a0209012003070605040c08060f0f0c030402012f1006050f0301090203150a1808070b0601090501080a0f020c010c05070b0903040b070f060207 76
    0x4101440282ca5120980184410000b54150703000e200c80082030b80450950004800c58415117030202900250711100c041d002c204005c502aa803405c600c080070400350030200c81c20b0001e035000e907008a00091011841f00c0009501108601c0404940e5004614013802c0d95502d1018060003071042d100310701d02407000a8117030070500000340b24a480007801910703071034036528000d01460040d00048545009204200050760002c0701034000c07410000500446e0324103840c00b101e401104140d20381c0e55001c0d5801300c035400d484035041802510700440c0e2800d00301444005050885a07509800b83d455800420a03004910345440308980003161803a011602002d10440061282032081086440fa100020601c09201d0780121f0f0580040c424a06981c0d07951400b00020040d90024200c0241d003580c03040c52409980d060f50448102e1001c0200a016440048002501ea5085032106a40d42400c52000510440c1c1c04000c8030140c48540030210309001443c0c031200c4c01144d03c0c2e0340490b510b5038200016400700e8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 396633983 1250 396632733 396632737
    0x230403051c020d0e030d0c02122a06030f06060a11060403021f02030621010603061803030510230d020607150608010902030c1c0c0603050a110903030a030507090506 72
    0x1e801003801d101529800d402850004202d0803c81000501906400f082e580400c4292000c041441e01048540241c000101650081208d00040d480340b8507103d512017412a0001e840c4200e01581954546080c400340141d131700c42101c4000d01c0ba61000006400c0e071912001402c0e00c6000c44c0342c20100f003144820010b02d001da00355002e4000d40e100d64402c5c10010f501e0f820402405440c000190b0a605200001c100344200300540c1000c040026441d00348038000c00d600c040002e45d00100144813803483d0078501304c1392054809044c2c000a0500e00081d2100c14100b2142c412a00c030450032005c150315044030b0451300620344200350360046441d00d2040150b51044082e011240c02902c00080c480e40c5500c88104440c1103038401c10030307a41481c1900004d640d01241c040b0025400303070343e540f441110f03402c201c1600858003407006004005000011070340356815840f0034821341d00407200f013140a0b0304000320f41c141d010b5a1101e550581c010420001c45611a401090700080203051246a542d200c8000404035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 396635233 1250 396633983 396634003
    0xe030708031e06060a08040b2508010504050a050f0f071707020c040e010c050909090307060c0f0905010207030c052106070302131e03170d05181c23040305 68
    0x42c002c201c0c140c0011144080d0180d400410860310f203032415001000280060714002d01c00741c449650b820028903680c0304040c101003c0f0032030300150103901c3c02d5000050134407842030080900031454800002d194100b20701c80e00d4000c10101c0a1a0001d0350341c60101c00c08040000d0034035007003089840302a207105850214003400303040a80c02130034035a0368103400d220803603185058804203030381000c445040c1140c001c41180c425613400e8a122400340c6d580c83c4800d00e14410381c14000d1080e454040214640c990010b41c01c00d132189540d80300360340540d85800480c0da92616010142071984ca20000304820b240c10001140d10804c010610f42c1140040d9040508080b002c603403036008a600010380e031030925000031412010342009502c601e03484070603509140c0066142d0200a1468110700800100c5203c10820b5900082e48500b0500940c03501c11030090301c618403401424464407036410349202c128a33664090000790400daa03103954107004422a0007000300c0c0200c881800140402000c800b107441841540c0074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 396636483 1250 396635233 396635251
    0x1202010209090a0e0c10050405040903090806070201051008030408070b0a0e041505030d02120307050c07030b0a090b060d0b04030e0a03080f0a080c2b06120606030b01120f060e03070803 81
    0x10124011340190706007134140901505c0342d048007810301c05a580000596055400548000941008520f0180c03007050300783d000051144503500c200641c10341d05410441c0304003403a04502240c40d6503000c03c166030f4021409926940e0300010760a0010011134005096288001d1404034240a41800824111810f41e00468108847d0400501460504110811112500307100401025150700c0a01c600c502000d4030203001c0050000b007004050314100205000b841c1c012603101e40c1814960849401004e034410300303c0300303480c1042c0010001d282280c006d483d81900027643c0310310340d980e03030750211b401e90803815500ba44000003000101c0414003540c09401140484660075070398034100e02000d001554018600840c006041003020a90451002c0321803051460062405692040d60500c8020f05066080401300103a251101010300036242c11083c21640156070594840e62584442440e00c03100b030350040c0c81d4043c3c1c0d1101c00000390260340404d1400000340140d0f4281100c07584c805405510988013104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 396637733 1250 396636483 396636491
    0x40f0f0b070e040b0a140d05012d061203210e0106080a05160609030807061e0c030608010b0a050d080d09080c0601150c08090109080102131805010b071202010209090a 73
    0x340b6410544a0b94880d00c10446081800a00d0a04002c515045d06250680600c0081c80070381c04100003500206449400b007a49000c0641d50402c0200b0b060f83c8500800500741e06101c2c00207000391900c900308d18034a4050340d0304000c103002213500768405410070f00c9060b101c540d03516138541850303800c0c030460015088400190640360707194100175151440310901c002d445641004208641c3c0e4000340002d00310384e800b10109440321800c1c100340c80241000243c40610941d14100a48503600c244e00c04601d01c45980c4041101350340302c0c4400e40c2211710640e110b44c1c101c0e200f00c00611041c6000d10343e1000707851103854164a0300d411402040c00362110700e2001c03500e0340b5010904001c062014003466014010141720307a201d140442d04004c1121370b48030006401100300140e1302c1410391052407001c020b08800d0000b076541c0c07040903c07031900b08642c0c1e220700300b9488805500d1001d81070542c0145812981c0c01c11466080c01055120548030864001e071800070740d035007000244269205c40d0070f031911030360085400103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 396638983 1250 396637733 396637757
    0x70b030c07030314250c050706080103031d011b08090a12050d140906031e0c030a0b010903020a050108090304120501051504020715200d02040816030308040f0f0b07 72
    0x15013038441c3e08083d420310628003070030032070303100f034000110004502645055420781d07440c1942503400c0151010054084d00410801007140c0703801c40d004904072482070341ca10141201c0c02240c1700707151150540080c001a00c48242003c0140166505480c0c02d014801480c54800e4620015440c08a681e01513070418410840c031100f4030209100710008100d1034208400b100f074002554107098491000024841c04002c004640071611803030050580914105003241182440000b94002d0381003220201720702818114030146a500c110010300031664094a81101c09003020011345a07487e00616640c01231205000011f40c802000003000c441c41d00400c000034181c10710b9602910100036400455000790b0040108000080b26200c683c1445c80c2d1910000651948105081c21498919a03003000e0140000c15614100e00165004200321100e03002210213151f032146c0c0903503e16441384006008503024000060100303201400441c000340c89681c001f503500950303079200c00c40e08600f501c0700d20000d10040100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 396640233 1250 396638983 396638987
    0xf06060f09210204021b070603090203030d0c031b03020d06091a0f041b1106060a05010807030f0b0a08010903020d05031302131812092301050a02070b030c0703 70
    0x55028214510341a1a000d1201001901d29462445100580c0350024414000104042c1e801c0000542c01481076603207140b9892030380224500d40c081c00015016000c000140f150107446064400c03603000d4081c5080842c0c1003041c0d0001c00741b5207608010301d912155000000b211411059405c80d8554030016200c1d030400442c0000c84406030403c01e44d00380b070085185128079407900350716000a001c68031052040d0301c110109000d0000280001c4146180030003960102c0e4000c0c4d078010302a000882141d078982c0d0b4450801c0b10100c25440b50754041250301c004500700d81c1c405e800c070150101c07032000086150407000703000c5031045046a00000e042d940d50714002c400c050b81844100c070080241c0c41c106045062000b404c84241c1e05006d4000d20400259000e032604602980003c0081c042154120700c10f4094de0818030301d85071a500281001440e03411010a4500e0b0f82c4640011040c0443c5000c1c103800451401541d1942c0001e61820030342c8107079800054070000300740040d88a0000c3c41455034640c4028a00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 396641483 1250 396640233 396640241
    0xc030115031a040b0d0501050705070b060d1113110708030f0f090d0c02011206140319080d0b061315110a0809190b030c091203030402010c26030a0f 65
    0x3040100740c140b9080c003291403480200e10480c200100c90000341c080100c000905501c1035002c00405035400d2000b000358854000000e091498000c0c1d00c1b40c6030381e0b0707a102d041204081c2654401040c50b40b82000c04029810002408144140c01c5200018803040c0c415000c01c058001d810b003200d52040020030031901031699800560440b1401c10580e0b41420301c0c5c41040e488004d4241d444040103801111902035a20480207a9106c030107443d030810070b042e180d0f0750b501c040341d00c12010f071070180c800d03982c207041402d581500c81c03000c0c5a000107119041040c0e0403d4400549201554541c0c031203801d202201d030301f160040720a001800300c0c40014002e425401f0313010303114241c030404c4084a6003210006501040200d011100744030011140c10034103402440c071405888513140c01000c0e02c000302104000000743c9100041c481c841d0201c891462a452404400ba502d1004503002400140c011607290001240d03580d110700d02085a0403880c030001d41031014024240c00c201d4402d0206900caa5181d19620110700c6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 396642733 1250 396641483 396641519
    0x403080f0a1704170c030d05040503070c05030312060d020d051006050312070c14041d01051909120809031c051824090c06040303050703120b010e09060310050c0301 72
    0x14030b003641e0345000d45442c0c0314007108044510340010006400c451840c2c0910440366802c21001e4108407505043c201a5980d0b04401c2c030868039000780d804041841c1c0b600000b40c84070300101a96403009607652505200042183d840c00300d0304080440b0010340025801d010b03081400003640d00001d20b02e0314100806161070490300e040d40c1030481c01c010f200d02081c02d8418000030b03070b403003122140319180102020800400b10000000d050601d40c02c2c1356843c036501904117900400082c0c02058110040301d0259003100c80314230000342400205004442c800d40610031403680803010005490520220b2101c2016280030a890f0262880c1d941c1c00700b0200c4082010700c0405000d4843c01410a03030040003603021504900051750140d1042040010f05aa40400c4402c81594000d410140c5496591030050700c1600642e40880205505680014104240d4462540c01480580d144410047d640c3e040c00360425001d84901d4040c010745100b9015440701d03000f0329000b04d00e1882403544c0da6150600e01c0c40b0301c2607070038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 396643983 1250 396642733 396642767
    0x50408030f010f0b0f0304050703020307121103011b030917040f030b0f070c0f050316030e030105060f0a2c070507140309010c12200706090504050603030a050705030403080f0a 77
    0x740d000e10400700d119045d03030403c44454000c60b0340c0fa210790400034980b0f412a0300080d414402d112000c07620386030780703030142260a200d442e140c03040244840815003a50460101060000000b5940c601001d103c2d0f00309a84103070286001d0000740101070700700c1c0e01036070158000e4064030582000070820844a6094039510582d00040845141411440140000100007001e40704550421400041c02018030850f9411a00d8000c48480d0003e507140c090001011a09418829481d000000d00203040c95420300d9070785c040003090f1600c002e0409211040d0b540720040441e240740112418103040719a4201c3c690301801403030319010707200c02e414a08160240200e10880b40179400034450301071a41d8000900451465010200340110602a40100c0300e0030303d402c1c05c08400300c1c031090703045000401c0031a000042e03658940e1020405a15070040c802962801e40c1c032560140d04c100614500d40d4800c0c00074011240c03154007505d01e0f069882c4c4940c0e40c5500300d5500002c0b00180064203034440d40c0c000701160b4a11002e5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 396645233 1250 396643983 396644009
    0x20f100605090a0209010504080312070f11100e07120b01050a050a0e0c0a0e040f0509060c2b0e030d0506041404020303031b040f03030c060f05010506040909030909050408030f01 78
    0x100814180000036100d0301c0a1a00450140e0481c7c0c0948265406081c10b40222503d03106a04203000065105441d51800b207100720715920081441042660b81018454008250740d01018904500600c80007460040501402c4004520303040c0c8542d40ca5401b50050b04408181c0d41004200301020300f044d845288201c0f545170080000d03074043c050300c13684908800039090300c503800c11000350b85010300303404000c0c2d01c00d00d0100d051000c9600d0b58400e50061000404513030407940e170074a0100352446480428a4003080200c185450030301b0b030802070610000c607058045200f080e030701e01d01455508a00d01c4030f00c500b5290004c00206040500c5481d41082c0895000d03205400c2070340102e80c5910000c0c1498421395400c0da440c900d00ea04d8402120000d040f100742216103265203040040c04080d0203002100c0c0c65081c1041c006400800d402150305031240249450704d802c2c41c3c80e280c0700c000c14240d60118213000303280300009190200c80c86100d200368000c2c9851079507854000d00d01c8005190503001078a060b004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 396646483 1250 396645233 396645239
    0x1008030307090b030606040e0a021e0a120b0a050d050709110a0c03050a180803041e05090f07021006270c0f0c0c05030a210903030e0402210106020f1006 67
    0x2c0010000d084901001106a6036290640850030070b2003039400403280c19021a040c00f090103841c0d8020714480301c4a42040c030700011940c1c00541148151400600000c88000340c040c43c80c03216074004504000002c1500c1d07078450faa000400c800d544140c10544141e0031110003081f1174007840c02503080300200d0440c1d0502d80f0049850182c08401c00c1d0780d01404201c800304000b42010b014a200c840d43c2c0c44001b0300c5a03e19139030b03040305941e240d005000c0c2c0301c40c2d004c0d11403040e21a45ca42c000d11506840000300403a555507581401888264002072070a011407042144001015505201e440013909454601e56031807a42903600c5028115510215103541c0e1520304d901c1822a4015012400d40c1814584550416410f0900c0080449560042a4103000d01240103040021078031a911107032217040032982c41e10142c3c00051b41d48074001e10025005c907184184c88001741c5020307402881e04885000a0840350303c441c640c12840c0d51000d03040000940c0c0f000181d038400c5a010130901d422000f555805005040c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 396647733 1250 396646483 396646487
    0xb0a060c020a210c030b070e01080c03040b0903120a1407050703020709110f030c030411030f0d0f03060806040c172a030a05060705130504060e0f06040b0a09051008030307 75
    0xe85204020201c0d1052038020101040030490205240e00130311800882600c038102200400b80554011000c40e8035904010210350145c0140d501c25403442d0046421b50380c0715100c114015200903d201902d00041100d401c080c24042c0005005004040c40094038110810b2901604000034081c042408018061600003990000380c0e03c0941d6500c0e400170508907501c030310034001c500070382e0350a142c0c098001c010041c40030503550103141305038090b440380c0c41e820b8a200145619452044800120f03500202c044140c45801120b2100000b845032070b0002c6c3c001d80d920500b0f07040103015541190f01c444100e00400c400b101c0b09880c040a40135046c041c042001c10308001da0b07044203a142003181c140c0881868181c0c655400d228550410740c01500340c449614203180300400b01d07801641c0c15100c040b0b0814020405007020304c903c0782070fa803000200180702d44461000e801d050a000381096440f07034603510744052544a101c014070042102e8200403d5505050940001705d002c00c0d01305506030b52013881004032040d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 396648983 1250 396647733 396647749
    0x203010e0a0e1e1c120c030c0206041e140a030e040606021f39050a090e04020a0b040b1c090b010e0a06080102031305010c09050a05060a050702030a03030b0a060c02 72
    0x7074003d9503c22641c40c6010f03001d81440c100070482c07215100b621030500b5050b03401480042502c0000003042000d9500000160115040c00060b02c0c0164404400940026030030700300d00320041480741034840003044990702c25261800001000091750011010702080617080602541820f60880d414403030349040120080da0303284480011070035804420b0034400d1420341a40494440b0000520443c007014506080703a56420542c10405040700c8010801c4001620440640b180e03503600382d684143c06413a04020100b18a0040d0043c0d078006c03510704001070f604940794010f00003800e4400031301c0d4851200e40c3c0c07030b201200d1a00c4a00010309060001500c0055a0130000314103544041c1c1034800e10303848528000c1c00408094001c0b8800b0b40c07000050045400c3c1c01c2c2000c8403082e02c558006c2c40300e0700c9000c0c400c480b104603030300c00e160300140940070070300c900d16105001d049450402d25080d42000f806800103454104240c90690100b581c9075050310783c504024190380003030020340c10100d20760000d07640402c1140e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 396650233 1250 396648983 396649003
    0xd0b04140c27060304060b150307050d0e10090308010906120f02041104080601181a010f0f020a051e071a03060415080d09080601050411070807020d14010203010e0a0e 73
    0x140c1ca0150034018240c040c2a02950503405001992a480d03c2d29100300103044004e000f230310504640c1c0194020f00b59440031a4410030603603a520741403030110b4840801a1249240546c10350144410001d00c2c00303500d10461090078044d43d075450040d45081400c0c42103440a800900e0038602d9101e041d004154442c40c0c0740f1200c1d5040da40080d0391f0f0f42120421900c0c1c0555001900320303004180000030460480d4045084400103088104120303d00c0344141d400940105000e5800315a01403407410480e03000d0200c0781740501c00342c01034906004c480d0303480300e00700f4203030718038003d00d803810080320440c01c030000c2280310064441c04a80d541000c0b000c007803080c3d0500000b808544181d0301e070140901c0442c03454500000404c407070000c079480640500e501a00c00308287c0200701c0640305010000480e40f51a02440c43c884940ea03050902d41a15500c81c0501680075400c16a000205111100d0000b40d91480b04144c0f850320600050700c1e5410460440718120300a070039a00c001c0c0c107010212000c101c02040803074103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 396651483 1250 396650233 396650257
    0x11a07020f1503090703060b0a050916030e150a0e0304080a1e170a18050f04020d0b1c060c0801050616060b1201090b0c03250302040801020d0b04140c 66
    0x500d085000041c00d40003070071120b100700101c003100f4081c0c50880084c201c0192071140c0c0f001d00c15056a00b0074041d4a54092007055032110510000c10320100391800c00a9003008036240c04128145a04941441c20144251203c01c00840d1070800c01010150b10441c100400203501441c94035180651b42903035401b0070b0001401d00c009910f1808500708549241c40d02d0158032040c4d980140c0304104242015810035514800030074403c2018401c81c1c40481b6000041d1000100808119803e08090000941001d14031146085e40e84a820f0040da03200e0100c02600e01c40e81c03042d5020101180f910707400342c9401003049014030015800500c0b4079540c20082d1170b602c2c1590740b040c007815405410500c0160981004d910740100c0303c4101c4045680301900401a5039008441c0b41242d0b03100d10b021201248000c80b6041d0f080f1200281901c1030708041305804484010a01c0c0250400717445c0d05185003280e01192403108041d80da113602c0d00890030540a8110f16023040074403403c05240c4000e01c501c15100d10012001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 396652733 1250 396651483 396651499
    0xa0b07050f130e0117060105060a05090f0409080901020d0201110a030f02070c0e1e0903030c0c0f06010902030f01050409050c280311030114040c121509050114011a0702 74
    0x100749003016090300e611a420b05600310240c0d0340d50300b801000e000d0a010302c51410302d04c05401080c10710005416030403120081c1840b49003d42b5110229a150030810a09030b0109a0244034a42c0b50368500440880b5400b40000c10307542e445a900280c40c0200c803040700c10035a41805940d0440d8014481511806800781c100401c4d00c1c600ba181c800004d2240303840041460081d010041001400300340528400c1d051800c04403a0042c1100c40f01c452030600b11008440d40e44100002084600c010010308a00c025200c01c0391114103409860354106842604203100055012080010f803500440c41d090040c001581d080103015521340301d0a8480c0084102603014441404002202c003050400d0101100840e01c030781494151240340445c88020b00f002c0c102d20a40c04c1c0305411099103010038025000350307489000075030311504c0c240d040302c40c00b10700c0082994a0230b2410160900d4440f603010302040103100d20000200c1c4011520958840103040c0c204050700c240c1d40144201c2c110402c01154400390701110090 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 396653983 1250 396652733 396652747
    0x105090103060306050a1506020304050303071b030804080604020307060f1b17071a06061312020310020708030603010501060534061b03180f0b3408090a0b0705 70
    0x60041c2c54658401041c540c9888100038044040d6441038061400720145a01e003959180d00c100c0c2c0d64007644c040c65070700d500200140e17000502c1003400c0300c0d91482c1501840c00d956590303031144c0102d40c1042d400025150000c4040204515040c0409006881c181c28082901d04014100900c80100340c1e5061041c03860b00d09103241800421025800480c10102505958075098546142ca1100d41103c880e031040340400424840d207814400c1c0d6801403034122a140fa41071810241c0003c40203201405c0e60180565410f06540351b40600007418014003600c11907a40c4e04240d0705250031a48140d1040040002c10301190101e401c449181e0440d69048808681c102c4010640414840d00f00600007400f0b185000317104511440b04001d495180c42c0103032410417803074140c421003400c40f04000c40020b00410480c0f1040c40091139200420360040318001c0140c0c10601c110104110150844409101c001e00b1075044010584e40000603e52101c0d6981c090704c0c11200b00e0303031400301c5200058501c009121002c1411 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 396655233 1250 396653983 396653987
    0xc03030b040507230c03030c0a05090a030b090f0708120d0b100c0507060c0f030f0203090a0305010b0a0b131418071d0102010b030c090a11031603050906040b0601050901 74
    0x25040d85030001c004010742c3c00c00d244003400c220200c03d460400c0000d121003088240b0007860540c2d44081600e03018510315036131400d0314070495002e03203444400e1020074466407000780c88500100000d5841241c070400542001c001182c98003c030404044050341c049041442201000b20f80401c006604046e11a244c9505080349009820b07202002904000d000104801d4554024800302055000d003003546d14642e1561002c6401d9610780001400c0074200c032141100291041c038448201204c1407040e2410001130100059000105900c107403110b0391242003075201d503d0a01e0007a0010807840c440329190200d080c0c10300c20003a406129404a484002d200c5c40c0340fa2f2a5560240003010401e8681e541c1460300c00c01c050148904900986021107203008125615401445441ea90a40080051030f460402000300480040d0041400002a803214010114994a100950b0103940d11180b01d41c00000066401421107000508440c900e40c40f00e828400420340402c02d15030405428609107644c0c0d9992001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 396656483 1250 396655233 396655241
    0x110d0f03031e0e03070303051b070b07091e080f24101e0906050a060210050a0e07080f0c0a05090406050601020c06040311130510090b04060e0709180203070c030c0303 73
    0x100b44a442e0070a40704182142c408001803811703901c02c5d00e0400258881e40007038104c0380007980c2d202001304030401917070000c60b01d80c3c03402c82d60009607468641220750325131030701c032445030342c143c5480c016401400428803880c0414080b40040145a0b0003e00c170000c1d14440e16004500141c00c2c9822040c1c0410201e20800d210824031809010000440180030b1006150941c480000d0700c22100c00b80d19007040800c0c140b40c002010b500b295100d900600d110740c0c0014400d80105006000c240d00e00e0b0b074410b009038800c03000b4813100c002001c501000d0942110801d1000e4240310742004043c2c440d0301c12038014440ca80d9840c05180e04940c00103000074440c3d90b2500180d04d0107903400085603101c1c0c00031a001041000b18001204190402c0d16599600c40f003281d070581c203444040e904a07120f02110038003405107100c907501c850b14030310000700040ba9580e40da114021020a042c2c03007810000d0581c000610250125215004c0640e070628021841e5152144e80244003401d03070b1340001c0402c01c690500000341403180d00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 396657733 1250 396656483 396656531
    0x905070905040804080706031406010f020705030d0c060b0f0114030915040b06010e011404091806060e07020712020109180e10020c0d110d0e15030a09110d0f0303 71
    0x2010401d506241c104400c058000c1c0c890060180b04a500100d01c85200780100c00d004041003203403030300c0340d2603081c015210590408032000440c855150300040a613010010700f2121085e64481da2403904184c1071910981d8500200d01f40a2035103440300a107941da1101c00034a07801001e404140d00c1c1d0720b40354119400c1580c2c4a41180ca404104002c1c13000380704014180d5070085000b40c1305c802481766107030010343c1c8056a0f500a5440e9000501080044844d1078010703283e407420b10010078000c04010303501c101c102c848a030008400341d01c0d1142000b200030740411514015103031802042c00550200e600007042040d0030700a4040311841101150841180c5030000210300c1c006205803441c00b511810040020b4010801140a610510541c240c205010341e1810040d2100d00c80a8184070412060980305401440b01c00c94209603504503003407550301800c014500504403e80f0100b90360003142002c0c00d0542042017464400c1d1611a00303c000180204100c103c041ea141c01d000c00e106410303800c0030641c0e581843d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 396658983 1250 396657733 396657749
    0x9050a0c111e2506030e06040f14070b0d0f0c0804080d0216020d05160501032708160309140108070e010e040f020433080a1806240b0a0e04090507 64
    0x700101000f40d401c2201603400f02e5130104007103a05c0b16103407940c504003510b0190400d0514401400820781390f41c1c0d4038201500c18011200d150355290f00031202680700c22903d80c107142d510aa100060740890042440b0540380345004001c0c1d043c40c2e10f80228500c148071744240d1050380021601c41407202030058012943c0c0040c0894240181820426100c042041c07520b08114841c039000301d195030280c8610040a500c00c0324507066900c0004034091700301e2558400b5107020000b4040e000e18001400c1803001c46030310036694500d4141c0760000208030002040304050620440700100840580d00000007030145000b480e00c0605840c03282c02040081c024070114018040c000500499a40201841110135404071868080310140c411001c0383d190b1070340d80c03141c4001040740c008150ec41c3da007500300074141280c1c3c80c1c501070300351641d658903811520a2049240c110134402a030481404404840d01c0052102c401c04500c1d2202d40080100008a42d01c1c003203103d03580d02c103a035100f480301c1003044c003020344920 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 396660233 1250 396658983 396659023
    0x18060609070f20030705060a02160609080f0c030a0e01030c1e0c0c080102090f0406060c03050310120b190c140f071506170c1e03010b040609050a0c111e 67
    0x102c0d90241d04c941c0048800c5c1c0e5075100300ca003c66020841c51003111074040316035171980302c408900d5440030094200c40070155a11041804800209072314440207281c088855401555101e14805018018030707007a400300c2d03061506e460030782494240c004000c05210f2840d4000c0b060802c403003440c2501c0300c03000008007804144503100701080c280c10550082c04e01000842e0480407840410003007000f6142d690044d40700241d1910002c00000c0e000b40b0281d50420400d0b418120401c0e11011000044c89100c1e2041d0345a03201c110902449101068804a1072221003e081c800700c60000006801c00c0c4403040740401072030300001d5804446881c101595002c1b6803111840000070a46103407040030300011b0040449946070900d000040420000313800700ba1a02c09801001c405c00c81481c18041482607080d0b10384c05548403104416203584038490341001c0c154107400040e0a0034030800d004101c60310890ba440510107080d50081d00380741c0000c5c00900f0400307101c40290a1796111040f1505107106401400701c44505 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 396661483 1250 396660233 396660287
    0x29090303100e3117090405132303090307140f060310060c0c03020d12030609180605040201090509070e011e0e0d051c0818060609070f 59
    0x4040011402003428060600d54551240b940030102241542d002c0c0540440751459040064030701d0941181c440a10f0f86405002119100c51443c01020b8120808a1000054640b0f081c98284202c0350003c200304801da441040039078402d01c2c20227441003600f60845a03040c501e401000100100c990040001e4256010703969108403903040e15260701166071003420b441100e40405e0030500150780c030547c815070911401c04e182030421381d442445810291a440020030f004009a02d56654802140e03200310380d22043c1c0d5092007002030440c0d40342d4128104103400c2c030580781c1d02e2000b942009018160030600004d01c80e00c40344016500c11620380c1c000754210049504000090303030005090690428203880311440c0e40302c00c1c2c1d00254805260712040001c1a0490700710b904170705008500304000c600c01e000b206c05240d0100241d0000c0030000f00000001141c0004000d4a504040c907641161b00899004241a040010004480c200024105020000b6000304101214440c3e40c5036440c509184007000c1c04842 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 396662733 1250 396661483 396661501
    0x1103070308101d0a061a0304030e01020c060403080c01050106031107150b0a0305030d0b0303070c0e06150d06140d050607081009140916050303030c18120304050a090501050d29 77
    0x1c000c950642507103140c030f0400120b01181c080105001d03c25646c150b407945e622558140c40c3d46d0300c07a0050b00c1c11446090728000c5103885100007007021754080c034150781c0c6400c7c0e425510390075140142c00490406061241252203511602c0540312901c0e84000c0300c4802c5a030181d00e510090600c00350150740100000720000a209003c0001c04401c0c11000e41407001101d40400d00d5075030f202d0410000d02070690000100b040b10206491260000401081c45514092500c0d0026250b00545810002d041d91290104158649482140b0300c0040030760750842040d0440d1100c0d03480b408010201018090bc1c240000c04010328002c015020f80342d030120801080d0207100d50482c040a0882d00e20700603118200c1a0128141e040c2085811190007d000314034558903a0155162031700314172280031640c25005404030096540c4222419055185001962290f250608028200c080b40d070100c408185040c005006a4440112010016800405815007481c41c4504111499a40788852101d0424101402a00c030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 396663983 1250 396662733 396662789
    0xb03120304020a0f0e0c09011701030b180105010b2a07030b100e0f040201050f1b030702031e030403110d1b030c080309090a05100305070306050412110307030810 71
    0x40c02039401c0b0f4049603d40c55242e0482005002d071403002c1846000050050480c0002414146010314060780513011042c0d030400d00c0c01080e0400c440c00c4400a0401441280c402c09034040340101c68024010b07540362240d412054425481c800407000301651078101440c03044800916805800021500015070303e04001100c8101900c1c804480c0c8503043c000151080d800300014003c1c440040e0700d4042d41c03203d42c01540e182d800300f45185000c010900000c10520300e85030340081c12001c0d8030302031a522201841010b007440801096165001c0c1418521000c115000003034034142c2781e100301400d42c4010340c00001080706a16a130700500b0701d0309955a44104910340d09100040381c0c829070780c010003103489208070f50300e82c01100c43c81500641c03580c00103281c3d204140c022503001035006a0050165442e900c541c0d0900311103410645d55540c84c0c8090100700f00b0101c42c900c02c0d12103640b520b40820b401880c1d034180c8078491402e01904120b184000300e1010805851480010308052203106007104800118100007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 396665233 1250 396663983 396663991
    0x40b121501090501021c12150806130302070e0702070b030a020a1103160303050411060301080a0b0a0b01090b0a030e030a020106060e0301050c1e070605100e090a020a090e010b031203 80
    0x2540a8000c0d0030550051800d081038034016006000700900c55110701c1c1c0500081181e00e001c0000444001c0441c0603107100780d5000e2511183c2c0020081e04240c90740d86024406082070390f4207100c200c1c40e04007107503001c00d43c1d40580d0210980110320f512101001c92070b01c3c10a03080144078000000a001c0400c0903607000f800201e01580380ea0f201492900011030700d0303014004100c07000e4401c8c0822080007a110707600140d400ba1213920b80501e5509070102041d4150401d0300503141c964040f0220000340140800078560058101c00280403240b01000028903000c2c00b8410b01d18440000700c0c000c003045002c3c0d003000c103c2200c41342c101c076280c40b1a210000e0203840d0a21600b00401c01112500c4a0b03414103000381c900c40c40000281030314160b08044500e4485625142d5404a00010f001001c0000c002d030040310302810403c0e0b84d4001460038031094100000010300b91003100d5010404520050300c0d10784042046901c00e01c000640442c965021078091b00503528911781c140203950742110321054201c051806 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 396666483 1250 396665233 396665251
    0x40f06080a1a01050a050c010609091505010b070209060d020306041119050a030f0203150403050d0501170a0602031528050102030c100c1b0b0615090d17040b12 70
    0x19160010407104440041c41c0d840400710684030010a80e50182c8000c1c5007840c0103103026460140d15200b0340e130865010760841981d139034850f00c40c4001e008143d5040c400c5500060020003095241c011206218450088000c0c0100103a0300018055910f0b84ca00190142d005000d96545240070f2910b0a103048048000a1061040140081c001c001880109080d41c601a09980c011815901d0710003480c8010b1100301d82c107100311050a240315180c2400c42d0701503031194507655168841c013540d000641e60141c128861061001c44000595076000a4520321550170842c01aa29160740606100104000000c00d030018909942984044050b41441c00a00740022010105ca511a401213880f07108240c0701d000d060303108101006038aa00d6070b1021400a98600704501c04010342d00800b4902d04540b2800e030381c00351906082046500344520343d04014003140303030000d10b0a90610700168403006140c5019004d60061055412400220740840d0090440160025258403000900740c4403404110390f0720031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 396667733 1250 396666483 396666497
    0x1a0414010c09120f0503130f05030d0507051b13020703021005011e0303110c120313080d050f03090a1406012d030803060a15090806011208032a040f06 66
    0x1110300d00c11111001a103441103402c40020883c1e80b20130206552904060711140020407001040c411700c0700c1e000b0020821452140c0d0314515200405003015021000c0c6403c1c0a420801c21000882c0440c81188500302a0350283c260060140407a620a070503203600000e0300c1c4005890428075800140340a41005501e40500990382c84040c05048295020198110304007160700a100283c01550903900d61507004040b03982075105980000c0083c1c1c081c9161034500c0d00001003442100c003802250b90081d1090704000d04d94500080e100400511400d540000b0015001c00482c0c01400309200049e0380da070700300003500341c000382400b18940c441c1400e00c1074401c00f01070712080c018640090211500303100520040e03c0d40842c0b960f1501d4000c1d62000f00700319403141c18203c0110302c00c0c048460000707000c0364035614899540d0034010510301e4400e060700028184095102c0d080e0006444108590340440011074000003500545050780a4008003441c1181080b408107000ca0307a2245203030ba0078100c90060381c03108 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 396668983 1250 396667733 396667751
    0x70305160512010c170430080f0f01090209010c060c0302300402040b0102010e06040318050d020310090816060b04060b19140c0609060702010c110303010603091a041401 74
    0x240c200c508501360340c0b0109158491030b100c2c80103100c40711540a8000c0c10b135809280410020300c1114116410b40701c49031040030ba0594541c1da0300810081e0312010110030407019080c11240e04100384c0b41445455146034001454001c40e134400d0008680c0c0383d5011000340315440703c248028010750000c68507055202480c048403c00000e6000c1101c45032540091100e069850b1502808054105940814195034945130b40301180f001c104500f911a50203a6078600100381030403114100c944d03943d4000380c4108180107407000076035404201c0c0c1500704c0c0d00c1200001c06501c6840e00784818043c018a400c424248803640030f09020282e002101b50040c03c540c1002417645070710441c172203802a00c3d01d030740e245004a212440040e00550010004951a6180c1c906205e50031001600d418001c0f1046040da400810a0041c411740900400b40b0348055400e00280019112454030340d01d0005124540805488070000b07024010f141c05130010b031810004a8060700c1ca040e0400c00303852000c400002000d5071800000d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 396670233 1250 396668983 396669019
    0xb010e060f030a0c030204050c070b04030f1d18091507030f0c140304060b0303041a0c0d141210170f07092708280f0f05030a0504050703051605 63
    0x78070360f00303030b2010020304039a045070207000003004000c0140d43c1c01d14081290802203100b0207101c0d885580b00b5924035080307409d0004000d0100003e2801034100352600d03001c600c115950b440d540103440301c4e4903034141461b5484406061801243d54208030036100c0c01028021102d40c19040b0306060056080140400c40004404580e481217444280810030700510108002440a402501c50024010122410170303445502138000030b03c4541e50f00031b0089002542400051050148401850b0f4034103010041205272042801c2c60302c0340a0030300409410250000d58400d000703103105c802401011140c52804850002d056a58020000c55911588200c100001c1c1206903806440b0040d0600100c14040250400b04841140e8400d501261442014040c80f03407810400300c00d5200441080c10b84c120045041a80540f01406441400081202c15035104919540180032250441400c58001039079507500e040c01420035840350401480341c01340e103480f640510781c03101d16003040d94030803581866526220612 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 396671483 1250 396670233 396670243
    0x6100e3c010b03070903031214280216030c030212070303061e0302030c060705011d010b0108012c270303090c03011a010c0312090b010303080f040308010b13030b010e060f03 76
    0x15000500104006d01c0040e01c0389103d40e0381d2103260000411603002480311114179840464684000e1000348500c82c00d035102c0e080c0000201007180ca0b0861401341800703441c50052016010107000d02210290407001c05101300486083e104084807882d1f10380fa0a440e004010344203078030074001c0c410419908000c40f44c04240004041300d50060042615040c81818801150084001501c0329580d035401103940383c00c041131820782c41c10340c00000a2541041e400151048034181c21118594078442185240f0010580700f2100b030800b40011600036a84804807004403040542c080c00348000150303c0507030384260010180d07028014500030f5a00c02d0903210207250072603045204001440010005aa11a5000d0714811a0a50081c40c20b003000f40d02d05c0f404003007510300c2c011048400280407001041410741c010754094100300700e841131030700c1c0c0c1c2840c1d02c00411526040c0100c44c41d40310009640400801c9080c0030200a55125001c551150b95030702411110100c111001400f4141c40c4003103000c0d81c0303000700e4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 396672733 1250 396671483 396671491
    0x1202010314101e0504020c03120c04030f1502090402180a0803161e020a12060c03020702130e0c030a0c0e0c0705060711030d060b0d060806100e3c010b03 67
    0x891140d5250a00d0442c00310b142480b80666103140010111300d94172180000e002c41c4400c0c1e0003d598421001d00c0451a1080040c0105a403032000d0006200250003c4001d908080d0428480b070b4000d400898258000d100c0c00382801d81c4144001400842d4809a402d500d100b020126617400c81030f40c2c1c4980e01a221f10078600d0380d1643d01c4d04440000c002a0354000d031000e002c13051042c00080020a0ba0203c2c640365129000115a505034040d24400c0090354040c0c1140ea041318030b030641c1030880c1036001c1160f400c0b41d00d04105c034013511040d81c00c2441d18100108442c0040042c05c40f83c40c50003d04141108a00c0c500132102803268400c0044d01d5100301808450240d81d0010007002e0755903a1030f0044034401c1000b1310229190004000180c0724401c00d004201c00341c807e40240c981da0300140e10f91300003140c5542c0e11030300c01c03a048182040306011981410300d0484080c60031241156540300704150300c10702c0d400e4461045c014120004014503504004140d0300312000c0c9410300d51641c03602c4961445010407a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 396673983 1250 396672733 396672751
    0x610020102040b25120c0b0702030703050a11010f06090605010e10020a02011b0602070b0105041b1d06070501050106020c090708090a0f0311120901020114011406030c131202010314 79
    0x110b0404561854071280080d100c0841d0115848103080d52600d501003200070181001414680905040c8401f80e000b442c5c010380c0600085182590640c0d0180c468011011000284518903001c000c4110080d080740030b00301c002c1c0c00e0401215854482500080c060340c050346000803044081080c05040c081942100000342d9001000038100d03903801115400030b1100f0721031003084064503440c0041d980e8000b51510500c03a040c1c0608960404060000305c4401e682c01034401400d00c080c9116154203c00004520390b01d40700104140c08800001c80d1051140c401d004140b5882c240c00000c4840d804600440d1400f0121142651500d070301c0400c41c1c20354400d030703249141030701304501c90000540a8000e18448134481e04112961506000a082c1000040000840100e40014000000d9070742841081c00c501c20b40918000c10f9414005c44000500246d20607034080e004c0000426005c0d1520000e448600381344110a140700c9071600c050002d140c12010089011900300f51028040340024002c0703074400d030460 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 396675233 1250 396673983 396673987
    0x11180a0e01120f0b0f160203030610110f030d0504050610081c0332060d050615010e19060306050603010608131b080729190504051003050610020102040b 67
    0xd54a803a030502d80c1045580700c0c1494554400030b41a101003e219010b941220041440c2ca60304a0480200000c40074085420802c10443c047d0b81c5d05910b21285030031480c1481003800d00207180d0b4580210880299403d200204d0550181f64851704094030030f600c102c044c0e482584904062410800080c061a0b4403608001019518184040c00040d0740111030b180118084901108804007070402407600050340c10b1030f41c1c0410031041180e6641d40c0129080d038035031131081c40949420f91500d202910081000c2c0303c444200655038811590342c05140c40c02480325416102440750099440c1d139511444010a08002d80001c0da032400c0b10540c2c0c100c440e0b40c0c40e0b2004070b5884507804903c4019014049401010300080040e0045405020300080c10303500c00201000c60400b0f0030360707120303241720010713442100100c200c44009100781e04d041d0354144580d5005003c0200d854101600d2078052500320700c0e00b03c03425520000c0082c0d0f0541003107000321070a841d12803903015200c10481c01d1f0b01c264000c1a03041507003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 396676483 1250 396675233 396675239
    0x1401060503190807081c0903091430011103010810020403030e010305060a03050313030b090d140c07181e06060818010209120102030601110610090f020d11180a0e01 72
    0x380c1d41c0284076140c400c0700c0681c03400e090590700c0c22184041b424115100c42c1d850751400d0400da007010010b0090b0602c0801c1161400c0114001240f000c030380b8401383c640381c0030394442d41401550000d4549030700d480880288061000600b071540300da0800d00c90100144944100da5107026040d200321410b69425950381c0d01c0c01c0321510019006030ad00605019000680c0c5080000801c03070501c003030300c485000210350404003451401c040c5c0c00e00c003000d0102141e940124801c00115030f0060a68807000007000300f1540c0b1142010710b0709080210a41c81140400d00268a8555100c401d5114003036174600500030703001c0d40c112030000d501150000d00030034020560b4200401d206000384028080143e403100005440c000304880890240c000d000001c03c0315030f4010003030101540e040401c15240c0d01c0000e0081a091601c400b901d00a011a4450441075a980c0c044020400d50140c04a50150042c07282c11300041815078a0200c6d55171246e50014041080a000700d0310503d4020340540840d507c088c3c40d0402c41c1d003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 396677733 1250 396676483 396676493
    0xc07030b0603030c0709020a180b07060e0a0602030f221703090a1a010e0f10030f08210a060b13090b030a0510050604060f0305062a07140106050319 65
    0x100c00780c12154584030621961003804403c100e07100203407408800c090303100c038000b16015000c81d4400c030400102c0c400c10301092110a0140080d10f844a41004000c501d064000007131504000621002500544c00002044a449a039215050007404405100369669012800c1440f4001400e0380091410bc0080c0b4104202c840141c003550b00160307045d09946102041c0e03503031510711120305241085d100302c100c030040100035581c080c40f0790300456403080c3c580070745456818200f00260070701000b002d00c00c00c11269024031a02c802a56103400c06180b4509280c1d0450020f0f19110b4022240203200d18201140480c5482c0c0f410280c550544107000d84540700d9080000749406050340d44109a05407050007800001b00c0c200b005400e00003204c01c100040e09080c1070b03007840259100c9410410b1002c0800004000158000030360b540d1103159807030804600e6a0100081f448103100140b2445103120100c1d5200c00d10048000c4242c01700c1301c080080204642c4c444c28151a1046480e25190240344012082c01240c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 396678983 1250 396677733 396677753
    0xa0e090303060909122704020c06010b070305070803152e080a0906060b03090c0a06140714030a020c211c0e060d140a05100b1e07060219050c0703 64
    0x40d10000550303003c1022401307090003a030000d0701003403021450320002c0006e4040c4080b0382101c008040d5001e514011030408415503610040c42103043c087c0c1d0003d001d0041c10300c210155402c6603130103200156030b410045000d00751a4204440c1c1c9100701c1c12000020b0b02a4401c8805075621140303803100c0e07180060298800e5940540c01406841201d4840c01d03d04001900380c4250000703270a03203080854680c00c00c84800da02d80030b84080ca240c09014661014044103401031910300200055540d250390707034000c031b00c0d1030003c6006001c81c000c658030010901080084e00402d46a43c0c1040c10358001180b08800301e00111024207640940201e9040b2203643c502000811001994800d1941480d844541c140e501044143d40120600c5d01c4107a0340e12140000000c062103a907800c004000010b01180c140ba50044001c0c40c01803082044004000507803820603910040440100c00650b00303655255906410a070020758851225225034508441030005a82d004000b41c80c801844a0000d054142c2950740f40d2a0704 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 396680233 1250 396678983 396678991
    0xd060503190c0b0d0f0e0a03080a0606050d0f0e072303151605040305060c030f150906190315051015020307030c020d020306160305010609141003020f0d0203060a0e0903030609 77
    0x21519034013088175034030340e90007007840b0121594010b01c465480da0500404104002d4061141c2c2418144200111a0300509845c2d280364104000145d101e0440e064100616140000e03a40f180034548000a19a5411281c07101c45181c02411172610071070103080640303412800c0741c00120201d13604042400c0d141c840400c00380010403818103500c0d00740c40351501454900111884051190004100104c40c1d40340c0c101c0ea50445c001602500300c1104e0040015545c5000500c024011004072804080b203403240c94200c001180c12414441090b0240b0311030f00050402140d0240da150840c0c8400100ea9022142c50006032050758040e40c01d104d03035650101c83d0340c10b91503001c6e6440f4010088a0000da9000c2c400c0354000c505014541882445181b006026220140d2052044c0030a1a03010080854648402004a84109c4158002e88115030040c0d001340180380314105820004218820907448981c02540a100110340d64029281d0343c040c3e281039200c00712041c01c1c4a41047c070114600342004904039401c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 396681483 1250 396680233 396680257
    0xb040201030b030a0c051008070f0c291b09011205150a06030506030609010e07030b190c0903110907140c0c100302120c03040201080403230d060503190c0b 68
    0x442e1a000040d207842c141d880296130241e09620100091325042c3c4c0c102503601c806051030492481e10b850003410a40641d10184240402504c0325401c00c084480640310f02280d4210425414524a00d40c1300c056408031500501c605c00c500d4201074000e00c038020342c0c1440205949000042c030020590001801300038001004c00c40034101000d0a0380e50300701006001d00b0b82554002210b14160042618186002c2c5c0f10503426454500c040c4c201b0312020070001c041d80d8008280710402c0e290407810100030059264607140da2440c0002002c0c1099008601000310380c001c084d0380b0a003181d8101007049011042d00d43d8000702d4196801c1ca41e00c0c2e0f50b01070180000710318410944203040030010201c2c410410f811100e00020394006160900322030000b0000c0e4200720351056240c11407038207500283c400d010141c805828131488264800c2c03500403a00e0104584e00b9050f039896100d04015035000d011300200d0103000e200b4010340d08082c15041c0742c81c18152115401078400382100d0b1805d00c0d00005a030181c072090714 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 396682733 1250 396681483 396681491
    0xb031305031213020f0409080306011103160c05010f110601180b0a270b060909091f06090c030e070e07030f02071202070b0a02100b18091b0402090901030b04020103 72
    0x1c11a00110b0203403241401c5240d5400680051040286001c0341c0c90f4510303c124544030269003c07500d20030a5950110323003070801c07045040710040c5080c40c0d809040c40b0007001440341030340d139820807024004040c1143d90a0701c4600004402c8142683c50038449040701810307a0203140100038455081c6102c2a07440c012840c00555064010085414090142c00c8034041031400c51032486018212181c403650000c003070300c0c10454180c40c2800210544030302d004203032084c01450300ac00c42c041c01c03e006080b40180d003448817444030015054000c0141241d4420451b4262400200101d000c1c041e010b9545032240c41c030b0140a900d13081403401c3d005640c016082900301540d07403400d800c03100d5040c4000e00119024151190b1980209003000380340061f903800c40809003400380700e103c22864001410207109222403c02003038446071200403038041c5c206807850040d01d115103410300c10002c0c801b060b44050b004240520f126920083e10900003607200c6c407a122a00410048010400b08000d040e6194000784140341c089 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 396683983 1250 396682733 396682747
    0x10b030d0c030c023706090f03110904051f1401090b0d0210111209030c2b05030904091202070503070503030a2a121d060306210f15010b040b03130503 66
    0x1041d26065405440c0500c2d17040d520501890f9005084180148254400e0445050469a650300c011856101207402103413003201003810040c060060800008030024407040c02c5444402c1c10024100114103070302d203a581c18001151695050280b086495030150040703521034903d9090160300d0041212540c1004803801c281c0410803030038004010b20702e80c100f0314145c13105100d50406040c0030186900070b00c03a40a85214080514002038081a8a0210a0b21143d111541e0908605502c545846294010310b424544810010790490040e40c0b1400c0e1350849624a80382d90606580707140034015a50300d54024040c03040c2042c440c11882604469409441c1240016864040d402c0c01307104800700c07001b03402d54813a40c240302d5112680801802c1d100c008015032b80b0148010031540e2002510583c0220381995408103196070306011588070984881c201c82c0000d4140038480d448101100e05030000445110002502c03d42280903903050701c043c004418a5920350321090010fa2156580440e15404180029 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 396685233 1250 396683983 396684049
    0x304020a03110409050f07050102010e061b0a0504030231050f0610170403080906070305010302061b0a0f0501020a0e0f21072328060e12010608010b030d0c030c02 71
    0xc8030101b00c2c6030080c0350080c1000d002a09442200b20f145c41d83d9404501040803180500e501c0108c1c0d0b20076084002e035140d10f0303403100700c802d8071071508060741007a42c0b07900b28494403424080d207100c511318200c080750311101900006800e81d1415640c080015042401164441ca40800480542207044c2003082000d4440180d80b20b0018003100c0950205030110200a01e8480c1440b0b01984010146000c0199604660002e5241c0c010704c0c07001100d038214000c8406003141c00b04401c04020380c1100221141c60701501d00345003c0e40c050f9201d07200182100f504074499043c5064420102d501c0189840404207404484040c44540d009014078144504440050002c840d6074007001e140007440207545517080d407202405014000c100c00b03582000200014600c0203402900715005640702890080c0484028800052000d1800b0400904a5190800000305141d05501500300500c0c2682580d03950740c0ca685054400f895031002c0540400d150b82c0c07102d0300501d4142c54860449580a014132040b00e000d04103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 396686483 1250 396685233 396685243
    0x7020a1514240d0507030f03030e0610030606080307021305070c0209090706030b121e011e09050c0d151e020412020339120d0f03110304020a0311040905 67
    0x110325422070302003080303000105103554182050000750f456410b003a0440d034030780f0350fa4a020310014164400c14046001010302c030b40c2000810208050845845003070070114a11074004512088603250300c0c11700e00140c80940031050310750f0b15400078060290340d505828080d0142c18003d005008010b49160442d0040e0740e0a0000d50240c10424002c1c0f5200742010030107012a02642c040c10322500d20050761081001002810001880c41500c070444441ca01c0e00c0c130f15014180214041184818003816000c030340841d603024100460255045446503100c0e103081c4a5040701d07821016010461905103c65801c0c0d0580110b02808141d1410700300f500e844200e410201d801540210321680f0b4007011820640c0b03810800141c20744100d001d10071008450f00b183e00d60800175a00c007080f00050b2100810311a03914207024070810703000c0d50103864508101200080c1403001c2458803078082490400082c040148180c20341c2c1c80740e94060f02c085d405a0954036400300610042c04000d070f00584454008001980901c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 396687733 1250 396686483 396686491
    0x20a03050d0c051209091503010b030303010602010c080124082a09130b010813080d05070207060f0c030504180207122102090904020108040311010e07030c0e07020a1514 74
    0x10b1205194029072600508040884090f41c841050a0100e5501a940c40020341d400980015140c05c3c0300440c1c4000c00d016010b41c400a950601000c40002009034045d04100040a020781e1528113603a01c030a0007a00c00c4425002000101008400d400d044901803400503800c083c800d42510b05104541941c000130070302940da1010b00c2c19001ca0410b100d800d00401e48003040c81d29050a10860310203a000038020300300200211090303005a0260010b102d200003c036110458a0001400700740b41c0301d44041e43d1403156100300320004081d00c000b031203158840c5110350131a540c959030301c900e010301d0f200312000361602d116420205150b0030015a80002e000403580c0501382e0b5140c441100490890341c0348202c1c04248107211003118010805480c166441d800d100c1e50080e82403d24a0349a256030908481c6030900d64000d8129600e00b2280030810540007441204030b0788521650181e0f10b80702e800110f91480242c6031100503030301c41a09880062280e035600d4044000a01c40060107254542901c6140081a5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 396688983 1250 396687733 396687737
    0x23220c0306060e01020c1302030a0e010207060501030201110a080d02091f09030308011d1b091011060a020705030306090c0f13031e0b0a020d090b0c130609080309040207020a03050d 79
    0x42030402c6107070381100301801c0c0c03200709002402e0400018008904200315403100d03150b54913070000c005003540030168851304686215070001c6449402501d04180106020b010070b03400314035030898000c0360243c009540001968441401802c080e1000d404001039041641ca01e42c0c0140901100c580d0002810f40110403d0741c0c2c1d40d9600308a0b451400c001e008140107800c4030201c070900403c2c906442030a0442a501300a40e07090345002103003000c03480300c0d142c0034445072580d008500140007201c440d841010341038540e800d0030a556503a1504000b9104031712940c0c900809030b4000344001601407030030f00b0072a680400340015040c40c0040d0010f4003000799004480d1641d80d103880f00d01c02c3c0123000542d4921032404105091200c0101240c0d00d50030300c9000020004c4100c181c000510b00c030012807a8000001c030550046030201d50b4140740e002408644c1020b20301218504402100080c0f00c0d124481c904200c41450000d103250490410078000a940000c509980007001c8001c00070004000704406e0829240503 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 396690233 1250 396688983 396688991
    0x2030f0304060b151c020c03040308130506120411180f060109090e030a080603240a1e1d07051c21020a0201170609070e030a0b010308090a23220c03 65
    0x417404002c0700d00382202c03c3c0320518414800036046400000807a4140c941017000c05484585110020307070703407c1440e0011500314002045240b0440303140c1c0301690141c1d10500c0792401e00c1c0040c20a12665405030000142c1c2589008082a00303000c4040d40150811410f15005070310301c3d12296040140d46c4003042082c096400002d00d543c40d0f90303000c1203841d0031400c1240601040210394120032011121120007610404d030f404085011044641d01c0b070200704003034003440f22003e03407051014001456440100d0726a82000e03c007502c2c17002c00c04943c0f4400d8410042100c1c0410640e90000110089415811035107005008e560f10032600040c1a02850f440c03465004188841581c80010008201c803400703d40c440c0311400500c076440d030310a04259440342c110300e84480d034110f13002d00107445c0107160340000d8000313540c04002006102105008104800c001da444500d40c51341e0340443c810901c030300d0480c400540107400c0c481c401450b0070510402da07400e01150056400103001c1c1c92200300c84034003a030714020139a6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 396691483 1250 396690233 396690247
    0x12020307120203300a0e070801092f091911040906051002030304241404050105060405060604120830010f0609060509190f03030c051c02030f0304060b15 67
    0x20003080424000e0a4090b1031444d11030700d00c5050403003600944641a0a6100d15024015285c10040030008007680d40003481008070600b8640c0c09100b2074143d0100200e21164001c02c59140502e400010410240110081e5601d040d020200303038035900c4030307201000d46840619104d4011480079001030601d5000000e400b03840c2c00104a500036202422000790b400a0041102240c8400018001c6a210014801d820b007040d0035140c0091400d4240c03c141d602c02c200600040c004154055072083d842643c040000d078952000b00b00c1117025a100780c0c40300d1404a00003200040c190f80c0600060040080d96480740780c500008181c0307541c0500340b1513010f440758800402000380b0310f040880052085061070503009040000041c2103104201095000d0680b1400c031b0000d0ba101a088940142420308000419981780c0c9401800200c000e0019611840390b40306446000d0703d0040c80404c0c03001c45400451030a50303194540c01603900000c00c190b03540340c2d442284209a0310b0709c0c1006448268080c8050b940c42d05 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 396692733 1250 396691483 396691507
    0x1106040e06030d0e1008091005010603020306092211040b03030406120f0b0a140d06020408010c020f03040e010302091e0c03041202070501020d120b0d110909010c0c12020307120203 79
    0x400e1901c8401042010303464281580c0756017180c545802d0f018a080c000381e654018460786400350600c074660801e4542000000c03d070358940d0145011340400c44a0038180d032162030348810b4004900012043d4034100035040b800042c26100402c0c0c0400b0061320102d20006017400103801c41c0c001c1d80c0070f20040344489070305545d0741203940708008810001807001c000b039210003030104040c164a4001d04400203100100306100d035a499072000310107903001034150b690b5034950154501a280d22884603001d031044d000381c90500c900210540f0140c40c4940380700000c50b841c6800b00a40d1280141104066102d00e010701c1d0a0100c21070103481c40340603c07200040d5a428a490904040d020f000107507002c40d0003110080c801c80c0e901280582c8041980d02c0c180e400c144111652200401403031040b40d82c4400b11500103001c02003600410104480104c0c1d04034000e0b40c8060a4600341c8070107820890000b40340c01d0580c070015052503191001a03c580c41160305150040d0764aa8458070003011000140e1700c08201c01001030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 396693983 1250 396692733 396692743
    0x706120f1407020d0503190e010902030105101d04051b0a180903090b030708010e071106040c05030723150d0203070903060606020d05070b041403121e0402010215041106040e0603 78
    0x40c800d10301705146250241c2c1b0100403000d50141900c00030346400b440f0b5055542500041c131502e070020020041401c142c04103401c15280b52040d90905482583d010004c2405445118411a04940680b40c980702164030f400420800c039848581c882c041040104c4e0702c9980e00a14910320302d240400184c0f0b40c1040c1405090121582d101c1400400e003001040b203110b0b8084040d50444480c0030503011301e40c44004043d1100c015400e00c5a80740e229840410040c4041002004c00711201076003510b16143d124010707491072250410080c602c1c0e21203000d07281654202991602d6411010224231170034850408030380d40581e4030036120100090b0348140240103106c110b203c3c0c10010920b5000034a100c092864000d030013405070000290002d00341100040600c091184240006403200c0d0548bc1d8503542c031040c246680b04165094110400310381001d108440c8042083c9018680503001020f01c20361b00c0b40c00c02c01418005100f2902000807015245c641d4503150064009015001d42c0501d10f845c101c3e0601d443c1c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 396695233 1250 396693983 396694003
    0x403050d0e10020c04110d151502010501051809070b0301270e0d0e0d0204050c0a020f0105070c120e1011010506042d060317030a0b03060106020706120f140702 70
    0xc2c000b410340c40001c640c00040c000d410744401c4d2000b1640308007109483c5424000c0030281b80b803050400c0403a801d030f1210304480c84242c0e110164a48020311400004900305c0d9024040c044c0c1001700b001107600c0c0b00300390100b81039006402d182142c510ba925041010343c03c2e0420b9100e0003003103600034480c20328060582c00d6140c40311038041080284541c410151552107a44035002d406005079a0b10380904c9455a6002204081d000391051145040040d140e5605030300c040350f0341c00140540c0076100e00c4013506028050059010381d50340c0000800c0c41d140c00e80c024200440040034440c0c2071000c12030503210141500f0b0082c1083d01c4044000342c46d031005a00b510310003040140700340d1400c1c0c4040481100e04c45d0b1100600ca0f06076002001e160b0421035140208413607000940025006801d40400700f0281008520039003046409101c81042039003410741c0c59100303000755809a0017504040c4107413446107050411840781c0140c0454881f5034000d07050103d038030001a41084007007080c104480150100800641 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 396696483 1250 396695233 396695239
    0x3100b03040519060522121d03120405120105070f031a03060403050901170609162102030a110a0f0806010201090c150e0604030809040b180907031103011814120403050d0e 75
    0x1d0325040e036031f8066a81344c2c02030400700b0311003910300100c602842e28001081021b005800ca564612017041c0c0c0d02d110b500075101d010f125901c421180d040019040c010766000394482d40f0707422040b000440c01a80500410680c2d1440040001e0203811650307001c0011900850280e01c2d01a540d078044000144040c0072000c410031061995800e008183d100c01610aa00200c044401001003618000448072000e200391031a494400401c4400310011050f8021409119040b04c200000c000080803136059004004119010500e60440c50051034083d003013040e40b1240502c0000b8803045140c0d501041513015400400014039000000c4c044075030400a00d98900d802201c105007030038510b5440800c1441105492405951110b4405070300352524690060282c00403000b511240c9000d83c5501d9540c1a644170940d96600444c000040300d0406200b03c490728101300b01c0c801040c250685030107040c400d5038003064096105a009441404801070090009503104070050310040e2a8044010320038100c125030a48 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 396697733 1250 396696483 396696541
    0xc0d0f0e0d02280f080304060f03060b07030e030c031009020f09010f060302071a131110093b070e0109151101090203030d0903030f0203100b030405190605 68
    0x3016a4968008044034240c03c00b4008000d0b07055100140c490b030303090740041020030b0140804500c210380400940159981d9135141c040346500800103c040d10003922603041c21032420890394000c20b10544400c0001080541141ca10840400c0400e14011a0542c6103101d25a07640025085140042c1848000101140e801c502941007100c4a0608401072140605051f80080c110040120b8040300103180504403000e00300380d2034410f4885100380f40001d130031100c01c410300d043c5000c1031800d00b0b129040d08000d07076108590581040c0315502c004402d041048003080b1000103a000d580d05600c251060382501440e005064108814090505000f0180050601c400c1c1d04040c814056181050f41d00f910292806154400140300d59900500d602c000294140c04001408480c03030300190440a600e9100347e608100180d0b80d02c10f801d00303d01041d2070948402c2c0043c2401c10414200501440d001409a000d4aa814070207100003144a020140100c0303503252603000700f06040722000700f40d60081004a035402 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 396698983 1250 396697733 396697759
    0xf0603060303090105070515010b091002070b0a120e061e0f0405060a0209180702031801090b070822080705090a020307020705011b0c17010b03030f09040b0103020c0d0f0e 75
    0xb500e0380260075039036040180c0410000c050140410100d0340c1203148140341052543c542c00303030304174075070001210385d025101c0300300c210800c0342c03000515030104d4151004060600c00c41600480b0400103200e9000d100135203800389441411810f10000b1701414007402e03500400c2d0034540c404131600e440100b207004803481032010800404ca01140d4075034000ea800307070011386d501c0b100c10010b00300c0001d40024590860300b5200300b00b21150004010071504122000c40c002c550300c0308004507410742c194042d611441c0d0052103a440002c46400180c0030408400080b00403c60503400c0706050442503500c83e2280c2d030300440c001c001c5400d20284041c2c0006c6c24103000e6207035262601001e50b81c0c120900c0344904001d08a4149150b82100541103003160b0f60048100c40b01507980d241707a40d4080f0900c240c841c510b520700b0713207040c00342d00c0e0010854980c800a0320a50b407c11180700104402000b540044506040d02004404441070052000e03040820b01900c0e030010940300c00000401300800700c140d1600900da00d80d40e030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 396700233 1250 396698983 396698989
    0x120d24031a0f04110a0b120a0612050c13060b030411150f090904030201061502010905061015030c051e03091204230f0d050f060705120f04020d02031b0f060306 70
    0xb8660064018420702c0c0184000408034030740c4180e552250500b2440481d000000c08500303400c550042041601c1840896112180c0742c800030300c00d40700100540d005490600040c1040c2c0303541c40c0341014004001803080c3d951401105241d0080718200c610707149800c1c0d203140a20704440003003081c41c0841e04490600c40b40d14120066031044c0040140b0130281e0000040c1010310035000280600341c007401d080b8a00c91401c5010340a000d10310011680e1340543d00000d450103050040f208215100c0f106103141c015040c61094005240b07680034a0f0070031000300070007035512107142c481c000c8100c0401400c5949141c0402114142039050f50038540f03643c1d040104200364006622501440d9543e640700c0604110505c1c0024411380b610050346402560510740b880078010041000c001310900001034a172290346d481c804035840d2141c4400e5003100300740c0502049031901c02e20513086e801440504030a100aaa070340000c1c1c5030504100e00030082d012400d498400a042450507103100c1402030714038034103501307040d400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 396701483 1250 396700233 396700261
    0xe041404030f11070f180605060a0302130504020c0c0105070c0f2d03051b030109020a030803190203070804030c0311011113091506030504080d1505011709120d24031a 73
    0x5203030362229141c1c12141616541e1f800030004000050145039200c10070900600a900600d000600c0c224201c20001010708040c02201d103c011100054a008468200107442942100780d081e900ca015034400441c1c541d0307401d01140c0c00340103440c1c400d9421119007001222074080340307000030b005541c04040400014400089490107071040186110007644100c000c00e004082c82e4901a610099182c40003046c481309100079070081e0b6100c010302e8900f2500f02d045c60b06a12007585d282001520000028010902c50004846242d1192900c400c500765560005401d4507400716103a000041c0020300320403a00015510034004043c0c0f4001400603050003244140c034201e040c401e581c01c1c113449100103803c10840404860500007288030410804104041c594200c074940e0046038003180600c0100b13141a84241c140c1072003501104000c020000c0c0f100c8440d40290030242c0d0b6000a0b035110840130508090701c0003072108800c0c5207448500c042c1c0c51400c3c11542c0c92510f455004000120105000e08044d005c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 396702733 1250 396701483 396701489
    0x23160501170a020f090319020102011512110604090c03051005121203070216030b09060709050d11130204080f1606140307050d06090c1107080a030e041404030f11070f 73
    0x300688810a1041e0080284175182c241d590500604040090380010000003c1c81c082c000c0c1d0003004410000d0290170041d141c1c3c2e0003628040021001b04400040c0d00c040d00c402911030181105040c03940d1514250306440e1881c44440110b070f11001084004404c00c0b8206006010072241011304241840704107489142c0400203803844040000080e50b03d5000f0800c0c001d91504240112802656904110b4442c43d0b00b034811102c5d50190b0b1010a10380d510031400382090340c038020024844013929544103043c21800c1020307a5000807242c1801c00d4408164030192005107a00c4000d042e000c19070500c5107080013200341440120010303401c01406007542c44000c80754a441c1000e10582d5948511406441d10700940c0c141100c410308005000c155080b85130000c444140d12515032415002a8100c03290b100c2ea0180107041065008000e0790020a12952040b809040081e200150458406030035103241c1004030380542c04600400b164041c3c0c2d551100c0030074404103140c000342400f80c0c14004000ca100c1c1e4284 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 396703983 1250 396702733 396702751
    0x21c060507020601141c080408031309020a17100e18190803010e04050a080a1e0c1e150204060309031103210402010323100b030c070b042316050117 65
    0x80d030006d517840554001c040660400c24141d2141d9850600036942d07031003031081c55203205246000084400d03850094800101240d101c0c242222903821800265401c0109206040202000e00040303400d207002403039018100c011140784080d061480d20500d001d5501c40c100400580840308680481d071800e059a055035400c901d92901612681003144c94021501c00182842c0300000d1449000c44d08803250400c1d611904204080416060710300307a41620b456400a407002900013003480d0f041a0120b04d00c8030403886560025426600601218101c1e0015080b410200340e44038940c0c02411f41204180c21720827940790041d46000c550151215034081018070281c0030025620114046a0080d0010728181c201000c00e811451044d00d041c1680941c140c1e030414040c62a43c0e804103000c1620001c89100c1c032000104c1500d0156642c0c0c41100c03a090040080d1112150044e003010001300000030540e03e400b404006001001f00108035801381c50309688007a043c801500034405034103050320300e5182d0000b001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 396705233 1250 396703983 396703999
    0xc010c08060d0209270c01090b09090a0203070311040807091103010311010507060207020d0f11040e0312150319031803020918010e070602030c010509060f040f0f021c06050702060114 80
    0x140220080c0e8003c0c842214601d85501e040900e2172200041116219101340d8904030869a12940015948600d40c140c9801c81d0403000055800e41082d0000c5411000c1890000340701781000e01a280700f904683c00260003900110401c1003001418002c0c080294108001c652075540b441c0c0d42c810011020100d824180034010416605112103035060b42d118640103000b40300448400d181003010f19140180c11100c1e803030301607801c0c2200d04090ac901036207410f0110003545041000140e1603624a0010441c50880104540040c2d0729181071000403941e0705451400c0b5008415481c000d00170504010300c0142c0c60034645802c101590310f180303009801c552a400310003140c144c00d582003409044480040d10041c461103c00013001c5500000074008404400c008105a031103001c041505c504e8152401c0c0144105034000c01c1c007003400c3c00480c1490340d104071095140072840b41e02051002d407644480f05e8068100e086242c041c0b104501800b82c3c0980d01c2c2c805016958100000d46803002c3d503181041d8000d06031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 396706483 1250 396705233 396705241
    0x612100f05100315030606121703092a030a05070e06030a12030209151b0c030102040f0302220501060c050c010918110706060905270a0201030f0b10050c010c08060d0209 74
    0x4004968061a0030000501c0301ca034075078a0404040600c01d02c1156401400416840c2c2c010524051ba805250740c40d01410310b10300441c010b0b9020160b044260b50810310a4001d4022558dc208040c040b16485000500001454000d642c104420000c0001b4040d4004218a00000325140791a8458039454200183c4a00383d0001048039501c00504241300000c0002e40070004c214442c500000304e804000840e400009607006041c241e018078442e01c030351a40d40780000c0c001841d215a07554051021000390f031844e0b80c000302c6443e05070780e005e034801c0300881c400c3c003019010b1000510540200c07034428208131424515040c818100ca0060109058013a0356a60034400313411a0310341221550383e040a030911490762101d81c5c940080005a032a0440103d4110190107040480b134005042025031134044d1000c07141e1500158080c2c800c010354041d9007603948180107600e0f90707070704074074441840c56985081d122903801c0340e52421170320b403d50100c040c020844104440c6603984075043c01c00903815151030015840d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 396707733 1250 396706483 396706511
    0xe130c051309262704241a03060d03111912050a0f0e03120c010c030e0a03050a080c12040b060111010e03160809061209010507090e040f110612100f051003 68
    0x4a0f646401d61086c01c00694468281c04200b9100140d4408128100815030b200c0124a522192078015040308405200103139a0b843c142c801581818041d08182840000c0002218104407007505001d108e04043c0c1c51080034480307101c403450060b856500b011071416102d04009002118604d050f4000c200038046000445c0e14180a1000d409812544140c0c844981c51041400f801071512140006807502d0704488070010009100c09506405480d207910701b0700d00d14021210010000e0102c08941410405580643c41144186108034010304949001e410050300040040303240f4004684181c2c14100418601c810120403240b001c280305038041d01c52542403a14200e0307030151003e05980300102084440f61041000c5c0b03014466500712008110320342d41c02c0c2003912004002c0c061605031000c900005000200d52844d9a4040c9000ea50304100d00050b900000d500c90348417194850700e040e43d22040c000107001c03000c44d00c0003900a0380203441000e400d0030082129151026006010940c07159000d0381220 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 396708983 1250 396707733 396707797
    0x1d0402150f04091d0a021e0a051c0302010b0406063213140a0e010504020705070503060c0d14070212030403030623010f03060e130c05130926 62
    0x70894080c1d69110ba40e07035542d9038003c046107010714000030282140f00751403036000301d843d05c030044d8001c0204040503070682c03100700320250b0074125507000700320040c02080a81d286c252a003601c10000001c00484070305883e0003800e542d9501c002a02850a200b81807103030b0354100c4460b914012615030405500411302410f4070401280d4100d9216501000909100d0020b54441c2c42040d85c2c54156908480c5581e00140140c22415105400c10102280014003c901e040c0c1c0040203040d00500031a4601502e030000207042c01420f45100a10b6400024004104001806a40d40842c1d0b0111032804914040d08080c0d22002140b402a0014800000141c10140294807800c0070f030414900d0320100d1010142c443c0e0441113100c52541c0420500a10050b41d94070900558044d03030110f410f100e5040d1200703c0f041c001e0b10079110f42192a040407103400300d00b076218601101011288010081403444442c24100c8404109541c2d8049845446e250207001e204880111760310441071300c5100d91500071003002d0401079 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 396710233 1250 396708983 396708997
    0x60c09031e11040c171b0d1a040e0601090f020c0d0804020a0e010f0e091f1a1504030204200a0806010309140a120c020102070302090709030b130506011d040215 70
    0x41072400d1805a826907000c42024406601700320084e146441d03034890817030742000c0ca100c5c024010340c0401200340203c04580043c04409120300207101030441e807200042c00e90300c07103040400e0668044e000420510a0602070b2030110300480404524200d000c0d68002d440312150340340303002800740f1000401c0071034807211031443c0200014100450385584641c40d18100d40707150300c0340c03000800311a40070072201305011440080b0245103124003003aa03001605002c02400030315180d0000c1416001000a603600d411070100e0184044985050380c40341184104030131207100e006008443d2000075905012800c0ca81c089810220302410103900c0396079503000403000340c103a240340244080102c1104000c2030400054030580c00d44500349840044000160469019504400103401a44241c60400140c01d040c08201d410070114074151610645a8031800c00300417040d034600519510301c484560500c041804040d02518034400e281450a6603034148500d4482c0140c400ba1041c04040039a400c0a401c8104442031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 396711483 1250 396710233 396710239
    0xc0807140607021b060405100c150c030b10050403021e040b100e100e061b030f0304050f01180803041e020301050c090a0f1a0c012403060c09031e11 65
    0x340b402d000025200c0d040103210f0f64144c2142d12480329540761a2095506646000c3c02c1034078045803004040301e00e402e5080081e1540d20541803240003040c2d080c040c1d20200050f90302c0c04100c240c1401c0520508500e4203108108102c8144410310060b84c80c1c10f0b807125040140c3e80b01d540f00030a4034001a004205030209150300141f821403c00101da04043c40010f410411648a5001443c402080d643d501e502d00d24640c0c803440c1017044424014125640d00310038405a41202d00303050300c07a03e61031031030303130051310103031010b030322003120991803180900480f0392160203c101c1d03a030054015503410f2554040074000400340071018801c1c0c140780000d959920a840e40080080c000c5003400901d0911503030000c54010700410b81c0b15808071f10100700ca00361104480d203d441d03200f501c4020001c4110507800035103500c130b040c0d502c4010280712854140180e40c2d45107009501d1b841c0e002e10307510f8034004845110742020244498810708001107080341000907404814940060000401444c05c0c20744a890b820646078 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 396712733 1250 396711483 396711493
    0x105030c040b1818040503030a15030501050705040e011a0306010e0f03060f06030f0a082d0f03180105040c05040513171206180604110d050411010306090c0c080714 72
    0x4143c155100301180804021344050040001041854107040f00444000c0c0155208202080c100e0400c2e921000c80165001e8800450303c1c1c03640d0303c0e9425684151070f90400100e0110b4144010a040c000343c2c2c0c0181040803182c4201d681c407a40c0040c89000c01081c02d0305204a8940c16490303a2180c80740c08040c2d400046c2a14802e2411601d882044203080d501c0c0c500a02c207180b03c40303400c0e1800060705e0385540c0c1c100030304509208640c00f42859a001e1501c40c9840c40059070243c4090f00c0d00036000e400d001c0b101c03601e644c1c0c583c0340c003a0303681d134030384910001d1114141e0416090001055500884a017542c20650740412240d40c0d400c1d415004100b070103001402000d0300c1906050340c0906401801d0181008180644203448141c200a52140500546551f00260b00003040180c6469801079423a20039406000d41000080b161000403103c0c221803e403440c50702d5203000d4410b5a490b218070750241007086000c10401c11600780051042e8640710300284420400103560040c40401546d81c5826010302080718 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 396713983 1250 396712733 396712747
    0x51309061d07171b1b010b0d0c050609120303130b0f070e04050703020f040303020c18070504090218040f020a0806060a02070e090106150909050a0207202806020601090c0e0105030c040b 81
    0x1e6042050f0f85d508203015481c0184000840c13600c0d003114100c2d070341c00c2920305054500304801c201c45540305441c5654413661803d80301c1c0c99480e00740f02440c4910080901e40c40c96254900303014074403040041013041d02c2072001081141d0b46800580f01010320b02e003036600240b2503490040a4000b8401c240041c0008107010800000301a4009200c0c80c41e4841a1800340f820904441540b29122098820401140e000d01080c481c070122a8058000b40f0303428001207907200b6600e03000c1001c035400800d050720015000a10003040e2034004160719000403003034400c649800090700c2c1c003d480391854007555400c03c5001e4041080c0c10025003250340030342805080c40e040c1200c0700e40041c0c40fa0f005849040c0025040000081210341140b080d0f81d000d903003240000d110207458442440014a513a580b16a00841c0c1100d00e40440102100400f00858a082c102503142d0074000017130f142c11016807050f52102c0c00c0c841307803191640c0e100070281c5108a0070308009807680c441038107075912070150b6004141a90408034106c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 396715233 1250 396713983 396714007
    0x6040b0a1514030f04020d150609020d0c0908031c0b1324050d030c060914010c030f0506030a030e0105070f0b0f0c0a0816051309061d07171b 62
    0x146030041c80d202e501e18401d0041e00b003261404101c4007501071036240300001d405410011140006e0b079211301c4404864240907000002103d843e40c009901843d80415491039100301c83c46084480052410080d500629080070326650b8428400c0c1340310910f10449030308a031840b041e0800e00b09250001c0c0520415241c07848080020704003040703640c09001e00e40313411103d408040c008031419135402404c1314811059549090b150501d5640049030708980d41c40300800418940340902e520810900000700b9103414610380141525040301a20300e54034508018000c1a0780c0000e81d01060507450b00303150a41c000034400590342402800301c0980010100b100401c10050180d07000d5104180440e01c00c1c1d030607110030125582501403180c00740c001c20a19404108139211100300d9040c1c41c401868820300c0d01c4500c560143c0a00a294054540e464803400c080c000000b160708409440425010300e05a1841c0120b0028100225400c100f22007024410100d11007101111454000c04030001400313940e18065002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 396716483 1250 396715233 396715259
    0x70c06140f070807110d0b0106031a1c0c050f06041208090303070b09011103070c0b0a0f0603060219031e09021f02060603160b0f0d0b031c0e03120a0806040b0a 70
    0x4200d545078000d02c044101c501c2c0c035252000c401078001f441c0103043c2c1c1c09c01d0740940090803003007280040d50484040c1c201c03056413090110506c034660003001c400040d050340b030710300c08904054100d06c0c07040040c00d60141d91034541200b69000c0b80c3c10f0b80c4280c401e03142242800c0b000313481904881505800001400b005008411003000e0042d01d2440007003000701c10041901ea6a40016903100001511406110000c500f40c0404103030440801d103000180f403035141003010100c3d04554001c541060f00450083e0000d5904242d62002e542c140c101484082c0d507045612404a4114a82e07141c8107a85454250a5450380c10099402c0c00c030000241004207000c1e900a9a140000c49910f4843c1c8a110740c8510040c0e100c0a5a00c11604030804036400c104000e007a03650140c04c8100100d02e810769481200d0100d55040101144042c0c0080c0204075101450314010040c504000c076140c001e40c0946c441030080c807240380490795541154642900b640d1a0480050040c2c01c510300050350000091501241c2da961800c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 396717733 1250 396716483 396716497
    0x90b010e0115081b07170a0c050c0a0501020a0206030403030b1503010905060d080a0c0318030819020a050a080703110a06050108010b09090a03050730030605010203070c06140f0708 79
    0x141d0700c0300e8110480b00803100302c1c07802c54581080c406490802002002c010b07020300311181c8a442c0b008001c00290b0007020542e04003001c90800a0000d040f001c040c400c040c040c0296030710082da003041145040c480040d56406c14458028000d4000200140030305110b0b0740183d0b12018000c1044090804801c0741380d00d29003081c080d155101c0e141030013007442c0f45810b40e001c540b00c1d640018500e007050020391058a41641702281581032162220016810425041006002d14428203119460781080048060410030b1030f03005400750350040c0134010104800040c18180c440e0b2001e800703a81c4484925007121010000c03003040c1e1140c4200c020303071000c1104540143c0c1c180d0302c0c4240200103400d040b000b0005240070940d03103401c160b0420181d06000c644070707400900806003d001d02c80c2d2500400740c118883c0198014113900e484200b80d0750308400700c1d8107002d00002008244002d505282d170b9615041402000c3d48600024407601e03140a002c8900310000340d5804264004500c0e4881036581025406540901 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 396718983 1250 396717733 396717749
    0x52802090105010c110411091804030818030304151d0d030b010926010b06030a0507080604020304110f01020c030a080913180b270c09070509060a030f090b010e01 71
    0x103030011440c1e5211300001510103410a022003801d42c1c0700c00500000303100c020000c0d800300204020030079a41d11803140c2050410f20100060307146280500b4020031180b0040c040b10b00915018074050310b8080700006803500b007500600e007003a070142c02101c40f100411325404c190028205048110203104400708902c0300201c0d140c3c0b024804401084011110301c5400d0045440455a0303040100c01d03441318040e406920261600001a840796901c0003034099042241c2c03100603da11041048601540003482580182c01540e00794214281599500c4560f26401c5407240030301d40c9203d81010f903a01c01c202044511034043c081c0e6a00149900b0401c2c09a4013580d8030600803081141c01000205142c41480340c1d200c2e115130003090101e4035176030721b2044900c050120042c621406422020700c0c5400c150781503200251000910f1003905500500060316001003545007400010304c17200c0072540710042102c02410541c0303000601d400e5602d400b072000f404801005030a40d003c010010808420030f00038035060310340c06 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 396720233 1250 396718983 396718999
    0x20703030c03020a0c030503190912020d0309030e12100e2b020c0d080721080f01030c0618080712170901022802030d05091c080313052802 61
    0x5400b80d040c0d103e0440c2c041c0009201881940100c0e2184028640126420340a280300402500001c0c082e2010801c0a84103a07d140b4800000240c0402c0a29407840b19400c050140c00219180500100741a01c0310034051f01440403a60207032034040c440a024081d011a0802083e525089081d0780c5074031601580340c2494880140e83c01c2c45001e07510400100000350700600d80c0010301e50600010038a4203004032030300380083c410000013034100300101403039039400c1030340e08442d501d6a60020324102c00034164450440d4130b00c0040c404a4a0745140e0003c1d5007060a085c0c449100000c00c0e00090820340e803100c98107018000c0b0110356141944028070040340141e1035091407039841c4074002000c0c03140c0c082160142c1c0c0f00300380c0e1008084458491107244000c1030798254100c00180c0200e801c222003c074401c0c2c00620006070103000c502d4031081050b003901d91590b400e1f101c3d00c259a18076020344409007495440d40019100b102c1000000c00c0440580c980c480d4101e162070f42c015614904001503d007049200d80d0355 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 396721483 1250 396720233 396720251
    0x601021c030b03150c1b10020a08070e0607150c02030c030c0703030801050306070e040504031b060b011101090c030f0206250201200316020102100903080a0f090302100225050102070303 81
    0x61580580251607152502d0720304541c40d8030383d45d0406c3d004d0610102d00d0250080802140410b4400781c000e98070b02c0c0d1101c003524a0082002060b03070500060181c401d000c21702c100c0e0082a8552035100c800800d00398005141c00d9100d13030592450141c20440c002c107101c0012130195820011900d02c04482c0700c0e8880401c2a41c80d80c0170583c0b42c0340103c803540d002400300d0b512035100b40f41940100c0c3c1c00a009041400340060034071070640c4208010700c000c1d0340c3e090b203481d12a5500e580c060b441c80c040c440401d0080103042e03525030b11103a40f001180700c06002c142000285405541e9a0401c81d403c514840910038001840182046d42c3c82c03a9620040c0c3c04913003038125902c140e043d008007c1d10180c2039080510f281000710105c102d032400311524161704502c04d030f81a13046466018460400018040d848036006031070700d0403050054032900c2520696403400d003100c000010340c0000741003102c407005501c00b580f903003280c40d100e00d094501c18035817400c01410b204840742480011343c002c0c82210300a550502c40c040b1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 396722733 1250 396721483 396721513
    0x825051c020d0606030b031c230c061833040f120c350f1e04030c03170c010c0e01021006030525050d0c06090f05090109050601021c030b03 61
    0x844403d0341c0d407d600010300c2198100d04145420055904e2800c00d10f09580344500070b10740c4a42c3c200d542e079400f00310000d17203820b007184100300351a400100340c034282c060028803109280c1c079004205039209035001c1c110a0920004e40014400041945a443c800c40314580343c201603070450020802a903c0701080e0711040070503032107602070702d22040e0402d1030180c541c8000491404070000350025059099441410b00218100c14402465040340c0640c906440c0c03a80c00040c250340d1402044c040c500b0401c204802c100003041703404441d007102e070042101140c0f003150071140402031141c1d8082214552800b03000e80d080c0d5421001c0d20f2170f42c1d0001e0b42280c43c861400c482d080100c80705404003801c00da009040155004000c05a06540d20b070501d0b8002c0901c1e0390750790205240442c90141120310507052041030000561056003003006251904600a10302e1070305020545268041c056061555298400100c60780d0081002101c24950000c07605284460050020002c00d04507003d0b901c0ba000300c00d24002004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 396723983 1250 396722733 396722741
    0x51c0f2d09031e02101b060e0d120204080c01050318010509031201050d03080402040203060409020a080705031c0801031b050603100e0702030f2a0a081206010825051c020d060603 78
    0x13039014111501d8051104d2050310351032210140c0e01203803520606164005003480c0101040004034170000c00c500001d40b44090281d24451680c00036462050004201d10000000c00d1903900d6420700380942da986a901d0f442c1d0386445c60301121000743d800d02d010b10210f003100100408805880b40f10304191641c0318810030400306040741c0e019000a0300000854090f281c20307801140c0009004100141c2000c40707502284407904030358030035079090700000e81c10000c0b07003030520209140312600f0700720005001100501405004040c000030b001d50300441031000f2071050802151014020040c049074680c0b4048004a110401e43d0040203001458980825901070000095440402011120504200701c45141514a1200a4041215a01b00d200410700309809100c83c0310840d0040c3e008580d6149502d40070000c04038090b103094104400d680422101d08029182c800389010381400500702110240400c441c94018440e0800d05002c4040b051040c00b142e644c000c10104450103814400075541d400b0a40c00c035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 396725233 1250 396723983 396724043
    0x8070305130b190f031d070302030d050313120201020d060e0702010b090603070e1e0c0d0e0d080a051806151201020f0910050c011503051c0f2d0903 65
    0x10080380c06070002858041c2d00303d611341c030700540780000740a00035104070f440c1c01921807001e15007070700160014000d43c14107110022441c6142d04055280d4205400c034014103e455100c0640b155218940d0741c103003e4800e40480d8244408440c05020b1142c0740c11101c03901c513070280c6091000d503207005040794840c1071a901045c4038280c0200600551480c007840d020b005280180302c41001d40c00c09003998240001c403a00da0b40140c00a140700c6449003286002401128000003070107140764003c01242c01d03601e034003560b810792103a03007000040b400c0d440f8218032841460211610303409601030141041079000c0010914042840c0449842805501e07031a40b00d400c07440340d0360f0403010404080040c550a1300300034001c88403100c83c51610615080310301207103908403411415055484800c4070410000d0000802c82007030142a4100480701c030484503e00a04460210000b05091126100034401d81c0d07026080485050780705644405044d01c180d1100800490140c041221110052250014009410314a4201c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 396726483 1250 396725233 396725257
    0x7110c030109150f02040306090f0c1a0405010f02240a200a1803050102130e09150646060903050309010318080c160501050c1c090308070305130b 64
    0x60650040c84030b0152801d080c141d100c0b1360302008000f0024416204400c6110f00440000d04c00300b220b407030121000582d40d0720480e0460385110403000d04580c5070040700c040325400d0801002140d441c541c140e00304984120707903010408a4804041408030b075066204d2154076101c13810001d21109410700c10300c0c841c4d41c1075a466012000d1040c5a0607074042c80b034111483c1135000c2c0d004ca04503540c4d560130303007642c1c84031056140c1801480c40800460311611400c42c0c01104a80180c020550094140e60103520300600c410302c00c0001e2010b084820817102c021183c488841408a9a5081c4613848120704d10200d222400851410400026040344520040c00581c1c0d4004007031443c0001040045000c1c0904000c415910302d50042c0340c0740003448400043c02d141003018043c0210702400000d00148245561200381031150401004001038404100c203408040301c00180904204020811a205100c0e500000d0040750000394280505420401a114404400369044c54990326030010404d64003440c000e6000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 396727733 1250 396726483 396726503
    0x301020703020c060f04150f0f0813240212060f03120406080a1404111e010905120a020414040b01052202160503130501030f0b1c031101020307110c030109 68
    0x7244c03402100825410f180b5040c401e050903102d035511100c0b802800c6071a400310340d0048242c008640c0180103c1180e24050402d45000c0c035000c1c0c5d0140c41342d0080d0030b0040602e07101d404400e9038240c0340405007480e0600c5400031502c481030300c100d002c10024140d42031b61044d0002501e00c1050301c0c000803898200307611551458102450050195500c501c050b24100440d502e82d50021030b0210f003954414490b80c0552041d50342c09081c00c0c02e124805085003e0070309060201d040f14080b59805c544450101c54054a411040c1c030203880c0140c0c01c040d03c05c6c5000b54801d04164504480110205080d80600e024108032802a66120700700700c950580c0003401c208902c00820804015400c2d680a000b0400000740b810302c404089603912802c40c4e005903074090389114000d07004c0c0403039641841100e54032500c5202c00c000202d100300026011907101c010b2428a0200da408441c10140318170120102e103aa8000299180c5c10540c0d005800c8846002c8480258899003010142034601409121201030700190800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 396728983 1250 396727733 396727753
    0x403110603040c0e0a1b170a05060108180316030c020a06020a03021902030c03070e010f05040b03070b0906130f060305090a020a090c0e06030901020306010908070e06090a06240e030102070302 84
    0x41d04c0400081c1000102d9030f54814040c10720141034200e0495502c0f40d80c681d07170006403000711180280c0010740110701007403a1078100001660006400c3d80c220444e074490781d080012600bc11072641c0f154181c1212016000075102040681040f014180706201b1145443d110b82c85401c12130f50f41c900c070780c7c0c050010380c041030030300c0718031400496a00141800613082e10f51005007440424649940c80d4407460445946000421100c5001300c2c8d150040c0008031000c0c0590300440c000a41d507071b003c03402460107601d40010401c0496948200b166049154040356045580e039401c00e985019216201d0180840c3c28440003914200001ca10b0002103980146800303185410260540c3c01002080c0c01d18041c003c0b40c90030000c1c0ca64400f0050741c403603c046c4c8005a42d9107400710005011307802650011303170300e98840345091000303401611056501220a6400e040140e44100c0090081c118070b5118840c0490240b5036090440e006603901d0204014a80354101108010300601d403c030300c82d07940c01a0040e002800b500d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 396730233 1250 396728983 396728999
    0x1c0506040612030f1805030312220809190f12152307020f01020c06090f03040e040305030a09021e0a06050f0412020d1a0f07051207080601120c050403110603040c 71
    0x1070714115410541c114840b40c480b40800c3c55984027000c0d00d02061824010481d099640d6011070104503100304840504030741a40e1000414056802d02c1792207504450b0f241c0c00c1d42200a0090001070026040c08016260394080714002c4280e4044240d903030741c24900b001e5100141c54092114501e490b84c2d80700011184400390100e4044002d0b2101085000d521a0300c40244000d0026005815405000c0c0c07405050044601e4074200311180c0c010029042072204004088a55103429480b60705418243d40c1d0755030344007001c0014520040000d500c6482c0c5c45601e503150950200c4c0b00d54040007503420281c3c26444080c1558a03001e010030a420341030003080144a15200c04d6000d105162010b40710b00184090f503034980c00b40b404d0090705c00104500e01000c11881009501c0055045101c50030007614008824500e440019802400031b800c2c007407110007180d003c0e442400e080c0c0b84030303503c83d80400840d09507200c0148198400e100030303201c4102d00710740740440e0f00e01002240d001c0c507400b01151403032514002c29 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 396731483 1250 396730233 396730247
    0x31101020f091c02040c0e130c02030702190e010303121805070909020d0f0803070f0309051c1b0501060f050a0e04020103111306080f0a0b030606060309031c0506040612030f 76
    0x20180b000f0244906100142c030b4901501d94902695107400c155018810305000303404807500f0b0703100005810802141c96858011088440325901030f50f9461001046a0a0700700c2c51910781d000802c50360880c0000803d150b8440c10014080e80c500d0300c2480200302d0202da181c100040c1a102030200d07003204104004210041d4080e0030482c3c409082d20864020641b501080c2821000d016a59418008100200140d02c00301f03101d004c1c0b202e4182000050159110300b0750342da034035400d40c40d5250740003528a03074442c0c001d84200c50b40548890740b0340d482c031410f498424081e08052080d00100d2400341c0f004146803826204070019100c00e0f80702e002080d51540c00450140c0081c1c800c100c4001000c000f100720110050320f0510183c259500d074003c00c1d08200940c681010b00080c80900c00b58030380b40c40035860355001300300a5006007007150f110342c1340d88031826114114440c24002c03540d920030b40c2c0005251070140b604100e105001c216801c01c5020381c1c070400080e1039504885c0040006400d052048111805858 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 396732733 1250 396731483 396731509
    0x9050d03021c021015050108011d0c07020a030b040c0801110a02060a020f090d0302010e100b030d030f020c0307140709050106050d090602090a0b1e0c15060612040f031101020f09 78
    0x41101c06800c5100000d2040782c1000d007a0b401d01c030064501c1403142d540c00234401e50041c4003c4403c0b24142c212030b425000d031502c1c06403041c01464000145038066644001c2110061a00310300d451003682801d10302000749100c240329180e019400c10758000d264000300fa090710808440d0750040d040b15603507401c2010080d80440115228407105003d011060b40785d05600d40c100920031340000849160005003e4605003086030710481190820f171101c8442d840c04900780c0c2d2110307028100494100c989101300c00203030040324030b031496910000c90b62906200c00c103041d0881105d618001e80342d030103403038a85140941d0803d00030031000ca10100005e1420152030380c040505e9a0041d00014201591100000d04080c0207601105204d040820512110491812404407030302c00041154134004170104810b44032580f0f400f603074102181507000940151202800ca0b03803c07196101c0d4480c0d90b86040c0c505003c101c118850140c00041049500710400742c0141308954008440940c17490030421010200514420810 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 396733983 1250 396732733 396732737
    0x41104060f06030f05010614070b101509061d0a0e19051311030606030712030909020d0e0d02010b09010504020a110a08190c0314030402060c2a0d0b010504091b080d09050d03021c 78
    0x2040080d80c907812035103d40cc2c0300b14076601d008900e0318040004201400562004803901401c02d0541610359840400008850540761681d9040d914294420000b00c01518a103240a003007108101031010072038400c0f05120711501c0e62018001d91882070540e5000304841d40c54045c0d02c00c503c00d20150300404809030000380700e45002420551110784180980e000707104441c5500b51140f000842d0403905024541140180d40b008008013180b000001d12422010b02c10580515400208140907501c10120160042811300c221030801e040e61030012400e92004811501a580c840c911781441c4ac412000440700a4041e0348040000340c41c0006000141d00290040760310042c100b00f03003600c003403041c072070342c1d0901c0e5144d0700c0c200862550928080340d0740101c0d0900391050258690030000115414120760560740241c0b00094804564a0411460080da03038402221011059000403c100300203118021050165900811a5694018002005141070009000da0401e0501c205210045100518041524 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 396735233 1250 396733983 396734011
    0x105040b030f010c05090405060904030c14010b04140402100504030c030b1e041202061f09022b05060a090605010c0209060a0f06020c03150906041104060f06030f05010614070b 77
    0x4010b1503084810031040d035400f01d00007180c1b001030ba2030644140e03980590150341000c0340c1e10b00b59400400148045800070104e14480c03609060b1540254081c98503080c000d0020031900c80e41ca4882c011004040701d049102c0d030302048102054502c03400a4030308a0741e00c05209104c1d1400c594a0303d0200500915489000e9441d09404050004ca8292140600d008030124000806003142c001e040c658010f107030394141803040e40c680804408104c08042283e012160058448840150030010a841044200c10014400c60388082191455120700e0141c003084450020140d0f0342c1402c0c03420798807e4030610340820b68034629040982032546180354030071001409a5015500d0303a00640184071180c0189006030704c5187e0401c0c0c0d1f400d08100c9801c1802039035956002c03900e48100342d50758034171000300003c00b0071801040902180e10b9940200780030f003081080b02c01800d42c40b58801030042c4026044014014101400007420a0241145130000e03100700220300d1070900c035611605c2c0102c00241280610b88a4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 396736483 1250 396735233 396735253
    0x305120a0c0804170709020c0c240c06101a0a05130302060c0d02160825081507030f1b0309020604030c03030c020a0806070e04050a0f06060509010f020303040b0105040b03 75
    0x84001c0000e007031340304402480040d0302d0400310318200094110b50b90580c810460300311a000c0015591102c054103c0781135103c80944810200b074000d07001070392403058001094010700300d80003040c101d118405911181122640c3c07081803d100d210070a038683c200040030056000110711810042c000c036007411981d5152a40c2d00c0d07001c1201a44800310310350702600880d295417000d80d0f05010141c00490704500904589007400c0080d501c448010a0740c142d0090184c2040c000c014589070424003c00d4a4415120182c000d003003405043e0500701e0710300f40000d25107180003101c809a4454600302e854294020740030300e0743e543e0066004200c0414180e0f4040c4060200000003551819841e000d148280d0b01e0102210051050249074007003900150502d4020004000c4620750041c01050303540402c840101c0c280e210000c00400410346660451b03c002c1c101507000c1900d5403c500240b414200070f9035524400668030707000702d80742d00042d40c0003002072403840010845071400c0d801c21540a01d0080540700340b03942c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 396737733 1250 396736483 396736493
    0x170403080411031906020c0d050301030206032706040302060712050f01051212072616020f010306120309150e0307090c020313030b01080105060612070f030b060d0501090e070305120a0c 81
    0x140003442105d199400103016204054144200003221110b42401130565041d0340c00101c95010041c0840030311210a00c030400c4401c002090101110302c502c095403064201800c2c02500c4640845038400498030000030b490000000e44240c0344694403402c000e060907420402084290112101e10405a100703a503600d1011f82c030101d005000c0e07148542080f08114100200c14103040c0070820900c05240c00c2441903c10746403030b1602440c000c1e0303411116180080c0090005900402542e000701500405000d44bc00805030000c4c0c01c48159540207506203418807040c0e2003125050b03564a078494040d00510020842c40d01e50b81c000512588803070061f2070801089081f148001c0324240d006075031820390500104502082031040340e0300158207a0390140f41124000c0d140141000103003684e010800c1201140101c203100f58007042944800501c559030306c11000c00102e000d45428000c00b0940d03854084034026400d0300285800c101c0c2c0c0d01070098080c603000341c5000724007504900000014040c4039498000050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 396738983 1250 396737733 396737773
    0xd031704031e03140c0910050f071a06190f0b0702040f18110301050f130c050406080a03080f15010c050705060f0403060f0b010504090c0c080c0604020117040308041103 74
    0x100b80d907900041c18441c100d203600b400440c05880c440c840c000c20000c00e6015150038020701e004003407506025a0b107131056805510903111700d44000e042c3c5810004c2200c1140c0300c62030058003a003800c81d00620880042c60106d25403241c248071ba05524000f0f42410060140303000041c000341800240300040c100c000407070143c19180710280800583c010301905030201f1a50b60814001400164000c00c802d281200c203d0702008000780407100348116007c2e40305c042104103165080a008080c000b4095a9500e54919a403148500d10880200b10031342c00041e1004c1c2b0034507095119019600c03a840412192030010340e0113084407801900d245c01058008181511014010440207111840c0d8039600c628508252049030780c4954140c481505280280c4843d80e030000a075010341e056500c00251460b2211819160b641d00004002e06402c404202c80403da0004100688100c0c001e80300d9503103007150080d0880b20300808481c01000f04240b04041000300724000c18200b10717180c02804035444030555600f500c20f15 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 396740233 1250 396738983 396739037
    0x6030a090305270901090203040c060302092e0908010203040209060d020a09091a1e010501050c07050a090e0105010b0418090c03021c1101181701110f0c010501050d03170403 76
    0x200d1140b0040307290901303010308218010515a0011815410140e40d004c0c1003048501c030300401c00d40c01017084200340e0303528141004c00028140ca004003421080740111202003403400ca1101003118140300080c5c014060013240e00c103950092125240383c4da0b240400405050102c001d0341c210305660000301c2c40112070300c01c590000380100401c000365007100b907444120000c01003610146030308000303c1c0b1044108903c42e9a040d18024203150384c07940052010304d4a03000d52640f000f07a01038188e9400003501107507581b014180780d6440c8003d1140d030f80c8800c8035039560720903032281c5e2022507554825440700340865400451601d00c07500c501c418441c0e5035000110000c9541003142c044603000e410300410012a881001407108080c20b1a01640825400c20a481c0f9590311a00b81075000fa07031011944200294400202000310803913054580812200104083d000f20900c10b071150301e800c001140c0d44c5809141c4004041d07060766000405056041c00d0100c402c0091300c05c0f014403c59101400c29900042410115 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 396741483 1250 396740233 396740287
    0xc0c1703010311100206040f031e0302091003020f1219020f12150d0b04060e070602030d0608031608090d0203060a0905070b19050313021807031a06030a090305 70
    0x10395045041003060110011880f5110700404814005440e0b00400c445a200341c11014601d454022400c0075243d6a803150035005c0c610740c54020a4445a405034003400300403034260348031112448246410f60491140580c0f4280703d103402c1c000100140c00075041c00c1d034080110708080701c8960b5240c07481e0050ba045070a50318803900f00800d061740c220b80f0900701079500c50b07000c1c45400140c02c081c2012480b5a0240c20700030b0031044a000c00a001e20407241c01044203542c00c6001c0f142e0b4180c0c6c91500940701e8000c01001c014050401800003108213000050b1043c080c3c1e80d40003103400203895600c0c50250382c03042074080e8100803400002c0c80503a90a2005902c50382c00b82c4404600392809107005410b20025400c0340c041d05a003400040800c0004440307c052800312802c0042d40c170b444241040040714041200250f102042c00301d00e60082d01202c1c1017a010b603a190f01c0502080ca0b040d20491420b140005200340c0200043c40059a41c100c903400c0180114000e0810b1440d284c0c041c1048911b412100b2205c4407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 396742733 1250 396741483 396741487
    0x4030305040618080a03020703020c0a0803040e090714040902180f10121e020307270e06091209060412120e01080c0304061e0f0516051305040c0c17 65
    0x100b84180360203099001c2528100014044089a881c503005014415500f0304255010440c0c0081500030400d025031140d005181d5a8041c1c0d07600c140741c2c1d50703a1041c052540d030483d50102060180034001400e000b910510046840702c0c2217a403040c040185079a010680c0d03c0901c1d0030810398007140c6108154080c0c880d0714010f51003031410104440206c103c07a07000011305c5200d0003030382002c102c010244402c5c428840c0070442c1c551400740002444e0a410707800c012a101251408540242e940540d00c6041560ac00000d010031070a40b0801601d0fa18200c4002d1100d81000b1188251301849600411980f0f00050519007829207800c07041d0082e41221f10111904030049142c20303400d0b900868403e00720742091130b06a0503841c0c000c0c5007010034003002e4402001680c035154001614014005d41c12130551155000f04054510581c5201c044d00054541040030104002c0c04503103180326100f20b0f861103500c1c200c0084014036060500000341801020b500400c100c03000a9400204042c1a02c0e005a6461048903 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 396743983 1250 396742733 396742741
    0x10171005010306170606061e041d07030902060d09030306090c120e0606130b01020c040c020606280b0d0b03011803090927020f100314060d05070512030408030304030305 74
    0x15049821a0b00700e41d900560b11031381c1d581c84800000300645d20003c140c550075250f1410220f41e403030446034420002c2d01e41002003004143e010101a09940c407144411034400039403927420094007203590f01300004e0b400c87c81c204003540c141c0c0402e4100c0307103400707119150001d1410f0365008080c040f81d0140240c600001c10841101c0ba62103034a001d080881080c0710007400d40703414001d001900790f1740c1407192400c000b5162185840315070b00901c1054840071020344284080c08070410000e440390400c40f6070300c0c480c590031084c0c0f1406040c0a07840d10042044850040021800c000150445412480d000b000c05601c0d4420b40d0240d860a004082210603074100c01107800314140f8010f040d0781581c2c0c03c42013030746250882000d0b06402c0c00c03a81c07070642482081c4070181e89185002082c82d00e8642103003960483c45659609500d03a50640c015200303640201e0120100d0b0700c5030410441d002c8101c9070050b01c5c65000c80300522044c0b42c0342510129141c132080850380b9081c1d0321902c15065400444050317021a54442c200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 396745233 1250 396743983 396743987
    0x61c1e060f1b0f0908060c040815070e061312210e01021b0418080405040e0c06040608091609140c090d150f140601020f060906061017100501 62
    0x410300c0444445042c444001060240d000700228862910100300030602e4000c40f10740583c400c84040c142e150142c40442c94001181c0049034403500c0b900895114403541010785400e03400e001401801030750345072502100c4050400c209038020b403111900c440c040001c00540003a40542c0e180c1e0305071040c3c1001100d200c0214504c0303100482c0140c3d8a084c48141454082d0070707a404101c0300c000c186507140c1c8042010000003c20000e115410244010710804881d1109001c40300303011300104c450807039043c0010100c5001d01a1280300c86160581c2220060100340440d900921a640c0d02803503210444002101a00340c1d4540140c81350b01c4a01504d46d6030030a000d410044001850340100d0640c1040c0c50b0180b140040327a824043c0703910103040716484203000a45081290032000f60300d17810000901c240b450015a4808040090352000d000d03102d016051703005100301064851240550034080c00e01a50741c0d405022034600c100903643c04009040310000d04401404001ea0301590126400e54034580c200000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 396746483 1250 396745233 396745241
    0x905040c05090f1609090207150f060303090b070201020f0a0303091b15030e01020c0708010b0405060904021806061902010912020339010504050d031a09061c1e06 71
    0x6500510b031401c10400c0707508420507825002041c490b403c070114014040c04582d01720a94100c5040940002166028840e0140f60700c108543d5150b0700700440181072034a03000300c5078244001030100e03000c0941000240d00020250140500600684890440841e0310604021503920120086070751100c400c030501046405c890382722380002c2030750315072241002c2c4800b02210301031110a0815464000703087c2c86040079015074940a451200312400d0584031901d0074064400300d01403a0045280c00001444d43c13501007040303400b80d50003070800c041100405e001e401e03c1010013460942c0005040042c421401c4020503040441c0d61942d00001e5642ea4501e00b1901006880d05001c086510034451141c0e28160501ca0903801c1c5103011041d190b5842003003038801d07045600c21514946500c0c0504000600c2070100b9640c6111074150f07410420a082c40c0e40f40d007801008449040d800111010000b98642400d00c4806118032201d41802d0800d1644d42d68500c010002d000d40348003007401019004200052401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 396747733 1250 396746483 396746489
    0x2071809020604170c0312091c0512071a060609060a05070c09021801020d0806040b030708010606031b0512010e040303140a020d1a0f01080705040e150a29130806010905040c 76
    0x101900104c8000c1f0140049800f90080c9188607a6014420181d407500d11182915403a500c002613132410700c002000d500c00c0c1c0d000144207854100390b1108844810b10320b41c10051007000010301c0c5606160048050002542040301c0c2d2406003d030401c000404039105410310710042070b040e60301594802c2c2c49101400c40c100b140309182d05540c80140c1d0420740311307044488180e00202c1a1400190008450300003031508040da07005074055444e00c100818140da01d034008800d080345404212176083c0724900110782510401d069402110804001404031720000045240c22601030f25000c502d00fa000c000c903045598007513580b00c81c1d00ba0f002480b041482c2143c0100d1021003141c015048003441d144022034002801c40e5400c50401030440000b605190140099a01034101403009140d1860903c404120b14851202c0c058410034000b200040c01100000e240d215101144400303004020340448064610b4001c2103900022140209010940c010208400c1d8000d002030800400d47d82068100a41c000300c142d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 396748983 1250 396747733 396747739
    0x12051312170913020306030a290108030c0d050d0615081518180a0f032a1e0303060801110d060b03100e0a150e060901080d02071809020604170c 63
    0x884040001e80d503c0415a410301034641d4090399994913030b00000e041c80d410307941c010614003d0a1401318451102c0904516131420108020345c82d03629190190b50324000c0e50403076955036100034920380410340300710301820300e40e0440100811741316260805100d0486402c0707031100003ea5240208101a0340c0c0c0e0620f10350001c17054503500a001d10003186140f101c04d00500058541110784a030581d40e51003005401009034200c1d10707444d03201d00d00c0d150003004040c096002c00021314203108031411401e00c805200880c16442840d10aa11102c1014403080c04545101581416955003000908070300078021424404400d000c000d659400c5110314000b200c0d06030304500c1e5001d00c14010000c00542012049050322500c4420421945c3c88181d014081c0400c6d0b004c1051640c01d00d580006c50300d80561401c0c2c01240110b4061039a60b80340c0c2c02d00340d0f80d05114114100140e008000c10041c8110542a80240d4502d1901c00308190199402049061344503a200740b02840089041003070126050141c0c01840801b1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 396750233 1250 396748983 396748987
    0x1e1a0601080c12040821010e0606030c040314071512050c090303040b071407090207050d020a0308070c03030e070e06120304050f010815040e031309060f031205131217 73
    0x41030420b1041c0908000c0504914414010801380f02d1203006680d07021a601c1080c91030003044541d081c1c0504800c0c8075503000101d154020690618120056a102d014840201400c051560b01e130000c100300c103401600c020f4006c0310b40119290610300c05001c005012900c8242c88038003c8a80342003120001014040c1c800014000d46108cd07070f020080382c084400392040c0c1a1261340c5802c0101140044a510710844d10452200240e1007000740c02408000380100c0640300e030000c51090590b02e80403507100050004040c60005000713540a075080c07102d86406440e00088a40c9184510f61601d4010f0300b00b10b000d00303100c100b008442e1034181245000141d805001e1400d09103050701188000740c0d50040141409000c20000d0611025601c1054404a005000380145178551034540d46030f80c04100030084d40b40203c28045809981d038001d1404994680301c641c0201855602d824100f88004c1a1180810500700071502d0541e04140c251070140c05c200c0042c0d900001b152900d80c4540010116502c400c403c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 396751483 1250 396750233 396750241
    0x61203070803040b0c0d020403030c021011060711030c01060f08070b070510090206070206030a06051f02031e07052407170a1109031603020f0a080d0c1e1a060108 71
    0x103009883d0041d50040408800d5100c201031602c0310300601e9001141140f000c01e0000506a01c00c00702281c003802a11040d5001452400c2120203056442526001c0d034481000b18514612600c3c164820308440010740e8100004800e80c90700703442803944201407030007207590f0a000c2c6800a01c441c10003011000302d0503141c0742056603070a031a22100e82400100a545215500a40d01d074482100d4202d5030040c071669991034480e030071100910306401000e00400580d07064070420a041c80d03c042c10080e4540045003000959920281d8000d01c8001d05507912100380b020380001b8100300880100f09646180020348110203c3c070195940000810b440200000e4041d840e0142040e1582c16401c05441c010100d50141d01c1c6000c03c03442d100b0310551a0709071203204051803905081110342002c0e244202c03440000c03200c082d010800c01c01e001c0d0040f040f1075000100c54198180c080c12280385107034418681c009400340c507141c80d41c01d170b4400c5001c01d0b100c201081c40c07900b401ca008034490a601c000b003420100040e0034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 396752733 1250 396751483 396751493
    0x306040b120d03230a020a1e050d02070807120f12060e040311071a0a0905030c06030606070f0203010207030c1e0302300d0b10032a17090606120307 65
    0x801c000000c0615950340000504010000c13a640d003080c3c1d8100d42d154490030203000b10002944958499030008a8000001d10304423142020504001c225944840c24000a071000d14002c0d4030203138040380d42c44000c002210000d168101075050210594640135500700540e040a0216506810300440c6e040c5010f00071b10418180b1001e04d07030481e80519052000c082e010800c28034040054100d07400a8803ca00801c92000700d070780007850b4412065541c445862390b103201340f554842c81c00440a5001000740002640307810001c02501704140540c43d02ca84042c60f54004c00d003281e002c00c03401d81c0003490000c000320500049099240950000e01c11030602c026254900a484446d401d007900c40c40442c0c10060405070b5074462101c4007440c61403803030076600c4041c0c115020090030f20490f05400f500909078400101802845070302003441d0741d195801d02000c5442c4c40c644580320010410b000f881000742c03120601260407159039103d82d4802d402050749040103c10052149924501c070705441e8030822610f40011 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 396753983 1250 396752733 396752743
    0x15060a0303030b01032c0f07230a0b0403050703061a010e1003090203011103010302150c0703060c031e0510050f010c080703030e030309150a020301120212010b150306040b12 76
    0x780c052a00140c00304100004078060440054039200c12210f103a50201905183c0912001074a410000c60352640000040d04c0d80b190750500c100c000d41c0400c200007000e103109030410600c4e5100001c0190038440e496407078481035a0090340068442d6405807100f4001c1200324810420400301c0080300c8420352402e034000038140188140e50341e00805540382a659045d0007a000501d00650043c000c0c4010510403c0a1085400c01d2000740d00c50704140200304882444001241c0841da9284054822142152180e02c049c0813a10784c40d2040642d656588802c500240e6180445880154001318103402d1448060640c011244c00003440b0300080c200c0340c1c20071f03038200c5010700c68030742e101901070344401e240d06055005203903401010b041070000008004020101003440310b0009402c04440c3c17030035100c0f00c140c1c3d02240024000c03028891400d00710140075182501c030301c858a50b082000402c029074410f01040c1314280c100d2002400b5072010041c040103261500590440e04416540000e03414110070403e036640d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 396755233 1250 396753983 396753989
    0x90f0601020a0215130b070816020f0a0b1801091d070c0b09010c0e0f0303092701030506070206100b03070309110604080d09080a030804081c0510090c0f1e091205030304020315060a 79
    0x2d00009d403281c411915840d00d03a1865040081c600207640b03035140016400760f41b00800071002803940750320701d4003550f00981c8040142c4c1c80c604901c2c261605003100c400341c0c1a4002d0454001d002e1406807020001d2030024405104140c0000007180412a02c2c2000c1c2001c90400300c3e180c0b046039802d1354544030b5180042540e0b0440d01c00c41d400c514420b100c411032140b980c814004080140001d2b00040148480045c0003409024150f08440096540200c00070200c4044d006500107003004202090341c0c42e200390001600c10703015140c90392001d00d0703000014001c1c0d80306600c040c829410030b600e41030145800402c181300522a10300600200c04076550001c140d0b15000308000c0c066040842d4090fa030707a40070b00c40f0212020201c4801c00507800c00100082044003944240b0a50b24200801d4022300b84c4624901c000d02c80b15902e5907800703170001d0441c0000c0800125404c0702000704420000400c500d200140082c010f0049002e1556070810740145030401c600e50210025007240e0405002494841100756000c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 396756483 1250 396755233 396755257
    0x3060b120601150c1b030615090501030c030f330c0203090a0504090c0b12040209090a12030b04090b01030c03111207051905041d0d0e090f0601020a0215130b0708 71
    0x28100315460505da01c0259801e43c4004108441004810071895510070412100c90019669a0b01c0c0d5441c845c5043ea14240030080441c1e14070b030400c1002812801007010b0341403044080c40019181081c0680038940510f000c1007650f4003603545042d002080388030b4104400303480d1015620f0411740b60085010000a44200c41c0180c0c3c1e1108040148040c0882c83c00140c852070b07100b80c2c0e407000e01c0500047c4862040d5000ea101e400700201003403c80700001240061681d0003500031541d1180c00740e05230f0082207903442c0f90b0380041d10307845090300140b00c41d82c1d0341e4061481000e4044071141941003011a441071540303014010741c50200c101d1404400010000c044820880e95030101251443d20a1805402940b1441d04141410040c10200400c140b00000101065048810620082300110b42100000c03800315040356425020417108420000020352080c410b004840f200000c950104640345422001c90b0070451000c80d80309240540e80140c8401032182000d0b49082c10100c0d22200040d1182e5010021 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 396757733 1250 396756483 396756497
    0x7120602040305030a030204090b01080103050d0e04181401150b1209070b03250810120c0312051209030703090b1b0f0f121801050f0d0603060b12060115 67
    0x104442030301180d001e0756100e0306980e111141c1c5200580a50002d0150780200c60412000f0382c03a42d449425110f0407a0b810100510b407442c0c0c0041d040d0740e070081800c01030750041d0325000915840882d4844070035010b4413a02180841c52004020503086504400841140c40200001007114055400640d500392285d03101d140003035100c0036940c2d072400140c3d40c4a5481c100000c801c011102c074800844445030241d807518038912402500e41150452021201c1d40c0c0402c1070120244490381280d01d412102d0340c42007039071400c0c10762691285550f101c20080b0301e0002850001d4980d600d520b80e21281c503040b105000056080548a60f400b405010450103500700703e0038080791160820b9940901118030078036010507580300110941c042a11740380c2d56030304c4030300718804d100840800b9418101100d1407001c4002c40c0c002100345a00c0111256404244803000500040c42903c0142d030f8030784142c81c0158407860001800701030324000c0c42000316880b80d2245443c2c0000004020180e0f01c004480d060030500d1070009 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 396758983 1250 396757733 396757769
    0x510020d1103120c0406030c08090303190902030601090e070806010b0f0901180602011b0c0819050f0c1b011106040212070306050a0f0e031912020702040c021e030c07 73
    0x42e1560083c109681d074206541c00c02d00c42c458200c10002c2c000d03250700750780500808007075510030340b08200141e40182c05a4010000610301c0200d074041e040301040c000d80e01003404a031035000a854004282c1008611071b5a032070030425401803c1164000030103410000d40780070341c90041100380728003c11030745d00c2d202c400000d02495641e00c10710750701070b000c8104151008110789540f0700070300034800415a40f41e603000c2048201c00007805003840042c002d40c4a9540e51500d04602c04185400c1000305070381090100a102280c800140d11020b45050f00d24440100324006203032440045006188013124140301c5d1034041d1000c28500815110761043d015504030580140ca640c9080c90903070181c0c0003401c607901c4c00043c030103000c042e5000141141000c07002403042144180000c0d441c2d2049420081200d10040b00d0401c025006041d0308401003d101001410030384213401207016510102131031001600808201c0220820b2906010103900c8110019800c00040208165440405010301c0c1032903800b031640d070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 396760233 1250 396758983 396759017
    0xf0f0f0a03080c0d0f090b040203010b0f0a0911040510030b1f05030f0403021e060f0601090e01060e1c0b0402090c040b041701020d0c021c08040c05010309111504050a0510020d 77
    0x45e4401141c1d101d000c01c80964981043c401116040d58120300c82c0d400c1c4124500146440034101e00c0600c402006424090700e0140c001780100010a404201d590b824400016143c0e2000341402e200543c2e43c03004244100b29a08100c954a042225507071078000d50f801c810407407544001038035403007035003c51000104c1c1c407242426480c02c009502c5140c0b6500c034500344409001c0e80440c2e028010041e0300781c61403082d05e460005440ca1032450281451542ca0701004000051140200410441d005022003000c0098185d01440119807428203480034110f10061108504100704a60780c844800150141080d04104040e50103110754031981000b0441040d00040c03441c420360403120a5080c10344200851069100003a4850151403c05081c0c013078100300c500c41003030082140603ca1503001d00149285403c0c84015001064603071000e4401c098403006862040d1201080460202441d001942d20b480c0350508200410840703800181c020742540505107901c80d000107a108081c9a02d04101c8072503000c112403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 396761483 1250 396760233 396760241
    0x12020d050c10050409060f050306040209040614070f12050402030d0e210706110111120403020a02210c040209090a0b0d050d0e01110a03090e06060c0f0f0f0a03080c0d 73
    0x100c1c0d1000c100b41141a01c0360b00000100103c03044850180301003030381c800e805904d0002d548103881d01508690006001450302007044e80d0311911880700028524402586008848004c46034100400c0b01e103411150459000070780d150f07017801c40b100c081c00a03113020f80c0440c0c0c56080c0c03010f000003440580b0140c600242c0e1044000041070005090464149002e1200540d07201620310401000c1003400e60081c09540b0113024044043c525165407624117060400e95009000c4010700c1070f0114051004a040165980700e0310046200c0c2104c0080c125941c05403e003030805410b500c1e5240700d64810844c2c451151141700400b50301c410701c0303040020262410008901020000a8028414081e810080c3d0041e40c0000c441c050703212080e644d1007414225144455503a44000300c024001c1601004200404500d04440c0f95021002411040c10140c01036490303490b024400c00041081c0d000881e8403e20040100841482d03200700000400f032465058401034640d0401800c00144010000b444040e01501500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 396762589 1106 396761483 396761503
    0x11060f0f0304020609060a09080d0f021f06180906050c041d040228290a050c03120708070809011e02180a0b030708010b0412020d05 58
    0x1031000d550700300a0080760300400070031100d207994980f030015000f140042e45508003601e06080155091805080c0c07510304101c440b160a49145a00054100d40c50b42c29050308040e09080014080c0580507a8025582034105003e4803240e80e840c0d5801840c1080c0120b00400c0640c84802d8112203500c00c5100700b5554106000160b004407440140c00782c0c12600c014184a5407010b5031018403045c06e606141608011200b140811a410911103136901c800c03080e50304084a520542f4401100340100e00c41c00c41000700100e280000765804000b1182003450300075980229280000d40140902402c0340e184e4006510200425a4403005008161503a035603000d84809860014400d000250040c00d040014800450600305c0a611581e02d550013070000c00c483d1540d07034580144041c040b01e0044e404550252410002080500c0c030b6400c002c03034900e5044074980503940303550070f196103007880240d = true := by decide +kernel

theorem cover : BRFrame.Cov 396582733 396762589 := by
  have h0 := BRFrame.cov_init 396582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 396582733 ≤ n) (h2 : n < 396762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
