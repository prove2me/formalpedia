-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1072
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:06:56.347702+00:00
-- url     : https://prove2.me/submissions/b1b22881-b524-4fe1-94c3-3fda2386f008

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 192625899 ≤ n < 192805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 192627149 1250 192625899 192625907
    0x507170102030901050601030b0a0302060f090a060903031101020406140c01110d0b0f030c18130807030309060513080a0c030c0807111002010e1b010c0506010e1f0509041b0e07 77
    0x110400e4090000c000b19110103004405481e2740d102c156510205011050025103003003402413a0015140e05458500000d01011410b481d66a07030201b0081741d40c456007007060540242441804843d034000031480c06003820005400b0192801000410350008036080d200752a00b58041d803104d115103031465483d800103111240c06000c0801d005402001141607400745030a002880c4640039100910040c6801003488040b4144a001006905000c0c48059481d02051008000707041040c000d680115500303040303050bc0c500f45c078000342c60141105104400c40002c9010031050301c0c501c1200d031405070358155050408036511509880b0280907400d00080744010004601e403004022102520301d4100202068001d03800c8440704102400560800308140c0c5500150000419190205040508111001e500e505203000c500340c100e18045802141442000c40780d400000906803007030302d41804954202408a403000a010380003d0881140341c0c45001ea02d9040d100300c030080c000703d1007192080e03c0c03c0c0c0c1000b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 192628399 1250 192627149 192627151
    0x50702191409010515090316030605010e07021908031b0d06090e0604051b0a12030207080601140a03061109090a0209012616031d100f06150c050717010203 68
    0x1c0d40010403040d41611606100000d41e048030002400b0000c1c2c080412900d035003a038001d5114980c14051034940c10a03ea90682e03003500518050400041d4540c1480010f540c0c41c0b01c060010380039540540c100780ca5032a10661400b540e036501000d515182c3c0c640516002031038030350460b10b244080012a840c0c54401c1e035507020200322158584140200b412808406460706410b9a020380340d9084030300715035810026102544107198010740740241e00c03907445401030000c4c0b08483d400c8005800c4513203f00020282040046c3c05003940f8150300441001034800100d840c0c0d80c500c0000c140c2c3e6190302003482040f0500c0103a685184001c2e00585103131038800c0009009501ca034842d03a02144944400080c40100c0d019100c441c03191803100300031f0945079220b080306054004039a810405858000050080d008055115841018503004040e80c0c07003141015419183d040f10200925841c201040160b1f04034159000b4562289003080c404c0c403541410464240703030b6070781c0002c2d004440009007030004040540c011 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 192629649 1250 192628399 192628409
    0xf030f09050f12040b0414150a021c0f051e04090c020a03020114041101110a021f1e020303160c02031203010e16080105040e0709140405070902040f12020105070219 72
    0xc1c8103e0303080f0240c0c0440c0c901460142d0342d44844c062000344040300007026049009400185030042590f01c12140030240d0340040704800c0160002c051441400b0b240702c02c808403003210740c28030001f0458050030042040c06001c200091034a5800000c0b103018405808075009400e88401c1803014080245002c0d5568610403c01c5006601c2d00084052403440310f4056070240b60312120380c02c1c02580c100b0044640b0320010b0492401c80c0a80100440103995400c100d2117400c82c0c9001c0104564007202c07014240751f15802d00751400d401003011030204260f02008030781d40b1242c010620542c0341d00c051001c440c0d5100700c140003074062044944200c0120440390107541202d00e4a0701003030b41e590718641e00d80e03040604603000f000411040c50040c407443c907040d000b41c1241d08a2a085407446035540c003844096407140703e01302c5000030015083c0000c2c000b05010050281c0401c8000354545840e241000040240c035115110046460701c2c039000c21688190704445017180c0040406400644d00810110305500074460 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 192630899 1250 192629649 192629653
    0xd140607020d02100207230d17090a03350f06030d0804080a03020720090f090c010c0201090e0f010503070504090f020f06070b151003110702010f030f09050f 69
    0x542250710000303205680d0300b21075020b0301100f03c10220850103500091001c603007060724607d8544c1c28100071000e44a680300307060010060300301907501c05418030000f42020845080c80f030f4200540b01340c000500d85006980f5107041d15508050b4100410000c400f4040c0c188107240d0031400c0b00006406608a501440e05901010119107800c1e0405507203400904810f4049816100001c0c040342d0024094014a41d290801624104041d03840041c0003a5400c1040070f21144a80e8000c2142000c81c4079540c01150303440540601d0502c0b0844940d00c000d1012035504020601513004116413150b45240014181b84d580591241001e60848032560805d0141601921130420b001072145024011040c03070503042070b14089035011a809006032140707000308698005504101543c0002c0d640024148241c551141044030001e8010403c42c91210740000f036001c050801c00073340a03258800040710011a824244800407524014003503000d4004228040131451070f00b0701079014072801180308141902d480003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 192632149 1250 192630899 192630901
    0x212070905030a0303051015051c05091009030212070f02130c050909041b060c1403031b0705010b0307080706180608011a070501050705070501050f0c0a03020a0903020d1406 76
    0x100329031000440c4a01a4141e105680b8080802d000f68009034100c0c1d50313480c21000b40b9880315400850000408114030014200051041c050141d0b03000200c2180c5d885031b0305224509022686550300c003d20b84c005002c0b01d80e03841000c001c05000b0001180c1d0780001c059901e46405036801c10181d00f12070054146d0054041002441811003144070761824080785071165400e2005d1203051001988005004607459100c0680c1c40d441941c0c68010b000007004d040d0b40d4002c648001e40b800c0310102031824822065944181f040c003840800d07088100c5003e00b000100b0300e4030f40c500c504065014001c3d1a200eaa014061103001240101d0003003206e0084e0754440e212500100240c28400d140c5041500c184400240007200501807400784803080d51121101e0085036040410907260300742151429a01140480c0d0001960400c002d82806401e90100dc00414a403481c0b610a198010070322400303c1c68020507500080701e616040c040c0e400c0710f0182d034000e030074082036114611b0b00102c803401034501c44c01d481c42400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 192633399 1250 192632149 192632161
    0x7020c09010e06120c01020d0e0a090e0d090f0b040533030601170f01060f0207030b090604020a060c03170901020408010501030506042303040306021c0c09060806030307110f0103140a0212 82
    0x16085170000d00607030080020360302d0760404035084d190661015034040542900000c0c00303100ea0007143c00660009001e0082641c2c0c40d00007511180b480c2d40b040d41007290441080100300340705419a400c98200707560680082c5d03000c050802102202c00109840c03410b105581c1580101c44a020f54030840080c4c0358040c12108100004d601400200c40010a1006a60041c80510301c502240009042940101c0c0c55054a0769a0a4401079040b601c0e08495071050b41080107500d80b001001d0020005810070484400d8941c034010405c0a11000308030404c2d80c0c81011554440b002d6044034003c109600c001c11640d6140d107042c42e10307140151030540c3c0c40c00b6841044852408500c041040490100300114032b0245145d507081c0c040d40042451021000040c2e400304003c0c01e080c0a1016450165550361403818280f005c050310030784c0c0c0501b086000354018403495000031b80c409810365000d4011030700c1204610316500120050000c140344691304a0794101441041c0c0390340d4000e80740c0c1441d003400c050340c00d41e208 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 192634649 1250 192633399 192633403
    0x90203060a0603021f05091201090318060203090d05031b01050f06040204050901120c050405070804030305150127030c0f0e01050301050f040308040201090b0c1f050c09010807020c09010e0612 84
    0x16003c080c0d8800030002d0100e01074125503200c58050001414120f041c000c0060004071010812442060725075110300200c0101070348010003c10900020908075071060400000130755a011b03101d1000d0103108504070301d80912000b0010380b055000607000440780c1e00f0302c55004074041c0c0001d41c3c035210160449404540b0619060080c2c2c0d056403405407841d001c07686071040b040e50b00d0200000603188801c075000e010903a9100c5020352441001c2580b100f01d0715047c1407800400305d0708002c2811248000001580c003050f82e0140e17810042500d4406252000050f40991000c1d80304103610040c80441d04000c0040d410f070710341944030215060440404a0760303a848090600703a47d401c80385608011945030002e40000e01130241c40d43c1003030041c50321401d15616800035102d2a032041d160b0764520740c0024040e1001c0e410010021443c10304000003807000342020080c680e40c0d4001c1880710f5050220404c00a050948204140c12018200414620141d65181078145100001780d40b220b00507407201308100c11000c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 192635899 1250 192634649 192634661
    0x207180606080907120f080c100b01110c0f0d08040803161a06090103080d02160b0603070501020a08191206030f06060b07030903140708060c0306191d250201090203060a 74
    0x50007142001030300159a84001c2805040e1080300c002078107000241003a4010400546602d504080014ad54140b410016114000c3c090350701030740b54040407204901c0c0d25000c0d40a03054550590f02180f0b04513a07450901041d004680080685100c0170601d141503100c2e03041180e102900941641c1c0291800300c20005680030304076009500549540b0040001541110050130b510718150401818808020b020f80102402002d082d00d030284150140242440d0611a0f0f60040100340000e00044242e0707511140140288114442c4900d590001c8034101e5004d0034515a402da0034030320400c03185440c0e00d048503d900148c80150b9005180500101c0d803c2d80740d100b26525240c1544800c44034501d907a640181059800420071000d0103040360000700f0400170080c032405100072080c0b8a440c0d03e1b00c10306001c10341c0000b04065407801c81520040045039640c240c1c6000d41016100d94941070750341c80c9a906070107030401302d100700078030080600c06920f01e50640c0300d500c00c107100318155110b980b16500070b0415951 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 192637149 1250 192635899 192635909
    0x605150904051b01030e060a0b130e0a020613120b090607110a0f2901080f0106031a0a0b10120605030106180f0b0604030803071101090b160207180606080907 69
    0xf1040c0314030160512000921a60f03c04149404114004407440305401c069055a92030f0020b80c81d50320868042c42c0c008440100c0c00f5901404000c01d0b074420f40019504d076400c020107409001c0002d00e02165a401c1856034015154420300d500389074446107020040880222460720680c000c0d0008904058451344000c040d2002c010001c003903100c0d6a80b07546003000802203048491a503460090140600000c1c0c00420426860700c800c03c003917141075001d6040124078503040f10316902d041814400a00403260444d80750604100140035613481400200c0103000c04802d085e0300005d01c00c10410b4031a4071884420300ea501c0c000060068998850074103007600d40c41c1c080c1e4101c006a540e03e50700484010342c440d4901c90310390fa201085030360900002c070b291b0341e1042d0000e0311103000000400c814a42c200844d8544811040c00070030a440e001d8440c0c0071403590280c021440b0341d04032030380115001d2007045000017610400310311600711030007400800020b00242c41910042650034000640d03c00001c40d101040701c2d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 192638399 1250 192637149 192637153
    0x3010f090c020703241413030207050414070804060204090f05060102011404110402070809100306030537050a0b2509050604140a030804120b06120d030507050f07060515090405 77
    0x25541081c000c80104800e202c2101251b03a07265507001c44020210441c2c001c3c02806c509070b03862501410300a0801c004d0390489409031b1b08242407502124090040e060b070141d11072900d61100e07200d40c07400c2000391040ba8806001d05040040e10b9429004a51083d800303904240c000700302c00c98491806150044040b41e000e020200c01d070f080c04030300c2d0900d0b400a14140c3e100e192590b01e04103107800020a4101da12426100003561141c2c10310812004010b400458040002e810313560b90140c080c00400c8901c3d0140d01401940b110301a4402c000081002c481030340c0d404180c0311054903103034080c43d005001c2d219034032050f9202001c0c070740d030418002d008a4081d142c002c0e00392407606040100421000103080950f54029010180020104292101400c00391040d461005541600e90500d420603e40185c01e07107129460a4a41034903980001501c80e6201c000c50030046440d58401c20f05460340d015000300300c0c401000c00500642003081641c84144922200c07406480503100c400140109c00c4002c9500500755 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 192639649 1250 192638399 192638423
    0x6051c06020901120e0a050717030306150403021809010c05120a0e070302031c020d050423040b1c0b01080316061e09060b030d02010b0a062303010f090c020703 70
    0x10580c280c0040038500340604143da42e800d006000303001110011002c0045503004021503104020781480b4002c0100b1207030240c82d2000c0780503411652244030203807480781300c0d0000c6107510b6511002001583c00841d0000c0800000320714803004c039400740c01c0803a03450005500c1c20308000f41103401102590510203601c1c51241040c1c0ea882c1e00c00c0000d081002507400d90b03101d054000070059074200500e0b03840845c0000c21f0541070003034a401074030307041c08442c03454203002061209200810220300e4400c42145180c40e00c8940c0c8d200700d00440e00600034289404d41003211084c543d5580b0b00746d40203990381248121898140c50b130fa6664070070f88900801c0110081210071203c06004076085800c107481022031100f80701c1c2d6032001d5501103400c50382040011078007661910001071180c40c05006000240031240001d00172001513100184003881207000301000d004002c0c4640f15800c101011040d00c42d955042d685a69503104c4480c0810400c40d071003080301107810309070031000e000c0c40416601c0071030760300c4a0a9492 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 192640899 1250 192639649 192639653
    0x9030d030c0e0603040c08060903070501051513020d1506050a0206100b09100e030d03050a18020a15050708221a121503060106200303041502090604090212010906051c 73
    0x2244d101610650b140c1c4151500400e01440a001544c05a110750000719510b25183c50014256000203200080b02d844000755100141c48400b082040d44c84006401a0740e0280b503601103004105109820340b0450080802250f0300f81c20030b009000542081d02251811fa4603004000c40e207090600030303c8403140090182c0501814640907000541103c2d007008103a01813a600800d10f0305040145400001c0d03183d00600c0a41c00ea07a100700700080000c7c8501c02441e40042d00800c01c94507041c402c3c09222004031001a20710751244003a1520240d01003252503881644034104050451030042407000015600800074100c01d0041c641885e4242c144801800c1010f504518041e000e0018000325014001c0c082001c0035650034802c44e13000e0040d0381c48134080da103e0301501d070344004440e14046034103a0007001030101140314030b6020312020b03070210030250f03640e010003010070083d0145500c0312090600220710710300803c00020405040c0e82007a0420894075035180104045d5400e0020b040e1100b441d65001800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 192642149 1250 192640899 192640909
    0x90e01020f09010f09150923010806091e04080c011503030c0b0a0b18010e0c0a0c0b06060403050a03020d02100902100c02041503030302030109051003170d06090204090209030d030c0e 80
    0xe0305120a0501081050340c0c0c0d02d50030350801e1003949001c0003030342c1c7c600240004034801b4910103d08417296144090100f0303040010b48551310107408584243d01460000700c1ca5184401100e240301c19440400750141031500d000c0300c0c1500240d426600d154244a510340118803c1d03000a42100d4141d514604042800c0c1c40341801d45030060010788801e500c1d042c185078142c03201543d030714080c000382980703101035858104070041c2c4110260002140da8403c0100340900b59001684180031f03600310031040e074070f07445000004d00e0301d101301e5000030290b0044074081810300d178001c100380d11a091305409540000e0a841e070040c040310072603540203520241c002e0310101094420b8068035001e91001d040041e652690b0048001902c070310b0303882100060780000040c4481d41490203281d0300034840c0d00ea20410301e802c40d950002c00c0051018001074070880450096030382444e07074101d40014601c61404555903620b810f072804c0030303601c0308418038006c1c819042c80c0c900d090700c07912600250080300c0e03030340041036500601000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 192643399 1250 192642149 192642167
    0xa0509030a0804080912161a180d050f030304030306050f010c12030e0f1f0902060714010906060f080f120301170109020303040608040213020309060f130c030b01090e01020f0901 78
    0x60707494130b414800c000c1c00c0d032a45044544500401c000404501c50300b848502800e82c003d0701306407512046031610004200300c2d44d05982d0081c0351409403140414411012844ca0707032084102401c1d078811000700c034040b107202200450080707000317070380034080c054035941800b11240d21148080e000907031100c400400700300c001c0c0582001201d0783c074022440202c0251210300d0b02e0101006442030ba040301750901d0241000ca5001000d00201001c18401c3d03009030380004085005060f03014008150705518000c10030400c0d844046103640c4401c0400c0902d8540d82121344c00801c82c05800c0d014440d0180104081e1400160f00f10700500b21185580f1316030030001c0c4c401c5015145414038015640711011040166800d0014001a0005a44242552402c0d0042018454042850007007203403040041c811401740110b41540d0180c0008900030550300c403810b04003030461740200d000c0d04080588001100704122410101e040303c07407805040c0902e14020070381a00300d1042e0079401c102904c0810000362294000d003ea8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 192644649 1250 192643399 192643403
    0x708040b150f06030618040c06091e05060306150c070f171b0a0302030a120221040b030414010207050f0f010b012102120a0c090605210406021908040501050a0509030a0804 75
    0x800a0520300c490111b19850301924100ca1340c480007442886040e0748101a0070061000d5840c0103c4011050001070310304441e8050a80140c0300040060301985985000c410110841802250b644444103082600c800c014002e0300104070005100044c5400010711001170030121030080d103400c52582c0e60711101c8864660351950001c0d80c90a000016130303070a001805060380101c00d02e000784410203134000c0c100b040024500002814001303406e000451f60a0603103043c1d60340324008641c1c0b07440d1410103001e0f0800c0d51294401075030001030712404108000c1100000c11070900d00f15104280da07042d0440c242d0b42d824914600007100040039440e05084800030b401c910340300706401881c00389010859031030040100c0d40d410481da104c08100901c1540680070314000c168a251440c10171000d90350031000c2400c211081981d200960010034288201c980c1201c007000c1c4200d0313003481154600341028001020481d8181d84031751030100020b170502540e000c0c0900c260580c41c00355281c00b80c00074064034a0080a841 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 192645899 1250 192644649 192644659
    0x30306050d030305040203011407140f0f07030c350f07020613080c1f0f02120a0f09050307030803010302061b01090b0a0e280f0602030708040b150f060306 68
    0x200042a441d41901034003524000d0350003007250700d818014142900ca20760000790640b9490b600f0008855408a03c0113a544000d02c0309540d18503600c1c880800a0042c008400883c000000304042095044400600181d2041112441142000c2c0c582c04050f005c4201904078480c03c28407200c6240f409c0d100802e00d182c2c01d4036a140c1417008640104805401040c03c116202a541006100c04032080202020000d004c0b924100110100518a910010900085414050011142c800d4640244002d00e03002006884003500c803000c000005040100030644c52000c110079510208203400c0111700401034079000341605156074616424012550312240500e01808019621900c0b851002c0c014400c04c60b0040801221a0a10100c1c040807640194400c41d0b29034404d145c1c0300035111860304035400c485032801003c1420041c0703052802e100041002d0041100b44004200812150480140d81c0120300030403d62249586403200e0383c5e40140c104450036446051980542c24902e0000c006507400280504 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 192647149 1250 192645899 192645911
    0x5011802060d0e03120f090f0607120506061b0705010e0111070614071205070605070309020918010f0f0609060e0906370c0210060b070b1005030d0905010914060904090303 75
    0x21884003813403000d488030b4210360a05000d00100380820040c0f08ca4020001c0090041c50a140e440541905900c081c0029611344441c0020b01c1c65480c241079800755000c280c44800c402240310005510350007030740991400306191200961842d44940384100c0c0c0c1c4980c80d0001e12409041000940c3d0450b80030210044003e1704010001c001120b201c005050525107032502502c6100300c1c81c1c0381c1d050301c10007070003841018607015250016a940060390f44e04004425220f01e00d41201c407440b036014140410301c800b026818450161002010755019908403084000208021500c80c0a01c00440f041910341e412a50322010100d110001e03400d044001c20040c2d65424800041c0d049a1003041d10080750912070482d507a003c0a840494051001030289070264008005680c103201a00c2c065002c3c1110140420030200c00045860b40c4800d90000680b80050440d5410030016400a240802c3d03406a980043d12003c000259041040071a1001000007811b140c24204004103020050840c10415010161120 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 192648399 1250 192647149 192647167
    0x50603030f0a030609050117060a0c020f150103050c0306010303050301060810050a03050a0c0905070903030302070212070305030418020f04050609010315060c02030708070338011205011802060d0e03 87
    0x580200315800b55501c01280b00c9190454050841e9070581c00840303880b510010141c2c07c4980420a1680075155040014035644c000000f05d14004404c1c203006c005e442106150140c0144100c1d4244c100d0784a1012514283c500c4001d06403a00c00078070000f000304c1d0060005019003406101c00704c4d40040c003842c0c07a00b031050361000091441c20071544146c0e0309800002e2080c1c10310010041100280034004028451400c00c103400400c2c51040f44405010154040f52a0003159213849081c1e4070b0f1100d01381110301903070300d07402c0180c0c59138020310840310a421365100d06450196240241d561042c01030742041e0500746000d040c044642d00020895040590b12400c41030107003608410400501103e40c3d90100341c001e1391052520f49241600003072030396403041a00300001112a200800350420301c80f002401543d200e10060104404421310711007a4003800004501d000740a043d442c02d1038091402400b0b44d8210000c1e0310800003020b00041c0d0461001c00410703180d500f450304004103a40810701184e16000b101 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 192649649 1250 192648399 192648427
    0x30103260d050105040507210f090501061410030b0312210108100e070f2c01060503070e040c1205090c0d140d0f170601050c011503060507020f0a0605060303 69
    0x14200129078594031001070106060620609038044440c0c01d0817040700644841c1101020341003419904d0103900c41041c581401e12540240e01400c0d4001c00a1100703c0c0c0380c82940c4188114041058092200e94815414140c480d002c3c030300c0711a40c0580501110680b404500b0203a900409511004080b11403c0241108902610714000c002540c042e01141c0041d940400940d00d040c410f501c1240d00100082c0404074400a01c101240e410701e44681d50564100c2d100e01c00008450b40c1d07500d030100000b00001d22540c220008511416080d900c000303080305079008001c2280ca49281d00d04c0081c880e284405400b0f0003d500c842d8210441c00126080c00581100042054ad000a4115160420b0000a61441c4403c00c5071036001c1c441400c00407003840325080020300400076512403c102d1a4150085070747ca074060300445107010303480380091120752402810724458002c540f2040b91214036000014280138408a05150810700b00c00c058841441b498840c0c9025007006001d50360305020400049080c2861 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 192650899 1250 192649649 192649657
    0xc20040207080c0d09050a350604030c0204060f060804022101060305030409060605030f070302070314040b031602120d2a020a261204032003040302090105031203010326 74
    0x83d0000349080922950005c114158940c0924021115100140030001f058601000042d0301c03030828000d0f440c0c40c400c1c0d22070b10104d42207202c8074a000300310070b100030715900c00d03400801d8500a446c1445041d0355031520300301100c014072410380054056030110300185010040401040048941c10340d51005817030809086415030342c4103d942e540000350030030240d00d141c02000007c143e60b0a0103411498400b414003102100142080b04041d030003e00c0e402018080c5210789221400002941d45658403078000030a00e500607266106142098004602c40500c0050007003d41d640c0040d000d414140f6080081015001390264140aa030030201d1842d00c1441580f04000c03083c0c010350040c6400115400c110658554000c14428002c00c8a020a92a034210a04490540398060315508242e41c4604040314600143c1e0340031a8616004003220204510000240c0103603802100c00b005c050b40e0703a800700f607900c03050807100e11a458020300c01000031811004c04a01c1c0c00e00c04210219585d61178681300041540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 192652149 1250 192650899 192650917
    0x1f0c020f09070e0306150102070b160b070503010303180303020c131b08040210030b03060f04030e040e0c0a1d0103120c08070506010e1e180f0f0c0906010c2004020708 73
    0x3d22269514074a1404000107600080705050203060340c121100000c1d1206200d00403005903150000b4000000d000446920925076002012100300e03041c400002402031b403007840290300040f200c00310b8140c60010500b032201103c3d4190020009000e46405200025540000900d0503075a558121010f00102c6510800d08280a5440c030205182030301c1000160840c0c80ea810b41007515081e03c0121a0702c000440341d0b044210b0791001d9850b0798840c030701101d5003224003c20b10b401c9411701440700ca01c4000040c10540600741100c00c154126140c1d9090040c00045a244148030101d8500410102e0240801d02c2840e20652030405400d164079101c2c0d844650155004031501c1d40628010840103c114102a411401c02c8003d92441c00317641c03030001e0340b4901c0940301c91201d600048003a890f10204018404c07001440301c054549101d50031203120344503801e034501a801490b4007000281c042d80301c0d0381c002c06201c1c0c2c815561014000070383ca102c90201610044a90407036400c010000c0491142d0000d408085 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 192653399 1250 192652149 192652157
    0xe040f050a06061e0c030305060d02120f01051e06040905011401060809100c02150601031b0201090b01050a0515071505040803060a050405100e10090c080a06051f0c020f0907 76
    0x3601c0c1507801000b07504e20601d4616003101414010392002d5001d000b2101145c0c05241c042010b0720761400085100c800780718025408000e03038200c00c0003a08085101449680e80300c1c020402a500c0d1326000d2070b2890159030001482c00c0480001e640351600f0340c003d0395003500880c00020310202803070201c5010a0283c1156000c0f4588404200d402c0c1c90800000c4001c0904010502c11081801c401a668464024036a50214680300020b552a4440c0e03001d50b01030050941a403082e5061040060b00070700b180741d400d446a11002c000450142803144400088860140280d0705400b000750111a45420041e011104450258401040441d4034025507010700e024046055581c1017400030041c1107015035100c10b0041c0e00708410000c1f004014050f500c11a540075900d410695101c5240080140d501d800c441180c61515810003c3d044c1e111b1166845000f080404106140d1184100b126100c50400820038800510306501c651902c2244c900c490144054440c03001040740e100040c1c040601110640000307 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 192654649 1250 192653399 192653411
    0x10218012105010b0c010b01030b0f090a140a0f0e0114010501110309030303180606030106030b0a0e030c030d0501030b1023041e021e1303020904050a060c0e09090615010e040f050a 79
    0x402001e00c9402c2c4141f109003010800b280000c004a0204101c8288081c41103c5110020300c495801d0340003c0c001c0001568200011301c0d069a52100801800c0a52040503262855004c03912105104004003000640300c450a07980c07915004542c01a41ea46043c84280000e0000031940e48042020714001c0364002c19580c0c01d0000e61540314502f0300010f10641c0310381e040080c00c20206400104054101110030001710300008419041842d6114070015540c5a20001034205418201d691001707061324480c0392008030300e40354000e604041d80001d004006540000441300d10b030fa25106400e910403204050000314003414039181001c280c0c12501314400c007041e0006001400d090032072211040e02c070540c0e0010750401c03080b4a940b01402d2400e010080c050b044240c041020300c60100402500175a1019081c404000340100007030002e204921003038081c8803460042900050045521481803000c0b49060201e5044000116002000128010340266549004a081d000d0b00d00849d0f10403966040b007c80c1c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 192655899 1250 192654649 192654667
    0x706090302091e061e0d0b09010c02120d2012010314010c09090216081908011221050d0c080609070c0807030305040804050406060305090d02010218012105010b 70
    0x700b194001c15803200c0c0d014441101a40c0e51038000e581c0c0d0094000d844804d019680e80540b001501910307450150700441c118031203002c22442d000350601c9581803030000d020440000f80284e9944005000306d4401480501c41c41400340307075583c840720080840440c0c4000e13009074444040640d9010204032908156054014020300000401c0740004408060003000882e0000000078542c0c9079502600c40040e400181499a00882200703001c0080e4203c40d11a030348000001402188550100395540032800c44400050102001c042030205135400841080034107805250100220300c2a40070328051190900c1b28104414051064064001c09a10703018500e080000801c6660780005180204210500c08204001008031007503560440e410700340071805480320300d0304043c335000355044103400c1407074100009203046c0c2c140c024900501120b0f05480c10519200d208900380c0c442c54000301c030b16001c10448880194450007051621291203020803420b4540c40c508203068450070ba000d005004c03004100c4d029 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 192657149 1250 192655899 192655909
    0x6030b0a0c0e0a080a0312060f1203020d0201020a0c0f02011106100e060607051c0201020c0d1d04051005060d020d06080607022e050403030e07030303020d060e0615030c07050706090302 81
    0x10410500b2103d43c4920380c9050b0840da0780e40300410f00201086000b1802c6411510103400840241c40320341040710406403508a04640414641c10a0300103120b1a040301d4400c0f1f0040c402c13205070100c0c654500c00980030399124001c0050340120102e04102833140040d1118200b030003240e020341d041410700710400f4603003901d030001250060149440b03030004010140008400185c1ea00d506c190458031943c142d87c20031070581c02401000301c0f881c2d190041a016000c0c1d560b10045410b10b0700c0c240000c00c1c4900ba4110140411640c0c100c504340800000901d05201914003480031382621200201d0251400b80300200c40400d5845a0740044440d5200b0000c2c08a860740500c4044907100110b4485282e1410928521082c04d44451862820f00c0d034030004181414401e0700310014040c090740807905040d680c4e1400030021740c0400d010072903041c6010404100041200c03d40e0307006200c010031242c840ca1014007a1443c1c0e50001d818a0702846040100ca00020010300445006245540b9040c005600e18010301c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 192658399 1250 192657149 192657167
    0xb01030312150506030403180e010305060f0903090d02060d0f1505010e030a050309041802060c0c010206060103061a090a170102071704122a08070305190506010e04020406030b0a0c 79
    0x3555080710214140f05545a04043c0c0360300580618002101141801c2c841e10022903036001400010200e10000c0144072001816034024848038040585503603c9020103501c07409026030302a0311503a0303c1818005071400d00098490060b03100c5001440b031500140c1c1030115000340d01000c042c60703601e039020040c941e0042c03080b0600440c1a0050301c0310011303983d03d8980380d00c42c0301c0c4c03607030b226a5035400c04801c103500b118200601e2580c09419146d840243c8032481e941c0359a1391810340e005105200024185502c40c2c0980740840d40c514003100e0141e540d208007100ba9400645916801440306034002a40098208089580304568400107980b0441030411110001c0440e900503104070b0304102c10411125000080201c442c1c02c040070a280340c041070200042031440c0400b880300c03445400310100b80c0c0d0b10301282407004c82e4401d608440940ba1410303814100100130807005440394101c44010462072051884803030344144000c0000500039241e9403104034000080d649500b40079516282ca40410340c00078503270 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 192659649 1250 192658399 192658421
    0x6050603030f04180605060c10060602030c0d050912011e0f020f04050f0f10021b0d0b010611010e01020304060605130b1311070506090f060a0606020a0f030c0b01030312 74
    0xa140741c042502c6805a89101c0d500c2030241039000c21600c1d19032031840354080070180400030005907440200440b07080d40d4541041d45480901c4c942240060780038000411134412a0765200079048500046109076191f03000400c0f01c075002280f0480c07040601c6e50a200b20800031150001c030700407903a4032560440c2102c961318602c101d20b510400500040c20040390903501264401c8903038034203c1e40340c1404108050b1295441a030420a507e24404035982c02041300c0075400c1071440d000ca0401c000d1000c110601c0d0007488090000e42040c80144801031007081404035500d202c8001003034862a0026613070890b88116001e03601a40e842c1da0500462a04100b059490644140140446203040000820301d0246400f8003000640d6211900e4040302ca803825600c0d581e810000b41c600601c0c002c1c40c11a00c80e9084440b14140340603800001340d6540042c8210380a5604079130040070803200e503035540008a001c10303406809000444440c5800034000d10101c1d8081c521030b0380c5400c0c240c5c0f10025028140c1e0101d41f05 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 192660899 1250 192659649 192659653
    0x7020106030c1e03020f010c020d06051614090409020105120720010b131d0f010501060206091b06070201050408060a0603120f0203070b0402180403020303040c15080601140c07090906050603 83
    0x3ca0050090407650401c0d2a01182d0407000c0600040041e20f1724906004000d40007648440e401082c40801e0b8031581c4030700c0700118001d03860007052000301c1c5c00342400e4442000b624410700009005003050ba10240344648107041091610381c0c80000d00d92001d10031a404030000d5000903042003020642c901e502030750100c504c020b1280c81c010500140c0b50b009410070046c1c0280d035030080b040f4400c843c03800348158098403505840b042120315500a01070314007402030401510072000030a0b10030b00001400c00104a0203c20901c0008440781000500d5112a2040c0e04128040c0030100e01d0080038480c82c1c1c003c0c030000f94001402c9140d03240038449510541c0360f02c41402a0903a42c822040c2d000b004440e1525481038814010359120701c0014070124141c0d00c1030600d0302007001040704041e00000154051b41c02641c60018140e1f40f018030b201d00ca51000c10b5540000d00070720208000b940900300b00802442d071000f02d0ba082c1190080c06a1903d026680310b020400d490b56440810300105d486819002501500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 192662149 1250 192660899 192660929
    0x10090803070b0606040b040906050907080903071103010914010903090614090f04020705010908030a0f0203070921051b040e0318060c070302030313030b13050c0609120607020106030c 80
    0x1aa00c80c0a024000b9080550030310000781190344180445e4040c006007195141c545e52511481c0c07008042500580340616103e10108850707500a014280c4202c0c0448029480d140003561031000001c048044580c266403078118480004d4400c0000401c00c415280000401806a0500820350b92007548030f035040c03000d0071b582000307100707221411280c0159040c0d80d02c1c0018248000132800038491540083d200d03501c1c00310010100b050000046002d484550000d00041e0950500344080b403000f03490310808104d55100c200402600e990003103088180c000b0b41031036081003644407142000303015441d00550313040c404c2c00401145003078810f40c000b00e40007400450500056900300100c41e400c1d4144588144008108480a03c0081001c0c8000c0c65000e030a480d00c0c0c64454900c8a40300e4000d000440e03c0c0c0703403401c0c005403c0d10102d01074003996581000c000c0103600801403d0000310703480110500d802580101103060140d504000181c000c00d1180c0c0000741e0bc525600785284070419982000030341d80725a078 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 192663399 1250 192662149 192662159
    0x50118020a090e03090603150307090204060504090b01050705010e06090114040c0b030402120d08011703070b0a0b04090602040b090405071d01030c03020d1802190605190516050307021009 82
    0x6407400d000d076041d0714400514500103186991542c043c681070140d11030000010403442111501c1c4080c50940c0c19401c031140152540e1520080c0e009500aa00000b00144000c10070501550404443c6a406050051030490161141740c250742003101c0c10b0b0407036480681482500c200034031444191706561243d540080c140ba9407611000707074061140c4903a010000c00480c0035540c0f10303840d00c034103030309900111440c0082580000c1c040160903c244011402042d2a10f0307010440801240d0760240c1c0070216119643d5a000240c0041005034103050b00705640d0442c240000c3c0e090320040000e803940313600284d15106041e0800c4144c0e10010601d03020406000c61410b198104020704041641e42401c010900c4140420200c009005d0100680d91080c203002249031100d01034011918081d000b86c9122011500720008841c003540c141c441c074400150200000c1e408141440110f1034005802d10b449440c040d21000c44d04800402c048003a50941c2000410104520b0602c0001e40c100005003001d00c0b00d01d19007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 192664649 1250 192663399 192663409
    0x615060903020904080714030307020703030801090203250504080a0b18070302090a0903030f0504030c020103060e010b0a110f0a0308010e0f06010509062b020c010e03090a05100e0a030f05011802 85
    0x76000170106500031980c0b501704800409100c03581c03502c0d481240d40701e1400740c000a40d100c0785440150003042d0984004182c05000340212803040096640d1021104a680c080c0d03484503182100031400c01c607040c440400d4030300c028000155558090100d0f801070703081c400143d40502c0048130131140c040d03202010030001620341203415a4400160a0002000d03039440c1000e401500c280003100c80c01901c1c25007040304040e0401d60b42c1ca0168001e9904104241c0c4680ca291b08800c03003030280e01402d110600404441c0b5101e11403040d5203410f04401d44520301440400b031882c20481300811000f150540005200034600c64034290390003805840d42c400a8104203001030319502c10322424074007400d00051301500c10380100c05000c4800d04460455200e80410307071180002900070301940c001c19420b00e034001c0b80c0c401d8000f007902c0301083c000308080b507110719150400125032140d42003103090010321314100510b6a40d80c0d202e0401140500152031060100d49072840c211031f610f0030a4101144c40394080303000341e159 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 192665899 1250 192664649 192664651
    0x130e0a0803070306050604060507050d03140115140307052503050f090f0d0501050603010f0e191401020f04090c1706061e07110406080d0c062706150609030209 70
    0x40003080755607403a909811006840c0a400c0035811004c0002c0000300740d98050001c190141c0100155500d082c2c0300745d012801d03140c0703d035542050082e102c1d005000030760003080040181011400c08120481c81110a80303ca9081203c100b0003080c3c1c0402c111440152828080c190700c04085c0081c0740e8003490b0b85c0c0140041c02510001c40c60780101141081464a45d8000e8018000780280703504c0035400d240c036029018010841e502802942000c0400c50400014044d40e01146c14080243c08200105c0d50b00305e004030002081554580501841100c055000b880180120124081d4141d940c03420000f484017614000100001040100c4101c50300308210b51512541000c0c0441e40a95101007040348280d926691070302c1c5010300000040c160040264841c3e4829620209032070030702060390b480c1d0a541e03e43e609206800049400011701100007112a8400203d2015900783c1c103007002030070202c0124140b0104c004440c4203135941c42c1603a4007121748410078024030076454003840703140c21940810302c5940 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 192667149 1250 192665899 192665903
    0x100f030c06030b01050408061f14130c0e0a030f0b0f0f070e060903011503020301050105090103030f0e1809010c171501050d020403080309031201120804050108060307090203090309130e0a 82
    0xf82d515451201e0382c0c8120104e400601c0e10204940396400c0508168800d1624546d41200305020788900240103002140702000000004010100f0a0114120300c4080c001040c01700e010822521454401581c1e409010b00c040c40c061642080c122039240b5044034013020190003c850f41240a080000d01950210f0240d841400340c030b0b051030f5004084002c1102d60084800c55940341d402c1442c02c0084404024190003100e000300d00030311580e642d440c248003a45000b0b01000e40000c05080041141c24054072441c038100101a041c8810a04601c4005004034801e9410480903512500c83c0140a9070041041202140da00b4089105090103104810107485000d00141440342c0451803030030024440d41a03400468100652070b58a15141c0c41440e260b03488000840b1801240c1c50000c1443d07518403004800d101d030300c134400a1800c1e007041c1c0151850070f801407030107900d48200c13400800e8620303d50020314003c6242c4802540c0f070b029100c00704400d030500700d40c0c8034020f9441c103035035034114000010300320101d15 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 192668399 1250 192667149 192667151
    0x1406150c0a0804090c090f05090112170406080f07181208040b07060608060109021305061b0f0c0f030f06010911040b070b060103180b0a020a0e0405040b100f030c0603 73
    0x44540c4060820302800c0c0040d001d140040b0780090520f01d10707003004403c0b6a07603686598020303032100429030902142d8020315130000c02d101c005102d80c2100c072034443c0c0c03064001c808507100245100000e50055009030000340c0041d50179030074400d003a0840b189040d0024603a061410038915403c0c101e0035150214071444420454451600080c400003908440140641d4185666510028240b08010f041c903441041d09500c556400018100003510a0b200a040d203000c02107107083c504020016a038200d001d40684c2c800110000e8400c4980400c126200359401e4270203811294402c0d13080001035002013a806002c1d070030460140b006090301241d600d05640300f1480c00034000b40042000c10241c001c0d038002c9001da4000240820502c441c02000d14440e420998092190501d034520380715092001810081400c21000c0c00328200d1007094014000040c0b070b5145c540c1147d1115030000301601c6c401e640c141d445126450901120300d807041c42c82000340008100700304406145555070300145109224450405d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 192669649 1250 192668399 192668407
    0x160305030a060e04050601031208101a04050d0b1b120f04051207080d0c090308070b0403210b030c01050a02060103061814011506180e040c030b010612140615 69
    0x1807078940c08540035114010004106107070901d400c0f681c4100a020517241070556000c1180700500c6806824891400c7d481c070302011a29044424016030000040fa880400043c400402e003034490303514844c5d1080c0981c004101d1170400541c04041480010910700c030207502003020304003248290045c6500540b007482842c40e560350340d0802c14101510000f43c640051000030b030b0b40007030029010280c408600e6800d410810008100000d032203103041c620009110040500c102c40c041890000081e42c002d02904200e0010409480b04240d50040703c071030501c1381591040786070440c2c02c041042804041c022b007005440c0110b541c0001e517641c001440300400031600c80745240d199500501d101006140d0205d242801407280441040c06860442c181200043d10120700103007080c4100011000074400c0c80408000504094400c540240c000f04251400016001c0010004030070441c1a4020071090343e80200000000c040901034982204c80c5145540340c1505020059841e05044c0038946003505600b6a1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 192670899 1250 192669649 192669661
    0x1021207020d05150c070c05010801050d0f0c0503071203090e04030c0b090114070503060f090f010b0a031b05090310060311010e010c02090a0b0f03120322061802040b03010216030503 80
    0x140c82012201030b601034014406000700c01c00c5c4100640f80d864802d03074203141d00d1a107440044404240903c174140d48600d621a000001c511041e00c414045c41c09840b01007080b580300c0010070300d015016030040c040c06000c0d4170b502c000d060b4070004482c0500107004c100c40071410241c81c001c0c600700e0021009468103121102040d003030b100c254046510080e20500c1e00606140880000c0c081d50400c403410340c050209070212200038034010342680d10582442042040913401c0c00d1208117179030001c03d80f01c0c1c01e0642c2c5114010000406400214445000f60744059aa41d5000241428000001c1d5568407042c1405c206000013010300040c1601c9100a2a002252015030320040b1410340158a01a41058002080c070810b044203800c0341c4503070842940c815041d141c90409055a40d481c40c4510020711105102084c0b180220020303003201186040380c41d800c440385c0358071400308403448003080982d11101c044000f811424140503103902c00000710000c50510130a122244880000c20308000c040060003c00120 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 192672149 1250 192670899 192670903
    0x3020c0304091404122105070c02150301030614090a0602090f04050901050a050601020f06010e070c0212030c0709060e04030c0314040b12151008071e0c06060501021207020d05 77
    0x4024140d000b010b0069501c59515070703441070020340d82600d400c141548418101401011480c0600c2c1001100a1018680d030004000504002e0918404c1041803003455001d655400059020716004202180c4e0300e52540c07800340100c94202c440d903413200c1140000c01c00b0a0304041070a40586800c5540135a80d0506800040c43ca4602c0c1c0000b20b5109107001c00340015440154003440c0308405103002003100361160001a42d0310024a01c1004056001c00010701c00c41031206040c6401c002c880c00d20210000d42980080d002c050700342010f08035640042911541500204200c2009114030322301040310078205014031590300310040015060055030240c0c103003007503c00d007003048511030088607142e1110348401c08404654020340326090048554404602d100903294401c03090004004c103014150320b5203640030303241d081e0010b0402040c03020780240c50074a02651104042c5249481d600d044100c541440e041d4105c035a950040c0741154448014441604840320481d6410b9030101c0e10070950b0100c0c1d240c4a8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 192673399 1250 192672149 192672157
    0x20709020d02091c150b060f0903010f021b0705150a03020c0a050106090605041a030312040f060c0305071e0e13090c270216060c050d1103070f020303011503020c03 72
    0xa038005603e2003884180e001d01084c0b600a0900c0341561207095204031800c001610f280500b42039100c0420028001c030300310f8805c01094030010141c00800d5222032480c45000302d8000c0750031148140400072030308144003010b010890150008440070103604071171000200c2c0034080c03c800d10043c142e00007402c8540701420803044401c0d5501a00038080e0381d884801450190001f403082d680118100005050b041d01e6043d4540407600c2c003e4020f605021041010381c055960240065525900368420000815514040c8a03042d000035100800c40d420801c40042c4141400d0288015009040085a100300d40c40f074001400d136007080700c100600300000811034000305410728008004180401001400d0303011000c60200303420010300303281c2069064840c1d402c01c2c0d202d2400c03623102142d100c0030b0380340010350190b014806807003282c685182401c039610340f0001141c518041013100c025020007003110388c41c0e004620600c0f00049202660655240c01c80031103407405240c01c1082450f4000c240d02c1424401003050b1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 192674649 1250 192673399 192673417
    0xe0306071b03112508010c02120901030504150f05060f040b0102071502070f030c0905010501020316030813021008010905060307050f0f011e0305010503010605150703210e0c0306130201020709020d02 87
    0x10403a11303075052111007200c0d80f40c0d10601c1180e50806c0303141c03d034090010034081e4411028100452415030a00011402000014030449024800401d411017030341440c85031302d40d811001880091681040c00030030200c0f21502c04e80510032810000c020307402da40d0229244e41100c02003501d44240302e049810580c1000c44a4220581e10400420000306101c12031b01504121800018204401c2e601e86004a0f164403c410059014116052030340b40081d118811041d44a65900201c101205141d0f00159500ca0011070010001d1034000045c000c50341e251041a07003003003040f00200f62407890040811681e04500121500c00d400080208445074083c4a0000c2c80c01404810b210018286440181c0200020300071b0798005d61a0440200346030804000340380b520340880700b0980c00c11100307980131030f6440e283d0024044006900303505404900b103540982c1d01441c0e000f80180c50304144a4043c54a0100010a0300820300b06626511015076004554102aa02d1041000d651401070031206c8021b44200002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 192675899 1250 192674649 192674683
    0x1032001121a0a12050319031b05122d0a02090604030f12170a020d0b1203120c1216050702030a0f03031401140d050f07060e0306071b0311 61
    0x807102c604503210726084820703204a5100700c0d0242c5401c2c00c1807541400d280020020780c410030142c11001260004001e00c41c1c614a004500d40800b84e40e11546caa910400e040c0c08141c1c081403010a0414042c08a54086100005440a200c0c009038900552010904012001542801190703507510940c0448446220140140d580d4513500e18009209402400003910410005218410241d104001d21480f503e030026003142d140e1690030310310009512120750301d00c003d80c1c2c54406041e15100c03050070740308000f40a0060354407020a0303440c51402d1b142c02440c182e541d8a0030030000c0300380c03211000001e800c0500305c0c1c01e00b81441200481640c2034882c0e0740c40694076200c1c07040c00200700a0041c1050041d0f901c40e6409202600d000c801c0b01084180c00e0250921030760440700d80d0000c9090000004020500070003c8611042d0440d51150810000e038101c40b000412040000040e82420071446401c0041445c1c160040034003d000001c08207900b40c0020104903c0c04c0a400708400200902c800400340650 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 192677149 1250 192675899 192675911
    0x3111303050a030f0503040803010504180204090809030d05042d030f11180403140906070c0807050a1706010e190c030f18030206010b0c1609090c0902030103200112 72
    0x4260b03954240841d001c600080079031a106901320701c40c00c182ea0203039510000c001e0840e401c0c4000c110141c00c44010f903140c41b040b20759181d00969194064056500d02070440ba980e40c2c900c0806140c284042905079a042c441d04210800c6000c4401c000303188800080f00044c91010100d40c445002884a980701604400118622005100200d4069040c5090880344581c040390002014411b1140441c0c0150108100f910521f580049000080011801c01040c0d1807400d005d07170765441ea000905801401c40780e070040005014a0070040c6409014041c64090f114602d0079400c4070390750340d1005010f0414039451b0840402e81100c0d60f50301004440b0101003042c00a9007103208014002c0001c1030280c0b18817414085c2c04010a1075089001d115036030185c4c0500030316800c2c42c2407520240c1c416413480c6014403401c00501741d43d09040c540140681708001c0045000502800c10030103644007504942c04a51040004200141c0800b10400701c14000e5141d510021240f4801070340e185035215456469241004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 192678399 1250 192677149 192677153
    0x40e0a0209120102040510030612030f021606020c0306010503030f0313020301020f1c05060901060e010e0f12030a08070503071e11070b0d050108010911191508010305010e010c020c0103111303 84
    0x3d005017081d5141510410803901d00403901b00e0035900a03108524010f5040914800400e104903d85c403845810750044464590f0880c00a148a100c1940010016004103800914515092003000e0061400300c0c010344c1030921a10301c0301c00512010744004003084c0690305110031500c0030340603545100080600340d0348a100080c000080c410001c2c4103d46076500d003000203032041c5454403110381030381c419a840366182c001010043d1001040070743c145500c00710001d141b032500c0e540c04000c1003080361030302c0183d501d4403d0220041c2560002811910a2100610401c81c10319800500d000f4028011070074104032042058050b0303001c0c1c2401c030741c24986010307040010031018420402455541202c0d402001245c1e84c4035902402c0754a614001040300c04003003c071302c1c258079100040c0d92503094040c0500e26200d90701c5421010b44030014540f8804500304074010414004203200c0d80103802071500007401541d02c1e01c80c4c02034a810921010605055940000e4059030342e049064030302144030140803a11298580c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 192679649 1250 192678399 192678401
    0x1c09050607032f07050d0f02040608070513050103051c030914030a12020408030307030e1f05070905040506100f020f0f030c06070f05070f020d0b070f021b06040e0a02091201 76
    0x442c2002c4240030b540c01c28107850300362040001240f0300c03100c000d04041810501041000901c9000540e051500402c1900250f81c07248105002031010030001d01e00c4030310344403d005030041c075103400e10303905407400004002050001c1b440701403400d080010864002c0c0300340b038168010302d2007005c094004086420301a020900c004020f0000c0881a1030740c01a8402944800003644070360702689103181c105001164440e4007d81003041511500c1060316440800a00a015040618440451195250000d0108240d0412002d00c06418151424031040c43e283c4086241c10b05206000002c0140f800745410f08140300340882c0c5401a00d640a44150b6564050110759a821020030f1465500610300400e501e0b0b800f46034907a046086036243c2a041080d40e8403815141c0d00401d00a9030400c0503003c4520014010740c03181c622a0780703940c5601203106407a440c001c2c81e049401d410020006800c0300c590078199180390642d400c4032005800d1441030f68450b010940a03004280320103800008080d0401020f20701 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 192680899 1250 192679649 192679667
    0x50114060a0906060e1c020306091506040507020a030e0316080c130c023f18030106120b040c030807210903170c070b130603060b0304051c0905060703 66
    0x8440d01e20303000d5240c1442c0e008840041c421a8085565880c0c0381c00c5a0400000754102260f1005180c0191746003030b000b00e0700306601141d600d4a9078025807442c0807515400d060081d002001910300300082e25202002942c1c506c240c900c040e051105a0031901320ba075404000759007404c0d05262011350741d0307540d40300d010785d43d10f640c480c01620500f204d2044050311241c61145440440081c0d000340078040301040c80c031440c6134000c00042c07603442180c65a090b40d416034001509241c02d607001c07419a10310340e10740603200c40107015201c54482c3c1d041002c104007101401c501100300e42d410034503540c940e8566150030001c2c102250b0000f042c0700000306401341032102e40d08001110303003040001125a800c80d210100c1c6c9519040c04000e000a1520141021544a4001808540ca03c06084694454a030b81081a071600070024580e1134412000041c400190b160190720001d065040000d030650a2036074800362031b40f0512a0852582501400e03a060035072003070600800a010103441181c1d01c66413418003e22041c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 192682149 1250 192680899 192680911
    0x70305040c05062d1e0c0a0b010f0602010c08270a020a0305060f01210b1e0123010c0c030b07051b0c010809030901020607030b2223040b01050405040807050114 70
    0x204c1d460954140005181c01c807103130305004d861003c01c0c41c811900c034040b541e04103404807801c5115040c001000512600b6901d07005c0c0003150070048000e031420308001c1c2944e91174103040c400c00001d0814440101040004c00d03101c1340040441c00446843c3d5020343e0314001c06038102070b51046c4400300002c01e000021072814003802014041b443c1310780c3c80366504181c10030ba81e02040c21004140d00950b0119410f810803980028110751040c8116280001d0030380303010740a8104d0b070100c480b45000b101107204107907885181030100f802c0ca0700d1a8625a2a444c95200c01d500c0f001c0c114000040014020b54881d1084a4621154500c13644040d1034100711942e130b803418040014040386011020903c080000019159141c60503801826030350343c1c0c0d6004074058004c040000343c1050880d6a488902e4103003100c4015405500400061070240c00004038034040c0c0350500032030780c414903401840080f841805885054403000d03900415183c445203451112441450000340007546001207208489042c054141d000300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 192683399 1250 192682149 192682207
    0x1914042a080c03040804060c020d050604110108010602010c1202160215090a0509040b06010c1e0506040b13050a0b040512030910050601030246050d0606030b010503070305040c0506 79
    0x59503000e142c201c50320040e500a08044001d0204000781c81c03094000813540d92028280c1f59030507640781c1e1550f250810681d0210b60000300d4203038000d0300e03592024106004019520003400030180c0442c010b054401040d0141380b40d81e0300050f001e400031426002041125074042c0845001c11418040c41d0503a8009030800381c0702e0b520b103940005640c9003044400b801241c110303000c918030784c03116001902d0400c407074102103c0c604801801088211500408120030500030030240900e483c0c18900864000c2c80104035002001039488101c0c081940040c1c124500d81c0d00c41988103094980c1e08099242c08150100c0500842000040018000008c2445c2c2215810302c6801c0c0469144c0340c00541c00e9000e10310700780d10400d26010060b55601c2801d00c1908111108105195000001c1e0400c00180000c10008501140c00040e1070a50002c65203c2d000040c9a41d1804000420340f0300002440c601c0064070403401c060316100802e0a04c100b400c9810010b00f8002c0c20b05070340c0c45142c0810008c03040c244000c0c82c041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 192684649 1250 192683399 192683401
    0xd020d080c06091c0807050c010917070506130512030411040c03020a08071713020a181b0504030f11130903020f1e0607050c0f070602010603020901051914042a08 71
    0x15120781c071102104c4007080d03100d46130302c1e507190802281d03160040140340c14559240c03180300c40407402060403080030080007030201b0303030302c0c411810654580710740500f500220051300c0240030040380004c40c107611080c5540d811980d4a46480c10300d540311040d00055641c0c868a40303011050680c0c0c269001300503d10071034071800352940da80355094540201071044a49040d80250000c0d00f10300c0000d5120345111b1008250070721039a201c07204500c00300c042d41c441031165941d5510820301200d240c1011040201e00786440b074501411555030030f0b1030740300562004040c00071900920f0819034807034840018130406081e0404c007800860800941ea0640c40070403521a0042c42c5d10603085052850300c20606000710f50041207142c5441074201c0d401d510440040e001800354041c007900303001051002c80000c28155001050302420360042140324241a0f0015100311340741202c41c0699150401c010080786c000301d005000c08a003150114014020300c003410a603610301d05000c8a0307500580d2459894803291a6145865 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 192685899 1250 192684649 192684673
    0x9100c0809060703110d02030f04020f2403040c030803070c060c03060f0b130f080106030506070305060906090606040b0a030e0706020705010c2a030b040210020c0f0d020d080c0609 79
    0x66040a44041c292030b0030034000541d0340d5000f9003010b015800007400f07440c41c14000c941120220380040e124525048501d109000039031a2030702185200c802c0480d41d01c09940f59580c0c02401c0d01030780b1580c1d49420040807000405006141494100a58100d501541d880c580f10324000e0500946081c103ca0552174410302220f1984203205072000d403080501500c042c103007440c1000013107400c0802003900041222902184d0840403918441c01000040000b00b00641546805410250020001d41c01c1614003400c100399035071407450b0311380c103d44280d0300700076a0740342c0e1000328803a44240e801501040100042d080034180d031617444032101c07050900607103c244ea183c0b00100c0c2c5840a40c4100350008184c2614540420249000c01c010103505003483d08910112000550050140e40c2c019550420b0725006c12003035040940b500f209540c2c1c0d900c064060000201d0004610310151000c2c1c82c002d40c202080c4104640350711010000260304621003e4880401d84503041d0303103c0084418240c01d000d840e2482d61 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 192687149 1250 192685899 192685907
    0x5150c060115021518070816300311010c020c030c06070f1707060f06150e130c0c0503040e0417040312110a02091006030e07050906010e0607050609100c 67
    0x1000001d20b5000c4c2100b898494401d62048101405003080c40c001c08000ca90010030402400c030080c50703d03602511280d4440040394105848a91100103070070355040b10385162503805c50114400c10090840c00c21000c0480c1000c46900c101c005c444c8071190718040b6007807001038001558a502c01e1003101100c030b03209001000c1c0311940c0104e81008101584012080c80003a4144005041c403021a030030444c10502c41d5160402655405011104400d5840100f8007080818915803030011940d401c10385809800000450540b23044034056007101075a5842484203940709503401d07255541c200c4100c1c8d0b00c0b0fa8460003160041d501c2a41e08440141c8000016007040e001034007550126600940c1001541889030401d0300c140c01305001510071405421060300042c1e072002d0303029004004030100c03090307000d00b009000b5044440707031801c1c03513036030b503c09403041156075503c011565202c0c4080c83d0240304240614003150240c001c2c0100101207008520811010200024603110304a54444044c403d0034000d4805603 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 192688399 1250 192687149 192687179
    0x30e041505030606040b220c11010507092702040f060809060c030a0c05040e0702060f060301020c030f130b0a0503060102010c0c0506061908010e0303060a1e030b04050705150c0601 79
    0x9a00b5811180000300c607071819a10149150750050481141e200100c0e4100189000008405079025a24000d55075081c4d4490f1501c841028860000c000d541420741c0c0c0503140181c3d40c800c6078201840d603001030503044114103250041c0c001480055407901d45407008d21844414a014010000b00343c000004d0a01b10000794071401903818411a03450b54481c0031450002d0440300d820541440000c00001480c014051505481100c0d281e01401c0c07903003072150843c1140c0c04040c21326842a80180240b50100c4400300459407505c4250046594032541c0241c03512100459a102c0180d01c240454480c1450b5000802588218026402044012405941954a038046c40006031042d80030308001655030600c4000103d800c4a0b03140d250a8079592414494203444040c005885140c1010091100303904140110001501c0c0556504203c0c1042c0d01800641100706d201c0034002d5104400880c05005040c00508041c0c4009440503c0c00b0140184d001c50685c000c035014190ba10804000140d009135114801c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 192689649 1250 192688399 192688409
    0x3090a0b12090a08190302090907021006050102030306100318020402190806040204120618120c0b0606030106080c0a031503030c021e1309020406050414060916050d0905011404030e0415 81
    0x282e820030848404060790a045080c05c1000d05a0800405120b991a02115882103800c4d600038101d60611a10810136510a0750007507066502c140b0900801c0d0390b0309614023000c0509803400250010480d011001042e08003003010350820f20009140c4201c0368140712213040c0310303880d450b48032964490f90184022032243d4441c1c210304810a604d03440000d1040c0c0c00822040388104c810901c015940e40b2030440c800d5941801c0404134a40c80309140400c407141040035030040703003184c400741035614107030010b0314480f00289250a00100021410409400383e408198440a1807540100f0a5124640a0049203841006921486512600c40c902c180d030f80c03c8032192441d0160000000024020154020300002d10049070301585545000c2810340b45c82c410341e56038200342c807460b08071800c00300e080c0840004003a107080740110407150721840c07050300071084842480340e0540008400443d81021401055040844005203171008203200c1890740c08003640f002680111000c20030b0001102e041010840d0600c07503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 192690899 1250 192689649 192689663
    0x1a0403020d0203030d05090c031005040c0501260c04090e0a02010207051311030915071d0904061b03050108010b0301021309180803070c110109052103090a0b12090a 72
    0x1440141000d500508280e0b00c0682140c1c00c00d03c1e9560a00142d8074104c800b41d101d9440361310b101c02146010041c1079084044035000f00054205030b214000304803d5802554144501c001d4412044003142e816000703032840c0070884c80042e0a1070460340c00254064880c0e035020f00d04181c0070840a042c041640d81903c0e6058008003030300d520340011300081051045001da0299918001b2030880c81518000f14412200c030009813007601401d0511808044018042030100309511921003c2c2c0c0c0400710b61000c4190044600189940d164500038000e4690b84440f843c0201c024044510000e030944c00042c1a24444c10090103100f0440c0141801c074003602e0b1202d04a444070040402060400f80d0050004105920441e1581141a12207603050340c425104040060009000754080c00b00ca01080302c0c00b0807003440c100301c02620b04800030300344844800710140802030300f00c0d556421040400846100d9000a03198400091303581d484082903400031418402501801000540c0004010a01141403580a14 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 192692149 1250 192690899 192690907
    0x6161203021e0325020705130605030d170424020c060906060922050f0708030a030b040c0e040b0a17030418020316050c0705041118040e0c01050a0c0f050102131a 71
    0x10f0441800394030f41c1c1301c44041d4000c210f00845c0b1078407103101074031075051045404609503181070103240ca014081ea08620800c000b60035805402e48444140300d400c1508424002e1003202d01c060503000e640d070b500d03000c0a10144000340700d81070488085402e900c030300300c1e01741075555681d9940180440f404084400d0849072001c4100094410481003910744018064000c4512a140304c0703151510b803a075150005010740e413000c201d802090f58940075401218800f03480900003144c0124010f00400e41c240c00d46445103454032009c0800f80c9848924600805006807041c0740189940e2503241c807540300380038008661a080103c541084800d00031070380240701814414071000e4100c00110f4807a004041440d0150143d2600001e9954560061803546495000010f680300159450881c040010100d0340380070314107000000f9407030000490514901c007002c1c2040b559800104c20100c030b800c141d030707039006000300074a0034808140041580034180c146554201030400a40712403559400d4548030300300d1020315800300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 192693399 1250 192692149 192692191
    0x1020c0411040518161103030c0a030f0f06170303012603041d070f39051002070b0601110307060f060e04030c200a0506161203021e03 59
    0x1900800d60032412811007420305440b41c0014466075810207900078804c081a043c00a00c0000c1e00304420310102e00c0c1800a2049205010785440c0d000040c03564607480d1001c6461284a07020741c000149040c5100420001700c490700b60f00c00000d1056010700c3c0c4102140900005551800208680c140d41c005001190380c28210303c0004440505007000d20b0040c001400300240301009200d02007031100070681c0072032503854000001030070710503001c1c0e1141c1008240701784030f41c21042e410300103039121003101c402800700400507202c40010341d00c000c001411849030348403040303889103030b50702511425104072440e659540b208001152130100c407005441054104100000004078254410203d13140d02d00c02c0820407642e690584081010304440075008550301c8681c80c020084211450340c0da84800300e110019260040c0045560451307140140c5000e40d100044141c0740000c010031411810794000c00380d440e91109940010060f4000300c556050026140300710034031101c43c0b001540e1041d41c0c0c0c100c80355040e060303d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 192694649 1250 192693399 192693401
    0x20705060a0e0f030d0b1306060e0f011b030210110406090b0a0e0a0806060102160f03080706091211010509010605010509040f06180e0f0f07050105030901061e05120a0201020c04 78
    0x740e590b005040c8550301000502071424000fa003540c825104002a10300070010500c0307180009004420b01c00d614141c070500c09187c000041d004a000b00780c81b10100c600d03003400140e44400e00c00300040d24200483c100d0000701540007a280282e40d4000030103010112542000c3c04181c0205d00071000030a900a80501c5041c4612001c4c140c03540d02d51400c2c0c41d107843d024000c03490081e0b440d04060001e81001c820081c1c40d580412054034070413481c100420030b051518010b4844141e050000514034000002c610341444540d402100203960094441104245100d1303002e09242d02001d82e544440d401c1000040003064103116400880300c040e140c540c0780480400821008025aa04a050342a03170b8560101c0c0c0c1401c02c2903812611620042e0004010204004481c50041103010881c45a403249083d01603401c00414418101d901c203082c81d0392640c64441c0c4942c00341940d50014403000d2a01c1c41c0314211501001c0003042118000d072444456041000d0000f916110203200280c05a44602c0caa80c04504003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 192695899 1250 192694649 192694661
    0x7051903030f210e01050f1501050a2703141506040f0207051e1015030b070207080a08040302094203191406010e0118020403021819020705060a 63
    0x4600d0400a60145003c00034005001d911818403010350b1164600d840300024866183c0041040132075440a00e440142c0c0301208895201e00790402901180d5030248500500e41100c1c0405140010310311006c2030b50303011030007140c3c612003a55424244015149440400b085030030303168183c090060241e41d20042444064110544400a912380c01c000c40d02c0812010301c840348a24201d910700ca50031212850219140c070000d158402c0c5d400303103030407860441c401382076807030310100e980c0705424080e60341e40c00206a04048843d446024903000d207100d0340c0d0400c400100200240c0b8130071038004906807110728800c41441d903150071440e956200b0060741c900c0c90492010f4066070348003d44240780000105404242030550800301c6400103941140202e04212035440c6110785000130038010b041c9589401240c4000c1e54040c407800c1c0b20110b48001000300c04029030125000b070b54000d065400f1400501ca101c44160008035214000c0c041c081d580c80c1040107444c001c4941b03803600308000f8100394440f042c1741001818 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 192697149 1250 192695899 192695927
    0x20c0c15070312020a09080303101a0408031602010e030f07031a0c031503010b06120912030c0d15170607180b07021201060302041b090501030c080403081b19020705190303 75
    0x1b0200340c00164000e410801188240d55100d1604106464440c0b07001c01c1d11078400c0e910000c2d207000c0c0000d00c5100300000030355805078001181c0742c000c03170903d0005981507010f035021280c0502480741240341d48440000c061045900c42da1314003015141722061844207840603076064480a004101003416407a2400c41005c01e000028000501380310072070001603066200f842000c3c0341c05014001c000b05040180019514541c003026003603c2d51401000005051080d4410075410641d5021f103200b4040b42c0303202c6140075044020072196091900b0b0303000c2d640c1d09030031240d000c00075001585041001100303024010440e0141a0210b0420015500b040391480d00024042c00360741d171383c3d40008050381e1540640034845040c2c0031030b0100c4480c641c100030000d00940d0010703030502d42012000c014103540548a141e00c2a09441d1030084c41d182c084030a420800e03030101800d07400d14040360350060996865503c5078003c25603001c8034415a584c5050000c4003a83e890886a4042c4000003040824040d09001021907 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 192698399 1250 192697149 192697157
    0x61203081e01180e0309090606280c120e03060109020705120a030207051504030806060306010210050f0105031e1b1504030f1a06030a060c03020d020c0c15070312020a 73
    0x18580703200e408080700360f100032440307407001c08141e4411145204440c20241d0041c05140ba00074000003181d10742c9009080c0a01842c40014520520707a5004d8105164540c000c03400c2807403070340c034001c01002d916128100b91105408075078403003651801004c3c00030301203401a025200cd68070380614800250810481901d080c0140b10032980001400401480a0009a00c006843e4100e600740a441e00103000504102c6d1048102800086078001030b034142e20a10071610741d540c980d0342400403814580c0c2410b41224840c01e002c1403000e140d140324001416900203404a600054500620925031841258500c1890f001403e9002948016284402c20003030090040442408480c1c50541e4603170141c0c0c42640c8030010818a1810440101c022903101c82d44422020050700700880001d03168112014024030b0255900d110001c541d010f501a01e0b10704141040454603400113541c641d803500503544100e4841c01c00c000b1905107a41c54182958038098040d5a21600240340040142c000e41c0807042c0007043c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 192699649 1250 192698399 192698431
    0x10b0a0203160b0403020d050307050d090f021327080d0507020f030403080d1104051c1b09021e1303060b030a0c03060e0c010207060c021c0b01061d010306120308 71
    0x80a0031a8121106500ca84402e80e0f6629150400a04042d1500c10038410040704005100d041603014065131080c5603204c178000f0f000041880c001040001024000f074005820b00c82548815500e0780c0304c030042110258200c201d0304882d00200300c21081049008044060500c142c200c13031502d5601c20b42c1d000e04a0300444810080302100e0601d140c000e5030003142c1ca54000116002860258021b080d10700c0710f50a1014101420030000465a038010030388860361340080c101c5c40f0248404510a9031701e100c60b5482c055030591300d500340640a50b0110b80c005040340b8000d4024043c11000c0340c125102070140c05685d84071542565034140250018199940d454410047c185021030200600344004511403600020000d1040303d0301030405000440250541d009450b0404c41d2a801c641d1181d0025030440e2142c031100e50705407895420300c581640c0600300701282000414050342003982c44240c20403d8400c0d4192203000c0c4011030954208c0c3c080e000308180d00e4041c0f5000680240c1c039494101003024911800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 192700899 1250 192699649 192699667
    0x906090d051c030c0807030207030207090e0705190308031902040305060f06090f040b0117070b120f0f01080705091503060a06060f0305090601140102070801020703051804020c06010b0a0203 83
    0x2084001810940702a000b9509100d8050078911540d0303121000e50405000c00351080d00003410304c1c140181908180750300000c3c14810184240503820242c403070b50104000e01c0c0000c00c1c20359a50801400b44a000c3d207110302030001c4001c42d07600310382e044903409a0018510341c1d843c94444200788031030445016240d0280000b000151050014520481c811030b0346c00194a0400108000c4080240c2504400410700092001050f20846803d042d00c6810804a000c0008140a28a040c0d200ea025a054940104409003003800c980c220501a0343d82c81c44201207034441c020708407041107007072186801682c0940d0041095003041d030846030f4410b000c402080740c1f205403c400300c1c0c01c040741207408204599480b0340900c0810703040022010500304a150070000d9250016403d03644040c180601d02c410f480708914400280e10030000c90028005030320080d07440744002c1c60068115004852110007242e0170b0501c81481c0c2c2020b100741c80300500950010111a407800b48415a16800b805090046010401285e29 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 192702149 1250 192700899 192700909
    0x2120705071e030c060c08160518061621051804020f030f0105011e091202030309060c1605040209010e0f0a09060807090f0e061f030b0108160807050a030602090609 72
    0x40b00b03900a407683d9054004910b480c0341190380d0001c80c0002d1000c103905000da03c2084d0311081d441d2030703c2414915511070000c9411200b040020f90581d0707101c1c02c00920010042e40001044810300d2003585541d5412070a050340e0590301403650100350004606214031451401511503400b16180050001840e03c1c04d40040c1c00302da513000311500700d40c03541808010032481d41d024682040d6658201010f40401300700c41d03001403405c0040c4c41041d10b100040b00c440340039540e00f803044a109240003011113a5501040d500b160700d81e0103820100180d071502040c00241420240200c070510321050352031f580c0e1140d4003010407070514010302c0d2140c0c01411103540403540111502c04e190203841014024585140380140354000c0d520000c030084402801d28450a0041900040f002d41000c00e15210070f00035001d080b1a0407184010b907101412520b0f00e44000556540045a40464403440003644184691180790f0340380e0310f0069106240e08849811020008600390340c1c058102450020203841c5000b0702080007031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 192703399 1250 192702149 192702203
    0x10519200c030703110705060f1305120f07050d03120f1b030b2e050f09090109061508010311040209040f05040c06090e040f02211518010212070507 65
    0x20180d60710000303d0409040c1c0000a0b180c8a40c0c018004144880c1031501003071583c02154140b003000d400214000300d10701a550005006440d018107017001240c61130000c1e643d1004004000f060380e010b180c0e00070034281094031940c42900c1d0141c80f201c1e074000401d8002c1300105081035629150650341c100104045068900d035202d4210b455402080b0f1010b50f10401503101e101000001701c0182080024000412944103181150f00381e0400302d490392000010809188202040d81c0d50214045001150402d12580110103480070240c80b8452085021070589a411080c00041d00d40c404061070f045261030305800a24440c40042e04c0440c0112450318000190340007aa0b084074104601d900501142d0b40c032840d9080141030750140500c03903051030f80b41c48071000100c5e04040e00070b00301600b400e040d07042da180d08084000880422600451064240050400c0c001c3e030308a00040200d1004039000c00e0b05000344c038140313480e8074207070122500e40b030f00c0c15149680a0001242d403030112000c400e02400b4501d80c20 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 192704649 1250 192703399 192703417
    0x5060a0203150d022b240b030c09060907050702150306040e031602011202040b0310090e070302010219031e08040317010e061e040e0a0b010801051920 66
    0x158480c14192000807811006030b0700a405480b858004901580e251200010107040121006000b80d03d912843c18203e44800005460b0807210b5015468040c2194480307210f40740f6480003046400d48000425480d40031002e00503510100c12070110f4054505401802c2c0c22001030b0400900e80704c848d03800b091039140380116401c060745001c410000329041030301071013a002c01104084d40c40c044401c1f40c0c1507070f07042e08514081d04001c0c12080507054104244d040710f0150090361002a1a4500196444405603050055801940c140000c51292040000b070740003e4a1b8140c004d40207880070300700301486c10680d1030015410040d80c1c1c1229014030903001d034a9601080e042c0e42d101024034080c08c002c4c1c042101c2c10380304102c01c00a03500410000040d01c080b01e410000c1201c0700008407681580c030329640005180159070052901004400c50b03280010030074540f034800c0820901582e42d5040041c200d60b02120505030001003800040d2a851040d8440000010040c0c50000c600d4034038140d2400e250404400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 192705899 1250 192704649 192704651
    0xc030f030d051b030406110403020a0e041205041401050c030909040309080706050a0509060901020f19020f0901060504031e480b070203010e06070305060a08071a03040f05060a 77
    0x9603a101d5407481c01090f41c0250240080d1007500a80d090082140c4001000509150340d20207240300784180071804c850045400408880000381c40b225103000e032004c2501d003121441780d404007161825000740260b5003100c20500020f00180843e4005451503440f41600d050a030204211030b171340e903a039444e001e240514041d5840c0754820f0f0a1401451030700140703410100521005002490300a5072040c1102c010312029240075888210090050703181c00805007114006000d506229010604480d456800c514000c1700c454500e402c0d0701301400f4013803070f0030300036000040c5003003100388045100e103907d41041041c40030000c24031101540b07a00780540003c3d5041c800104249980008580300c1c91011000410100340103045441d03078564985c0f60000d140f1801c41a00c00c00300d140fa0565400b98020444100355100380d600318501040001c0003014100d480a110350082c3c007002c2442c84002801500356004c0c01884c04406e151404441199000240101c0e4500a07442c0b154002a0040c00003d00454800704 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 192707149 1250 192705899 192705907
    0xf0d020a02061509070c020609150901030c0512010b070f050f0106052704020f06040e0109091209080d0e041d0c01030501060c05100905010e0a030f0e1e040b030c030f03 74
    0x100a04090000d09102d1a051030141c1e031401680e221131019810011341c0c1441c2d881c20080f4408107038140200003090368402060301c440060041501d00401b04940c0c00da904218040d04020705231010300954084d0072054216038010302c00410890000c000e0385000c0c9404410300c5281c0e5032820b2610111000e980d8650f510345108100c2c60411020002d40481100e840c6501c550030b82d060383d03803400341c0213002038410404280c01c90740640301e0707408850250011211004ca42e40c1c541c24500080c01047c10222051f0f40882c145400c4180301e8200031040d02e014101522102c0408041202c40852071440281c0c4aa5525401c000314826554441281c0715044060001040484009804c80d84140d02550611a1032840b190005001040d070b0010394600d002c0005d408402401d029006003c0c49a4242c0381d880f8106c503900906402503069880c0c1246681d807424201136070024003078401022440d050700b0040e14902c02400f4540b81d0000056104064111000880d4090010749025180d12007640c0d50b8000003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 192708399 1250 192707149 192707167
    0x2030904060f031a1512010e060c071a04020609041e0b091b0f12070504030c140d080903010f020f040f05030a08160303060e1806070e100c06020f0d02 66
    0x1c05840300030000c45031901601e81c0b45840f0b0303c800607080d07501382c1114159840010701c4644440c4008444040142010410703584c0024220f0084c2035404c0d02d41e01034414500040c8642d08000c0441300c0840c0d200000e1040d0200c144107400304904c014000b2603004005226100b0161154400d84039555070b205c031001064802844001d045419030080640070301440001c02100e0344002c05000c92400b01503588a5442a86901242190043c100d01441c4800240148410f00390b10501034010780340210164032050359640500142c141145c00140d0300540780c072220101144800d005080501d2014001240c01e0601400b20400c0f80d000000c0008880b03004502800071202198001d8082c1c4020b03402060014016143c030714090151301700423000708410175034900c10184a500410b00404e180c1d9580c2005060116007524440c140380c0700141640710315400a211144101041c0440c00f00141003c0a00003060070200c0c0d4034107038420300313603030207038081102480340aa020010001000d0209005032180400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 192709649 1250 192708399 192708401
    0x308250f030b0301060e01061b05011104150302071a0601050c01060e090d0203121506040306020a020d111605091e04060e0d0215131403120108010605010c0305030a020a09080304030302030904 84
    0x4004120f01a03850150700340020500c0c0000300f8103507082e0341003100c0b1904d05121440340030020008010007550a0020308201c1030750000c00f5000707071091104000d010b800000c03811000c074003400b03038043e14280707108582019070384401ca80c2d03542103001031411920308030106450f18250b07802a40491480c3c0e02c06000c2201604081c08415414403091020310320f044000c16a0221650001e040d840070004840391b680210f560b1901124011503111000b551194802c0d04c0194640f4410422203003c100c5410200405400c0818801844170301075854203020390030201442520381006101c01980c5410040718a510030321050407074070982c031406c4040b6003084042801ca0400c81c4d4220350505560125440380e90f031800043c107455003d42981d144030784102150514801c1070030119011030301c5020019072806021410b0303682a041e02d100100038000f850b501c80046405889114010307000076420310200c2c4141d002500240650340c800d140c17500089480c0c01c002801c40d071140d48114050307403002410700100d00706 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 192710899 1250 192709649 192709661
    0x20c010e0d020d0c261902030a09090506090a050903090418060e0708060a0b03010207020907081b09010212070c03020a0e010305060106020109020d0602070201200a030914030a0308250f03 82
    0x9403130501012000340d60743d5524031800a80380e0351003141184940065480f08402d490080142100d104180342407000044d49a07846000703103000140f03c0800c04100307900240103050040030058812641555503080c40340040c44007074a498005c1c0000c004088803680c0328050005000e0102801007642d0074940790440c1140d402d02040852600800c80800000102280d1103502c048019008a40c02100000081c02807203090300095000b400f241c14440925401902244211010011001004040403a0500c9030240499032030040e031058203c0e2401b00e25020180000902c038070840101d158507071f4000f404007a00d580120b0030b841003000040050040c100b01407030040403907000800c00d4200ca50049900d80f0031070304010f88081d800103012811a4412452002000c031240c00004008420790030f0561241c11888003917002444451011038104107030049242c1c59080140246030a03103580c1c0e030554251100070050540003c507511200216802e4a40040c50364140d55101021007001100c0a421a42 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 192712149 1250 192710899 192710923
    0x908060610020a03050d06180507030e0a0203030a0c020a030203071202190302060415050903101a0105030609160908120409060b21090c041104060f1103090103020d020c010e0d02 78
    0x480391a00e9640035008100e080681d501403900690f195403206ca80b40252045500a06198020700703074089084807142e202d980101c103140d90600014022a15041e41c48a0409000c3d41c10307002000010300f4240151b6144114500c06450100d000c1c2c0d03039800280c00c000c216070191030701200c103501c034600714034080001900d520350f0094030004060554000c0b5000b4003481c000c1d0540c91041d4502d5410701809081510b894603801011141402c09070b0013600064810189103891742d0001f000d4805040d03005400346c902c02c11000d81144015a2043d0038118a40380742c00310802030081822010541110a024100400040656007540da5150626002c1112500ea0001001c11001c2c816152050040000d030740958034410401c410a80b40c40a00a0505d00484401035229160400003518141900302600440e096500c81810104201d481540c400d200400080c5158000f040700e00e5456000b0f5014284004c0407000050401a0056004c0e00b100c1c100004644983d01542100264560402440e54006 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 192713399 1250 192712149 192712159
    0x509040b1e0405090a0f060513020d12020f010605150702010309020a09061e030308040f11030a0c08011104050130021804050a0e032d031008070617190b1009080606 72
    0x8415140d9000406d608400180000e8481012680300c00e0400d03000007900d0b0b0010400d085400c600e10301050b00c41d042c0d40101e8098005c10180428525040c45070000319200076210162180c1034803416940c1d98405403040b410b141d500c0b09044c000d62217031f154005c0a0030072007000003030b2681403d18a100b81e0008001b450145580d4000500000781c1c1301081607000703030307028140119036145850a4080701c001c803000103806219445541043c00300d0b00149070100e500302c400800c02800000c030381e02a10300c59406140d01050540080d05e415072050348600c00d40141c0e2029024a56004220340426a03005840c0d50000c080b14200c5c542c40c5282920070390303811061000c1d04100c0c1004071a2450b8076130086a14804c109440c080d8070003040d0321a945000810310100215507640d00d42407452061800d158044d04c00700b07204140c1e012840d140104e000141c5010741c40c40c204110740d503030700003125080c101e140c4170180d85883e031455443e15151910740100240943d203521b54280d0070b083c0d40b46c1c509400100380c0c0d0301c21 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 192714649 1250 192713399 192713413
    0xf06050f150c3009010c020f1f030c030b0a050906210613031d09010504111204081207090b0712020307050f0601080c010c11060304021f0c030e03030307020d0509040b1e040509 77
    0x503030700480000301e4594140d4018420000711230015108000d6100c160420340341034280501940e905a01c0340a904089840820a25004105101c20100c250183c2c81d001441c1034003003116813600344016540800114003044140103c10141c07800c3c144241c4032070741c0d4420082e1031030080580009d4141680c40410500c00c003004401030004003032074811720510380940c0e81d406541407018141c07002c032400d5a5040d00c1c0d008540c2000e01e00000c059120303d54161107031403024003181100e031007040c0c02c100300c55071040c0c800d06003045616842015070350304840381e0540c0310030483c040000348180080a0751558082c003410302c662401240b141402c040d80400c9041006010104c00010000390a000000400f500e01c1500c0351355a1000c2440c02c511250341810140b00c0b000d038440c042c0c0d44540c510b54154032a43c0c45840840100c0305260362404160383c0840960441e8840f1200c00b8402c02c00b45c80c0302c003002440803070700c042840f0104000b608001a6611110620b0107145a00d0416024854005140c0d500810352 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 192715899 1250 192714649 192714667
    0x613091b080f06031b060f160605060a0b09040b0a053307081c0b1201090201020d0804050312040c0b0f03090c030703030f030207060b04060e0702010f06050f150c30 72
    0x31414400c3ca8101d80e458500c3e64015907484d246e043d0390b0032090100c4401d50fa40c240060b92103038180454400c80d1000d00300b500180c01e50a010382050200c03908007000ca420401104200800743c110b8442c01070b00540c1511001032036070344a880c00c0038602d00041c10071200005141c0c0b42d5410b40c201c2d19180c1d102141c108000340000e0031900464020340d15142c0c44a800460100311540a850240c20240d8080c1411242c0c1d4103485065002800c15407007602120414100588251459441118040c007590818030200d407141c250303500d500f85d110f841044220181074484100d40010b40100c91914a0303000c01000700400710b50200402c0ca50503808030014410386155540044c01428040855404c0640104204003005410340100c101154028410b104c069280c02031030a28802c101c80761801176003001c2a00381da00c2c07114843c21069a17000f81c500c088100c440e008dc85902c11040a2150b002c0c1004c1090407040101808103c075844081200a0015160003e00240c10714100e0800c1003042d00401c40b100f5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 192717149 1250 192715899 192715903
    0x906010f09051908033004020a050907020120040501090b040e010b0d0b03030a08040b07080f010510020a0b091c020102032a0d0c0201051b040e0103020613091b080f0603 74
    0x1101c00803610200c3d1a004078825591510859100c1c0d4842c1c8008181342242000041a4007180c0c1e900a0800c03000c03103030011005032041801e071401703034118220300d90600c0f06007010016158062042c0c0004a4910003031544118030f01d036494064100320002003010700542d070f0700c0000640184141d844907400d00d030a115a808102c2e5041c0300d9603004050014003213a400d221500031060b000c10050a03aa00c4a50503000235290710812070301110002040400544941c1c052607880d80114041c6995035540c1c1e0900c0284400b2100d400448802d500c00d08501c10001580041c00c640f1805170127028080a0450300101105c84140640038815640140b04006840441001c08003504003881c401d2441251044c601c2e03102d91152007075640c3c4860800c0d0420341c0c890340540000b80188008584110704c2011100b200c16580074500411001c000e40390010005454007034060190341441484003108aa6294812001c070380e00880880d0310b400541c0031400b521900718200331380c0110341100703c0401c0c1c5003050001c0d0b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 192718399 1250 192717149 192717167
    0x906090b09070c050f071517130303020a02070b0301091a030f0a120e030d08060102070906030b040b04020f09130201080a05010621020c16090b011407031d060a0c020906010f 76
    0x102c10031100c02d021205000c4200002e10a484d400c0043e40c07840c644505421250721081055003000c85c181400c4c0b080e080c0c0e000d000e00c51140b044268070605000c96a03030110003940c02181400c0c11480703a00070110700d0b90740c01c900544c02802c0710440069a03c9900010301c4c5454008170741035101790060f0000e000c02c24400b04810609503408070010384211500107040d6104a800c0d02119010b10689101d14a006d400c0006280600c80903000c596996581d09410003c0e2416070000405102c41c8001040c005032040100b5078000740f00500c1484030050102c04260a008221007030318060f001540d28400355601301d40310a4100c0034a85c82845603604140c2c01905c0a40042ca000b4404480c041b80304201030240c0c4d0541e0028100d44081c0da20009079000000319803a21801601c60b44d07840e03c0c0e115003d56002d114204226401c0b400500d080003850b450035586050801c3c2441c56080c0801d07650a0f9950b035220080101c0e40c0c20340c43e0f504d9000b5060040c1305140d540103090606002503041c0c4c60b00c0294104500c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 192719649 1250 192718399 192718411
    0x405060d020f12090604200a030305090a090c08011a040b070b0405010e03031e09010c08070503070e090703021b060606030a0b0105070615060f080c1c0209090705040906090b09 77
    0x140e540d0307442c0c0300800c8680c410901e1802000c480001803100c200381c00b2854074051402110200200c400c81c140c001d40310662007a46035407160b040c820400000e8051000b62039207403c000d014403540c541e55100002556000716800000501110051203003102c0c1050307036282107402e4450715080508200701c0040328880d560010f40100c80b140700150800900350045100750541034140c0c1d880341840300302062242d201c1c1c8074204441c3d85080000d00c00c18014828004800041d03910340781903844802c4207441640c4054644c40801c1200c1c0d0760f2154a45940065038011202c0355001a541c24608050885410206036882c41e19000101400318950300c1030140c0350807080380040000d1a262000040e100c920500200a040a04006080b080c410400c00704904864154999401403076031a042180c401d1344c00c44890640031001d02c4840c1102254071040c8003c055201070045c81c042244000587e500c03c22511040010b00008080c031140e1160b00403040141180c2c0414001d02040d1f000095203850001c0c48 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 192720899 1250 192719649 192719651
    0x20607020a0305250c0f080c13051009020a02060106080c1e0d0e01060810050f1e060406031421040305060a020705031c0506040b09010501020d03090809061803010f020405060d 77
    0x140b1401c0d40c0704030649070513403840c0543d819448000d5142c030038480e02d05440740d20008a0aa1300c000340e011808a010310521074002e2030400182a480c042c94003c21001e084070540018041c80415081403900c01002e903000660000e007642d600d0010001e1100c440148581d203902c0040c48031071943d4a5132034900d404804a02d0046440380c0140d028640103000034501c225142d0f007000c20000b071000003c560b80030900781843c41449156503001100b20745410a4400b21000b52144484210b003221408406400c440e0051020906580e42d40f00c038011003180210400c0c2c65040081c0319a0007040791101c1e1045d004c07110010300c1c2060302d10f44886458000082800840390740028040c010000300f0b200700c0d03107242400d494020030610004581001000c0441d0094000d034542282081c030341c41c14441080c1280d00590003071190202943e000c402800c0401c0c0c04680040d810700803112580d03105070107803442c0aa0b546000e804480103008140c2501e06810f00700e2081c80c8100000e001c0d44d241c50080350149152050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 192722149 1250 192720899 192720907
    0x6060f0609030d03200f0702040b0d02090c03190203160e040c020c120102041706010317270a0e090f15090706180806010f080c0301112502130e060106020607020a0305 73
    0x144008140654801d2200c0c5c44d400000c080802c61110310282c500c207802901d007040075903040b1041c000c10b802c0301070000e503004000d40c00003500c60b2034400c01994000c0c800c0c0300c025425502080048140c0e002a218141c1c1480b2031021021103540c045ca148801860407501800703080e4603c24080d44a108160406000fa011340580e111180000d40442e0010002c8141c8585840500c81d6110f48821007800121030703014100035101807000c218010b4850b04000001049040400c84e148618032402c120f20141c0c0203102e000d8001001c142c22000e240c840d90425010f84102980340300c4540c00c064400e0030080c220b6000702c00340400c4800005001091f01c43c0750030865044941594031071655850399201d1701e520301c551000810031942000c60381c01100c1010303044824607039405040500342c54420841e02030641d014000030102c20308401d01c0042d001080f0820740204803585d004924000040703042d0101c1307181c41c7d41100c985c1c0b50003048058010075181c40649201d080a400003034940203c2030380641040b5000c6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 192723399 1250 192722149 192722171
    0x10b0906060301050d260c060c0a0905130f050109020c0c0a0305071401050c0d12060b090d020112020913022a0304052106090c010e010302070308010302210a0506060f0609030d03 78
    0x707035207980071240c82d4010b01c15108001115a980e87d02258140246001d2100482c056003115002d482c3e9030502520340040c46400c0c10284101415958200003140d900c6415a020302540e501c60076019218401000d40c1d41e4409a854038030f444040c10180b8015070080c0320130070100e03102248032415502c502c86568a1610000012980c50099002400b4075000300f10290380c029411000100308004028424070550740d0318214a051405011b003c590401110b01c003500c01984a4840c1c150500b1141100500302400400800d40c082c10440709815920f03170000310518515402d0000e64113101b005007a204101500c01c044a44901403889841e000b008110308118402901802d040da0f003524030412030744d5601d81000001d69400340c15204a0108199005002d030551203070007190412600340c1c0740c80c3c200380d04c1c0d0780c00c2c03203a585001d41c15400404503024502e0944d01091040c0391b0424041c00080c0120b050100030019054030100c2428481d410070400b01070782f03480214038002c01c0c2c00c05043c00982600d000d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 192724649 1250 192723399 192723413
    0x2010e013009080a020a0203060c030f160909020a0509120348030310080d0e150d0501030305031014010c0605040507150c030905030304080307021002070e0f09010b0906060301050d 79
    0x211100601110020406624143d80082d01401e46c074001c4049a105d03482e125000d045620081d6101941daa41f038100003003040280d400d10000c128010300e4520030340c0b69101e010004903006020034030300052001801c52528541036151101188071540514609131644821031140c80e00385030050510018900c03c0e401d940103503800030f4548184240c06a0080712032044040e141d5008441b4080c0c0c207980d858002c9211100014844444c18494885180e111440710820140b80c203d41040310700c584081100030700c249403d0007618002c5200361034007a01c0e818a00d20b44004902150420303180c50030f54a1528031280c3e03000d0b4281c2c28013138102d6800074081c0c07154140385051902c950090b080c003031140d10109510690280c1c25020150195645905082c1c40b5001c043e00c038425481419403a0b0300612074040580b6101098034210303025801210081c1c2d03980ca19800b15400b049429800300c101071001c10683c98000e0203280041e6100b258120340c0c13450940002600d0340018000d4500030001b0042c03000c02c0000c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 192725899 1250 192724649 192724661
    0x6310b010810050d1214031819050c1c141f1103130f020a080610050916110f070609060e010c030804060513050a06061502070f090c090510030902010e0130 68
    0x406c000382e5501e280410070101c40740304000b40e070500c6105500a03058440b0001c540100829800400780c040c54403602e041205054007031003082040c203018038000d4006102204034009c0741c8009000b80c050708124002408c0c800c51030490706400d041c00c142040c41d200c41c3c000b080340e502c064006d100240264990900d00c11030384150400940106a9000102c0d078985e0005066101c1d50010b403548007440d40b10814450482c1081e5042420a104c08172500c100c030b80502400c440840c8400c041358030400c2040c0c565440c6ca506940306402050b1048018083c496000c040d00d00c840300c003800c216075103040c6941e004210304c10040c40030740215030b10804a0820b0002d90b442104187e044000c032780c603c0c0d03d1410094000d00c124410340050320b00000794440190f00100b403c01c112243d80c0200c0e141c451500080502034510349196204001454101003280d6071804811256524559400a00390741e15200241c00f4442c03101c841d5042c40400180c101c4584185c010701400600c2032445040c000c55580f00d80009050 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 192727149 1250 192725899 192725927
    0x5040302030f0a1506051c11210706051c0b1504030606180b01051b0109020d061a0906210a02150316030203040b06310b010810050d12 59
    0xd841c20140e142e1000040da0410a8025804803903205030203140c01d13080390360360305c10fa90300f00e4a4180c0c17007111904403034044042540142101c14034002d900300041c8141c074810800c003803240150700520b8140e143c00c00405c400b0f01400d00b822032400d005c000028145042d41c3c01c4007514503480b14a82035840d01d814401114045190800702e448580341d20345a006807089001e401d09140031420342000e901d1301030050305503000c810307100d4628103120100010800110344124581e959210254000140c0701c003a911081c19004010000e010041003c1d42c030a100030280d04940305415040c180080b0fa62849490080c80046031360482030500100c00d072a04055829034040d600060a050303880c400c84584004500c95220300010301680d00078007809604a0100740c6014003c4000381000801d01c6c1003102070701103c0c003a0a040c41900c074000d403d030041030300141e40c4007180c0d840e2a400c0103552542c001024a4202e01c191480203209800c0a0200c5d0b4210b03d600e0000c0c12240c12003200040c01801120903c4d01fa003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 192728399 1250 192727149 192727153
    0xa0209090c0705161514160b040609080703110606040510090c0e041b090602070f090b0f040f020a02010b030601051f11030c0102132103030b01050f04030c080d090f05060304030504030203 82
    0x1d596038060342d030f6040250068402280c6c0f582c415542c1800b070744e03044400c2114881000d01c2d25501076200e0001004000780200c1e265503480525401003840324019101c3c151095840f0988240b0f00a080c40c10083c3c060680b500490610301440040c821b503d00000c241c80724800f0001e240241350804888030501c50b610700380c005160285070307800c00062003540c4084260546070014010795800040fa80e0b04180d00c03d4640000c4924401d204078182a04282066007000301101d10010f0040c0014003101c0030b00c1c820140c09540015184000303074081c040c500d4185c0c0203c02a091540c074000c041424820825410083e51007000043d6030303068011011420085507010803691900c103202100f50003940711500440340e03104210b20020300c03020340d11110750102c40c40c08615010710724103075420b0b8050900c100c80da078140071040c400e80c1c0401601d1405000150702442c0810001407600b2405418075483d030007908204000c80500f405040080c003400350171140d0036034120755243d445040442d420b01568000030343c54 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 192729649 1250 192728399 192728443
    0x170c100603080a081608130303020d050a05040212010207020114033705130302030d05150d0515010501050a020618030d02030901020a02010b0303040810230c0409050a0209090c0705 79
    0x100c640940506090810b81c1c40d00121030700c8081003041c1c02c4080380300700c05c0014600c02c0010300c60340b0301c1c4900066003442070034094200b009044124080e124200c40340d07040d242e9544100015441c2c010074140803030f17144200851401900d0740009100103c5211000c0f4040702c0000410048143c400f900c10817146610b060700b100000c0039003988210b45004c3e104034481d42c00c05001c915003020018681c07102c240c1c1074008514001c011884440a03080c010800350b03c030341c0c1c0d02c1c0e02d451640d1166404940c082d031180c400b501c011b402c0c0004420b01010706820042c100003080c0024001207400042e07454008020f02e1440040481c3d40005514612030403d4855066001005000e12800150060600700700c203038009200b141410020b15950b8044c511480d102944a81044c04500e040f0354400e24014100e9410940c2c02c0c02e02d050340844840341580d004482c808005410420b1103d1442032070741003100444154a4000440f0000701c183c1009002d00480b04000581c9504102d41004402c01c1c65501078065014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 192730899 1250 192729649 192729653
    0x12060d02040c21060b030105090907090c0c03181a0d0b0d0c0503210d0e01020c07060206040b100506070b130b04060b0f1504060e0a030b15120a170c100603 68
    0x1804900d480e480712110512001004484e0207000103540c0301219003419607107071804000207654050646201401814408034111307510740107000007007644d52207964200a580c90024500c4001c90303203041401c41209824007180d22140b80081000d642d400d0b1450300c43c59104c410100500c030090025134020303000f01c410000c01c03103902e4000b011a8002c50a503880e107120212010500c40c21400303940702c06002048148a00310f550b43c062024899072200050806c490040341501d404065013000300503901040402042000c1204041e601890407003c00c8119484d290104080b8010088028290350b61080026480010707840b0014805401007002101c90800e030406000900074540c00d60300882007180202451b041484c40741c0c254009140101d490145032440484100712071198982e4000310003030f00040454000300e14540506088150100f00b56200c41c00c2020450201c0c410300b03100d400040501d030218040003148500e010801c0d045a96071444070060a0904943d187c5c6510001e24041022003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 192732149 1250 192730899 192730907
    0x8030a03140112020306060405090a02130906050106050c1506012f0f0c010813020a0e01030b0105011b021807030e0d030f050f0907030f0302030d0513020a090209010512060d02040c 79
    0x10755146080e450300e441d40d890b45406400700c0c8200c00c0c040d426030701c0304010130114145984a07983c040002c1f000d48902c4441c0b030340081c1c4440d40f1100c1e140001341d00c41d07406105110796172007a6801031001d41420751400f00003040c095120128000780c4175580c0789c1c0d0000200c0c6030740119180c400d0088102c01e407142000382c0c28003404004102c0c5056100c5032003180000e00c1842e000080c03c0f0002a41612004031940c0e640005600c01e28450700220b80100d0b1400001034440207140030719010b544181c09600340c940c18000014000f00a016801e807001c128203904a001d40c850f02d80c0c244040180b1081d2006943e00d8220a90140c400c0c2c4a44103401d00ca000f0682c81880c0d4507500152103840c4082c1c0c1030000b5240c2081c0c407602c1c280c05981d82603035a0031900b02007001410050b24240894801d00580c0d0402840340010030403074104849016400701021106d40071860324050f0074000c0c0c108003030114201502000020041d0003155090420111000045502a91078680b20151107034000c0050001e100c014400034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 192733399 1250 192732149 192732161
    0xb0304060e0d02010c0c020609030a081908070804020d1b0f06090807050f092403030414010e0111030306040b01020a05030d02120c030105010c021507050d02061006030e1903050408030a03 82
    0x2032824091140c0840d802c62040c0a1103103d0f420030354036200305440c5502040020780c8041f08856040c82010341010000381494054103a0040044000340d4528134000080c00300c1400038412410000e103981000016600e481a400c1e01603003043c0b0800d4141110300070f072007012003950082e416400060303100013821580f0181d03d1082d5188881030f550a1565002440010480b40d18400d91000d00700c0700203102404d06589400b009400040c5041d40f03400e03a540464210f5200790060309144407001005007103541c0029540320703020b0084c80c11010b562440b0400b55101c1c00040c180520542e1034841004140e842040703618681a009000e41e981d5210203402c0070020742c48450705140304808917001825041d18081524100d40043e150341e02101c0240e0300700151001c40102c040140c074001e2180001081c0b08000c0080ca04005400070b01c00c42c1003100104420000f00d5101b403007054180011010900c0340400c42c181a02c0219030030701d140c107001e4603060b14640100c1d00b20580a10012501c240c040d90f158003c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 192734649 1250 192733399 192733421
    0x170103081c05060a050d0c17070e07083d0e0106030b1212030a09081c050901020c1f02040305030a0201020403120c0201020309091b0406080a0c0801240203040b030406 73
    0x21900d512900908a010780d0000c035403c0e544903107004003c200178103146244104181c4502e801d03ca1054440300c1029690021000034a016030201405220b081c00034510345030000c009040c031110f1450010b155443d07800d90b035100d1410764454041d000722404130842150303006000c01250404240d4071400c0621080307009114000000342060102d00c0c1506001e00400417035201200075096044400462840640c00944485001c655492184020a6180c0050201c0b40c0312100040321101d1002f0218068440c060550b0300706034810041e817408072030000381001c0011900c000038107090000307086600090003954805400350200061006101d60b040d402002a00d114100b0359003c00070f1560100c412600142c8000e001da8810405200170303203401c18280b43d0000b090426051466102d1441310b40a8116912510110703074108240010b100c03050180c140c0c0044a23144c444010340c0f401c6d40324000746200c515400264002850b50a43d041c0c0300384120340291000c1e50f80281c0d84e0400d40f4150004000160310 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 192735899 1250 192734649 192734677
    0x708030f0c190302070e07051603050a0801170a02120309041508060f0c0406230408010b010813020102120307050403050604122309040e0f0d0e091e0c0a17010308 71
    0x1061100b00984809401880e0075500a01016003401000301c1255006804142889402e00500180b54441c00009480c2c602c2540d40c552034403e071102c054100b03001038101c1c0c101d040006210020340000011040b00c02a01243c01200c120310b4500302c00e0542c42036032402b6130403504103401854810f0140206100712403a8800701d4409548082442c40702c0c00044c2c40c021a4442c04000c1000305900c2007118800801040304410441d036444100700009910980c480003259441e140c0e60040d940c1c1140015a01c11014940c00010744400e60000391640781c00d03d40321180201c04008101d8036807240c070658000c1e55201017140c1da00d00f4030f1705045115411100107080080c0c0c0307a002c03c40380c400740121000d000c08406480142842c0e03072102000054200348181c120f091152540c0c80300d000404018070341c00b40c070040c0c03a40c0440c07528140c1441050280282880780c019200f04610055010402d1802d40c0000c1c903214694423065081c50460745030882c1c401e15150002e68000204c184a1408010840c109180607 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 192737149 1250 192735899 192735913
    0x1005040b12160309020f040902060904150614040302030303042a061e030b0307180f0515011e080105010c0c031a06010801050d05060f04170f04060806010507021e01020708030f0c 78
    0x21003c4d1191500000d4000c2c515100d503c04604194021011403880102a01e080030070801c00318007281c1c0c0103c0800d0b60340707800c64010008181c00c0420020b419001c0400545007130f065401182d940d00c4064030060034200b1402800130480868100a0100919610400032181e55614018404000d580b0f030404400c005c5040c10030040c0c064422541c00350009000f0341a4607190550044c2001140f9500a401c6038581007540d071443c03894414030781b05108004183e011019524001040844c440223170403110781d0750110290304142c0002c905811a00246440724001c09645400c00d4104103950000b018050030346400c80c003141d565800c451103291700f0307666a85035a036968208000c0b0580d03260090160741000010441c0c500740f00948581c060302030101a800d100c50940500c0f00c5920400d02c24034124030101d41804100d45c040700321703500a94246406c82c01c03c441900054407144050254004040d000081b82610f170b4000e11020001780414410381c2c1e05d400740d0258124041c2d0000c1c825040e20b0090790303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 192738399 1250 192737149 192737191
    0x8011a06071a07050d0c0818161208160302010c03050a05010b0f07020303041a03190b0603070302160605131e320313080d1d1005040b12 60
    0x8415648081e4101c0d8181c2d00399001d51500c500c100002421a4081100030000d2980034642402810300400541c1d407280c00600d07200c1640716204075810140b17140c1e5000b0040c022020112901c268058400302c0c803004500341001d284c00c4a142c411316100186a44490941d41e0034103070107601c0b200e071a007400c1d20288000c0d5220302c2c805040f00e4003405070b4070f024441440f0b0044541e01c16000707000b00703600c0681101d1910b600d501c0e6078400d160300c0790145003002c030000040003034400c840d07a804003241b107001034217120114282c0006591404005c10f24400c040d408164260103d50a14070200d206810010402240c20584107402800410040c280c58480c805050a0440b11a040c401c0107416000140707035801c214800c1102c00342034005480315541000c1a00843c05c00c2c881400100340c41100160302820707691a150b0b00c4c1c2d003010200c0c40000240201a4030480e09003c401103c040800012206403e180c03c0c8140e0030307161805260080f0f64000e10104000c01c58500840c0154004e0342c841896201440e050 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 192739649 1250 192738399 192738409
    0xb03010605030304090908040e0c0301150828090615091505030c04020702030304180b0a05030f0d030c03021c0f05090307031d040608032107182d08011a 67
    0x744603050b01988200010401d04100c0d41c4594501442400100d15050f41c41c10007085540c1c00369030800700c2d050000010042601031007200f641c00d006504120460b4600502e8229000b40881180c3c8030000b00d02c1c25940b01034080c4ea0241d241307258010000c0202e09003071003552044d50800d000d0b1071075581c40c1c4401c0703403190003041c0040d4080315002001861030480e41c4003840081d410114040b130300b51001380302c04640c0700c0b208000301c20b8040608000242d60f404010411004c0c0c1043c2d03000300d000e0740090491640090004c2150403005003070341004210040300c1d05003100288500e900e940700c80210a80001c004a07000d4000c01e6007148544d900707020640700c5000c1240c89115004004000c100380c02c66040114544040103036168400400010b62242e83d1080c45003140c1c00410707603841c040b5800e500781010060046110f50800f4207450705005030301102218100c3c3c085a030044e0855042500b82602d0941c00701c050080600ca94070450090b5190740d01030f07040c0038050441d1654004101110040018101 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 192740899 1250 192739649 192739661
    0xc05031b10030605090403020102030a0b0f01052b0c02030c01112b060317030907150c0807020f060408060106030c051c0513200906040c0c03081008010603060b040b0301 74
    0xd1126000c914514604110705500c1d0402408203050300c0e030340002810398650103000c1c4141d000c0e030005a901e02d0f044590780b00300c904105841380700300e85400582c1c0e0280d9203c01500c4043c003070039079840b01c1c0010841003403803202900641c6403c0c007800c1450300d241c0b659001c80038103601e0300c480b80244040303581240b40204900402043d00c141040c1c1520f440d0011100945d035544c0078601c06000680340e500c940b0b07030031147c000309000c856010701c3c0041840201c030300410210b00100800e003211410580b1016004060340d0341500042d00d40765001c03480b1415586d40110100903840010002d682d11950340d04001e03101c050034840e00021a02c1d042c8444070440c042d03803c546102c103032480ea4445650607042c1c0c2d00c7c010300303000d4040410241c0704001c0c540090000c01101d0f005008140c141000c080404c410408820b1000b041d081c0640e06200b01654100d03000540c0b09155903042c10000d507140c0e15203205240282c003a902c00d07248c543c2032042c0041404003036808141c034860306407414403881a1400605017a181 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 192742149 1250 192740899 192740923
    0x2030103050a02060f0f030f240a12021314071d090f040503161113150b032206020d2d050c04030c08010f180c06051b06040506040c0503 60
    0x10450b201001494468010003044400d0078095042a030640c0354000030350402c5943c00d94200010050254180052880b2805452144450440d0342c00601c04503021400a100303040383da107010a041800c40d52072011544107101c45440c10045100003903410b449100c015200800401ca8801445840400004d805048440c001d02110300f15210385103030f00022240104142e809000034400702c001806112082c05030540500c6510196245400410504485030310542c0c00c201d19000d0003201c0007c08080c1036080741d203030311041500c039900c40c48058201152071030030031450413480c411303402001016806070440207095141040810703103001103160307480840010b19008541c00500300c4008410380e0419a80003042000050402e41e0f60740c0d40404482154200384040c4c5d440c2c040104100c1c4241c800c081d80b29840580000758507040791510654000d190061002700800092804102c501510341501c7d181e08160849403249001d0a0840d194030090781c040321140c2d0300700310000c0c062074000b03240d06180b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 192743399 1250 192742149 192742153
    0xe06030708070f0c0609050c040c0302040608010b070f02190305070b09010215070e100201201905030a110c010c1101290a0806091623040c030b0901060906120203010305 74
    0x1845140d4141d070f111040e99030100070030100c103840c500058803900400514a106000030140c2070700b240c3c100026280c440006000f0581305010800c00e00b68040c03040d0341140ea0116210703960380c42908090142218140c0043e400100c00300c014070365003241c00302c400d00310380c00b031400d40300d803162a0380c10300c1814440c070132100e40182c1c80050514990030040b03030f586400c12024142401c076546001c01003400c110000f5081400f507551102c1420780c400440300818200030b0790540c1c1510b040d42c00085001114540c00d0301404020b408000903a0100d03081e440003544218250a9980721251020350b54081c2c00300ca4000380004d1030060581c102e407071050082007000740c0d01c5090300c0d0a4050a409241c00103510015141d400318601c140020019422f00000340a40c0743c0b40c003d404841302e40010880d0440445e80041c00511281d0102c10000b407001d4500040720108441c00f0075052a0350b42c0c22070103040305046c0365901034003500000030aa5004110740d0103d80c4107481d00c0d1018940140e520040340001d12024082d5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 192744649 1250 192743399 192743401
    0xe030c010c030302130305060a1a0a0308190302041a0903010b040504030503060411070611040512060402010c14010b0406090e0712020603040f021906091d040302071802040801050f070e06030708 85
    0x80c084d0300034288402c00d110030240c04903074903181c881c07500340140c80c51241340c0c5c0e840101d03070340340010b46102560b60f0380e064410f00b5409103960394611041c490440b18100e01189071083e0b01d40c181c400c3d01250000c16481d2050329982c41c00e80b80c0070b100da5102c038012511075881c1151034083d6050500072244590b805448141c1140d0b034441c01d2101070b04003800d4000941d01e00b004440c000601c2417040444132583c1c0100f1541b2a8200700500541003000300350b26016078041c1c020400180c2c2c4c803461259000d03901403944400c1048070301c0220701410301124060b030b001c0d04141005c40e1151050340414203441800c4101c401d03140d42c82910321600044100c000e07410030340801c00200030903030f00c0c88881e64941c8054520310750161000c0317030911800ca25400500000741e00391410003442c0d610065000c103101d806c040310402d5003825640a0b60300d42c06889a0260b450249556210884142d0f0540d8014080c02e002400300340307071040035014006001c55185c0081a40c001107801e0b1424403c050340d10074503858582003d1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 192745899 1250 192744649 192744653
    0x11508070e091902071704030516140118150c050607050403030c02100215100801051b07110f040e0601090c03090b0c03130c08010c020c24091512070e030c010c 70
    0xf080c9012010300c0c0c90340070001040040e03ca080302150780034100d140207886500358078001e41400b200200280150f141008c092114000340384290040c064242008030b44102d41000705c548a00c060f9208450010a461041581c0c0f03070413403c1c1402e040d1140d0240c421640d280e2205881c18003c03400301500040318181110010b080c011a411039042c49401140c401107913112040d003080b50226400804481070b003100308075807072003405100d03000f82c2d12090041c03006000102c1c804041c001c800028000c20b2010403000e00c25101c10b201000c460002030000c1c0001031105070b0711a503581c0c0a00c10f411401d840c2415030724000f42703e03101d03101845902007202229512486121007407504041d0001c20b10a20781201000011202c034085002000031a001003030604100901908045000501d140207080701e42d52018941506046501c0c00303d914180b29890700030440106544800395001c20740d01130300001d0b07100c01c03440003000c101c0c0c4501c0595442514406208051546503401c00702d00764046402103d01e400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 192747149 1250 192745899 192745921
    0x1b0602120c030d050c040f061706060d0902090a1409210d15121a150d08091009030c060c0803060d02040e010c05041d0105060403060c17011508070e09 66
    0x1e1034506002128200301480c2428001c0b5103058414004101c400101000720f461080100700c02007007242080b4107080022407840a180c0340007428184203040004401d100340099a00c1042026005814410a4900442031400a0480b287c078260f5880720200056005040001d0442140302a0803012808480001d01e11407a0380141c1e225100880d280d80300003103009012400007000344201030341121204003a040641000000e1029154500c400108010401140c0c187e01c5240903416603411464003940d040415441c090b0408443e0301000e1440b1087c42154451270690603a4040c4c41424591690f030181a01c054410300c2d0010801c601c1480090140d04c0c128807011912030010304003040f40283c02078418210346038800d600c40800e1000c80d0500405021a54400b4200031525100900d541060009405409a0300c00102515105d614a0146e00c1c0728005500c5d5181001c0d1540d0101c0d6103848414038801e500c0d072001c00000b894000080d040c036110304411110b03103c01403c605a2501c8802c8808 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 192748399 1250 192747149 192747157
    0xf0a0e0a03081204060c0201020c0c0f0a0906230915040c050c0610080105010614040b03061804060506031018030c140f0a02040e0d050313020d0b04050a1b060212 71
    0x2a9018800d6240040442c058400910542c910003620b0f00c0c051400e4680722044680c11201740003160b106200820a030400003d0080c18101e0840310715019519110000c0d40e8900a07410200d140341c140000051304899400c444103a0211541c66130340655030707080034005c241504603051004009180f410a0260529901440c401041454200d04e8602c07450502450b083c4203039040001550340e00000c1040071401e02c9010f004d032000380ba040076405009030464215000f980282200840c0000124010b46d0350006403069240325441040c07460314190421000900e02254803d0182c0210944200c050031144104841e201113500c0b0310300d040c0d1107620b007140c1401110300120365a0014410b001c1c3c1c2507d041200301d074000c62140003044404201d1042c001070ba0360581003801c4950008600c2000f50360080107684d07010101e01d4000808400500008000c030f401c420000e04251060340501081c81004140300452600800040e0000802a0111011300c6850b00c52a001030b0010140d035481540c40c10004c1c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 192749649 1250 192748399 192748427
    0xf0402010207030206070318081c050c01091e11040b1005090310020c0d020c090106021903021906020d05060a05060901030908132c01150e130c030209150f0a 69
    0x5030b41e8241c50b41e020401544c07118405601151400c01c5850f00d00c800c8440000180c4009800b03001410340b00b04005c0008000900984140400888c4030b00c1d60b1070003503104110755508600b04004c6400f1000b13594880c220016401d0381d00c0408128400e081d8205030152040041024004e2028102001d101700c9880c2c00c808102903140c016900740900c030b240e03276002601c0f410348440d01400d19035403d010042d142020502d00d81c0e000da580300f40100101a00818003040301601d8a0100360701400500d0100c0c2459590321407450705554000381082403007101e030302400c04548004009c020a4a4860420014180c680705095003c2010051012154030981203c003156209441c802c2c14081c0903642c419003015950041d07401c3d0b0b0705456240801c218942c600d540b06084c2c80d000c1c44a1541400300c507460035100c48904009024038400410710740e0721564031010407034000c0c0310100452408110018043d500142c00e543c420301e00c3c000140d00b202d40140807078525a00c03032042c05103002400d0405442801000c194 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 192750899 1250 192749649 192749653
    0x3180c03030f091c05010507020f06060a0515040929030a0f080f0403060e1005060105040f060c022209030e0f01171305061306060609030b0402041d100204030c050906090f04020102 79
    0x581c0c0d0341d0703800c41d031030384d11850b01c904000301c0d20b450107101c0280781041d080b0103a0361540c005400c2c058561122500501901c0042d02c01c0400c004820040410b0340c4903a91200d402180741108030343e000001c5001101e8100c0c1030082c01001c0b49280e4017096514800707108042c0c5032070001c514000c0000c000c0c00c000d1140c40f105225050520b03a0b00e4407032008981c4e0f403807403007000c5820000303c5841000462180c04d030310100900741182418100180c640014038640034101c18000490403000c103540d940c1d041c80030303c5034031042c034501d020b000d908401c0050524501c1c2100891003c81000e001440c102e28041e450100680d28500754010303030559460300d030702c0181c444c184004c104050701d80460700a0001900c940c03130000d81c484000b43d80346040ca0868000750302100c2000080d100078400108145609a0007c0c3c044a000c5032400807083c1103099070015851452140c80f401465404030708c501d80141007202d029451001e042941d480501840139000c4070f040341d100fa000e40000d42c0300649401a640c00600601c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 192752149 1250 192750899 192750919
    0x6101e09080d050c010518101109040203011d0105152b05010807031e030503010501030902030106050405100801140c0307050a1b061b0c030509010c050c0a0b03180c03030f09 76
    0x1009600301241030b02c4420018100003041018244240280c541000c001c00308180316103044c10400c2d4440782560180403055850710540f40700d1003080d41c03e442241c0700c000c2c02190380e960748006440c83e81c44034500b0150709500c1b40c4000161032070581860103881e44142d207403c2c98800c55040040642d0402e01140c1098141c0203041d81d041d01ea00d20030075000c0d1401d81c00410946046040c8000c003414071a200714211040d074211180080c1d401030a507411a00282404180d0030b0181c0f000074003500c956000329800529020403c0b01c0320000701d969400311114030008202103002c0d5440000c4030f940484031031960807410000f00301c550748200c0086c0f8a401041c601024200f040041106002a00484c144c0d209616901c184203d0300f40d95203442c0ea0f00e200c6040114450015a034003409501a45006074184064070180805000c010301814110034801800040d20a44807030224019400c144c8074818550300100303480b590083c0014648150580c010021030034035002c1030000f012030b489041d000b07420200540c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 192753399 1250 192752149 192752159
    0x10f090b040603060f1415030c1207020607030f0209031504020d150603060b0102061501140d1e0e15041203180c0e0a1404020d05070305030c1506101e09 67
    0x30203400941140d0b40e02043c0c951070103034160b5034180c1c0380c0c1060b07901103030040051351713256900110b0829903c61144d4603a01c95543c150320000901a00e80a0303081152494100003e90742c0c0440c80600c10700703286c1c034100111002a440c0c14202d0280c43c242c65096440702040844003801040210707841440103282019084507550350703a8005212401c00c1e01d400e1f403200320900402c00c19003e032a501c10800c3c0300900e10b51810020328040302c05150381c014140041c03600042c0c000d10f9a01c0488a80c101c0140c03040c0814400c44113040d00424210f40400c6140d031400d200c0c00c03520100406ca10700004800d210b1130415440c1c3c0c0d1914051001d80740568014950340762403044000042c042c1201046010361480d516640c07a110340e00b43d40741c07001490203c43d20300d0550111030442d900c1c06680d0300503030180e5001a850f8100d152580c40c03d2550b400140c82c0c0e1001050102034001c00280140320080b952010400030b86424052000e46070b80d614034480410040c580601056050240030403152800d480c090010507a14 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 192754649 1250 192753399 192753419
    0x1180b0307030516060f020624060403030504170109020307060f02031611090c03010515070606080304030b150303090d02270a020c01180809090901020f191b050606010f09 75
    0x103070320843d19600680f81c0610380303080855107403005001a04060740384200401d002500c031a001080c28020554510003000101c00c841c0c81c841e450784014103040c1c1d85c0c131f4490901820b150098800c240183d070051441300384480c01030040d00c001c160b02500800e02c00d82402e5081c1e4017401482c1d4994214881440410b0f160382c50701d1824084280502071000107401d0f88401d002000b00700a00388081b0341410001000152900303800c00d9480c02c801e2180c50f4a40020b840c0c8400540b090354016445c0c0d110204010080c45141204580950748010345101031400c010141078417401140e02c8554800d5619a43e078025042405560351040c424030a52071080602ea01c495101040645001440a1f4045442c0040303030402d01c9114280c1c08602900c3d85c4c60101075954015504c501071205014113800008500103600035010389035031403024a840e6803145561400e42e280c2c29180da020300300241144071149900c1c54003000f1640c965030003102402865903058019140f0810901c4900c0c208419808009146108 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 192755899 1250 192754649 192754663
    0x1e050d02120402010e03010501080d05090d060c020303071214040609061b050c0106090e06040204020a0512010618060f0c02150f03100302040b011103041e170c031b0901180b03 77
    0x20390352030201c281c28603000041440c00c43c1c0b80001d009a15100060001d005c00144840c035102c4035107899542c800480c00424184c01c1407010048c84103050505410a00750044091449034000d569000d0220710803058000c00c1c1c03455a0390789400e4000f00800b1401213503070f80c0c104c4076505004031004101c5500a00e1424505590104160300140c00484c6a00c403c21080c00340000800754400c05100f00c03904113010f40d440c0c40c40540020310440d80082e281d21064001c0d02500e42e05143c1d075500d44032540c1e485201030001020700c145030221200601c4003050150051901a90080883d51414080300c02642840060004161031149103081031102450490b81a070085d031041101710074a01e84c19185206000564145001443c103010160000c50382110000055804407403840c07001041548000074110384600407604428050340d030440c0202a151030010301008540e01c20b5003101c41c081c0b1140200340c594501d600311160300094a03401000210b51102405060704400300001498500c8a4006490018 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 192757149 1250 192755899 192755917
    0x4061b08120a0e070305070e070c0506100e0106080c070f0c0506040303030f0e06250c120c0c050901051023030405150106050a1b03110f0102040f08010207031e050d02 73
    0x80c44200a0704900310301035003030b0f0303401254024034520b1306580e03c0c0c944802070f03400b42c5100c03040742c20000340910748207001c141c00c810b410000307071803490810720440080b81085005140c240e030380e4080001401c0c3c1c40713a0180d03031142c5c0400088034148030b403076075810300a00d040d400180c1d21000000c03008500c503594080203000542c4203440000307550520007110400d8800c09490030100c2d4116404005016540d0104c01a4161210301070305a07075107180800340d58915000102412001c000000c0000c02d540150810120794040d801102d1480e0b500c0c010014100f0003401460b8004410f15880230580b4052008840400e40b0115909071110f035a00841c801608102c4d015035680d84240c1018540000d800c811501400d040d10b8244d282c02d621507000790420030603000301072010120b00d03010418140304030001060f207140d2100b5521030081201e03099000c0d41260180340c428105d24080090100d00500c21640180c0e45074480090542d0440350301703903011002011110a0000800c40520034181c0c520003481151 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 192758399 1250 192757149 192757177
    0xb0612030d020c190809091b041d06030105150607060b030d031e05150d030201020702090f07090509040b0408030907030f06020301030606060809120d021c052a04061b08 74
    0x25400c45605813402c03c01220301d034a0010409400000f00309068111500440107031038114154403941075200c00c0710030804040103c1e4102080120318402c4034402c1a503d05420091140c1b0ba40380c031010503080312000d480340000059081213190719800c02c2030140101d180610300c0001c90b8038401c00460f0825086212103c0081e80e203510030407400e160b0859014090824602c200310700d00e0000d40c203030000c89132140d105100749400341240d4100752003501103960203580600a4070941c24141d051a24029003a83e81c6008603c1030728000c100c5080ca401d0b001d2190790840e100d1070164136581c07202d51181d4801b808000d014083d100c40440403030200740303012442c2d5109150041e0f4961450419504035041600300108200c00d0078240320f06c0c03080c009440012146e001d41c285a0380d940800300075009220700362122201036400500703400c1e4069140e1040d485441c017940000014401c1000c507614054201c00000c1150205003c03e0080b54130801d4286c4e007070f40340201e20f24544c100301e403540c80c0a5040750460308485 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 192759649 1250 192758399 192758407
    0xa0209010e0106050304151e090209070516020402160f0302060a0f02040621020409090c08060610021e10050a1a03070f0603021303080a1d0a0e040b0612030d02 70
    0x181406018640100792106094801c0c0d41000d100601a00c070152010340128a0303484401000342c41c0d903000e445414060906022a03080c1490350b00003805a2442c107a1103014503000103102c027406542107416024442000404005080c1d0810009410240074035000c1206400740c0b00002d440105c1000050340240c0091283e0b2900003240c4095a080701d0228030b0b1540140f004000aa41180f910078440f4680c0d20203e001401003048403000303001d158441174440c0d0a00b108013080c007644590365800da84201b41175aa180c1d4484061004500c40041d084005902c01d50b80306e03406220340d05100058604020584540110740e00807881130700e4050b5441507500350341d0f9003081c010313468101c02c02440a00c180c014054032840d00c0d440e12035400795449108149a00003c511482107040740e004405968440c0b1303d1500e552516400801380040c05480e1141c03006c8410010170b80d85050a15101290380303000d00e043c15643c2d1540e41035003200c030107044560000410b184014a291051014000b0070401240058503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 192760899 1250 192759649 192759653
    0xc01020319061d0601113c03040b040b131512050708060306071808070303080f070809070504021b070303030c0e01031e02030603030d02131d09100b0f0306090a 70
    0x46540075030000c1d032240c8a1100c04940105420f00e4550301100908000300104040001e4508020416041d000317601d44448099510442c400c00c00c0d080c0e0003140d144ca0005640480e501a901d219034000c0e440c0d050300a000c100300e0300b10007000502d002945001c00702c42c940d99680b02e4891104060303880c2c0c0c0126a014080b2424039142d803080039401036441c40c2c45c14107401c1507808681c94450282c0184101301030200305254032864034100400030040c0c841101c0d0269600c0c10014040d00d010b03070300c1c011212964004510514400c41000c1c0c0504084809054168500006c01000754801c201e00007619020b00c083c100d001406000c0d0000071030107918049619580020001d200203032181d4000e0505152403035924200408101c11700049d01e10000060341c94070b48100280c51402040510703248103000184d105106000700490804070307515070b80358280c003444507807680c0e4140d401210000c0a80e403000900d03420b03088064214822450b0701a198001d41400b0001003803d2540031100c04c0c02950200c0034040c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 192762149 1250 192760899 192760901
    0xf1207090b0f01050a0804060f091401020a08180706050306040b0402120a0606171f12050c0a050105070b0f0a06090e07080c0303040501021c02070902180103140c040306020c01020c01020319 83
    0xb41800900e4010316017111004041e14049000d000074040650ba80000700e101100c5900c503035242500301e04080c407440a03002005020358043d03036440e00004c2e00000801c80300d00c041120343c9160703198207014012160034810116811341008001a50142c2c07a0031081d2103648441c8010400790700f88040c080200e00d801840d41c41034840e40c2d400b0340104600b040039048000709072a0401d0b04120642e200c101ca00700300c182020284070050708181100e10368041c012080107800258240342c0c042c161010702405642d500151000e008002c4041c000002140c006500824070440c1ca070382c8170f14421070015007282c071804004122056040c5601641d44240c1c01800100d004000324100650101d005510345402e002c0001c2d100d05058100d4061384507400c5a41c50b1032402408494050140707103104548801d43c420034507403810742100046000c00c1c5000070340510030251228441c480d400700300300c07246024038550711500254440c02d04103115540c203011000d0551428002180224100c40000404480440d0301c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 192763399 1250 192762149 192762169
    0x3050d2d1103060a0308070f051e07080c010903080a0306030c090e12180108040503070b041a16080712090b0a05011e050a03080906130803042606060f1207090b 70
    0x540000003842041055130310790b00518107a80e88a02641d844240358640700d5441c3c4a40303107004207207002c6d005806001e50007015068a5100c0001d044400302903840c1031545d19052810b00d00c0b40080c40070407062002c9403101c0018000901c0610303002440341d50301d407612985410300b50031482c411a15403030400c1c0c50001c20480a1034665885281c0392070000ca40c24124203542040b4503050501605600007010300c8001c1c015100b0154104803c0c50061501d442c1c428005107480f00010100c0a10310007086030f0441030034050f0f0348540182c54108054a440c0800d6514411110940700384075110418a070000300010300050050001800104040d410911260305441e10391102001c113440200081041d5a214800c400440303400441d00369582c203049000c540381d84a450810810903d40300d0000a054600000901c21034081244403001c03400344403100001c1256052001d600b0b50711080201d00705160508005107038602c000d2292400000544a550901500364080c0c0f0036030b50380321540b1140d0b040800103a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 192764649 1250 192763399 192763421
    0x803070e0901050a0501030b0d0b0f010329040605090a05011104090c110a060506010527041a01080f06030a0c0608150603070c0605060609060d020702040609110703050d2d 75
    0xe504641c1000f000c41c040714081d1054604068a4010050b01070711178044040ca40e6402c41c0b0202a030313140104407034030318406c203200854a00e410b001da07141d0440c0140d11144c0d040361460443e20501c1d162a2580340241c04054039406250007030352668000203109100341c03008032101c0001940c403a490003103858100c0d030b40c00c2d9402e024880000480303103a00901003604801d40c0d074401400911a1a0314004840c01d003d400040c800888248400c4040d210700a41c15282c11202103405000b60b04612400050031828580c1e540d022902c0200890b030030309244c0070016448240038040b6501c25107161200a240007003075120102040040c1c040c001d085602e91a0b00107451400d5a03928030314281440010880280b201d400341005541d000450925030b510011503891072802040c03641c0369000f48006000a51220a08034441d618119002a400c40c90b800703a81e9100d0224601c142c00c142450702c0984c1d1681c86920302025043e96051394025090059000b12000210360346604c000000300310000b8115400325a074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 192765899 1250 192764649 192764659
    0x206010305210d050c1c050a1a06070f020f06030f0106080c07032109020306010803250302030913181101021e0c1207120b0f011202010f1116030803070e 67
    0x3500311100551400c40d050800c43c0d240015159448550700ba00030301a5450064001e510089031100c03010403500a04c0c01914201010814044e1104c0e80000e054021ba2038503412071300070b001c84004100014501909180050180c1a0a10707440b0001180c951085540c0491800d03000010320159621000c056032000c072486800f490f2111944011300812400b02046918240c0d981360300d4542003068100c1040107a0141c201c61180d41c4958009850b03411182d403402d03051915013408092810b203292074918940d015005140f0f013180200511240042822803d007600d0b0f20b074038281c1a5060001c0010b0421401040498018035120000a050011703041800c10020084510b40200321008114540f140700101c8030090707102d03015250141490b1543e0320040151040c3c0c141d4006120380d0408151248800c41c4c42c0803081d0381c03200301144580e01e04a20181c00601c81c00c4e10800424001c00442030104e44150440e025001107090b00ca0364070000380c0003156119070100500078480e0700007102d042c5a51048403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 192767149 1250 192765899 192765943
    0x2010506030c0d03170906061005070b06090c070b0130030f0e0d140a02030d0903030207050105030c090d0f030813020f041112040303090c090b01080402101e0206010305 74
    0x8006542e60101c84075070707032064141d00685030070107002e15181c2c80c0b0b041c4c400c0401c1c829450180040d541311901152800d0141c4440041419401c0c1325130111060035620200d103820b40d441d050305001f102030300203001425001d010405d00300464075018600e4001c150000303825420030034103940d88405c200d21601d804884856800000002900040150482e9402e840c200501c0344c164800180300d4149484050f09400e51500610b48180000c50000c002c0b07402501103401c80191005c01b19141c00b1030740320180041c0c10012040c0b04d10340c810030045800c48081044141801d0304000080c401443c0b811342201d841d40e500085000b0540c01c241a55406030171100209a03020058000ca4078a003071801e21248160f0b82c44031007451902c0c2600c15192200410036139000340d0300d85494054024403152100741c03980340c0004800980c240040c041e0b030741c0a10b07060351808090b403035030380c24420a0b014152071030003441613001000850101242c803216082007264000d082c2035140d070a149051460018160001200881c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 192768399 1250 192767149 192767161
    0xa03060f140111011503110906030f1002180a0e070801140102071404090f031808031309020c0c060d020912030a0503040f030e0603040f1119050d0303090606030f050d020105 76
    0x700c42200460a0816000d01080d400325507004007001807200200280d1218003100344071408555040c03040c81610080d26680b509020941e540f07068040054856114209040d0f06028540140001d01d9803160480c10030340614000070390200240d0084100110307442c00704904954000941c07030041665568260a2517546c2c0c000035103070140c034029184440c10740312007500c107a251079000141050b002181658245058500203010f8803044000503010b580f00e01020903c401c010040701c0010001e84070245c582840e024804002c1d4000310392080e180d001d0713501d100d511501c1700c0c80205008003908000583d110951000c0040074a400c90440200703a0003409002c582c4da130840c0440350080d07049200c501c012060b92404542d085941c07409150405404003e110070070801c20752460103640f0400504040300e80d01801d11a03080b40c18205c942c500c0c5c000c400700b0482c604060540180c564000d03c1c01040351803241d1910004d84429034401c461181e69100c599042c084117105a507444540751009203e0b604001c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 192769649 1250 192768399 192768419
    0xb0c0115080d050f0409050408031602010c020613020103090c0611070905011d090709020703020d2006010b03071205040f0c060c0f020907120c0c020301060501020c0a181d030a03060f 80
    0x119441d04148000010742d0004a20444151002046e007000c013481540f410789024a410740040e5204402c00384110160030210340107020307904031200036900810041d034500800303240c4558192420f034181a42c1c5e00c002000b1440e0306503984064030a40d10740c000c1601070b59030701526005860b8041c0007803d14100050101140880d4121340c8240c217280d800210344c0310b41c1200350a02c00540d109407011071001844070304054010420a40400c102c1d2038607482c0e074000d01c884610301c0c0501103801d91250000001440028a04005160000c0c1185451040c0d2018882190700710303141a541a202052201060010480031078002d074090002d03881c20608074041c5035a02030500c0c1d1022002442032002c45d00245405100748220682c0d00c0c8018414080c1c40200000508140f02d218001c1e4001c0d42012004600c46d400018825400f05024058400b4207240c400c2204a0400c0000d80045042d1a0201c45000d2030f002d24201c505e02e401000030315950324a102e40a0304440050380412030808842c40c0401c107135240 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 192770899 1250 192769649 192769663
    0x20109150902030f0703150b091302040903020102041d09070605090901060e04090b01060c0b01210b041110050a080105092e030219050f0d080306011103130b0c011508 73
    0x10400c003040c409082c0c40060301300243c1d110504118443c01d48000144100f50354911200244a5000c0286402d040c4c244500104102c0700f010800164242060060406078400100240207200050809480c1e48200488031f404c59942d502a0340c4c01c105204000d0028404000100b00c00d08281e858028520b020400c4024144078071414800d80c156040d20307035107403604a54486940700500111300e60f12000301500f0410818000c2e207050300c0d15000440c405003e17030400c0404045680000d1264a95036640c60a0307484002d00444102c2c129981050f0292150604031680c000c00e0780701c540c1c546400070401020148140c2c00035101e44829000d000703450750f45c01c00b542d684010064240e4043d5165030081e01401040b540001e4120120000b030f02040c0c041d020f280b00a440c5c04540c17104041085c0d20404c040d580401a01414000040002c41d81a601801c00300d050b034104401584e0901c600401d902698070303030507071003d20802d1000605402d1954284181801ea500d40c00080d000b01d0304100c441507841c40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 192772149 1250 192770899 192770933
    0x2d03100b0a0b030a0207062a080103053016020108090d0c0807030e10020102040f0509010e0112051c020102090a060c0507090b060f070c030b010e0f1306020c0a050d0f020109 76
    0x282c008040b4010a4540d011600311981200d03040c4074509454010a01c0c0e0300d4100260380640e411204c403206024030070301c640c0781240e410200500300c0c07684450411a250b013074558a4201c8414242c10303045030740100c40160212841e03045440e50361425a00001d409010010548010354214020384441c582e000b494210300b40e504403810946036607607490306645007440100c03016840403119402e41c01c607a90540041060310841c03c60410030b95990421b00c40c00c000280104064036001500600c180f40c0362074104205507001c3c00c102c9a9804140341566491100340907540b0040c1d400013101f0000d4100804100010a003526000102c07105584030603860b032074176005064100d03450b280305403031a80e155400c1e02c5400c071403203000c0c1f540c5202a01e44100715407400d02c02203910a4900c1e0001426502d0222114400d03c074000c0c0d60115070b5074040f18500b402542203800c4174065404d104920a00c1c10801c12040381c1c0348503400400a0031285d1901402c1c0101800724141168100b0001c000011003007040d06072000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 192773399 1250 192772149 192772169
    0x20d0b01140a030830040b040c140f1c0c06260606030f06010201112110060903080306030102070f1203060e090a020f03100221150a03020603062d03100b0a 68
    0x4481c2c2100b952080d058071510102840c00c28050000341f00f4000301441c000c81c880e8904c00d05095071a88029400c5181480c44ca502c5511b07000c82d031a443c240f0100303032031040b200700740342440d00360380c81e5144000c0e0702d5583c02601c0007a12008803081c000c030130610b1405c504102420040c40c03601d0004c0018140d403000604504440c400c0303402241859000750072549141c40400406900c4403030910060703070f8a1004a070741d6501d002d4844080b4012412211a10050700c1c9281d46038a807c0d825a103601e24580d0003d00f0164156500f0010b44000c50f880e218000c15803489090030301c040002409000301520b00642080850500d00814031440300c100149011000d035059484003c041c040c00c0002c3d0600300b8541010f01101d000080301100394000c6840b065442e10040c100804070b80701d010844170341c00c03582c00760540c002d000941c1c00d05c05072500030003450340320038018000c011011014880e100d42a04060150016214511120003107103014406402005040c507405c1028401c0c400004400009038442c0360a01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 192774649 1250 192773399 192773437
    0x20708150a0b1503090d080f04020303040608090312070507060b03011515030e0102070302031e0a080403050c0a0f12030605090c03040f080d0c2006160516020d0b01140a0308 76
    0x80d4492541808000d0448840d4513201d28003581419144d41c4040708240003d840300340000d0482a41c034060a0260b5000340c001c0d4142410301105945c101c1001c0e0400035584414401421040d11380c2d2012407141105540355910341d2034601d802401e42c0e03141c55002d8031a03414004041903501d18281038200b03c40320594a0000c02107050016070003002c10a0320345545500004110044c9500000100608102e10301c0c0e00d0100e03180006000158050290020001a4030030041004244070700040d16100303017458155452171440c1c1e501d001c035603140703000200c5071056206489803940b5014801c1030014801034030b00e1002c0d484e10f10034004e09840010002817040c407071280032009025800041e540081c000b80b83c108220b44d194003000d844440d444009180e649000301d182070241001060f0b42e4040c0b0407040d50740783d1f88034200b02c00352a160004240491815903000342003001d40e45900c5958045809124040400e505115071012190814890a40140c00b01d0034200b000035140070032501241e00110120700d42d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 192775899 1250 192774649 192774671
    0x50315040c14040f05030f030406080f0411100207030c0803042402030f0c010203010f140102030a0c290108070f0501121503060e010f0e160b0c070e070f020708150a 72
    0x890440711441c0a0002d00410041440720724209501c06881c0110129490044900c2007039907a03104500803032001585600c0400c801020303010f1004d81003441162140003032180f10002c213000580080e4240c00692013a00208103001c88514000c020303243e10b038040c40c40e090411211400c401d40100000c05001d807200681c4100b01d109000391b404800410201230761300c68026070058040d400078050498020001000040d02d885c0c412160204030406030051424650350b601d099401f04111107003901d081d03106401007c0352000d40006040e9900054840203402d50400010510f0702180d80c1000c440b148282d1000d002981c0c0011900700c540c95614004108101050b0700005900c0582d4402018142070214101c0905419001a2100b500c814000c1010600c811b0202e65103403201221010100c5012009014044030000204a00c0180303400300c5450300d0796185400c400542c202c80c480001565018800d904580c14031001c0300902c0c81000800803224101469004128080c14200c1140e550b074008490b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 192777149 1250 192775899 192775907
    0x13050907022a19030b0702060114040519020f0d05060a03020108010e091f0516091503020a020f0307050616030212070c02120114010501110a0b0f060a090c020d0f050315040c 76
    0x11010b07016014100c60902c080300303081414140c0c001250950f40e10f000090b4403c3c400103c1074101c0d120030401080e40140305061100801c03026203158140c0241d200552090910303070008140c81c011760102d071a694815491500c084030340103059a885445924010000b43c0e80c00350a00e0305651010706141800d4032605080c629040042442d11241c007100c001d00d0160504981c4802c2c4104005c08440e5130344010510708945001d20b030f011701c01a40302c60980d600c0410b80319034040c003102e40c4a030040707030014031184214034510b40292000b01d410782c0c0000104111203400801d5414034803114102542042d40c9000301030480c0000810700400c0140b518103240a541c1e41b0000301ca141084140200605112800c0c12071038004240901804507002c0c10628001c8100007902da1032042e00b0146030b1a0703030344944114260031403001d001240c0c0f04030400c802249000641c800c2201e81c1d0b01d00e03001803006641089018044205204040061000c00e2041280010581c00d10707000419084500203203d01d440070080d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 192778399 1250 192777149 192777223
    0xc051903060302210f070b07030909020c0d03051f080703060c0503100e100518101703070b0601090807091a010f170405211b01021e03040f06020706021305090702 71
    0x84061080c0d0100244881f2401c005180c000e0103a83e032151000d031118048020703840b85066060031940b0020202030168440d0b404150890201c1370350040300c4030034071454001c0c28107907004102550004c050800800c400c601c0741d0168001c0f60b0a1190540c940600320006a050600c62400c1c10040c2d02e00054040c10711145520180c5070003046060103e50642c890444401b044072140c0a00c40401c0020820a40e0740a0202c0c050082400543c5001c00c1560b4050031918090411410700106a0700071540741c40900130240a000d013100001f440d01c90310020340c40d00c0c10504210505004204440b140c0455000d842c280c0955091243d5005945491803e1840c1161607851203000e2200ca500ea6403030030000038003c108111a0740601d21000384100c040c24200d02c41d8102c0650018000c1c0040d9070740d40c00d0b1201440c0e002e4050489035004039119282d010a03a80701060444d009a8000740e02569500b800807400050b110039540030166180000019507114008460b548005a590303901104101c00503000c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 192779649 1250 192778399 192778423
    0x20120100923030c03041a0d09150f02070b0109050403110105130b09060c0a0c050309041a13060503070618150c0b0a050c03060d02060705010c05190306030221 70
    0x1004007501c0303401c1036071191035500400202040101940018514000181c40000c00001c0c055481c01e0700d0603445100710b51031007960341c0e50b0000a111508411395144140b603c0306000300d0329481c10039480e0392a001158150003840b0521403051021002050881c440c41d415500c000e03d0004e041e48030303400c0030384a42d00c11301c10760b02d40c80d82080104449011446240301015100705541c502c252a1500e00c2500d032a0125654400d600d824410b07104c115105642000710745001e141601d1a101159001c6003d48000e00e251080091031701e20400d03210708001c01549841203801c40100401418075000a88640705445208108505074030451500c06000055000604d000c08211215010803c009030100104013020b45860803101d0003c1c1100d42c45000c1c29126541c5644910700c0c50380d803041041824082000241e0b08400300f030000000040e424841e041d00d20707800d9141c4544517194400c015000802c480c00510415081c080c0810068a0349128600000f5010380e4508400680c50b0009203046224446 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 192780899 1250 192779649 192779651
    0x110c0a08010c0e01020307080d090311010c1e03020a0801030602180409111c0c06050f0706020a081f0503060a050408130605090405010f0e07080405030903011a03100902012010 77
    0x28211105502c80d8403050310740d48410400a042200680c1c49000c2c485010703201200c100b28203150744440c2c0d4441040b582c803e0400764a00c400c58a10702d400c4034001020440811000040040078001e011002d41e00a2014a01540341420312400141904030600c001800c080e000b08084280c0717609a0580c1c2d89400018004001c0344000d420019018603d48103081d00503941031741d082069070b240c00c00144c203080d000038000100c103160100840707581e07100b402c1c541105030303080c0006030000e4118001403009007030700e66901c00241044041c1c2102142a40015848903459020800043d2808250298001103240740001c850b641c40c00e007244240b090105103d90700189010220710360340c001b00548030000003036804021581e00c4111600c01c039040d6000b50440f042600c000240c030940702e94407445d0300c580b19206890070700d800040440d003920781e181c078808040020014132f01d2407801c0c10007003c1c3e00680306000130701c2001029000a408100c00c402c2100240c004041500e24600d003c009440344c0d0b00300910 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 192782149 1250 192780899 192780919
    0x5090402120105090a062601090804140306090102190302030a0e070608010303030501121104020a022505030f03042607120305030402030c09010311040e0a02090406060317030103030c0201110c 84
    0x7110490a80c1c0900031144110741d103201140d0292254803407072054485290804412080d520201d071034590487c110081c85648901c212400103806601900c001d140919100b001088484201410310800400c00c403866032060240341143c0c0184040070400010a050040ea41d84400c844e14003d814989919403031445021000208144d024808a0480340640d07001c00145e600c0e4645c916192600d590090100c0040b10b807400c2c4a8503243c0d0040507100110b00460301d00084000407043e0541d4003401c2c4c03040000302c91a0402207400c1c18000301840d00d07072032000741d40780508000c884065902c0341c00310100620200d00120080301d40400076000034002c0a2481d19080600340b600904035442120100d02a000f8050000c466043c150036160517203501504400032020b009050000071f1400d00c07000300c4148921900c0d00d01588403000d00c24040d0703018050100d001d40c01c50500e0701d450502c00030300e403800910070401003000c01e070300410007441c5550920708145800d454080c5245803401440c8600c2e03000c1201c0b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 192783399 1250 192782149 192782167
    0x90b0a02030903100c0905010f11010509010506030f0a050a120908060c0d0605041401061107030605091623010f030f050907170102090607151d0a11090108030703030c05090402 77
    0x1002d0061520700320704031060740c0d40c4110000142d07030f4460004404204885800e1001c0c2d0700400e486080441c0380c4c90300c50140c1e1410700c122400d40e0300a0310310070031704d96560040c0301250400340148200c0c4030011006240c08203495035801c1d41c0700c40780c180151003a1142801a5000c0d48034000740b000610800b0708a03603082c100b10154061035445103402c024124607000300040d44d820a03004000703507606984108441c41c1c6c43e00401741d07030b5071400c102da240443c0601d250100005e0300910409001e421904001d01424082890f0700143d184903401c070a04007043d9103070b00848500c0300741c003030021800c0a18140d5940072443c00240c001e494864180c4080c80c0c18101008410600000d28100301c48841d881c0443c24526468410308074410154000d40211082004030042201c41201401140d44c03060009038000a0003100c41d41d00341034000d401c2c09600709130b00072003c1c82440d804031129004126581c6805501d4180b07039550328810701400800b07042d280c000c0d50240034050307019522116409030065585180394 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 192784649 1250 192783399 192783403
    0xf1d0c06182b0b19060608060919020715110c0a080918070e10110712080904090309090b0a1409070903080409022517070c0906030b04060b040504020108070c0201090b0a02 75
    0x403600c6401c1541e40943c13074078109100340165012201d858580c1c3c803940d25550284840220010000a041c51401c04c640050380742e07030310090116074020a41d0310070313034212078800d2419074290b030303107580c80c0108240560540b4140100c0e100200643c84849107a580c0440c4c40407490107064003603080c4c80c1c100b04904006c4490740060355421f041808482900b101240313190181c1d007410340c0146000c03065001d10030501aa004081103911094000c15409040a01c0c050000d402d5070082801200000e900160802c0326050700c2c001c40000c104122411841c2c00c1c108200a505241500c45562149401c100890103840c01401c801c00031b10b4000c01c09a03038554440880e0b402960203120b0240300c0103079003c0c03168811408074403504050340d07001107090035042e21011004e5081d00440c00c01d6603042c18450002590302603c0c421000210301c558004c007540c0c945400c2410407182c94141e028003582c140300c10040180c0e8807450703281e440600c80c01d107804650aa400100c80d8080382e41c0003407004460000702c9074602d61700 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 192785899 1250 192784649 192784651
    0x1e05070302160f1802040305030c0c01180806040b06060d05180705011103030403080405030418060905280e010e0303180c01140403080a030f1d0c06182b0b 68
    0x2035000c070b0b28000007414002445000d648903440f0300b8101000305101d0030100540c680c0c6046106040581015220740301e9505540c0b0003040d5045940c00f402c69400a96080f9807040340741038500d44e40741c184612308445c0984070000140010000c5251800140a90380c0742c0003500e90300c6a03001e1301005245006440300941c00342c43e800707205151007003810004607584558403a50119031104040c60458a170b55405480416018000b12440e0100741300106488182c803035420b41e10410200c1c0030400c0d52038507103400f00301c50014002140050300d5401800c812a13198100d03610080d5000e00c001500b00704592601e006004080803561580000005c1c801d00b081403040303500c01c0d012014241c9004a0040c001504c0b2010843c00d4589025410f00c410404100f00a001e040710503400d0402003001e00003105a281140c020404441100b019203802c1c036040b1071f04001c00d2014000650f075143c03900e0860103a0b41e0b0300075140220300b4424501d03c58407840b13140c00c400741e8524035060a500d1440d0b44550b4540580d0010b4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 192787149 1250 192785899 192785903
    0xd0b011101050934140301020403051204061e0e010e010221090a050303160605150d0308091002040807091a12030c01050603030a05160f14070e13020603010b0a1e0507 73
    0x130b140001a600b0003001181c0921100d01200444140d19115008080d0441c5904066140d542800f00001040c010f000848401c00d01e485000d03540c506181c4064200c008054801c0041b2640e0b9118106103a0000c0c082e4089102c01d007040038400d500080100d01c1d14240c0d0300b090100c0381c0a0200450502d01c4d2502911424030100c0d4600d0903070351074606242c0e603400340704080386210803041006004120281e01c00d5402c003082d0341404011156840114100103604030b011800513103071f00100502902e09110754591449242800d5207414501140300380d40c0c850f00d001d854081c640c0c580c1c010b04600150a000e00d5140000b51482e295420543c00c420303103d8000c0700c0c10200c5942007500140e05403070b0200458a144800c0e803551030a050882e40c89041e20601400d0455a4544003110000031400d05007144c503090780c4840060020300d05000b03841030480e5000d4011110b0848590801005a880303006890548081c03079400360300c4040310001261070303508500b035001007100c2c8400e01c1d03003500d135211380102000c43c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 192788399 1250 192787149 192787183
    0xa0306030218040302070608180102040605090111010903080118020408010e01020406090915090b0f130c110303040f03030e030706090501090c1202030a081c02040801050603070503060c0d0b0111010509 88
    0x2001116201100b981c02c80303000f00107070090b58091000f02d0140c1003841c1c00c41000240c18030400810012542207074040c1d00b0a00100301c0104d103ca03103540c0d201c80d11f4584a09004000d03c00320501d680c01038180c02060040600300034441d9282d0690300b5259040d1401002030f41c00a20a80221248a038002d43c0940542c0000031080d4501164a2555016008034070084800ca00c0d00b0303a240c02d25500c024059140700e40e6000e20240c3c440c80301d40d03982186400c4400c07002d01001603c0180c00f8006401103048840d580c945800610401002c034241440c1f14031880e40604000c1200280c06250780c2c00d610400e84014001c902d00040030f001c0c807405501442d20980b180d601204143d8807040c06921440310b0400095150f800b2900701c00c00200f551000d420104c0700c0a00c0104903000380c00301d9405036041038201490390380d03690742040440c4c9801c20a20b801410280d01608080c140b0405240c0203106280d019140107488000c819483c1e44615140403105110900803c1344e03092003201292101074208445000d4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 192789649 1250 192788399 192788419
    0x60603130c0b04050a0e07050a180b0d051008013e0307120b010306080a060b0307091d0d05090102030a0c17030109052a0a03111207110f060112020607050709020a03060302 75
    0x1107a01c06c8902030095001c0e440d0300b0708150390018200d1720b1000007026a0a14007000c81c0c0060003c915002400320590507200c046114640010300802d2450b01e5888035405a040070040f03c06901109081102c3c484050a085254111001001040149034130b507500510000030820004c40d40c4440c00d01094aa008001d0050528803c011415034401c0e028030109500800c0c60321700002c01940c80705042aa01400383e62616603204140404c5800312541c6c000c10111086803685040d00070b11030709003c54807a0034054104008080001d507030f0700802c1e46500510039100d83c5002400341d08031041e00c800080c294181d80d03070368540100b600a408180d982062894502d907585a2185241840c4c0c101043d64500280c102074018400318080c04500300e90000380d6500b0401c20301500e21803a40135109103a039445150f481c08106c41d0030b600e4800c181d04207010340c1d041f00c1d0051001d05480c051940f412501150002c3d15a050340c2002420540e10354080c20f45036100180d90f070515501030b0015801c0740d000700c0e480c0e440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 192790899 1250 192789649 192789659
    0x1e05031b07050102010b012c03100e01050c070309122a080f060105030d0e040609020d0e1603020d11010302120403031a0a0f051c0c0608041103010212060603130c0b04050a 75
    0x2070b20b641c928047d000c11019045802411404240d5006121800800c49203c400d000c1c0428180a0015401c031031035505c034a1170300200031003402800e8005d03603c072692031318159030354500400c140d03090b000383c00000c1c0c0044c2d00c00c01840807000d05018000100810b4101040d00300e07060120007038043c4522402401400302c8807104001c0410060b0403504080c01505518511400171512042c210303074401e80c46550b401e4045003003002d51021b000038182c08040010341c0800f01001d1450108010014884940303614810310042e240c91311000340d2254003560b40000180c4000041c5e0280c041e070000041e070524072004020078954581c01a000e00d140e180000c2c1ea000311039101707011900340d550013014070120564104115501f44003043c1004c40106080025141c1c4850b034132012200c0a580c402c0c000909070406110521403500b1b044c14403964100c0003185440100c2880c0d50300700f800202018824040813000480700c019414003000c0c034640c03250320900783e42c1d151524900c0d00e8119015850164851142c0031074 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 192792149 1250 192790899 192790901
    0xa080a0501050627040e0a05010e0c030703051f020d020d0b011202160f030c08040603020c0105060406030506060d0c05130f0b09061e190b0702010f02010204060c1e05031b0705010201 80
    0x1003a0040324000461220011041d00f21a016041316a03400c01c3d903c0b20104480034040c0040b81e200707841080042486000f110142c1d00d85025403c5e02842034000d000c0404c001340c0e0004100030710b41c400400032a0704c2880c0e155440000d010704411140303440d0001410130102040c0341e0000f0000c51090b212901c1400b85000c04404034000c0f01c00c4c3e840d004013221a040085040401813040d018441d01e008640a605d5988214194103d50b0055001c20b40200315008039040a01855a06c000c041d00c04000151644e103400340d0307500c3c0c080d00c02c1f0700841c06d8202000521030481440d102800002d03001c022100f42c06203100004080030166081c2403840d0002101c4d00e81b0341100d01902507600184130860440039082c41104290034981000c0c0c0c45506101125026980c102014009226150b105c40e19101da500024101142e188907007011039104100034025107400842c0c00600c60381088a400403100c0d80d084401d008001c486000c2e0030741c4004615000070300c072400c07ca082810108010b5440f007541d22001a4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 192793399 1250 192792149 192792157
    0xe070e0c070605240d020310140a050c13090b010e040204060903050c060405030604020909030909040311060711070b070f0507030c1d0903040612090f1101170c0412020310020a080a05010506 83
    0x5070700550b0b800710003055171402515000700e61740001e0070340b03418948039010081115228a40f01c41c0f182030590400060540f5449115172140e40318501c5868006003104804c40c0f840c0600608400d82c2d601c2d0328004259104859005004001510441d070b03450700e4020142100500344808c4403607100300401044c0604004e401e9800f12903000e80180340036200d95081040740203005000c0c441c90710007405100410764910082d280100d001c2d031600100e484558502a003429001000f1005010ba1300181040c6407000140c4131084520900c44243c8030344407440d081410f80f8030403101410600c2501070110900c01c00b03510b0442100c4052584150010f8081c4264031031540071110b0456030307041800108031303080c082c2c1c1301000f40e50714030b440000e107000144c1c0e40c2c01d29001541100745c440f05c0c00c6000c0c402480d6008503280071252241590426645810b00c0780a4079407155004007280030036132112a030219242008030007403001780c1503015500c0b215081401000355400700c078a40e200310704180c0000b9542c05c081c001c032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 192794649 1250 192793399 192793441
    0x180c1216080a020f0103020a1205040c060e180106140c010908090a050a0315050a020f030a0b043b1f0c0210050103050604020d020a090c051c0506090a0e070e0c070605 73
    0x3d0010413446400650007508492902e90a005402411441a410303600c2a9403003540304502c4d040380b031414104001c0104200d0f00241d400740c0d0101801c00e4601c1d510004040c1152000d19009480d14920014a02c0701d00800000c00ca95608080440041000d030b90058200100f096600300036659460303040100d01011488007601003501090b120a840046420840d40081070141c05072804180200503041d60740215040584590b4421100b2494502406038800e40c04140c0030394103443c82e01c0310040001c1c81d25401c201c0b0112000313900003990329000303004111019007110b03903c03111181142084409801200c4c1650014040e030706e241e407620303009481124141e03508030001301410303036440d400d001309480c440005030703071014101070b000030f050545000f140c00416040d41c2d51a00c84a182c0c0381d02182d00c00e410b82d081d00f4503040104110a68442804444c0d02c528000404150b10101c0300002d41003800b036410070f114030700c00103041042040303a8500070107540f44500700401003541d410b0040024a075811680c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 192795899 1250 192794649 192794659
    0xb060f090f0718050a1203020706080c0a03021c0e1e06070e010e011112070201080c031608041103160816061202070206040513050f0717180c1216080a02 67
    0x106150b030b80325400c042c0008211150702e036041d98a42d400138816021a40c408159100c4c01440c5500b0554144410802043e5905000050f414907148194540c00303000201340416034041040c2155401c8030304ca100202658010802940c0850851103440742c0c680c1444420070100c40c0c1111084c2c84000aa841c07140c07512343e68403004e004031f1600441e8042c8081c51a10b040100c04140460350034018440e2a60340a61254000e0f910b00d140e01c0050a0144d0081101c440d6042c20f204110190701d07404040d80c022415458990007907500d524011040c04039a00b6015014440c0810b240c0c007050500e41008142c0d0480411078144c0c403402c500c4540d44520758001d503c0016164265860007600703540180c560ba07032009211a04258403900400d4000c1080c802c1c04694980b44c6041c806421002c5001541000852401060160101c0c0307201035614806070041e0704136503a0000040e038084c001d01200d06440c1004000b48000640e10f100c1d1961030008054468441146071030000d6640000035060b5040c03980500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 192797149 1250 192795899 192795901
    0x117070602030a051b0309040507020601140109120303091a191107030c12050705060a02041a03090619091202010516030603051e03130b0409050a1103130602160b060f090f 75
    0x103801d05c8484c4021140c1c41309101c00c0c0218000da685501426115010a90003404c40c1d6140229483c041061a152141403246d46802805811510884040400d405040c04200c41e401031600301010f0a03040b60780b42c400200c20003400744081404002c1e00700c40d118004c06114100807504c10115a2041220040214108049e00c1c00050202000300304c40c00600d0a080b818041180c0701c0f241050f03000c9814024242d8000f81c140407801d40e0701c2c2041c070101c00b80b1440038290318090b9200c40c0c2c0e48201a2011040b14441c2d07603101701c0e1941c0f0390400707120240c0c070071004001106050406400303883c0c2520020100c6080504501c0e84602c13900c20101100d40000040004020060f07114a200290300d10421590004200b882119444442004010184200380554491074406000d044a6006d86510203140c14000403141010060007500e4200c8064a681c41003031000317240c600028825004e10304041000c42c00305d2000d10402840d030fa0320078402920b0100c0000040e1003081003080045401d1142c0b000090 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 192798399 1250 192797149 192797167
    0x90c16050309060703031b0903050304090b03011b05090f0f060d02030a14011d01060503010b09011b12090801050f0906070f03090c030b09010b12190303020d050117070602030a05 78
    0x8451021401039041e80c0c41c08540d4008102d56602c0407a055020070b40b1400d031414400d9118441c14a800348900e400303169141155211901c9101d04c1c41a2041c0e5501c66a01c16070558003944100003144115101d001a0903511b04050415042100c02d00d03ca4004070703641d2092800c01210008918100030403191411070302c0310306e800013904064617050000d0743e91102e04001022480406020b44041800140d42e0038208402c0156160160404c4d01009814001000302c0a003072403c0c0c450b806002d0820601c4882d260711902c540d06060540a0f11032903000a8283c2c1485e000454003081e220200c0082c423050b0f440700c142440c00d101c01d8458142a034801c0c1c00041c10f5a204180d4070414111a203804522915a40c075000000745a079007003901c0c16100d6070b0600200c40b10074400c54182500c10f0b41c503480d5203070b01401190f8407801007141d2510100881405101098420b80c11154a0054054100074958451824926461141c250320a180c070800602003011f5000005a4a01c240c29540325450043c43d8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 192799649 1250 192798399 192798427
    0x11031c0b0307050a0618030203060f010314160302010e28150201050907050103200a1218050c0103020a1b060f060f0f05040c120c020c01080106140712090f030c050906090c 75
    0x6d00c21002e41440110408001640c051101c1401b540d2841c40c109069411402c010350602c02041d1400320640c00f40510348212640406198116502420441d5040000d08013190801c90240782c5291a980f02030b0800d95640d810084840c1910030183c072000c458102d8050a908031001070b00e0300301d2140e00c00311040085602c65000f10900100302c101c00710b058181003040000c80d42000350315502059820f80115011051481200c1108103141c0340d043d0764802e03d45941e42c035840b561001c14101900022100c010900400e004141c20100c0078000342181594202507006100c8907016201041c1043c0e800507240c04100b040303d0a50302e2840781d45080781d2410301000001c00d001d04418080c8018403441030103600c3c40b4411412a001c1c06c1d006080095404000144036010507003008051061180c08002d080c403521b014aca94507544692074080d10410440b050758401c00d41d90100414460a00011003002085078040d070403120292000c52407501c44400300140602c0c1120506010041807248000210708 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 192800899 1250 192799649 192799667
    0x405060103060509070309170304110904060b0d05070810141909020405040f02090609151207081e0105010b0304082b020c0304060e0910030f0311031c0b0307050a06 72
    0x414103001807400c0c3d444021a655540460310741c800700e541c1d001281d05002051005106850203a60340750b00e1898650754080c0e1a00301800d11600a42c58100005d080201c1d991004001110003000ea040000062410aaa41645020311f45040c02440008030001089008881ea98003c0c82c01d444404c0c4d45044900c080b140351301c580300421580b51018000903803203a104443c0298007039103a200f10107441d401809150030b0050109405182404204030034402010b811321909041164100008541030000f940b81c4a556000103a01d40509140307181c07440503100380e0b051031514240090145a0ba11200d03080103003c2124041c1c0003100403c8107401a4441c0c0c0c003940ca02e0625050000c2c0240d89440040c82240c004d05000441c507840042e09114594210705560740444c8201c0d03000d04145007041c400c222080080c403004011050000407581014010403007000e1003103454046035190f001402408003109050340c0302110440c03400c507684020f410003240c2c4009944d40035001605051808801721580300c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 192802149 1250 192800899 192800911
    0xf0403021207060c020d210309060b0d150f020909010605190e1003050a0219090501090e060f060702030304030614040b0c0a0f08060a050a030503030109180507060e01030e0d110c010c08090405 84
    0x2040091161a550001ca0a849601f002c5e900002d0744505803034030500302d80ca240300c0f6600c06c22142c50002c1c002891000f603080744900d41d0001250840540b031218000e809400710700c59002c00c1d10800881e402d580103000e03007001c1c01c101422009000203c00c0039110342c85c5103400240c00c08120100c10910900075007015070841c183c40700052815100b910307000401ca41d4a903003000014185041081950781c0a0b012002414202d00040c2d00da0402074002001840901040b82c052100481e049055581c00e005540045400410034008010818449180282c1c01c840440d0f03071165120100301c0e01c00c80c900980c0d82945031620341076402c0d44010010313a2440e200524151703010140b2040032a003500d07800b0210300158030841c001d540340d505141d009002c0c3d0384214110586075102200e918042040003c9010031581c05042c0001d0f00c1d4200300048004e080c5800d0528014810203640709601c17680021101c0b81081c0c8807094448503201040119030300340301351030050040c807000e00ca103100d039192507400340f50484 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 192803399 1250 192802149 192802163
    0x6030114040b121e1c051c0b03060a090203010c0302190305060f03030403060518030703050f0309011415040c0219171b0d080a0c09030f14030f0403021207060c020d 72
    0x948422074103403410900781c2c02d2180480c15a440840b4020b07040041d240390384c0d01032400f0b13007016402da80c0003403160007644071f0746030f440501c4442e800c0c0103582076006048002002c0c00b40c4601d0319041080300058501094200c0c0039629010308100e64a00ca88207842034603244220211003003003241c1d0f04801510f4081c0c0011350040701c3d120102c1d059607040006100440c8528800b05c2c40e840c0c01c103e610802c415802ca07071b060f1600100407110000c0e51100032211403103070311044680c60340c0b0740c40250303401059516440c0e260600f1036010701c41d010b51040340c031012030030046505201805045408076111103e943c201c2c8507090300c0ca41c051f000130385610140680000b010110906142584035068031485c00010002c50303c0c0c002e00041e81406a00c0700280e5030100c0c680e20305000020840100600c2d02c0320920024081e00c0d6155840c400300a41d40750000c0c2000e0884048a4175100ca00c110300d40264001d10040340700c1c024400c40e45040e01c4001c985042183d80b561104c19222145800344900501561000c03a105 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 192804649 1250 192803399 192803419
    0x60b03060702010b030106050307080307081b0604060209040f0c05190302070b040309080706020c13020a05090307180c030b090c07050a06020307080103030f110d140705060a09060b06030114040b 85
    0x261020012144900d209900204101951a0a041c00c45080b0782059010360041241801740345000000c41d507615511081159590340b800170703000940b1421820500c024046c01080c07000b801a941c01a003486c01d41103070104242540f641c005011a680c4d0403449001c900b080c040380b1403c1040e1380110802418604003d4036041c0343e0b95801c02d00e013804540841c0441c040003801d01906004000c03040c05000c2c00d0000b0310f04140e80400140725640204050000b842d000030300b010b4454410b600b80c034048403015045641d40c94841013589083c0a0003541c0c081440e203000200850306100c0d0040c1c000302003010f000000180c403102501d81d016030006100762103d200c0d0341c000d080090b003588019445600d607a9221980341d4150710340282080902d00e0910108003448100041710000801c101c450040036081c0540809070904c140364050240310800f03000c40c018942001094400c6400c049481445440308118508074402040700030b00080c0140c001001d1035240c5880282031079800314000080041c45860703c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 192805755 1106 192804649 192804671
    0x806100308090609210f0f2d01060b040803041a18090601110f0102090a05040c05070618020a0909020315011d061207060801061404060806060706 64
    0x441c100000c1d40d00240e0361212504100001e9400305d40300d036401083c0c0382646030001c500c0c0c2401c10380240305071b102403000c0c085410701034184e29401035984c01d0041340300c10310f41c1d0b440d02450100a40d650b0401181d240303d0500640001d04105009594860600c0307094007082d4a800940c4d2002c01c0180b10511050524156518100c0001d50303100c51158ac5040040702d0500025154040d20300400100e400300e00c0e019001001031440a84540108d04c0e03552040c04220340c0e8040d980000140c09004000000708540c0201c00c0210980072030743c1a014080d00040d00d0035501d54401420b0717964070041d0200314241403083e54004480606102e25542c0342c02c1070b24899034a00c0400660b826180340010700145c0c0c0d0010381110780840c072821a03110a8480c0e0b005000d03410207000b02c03401704550808588601030000c00703c1d400d41c1c0b0b1036034585001e41c46441c2400700b180c20800007120b4880d111004c1c054 = true := by decide +kernel

theorem cover : BRFrame.Cov 192625899 192805755 := by
  have h0 := BRFrame.cov_init 192625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 192625899 ≤ n) (h2 : n < 192805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
