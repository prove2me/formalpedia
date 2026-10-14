-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0571
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:30:13.385859+00:00
-- url     : https://prove2.me/submissions/22789b13-0a5a-4495-a59b-25f8352469a7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 102517985 ≤ n < 102697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 102519235 1250 102517985 102518011
    0x30c1502040311041503050a05030d1107030e01120b0402070507031104020306030a0b0405070302040203040b1501140f07170408030c06070906082a0c01020a1101090203250302060a05090405 83
    0x82c41c0d494000c40d1854241d090b0113144c45010881d14010003102c1e481c021900042038600040103407030025240d90103030360b2642100b458500740042081480c005c3d1074186506450351410402d5040065507130080050560900315100e014481c030a44403070004e0200281b140005103001402d52501c1014443e101000754000e503c1402080095500001c0490902c3d402c08920074054446090083c248080c540000e900507000000380410003004001e03192040302d80b140c000c0f03800045e6000443d1074100300b0300c06d4be02e800c009016210701000c43c54014161148148800c804031008a109441c803508240d0200c1c4607074001040c452100d54040c407150364021711511b00309480c14240030002c0e010040207400000c117040304540025441012034a4850302540240c812501d44925000031400303540914883c100140c801d00400b41031200501440d00401d03070040241025003a80303182c4061030206101d070101130402040d000000342e02c034070b4007c0001c444150390b02941d54081406000617a400030341800081c40ca = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 102520485 1250 102519235 102519239
    0xa020a05190507210315030506010927050715050c12032d0105030705040509030a0e06040e040606050a12032304090e070509010b13051318030c150204 66
    0x26105007154104000a00381c22207112800900b240c15004200005004040c25000d0100742c603e440d14005056840303542c03c0c4030200c40b003040440864114440100194802c20041c0500703102d0740c0142d1070001c210f40f9140340c43c10f04115003903103448094406889a8001c2c02087c0304040409042d0402e40c089402c0c141d103066030221140d81d030b03041e010400f09216040400400c2140c40403d2225071004404160b030f600111030055500720300c480a01c1100e10911407244002044e05013070241611500c010f1002d541001412142900d410360090202c5901610810011510142d5030714158007032401241c000131441e0030304040c84074481a54014590702480c03c0002070020342c1c00b825071200c5031654031108005010700c00c1990082d0040750000100d007400c000b0b4441c0d403451b001981c40210343e0110341c42904c1d0f0343c0e121809411403141040070000c0100301102480b481c10f2441c032500e0244d800c845c000450303200394540d000b0307500c1d051941140002c0b00720712040c0a0002c1903030b0a1481044080f01185094 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 102521735 1250 102520485 102520487
    0x40e010807030f02010f0e0607140607021f0b0a0302090a0b0319080715060b070f02130e1203040c1809110303040f05040f02070602070821100e09011b050406080a020a 73
    0x40e58003d402030402140c0c0b030515030f2080c4918121252014090101616003440e0700d48100504c82004002181d48503110018849510000c2d0b80200c0c0401d010450240900244c2440f0152040c0308400303810a031517010001c0140c840c09001c901c07070020fa1100164a1b54510b081608019003150342502c612400380b40000407c0a250868a0031640f104a00d400e41340ca6102e00000f41c02140d02802000901244403400c1c080007a141c5c40c14207100320340210001c008111900301300c0310341c5003281030710b41c1c0314000c00807103a4039500085801c9401000281c28281d9030f040710040320303012140451a0580c60f1541a0100300b02d002c2d110340c1d00c500440256003400c0c1009111155123500384565407041e915545a6101002160704841c0500e40042c000e543e41c004a0408112903805031080000d0711000100440382c001c00303044050b0251000010300700925142c0350300c4403402c040107844000517558506100440148041d08005484034585555480d030303180440280581c0001032290148500410001e00b1803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 102522985 1250 102521735 102521753
    0xf06080c0a0e040e0d0f021005100312030f09030c0203150408090d0f050109110108010806061807020c0307081c210c02121204060c112a031002040e01080703 69
    0x400603240900101d9507990000d406030900c0502c10308240034078503d00102c1781c0d014050000004042c0c0807102d82c0007481d50008100c600841d03200d4203a0000c02d00910016181406070b045205c6a0b250100f10700050465030011940031090450124854080c2e9808500f020f2240304a9203144260348601403038252940140c40c410118128883c1030306821220030000003250807485079412100030010300c006880c014030501840c484c158003052034900001101000015441d104000c0908030340300041900701449203c2802410701010350003440b603102e2640d00c04000030740007800790200500c14420035045110010305e54000d00c1c400c1141d00406003045002c60184400701403408003000840c0321261030308034105030a41303201c0b02c14044c0000c0e448020020440c1c1d55030049000341d0040250440100090b994090022405040c641180c190402d02c410300a1108440d02001205240c0e074120740c20000e400e150b0415002d510143d8045014418801d00703052207030140c0070381402131201d20309540743c1901e6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 102524235 1250 102522985 102522997
    0x30509061e0c07080705010c0327061a10090e0612120304170f040302040606032c0f0a05030309070602010b011e020309090108010e010f06230a030203030703090f06080c 74
    0x140400c0700d004940307004819402c441940d0741211326a500c6032502d141c000c1c060800c1c41c916000180c00d2410341c0c91020010380d101d000004200c000c4200303904c507655621010b030518a20140308000800580380c07268969072040b040100303140e51940d90b0326050080807090340c3c0340600498050210b4400c0240b000100140481001088004094817941c03070f0b24141e0b41e0040700759030b19070700c0f4100070607101200441c402c054015a0710864061011030b485107022000c6600108200307400c1d00c0e09407d2035030b800a103580010519107072041651100345001c1c100e1480c02070b01441c2216143c2c800420084010400c1c0714410250520b803000b8066000b1500c0020b01100c070030100070b130a20241a02d2103518600800c1111810305000d41500c1c000d60703443d00403900a00c8524418491942892024600200b241c0301c0d0409503110401c0c40c608880c606040101f040481110b015040701d0b500101001680e030070005426070b0762180d603c60312014206104400c41d021585d100c8020302001c4000c0c040c6035803a80d400e03520 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 102525485 1250 102524235 102524281
    0x60809070b030c1614010c2313050405090f0616080604020406020715020102091816030b0a140f0306040b2a0702040905190804061107050a0e040302100e0a020103050906 74
    0x1201303642030841c520000004502043d600c0d100c040306005070440303080300d021200b001c01800c0c2c0d848191520007042c861001d82c4000380d11810001d100c41c0c40e25901c02c60f00170031020f003102e0168400041d46841d0060039200342c0008404500140c100e568404038040c1d000105170303000c0d4102454080082c4d515002c0d40500d01410b110440381c40d4030329100758190740080b5001080c240d001002c1604425509801307440c111480d042e00e04032070011501901500c1403501019048007d03003460604007909008a003025103901900c5604686110f0f502001807074091800b407040c041c10f50804218100e13030460717580d441413a0104662403000c942c8a10100f0380700c0c2d40e60140e0340031400034141e1510318240030355094030440202045280006000680000e0300a41d1f40135113502425912a28000f6501c0382a0f1240a50200160f030f0140301e094800c041064025110380101c5d840141c2d14400d0b10103549040001d40311541c40316040c1c400b17540c2c1c140946a0810255005808a4140303420b04031481c0504c522034003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 102526735 1250 102525485 102525517
    0xf0306040f0201210f1805070b160b0115091d010e040606170c01021605091b090603180706080601050304060510171e06060108041101120204060809070b030c 69
    0x4070559014098441114081d002c50044002514041d00001e200d08243d0400592815482e1070146c0200054030f400a6088001010042d01d000705000380da43c0110208045090503c980500282316562101c5c040c3c16551403500e58141c154200034540b88450b03102c1c1d100d0400428a28540030031403008981514030000c1d0142c280d9403507051190240c16150301c010170070042c3c01c034200682100820b814400e0f1600b6800d940f00d60b641c04000d060f0925840c066140d0040d44040032070750040000d01c90038416800402c1507401c11010100080c07071038000302e8a81303006c4259080c26108003401070015401800050034240713080d051010008100e808020001441c6640c0d42c030100e8841400f0410020080c070a02510310300900d40c0011003900e8242c2e051064060140740c15032641014004204d05100d840180d4505c842c0340c0e100c0d00c8512850414011103818800718000803900410b65000a1019092070340302c00005050140c42c003440c080c0c03940c1c0040080c5d4000d20a00c03003004007003401c0342c030f1626a1010300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 102527985 1250 102526735 102526763
    0xc0b1602010b060301060c03030e011a01050d0902040603030207030506010803040b0703050a1101050c070506060f0f1e060703030e060702010e0d03020a090b041511060c0405040e100e07140f030604 86
    0xe070700400c10211080d5108101000004a050740050021f41e034034401e5034140613040c120012542a605102d00d2035040d021159412030403548242c003e0070295800034800b04d226502c6401150440d08903410a0340181c100c0402403081c003030200030032401040060300640c0b13054075080b1894010b008201000f42001000100da501051245e22400703150044e10000b00010304058171500c01584c07008e40c0c100c0d0a4090748000901503d031800c0310040055015104071013a410300404c01000c41a041d0040c0d001400144003403040e0740300c00300a0400d042c03182e200000c01c20468600c182ca8004000c080d0000c680c1426021010388101091604000116080240c1c681e42007120545001d0015080311847c105d000c50b0014200c60329104d400c01081282c2c9602c0e410b0503403103d009072501400c6031030300c00d80c00d4100400c001c0390800f5481020340c0d84521056440340d8502120880540d91590241511988600c60030310400c8103c05500300340c0c00044460452840e1100d020a45a4500900c0030b080d949201007a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 102529235 1250 102527985 102527987
    0xc0a03020114070501050c040f0b0c0d03050c0705010e01020703030509160905100b191e0c08031302090712050127200406051809010b1b190606030b070c0b16 69
    0xe9401c070f2075000c8000e128030b1a00d141c10f24150f400070311801084500040340040d000c1e610078215410501a40040c10381000d000a094009d00380281a03101e01c2d050070084c80d00400c03020312414030442d40131400075030b460000f405d00070165480600060803035004404e0158802c0840441081225005600480c1983d54401300c0f01350300c0d507598803075041e003580021401004400006048030b1941c0d65104d84039001002c054220004250300304000128442000c104049500013024591100603400072125a0f41075501242c40d106042d00c48501140313400e6006c82003034009008890160500301110310f89072940d592821180c03010740d580c0c00d1380d00d5a0f408021070ba45403491204400e040d68403846a60307403a61810000c00c1540a40007520003201c000380981110b1800005150484800205680c1089400700750800d2500080201010901c41c15100c0b0140717400300340c201002a8042c03480001c01d2495401c00c841c100000034510404c10081da5843c800080e66400102e401c52203618040c0550050200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 102530485 1250 102529235 102529237
    0x103050a1d0f060f07050403061503020607152703050702030a02100c060506010203030402011d180a0603020406140109061107230f03010902010f03020702010509040203010321020c0a03020114 84
    0x180c91a92140e01450700d82035810000d00d01c08a0700245084900303507514200c000c40d80f01400c0c0c490340c0015404001c00c10205800d03401440c4d52042d0341b881c903240150b0b00c3c0d0003d6000e912280040350008841c5114801c121028815040d40072200e261240040244610070446110700d4040107052200104240d0259101000b40e4504668041d10400308140442005422620b00a000b120400c1c00c0c000017400d10351020050f60b02030741d41030319002c42a010810348808004050081660841c0c60322445903007001100c480d16014540c6150300050340c6040d03006201c00c0e110307103401845840c501a4555920340e42d01903440b904645040ca422400174181440d4036081c090140e1108100c0c101c0c3d5103005042484800700e40b14010012543c11600b101100140f41c00d80b520784002074003080705020120b220740e000c0c0c0c000303040342481450700510300700c0d036000050200e81081c0c1085c2d6504280a031000341d1602d00d51248228195130b070004040640424000420005060000074100112103c0c035a1407804640 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 102531735 1250 102530485 102530501
    0xc020f03061612020d0501030503030402100c0c030807081603030b04060b09060d0506030307120f111f020a0509030a05010903080c030c160812070e030c040606051b0f030a0201061806080604020103050a 88
    0x105c240141e5035241040d564940060703500ba0310a030794021160b101240601500805158007842c001411880c50300c07805c01c030390000c00382a0307844001008035aa08000064440c04e400e403003605d0004081e2080410b21088507a40e80003002c00c2c601c100000041075491030140c0d1800403075408080f0321980c03603c1c04282103009a4000800e10316030898400300340c41e00903004030341140096507400603001075809080e13610185912801444940d45030340c0c0c5032545858005041000880c10b140d032a0040c4800400c1c500b40c1c0a070829601c07650b40d032183c1c07010941d00c5070b1600d422040f051045425400e200d40304000714880c8004411010960986d55020400d681c2d09640c480b441d00d400c01c0c10285060007010313242441114001d442809103445060041c43c00b807040c42c3c246c41035039654030b00341218440c8141d000c9511011090380d1740303c0c8007000340c4564010001010070880303da0000c41c11518044100c211850040c0d640c2e59002d0400030184140c8000185d8560700030340910300400c1039210058040000d003461 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 102532985 1250 102531735 102531757
    0x2f07060b03100902040b010305060603063105090f010501050102100504021309050102070201091a0706050c070503033301050d0c111006180b0f09040c090204060c020f0306161202 78
    0xa9429612005110f5103c50b4960f03000f681e041c80b20300017a00046040b81c60444d03c41e075100d00f00f8000300d0300600313200110401c0d40c0351054201000715840c2c00100e4180240c0341e03e50034a651610104020018180701180b5082d480c00300030f024a504090010b91101c80114104000c030340d980340000d0a650b9914102c0442c50741c00c4004000014650811034040d501440e002e0340429008000040c1c441c002e80f6000f5008010b0b0a1898100b4006035a01c1d00581b00141114a80b00000e00c03089000c600144001c5000305540d111b5007500042d5024404111813514001c4403100c541d40641000b182d0700102190303c0d240c258400040e8412120b60241da140c000464502c40b1881041401080303041644d000310152885064003551001c015072001d0259000701d00065001240c040d001001802d1160b0300e9138000c0c1c8215407c1c41c00ca51036110b05412a041684100d000412400e480701c15400d01500482002005401400071450400519107400c40b040310078004011120721610f44009890381910112446 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 102534235 1250 102532985 102532993
    0x7090909060204060f090501120207030e0414010e100302181f0803041a040308090111100504060504140d2c03120405150307020d0c080c01140a2f07060b03 68
    0x280d05100340207410900030307400440e00c055400d09603d0301a0350101b00301d4205a540d103280480d2480341402942000c501201408009220b804441e9200c0c021005422a00c5034203509a615102150407540b8000c0c1024004500b1800f0900140e101d0380c00301002500c90f0316680400b51581b485000e580c0070907011500380010544000b0450440100003041168055110000811040e032030742c00651140d844001c6c01980f08020094140d40201d0250300d09105001c1541c441814030321511302500c904640444131705984034108010044180100744114102c0750040c440e0419500c405800b400e00e0303240303c514003440701043c094001106208041440c1c406401d490792001850f4820000e6001806198428240c040301c4148a0729140241d900c0b504c4c3d540d0081419805512060b00d8041c2640010741d40c0082c03c10005180140c04d000d100c00800c01d43c40c81202900d41180054101c07410700c240d400a5104c914103c0300038030908440144211084916079580d038510b460700100a0811010380750b0140a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 102535485 1250 102534235 102534251
    0x1103100501030c05011b060b15030f0405010c050a0c0f0813091a030a08070305030c040b040e06030c0307060e0111071502030408010f050708070c0614010b09010e0d03080f070909 78
    0x1445030049412a0311606410800a40340c100645600d03a000420000c0d031148a1985c1011584541081064410240030b1920754220139030080b4140d0f0007158007481c0480404280030400c6030034810011920694501a8100948000c005105101003640504010150616041030081100031944071382c0150100402480c0e80b048000013800d0701101152205107072196800307040c11301041042e2901e600024491801c0541d0ba010742d0240c00280419802040900000c030380d0303a0b02580100042c201d6503405100c18074103501010b00d4480c03641e075028001c0e0040c4070b00700704207600301c4960b80d40081c003400e03c4602c038208440c00501e80000c40e03200d4615541c503148444111034000c4005c0c000e9400142c000d100e10f121088110080c2d400550308100001d61078800902401c3c1300b034210040e9a0311820010076184903030281032a410601303810102416000042008072507800101e9200c12420541d030032112207241340c40c06410400d00030144081030344140300280801e44a07040b0000940480d05081003421 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 102536735 1250 102535485 102535513
    0xe0102031003110f03031b01020405060f040905060103090c12030c020402030106030c09060c03050d0f1d010b120c030607050310030606080a0309060e090a020a02010603020a03110a060c050a020d1103 87
    0x801c00744000c1d111511141d00245031820031000d0740c440124054001c5182030045134090390800101c44140d20155402e00005c00d16680b003600412600c9810f075249d9031140d0401140c50200e81c07000c1c003c1410b1600c0c00c0c0000340061815030303000c02180d101d1800d00740c3c0c4000c14102a1040c01065100950080c070000010a00680692118001d2180e5a1340c0100301510b43c04183c0f682071181c4d501134003084080c00310713440720323950303a0000d0b1180041050041041424100e0015a10800030b296809594407920311041300d08000308003140d0080290000c01c042c9103c04003081d11000c02401c1401009000800180580102040200190740c443c8040000300e07031b2620300c41e480c2e2514003801c50000303105410003d1840d1003207060300310030341c1d00501001c03036501c4240d5450000d5021020080c1035540380c03000000541e80d620410402140181c000000118044082003511182078000405100e190700102c4081200007464407000c542c151001145006241003590489001b0b4000300e0381841907424800340c030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 102537985 1250 102536735 102536761
    0x81b04090504030e0d05070311060d0f050603060901110f07030504080604030302041404020c0606010f1e0305090706030207050604110a05040603062f0906130e042402031b0c010e010203 81
    0x82d41c02691032000140380101080b600003d05440600107501841d014000325120101e00081741e0001030a40d443c1000382300d4114269111011030038005541ca40401c001d030300301480100e500c905204002c0205c41c29152101c02d42c0c0c040d40c0c0d00d01c0303801000420701108250244c41203901074624082294075a18191a00801940c443e000e05000c255891905103010304046c000d4031940032030b400c05880307966140e10044030340c0c50700788031180100044013082c540902842c2802828001250b42e010030146030248440e80b42004c164031620405204000010201c0d8010906a401951041d0083c05e8000c074400000e410001c02d401003980145401030000c00c00203941d000300822489441d41041d07030030164803000341400c858008904c524504003c1820b4034502500104211030412202849050f01d038030400b508460126000ca8680d65000445010302956807100705000f203103060b05600c0c40c50039540c7d1824400d0240051580d000c004244591605003c1d00f201c075a80d8a480c000f15107914105802c01e5203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 102539235 1250 102537985 102537991
    0x3050903030903300702090601120902100c050c0d08040b1c050a0507031a030706050d090b40110607062c01090b04020f120d02061603020a0f081b040905 67
    0x11061103202c50308107000d64581074170742c40d46d0000c084103410741d00c02005550340c1d83d151403039034190b0303075140d1035500103030745000c0050030319402a80c550140340040e203400da1800542903e03072842203154194810000301d03403400300c4054036900118152078084c10902001c00301c0c044032010840768201310800402d40031a1703012900c1003041c0c0d80c007400740d00c005020140c07070103900750342468042d00001811304c403450007000184042607150038005482c200c1750300e400c0d40000b0203940100710390400341468012008a24240e03444914000e91460a65201c456104034803d040c3d2401064032443c1d02005122740e03a8203041e0f8000769003050f020322440d81240d80b002c0981c802480b130b00c4d00400d202c001051400105114200d03071950700c00c2041c2482e8035030b0740820598419007054650311a224003400c3c50102c40600090603101101d4008114504008500d841d60002c5040520100352045c090040081d0340010350700b4010f1402d050404407602c92100c075805001100340c51100c804d500082c00501a1955405288 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 102540485 1250 102539235 102539293
    0x219080d0e04090b0105090c1b0d140307080601230d06060f0e0a0b0c0109080d021c0903050d0e10021b0d020a17090301020403170702030d09060c03050903030903 71
    0x30810000400b00411200c0d10000901482d001100602070707410304081582c2c01401c62a14182400f1801e100c043c0c4080c524500c0880070780000445082440e00200d04100d44140307594031600f98680400014000d101c0109040c1c100150b203911400c6000190001c240100303006e41071950b881e0390105500001d0101442010009150300b0400300f010351243c40340701c10030b4034014448a2100d00d030462224407a08066a105ca65560343c08800c00041e010f03400411540420b90b40141c1c84801c0c442c00b040d1000003130b84944404074103000c1142c002a6016044425502004100080040c0340b01c1484d440c4c0715440300318984003403002a080300c550703111102511a946011084a81241c00650300f262103400c0010300600004190454152050502000d011a6980640014185a030f42c1e2507601c8451154031300782040340310020f0801c00b0740c1402d11845144480b40d050052640b40340810007072002d40c50700009010004080740207a429074091003103420b45c4030000d041314044101100b400540c2d050304030f2014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 102541735 1250 102540485 102540497
    0x50a0c120e0d110c120a0b060f010c03081015020c0915100f0c020d06050411040c080601050903010b090403051b0106030206090d061e05090c09060d06090219080d 71
    0xc2800ca195020305070942000d100070700341000010109860360110002d071803890f070081000d0248652180801e4a4103259410020314402c4800d040c01c01e2429005044940070f4040004e0a4426076040149040c41e180e051504401d03541d00c0d50944101e14209401141060f289034009894566000480f003100c0c1038201c503401c0d81522031852110004920741708650700090010042d90040b40910103403480300300c241c141081c101055900046900d000000100e50342680d0350305000603c0f07411104081c41c0142500c080120800c41314010f4034400703000700081e04100e0002000b854980b401e402410076848040c0100f00030703040600d00900b1542000790700d48a0849840c0405840310814003031501100d4002e031602e440e0625140c00c1c040d690310155810794040303803580d031040c22201c07548414807000c003100a4001400d04100c890182842c640240d4644074034064418002071365a0000c940c00d0150303000c0400903403549036201080d501018680b400c05e03100c1c0c94910008200f0404600603688100940d2070f5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 102542985 1250 102541735 102541757
    0x307030c152a02060415020601030c14150c0f0a0b07030c0804030909020d18030903060b011701050609220b090f01031203050901020d06031109100806131104050a0c 72
    0x480b80c0344102124000c1c444501d41c4050051002000b5550406001505851415456002141a00b0b0f18101040010303030041c03004105126400e0180c00103803c404d00c201903181d04440004078003003045021301e040300c100000e549a050320100a560403041d05c00060329803d01c03450516001d03e2208564080210342064030300205548500e8a8900c100d505445000d01c481c2055400d000940090030a0382ca250340d034090554417003050070b014440e150311954507036071018190301d406410341d040c0030385650600100d03841d048426100c005c449410743e03000f9108079031624840000596143d4400070210062408245a071407004c500e504070f60840e100507680703460203840300d507030380f45240409201c0a48001e800d40e104800c8644a03400564001e00342c00009400c2a1030081c0904c102c8a4650084508214031030000c400b504003046216403103004441521841c5241240d0036890b20320040c40340090706c04440101c1d041250706200d0560184024008200c4c80c0380080030800108811341061001c03418281034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 102544235 1250 102542985 102542987
    0x2031b0606011704060b18060103110306030c1302040506040e1006020604020f01080a09080d090614010b07080a020102040306020301182004090e0f01020d0c121104120f020307030c15 80
    0x208500030071040e911034000c0c88860b142c5000340040900200c40650302e03035120394050b5442018841070000800d48075410313400c0801c0090116680b200008910680034020408541d402046c8060900c1083da0121801c08001580c20000d210300d82015501ca8070205011501e800941603844c0f0a0542d22000b582541e104d00382a40d8030082201c4c001d41c40002c408006915500c1000c0880d080316510178003165520007940c80003100d803c800500001603a4a0701c1c40c1080c00a1070140c5050800341310006c4131b140d4140a066840c61241a04c007401205c400506c0c1480c1034400d5040383c0056400900c1107440b9611055500a826101003c0f002c12500300b030401c61316140c60004041d00540100d8145181605c2c1a800902038900d09250810b00d0007544502d07040100700703000420700e10400c10400a03000c900d80320064200200c409045a1107890001d1404801030740c00100c9054500d040c10315a60744016203006040340000d810700035010300135140e001082202500034481503c00c1824089170a41c4920340c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 102545485 1250 102544235 102544243
    0xe0c1002010e0c0d240b01030f050907030f05100e031b030a091a0706050906090f06040803010303080a0603060903090509061c06091b0611060109111206010e0d0302031b 74
    0x31446800c03607864101a403401e6001804000d1040e5003c640220410710140c80c641516085c4410b5651035108440c0c03075681c18403a8800074400c10100b08850705020071001d55070041c0703000c014601a244892039052040800070309145450903a420f00840c1d036a0418683c480c4c00c06100381d0220805040b0140c1c221201006031a080200c1e65244000c0514007250100903010441491f0300c2240e0821070640031607024001d032072040c8004401006035090400944d840c280c40116140402d400920900c4001111002200d0440b034142c0752410450f10b50340e1851004007007591004180c0ca1810042c001010f4019045904a400813200c00d84503555000502819001c0d07006082d15201036112400005161503000828040c040d50809010030807002e0210084c2d050f903040310010961041c000c035501070301005854007401c00450113200383c1c0c0180801d1001c40c001c249020388000d140c0b00004041e0303445100307129106800142038040d02c9c40706040c041d40300c1c0d01442040320600303600101480c2c0814001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 102546735 1250 102545485 102545501
    0xb091513020f070318081002040e06450f070906050c071211041d010b0102031306080411100509040b0a082a13020a021902010f0e060408010e0c100201 66
    0x282401d850102c3d190307400c8030f088013000c0500e04400c22090010a0054040211907000100c402c00181e03107134100740341500c01480080180e44140ca12111148000b40c110761440c0c5103004229a51040b008d1403d25007c14822a00400c0d54a00c40a0108030710110000e440b940110480c2e1540216152124000c448a2058030300d60061548400c070100681c000154140380c5090203480c902111b01c00d01000241030b1079025440d541c6445240c91180e480b041c080c80b86a0b4484824002140f818242d207401701500301003407007100d0501486a00160a0024200f131300074107403000528002c0c0314102c207900541150010004140680c0c9082c01e2103126040141d0041c05031801c10008000c820305500c420f910f070004c10012207109a01c50b543c0200107807204030300b041104100c1d076405030701e800e0300c08002841c0c141e0110040b8140d100e007840000260341c0002c000d448001d100c0c61b00302c0000034801c1c08a04d4601c503030744c80240c3d590b10f0404030f602e1420020401943c03501044a029696100700782e0120300740e030811 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 102547985 1250 102546735 102546757
    0x405310b12011122090609150603091709130f0219091a03090a050106031113051603051f030501090b0603030a0503070509010c020402120a05010503030a051204060b09151302 76
    0x100821201001840003d948079015015620703805a05e40c0c01c40300594000d51b10100034692204034079040300103207009880140c071a9160410224105485800300082d0841ca42d002a08001480501c90303280d40c201002c008024210610800720030545101c025845441c0003500328154425403080c0e0382c4600c410780219402c00040d200c210360354100c03800139039001402c0030b54144903800b45640001d50a00641004500440c0300031000c00804041c07103400c0d14039246260a592805c0100b0880c4c902e51840102d0f80140c3d450001402c2c1e4503030182203000c0c206640d001d000007414003000802c00c1415089401d10394032890904505072151800e056032070003083c0f92400414401c0c80004c00140c0b00704050251100c0514103029100810f401190881c0d001c1903010904a0540d010007284a0907402010300500e400d030001c500e4503021090003085401041200c07034a841248003c501407204581168440d03103801081c055117428036031281050140c0001e0719034082c0c090412014107640c500e10a42c0c400000c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 102549235 1250 102547985 102547987
    0x80c060d0213030f0606060816231308100f02120a050c0403120302030f100f03020103050a090501150303120c0e01080402040908031315050402060405310b120111 71
    0x114400c194081d4208071603440701550b0010000010805103800340d00040d00070a800a015400d002d001800d6050091418200079844004002c107681e2005103401420550303080104c40d01000d0315040c00700e00c60783d001d04202c55402040800c3c8c81c8404120081015500c46080101c1c040d00544401a8041d880100e10164110800541c0c45119500080d5011341290300c890b15040d280d9640b010300710080825280042d40c00f20070000300896441c082d580041442003030b0f807a41898114240d2201c1e049000c024105515600820f1000c12a40c0194445550020003801058004109410b1004651000b41d00180900c030f5040c82c500c1e0184104d80d82507109039158a50100c0c50380040d40c01042c0604100d0b0442e6890003150701143c1c2440144d402480009205010841a41880101d2080300308044032080d142209000c0180d071000111011118250344055810b1f80718021304601c404091507103052080c0000c00d8005d460210f030300406c8042002ca032800d0801440040d0707142290b00301c8030182038243c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 102550485 1250 102549235 102549247
    0x2071404060b09190b0a0c0201170903191e0e031014070c03052205030f03030c03010e100305100506120c03070927080909071b06090204020d05041b080c06 68
    0x81189546182c41c40300c4e0070301e20b6201d95a4070050320a5000f00c01c0e110000c1c2d80081400c04542c4e2282d02403040c4a58171303405501c0d80c24500c8503da1a403180030b00720301d1700001500d038105c541401a80c10041301240c3e03208001c0545898240500368a07810010f080c405e01604040309145040c91040c0107031304040e00072207066540d460703405070b4070405801c000f80c00344a42400142200341c0c43d43c5650740040040004c00200500d000241486e03c1004c3d0100125900300744100814003440074141ea044606603501c10034151a8800ea01c800c20185030406000c9005001404141d44065000a40a1401907a031000c4d040700d0044040c0d00c0761000c0340d8040d8160441c2904201d013000c250004800d03080144440000c032200c00104400c1c2201d5004100d81320728002c910920300e49041c0340f146600c4401420b01c0382c443c0da00901c3c41e0f8041241c51000a1a80703503164510401d545aa50698000c40f000c0c0001300150b0906040086010503050b00301600600201c6c030104001102058840e15014040d00c3e0a052003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 102551735 1250 102550485 102550489
    0x40b0709060e0603131b050319030507020904231b01090302030a020906010e0a0f140402040510050d02070b0c0d15120312021204080d0e0705150a0905030d02071404060b09 75
    0x540080c28007075149a056800b6804120682da0700014401b00412524440d4a807809040c00c0c01030600d500480b03001da85400e00040ba800900b11001030364109d4000031f99945a2810022074624000030400414500c00001c0c002c03500091610f1140c242540301442c948408801124036102900000350141c1107400800300504007800c3c0c480d00701c00e0505043d424a0310000200751020841e41c8103064442095104000c00303601c0740c00c00181c41c00141c40a614003410140412428040d5295400c100140090380c1e142142040d41500d044a0b4424800c00b80c40c10820311400b85604071044c00c07012185016a4501020030a89940b42210040c0007038440404e0b098400361080348000c003038030305802c0d004c002c12075082d498424260b1003684103820090301c8015181c140b0301110140e1309030449540c8031240c203000750380d10419000307410045600780e00c0e91140040d0007140c0c000c0080d405603400d031084a01d803540300e03500070030004260b50b0b4180c5491010041c61b010403042da14507108586d09100d042184130300078 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 102552985 1250 102551735 102551737
    0x609080715031e0e03090a0902040506070b0901021309060e060108010303080106030905030721080a11040e09010212090d110304050a0504020f070f0c0e06120c01030c0e0306090303040b0709060e06 86
    0x75880304840039a10b021100e1001604e51015680185400c000740e030340918503040581a02608180c202141018180408144c86100da000301400300c21014001440c8200250115503003203000106c00c10f0707910380c1c03101034001602407400341c040d0810340e000c00a0070315403080400b24122034040e81c400b1184d07440c001080e002000440416590348c00100098400700301507c0c6c8500c01c007209840020205000b00400514002c4081d00c0180b10700d003811840b40008119509444c180d410100741e440b580e4944060042c02841100c05002624621108001c2c4840703010642d802411040e850b035001c14062021159100d21584c090349a1140d0300c41828096824181e0180032000c0d1502c01041c50040251980600510082002c0301d8000f640741d014007146551801c03907a040b4409640d941c0b0141031941390345854202e03590920341007665130101c410819108000035014140042c041e80c6440c242032001503107a078000c440680b040b50702580414001846040c04900f288d16950760708070300d1612203041082e6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 102554235 1250 102552985 102553001
    0x10b010c060e1006080d080601110601051021050402040f090203060c0901090b0f0901020705040203090615040b060403030e031b01050f030403030b090703020c0d030209330f04060908071503 83
    0x2c14480c007021804801e5035031088001a203103420090851882e040d4000304482c01c0244164104850881c09c0c0750203140008a260546a049034404401071700b10804940c4440b00600d4680030400d40c0e100880f4070403450f070009000314002c0d02d013840000034560412060302c085100082d059809640080e5540d05520040c4c2204001407501412503580c445205541c2c0c1c0060030403030081307180003075288103a40e01003200400404081e41c0c150b00354589800b480d40c4800c40203154802e8140351102000345903580b940004c40a040042a5944554807410f00070305e410f08151343c450080c0701c1e4107020b040c0d42080c0c4908080c5404140d41e058988007412203050103d80002d4800c805054580c0114200c03a076845103c03034410400d940d0010307140c1c1440107242d03140010510070030090610400c1082410b4030303081c0c0200080d03402c21080d00c1d0748071a0042c0401041803018800900720f20085014000649900002d1048542681c0d40b400d0040d1510b02094882030548102030610340c401d201100c181d4001c0d002604 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 102555485 1250 102554235 102554261
    0x30308064e2b08040c0501050c0a051c0809070b09101b03080405150601050301090209060d0204030809032b030504030c050d0503091009021005030903040f0b0406080702010b010c06 79
    0x4440000c038050500c0c003003021070800d40c40c0d181030380d040b169110b0200340b944800c0c035185080f2069041980350040350b8040d50143c14104a4002010213803410100408401d01d075000c0708990741021403100d003600000080c1d44c02070000e00f12070042461040b00013030030410385040141c504e1074004c03910100040c2001c0e06504030140021101c0e02c1d400034280ea8024132406000381c48032011881c10b4501a0b040c030703460a407007204c0d409000d024007185982c80f50550741900c03800d11005035100c04010008103680a003080703488045000080110070050110050001c403003041c0c0171100340c2c0c80301400b290f4a105d84090a00c01e003040318080c1c84241446504150782040c041d09001884000c981c03545400e002e490503c2d200414000014850741c480f0800003400c00c94030942080050340d00ca503000840c00b5403440e145004000c03020000c00c41a0300d0500840d0028203003080c11900c4240d64002c00b8030719400510894021a00102c00201c4d824018001c3c20088041651440308000f4541d403414028900148025 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 102556735 1250 102555485 102555619
    0xa05030613020f0909180c01050306040908030c18030304030b040303050408162a0f0510020304050a0311010e0612040b040501020409020c031b07030503030f070c0c03030806 76
    0x264026640300900f205000e00c3c001079034402c01e24041c440b203c00060148480640340c05044420150080b4140c01020380919040da501d454030400600a00040003000d03016910000c2440706904e204402131002103000308032000c0d848120000c041d240c1c042e41c0320140c20380714608005030000b41720f039001c00d50082c4250030b80b9003030a900e4416a246e0170181041140c0c49811040d0784c0c0c200740c0142c040d5081010100b180c83c1145401c04141c0d1503100107901c0340ca80255103ca112808440c028401d660180201808074444141d81e400c19240d45184074040070f0100e550310301c4200c040d06082c0211b41d040c4115103078a1015131100d0795039994038400184241c40c507542c280000b2079105010300040c00747c1a911401591144041c4c0110b003a150101184401c81c0d51084600704001000801a2a0b219501d5200c218140e0791f0340b2000c1d100a8505013004201894510020042582020000780540b00a41d1004010000604400091103072500c0b140c0c0482c66030380c100c01c0074034020040d1400403000e901d156 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 102557985 1250 102556735 102556759
    0xf0703060905040809010306050609100c05150c030f090706200c04110d0e0c0d020108180703080c010f0501050310020906070b130b0912040905040816032a080a050306 73
    0x300b1944207507011070301d590b00003800340d510351303890301850300070381000c43c7c00c0c3d840c0a50300c9001922040751a22804148241e807285c2da4140502442400d46210500501c2c00f5585400307000c0c240d150b402214405044212180442ca501200281c243d00343c40d11906c800080300d0180d1112401828100161111f901c507150702e031070050b181c90256420030100443c0c1035840700107004098041c0d443ea1442088141d012004a84050780d400c444104501c0d028286044181c8038860b001a03c102e420b14040041d00c03ea400000802c01c0a02c0140304503650071000300300104440b0401c20030b4075000c3c41820742c10f41c454110313545980d01e150f0051180e800300401d000d02d00f00c295960608200f0045401c48455100b942c070500510800140300e55100c0d5001e00a0000e9451b902200301ea80c0c010b0340203a2180c590394000190810100c0011501c02654030150341124205a280090500c1d02c130414140030000c15504043c0010380c03051001c401e0b0b6901543c424108000f105080341c00e500f00400e81c42c1e0003404a092 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 102559235 1250 102557985 102557999
    0xc02010e03030c01062408040f030c02030a06020f031005011b0219082b050a090e070309020306040f0507170a080307180308030a0c090503060a0c023301090905060f070306 75
    0x103150000d08119005980d03110040d142489203401001080c0140f140f22420000099909c100162801c0d6150520041c2200c490010030324218041000070100c038800a254454500103101440c030461a20340c459000e651110011220b54034031034007000f4400080b4000b200145820000448801c8813680b00c000101da035680024500900c2d008060981c40e414800420440614515860441110308005160640c00c00000b81002014881c10030450301110110b01254420b13044050080e8005048640c0e60a1034105003900c0351081800716440e02c40c142000400803220401070310202401005022202219264203c096100502d0354080100301c52404400d41c2d2001085400746000300c00b41512450501c1c040380450b14100c12036001d1081c00481049980e070001a00b590060a02201065074040400c09901d411121006030981f03a040002c43c4001400003c0c40340008002c40d050691180d9899a50f20100c8030081c001501ca5003291740051180103030002c96070b40040f120f2800184180ea14a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 102560485 1250 102559235 102559241
    0x9050f040c020d0e2d0415081f0b0604091a010e032d070605040e010b0f09040209010c0821011508062b0311160f050d0f06020a031b0207060c02010e03030c01 69
    0xc1a44c0d0b0100060950000a040a210f103410600c07c1805451410f4142090709580300c01040d02001030f94421103040078160b186410407030703c441c0043d00c5e03551116104c95952010700b0041c0d034414400401407001d5071072984a10030034030280c2c1c0041c0280c6900384503401c1034100c40c0c1c0c10801760720841003001c40031581010b0401150000300798541d41c003621142002907808900c64181d205801c40326087c8580180e021601c3c080ba04850740403900140e49420400060b035201245181c041c0040a01046017950a1003403040880302c203042030b02040d500d0f03803585050310410810b8601100066003003800207101d4105010242c1000da04161074500c00d0041c000301080e2000c1d0302c2011400202e080a880d407900d1800c100b142d04060765541010701503401e01c02881400591885020b10508480503840c09121101d03c410000b0303074022070190340c0c0711402c0c0300140c050003040060100e11410385000401851022424006803401583d42000e03950803600119901402e41e0500d0b981404200218444540c0901c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 102561735 1250 102560485 102560539
    0x80609070c1106180306130b060402071b140f01020a0c0b07080f0a0f0305090a050615010c080c0601030b0c0f03010e0601110a03020a0210050f041502030c06010609050f040c020d0e 79
    0x100043c10388409110a2604104d0003504003038060344c11030442c0c00010b000c0181e08c2c1d8030050503200182c8803001c0342465a480700300301131100ea0083c0b1201c400f18814403000c2240e001420290380181401d4484001242e40d0000d11034050011030065006101403084074004008603402a40114140f1001c80d4014070594404001130010441d01ca01e0b030302c4581e0701406020b5108844801424004405407030b91034541200800111600416003400840784e80102460001076410052107510360707400390f9085070307194001c0c001614819070b000005852000000111240d55100d4030641e4216440d00a121a4201000e40718605024500e290080604000c01a041040303010368001c0603015100d0042c0010102860780c90010064100224044a00008122421502c1e0703d86c0300d503c032011211040b4214001d40017821101d001d48400011042d0744a0b448100380c40c4110781c070580c000d49080810007120400400003015800c50f1100c008058040c9500c505085c0c00902840803428600003a544105092 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 102562985 1250 102561735 102561757
    0x1120209190b12011403060a0509011806060807080606130903141c0c08060a03030e030307050105100801051609050f0f060409140604140c0f040306020406120b01080609070c1106 78
    0x2c00c00c41d07000b001e403444a900400c80703840e005810b81790752030120b511464002e18084911342c44402080f01a0025445200b400d18035150030001000380346403440140585100d04011441440170100c0d00e0350002c5001c40c05080c1c000c04440043c12031010031000303401910b40541c01e00004610b01400e0300311000052290044984003090102510800101114500c80020041100b03120030803d031a140c0f46841000e4039007508151013801c0a010009166104000c0000d0155080c0020f00040001d41c01a110580314884001d0103da130f80e4501c10200b4a011203032810004510b50403c020074104007050440050001d0140381c00f4003121070100c0c200d580154041c0040315a60750000c000902e1460046812070710498090125009080209a08440140400b13080d120300049031b007a14240d0740c0445000750b0380440255112681c0c3c2001034115880c002041070403d00300301030a00c1e990f1084201520443c001000001d4984888404503809400304e03008580090780500d080401e50ba841010300006524 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 102564235 1250 102562985 102562987
    0x110a0c03020112200c0c10080103020a0803030c0403030e0102010b0342060402031e0702010504140d0815010c020a03050a1109010b0d02030c0714060603010c090501120209190b 77
    0x40c0d0301c0014440c10300403141180007480c10714007400d500c00030040d040007101d8807128035884070b0303000080600380b01c840018298051462403401d031509801c44c003190b0490f402108c24280c1c0036900c0100d140c0302e100441340408802400c100500000b40a100b10445194040c03000182410b00c03480031038508050762102d0202810040261102640120ba000400303480070a40488001c90620f01c0c010465005410b01d4415070b00031000403503100b2115006801490728a00b0040e150030b01800180c000e000903102904c20000351180510111030015030f508050b55196540656941c0301800019481c1c020945141044149403004025a94061014000d5401072000e030a10311000e140484a540209107031500614000b00104481d20300001618012840b110015a4a588110204e0300501c1503c2c4018145004040e91806c1c002e40080d9041c8a2034065000300869a01510241e42e101c11078030070607000900c0720a8200d41542c0d10380160404002c041c1000e2440348100b1449102031505801ca4658040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 102565485 1250 102564235 102564239
    0x172a0a050d03020708120a02070c0f08060106110c0d051009060204090605010c080d0b0402091201020309060601050313020114120c19031a040207260706050105090c040312110a0c 78
    0x36081c010910389440070b0800b1032400300180e480020a010b2400c0c68404190340c100081e0b0800c4107501111030307031903000000c0140240c6500c0300d06400c5484d4000c92070644110300000c03402500900000f80b1004c1403d0050181342241c0042158410314600d044070180140300b03e030091042c1d1400b03500000303403241c1400768481d8104203040003114459481181002038180c0c481010601d03a00840f40084410f5601140e01000000030602a12a00300f03044d4000004c3c0c4a07070008404198055030045030710b80242c07049500d460300115000c0c001610748104d15550003001100641c02040382070013800701c6d60303402c5040c071000074640606514221001c2c41c0c2d49034006118001d0340c1151044603203101ca10f043c104480e0b03124000200306405a4009a4040d41d4001103810521000755100c229950783c2c0b0ba94008404181c6a511610360810042103070100e040c0000400e051400300381c41ca05c0b40e911014a11300f442d1440e124405450040b02c2d9241c1801940c14081c0340380030060082c00d444601401080b10018 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 102566735 1250 102565485 102565493
    0xe0109031805061b1207061a0d12030b030a0804060206040308100311130b0a0303020705040609090b0402060901050403050a08030601140306010c120210050f060f0d172a0a 75
    0x1c0109240d507916841c504040c02642d0350304050b5610710031900000c0003000e890115503480d28a07008844024124080b841030100825070700009160080d4812241e551021f06c07082c0000c1d40382c1035500800c084440368441540030711907444044580001002c98080c1e15581d102d030902d42d44107402c4000140c11a03000c020505d40c000da0030320f4001505800307024406245442e800020003c4508141c0b00d1510200072003400100358000450485c4000d01681c0038664914000e035542c410740c0b148d03074011800c00c44002681002c6202d10b40ea41c0780c003c008100d071640c4036400c00840e980f085025606120041c40007101240007040301106490ac00c50b00250350b81002c40c005001000981056004403000304100001c9980c01111b918100368440d160403004d0072a84e070706a05110102c0b0080d901c061410042020b48102c060849004803c25500700b5414400d0f0b1041c01070541480e00081d050103501c00c0601e0b8040e001500a05120400c03a89a0550701c1d10000e50504060101ca030b1090641d001081c000144 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 102567985 1250 102566735 102566747
    0x901031101020706210b0a030209070e010e01020118080904061d0a050a050121020102031c0501031703010303170603150f04050c0406140904060e01020a02031e04030807061e0e010903 80
    0x3a14031382c00c2c001c8030040c25060030214950b0741c3c200c610801380ca038114107100d03840e06140180503660043c00c1076414a807006006084421812807140020020204104154010700c1a034900302c9015941203682c43c12911542e410f544400d0082c5e0304aa960301c40060f051a4142c80f51075061064a860125410060030441c15a400900303441d03070041c9071900401000c9008104d4000501402d0b40704056100c04e0300060b42980a00031000740796998649512044035415481981070302c1c402d0114001e030f005c0301c2202403401d000034040140421105003601f00007040072400e16900c010000d0440705021000e40c0b003200c3d205010b40d2100551503070101070208100c0702344440307c1550000d84040000c80c4c50582210b005403440b400850240d05081d0201c3c0c28808250400c2c0403108216000750340e14040804000d590380d01030b4a1031100104514520f00c00003d0043c111360451341c005540710701300742d0345455007001029070030350402c0000b1081810305840022406024800100310000003507024040c24007500d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 102569235 1250 102567985 102567989
    0xa0b091005010b0403020409060908181302040608010611010902041406040f1103190906051303200d030b12010606110111161e0b191116020111070509010311010207 72
    0x344600703080050041d10556002d032000c07a034044802094140b001d0405600900005501800c150700019a0b101c400d1003c0030000c100c410180d556010f04c821001391041240158040ca100003203591300108021407054190a66005120780000740041c116070005003180c1d0302e0003a82c03452000740341c2005030760301c1c0500c142c50800303032042404d001000507071440503014440103150841c7c1590380c1c207407107454080d5540044c14031940031800b004641403003000c150500004c000304400041c1000c0912407102011002c4602102040d0000d0660440503801030303000d03001200c0aaa005043c540a642c078415090040d040141583c2d140c54213401c2c0c240c0400c50175070b811701c4098001001c0c02c000c2e030001070600c482d058071203d0700b0000108030f040240d0407a03c0e0400c01c161002c0c140e042c0380c4c0203111580541e030742941121038002e40104100080121800c2143c09142002c403d0101010748600265004d508454824100781701510801604c0d000040e003042c10a0b0019100c548260350550403950b010415100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 102570485 1250 102569235 102569263
    0xc010606120903120510081b03010c02030406081909060c030b0103060807050109090e0a0503041d0a1407030e07080d02070519031e031707020114070509060406051b0a0b09 75
    0x82c00c0ca168801a0245110030708050700b90b0354500000f1a60111001c100001d0300c0d000040c1d0f4500e150140702981024482c41d80390348694a03049504582c0e81c0000112421603415440d0084241da40301c142c8450b800c61204540880c0b601e48803503100260180c81032090310146910000344980c50800010b080740d20580080c14aa8440b034018480f681c0c001c00c90f1811240202c4001c0381c00898041158200040d0310401000d0303100120b004074010303e6074a019a00c0b54800d442d5400c2e190769501d504415251703480340003a1a104400c000c1031040e0302c290401c1e120301c200700007180c1c1c82c15039a41603145010b100208440042c2c0294006011a240c1013154212085520f0300c081641801d6451382c205442c030300121800d009801c3c010140401d40034000301001c0c031038900d560102c240382c90741d070182c00f802d11000c1000c020900d2100040826005a0076a4520000540700504050800c0825207440d4044140c03d03451001804100e0403056042055000c42c0c4d00c1040c4071121418064601c61414a180c0b040d21 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 102571735 1250 102570485 102570491
    0x70e0604020f0a1e03051905040203030910050a030b0301020a0f050a0e220f0203071e020a0807031e020109050c0d1103030406090f061b02090a0f0e0102040609090b0a0522020c01060612 81
    0x10b9107007d403150b419a030606a035070001d03c50311a071001a140d44117184481c1e4205504003d0500c004e038029004d80425116914180300710148482054200d100b0741c1c00c024082008034100500a51041c0050600805242480c02107031b2020400100641148400c1105200c0726203814858000240a001d003640b009003410742c03d5041094020709200200901241900d02607152400414420080e005480343c10000d00d0750b80e6500e504004001c0c0c100e000306030230712320840030350520114170502c00e00c1101d40d0400c029012640b030381d104101c1b406441d0b19064a81070460302203a616035800b0310061000301f051380c070342d403615070b140032600c3c000d0001c0d030b511450910044075441074484140300c1c0420036003681180c141c0400d90714000204001c003424148403500c07c0c540b000c010f01080055004105507000c58483c62035490740c46000c542900c00142d041d540250745048208030500300002001c40c0d841c1c86481d8030818401400303820040340c105a00d985e042d030307444100400000b608015030007203800503030740e042c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 102572985 1250 102571735 102571741
    0x1e020d150e01020c07120c0f0e070905011d040b0f0a090b010905030f060a11041e06020609010603150c052127030a2d02070f05010503010503070e0604020f0a1e0305 72
    0x11781c0343e035103034404c0c5c12031240034611180402c5940c8640c130b0701030000c0c2040c0750902a100d02190221150803282030f000716403012004102c660051420303c0c1c1d60421015161b804842c41e0080c440506000c03406c2c2500b01c1d540320f1009005507903844d5204081c1000e038400045202e1480001421009684d0003640203802c07480c41d00d18036400c08201150f1107072011401188660b01507843d0705076032041d6885101c1c01310f440103c189150f0802003640c801c8920f00e5088485030345910300d50a08035005484000c2495001344100c80d4145106d4100048010007401c0c403c0c200300540d014400006000581c5484182c41e000810241d00c0c15050605005403440d4580d01200a035024800c0e130701d11643c1e00e0601030040034461680981c440e64041500c041c05103c42d030441e220301c41e4003c0e548036524000c020700d00d07001034400304e0b1a500c14000d42c0d04a98004001300152483c14100311049940174020640241e020042e0b001c880a88500401d02084542e0341c0c072203414074543c058413035541500001340c109030a21045c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 102574235 1250 102572985 102573007
    0xb0f0606030f0a050405030d0c050309010f020c07261219020d0503150a030c06090806010510050703050a0215040b180609101805010603050f0607050f071e020d150e0102 74
    0x2c60764001c031107040c005003903200c034240f107403440c060301c002c00070b000d0300784006a1401642b16015601502884000380104004040d0b0303041603010b25a240071856114081c00c20485540c645880000840d9030001100303402241c5d07400d8100102c031860032108440000c1d0a40c84901d20009401110705141b000c0d018025950700010094030002e480c42d039804402681d074400940c2c03103104810081d41d03c9070404801950383d04016003d850b6a104001c1076014020000406050140c501151082995615850319100e9038003038030f040d007180700c80c50114030900701051100c902070b4a019001302e0107000c4403130076494003590600e80c1c0d0308282d10021941d0040c1080c400310100002d441021022440d41c0802d141d18104450504135900c880081d002d982059030000600c0341c0031864120742c00352501a5446075480c28002d80b054803600f00903841d401c60800201020452004d0b61307000c4011f503100040c05440254000510440d40b8107400e0758411a1441a9511b80f800c6100c2e001064100500941c10104c1c1260 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 102575485 1250 102574235 102574261
    0x20301030f03120b12010e0f070f03030503180a051506030102090a0e060303090d0605070201050c030405070b09010903050d030e010b190504050a140a09020102060c07050d210204030b0f060603 84
    0x4083c00512401c07074051507501e4100c1c050041c00a002c001c07522071100c6645002e000421506a050701500ca94400c0d440c0002c18000c0c15184440402060300340b941c3e070212210381c0003c00b040381d00442254440c1d81c0010501c400d11405018200a0000c1d40c000d2045040481c0c0240600d0301c00e038410001030b580c0e515102c91120850b4080200c1d9179461b5264404030341544103206409600007010f03901c00f070822141c2d0340524003628040e4002c00a40c0d0340d9035102070f510700c0141c0d0f0140c210742c420078080201c00c02c544d008081d1640b040c50034041047d50782d07403118604002580c00c100820348513626158402d001b4031031650742260444a039007102d1481c8401098075446801014056600c03000040d0346c40031550010000d0010382c0c4070161251a0000159008141e6441c0490041c01003c020950401c0c50009460000b40c0101c0a486104454030068403a9030144034110014024a1038201c410007203403000e00300846c01809104182d182c401e8400014003001858140f15281c2442403000c3c503100d000d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 102576735 1250 102575485 102575513
    0x60306010b04050d06110409060308120106260a060312110606010203090618040b0d05030304060e060f0a20040605040515070503030609100308030c07120e03120f121609080102030103 80
    0x17800101520044811100c1e44281d03080030900360f0030304100104002416000307000180c640c5141d0090790341c8483c0100c0c3e40000e800382042014001a0051140b810080e0901303030401c0c0b900c400082c102d6a40da84956110600c9014100820030645949035060400e0121640c061024409940351075102d00010340540a484100e00b034889418450341e05035115076010300c020060042501d10350150904c1c0061340c0f03a00c110b5044a440342002ca03e0b0344010340004d00030b4010700c01c00207902c200b5600c484100c40148025010b15940c080480c0c42256040f081800600150601ea07035a29515810803040c03044105604041d0410f95504108a0740800c034048140ca401c0354080361416003030f0310341044209491805810151041500109104403486080d00502d1210701c41c5420800011940d041507032100c010350b50700c5801d0b41205031101c1c80c520138000104410081500b0031805c1500540c5840300c56001120810846000c0c3c6040250f00e5800c11141002016008025032a41d030441d03584e108243c582d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 102577985 1250 102576735 102576743
    0x1030b09280b1c020112050403050706050601021c08100806010e01140a08070b0a0f030b0904111305010905010609080715030513060203041a0a0c0504050906010c0506090303060306010b04050d 84
    0x21420308404086030380015504040041031802403403840603400225581001d0708071702246003400c54540024403802087c3c86141c141c0c40b040d092840945a10303000c1e12009044a04600694402410f1945a003120b41e841244541c3c480c296440e004ca019025643d00c2c0e008900301e640540010803250f2130711030748141580e01c0c2d030510b01203901b0700c3c50104920420642200700b182c0500b580110b030808040e00544650005039039a03560002c03a00340b013a0f0071503c11090032500302c500c4100050202d240b20440301107000c07010f88443c160846100c09941180c0080e00312400c40758035440100901c681c013000703410103440c2501c0a0b024241c94087d0b03501d01812440c40400900d40c41e480002c2607075610000640d075031038102806640d00d1074540390401401802c4001c0c101550103e00c08a10790403100d101e18030080050b5203606141c281040304000500d040240003a040000d1080184002502884418095005080150b0722400c0034401c060815205801082045009200c108030760755814038403014007500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 102579235 1250 102577985 102578041
    0x4061a010e0d12020f1f0b040209030307060902010212070c0f060e0616170a020c010f03060b0f1303080703020a12030506100809070e0c07030201060b03060102030f13091a01030b09 79
    0x1205406078100055452040714500404041c11110681c11646c1200d011000d80f00300070780b03000c0008100c2280508050160594000c0c45094002001035105e40006c500500488904d550b41c102440c00c070b580031400480703400b40301d55010403d042c1c3e20381022025101d0781c101350074600d0904000c41c1c032500032800010342120a0700340c070000340010782000000c04814503203869510048104082e564070701c2c0460b05030004d400d04800c40c1520340300740f1a040c29620101c00f0240342a0030000084c02c10f8004428040084680000010000784900000d12a81e44250003400c40d4070b43c6414085041d8060410200606003404204400e59442c1171400443d4816402c2110f03036503c41f00042440c2c005260016100f072247c2409100d0303c8002c02e806044010f100358004d20003152a8610b04001e03000c00d44640e80541c1c0309000d42401a5001e0300a0070414402e80030400300c450fa01c03040f10094139215101d00075044000d035000c920310750b4940141854900141ca880f0282d00380b80300c400c200c40071101c50403029510 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 102580485 1250 102579235 102579263
    0x16021006032604051e0f0901032619020601061701050303040509131202161703031b0d060b04030c150206060402030907030204060e010509090f0316020d0b04061a010e0d 74
    0x42d49064501608018003500c4003814000003100f900002150114403403207100d0555400351400b8908a070607241d1180700486110400b00040b02000f0424656805a200074080401c0e5601c2c40d0010442140440d0300510750303545030503c043c1c081407000c0010011008080300610107502c0000499089901c240c1c5c0907801c503070340c02e10a5005096684001004941050307030f01c0c070540d0390015000301800510101c011b812039a03814a0240f180c883c143c11055a0000e01c001240c1c00301c08040a0000511124580c0c5030100c0c007528607080740c01c1034000786070b1036001040500901c8407501500d00078041d1140c1f000841c8080c0d203400f0b9500c00d0001e220502c195000000035034034050500042c1c0042d03034003900038005075403150080c458015003405030341d004422401c0015642c0700b001071041e20818145018514010582c0b00c050240346000c1c0003aa001242a004100050141485944946d001d2040012410925010110b10ba8050803009041001c3c1030704e00807103952009000452150301c0a0180307003900e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 102581735 1250 102580485 102580553
    0x321090821090f09040c03030318230f06041a0a0902060342180f0106050705031308010506040e0706020d0c05010612030c1203060b0703051e031602100603 68
    0x201c0b0000d80940c10184002c107010400030f940d03c11b603013a0303442500c00b4402454146021003400207400c03030150420b80d42900d0070a0a145c00d0003141c0790500c40500340d400380280c0c000e0252030036405440803903002c08144040020b55a0384403200d40c000141c0303a420f0020030701d16000206076000240682d101c800d0100214600410721184449014651045081e22191502886c4400303100c2062514080e0320001c10030b8942c0280c0601e2540302d001002a402001d07424100c080700c00780c01c4440308480b18401000100102035009141000500581001244620f4008107100036180d0400c2035110561008030305204c09030300440d080200701558a04203801e0002400c080c1d003d84001d502011813064142182014540d000a5842425002e080c2c0b0301c42c2e443c80c18a00f1400c5031498031078400130f84c0c414822500043e00c02d0008ac0504e20f1114440c40b0340e2a4034a49000456000b50303540c0040c01c02c51084e544100c0c2d01030000189800d0000c608001603865a200c4203ea000140e14003a2964008900b0000034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 102582985 1250 102581735 102581749
    0x60102070306060906060311030c0406050706110d0504030e150301290d150b1204080706090b100f0f0503030f07020303070807150b09070e1306032109082109 69
    0xc6401c0315083c8011a50340c41004001c1201d40030f4280000c2c2001d445507646807880089902800920400500c0d08cc0f50a508441c0740c0c00892040710700c41c0d22071401164002c01da074041c10001c08102c1c1b0000782400c00340740140500c1d000c801900c1c041d02e1216100525840c00e60292811104210052800102c482c5040700c03008401d010341c209080740100f05c240e605411588804600a05050400c0c85a51108019074142c041c950324030f1100c8210700002400299030b81c0151545600c03400002c28000c0082e5521501c0f842c04071030341e10084d4030300350040042d0ba00c083d1165006084500b034401c003032400d241c0070945038840c2002a4595160003d1100110b4400b001103c8071650030a440c903840da09289000112130203405603290042d42482d4441d1890b1a1601c9a140104c0e0765844040001d0301d2a801e0080307200c0810340c00d0f00110350300d02000011403807420140740b00e180705100da549825020000a0001200ca07040300700694032021208215200c0f07070056049503903002134111340301c20003500041e040d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 102584235 1250 102582985 102582989
    0x414030f0627011a121c03090c0e07020a120306030c0e0903070b01170d090803120a11041805090604030c0b0a0605040c050903012418060905040507030b0f0705030c0306010207 77
    0x1513103000c014240314404101444901d030b50484030144090300400f41e0340d03a20b8201c40076804903907815841003044c03980264441307180c0340c0c030070b40315440c2c2c030303a681d04540351703200403c440c404056000280f002080017403416400e403c05c80a0705081003400e003951103424442c0118000d0500d8100103c002c00c0c035a182c20416120615403000c2d4001d07207580c54905032501200a44800b20720713482030592102405005030b407002d00741d4a20000030340c14071501d400402d44002c4042c0a030202a82c0d0b0b0314000041042180040c8040c150300108102c0500c0c154000d0b0089801c0100b5440003034114505000009503c60000c440250b001060b8a0154a4801e0610014050b661240c0d501625100d07102d1011504100902008642100200001c8041c0c0c090041c0781e4485488200080505a1042c0041300c031030326a5086040684400044554940700031008440040d00c05071410350050404104201d52880d0545d480b6400c0b902082e964204004064010700015005211508020002680e20b074805c12403540 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 102585485 1250 102584235 102584311
    0xf07020607210908071514030604060803030703090b0f04030f1224050108150a0b0f090d030c02100504120b0619030602180103020c070501050708040f0801020414030f06 74
    0xa41c051158018105001d5485400f01324056030400141402184580c06c07401e0100d525601b0905904040c804035030340c802494641c0c41980c070b41c40841d00340c0c0c007003010310711070092901d0000701e0201134141154ad140c0000c142d24607440c4003904200001e68058000d5100081c14100201c3c02030a14500201910b440b05007140c81c112007440e405042c100101c208001c03200300707803600c000c4c0b0b031101800404448800c14201341c000210031420414000120001e10066250100950a00c1c0c08c1000091207002d0440c0140d0000b001707125001c0075490030b2401d1b44c11090850400300e150610f44918485010300260340604910b0b4800f00044854480070026205404205481d003106034680c0f0380744000f0740007041c03d1a01581030b00958030b00c0c1d50003131003282c1e844bc10308401003a11f42d1511004403503550040904407008a018000014480451000007010302401400075842c1d5090001c4244101080280700c0d00c207500020389000c86010126810303800c6440d0045078207a040b00391090056860301c40c0c01402d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 102586735 1250 102585485 102585533
    0xe1b010f1e090501260f060d060e061f0e040609061407020d02010c030b030a0b07030204083403020f04050702030f16050c0901050108010b0306030c13050a110f07020607 74
    0x40031503502c4291142514001d888140701d150300040c6001428150460078032542c1101008544040b104901c0d0340e43c0490000c108001d0f60300d881d50344c035090b2110b88115540a43c016024480701091011211401160304811030f441d580c9881a0010203400103003010704080e55650241c3d0500c10380e81c01c6040c082018180d01501401e012400940d10360540b4039100042d4604201214a540b0901411282c24001001040d0124144c2c0303a00348903d030042e00b00b01c103044e0308000010702c1000c00d0150252484001d807000214584810610b0400382c10305646040504410b0b80a2005944a98a01007554070660f800102591444400ea155108442a8455596010540042004450a8154840744160261b8503150551414041c142c5400c2c010b0601041c10b8100520180c080030016641c441c40040850f03c6549040011134528038040c0021003201c0d071140c0401900d01c500f03005080c0704c0580b55403818a4481c42182d4241103020b1104020301c61200052540244481c14400d4440081444825 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 102587985 1250 102586735 102586787
    0x50903040b04080a03031d0c010806030307170a091a0307050901020a0b0a06090b060703050a081b04062c060a1b1505090f010213030f081e04090e1b010f 67
    0x3680c41003c00390890006c1c1c10076512010320150791840032a009000070042c0505034100c401500d4908000745042d030184400e0113608003043c00c060740c94206070521040c050307660078030b141e00501c81416038110486c1c400600382c1c0340d5106080c040413643c0c080000d00d012515100c0010040741002c80d07001014205842c91b00c10b0180d45078680e0700510403100f42c03200c1003190110010a00009005950024011400c1482100385250080d03420546c0700300802a48090403518458003d480e4000d0380254000911846030b81e403115007032072940212040181e240f040705848000c0012801c0c0b00d24100481000060566801807074482e80c0c1584106d540b003d007a040842d0402c1a010003040121038512052240c05200c0e600322506200f2660105007007a14030714090f00359210b9042c0881c1c1e201007240c00107010060300f4442502c1c40d540010600118861035076803480d280300b480c02e0380c085031000c4181d0b40080065244686681542124018080c02c2c0302c008105541826a08012511070900c40d09021844ca = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 102589235 1250 102587985 102587999
    0x309140106051323130b0a02030f01060c170c01021309090506060109030f0209070c050a03020d09080d0c1b051207060305070908030909190e06010e0702160603050903040b04 76
    0x1000a86905544440000603009034020070358034003200c0082e0b605001c4d402004154805450a94402044450140811041da55075a040340c000c0b0b405103007403130b03020082c081e80010104603240146403170b26041580c08016107405450000308411441340b01800550441c0b805800c0d0159059150540341c001c881a60b2014036401070007120004483c04d000300c2000603d5507000b1032501007580d40220b401c0070004e0382c507401c2c4410507001804084c14820f005c59901c7c0018810002d1818280c4294003502c0d1111203210040c184038680d41241d90380c7c0e00410076800172036920030310360103880c0c0d00701c000c85c402d5076101920004100802d4100740d800a0140104040c680c00000d1144c00303d0b0000d43d420050703955100d50854581d0541c2c021081c40d9041049929420b1a05810b6980c200c00f040140c0224444034500300400c88a2030b50741140c940e00100d004009040d07100c3d180c00c1c0d00401900161540c08281c0012000010542c044c4030107142e030702c00119000300410010f6130054401011025526034031a55 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 102590485 1250 102589235 102589241
    0x801030c0b0a0f0f090b0f0711041806020912030c06070f030b0f1210020301170f01050c03010e09070e0a02030a051315020f0f040306061a09030601120303091401 71
    0x584403129000c40016810a451086402401c515643c0c00f00280c401003084489201104a440402590310303008200761503040010241b03214450540b40e9590704038a0315500e0140c0020200d0b01c00d81c501500c184080c51990794024045a00080050742c9045610004a503051200181e0380f580c40045810b002c8602c2c0000c0f000c1c003952030340d110030f0004100d50404130180c0d9090004290080341c03124082965041411001710303003044408c10b80f5002c0041c541014120b0f0400d0380320201c500b000b2114030145403402c1c0440900c1c005014000c2c065850300c01c00d501c446200600c20300d440103003420000741200302d051101901810000f450108603040c100000c102940040d51401c04180c9000041130349504440150068154803e41d42c852402c50781030500b00a42040c141402c80910400010112900a100800c00b40d8400c00000405a041101c0c0012450101003903006410003007000010564000901c203044401e420070506440c0c0691400b10050302030b03140018904c4203208034241c41600190 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 102591735 1250 102590485 102590489
    0x304080d0509090a1107020405091005070f090b040e0412051c0207020f01021603120302090406170606120303060402030c070b250203040311090901110301030b0406140105060d1a0d030801 82
    0x42d6408482c0d21229104130072280000540000700780104121001030600340c0015600203031000035100301300034141b500829203004540c5c07200002c0c91080800051604040b4103006003031201031090501d810001034284403030001e0005499007410a000854451060041310461500d001c44c200e2582176942003107002c0c5d00400d00072480381d010102c10803aa54400075080048403400341d4100312036843c5883c0c20102c0382660120404160b001c11086403940c490740545001450320b4030000c041e83c00590303891410b0079005080a44030b1449000e800401c08400016290400401c8500503600d440c1c1580b2005680718410006220ba9000b804002e803480301500c80d5142c05140b03954850b0f0b45681008101d0b02c0e0712079804010800811564010954103040900c00c1d072014003400001115101c0f1041c18480350000d920454500d185501080200310060180805102d484248104c09504040000b41580900301c0c0180c400e9566402c0c3c115184038182480038902805061101d2001d118280201010424 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 102592985 1250 102591735 102591739
    0x60801060e04171e07050d030b010203030f1008070e1602010c091707030f0f0b010504151a04090204082505010e0409110907020a060b030a0f0f0501061e05030c03011a0607050304080d0509 82
    0x107294291007c81c0039010b007821920050307024524581e41c55182140e60782d40540300c0d12218800050104600004000c1a8003802d441200a032042c40c200300300d0007000e5a540700610869051002d01790500d5008040708040da1078904641b481c840c0c1c90741465282511540c0f01400504c0d5802c000c00078071007051040a01e481c090007520388a81c1c1c070340c814413040ea48180c0d0340101000501c80100404c40c41c0d00160042e511042e08035528041d910241c0c001603801035000781c03200c1d0304034070790f03074921801d804030701c00301001d0010040704883e40b4210010384480714480ba00c1d80101d842e01c0d00d607410001410040996290024640d80705424100b41c029a03d580030081295654544038203404146000201401416440900d210101c0019520601d500e20a040704540649d210031000c94400c620080305002c8044198400010a01e0401010324000012140d10b0003070b40350001030441d0300c104030000c4d114241c094810680da00080d162480c51482554000b040f68007840c1141f1200d44e0b4040b009107505c2d442 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 102594235 1250 102592985 102592993
    0x103030c0b0708010b0d020a0908010e01020a021b03061803090d030e0102120301080604060207020316081b0405040b1b0d020d050f0906240105040504090b060103060801060e04171e0705 81
    0x400302c05079031021003801401c841e5001401000072040b142e4000303010004480c508100c5071580c9416413800d40f41d01c0000c40e046a500031940c28906641003086030307000c0300d042105480301c0c2098400700340c079a81c014000200f01c0e02481c0b4180320a0344c0c01c00888201c2d10740980b05000c8000203003001002c183c00902c00a006002d240700038260300781010181c80c142c50008024284035180c030794a8000a501c02501280c25003d04003900d05164040d210a81c01002c2c2c0c000945010090405005103c80c21035014038030407403414040c04041000042e1055002a08420484030042c100f04d8a401c00c2c09130381d4242490700e00004004103480c0c5542c201c903000307240140010540d42c070790004403601c801040b560009181481c00c000311040d048100380a180d807106040031460070b0740f5600401d05071507140f001620340003c02c10622216591511a24000b80541c2008000c2c04d42481d0030400c140c1d10251010f0305200d800340782f01c03082c200c5070000c86132654001294649094505c0860316010342285906540c1402 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 102595485 1250 102594235 102594241
    0x50a0f1e1809061d041b030b09100207030c1103031b0709050907060807031517010e060603300c0706080a060902040605090603040c05041d0712020a1514030103030c0b 73
    0xa440c00303541c00303a5400400d11401358411490245203104024030a482c80344681403641e8000e503194990380085d40c083d2303400002914041101608c1c0040300da52084c0d2140c030402211001ca5480050303004c10300ea01501040d80100f100002905d5401220700d0201e1045c2d620407844d20081002418008550b40c81506112540e920002240c41e44098416000400d4003100080ca00c0c1d4401d6024860074811005004089511102490341601640e282c0404030781d541c200e0f10f1510101003202a42c050b008400810344440c50b009889a071011429040c8071440d0b4040c1e503aa00742041d40165401441c5010454008039034405008220b1007094400240c224502040411004218000c59054400d2131311850324140c071000600009600c0200169000311404001141d00c0c6d480d40980303000e559480a40329001e01e01450128101311340c5170b10034090304886180c03801c01030322070b0000d4108565420200203032801c0300c583c060b1900c2c00d41800046c6802c41c000000b008051f04800301910450060042003082c4e5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 102596735 1250 102595485 102595499
    0x8072d2102040b0a0b0418020c01090f0b0612070603020c0c13060e0a0504050c0d02030a020a0b03071202090f060304080415020d090806090601030206181908061303050a0f1e18 77
    0x82e0b045c0245520484100420f000c2158414080300c01903035240e8005180141d03001e103507821070b040380d13000b00d0f0308400620303421040c400403941c2c40e0741201040b5803101660f030103018699a500110311071542030540221380c103e07102d0b0060002000d000000b0b0b000005036245400b0b010000c00b080d00403103c0d002071300d40c086165042c10384a010300c50350b03200004140e40c0f1694020841c0314110b51100304da01d8801c2c00404001070700c070304050800401e103994016440b407c1c60360018140c5450002d140c900f0510501541c0c4032030741d0780c00038410340400640e06140d036901c03607091140d4580b1940e0481d009128540892081c0103500290350b61110741c007a604c440d03140b1740b502460781e221101602c510b0741071340c0400014009450030030000c0044c90020541d005d040d22544001c0f5100c2e040040c0020040c0c0710b20a010000380c0c100348065540100080380e4041022026a0050102d0103402212800c00c00c0c0400b0210700d9a002c0d0415912070a07a41c1e2510031409030702d0000070014980e204409030710001c8544005100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 102597985 1250 102596735 102596749
    0xd0602040f0b12010608060a05030109031d060a020712020a1e0315020a080613020408010c0503061309020d03050904110705031b07050303090d060209220608072d2102040b 75
    0xc5181e80b111150545d04c1d0140442d01404043c1007280c1c0620300c0300c3c1c0081ca03540c0034406c0a9000e407080d142c99086143e03100c50008881143c04050740660410003c26a00660100c1c5940039100901d42075540f114081c000315519601c185c0040c1182c5d10300d821020030308030070003200d030701242e11400a2a0064807000b45002c03d902030704443c40b022071007003004502503180c13030949100e003800c03030040c01800d190b40c0d03070344103030944610600c1400130a000109212803030402d00d81000c030500081005100b11440c690110306162030400018003001000b29680e44a0740d02c541009950020048035aa00e920342c0b03003411902c1b030388580d80c9600b03881e610301d441218982022038030204a440040c041c6007004001d0090000a0100f0745003210250703820070440100303031398602c00c00c0c4484d59003200c84040030030b0b464011012241260130608840d80108070030004164030050648814190700441c0e08071100d04500c100d1103007003a800860710702d2090014102000c100c1c0d2007002c0000e0080b1002d01502e40040140b00304 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 102599235 1250 102597985 102597997
    0x6020708011104050d0605091218030c0d050309010804110901060327050d1101090c0f08120f0904020a021009030503090c01030e0c090405070803030108030304060606050a0c200d0602040f0b 83
    0x40c1c0d00e0200d603010645661055600030148420f8039644001002700d00c0040d07104a0b404074515090805660880c101004130b5464034509903402d1034a828180c0b00e80d59240640340815040018840009040104042a48850b9000900301121035615010090050194007641041d40014164280c0d4504100c0d003011510a400a028000301c400c1303d08100d400c030b50400c090409540d2034000d007200042c501d440c440010021003009541903414408400d04124107500c041e5041181448004c120300382c8001143d809850440740140d031440b1410702030741082c0c002c40010311071600e0400702ca0203154120005600c5402118291021800b2040c0198112a6103289850560348039040390b11882c2030040f003c41d0018000c808070394005690340c240303d1031680246c0182d0102e41012090000f00041c038000c03c00500700c41c0c2000d504000007140000c1c103070140d01300050040042c107032001e0200015031013010407019004d8210340075030b0403c0c18241d02940c403510072100020450040050510003010030742d80707 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 102600485 1250 102599235 102599239
    0x10140d020a1a0403080315040c0503100e130605070e0a0f0602060c0706090807050a0501050106080c07030c0c080d03060e09010908070b040201050904050a0509010b10020a03120b04060602070801110405 88
    0x41414101190455070290640c2e4000d000d860070440403012074401805188140340c244081c4e10a244c0e25418007080d110f04541c00024000d040c0103001030502e0200420003610b400000a0402e0707a50301da00b00580410064000d05454907040a00650300e62018940005110544a02032071b0341d900c95000300300040ca48660001a0004404240421031000040004900459020814840645415201d0740c40706100302c40e544d0040c00c3d03603800c11100f030180600420f040c0c20405481c0c50080d00104080c85411801820889011b10000c104803c815a00c030160100382c040318004244410040d0041006010300704080300c0442c006821a481401141e80c2e00e94440c1c5081c0c02c1c4103e990312440d0041014204034103004080c440703014280c4951190700d1240360030440c0481e0342d060402110342114911070045000381c10103144003940940010740c0400301985450040e1000750006d16610041504404665000d070401100040c0182d00141c100309076005035008005035248042c40d18424450791003125 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 102601735 1250 102600485 102600499
    0xf060a0b0f1305030303070807140301032a1a074202070501021201031509020f010c1103060c03070206102603090a09020307030e0312060d0507090510140d02 69
    0x250000076454064581e00b2510004a814075407200300003415904104c4410f0300260320785003088140f5038094001c0c13034011040d209a603c3c40d4115100d2021004d84007058418101c01520440c01411a011070b0b4001030000384030054901008402c0f10301e4541c003186e400d541c14005450302e105228540748501c000c0c01e4500070301c042d44054640203410030810080c0030b60800d43c2e0a210b0000411380a00062100b203041010990966045191840600e0030b03040b800c4404a05d407071500d20040e181d811030500484000d091644d11005107280c880b4a2019000c5216054011001404481d11140000c0c60140c40c0310b0302619165900c2c18110070103062580704d00c41100c00300006541824500340c50700d03040c503865201541c0c50050146c01246807842140d001c1d540d099400400c10410307540c903210310405481100003642c50140842c000102804020307210b540f094a03041220404c0003820807812000707218400c4280083d240c481c02070300086040380304070b0b40e00745106c40c1082554a0002c90130201035600801d29 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 102602985 1250 102601735 102601747
    0x1060f17151201050901061a0a080105040209030a08040b0d2301120c05030607020a2015030928060b01050c031b03040812041d04020307030303020f0906120f060a0b 72
    0x1072000d141000d00454121040c1c8211061420080c05618071404484001142c1203190007000032242003544892550020107002003441c042c0c0c003150b01e40c1100c0c01240c0140c0c5990584000a0900c0700c10305008001007400200090b000b1039500150001c3c1c07a82c200100300c40f0000d1003480d03034420340140e09a000d081c0f189006015500c48000b144034100c3c024031000c141c0944036008a4648441604c0120140c0e004507940401c002c0d01000218000002c01480000e090085022410461343d68640902652001c0001035090104000090003074020004a649407820341032143c500c90b1454000769006824806001850b50090701180c2403400204d00640c070f401b4403a41c102e000d1000800340140c41d80410000025150800c1000c003242034010485176a030395242400252811005142440e4040380311030402c409642c010584804403134140c03c01580d50408034944001d42d04c07038407400e10f5101030080f6103090f141a00c08021441501c07041020301c4d541d1601030403c104803c8a00c20020902401c00c0b00c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 102604235 1250 102602985 102603001
    0x201050d09050a0c0b0d060801020f04170a0203030703050408010501050604050d0209070201110406050c1006050607120e0a0e0103050d08091c02030c0109031701090b01020c04020a050c0a0302010501060f17 90
    0x88224060300800580342c3c40d20a81c1e6a0f51132041056004a200003c00708113008651182c0c03103003078002d00c90000214a4003128004481141c0260301c0303903542440501200d841c0b005018032454001c1d65000b0103907503440404e4500588140c006006d0b251107907203007034000f2810341464412101560801406c0044048660382044040304008102c10210b5407140d115004490400000c0c1002c2c001c01d0b21880c1d107881141e04400c1c83c01140900e0401e072103007024402c2016858a4040306d00d0300f0742000701d000400c20001320607910312038480d40941c0c10082d07400300094061800c01c0ca69050360f105109450050345400f4080394102c07020b589060490304180041c443da00d4002509000750b00307682c010b41e400c040f1300300300260031100d9140040d808560384940d400b0340e031013007095024003500c0300f81e80030454074540c40b00003907889c1d14905c03907503009540c001052007106e401a000d540342c003405103089520306005441c00901902c0300381310315008180c1c0d41d03812810041c007641c1840b800b1352511405061a070f58000f0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 102605485 1250 102604235 102604241
    0xf060309140106052d04060e0603190f0209041a09030901030606050304020108150109050301090506060406080f0616030605131e060b1c0912080f0a0608030306130204050301020d15080304030201050d 87
    0x140c12034412201c082d40d0121515240640d0b00104231a00c000710541c07520800b81424403015841010f91600a804503d002072007080d940c0b8002034040d41c80c444507079103601c0c00d00b458811081881e820700b0003000c108203075024000000c0840780c40030b03a810f200059075000141c0c0e0318002510000d01003056200003503002a80328807400b10890052400c564040d80e1800170908644400070185d0301e64011500b00002400c1c01c0c0100303401400b80f03034000d020700b4184280c2d09880d0940a8400d00f4880041d0804510340b603c00e40000000c0d02008003001c90103400004140003d152960080585144034007502403202018410601102c0920b602640b0b002c5031881c0c90105a1108600d0440785652400840702081200300680d0781d000b0300b901c40584604104640c22208800149651001c1d03061a0341804170b80008019a03801401c151205555041c43d040e964001c3e004940003103401d1361000c500520003281603044402d20220105071000302da0345500d801a101d206601010380466000c03c003a0304520080e078 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 102606735 1250 102605485 102605539
    0x9020103060519050a05030f060415140f0906010b04060507030302090d0602040b03040b060306041104050403020c150a0e031c050d0f051302030d0915050a090f06030914010605 77
    0x11600240d52600e4200081d640e0300c0343c00b480710300505407401c240480d04156000c80082d2138124000c11040d18212281941c3d95070040c0010820001d01701c1c80f4500210540003180c051801d9840c1e11460300e401440c2503400301007210a5041c510468000185c03810340ca104440039684203a60b2185001d0498805502079401640710b250403c00200c5c030b50300803400e40d101034006081040d035502e0f81d0f0705007824001ca0200340545024402c2c0c00c0f4100b80710020f0b21071a0b001580d40c40544000c1580c5e0380e40d08059040c00c0300010850340051000c00346ca001c03421900000e14042003035446031210174400e201456910302d40d0980d10762305036641149a29456000741c01504011307458000c0810141d20605407082501d4065070b12041d152000b0300c00a007107103801d20030202954420f00c0c219640d40e14207080c006100703580d4000002070080c00544c01e50390a1091041d8400341155440f0416007940c3c5034030050041c400140c080d5000ba105d800c501c10142010b020783c00803204014160715800200c0301036031450b11016 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 102607985 1250 102606735 102606737
    0x1060e060f120103080a090621090f060e06090f1f050603120a020601030309060c0b06010807030212010f1e0b04060311040503060403080a0b0f030613030513031401060b030c070204090201 82
    0x620061002042d410069406103100b0078603a0745600d0704960142030303079070140c02c00b006100030f041640d01c01d00201c03d08985410310000e00400c016100d800d1006008880340c0703000c0c11240c180350000c000900d00040881c0a40021030841d00c10b103514511050f1124024810103200b908250980c95150715903810080d04900000d050320034440e00c1c0d560110951707200c4404c990150700688010024190484c090070010441400c1207114a003041c2d80e0303120320440013801e4074103106001d8041170246100c0c1d4151200b994031003000002650b181d0341e49081c6101c40c0d1056104854480f40000d012400e140d4007070b4202e9a00c40c03c20b82c180741c2000c1c1d040e4080c19074501d10940211f000c0c00300080d0780da010094980114000d031100340d41414035030241e43c1135030540101940640c0c0070910210b1380e6140000c034554885800d401e09100e0091520b0211602d100f004030040001c0c900c50030100078003805a046400b991440340080007803694620000780e080c0000ca07403049281c0c80501c40717140581055003141e1001841 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 102609235 1250 102607985 102607987
    0x807080118081e0705010903090e0105180415090c03120f050a0f0c0c0612050a0c05040b090d05030705060702060603150f0a090507080a03020c063402030d051801030501060e060f 78
    0x3002415240e13402843d03054171141c2d16a0410320a00d81c004a403c00a0036600211081030b41c1482c0108544c141400c10201d50640c00000080c1480b009030540b001001c94140203018150301e5007070400014070b5034001590030700001e021000c0518080c102e03d0045440d2515070302d0502c80598400d0740c0c1c1800c80d00a800511007401c100c1c4000520b080c11003805000c1e41c1e00d9940c0442415044c4504491000f00105801d501d84005e41180c2500442a01d040b10681003a5a0740c4003404008292000303800b41009000b81b0002c2405c2c02000304c04100c6500c108100d82c01c0f81d5282e6604c00030141d55070500140b00c1c0c0c10707070312000200b01c1203070b800600c0e203921410310344002c200055540c0d1040e2414519900894083e08400408810154140102c4480b00d43c219038250400c0e1908920040d0000041c465188142c020f81135500c40481c4501c0145209030000d080da40e400440c5180500a0340c000807040f448511040b0741a1010341c002e116980c142d810b25541c1485c0c4501078801d0181a81c0705600d0203003c0c0f20 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 102610485 1250 102609235 102609277
    0x1030b07030e010f0f05060a0302030714010201020d14010302091e04061d0a030f0e1e0906010c0f0609020112050709090c05160c0504052404020d24080708011808 71
    0x3401120036080c1320100005e4070300100c203611021240b000d0b00c054441c21030a0410000341ea400641c0c4000e0f1403411214006c510a840b005030b00a102c0d44448040850070a03d10307940d00342004034014122402603600341e0b519540c2c005d4900b0005400780c107440c26003181101040104d90598043c0300003020303a202c1e014064003080380c403625009414208400103a03206822400d0350b0b50108400040c0351301560860700c80ea41045035980b990b80e160083d40d0180e50380000042c020307840740c0060100c0c03a4011080d10510602c80c20414003030100c50005901041d582c15045259120510516116034404c0e5035400170241400038010103091950580006c004090003d14002d2145441c00000d051003100c7c0d58060928050500040c0e030302c000c140c0d203042c1d010400812071304030fa04a0170444d00102100c00613901c0d00701e0040b85005203c1d150418400c4a031070314203880e45032402e45102050352900030403500400da031141c541d802d031a614082c0340b1040314040090b20000720424040d00750309012000c0964400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 102611735 1250 102610485 102610511
    0x2010050403091d090c0d02060d0c09050d1208070504060e1003020d0c080103060f020c07140402041502010e1204050d1103030405060a020d08060306060a12030905031006080c030c0901030b0703 84
    0x300c6001011040c26040004d001e24a14104604000c0c5501134480e1a207461094001540601900110350125a1100c1410f1201c0c2e10034450758000e4030b80184210620f44207800c01107031480314840b106020a4813000801c00e95805001680c0c00c560141c0e40e019883e2582c0c10038061201401c00340541899002e09c00c0560030000380c0216a452010307aa1803240c250f2650030b100d801c0c0c4106605000b50148108550003940f040030038002d054550000030380082900c44004200241b0a55101c0811a1078202c0300c000c4060381904903448028131241110820400c0010b4090940300300d1207200c0c0d110022148003000150f00a420380b02d014030081c1580e050590b80c01c04110554003180c901c000680100c0054188550401710044c0c20240590040a06141420104564802d01d001d081152071550180d8400c2500c54410b00029210113000d035141c02122031107120280c601400784132400d010f5003000314618140003455269800c030080140101e83d02c0c548698001c2030019003c503081640b03c0d070b1554421 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 102612985 1250 102611735 102611759
    0xd0e07030c08010c03230705031f06030c080708070801170712030305010518040803060111010902040c12140c09010e1c0f020f061206091302090c0307201005040309 72
    0x6194980c0041140b40f013218008080f90a40b0207070300e4581e040c2080388204408595002c50740308415040c5542d80307454041003404841c0c1610f0441c0000c080d101404a03c0c140d0581218130740b032a00380c441c45495114144250f42e03007641282d0306130000f880500104080c404000d040c048000801081d504066200c0c490001042c1e1008800d03004203071500010080c906015454000d52100100308920504080e9501c00491001810450411040d001c508418103020350260f5180c039402013042003500250280a0105080c200315036003410300d00811800c210341d0300c91046200b82080703481240703403403030100040d101e24403600f898036080f00352264401e44404400d902d0400c07060103100341881c9c64000744101b004030305044c0b0050b40138040501171402d011601c0c80c07000d60030000446070f00446a0f25840881049010440c010354070a84001c2030201c80030540001b54043c4802e951941c07014282c2000420010100d034951018551080e504c40804080b55031116030424420724005005581c2d514060304030b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 102614235 1250 102612985 102612989
    0x60a11070b10080f0d120209120a0c060201050a091112071508041707031d030f0111070203061b0403080a0201060504020d020a09270510091506030c0503010b0d0e07030c 74
    0x301c85036072a05003c1800c2c01c00074114050160002060300e41140e820007882c50a034640c40d42e0f1002d401048480050743c1c0e460207034060602400407074246280906001c8609046071103110090352811010507130901007030040344003550308401500c1c510081201400421640c2c4501c08203280184400401c081e0a20754030303c0a81c5c06039541320f2069041904007604107008a5184550b020b004228070b100003500040710b840c50a603440445004980390b64007007030514010440070000c652130500320190000c200c41c0a002010300075011104155182215140c206c508078807500c1034110240401c00c0054400c10007000110460310002c82c05560b6070012030300b0f80c3c014011510880da00468400d090582c05155a0001c003034540b0344442000105040082c04c007441c090202c100c50300d43c00080d03100c584800405000300b102250420001d48030000d41d982807102802a49e0000c3e041c8494882c140c0d00c40d10560781039440b48140b20380340c0010381503000014405446030349120701503644008041000070080d000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 102615485 1250 102614235 102614251
    0x20702090405071508071b0521041403060103020102370c0e07080f01061b0506010e01030506070203030603100902040b030a20030f0a0201081b030c0406080a0b03060a11070b 76
    0x144413420002404602100b90440c0f500308091241001a416404118100c0030000121100d01e19015410001d040c10801d425440e650404541e909044450320782c010300844900d080030317200c05940b000030103444007820f11010303005a012038403601e84184050302140e03d140b15540006843c108041c140c1c40e41e8159070b241542c0f4000000c50800015050141032030f0700107464901070500d450b01c44140540300506002d85010418080303050041c0e0588800040841500101110703000e41e5100c121a004c480f09000440b103901841001c01c80883c0008140ca0040f040140502401184e0441c000010300b08a1b006a03071241d103994540ba900e80f0f082c804d00024a0013030440c1d80d03c52541d41c14503800f0f41480a0000d0290340201020344126802150b5141460b074240381161150302d843c42c45121190140001c0006010000700f0b0002c0d202100300100120b442c03644405c041952011803060448000759140c5806400200c00182e0b810b0441d80410602043d660025090040c6038480c6e980201c0211171501c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 102616735 1250 102615485 102615493
    0x513060911040f0207021e15030c090a080f060103060f06030b04060903080601020706021011090a0b12060109050d2621010f0503030f0310180b130608030715020702090405 75
    0x400074200780c0100f03030811030440e0056107800d680d0f0380464400000e401c004c0d19030401000032203d507540d410107070ba00d82000c0741d001c041e241d040c540224a900c1d4070501c06d1920030140b00d60001a0710f040803401410f501116400b80600d40e20316140c020240040703904840f01603694000101c00a200e0071501d03806240200d000045603040d40c07030040d210b10800791030541994801e03c801c01c125a030000b46d4000c014180355020600d500c40424051032400b4540e06694400060100403031035000e504081c21b1104108032180e00035465a40064400b280d8a00465812414a02128020a1210300f2004002141113032800440004500c140c43e96005a850203580003c90398222840200b1101c0613030140c00412003c0800d103190000280c1d0300c0c403d0042c071505c020404400115800d1000d400403008281d0802030b01003070404009864003e03c09040b61030300c600c11440f5409020000c038400c1209a80d03150008515101c0191954454090381c0c91494040c0c0e03408100c15401a1181c000c0d40d80550301c02d034018 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 102617985 1250 102616735 102616763
    0x230307170d031a030a03050d020c07060c03030f140a150902040b12010906050d033501090c020a03021209060708070c03140a0b070e0d240c0302070803010905130609 72
    0x30b0603615089180c00c9491801890780c10b0682d00401e1900340964107040403643e1b0310302d040420000c0c2c0180540c04445003d1128005403090b0001408507089109680c2000f10320120324002e02125055410000c03440340c1000050905500d59002000850302c0282500c092a41c0309403880c00c1c0d0f401504901c2e0b006038041a1100340100d0f201805014021a0101340880340c00c0902103950720b91558006005c1021b0304210b0b00c1c1495003407040c1802c1400409032056000d641203503611040300f0a10511484a1900c000806003074400708080c05500c0e8903501800b0908061841a06c203a0800c07414554012003c024040c000303441c4400038940144600e0395014400e06d50f0802c00400c04e4280f185d0b10047e044080d04c1000514902042c3e41e00000a0500400408601c0d001c52030350264034800606003112103040107010300b1801802c6011505040c01840000c20000c0e08030142d0042000041c0640e90920051118407910340040754001c2c510310080301510700315241c0c0c6042d6680f8081c1503131540d1614501d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 102619235 1250 102617985 102617987
    0x3120e0115050306040f02150403080a020606011706090610030f090c0f0f06080402090c0c1504060617060a02090f180f0a0506130e120705070e0a0501230307170d 71
    0x340d800180b004a011307014901e0a0340302c05a01c8012560000d128503403200218403042884425100070710341021000780c0343c010490020f5590070f0190381c3d071401709840d103141200d4582e04034100380c030901d400b81c069a001d80745c44080c0140402c101460f03809041d140c0400205d034044500c0b0385c0d40f070305004802c2c10b12858a0800c011566002c03030742042c001019040414400b481e0171540c40c60300141d0680704400c1594665140e1426400b50a0038a182402519614123006000400c2180104c0c000c000c10442d10f595021402c80340e0051302680700e01d5800c2000001c5c5a034980e0380c0035110244000d00800079a00010000072090042090400720b554412001d000c1800c009a21859000001d501e0403c02401c0400001d1603076070700c80c10718a0038640c81d6403010518078024080c0c50991010b50b003401340c03140c3c950719205807246080e01401001010200000307524446d0303409114101e507015442410329464074442c024801d01680421034061080a60000704e0790380782e00303070303440c021040c40d0240c4285040303e50 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 102620485 1250 102619235 102619271
    0x3020a1208090316020a0e0403031407020303152b080301030c0b2b090c0902092e180b0f030f100e0705070606091a100504060c0f03120e01 61
    0x103404204a039110401540040c0001100c00d000700c0a68840c40e08003d6100050840d649504501c80da10148410701040641503001909924210101e80d4119520140d0481e9203000485403000340c1240c0d15100344aa08110f100c5800c01c22903c10007070084d2400031021243c1c002114812142d9600010040091054002d018800380c41d081d0301d12480c00c10301c809500340c1c000c0d82107d91690300300224040009407415902c114001c65100d10301c8900315554102c204000d400156401e030040007443c01880e0706c030300e05008070fa1542500b00c10014603405010011600c00300403043d40700c0c0c00d003130606000c1603004003e006418098104803c0d01e03681e2901c0d200c02150098054603080305028280070510000c42e4526403264401d01ca80380107a103c0181e42440344c0038090702c1d030003000c02c2c030328082d954402c00000c00060248200140c1d82035125020315041201c081c0301d40d1094000007001400c1c464001260340024840041c000e14007038103603070040840750741281c1c020740303401015030340d940000c884843d02d41c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 102621735 1250 102620485 102620513
    0x150c02030f1c08090c0307030804050f0906061608040b07060606090b03040b0a180804030f0501050c0415030f24140102030a081303020102070f060207020429010c06020405030a03020a 80
    0x280181c88800c0082c4480c032202ca40940d0850103000d107510005003540f4041245005452004080301d2841c1c1e43c0b4241503009a0080c05000d000c1c00b00381103c0200740c105003500794064480a4006403410300c61001840c100400035104807000e036002c020001c0c0403000c0308042e0805600a2200182c0d1600d015400340c0915501d074003042010a003401040003080c5688410795021040d1203012a40c0002c2c0749001e00031121441c002443c84401080c08410300c402000300d010002d2040000300000d4403a601054014021881141c080c00350003240d240e031080c07194001c4810380c034051801048402d0710700d02e074100c010110f405104800000080c1008960198035a026500c807080c0040c520742084200c2c010040c010051031030302c1e0407100455400405200b58112804c0a41040044101ca1803524080000e0341c04414140e204a083c880d003180d8414040517060b603141401c00c41c101e00e0311f94440055440710711104080d03130300325420f000c00111502c06001c42200e180c865406800304003014a840f1404038400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 102622985 1250 102621735 102621763
    0x40312051003110d060e0712050c0a0302060d0902040f0207050a02040c0f09091808030721020f160c030506151c0c05061b0106060801060e0301050708060f0a150c0203 73
    0x7036502040410503c901045001c60296860004a83c99082c0740c0301510040c0050101d0703100b0040001141c11222490707201480c4590300303481036030710414100101e1340e000d0301010b54492810400c40c1664803039075000c0f00840e44060000f01b50400d0b1320301060101d1b0044801600c0a4010000b80411032800d44500d401c00d4165060942280c040501c0041041046028a91006640300c8a000e5500040c166285001e41d02c504a40e5580c9414034000305032103007115808900004692525091400354000e0703e01211044100c1801c208402414990240c00319800703440145c8082c40200229405010340d610030099100311036003280448080c08108c00344060342001440300c0b010329100140506000004403030085907007035105c0042500086910041a41d41c3c09250300c5d0074000164141c002c01d00504882c5662a401881078140b802d150913110f044403060000782c5004002903603454040e08024694001030520000c0f191940041a1340105e40f81c075190114240004500861808200c044400615 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 102624235 1250 102622985 102623011
    0x20030310060e090f1311030a0c05090c07031e0c140102030105011b020303070b0c0d020a020d080106031b0f0323040c120503030402010521040b0108060a02040609050f04060e04031205 80
    0x3014504e896035940107010b841d200c0224800400a12404620050000c07038020705541b40d08d07003140340c00282e10386180300d5a07005850110000e21451408003c4d03c110a81640305c0d1681c80d07007558440c0204140035042c9109214090003584040b486242412054042910005aa9504080001d00034162600382401c000071021000b07130050f10080300b510030040d804504203550f42c481c03000c403210350b0054048040100b4808a401c42c440c65000030310402c000469180d201c2c1d141d80307c0404405550102e813104407a15480401e290405119400c803401080d15494005120700820b07907550303444070344400400700e80128002400240000498010001c05501300071826910440d83c6c1c0c15200d00000b0000703414484041080184810f0318020040d0b07079100f08034503030b0443c80e03d850a200485000c1c060f0a825209020014862151510881c0c090f215a40c80d0076188078500b800304189072201040c0c1035001a120480086c043c9004400540a24400c0d110340c84000c82ca0f424040403a54024080128501 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 102625485 1250 102624235 102624241
    0x106081b010201020f030a060f0b09030a0f03050904020c0c0406080f0a0303050a15080105150f011b0f060c120f02030411041a12010e070e0402030c0120030310060e09 73
    0x44001400e0266100c1030008455035814000140e00900500043c1425060004104804843d1a92207403043c1c68512783c5442803d5203803044c0c00c00d180107000350745405601c0020303a00c000c00d82651000d984039101e0300d81030385030614541c0880e082c2d1f000490050410b0b8000c0340e02c1d081c0ba1400c1c0c01068081c1011000a01103850300d01802a950000c102c3d0140c18140e480c000300302d00f01c013280c00114804c0003000b0304000d642e603181a014001c0c0800c07500b072104561102141030341d5103440a441c01011405070b45020075a02d010050240d84806103900311400d45e031004c010400281e40c1d010f500020000c986804c180c80302c0c00032111081e166182d1701c51705490701c10010000003461281c82c0c0041040103880014036000c4c80110f0607a00c25450350010380c030103030500000e51f645030150020064007041401351100d603030b84c0d050380c803841510550b8000e61580004464480320751040100b0130781e03d00e007001000b0f1503a000341c2d081c6040d540240e510b040030800c405801c0c800e00b90051b841413061581a90385812600d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 102626735 1250 102625485 102625499
    0x2060705010f391e020c030714180123010e1002010c0807111b060705010e0601090f0608100c020709090803010e01060203091020030f090a06020a030f05070c031406040606080106 78
    0x2840c1945070704c001c51141000b11940c6442000300100b03004019080b80d000a485180c21264010a03081080c490f5030840c269400340c0044802d550b0496680b2895003911900b0b0b02e2200d40c2004406d0758040c10000c06c0320343c840c0c42d6511507825840c0382c004c81c1c00025498103002c50040480500805503410f11521000c400d444960004d101c12034015007200c048041c18106000400b03500c03494901403315824541c404129682c0440c00038100d6001103002c00c41c2602e01413501007900c0c030341e01c24100a60002c006808000d50584c00215180c0800d105070f80c00b5948903103008040718800e0100f590001e4002c4014800042581c2c0c000f40940380ca400110700b810800c0001515031600742520038108142e8503081c0ba2505030203d8689200b40910b0300307a81d16802040501d08458000c417481510640c030031030b0300103002e50011a1040c0c0160305075a4a00c59020380e004281d40c01d40c0505421203000e0180308000000c01d510f8002490a140c5400c060051402c150030910260341680d009220642d141400800080d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 102627985 1250 102626735 102626747
    0x92003070206011a09030307050105150a180b0f030f0102030403020c120a1b0f06050711010302160b1e04060f061505090910080d020a05060702010b0d02060705010f39 73
    0x1100c918250030384041004c410b000e140c2c056540d460b501880049051010401c041d00b0003445016484544800012030700100000c04003144680d000400b01c2807200d110960302c0f90032600700741102820610050780044c0c003207450030b43c0c10b00c500741721654040240000c00d07606010180c40030408885003440d2101c2c811200d500c5020840c4c1c0203040d028200820180c0c080c41e902440000d0441c9452461400c0d40c0360300262070340e805003c049980550850780c40e8041c1d1300074401e0b5000859070a0f40b144017900c1564604440560181201105e0321808002c000c1d120315900b50107100700e20610f8085003050410082d44180e803020381080003503800c40d5401e10b00709075202055900441e07040796407501d03648558005d42d4400000b40c03c40b0001b4003455441c140b501ea000500420700342c0c8078004840c00e80d80c40e10740807801c880d01040b8050744011580500c43c05403910300050005603008600002e9150140340c45041102e03c0c900130714035417180701281005101c03d10a081041040c00e08186244485c419100800d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 102629235 1250 102627985 102627989
    0x40b0a05010c020d0c090c1403011d09121602121b06070f0209010303181505030a0b011710050a060302090d14070803071a161205060303120109200307020601 69
    0x1080342ca6071005066503a4107000c038802c42d03003103480510b0b034540f40d640b510050800d0080c201c0100d43e5072464400150700d85000c480c129205110104400200e80499444080717020b050440d19115110b0041c030070400c00070061021713003081010b265101c1d4280c0305010160000c40a400044d0701f124030100c100c0c0790f40f038650401e0248115080c0390358804500d80003e0000d00a5806500800710700004010103400c018a0425400d040c041500c03403503907403403020000300c401d101c0b01000180e0070700c041580300701e140d0010504c2e903038141410130803984030070040c215800049442c0190a011048100500c1c03e002076900c01a0100d80740070351820010750f01154810581107401481065000800c0d014a2801d000040103045544183e9944442b00c1c24600c4100c0489141002085c41d41004104401d0480303281c074186003426154003c60201905005004000041c0055010f00003040701b0325880380b45404041c045e1959110003d1841550003003100341c1c41d0745500800c9814402c100744403c40e0740000d11141 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 102630485 1250 102629235 102629237
    0x3030105010f2d030e010e030403060b0915060d06080d0e010f0e0109050607020d080c010b0108100e270331030b010b031506070803040303140601050a0e031204030c0311040b0a0501 79
    0x10300f80140f14000c40040c8084210302d8100d51a00c441064903100120041c001c40740500c0701401200c1c44101081456a41540d000320601940d00b410305c42410100007415441030480c0700000c1d043c0e5511085400e2074030303004588000400f0907141c1142d560704000510600700c0c041c9480d0264812900020f0091800f80c05807038855200031075014110740d5650103645056900a0130030f40c54031000303080075020b4407001a4050100e54ad80d0700181d210400351030341200300c8400801c0503070180c6940c19201e000008a6019842c19982c6040e19004c3c500200024a02e058030410307040c0d0086074040001211403d10030007003007140200c0c001040072549280e2000e06449061130455a280c5400c4210003402c1d0044401da40c1000300410008103002e090800f844c41240280c0301032004041421140c9050102228000c1c00700d41d08bc81740f00e903894402c040b407040f4448040c04451854485951002082e00075138800c8400106407070043c420880300c411020400b050a0b5401d1080c10f803007000003102207096020b0710b4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 102631735 1250 102630485 102630557
    0x3140414040f060503070b0a031b0c020405070e1504030314040e041b08011416080c0d0e071232030403080d15030501020309010b0111030a0e1201060803030105010f 72
    0x508610b107a010074020f1100608440b0035603903c0c00040b43c2038101c0140800440d150081c00300c2c0014021b422108900303a6565105001700390780d4200401010301604003400c11490104900c003a849002c8400c050140c0300841945030313844e51038028601d8280038908140d60405002c00c0009000c03883d20250810360203031584080c1c15100c44031344040d541d16800851650309040ca0302c54160030400354180206d4142c03a80700214202103e0949003108140c803100b2840004000303528009a031703940800200440c80055030030050b6114024044940080c00c29111114002e4283c40d84044644100142e0300d86680c145551241801c2040e48a001d6440701070301104001800c0644082c2c0356010380070004030f981d9046100c544908156000390412182609507618200c0b200c1c13582d600543c41c42c6107001e802d40045203080d03c4018100c400b41c80c25400340340c03c00d00e80303490a04500000e01400f40a0040c5800554503507250030001058000313903002420a1010710455003503010440e92545c1402c00c2c1c0600c0c42 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 102632985 1250 102631735 102631751
    0x10080f15070e01050c0304090b0a240509030304050306010b0d06050108010b041505040902030709060210020906033603070b16020307060b010e120616050c0d0309030c0b010905040314041404 83
    0x162401c0c485c030340710780146003c002000f09500202c0d50005c803082070255001c0d0b40f8561124170141003016030950400d1001000609036288500c41c2000304000c138409016642040d0ba6900400c2c6811801e820101020001264030300141031288502e800618092a00f402194500341c1505024403c0e03000c3e44c00e105004074464a009406102258000d060907001103540c0d00e0000e1000f4449e01a900032007005000710750140c2c04849144c003e54410000040c807152440d00c03405010710604800d46480c80082400c2521051351094441580180e0781160b000365556282c186003001c00000c0c014a01d0510303110554540c9401d80e40001581c00780c1d40c2c032400c0019000340b81401070b11200d0300d10440300d902c8070400542001e020000b10300c05001300017951490300300508039031043d60369003d40361072a82c490f8072207001c40681a100342c000302255030080c00d0046043d029038407100034a51003604076110303841d118000d02c420541d0040303040c084540f01880315030620307007841c08204410f0f41800c000ca1040e40c4a002c8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 102634235 1250 102632985 102632987
    0x6020c01021201060e09070207060e0402090d0c170606040c1209030207030c09021b07030206161e060507080604140a11090603010e01081908030a0c030b03010510080f15070e01 77
    0x11540c02d080c1400c0100070303a41e0b507a80700812941d00c60100b20b000b841240045030000f4000500304040d660b00c0c0c3c644400541a40050100a400c510501980040c401c01c00c0000300cbc44c40f081c130402a00c41a0b1f8006843c0031a0200c080c81d011000d0f24403800390b460035803042040340c2d10210300d0803010f1580c0000304038401c25003803c0740b070b00040d03400190240800d8140001c5d260341541c01402030100d0260b484240e00b41c51146a92034104074400a0b40189017081710340240c030052148408054400d078071350342c0d11104e610107083d001c2c2015502180d074160f5840511907101d4014403c00e034403403000c41d804d000400d0040ca10403c101e070060400c2c0c4609480c4c0d440d451454454500340c807481c06010300312340e84940c0d40e10b86c0300404410a204510381030003140256a4511070003030110700040c2d0000455071950b1a41880760008100c0700300d424080565500c2070320120303502800f425001c0d0f41201010b404140c2042141420b0882c01211151558010342c40c2050505a0801150741b100c194204240c6501c00d00b00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 102635485 1250 102634235 102634237
    0x6040f1106090406090c02010c1b02060304031b150b0316050405070c020402070b01051504030c060f0504080f060f062b050a0b04030f12050f060409260301030213060302060706020c0102 81
    0x40740c2d541c0b240c10614041616505075103d8004403078140e0007441001091007055840769451194589611208014a009414003400450304940301e445d11015070035003140004503a2880c0c420444d007600103104d034203440f00303c1c60107a4440961b045010300842c4100c818501a001094071405000b07913121400a29128020030140f624260040c0040d036980f1a07501d401091600c0c00d0086910543e01c1800c00c01080a400341a1020f40394002e4111400900703266068031040e441e40413440400c60300b00030201c0d298009000e103000e0002210300038503040c01e0803440040c591a00410741400343c01e88003040c0305404600001045490342800004140c01d50380c0c2803e40c20f0a206100103005014683d0038081090307030240c1803032040d903070640c0c41c010005101e45410066440a035030b0310501028003404100d4a01c4c041e88060340041c030880ca0780400d0b1050340503d43c092030b000035481d07402344008401001981082902c03420b0161003a2000c004007401c55000030010300030b81c8000b80500e41e02043c08450030b24258 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 102636735 1250 102635485 102635497
    0xc0d05070504180606090207081803010b06040b070c06080910020708070606080a0c0e06090103111206070512060a0503060f0c070807060c0f02071511030708280206040f1106 76
    0x40c105011490036090101c40035800d4070f00071289107180040005441c00c80d4426628503030b0740440400c0c9088020380c4940e075401610800154103568403901c600ca91307a00c0c1030050000703110303200d00542c580364281402c5640407520751041b000d0040c04800c100c00364001046021641c0402000180c58483d6410022407038000c1c154020011031030400045603e1400007840000988034075003041e0281d8852070a2041503405a50440d04001d110005000040080000000c003040182c00c1d82200c54000c0c605501e00382c001c1d00c101001c5417000440c0070a0401c10800b0310340c45281507a800810303030314040120b95217100042c1018100c2c10018081955010940300b2152940e401c251941d85031030803401c2100083c884900c100d0041141501e104403001e001003240b40c104d5421400040020b21410400d48070008040d030400000d000030002200000d6001010303110002550002034607460048800301d07984041d480403c0f007958041000c00c80001d9103103031008081c0750721500c1d04141c22210008a10303540608 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 102637985 1250 102636735 102636739
    0x4051909020a0306080607030b01140306010309050a060b03070e04050307060b06160615090515010f1202390601120c05090a0f06140d0813050a0305060402041b020c0d050705 76
    0x80c5072002c440d8160090790030b03103210b1400d40c4d1031a100e42c58160100e0713080d19180341c08200c0c540400c982c40780042c0003071035000c541810042201d07000340d13440d1410032100349030440749903a032110004c00c6820100b1500020f080c0311900f6480382c1c10a52a402d60303901030404010820ba4071327040c0c141c1140d00c401e029540c080e110740c48822560503451510001400f50014250200c00b03080500081007006402018090701e104407003280211603d03001107601e0080c01a01405001462650380b0300ca0825100070201040e107064007600240840c0352180303802121070541d10001c82c451000084002c0f010070094111125144010f2102900d480c00c0101c0100960100d80d00c144a0410409603d1180d08072850b0f042100c00304000542d100d2040d10740040303280b01502d41001209180c4400106070000070328006250541d2802e0107552000064100400c6400441c0c0c5a00007505210850415021b4614002c00c10350001070440090710000b90748403035548100b4803036414100030005020041c0312002c003403e40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 102639235 1250 102637985 102637987
    0x203030408072310030c0e0a090b12061012050705091e0106090f0302060304140a150f0513030f030e010c020a03091505031810090f03180b0405190902 66
    0x141e03150140d2a00018031034040e0718241d0000321240b6001100310000b8004004000e441307001400a000c40003408411821000d000c83d04424255665840407e8801081072840104040d8010001d0018000b8415100ba400d64411028800015021144182a14440c0b04400030452050415a141c442c0590005401500c03641c04e00585951030102c01041c0d00c40c50f000ca050599030340a04035040001441040c00d0b4030860b0205100515000c8011600030b401018486918a6010110303410482c0c2514200d0b070183d0781694070030482c04c6c00e016600c1c0402d4450070400540c03421200b80c955183c03011200038204010810a020004d009a00c1002c03d28100c030003c01c07607001428000b82d80ca0700754071000c0c2c0110b8038001c00028600c940701180303240d5090ba40d80d01c40c11501d5452400440000d00c01c000c004074041c2140300c902c0711400f4403480c460903000d1030300070400c0c0381c032418060041f0710380d01c40e4804410785085045c000e2061040484080340e500b0b84807000010650603442c40d100180e40c00c03c13503c20740 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 102640485 1250 102639235 102639239
    0x3130f060902010e030d02030f0c0f1e0d08160c03020a0b040c1a18010c08071703070e090f0f070302120f010905010e190f020409020a120e030a170703060302030304 72
    0x2540e680a00c50091007070321594a0055440101551040103298207801130b40b00b0421030180c102c031000580741c064100401c030388040d0240300c01241402414811071228080111250048500421800c00c00c280750b400c1400340c83c14482540c40c40140070350481c41c240080444504201482000304c1c1c89050382102d14035825040518000740f0740f814621813056518000005031210b0442c10080301c20f4003040b48149080d45111400541d03068400e030710306480f29031007440b500c4003091150300b000f0041090040c80564a1030700e44800f44c008408105100d004180c4401080b1840071000d5004c1c0e007050000c03089000c25030714001e0803400380c801c0c2c0c1c04030608030b003404090011010540000c3ca050380c002401c10320250b0303200c90034508000411030707140c0540010a00184860301c415404036280c40c441c0000940f5040c0c0b120510742c1a80c0c0a12100c1000820f40e04c2e640f50700184138403d039085a84008051850043d00300402010282d000c03807041003007611040865181802980041e005590290989840350703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 102641735 1250 102640485 102640493
    0x120304021c06060512160e06030316150f110a0e041104080303011809020312030c120c09030d051303150b030601150801120b0f070e090a0207060605040b1503130f 71
    0x102072032088500420b1170f442200084a40400c940e181c2d2148401030800c1c5924041d10201405009810680c050008014081040b651070a0420060340191b1000d00d412030301e50b0040d02200d044607074000e821440e00b05003e40380d0315240111240c042e01441d00c0e00480030000002402008102d458011510f0300007800500e041010000e181260158000c12441010141411007a0f42040d41c0007503158100c0c600c0060280340b510007554100303000b179134214208016141403a1080d081690341e0400702402040f8180c07107207807c001181c100591403070f01e5810503584400c0032400341824000100703626070380d200d44452810254880908964001e00710354040d65103c10303000300d0400054a0400042d02d03000003052011107141c10340b64007a0301c049107002c150f41d00c0c3d00305a80f001d4098402c1040140c100801d0100350380340b0315114010702d09503400503070f508464a00b6000311341060b130200e0b0145041c078801c189d0381c0ea100858018800d40d440e20145d81c0c0da60b03c4564007250361110400510f88005100808140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 102642985 1250 102641735 102641741
    0xc10020a0c02190b0a082e1517060f010e15130902030106170717040809010f0813022e05070b090102070f110109030c03060516080405120304021c06 65
    0xea07009840f000361880320100c02c040c919140340904040c0300c03801c1103403a100900c5500b04036070011040803001030005611109582e441041000310225041100c8103004641d1007546070030f2454510b041080c0180c80300b00400380d104038024140c52280e0961040d44040340d021b0310140041040c020011003201d0524112a0810b400003013000075906c0180b0008114030405d48200c81c1a61055218000700e08004400228119001003001e000c108040209030b42e80e40040c0b43c2240100e1141d01d83c2c0703480e140706034001801480ac4248140410020720148000c8000009a080301c417901035903040366800540040e02c1804244000c01514505d012001100f0241c0c080003a00c1c40724410344842d2420344411340c0303143c04d034050410060407407029440c1e080002010014440ca21100604003102d19540c0c07510342407040202c551058480c40e440d1420408084407d40540301d01101608103850395007880e4403815030714059032951440c2e1240c00030114081d5507600c0070040c90200f50140340000741916240030005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 102644235 1250 102642985 102643007
    0x10c110f1f080105010c0302030301120201030b03010504120e03070515030c0c06090304052d0d02041d0102071a0403140d02041502030c010605010f0c021e0301020f21040f080c10020a 80
    0x500d02c0300002c1040e600c42c01c568030380d06030154011070469090901400404001c01000c9041c56612054003100392001c0c05080d01c10360040605602c506440307200a008403c4529802d4441d400ca80000e12581d6a4800c061506161845580d1f403a1b86d5030454a100c0c81c4591251a0800c0c0700c0d9200b007040c00000040208155001034903003070b001c41d401c8000170b0410080c001c0103a00d440a02101c5420b02e09000540501e01c90004101241c244000c10400c8444200e056800b0b40994001550800f8403005020070f401041c580c20030ba4610385000d4600804110410006e001e404100007130199048440d42c05682c0038003603152900107542e01f000030295480e800405088011b50070440001500d60060140340801000d5840c0e01e5111080e6034200400d40701106400c1400d803450400c2c0da035480d2024809499004281818a56101003a454041c0d810308407140c0c21210300e4400e820000060809089000010f9001440648a48144141c00c1c1800b42640351401c082d44086020307640e1320b91180002c55 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 102645485 1250 102644235 102644237
    0x60a0902090f062a0313140a09050703230402090103170d1401090e0f10020c01020412080306031b03120903150705030a141003110a0e1005120309010c110f1f 69
    0x41c1014420404d65228004c801204005000180c002c000c1030301003d1541d0031101005016101c15522a00e44600300ea10907a000000699985d10090941c4529052901880d003000101441890aa40055012503050100410f0484c0300d81094144181d654255100000c030040107100c4061882600c040541091081418290070600100d11091380824412464110000502840841c0f00c6644c4040e510080242c40b07190760800c00000d40d0f00d20215689515482403404a607a424228101440c11040038007035840707468200784803500c9070740005c0d00c0c1245104540f000e603120f0b010000041d041481c200308000c080780c8510300b00714001d030b8001c0066210b00c490007030800203890003c148801140c0d04540d09800c50b417031201c0c01d101250003025a1240000000e0a11100d03c0c1c035042141c411450550310014441101c0c0020f00c401d00e41004981038a00003403005500380000a80000e002071190340c00541440040e00d00b0300d2a984030004100030244002e05203001c8882003c00d680b8038000c41449100c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 102646735 1250 102645485 102645547
    0x20114040b07060f0c0c050c010e190f031403030c070b06041103040f03030c0e1311130b0a030f0b011d0319080309010b09090a0602181305060f0405060a0902090f06 72
    0x12005805008056841b0b40c010b001000e410034081c0040d44c0108440c4103041e400240c20031444c100316403079400c0b000901640c64507908a9807842c600085920400c4800040310b8105004008810500405544c841904200811650b4440c88081402031107001690910700c40c0000400042c400c0c0110f22000c0240301c1d07642008140401070003102c098116030071156000d2078404100041042c7c64202c19461048064810700d00051501401c44443c51039020310845500411110003440c0c15115020701c07014400400d200090b02140002d21070420305c0e83e0a40c3d4100e071405007451644007041101d117541100000341241901e107007000d1040b500115800070041d824044034082d5401c290800c01d020f812424014251034502d0365400740a900315136440144404140041c1e842c079660741c42d604d00d2103141f0000c0098035003441c400b40400e41c0d40c0f1884481c000c3c0d00f008180103031625202c01040886000d0240142c03544050800141b269240e280c40942c024400700320080c0c101d509148511030740806003105 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 102647985 1250 102646735 102646751
    0x6080105100b03060f010c050c030f06041205030105060d180203010606030e16060206190b1809010e06010b0901110102131d01090b010905040c0c06060608070e031207020114040b07060f 81
    0x1140e101c119400303500100003069103174180d40141c21412045120f04140c840004145010a203800c06481c4e80300030031360000040c08140300790381e80030b070384c2c0400d85141040c03640d070400c0c01285052260b440e03800402d0b0b0781e43c199162042801910900284c0d4020000c0c032030706036120001405170400804080050082c40318411010216a801c3c0d0200c07a401d801070041691559914501300d10001003c0106c1505c80e0001902661201900d144622050381c101c219810840001c900316008140d51060320303400500113101300e02c1d648003510090002440c281d080580700303103c5140a80904000301202d0b4002040100798034a01d003001c44003166007403104203c3c507039032540d030b03032064618012640d40401c04100c000e22160815400c0115945080e0a00480b2854142d82d44000c441d544c2d880301c00000c2c401420700c0145035200c54642032a0350300300d00401c0526090000075841d07106050700241030182d0441510f40d40c500b224241c0b0024440c00720030685a010320308003580a000681c80443c8202c0c036003444 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 102649235 1250 102647985 102647999
    0x8160503211b0118060501120506160e030708010c030b03030a09210f0f020102070605040302060d020c0106120308010602070f0803030f06060d0c03140a09120f0c02040608010510 78
    0x1070480c5008007825070340900e00c80742094020b9114414100300107105040001d030400003409103150006820f130101204215905103002100c4040e04943c110303415182c030740c4000c00c84c00035505410072034000210036050380d2200e00b034401813014400c16401d030141d10b0000074609010b50103002030b480d40d41c8051050981d00001c1603200e1040e200d4000c00700c1e00c1c0740c0040c04002506941d01c0d02d403101460b06150003c80c5a1200d02074016038150417580c8800c0c07521440215641030200400400c0e00742411410241950700191642c0070b29290b1500040d40480c1002254401350800c50080061180c00354180d402c2d400c0c000e000c40b00900a520141c0304c0c62000040700030354004c006c0229291800030b1429510792403019049080081c045c00d500c102d00703011501c1249024410700c181d801c3c03a80c40000b4194103010400584200060100360250714021000e000f1981c040a030865108091500101803c40c0d40002d03990501000d1010f90403034901500400c201005602c07280c05180c08805140c0c0056907040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 102650485 1250 102649235 102649243
    0x4140109060605090108070e0a05090421030509030a0c1a0c0a02120310030f03090f0f0609080102030906040b0712020a0509091501090b0a0509040903020c1e0f06091908160503 77
    0x40c4c8900144640c00000d001d01d2080305480ca00c41001004200d45903655030004048820076501a10b42c0c440380004581503040035110b144070b0101508080c405c9240110705c65440b4010410424203004803449020700700803204403807801050b084c410745032290810b0500403031030740c0200104034090b100301a0207211000524040c2c0340319170181e0b000d20807458219924100b940402c2d403002c07010700c540290007003041c0074070390f400c1005000040d84100b10180345c410003e12890f43d56100400c6a44100103004218101140240c0c2c499007100380e5040648130454221086400000354020703003480498420000e640c00380042008010445009865454160a008807100c42d42d403018046040c07413000304a4101c0f080083c00602e503050030003504140b07059000c2410745140000460040c0c00103140440341c0e252002046072005e1000400c820350810148c085110381c2a4031041c10301c640b6000c0385101d003039611410340300151001002e0009030681d450081e0741c0e5130655541490848440b018003c40c1a00b0009 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 102651735 1250 102650485 102650497
    0x203040c09060515071a010603020d06120215031e0903030601110f0a11040204030609050a17040324020d02070b0105010f0507030203030f040507030b16090b04030305070201120b04140109060605 85
    0x144840b02c2100704108440c125032004504481b289100c19131008458039096116008240300d0f1800b50380c0d4284814140c0484101d03402260a0b012512494005600d80003900b8102e4600c42d480d90fa66034407407a0400700c0c65910920800310094051040028012001c0061402880280ca940200a908504090315035940d01d5042501d9032201c0542004120700c6201040408809000181b81c0380d240e49400090b900042802d80300c60348000340200c1042a00305001701180404403a0070b0500d400c503942c01140c00800400041115402ca0301410250141d031304840c0c801f19001c000715030f40d940c40e25000206032004d103c2c590104d820030b50503035540350280d411180b0f4198181e026620b15a1400c400c507a1404004d03105070b61904c94060b0100002c0d480600c03050240c2c0704800043d030042e8038100010b05280e800e03005588010424401000020b4004080d917210503070908204000d0200204400c1c0102804450b450b48241400000c2a42403143c0d000c141c1030320640e11060211540742c0a040e90941300350b07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 102652985 1250 102651735 102651739
    0x30a0f0c0504030b060103050601030b0613030b130c15051c14070518090405070e040311060c040b0706020304060b060a090501020c04020703090612090c090c0e1008010b0f04080307060203040c090605 87
    0x44c000a030b840d0301c80d6004c175522640504001070104030a10120315990002c1440c0c40c05e02821f02d1040c410301001d030380c0f026405044101c0d00c1c3d05080c65a51030700c10a0300c9611030551481200506c168104e40610159041c0c100601100310380128101d40440c05443e0746c141444e4086007400c04207040510403001c07202540b100c000b1704070b0248241c0d028807181d40402041036400303010b8a00702041360409108850700545c000d85d240008a9142c0d40107905042d000740054207608003c00040003810392040945100c1500800c006842e03980b0f41c03e100d000f4082e0034000d168440400600c10b600c268200d04248203850003a8211441c0710754580c00d020407441445c0028002c030300c0304001085094400d80500c2d820000a10001c241d02285a03214a01c1564071b40120840a40328540588001c0c1e03c0310b440a080c030000c640c120300350342c22200007034a00041801203000044002421101007a0300c44c4c11500104022021641c0e6040c1c01e0421100030340040d1000c862002c510580020401054025542600c0300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 102654235 1250 102652985 102653003
    0xe030a12060915050f2b031e050307020f03070201022a030a06060807050904150903020a0f26031006050a05070209010e0103030806030318011d030d090602060106031509020f0c03030a0f0c050403 85
    0x308458004683e50200421401c03c40f048c46a0701803230720040e1f02e41c40f04140e030342c0302e464032800d011601a040481400c981c2159070310038072405000d80c1e40040d109281540310403d40c000d9025a160402c01140a45031030354152084103503c8041088079804201199880c0c829a42c040e500e0310300700400450f050310058417219035500c1e609080c103403d51002020350310a00451340c02c10820b50702c01ca6003941e03048040e14507440241044501003142d848440b0551035a80703030303140746141c58500d00c2c00904141c0030344010094003050146200d0301600c202c44040382c00601c1000030f903039180d040414107002400220b00154803080412031500300042a0f80808140c03203104c1000041d0782004444c4d14100074800c442890b0205501502900c1c18002e50b482000725651704052541040000f901e0f2001c182d00c19020140f805003100c56501080e01844107030b48007628003598034010310318195110701480c20312401034000041070003a40301c5958440d00071040c240a090024850640c01681d850040c0d10020b0500d2403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 102655485 1250 102654235 102654289
    0x1b080d1409090a1814060711031206060c011104051002010e1f090b1617090c0904080c0607050d06060206010f33110708010e030a12060915050f 63
    0x80c000150030303444004800700040c1e0344907606500500e84165401900d49848400554150f521705022441e4011100e0030542a20781c1503a100f690360b031040b0f14000c040c8401040201e0403c0d6654402c407064a0349407002840418030361550300f005a4030510620340f0500f0441201b12030140180194803091001d0400b80204001d8955580940c4140407803001c003181d0b40b2806140001c00580710f880c0911040c103010312290b00350003005846510b60018550742070701c21008002d41c000380095481100b08007542d44042c251120320303049829008020a85845001e8070040050807544000545000520200305010440d40c3da00143d84403a0203010308140d60060010901c001440303003180000d001098038071420015004000207610f1072003a4005000035400c0700c0f2400004908009181c05401d10000803c441c541c1a0251542e030700ca1400074809004400e006039001d00b14039070019008149a900512000d010280f0f118212151401040c0c8910003680c4a04140c0c102404203503092400140034582c054 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 102656735 1250 102655485 102655489
    0xe0a0606031d2a03010f0903020c0d0b150f060301030f0201091203050a0804080c0a0302031b0613060506060c01050103050a02090a0c0903023c0a060c17090d1b080d1409 74
    0x400f0220140146850420f00e15003510709200d2000040390000740040d00e44050300c1d0003420852681c400d075200c0d0321700c103002001107101400d034150402e5441c006500d41c200f24001140140c6000341103c0e902590100000081c0302140d003ea11401d403003681c51380341c01501c07080c4013134081c42d030f1030000340002300d0031302c03c402c02d4038022000d0a8005004103c02030a00695005142c40c1429000048005070008030343e4005d040e283c07481032184c1c03074904409811f880c58104582285484081c034040c09880e1104007007005a2940002c590f000d042c40b1000b805550f0b142d041c440d54030b07941070404038007500c001da0006d000b000084c8141a01421a82e03500010a0b00d03540800400300c00031035682c0e18500a1000a10481d000000c4518594610404801c800180d84080108020300341e0300147c00d10045051010000da00800a00d4181500c00d8201e911004524003290340c5041402000f0700a64440c01da5042c1c81c7c0c0402c0341d02e001c6034a010100c8044c00a95082102d1142c40418001c0c455001400311400c94 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 102657985 1250 102656735 102656773
    0xf03020c010c111e0d061d03091302090409050d080103030e090103051e030f0a02071d040b01060315090501030f052503030507171903060603020304030905060304020102070e0a0606031d 81
    0x910201303024400030006800540f2000d000c80d801c0350b4199851070a02000c4108000c1e1000803c4408050350034039031604040340c40b180d00c034074800700502e5001031025420745e2150b1100710b40581141c122000448110700c0607028003400e0000f50081028a20705100500e010701384207058952100c041c2c80c07201600c0d11000080394500c0c41d4072040b40400d000c041c8810810034041c210306025907000301039240c98032607508040706e45210405103d840c100100301c041802001302c3e60465886181c0024aa1600740e91040011709541249092504210001050111000c280611103021784292100d4642100503900c05c059107000c44041c43d00005070030808a40076101038495140540c140143d01d2081c080d000685034081015007c40c2d00c43d4010000e02250325214000261402c0e04045203107042c40d460143c980b1403240304141c070a01e0000002000c5910910482008102c03003071406480b41000d0780124040c0005026190000f0310b0044000c00000512800a044403407890280c40b00d150003034800103003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 102659235 1250 102657985 102658009
    0x3080702010f031413020a1203090512070803030411091006090b0a4b02070b0a020a0605010311040e0c0609040b0109080607020303070e0118090e100203040f03020c010c11 75
    0x145980c40a41040c00c0000801445c4950955201d04e1503100035407040041540341e0b03810100c030034201c84030005c000907000302c0c5117002e0b030b803046850040451700308400e01d01d8003d69070490155804084140420400703a00c4688a500c0f0085401c107210341d88900c0e45881448441c4102000944e50400c200030704c2c8030307210040c2045480c0e4a8403000290b8040c080080780038445817414695000e4400c4156030501c6c2d02e0703945100c4021010b6600c004200038000030366034002405070041c0c05c0000030307852140c00d000b0003d14600d540c0c450001e201c150f95a04001036040410f4415500131410303e818005001c001140c880c0d680d400050900d402c00240341e06000040c48034514007414000c1c002000b181001c02000190b2081059600843e0b85c8d1801da00002d0000302c908403854180303c03000301e6544403105280284000c0d030302c00780e000186e013055074805140f405070b4007030410000c9480002803100b400000000e008400380640c0032a482003144000450700a10ba41340041c107110b01c1010f8003591803902400b0800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 102660485 1250 102659235 102659237
    0x90506040606260c0c121803070f060e210c041a090a05040501020705060c03150a0302010807080a02040f080f0c010503270304031406040515060310020d02160804030b1003080702010f 80
    0xc00c111004601034031b0103d502e285000300e00408900d640b65140c00700314040100000342c019140e110300d8421180c039072909174000ca00c140080030011882a45074001054403803160007d52510b81c0d40305450064464403020407150203541090b90003a00c00120900044a040b006064040e40d55204980c0d03500910f4090b20032210380d5020008140802c80421515001c0c0352a11812503503030410580c0b00b202d680d4045c0e0701c0350044484803004c0002d81e030008005076001d481820714030b03070036074926582c3c000911690704440003003c80408041650300c000184c0d40d4440ea8244100c4414860000040d0707494041201c4210403400000010394449015180b2000d000b00d150040740d05098485e42e40a10103100c0b14486081540400208800d1010400c0301703680300500d028080380c090400c400800c0e01c650b5041807282072076400080300f22020000d030b4121641444903090006528241d0714007103c00f40d105102c15030f2003d04050100e44124401d49500c4100d030760207810780e46060200c3c0c1c015580c14582400d884 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 102661735 1250 102660485 102660487
    0x307090b0d1803080109051302011706030723010315080613080405061c0c140d09020d050d021f0b03150603030702040603050d1d03061f0807090506040606260c 70
    0x60b184400c0d080207180218403a8441100307660414044100b110f50003407842122038a040c0d259400340c1d8104581e105a08a5542d034980f00350b840b40c02007403a0110701d501000010303c2208410504000302d02c900c28484c80c013640c040c400c5060b40c01c940b11212a1034091a0030760b400000c041001003d00816400103213210340480b606180d0760b00005081e81d000b1022100c5a00a804201a41a5194070500c110310340f460403d004084c0d0300e490100194000d002144e07080d00d5842c0c19520035541c40303492448100390b108048038400c1c2c10500c0001c2d210400740590248010040342c0403010184940a03c4100743d0002d0018880f944070403000c6059000e001d0840d5800d80400c000000160300e8138000d2802440c007032002400369621000008014106016009400070003a245002c0c4564010402035040100e03008000c8100c42c81c9280c000180c14243e000000910802800088422103500040c1c401e1004403000c01c4203640e80c900940f03060b01a00c1c803400d00f040c0c100c7d0f0a81c00c0c175455018a0750300041c00c91441 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 102662985 1250 102661735 102661751
    0x40b101809050a0507030c1b030806061b030a020d08091f0204080f0a0c060302040501050d090303060b0d14010b040302060316030f02040b09090c09180a0216030806010e060307090b0d 80
    0x500c1c2254400d40d0b881441980392400c21201039094052030749086c1d26850024000321104210081c00000300000508010041c00071030901d588440c141c038280702c005910340038010003110040351349511920820015005044a01b040a0300039000684241c0c9127901902e607468040b4032a40d80a510407201c264a02e5003804085021401045004c0000314824002c124018150404603030080c0d15907c1034040500420061109903444800d0740c01c08900500d0120700f120306440c040e00a400345c1c0d0402d5050310800300e10b0f02c00a00302600303c1040481400b040041598032062868024411800060340100c070401c040b840300030040c1c000c8580c1e240f080c900081d84604a21070302d42640d0003a48034014051021800c16900e00d0462007154020940c512001d1a02c0304100200d1420015602080541e80240d80020b254600c1501225030313141c2c0d84113041036880058a00580005820b0b2419800180c544400c1101c5080100403a0300031449500c9040ca55440c0020f518415405140718804698540c10b80c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 102664235 1250 102662985 102662999
    0x3040b0322030f020f010510140303160822030f20060f0c070b04051507080f0f0417060c1602010216060503180106060903030804260c0c040b1018 64
    0x540c0307061511035900c030001e6a19081c0020f1800421961030f08042e450081480400c40780100c00307504a4a4030301501c401402d030080042d0030350151205090040741c04140503000c004402004040a0702c07811020241d41a042590f03c000e03290500005100d000d1006048002c2481072040000d00484007007400d102d4aa0134002c100c054100600d410040940450f000110360002d00598028181401c00c00c0c0c01c0528000000347c0d144404019a0103003080000c4490500c4050360460306c0165903140d00550754106a2010300716640188038235400742902104103144981c0c0850810f0080c1c42d266805410883c00c640309030448192420100c2c150311842c0040d5540e09800028180100070b25120280c13286440580b05003804240102c0038541d901d0039a05105543d0068200015a40c0508d8960019903652601c0505001204a0282420708048581d03000c0206c2000614240000005a5031000f5480e0306000c16980ca0386441d41d0b0022446441100040c4111300c10030404144074450740c0718a03540c9a07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 102665485 1250 102664235 102664291
    0x9180c14040b0301050405030a0302070c0b03130303050702010c12020901030605090f0106030c02160902090d0204180c0923061c05160605040e06090c04050307080c1201020a0203040b03 81
    0x409041000d040003440515450070344a21a40e41105070001d00007441c040d82e95507104e01c62401820305141e4046082002d0003204621280075105032000c803592801c200c1701d0120300d01819141100081c0c1808002030086106001300c0c1643d100f96214200d0740036007002e4800103500400001810980e40d011b002880303590761041c2e140209030480c0c821204d5410f14400a00352091190250259481400b4800b45c50041c0740030300c1c04503110241c0040c1c48103442000200ca4807051100a03522a041c500783c5800000c0c41e210034042d6500c100400000c80d0717601c036a900295904814281d0f400c00c185022404003820203440540d10102c014484150141511482d1041140703061040e21740c0d0b40045068070784e04503007044a001401c0c0c00d0400a0030280f508508541d000c0e00104550300802c074610100d02d40100301e100352405003900500b03880c2015220a00580c2d204490320050b0701c01d0052203071081c0d0020043c4211000182a98061071806042c001102201e90003d8158103400c01050061600d036000c181c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 102666735 1250 102665485 102665489
    0x14030903100221040f0f060605060705030c0106080c0102030a0305101a04060f1701050f030703050105240d0503040b070807060911030f0d02070513060e07050304020310060b030109180c 81
    0x40e100503124084450f003424404110300d450030440003c802840007040c10300400402c0300b5480055940402068038210018024590000b50012400306805c8104100070000d01510b2020340020020180d0343c04c9560350380c0c00c41c0034840f40035030410080e40002078460381246500c8030885003060611507a516005444078a404444c024005d400b003000d0007003c2e4031a4044e014583d092508404007009900c044922071010320403a8422081000c0510303081c1c0f0103014a01c0115001030080010b403600c02d43c044040424200402a40414144021024030b8000030041c102c2d41c03c10b004604003420520130b40110390200c01c05544070340c414014000010154003564000038400d482140c0f080300c1040900d0b213041c2e00e00303000310341a401c00c000c0c1401003580040e201c0d04540080710081c40c09020400e8a00050029800003103104a809040000460300080294041c51095007116018000441010304864041c0104200c03464108010000424103412202000b01c85409140714140e944c1d031600d074500c1c125 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 102667985 1250 102666735 102666763
    0xc010204030201091401140c0a14010c030e031201270f060501090e1501080a0209041406120303100e1b0309100e0a02010c02102c13061214030903 64
    0x2030a000b1568000e074090014103071040007050020240b00081c080007100324088250903c0401d0b0606461070030002035507207982140b101d03c00220222805406410b401d410b84010a0520100307114000c000001c540c5080d9000344c0000b00303a42848000492020850300380000c0c04005540e0002030a03083c030502c0941c1351000340020b4114034000014000020640c071820390400c04000700840760803140f00342601180d092030115101d64805d02070030000d0107400b880e207421610301500456110b030401c0c15113000f804c04031607410215911500c200d81d24032084800e400c2050301c46004210008041c1a803d070882d0903c20b4450b040c04d42c03c468082150012a51614107034071048030341c442d0181500c0754225100c40c0502070900480039800103032583c031210000034000d00b2544004c0400034030070000d85803690002580040e0b801c0000b1001c0040142654800788591a030908540108145d44140710484d900300182c2e80780640b4684545088075028003244245000421070407030956814013801c4592946 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 102669235 1250 102667985 102667987
    0x5011409030d051b070f03030f020d060906080109030504062a1511180603040c05090f041e0309052e030603050c060301060504170a050307120201050f0f16030e030c0102 74
    0x4a10607030b4054480203003900341031140c000e004401e40042c0008a9032216040356108512900e40e14007200104002940b6000c900d1011070b51419800907604884111a0010800d010349a11510181d08072203600c2d000402141b420801082014010840d600481c4824443c45030a140d100458544804003040d0441d030000d59038039401c41204192103206031420300f101c00345090207005c0c04035511800c100040c00d0b214080110005003005000c49021001c3c24016090440c54104100c0c806584030301500e084608105a50001e0501e0345480c3c1e0030040f0f1b58051741c0755584075140c2001c2c061101c1204200e03150052160345c1448625003a182c2d0881c40c24242e036000100350b172031802c1944c28019802c10340c81c4105d600304010411554030105890a446207100301c0741454400200703241c0390540049000f050b90101290301c3c0148111041300f00015403150300240440d54030f10b43d07031418460040f82c107015906d81c614085521115404408541007895040014098801c0b01303ca1b0300c0c40d04500701440c0144c4d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 102670485 1250 102669235 102669247
    0xb0a0204031205031602062707030f05072303070b0f160506060a08070e0105120f12120105091e09010204121b0e07020607140d050f06030708030c0c0d0501140903 71
    0xf00c0040814891174502c060f10351800d0404100d2040c6034000303609104511000c00c0da05c140c2e2010301c140402940d0000c0c50b03001e16200c80c502603840707801d1762080364889e80440003905600800e80307a03241e1400100602030700c4464180006543c103508251f1030120300c0d9100740522001005102c81481100780580c004090311b00d0513108200304150243c1020a9940017400101711104010740a40d040d903408840e15481c200c0001003492500d50302c0b03200c88100f8841e41401d014040203420042c608010300c05100352241e80c0f15020303c4160541602c00c3c04a10103041040c8200740c6c105000903400c14070480015290950b40c1603121031407003024130190b07211500103203850b20500386403c80100600300b41c0c51620301444c02507030103515848010440d0043c844110348003289050281e08031041481c03000010081d9003000d00c09450000d200311115030292045040124010000205a41388074030f007034000f402d5111400d41808040c1c40c40c1241107602d9900da02c2c0f8242000564400544036441c400300442c1c60364 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 102671735 1250 102670485 102670501
    0x91e01060309020a0312050f130906050406150c0c0522050a090b0c070203030f03010e0a0b150901031505030102190f170406020a200a0b09070609030b0a020403120503 73
    0x101a8880014985045620301c01619012842401c03284c1101e40100c030185d124000741c416120700e00d1099400301d4001603003134041803051307500360903940c0040040001c542c6034001d0100303c558900941070b100304281144100c9138402c100d041d034068070600c01064010f95520200b5050341d90540c0d01101505400801500d00078148110707980300c1d02001c1d0034006c940160f241c00383c0098001e00f12000c10540002e1300340135034034100300b191030a80d401d000003980d031340c0e4968409850381015a454100c1034145441d034a280e14150b000380c1600d040c0000300c0792500414200540003410113040341001c2905118002400ea40c0a102820000d06118480100c01c00705140081c035100f55880d400f41032001d103450241d0290710320700f14a41e00130351001c130060b44c03402240e20580391003000525940c486440245410b02c803600100344118550b102e01d1288005440b500302c980c0d10307240d03940607400c0003824a00003000411a507040c051b400c5048460011715158a82d20f0300014000412030410103e400081441049 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 102672985 1250 102671735 102671791
    0xd09080c0c0301150e010605071406011401260a020a0e0301050109091a040b160507020a150908030c10110412080910020102030702100b040b09011206050f0c040e10030209 75
    0xb403012440c0071314006050844a41c0d01750340c180502002c102c00410004200107000b000840f40c0e00400003200c2c41136030354000361a03264100900c982c0c0081c4c0200300e0000c9101950511082903542c0b80317180301d0507554841880f4001d4000c42c40e43c104020304810240d086490038840c4c54042e042100020920204504040040c501c0000080c008054200104000300f1302c40100c0c00c1d00840c11900d02d184005180c1c1c81100c0c14040e171540607500ca142c05000240407107400f00c00c0104640103840d50241540d0392342c040c903180c0c099190b00e00341b641c02c038141ca440603410550141180c40c0c40410300a04081d00d42d1b45415440c1c1d11100c0441d04401e00049020180c80c14400c10240c50300c803440290720718030b01500001d48940d1465207000e800c030744a40344808107503125042072080400103002810950707540c48060045e00e5034010292011850038010600000c40d43c1180c6105015148800d0716183c1780030068220700304003d241529000403c2130110041e41c968001c10300810140c84000c00c0c1020042c203120304e0b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 102674235 1250 102672985 102673001
    0x90424021305011b0b04060c27030201020c10020703020603070c051605010e04020c0a06201809060a030201201911030c0418080c01061a13050607170d09080c0c0301 72
    0x8142444020390300040282c069261b00c55402100400e0f00804290251416119003590710035801c0c2171440c0e070500c3d4180c42407040c200e0307000340d085034200400d19041c010804110140000142c0180d40c040c005428000d0056170048281e14240e01076017a83c0d26181e00304260115002210940110200b048bda4050384904541c101150111300e06111040b045594201e083e0000b04540e03160080500da421000306d2040c052038450703003040e644103440061454402416103049100c4d03038042010a81504014030290281c0e0750603110080e8001d85141d05510065400300b42440c144540489400100b50718400d18552604c40c01415040b1200b4504041c2006840003005024a18121078064000101c4009000003600191020380d203003010600305000d05255000740401d418280b08080304404c08a0082032288a5a40366608454a80081000f0f070300c2904000b80007010315a044007070181421000b4010005462000140000d44d55100354194010520b011525040244403c0c050300f001c1c054061 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 102675485 1250 102674235 102674267
    0x8070303080601030c0f0e0a1e0f1a0f07060207020a061716021b030304120c030519080a050d0b0901030309080c0d020612070203040b0c01050714030609042402130501 73
    0x2c094020045c0003010070352a28010710401107d4a001d042545914501e10040d01e0044801f00818800d60b03411020700085104040c803881d03036508009032503204201a520f0030745c000034581d4580b0300300b1300e66072905400c084030650300c0a908200d014016a9500803503401080203840362030104200b60300110104000030000d40000a0441d44005c004c0e602242c404c0310302103400031070b520802c00440464614010740d0070030007030b00289403410002d006500c1964000c0720310403c1142ca40038041010840e11080d825802011f0b088140320001410b4058005070034880d004550014441e80c0340400030b042c5450a91041c1c000c509410310600005c03c041c46240d11500c1300713440544c640c40c0680d003c12114455441810195824040490706442c400c1c004ca034014032071050360350380f143c0841e403840f03000b08010303580d2030003044414040d01031400a11045e24400d0400800b60180c9075034949402500342450190b50000d40702e40d0711088040e60240c4060b00a000c0103141010301603081400240c080050315809803 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 102676735 1250 102675485 102675491
    0x7091e0e0c090a170f011e0c0c111e0603070c03080106030c0912060b030609010b04060501030b0906130b04020a050304020411030105210118050a020901061e0302070203030c0303010807030308060103 87
    0xb50395510390809001c00c684210a10f1880000210b10301c509040008042090079401c0074260309400018683e000300183d04200b0400c0140980390068a1003650138030010305c00214011103102c0c82c6807204500170700e01e10000d011705103a199440000c0d0103900c206c1d08000400c512592060915a01182181c00f5007403e00302086201d82c0b195003d05680d850340305104180644c84441c004000a0350000c201c0c0759406400c44050f42408a001c41c087d08548200354001e92170040001219131003405030409c0000c015203c40c0483e01d4007024022000401ca81090b120303038941e035640760151598402003140045640c1c8981d1039052500c10031042e00d09401003000c0400041c0014446030752401c1c0d40720308101440e1002ea010600b01520940542030f0304e21b407140c940d0341d10131011041c000049042c2041601c2200c00d013429a8881d4030a5413a4820214240723140c9860a04400000b401f035401002685e0001382100c0c10300740c0b08a461850360380700740c0003400a500540e808008140e0043c0071642c100909007024 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 102677985 1250 102676735 102676747
    0x411060306010c0803060d0c0611061e04031b050318030c06031620060705070506090106080705190911040806010909051b1c06020c160f030b07091e0e0c 67
    0xf8041c00c44410080c00c0030a00202160156a484034004140c2e0f40c031001c0402c8140da6801c000d000004000d846855501800d4002041c0f15140d135001d1910301301c0003205100c542c480d5241101c21013403091800500100608499000c64030801c05001d10502ca84c4c500107460b44020141410203000843d15406102c09006021510030f4a589071650401540303400010507a580d001c1d4a4140a02910394205008480521005661210080404078029400c81f042d544a02442508a5102c0d1041004903000450140b0040c40c00c04480c0b0180d98848d01071207140c41c0c031000c154044460389003501c400c114001804200c07803441400701500410321000d042040520a0315103a4640000c40c5e41d031081480c200c0b4100480f603a0f0301c07031b04200d450394102c4841450172807441d101d40290f00801548140e8407a1004072038880340c52503020800d46240c41034514200d451036890b000e0b0300c10040c084070107101d01c148001c200c07600003104400390f10764200c1f00c1c00e411500d020003a130304001d4080d04142a052003009030b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 102679235 1250 102677985 102677987
    0xf1709060a1d0705060702060f0a02100b031902040c2d080f010308040312030e0d03150f0b0d020a030207050d0201050a060e0903070209070e1008010f0f030c060305060102150906041106030601 84
    0x425070444c1c0303069030304135034814562000234514810094400c000100201c1c0c0c4801c0c1c07a600051030940d0814204041000c070a0500416075a080f0b00e0400191600c140203003080141002e030841c2d56070007640e042548101082401d03007a981c80d5100c00c038102c00c16100e90803124242d80018240c0d00b140d80145001e081d03505680300e61209129a02011300f20074034103e0050409407081c2c0c041a0946071400680703031130031a0090010064540118071040ba200c0201000c90560380151502c01104c6941020b2440d0009040342ca6010b908441076603820306a0070300490002c22000d01c40c030504618030745e00014151906640005c00c852042c1c00c0f05c04070322201810050540000021501c000340c045840c4c0e2115035603444c003100c201d413454040c980c04c040c0c514403800302c20341c05c8080141030307030010185650459205c00350150490f030740b0b20014280144440c400c20916000e07070f0003550004810310690304406003408048003080000d4036661810343c410010031040c811240f18000781154216502441c504090380 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 102680485 1250 102679235 102679243
    0x9050c040b09030304050406030f05060708090c04051503060103080418060b0702130f1109010314060315130b04080c0f0a0b070f030608190b0702010603050604030f1709060a1d 77
    0x200035015200048403101964100145d81c000d01c00104107000e40c1c3d4403807802c150040755104007201c0b144501030104026900412011b2b10980c1d051008240c0030f009942004080d081c00b4103c64a1020040d404481d036440a01030a4040c0d03000d03a0400b0365903890480c1100300c9a94142c0141c26079032624500b80000c4c0b0b000400c480c03e450301145c1035402a142441108020700c5008001ca42d200d1411100e981c0c19808007000d4030300584242c9040004101d58125a000400300b15099581608220080300080c90307180300d0301d50080090302820559125550710361115140984041c3c694200c00b0810402e181420403d11003181001006802d1504841d521241042005400388090200711403072804074074801d81c0100010b09140007164020250b1440c10700c0302007641842038480304110400940c0c800e005021301c100300c0e40d0150041074580e95944044a00400301c2c5079090401c008c0799040244140c02070300e080d0261421078003a06807420416699000c8851804150b1000007100ca030603415000c2c042 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 102681735 1250 102680485 102680489
    0x201020706030f290316051c03050706022101140a09020a02120d0903030c050c03030a0c051b0105061f021002030606070c090b040b0a180e01020d0e061009050c04 71
    0x400c0c0400d50840c0c2140f0200071349541840140c082d4a054a22800750703a0340b080b49007209009600741c403800041e00c0c8660b809405c40e40102d50b00400321000300c02100d00008110421113000303262450a00f903565484c038083c1d0340144a095240425145811800024151200d00520b08400c10140c8809444c006c5016010180b00310100564003040c055141c40c003c0c07207a20060044c11200702d84d00c200c41d1034070030f00030700c0c52041c20780000e454111002100360241040b2522030010310000c505540d51162030a020f0000405650104075041c0041e1440340d0742042802c00c1d43e000000007103114a002001c2c000340380348001e0364504181c010340081106030307004244410000300c0c4504c05643c940e5028041a05803159401c0207001000009001481610a87c03122441c1041214144180d1100e682000035002043c00350000341d03d029104001101b6056011501c002c18104c0054107041440ca040800c07120720720001c4070180c000350b0400c6119503c200c00349014181c583d800300301e1820030480b00c0d0a14000c42c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 102682985 1250 102681735 102681737
    0x1050403050a1211191203020a090b09060f0301090504060c0e0a030209060a080604050303090c030c090106200d020c1305070f181e03060e06090c0d080408030403060e0d0c0201020706 80
    0x200483e680000d12070140c5400110f000400c0355030b0b40c99110007512408081c0300060f524600b2040d40042c056120380200c8400d040d644e514462610304224606131142d10146005a00c94010414072981a4426000d58020b14040000007120304e05820400c003514010000390b001c02040301b000c1220741d5562000d9400390f80e0191640383c0030366600c501185210b01681c0040b9111b1081008100410100000651040d131503003064555500d8148141030b034607000b204110340e1258141e801481003600c144240c2c010301040b060301d0207000d61a03c3c171883c1010030090320000182c1221880e203009042001c1c40031005484900c00304140d19200000414000748400880d00304001c141e8660000d150000a0f48040d000c030304002240c00182d80c2c400304001c078046c4003c44038282000c0141405c900c0101d0b84a00c211041005000a44201001c02c10281903500e801c8500d480c0a020102d40808100050005180728010010707284200c041114a04985c04c40c0714030811101c2c040c0400140d07400300b2404215103203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 102684235 1250 102682985 102683003
    0x40c0311030a0b15030f0303040c06090e0603030a0e0d060e01020414010e0603072706030606112109130501090b0910081002030a0b0415030c06020d0503010515040302060a050c060601050403050a 85
    0x144c200080c2c1043d0b0460221120b03440040144410b2107000341c02e1408440890300d4103980e065030340300c500128070300c01c9903d203600d50410f0080e065001d02400034550b04520003845003840700d031a036407a070003220a00185804269070110f0103000360608080943c00d06802400c002030350550640000300540320080141081040b40401005203440c80d010b05545030b045902400e40e0740781c9904005000b0802032040f03c0c0004e00190700c002d440040403d0000000c50f03225019890345501900840c0e0030340c064600642c010703590080e450707030040352445550f000e480c4000b070200d1034440c0c0c001003102018028003521101d181a40303081000c1800040c03a185445102c200150b200c0c7e90f540d4202d80204568081d064005050100d880007440f201c00c84042928440d00903a030001e03071155001c83c4d8840b24030f0140ca011030402c000501081ca801c040801d0082d00400e2031304d152a0b260f0740030554580000076000c0c046078000c640030300a4002400fa0b607900c41c0342031a18074145071641d224569154a0200040c00081c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 102685485 1250 102684235 102684271
    0x30f0f0903031c020d0b060304030c030309140f01020c0705061207030507030f0603050102030603100605010e06070f0606180e0307080409051005040501171009020f12070e040c0311030a0b 82
    0x40a1007510b903005412010441c0500d60302c550344010354404070385c3d8030781c41d850b200c071a41442c90a00186c901031b680507503c07507040700d1040d60150010079400c8015150091810300d0b001c0d410008018942d0305880e400009600c42c510400e40c81c0c07401c10a80c2120b40b01f150244143c19150106500003588451140390102e80ba03240c941c000d81c01000d007080c902448a00382301020080c000c05400442c0a01c2041d4115aa0542201c030844111090307806090b001501684c00030b031140c54070001511120b0300805084440307080c5656280b00700d4060b54400084800894680f410020051050403502e00a0002452400a107580c813086c01e403160f4025404200c2d0744030045080c0c05400855480504009081040207503150810f0700062000b00d0f051101a1207411400c04801d00140101c610b02640900300c1c07103c08403424208103c200c401a58405c0603c102c03100000d850b46400782c290300031402040d0395200c0c0343c03c41c03c1c249110ba18207103a4070700980c400c001e0800082e400d1103082d54130015091440140c46 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 102686735 1250 102685485 102685489
    0x10f091a25030e030f03070f21021c06080a141f020c0c190f090209100309051c050304020114090a03020609030f0111040801050601091508040309120b090c0102030f0f09 74
    0x40000c0840c03c1c2c0c4404680c040140440000846c006d098a8442c00102d142811040701c0748200c4480325030a039219000c010100d4031242c0c006c2c00c0c500b030f40305000c0c94800000c7c5100504441071039008001c16400340c1c09600a01481142c8003401d090584040d2100602940780c0c070344a81076031010209016400110001c0c0e0322030901c01c0e201038082c024460300c446120003014400303029860281c104583d100c8600080c11004030b108075001980302805940071003500c0003003540100b0111405607520301a5901314140c104402e2844d00d56828a511440d07103905141c0001484141131040b0403003440400c0214031415543c0c0980b1000b2654115141d0b45d59802003c0841e090600e000c034407800960800c4090024904998061304c155022840204220350f034840045494203070910030450f0030f00c150b800d0280c2091040e414a503019001e82004524030f035441d0003564064101600c02c1d04d003c01100140000902d0500c580c01010310244021410710301c0301c01c0e80400c1440b03200c008201213040040c110fa038503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 102687985 1250 102686735 102686741
    0xa0506010e150603070f0306080a050a02150f04090501060f0806030c101202120406271e08030405030307090906060906110f0303011e090203011404020318010f091a2503 74
    0x1502e00582035a4803400c1100004d8203066408015001180c2009000325041d8000114441c02c0754101008000012440d0203105040030000f12070401801c040001d1040d180216004000616001d100001d042d03150000040810360780f012201e082081d914240b207002e41d00090140305812044905010744042c4072410340d041ca801c80501d034500c038000b286c40c1940c03011001105108601900080c000c1810111104007044000540e00d01c01011800c21680492a6084180420000f800c5002090361890300c3d2041c403130300300b00d40840b0b15500000400601c139600104003402000740060600000c0e04081e005490315480d0b02580e410042140c50041c940301e010030909010002c0003041d40e40c1c9585404480e0913100780c3c00f4030b469206e025943c0000d42d0240c54400c580c1203880c88012801270f00741c48030400c0013a50006c0d040960000300000c4032a1428420301c680401071400601c00143e0450510f040702e28103c003000500c041d10003405c200a0141090048038502403598005694100170000082e0b000b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 102689235 1250 102687985 102688021
    0x40e0420100306030c050409050303131707060c031508030405040b0a1e0602060c2502060c060a020c0714090703050403020a050f06010e09010c09050105131a04090b030a0506010e 78
    0x11020905950010740350300359100c00c003500d0040700b10640d02078a91082c0015146a82001807140c0e108000103101c54207503d80f2446024484d41550721840e80c1c18001810a8102041c2078588030f655821601902d60075110b80001e807642c03c01c00215041c902182143c590203603110f080e0041ea1501102c090307940c0c4000740c22010b02503030a031800c0384040c0c5a1200400808600a0101610841c0c1c0030640d03000080c02912079580000c520b0360055510306c001c071000300e4412001240c1080d01030000701c2d9000400c0c09001d2107005014001a1280d84807005c031482d0a030141c1c025000c102c003900400180d922181c2c85d20758424114180480c4684403840d0481c50b20340c498401a0031401b40160a0841e6100071030301604039800440f0301e42e025102c0c05255801c80e00c544204901090306810104501d50041000c0e1004140c03d40f48803104aa94884840358103c40070b00c1d001d08004009418402c0034511b00c40d02c0c610040950040c44004400c0d40c1c0c4545c0c45d0f5042c0146e21000c5201030024910080401010071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 102690485 1250 102689235 102689239
    0x40803060604050d0501020301031a100b1608160302120a0804140a080304120e010311030604150f0803040e0915040609060605060f0a020105061504060e030c0d0c080111040e0420 78
    0x1141340102d0a10500030740007800100c40340348000c41c0c5030040910003800c15024884040315500aa49040714560880d4019203088250f0403507400c1d900040b0b2080c00c090240c0040842200300000e04914000b801c0c0881107500e041104000c1c40341048480c2c1c000c0305503610551044640780c03407840b40c403811441e00091b013100814003e000010403007044456030400584406603100c503902100824019400d0750b09141c280841c0d40018400100c042c5440c3e00250954110715449041d826240c2c80118290003440d08210a41d0740000743c20410500400d122650001c8034102401c841190700f00032482c0040302a00242405842c1e0b00c0c080180141030780100c1c002c1c0b80091120b90307248814003c28101d034200c0c516110142d481c280004502e420040c80032458842c1d41718406280a04020381a90b41c0c5405c091001e405100303520000d803440e01c66070003410240c0e01401807484081c5c64040c0650035a601c0c2c04614498020500007000b1104134a00010340040d0301000d007103070400516109814516071000525 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 102691735 1250 102690485 102690499
    0x1109090705040306050c1207050d0605100216090c0203030403230d0905100603051e010902090a150b070f0209150a090501050310050c0a0f11030c030d0c020a02010804080306060405 79
    0x821210780040060084a1040c9400e2005540d040000c0405004080d102070700c240000c1c0000300405d21a00040020382101c650001e0810307200c60124440d1700c9460440c07000b40e400b00e0000001c40c1918030300300000b030054101c184502c0b07200c008000e40b6400040c10003002d000c084140440d0500700088144005084991140e0311411916140000751464a00c143d0303d81c02613808034007042001d8020002607a4110006082108a0201c1100d050710000c401c00019541d034051000107968130340440b40900c901003408a0072600c1720195510354000c40d80400c40c800d00801481001504c401c801d100203980403554010310741d0710508400c0d4082150140241c1c46a0040340200340c04a03070350b01603030503684107400301c40e215552400140211401503451685400051107641501445078244008086051426581c482241c03181e162071600101e0407480f2940011400c161881c070548500440322000c4c0c4002c3c000b140c0c039500042c002c910080d102628410340003000420a0b22040201c42c0104005803c0c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 102692985 1250 102691735 102691741
    0x50705030313140105060307030b0c04030c080a12020a0c180209030a120906020d09030803040303020418020909160f2a0f11090105061c18120e0102060c0d110909 71
    0x10303100c800003640100d03581c3d41c5644607000e02140503c102442194054020640e1509603212001c4404009002500e4000704101c08000220007891000041140c9001042c560703031645080c0c03035041106036045085601001c0c8807008100380b0500d550480e5a4403405050043d400d2000401130300c01c000c070407038252199102c03013002c110030900d07861108030086d40c44065503922900200c1c0c90b021800c00d0311340000d080500500116000c00021500f00c1c0c8a818014501a6680c0000c00b124403c0c00048040d50ba0203d10103189052900c0ca0a6100e414003c40401040c150840689140048014101001a099840c0410541140c662481c1401c0410140790001051030101d10300742c07520a0403102000700300080062414541c049134160f4000500741400c11011021614107503400502a120840d20703610891011070b2007844011400d809201c0342180400c900b840070303121052480c0b5a504540c410401c1016182213082600e9401e8603194000c5050300481c464583c40e0701843ca5000e03482400d880034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 102694235 1250 102692985 102693001
    0xe0a06210b1918060f150b090a15050d0c0212160606081c110c0315072a060b0108070504060c080c010e060702060c07050304060e01050c0d030b0f120a0f030507050303 73
    0x102d44013403080806000f20303243c0c1c0c1d01d003000307503210b601c0140103055041005200010111001d454546805060f140e0100d54810012075856591030501d400714100041c500b1074040e0500821005c41c0550000b8a55581e2686021046209100b05003601000c20405030080222603049400108207074000c450155078201600b05924140c0807a503004142112002c41ca10180410030780b10900c1e0041c0601444051000701c1d03403002c0001406c500400c40204652181c1c20749442801084560740001080f4801c0140703040300c100e502c5c01180d0b0341401200c1e4104000c041d4070108840a5900d50703d0301000c0240980341c14040c5005100e4200f0700b07942840d840060052000800034824180780c0c0c200d9143d41c98421048006200ba130300301819a80040105000f603c2c015008180e6034103061514925001c190600542441860701c1e4040003c6c2d100da03d046031610302221651403184040b00d010710707400c0c0c50040302c5590b8035101400030980c00e074907600c3c2d17070916001d1016a4400c07074009058aa0f01d14100c0e030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 102695485 1250 102694235 102694271
    0x903010c030c02010e0105090a0609080d110703031413110a090504060218190b0a0504030f0b060f1230030f01031a010e0f040602130e0a06210b19 64
    0x101c4200190305c3d083d0400640181401010f0203640090003802d66203c00d070701d540018240c101e800b82c40c003000070403403200c05511902c1aa80e005942000040d03d4a00c18035008085d6224990900c07030458440b4140300e80c0006a010300407006134404007400c1d070b1121800229252080682c0011a01450710003003009002040d001861b54136024903a8034010300301c100070841c66841034160600d59107120350043c09101502801000390300820b003052401c10b030307032583d03a55840c64020508940d02c20b000c00611207103040424080700480070485000035001046030029a607101c0c000904100b07804c00e00313a20000310900d48020488900600801a03491610600d401035441e4203100407a82030050003045020720240024040c140c42d0165404080d40d11203447d0074204c004082c00940d81a54200248105c43d0103258025000f403100b98007542c06498082200411074a1544c001c0b150102400d02e881c040e8071640c1005800503501040810590b15100400146c1400d00c1d1700180c92549401040c64038060f080c2c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 102696735 1250 102695485 102695501
    0x612010e0604020c030f031302121f1b120902090108060114030c0108060f0a0e1905010801020c03040302010c110405040602190903050c01050705011439071104020903010c03 76
    0x1885030076100c42082c48102d104000c3c280d495900180210034080c018800107607044000081000442142a000100280d03424903028007203503c02071a02c5403030100c8a001e0a03030b601c040c110401880325190300020308044240041c03810401000003008080c182c903402000d84c5034001d40407400960311130803c0341c0e83c1c0e1000e01405900e4007440411000c0c40c80c3c0003503c02680c1c2411380d29000d045d11268188007403140381e01141a840b0040d0f44000c50120a15072403c1e204255469600c50700300724000041c0e04455044c1c1140355203900420200c01d130f00c80000304403000c0f80d0782880e240704c0c0741140d41004640d9408400c941d5510505280500c0180801a0080c000782080702b01807400320b17184100140d60041103848018140e0f048440c2c0c2e203601e58012030107400400d0241002160070014551070703208000d402c841460341c90100c5445901c000008644241c0520080c3c3d1a0341007200e100e0b000540c1500840000415100c070038405002d40b6240c940560305008001f400030301036140241406400382c450301c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 102697841 1106 102696735 102696749
    0x61b04050603042402130807030f17040807090203100501030203101a0706021b0c0907120903030e0109050105060111030a0804060b040905060108030a080117030d0b01030b061201 78
    0x120614130384ca03040f10080186c0e1490810801014444140c000f4241c1d0b40c0000f10600009a81d84044030103160081f41c0c3c05842c0c01d05401040c41e1f440b450b00b006c0e40c00c1c00740c0200041d102d14942c0241d40241c07050400f0032901e82d1501c0046040f40000c03210102100000c1c0e10810900400003404c1c0e0070520b201c47c07064070b400c0c000d440341c0d0182d80c000c561080c2e21440028502a0740d240c01d00808410440c11141590b090800e4440200300019045c003007200d080d0340e5038170b036400c0501079170000004000c050028030040642c1e0600f2802080101c8501d40440c201610032000c030301000c0304948030380d07000e52039a5004e80c8840e15600010a6626400c0e45c0007a91040500c0101d002005510300070325140340150741d0307200d908000030308a40c41a4440d001c0b1204a0104072485040072044d41e07589461081e00080051100740103c003c0d1891050858100000046400410f510a413401d0f05982c50 = true := by decide +kernel

theorem cover : BRFrame.Cov 102517985 102697841 := by
  have h0 := BRFrame.cov_init 102517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 102517985 ≤ n) (h2 : n < 102697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
