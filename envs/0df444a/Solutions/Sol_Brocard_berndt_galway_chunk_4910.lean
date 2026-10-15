-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4910
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:07:52.210609+00:00
-- url     : https://prove2.me/submissions/543f8960-e1c0-432f-8495-16bd7c2ebdbe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 882913669 ≤ n < 883093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 882914919 1250 882913669 882913699
    0x300c1101090b0a1206030b070228050303010611150c09090a0510120228050a17060610111005090c042901140c06100e060f040e0708030304140c 63
    0x180440d10702400f98589090502d201c0c2c0c0b0350700014202504000c00410009003030000036a03001580100c080140e1140002e01c050340c01d65a404010111402000b94109000400c0980c0c003819050401050880682e45103041c2c000d036038240b242c0112030440c0c40010129100d0540d007041c801c8039a02086c250420042424440d410418410381c9115217600200211001b404548550178040710140300076a03101303a10008000010080c0c0c0083c001e043c0281800d217000903480031400c1c0c0312300381d402e035100207421240ca88500b4480c0c1060203403064030a1000c552884c5800c042c08009211010983c0080040d142c1007003800c407410312514509152240307003031000d4480c0b00f005508420540046100c286040201c8160060f0303444000005495501d050108e80e0010503030000c20402d216031601c1240b1004651107040c160341204060301c3c140c0e000401481c20340c1d4181415441702194071840800c45580507650340c0c0940c9160710885003292000200540c0c2510203108010781c98551008903400140515a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 882916169 1250 882914919 882914939
    0x150103120809120a02070f0e07032007020603060406180b010e0109060818120412063b01060b180f031f0209130c1116080a300c110109 59
    0x2204880050303d10004007103080c070740200940c0d40180724200042d459150b0340d21a8014000c0101c0b820380110741850811501c3e01c400c0e4121160401c51410706078145031035502848a680c200800b41d80e0800d58031035011642c1812850002e007038800010011030a4541280010701da5228550034605000c2c0b01d01062100d00e8000e03650a034000f00141d44106030032001711120303107469460440c2e500b880b07000080105041010100800545000d84028000100c042e9003d42e021044441a001c10110714180c1411001203030740e03403028980c0b40000100301d082c0c0310300b071910035544800c690600c400f0200300c62060318200403c48140860045000e070141d084042ca00c68500e48000e01814141940011142c0c0c040d0748460701c865010b44515000c026110b170030b44c0040c01c00300d104094408948541d2020401101d0040c1c101010f5400ba1070181014036600d40e40c201d442c00a1440c90040c000c520000c4100c00b0410500348016a6100d40e01c5089500f200c2c10070b00c1d20100304207807160400c034604106010b403103d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 882917419 1250 882916169 882916183
    0x10f1d06040c09051314100f0221040614101a040e07030b0d0204061e0f0302060316032304051506010e1201110c1c0507020607030f180b04091119050f0705150103120809 74
    0x808ac2c0300142e40e0341c0d5250800090000410804650a220b0300b802038681144c0e4155040c2c44420300c0351905500c00c003140c1c1225010740e12420100501900018501c6071094110800c4548040c3c0307a01c41d262450350028040c4d82e840e402001d200300009070100c01c00b0040f104102c00604214261200d59030958011601a10006000c00c03c50310009481380c00092003540b1031001d0145052a440c03101384400030411540400365401c1d1880d22a4a440041e408211038010b400b40c01d050f1503c211003d4181e09010115510025503110340d50780c0d1070b0070b5a4078a100ca004084031840900503009890105c2c0780400c40c0b0717041e18080d104004090140c10010f031594001c0300c05e09138150601506c0091800700c2126000410074103590b410003034110004001424402410a490191406111403c204a500d0b8668082c0d20302241c1e00101050b20300d41e455001c0e000408074514007a4448d03141c10280e81381c491502c000038040c001306030442e030010403d111407821000000a214901280300307040640040c0d0ba6030710 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 882918669 1250 882917419 882917467
    0x100207170304020a0914190e060402040c11010e03280c080d020c0a031713050a06050606070c0b03070305011a1801030e010f1d06040c09051314100f02 66
    0x22000010074250744d0744031052001031200800510540c648183e00d0501c041e01a01c0c0813044840640682c0c6070000f16018840044841d18018205c40d1b45503000c04c00030b0f02c08181000103010000da1110710111080c0904200c1e140800010350703035042000c41c2e0440c5441e24440030300180c01d0135006813840e65402001d05548a801c096201e481c3c0c001204540e0007446031502880c080e10500b20100105a0032248030b8040201d5003402854640d60880710518050011038001c05a40040103030800080903907006540000717025041d1420002240c0d1240d0004c45c0750b4001c40090034020041007101039042c000c0c0d602502c00260f80c45200f21508000b1020f078044da00420541c00c00c40003074260b0b96403107684a24a0001d10b14000c5c01582c01203505807005000d42001e00310122640d400310412100e001a071203001e01c0c3c0c02001c9904262500f114040189000f5210f41c5494161441c1400070a481100101c2140c425102030700300c3c22a48001d20b01240c0e22618403d00e0a4014800851303452265414410103030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 882919919 1250 882918669 882918713
    0x6120c060f0c060c031e0930111908120105030a200f09100303030b030d08040b090a06050a0507022b05090f1309030f02031e071a0a020a02100207 64
    0x4c605918150b000e40100c0c6030300f0a848450201d440405041c64121603103480c02408808044440c006441c02c88000345114040b05007110461010007a1085400900e0b0302c18960030b0341c8803110202010f070700d07040010200340d0b00100081140d10707244805000c2180140012001080d182103103075036004407034005081998410703c2d80d840c0078030240c8071465180340c20038004061028071702d0614040c20441c5290301054000900c0c100e10b50406e03040c0042c1d01c040505142d11a54401e41d62581d8441202000900500480c0500744054000440a028581c00b4000c1038401207036501e00341600074907140d029403440e81c0c2d025076401d007003031406400404e10020020300c0c038025980c6e410a50201310050840b001c995002401d07902c100840c3c00e030b06d61112008600c00c2d580e03211010900c2004990780e01407407042040790903882844a24020304100140196032081d072a9451110046003032080d0203a04862040600d40c0010700705000642c14004400c118414010450400e865600c441d220300a80d084600710719 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 882921169 1250 882919919 882919931
    0x203090c1f1707032c1011040b0304030203040b07080712023007140c0120060a0c031e050106080c0a0503190902030d0504030b060f1008060402090406120c060f0c06 72
    0x240d2081d0088455888010110804400002d00c45500301c200d14001d140b55000f0080e580a5609080c01500107550aa0847c68102414011032901c16400a0300440a520041000040740d184040140c0106c6000303500071034507801d240c00c01380c94200c0e00d14a44421074102699024050543c50458100c01c21038a410380300c11422a050501e00303108202026282e03c14045021103010000600b80400704400c0e690360406140c5005800c012028040d0300050b030303400c036100050442c0740561000d60040c1103458041280c00b0581242c005115080580144180d180c40051041e07a401032041d90b00700850101561a00b20300f094018030f03d000151214240031001e40c04003280d82c3c0107030001e6060980080036505c191001c07003406805079009110440b1603144650002e40c1d1490724081140f2005006801080902c100340310454003140010001548a903003070051780c0a9880d54400c441c00f42115060200b00c4a03094200b01003080d075550f1001041145400340190000d40c000021441e480e0710210100e60 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 882922419 1250 882921169 882921181
    0x1d2a030a0c09050d0b18070602070902090a0515030f0105120703031803051c09120f0201030b130c03021c0203091f020408011a240301060c0c090203090c1f17 69
    0x1650340c03e502840d802035212507168184044010350b640518411a001c200a0b034451104988843c128402c0c94096004900f04004240c8650018901044000c3c80265059150790000300718800e41c4081c401100d81c040100270750050804601d0303015040803544140b032040c1d0100000c0e901c84039800001c04020b0441640c41d28501c1840030100a140e00c88180c03000c140f01000c0c454085103080b20581d0000b18141000030748100013000d10000c164105080221509403a00150080c0448540035a00701484a03e08a0500824444c0800005030741c0d401681d90042c2e000752500301c0094140c080f0300e03144108140040720000240c0c1d942d001428100c400b9100c0c0704000d80c0d000070300031a0300c205445e50800080320106041d00d414481c440d030f030855540050800d0003400c13a2a01409010f000728034001000103220141c081c0c0f661410b900e11544160484603200e12a460a0380c0040e280007a15034040300c4414020725006102c1c20281017400c1c0c3c2089014904800249813410328615605850081004650 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 882923669 1250 882922419 882922427
    0x302040f05100b0d1b030e1501080d03020a051624020f0403030305091501030606170319030e03210604060806070f080a1404050601050406140a0314071d2a030a0c 71
    0x105e44421031141d04e907910488001401900342c1c07803803203801030141012244204e103003102380305d040c1e84080d0018603401c046a1020750003513001c40071b5981404400d02500c010440600d0311801d02c83e05c2079481441c4030210b40c60307820100c00703080010500e150040c0042c05904001344203803000c40390546404549901c402c03016505150500d14100d00440d442d0340040180000d40e0411412100c18142c1d030003003504030070802500d17401a00100c01c2c0c403450700e80180e209c441c440d03040703000303942c2d505411740b0300d02908820303100094240d0400381c14490f1684001c020a510b0030b071083c503000340300d410040c125a01e00414020002c0114014210502024101144100d081c5a00099118007860704881c8070741454100030750381c0c01d42445413a2150303080007400714070025450451545036074041e01030210300e81140c0d20440000f200e03083d071500d02c2c40b9440c000100b14060a0a0b1491801c4641b0800c006082c820141c100c40141010903c0d407401318a4804009107c800003120f91082e03e6140004030500403a07400c071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 882924919 1250 882923669 882923681
    0x50708070303060e0a02071109063a1401060812030a090f020604031a070905030a0201050c420f0402040e0c03030a110609010c05030f19020f040302040f05100b0d 71
    0x1c00518601c3c0800c10340d0841130b07005190150051141000d500201020009402703021265a90010307a441402c8094110000d008108409012101038206c40c0f041109003240c2d41e4010199106010f005000c1c1c4407240a10504010b040d484001e001070f0011000c168945200141051003026070750550710b8248484810305e048a103070f005004035515580d0741001404004440c92405111341c424000c10342440c000c05807401183c00c09006485031030700907001503607540c100c802c1d80354a900868100e501d4404440402005100d8603030700c0d406a1114561040c03111044540798080012101c509204810001500342030307003c6c0d0304890208920040300070103030506104061460f0036101c042600714103290070104003100120b45104070340055031001000d03826a1018009900826020004101100b08070404507510402001021945881150040c2c080380d1102c00c2c140c020010120b014011494030b0700400c030000c00d40030800c0c412814420315200600d2030610a5040541c40014103121001c0700e90864 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 882926169 1250 882924919 882924929
    0x3070f030f09081608010b0a030507060e01110105010303080108060c0703021b0627131a0910080f0309090a0506091801150f05090105010c03050a03050a320a02040605070807030306 79
    0xc4c0d01c14050301144e90482442034098040302c1e50074009105035500742444407a0450b40c00074001e140c074520303000c000c0c0d40481045040c03a04020050748044080c003000d02580b4003d5100ba0f0f41c03194658074040485041c2103014196102c4010704100400200350300050440005940e4903000000c000c6450002e00c02d4030840548440d42c8041410381d80604c4d480303000140c50b2080954134603d03c0c01100042c101122101100441c030078902c0c2c12840841d09104031059070118404498000003070b2245a0360b46826800c00c9990043d40c03002402e100d15040049045810001d1424144a14107181000130850709000344003008250911014a1880f00e094000c0b00c2c0980851300043d4525031a400025648140c60050034007810340e0074000500342d445208484412605070760766506220f1500f01c201e01415001d040030004030307140c1c2081000140c442550348408a040031421092100800c0305404402004050a81d00c40c4188810040303560004111a05280c3c040390075a900d0305a8039042d07008001c95005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 882927419 1250 882926169 882926173
    0xa0519090302040e0d020c030c060d021308030c0a03030c0e0d0b0705130806041109060d030e030a08030f041a10090504150c09030b0c0703120902030c04020f13050303070f030f0908 79
    0x10013403628400308124040c1d9110790f0130789085083c400c003403540d1607500186490f00710b0070401821000f6426a400f400503100f0420141c004d4941d6010f8581c07039a0090342d40c078609074010b402c840c1c080513094414200d41c0215403e0a41214410b50300040c100341d074814010b030a82c00d000340000c804c0c40c45801120030140c41504070888d81c684500500740e0750041120100c86400c1d030384400402a25003001c845210f110020111150111140e40440300074941503665034140c4150290500010b42c004080c501c2425403404604c010b18160a02c4011558502c0540002d9565801480b100042013000d0400f41c460444c4007090710b0f11030345400c8488100380318804000900d0510900f441607800344a400840780a9006c5108580743e01c8002103035881030900003004503a8403404902400c22a80060700e010f4001400e0f034200c03050910101342643c1c400c0ca805290100e0004480103e8800b00141c4005400c05038001c5060070b03056034800d140040030300405000c6c0441004c25450143c4030700c0b4040050501042 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 882928669 1250 882927419 882927431
    0x804020409140d141207110a021804210801050d0c030506010605070c08031207110309032b020a02090403030905160905041106130b09190b0d060b0a051909030204 71
    0x40c60320f846481c10040380c40019100a034143c102211601926030380b45650703200713044507190800140c4180c4032100c644081e600506030800003690b514020040c1c142d820385a00401d500c6e2a2401c80f281d40222100b441301e5264001c0d00c8034450703620542d010f040d22001c0c3c4076015844c555041840c240e040c00e9000400c070740300740c00010580c540d10901600d6800e10030030f407008a10f604d94100315200e00a00e0a404600e008581c00070b0380c03403440744002c0500c44000d48142d903d48030700d41001c2130a0800030748a0400c40c84111000101c0c25200c60000100100f0b00e20241c1f06407143d960000d500442c01400103010592240314410a100c030500004882840b40d403956000c050307569030035001920301120156020400300003032103100d007800c034210b60110552604c80d44001e07043c04001d003916086a50031380d81191035030601034410015103070150094040751810945524800c5803060544070b99030050b40c0402d4042c0310002c0143e03081015500c2c5c4108070440c0040303610041c08200e407500c0c2ea551001c0d5009040070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 882929919 1250 882928669 882928703
    0xf0302180415030303231303120c02160b0a0206010b0318061504050a05011203030e1207060b0f060a122f0702030f160b090a09061707050a14010804020409 68
    0x101c07940b01124072070340301804001505100000c090f005043d07010340c000c104500148100c80010500380c500e0340309042158011104001e0f007011a0044100000036a21428030300c00c042c80355018010003020035100f8940b4000c04203000946401040c82201c0c070550b03020021510140b070000c1d54182403e2854100c1d50240390243c07051603d07080c41d00245001e2454030000c111044058042e56043e40d903140d80b000040f0450369411401404070f5042107125000d128aa41c90f00b50b10076005084050003035a001c191004000304100100090a2090303126400c04c1010140082d04883c05460548240c03000148a85516007110344500541d158150868059190561010751a8018006c0c2500030742c22104014a50304070f056030b820541800584001c0c24100811940b4490001401e8408000d4010040c8990702c8100c1011b0354483e810154051094440002079004100416001000e01700c0d61090010b10b8011104c60401013442ca0700d04100d600000035040d91600d40203064940c1c1d100d901454001410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 882931169 1250 882929919 882929951
    0x41202040b0402032707030807030e03010e120a111912020111070606091505090c0a090e090601060f0e010c08030c07021306050a0b210615030a1b020d0f03021804 71
    0x22412106030700c17448032403c41c4028001515606690788000b04a191001c1501c3c00c2d20750f015542c480c6580766494490700c10b2456418800301880b440200c0c5480d0300d5010401014104000e2880c00080030703802580d01002e000c1750100c82d003580e541c001c6007800c1807125842089000d400114005540340c4000a5580d080010560202c012234904007010043d002802e540410340a44c0343c1300f400d50208050000c00e1440402c40010420000c25061500031250b41b0320300e400c0b415034102c403500038503049640100202c540003402ea01c588075440c9850081d001c80800040d0100000b1140640660720100003e6060004602115849500246283d0096401241c4040a070189014440c094941000000703100700c00703a0300b1349041d0b80402d00903141d03c0c20b48a9000301018002455180c0c0315810740414280c0a02c2c1000541c054862404c0100f00034880307800032230300089204014001c55200c01c41ca4541c0316400752551502019034030300543d07200381e0070307482d10075241000303c01c82e034014a0000948030380030030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 882932419 1250 882931169 882931201
    0x230f090a05011803020105031003051b0108010f0b040b030a0f0509010e161404020901050403080a03020d1407080f09010609020a0206011a071a0a02161124041202040b040203 76
    0x1003260240c0415072600c0044807000f407945001000120303400401c0c00150300903406160301509200c4040000c50740c0703071101c902d402501e00c0c8030302862001e0903810300c0d9968000015405031510744840318401e854400b0780c0d0b83c0c80c8211f01c1894100300000c40802c0b9210341e59003002c140208041d07818400c07400c104000d24000d02078142d008003984902c00c112201c1d103051180400866400101403400305984030f05000103036202840e424100402044040000341c07800001e84000c1105031b60061726940707503c120711b08aa4220039100401070000b400c020100d175010400d258808680e01040f82c2d142c542240b0140905210340080b0b16240c0041015502e990340002c156041710a1581103000d0f054130710601d4000c600c11a0400351425241500c80c46044a4940bc40354100d60b50101c01860700d0440c070f0103a01c0c10f0f520748404a42c00c4203c2c95110301c251403d98443d0301da202c4020030020005607402c0700e040c2248123502c0b610044a407070f000d840c000d40d600c0742e0000b400310001500a65807440c10080180781c0b004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 882933669 1250 882932419 882932437
    0x4020a030611310e13170702060307080a0509070b070201121d0102070b0a090503040b0a052701080601020d05160f02040603030f0206010603020903060121151d0a020306040201230f 79
    0x200c044000381051074804128054500600550203450054072070968100641c0c1462000c4a003c007c1c000045c0c03922401548500196600c3d080b030b50810004110580b20090052641907116200c01d0080f03642510441307031410350900f4482600703081203c640d80070b841076682032510202000403517613200e003040d0010001d06108204885255944000c17003821103030a814083e209078402c0c072040c4908025440107090342e603a142001d074109145601a020b02c00c00510700221021054036403030905580284040b5000302c424005042003810785100100940540000b4200041b40d0208000030b01640740265812a83c020b0024403400d500c03424041d044007004000180144604400024114424404d0314001c1c031004010b06502e9207051054400c45445100d124440491f80d1025800505a8400040211009031010036028200c4001c400e9200c40705100c2012508524202e00c01690041120381d0300c242e0900741411810ba0603080c2000070b2240c114500860314000030103c007a4400c00001d00300350b503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 882934919 1250 882933669 882933757
    0x706140d0b03163c03300203071104050411150706020316090812040e070e12010c0e0604051507050c0306040627080d05041b1d09010504020a030611 65
    0x40040d034214405148200045680656015130038000200100b890304020080380a5060480074580c070b080300518103181038038001d40e00014141040104a80708110035210032a4204100d1810361980243c04424880d014800d92000121945200700701080c1e440d003540080d011034880c0b801d41d550400210304039106601045001d840091400070019102901809800c2000c0c1420320b400030007003110030090300c04010b00840281241c5a5211501c1b1183c03500c01c080000700b1540c400d8500030b410113401c200d00900542c1c00300003c0c4401d44400403845a24000d00038103035590500b50411909111f0b00b00b103250303030502448060000707101c030340c1d00488a0003c80140720b03055141199606901c440c170f40344005050407018007024810360100d901070740d403250060800d0a800d2004901c0c08449607607075044441801315419968041c0f2a03117101165021903080000c00980c1411340010320660071510000b01040d8594420300880c0600d07001f0b40c1c40c2014131038100d01c100c1e4842ca01c81034400c0d041d541c0342c8100c2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 882936169 1250 882934919 882934979
    0x905030709060506071e140102181c03080405033001080a030c020f130501062304060207031e24140105091308070b0906090706140d0b0316 61
    0x541d03080c03140c50100d9000a0a152810714203544181c5041d030b8440b490a40c1004802c0240003203010540740c2e40b4000303031001c00140d80d0381c0c01035110030503600349649070342c025913001d0640d038820216100316165164050401601d195203a25010b40b861154140b180b0320320300c99410002840c071802c10b0303255503a06602e4482441e13a881d40511565488801d00282c001288920004c0c00b5081001340a4000040034201c410b071580c0e02e01800081d5102a44640001008486da1208082c108411400d80120096069252a10f0044c0c020f43e6440c04c0c0c04040c1482180c030381c1c00b041c0d5945111203170038502d9200c090115210140d80324460368400f2641d11411050620740c20130344640180303120a05903940140480140c0e240c60309120301c07802c1c20728421039078140108040e10114071000c034424411440c1000902032450200600d0742042d129500c000f003400f403031304030142e42c4641d03807401d50720044541c040000700c3c450b52800084c5070403214030003041203242e16a004180c1a00c07a2084440e0981400104048 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 882937419 1250 882936169 882936179
    0x52b030e18060d140c18090f07030b27070303021501090513060c05090d0605070e0306010f050402091315140a060206012d060203040905070306081e030c0d09050307 72
    0x140008840d0503500442a4502c40000742105100400d914004c8088800500b440300c0400c540001c841301661210507000100103130301004201c040e05002c0908060a40c1e503145686200004102034070314043c261110f003211003002c2ca001e03114500b42503845c00301c030b40c03da03664200a500e42c0600c2c40700603031006041c000403a003462903004140c0940d0788655481d490654030f0315110010300034a1005400c200381001102c49582d1150321004606e4042c8000150300d080401c0d000c0c1682f40c06071240e5020f9013020004000a58080404070203c0d0000c1d9000341c2d944410320002a40442002c01da0f4003214030f03018241e02910b0300d80748944103592802d807181c0c61140030740d41000904015803042782e00580c800c03801030020918a100c401d0b580040d40d207198515402645000415003000d8100e800103a10100e0704002c462a140900d42d0402d0b0b1a040811a1314100305125494901c1d0803611282c03885c2d00446940140b00800803521214003490660701c0240c441c5c04010081b1a052051510a00c60b0360004a1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 882938669 1250 882937419 882937459
    0x70c09050610050702011101021308060f1f170705060c030c06280f090506040b04050105060616260c030c0f0616231216020c030304052b030e 62
    0x7000c280b403501c0b10b03030400840da4011a2101c00000c41081c282d5000c1c0701c084c44c04902d2b80090000b0380404009080280ba1412080091001c01080c41c0031003140040c0702d804898006844c0720a440c8041c3c0690160055400c2035440c0c4005d0f45d00c03158110000090340000c025002c00034200d980f07035000940702582c607020b10000c005420400c00005040004d026080f104e00150b000c0c00b50400b00003001702d80c015240d1102420b111040b01e041e00d107031000604000400c0820320034198410400c81d001ca00741840b0f030307031070f0000d1401400004005070380411001110f42403644c64004040c4c9080c0c21581e035034410320202078903600501800e40184c811a034800c50440c201140903803144010009003440702806150454000c15100644d1060001310501d050891114030000c0c00c080048060300032040c02d26041240403840d0390002001150081120300510f90382c040100c0d0b088900c21155180001c5490b4a2145401c1c01d80144000108029607090304150300f0500070442d5400440c1d2200b440350405016007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 882939919 1250 882938669 882938689
    0x3110102210901020a06060e0906010905101202011b140c012115030605011d0f04172109061b0406051c060806070804110102070803250503070c090506 66
    0x1000000700000d000351011420250821800520403540000324948440c0d0031504580c0003c10040403031010006450b000f0407107240105001a8100507038684048e608012680c0e07030240c041c410b0050348501040d07a1190301c59220b034031125210718100d20b80e1031410150030202e13a07400f802c9078021450380c4c550540c0141c44211800780107141601e01e001d04401170500804001c0350072a11110002d10201c00303c1c1051113554080c222011901c100081c441008040c0d144d00140300d24807c444000410000841400040b450b6449140000e611840c4c5e80080708004408102c1c4980100300700c078200508004002003507409802c11501c3c0d2000b03040000907500080c0702c1c2d4091070f40840d4041007c1d00310002124030344c904039100b025000410301e803a206941d050110684500000664081c140403d01c6080010001c043c00e09000800820b490311020640780e02400f2681d070300c1801301c90498041c21455060011107154841e0035295600880d161811171005240100a0000d28003800100d00b030070148051 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 882941169 1250 882939919 882939943
    0x309020916021e0d0e180f1015020309040504020111070e15040c1707120c05031806010305060103080d0f0f0c02010e010501051305062b0303050702070b03010306020a0e031c140f0306060f04051903110102 89
    0x44c2d40741016550034370000e00405402241000205102d101400c01e00b880307500e003d815001d6045402d41881614000034441d001d10651189240a55003584260480f266038402840a40218119030347c2000944d44600b80414813548c1508080d00341146590140086200b1a4025490044051000c0e640c503030351642400001c3c055800b078001800400c6501c8094261161904004184400c0c00c0c561b45040e1408101011080d40c1c031100700c20540c940a00803aa6401c2050008000c10740c9086d0014011240d803401c80c00d40c05580d880450142c0e2074010601001d0040480c950804070300071410302004003442e0700107400092801c4040ba02d0b191000c510701040b10300c03c1400f00e06507401c0d40c40e404000c0d8800d42d41481440030b50780000030b081d1003d2040c81c1c20b4030301c1403000000c01e01112102802031549107013a00c0b0110000c014042030303c144202525041102503071000c0e00c0720f002e548006454829504401d50141d80980302c0d00c490112103010000780d84c4641034107001e54030204010b9035101148000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 882942419 1250 882941169 882941173
    0xf020708040b030c0c16060206060d1106160f080417030a050315010c05060117011d0d0c02060c06241807050306010309020916021e0d0e180f101502 65
    0x20403404902402031500160480e407250700d000c1c03100740b140f80382c0760440c6d44880591b140c0c03100801c4056018444a03130321810541d1105c400c2a916510300c2e058142c0070540c21312403035011804512600ea200c420405141e0b00142d2250b59001a0904201540040c0705040ca4541e00b03e0349085040320220641d080c01c005a103440d421034445507404060f0002c43c0c0e0019040000ca49540000304404105407402030440c13803200c60040c0d0f5404070306425603a04442c1c0b03400e0461100d109040c80c140001301098845c003507185c41420341d40c80e48001540d40c030402c40841c107180304107c00e11201100c2c00c0703002e040c90745000003082960a1801c00380000c40075121209072179480a000090b01007030040c0c000310b920a0f0145800a0b514061760f0015031311040988035401c60341040c1c2d20030b20309550104420700c00b0308801e85061050452083e006582c0e03400402e11942001107400302e060094860010084151340101c0d444c0241d07103481041c2c048035480071035141c0c0308004000700020310212003a092100804043d80 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 882943669 1250 882942419 882942427
    0x2120714011e120b04020d0b100e1503070507051b24030f0c0903010204080a0606120209041502090a090209040f1505240c0312060a0605070b1008011505040f020708 72
    0x1400f6591002103440c600034807074039a000201240d40e11301c001c1540e521520302c0043c00102803418480c0f00407500710700800b40202e103002288a5501e480002c680300035007442850340da40d103466045410380994440148180300d80400d41c0c42c002512520695518030076186032414070350103011307944514100402984426000c01c007064802a00b058401d600c4801440c0452606889401081c2264010351200354150403140381001000b503e400f43d1300013443c0c650702002401469800007030344608040d00041120b09540441200d040c684d40540d8101c22006000300c42d0140d4603c14140694484014144030300c0c0b400240218501003440307244084102114848021030411040c01180c01004804c2100c900c901414039114140d40ca000f806402c0024019684824222111440b4940050103603441107100d100b0510406078403038199224550040001d643c203844e891003144010b080c54001401650038006203589a44c0e60f583e90800310388081d01e0130031560400c221100224010854000e0680b40108 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 882944919 1250 882943669 882943727
    0xd2102010c0503010e060f03030c0d08061009052707090302040c09080c041d070b0403290609070c05070305070f0b040b04030201030c3c031b0f05070212071401 70
    0x17000d0568802c00181160540c50800310010342380d90000c000c070403002d074084250f441c1c5180d8000320f07443d0448026581011030b040c0d0080081c00f50320f42030140500840322119044056900045c3d02e00040720141d00040c6d280c14040d100403d050300500091740070314181307004028164400e07010903003280c40860281071a030b4003002c200406000d58090f620100c24480302002d070401018000c0704020b0086402843d915465072504242c000c00411200402408454070381b0b01070b80480c40140c1e8400d604a070400d007159905036003500e01c007580c1500035081d0b100300e080101c00c02c0400102401640c490384400b0700f140e603548000c269140300758080d000398401c00b80000c10040d40a030b0401d03442040075080c2220076600115040e110060100411130b00c0c007903d00c40003080601c482c00341e42d42000e00c914050103481503881d04240d20329032000c07800b02005010840c140c41c1a11440c10340390155030007024203c41d800c1da10100c5a0b60b12a500503c9030383c00e00d07101d5401040d130084ac4400b51030074150980f52004d070816 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 882946169 1250 882944919 882944939
    0x21b0d03090536220503030a150b0703111b031002130e0903090414060f100e15040f0f030b071812320c0904050c0d2102010c050301 58
    0x300c80d00c04103c1004103078036034404070b5007508800c0204080d10707140b00c107150130000f50042c0144242000340c409916840c800200c0c00c0401100d0781700c88400300204100301040c0c1021403040039a80180a1144041464000c040d44000d00c09052a500d0003221504c200200085050900080f09a60b143d44182c20542c4a80c40c142c024089000007407061001040c1d48200032007a402040312000340c160000603000e0040c3c60240b00306040d07049404980d200300e00c0c10300041a290502c8808291060f00044c600750702c441d12490301d40910481c00340c03001e0b0021400358041e02464025000e50352541011242c0407820244640e6500700b26900701e1114000d40c2c8401c0c0c41603600c00700381c0032051406901c04d600490460560701e01e20400314440d0b0070b218030b8030310528400d200c1410720481807060040440c110030f0b001c900000780b05848090495108500c0d07116850700918011542000c6500991240c100030140a1444030030602d201443d00b580d00800d1001701c08030f08941e00007404038041241880148510401c0d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 882947419 1250 882946169 882946189
    0x9020310090518010c09180b060a0315030804060908060615032a1201080d030e0706030c0e150c19030203030a0e0a0609080904060834090c021b0d030905 67
    0x280c0039003040f100003c10707415800d40b1610481ca03404540c0b42c0c0c508001c10341d02c0c801c02c90400012140100071a031034000000b40c080c854140c0c60010540c5031104100c420710300031050b000035548131140caa900d40c0d4032076020f4661039a40c03290388000d00505001a890303041030070036038000c940b0301c20282d803469403440e084500c040106840358610807a078004003903c1c150b5480c0100b01410000c140010250303d0b00d6421441c10062955190415040181104050300c00041281c02c0c1c03503181c10045010100740074211111241151000e03800071400390320441c02d02c2550010305804a80700c00ba5800c0d140f800701e074ad8140c4040380c900140140c0c01000003485014641d030014a480c0c0790001540c0d81150340361640016140300040030b48204000060500301850648280c0c00105810409840c0c00604602c00e00c5201080c122841840c4e509a403040c0040155040401c01829080408210a40140c00e0003965007406528034004200403501e24084c0740392044041041a5144c0d644001c040e0500c4180180000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 882948669 1250 882947419 882947431
    0x2160b07020307060c170a121b0207030b0901150909060b0105030c04210803041208071103040311010e0a170c01080f04031d0d031d040203010e280608100501090203100905 75
    0x400c0321b840380e9a6100c80080000c000c143d5100c1a8015282191008407042c0362060403015846121086505801003184421250440610303015540c075601c246015140c012294046110419400700d44051070784e2101c550980661804c00c00903172036030010354982c441650894241c41b402e10040088070804c00c540c106401c1400560307940703200e02e943c80c400d071608103650881342003042c10064841c450380140160fa000c42985801e07040c43d4840b440a507100d1040d4000500105520740e04038002e07900440002419410203480300d86805d6495030400c4c0c1c0000519903640f298010f414440145601c02c6210600400112400c4041c0d40c503550b03030030764040d21144c801c06c0000400c6140c1d040e40b5a107580d40c62085500076202d040307290b00e810b55908000b915070b00c0028411407041c0014040c19901c400e2603031344542c4c185507003400c4002d0138164035684a800421010500e00b031200208010b01d000c070f00300c0e044044108081c00140d032289180740c1070340411201909508500300c003c0161861640180703400038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 882949919 1250 882948669 882948683
    0x10b27073902060a030504150c0c060f06081e0d05030610121d070602010e0d0206160203040503120a030b040915110405040e060f0903090901060807020f060702160b07020307060c 78
    0x2a00719400300e019604180313072200202c2d80d580d0030402413000607007240780c1c2030320a540308001074440c10001038034404d040b1002902e11a5a0302a01c3d00f00200d65110001a20500003200e20120310703629030302c24440c641c1305001d50500821700c080d2034850181c41a40c1c043d5000800b0000c04034280c1d80c0c12100e80801d01c1c000c5c94a50345907040c981d030900101c0c2d0f40f81d962081050190071014204140642928519042048150b0005004281099000c0f4a0700c3c1c208003120710181d41603001c444101d01e180650740002d6458060300844141808074070004107412840740d10705100840540b0104801c4540409000d0030854100c0804859600c15a000c1302c803040342d5050b03150800b0f0720781d00814204c8500e190340314181d6001e9800d00c03003a9961550950b40c00881c0c1002546014401c0d00869541072062140100703224900c80440d03000d81c001d002c030181c0d54050808545691801d000000c1da1103030455062942c80b90255004101c440001c0b00701d40c01183c001d4000c1800741c2c030f00034040b18440f601c0ca07001d8441e8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 882951169 1250 882949919 882950027
    0x2b0908270409060204150518090414060a0506041b120b131107032010050601140304050a030e0409170304020d02060d1e060608070e0102010b2707 64
    0x250740710320401c0700841c010000162541d080c2802c07600704081412200c014811b0611801030340294603040c80d40f8150054038500709035219407030b00d000c11300c02401940105004400c200130301d00b4455403003180300750012036051041c402c410713040c070300e9281072141d0040018002d00707442a14884141c10242024a02038400d004200c0c602603003004851498400c0b140ca500300184820915070702884164558004000743ca10400004014950b43d001d04000360380903d8a030710004286070b0140c3ca440c0005211000350680d2494185401500c83c688110b0403002b28000b403080d1800c0c0e08041c801c0504080d4810507504c01d0300c0421260340410341005101b00d83c0010b140c00d41c0c0c8010785030708001d4503128901c281c0118000d104250151030407204a500b41051900d0032104001440e44010403503005410340c1810351041484100413400b500031018a00c0d00440700501d079600311032140424a585110500720803020b0b4850042c1242c0a824401940c030000c0c00d0f083c070b1024072080412180c500e0b8261001c0310404 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 882952419 1250 882951169 882951247
    0x2120105101d1f020a0b0907210c051507020103110c03041e0f060815041406130906050112020f040c020a0b07050409180221100f09082b0908 62
    0x1403000f4200a500040e00401e80d42c0c0100000200c5907078200e0000c4000e82005400c00400b5494610510210345010316200703a120240107030f4407000300c00781a020b00070101c140d40c1d082e04410a03602049d0200c1c0000e190071817054040c01032030309551a444515020b036240500c1c102c01c2040e25030800c41d2410103075410341000170342e007450914070320b00038411901c0e41710403481c0c88140030802018000c8404d00460402c903040c43c6c121640b8481d2584460704943d0301484080c4081004010010328400a05052401c400414140e202140030031045100721000c07003921800c1002d01c030541d158a4124009130b0b000720300000008201d040001e910082074a8035508142d5141001e00994580b207140200070000d030403005065013809200450b081800e4003c40d845c00c42000d15040e6070b00c80e5a400c1d000300a607109840a034001c000d40001290a80042c426500e5004810001080c3d80401685800201904420440202c2240910016260010f280784d00f003021042801c400c10106401405030400800d150b021 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 882953669 1250 882952419 882952459
    0x3315050c0312070809120304121101141906050607020402070f0816110301090b22061b18120807060e0f0d0917060406090602040302060d02120105101d 66
    0x444a0341c2e80071148900d007040000038101100c05810b80843c0d41103009003000d058120b03800c80e600a44d000d140b243c040d20300e900c400c0718160204c45400302c0759401c0083d050600e44402420328000c1d0140c491508168a8a22a100445072a4032450340c200d402803200300b01502d050f80c00361050901900c4200c0d000d00e9541d0301d0001e141e0000141c01c00203841000e00324140501100c0c000c50420080d03000b0011001c06480f20460400010004100c122003a42d0a01c07035286d1030070000041d240c0c0a40c06000d0047d04207481d42511094005240c0003991003031982d4180021030100c10110f0b03c1083d84400c05613115201c1070150780c40307018156010b0f82c440c480c03665800e400300090704607400040080c01c1a05204180200300c0403075940714604110481103030100003d00820040e81040c0c0c090f40024200c580c0d807405074003a000701c1e032019500050108459620710120740081001d40084201c0258036a05c6104011103841d24690000010300c0218445800180303400c85100f200d20000e2000600401c5202c1d081 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 882954919 1250 882953669 882953677
    0x30717090301110f0406030b06090913051e150604140408070c1a09030d020d020c121608030408011503230f01110a110105071413050907033315050c03 66
    0x46250006410006c080d818861a100e10a040b0340052501c541d52002640219010300a000440018042082000700c1001140c20403225440c990b208168441000381e110940c24083c10404148070001411603c1e080c8140010691040344440d815142da03207a6994076000a082250644500000401c140506c42c42122400704e50002669481c62014140f60601103104040801c0d503020645c4800d0030740c0c010540602888054a24012021aa2803545d2508a0141e444c04010080c82000b0440342c1c40800140152000324000780050000f01401113441203080c80040d2800307ca92038407440b00300800280c0100210303803200300d40f0200341982c07449085541c0c5102c1d104043c600003c04100072500443c2d41c0033b5003400c00c8000c00103881c2031400501101401074041d00124800035805004400c24003484001d4140030b48035804510b422a009001040005129a00c0303284011315484035900d550390711202c00d4074031000c00380c0d000c0c901040384444a07400c86c5150103004003448004070b0700704104060 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 882956169 1250 882954919 882954937
    0x30801080328030b220c0305010302130c031b020f15040503120603010f06090b24070b18071214030310060509011130041d040309080a0f05010b0303071709030111 71
    0x44001d0102c6040c82012100c0006d980d205040c105401000943d0703501040c8509004a88004115030554a004a00503d0304440d1200081d040030b50307000b4103507800920f1228101468044840807003048250340844502194010300992003080503000941c00a804160090400b900200380383da05682c01d04107079040d90708030896041e92600300490768035161664103125002d5964040038405924020303d40d0748548200030301002c2d003c03000b00d0503117650301c2007088000010f24262580c1d41d441d2441c1d81002c850214040d82c800b030b0324010784000b40381c0100859014252a0304040c441c685411400d0b1515040303aa1580d05025203e80701d0303440c1013000d0000e44200040c482d00d50074a4020300140342f00b14652440703440d214500602c0144050301400f11551000700b00f4010300085d41c1d0310740c50204c81c00082500200d6950044200c10420000e1510014031424400d000a01a1200b0b0005266890040d00c1000d4a4400040c103c0e140440c8244001c100c1d09001a002140c4401084078001c400d0303000c01c13a1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 882957419 1250 882956169 882956209
    0x3030c050f180406060c05030304020d1a0c031f060e01080403020f1e1005060109122d02010f020105100b21010807180b090a0f090506090a030801080328030b 69
    0x1802d1a1440c0c18481c19025003034500303000003917000c1c94a40664901000708000d01420200c150007042c00441034213129902d1400c0d00d4170704503181115201000c1d4005540804107410340101c01c0301e46400f9480a4000d841069513440d2049854030700440f04140c000c0c0c426130550059000102c00c0d0704080c02150f044030700084442c10001080407102d0301e0900c00c240102403091514081c0050782c1c0e41b2000540444800540d00c8081906074105202148030300280aa01c2e40204007039820520000000150a44d000740c0314264404248413059007666401c1b42c0c0707050030090a107002d004031500c84010f44401500040d5481540b01c000030940c0c800c0c48280c2003c03005900060041101e20903002080d90821440c000c14030551500001240c0103507000b4100054030740c0c4600c1c1550595200e0341c041c2c01e8032034108044448074108440e0040d21201004816000240040b00100c1c901000104484803981030f080d480c0e42043c124500c1140d40d04080b901a030800d070b03c411031a00710750b68510340c140c490810886 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 882958669 1250 882957419 882957457
    0x203070f0216031e172b0c14131a0903100e060c0913050109060503010c0203030105151608070831090f2705070503120703030c050f 58
    0x29010380750104942c203030b8010001d40442400014111520039000e10701410041c0c50204080c580210030340e55880059031204000305a860352180340c0c0c600030203240d0680841000900307000e0900025101c184241a021450300d110300322449048400030014001807401041405445443d54100054a1480225010004100016907103018081c0b6920301c40004030411049000048081d02c41000610340400070401107171035212500d80c0740308650380c0090300b2020400c80da1128440d1001380064000e03580250718200c5ca0010250000041703c0c16076030010300003581c11724644c03040d8420b81c8c40900a200603144024003c800145100e0140c8a81481040d5180d2111640f180724032040007100f8202c04428150303040003c00c141c401c020001030300c60b5400302040c155003e0441c600a0041a00c5043d96100c07120f1886003105012100010342074400c2058a0207039588000301985d8905200044850000030851000041e010303070700180760800c050806a040004202c14081180c101d5805331800800e500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 882959919 1250 882958669 882958697
    0x17130519050414160e060706020c0610060c0807020f0a03050f0c1305011404051005060723010c1b020a030807050114060603090a140c0a060903030f0e06072004020307 73
    0x2000380380f003801e6082483c020307034900045440483c2e4004420039003804411001c2001d03d4441000315140e898111100b5943c40741d20110095803034008580800c541c3c1e60f4084003081e1540b0030143e4020300c44d00400d0003828414550200814009400d004035400b4400010000000c1c7c0b00780f103000507040421001d0226a1280c80900c8504410550300800c103900e044014001c40800c900c0341d41014030241d1700050f05949804002944046070b40090754000c0012130728104100c419218043d0a81c40c404010911180b0302c4403641c240c0700d2050b11070b00401c003150045510b5404c4a8941d103a511b0004105a030561341d40e40751500b10b80d100d040c041d60165180d5000a51108040c0800ca4000c40300380d40071403079441c040c80303030a86494034107000602c0d081080f820403003080002c210f02c0003940d030300414400344c55590760f102801c070704000d2000300d020440d845003010401d07010361551060080080c104c1da1410125540e83c000000400c1848000a00b096a032042162030364400395100703904540350b440001c403000e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 882961169 1250 882959919 882959921
    0x11404030905190b0c070e13200d14010f06030309080d110d0c020a08030c24010506190513080705010e03062a04030b090d030513171305190504 63
    0x1900810302801d84401c07505400388061090008031050300040c1138841000410941c1080c06c5588021240d4211405108122104000c0c14034058411000d85015002d84006517030481c0500078200c0d07100d4400d09240022494079034441c00640042d00c000207143c81c0c40302c1c1e850300301d410303942058000460700d0703606100300d040800c410303039502e0100e08105005111001100e50740e80c03c5404284204055280c281c4211b40310144080082d00d05207040c0c4e0f490745414201244d0710302c002e983c106171300301d20b500d03045c0090040ea140040c180d480141c00c181c50040e8101685880c0d8000d11001c000f041b904020000845803006c42d81c4020f4030426000c0c0800c2403030b000004080010792988039119803c04000d01c0744400610082c4030380d4012925200140c10b000c04e103102158007032688003600a4082c0d00402c54000350100c0c4101c5403000988080006403513a400f54a08444660360090102490344860a00a41d01c03801505032400881a1600e00c5500e583c04200c5071003041590071034081c2c4800080c0403910700303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 882962419 1250 882961169 882961187
    0xb0d0b061303021306090204090c08010501090e06060315281e0e04051e01020304020a0e01060c200301060b0c010f020c070612270203120406020706110f01140403 71
    0x41290200d0901d0540401c00c01c070341d016440002d100d4003040342003142c014000d40107a4001d24028000315103d80c1d03200b06d584003a0140d5011240018409400400e6540c040d81045e4141c4006c0b030072980d0f00d0307a102c81c1400f240b0f51001c1c00d4074426401081c0204113a541e00c003000003c00b50241c2d2642c80340000721000e0342d014007954000000c120f02c610b400c0540500c1c0c400307250044070110581f159150712142092070030004c0f10035a0040c90001e006e071410500c04150000d5010f54400da80b24070000e607071107117410681e10f030a0140e4000581801000004641c41740f041c1e41c3d040c00c03401e4624000b003150301c00003800c41c2c1d01b650254824000116040c0c04102c006e00c540030042d0300160080d803170800c0c5211201c1d103440082c0680c50a218123500c103241c0d410303c1a4804d0034003800c420f481004c280484100f104805141c51803c0b071207441054140800c030b5100505036000c40351560000c101d914103180e400d58140d00300840112692140081e00c0140704000d010b5001034521051022416007418100241080300d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 882963669 1250 882962419 882962441
    0xa02091e03010e0f03094b03030316030e0f16080115050a0e090709050c030103140a02091803070b151003020a08070e120604050f1b0d0206030709030602040b0d 70
    0x8400c546003100220845001b801c01311100004c4c1b0710403030100c024210714038200a210018001e422083c04058070310140581026004503040941d00500b01690303440210381c0201800514815080080d0103504401254542c04081d5144131480340002440c10042902c421071403a19074004018242d400c0c0316101100c036445611031081818a00841d811703810b01d100f100340030010480000c840f4481401001c0192140ca0b400b404903040908048807190001e00094cd4131030301c3d10190b40c4402c540003400d401200d9016181d240036603a400030403ca43e524810a1400d540010400e0302d0008418020340d9201d0168946444804420407080c0074000d16800101c1d024544100020b200e21500300440c0c90b489051440d04943d911074420204103d01c1c44a200c0440610624050100700b020109107072016884c0780c8111078540010000d10f044103040424a03940241581071118003504002005545c802c000303003054035021781c0d282e494408036440342d800303e001c2c060302007041516000c1ca8060010000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 882964919 1250 882963669 882963673
    0x909090102031504060b1b07150c030801090b15130506161a010602071505070210090513180f03030e0304030f0c050103060e0a0b012601050f03070602150a02091e03010e 74
    0x290900310403120f1032280000c0414441c7d401c0c08a5040e1190070840e01014020031101050741040128026040c000030100440102d42090004100200765105e4210481001032200d0f4070f69003401e10b8050305d5409541882406074000c0404580390b11503000420303c9100e11503584881070184d0510a05035075852003044401c0d425000100800d50b0f00244040540300c0280320071501159180060307445200344840207400c101ca480030039005036048888041101e109a408101074030040c40c10300c0484004511401100030003440c11030100303076940d000c000390382d11a0800144102440d55143c7c550340095000301c0f12160040e11640410403504000b400912003800c090000604110000211b06001020100080d0740e0b088103405903803041c01c0b110044200c0303484041c15000755090881d0b03008004d001d442d005a141f01d08001940c240010644121102c070341c05041340c0f8403041074065036054003400381030300a80c0a00c10450300340c5d1200302440ea0030301100c440d40c05100c20320060500756000c81614100e25 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 882966169 1250 882964919 882964931
    0xb010305060d0b060a050a030609110301050709030602070821090c0d0f03030b0f1905030721080d0615090312020a120c020607172511040504080909090102031504 71
    0x1d9111840c1c2e4011169129202610f10707510708010481c04071042d84407961200c03455100105001c8141c0c0300001c9180207043c2150b005c4078070342c145800d0b1281643c040c000a40402c05c20400b0074510381c041c0040c01d1058010303e00e04261402c00140c02c184102e010b0303003030002c07541c00c0c81030300b80e030810030412076400641d00c2210440181d280c1201101a01c8030140506484160f080100d5490110000311490b004040102c0c2e883d06641103010030440c0d003e002d00912074003002245007070042d406501b00307905291001c000c00381c00b640c4e0f42c003c03904002c03210b00e0032a8441d88080750f00a1500c02c0b610001f2401c1c2e4501d01058614144640c9008904600328195005800348802040c03042010060b030000c1810b20031300c03001a9102184285c416058050309050018620078031402014009004415008050101c407079058072403100407030800030300140082d00c012842011418581c00c00c65105000d2a2a81c0c10100b040010038481c4004561004d01c9940c00000c0144480b240d0351185910b9006507420000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 882967419 1250 882966169 882966181
    0x20d0209100c0c0b03070318150b06090303030a02090111070909060612051209030a08042607060f03050a0914070515120c0c19030509180702060411061611040b010305 73
    0x3c000b12a00803ca42c01c80b0010024803001c1c000d400c100500b40c41c0321100080c0300c0160511a031000c03403002ca607189807800c01001c19024540417060f00c0c040800280a0352841c0c03100705070803000f548540302d1039043c402111b01c90a14184103001c1c1000400b100f950103d0b25851600d00314045070300a80041c031000c1c1050219034041200044c01d105030343c41c00c10105603034240c02c1c80040d08d0142c000700028415980020046540149180070b40c002007006208048405940002c070344c0c56030090b00038207001454640c107407010076100703412098206500140001d812902d5803130309119404910030442170395205441c10010760038000856031243c0103400b04982015400c107064049408090a00308986002103034894004105010a400010207401401d56003042c074580600b054000a884600c10b001100140c451072000e559040d01c903c0055000d007046070b45507070312a42c403036640c01440d9400190502c141c1e80c83c4001c261400362701c0ba0041000e261130010300d50801003a508900a4030381094103017800c0c001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 882968669 1250 882967419 882967433
    0x6010e1506070f02090a02040b071a0108010c050d0b01180303170702010606020c01030906021204030804110402120412021507200c0612040f0804030602030403080a0911130e01020d0209100c 83
    0x3c2800d82c100d80002580c5c4461505a029018030b0300840c5110b4400551801003000c038400c807030150108a0440703451680da40c1c11081c22105050200c0000c65002c00c0940000784403a4400814003605043c010000848051540d00320802c0d5002140031491140b40820101078444400b540601148000d200d0036090010007034449405010302814542c0315142917040110380d8056903001024030007440e22a182c0b038200108584000d8800b40c51080101b80303510000d003054001c13a00c03c0c0c2c48002e013104040e10f491f6101144c800d400c0c10070100310302401e503403c0d0300c111400e0420740c0100c8441e5904a001824101a0304030440e415050016030f81c0013459043c0c607078642c41d003545c40100b02c9441c0400140c1c0c43d03040048441c10114070040004800050110400c038080e4042c50042c0d002e5698110141c1e54440e1f03c804403641542d000d41000c0b00c461209981d85810703200600e61800350705001c500d00c2e05000c017460a80c2c20185002d200d840c2c02007041003071410152009000340e051482c0076015480c80d629120 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 882969919 1250 882968669 882968693
    0xe010201151a160f03020c090112050a02010f050c070f060909020c0c0f130507090e01080f0606040b0d0f0c0305120a0f0507030e1e09060406140d0c050306010e150607 73
    0x60b80081010910318560581c03040d071a50095004401c10840b80c40c20302d402510303000c2c4004007901c01d150510010a450545c074650f511100e50100042c4050942d42d0010b403191b107403c0d603004040000070030140d011b600d418011240189880072400c0901400c058004e040484107411200c003440c814001c08400b0200055100c07400b0b5010388125001e05501008504006640c180c000441c0e4180005d00188640c05441517003258115000041c03585d80340e18815440b217414881c605190352140c40420560302d42a40085000507008240d00e52000c3c541d40c2d0303107900d4a0500400c0e149002c00200800c01c0c001c041c0018050715069000719844c00e00a190007401400407050140c081007404240c0d17100b01409104410000e40000700f44031030071340b01d070000c641084050440903401140b0502c0800c0513400c3c9805000705a50241d000c18200d01044004e20081310348801040d54800c0c16008001000e8038180040e034040d160116510400d0b2804048000720000203c008078020b200400003003002c01c241c04000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 882971169 1250 882969919 882969959
    0x207120e0d110d0309051002030a020d0903050d140412050a061b0c0305130b030c0901030b19211a090c010c02012f0f030d050f0f011203030e030a0e01020115 69
    0x10f004000614142203800720001d80080e070f00140d40b84010425660000702a1143c01c0f910340c2102e4900f03000072812201c0204074803006020794020f04078441128000c04886000302c000c54111400c01e580c9100f0845011070000c0107440c5038205c805450140110f42c0565419815502d0803d1070f406291070008140c0c0d0040c16010f000c0040101c0c00450b8008007551480c0100805506e0b07945a08109c002c40361194031606074280807031b00e8800c0c508424201050700114103818501c0d00d03008a4a065160180313000c4040c0c400f50345501150100c00090091031019214020324846402c0c030f40392a5610920b0800804401418021001351920040c0c1e44110414a50340901e03000b80740550301000014035140951344090450b00400c074441c00e54a9000028100045a00c00180802c1c1c8070460b40950151094030014603039403140005010307007800d0810354036906209103800030b010290401d1a50030750304004551400600044007840156909000d030590200702529000c50441c5402c000301a00c209031510f03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 882972419 1250 882971169 882971179
    0x301110c0c100e0406270504030503070c0c030b010e060910081b030109050f030a020706080c090402070203240109060504052404150914071d1905040207120e0d11 71
    0x4001c81841107103110003080010388180202501d1b8481020401c444502590303070304402c1110781580141900130a80195019181c5a10390f45510708111800300f1151015110000504000000900300c2185240242100070003600903003400781c00c02201d10000780107800c2e0b140c1244020300104d400890000200701285041c0506094400301180c050280716001a1040c062a250f09940483c04401013000d0036036030f4262030300d4a0f22a003040d00d10f501c0036500e41421345403d010008044c101075000b000c51a000800301e442e400c0802d041d00c0c0d994003005400c0d03034044840400400c1101503500a0070043d00003150148100e2a144100c4c1d0340d90144c5000f040d00c844414000300381c43d91500c0c0d01c28410003004104d02c041c0580c1343c011820150860000545000b600e11000a0b25107208130103e6400721842c41466611003054810000c6a000307030700ca4000c405c80c0700701001038650385038070040554901c01c031198040c0150200c4050710f110031119005004100089542e800651f51510a003c070740000c6036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 882973669 1250 882972419 882972439
    0xb18010c1403031302040506031911060c0d1e0f02100f06050307140319030504150905040c12050609270c0405090304081216060203130204020a0e0301110c0c 69
    0x520040720510042249080e0000000f030100d12128058210000d50094074240441d0f1564028940d40d40a900541c0214483c240702d81400a00c0c0804052411100181500d080c20540034445081a51142000021409000c081500000d0310944020008280c0c1019180c06034990400ba45858240850070810f0f9900c41aa508942196001c8400303048060115a01c654403281c4c0f1220081e40c401c0280d00c039200c0d0406101807080c20340c041c130320502da2541e6002c2c285071401d1300f80c0c6040341807c010307401400f000e0700c400308182d1582d12035a24212256580c6061a45182145400311000580524081c0120808103c8900d0400b00907c180070f4160039403001600d142200341e81004030b845000c990040c18541445014180007000d88280c90580080d542a05050300e18a15035100301e188140500e2440700d00c1801080065024542c00300c2c840e0030a0400196590020701207900c8a401303e00822445181584242024841c0540001840c5902031030032003a821500c2d614680400040d01c2161011 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 882974919 1250 882973669 882973673
    0x702030a08010e04020a03120f090b0301061b0c0e1303031a010203031f0e010e061003020a1d01020c120313060306031104090305040b270117010e06010c051005100b18010c 75
    0x41c42c1b030750042d9080304128800d500455001050f60b103444459170f0008003800390200e080c451000840c0d0488100342c9421011000c01468541035640280741035030300056001001a0302c200c0100f405200344000300103c400d45400d0700d400b0341140e0010341080b4608601842c04012039800004594001807880d8600810070b8149252442064064000c540040380e580000a10032140b000c0560064800303d0340307104501c0004104500b01d000720740807940003642d500038500c3e0154001c8044949c8020600c1641d103001b820f100403030111214081c100c156136000103a0000d000040c81400f601401143c541442014a10f0311030741d00201e08044010701c650741d40d01a580c1014000c4c002c8600901c10490030544a03000c40002c8243d000c035038141006400e031150200301c3d4543c400c2a004125612861020300d081e400c007414009075010081580d4140414060b8200200300c0c1000b030440c141c00780c19000b01d401c0c0f4240c2c94583d00c14080b5030003806000b505201d00004202610520b0410f10b00a2915000c801128 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 882976169 1250 882974919 882974929
    0x1080105060d0e10020301170313030809060d2d0618020d1401080703020f0d1a180307050304051206010501021209010207091409011103060d0f11030303011d0702030a08010e0402 78
    0xf54002542500c100541c054000c030f2103401540c1260201c0b45041100f2031420103d41d02c0f03100d426441d103003c0030703142800e00026203154058501c03441c0c090042820304100d040e40c0021141001030440404080310110355101c1e00880032a4000d060b14402889280d01d4104003900060301400c4c5a200303c3c0d00420b541c0303000d020941c0688100c0388190b443c0c400c1543c1d6821705c00d4441c600c40c0401c9c2e0203000c0c080c580c9076550800310702c036962617507000520000c0000d032840c58282d074500182c07070590400d12101c001c3d10031300c5003000a01100360250000e9a034035480c000800000c0b0310480038401d070070303004100100016a004900c182d440781407078901c541e0390641c101c0100d00740503094200c111d00d41c0c545010319505986e800391645c850700e8400d000300111185c0145a1055010440d0a1903000b0f440381d05403000600b8100b8541d85051240c000341c10644443d400080c11a0000d82051007054254060200810031011107560000310b180061880d02080310001440c0e0340d01409109640e0070000049002c54840b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 882977419 1250 882976169 882976181
    0xe0c010c02040902090408070b01090203060d020d030905210615030d080901180308090d031109040b010c06021b06010b090a060c2415050316030618060c031d010b01080105060d 77
    0x130042803021140b5061400e65500d400043d01078400070702c81c0c0c001091280c2c2510031240107000c02000310142040641c20041140d24070300044042001c41d210001e20707034a130f101841202c1c010542c000700300c002c0350b4100b46140ca40020f0014041d0002c1040c01a602d031004194015481c44e149400c00c0d0f1a519001c00354054100b0081036040856610582018940d11400c160300900010341907071001c40316800220140d85205440d03920240042103448040d1030180e00c08000118181421160590103450315800c0380c1040b02a603100d500b051160580301c400a02c4aa409000d032440c006003010161008500c5480d039a00400085c0144003401100f40821034651180004113018200c41c00308119000310041c00090b2a48420b03603110b041e020501d45408038190b17090031185c3d151048142c0c619243d00c0003600c8602d91a41c030303030b000040040c3e01040060080c804480a81c0d18041222826010700440044049075010496403422000103621381c1e004a4160465004482190301e580c602d182c0c178801011 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 882978669 1250 882977419 882977423
    0x40b0319080a0f0e030d08090106210203010507020303010303120c0522060e030c01140a051e031905090d0804080c0a0c050a050d05060106050708090402120406050a0e0c010c020409 79
    0x340c160035036040140003001481034603020355945030500c0700c201041d00c81868414100b903040d0400840010640d106040d2a40d2120010300003190560b0f549100c51060201e10510600d44500900c82d041942001d008543d0002d82c01c0c07006600c0d56145443c020304854001840000d90f07500c4041040e1058070030020f441448900c0051114028005400d101d01d1004070b01c158070104108815060f442c0c600032981070020641130f124020031001400400700154003140250b000d002050107158140c0100c40700a010b00010500791513502e040003101c445030700b0041040342c606c0d80c1c141400c000c0401e0380812008584070250424400c0c0f40c4842c034002101c6d008100700251217110364205c40091100b90491501111170503140c8460082c1c58500303200c1c012840d004042c2259002d0401084454458001490110302400c0341600b44105480060160fa000303290060210816009000620142e4030036076030030600440b020058075443e140c1444d1030f1868045554140a009080700e825511140c04c14200b072a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 882979919 1250 882978669 882978703
    0x90204020913140f1b0304260d14010f0302090601270306050a0c05070311190308060f0d03080a0c0c0507170d0807020703080702030a0506010b04080111120105040b03 73
    0xb00c01000b140107142400740e100300700d082000410902c004560301c0034010071640d070840510007030b00c0d00c0e003005950018000b20b80071440304824400010120400040b41c0c450520016170322115003602c0c009448001032200d07007501d0070030300401c0000141008101182d50644210001c0c4e42d4082c01642e2001c920140c4208040406c0c9600c0e111982d00c1044200382c3c0e120308400c00c89138452109402c01c54030030010100104004105074004a03002b800c1e20503c4007405001c42d401054190303240e844017244a2001c60115061b0700030300c00c8500c1e01040b4004545c0040c2c504031b20201d01c60310300600c00580584001c483daa17171046100c030828881c00400100640040860340385941d41d52101e0004015212445003500903180e5102c90b5a1080d00e000340201000d0b8003c1ca40c55003140c90b2040c040c0e01c448422685840b4604078040090700074801280201210507200c2d89031460040c1071801d440c41100f07604140d050030030034600f0f82c0d81818000d5056902c00e482c000b55090066000c00d18101741171050615813 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 882981169 1250 882979919 882979939
    0x90503120108070603180c09090221030a080106051201090509070b070503040f0b030108030a080a091209030b0c070515090a0b010f1a070f0209040602090d0503120705090907030902040209 82
    0x241c00b00081c4881150265a010030045078094a03825030098024002441d4003081c4030100810002c541081d00702d20300040c48110f262224407441c103945070021403902115000030400c0c6103a03a41001e0318900400341070030440e01e0240b002c0510000c00b60705000d8511046e07561000302c0c80c8540100f010801800810000a80d00d03043d50400694036041032007525165103507188042482160001503c0c1240c640500840c20440380307180030f41e503c010041c04140da0b50350b1007007410041684050841659543d42e2181403110b801d44c203008045180007856400f1000301041413400080700003640001100003c51143e0b00e98440c42105070902c0004080a0100c003000000802c490100140c14007c44400c040c50340015110918084400e000318140030b0308010310134031610054240a020035500602c619401071070003070340900044000005500945942c0d20103d924070942c4144020a600000c0a06004e0304100f0f20000040c070552009241d001015140c450000840d1031f19010307034002c120006d002c9148 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 882982419 1250 882981169 882981179
    0x616110d051305150d050a021611010f05090319020307030606150f03110d020a0c02102a020f270f151203090d0c030c0b120702010c0c03030905031201 66
    0x407500003030750202c1807030800320000401c0d250228001204811501c400c0d03081003480041000106001400e00320a5138080000280da207001c14200503d00d481141c80f4650016218001070000c001004000c0a000040042c48059540040c003201d50101c4c4001060021145101003400d182c002d5000a02c0103041420202c3c048524055a4402100c1d981d20000070310704e801c400301e040d00c80e131500c0484074800801c82001c00c1d104c0381d0001e10390807246041c0751080c620664007003244084030802d0080010380c6103054281041082e548400307800a071629088000c04a9000524420f8401d079103207100d4401c07156102c44500411184510142042c01049414038110102d0004035504a40390300748888507203c2d80c20185813003180350f07121844038001541002c0d07211040c40361402d507121040e1803a07107102400200042031030240801401c84d00b40e01544441420b4065010407030003601490641e4140058001a954080b205042060b0185030110702a070041c140035041d44240c01c4207100c14014000003181d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 882983669 1250 882982419 882982427
    0x12150a0603021005190e0105072013050402060906160f03090513020309100b130629162d0c030201020f0d02060c130803070c0e0a0e0616110d 62
    0x301e0b4000d86812907011100c410455080c80b8581600300182d02d5214895105840b64013080710500b01810410300d00521030b1201529402c0f60b003d0030304290051051300c182424000d604804a170400c1c070060100c6d0800b0340c00141a80600b0708028000c690120b400f11041c44c000d000700346141e801000d03509000c41c9a0400400100c024042c4c0785c00350402c078070300301050b00d49882100e2140100d10050260031184041040c060110301800c250f00142c0340e00b0440440d0b0007485000300074050891295901c5003c0e0b0000101e51400003001061650700f80081d4102c1c01084041c140160751141819042e0220b061030281700303072401c00030558070900310341514041004000456007580e00036002c03610184542d854455541c0038403406107005800c45d00110341c040244001a00564101001100180d030f2030303124451039500701070300a4690807013030f0004000c114018804e10f138004034194418040b80810343c0c4100d54070a0094062801422426205059240309100b0f1114543c40c14040d0b035280014900010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 882984919 1250 882983669 882983681
    0x302150402221b0c030e0d110316080706020a020303030f041e050a0b061929031f090204060504060c0f0b01090b09060f0f130608030a0306090e0a020f12150a 69
    0x100f5010000700580c0c140d015450a04019a06030b444c4c0040c6403c0b0002c0c003961114060040f100c16034401854102c50f0f40500401045078010000c0b40ca03168600305083d4a070a400358054400d41d0004504034000d600d0110840307a018180b4404507810ba201e41c5441078409642c2001000c3d48407000b0015810841d0100d010f960190261b070181409486160401142680b9804840b1180e00446000c01248031046815003032000c4c09007055500c0c003410456600a03a01c100c0e039800707a0340340b8000e1050040c500301115001500f0141e00443c1010f05108010300341c0e02c0b544c0078210070b100d401120314003000030441400a05961001680101c0c0d42d490562901500c0303600c1286209841420020f466410300c000400b400e07480090015110040f42d030103001095010f00c0080c0e1140d52100d40102d480c0c0e80800c020500418142e03130020f261450841803104541c462000d900d0b00c0e4020f03084032809680c400802c4004808210b0358080c4114030980c600b8034082c00e00e441145a188900108811901258014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 882986169 1250 882984919 882984941
    0x1c12090b06090a05010e070e060c0604060603150e030a0c1509030905041413030e030f0a080307030f0b0d081803010603080705010e070b0d0903032c19030215040222 72
    0x7804043c2c80c0c40c5040030035514240107800f00300b10408001025648601101c20f40c120707015150b00c1c60300c1511180070b801d00c0d4089806940980e2910402c004001c0104900c40c0905031418040150314000300f0303419282d220300c41c03420082102080c803c07070030710801d6156189003042641040180011514010b8a407101d0383c420766100e03519102e02c010b03150f80428001031156a5515600c0c441c02c80c242c0e415078464107224481c1da014070900000c100891802c11041d44080e024142c80e9490b4034001134008c003502c900300f100300307805400c00181140b203440e8031740e8031044981e107c22203580b0f6600100c140740c031380b0310100e114903032540c00c140c4c002040c050f40c0401010010f001d1802801220a07000b900e5944a8048c498020f130018100700464030080550700c64441c03103100b071a000c00d81104e450007031202034425030016040b88019080500c02c40b1003c026842c805104501c2a13100d0040c1c94401a450388084001d0071080310042000904542da00004d10000e61007081183c0301c050b41070344e0190003d00006002c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 882987419 1250 882986169 882986179
    0x1510090507170a151a121e07091d0402012f150609010603020d060513020a0306060311041e17030a02010b040203010509040f02181317070201021c12090b06 68
    0x1107510000540101c849040030440309a4905103031140d20791032021702040819103540107010100741062179091950003000980000c0e20341ea2000100171031010005082102840341080b8100190410341c69044554101c403040380c0501d5896000603181c501e000c65489011500d01000e0903c11000800e100804050450454000c10300094000d044da5a065410756405210000100500d522a40040240070003c110129950355079202242e4105d10103046006142d07000314851f144c10358984141d500600c0146810710a012605040d1400c500c01c50048030355040940c00840c1118034405007010080c4a10343c14182c0d406401840d82d03031244c1180400c14015420507000d958107180034000c0d6810303a6030007800f203074064a69076100f001502e01c01c4012030700030510034038074401c11000c2c9000c1d61080c0c017480780d04051400b851401a81c4c56010100c04002408248010b00c00344c1d900086850000208005000035032420b00341c103440741445140d400100b03d0030300300039008001d10f000c4524040c0c2c030240d078 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 882988669 1250 882987419 882987421
    0x715020601080105010e0f1b070812310609290f0c1c140c0d06060201060e0a05180f0307120305070c061a0901080c030c1002151009050717 61
    0x2d501380c850030700c0740315003c0c042c42e4003081c4c841030010005608210080184000b0f0980b00c90006402e03000784c00d05035503941d400308600790800c1041200c203602650103030310107074100241007183c409072500c28142c1e04800102d4507000101700947e8403c00e0010b41020380310708500d50600c14114503c0e50305545081c00941d4401081c504042100a1402000f0b074040c801e041c0308000742040545101d840440308402d0310380609600c1d011031800c58500400c811220655075a452070000416154240d11110840e032410700c0c1003280454401045411081c9540089060307200c0aa00c040b01ca1003103818102c1030f015007800081c410200200401c4024852654402c0040c0521800c0e82200c3c821200f500c042030105010000203125613000079003509200100380d10345244c1c0c0c404103004134000d0300b00011a030b0103038820350034504d002c1015207000101200c4034004072103d440020b403104403d049401464601c0004215a82d50b030040c0c400103010002010006460310b1400140b2440780c208201040e005290 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 882989919 1250 882988669 882988679
    0x4060e03040320010c12090f080d1d0312030711060114031f0e031b010f05070518010903020d05060703050c0a1d04090c06120605041e021b0715020601 66
    0x44141c40460f9005402c80400041d20341859003803160003007005040141d5007003482c0c002000c807680034046500f07564801c845581807491245004895820511655100071991000141d205107440c2d0802d0b070107612882000203070404245441c01001c0f81d2210403001004102d480c660144182480e080d50700222006030360b03990300307600540e0380300018590103400142c2da2496005110307007007800d00c10520400007000017200034401d08680004d0b4481c4011a21100b034403290101c2400b07188000c906c0c100c420052810706410107040340c4910350030034070a1490380881c198149c1c06400688003c64001c1c0484c00100749902d801c903120b8034100d621030046807400c00880c5640b20050165801e10203e901c030700c2c1c40e417190b299540356000150500c07994407940f40e002d100c00151402c03d02c1c1000781220740b80c001c1d400741c040e441c0405950083d0001070041d840c00c110585000c020a070784d13040d10030042c0401603030b41120070700c003c0c8002192254143c440c459503c00144444800f0300e1071440700c00e80c0d0309941c2980d80791 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 882991169 1250 882989919 882989923
    0x121e0a09080301031112010c0f110d09053304091401061b0203280b160e100315031407050d0503041401110d020102030627040b060a091404060e 63
    0xe028080041c244010300000700c00450b40c1c003100304006d0202c03403c560221a4203003950180900080080d5180e000c410602d40c03c1324010100c446420040c0030369940512000740f01c075000b071046501c0b8ac00e1b400b072440c41219084c04003400c0000c0c03003c444000c160001644502c194040e10414500616000d1802d002e41c11207140c041c1604e03030380d03030b01d1130000c41d920030b42c007200d03100e00140580c0c5c940150600c0041c030203110103210049960651590300321240030b04180e03000c0d00c8000c00c4411440701a0740b031128a250721680c4a08040f0084070381d101d00d49494001200148540702100d40c0c1102014000300038005401c00200a02502c10100e0300c0c0c858468050100b400d52843d001881c650090001b4080000c2d80744042212103c1850a4091801210b4001e171425405036101340160354000140580e03420481404920003501c021000c0190751184422a0000c400a0018003590240c00100e00c140d56590120030040400e441c080c0448203400c03144084000301618210340c4103140c000280140340700 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 882992419 1250 882991169 882991181
    0x318010f020c040f020d02071b05030a031b170d090209010803090904020d03110d030608071403030d05100b0d020c0c04060305030f09181e0c03101802121e0a 69
    0x210780c050301c861100302c420702014080e4820300381005902800001d0000d0818405046480d0082c03080b490041e04003c00d49902c002640c00280c02604200b100a01203070b006800000d28070704100c03204940c000d032410f02d004601100c0c50780b2490040c0009030070701c0b0040a5000100d06030f0080312031040690ba120b021079624452000c0c0c40e81c1141390700d00000d001d490400e110b0100280241011101c1411007024182412448850000402d80d0ba04080c0441041040003074050061000104025407c001c00a5500d00410303c1540b1142d40700c17000510860162458013000b4445800402e81740c4c09034030f03c2c40010b5040341d281a4424400e942d05040189450301900c811690401c0181d4641924154400c1c144d9212110544d00640c13045010a00400003041c8a8481d20407100f9040415517480726901e505c600c0602038062010003802070001050910300000103e170490142d210780c82e900450104081c1c010304030cd45181d07201500c1004410502c83d008500070f000840c0724009161742d092080011121 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 882993669 1250 882992419 882992447
    0x4051218060c100203010b030a0506010f05030c13081006030506090703030e120a080412060b040c08130507050a090c08090d0914040b090411030d080f06060f07050609031801 76
    0x3010510120040c00c01d0001000064401e00a80f0006820040c119090742d10070380c4400c040a50010400494046901c6400e4110200b46060400040140b40040007404041c080711008040068202141c0414616100050120b0002c0c4d0f0b032540381604a02e00180365a07c801c5e0381d503006c6d030310004c2d01403000403403031009403949900c1d2502c11070310210038040d0102c0b074905016024419100b1140c0401c5440000d04010600502a4040001c0e9403070302d0703400e4888284005002d0380c204242d81c0e51454100d031020381d211004440c040c0c641c0c642410310342d20b410201d070310282c2c10000700c10003c01d201600350803e601e500400c0c4c4601344036445071100e4a5403142201d22903030000b0300b0f65005103d030a9030a032107041c540100610100304072681700001240e1100551b4121030b0081c3c0803152980c43d00b41400002c40ba9960b50414842030b2915403400358651000501c0c2c2c0e071088100148840518040409680d102c6410404440030b0f4a481480365980c0c1e4403843c6035902900c9110761030b58256106000f5800004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 882994919 1250 882993669 882993697
    0x3190212120405160920282d080105060f0d02031b0a0c0b060d15050a090c03050f0c0a1404110408120301030b0108060408270a0608040512 61
    0x301140d515803400c4060021111802003140c2c4c64032001000b1821005085a40300000d040b40c10107907586403140c4a0164804004020b0010004600b16200d055003521502c0344922003804030000c040f2005c24070420160604045034184110350914031004198100140c0c8540040d40d888804002039400349040b070b032001860400c20003090101640103190003076070103000c540d0b00c41d5400c1c1d100341d4290000b484400c0060908403410081c0310f03011500d00d400180a5070351480d0251107840d022001c031101300307404a025444a0224401101990081c6849030300710281035401c580381e20f400c60311114110411203842c862502d10310154a4595807000448000031109006407550b0070a0002601841c044026004801d000008402405211044000c581c00103407603501c0d070452034650410001a006003103654448020000002c2c1010100c0d07034502d1103400003400d006020f5030344a02c410368030581a5040341c1c3c106c0d0300003403090708031003000d0156105030151141224120341081c668080c00031182514 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 882996169 1250 882994919 882994927
    0x606030408030a0c090e090a0302210a03091518123f020309100f061406070611120f070c0c05011107092f0c0a03051b0a0503190212 58
    0xa4051079010400c4925079040c041d40c070300e0303442d0b02e0fa03004140102c41141f0103410004c000c0b810140d06202018454403001400082c445151590b8070990243d80d0410060650b51507030303034051044501e080b014a403900c003414800d13003c0504207420308500d20102120344840b5043c42e00d00c0c4a001e5554540a904801c44041250241020300700002d80c03040310440c100c2c8112a4244000031180c00114482c00358a00240000c6c0300e6121401d0488100301e014480c0e040c507042d000d1202000082c10301400d00c0e0120b400c030b43c072010386080007030080480500c030040388280055070800700c4a11400c498441c2c00460541403080e80c442c2020b40b60542e92510051144040c01010305c607642c0181508603041c11504201c4084c1d60b11443d2174400c43c1d032003600c0c407120401c0c1d49050182c504403920b031440d51442460405810510161301d65a540d100400c4010180300011030001d400c907148811032002c42c50b21340704486454000742085a00c036070060f61045d00f008504a42401501d00005070ba10350281544081454 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 882997419 1250 882996169 882996181
    0x120703030c081e040803130f111c0f1103030f0d090b060105090a0e091e0a021c0812061c03090f150c06050c0c0a03090e011401051c0e0106030317060603040803 70
    0x950744003d00d1880700141f514602030100e00d000d051221524440d105659680c547c0d641000054200c1041d020742d280501c03050702c000280c42819488569901014010480315030701c000078154082c1174810455400040340347c4600184a82010307180500480c4003040c3c548400004480c5403290b2100701d6080300c81ca0400300400d41c1a8031145034052031b0788042d05c01051202c07039200c40070803000c0d2048506600503000007055281404100c03040c000e50702020141c00010365034030714990088407000c00c6160a00030009560f903d65003204506007031101601918002685005044d1f0480c41c001d25003c40100c02c00824803200002d00d06520079060349503420680c5844d503410000d40001001804008002d000c0307411900020080c0c451b0880c481c1d200c1d5040b460401240000b0300c90143c0c00703002d0080e50340c050141d4590304070040b29002202401501501101c0e1246030b00540f051004200a40d8a0490f0000c2416440784400096901e2044e15402c980ca0b07107810000540003e99001e0540041080070800c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 882998669 1250 882997419 882997433
    0xb0a0f1205250e27010e10060309020a030804150908031303170d140f07020607090b0a020114010b07142107051f0b03010b090c1605120703030c081e04 66
    0x1000740c1503d4266100c6036864080342041d5240322070501900b20b034105110114080c51803050150030719407000c42c0d481c0b0341031083c06a1480340b1710a00080c0340d40c036203c2c1410b5440358400c1034055a000850280cdd44c9690300c00a80800352100c60400004005110100740340c400482203c100a420b0b0111542c80b03410b580703d92402081a030990341c0c1900080000803000516802021000303d251240e042c0e8520b804032022207142801003461381103400c000100708416402014400c20ba40c140d120341520b6426212040e4010320081d0719084412034074500002e005000c6000034050319110341341c02a00d14418214050307803441d94044064150083e11a45907031380340c04001501d010b500070401c461900360401c4010242c802d03541005c80c0040e854140300140c0d0b007424000c90705501016280c000d031600c0c0c104020b680f24041c1c1e02415030040510034242c0c007841070410802030089190707245c0316901d04c902d1401a0061101400500c0413542c0e140001c0d08034a10b0308280ba9a81d5205000c0c08e2b441c0d40c1e540e40701c0e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 882999919 1250 882998669 882998731
    0x4021e040b04061719080d0507030b0d051606030e06132604050901080d0f030e0307021801061701230105070605070914030d02100f060b0a0f1205 64
    0x154000c0d80d191400c1c078003980c440c082c0c03c1c010b20750011542c24525492810f0340c102521450303000518079804107402c0000b1181d8040794201e80d100346000515413905101180609402d1001c0303507002d0000b440c800f042c0702010458449414401c002019076503a01c0506a044e00c0c0d43c030026440701c1d00042c0c0001c083c1e060041100400c24820400c0c000c020600000008411103c0c0e5184445d8041c003107000d11031820600030290241c00c002d070040190208005000344a018182441c0301011b4413035503854100c560800c1952801c41e8002c255a02d822030351400208100001d201780800603000b020504483d140710340e22a81a294100081c91010700d950341190380101030b1840c058100a800c2000364042801c5d0f120301c902070041c1e66102207040c0e01e48500052203025029049201c0d07003007615a0001a41c0001d02c2d11085a5848008142c0312400114503008100590100039501e40c001408107685900224a104100d85501e442050242d6800514201c80c400c80310000600310f070300708211103401c00b04020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 883001169 1250 882999919 882999979
    0x504150302060705011505010c0b1b09150c06072307020307030b010801020711010219021201020f03040f0308070815044b1a060c010605030a080a0f080402 68
    0x8441550362a408540c0070740c0050026202e0703940d1001c2c4080d0740e6000b1075004009040910740000e0703403201313600c13072501d0020094140341d14030000700142c04500c5004000d89483c1c0100404032086800e2200340c110455014400d01150760144c440014006030084c070448841140d00c04505003408070110b0700140680c0051000d076030601c211b020000000301144009406094488000740e1949242c2c0b9100d40d80c240c80d40901c80c15508050040942c3c4110484043c1c00560100c80559403e01d01000460080c070501c551001221000010801840310100e00746400e544240d642e070307100b40d451100c115010f041c182d5580d030326110720090f668540d140c030b13030840c80b00c90b45103140c0314402100600c1c48880030501d100e440448401001e085e101c9a0000d620320311000748030404107000034041242010001c130310390000103104060110307045401200951100000e0240076040301c1d10740d00d0728103060065810142800700000d120b0400705001d548121072080c002c07036010340820703d844030061155016000445c05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 883002419 1250 883001169 883001201
    0xc04120b0a020c0636030306041104090e030912160b03070314010f06030c0e0a06141207120608010b0f10030b0316061b050705010e040f0f0b03190b010504 68
    0x500e40314030f0000d00595005284c2c01d10b004e0b5005800c041810790300b603030b524220100b0710301c83d02c0c00780c51440b0007200b180d0307104030203c0e400901d03d0145800340540e409603400404840e440c15128070f183d520004000e21808000326140c0721031a402c681015039a13801c034401d030321b584488030100704484900e01003e103802510310b04001c038014002190500c41d4031807da200101d00c0045940400600e5018401c0000c18016850302a21600e03402011aa0512103031051404103c80b0b0a400c09c2110045800c1d02ca4038140300140390a1420310020040c46158130b9501003d2051901100085c20041442040d80c07980010384440c0e030700d2251070104001880e40c140600c05060b102d15040c40c0340d03a000c0c0250b4880420807804540c0c424145040104000d9a4038055000e00c903c140610780440c80c002038000460b102481d2025040204e0000f0070b014055150454003903d060103110005040d05402082e04003406504a0318549a0803130366040307560078040701800f40903055005014600381604203518140c03980b84 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 883003669 1250 883002419 883002427
    0x20118030210021c090305190f050f0c040b0108070c020f0f0a0603051e191e110c010e071d0c07140d031a220e1903080c04120b0a02 58
    0x481c0030203182d404080010b070050304440320405001a0880d42c079403070700e240c4161814110ba0701d69036500d0141d54103003c15010300d0030981c10000803109040b10194054103035021484255002540c2e0f4802100c142d119500f0840300c205154407440c0d40358482d41d0a03549036000c480143c2c0030703c0040201201c8070354010542c072040e4102900c40c407080400038003255800040d80d2510820360755004014002501045240100f8091403071040190540c03454040000042c1410881c09803400502d20700e040d400c011401e10484040410b01c68000c2c0a20700136500c020322071210200d24894a0f202540100410600001100c810050012940c41d40c81515441150b14100e0359407a50308075520340403107250305a0f01994045004941c9402100c0d01c0c07a2081118981d040b0b4081c0006001240004240003000440d4507400658035060300140d9035001240292091029115400e1000c3c0c3d0000000350040368581000c246186100c804560844150718a010010000e5545d0040600405010b55681c503800740 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 883004919 1250 883003669 883003673
    0x16231809070e0909010b09040209090a0f0b0f0f01061b0f0501060b041e0302010e0f0d0f050d14090307030311070e0a0203011d13110604081204090506150702011803 72
    0x10055805103400e502da08284200c01e0703003048280c800041000340715034180503e00c469621070b20b20752508940e044400139426074800e41c0f4146401400007019117508503641056050104c9101c045008920f590501c00145d034403140f10089801c801e2080c840011208102082000e0002c1001c82084d03116548556940c40c89488042c25205107400180480c80b00140400c00741c041d0340c100d404402581301604a803c0c1c515000a0000c044841c201ea0185c5000c003054a00d5035100750005000941c4600f0380250200c140c20005d0390745014100d248049218491642155401ca40a68880c12001001010014119130f005c407040c540a85012900384989100882d04420490109228407a07410005849c0d615121080300582410307210034108140300700a11001c1a00081000e0049800000300d503240f514078804a00c0d5440340780c1c8410b690303000e0090441058500341c0014001c070f9403002c2d41030185803901002c000c003107421007044d240e507104104034500065026100ca0707a50a940107601c50491170303072a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 883006169 1250 883004919 883004929
    0x10206012d080607090e01080a0204050a140a091e05031e090d050d0e0906060d0b121902120f1b060d060b070201170c0a05030408090a0806162318 64
    0xba049a4181d801000c104003000381c1c46500c1c240103044a07981c16000354940807009898085282010f40903586882c002055660030350011021410981e0300444285000c2031804010480018101d40c4000104004149240102c020b100741e0364100000e185051040000c0300880d0a614440300c0e840174040c081ea540c5036403900211b94416026402903d0200340202d0b0041a03e440c011016110b503648009110440d140d500c181d0300f081803410b000040000740c0c400012044405903003400580c1c40703104400049103d60401c2110154400d50b1881d16055602000d261500c14115414016a100001c0591700d509072440907110f00038080c1c0307154907104184261000b6030780180c006104600300001d080c4119640306118030080328030101c00d44941d092904000c140e51142c002010100900400894107011015041384d9035801e008054017100c03a03072891200e46614003100e8041052110303854040a150141d00600c00c401c44031510701002c01c4042c181c02c0c490782c200380502d4a107071441d0300314100316840d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 883007419 1250 883006169 883006259
    0x12050a0209091f0c0903030f0e0918010f09111c08030f0702160302060906070c0f03050717010b09060108070e030d0e040b06040b120711070b030115030b01020601 71
    0x1114081c04803940c0b1100103259107014800f0100185107400c14401c6039981c0044014282c0341c0c103103040400c1d0240c118040f584208140c165552101ca960280030407800704400c00046801940024404a00c90140748011201c00c848003412000c601c41c1d4030000b034901501c14194100c80304009030b0341c0b910303a45c482d900720360012500814080c0401041c0000e2640401c0421401203400515086803425030b03001c1052401180300780d900a003008584c01041200035a50100a002d00c1c03412424165940d09101d0360340d01107403007032100303042c40c40b646001d44030b1041c0500100904090054541a19400b004507141d181c0281042c00700103c81c0e042d158590340920880450701c1c090b903101c00d20b5070b00040c00c01003190f10b46600f05100d00002c00c420402e846025003510561652480314542682d603000c4250703540072440c0c078508a5030056003c045441641103004d141612403401c1c0d2007443c3c81003d0019400c40d4500490240580d0011004110100e0b2544010003041c85001043c182c85480d0004494a006 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 883008669 1250 883007419 883007431
    0xb030c0f191a03070801080a0317220809010e0d0f0b04150212070f020706081605070c0f030618020d0f060209041505091e0a0f0204030b010323011512050a0209 70
    0x4400414410010717403095035540985444000f61480000c140e40103850700c07038004071420a1139402c20008070624107800012980c02900041007008003644c0c900801a54001082c050110b503800210039000d050007514042040da2143c41030002e01c3e4039440d246480400100300700c0341260030305040700e5861060f0000d01220342540b2140d00786400c0c42c0f43d02900c000034070004902154801a030030800305030300c1407159820140c010303a444880d40086000f102d0a00c9034200c0581403201c807200005c2d100c2d40000380e920480303005180030840c1c6141049405a00950107030069400760b404482580451107010a880c086441400c00615004400003c50259200003030700094190a0032410001400c00041056011349589a06042031410200e01e600c0e0000c06050b003032000c0d640300c80c05039490f10507a0444016541001c218119580d4070702c1d01424005215440301000d00b0010200414103c050017548000e102d8466140400c0e41000703003454281d4040241910980304002e100360142c0ca0761410640650 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 883009919 1250 883008669 883008719
    0x21312060207060b0102030c030f0c071d04030305090304032406090e0109020301144804150e0303190309020d060905060c1312060f1a01030b030c0f19 66
    0xb140701d04010302160548004181550410003000d1498000032040f10f4903407440020031070b181d2031208030035803426100750031916900350a401009041546015403d02c1103100360740900803507560310913503505c0340101e1000402610090003520484090502c40c0110100d001e000058816a40c1c01304505490650b11105844e075510070110043d41002e02844021440100450415003000c80c0c55503805110344005a154035860628002c03c0500400c21034450980d903402d08030f80440b13071a17201210f03a0042c030401995460a42400080c01c0c02155040384030003005000c0c5040c00d400c2400c0d0300b61200070302900d80c101076a40030740c400140c0d034681c0c000054078000c603070020310f402e110300d002d0f8a0314101410500325140140040b82c005100e00d000358050b84c440b000c9421902246141510143c0a118050285a030801d10304080361911514000d10b040c100741e0301802070940ea1018180c50fa41610b40c0c15401282030880c00001e418001e0b48540f002512100503009a5a40c00d00700c1188017110f28072800700 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 883011169 1250 883009919 883009927
    0x6020d0f0507111b0a031101090e07091d070f0e0103090f0501020c0d0504080303060f0111010c08040506010909030509090606071a040318050609190f060809011a0102060403030213120602 82
    0x481c0d410013140038000341c003011651800001c40d000400c00e02e0720348001085d10b0b12095080c4610f0740320b112020010601d0840c082d100b42440304006c1c0a06c0301d0b5009000c0b1352070580c1140c24507804024a818002c107000c0c1c40710000504c078101c1c100e4404c0c1c40c40f04024140f40e2a4903165001038400032001d4945400307203000580b02c181e80d004050505580301210700810409210900c1554008412a5000081100c1c900f030b41c403080305e00503511903800c242d0322410b651034140400c4daa217811a030400c1c800c5200707005443d0203a8803001c154007258103101015001810a00c001e9034103003447e640d03894000078020074590a2800d1655111280440c40340240310740e0030301c40140020140c220314414100d0344011a60f420b55810036011034028000c034040a4410450300701e41d000c41214040104014041c0401c00196603522000c014110701c80a035403014441d03181c032444104d100658500103400c100160f014103841e4585860440c043d421088070500316451550700003590032030613060031b01100d104401c0543c031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 883012419 1250 883011169 883011197
    0x507081014010e0c161a01140103270b041703090d1209120503070e131e0c02190819030e010c0215010b0d020906071b0f050d06020d0f0507 61
    0x22290042c1e2020b6440d41d40a424045005114400d071030108080401c191048400350400050082c40f03a18a0025006c0030070020900388100000250185000c0e2414840b941c5c80701d1400c01c41800b92590520000c1000f00c1c1d040c0001c030030075090b540007400707003400200d00308031002404181d1740251905071881e1301515039441c416400a41260204901d0700c0100031601e010744416102218031082c0741c040000000c0000c2c0e00c14050f1803103503a250b40280000c88103240c442c026100901c0d0313080c00580c1c2c4021150818082e81d42d20300607280c0d400810360242142c4a180120202d2401c3c10540403181d0100911141c103c41031007050f94910400c1344c1d40c6c0400c0e01662a904a4210f8400c0c5a0a0007103410045044d00c001c0d40700d050f440d04491188014690740d032004035640b002401100da610368803043c0024202e0a026500a092a6402c042591440c0c0c040e50740ca0342c065651110f10684d60441c1c01ca241241c082100765000e021444040305001c500e880c17503401d07031504460040721071001080300840c654071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 883013669 1250 883012419 883012451
    0x140108190f060c020118050c1c110f0d0602033d0e07020307170310170606040203040c0909050f011505150a03390c0f060905070810 58
    0x20903000810040c0603103900c203864584035810050009050580c9403010700003e20300c00d5000c246208042e0340c00c41074102c4103151240c3c541c1c08420381c3c944150749000e14080c141440e140c0f41c40c1d00c150b00070691181c40242005010030780170f6196010340e001540c800c0031008074800d8001184140244002000800c81e03040c030b005030a235226213a1548406009441204903030340d00c410384044d2540046000d01a681d141b41c224510310410030b0041800700d8400c0e034a2000e481e042e02440c01032882c2c140b0307000a6505e4481c40030142e1600b60082d0341c140c0c01a0003240141c1070135030084d50840d0203002c170004d4890311800e201040c0e07844403070211019807010f0031443d43e0030428030a01c00803002d0500751400d000e203130100166a0601707109600314801c43c001807500509000b54003d00c010348aaa0140d400122001c498000b078103402c00000c00300c1542990080035140c0b00b901100b0302603600038100da040103903503110040203005a50007111240314004c0c0120b050b031820000740c84001c012140104426200c200c0701d42c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 883014919 1250 883013669 883013683
    0x280c030606050a0c030305180f0f07091803230a1112090f0108060d2a09060302010c084e0609060d170a0e01170613020c0f01140108 58
    0x4040002c244003a01c1000d40c014600c00036903806143c0811507456100c02c0016451040100d4101c602c103141c000c0143c0c40d0080390f02c0180d910303158240c50030581d0350420041a81c0031040c1248240030800d03030400c00640500580062040c02150081c00e06440204032804c96111a14420107c0c0e1620000301e02507000b004446136140c0560700c0c02c0d0074400180003094407010000300e1a41485140800500781da2601103a050760030380c00216488444c21414201c00d141d42e1500102c01c42070b40c01e400041004003107806200c0440390b060f540c0031952241d989030041141c10007070f0034200205034031103001e400400070703510f990b41d019500c41d000c00001c41d204988101080c0748603441002190742400c01980c1c2d81c0d40689a035004405650442803c0740c145003010740c20385d250708100001d120100d0398030343c0b00b40c0c05542134103a103a017a2120008945101520a000c1600311440c41d805422078400d084242d443d900944812041d14080b24a09040100502d00f910701c14500e540360160000c0040002c800100149 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 883016169 1250 883014919 883014929
    0x110a03140a0b03060c30010807080609030406052206020c0f0a29071407031718060c01020705070b0d06152a0209070207060809030a090e280c0306 64
    0x80004420000120b6142e00008010511400c0041003803804000c141c2c42551418503450300f0040c25440d01150031200c021b0a003e0f0a91621401c4804900041c00042690095100030000c42c02c2602d011170444031b40c2c6c4200d000d508903c90b50700f9a9901251611002c80107090315401505045002405024190030102411480381846410422008404c24040d111800c000502c11282281c8427016072001d105290000300140091001c0900c0d8580104401c000d43e032084c0302c0b40310320990364016544603024800c2c00c210003411034180c284084c030302a0028500c00303603020005810540d00d511024200905903120384400c00c0005450032026450b072142c68060709101401e40103400110400503c4450101080400c003c0c1c00f0000320f80c40c0101c20340b40010291f0003131101001d0328202030003d450707030300501c80c007000705003c1c1010070511400402078600c000310f107545103002c15240c000c00e03100000000e09855810541070300b07200d65268050303140c00300c44550202c0200d0b060142180080490300107a02c6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 883017419 1250 883016169 883016171
    0x10c0e010503010b1e07050a05010f0203010e070e011107091a0d170d061a1c0b31051303110c06030c0c0708190c0b0a02150a110a03140a 60
    0x10a0900e0703810000781c80c15035008120300c1d91600725038100c001403082009060181d04801160340003c0080002d00c07194118802c000901c00d01b401000040140c1c0028058200301511910015220901c40d00000344175440524201040003003099006081c10026000281c0007621b84150705001f0141d1620f58603281d400fa104601c0f548001c3c1c880e40d0801d01e0404220300741c154000b170501031058032900600302408a6150103410b41c458401c00c110309500024440104009249000e61010314512410710f8000004d481000750315900001c17105046a44100220380b246403c0c030070070424205100c0c0520858020440307003c000e03000e0034058080044030046500c00d82c4140d0050403142c841c201901e0f0040b1030b0f0294144c4490304404240c0c10081560401426442102d004090f21a202046c10020501400d080c0f6007058135014a1000d92181094000c00b59101c0d80c822403401d0003240d1a90307440284540d00084052030102030f40b29540c07290020702c002036103da00c2003464001660103e504940b100034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 883018669 1250 883017419 883017437
    0x905030c0618060319051005091b0904020d020c0d050a090e07050913090501090c0504060b0415110703080301090203010905091603081e07060e1e0a111f0908010c 71
    0x12040c20308055004030b503400f80e580030020810054000203000c8080000480c1482a841c0c05440d810101d00390b8850684541d100c040410426254241d01005815904210510f400300714820b100c0a50f0141d07804a580590030441c461182000784600000308900c1e9545c259140c034600070040c594050341d041002c400280d50144146079400c041100c501c810309a401181c0c0c91032010b075841c01480c60b80000b07040c6500300460501085041c20141055581c00c03a402c01c2070300c3d110044604d150085001d540141543c0f03070a16412180103a440800110792013084407000e40d240c0e91008119042a405184081c1d004001400b1a03125070240583c00b1454200514610016004c0149203205034840a17081c550005203c51440000d9844030030703a0040d00e01c041e503a8601e28a8100010300602c0c010320602d00170040825200d900a51003002d02020301e100801c000e0349152207941580c408211025441030100079102401032103200e110364844070680381c40e1409490904030900b512640d90304802003040641e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 883019919 1250 883018669 883018687
    0xe19051203031e0a0204030b0709090f0b0d0b0a0204030f08030603010c1d010f031b0c02031903090e06010c061a1207050618040906022715070b130606060905030c06 72
    0x10240003103256200f82c1140943c80c2d085250009219540000d07003603203101400c1042294029104008880c84031a0811181e4001000d850844800021f03443c2c2c029240404217012541c602e04103a0010300e41c01c1c00515050380c80d0740758620780724055400c603244000842005080d280178450380300083c00500703001d002e0100c030750035401c04a41d8644a03181444001110a05002d200c1d1780610503810740381c500905e0600403201e020b0401680d01404038400d10a904040029104809210800716810f448900c041030400c81c96a510350401040c050401c4404040b0f03d020a4650065442e216801301030410072100030424031281c440c44084e024200d5100b010304000a03240c81c0304032030850f01c120150060701c901da8400640138160300140030b41020300104503108210303240019000c0103510a0407110400081109001440c46c980313034811403202d0306109403008108545509a840304420400f1681d400c40340e980e0404a4020760070010000c1c034042400d1149040070801e1002150040781c800342060642 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 883021169 1250 883019919 883019941
    0x90e040312090f0c080304180b09130813060e04183203030405010c080108010504030e01050c0c1f0f080f01051210020705011a2403070e1905120303 65
    0x3141c201c0d088580d035802a034081c04107407044445200d51040b10080082d94a01003281d40707402038001c841c0d14451500c40d49000140c0c030700c1010408503000e8182c08059032602c4440501c904010b07410781c0c00c17020030042e118041d0140000c1d00013a092680314003400c84d0f42001844100e8000c000b9006543c6103814604007c00c0c0d03015100c00e0240c1c1c00c15001010311105c5081c0340c407000401080d180c220310007c0244010001c1c19000200b900007955142d0119a0b40c61859600341d420995029000c141c410802c500d955100d071000b054400b40c0013040b18951040e80002c0b030801d07000d0f070390b2806a01c1a00760340028026030140f0b07008899001484e200f410390501c1d520340008558107104891107140c0d00700511800e102c0500c07124012003100502103460751000d00b0050b010b000c0000c3c20000d9050550712201c02c81c03910548800000544016100d62090301d03403280c18481d40003401d800244500c4100d1810366607139001d46100501e0400b920b1000d01c5282105010f00e0801d0114000460307081401000610418 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 883022419 1250 883021169 883021187
    0xc0109170c070e101a0c01050f010b030a050a061502010608010b04020a0e041d0307080c060601260c0408100f1d030f2a060f01080d1407020f040c0c03090e0403 70
    0x542071102c0420b480d080c0c412086840303280c0c090041c540350f0007100d8000030340031710103400d0807030b000c400034040d580e030310202038084900034064601c00c50000c0c00800d86c0c06041d540702a912184a5030700092180c0c0b44c2ca440c1e40410019581d9600503034440800b0b0115070004e018221051205650940c1080e0b102c00020300186c0c10014594020342d5284488482c003000204651503078400311086e01d035070f02c0c1503082c9180d80c0d900c80384069065215460101b129544102a01e14032142d80c5681040a4890400c210351222005400384141d140c040c080401e40c000c06124440301c00c0b01004000a0710561421401d090b16001c140c0704420b04020440000e03801d102100b2107051124850742207581e511520b2280b0721030203019080100c00d000351201c0301d1122000003441802101d130703c151041960791300c00000e60345444182c0c4140008540b031040704035078048403015125152004054a80d03035029a80410304952503521958001100c0c3e00440d421b154120388110050142010b502880f450f0684001c0d0607540 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 883023669 1250 883022419 883022429
    0x3050118021e13030c0509010b03150d0b07030e0709020a0e100c0803040c030501050a0506030c011d060f04170d0905090a0b031005072a030c050f030c0109170c07 71
    0x1400103050540307181c000c05801106010002c2c401d80381c0000c844a00258460b901003140e01d58901030010810f881c5c03480c40d050403560b4070044145075599540440c0e000f074100b0408981c01100c4203590303a00080846464910131501690002a0074001140f450310380311440e840454003a10402402100c540e00045854a8a6040c3d88000340b070300c84107804603840c0c1d00824000c1c1c810303100030003403108108044c9010f101702d902480c028130070380c0c0f01c0e200e100f01107500c1599956407691100007a03606a5002d0310406080c6c03520200525160034005000c260258800c0a4030350345003900060612620408a2503030b01d405049030001d046042d10000090720310105400ad492003070410000182c5c40907180d400be65880000902030383e40f210120415200941026210342c0e02182407405010180000036500d91803610400044c4008448252000d488207082c409081e82e01d405521040a400f80040001342000c03046440006050011400d003603803600d000000c3d01c1100ca01c00c11003002c2e051000210401590 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 883024919 1250 883023669 883023671
    0x12006072007080d0e0913111c0c0f061103040b0d06031e030912050a2006070f0308070906080712240f09050f0103060c02071d1603050118 61
    0x76205407098004581c103031400e144288100d18010a00c9900810b805071850b529454800e9408001000c02002c11411160400e64192440c00755011030b601c199681c11146004c0d01e8000007040c4c0105190035180903507000c1c0c45a0444840401160310000a02030003056145406402142c180054988030701c07442c4101d80510101048804800d042980a440250744c04151140b000c652044003196900c40d41c0c80640101d500c01c04000340c0e0b482281d401a1101d0b910074007520303801c4c41c00d44d150100030003081c2d0009072440030880e8452103500d038203005080d582d0280401d04110141440c2c001e08401009240c4006c02040320010001103402101e0550030405508281c25100a0281c03807200a00c44661215030844034010000c1440c0080c61645055501c500b1140c00410344540254003078420517240c5145c824841c00c01000801c0c1282e01074244400c2501c15124400e545510070a0002c1d280b21a6011540d209410301c2030018031100301d074110307402c0307814140507540c50003962820208412490010603 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 883026169 1250 883024919 883024937
    0x61b03120c1d04050618151305092b03020f160b040b0c09100309050a0b0109140108010b0a0303120e0d03020903060a1506320301031502030103020d06020c240601200607 74
    0x100340a43c400891151000d894070b0290000040b4900151000352b410304031602415030000712200c0350f044a50b510540032682c5003e031803110380c001c0303009501024800c0003100f0b060000524a02c08010044901406074080300c2150a09040004401001170302c5110600000c012a84140d19074400016100d052420f00140b90072080c10424242071128000903d002c4c0310354004074040c6296407183c030b103036541c50303000070020f03a2215260381c2250804e61815034030001e440402c2000a20548a086003016140c1c4042044d100015505280036581610310020a8001c280f81900381010022540e01c000310150500c07441c560b000c280c1080d80c201e80500b0007007200ea03150301d01c1000c0845000010012040704009d070350601c00c2c94a035100e074000780421104030746408040c0000c0302d16402542d040c0c030380040038000b4a8400d2313a44c41d002944a00c3c100c6a0301d0041950880101b48007070000d91300500d400001810525109000410f011020200740b449019903803803401030900c0009240740e0003c1d09082031418 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 883027419 1250 883026169 883026181
    0x10e0f04050f0d050408120f041a0c0708100c080f040b06010309021c051212010905040c0b030f0711120702040203040614040312060609061b03120c1d04050618 70
    0x18400040841c80d11840f6032601021007a6021005108641c800400e6a10741c00e800c0490320b00d00c2c818a42410707509042408140010700ca1092415841e00a00800307924000c00194030508000e407a502c0039442e600041c0720b400c00000d441c0100440c441c428500080e0301d2400d094007803103418011f070020307142d003d02200180b842d9000b5442942d682c0d4006011440e803054004041501425110089507a8000c0c80c03d900350794405036080c0c0e240fa01103011403443c61b070b00304011031004282c000c00507203400c441c5400005850b404040250700502ea4002445002c0c034200001500643c91200d1400c1c00c0e03070202d4850340c092031451042e1620a43d0441d800b580e40d4549040c0940070b407405190002c28000e11400340020940c01c808440c520b5881600180003841e5100d1003925040518441e00010444805032056a0740041c907a1130708080c42070074908488071000449408884460a00c0c00108031542c0110b48002d0f4090701c2e018185a0444060107030780340c80404500b140004c450042c500e4100c1c0408108 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 883028669 1250 883027419 883027423
    0x80c190305070b0a0f020c0601080f06070207170c150a020106080c0303091302070501020f030115020120070f080a02030406090503061e0406020702090f1501030e0c0121021303050d020105010e0f0405 87
    0x5c0403044040155102c1c44505046900d9280a00c5030420300c1c0b01d00c00b00418800004035105102d41c10036006000c8e01881d2000306122185111130302d5415000d1254080041c0e694039400d0a5607501d0f5240b09905e802401d100070f42190b0080c0c0101c1801d9020b13080c4038225560010880c0c0c41e801e0b007906d440f5024a07080070b480c00a8010300038001c101c2d500125410003c020108069412540701032281010800400e5041e800c0f9060320340b2101c10360040b000c4c4480c505980034005c080b501e209101c201182030720b90308c0314503403500480100801600009030411020703501000b4007014040480141c0503500340204141d07044c2c401000881802110200040d050240c1d03503054030301c1650040c09050561a280c0d401d41c2080c201201d040d1200c0750341000355a140e51282c400c60424001090042c01c001703680600660b004d510b640716040185e181c80317180c5050b0311902d001601c070624000040d80e503607904510340542003a28211240c011685070100405c01c802c440d00b002a044062107021802644540c01c040b4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 883029919 1250 883028669 883028681
    0x16180b030a080319140c070206070f05070614040e010603360312050f1b091807030e1504031206030602161103150f130f080c190305070b0a 61
    0x25a041c080c1002150602c40002c00441c400c0081041d50000e44070448004c0f0100d0700320b0005c881c041c07826003000401e03200032040241100d034001460703d81400c000d41c1c0c4107486d00000840480e2543c1002a0410400340c000a1a40f047c440c0704100c2402c05050112403190f21005120b40801c16803100820a036110010a034001c4000300e40092041111040c00c0d000e080c2d4000e1001140002d05841d40240208628850b481c000c02211402c004c850f2034605080307170050945145032085c4c000401c052261565980c0c0601c0d9401c44415001040d40703011b00c006070455000300351840064001e5102d0700c0841d03c40000c2664406d9260070400c1410301d80448a40090455400c014100c5100144000e4403800c0044850085441989000c3c000040d11092680790079050202007822130007003000c15598001c100c105503020b03903c05107a8062600039242c40c0c0355043c5600d01030b2402e02d00041c1d01ca04a00003844580318034007141c12020301c042c1071a03600a0261081e404040c2c01119200007003a002d40c16038003c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 883031169 1250 883029919 883029941
    0x60b130c0221480c040c050d090606030501050609040c1215020307020c10021c110c0607030f0e0103051506310e1b040506030a0615051b1618 62
    0x40010003900304801440c100c600b0f002c5000030140c401090104402c0301182200071400103030100e2081d0805100c081d10b61440040309100b014401d8a114800c948121515180140004103040d4034600f031060846401611203409a0070340c03400c000100700c0041d013850894101091640420304035040a60368480c0100098210342c1c000801e0010942c1d000482040180048404d100414800c43e800d0342d503160142802c142151100400d81d020368042c3d034108032162244015250702908040000754141d20003034040303010680c1101d003a00140c1e80503c10300c40441003800c08101504001d85025048041e0144403489079100040125401ca01c658a201d0703c001d20241070030401d4107510b803e000072204d50040d41094916800018041a6244100c4070b0004002c034000b17203003608100c00c0c80650380c801814011110b80300e003400500381c0035410344000e86d900196595a100c0c1c0503031004142e90f0b0403620031003405074014004034240e040d049078040304441c11740d41024603207500000e01d00701401c15041783c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 883032419 1250 883031169 883031197
    0x21c020904030c02090a0c02060105150904090308071b0807350d0f060f03080f0705030a05090a06030b090f09190b040302070503060103030f05030c070f060b130c0221 73
    0x1407104040d00809809800ba01c02c42e0050034640e60408030808640710307e030000006a0048004201900b07000102006402c2c0741100c070391404180f1008541583d581020880005007110100320320668842075413914600b640511810440e02500e85025500135910050440c07000e84c4211155841000d1200e130b0707004903003d0000180610060005c0954014100740801c850801e004005184010b02c2100f050314003c42d2030701002c5040d43c0f1441c000740c01c030b0000e1a100505c108003507008a482040903120f0710016588036541c590030b80060000d0201c1c0e99114030149410503006c980c03646c1c0c901038099440440b80d1209140c0340d07101d01860340b1380030003007600e00b60510710501c441c81809102d040c101c0c483d6003c5e408466500790f0369418165542400d20020380040c07111034214034514892001950003403403a00c10f490a1540c0ca8a8502a649504404480843e43d5404600c00d9050250031031642805a6400704180791003038401070348031000d4040c1d6125004200030154801034414007503500e0310001c156 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 883033669 1250 883032419 883032421
    0x10c230a120e010509011a090114010201021e0d11030403081f090603060b091f230a230301110d2f0a0801050d02060409022b0204052407021c0209 64
    0x907183c1c000c09040d540742a80703500700310100080203403d5000008520000d0103040d0560300e0140011684030352a52558110b54082080c101c804100d0a146d00d0ba42c02c1140e41c03070f561040c940003403100b29090460310840004062081201194002c401c4035031007400104014072210060100b5201a003c81c0c005030845498900040b01b880015440200d4901c03095440c2000b0741c40c2c85417280525039940c19451800c0840060501c0190302c980207203d10f80249804a4080001c80c1c40003d811144903040807000741000728543c6072062202840e001404010f5000300500100a0740c00c440c0362003182c540182041e00e480ca040e200358480701030300111565a40b408100f4408800702ea072a84c1c0c1c07140304000300007a0030f0300c008510703450450310f020340c00c550080c25145060728240703468010750003d00104024205503881244681003c0c888001015680d010040c3e540b814201003000b00081e1214800380262203e07003540340c01580303d0031110001e804482521859107415000e81500d90800300094010360307510 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 883034919 1250 883033669 883033691
    0x10609060f05090c0910020f070e04030f0806030705040b01210923060609070c0c0824090a0f050a0c1805070c0b060108100302030601030b0603010c230a12 68
    0x5882541610208032015541c980d03200704110b41a00141d0380e43c111200c0804c03800c00940b4108001c2d2820003898019282030100c516000341c10000e496104130400034101080200b00b513400b554422192000c0c1c2858101d07801d00901283d2341e03c41138000c441c01581d0341c070b801c1040b60b801202099000792030751000c21811103d13544008042d029200702100da00103114052030040c4603030511210325688800c010425992850200284084090102c005015000c0c2e1000c0c00720b040300d403805c03000d44038040007044401d00400d01240e408803600b9545d05070309131500a0020300107000ca03e070f0b0300c8641c0290258243d0016804d09905101501d00000c1c030a4040d0300380000c0d208083c0d403007c5465008a502004143c2c3d40342000c0e42e422100100090041e00c80c0c0c00020125030280c01d01941003502d036040c4c2c2413441d8403640070a180000a800544d01810303154200300e03e510b000d000305510100e07240351800d00725003500089640042800105c80701c044010a410045602c41c100700d01250200c2d110900950201d8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 883036169 1250 883034919 883034921
    0x2070c15030f151706092107120215060d0b01030b1b0a020c04060906031a0a1b0206270a120c080a11011a21030d020406201c120e010609 60
    0x25100d011310086070070302000c0c2d21040115000e44038150410160240c006800300320107041403043c8280740800c40c1403003600003150060b0500b00c101305264004020003106407402d010310314801800c09220b4082c600d20100003074100c07440c0d030b41113950000c035804c010380760503d046640c120045d026000032980820300084c110743c000f9410180e04401c0d00c0030000e031921074072002c064410a000150100304092050745182607400301e04d0394071111041d000103840e500211822002d4a000d966000140e1010301845003940504204005d201c040290103030003042005003031034542600d690090241c40313503000001c81e0940584454040d030b90b40700306103036610882400d01812000070201005500e41c49d20100e03401c04090000070410003d0001c0c0120329072440c0c41410b82078240102c0c4032000c503010501c50060140030b5070015001911480d04c030791940046120030715a1841241c0035450955012503e40810817030480c49501c00c203101072800140e402c9482c52102c2c05002e01e040390f07071480d621b4440001408141 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 883037419 1250 883036169 883036211
    0x304030f0c0905040c0e0a1a0d0201030f15080f0309030c010507030c020a0306020a020f0c060409020703091701052208030402010c02010216060203030118091109220804050405070302070c15030f 85
    0xe628015403a240c0411081c121000308c0030142884a001c80702000c1460020580d403800c510514000c104180600105030075120b100c3c076150a140702d2898103004010742801201e02c40302041c00203504050301180040d607528a42080349052040c00101f24092501c42e00c802000580c0152039880340361794a141510096214580f49001070143e610003904029011510000034075005008030706260411142400a502540c0100c0900440310300000341c0c41c40c1c1460500c04098034000003c0e4a03d07083e05d5441c0201030a40c050030804d81c04901c004005550340c81503036045902842c2c02080002c2070b01c0140e10300390b0250f011410310b1070307101400221203030f00200a5050340c0100707181604052410201c0300548010a000804a0124000d02035860074045000e59009007080c44c050040c0041141140311348044400a58000f0800207060241d41054024542c0203029854110720340100b544408400800070700079442c04041854051003001d02c04c0c0c00500b0b01010042c420080420709180142220030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 883038669 1250 883037419 883037429
    0x1a030309220525171602010f0510050901150903110a09020309071703070209041205070f0303050702150108060609040825021201060602100e16180e01020901020304030f0c0905040c 79
    0x2e41c400c145000d45100f10103074072130203011080644594940d0a203031200c3c001142e400601315076070749a907044d541301c5038001c0c1c034041c0d066130b0041c902c0d03241480c2c14050300340c0058115100001030040748000042d03000c4010390490b1340001d10100d032103e00c6800284406910750107142c80c1400402808007548dc040390080443d022000d100d4601c071808014261203010b0340f100654090151030025010803045010080e02e10740902d04140380c80c65136500c0000690300f510007a4002680c030010000d40580410041c1c0000340030081c3d10041d9858880100e40d0740c500141618041c000900c085001c00080d0000d88003c400201000905a00040301c031003140c8040c02c101707a11400350028031501c4400184034032402e41c0c20650103000900c00e0b86200720094200c0c02e002c91000d100320304800504d07502c2102600d002c2c21104d20b60402d40c0b0303880c02200054800903580c0b00256481040380c288960f8000040301c017202c0e400003403040f0080160900300340039010340d0f1007480007500340000c000421140c84042015a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 883039919 1250 883038669 883038721
    0x3040803180718050604060305031207081b0d020c0c0909030c01060e250e03010501260705061812030403030c03170108070e0c0d0e01050a1a0303092205 67
    0x340d081076541d607291101d210305401118982e03c1d44011036143d4001300d502407030140c00492078903920790320f0900d5540403031a000381d4441000c0507c5201944102e88039000401000315800349007400658640750301c1180304010500d5400a80348110382401c2c88882c40c00341d0300070145401c600c0c090000c40d8503075010200d49172195103403900100d0984005114030340542041030740d03c03a400d603403546040001c418503c103c0301481116036440c200b0341c1d02401881e0280020b909a40c0710440b008001c2e518490301d51803107104c50782120034180402c2d00e801041ea240c4d88180041c02154a010101160b104000040740c0d000ca40800680402030640021284000e01c2c420b585030f0a03825400e01441d48104400c0c056603a49820600e420400004003d1005410026048206143c40038030950f880c11602142418821a511031042140310601d40c0700300500c6403940c2001d034025281c840002900d0341f0410404a110300d2411244003440d8400c05100f001125140004105c541400c120402042c0c4124800000c0a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 883041169 1250 883039919 883039951
    0xf08010c03050408030a05040203280b0106052106040b1320030f01030303051801020a0206150a030812180706020c1906020c0904050f070b0304171918030803040803 72
    0xd188248509445950014032040c02c0d502c61b240d40380e021301005082a07902d031080d900c0038400c0f02124000100300a09000c0c4030303c0c0d00311131498600032140d0b05a10440500c0310510400640541ca801450102d441c0e040180c0401c0e990301002400400380e40c0409600050080e50305100c03603c26a1288100c803800240c68007020300c1e218000791251000f100d1540074007825100400009020742c101c1508003032914010a0520f0b050203140e1708a8000c44080401640150180301d11104600144110400159200100395003076441d401c4e4544551680c0307140b084000e00004000754810343d8040c9240030f0307010a94001b29074680e070095464400160030340c17117444c426031503c2e15041c000743e0a9048481d0313500a011a0a9030780c080100b00d102c010010b840d2406000383c002c0d400d0006000920140c1000049684c503418039040c40001c1340f62102d071604122008220080381661502c1c4d45e440100101d140c031000500b84650018a0820035038001018604044107010421605034080c521405040b1a50f10b10 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 883042419 1250 883041169 883041191
    0xf18150f09021f2307150506011d06130308130909020d020f0a08071205100603030915020a0605070807031518020c120711031c080726010f0801 63
    0x1200d000c1080254014a460080c010a5038074001400394441642800c1c0403001960440d01400c0c290440240000c4100107811400c1003402c907285800c017100084208002d242800c000303420340c1c002c840001a000001d022b0519076a58110899030348110551422010360383c0c92610174000d400921b401c810b0380400312008101d00c04244108450f0a0f00180121840e880a8083c08140c0c900d00010540040d1080c5c0d02240e50241009203000030b0980c42a1032034810303401d003411803c0c0a510103e201c07403107040c003a04001203540800380e0f00c1513440c1040009e002c44e00f0041c0507454035035000002040d050600b42080402da402088040c81110141ca0074002c5003d6402d00050342d010501a4422040414488400c41080e0354090b0840311000c0045603541c84100300307442e5094000c0310041354221045170450700700d802e05000551101c0100c3d101000f5400c0028809444180000c2c449020040020004503030304085800e00c1419038804049283c0d03d5031500b42c034a003000e4003405007000719801c203404000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 883043669 1250 883042419 883042421
    0x702130c0f020c0603070e13060618050607110f01050c0a030305151020030903102003040302071208161202160501021911031207150606050306040f18150f 68
    0xda40743e004103054515030391050180c2e402648030402c641c11545819010300020001e200d03801c0a8a59900e988010300101e901000707040d04107800290180600380140d00008000510184a00508940700000300c042d41004841c58014151700640c90310030f1841c44000c0c5501603000f81e006a441401c0310000fa0124828450f220410068080014a4040c068140c610310381d04030980071404401900d01d801010fa000074030704030f0103508030602660760700e00e40200c8a9044e5a00c0a4080103500d41c9410752500c1d031806501c9a0384c40c80340d41140c41c3e9841d4100b04105201d0b04542c1700002d0703110035000c814450b0401400094442d11007501500c2000b1282029100b1168408201d40c030503402040710705003600c9100813403485048203d641c20703175040d014100c55034280002014403149199091312510030f400c003422044100840c1c6074202c0c2c508207051040640c420101c0754444c40a03a40460a2090092040003c08140b4801078403000c0000c00b1070f0800003d441810301d1081c2d0514203001c0d241c3c0c0280808 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 883044919 1250 883043669 883043683
    0x307151a120d0c140d0816020d080a020304020607020a091e0b030a020f03100c020a0615031a1302030607020c0a0f051c050f030d020703030e12090f060702130c0f02 72
    0x70340c0769000c1005000a2480350022291061041c0c1e000764102d09102011460104980d1000010841d007600b080207000f44c110751940c00e541c01c0c1c0300a00d46d41d0b0070900d0151000380040d00390050b0640000000707095440382c1c1c04481d105603002d04198045a030701c40d0408002c210000f9050072455000000c10782c410381500828010260050180c14141803942c20032110030b000f02075280e0907000c1c06128266001b594400d1020003e030507000303005100050b1400c40308039a104040b032020407490360414008503104040b405141159541003422544840981140084010800039414420b500801111580c0410400c5005030f040c2c1e500708050b070700d500025034410010f00559030014441002d14000e00c521090305054240a40e056584504511800a045a201c0301c410a02590002a020101585403080c0c41d05500b103480604400d4002000020092003000e4080e8499000d058071036000f0b40d56601150661540104040300c411040401340c4d0150004a444d03c01207046c42026621450001c180c0c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 883046169 1250 883044919 883044949
    0x304020f1207090f09050a050105191a0108090f010c05180d02030312040305120103110111030a090618051306090b03030a08061017190f0608031207020307151a 70
    0x54a0020705106245004004842e1070406141e00c5d484802c010038003e10806c0411409100040340a1400c3e507001b0714400008102464990f103022040c8002c00d0151344054403403a42481d084402e9101c0240c06c62800f0264440201d05529003e107810216810034021300041c0c030740350740880c80200e0010412440c400307040000394150700104906c5941980c6082ea40e0f6101d882801d00c03508240c00c4251012105000341c00031164000710400c840c4856820403044090056014000d5107002e100b250700900c0300400d413241005000c2c03442c1880c4000c84d00003080d18050304014103281003a00a449540c1d01809aa110f07029815103840e41100300380c1400310440d000f000042d110540c0a4440c5024040d494405000a90400c100311403003404c0700c07240d044c00301c0c001c001200c0500c103007070b03821002a0102e84400301c001c0d0042e0f140c03e070100845000481514000c05a041c1001c0e40c0f075032080803e07420751085c050300074089410242038642c501c2139584042d1303d5a441d44001c150444c03d030001c2c0400d85a0750300720 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 883047419 1250 883046169 883046173
    0x1d012103020a0b060a120303051b0301080c13020f0d06140a0f06050f1b010212070908150901200c01060e0106050403080703030920011d152d0304020f12 67
    0xb224010581d030410b45600048043c00c0a00f11655a1040e03080d0078500800441c0000d4a0304c082c172045025050002c1c40300c0c1c560083c0300d451545806c4c40265502500e203c0e40c5c0c050f00548600b00803c401c10f03410f0318406001e004001c0d03550044050250002d2400e4042d8140c20341c0c0b895206003007420b000310340005540110500c86507081c20a0380564184c1c04c80c0104503070141c420044101666505500380804201000006da10780d03410f200300407800c560040c480c0c000c2020b10f0b0402c001c407000010b10718000058031800010613031150003409000d030480030100080000a04101e1000d200c0b07000c024005064210000c00c0901e8985543c00c5021001784510000a042808107102089641008011480c8030b810001440c6040d41c0e140042c42c03c074040d0324030050404069880703065800c049180f01c11020030780d10440303e801d5800020b40c45040d6200c035074038a00d400700c0c0008100c481c031000e5403203401d11050320502c008180034003500d45a10071a4202d00602c0f20b6020b124072030411008840740000c003000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 883048669 1250 883047419 883047433
    0x907270e0106051b01182001021f0e07030f0c081b0f03030706090320010b03151f0b040303030606110c040e210301030b0115271d01210302 61
    0xa086403070b80c00c644c00d00042c2d120504003545000500b4802c0340c00c0b4179886c4800e100789000750300700065040c02000724000d641c808104150b0103a039001c030312580f040c1d003062804103c0722a07070310544005042d8210780d68002d00c20b4420100612201e07280c000020303442001c5041e15140c4464007603485408014815450183c0ca1740c0f00340710791518000b400c49081340581102c0c103040c180d440749803e540840005030045500da0100d002104c07444c0c4d21503443c9032548030090007210904000700c0d0761000c0d0b483c0540c0c80102c1ca0001300f00b500304560303290940340f00013020304048103449181d03403041e51f80310344011004a0710303003100005c6e098040c8070b24010f09140c04000d03001c05282c503403d20004c0e101c981400c0d04203014030001890b091508002d510808440058403a0700c0b036040d0714040c5651901a00444003050880441c27201c010380c0018034079404442c83c98160b0884c0e03051801401403045a401c140008076035030031140c0c62602400465412140700345001c0e5031100d81c0d014007a00c0300135003040280c0140c201c40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 883049919 1250 883048669 883048679
    0x408010f0c020d020d050a11030a03270302060f0414060408220e06041d01061205060a0b06030411060702061204060c09060c031d03030f13062c030c0907270e01 70
    0xe001c4200203408c152032882c0031648464207540c031100f4004042035445c0d500c0c00b0b03207620400240025800100e541c02038100c00c3c0d00d001c2d5542c00014038074100c19503c00b0000d000c0000010110103828030410407520a801c0c10700e03141c01190004911400d40040c02d020000d034042010300b40301c04880300072070990b90a4a03510144006001003d082c40a100d51800701d2040c141401d102e0703603005110034800c20001500624106040c41d030301400700ca044500f0b080c1d6060300da6403401b0032260815406401100d05180c0c1c80d02140c4240201032011754010000718001e00d02818a41c1890f22032803082c6420802c4409080302514030541d1406250f0001d801c5540c0c040010380501a402d50402c0200621070b8034100b00c0000901d103500c01803c160b0300040100356900344109800581003d00780300d0a140c0c0c501d001c0ba0380107050a03480340c2034500c4407a41243c2d44090341d840900032141000c901500004080c40c1c40c0c50013515103225000c19101c42020b801003042c444400c1d40040058881c0c1e00c00b4070802da4a81 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 883051169 1250 883049919 883049927
    0x30d09061b02030717060f07020d0c03020a0b040305180d15150e01030c0f09020406050a08070c0b151c08070f0503300c0a020a1b0b0408010f0c020d020d 67
    0x2044924074014404416080541e8081000600400e24080c0403210107501c2d2496600b405005004404010002c40c14050510340100390610214003038540ba44910f040f60604030b2402d07071070010150544842c00e00f404140765114000f000c4007103e010752150360110300820300035425008d201c098610701d0351460700325480a480e040461001c0c840701c0c5c3c040d00203403204002c0c881c2c010300703900c120b40e1944003040400a400c0c0b02400c5100030207059004604183c0f074400c01400f03911551900c10100304007000044c44050080155010540e0030660f460703494039150052078403010145010302e11030848001e44180712500c600401141c90b030700005203403d011a43e80c441c601c07000541800c0711503000500c940c0c5403004a03d40c4190548912140c119807001444c1d207101801b0b41c001d01081742001d801c0240500460300000c4400c15103603c41300702d52801c0714106000000400540065100c10b46c005030003d00010305420030644800503980802c400c1d04000426683c60118008580c090b80040401d01e107642d0003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 883052419 1250 883051169 883051187
    0xf090602160e06130e0d030b031903030f1b030609150b0706020c01021207090609170604030809030c012a031b140d050108060708060108011a03040f1a0a0506030d0906 73
    0x545035640000c410070462080e02e0f000c1d000000c840c0d0000404046c03080d4180034041b90700304190007031701d0022854220180c00062000c8040c09241c0c9030034030940c00450302d6100d5100d000d442c003107402e0181c00f40003005000e060184505407603507080c10780c28540110032218070b008440e80381c0da138145014842d82d41e502c0030350841610076070a958240300c001e00c0405180681c41c072600095440303003111420001c000c1c10740c20290304082051408035a1010f490100081d24035045501814001c03d181d070f40c2a80240346102c3c2c82d039908415400c111070405142698500074600380001c050042e80c2007070411084084460025111714117081e071009503036006014103039030105030745002d000750300d00340e203106072441903620a901c502442c6e8803140c00c2040300c43c0e0104002c0d0b0040003d103000612549406001c55003004510aa8542d407131000000c07030300b0410706d540800241684011900700a138081c401d0307202400c008035104115541444001140b514010440040c5005191036280000341410000c40350656 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 883053669 1250 883052419 883052431
    0xc09061806070f0b09060907030f0f0219060302180d030519050d02040e010302011b02060910091e051201060302030d03020a0e03011e23011203090f060f090602160e 72
    0x1070410080300458003400c0c05030181400b4035449902803e0030641c881c0b501034010030000c000e8000e44400d000295904d400560b90343d8000205080420640c0002104400c0032402081904155000000c0c0b10b03405070007421035010142542c100004615007401441c002c400d41c0240002c804220381c040095810304505030641c580c1c41c0160a00d403001c91000f003240c0c4160003002d00d414182d4010821076a00c034002d554100181d9482c0e41001d51950b0205e8018029094480d00c0750200c40c940500440c400c092000003003c1403110b10100441510064030862071038040c880c0110800160a003110074140103c40851798007400a2083d080011b40860007500203030001ca04000400641511b01c0c2e809001c0d104a207484030304d60f2043c24401c44044c0003143d01110b0401c500c200e9900c583c29600c0356411000d4116001400c11b80312418451808a41030f80e81d5400218040e0703015900421215030051000303003004842e4841080298030380600b0380c2d84400300400c40e103030304507810010f100d013901203500b02ea0882 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 883054919 1250 883053669 883053679
    0x90403050304081209070e090c010903140c061b01200406030b012d020607030b0a09020c0111120105010212070b1603110708120105040c120c02100c1101050c090618 72
    0x2104c10302c02100b400e4107641050a82d0b012140a1010301c40b00514507030400100001086224500000605802114400900300300e90700009035642c407105001c1714924000080c11155aa0140304c01c10b020400b007443d041d800d40d031070040d0003000800001750302c0a1540202c507480741018903200007240030342100900d050403c02d4450208080d0007444254841c007503a0100691120700e0a042c0003440c15100421040405080c54035030246c0d03444130040300701505d00301d500142c2c0c1c484000c0d441a01401d0a5561890b101030009401591005100c40c40c034143c5509900780c070100d201002a14009000b03124001c4d0045a001012800a40c0c41c003800600e07182c511b0801007440c80c2c0c1060b01c403010b82c0012005485c0c5660004599000102e000764203030141038221402c1005684412000b0030154096540340b04070340c0c1d104400c0700054003c00c01503580501c115018071444010030402010702c3c110b050038103070320740c20403002ca00360922003000e5071580340b00645168180414461400140c4190038400d42d004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 883056169 1250 883054919 883054927
    0x9060402061b0c0901060c060b0402040b0a080411091317030f010608250f080610050f250303090201081e060d1b090603050d0513050622060206090c01020c09040305030408 75
    0x10b4070780042007802130142d03855403c413040c7d031f82c24007500f90364035160300910482c81000103008140d0b0803020740d48009614542031300355940d54900041d036400c0c6125041c4c0d02c80070b010108095146c04070a51042517200f42e81d46060150f82400c0c01c411070005444803220400410f005000591040c0c42d45544103130440d01c401e1300f0b0603000348082e10302c504070ba40150005a0316003501c5015a00015030540021003560410b5080038141e07070040c0140161690080040c0000640282c3c401d20800884814008100503030074140340c030303d40a4010290a14102d0210740c0810010342104c882c151040c2c1e1003500c081900d19955503072400c0108110b0a404112440445a0f0341c00810500d104002400360038030312000604103041d401c0003407400c076041452004008040201c90095808841c1c400115074013594840d807105030b10300d08419488072a03031281004000c84100025515800111a03008100b400140c8200413003c500482e00d03040011981c40d00610f43e1030110b40000d2140004560240c000e6440301d080c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 883057419 1250 883056169 883056193
    0xe0d0303021c05010504060e060d03050306010903170a170f0106230d0c09081204050d02060412060903110d0912050109020a03050a0507210f26040e09060402061b 71
    0x2207030b440301c0110404540d6800050020381420710440d0b016091008021000f03103084000500c0e0707905566070040c2003040100218105900809120b4082c591100b0815010460324000764410b411074008040042d0340c200002d410030038199081401410503c00300c40752071703092081c1900c4030503400c451202c035042002c11080b000314a50018003081c0b000210046240c3c541030f0002480060203400103501600150080c05903045103078111022504191140d1201c030085000040c454003483e80f0104030503403a1402c6504201a551240422502c252240540180c81c030681a03a100046a00ca00c08104020701c01d1058405245030325003d24450700c0042213009a560100364410020f52044030b19038091f02c0b5200411805022080252040380a4207540844003120012940000b9a0180c03400700102c4101003408a2a0346510003040c00d2003003620015002901d0140d10b030311901c108a030f09101d000c089480c40101095403400b40d83c009110a04051404107800c4200d6841a94920907100b50072410311 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 883058669 1250 883057419 883057447
    0x507050d0324090603170c0604140c04050703020307020714010504060e0a261009110907020a24110304030906080a09020a09090b09151f0806091f0902010e0d030302 72
    0xa0f00d01c150020400c1465840d080035030b040351114902c200c84042c01003400741040001d10b140d003e46c0060001ea00c2610343c8012600b490220a1800d42150420b420007040c25055002036014458503804c41740b400c0d07030741d2150a0750502411600da00241d01040200548d42c0b003140702d880040402440c3c0751340260380b50a114001102d8900c00009925201c114a20002040c49400b0459030130304010f101011032075960307481d109100341060340f0130440000820b0a0910802210340e419601074a1a103101e44800418a0010100c408400c2c800d8204144000d81e07840a000faa80155850b80300e986410b81440c0080c1c5a9040090019082035990f4016a02580d03442d00440700904988000148080250611814801c0d0084c2140619441307140780803a128007075080264000c010800c0c40004c54141c0014804445084d03201c00340a214850510904840200301c0e044100c40100583c40340c00801c2003c041071340c003605e80290108559104a58450800c503640d0800c00780b09140043c42c0004407a4414 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 883059919 1250 883058669 883058741
    0x290c0a180b12071b050604082208071e0806070804021813060605030a050a110a0306051008070614180607021804060f0207081603030e031902060105010507050d03 71
    0x10b541031242409001c01030703822803a4000e00032052840110444c85030b450b81c1d035a40d039000c0c000501522000a80160f1107501c0c41e0350801400d10300c08080380266a1300e442a54075034860041240743c600c4415030120b02c202132111081150000005040c00350307500201903412940c0180140e0f00648000103c0c80088103000c034051007125442c0303a032420340c1142c1c1080b00844000d0f41001e80a40d00c9038411801056002a45803011b95128000350210a0b5800c0810480c0c012640010700c0030f0b0070042400903d101e60980d2070282e070802e0301180d440b955603001c200c0700144080e002c408200300420400762551034001860309082000b0745001d152890b1540883d44200d030301c83e40d0303107a0341242005200800c40f04d802280c810740e554040031340c01c008803600d480301180b040798104410050540042800c06000f5084000824219001daa4030361110704145000b8404000102005004800021655601500c1501d01303040c3c00100a1081108143c400d03401021000501ca5121401060400a81e541100c0003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 883061169 1250 883059919 883059937
    0x40b030103050304061209080702130b0a0e220b010e0606041d0702010e0106050a0b09040b040203092b0923030609010603060e03070321020d0207290c0a180b 69
    0x110340c1c982c03a255004101b20404a901c00c0301034141001ca0000c1103c85099881c2950121390030718000d03143d44e4a150003882581151500071004220000c0d411400783d03040780c402c61032402c654041032405280768001105100c801840c0098640c018810b1401c1a00348540c05100901820718040e210350740b203048654541c2d41000d0b940c4401c0b00f0851080c1d428040c03c0d14081d00440207111030b504160006030384288500429603070b440041000b14103903540750018070b40d92901610441d40e908113041c0c5d00b40c5440140e58030001c6144242210b42c2040031611041c48400d109a80c0d00d00002c0c1040c0070001403c0d103032000c0410010105240e150103540a00000380a50900000003075146d1640c03800c0c0068640701c44001040c1d8109003d0f000101e03400594281da61a02c0f80c1100b0003181603080040300900803403241201c00d0344041403403010042841c3c1001c6000c00a5840891a1801545d60254808040390542911201880b650498a0150b50124030240805c0d141046960711510001e0880e0848002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 883062419 1250 883061169 883061173
    0x418030813080d0b030c010f0f050c03040e0c09010822140c120d17061f020721060e03160b060319060f1b140715141803070201170c040b03010305 64
    0x544d100c51904020301d2160681c02e0918460b040c00000d000b500200390329000708244000043c80d070b00718007014401c03a4007500c004605101d590400004010081d000316400501040707480b0f000c0b4400c074680380462040301075409400850210702e0380d07400007105000c07080d60300e86c2d100b44e44c4820601e82c0c4182641548034201001804021003844005004c84091441d5844000420042c4440c50321002e082600c5040250000210071341c074910120700e80301d01030317000c80203c07a00d440612007500070710101031042030302400050005040b40c3c0c04440c0c5038411900880100142440c2c0000000d03002a88a648a9002415075419804450600b9022a52440308035a07850383c0d100c003500c0d4403616108450104640410701803010803680f502500c0a0326a01c4011000c4501080a20421a100c61440c1c0441800320040c07006441c580720080c2c08180a070b41070042c107604508001c1c0d400e4000425950141d030140c4d210f012003402c800842c00c202c3c0b009071441045010811000c107240714464021030081d0b105d040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 883063669 1250 883062419 883062431
    0x606040507031812050f040e2d0712060510021f06030804090f110a030e0f121b0102091c06141b0a02071e090b0418030813080d 56
    0x8000454100800c5501414030700354008002403080d00b403440502e5031142d0004000d0404180030385a81c082c3e000d9440000c0700000b8086140e00080100c94024070751501400d00403007212644015600748400e0592102d0541000110700d00e01c1142d51015180043e000021010f4845012441c40308100040d40091f82c0000012400d0350111017043c106403040d01c00c00c20015084d0f03980d21000d48501c0c03142e03002e0036884000555014075243d10030f5480b41100941150340344110440540981701d85d0f113100e9800c3c01041c6451483c03c202154011080d00300350f584a103004d80d00c03445000062802c4c90792a400d99130a20200c41e140e15602402daa0140d50440200f41101a9103800d43c1611140c3c0d01d000008800c460610400440d805140c0311083c5c407550659031500440c001c101d2400d120341c3e00003800340846042500d400c411000040b0141c0d8600c0ea020302684842d40c00b44010384040c8400004121940903c060100c1c1c810040b16401110039090081034180c00e8488000c140c2050510f40c41307607030b5610 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 883064919 1250 883063669 883063681
    0x41718040e25080309010503070201180f02031b150a0c02030106090b0312070b15190609080706050412020f031e15150d17220527160306030506070206 66
    0x80c8010985140b845020000d141c10502207503160700071090941e05008011001c40d038458002c0d00841c0004682440400700801c1904010014504040c0f050303019014001c01042c022a60b0342c40ca070005071010b010b05400c1800300944841c1039018150b071600b041b544039800740c0141e03800e006642c024109140d0210305681c090003014109181c0800361215030404004035400030701c8070020f1a03408291010742201c140b503010f01140e05000c15121050f000112240046031580d081001c07403096807030a40442d010591268002d403854490390103101d60306502d0721b018030010700c0c200f00710881d42800941a11000940c64440900c41301ca400221411034201c0a60754084100400c2035079445207180c00e60300c44001c6181c01250300c503480442c0240100c0840221b01c80394500003400c0f9001450703148402c5540c640740140e0307034581782414080d6a01c20408854110782c01e031041e116242c003803001c216a01e0507549540f248602e52140d0210b245050544441000020581c140a024850b0740660090240340c9462 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 883066169 1250 883064919 883064953
    0x903070c080708151e060402212202010c12032901030b0105090d0b04020609060c01150e0c0a030c02010b12370b1e18060f041718040e 59
    0x41008280c904144070100907401c2440c40b40c0c0c075140c00c040c850340345c11601c8550200b0042d1080a070381d00640c000c80911640d50100f890141c61042417a5002411900c0c0001500e41d001840400c0c00703800200c481d0496401310b96013844c015000301040c180014074000350f800c503c4082d0740411804814070000002d00d5031030f5805024203d200102442c11900e00040b002c001034420072101406850b1460050014046407070f1402126021400100825240c50405079624041d105c400c4000041510404002401c150320805050048031558455800d2503d900d43c2103004200301e1404030304540d2140d0104180b91100240b409003014580b0140c0b91003c0520070035a60081c5a00f40c1380c0c100c1030750381d035180140310382800440c80e10307a44418402c0e07858a07109103505003c0c0c2c2c65528429080319500500c01020070110000c010346c2813802c2611400d0751503c0d40300075900400ca9000d004100c103840742e0003c00880d00000d01415a610030340244c10342502010500300d81e00200f01138450f601c0498001c4804105e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 883067419 1250 883066169 883066183
    0x9040212040c1802190f1814041a0f0910030c0906060807080606040909050709150608070206040209070804021215060f060f07020607020a03121205070e0a030b0903070c080708 77
    0x1580139803804440e90420381e1154002010001004018a002140940b00c0c40508448200c0c100c0c10400068440318203500111128078001d100c1c4e45000d09020907001102c0166480d120020081c0400444c06018404182e00c000c00c80228403034858404000220100c092001400240a00242e51801c00c14080c00480018180405118120080184640c0c411084406035240010003158020143c9070144c130b40007554000c110003a040420310500d00c0c1240800e05c04031a503641e04c0d0089500d50801c02d03a11041d0598010f0f42100c0410300182405001d00d0303d0b59041440940200c2c11072911120740d40c24200c500040034402c0d503080c02031102c0e070315142140c4500c481c401c1319010310309040c03690306108500c100c9400a016442c041b40c4503040d569644810401981c204e6100c0481c0e140000c4002c043c1040300388551401480d1001045540e807244810400c0a0406006041501d0850300c1c1d00d40c0189009040038628442000314800259007401d14000420441c0005d0050500304041c26080200c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 883068669 1250 883067419 883067459
    0x203040311160612060b0304050c01021c09050411040e091b0a05010203071e0f0b1b0304050c041d03280507051b01020123070e030c0303090609040212040c 68
    0x20020071103400d55160b80300302c003088030118105200c3c86a0940c8481000c2c0010b6440025074030300200812040c000d020860709204c4109031300340e50003048140b880d01000c0686010810001b0708260052009043c03035400180d540c40d030200c0c114100756460f15290700100f0116240405900086403401c1000c0030103030315000b06030045039020b449508000c0000e69a00030000050308176160301d01c0a4030307420f90072401c0c50444e40d007100e0318940130549070030070b003804907005e0311540103000400403040301c904200f00580e4015035029001d000d04030020390400c0047d01500b22120786030508400c045180351000c10080800e2280711b04a0200c14540782895400344a0101c034807c1071100800000b03001410101c0d29086440120310010051101140100d004201c0c00c05241c007400d03a030000d07030405081104200303803040c00582d40e50700c0c00c04004d500303150f1542ca514110903011ba01c02c1c0305a254a15008000d070418240280006082194001c200b002c1c450301640d09070b45501000f4400d00c403402400342c004542c18 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 883069919 1250 883068669 883068673
    0xe19060b0a0509070210240e0f0901051909031404121403071e03020c0409110306071809020f0c030a0302091503100e040203031b06060f011404050904080d090302010203040311 77
    0x200e40100041e48800c0c1c12150200d00c150b80d901c8202c00600b42081f80b4180b000e100c14440036040d00d85141c20080941940d0b1040d103100c008002130009070050180303c0c401e0a4281d4482c0d5600c441100e03400c054920f140c4120107114031702641d00c1d040c00c2503002030300007804d016200700c0070300d00d042c20816090880091010401c0e0810003480011035507501600600f000d1411804080043c1410201c0c00c1003001c4400f43e50050030401140700740311038946200c4182e6412002d4802540701e90344150f80c046103032910510fa014802800704842040e0b5805000c04d00ea0000f10702c1e2404c0c685400d40d900b55800300380104042a40400c50700541e003084c070308040c3d44c5000d03000c0d42403860070800003400609405105500410a158001904544040c01640c0103804200c030403194420300c14a850b500c6c0c4108403203981c000e169820003043c00390721038511100410340c8420306a1030141840f0a000250400a10944008504100d20b461703c0390140b1035603070440e00a0380016142d0505e403800800e0714030300f900c001600e9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 883071169 1250 883069919 883069921
    0x105090c0a210209180d020106090e0a0314030a0207050712121706101215050f030d1b031e0804150606020c0405270708010509010509030d0e19060b0a0509 68
    0x1204000b07401e454080d011214111076541c1e0020600c0134143c01110108a0b02a1030f1140030f00680542001e4107480f02c1d0b032014003d00503401d0340c031a85e4405d2050301a002502c02c1000e62010300340032004503000f03d5400800752522095071a2103180c204d456001800c44031a84c00c0c810f00b4401c010411152040007860080340071a1031240f000751031f84002d89101c1c4138111480340d1111349402001c0b509010320200381c0a110b05003021010980d6582c540c4990350241448840600790341ca030100d00406181c40b191100400502c04c2c940e40c0c2005484004100d061041a1003007000c80c6e00c1480040481d51910f60b030301c92140c034251070f2810905030b8540317480404074207110040c40300c0c81d00808c1c1d8506400d41980c0c001100e58841d0b0f0320f20a5828409044514003a00329040f00700c220700840c0080945407010001d10064a440e10240c0c01c951382201c180040f50001d03c804019507116030040c00e001134000044800f0344038234409040c1d45c0820424100c54041e0b8031030a0f0701c1e082c01e26080460040c02d08840a81d45 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 883072419 1250 883071169 883071209
    0x5060c0a2003070b13030f03180b04050a060e0d14070b0105060a030908030709060806090108061602010906020301060806031605280f1706011a12090f0105090c0a 71
    0x9a1046075259202441c40544040c080d081002540c64458020441c0070460510800024240310310340c034243d00042d4100816003007280603005c0c1c005089008034468000c6403180c0c80d45810300e88050411109400b9040c51200440c40d0b9004014000541901900101e0b1030100c02a02400407244c0c61031388400c0070710070740c004038050b0003086044650903520035650b0340880100b1402865510001800a03a0100610006552100c10101901c0072500d40c000e8a84a60341007004a21091184001e140c0c070080010724040c4a0464001400c0928000030400110640d00c45083e6002600312000081948042002030726040100c0000c21103015a50101e160030a001f29aa0510003a48a44000002c2103a0600c112000a10600401310704044881c40794689501f520300784194032440c402031050400106510180100c5c1a03082501200750616210f40c07840740301c0440000903e207585078000c10700e0310300503807400b030154a1040000300090903581052a080200d000015000b11100700d04103000084 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 883073669 1250 883072419 883072427
    0x106140403110f030a050d17130f080f0409050f0112030207090c050c0a0b0406050f091902040f050421023715051506070b060f04060803070f05060c0a 66
    0x1e99070454030b01041e902c2404081a101614620101d406100d080d12030828030401040251000c146640c40011400c0c03000080c1820040a8410610187d8810b8440000544140e070792507103584684a55400c1102050f9080c03003a80165005000b01758498040002410701404642e02402c0c084510918000460b28029035820443c0038601e84c00d0b9550101c020454060301c25246c40d181c40200b1200c208801d8035101d00582020350b400c8866504150100c1c149031151602a8811032517040107158001c003e250001115140300c0007039801559412007400640114013860b441223001741140780b04c45550151a50ac0c8088240001c13045401107103c8e461480d174090403098101e00d149103d4040712003103151400e001880d1000040c1106000500c141e1500c075150003a0744181002d01c03501000e000d2075000d1201c5031045040041216800c1c2001a03040d14044001a0082c1c1024000040c11078491010a02d0344d40850030988400d0503001030300040190030016181c0c0b08048151943c1070030b0300400054 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 883074919 1250 883073669 883073677
    0x50a0e1507140406180b07051207080f07060902121c08040614070c03030b010504051c06090519060b0307060507140c0a0603021c05010303120e010f02120609010614 72
    0x105942294001040d019445107840300642c80708082d0480d41c4a99070341d000b43c0000e520810031082e810100e0000584c210400e015a40d50a030000060306000d00c031604010507542c4001c03011550540280315108181d507001e005403050500c40c504c0002d09805900421084151011292082d9402408c2011050441c1d0500e100c11411908080d04540c8a501d0208046c00442c1ca4a140f07100301d410411030084d900c020403c0c04240a500c0800a1b00b03110401110184a640540c07900800b010b0300c6680320342e40344a003a50b4114090000081c1e4001660348450618442c10b0550010740840c04601d030030702c0780038407032480c2154088004010803450b00002030f2160040c004d001e003041440b40d03021264080c0c02d1002ea541004000e00c21500b107900c3d107401800a40020414181c040c1000040c2d41e5540103030720804d410307250503841c0d840c1114005a801c1018042e04440c021165494002c82c0e040c092450002d800341c6c418001c84411640381c00740600440b80c038160300003410000500d46c82c10000043c10308075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 883076169 1250 883074919 883074943
    0x2808040b182d030f0d02150c03010b0406050c0a1a0a0b030f070504050606040f080313270b0a120c080c0d081602120a0c0929040e07180b04050a0e 64
    0x4030000300b2120009003031090030044807140c4d0107401c820440070707540460714034203400003c00045010380b50302808242d90b000901403c03184002c01c1000341b2200b40a080580700700541542245c1a08c14280e4580064008440d95646488002400d10605400c1401075640d5110154000c2000302c4000c2c4000f6a520101d2003801c0c0266a0f440c0030803940d8a5020494002c1c00c464400078040503581e20402d662a40801b40c20101040400d0011075041c0c88480740114407104035003030302e541e80100741100004040c01c0c003c059200c00c1d40840001c5100baa4125140400c0c0984450700740d032340c41d001e403907401c2990505829216400700d0a422001076001425686040448056800305035003030b20108212071030102d0400f0051082c10006000c111010007102e090f0f030050242801249402c08141c06140e50072120b60b140d02d41802c05090131402d141c0e201d07004100c908412103114a0b0347c0e1400d03c4012101d1071200c0892515403c0549071801c0500813985c10001484c3c0c10000c01481c0e0700e0542d141c1c8100196 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 883077419 1250 883076169 883076239
    0x206030a09141b010807080f070e210c03100605100c080708070f030f02010e151f240206010b090f12030a050903070b0a022808040b18 59
    0x46041c005094040b859112002c070849403a83d42c3d050142c60010303038490304a4000f0380004000350806110700080d0340030300070f1154868480d4903508030070ba510075002c0c12010781001000b000a0000911000c0440d01da001240260400c2c90020051504007460400703a8403402d0300344041000640c03103080110617084050300c3c109401e801a494141150301c0380000151040a000c0307080c0e8240311a0703e0300c11050303d1194803031001600a540c0141e098848440c13096100f60440c0300a056401038403545035030b03c42c20900450115551034070840c02c0100150f00301d0320a03100111384815a800201108142c030780310a0000b42003540c900400a00540f00380c0302203900501c0014109903650f242d003141c2160181c1118244c9072030f80301840700201a0780042c5841407103481070a034000703211a001411101e02010300d501411006041810401190110401950306402e141d01e1010125a07814041c20281119040306a40c850504041c140030184181c0c3c443d115141c88141c13412915034480c80c00c00381003110301c8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 883078669 1250 883077419 883077431
    0x2215140c010219090518010e01151106090f100501080703060f020d050f10060e090a05180a030f090603051501030b01050d020f0a090608070503010603150801020d140105030a0206030a 80
    0xc0440d01900419052010451454468104090b0401d10020540f0025104440050103100a02440c0329007807058160146440005121080d000c07011203c140d105401c1903040c0e40510981d40b407800004492140542d040031106961484041c0716040980030a03200501055041954003612008244801442c09995420100fa42807054050b00e46040140e00104100c1c81c1c1690340e13090800b0100c80000c202c8501c0388000c100c10780100407950300e00310003a004207010382da40c02800b002884d020340070341b50104d1012410540083d0400984030401d1103991172001d070380308901d0301401e0703155960040c4051600300f41c00c0282082c0c54141550b1401024070f400b09904070a18016116440f520140c0c943c0c0900000d2040f40c100310769070090a0b03414182e0348001c81d05a8034081111115000e86020002400c20001045541c1c426041140c3c0001010000114590388441803030881e4006030f50708104c1919008083d280d4030003918902e0042500341c0103841505ca80da800210540301c024024048195616 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 883079919 1250 883078669 883078687
    0x1807090b161211070803120f04020619030f0b01030e0a03030c120c031406030706080c21090c09070509010903031103072913020a06050a020111221514 66
    0x144101c205281c020150b841180411000140002144949003805116107200080c0c800000001c41c0d003040203240810b5800d45800c85048100b410141003a41d002900784203000914220134042182201c031902d000400c0b000031003680c0b09a41019002d0ba061600c0c1a840b5501e2101c0480c142c180d06626290018030f815101405668161036424030f00001417a202c0d0614400d40c240d804403402213561f4034102c1050750b5601c10140c3d1068180200380005100c000402d000040380009032030a4402846604251204031444011080c0c086540020a501c44100b001860400c050959001107051405504d82401c480c00a0a0203a41d88401030130000c18080d40c1c07014400c00d0064600d0305500a40a01d0120480d8030303114548a03046c24213040d400c0c07800f400704d04140200d942107244140d0181141c00f44130f103007144c01d4529410500402e03082d0f5407103070842c0d00c900c00c101d401404800c00b160080a90314086086408804030300340c01c074810b040c1e180d685400d00d5540141241c540d000d07159011b030341c2e05c10040f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 883081169 1250 883079919 883079947
    0x40305070309030c06020a050f010e0307021c0204021218010e06180a0506070c030801080c0a06030c170412090501031103010905130804300f020f061c0603021807090b 73
    0xd984013070048000100c02107110b075400303d0010012070203642120782d2000500d5041c0d080310754108040009500401040005040270000380121154040044100b40b0003a0080341c1071381d01010901c04035107802002c000682a4020004201c90110802002481001605c555840001030480210116070360141182800100085070f11301d58001e007030350f12030f041400300a060403448a0301200460b00b100000310b50054000303041c400a10009240c01059444d141055008228045030002009107081c175410740e00c10040e5005000301c0c0710b41500b5010428042c00100b07040e10b99004581010b040940e06e41030f449503041a00d054419103c0d000030f0940303c410070041a00c07184000145805800b050000304070b001c4500d0314200c01201d0700e20091405020032074514042c0340d0840100701d141040180000750070000702083d805d1b400504240e20b071038204107041c40d8000d07001000010f059116038040c005c6003060701d50000e1a10400c0b1281c80c0341d04003100c0140c48036080303004203003c4c044041110406040704d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 883082419 1250 883081169 883081187
    0xe0721020301020d02070501050717010302010302030c12041401060603090f0206030907050312091008370204181103010f420905061903091103010213090e12030403050703 75
    0x100030021540c0701300c044c04101c00703508003043c1174515502c0c08001480a03409081600c200c07400029414007142e0031503005400941000d0300d810701800341803103c0c54404109040c803e01039805105281040700074a4202070944615802c01006c05091010410005419000c005900d45d4111600d940303d50303400707220524255684d4070141c3d051041c1c0ea501100b00740c609004000080b006c1c3e400031011842000d040d140d00e10203441d0041c05880702000102103170a44030079625040414000201440c1140c0c8680b07051360065040402c800e0144000e0001c0b85540348070742441c03c5072862030a420b40d07140c068600801141413040d8005154140300080318080d00c00c00500d00d001d4010b00ca518191117400819200721220720201021403014000811140f800006070f40c9040a000410a5003503141007080300582000b0708100c544e0900c2030f25006180d902800a03080b09900349a40b2805546028407a0085d0f44103900c62200ca6040444540c105601e508104c1e684550982003140c6e50714607600c0c04940840f0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 883083669 1250 883082419 883082423
    0xc080906031003050606030c0d060b04090c0b0406030e0106030305070b0c043b2e0801060305060714040b07110d0c0b04141f1803080301060804020a06030e0721 70
    0xc000003004094042c00c1e6038401034902407000c949007580c4031418140e49a464400841e03110306002383c0400022502d410000c80c8030005071000c1480e5015686d54509070300329030000d0041100212b001d01c0b82e03e5041c450030f84501e0000000703100b821300e961009007891103034000c0031340a0040d15002550301124002154003c0c0b502101403560084281489610b00d112120001c049404214000b81c0310f1211406541c090348002d588040400c9204040302404034622107400d456216134030001400010070710603c80294018806400c0d1850007510040403082c4820700170650100500c41030045031400b07401e4845407640034403441480b0303c00100082d003c90031400c0c001c14408405201050014000014000719480f1440041c680040001000141c8030542568201c05d045801d003022018807030048081a40000e03000011541e4903a21004401c0e031003600f004c400b08150b64144011414620a410f0040800e450304011141d000480f1a440d070340d0510030300d601003880628241800818041e0307450055 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 883084919 1250 883083669 883083679
    0x20906010810170313290d0b090c0a02070803040e04060b040615090806060f06030f040609050a12021509030d0f0b060c100f020906030a020f091c0605071407030c0809 73
    0x100b0074822044e5258031031490748102c101c0c000300c006a1800342c00c0a01c03c4018540e20990f8001e40710072800744841d080081260006a111402204651101940c1d203006800e0000b940d5a66180386002034a0031b41154000b9100d40e104000400481d02c4401e441a001544010b012542103081c2d00094081c7c82e0a400064035080021306800c1415088a50b200c108c408540135288650340c0d9408214190030420b6010f40c220340704100140c1d088000c1c0c03101c0d65000d8480c0d000020303240d5880c1c84007481c140c21042c00700c9501e0400c4410340e0074240c04000682060510040c8a841413801c510708584074010650081c21103034a60003c0202d00d0101e0b0401405468090407884c1c6403091881ea40d69982ca0400b410030200d49031600d8007200c00040d0007100d110308000342500d4910b4690302903060080d44400c2c010701d0030f401c01b8041c072400e640d51154842c000250760050030600104900b040c0c2c003281c0c0f000d44100e0900c02e00c0d22038186030007440c1b015101c0c01601410480112040d5003011034241c8a0048456880 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 883086169 1250 883084919 883084949
    0x203070303150f0e0f0f01180b03030f0c0609071e09051e1017010e03071e050303070c1407050102060c0f0c06010b190302070203060a020d021611120604020906010810 73
    0x755484c00300c1c0700e0542902607900e02c0d01c46007100c144910013030051240d40441c025149000d0040c5e500701c1000d00741c0150403245000b8400c60400c1e0950080100014031f90040810321100fa58100207040c0038000110844200502e492002d00207540240b203810929915074000852030350104544215104100420100d9031400381c0400100c4c60042c000e100e00e001c1002c0000c03001c60030510a0021169540000b1460300d4082d84820010f50407164910703626041a90090300092420720155000d001240c4603108840f04503c1c0004a074101c0c1c0c86001295400002d00b000030b41c0c1c1c000b80c840c0c1c108000021403543c0d0700c007000603c2011f12688945260a208070000000e0f144089e100034500c0c2c0d124030518107002c40d001c0350218183d200e07860b00a90703d58881c402142c2c2220442c3e00420003a404103e0051605294500313175400c0204021054800e401407002c0755106040606100c04000c1140020b0001464642d0006920200240510741040104400100a0011422903101501000c9204480 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 883087419 1250 883086169 883086179
    0x20c1c06090b10080d0c0c1a0c030403030e0405150f0111010f02030f01080c0904122d0306030c1502120306010c1e02310b031c090503010b01050a0203070303150f 71
    0x1440320038880e144d1035201c4c5900641042c0d00c42c0b07040711802c07640b003020542c00138038140503440c60801d0071905c00c0b180e203401c0001d1030000343c080000304011842901c0e072842d400034110400c400c41c3c07802045010095074104500e8039aa85110603150070b54000d08105804604201155004000706850804c0f441d01c00024099030303a2484198504031a0010304a0358180300640a2095010090b50f00510341c840d01905040300501a0790c00701c0c0ca03901045200c05038580b030040710340c820a06800198021a0b030710b407030030f00c1489603541d541c001801c080d00c200200f001030000029642e460b030020100c0c01d44c2c804008110320380e21458000645980142001c002c06c60204134007249040d450350300b20301c5030160b9140c0b402d95160081c2030040300c000701c041c1145019400261070b0003400300800105d50600460844a11180c00c2c454030821110007540d51041d11420b1005050844050703c0141d4140101440407103600ca60000844804070f500d4034021520015500c00d00c0da00040541004155902202003c51 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 883088669 1250 883087419 883087441
    0x605070e15090907260604050604110a21231f034205060406050109031509170a17040503030118180807020405150a09020703021203150907020c1c06090b 67
    0x8000e01d007c40e402c112a0b181c10080004403103101080e221810424000211142e00030b1808034198030000c00701c0e1346c0924101e8000000c881c29101ca80e50414000014a0200c0d038072105e0003988500c7c101294803000c411a045842402c80c81e03c002020281c582260380c0c0040005d007949412514500b10402c1107045401885160024203415042c0b110301c3c00000071482d141c903004070400c5420603159411100c0c19912104d04201030801c54241d0143ca6100c20000240c021410f11400c1082d4540c940d282d0714075031001408880702c41000202006183c0501003c50008022241100c41c00c098000001c000c82c0c0500340074002030300103174014040440d5201e05004100d00182502e9108440800950b600c1c80d08003030100174608030803070300801000400c0c00040314a83c000c1405500034011100c0c0e00150b85500501070b80300b00d07a588884e01c034031004806641401c0014981008860025121400c44403011a040e081c03c0041c0d83c2c58002018001018000701d9407001c09500e800181c03001451070300c844450 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 883089919 1250 883088669 883088671
    0x602030108101a0f0103140a06080d08100b0304141603020a0b0304050616051b0334030c020f1806120f0307020409020414040605070e1509090726 64
    0x4071900071903001c04891a01403280c4a00784540404440207200c0d50f405001c03046031809803003414155a80c205411220741c941c0e0103441481e241310003007900790502c01054140800c07054078105000d40001448000c1c1c04075105c94003a6000941459100d96440c14001c18502000c2101b11040c00703032010700c4207a00c0140b540e400036a4004d0340d048a00c00d91b2880690040c2c4400c0307074090074507080701001c24801810a042c4003050011442e1450601c0720b03840e0150b03641214000c1a00c4a50310000d00c44c00003c24000440594045092028103a41440c810807804005c5a1400504011042104800f1987d59682801c0c0000010300062941030421054000f10b80056800512a00441010005460000030f0440501084101550808080f82e003808090402498201d901588800030004c1c86180f144000e0310035401500d0209850400d42d0001e07240e80030640405020314050196030102e00303104400c5a4558400341c4806070140c0d10200d04940f4180400e40d00790910440c544111402c1340e9210405d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 883091169 1250 883089919 883089929
    0x1908070b041104052413061d0105030f06070c0f05031201120606080d090b0304060e0607081e07050327120703020105010b0304030c1b030f030903061b1211070f06020301 74
    0x10482512401454004030340040c800c070790007034203d0317081d0805410803140240c10300103034010214180b030302c03408035400040120a401451000440040250f03103030410500c9401a04000071345040c0c1040d01006103001c0450308090604c2060035081010040e08004588034103409848002017540c5030040c01040c585050f04c203a91140c1440030100d4801c0000c5204403110410342c03255a40c040c50042040c00b1504024400e031101542c46040034000c8105000b014828803041d920350382c1c5450141440008401d00100113411900c24100700314030180c00408690700300d200c061360a010142247c4a8025101c1d800040201c24003940c0c1941c011803040001401c400d0744680c00a0241da80c03610007001e020300041318043e001030100441e0001240140d40d40002c41e0010ba1252203030240c070380d2100341c0104c40c640c00440c0000d030050010018003045200301c1e803c41d40341030700040c42c06548031002001c0314058185002d2859541b0004064805001c0407070b40010b51084809a00702e809090100c000c1d0801d200c2c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 883092419 1250 883091169 883091171
    0x804030c080c031204060c1106041409090703050a0209040501091709041d07030303020c120412150b1806010215090105010602010e0601180c3606030e1908070b041104 73
    0x1040350b2a010402880b2841c4c000800ca0510380703840400c0f95060464178003510042c0c403800491026840b50002170000e4a0313401a4000d210794074100340403410800500131b5005411401d400d0000074404144d40c62800c3d0121072104040d02c03103041c2940108001c45006150101001220494a034000058044503a08482c00c200343d40d0448042c8550510310054101941c10040e020700000313001e58050b10080c1c03100c404aa8000060504000711540b06801121081c6410000c03c020080014501c6148a071400f00a20000780320f0400700f585484440c110900d013000000c009502e83c1d100304000940c2400c031102c1c1e500d8508100b18000d009190a004403c010750a000c0f0061410500244160407601540e0380004400c04c0c0142500041100903100c404000c1c68240c00c00e105902c0300282081c00d02e102c0c08045c808501c00c40c3e1031208001c0f41e400181071504105400c41c110101042c29042000b10b000f15054124440c6010080361149500040200e8100f405010502c00703280711201c280d01050f10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 883093525 1106 883092419 883092433
    0x703081612020304030219060807031e18050709050408030c0d1409010b24040b030c0f0c0601060813080a05090a030606080d020105060d0c210804030c08 67
    0xe000580c00844d05005500e0b042ca400c1c0341d01035001802456291520001030076101c4001d11500601d03641c1c0c4111a0401b911038419240c140f4080010031003a90821544030800302038000664183c81000c1020407a0015446403d000341e0308009041c0c00d55640b0f01d03000c0032560040642c01500350b2641c2806904e40440084c07a405040002c001040e40071107130b001e05c040108052952030068103440e040c0d146130000d880407a016270304003d201e555030b5a42d0518500c0c5374800d240e03881d5140034000070010101d500200c5c600741030710003540e106542e031b032914203007120031201c0000060142d00d81040804500c0380290020215070001601c81c0d40342d01d030740341c94203c226580c6038014003003a00009102c2220950a10407994004030407070300440c444805844081101e04280550020021100c17603a12140003e18960380c201903110603038a40c1d441c0c503450312007100300d142d114000c5140b042c0340b = true := by decide +kernel

theorem cover : BRFrame.Cov 882913669 883093525 := by
  have h0 := BRFrame.cov_init 882913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 882913669 ≤ n) (h2 : n < 883093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
