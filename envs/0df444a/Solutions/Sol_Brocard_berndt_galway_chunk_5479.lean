-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5479
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:59:56.5332+00:00
-- url     : https://prove2.me/submissions/342e805b-fea2-440f-8f30-dd1b84c6d857

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 985251798 ≤ n < 985431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 985253048 1250 985251798 985251823
    0x1031521060f0917071a090609010b0111030a050c01140106050d0e0a020904061e06080d08060409080306270429060307150e040c030c12020c0312070c05 67
    0x1100d90a40342880700440b090701d01c0d0407076000c0c141510351020489070366002d111824080100c42e0f43d6861818000d10b141d00c6102d40c282d00307100351401e000c1d0302c940c0060040e01514a0320000c002076149d200043d180c9600e032200300303240c42e0810710100c1c0c00380740140b02406203181c0d01800411122420000040d48070030980000c07001c5a0301040c2007924100510601000c0c03208200140700810302500040c00540c8001c0000305610340b0f0b002d110266940c445000e4007000090350050103a141c940d4282074650fa8603081c94000148048000351103440c213170081507085a002140c0508d0b54681c0c5083c091424841c01000060f0002d9241d490902c0da0a141403520660259800c000541c1c007414800d801c040d0000584801003001205010340c65030041100340440311072040201003810802e00179224060361001140d801854141001c0703619404d034200c8408003030144d460b41e64058000002c50100c1c05580d25000941c3d0003032002d4694110450b40c005e8102c1000e003000b40082c045035640fa0b18100f100c82c000d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 985254298 1250 985253048 985253099
    0xa090c050402390c04021c09030504090f02160609050708100b0901290a0e0a0b0d0b06030408040e040c1e0f080c03060402210f0102030702190809010315 67
    0x40c1c0200e59035094101c004a405900e00642c4075401860f0641d210707101c1654510540d03001800c0d0f034042205000c1c403c0c3c43d410003403040c0400841410080c0c01500148540c10880782405804070a4114a108440c500300d91140c1e090940d454940303d0300002d000166080391144a24100454528010050040d180d00e82d0503000c5180300000007480140c1c48181d1207044411810080c1c0f0792203007101102c00c01070b54510580b103900c5024600702111449100c55040d904140e5034040400c088402e07200900c060085070100b80059101c03130381442894802200c0240034408288030601ca03d400100c1c002c1e800c10701400740d080b009926200075030f0305850f580310105086802031100b04003408480c50726100404a490181c0081d82340360002c42d445800080000303115003441c1456110034a0b02d0440300d864401014202c820f52000303090081d0007540243c45e280090310407001105100300c500403003114901c3c0d2200c0101d090440d400e00641c060000f0f03050001078a07005903004103113161610003007440840a9180d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 985255548 1250 985254298 985254337
    0x120f0501291f0c0308060a05120f060f0c070f030314190606091406030903190c140303010315052e0905010e0105031c110d031a0a0e0a090c050402 64
    0x1000050308194000103000c0c600b14181081c41c540240c030300c5152075090b0a00e10340540d00d0340700140c1c0300c00d083e806c556841440c0c460710310a12840000e005481c1d204100468140e6150a8050385801d4030488410701d240e10100001070006481032a400c11241c404e0502290302c019080300a03a6101007211081840320321828002034505281c0a05030080c4044d08128008504000b005060320844003200c5000d100b0000100b81428400c100b2a0002c940d0074140700c441c001010002003ca042001064820444140e0000908140482200e04999101c86100403014100040078003400300107100e0300d0900750440220301600c4a241907c03506c0103100d280d10742d406003040c4100085820682041d440c0c556540d0045c0240d407800510003c00840d00c0710f00c098504210401140d8240d003010b003215050050040c17400d0510b4050700807045010f0403c00e152001e140350010300412003111722400b00301506020116405041c0c43c1d01074004580202000c0c0f104a440704041b50580c0e01000461011810008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 985256798 1250 985255548 985255631
    0x90a05100c0b041104051b030a1d3003360601030b220c03080c12040b0a080603010e0c090603213402060d0b0907030506030c0a120f0501 60
    0x1007403aa100d680c007c41140c000070b901d061803d040c000140f0305001d00d6030f20102c02003502d40b40c49842485040e02c2040b1441420300400c44a09110818401c01d503200d41c420324040c1c1c551180080d01d101d11809980d09a007100603040741061030b0b0703d0384e00c0041001e20184038220701d0481800f00740d003e180102095111030400321b01c00b01c004010350030301011110449444000040c000031b28541184d4001c0305041e1a061a411040c0c1040a4803101252002001500041080c0e840f006480da002c00c6403141c210395030b00d4a080c1400e9a0ba801910a4550404650141d0500c0d1022486800101c00f8040f95240c01e614013003141901c0303103103604000d41903001c01e02a46080c0b176a00c20303100511241040c0c505046909110841d0000c144500230b10600d030106299840f42060b0744080c5003507600030300b20401801c1c078260141c018171040c3c501c1c6010303026480090381035003000c0c56441c04030f40c006031150000442645a5004444e1311050854542d502d508946002601050440c01c0005040c2c00742c001074071074031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 985258048 1250 985256798 985256801
    0xc0702210102310f122a14040b0d020907110a030306030b0c04060c060e2404051e0723060a18050108040c121103070920090a05100c0b041104 62
    0x200700403042c1079212a03090040f0005050303140c00b12130525601581d405007502d001c6c8860005150456451050b11842c40c0721086980000701c11107460303200705e0545214420031310042d5a0600a080c1d084036840074034100605000900a0340034865151107031040c1c0328091181d0603c0b002c0e950070b4000a882e01c10500038416406401030700101a480014a03042c58088090900068032101030080d40d50394848040040060000031402c900c40000c0c1c0c0e900c46090200304011840a64080e02d96114105c11140000d50389807610710b10200c5403000f0000c1070303d0042c030139400352040c00409070f00781c150350604400340e2101c17405420090b28645840c103007001d0304503507240a08601d034899410801c9603818400440d46d23458282c0150b613a500c42c0d4840c205e9690501c907080c08150a10b0356050b1060368000558643c5560044480d180c950f6490141410b50041200c0c242c0a48241c1c0c5511402c90a1304000c107280c601c82070303032231007819040080b0400d09503141c98240003411101520044480395004002d850f01c0d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 985259298 1250 985258048 985258117
    0x705060a030614040e0d0f0e09010303200604021f1b050a02090f0f0f0c160521041404020310080f0a03030c030c0c14011116020a0e0c0702210102 64
    0x20f9130200b207510307000b4861651301c101c40304c188010300c10b981c1e9140c144148038403480700c40410050b1444070309594a10f8001c04040e1004a01c00f00c1004421812a043d0340200d0b02d2805950010f02c4200c0c3ca8030254081041c52040011040910521a8404007814840542c0c614081d0041c00984440701c482d005000001500420060303c244488080080080d00c24416580103000d203402d1403e1592449080c00d003601c00c0b050031640c000d2010f1020b5003002070001c1c0c0015281003203c02c01100c00c40e50120b003802402140074510f10f448400c0310000f41c909081d4017039907010645810001c1282e07542c42030541400f01cad00303802043c02d030010f0442d00700345070f01400ba07112900d20a203401c01c408102040300034940ea00b400707801815071b0381c0840d1300044210700350015000400c94802480d600e00603945114004410b0b41d50481c0a100550800200140c5051169228200c0c10309803074034000065080000908140d001c031410b0350081e40c500c01006600b40b000e070075541140032500c500e80d04a2500c200020b1403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 985260548 1250 985259298 985259339
    0x9060311040c0c1e1103100b01020712152c01020903160803030402040e03090a060306180c080712020403141e07150305060a240801080105010e1303020705060a0306 72
    0x1900d5010b50001401d80649207100313262128400c4555030342d031030300340d1480510424203071380b521071038600e0f40240f2010352040718000000d03001c44082a1303072040e1a0011503d8000080d0034050070b207140049100e4a50004031041032180c03500c1d076400e0514031071145010b031101e4102e0a6694089240c0b8840d08081016000400b12415041d0050f45000d0f07039144d4912000740002c0c042c58030340a2007161184200143c40e015840140700b0014503441d00f50080040c032541c03040ca04200c2c0001c46401003203010f441780340e0005407240e980c030820740d40e021015a004c0c0d000c002e560a00c698200800400b0881440d4162070048081c7d000c5c00f00d0100030401c64044080c02806200c4039040391408001d420713a18150140765003020b04010540c1e580d10800100503040944c8888100b070340003e01c044001c01440d6505126401035243c400702640c941003c41d089440901500d020058650f0101c0c1001c1c480380414009036100c0d104031103e4a440d8004070300c244c0c0204100901180e1a1842404072442036134407201c4a10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 985261798 1250 985260548 985260557
    0x815010e01090213090b0312210c07020a030b040515330609100908030a1e0206090a08030406091506060f0305060d0303090c0306020301030f031b05150c0409060311040c 74
    0x4111104c0705035401c243c0c0c811108140c1d0341d001c401c4119281400010100421814117603181c00c1c012000711007030001c400c0c11030320109005001031a1010b40e001030364141038028106244003410b5a44017041c1c02e102800c103545c148900c020f081160358000126501c281c00103038041c4401071100c0a40410100340607250007009542c07082c02100c07600c6020689a41080880700d48003014000710064505551581100d1000d000c009180354032581c00c403101e9031100310540204201c141c042c2c07100b241c560400f03441c00812500004080400f0406042c065900640241400a0500c4071a51158001c0c1580301034101c030b59031204000c00c016270300b09500d01c150800c1418144202d203410000500c15061200e0b005043c15030321600c100c10322a00c5c40042d409958440021507a030358407800c0c0171100f40c2c81244120b0001e00760390500e442c607100c10300008025950040c01042c480c0e140f20440030a40070007d01c81d50a40c00240300025205417035026030001903000d607611000a0301c0920a000540c1c0d0005086428031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 985263048 1250 985261798 985261807
    0x10e04050d0305060d02210c06070f0305090609030a030f180f0b0705070305390303090906010e030109030503091509030a120f021c06140d06020706060815010e010902 73
    0x340c000319090107988402d10300040c0f256620400284540c003a00c002170f40003008000380c01c08540d0b804c84944554081c810403074402d10703a00400c0050520a040000b05005040009540000e00500c007400150790014901406c184404012910342109910b040d40021162849581510741181803034640000010b001030b152410310b588210f11884600c603040c91090006120414050180b000201030365010081c5c0b9001c0303030501c000c210550750104140344038078079a140d1010701204800b020894100050055410000c45100300010b040d40244094140003544807048030a503002c0c456800c0c1c0c0c03803007511410740303034105422141c0c54180c1e00e04128241e440c120003400b0386240004103039081d000407841d0401000240c0c07401d40000d010300030b040c004150700200311000101c0010f41c189810200240f001c100325507403004003500107948880d40c02d80010050b9100030200301c06800502d00da500445001c128596114400c0307103000e400c420050025a20900103201d04006a8421030040c01c1101055007030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 985264298 1250 985263048 985263053
    0x160b071d1008063c0f0d0605040213020c0a06050603010b090118090c0608010501020f0601030c21120507050f0a0201050a111c09052b021207120501020909010e04 71
    0x3071810740c122141c14450007400140c540d6882e800b000c128024180c0e111400d08401807400445452542044040042140041480c1d0705001182c400000310041c82c40d4000a034940741c4000408010380103903000002000c44410544d650300040c156821001d000309100c0e20103040c40001c40b203002e007103940b00b41d0403c0340740c0c0e14613981d20080301c0c1514248003180b0025060446450f00414590100520141c41c1c1c149c001042500564110304a80c401c0c0c003515001c00ea000074068a841d0300740070007032980c1d8032124140710100407600e017600004a061001104140c05845001c1c249841400368000681d0000311351080043c1131040203205403070600186600f000700e80c0040c0483c01412100d10401421505e0205030800030031841a501400411104000d0f20968000f0319040c0180500341c010304941d9020740f420180c151111341180f08001401e000076280303a081010000384150341e05030512a1910216440e0545a1800c190f14840c3c000140d80f680c2c040140544140e050340000a87e480705000c02c4007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 985265548 1250 985264298 985264309
    0x5190c0f091a0a0305071704050109170703090b0a11010203130c0509040309120624030605090309030319030b0604090b04050109110d0b27090f0d050f09010302160b071d 74
    0xc422030f0900307010035682c0e00e000c8111600c242c1c04c0d00040070075551a06100501c4010350000340b1441c0135002591502800c08144e031030b54854100d0050004001d4401001110141006401001000e00e44880320308195100c650070ba07001a501801403c40f0101c140c0200018000288001c00701582c155200303281ca40c401800c1005148500004c05103111190310403c460355010384001000007410310072105002e04681c5180c2c400340000c03030b655440d0802103440048000243c0c3d0305604014001d614004086141c95891517804420707805160719030300c0001c2c903941d80d94040c001a00502600155580b615070030042602c0d0182d00c032a8040e4035200b02100c0400a02c01120b280352110752021860b0b48440d0f01082c0d211541c503191800044940313150020258240600901070b9200d0300071a13007402120b030003550319460b9040c0c0c080c02160081201e030303801c4050040500140380050400604007083d001d0030201c812078140045030712030300e41401c000304240c0105424400908a03010409558028070103c0d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 985266798 1250 985265548 985265557
    0xc190e0907081f0f090f1a24030a0b09101406010801091a120102090306010f060e010c260901030c020c090c0d0608010e010e070e0603070905190c0f091a 67
    0x3c4524502422001d40810181c1080e44030b408842c1e02001104040d08010714403103010a004c4681d4420006100c10744c4003141540f80c001c4100801568415405040191950005504c01a0103000340e802a1002c07070102c2090038840d001001c06852a9160711004808803088100f0000d140c4010720180022a6070141450f41900c0803208009400c0200940d10101b1503c0050a030b5480307161640080540201034025084071541034040340c41e00d9880d501410b450707800c5d5000d10700c00503405c910519a298412010445828083c5c141110340c540c100c00c03c005022084115401210400100815907503030600c505007510700c80303101400040350b0501c00185194809030401c200000007013440e940703040391980403078000c000000c002c002e0101c1c0d135104c90f4081d240c03040400b1054009d0103000130f00030302829011072081c1e0f001006072016a00702940d03a0001c010107013548101c41c090001c0c400b1071084920031a5481290380e20340d895200b4240c0750060000c412a0403290341118228841d00240d0b200744180c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 985268048 1250 985266798 985266823
    0x2809020708090111100c180e090307060c05041502071716090e10063809010827010501140d1a060d0c030b04060b0405060105070308090c190e090708 65
    0x114294080e0100382c5c6000035034010310a400d4134001d900d084280d00301c401489004681014002440c0c6d940224048605c011070b000c0025030802c01040000858a50150030303029901e003042810182c4078290f1400d5017030800e00910240e4401b481c00d100d042c1c4400305135825030301c200000740584a480b084c01d81e01c005242c13140d01e440540300d850000b5032020501c0916403503c280b400c108106641c841c00b0040c43c402000141d44003c900d08594105480402c2c028030b8a106000320941c581801c1b0ba004490048009101c000c07442d015000035540701100d840d900742e1800740880041102c1d4100100b40520818000c2e02a1050142d0a06d0703100088010f08884e01030604408076040d55655500820700480098030300401803145101c0c0401045800d40541e030045000712404c0010074100c0091008840d015220580400d02c140145000644188403c40e881007080b0103860800901501003140342c000c4440c108540e042d088010300246101100c1e20303a004858100801c525883c2200b45038031843e520606 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 985269298 1250 985268048 985268057
    0x60120010f0c021b090c030c03040206121e09010b010c060908120c070507050409020a171005090f1203040c03031d0a030c0e070915030b0d0228090207080901 69
    0x85051050203511000c200701c0405401c0c000490b01600c02510b8120301c4001c010800c40d0b01c0102030681c1404031404e84140807540013a461500d03504503103c02500000c0c801c80c0d10000800504103405483c0c40301a000309038165a41c100c43c60f1899111141c91801040c080342685004141c0d105aa40a94039910a581101c0700056040b51030601ca01e55100311149142210314a070284203a0401c034000500f0050702800a0b01d45942d00c0e071003004145ca17801c20002c5c0d40b00d4a100c0c41841b0b01c0c40c80d4a10402e01000502c1100c1e9120101e15845c3d0076100c088400e103659030040c10003989a00c170240144c0e440108881d51541c5180303010baa840c042c244141c04007070100410b0b01d1581901b00c019110030031007480c00034504007019960380780c45402d2050500541201c0d607e079802080c1450b0203011108140c0c0c007100d140f0403070280a603004400400304c044042d64050710038040345003d40c07110000171503010aa6105240807546403500d868000c0e1240e88003242041c410800740c5c000c01c5408c0f096032064082441e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 985270548 1250 985269298 985269347
    0xf060604180b04050703171201050402090d060f0b0f0a05030307080304031803051c0503251b0c06140a0906081005031b01090602010c0212210702071a030601 69
    0x154901600c41c600c1c000340598202401c0c04144040000c10108a911901c403544100d03056803140c00007400f868000800005e028001440f5901c1c054014000142c0041e119000036007058458900360b50861003501c4001d56103e0100e01c003410f240b808100316040c165107020f20b0034544008240c0e03038400d007540900a404044042820544540e05083ca0308800b80840d2105e1600c0b41006900c82c0c2c0d561254000440c20480004a95400b480980c1c2c407405802407040110101840c2460919001c1c468010802108160f601d09010b500080904d00a005100003504c090400401a01900c81c03031241e5060500c3c00e1012076809540464000d01b80c428901c1c007240c070786c0c0340c003200010780b84003c0e0013555060140d0305600d507045220103e01141c2100c00d9994098887e13540354168204c954510300c0000503001034460307580042c3d8001c02003071510341c01d01d07403440c003400d8410418181d48000c0c0c40c2d5000580021104100c40405903506400d1400e170303c407510740786051040011300ac0d107002c003450341c00c10f40408a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 985271798 1250 985270548 985270571
    0x606090612082a060703050f06030a02130605220c030b0d08181c0201080f010614090d06060e01030b0a180b0a0e0f21180913060c05030a05090f060604 66
    0x314202d0400043c00e451000d5905642d16140c2c448404441c2600040d00c0c5c64009000140d120b81e055004600240184c21a80c00e01e8080c454903510582113900d50301d03101c80c000501030b11010300200803d041c044662003034011050b00d0506440b68a6208400c02d406d2159610f1559100105041401e0b032241089a80f6503103808102206081c0c5c09030980e10416012110301e407041c0a0480701c00f45c174401d9881486550b5101c1c52001000020701903000011014502008402d542000800503190001d0003500301155030342e02d190a490b6140c006800030301112004000b080718500e12681c0001e0202c2c4203006940c0090f0550260710040302010f000907102d10007180021201c1d5202140514500059402814032118515030302d00c1103820b920b015406000c90414496120f1041d608542c40b4100b80d01e4100303507a8400c101c45c901c0c014205442541200c120140010468420640c0100c015141d0704d859250107542c500c11030b4401400d40000d5040156040e110b010089001c40e4844c4d0b0803100050f1196651 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 985273048 1250 985271798 985271827
    0x80c150a0e03030406030504050f0d1b0302012019140901080c0706050a1508061909140628091505100801052e03050a020904030c050118060609061208 66
    0x6400c60707505804009404548294142c02492140e401602254403000e6050751050750350b03070000120343c0051860b0b08012000301003603110884c0a0b01910003c1502c4a5150200b02012401e40d0740e4050f0402c0007942c3c3c031402c0803449102e184a00141018888206411590501c5200d0f0050792410024508002003256968100742c43d0070035040780007003002e40790030303003c020080695400d90150810141e03400101d8000001710b440c0700745c01a01e4014078802c01080c50340050912038804a807030040b00100024482c00422186116036403030803a400303a220b224090403240c8000403403e4011242003d82d010080b4042c010261108820a1400036003552000ac000180704034a0308520324039400e110500000640c082d200d000d4610034503003202c03a500f0003010740c42142c80843c07000501a8000e619108090700e8100b1259500034003c3c2065184003425560300c900310740030200d80b1102c18003074801e00000e103e140e03c110340161014040800c41a4208a8413603402481c60500914640001a131b103003850200c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 985274298 1250 985273048 985273067
    0x71e02030f0a09150221070807080304061107151d03031603020c0a0516060e0d030305090307020a0e190606141c0c3516030b150c0601080c150a 63
    0x500400220510f0f2580020740342c01b085906403003e02c040040d0039840b1801c1030215841e0030ba0100c0102d14116083d5104482604002c0050383c80c150349041c80c5030000f071418001c0555030f1098030401800100740419904542061050501500d00003213080c5681c0d00c00030440f80c005042c6014202c551381d80c850100e002e071085010081c054054810400e0030040c0c0003d10803110f403a10035040002980312035007101c00d070000682e090f601052038400300011074000e81c090ba81040d100d000350303490000741b80c010901411a5034840003070440668100074031408152001c0780c1070000340c1803d020a81c44d09100624003000092100b184000004600066000c0141311115401ca0b1803024400400c50f240b01510404010240c00e42c0ea0080d642c450b086820700f00c80d0204c3d01c604159030902c184d114521050f00d501c80460414052640c0c4900440381c5907a800ca14440070301a60320342e070fa6034440f40c603c00c1d4101001a4403070342c480d42c85181200015640c0320300006100c44820591034a91032680003c80d2007981 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 985275548 1250 985274298 985274309
    0xa0905071505042630041203020f0d0f0f020307060f0e060a1e0c050d1e0e0c03070512030708040f03111c1104110d05071e02030f0a09 59
    0x40c1c01c0380306034981c0d0030002030000c440c4000c429820b0609480c01d200301d0950410a249610b420000d4005071101800c804a440b4685400300500004007003400c9140d2544144c200d01091443c1c58040c030209903041242d4094102c2074800b80030f1545000c2400f5003000c0e00342400a05000e051003038110031074400c000751a21190044418401000000d220a00420306103c24016600950000403d00482d602070079500c0a984960f010180001003200c400501800c0b420380704100c001c00012038400000d02800c18241e107020425100481c3c682c07450421a006124403005c1500169201e18460f500450401d0403204144d50784001c1c401640c00e91815881040d100900010001c1008960f0800c540f0381d14013030341e2280c0070648081c01032408204800c00000300524410003002c3e01d100004411440f40900528064804680c541144440070706540088a5050000e96900d041004041d800030409001c110700d032080250310b6000300c2d030080d264880d031004004108000160301c1c20262140380b50350001c22 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 985276798 1250 985275548 985275569
    0x9061003140f070e0a271d010510090b060301090e15040b01030302060c03090c1908070b09040b0a15030e0c041e050f1003140c0316030506010602070e0a090507 70
    0x2c0c22100c030a040840070b0b40c103100012400e0311070805505080710454161003d00c41c0307a041a880c0403990440100104038140419078481c60803c1302242d0b0a160a040805c1020010a031460160f01842d6144032603484910542c2c00c16042150310340702d400071641526184040407441340850300ca42882c1c240189628008070303509034100020300c9840850320341660310942c242c60300c0d81c0700c0024244203804159540c038403a80003400304900078a41500070590080c21045800e003c150b0390742c0024200842a4004401d03424005045215071070140b08040c0c1e0650201d0340700302140c1c10540d0b5820342004030080c1c030040c5980d03010200d001a90070828840c1080e0010007e106000105200d42e200d074401584003050305040001241c82d20252034483d0b4840c2c80881c0b402880d583c69601d501c1030846040540546a0180500b100600d49060080355240d0410300786c0041e000e81f841c94031502e0590141d000384115080440d0071f0081040792032045800a501c031401003018074190a00c5410a610b6611a03480714 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 985278048 1250 985276798 985276801
    0x7050a150c080a02090f190308040b07030908010c08150a1802041806141519030209130b240c010e0703020109080105010308030c0c0c0d051b1c0b07120e0102090411090906100314 78
    0x400c958002481330502c203680f0300e40010f0f40d40010301d09807080240c0b0800442e044000145414941c01e20703011501e94014550802540e0320040b0712139076000900340400682e0006802d211100c141e01e111a451146603404000092520090500c0030203104100d03445000d271849100700b480b1b03042d8155041640150041c040d040035003407000c1c00950004a0003070080c503051301180e0b540c2e01d141c85580e1017000040c0a5012003107180f2840080c581030488028400c020034008607400e04004d204e40d07400c01d11904028030b60f450440c0005003020b91903038040561681090010300000c1c07031080035207400c01c402003992600c8680e000e0803203090442c0c82c40b506400001e100501028041d002030301d40300407040c518481c8050354564003408280c2040b141644074030301020000200244614580c0c03035000303001c1d117480030f94950102032138001c0d03e505000a01d096074000c60503804034502441280203104410a00519012500c808210402030082007640300d042e01603000ca00b058001d400c244800542c0742c02e031605a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 985279298 1250 985278048 985278059
    0x90e010204060305060d0f0b07110a051e0303090d0e0d120c1502070b0112050309090112030215060d02040b0301020c0d031a101407050a150c080a02090f19030804 71
    0x750400c1c031580c80081d003801c0c00300707229040020102c040b20750001e00080c10703903d46841d03224100b0f01c00740942c0204480e07000a54451002400380d0703c140f80c41203001d44003c00c00802200d15030102c070154400550010414089894400103006d107150280f41001000c204000001600412800c2ea010707281c404c1c54503808440e10f40c42100141c0f024402c9010b8803528007820802d02c201d025024000380306042010040c01031118070141408214801e00449152441c03503808252680400e0f0310101c0c0604035207546400709601403018103848280e116042d2014a4074400041d02d07a101c040020b40120358034090003009803000e404907140e050424003103640710054900c1c000d0003407000b21010040c04d00000d450a2881c035200e404000c49038a5990b03440c012100510004c541c5034854034044a141c49504c080c0000621024142c00c03440745000030000341c10011070805040d000340100380d9201180704002610040d62404e20707201c401101074856508008200d030308048800c0ba19000130340101c0011500041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 985280548 1250 985279298 985279301
    0x102121b010f0c021e0a2901090c0f1803081204030807080402010e09060a080706050d0b0303030c030f0c0706060312081323150a02130807050f040b04140708090d020601081b0a090e01 80
    0x20422164003980c0c000da03a030303060700d03034100e0341c0c1d080300000058207440020f5040c03331040c16006201a04001c0c42d00c2d890360f495450403103541c8a900f00056055080c8200414142c000e118030303900c200c480c00d14070345505e0a640003c10384000448500d1044110402181d40390b00c0b421100e002508100d401c59081c26210240508542c10215282c81d07840d0030800385864500380441642c2c010130b041461075040da20780c40f103040b8030100000c080004105083c0072020106406014040045002c3c0010b448403c01c01d0744002c02d111001400743c10404902c20000000401462105d400000100340b8100794021a446080c24807040b001500c400c901880103200c2c1d00b01e035650041003000552000300249a07030319a01e940d01c0f1540c9200c0c060b0310107950b82140c03886d0b0038284c102940e030b450002d00009040b01400810340c5a100c050740c0e0707400002d0007401007007041700c8100400811000c150000703148642c5842104d5540f104001d40141c1182c100b154a8401030302c800b000100602130510b0b0500c11a80d48204603030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 985281798 1250 985280548 985280603
    0x60e0d0206060a120c060c050a081303060f0c090e100509010e0105011808030a140904022214060d0b041418160501020a02040b0102121b010f0c021e0a 66
    0x3481a020f80d030001440034040c1402c18012035200c0081d400d80c0c2d190140544046020190589090261004032000101d64038000c0c000641600f0039014800d0442c100101191800314002d03005a24003014440d4081c1c10400c1c9100b2a002d40e500d21100e40d40f820f2610100b8400b55100d190400030040000c00d0742c420003036a01c2e06031282a6509a103400b00c0052005c2c41000c00c0c070a160464000b001408012072003801201e81c3e42081d11420b500c0c00c00a803000c50101e030b204441c3d03441000c24486501c103440c0c4c0141e44401c010209040e22004007000b5800080340c80c030894114129840e51060204460707242d94012045120002a492860746442d85404005580510b1409a140a6816281c0c0d034070084071208029640306a0080140e00c5260703007408001c00b80240c085055102c2c2c5000803445c016008010100308410f061104003540805040c103082d03034840402042a81c2c109021150f5103940021801681354041045200c000c0001511501f46511035102034035030a2003103101014400309a4241 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 985283048 1250 985281798 985281811
    0x4032f04020d020d11040f06140f0c010509010b01031b0503040203011d15010f060512090c1309350a110d0c020f0f0102030d0e0709060611250909060e0d0206 69
    0x9100110317054441388528400c0e4050350658001078042402240d00c00c0050141d0314003600d0705d2626215402640100039080805600803c0c1c2d107400800410450038081d50ad0380c100c0a080507c0003034460a009001201200704c03610170410b0110000d4295a4250024030f15043c10865903404844081401030304d8041218440c507071500024000201c1c0c0c061542d0b9501204e089035101801c02074445290f9059103806041c40031a0f1040c0328120b00507a6840c506050f60b4110000005000103080c6080d0070034969000c20010b1220b00e80d01c00300c1000502402d08041d990f0711501896445100c4801034a11082c1001c400000b0b2241d98011792140b900000b85100c4a0700855a444e6152130007020022154968016103005800c14000700081010795002008903012940c203407a0b145841d401c0d0101184c46030743c081c00c00601401c070110032002003400300d40c48a01c0d680d06c40403940241454904d500b50064880c0f81c00346540c809a540034080765900081c04456100c050320108210324400070b6071813000307a521 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 985284298 1250 985283048 985283051
    0x60203011e03020a030201051602120c041406060301210f080d0b0f011413050d060c03200a08040c0905090c120f0a0215070c081c0504032f04020d020d 66
    0x1145120035668081c0021203a00804101d156070465004540c99084814140c0c2003190f00d88400d03005965003000c004207607000344010995004002e0402c01540e000b950b400c609606a40e0500800c1e8036039000316070540e54407901080303007140e031907012510000300c6e408080d110800c10090b000030003410310014040007407940c00c20300203081500e04101c0d9048100f588180401e20915043d1084d448401c0030348540008030922814180e692004129010088181101c00320342e076020140e035058041c030440c40100c00446545c5a21000c1c0c0504440a02c140100b40c01071000d0070b00000c041016002d2100043d0150310f0f01800300741447c4105950382c202d0100098414a98454001c05040e00000e807610103102600042041d031025409000a01e85040031400c9006001c2120354042003403100070300010100800284201000314a40200c101c4080ca0702108000003000b041020510207911041d0111005040c984c0011902e200c50172542c51000000c3d400900204070180c4500c1a80d01810069103071000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 985285548 1250 985284298 985284329
    0x7080907140319110a030b09190b0a092415050312040911070605070804170a0f1116080f010b0a0f170f100b10080106090b1309050406020301 62
    0xc0550240c07050140c064040e44080c2c00c01164089280d030704088a4003c1c590116074100c030101017864003405800546035541e80c10280901440300304174240f1803a525004811804220740c0c0c0d0035121081c00351450a00c140c8a034003110900018092400c1d211504031110f071407241260320540080c100c00c08480032020b0b0034560005648c00c01050138000036580003009494242424071040003400440000c4000740320600c88900003480314810580144400c0e104c034102c0b4075291422500030301a940200c00c840c44180402d110864101c2200b001c008100d0400d0f1b2104d4200004191070500302c8620464494040000007e0011010440420215000000380302030000b003020310000c241305110354410141500010840740e0340c03040e007941c1c0f0f051080381514003004408030001d240414804100001960b100c40480c1d1070300d402010054040c11a00f40b4103019031400c040030301008040d05c40e07024502400644074400100f0300600c0c60180034140e10820090500e0300700507000b50030034050310b0020002c503070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 985286798 1250 985285548 985285559
    0x15052a03153c01031505100c11060f04170c0607030e0f19231c24020d0605120a030809033702160504020a0e210d03021e090105040e07080907 62
    0x174003200c2502c1010301000002c0405a00c11500c40303003c4613095610307043d2440e84010300e56560009025600351440080c3d21a0304246d007144512519400c1d0801c03961200c000900c481c1c40d1001940d650302d80508103041212407003004144544180c400c0170b40c0c014400000108111000c8840d80d09590604014100c40e035803a001224001c6401600550f1281102c0c000c01440c0300b40640c89001d2622a0a072001c0c0d0075030030900b480c110006441c140c400b150b00440c00c1c1044054600c20080103100490310010020001c100741d503103c258040c070140400c00c0d0000080d1a180c02002110300142d0f20000343c0c50401140c100ca070700754100d1185c07200f08004c840b00d4038685151000410f140c0401c08010651401d0b0f10303080401c03009600004142d400d200c074098200c0441d0f980e21580750194140c03902e5005c0c14042510a031400c103030000c007543e001d042c810301601c00d04d4150485403690100011101c1e60351804c12400580e1140110703400385000300030700820045507591205803180038046800403a1003407038961 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 985288048 1250 985286798 985286831
    0x1f0e030a020f0c01090501020a0b07110703080405090708060112052203180605040b1209120c03070b0a0e03121e090d0207080109081615052a03153c0103 67
    0x906c00c0c6401a0300803e100c074045403139000615042009810f0040031900359491050600d000d80d402030380e444001042c100728600f082d02c4981e91080b01c0d85041d2030186007520020700450303040044030820958400c0083c203c444460750895034048042c80c07100c00c0000303502d001881122030f400403002d0030400580009140703018805540565281503010343c01c103005554141000e140c000c0105400c1c1c030904811080d040c03441c60060420103005006185c1c6c0700c1050030318201140700502080c000038500501007140c1c02c2d011040c0d13650255001d03c0c00582d500c1d80c024105510400704010600e0b80481070500c100c0e4840043c91001e440095001d580b001a0742e044184d080304c906031000342c813140d410824a0008090001c044482a10404140d00c03103059100182003280e60403540d00138108081d0030481a00c1c1880200d0844a00e00303409118507514285800b2242424446803141c0603944590300002040310040520440c1c03041c0082600d46082c02c90010304045550301c0384c107404a1f1030403014181c90b4600c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 985289298 1250 985288048 985288067
    0xf020912060103050a02011101060f0b12090a03120209060706141009141501021009060b01030b04020c07050108060112051612090b0c030910050a0b030f0d021f0e030a020f0c01 77
    0x40241450105c6034005640201d22800e0700348040d5a1881c010898040c1d9500181c060004180000d03104d102d50042c464680c4000750040e07000740d024040e56030000354040444504003820800258485400d200860325038000d86078001c3c13a945c2040031446080c00ca50800c00d1054000004030720605a03524002c6045131905a20261440d035180e0001e0350380303c400d0855002c406010f00c1264103c1c4240142c0702c0403180c61000860302903880302c5510a0a40e418041c00d600640704031411850300d03110f4100980c0d100c805100fa1414448074074000f8003141c2c05500407031070aa45684090007145090a038824041e501c0d0549003000c96540404050b075152a81702d40d0900c164042010410341d282c03034030044107507000200b20b000f0034841c0c3c0c26040030010580c05020b010304018140030a14200f000e04040c14640a00c0418540c2e80c030a580c0780b42d565a001415501d40d02081310b14581411200c02c000019140e90444008203200024202400315400030302d0400b03d22042c015605400455001100d46150 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 985290548 1250 985289298 985289303
    0x10509010b0d020f0403050a0c031103030c1b010903021c0c09020405060d1e0212060a0503010e1005060103020717091206010812161a0106020607020102031308090102100f020912060103 81
    0x41c20b010031041282c843d40141001100c80c060b035401c3c50340d6691660320707202a8820445101d00c203944208100081c2c02684078880000700d02030f41c10900704856266a5916810103095004503658000106901800458028517000b40070600a0b1802c440d04050f0340114038000c1320b8107000b601c80000c5a0303a8078403c0e501541c000425a528003054540c1c204007400000b40c00d030320440015040c0c0c2e506076480b44010b004824502c1c000c0c070b09a1400c0001c0082040315a800103009904000301c4140b106400b203501003028000c1d81000840d6201e0b540120001e008192004000c0e120346201c2c2d209850038107001d4141c6c06421595461020402c2c10981e0311103200307206600103588595404800c0200c054041c220302c40d0404808440d0f8040d907215003c103441040201c24206a0140050020359070511003140d1000244c0021342c07440c07c0c030700b04c00048002902d101522018000c40d0880070390f80309016181024109c0d0609108201e05494800020b40c8151441840341010188540e0f6080020515604894 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 985291798 1250 985290548 985290569
    0x1713090207020d0209101e03030905090603060708040f02180108100b130207020409120822030804020d0f1a0a0b0108130605100f06021e010504020a1502030d0612060501050901 77
    0xe0150b4280600814054180d02000e0103035a401307e5941c0d400101078050010b44c21800d03404a2035410040c000c100f141d0800d5000b8401c2d142088059100000d040c4c0c1c01c14014500103001c0e42e2103040c05552074420b840021750010a00d45141c80b204014105141a511000280d62101c801303100000202c4002007038180e04021280310403049036105030301408c081400075101003001c1b00c00d9590703a14224040e0303001c5008140c1c002e00740004c10313020b051403107040810300d80d250b400c202598402400e9903c004000a02c1551320310f10041c01c00c00a100c080c00760941c007690300c0050151000044000d80000c032281305103249401c00e204d101c2c0d80719064440c0501d400034007290701a00151211006040020049001070f40010400545d070095060000c00400c80340d405424110030602e00c480c008003070014455102da040c241404050707903945400d10112030760f4500700442e01c490207100381d0450188154070407550785440c0002070b510140c080042c41c01c80c03081e082001141c1e210706c104102c00c01c080c0204c04040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 985293048 1250 985291798 985291819
    0x908191416090203060d02030109210903110d03140d050421080a0515090f04110d0b0f150d050304051003020406081b160311060906150f0d171309020702 67
    0xc2d50703600558004030064103840c086640f03600481d003990506001201d9040c01e40045083c40d2401d500b81c01005c07000744c40d15a112900d1501c0d004842030f1510300141c45008602c5c184410103010b0b181020040340c01038802c0341c5501617080d4040007014100c1382698540c00c0003101c0349600c90101000c4004040b2070311042e40c5500e81000000040c80014044100d038410110802e60554038900c01c98410100c4810840c06071405103080d0011001001c0000d000d01c011424030301c00202c85481c03095108041c441401c1c05a03646010313409840c01e00012050700840302d47c040500307000c00800140143c13402038846078042e41450004404034400e501c1100b0000780804041000640b00c5442250100407010486062170129030000e5074481601d4021008205d58081071a401c64061190542c46a44100030340340e82d2600c0c02d000c0190205000800d8800ca940401c2040603642d00681e0420345904105076060281d44103401500301c1c0c0c0042190781c1c5e9184500c400280204030750003120905a405080804c41 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 985294298 1250 985293048 985293059
    0x50907020d0c110306160f030204050d0308040f06110d0b0a14060d020c030d0501150206012105190f0b0a05040210110c0316050109052e0908191416 65
    0x2c01da504484142001c081502103a40805c01d09000e0102c516020002c0b01018070041c041c0c804a403000002c2c5801488100b09960707608014503644c94060800c0b0703030207560b14600180801310700310000308014035050300c0e100b1500c2510040c21110614800402a83c4080010015030a489214030301d0507152016000610341484070142443e181880b2015003016604566141141c1016100c51100d07a0b4402c0100139080c0c3c4990101400b000300c1c0094243c5504060040b8440c0c8403841c1541e0600680320201010007100300b03d02207540c902e440e503121030244246812400b90072401001d40341500c0400c0030620000762485018082d950091408032400301895040c0c40040f511012403000380190401d580c42900c0910580c000e00040111030032900781450000b421100741030b00b0950283c40f4205071080c1525440c000c0c844400040d224102c1885d0134010111080174058011040718000c84d248044980d42400c0350300080c9120307580c00168002d80b00c211b259075400d242d01d00f00d003020f1740384070400030b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 985295548 1250 985294298 985294307
    0xf09190503120f250c080a0201081311090910090809120d051606091e05120f0d0f0605220c080609060918070608090c0d02031c120501150207050907020d 67
    0x34a50480d14040010982c503141c1d00745c000d2060307000e080e850700440c0d400070442da4040e004036401101c11050031056005c586840908004084086008051010116411070401c100d22705a4842842040c4401d00707551400d2511504140c240c94003510340088c2159000301d02003001440300c4503950301c5508003101c58220b010741c980c604106640082d40e920031403002c01e0740d000d82201c100482c01010020502c1c0e600c2c0043c60005089801402c103403081c00b011401484183c00c5038114440d0b03000100f0200740014611005002d03603400a07611404800382ca40c014101a6121030076031030b10702410400c00e10411002c0c1c0d440402240c4090307001d4804400a4514584aa0130a070400d4008a44401500e0203d0b410b5280800030380101c408101540204608001c04005113280c0c10015600300d2001e100c9039003c40c1d9282a40302c400d0380c41d401500d5603036811910035074203180650702d005028007503542d4850106005400b07528500c030045c0144000800c81f81880e801c1c890144e030031a4014000440d80110465 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 985296798 1250 985295548 985295587
    0x20a050d0b0612180c0609010e1314070c060b03070b0708071b0801090b06030715120f050a020406080a050606030a0c031d012705030403080f09190503120f 68
    0x750700410a0240b001d801030f201c500c0d9442803074290740d0780140c810360ba0310103854452030384c19440c4071368420414030000e81d03446480c5034800ca50a03540c2d85401116040b40401030940c0b1000c03410742c5221441006000d0303500180c08295140a16000c00850b54258103040e15594140100740740301504104400000c0c2900000b0100c42c0d005800c3c0c4542001c0c02e104100090740654024201e5a44404d143c030180420032026036001b810850080c2903140c50124107c1c03c1440240c20101405070004802007110b20b15000380244038a107500401c000e00c0d04102040003501301d40614400501c3d1782d000940c001000348101c90083d20000c0aa070705507901c0d1010f40014090720011001010344820007860002405550222010100c50001c258400029243d42001c4c03a90120040e0a907808070321071000c0f030340c0801103c080c0c03a049000180e031600b2003401400d01e0b01c5211203481c3c100d64404c650090341120301c2010300a4440031020f50f00500602c52007020540520907400c20342040c100110403d41e40c0825484 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 985298048 1250 985296798 985296821
    0x60527012006060a0e0f0f09100905060a1d0c0f010201060f121214030c07020d0510050405120403030e0409051504050304080c041103060f010e060d020d060603020a050d 74
    0x700918180c140c1c10415820058100c0300856006509000b06454601403075000744c400d4004000c2140351006001406444c0548031290110116000c210404800e104928144030340c0352060241100c40c0c5001036992104588566529280170f079410401325030800040403880c4420010840145120b04004103191951032042c1950b60325880000c400082c0c4c10b0361402880c411000118000c44d82c00e00440b0400d2501c404420010071004440b01c2c5032410094079000715034a20f4242c3c841a00b07101040b0b000ba04e402d4060810721a078140400c4011058004170300c501e20442c00c0e81c2d00d500c41c0d245603911500a50200401155491001d41041e09003507005c1a500c03402041201d4803131f180300040101e024001d807000e813119040000c040c06507410400c0000020f00b03040e181040190f00c02c0e00302880501020b055240300f00c40c201d0781c4840c10b80c819000041d25035002455595200f440b0b1403000000c0d131080035403028140c1020300004480d4020320a860110f289600c9117460301d0408885040241900f5144 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 985299298 1250 985298048 985298057
    0x5070812090622021207090f0608010c08041707060b090903090a0f0501090e0a1d2802010c0209090f16090605121c140a0801090f050903090f130504030e0a06052701 72
    0x601010103010b83e00041d00300d59400691580ac04688a082d50f4100074210306101c00c000600001505006001c01462002078100d0384481c2280350070400f0b840e05501465100310600140729078000c011006089501c011288420039954842003081443d010b445210b0201d03203065010072200407000d1403035074040e6510344009a80007000e2030012010503400050f0341e466010418107440600c02880d0840c00c0411204c2c01315441d689640024a0456040340c001d02850106001c40c82e110300400c01c000e1912005420f0360300342144042c4080181081d8440d141c0d4103404c2c1100010b140c107090101d10b10720350040c00544a034150344070f50080841403060301d403401c0140c0542c1081003c6500400381015120ba0b50b50440c00d549031000d107600341c40c030503c161054245030009000000c8000000c0b00d4802e04c01781c8096021508d00e01c0002e00110078441c15010741401d000402040644c803508c40c40710b480080b52514001615084111454054140340d1803424075940c084c082004000c2c0d12030031300540c0500d030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 985300548 1250 985299298 985299313
    0xe150f09030f0706020a050609010605090a1d1e0d030506030a02040e1501030f060b100c141e0105070816020a032003070b06040506191203050708120906220212 70
    0x742c0d2410382c10740d1140d0010707004903ca54040080500816030440205802030101d41e09050000702c02000160100c0d407c030ba50f84240c490000b104000c000c402e603000e401a1090b10048030103100500d00d40c0b000c540e1a03030040504041c25540a881994042c40010b0f00400460703855a0a0000415100400c130b0b07106c6c861000414050301120b12558040d6100b0038040190038024504002510a940801807107103442d03001604079164480c1e00480f04075000303516451102e4031500410704095903640c070784100404c403101c7c03a40e014005410040c040c9100c5d9403180c2081e035400060340c0ca000c4c42c008102006801043ca0400420b1040000c014030000d284051741d0802c0361a204640303580c0c0a800c0456180c0107410812420f440c0c07034031441d03a000728266560074404106542c80e1940340f04c1030040c6842d404d0b0b0b200d000800e040c07041c415a41029404001c0d190b40c0d089e503412802c0c800360100d1700103845100c0c1c040040e26043e400200940c0030b540000709100208659803c00c444400d0136204c030025880f4185 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 985301798 1250 985300548 985300573
    0x405060c010908041e06110a0f1104110c0709090b0f1e150108010e1b0d02040b120f010501180501031a0301020a0f0809070b0a080c070f060b010e150f0903 68
    0x410050030400d010b42030480d40840817074512401a8800d6003032100310f400d00003d03520f02103074040095601c00c4242003a20641c0c81e25001181c1ca251245800c14681000300e41c101060138004d20603400b001089540c41541e80d802c10040c5c61081c80f00078442c0d0605008100074600403000190440408505c40390011600d4a6448107220210740c640750004c1e2040c0a0002540c008981030301405035030f82c58885901e044070322040d9222601d0400c0d21903010000300210113906d1a415500541000d25003690b944c20b0005503240762900942d03010541c401d2240000483d503003e8142c00c00000031000c9022505840d16006400405e1280c0c2142c9010490140810f078a69081c4001c0040340319640360000d2900d20a0001040301c4001061509a0b5000840034010032a1980940d040c881c0c1a1410f44095940d00031081c0040c000c0d03040c010080782200070301c6000c01405403c4101c84c81c80aa07901c5001250410810801c48030307003421440151010444d062000d0403180c0100060b4070b02600700c0e4075030000304 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 985303048 1250 985301798 985301813
    0x190306090221101406161407030b0c1905090301090b0f01081e0304030618080d0518190b0a060e0406020910050a024308100608030405060c0109 63
    0x403505a00008002d00030803500221000a00d500180da0300042202c09091100c0c4440215681d41d50520030301c00450100c0c4441031040504072000c0e48140040d41580a24542550b00d101074001140c00300040d070700241162080c0380540700e03852401107007103031121501002545c0310b50207000301a425540380c0b840d10b80850390380ea01c5903004444102c8007440c150b00d0054150700700120102e03503400da442000281c80c1104400016241603079041440068000603031482c2658a0b142d40c48020042080822038050b168201d41c0203070b10600c0c030380140014890020000c581c50b03414203080948060200e507004030110b2a00010740c0d80c048992080003030010781b02c0302e4441d249001158122a060740000d00006903040085038800d900c2d000e03003406070070964940c00181d2074070382da10010102802c9000c0040b280002d0550380001c48100200b410801c5c10b051080e0340300704142c6018041881c032410040300f42154651060001703c9a008000d141803030b040c0410849694000c0303841009a640701e81e000400b04000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 985304298 1250 985303048 985303057
    0x3010504030216060306030807060203151306030614060102030a080705160f1709090a051f0608060102073204060509010f030303060e040209042a1d011a1903060902 72
    0xc2d0700200a94105801106140c03100764110000b01070900c1400c00004008500303941c4203551099003d41c4039903409080302c2d080384114500642c00210120148401030155020390b0940c0d0280780140209502c02d0075907580b0040030f44003140141c1c0204a40640c0501c82c22005030040218a4460300d010b00390b585005000f20102015281c035440c04031031404000c1c268012416450408910a092002000000300d0701c00c0000c0c560128182c480001a4040000201031000d0400003014507a001b620740074000c0c5520320413650306000d0300c16800007144a400c0407280700c0d8038110700c0c0c1400c6801e00c01c64030f1802c184810403503000d420030b80307641c00402c1d03d54a2400d420b0280c42085408245d2a195060040680b030a6500c201009030300203080c0005070700e03003042030b43c1d110790040880e0394400f01c01c052042c06143c5482c41c50032410044240420340c084141c2081d00c0b156602900031351566203aa00000745000f203070803002c921442c208204501c41070b092001c8a294001c40c10001441c50740c0f0641842070380d12 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 985305548 1250 985304298 985304303
    0x904140303070f1b0f03050a1206030605150f0a05190b18150a0207151b2423130c0b0403020411090f06181c03080603060c0316050903010504 62
    0x4039040c0043c07203150b106240c001000c0100000100c25402900c8010480b40e00000113002c014002890118144c0039800f14210440820420030070f15a580c14041c2c01000c090302e200d100900c4c0080c280c0f580d4585007a4000c0d80e8a07005100f0355003680b4040c100031103118030800c0780004e103242d840002100108a4003800188a010751068100744404d030410640d00081410020708080c18040341d82034030340c0018480191030b81e94005c2c460385643c41009031480f0045e01450100450500015020450041c1d03100414070307a084500b19402034460148010fa41c2c0340202038a141c14010161281e1007000322005030405000401a04821f20316142d12110640e08d400044407000000740030400c5050502c10300848201880046050440740e000060f074041b03007849114407581012030040701a440900ba00c05040c403004062003458161001d08500301c2c03d00c000103802140041001901e141000b1503078521a8103102000d0740b540e070300d1407a034090a50aa440c080100501800000301c1600c0c03d02c5586d009030b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 985306798 1250 985305548 985305557
    0x604022d040f14100b1210090c09030303051b12060607050a0606060e09070203091306090906060e06100909050907030b010e190c050d020f0f070c090501050406030b06090414030307 79
    0x500c0c0070443e005203034018044034500d0f250140c0c1000302d000e0040594404000c0411040400c3c0c55450311011495003a8011540312071401d08010340341d076000103046c4112442a03c0a1003160756240980b10306217051102c0c0c20690104101030001070008003682503010000400050518046d034075014900400d044c821101c00f5501c0718180081a00540b42000d400800c803036100052134000d100a4481c00340c0d2000a004119200ca201200c21141e08140c2c050034041c002080300c64010f007030590140201c2d10601c003081400101241c00e50409040c00c1d0800e10342902c0b407003140c518001000004190040ca10442d502580c00080000307101d03080c846008040c40c2014030514106107807403000261940c03a1800340e1038545004400881c1c2c0010a0310a00c2d881000010b80300e814440100000b449100468182c6240c00290350041101d6154610103946c0c0c0e026040010743e0300c1c2d4042c0b204a031400d001c0900390080c10310000710b5034030301913420315841841180c440b090142c10280c05465500203503800804107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 985308048 1250 985306798 985306811
    0x31e1508010605030a0c061115090c0f120606060a05190905030f0c150d021308072412090609020409060203152b03170903040f080604022d040f 63
    0x2036024091040500000c9000d03003495181a42e41445202c4c80b8481c0c2c40a1090101061090306014442c00c1c8104007130750842c5089142034003203207848204404046100300c080c18264003460420b0381800c2c01c400503000042ca0103880e03680070040f10b50003500b0403504011080120b981c0400301c0140e1500b0036807680e103880e01400e0800b010141044520142c9040b158010500d0a00e5642d9044c08003170742e04040100300c0d54982e080712100010780700e01810a01ca000106c1d000143d040c800007502c0c000c440944a01c0040814140b20000009089941e21030020381c154480c02d80c20741d4168031000540b8407130f450001e962049076021030187c414502040e07840b9a4003200b0480818024001c0d1074513100d088801d01c141c1c14005c1e54121050f00d40107411100c50291641110425004074600320b240c00c10b01e1100700047c603100c880715075a548940102d0340714011850001403040302c005a41405540d004014008022002c40e8414080010000441001250b0080c40000b902c07244074080c4030f403a0009001c40d26 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 985309298 1250 985308048 985308059
    0x130606060905090f091c12020309061012170a0c02100e1f050f03040c05030f0307061d060a09062007020f09010b030403050a02011103010b0a0801080304080d031e15 72
    0x4480007442d07003c8900744c280400c4084440030a508000d1806a6104882040c0302402120002d55200c41d4691262002003481200b14002038410b128000c40b11044c811140c0712a148840c1c40d0007448005c00568803228035844203001c0c07401400c90110949012910308420783c0018900b000c4110181c0f01061400aa028131401c180b002ca40f82d0301401003641c1c0680780507000080030303489488401310000d00c020001c2410003040b62550002494010100c601c100300c6a6078003030b1641e0100b602112454504056400341c6291000440720318038560000e007042d03999003250200901080c0404035051551580d824051010745110500a61031808070b07142c580959105218400e000c01d0415441035442c04010019900c500c02200c0e4841d038546012504c415900001385d003d050100c0046c10100340110000c58a803c0c2d0b580034101036160340d40ca0a0841e641d41204648a1288c0c0c043c20100b81c100d01c02c89042140a078200f00540300039244400d00300444403150354200c0d103400e81604560640c40104010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 985310548 1250 985309298 985309309
    0xc0216060f0207080d170a0905070e09160609050120030d0b04151401050708041d061311270a03140609030405090f220303022104050303070305130606060905 69
    0x14080301c2c0c00611402c203640a000e004905803822402041b03000c480001c040742c40941000c221181e201c03084814007522003402000710319045807002c3c020310451a0013142030161090302800c80d0007580b9400d00032810080119003400d40d4600420711540c09480d40819104104020100065155400204000c1e044200001d0352000148034040d280303820400c0c80242024801e29901000c24200700d5500c0e0380d80c0c0b601e90b41074002c1d903000348074043e0b50400d030680340741e00c0354540c0f403041208488003040c44040c0b1f1000e10860714000246000103c0c140a11700256407400001a0104907403081940c103d10800000b52103504030382c101b2a5545100d860b1201855400c200303485c0c005083c54051410541440e0110301c40c004001d100c0380b07410420b50003003100c1000c8242c44100c19117421400c0c020401c01810040c002e5800401c0c0a503142482138954498042c00c54207103402198031102440c034544075a0b000314003800001d40601c40c80f0b2080091000022080e00c5000010708042e181c1c0761406183c8010080d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 985311798 1250 985310548 985310563
    0x120213080c0f01050f0d020c0a05030c010c03180b011a070618060c0207120305090d02061611060a0c121701030b0405060a05070c0209100f091b210c0216060f02 70
    0x41c18002c05000307242170f40a0050a9a950713002401e030041e2224804903140e4908030782c100340544240800149114980e030190444182c00c941c64405000c01c0302c28141c2c90191140418016041a0300300006200c5150140381d04050000c500e02007904040e010b458150840e803a8503c00b160b500b0305295030380d00f04041d50040c00941c2c1c1c3d86001801c10140b500c3c000aa003003600f10002010440d00007401089640d509100280ca20340241106032580d00d1145c109040d086a2402aa950040d00450b01c1152034a14100c6000d59003617030301d5861000055950a0340689003446000510400d814022620725045848500840c05011414814101810814141440500104440c1d803c00c0100322920342c00c501444030030b0b68103403100c1d241c640c0c074413150740e45140741500014180e5114090001d801426a00b0081c08442080c0c42241a01150310013600ea10b18180100045c0e8421180c01010400d050350220102c904540103848844075190340c51081c180d6150000b0001c20b600301c80c3c00408030360400030304 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 985313048 1250 985311798 985311829
    0xc070824071e050f3108030d09050a05011e0c090608060909011401080c010806030109210c05011401080d0c2d050a08120a0219120213080c 61
    0x50003503003048440101110b240503220103800c0203003400c1081c00d5103c0c10480b80c0f0000030001484d01d4002d11600b5480008880c40604c070b90500c241d400c0312914103542c40c40400c4846000c010341c6800c80c0200010f000d407185200030f54045c001c0004003c00300b2800c2c021002c22100d881a4464080f607650000400c03251085c005000300a0144000c0c010150401c1c145600500100c50051a03580c030b00890901408501d8240c0b1000032806000092450703000809191014090301c07281e82c907030745040c01c0c54220f4211046c060b004040e00920000c40e0001c00201d82c412082500d0620f800d880252200381c00e41d40048500310040e00c1140c0100190b01c0180072060340001c5910380707008401141e03183c0890020a1030b032a41071240300905c0c0c1d9006d4000c0060351404c1594050283c90368031103503082007860768000e442c00d2007121a44030001080481c061003102c003d041007544c00c9204a040490880b0700d1402c02a8a00f000c82d401c201450900e5580002440107204200041080c00c681d8028441c4c00803220b07404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 985314298 1250 985313048 985313113
    0x6020a11010b150705010f0c0e0411090d060209060d02070308060414072c130606090519031e020409060c0f0e0904060b0303123603071203020c0708 65
    0x200c459503c403030480484240c030038050b5481d19000c0c140140188900101410a1850032840d000c006030446040118074000f1a0200038182918000904a201c1e40c4802a802004401440001042076000e0002d10b0130207052182400001a14401260710071a02500480c41d04810004030345440d0041c000016109030001e01c582c100b201e03015043c8541c0017918031004a0b441843c492200007a1607910f60010300500c050700d064410703841d1200904050203101c001801001010415040ca0523000540805403001c1d800318603c6d43c1c6885410310050300340c00c40d01815946106c000740e65940281d172003083c051880000c2074644141c010f081d080311900d0520501090b2102c118041c2d951181060b0b005811810100300f4060050010781184109004440317080c1481040c007580d524410b607100071a180c000340001d29451303400f40d08001344041098404944e801009410001140d00351410611000b500300075043c00071014105042c000c003a0800e0110f6800100c4841e1622880040401c0d01c68140d0007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 985315548 1250 985314298 985314311
    0x812091908030711060d020f1801020d0c06090501060e0c0a02010b090c120901090501020318010501140a170a150b1504050a0605031b0d0c081b041503090204020706020a1101 76
    0x1100351603014032600540050201c0c0c04c402080e03202e500450345000c100b00c0045580e046000d1801c030140d041101a503800c03055540c039044695000050100030001a611410300503840303940d0340c002a0103103103800c445a54071081c000401001d0007015600075118450340301e4440710358160090840e07000491039481083c0c01c0050106411242040750340e80115401448891368802156038090440e85000030420761000040005084609502d4a250745052009100c6a640c0e02080b00710b0400c0103035007a078044800d150030003111a41c140340380b44841d0440103a40703200003161683d03c052818086403840c07045d260219040039140c04440007400c8113000c1074250529090201040d50004503000700b200f030080c0080429000440700d20a0400c0e1020301c1c45c1d0030745c0c403000c0d48242c0001e44102e20140340485c840b20003003000c0c080e1103440201d0306e51468180c541424030340f459a080103071480c1c8000090590341c601480140e210350004142142c00760001595403004080010180059001ea0b902564035000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 985316798 1250 985315548 985315559
    0x2118030e09071706060a02150109050609010603061809030c120320071505040206040308030103051c080708060f0a0503030c030909090f100c03020906070b180a2a08120919 75
    0x69482e50800001d417080d540f60072090005a2503c480700914118021511f000040d0011180e000300d44686030076030711304840b0b0340d07a981e0590940390140600300082407544540b0000610715805244028000e1070a004404050f4466505d5160810b000710002900c9024000002054030b0752890061002d0748218035081c45501e03510400c0c10502d03c440c1c41e054850000c2010b40d550345007924040d680000c21156039594a2810300d0761107101240a44503622134180840344c1e0750182410303500c00c0410751115445952982d00b00201c0b14401c4151a5005108403404a01500d00304080c00c03001311640000c5503640f40380c4042001400c070050811405a1141e15002d00c40700c4045404055a5010400410f03070b00842c61065020740103441074141c11140201ba4001440a0b92a41c1405580081c60302020780070104001612070414081c054081680d51000b0030406d40820225846105100301c3c02c11010307216003c090401c2a081d5020010a0000c194400c441c54900e0200407001c40c04d400c583c3c00c091424 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 985318048 1250 985316798 985316837
    0x40c0c02130f020c03040b0d060608150f03010219050904050f0603070b09041b12111306050702150c0609071d0604020a090807060207060e040203072118030e0907 71
    0x140c4003403109490340340c218603048854064a540c4071000741900c6d00d41d601d84149200c145c01c1001d8400d09141043c10000e04180100c1e64103000c3d42c7e001c0211042c03000c550341030221800e80e25603180c0d0035640c04c1207440c507080e100107010300c441c2c0800e5407030356602c2c034a04040006072400134140380c06654003e000c2c44410341c1d00040010850315818082600e40c40c0c000300140060059469282c82c1e001c00c108542c0c2c10f540d1142510700c0c144109082005403800480c11010075004410701600150301007401031201030301817405403070024401000c681c2c0742e110444240181e81c100f400b68038519801002842080ba00c18050070020705107243c10401c402c03001240303a080d0010098451405150300041c142e0f03245100b1403401024094000132105125580c510081d43d681ca648500c0c80000e084400c90015881d090003105d00803e5030755a41d49012054060500c10a5100c059000805a44404054940364a4840e496641c0d000783c4a011020403000c007130006225005110000f0010210710324030701d00204 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 985319298 1250 985318048 985318069
    0xb040e0c090a2304061521020a0b0403260309211201080d02010e0c09220506040303050a0c05031605030705071509110a0b0301060516140a02040c0c02 66
    0x1100d00c1e501d0742e1622218900100840b8404042c20040400710081070051210840d000c0c0744525402c200da03040ca00848070b01c42c1d03c0c9000c2d12002500c007c4603208140001540790491600040090b0300032135840080c0c0b40d2561040e402101c07000300303d00720641e814165241810282c0e840c140035034618034100c245240c84020b00d03040100d006190030041c819641d502e0741601c83d03203007200020b44019611410a2590b410800b1340070001982003142e010702099001c00e4428a83d400540312440c5915030740041d003c0f0802e4885071f24900b691401114010036420001c2c540500d009460008143c240001103000b80e0303908210007800d1040800502c119000b10005002c40c21145103450f43e16030b1920901140d10744101c1c00090b060140c1c0002c80c1440c01c18036480b0a140a1203424032400c81829202404900350070340c41405010300e0107000400c450350045008004000001805440b031100710b035514044000740080c171484079031200860b242103091078451503d4803000c6052048815110781c0c0000c413036062 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 985320548 1250 985319298 985319323
    0x9030a080a1112071706010f05040306050601020a050d0906020705010815040506061c0b030c1503070e030c040501031b0801050c04030206070507080703030c06060e011a1308010204060e040b040e 85
    0x40e2400d10318442d107040300541c0d00100308040d4039012800c0c050310081502c640c030002c8410110b690070106d80c0c1d40d03001d84441c500c0d0404503212541840d1540e102c00b4001c120081c031150550103440200c0002400c14410000440d0031912101445410000001d18050041d0410383c1844200401c0c01401c60801c008001c0544044801042c82ea541e4000b040d6540a4400c008981881c1100ca1130180580c03034020030604802642201c4256041004100803040704105250a2010070004144070603c100f032410030445001d412a080c0c010814040380856209078010f071019643d022100381005070440d100d200a00001000b4049400d06602c20041c0c1c1c80f4501c0001c0c4100f000003041c8003040000d0000344018181c0348140c1e965660791b8140600b00301020801140c2c2d1030b1600001040801c0300c0f00a00c1d068886144410000e036003052014207850b07110b80101c00c4401c1002d000055983d809000500c0540a01d0f0b45809501c0801001d100541e007030940321910540c184981d0341005034000401d8046140d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 985321798 1250 985320548 985320551
    0x614012402120d1a030d090314030f0301062d020d0507110a120b1806060f0301020c0d0905011409101b0606060228030c3903020909030a080a 62
    0x10035146040c0c0c0b510030200c955074401c500106500f070710b01e0042d5125540c614054014018400015401c0540b0348010840800110300404010f00c003050400740744241e41e245250031207113409010b00b08582190030992214001403001c1131031007084498402c00303016002015180701d0b03034140310380c2d00a922040010301c0e820822801141c00400d12600303103031116004001810111929403102407000d200c1180c00c4040d00c1070504240030540c1200c03007095080d08442c41401400302500d034502000100d1000b0b418041e45590203000e042c06525081c003100c000100580c5582c44510310b420005081da104944040481560030f0051010a03101c0c1609506641d503245084154188100924291070000740006801c1e14a02400440e00e81e8000a420400d079100701d07a82c1002409c40e80070070942400214004000444a60a40b00040c208040382e0161107103041246031080155162503018030b0000c0400141050121810003e50802c044184c0d000f2001c0c101841c6080c010784030142c40982c015005a540f035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 985323048 1250 985321798 985321859
    0x60c0e01020f0604080d020d0608010e0706050301031a180d02060403080601090605090909150903041409070c1103030904110316140a0c240f15050f040f060b070f061401 74
    0x20341b154125280c0102d240c0b010041d003611607021500900c208045080340e4800d8000114615001e141542e04072548204011a0b1401d80071081c11035180c0580144100c041045d4004040881400010781500141e030080125143c02e003001000128007421240c180450f4150620019034404103d8004280036114120607480d5000d55514000384941c1541a5141507018000c6c40035010004000b2140810560508000c0d1700d410080c0d4048161000c402103080d0019220010310b0130301c0d481240401c0141603c2c00c05916101040c140c504803808425514800420400e12120910385d1211550442c80c0c2800381d030103030f02d2101c2d0b80b03441403014400500080010b42c1c0700f017254a50440e07600348160002b003514100c0e001c0b282400fa010306088074007100d041c622902100805a80310758110350004001c000107920000502006043c060a04960745841e540c010075045600b80040c81992f220b40c000d00301000b120700f03210040320300549014a82c05611130040240d091101300d1444013144000d80507210 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 985324298 1250 985323048 985323067
    0x55020102030403060615270504411e0601080604141503011b0e01110328120c08060105211302091e0c0a1e0504050a060e0d0b0402010c0807060c0e01020f060408 70
    0x1284400c144107044000c480b03030300e01c90480d51612b145da54241d01100c031922680390f200010041c8402810f03e610403404a0001070243c0d803103004031a4000383c024000040100e102d202e64544581d04940c5294280500099003445e03003000d2003000b204880540048144c40726404000300010110406141006280c00d5501d102d90740600c06c840c0d00390300400c861a030407036825204124106800d5040c10101d01241403021500c81c00d8003d9484040d80d40c0c2c2d43c510380c0e035120700054a81d508445804007581182c4a086001c486c0c05007681401821201c1c9a504809035500c10001590801841c0386204e10741c07203100f0b5041103035500050760801e40e00d074480d03030b00d0310300d81c200c2118404410106448040388101c40303600ba094001000300150f49094420040307464881030180c40f98240342e810240c00082c0385503560007203100100b0f0b10f604140305240244141c10030743c403070f5034050b0840d90080c3c1340316030f8a11005103070703540003840104050360a0018102d5849134801450f02c0f50380042c4058072090001404010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 985325548 1250 985324298 985324331
    0x60114012d080105040c120c02030c0a050a140a050703020411090306040308040b0106031a151c0b270708061255020102030403060615270504 62
    0x1e021608411522041d40684429000100141034100115850400120340350815000e5180e0766152911510000c04240215030001c0403002c450104501081c050054480001d02442c07400c1c80c0110300078a9400300c10709142003041548941e040a075801001544c00162000c6105070889030100c90014811010954030600ca100e0120001d03413500507002003004154004c80d1007401507002e004004020b81c4c8940f0150111094441044040c4c040307481820b41c1850410302007610743c980505400d0510302c0100c100a402d00042c1c107100611902c8840d01086410304540c8090883c8191a44c5032002d194540360b040d5011001d0071480802032440700050300e540311401c94001c81c030b105a084480b8649012550384095410b00c07041d861380b4041503a03101b55148100c205020403502c40412841c52443c0f2950701c4000c207107110080781580411700000010030054412400101070900d4113007440d11156800070010ba110101c000484140e20842e4010481e0150100b801e03154280d60006402141406024 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 985326798 1250 985325548 985325567
    0x403021f030b04061d0604020301120f020d0501020307050a11060610030e01060302060a02030c01140f130c09051509060a06090b07020303040321090617160c050f0d1404050306011401 80
    0x6403c182440d00010b200e0411a210094115810755a4012038031104204030982c4420700c64034140b180c20820250100e000804803d87c2c4d030f1b100400d4600341000355540e980c2660800c07200c036404030b200401c0c0d640c00309400031103203203142c40010090301c010710f403640019031488010507a14003010368942103041a008250f0146028640042601d512007541190003507491b488102850801c2d42007100e44c00005641c4c400d600d014142c0b07004001841c0c3d0b94818041c00882c0c00c242c040c6c40001d40b0326000902e0a0661150038000c043d064000c004408046062105200000d4404d601900180400708183ca500483d88000c5c0d4086022440c0c0d5804c86000180c911b0060790000790100c072921950304c60020603512a10040340c03407510303000152647ca460503161810100100720018001200150300551004020032203914903040c08617880e0600e071181340c0303400400200510f980d44500c00005103542c01241281c0f1824402542030314003410071000c641c4039101885142a21604400c10a001e603000d4183d24 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 985328048 1250 985326798 985326821
    0x1051027060b090f06030f040b090a0b01060203030a110a08011a0702130213050105190305060d05151918080a02190c090c030e0a0b060109090c051308030403021f03 72
    0xa01c00c0301d44551540d0001d6002442e85403081a50044e004076904191040e43c0c499021a02030211650300c2c0e0f151030000f90310040103100c05025125100300001d014149141c00780c40700f40d008540b240f5090024070112408107644901c0404288900e0300c0207039100c000f16054404010030100d41d8040d850b0403080a0150480c003e500c011a408103000c1407a041e40034060b0060f81f214503c520760341e540015a05031042c40712520b140400c1c2122105094069001070750030800103000746c4902000c51311500c2c1091005549401e0104281c42031042500401e6124840b410b502042002800c85d22103075004825034980b001801540049140d10780c05000b48022080f03120540981d050b00d512500d44400b1020040c0940c000b40391074802d12032070781c522034480c1005141070080213122805160300c9039036114200400c070a04000700c81d000402e0842050144000c0b00c00103403200341d182d415030b4880c1240301d0100e40180b801d80e4000d000400c050f0352003855441101c035200103000411119000120040c02030584d00c0d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 985329298 1250 985328048 985328051
    0x50304030315230631090203090607261305010506040c0f03050a0b06070c060909110304020d02030c04110a090b0a200c1804030314150f0102030909070c0c0801051027 73
    0x80021172991444122154480300c040700d40820380701c4a80030100c1c0003e0b1425002e6038400e9000860356800381401102c444000400c01503401802d104065041004650b8034040003030165a00c41005024003c9540041048505101d0b10511303500040107860707031911031070401d92150701007100043c196005c0b603454840500510390301c000500305909244214071448000a052500008102040b071181034186041802294503503121034081081c2e4202251041c0e9040c0903500c12070070144c0c1c5621070ba20000b448001000d0b1107860f8880c0c05030074030409038400e80c6c411004009550200d035100d00c002481c500c81c2008100303010000341c0b00c80d240c102c41143d855080000840b9101c25181c03e80403181c4500c2c42950140240f10460090703980d400800d0394069281800c00e01389000d91b141980000301c1508061044074200029840015485882516800045114006540140118405844041c1000c08000d111074100a1006109803041c0c1c0704003040310004101b045008240c1c500c0190401140130300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 985330548 1250 985329298 985329337
    0x2070804031a1e060f1011060109050a0b0a0506070605100b0309030403110105090a06030e01020d090b15030a0b060d080c030c0705090108010c0206010b0f040302060a0503040303152306 81
    0x402c22100c1c2000e840088640c0409840391100104066000b4420000945100c070303403c90302c00c2409510b0314000d100e0424494400902c0c00340600c1041246c2c003c0c542541d02150038140610302104855103c000d02e406144540401d02c100e4845004907156039074800000070301c56581108034401c0841a400607090004001700340025150004060800e407400361030080102903011005641c0b03803041800d601e4011850141c10007401c0c0c025030007071002e0103003030001500e800d1241e0300a00403642402822903034100d01c1c2c010b1001055803140300c4c200011054000700344005141d21400078004000340400d1140042020b01070400c0000020303240e198071000c080b070b80c40f800100c554640701c840c176002c3d0318013401001000044030741050041c011040c0c40c50300545100cdc3d0a200d1068941c1c0d0024400c4c80b02c070b2104100000041e01c84100400400005a030703155128281464001e003a00d0f151030b01e400d100a41c492003030005a0b01c070740d01f500102001320a616140704050000c90240d000e45101c48071681d00c40e52 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 985331798 1250 985330548 985330583
    0x1409010f0e0c091b0c06010b0304020112050106080609070201110c010207060f06030b0103112e0f090b0a050c071203080103050c011d120f0613050606120d12060b04090b0f0d11040207080403 83
    0x20394040e5103762a0401d1200005584804035a424880c250010707491401007403007410300700c0003183c00c41002c2c400429001400c80b8035111692158503040420783d4005402070900421b44550401c0c40c00c3c01030140041c521350740700c51414100600004c0c0c100041800c0e001200e035181c0211b01c4d55500214003d49001e00d00b194001e0528581044440104102107420400d00b0320446180065038041400c0905000e90842c04a0f041d801c40c0b00800c03582c0c40b8008021038a2604d0182005144e88240e47d2a4695030451a00c1400c12210312015814446104000007032050703488251510904e058601d000b101080d100260300c0d040412895000500580c0d003802440070410004640441c0684112440f07510b88600b803002c00381c1c010030762168580006900c8049248500c040702d8040c2201800840c440d0b4480c4e45496950b40300ba80304007031465840c4414042814650307200048058200da844607014141c1e195440300304004007000e80700d01d0380001e0850400c0509010f65000d150021b0b000c416040310003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 985333048 1250 985331798 985331819
    0x50906060d02132d0b01080412031805030f0c251503090605090714030c0604091503120f090503030a08040803070c06060e0603150108120d1409010f0e0c091b0c0601 72
    0x15604000d1585c101040c410095000780340003806503034041036055191041d03800490003031550046200c0c80801801d50000031442c10005891801100860307030341d0f82d4420700720080c039000c820022007159089420003200c1c9000b0210b145821985660100f2204a194810860044c214004001c002030f29200178480c8c900030004115041c3c460340c6a149400b10582d50070075985540c1404e046500c080104814801e483c1d00e90480d5007900300f180f80e0200c00070340b02c1e590032651401285030040020f205445050b02580d1118892004000c29809580381244100700103140b820000c00c041c3c00320f4000000325020300d208080c948c416582100041103641e848031603a030b801b80c03015a40d0302d11a100c0c50079011200466002e400e4100d40a078401032100910088000350580c020989a0b0030080d51040c3c900143c0a807640128880d80013540002114181c4122110441c1c4004134282d80d294032005507841242c1785c0300b00890700120103100d460310301c01c5860000341382c030b01c01e4540e15841806070500000341102d22 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 985334298 1250 985333048 985333121
    0x2a02060f0f1c0c170414010b100201021312020907210e0606030d050c060a0903122a2a08041d071b0305070f030c02030619050906060d0213 61
    0x100b04244030400750f0020482d1241d04091034000e0407404c44012a002074181900000043c41d09000451941d0002001805840d80200c042c805030f500021000c00054503940c10360094000c118910b0f03901401500800c2c510301c0001d26040a01c21800c01240c00c0f510400e00e42403a0400310442403001c030115481c8182c880e036003912107034000c4c03049400406804d03000318156a01c0303c413044000e00d502c9c3e440c1071103e40035240c910700c203030107004514055204501c02801890003007010343c84821001184d01c88418086400745884500308210b01030548100050032071009503541101e8402e008461032820140903d04c500d0f07101d002a005120343c40c1c48000716400c0c030940f2860160300c8200800350920200c50300404d1411008001840401400b800551841c0c1c409038030328001d19065161710310580c0442e141c0b2800b500c1e0b1100070720a1620703100008109006a591088680e00604024101360011030100c01d03550b00000e11030f602c60481c00c11300100692000d41d2098400c50650140f0032042c103c0c190301030344c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 985335548 1250 985334298 985334347
    0x18090c08060117060c030103020d08030403051e040303020f0c2d060d060510020118030518100806040b0a0807171c030b010f0215010b09120102040305030a2a02060f0f 73
    0x13080f0016183e000f0b0070f01942c0c12070341c02030100c1540250554948450b640700910850901074240600b0600b041600e000030450710708582490f6480c0d055040c0a0b10f003190804070b030728059000c0d100c500d120b902c0e10380582c48298549081b8011014000c5510b00c81c080d00c3c8002150045408070700d40441d130440350032800480c0c1c81600e078050050081c0078124242e400208014102100d41741c208400680724400410140b002082c82055200e11480000c040703402010200c0b00140c40760042c001945014803940008641c119405820b0901c2d2012550300d91717107148140d80036204141c0c40c007000984203111200e05283c090380141040c10800801500074005030f015240014484007040c241c06000242c2c141c07015000440640080c0c4c0f0b0700311080d210340d014592068114445080548040c8000d001403c0591b221304050340e250321412900902e414070001e05035403402240c020030150003040154410b196601646d10603960015000b140100340b00700140310b520304000180141c850300c07000d12000c40d501c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 985336798 1250 985335548 985335553
    0xb0f090a140c0403082b02130311012a050109020d060507180b03060409080409060306060326120402030c090916060e01050901030f0b06040e011503020418090c08060117 74
    0x460b49007031507886010f1400002c0000e441007007036540e1120303290140b642540341c40040314404011801c081060380c000c420344c02c40510100d082030003044801d03519509020420300c0c0058040401c10700444084112a90f0410b200c1089590784061041c03e404c0000500d8002e4400c006c0304e020380c9401001041e08840705400142d5102091440000c000001011104084e400c1400c5499a0701040000d0410340012902900100000516120300340075220045010361030000d44d0528504020320a64034030480e81029181000e840380d0401c40c070300c09989100702c03080da10348d1a40d561840401d10744118141c0c150384c04071480c0304000000300c00140e000b000802421704841e00d1a624a0309941340820750030f0303c5000c0b40080c07140c110305511aa0100145614013600481d0020405d008181a5405a044088044010030040c4030340b4540d40380c004014001443c04502d0540342403001d007405501240180c1c0c04548078140d500501041508070009408880c007503944550792170a00e150b00c5c420b1a9039025060 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 985338048 1250 985336798 985336801
    0x7080705010c020f04180b072a0308041209120b190e061501030615270b030109050408090307090c11060108060a0c09090504030207050103110a0c060b0f090a14 70
    0xa521903021140000c3c2e0141ca010030300c1c0c0c9000204070207820b1101408030f20904030000000881c100c441b01da4051305094641a880c076108644101c0d0484a11071110001c0000e2122100000d81c0300541c07950068020000d4000d84610000440e00c901280d401011000c0c1d2a182500501c08844030103400380c1782c8500fa001300c44200004500948000111740a05034000c1c400040004071110940920445d05150000351140c46100402d03400004044080c001900780070543c0031f440003444500310034504406002d44003490712801d141a8401401064040c0781c0300d401040c200609401556440e040041c1511002515401d4903002800b1a20305200020031526100381c0c420700c04202c00d810b03100c2c004080c01d82903a5501014000e400e02441c480c0c02c005032020005500c02481c41102e0045200e540500030391490036000509941d003030700311180382c007404010000819411144c4c0e0441c160340003902040c0074640000040c946180c3e140a02d0700007910504110034041ca50344440804070440410a405 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 985339298 1250 985338048 985338059
    0x308091f1e18080d0b130b12030301030507141f0201200a0c140c180105031006060e01030b0109081006080d020304030203030f07050a0213050411100c080306041409070807 75
    0xd44140060314a64128070100b604081400300000307242c011000b41000c0f0f00d0000c024042050072052021040c03440d40d44048031425803a055000d04d4020b4490002141154159122582c844510b0310564079019011007100724692510b08134102168103069021140c111a05000b82c041c0c500e012596840c0d04100140020b6194549c095a00b070075001c0c0d072143ca181e5015500c141d4807840740c030303e4680d00e44903183c6c1ca05010b64841540500803c4007100c1d0610a500d0b100030b051610050f80c0710800d01c1420700f0028003410340d2003401c4151400003442c01041c0e0313036805401600d000d00650810381070760140d107868899980365500322804607641c250484400c1c0c800f00404a031a03000302e00000b50316810401007030100c200c03108080d00301e81e40030300285d48014415900282050031403081081d94541c98008001c24042000c02c02c408003041a507926645000b8100000c200201c0004004c04620011001c1240d5468960001e2444a41405007403810b080c1b10741d40d181c5e1011a032041081c83d100e030200100e04c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 985340548 1250 985339298 985339301
    0xa030f020a0f1808120a080603210a03090501110711090709050d060605100f0806010905061c020d020705070302190609030803040f02090703050a0605030303040f0308091f1e 76
    0xc0781c903601c800e44001e5082c02140c110140250482e81200d5051001c50301600512084440c0452004996031740d8681c580068241a40102024881c1c0c0000580c03280340200c401c1440024490724044070b54940150009034018040350802922541ca410146a6401103010060043d940510b04206010b00711703508129601e0b0044802d200003906040040042d407d0010000c2c0c0003d1203100c000c10301e9034846000ca02515401190000010048420702581c2c40d049440340c0e4000c40c0a18102014608103004911140f0440001018440c1d9400c0c881c10900100e5040c0c2c1c02095004905640d40c501c44e040c0b0310740da014580026445540c1d00c1c014403d000841c40c2104044074401e840e009561459501c0c0c00d40c00b90402042640c0b144500c445034001607031484802d0340f00d030441e601d000581d424244c2062088410a40105001e40d0080041c0700c0402c01d1507038108403055262a042d401c560316085000d080c11148501a644098402403610b0003245541051003040c403001d58025004519200200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 985341798 1250 985340548 985340557
    0x108070f050621061201020a020303070912020d110102071a03090d111c050d020a090905240f03160b0a1b11190b0c1c03050c030f0907030c08030a030f02 67
    0x14030700341503003010740e0300d19801d81d0306507072000d0300030581c0345e4980882c0e140c5800d81c1e020380740300030050f04000104007d06811410103c003600440c550354141020340d50105517011003100000d44024170b0f05144494a80c420441c4001034141002041083d550390035680403d42c00686100c01c482c05100b0364005043d102d020203c03030364031860006102c0c149420812182014502c03c4010030444100039440d00144207000514070f244035aa13a00c1090340c500300c030400459201a2803159001d420900050100c01501102e0101d80c5040320b0314004c0c4003880e40060724103c00189920f820044001d0001a10105180135216648154941b0043e003440c0303034000341000d00f0389075000301000f851904000700c605284405c1121620303100e01c0140002e07168102d01c0d80a800200c1141002d41c007004140c0400d04100d10440c41c644940c0c00c040c0090b0800b4800d164503400b009040618440310f600015a81e00001c03c450802590000b80890000ba21500e07920307144e03401750318944042800c1018804180ea003c0c4200c0b03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 985343048 1250 985341798 985341817
    0x10f020a0c0809030a06020418110405011706120106080a051c080109050a14101d060904021201090f0c0303170c0316212f0301031e06050108070f0506 66
    0x241e52516039566881860b40001404940500c40c2c081003e00054052004002804440096440407002c002204013a00c1d092006d1001c0407105001c1042070b6600000310070450240c2d9502c2c08015540d500c040341c0c02c0395041e058180c00358240280082c000c0e8010503809401170043d0142d6070102d0108a00a03e44580385040d4130016451302c0040100b8141d55200d0780d045040c43d040828410701c0401183c80c42e01c42540c4216020110100c10000820044140c0d80422501822006589010800101c00940052010b4055070300b0400c280034091013913201102d642c2d40405003d849040a06150b01110140e0200310040346030700c40000700290b40108070034402c4140700403241c03450340d807030482c5400401088102014081d5496076801c200380c40740d480400c04003690b03400050f00b400d40c2606070801054008070316a04d100410071486082c00304800c5a055a4001c01e0f41003c803c1000d218402c0825480e8016040c0c501e41000440c0b1518082038200440f01c480381c2c0d01d01c1710303038803901005194401d45084 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 985344298 1250 985343048 985343057
    0x3060a2004061e030f0c09060f09050913080c06040c03120507020906270109051f0b07031b24060902090d14070803040b090103050a060b0304260417010f020a 69
    0x1126500002c3c03481c0c4000c1c00540e140109198450600510564204c0303901c0d0408540c01d000d0238481a40e0103030011004032264030b0008140e901e07100114900c494061324849049240c0700c00c440910000104652008012400705c894610380f03400c1c44281c00c0c0c2c0c0e500048841d0514061048903441c441c00540f401303e50020a034032080e1300d50f6001c01070000c82d0101000700e103009074282c550800e021019540d000f8280e00070080350529042007507030140c108581d0710f101404030041081c4020783c80344007961801541400c0c82428921580c0d203101e031000420301c0080a8504a540344118200f1540c078800441d1441c072004c0c400640c4505100041e4012218103d0304500208181404074010740c1d41c2c060f01e840307172101b40c440490300c42c81442d066602c0364100141000740005e50142650b49442519400b8402020800400d410400450818480604090481c041c002c102c000340031518071601c2c140d00d54400f5495501d03560340350039503080c202c41170000c1e4065103450b004502c0e44645008071400041256074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 985345548 1250 985344298 985344317
    0x4081c12060602100b0319150b0102070e070f090f1401120b010c0f14030a021b0612010b180301150501120b030a0f0609082b140606070f0203060a200406 67
    0x40c1004040040708a070b80344c40340148007509940700302d81d03440c0310f00c1c05035881c0f08d0706146036a8020150b0302c82d110002c8c119842840e080220300703040b11203c1e0b0403110914003c00c945036210400c88926410390403038100070004120001c0c06001844295242200a8840c9011080c0305021142165044100c079800310300040504400140003141160031540715501c411410024064031501e180c00800718500580d0200d48060940c02941c07580130421030003141e0f00340c90b007030321030a6403a4028818451001141e0010070360482030354594002e00290741001d40200141c495200c0d0f9441c2c14030851007074501180b00c00b6800d1700610b50a0184100300c40c0c01900520708800140e590b10180709107075409566240c1e4505c2000c000861038402041211a078040c03151441e604c0440140070003c0d20380e03105002624020410003100d810081484c0c0c4044112509511a26541040320682c240910000e505010345000c0200d6407910780d015080414841650444036481e40e2034004091246010f4800864035060 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 985346798 1250 985345548 985345573
    0x60d082217010510090c03090507030c03150509031812120a090b0301080a0f0302100905060a06080c10030e2d0105010b12280e06061215010302060703020304081c12060602 75
    0x170401282110303107187c00261641c4035103445082030580e4000315011085d4290400501042e0641341d2074102200d1801c114500b88001007560742d100322403441d0030301741007250b0ba402140d64603211006245901d800366001c071008126105150350000c1400c6020403d0f50101103080501c403000d60381038034000401071032800340c0760f242c00704a815480c1c001c07401c62203140901801c1c00b80f0b40c02090700441c841e000801e05814107140030380c01da40064004004d954045210350103030b540c17101a00c0c42070320103030305001402e0200504c1a5003000c00004a1a20503108280c8012003981c003070b600c8105000c0648000c11060b600d6078909a49c51107101d940c0d1050740740031030100714200910012000d840d2188004814880c1519485d0340a5034515100c101858000004001d09400c2c00742d0480d0302144030001514044041103085090700c1c0701030101038022100803c0c4001003500800855018001a904441c5c110380030340341e0f03020140551601c1e0000607100c010004405100c40c010041600c0190700038090014001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 985348048 1250 985346798 985346801
    0x6080f160e15040b100f260c25060603020102100b09060d06020d0c05070c060801060c06020f07020d0b04060b0109050312090f0301020324010c0b070c060617030405040e0303040506060d08221701051009 88
    0x46180440103020014940190030305400c03411110b118200100d03140c4d01ccc0d8000a800c0c8043e601280342114108010b06181c1d82c4c2d046512903201c00c0440380051001d20604024000340a24410708100d40c0c94403d141086075008400340040034480d15000714521303111541110010001c0c0701e1203011800c440d841c60005051034000d01500c0d91f0b84c110f81800c00c4103540006900710000c10302035401e02c044c00c0c280403c1c06420b00032100c80e4882820440c1940b460400443e80d910a5003254450407072011500440e15500c90b00342ca004141c00800940d140c0c1010b513144841f91300e2248002c5040b45c2401c0d011503295014541e401c018a8000b0549c107120f5030340c1403082e6442c0890440481c0c01c5d46c0e0300c41001c114142c0108c540300321107500c2d10045440e41e0400082c41308448141e07556881680c42401008000381000800c150300c06420b9405c500c9014040c0f40002d0325004000c45002a1111036255800b40c40101a02400700d4417005030101d082ea82e02003d4508a803c1900c60b041031340200c000510021645 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 985349298 1250 985348048 985348057
    0xb090a05240c0a0f0b0405011a03030f0c011103040b24100807051204140f0f03041202060c0f0a110d0203120f0d06080f160e15040b100f260c 62
    0x1450070765101100b43c0c1c1d20075136640d407001030442d11942c8060600083c00024810742d440c250181000b0f550300014140002e50300d00480c042c0d08015a070000e01d082c00104290041144004603030b44030fa84030304291510002c080c0040782d4120032145010446131284d24143c10003101841c020b02640c400c8107d040303040b41c02000003081007060200070808881104201d04403d8440c034001c940c1c003884143d06141150406420352141c3c01c0d0340e40800b00c001010349021048504540040e408184103952510108004d80140c0100d40700e00e00410f52290088000411a1612244120b0030040301240d8102007003000c03068080040c0d019031241c0c000f130300840d030494000e040301c074400c40f000c0c0e04180043e41c00100740c07081c6400014958100c4815602070400c00c01c801414600000d040005507400c00300402403680b801400f0195405070314113504041e45031036100300e4280e080580480b14041c0c0002d400740c503464840c1c0b2500005400d00140ca60701c501001800e00c1e0704040b002085015841d4640c0c00e01d5581c01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 985350548 1250 985349298 985349317
    0xf060721030905060901060608061203040e101e1d09191103011d07060804050d08060103060f0617010b1305090c1306110616080403180305070b090a0524 67
    0x54810782e11000c1081000543c1c0715500f05c0700080341003801d12100620181028013210700440c18943c40302d81c0c1e090048180d03820350b6040540140e403941d80024659043c2d10652003182581d0110002c4100d241035003100c0d00c140c0704960b1408644808103040c0040c03000c021100c0c15090781010740d100d1940500d80300c812040c01d0040100075200029000020708442a212404011002108030310b00c0c480414040f01d0000e24541c01c101c0920b00c0c0075151039403a074038001203007410004501d0004005038000c0e4814005800002030390001907444070000340c40da1249070b0800b98000c80e000d00008816810074200c843c01901a81e18251151030718017400700da484064007040304450709000300c1c480280d1281189005240a80e82d44d50b45144030902c150070010007408400701c240703000300c0c011480c64200b401960019414a03040c0b012141e400180c08040310aa04000c045001e0700d100041c84d02481006804108401c45070600c5055031441001001654054240c0300c8003c4803076040d100c800f401e40601503030030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 985351798 1250 985350548 985350551
    0x10b09101d25140f1c0c08062e2c0a0603020a200c090907060e060307052803060906030b010314030c2415130e0106080102030405010b0f06072103 64
    0x215881c03505480e8001400c2041ca0100c0803625110741d0014a50703000340100c912000700400c00c01b2000080c6184030040c6481d010300308081c013040b042c58020f180141c1400c40070f2012941d8013a0300c0d4008003a56a422081c0e801c522001342c600140d4a060140302050000080c83c404002d0703e4100c09802079004011594203004200c4039284004040c002c3d03014116036500c0103400e0884086040040b8140c000d0082e02103a480071006000441d0480f410300700011049800940f01c0ea110141201e1611611011040b450340106061840f40101e8000c000400c0d82e41c0c5051001a0b110041c080c12102e49210203001200d940300100f0206044c5030390409680c1c40c05055a00e80b8101c5082280741000310701c1070042c0303000c140b20310221740d010300001140c21900055040d00c200c1e0354100044c00c011035442400501d9030383c507240f400b0310b840300754400c0000303082e141d00946d1240303010b041007030090081141140c003d0100c0e450046451410700210345c1a1540b00204596070a240030b2402441d40b40c040c0d9180501d03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 985353048 1250 985351798 985351817
    0x60f0f012f030705030301080721030309081b07061103070804050f0f0613090b040c0203030a0c02100603080304140606010c08180406140f01080603030d020c010b09101d25 75
    0x40028001003d810b400340340210358a5140881e5945000b42d9503000c0c440e41207510002e5207031880d5041460011541500d4042001001c0d8200050a0320a01e20285400114400d4140f00740002042d24400c445040d1680480c5009011030582c40e4802d103080104200c00c10041400685803002524074505409029214411540c3d004580c1c0d41d0702c003003858109242080d004220703400483c0102c4c20300150548052003100b99680e406596400701401c00809140c03130f00200c00c1014420846991400342900f801c0c0300e083c0d40ea080440440e8400d031001e0b1214103064800c142544c1c40040d40360b01844044e5141c0100c24815203481c0d213990006000d40e8a81d0046051b285445d80d01c50044002420006426000e8030751403c0402c449583e44542440c1405502020032009950200564900541001000da81c40b416610014010080302200d00c0d403000c02c60b014410410600440c080c1518985a1300c9400f01a181c01341c104d21240445682001403544020342400c580c4000040101e10103605040c1c040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 985354298 1250 985353048 985353137
    0x280e06090d14010546021804111e0405090403050307020307080301060e100c0201081801110712020601080a05101109030d050910050702150c1c08060f0f01 68
    0xd680c0155042c410405014201d10603043c00385d010030381d02d40c015140902d41d108200f8a00810f04040360b0f010b50410b54007084100c440c01c00e0700400310b0308142c001c204000181502403001500d4001499003200c49500324041040b5100072402c03141034071401070075011699035a0780c08551603031000740b2260450000b400075200099001c00954040c00054031f5100b40101101e091090740080b00d500c200420202041800140c1d81081030242c10140d2100c0700801380d130b03c00005501620203001c06400c16100080c0341c40078003420010b8584042240c0d82502c1e071507641c805080c0d946147c5a80c000d03045800000310441d40507030716405038a56000381c04e14681090032202c002410000880741d03a00101d200080c00f50f4081c98940500c00c0b041d2400c0c10510708101c01c1c7c0d00403030040c800c8102109106a030005500305d485d10104055a104952801b0072505154801c400422019056448030b010340c0141c0c0044542e0301d0b08880b1009540320603035030041c3c1001c1c00101400c140000d40780701103001c41c030044842613 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 985355548 1250 985354298 985354301
    0x40804030f08070c0e070f052704110c0c0f030708031602210a02040e0106080c0d0503120705180f01020c0f041806060e060d03020a081e280e06090d1401 67
    0x81c00300e4101c0e41014502050084c01c00b2940e4008101000401c01100200001400e2085880215030000840224a22010ad0000c1889050b40c01d400e8101069900510000041d10700c1e800d00e060300d25641c01610308041c556286514095130045030000e0007041010050300f0341c01c003035050000f0100d101c1c40c1c00300201079681e4504050900309a07009036aa59007941014003407280400303880300080000398176148020303444d001c02014003485601d10032f4040082c418100107541000c40c151b1110602030500d030038050815803207001141c180030108641c000051504688004000006030003500c0c200200800304118080c0382c0011644c010780d02d0790f4a9990007640710224003402d114100004480b814050b120002001c0200614418000000780b800041d40c0442c51140403a4001c101d5500d845142c0c00540c007000c58840411500f10b000b04049544190003170a46000c0c04c1e402d00b01d21103007905118100c9030300345810181a0064401c20080740c05051109158040e14083e2084541041584801d50b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 985356798 1250 985355548 985355573
    0xb13090915140405120415050c010f1404110301091208060307030b0c0a08060307031e11090a0621080417120a0203072915032e060e040804030f0807 65
    0x102c603624030040104200080080c116030361300c80701c00107081518180d54120310302d09080c010380820401140c2000039903800d4008080b0b103e01d030305c81406100b490300c04140c0c200c04212001e0340c0c0c880304907291000c941410b100f80590103400440e03041500392002401d4504c200c000c3c000c42d40501c1952800804503506051850180000c0d0380340c02c0d51681c0320040144031202c05000e16200c0e03080305c07108000048001d0125403503060308802179410003400d81000200141554903039a0860078890030040c007981ca0354030020030f4072000b80904021100d2100700c2480b50f481010002c00614003044144280c1400d244410180c00d035a9040baa04c0c4022504000215000303441132002503031002c43c41c6800c00102040d880d071110340c507503482d458600058144421221014014604058081e40000c1490310248040c0595180100c030040c02c0402e05002c009000a581e164507103c0c42c50031402103074040c0041c048602541d00700700f8450419085883e401207a8070301d09006c445582080140c08002048600c410 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 985358048 1250 985356798 985356821
    0xf1202120d02031804020c030a0819050c0901080a020903070302041805071728080901030e0a140d0302130b0f071502090112020c0d0c020109050301090c09060b13090915 74
    0x31616000135034840001081c080b10341520590050242045c403c40c0002600c00030700c91807a0006c416220340c3d100c4000400781050072100b00b403c0000300207070303407a1110090060703203c20380e2480c0c00ca50300c00465000f00d014007580c282e40740d0031615042000d45029040580e54034640407001202c000e0030356806260101d641d03c006052014504110511030043c081c0700750406100c609100d400603c00b005600f06003031800b00034100c500125000c8002e0b4400d40c804c07030411090030b04561301030709a400c04027201c803100100c117459031080d11701200007644a40240e070440d00d402c0724110f00050410001000a07040940440045482407041101007100808100d0600303010450040e40c1d103104600043c540e808010315440a1801003008402045002500003414442854588802c00b842d100484001c0b60a600913035040d03080080b40340601121b44000021220b04080411499559076800840c9000d030351911404c0f450702c2c0c4410003e003012900700204a03031107900300c0c07491104150341d0842110f46880c1403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 985359298 1250 985358048 985358053
    0x5061f1e0510030c02032508032e14060c0f011e05010905060a05040507030b04050712140103030207230402190314160c1103010603050120040f1202120d02 68
    0x10409400c0501d0b0111000c92145818080c80b0421100a50342c1d20400f1400301c00002c00303044040d03010340c1543d503840b146640f000c1c04035500d04142c0b4a01c0c022900109651035203171859011024141c58000c170340001c468516060601c00f007a007000300b02868201500b030740381034010071580e030b01e5240c805e115492249200307910205a400c04568000c040f00c5050f0060030070307549004140009035603a038400c00c00b1500100c5003c40c00390f03125142200078101c96454983c1142c10a41840401d039084001e040304407020000410804411420174010000d00b0f12019025802a080c284046c203a6201e01022aa025115041580c40003502040c00c0ba409862440e2012801a2407554455803501603048481d00f01c40016900c0d00f04540d402182e000203201c00001d100c40503980c04100301101c0391884020750000c0080011a42e00e051a501030301d10400c89080c400100c02d5002d9240e000b01c41914140e4546813a01041c0034102003075800344050007041a130340b045504d10f004610320010003c0c0386020400e54003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 985360548 1250 985359298 985359359
    0x200a02060106110c060a0c0b0103031101140f0403111c031a0105070302070501180302090112110d030c030e1302030a0f0b15220e1003030f080405061f 66
    0x4028180603040c0c000b0300c100100a0324140202d800000c0a0702406030481d40f207661001c1000040c1d41416420000500d0004030340d00010516400120052a0a040c5002401080c0840540c00000c100131101c0307060078a1444040340200b8840c0190009101400e01103d0405044610354141450180c40840010b52180700c0311391074070081800502e84032400c0c203085081550343e58010b500c0d01c1546c05100d04024131380604a01d65240f900090000711340203031100c102c07547c580340307440f6041d0082c9806450f0135810a203241c034503040c80070480806c26055610040e941b51f982c2d03000c035051401c10218662048aa00703045071340d0f40e00c1c0e100460182d0400c0d0000a610403124410f41e040c2c42d81c4000c414410000c00503190380c1c03454100c08035450212000c0d0115800c0191200c50102110190010a44400c0307041c20055100801d141348000d4900907114072500c402150f03801c85040c1c0703082301c3c010001e4110380c01040f8902480c14014100382004810380380619161044d102648842c0c102298003c600c410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 985361798 1250 985360548 985360567
    0x4080a1b0509060d200a29091c05100221010b0906070615090c02030a02101b0f020c101d041103010e070302090a0b04060315080c04020d20 61
    0x60400020802030b194001d40380303400c400103509807440d07440c003800210071403503c0d4111450441103800040d8004000f400c6141c1c4a0381c0055000110543c1800c218008501c0186c084915400351844940c00400804401c070760161113481040d0b0030b0b00c00715014405c1c41710403032490b412400038000300c605800c01070f0340c58585084442c00c1d070041030f4001300c41603008000040b1507803202d1080710450350300500f0102e48000310350440c03046400031398041c0c0c0503180341030454180d2179400f00042110904582c2118032290015145504030381d50109000c03032800001c200c120107980210010394401041c1c0c01581c01d110413038008511985090002c80c1c0009a54004100c8141066218022444400e64040240e07280c46014130034a8481805810607840d451000a08010702c030341c040384c00706a00503123018901d076038400000103590000d014580100e13040c0380798040034028052502c0c0c2202c0440d001045408508414800203500c043e040200b000c1e00c507660036680f0b11004668000032110403256556655160 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 985363048 1250 985361798 985361843
    0x1c0203060f0406030302060c090d0210180603020307170606070b011403010c0203190c02150a03020a0801060203070b0f130803010b03070e0a081c0c1202060702120408190804080a 78
    0x7401503110342c0c43d090090010070381c0015000e41c82646840e009942d41e44890015602100e0a04000c0d0320042a01c2c00d8084540d00102c0030091002d010f5841c1030b45519003800341c00f41e0100702c98010015881c200340450b02d07200e07061401c0e000350001d0085868101c45803101d51100030700341c0028030000d0071056040c01c01d080900c101e00c00d14100b84003440c100740221941682e20494030b050081004540640c050547da40c4602d944000004c40301110740d6581c5840d0050301a4001c0c0100f400400e0043c0c1c000120240044225003000c1d07402080c100d61a65824503043e0102350103403000074040704009800b00040c041034001c1d4064a900c6007015104e1900c41c8000788000800390300c05000701c5400d4420005188002920000d07000e110700295492803a00104603918490644080d08000100540042c01074000c00c3d61800f4100c40c0d401d40788203011500c41c00905204510a81e03000e0382c0700340b80e411145001000c2e004008c03485000c05a180c035076140c074518070700f40b00707490103941003030382c6446800308040a03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 985364298 1250 985363048 985363069
    0x5042409033209010e06070c05030c01090e1801021c09110d02181312030b09060a14011404050d030f030e01180809131d06011d0c0f1c020306 62
    0x382c080b60819034462070b5110402c11082c507000040034401081081c0315a008400b90003031a00b0203071016440741c40500341403070303d40801d1050034003134044c1c0d800001541d40b040e410101079030305400d030009054498150843d060007640381103a91030b55080c04031016104a02905c18000c200030300010544400ca0b0504404100025070442d104080000041c0c0068480801e2039640782d0020382e0703800700b5941d030503101c44096024260003401024580041d409158250744040125501130f1105e01050703980100b4048607290700c0c0180c44500c030403a54110103540c401d40c2101050105400c810b8101652100441c040828801d821000f04071105000c1004541c540308600740100224001c0c01074100b260040303440c5460f008400b41ca0314000289854668a138406030f0540810342e07000800075107181c065860b200c1d02d28010101840c3c01b40c032000007241c07075141202c60624603581c0d541980c6521668100c44496010140341c000e240402c4c862441802e44140c8000040e0f0b004a80c09a03032460030104000d41d0b000b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 985365548 1250 985364298 985364327
    0x30c0709050f0103050a08180604030609200109121103010501260a080403020f21010e010c0e0306010e07180602011d0f1e0c06040305010e07060f080a0504240903 71
    0x2c0c240041002c41c00000740e1251494001c2d482a03555040c024400c031410381d51003a01904001c0000d000030810610b640415925802180c03c1c0c4641d001e10400e42c400d54400c650990300040705a0b005002082e40e20280e039030350b41e1243c0007415004a540c00468203640e03007684806019a80d0400349110401d00142116800441d20041d00251686076180f1015010764040680150001d02c0e086c3e109480314126181c00303401842c05080c00410a0f50810b0207801e541120710307000d5090010b00071250b03014110f29080c1c1e000040c040c000b2030703080c07244003190640001e1400b410403400c8120800500e00d00390390f44d03010348856030003c5030500910206110b40198180385a1441e4007120f803100e400c000218151074801903d070100c00709800400d900c980381c03001010595500c00300026000042100552084a8a14030f00046d6560b165035200c00b5140c2c0c03040c000402011604c03450010300d4650321503000aa0041c4111018500d01c0d42005507810400088550350300c2c0c49944500101c14541c0040c28500d1840 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 985366798 1250 985365548 985365571
    0x103021908030a03020f04082b030b090c0706020f040306060311012a05102c03030708070503220302250803041206110f04030c0614190e03030c070905 66
    0x500d88040c1d141d8a200c0d906080b400c150303000c11600e11104146c4100c500504002e01250b1400e48001c0221032090704078101ca0030b03440182e846048405000340200601d20200404e202e15503a242d10748c4c3d6181d940080e408544442c0e08100d4a001d150022010340050b500404c400100d07503045241c24802c0701d1710b20781c4040c1800b03494103005a2076200304034010040c000200d0710600245a501d0034514114400c608105500e04111034283c84081c0060054010b0b440e8079280404441e40744021a12031209075a41c4000030414800119034602410080d500404207100d181155214038001192140d0900e03400ca0060b00069402c0e04441802c0d01041c00c026a40311b031500c0d40034600446103540384514403031124102e503107058080c14004281c0c4290b10041a2598140d40d60202240e400820380c8940030071644030030299004103607180b06800e120542610030b0059840d01903410f000a5004508640c1042042291501009541c8081c0003401408008a00900130700d0f080c10095815103030300418011050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 985368048 1250 985366798 985366849
    0x9061912290d0b070302090306100501090302210a0b010312080f1603020c031801180e0105040e010b130e0f0f0c010302070507120309090f0c090b092205010302 70
    0x20210701c1203241044001c0c0303445844621010012034040300300c001024294101102c20001ca10b034041d0000d2025440442c20b80e00340d80d883c142403121590140c0103290026504082c02d10040c100b07000ca001514040c0d041c1c2d0007450310380e004031030701d005005041207511014040040040101450410030f800101e82410030040ca01411030445a80340108001070b501c0c41361305030481050003030341141c14081e51b050981c1c1d03403044214105800c802c450105180082c2c4460030f03103208038203152045070503160304800d44212079180c04100000781441617000d0b14107560700c2d09080501e541e50210449188070b04580411f004014a1829050121140e11009150401c21761000c01010100300c422240d102405c0040e240d1415043c058544072003a0843c4400321011290745040c035802116031011034011040505c129080017075000d0517075052066050100c1c60081092041c01d5520002d00114000a0290041ea4006100300d00f1101c0e0aa6000180c2d0391f610001402542000305605124105004103100035 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 985369298 1250 985368048 985368071
    0xf190c1104050613020a0c02040e06060a17100b0a080105040506070e030102070b0109180b0702070801051e042015030402150c100e1906020c01060806070507110609061912 75
    0x40c0300f095440d4142c075560001c1c0f81801b5034000d00481c1d9207a90043c0c410004581000c0382c06a0303c50054440511074451084001010041d20040d481040e07104405020b0701c529a04114000e07010181c038081d405100703540c010400340001d00c1900d1203140070b1001050b490a01042c00340c00302403103a8001d070082c1d00400800b8082446502c4c1e440c1114415400040c000420710800d082040716020010801c070050428024007a0340010f4403816540305030000c106545544803069100b85024070200b242510032000030b03000c103030501e40e81b00c810320355850610150621007000840c00d00d001e0710a404443e80101c140400d6041000403030791030134030b4030056528014013070a410359190300400300c00b00c6041d101e0355071020382e03602849003440309007250000c0180c0c10710f0f03403915101130b4100c00d504040d5980ba018001540c1c030400240e440c060b002039140c09207071a5240d240c0b1490b03009084100c6422400c108840b50341500c5900003046442d409a030541100425518001d0580d0b000105000c06a414254507512 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 985370548 1250 985369298 985369309
    0x301020c0703030c060b1503040308060f010c0b071103030718350f030313061a0603070309081e0a08070f09050f01020a0f080901090602060906010b0f190c11040506 72
    0x2e403501810036214036540b92608001410070350304a80d0300844030b240c080f02e2603818000a10b0182d4481e403546200d03a074420062040e5260603404080c00150400b40710404a5924240749400204c24904107401100c070314203542c6103500c1640e001e030000b00c0e8007100905001c5000e0508014000440708411150000c0c00c0c407001070000c2005002903601c0d1424168401070040000072503403d11032054070384a180c00e0641e40c08a21900d602520003d06040c1d10f8402054054016030008500500e0740d41182c0700c6480440040841035000c40d00300000f080000c40c00c1020f00038800c8040f81e91144c06a89640100d0010000d40005d083c0c2010300501d111054071507900508040c040d1032040d1046032540c0c042400403458141c110b90003400059140300d1040c1400950401030061800c280c8034910303074a41e121002c0740d50325001c4442d1242d540081005200c0104540020305c0104004140c4600f024110304612045800300e000740e0010500320850303e03080010443e04074440348022a410405498030501080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 985371798 1250 985370548 985370563
    0xf03041d060d0507030c06030b0402091503090705030717010c210c030209040f05090c1e0d050c090c0a020111033711030108010609020f2203020d1505060301020c 71
    0x42040948005503554a80041d04408643c01600312803049542e070504546005583c0111000681884209149401e16008403400e0348409464044003c641c13045441781c1d500040e0400c40380d8000e040000500ba603040003980d02811135042191011040200c22a00711242000c0310414018800382003403284682031041c1c64004591400402c0c03805205804900a1040e80c240d00c0d886403a000e0001d414000c0c07076022038030680310507080b1080034000c030040040a07a440303421500c00c461250144002400d01419a42035103200b4022a4540c3c8012000201172003412944104403600200d42940541e60900031b40c00707017504010402c0d14505000c5280d0542200d200d01c20b100325008a266028542070280c44081d1001115104100c1400040c55000160b03200b8411101e80e98200100410800600d100715291011030b0103a540c6010b060850210003548014500d0340c0c05281c0c0c140000c09a1141900340e555103200ea8600e1010b00140e00310301c4111100540791300d0090b8410300ca001d80000c800140c07013 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 985373048 1250 985371798 985371839
    0xc030c04140c070204061a071401051501120603050114040c12021305071701140a080c0a12080409050a0c031503121b02031204030b010e040b010308031503010504140f0304 75
    0x540d0f65052800810041e1030180e001044103e03540022088100d80744000e45400c07407040054030022445020142c4c01d88209641d02c03064607111a0240302e641d8001d2481c010400c1c1c4004000c12803507500c1c1c480750300b103c0d4412035558058040c030f01000100450b0520402c080c4c5650303004800c0d040c0c6550042660b00500b48401c403901940d8a02282d90180540481a85001b0020617440d50b0f42c0c450b0742d1101ea001e100b0740014083c5018800c040b0700440081083c20401e00c02034240c541080ca080e0414540b04092036003600d0451017004003090b0407900b405118414030301514042610120808014102c60310780040100c01c0b03070020400d00000320604460300d20718095150402918a1200c000f0350f400140e144025070511545803e00c2c4064140b40140040301d0280c0600c1215a0f6280701c4442401c50880300107150480d480011700c0024032070340185401c03c0c03402c03e00e02c40203d02d9101003400c5a2040d103060719004035142036500c00382d4003000021500c14041c030155003018948500b03600c43c5056581036 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 985374298 1250 985373048 985373071
    0x7110a0c0905060f09070509030d0306080a08130b070f111c0305030924010608101409040609061d0106051c17270418021f11030c0c030c0414 62
    0x4103e2594030704044208020f801054469141054000034045134000f480c51802405880b050881c050300920400007128a1078028115110715541d9001050b809200c001c046901702c1000800d11100100240ca442803041000301381c0c404407410015981400c23540c50038415078445043c0384e0009800400703910705550505205880f511189803180c1402540d00c80c5541411185154441b0541030300390360380c1241c0d60354a91b5170301c0d6228081128201c0c8024002c0000000c0c03644000d40743c80c01d02100c0305902602078000042c0d221402e40d030b4041610240714002c00501400340044043c2c3d9021703c24a0018101202d5090005440c0400c441085003e004060b0801e01140724a0b030940e40d01130105e40e2101c42450b07a0034620b644040c4409441c0700d0629056010340d15210f41e0f100c54084100360090165001004070b180d150b4685030768031903101c0280b60282008030440d000c06905400708041c090884000020701081c40000051500d0700c036880e0b080714426800c02c00500c2a0101c10f034103003034001c00103030713003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 985375548 1250 985374298 985374301
    0x303120a0204080f0309040506040b150c1c1d030607170a02120708070f05160b06010306051c05160f030b0a09080a03050f090a1203090c170607110a0c0905 68
    0x203800240070300e0380150b0240c05404140540e402000c801450288400c480800031516a002480102c4202074080303030b0000b0300018150303090494040a800c0e2095554220382440c85503041d803c02414019401d140480c10800118081d1009100010703040402a40100010301c2c0c00040104400c48032420384480c1c11204004c0343c202201c0e0340442e8942412000031102a08111100a00d841000c4600038006114607064800c84c83c8148101c4501040c400140a5240c00c0364540b205d81c00c01c0070340058145540d580703000070943c503510030111070f0039441c459401300302825040450a100c2d200c441ca204124540c1c0082c04480080290601503030b40000c0c03e405150b6484407004018040c48102400d41000401c01403811641070700310911501c0b444c02c20055a40740d64045a9541d005964018103a502591021545901c0b03907100e42850307030040c0305101d5111303922920803522082c021540d44d210340104041229040d00300c44080301c0c0310200300051600d09420b858240e080a480c1c0116003229481e01d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 985376798 1250 985375548 985375561
    0x30b0402011d0a150221160c120f0506090105060618010e0a08102a050a050d090803060a0e15090606070b01090507090f0612020d02070b0717100501080f06011110020901170105030312 80
    0x401c240900709044120121409c0341c2004c1414071380d50741c1e044078a4814032000400340c81040c01030500403c0003510003070070080700095081c0c06100840389141004041c1440c42c801d5510890564010240728020b400d024100c1164003096490705241302164040090b0200c01c1d84080300c0200c070920b02c1a1404503218001810129007512840c811056101c0c01c107403410051000041c01940106000c68911404681da119010010001124092004560b42c4041d0400f030034039000141d403204006140c10700c1c04100ba85e40c0042ca09081c2c200c000820b0380c3c1e4040180c2950030052000140440007010307140d4138070b0190010144400048501c9030190007290552464040c0e4040e294100d500c40000c109524066200410074200745901441c4100c19501090342e4a02200987d800d852060791005520350b60701443c0008054050442410088416107904110310705000048006c96140c0001da6070320382c1e4400060080e400c40c21100503c403408401000700d60b078000201d4040c1e0790108a80340d000e0741e404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 985378048 1250 985376798 985376813
    0x9030204050a060503250501080f04110a15020307110303040e0a2a02011401090b0a260601030c03050c0910120f0503030a09021801030b0402011d0a15022116 69
    0x1035010340d815100b039107110f124924100110404115140d051041b00035603640044507220700581d404402e5000c1d2002290101c2c018440191100e000a400c00011325a00c0549050340c0440d072402c0401600301056500800461801040b14503008a0045d81440d05110382480124005406888500c0d5940c0c2e04039800346904408106501d8001c07200000c400365480040c1c040c01042c03210003030f908503440c00440c0012162190702e048d81805040001e49500b030444003d5036404d08a421030341480e46400c203240209081110074007a51081c50b115080d14554a030a5140500c0804958800c800d04003c1080d42d0440b28040c1040f1440e060000c61501003a00704040303072140c4500301401d240400010006c0e806400e40140c07251038800e85990000d0440108001e00c807010a000c01491420743d50041400741d8890401d00d0034020000c211400103216110004285070707150340c0714080341c503540580000d0b52034060044000b55543c90b08407c0300e104244002145174850084046010b03085044500180703c0304 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 985379298 1250 985378048 985378061
    0x614060c0c0d06092909060103121b0206190906080903030f0618011403070b0c0d03020f0c0a030801060e010c1212151205120a091a070b150f0f0109030204050a 70
    0x1c152403d0405c2072503003c07000d0180642681c0094140e5030030100e0015000013034000c0c100c0307070030006804c1205000d080403500541e00714201003a07100c06040d01b00250f80e901004052400769022a035400841000c0058610017240e4883e401b0300c1405e00400a4218000c401c80b030b40480d071030128112581e94100028820030785400300780c0444694000100342c1d06a619014043d52204401311101960381b1a01801c41d8810b501126803150800903105036918080d8018103140d1580d1b8400d64106070300002d001d8502882e86c04142c00158003100104030f9183c00542e0301c44410401c2c6010201c0b8200389c0c13540a000c0e43c3c407c500314200070112140c04042c541a0380000340c001145030341800415510a511101e940641e031003a2024000ea80040e42900c0400c400c45040e22216150f01d0314507480c106c00103070f0b45401410040c141c14000c00119000551001941e8481c91389e0b510400d840e81c102605020b44000000b280c1401843e010455000c2c50380c0001c090400c40e40d048030040350faa07031040840740142c0b19 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 985380548 1250 985379298 985379303
    0x6150f15050f0c1006170714010e130507030c1b1106270a0b071713030f15140c0702040b061b100f0b0607030f030b03100614060c0c0d0609 61
    0xb40400c04a2801c400455241044020a00c01340800d644a40d450107a8094900e80803409030f00014081100d5a00702c180b410386294141001034a094602e008918000b88030b10f10300e1441a640d90421800c160140f15190a003240352408510000c4802000640040c8900015250215100034a119690b82204032240c440328812a034800c000d030424401b1000084003038030b42c8036094101002c200d60b9184015541c4c59074000d120a0182c0301c4c511500c5c83d99900995034030007d150104804408141c0fa403d240d14414810010100269901c6030403404540c00f420708600b2401144041c0416005840241c80041c0c0e0115000942d0203950000aa014032900340e61710040f40719440081103850002c07450b40c91039940320106000c20b501c1e0b100e00c007040342d40c01d44925504c848180944004a03100b0992200d0700348803802c00150070000800041d140072448406030522544641b801d000c190b45100c5943c0400c6c1040e550941014403490381651550203084242d4041d1000c001101e0501400b600002c074a0b58 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 985381798 1250 985380548 985380577
    0x11103070912150e0c1212031609032102010b030706081b0403061a0310060f0e0613240503030702130b1302030a05070801060206040506061e15040306150f1505 70
    0x46025144c10385514000400364801c0454042c90400301c00c010900c4125007070400ca100e45940d540c0706000d00f04114600c80c0c103082105189001c00040c01c6070800b0601c4084107008140707085524000282500d482038480ca021b500b00d0107080003039a4002801079084080d501074100c0c1c80c070360041c0d00c9520780a5540003030702c544c1c20310603003281401c02ca6040c451100c00580c2500c2a03c46245c3c506800d0f00c015105140809103503d20801c07107990f903000003503040007005040d100b607002e800c804c8105036140440c94203000080300f10b002500700c20b012024001040290040d60400c1019000104541804036400b24095142d902010701565a44c04580d0030b032007544400c644038200010f190000300001c85802d40802e0180c000070130040c4c00000c0c039a2103194000000c000c1582c4070400e1046040b581d840781d0241c5c0301c1c0821030b9040740c1c0d04c10304404034044240e9112612540345007010020360741000c7c149a90110004810b0081034031000524042c0c40c03080c08001015000704000310b445201d038450030900329 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 985383048 1250 985381798 985381811
    0x1090b0106020a031d042307030c0c0503192705091308040b030a0e0703030201090201180b2a0d11120309030304030f1701060c110a18050a14160201110307091215 71
    0x362485010754024551694100302c0360001420540b07110403110bd0290181c0d00078424036010010900c84010740c200545041d04005d150075040810724501c102850301c0441340d041041c81542800306c100c5c0d078000024100e110b41c41c0e10b6611260341b1482a8000c550300c0e0307840040040d030b21300481d0b00124080314900d402c4400c1c0c17035903a0400070b0092944400c220b0001c2c0e16200c060a4683c0c0081300003094840d4002e10320b180c644104003100d00840c00e1100605544040c506910351608240803046161849031207030380100e9031030b516560130213020303011040c048802031080c4480c1c080c0001c00d0700e0b800341d414280340300302410402d401d681001c1d54910b02d0b0800e4060320000301d011580030000c1ca0b03405229032071080002c05c1d81c0d000c101c443c40c80350042032a0035520f50308051032494140c204c1ca401050800b000580e00399600b025402c0390404403010a250300c55001c020400c250b092107034103011b040384070f1040d00350b04010030001c042020a12480c055605014803613000d214812440020b03101d00544104007a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 985384298 1250 985383048 985383101
    0x11070605072d0c020f0a08100b04110f09010309050d0f11030703090e0907030c0b0702120703051b040207080712090e0106020d0309080c070609050f011d060f0d020c01090b0106020a031d04 82
    0x150234590710503c01c524203200c0820100d0600b130040c0c2c2d4100b0082c1040da030070400d941d072000c40380e5080780c100c507070425071199001408030b18248030407000b040d00d0360b5880f02182d00c407501c040c00010b680704441c0e860354400c01c400d90110740c1c4001c000741661403a0384880d5940e01c0300c024241c40d1190035080a40600b12070180014480d2000d8010710106100341c4160b400c0c41b8000280c2501d410083c480a040d030b80029041d00303402ca0121089842c2c500c80184014209102c98075603000c15000f0150485078048101b003502505a00301011900a01038041110880c0d81400c1d4000c3d15190600400d9040c5600c46d405041004403100a44020003031003004c4861507640c03014010081062071164a0240303103542541d803170340c0d44500c000c0f0420f42c1458030b596455000010502c141548004448881c00005000010001400e400100a2521200c2c00410421a02d050120940c2d0041c0d20503429544a1144400004d802081061141513400c1c103d030345041e410004900541518403449202d008400c00c0c01c0c28 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 985385548 1250 985384298 985384303
    0xf190b07031806022d0c040e0a150204030c051c030302090607050f060103030801080d2c0d03080405060a02090f190f0b03010e010819080a0311070605072d0c020f0a08 73
    0xc03070070f0b480c803802c0020170103514442c9600001168030859500710508841143c10305070000d006610005044500b204026192000100305201c4090b0450b40c000401b0400e00204500c3c0001070082211500c544005490b4500e8a00d028042c00405258020a48444503070b10f5400b81e9150980000c10764480d1523444501c103031a1602404205c0204848400214006034001102d84070600c171a21401e402d030380000102464900454034000251000c00852840c40c3c454003070490a0603c01d4980e000c1c01e05062524504160000341422205e600c1842140300a0b9078502c0c450300020806d0b40da40242643c040d0800c0f04024054210070205c82d00200009407000c03410340114100e9002103170350030340743e40ca80301c003103868507140003110000b203642da51070401292200000b001c0100090a0000707842081e0f071800c0003030390002e00c0d01399512560341c002c000c000ca800c0303c0421014550b0007080d1005034401a468503000707070b0031100c0804100c1d004c5860011501c411041d9400072034001c0c60083c0c595558503010350b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 985386798 1250 985385548 985385563
    0x20306040c0504080a0206130914091c05031504060e070c0308011a040b13180c0f020607050412140a060501060f05070213020a03290f190b0703180602 66
    0xa000381d00d08050610160302c21415038007075840c2d08025001e0081e150f000c01031075810001002c5c00b9401d919400090080607441100b00300140381002c895580b40c41c5109a05210b2140d243c080100707800c180781c0ca035903588441184d9101002c0076105140c9555213010030300814a80d000074030f117905500180110140c000c1c4c0c000010314404c0d40c5001940ea04c0714100c01403600f00f08030403180c2080502080c4048040307440604001c0c80d603403942d0810295101d01c0c01c100c501035814034038119a40d070240c00740302d1540a081c03001001ca040c00141034600303001d0001004d510840c0300b070b2560880009020420000890000e88501c5c0c0030804131220703d41e6600345800108402c0c0f240d800030801d5440140b1200b0b000f40c050320768094005040000045803202514083c1d0701c07907a551400c065554108008040728003c0c00410203909144090200c00200240901104902a01d0f40b14400c1072a4100413042200040c0098800745280d49031940d07042c3c0b405561004005000c10010004a000440c030540c1c0060000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 985388048 1250 985386798 985386811
    0x11115060616151a040b061204210e040615090311040f09230a0506070807170403031b02010207111c140604030306050915121903020708060702030c030a0c0606050d060203 75
    0x1200043d05130301044103c0d03454260f903d4109000340400035001140c107002c65403040c00b031034480c00810403001800b85c240b80550b01075400f14442d00242c0c02142410b103e24806400f00350510710040c006a0340250400306a4800207000a100200051141d00c65411903681c0c04c08285050040b0341c940d01d4018200030000788500380b907803240740c4121000c0c1c000254007a41d194203c4007034001521181000c484030a4002d00a0b014001003003422084a01c40708480c034410341c0030365400110344001d4a0135520000c807962017407045a0040c00100042920030410741d0303454404907490b0541004030a211149c11148803806055244050702c0c0d10f11000f004220140b00e18800d56003005003e841e1410820040403d8840c0d9170242401001c2c60b859040000002c00003900120866400200c1c004005083c6584144210016007016608110114081102d15000340450019605100540840d02e540707001c8e4881c07250402001030840d0040c810f050388100060319019029081804250416102952064030007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 985389298 1250 985388048 985388081
    0x4050321010305011119141207021006230d0512040303050d0509031c0c030b100e0a1d07210906050f13080405040e1606080601111506061615 62
    0x161402075180c0d00304c846d070350b030000c04440d0b000180c1c2c041100c20a0300c20b808580d84e61360810004590380190501c680c419105039000389400c0d600360040c2c0003030380c0c0241d000d840700c80290456500301e078030a11590b42a0300416079100f403e078105414a189015600c040001801000107804404d256018009142008180b2018405038503103c048903030700d100c0c2c0841c00e8002c030403029546403601c416070460b00c0c4444203441e0110b640b16279000010840041800c0110224004000345119030900b030b02c9410080052410380400c55511660310031800320001c07c05010040c110fa20240e401481e02400e60704030f0403000c01042850410b00c0c03c200109801e030b580640d800300e00c400042c1164907541c403a20703d407940701c00b200782060300c0c0c40d080c04050095166004070b940a4000c40c0f6042002c114081401045140d07550003060400f14005051182c00105001c1d50b03812a40c0c111620800e500e0100e0341050003034031001e0342ea0541000c0d6486050b08a18018070b18003040b108100110007035000440d904101081 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 985390548 1250 985389298 985389311
    0x9050d1805010c060c2610060c0b040305090d1407030c21030e030705060c0313050114180d0813060f21180f0326130b0405032101030501 60
    0x4000340e010801d116040c0001e40c0f40314807500013401500002c6041c1007a042c011200c08a40f6030340c4103071a41024034111408004000c1003001d10241c084040107006d80c2c2002d4131180d1864a440044140c000c1015040c08400920784507292520300728880c10702e402c50803070485203060480440d109e004920080d24800c0340ca01000c0b03440b1020710280f4080d0841084a1340344184a07a03001e1364540d0000422035807501555800140300c0d11040000d0020201d5440515900d000e82e0f0400d40b094044c5401160411100c0018620310705500c078111166400b103041c1105c540d003030700c10004400d035082c0c030382c01012a500800c0704e1010340c44600b0700200b95005610703000e8510211803422202c50740c8114909223140c0403a00740741480c8801d42d00000e520174518000020107011a00c07005517400850000314000782d0a0000e83c40c0000d007003030402060903070722801c1d0400c5050040c1007440079005c40c2000f501d4182050085800c20000300308030341081148092148004000d010f48050440007480305841d40c0d401d001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 985391798 1250 985390548 985390577
    0x16030c03080123223e0423130b0a060e03210f0c0d03150b030c0d0906180c090504170313150204090f051b0c010b0409050d 54
    0x30a1500070312041d12901815030810001c010311046243c9482da20303d094a2215035401070349014041c910380554803410218802d030b010720003903000c0e143e0303449120008856441905c0c0400101302c0d000c480381e14140101d901c99455070700c10036a071031180c456800204440340c041e50101d15000341951707540c1100d0144030f00d40e480c182620115625066030380d1540000c0307045001410985030a1246510340c105441c2040e655513610704640d441b50070450041e0b400181080e050a9050107422503034000810001c10483c0760501e2100c40d80400f6024003c14a0007207120108040c66600003c4644d4100c002030002101400008030a030f003c42d50165549031075400080f990380064018203000b9540302c41149585e0214640c2c202e40e40d00082c105824800416281790041070100703a105a184074006001699107241444000c02c40e010b076034045c2c40d82401e0000b0030810b03944501030405200d0150000543e40e9040f9107083d07004211448089a00034a00350f604d10901c8000540c2515501e100d4a80041102da400d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 985393048 1250 985391798 985391819
    0x405060a0e1c03180c0e01091107080a030209130b01090e090d0f0c0b0a15080a030e1c0501060308071415070509060721230306090c16030c030801 64
    0x310000001c540c40140b82d0010454040a0140c000039035150004d90a80c9100e01c0c9450400c1610f015906418444020311210b420200d0660042000b00010492080b5000424107980141c240240c1205404503034011140d000c3d4040340e00c2c03c0703001003c01c402c40c118060500d0040c003e00d1101d40c0061084100170600025450403940a15980d20090400c5108184100d6180c080503254600f000805000320740050f5902c0d1402e4000c641c06040481e050b02e4041e40e020010385180d000601030b80c071809051010076045404008000403d48003084040e03086051304101c944080c1c8000d00395884c0c520000148810031000e00500b0744200d5885d00c0b00c50000001030f81d80c00d03070b0b01418010100d854002c201000e005400070803111201401c01c6040442d6038580b1500400403c0304200d1502c05001c5140e81d09030301c580c0e003603050203d02c1c00042c00d001a4104604041c0001407555004a041c1c0000c103404001c03005c242c83d010203804035905000d0000d07140050a49005003001c502003a882000410717444500d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 985394298 1250 985393048 985393061
    0x90907030e0d09061202030405012403330b0f28050103090519020d080307021b040c1b1707150b03031204150b090c04170102030106020604030c1113050405060a 70
    0x103170340d200c24030504c0400c9000294005001100c007590783d582240400724016440301500180c04220425180ca5070420140f6079003030402c4102103e035444c2003010090f1222003410711083c0b10340300c00550391a0720b2010a12032040c1407807c03036020050940f2039240030520003502c00500080d0380708c6906147d840700158245c0d0b9005000800301e4000100c50010185031250b0f80b002c0e01e0004200410f850314549031074074207900c140c40343d00058104080d10303407481c03080006140c2114010741381002011410003000b0044400c5850300c0c0c00e00a8100c2c807900500445054a4240d040c01c0e0f04119942c45040ca801c102c01000400003180c00e60418000300c1c0d60b8034010060b01d2000078024400d24983e40c0b60741e02c41703038030260501111850a0b503ea000b43d4564951066140c814596001083d0f6035a081048200786000f045401e90501ea00400040c4a0a503004c94031039007296150800210040c10361404a104000d41d60b612900406269601440b0100b9908698002d43c0520259400f50301c078642800c0c2980d88 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 985395548 1250 985394298 985394309
    0x110a050a06230d0b2d010f09090f0222180207080d0c230301030c0501110a052506230903070506032d011a0f090907030e0d09 55
    0x2850300304080360007105044070401009040880120000401d075000b5085201400302071503640d000d4413003908240303520040b041c400c1500d90041d001204140c0d12400e400c40d80c564100484041c12070b5500d070180c1212809010b500c403052001c002e80c1c00c680c0d00250405000c40302c07566000c449881301000804080020346203d42003079481d00d0345440c2c4c200043d500ca054100c81c0c1c08400c004821104400f40b00710b051809580c0d40f0741c0503d142c0c0180c915000c606a01001d401e01100b0001000011140ba01000c01c803082130070886260441c4410140c20140b40307200160ac240144d1400729509100180382e40540030a01c22a01c074080c0c1c4420342103401c6003030a080807640d02220305400e00d025101c04050001c41c50020212440107454202107038841e0010b880304c5444031000b1000120421440900003140c10400060249543c50f021044191020044202180303400020380d500d00301e4414000c1381c1c82c41c000500342d045d25040c40701c0001d0052600131003000ca98094286900900752042c00c4e07142c111034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 985396798 1250 985395548 985395559
    0x306061005030406151d0402090a0b09060d02010c05030714060109020a0203090103110d3801080708060303070b0705130b0301050609120a0f1a0907150e030f19110a05 73
    0x99503651a400249484c4480e828866511790000908191180c030004080c0c3c840c0103c2045030800e48140060004007130305542c1064103010110416444103950198018000c9981080301030140c00181d60b0005070f004050400c1c040001d1443c1070001404403c4078220384074080700c0c1103a0341c89000108030f020b005010001a0000c104150340c40d84242c1026021250780400035241000090040d000c4840c3c07504013034001001c054503054032045a01c6e18040807860b03c1042108444003400007482100010406410f00188001060b0700740c0b0100196a0400c0e0b00020703581c06400c0141c80030b40305800c4040d034085038045021001c108403c9003403c0c0ca04030f0318003406050800c0f401008124541c800c02c0718500d0184a80080e22021401840440703c400b4002e0a584032100d0045aa81030980340c0280084d80c5580070450400c0160a6441c2441102e01d10b841c2c0f031118075030795400203410700040001e01052486109801101c03441d8620382c40d061a8402c03681070344c030500c01c8801c0c0001e0071001d201d11035100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 985398048 1250 985396798 985396801
    0x110d200f0f09071e09090609020a0225090204060512060a061b031110050711010b0f04022d1902070e1b0f0307020d0306050d0c1503020d020c0309030606100503 70
    0x241803240b801ca40001c41420f00a280c040c80c99160010701c40c081400c20001026880108518111880b8140c007515680700c09501d000c2c418480a55070790b1410b28404801082017071a205044541c1444d00040c140342d032029540c407aa1200000d1141c0c01c0744180740c0001d10800c0206100d81340c04810402103400c20340700c1d01018808540d1341101c500ca0440250244281015240c21407981406020300b4004002c200051909020400610446110302c100c503caa1409200f401c841d640d040081c3d404940448003d47d85240c6100c50002c80107000341d1203184048104401c9280c0b502110180100180b140c000001140500500320b9a40090b8400c43c3d80c041012130210722a201d561024207014555004031340d10301072103010b1131803065000302c070f07410b005030800300690010a515018036401400201c0d1081c03c1e02015448007950112180b003640d9100d50307001d0100c0d40441c0645c055030f148500c1d1402c11502c4041c01e888135a00c03580b082e182184240100c0000540d40d10f081c1c494860ba140090b070791581035 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 985399298 1250 985398048 985398079
    0x2040f091505190e07080618060c090a0b07050a02190e0402090702070806010308040302130501080d030c0e030109030e0f060403031d0102010b060309010e01060e090a030507110d200f 80
    0x2410050243c90a048074184200440b507558001e64801030043c60007042e0152902c800c050074404040c100007031500f014446440a8880000c1b150b810403809141c0c50307645c81c0a07200182505a82303a005201481d80884c01c9400d0100210314909918005c1d82e090843c00c41c04e0341e400c044407107140103002094401130b000c90050f0500303050080c2e004600b8011101c2c00c6880d16140d03032405100741e10441c2c48401c001014011810035406801690182c0d44007440654103100b01940c85031101c4140c941015600c20340e1001091084000c40d041c218050008c1200c2c20482c200200124503003035031203005e06103646544d2a04d00b03001d0207c404032a0503079a044e80740703200801c1008108502054082c115900d40702000420303646c0b40300560080f112074000050b50000c10001c80c0c02d40f29960301001302000740700f08001c141140469104080b03503152a00c0381d91070081d4901480c4c0011041d0031280c12182d840d4103102000751b4600f469002d4010418034a0f14101841c04101d0451001542250414122840d0040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 985400548 1250 985399298 985399301
    0xc070902130320060408030a020c040c080705070515090f01060b0a0e1c0209150f04090804050607150c05070506090325050309100f030605090402150c0a17030402040f0915 75
    0x905103024101c0000c03d050000502281c00ca80c000034403e81001a02045003034040050640e10002039409001c00b5044413005094210300070f01c44428054005401010008140407120f94840d11000d0346400342028014695964644600071750030390702e480804100030051106403080075400395a900142d09481c02840780750403a4295840c03000307030311015403c01039440200488c40396120042c9028802c4400c420000d1170301e0b250030501d0040345841508004620341c04101c4040c2c80007034880320b968484926118158427111280c500300e191801c480001d06a2b441002850b4039405801103810507100c02481607140c1c42140741d21512406590424012200b407074030098106030154044d0ba00780540b0101140b1030701c45000d00c039030004e01c0c0d0444840c0d0352501840f82c0c001801c010b4640309244d242543c00700c2d84042c0090340300d041c1401c010400409041c820088150384641c001220060381c0a06400040300b508103a41c200d11440c2460000854020303903212340d010503908015695a0301d17414000c01030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 985401798 1250 985400548 985400573
    0x1e010b1507050d2d02030901082805060a121101110d09050409080c060718091107060207170d0c03061a09010f3005060303030705041e09110c0709021303 67
    0x7a8003403083c04d100ca030600e60200f50980d841507005141ea8006103000108120802801d0600c0c9850407000b424036068540c840009001e1240c1e0000741981300c030000a90001c0c52640b211501004154a000030040c6d10303403804880000c281c80d1310500c1200c011030b407500c407041e01c1e40680006200311420060b5107429081240554003a50381603141c004100405c07403e10b0b204035544000b2070742c0c41c00c2000741d400c245c10b450740c0200350360801003003400d041220116881c0714001d005054650040b8460083c014035040c04c080c0c000414100603038490000c1300200142a25092110201c2c2c0b50007030001d01c107050309864900003903141d62098580300c08600150b4810044600d00420060204241041051071240c0c21140300c03860a5005040b44811040400707540e00100142c0c001e40007401408000c50b08101601e0035907403203a510010780c41c0c801c810000c500090b6807168030001d00f4007841480c800c550350000c0258418110070f550000d81c49100e50420b038411050500404503080c401000810f00780031041c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 985403048 1250 985401798 985401827
    0x80403051902011a12070b07020f0409051b041e0f1410080105060f0a0e0c07060c09060e01020c0303031807050a1e0617181e010b1507050d 61
    0x19080c4000341c500314480e00948803140015030340d118030200c071415071644e046050510468140380500001c80006440e48070710f2107048492030700400d8a108550b20101041103003440a04204078800300c0d4200a9500e110000c41d8404001c0100f09810507070800d070180c142d5454201e0300d202c03549800a1480340042181106030003105940b00341c00008034000b841418024202a8998040141001c07400d900311500a4540c61281400034a15500740c0c03103402c0040119810552950b00a540380e82d82151240f28400008145518000c1141e251940168045003614000c3d96104039135010040107995071081010410352581c4140002100c0503c0381a04403181941107054980c000d0f0380d0000b040b07809569400135502500c1051300b02500016a85d0400010406d40c072704a0034840059807024021900988181001840c1c0c50081d28054000c108056004cc0258000030f00e400b60704280500800590003400e200310a41083d020040305040241e0b1000c5030440060401805592702c1981c4104044250 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 985404298 1250 985403048 985403057
    0xe060d02120a0308060118240507060203041b0503150a02031803040f140913060b04021204060f1a0105090d1109010308041a121b0903030a05180d0b07080403 69
    0x200d000d1404184105411140300f0b03101d10102c0d040c0100050842003c1042402031306004a02c1040408c2d0020b882c607080c02440b0394030b501c9a0550b550210340c684145040580f03018000410f00c4104483c89440d00c400070012112540c00c107854004042d15082030366800204070940c48085103c50762160b0045400003503a030b0784403d1145441c9162030654011f90b016456010040d00108444440d280d08102c1d40d03074044812200b0707441c0c603080c0c500c401c1c444c00501034541a0b98180010f41c035211030341294855420780c0c1026826140c42d00c0c103000a081640d070700425150a10303003d90781008400c07106d03045000050310f40340c0c14040701c0400e205848890001c103032007502007000c1c6503070750351a4050074601860003100020394860a01c0149a01d00d02d40340031030200b1402c20802c441c0305d41c052100c410b400815940f502c64080381a40070b031b09a540125000c0a41c14000000c403d41200c4d001001008440018414080c500129204000064145640160240940e5400203010078811035610b03502c54422b060 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 985405548 1250 985404298 985404319
    0xa0605090f04270623070c031211031302030106150512060a09090f0c050a15031508030c07030303060909050c090403030e07090b010809010c020705040f021209070611070e060d02 78
    0x603c041d552124040a484c1640d6a40500030098a9a6001160603d071a01d44072502e080080000b000315921480c05000c1014074140e080f42d142c0300d50049904001d803994480e131030b800c1c400344824544032408001c03407180d803801400107030306402d49113001c804600ea502c8460800841856044401800900c4c0c01d034081d0a04101040015143c8905142c240c05280d42107400002450f003991801070a0b08204d01c0b900b0600d008014800728a014a0711a00244c5004110400303034240100d4519160703000a0060701010070190452a00010b5000c2260b00a9605005403a900c083e050104c1d59480000b80107500b185000c0c082d82d0402110441d00b051281c41c0c001750012610306020b0505103641c01c040c1d4040c0c0c4600244c600b070340e88000c480c0e80101d0818001c010115204001035a1070159100b0745e0f01441d00e9032054246d0b006194141c52039051540312054480c6000047d072a20340f12680207440115980340718042e41050002800c8054a040c203000306000c0e03e407002001603002d91032000301c0c1d00c607000320b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 985406798 1250 985405548 985405601
    0x609010309080a1809061215090203100c0f08010b122a0a0f05030708010e0603150108030903011506020606220207030206060906040c09031b0b030907050a0605090f04 73
    0x515143d411592000740c2c0c149035142c0034204807141e0b4040b0400134240501402801055000405c10030b600201b0b0040b6408440d002402810541d6000303035050140c00c0c00a80068000d0700000040d103050740e00d0801c8035101c200c094071408428080c0fa076080209015441c03801c440d41001a400c00c4075904005c2c546000c600c140324100c81ca2140640b24404046820404c5981198099490040c0350801d01c1c01d610341044001c0011a051043d241c1d9004500007040d86601c0900c03850706549a04c4544040640c1c440401594a03404031000a01075172030141e000502400d40e5011909540c15039024000945580040000d0040c06084440311030b4180b81544086903064401400d003280310350044e040d50700e0001e04001d04050020400d40c011402d00c2404128194401505000d8940c050302c448080501001356410445140e040120051400000c1c003100001c00985d49049940454152030502c0c1c4400c422141c030b005100c605d030b800130861110041c3c10b2400f0f03080380507014100d070200c100c440c1605 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 985408048 1250 985406798 985406813
    0xb03070207140904080717041815060206040c06030f02270411030105031024080f061e0a180512090109050a0501021f0f1506021501140609010309 64
    0x549140025034024a0104503003466102d40300c207948021225005207141c15140c113860f038850a00d009040100941c1c10045c01012a4140c1c2c024000d190329102c2c2c1c801c8166424002007100201282c61150818000a2a40e100290461140e035002c015601231618003003041c2d011340b49404109808035001c0c40070301c0345c04030020b05034650121482e5914004814013018003040300c06400d44861040010801400243c60001e4104d101480340d91000a000010311030016529001503910390380a01040c00002d0454000100302a65006050035104c054035014035007000301c241405200160b18103100001c41454907544441d200c00124018180159280d03541d4a080200180380140c4045001c11000741a5038406000e0000d00000e035055283c40b410200045c0d9210a500c0303002c14511760161840102c012207401000c0c0005284000384890400c1e6032500fa40821a4018080184661801c60070484890b1100c030307048400c880c0200090450031018410198880840141410f4844074954000740c240c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 985409298 1250 985408048 985408051
    0x60b07030306150801081b030c040501031a092d160603020307030c0c020f060a120c0c2108011a12011203020f0a05150a0603021c110301061208130b03 66
    0x103503800050340da041083c0c0c0380819009003081020001107000500c0440c1e0000744800c00040c04203da0300040e0b80180001e4078203000701c1c80141d001070500000008014042021800c04402c80d11011400e0b65054402a61003525942c5d0140003081c6a204100030001c0781060481400c04070705480b080300091101c02c07031a000f15401800082e42c0007080240c00d40d454810070401104d00e103404c010400d12500001d20007901803596503c00c040c00141400d1040c000c000b41800266000c50606c59540301900c040c0c0034860100003525540c0b2031080303441d40101454800c1e00d061105440e500c3e0b0903400d2007405a800384528071080380c032190401690541443d0008568020100c0e1490050790666a1500074104484010300c8031469120f040200b0000c1c00101e0b95408050110311480c0203607440c00d04441c00707401180c0c006500704a854504420001c8041e03903c3e008680600d000076403004640701130600301c581e14820b411003550010b1003400040d104000030070901080902200c01c15803140782424650780b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 985410548 1250 985409298 985409303
    0x3060a15020a030e01090e0a180210080405010b0a0b0d0903110f060930030403020a0f0b06090f0c0a110a170316031a040231050901090c0e13060b07 65
    0x10142d0620304055002d03003202d000b20428640200e481e403800c81820070121024003e980d00e0790b110135460301c4a0301d0030340e40b60039080d800411540218141c1c0601410303402c000d54043d2510f509144580f081400c040300d0503030032070b511b50078454a003801d60400b0b00b00420681c1c2c42101001502c2803c2c0b60402420448400c2414403d0301803d40350501090062401502c01c014025004040341d54004102d09460b001c2041c01c1d5903200e040d660b60301c61030202d0a000b98100018080e0b2240741c404010f01c8035401100d44244001d079200c2c1c44646412880101d1100101d40072040540c1c200b042d80e680c98490b0700070a007580760500441c4d413000700a58800d40040441319109107030040201c10000080540340c01841d900805003001c01c000c040880c0904c415030403142d0403074002d13a00002c2c0c5095051034201030700280380450302a141013003036070400c0b2031103540356216143c030400d603003c00820900b2192068440c1c00415071110b000850313001040c05881c07902c56800c121040d903034000001d41d440d038400003802c0c82072 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 985411798 1250 985410548 985410553
    0x307060f1809020d06290403020d08280f020f0709180210020d0f032c03130602010e010b01020f0d03270f02120105070c081309090602090f0d0c050603060a1502 70
    0x41c1040704440d41c1d800080e80c02d44a0340144003181c00d10041b14403c070303000e4940640c1c03c0c040c9080c09080c000101d01c1000b00e00c454648802c12001d506854080903050701c18007940e21035141841c00b480490b541c505225400c81d05130000d010400c40e5006541c882001d808070038810303181c1942c19400050b0031400c0a0600005a000010128a9280d0003e4032405200c0281810007400c84420801100700b00404d040f0282e42d5a00080d29003054800c0041c1c6244451802d4111040350700d4080081c0a071491001e40d0a6540c20918581e03095030001c21102800b4460000522420251000031000380110701c0c41d06103e52640102d07030112091400307020840310300401c1c0d0488003419a03c14000081410100e00c1c071142d141070140245564002031405c2181d03041541c2c2c1362a036060038076441000d5159408944800d02c3e12180c9420080584c028010008040340c14052114190301030104c1043d1001005202c2c0c44904000c0c030a502e49200a136030090406410f080301aa100c0081c1c00d4011070a560341d20159 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 985413048 1250 985411798 985411811
    0x170a09060f0c0830040f0f0303020c01050a090b0601050705061302120f0c1f021509010f0e0a1b1a07061404030c060f020a0e04051b0a050a0e0307060f1809020d 70
    0x11340c110040f50550020301c200060750340c44c00392a410b4024208010091214012441c10020301d0310a07016940303040350b0103000704203d0034129560700c000c03c00444211030244404000071050340c002c0007600c810a0b004005412569500d0420200c42080c034101240c0c02008070354000c140c080c041003070345000c0309418020003c12001d10104461400d0f0782103600100303401c500c50000c1980d40410800701660500040c0412510b42451050142500490b078000103441d01c4014200c2d00300c0010f503120b26602a02d50034031803c00c0d20f900b45c0c822030b002c2e01070300c1d0141201e13894880c2c1c02404440240101c0b4050800003601d200c94414a200c00c000a0342c00b0b41c001500d055943c400c1c03102c24440c86502180d00e2008500d401e5400c50081c120800400c1348a218aa5440010702101210a82c2e40c64061003c02d0b000e5480d0f512000141060304214414070005520480070400d6003400030380c440554410342c0700c2c0600849420405c80e02c0c10303080041000100509907000510103c980041c04592385000f00100e00c0b03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 985414298 1250 985413048 985413097
    0x6060118141903080a0915050a030504060f0e010204300209070c0501020d0b0102150709120f0609080318060403020604140c040c02071a1204020402070f080706050103170a09060f0c08 80
    0x5881b140c100c0c000b140c1d41301409820442d000021a40320318840c0c1404503203603803207060000c003c14403103064151150500c00410f01b80d10040d030041c01503401d02004040c8020701c1e0100e0310000000016010032a01d082040e1102615200218a501103054904094000d8007a518182660841c0030340010003502e507100243c0b2580c06000722090219100c2d0404032620700440000e09861041c8120000035240005207828000110000c903002da0300a5420b0000280c185010b10303103035200300c500b0b402d00900c5418a00408101140c1c09010342e405600521031610340b5225554134044890340586141708040d2029403a40361405030004000c01a0040d1000c1ca00e00204c8000230f0035540f0142d448040200b043c1c036110b003445544203410075011340d8016191a01403824400b521642200586006804503c02c41041225003200b17042c0c0e803140ca0b0f5901c00c0000c003081000c1d80d0255808010101c1c4c00b008040c46503500c1054003504100603131a0094100c0d1540d2145541a44500d1764810400d1703454406058 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 985415548 1250 985414298 985414307
    0x50706020d080f09060c0f0918041e0506070f2604060515060319090215090a061e0c030201060b0406110d0e060d0509010603140f06060118141903080a 66
    0x41c00410185446410301d409245030703885100040081b8092035001ca0100a18810a02598180580500100d041c0c00e011050b00b01c04070000c581c111140081544180c006e0301220308a00d80103175021b0f006040c543c8540c4003d4500082c0051400c042141900e020310031414041000e10200c124095032030301e1403e040c1082403d03140001c1c06501d03c003148414001860700c406040329401100c0780c190340e00b40d81e40069000c01805100304040c1d80030350070310802c031071000080c0014040448c0489202d1800d035503440040ea100da4000381e25951100030085500c1c8800d02030165050f9251092000140e0280ca4000341511500103400c80c2c0c001586481c81020b40300030410205565280a041841a0200e040d001850a219900c481c6000540701e00200e00901c00c2500882e003d035a1103a44100300d4482c1c6c00d02195101c2c0340440b035856510035a0b0224401d540a011904e6003200144c0100c0702280c1840ba15450034201602c650b40c000d02c03ea05148000c07200390004002a40c0714040c1c0e65510f5559290050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 985416798 1250 985415548 985415551
    0x260d0203150303090d110d08031f1211060c0a020301021b010f0e0606102c1009060e1e0402070b160207121509020d030306050307060c05061b07050706020d08 69
    0x1d000307503c1005030365040d550b030030180b100352644000c192100326140750204920414240d070091803120007005100e440b0720700711620049000b6402e43c02e0b403401d540362902040070084081c0a000c9080b6858041c9082c10404001d000c000c0040303040b20068065903001c13030b00726408a218051281c8202c0d0a90500396801e01031282400000075062007118025040303152030b0980507080c00e104415000019442c98000c10802c240d02c9405090401c1700c038040307981600c948965030541c40c41489400260070304540940c0c143c1e000c0d1801aa035034001e548403d0184411580c401048100001081c1082049680c890004004c0640308950702c051a051a03000081c5042d031068061007550441038007404803034a85120359081640140740340c030000c914444003400030184c0c2140039400150001c840c2c0306150701031300640220f5106604840201d66144012541d00f443d02200034141d0304551b012036a442106610703011180c103403803003a0740f5100c810780c2c50528000320390344502d01603004142a012810f81224601c1e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 985418048 1250 985416798 985416841
    0x6011a220f0513022a0a0b101d16050903010f180c0608041104020306120f0f1009020a12060b13140106050c030d091112060a1d0703260d0203 62
    0x940c14048844250050000542d0418a0401c0340179029946110b003003100751000340e00244550200c1c10140200c099548590140c0d540c04510f2144c98000355140e00d074114402c0d0a00c1c41e501c08100208402225241c1c080307160264591b403244181110b107100340c0703e500307003080d00b0311200c035020041c503e031003000c5400d103a10140500200c50208030104042d0300f80c0503250402140d005030b5035642c04001420445e0001224000c07032145559400c3e111900041d41d40b00d20100c06c00b110401c6a03120b454809446072104029000034a0080801c82c00952034021501c00d48a03410216030f0910610200b40710f4411119503c40d1541c1ba8110300b8038240150040c5400340100c0d00e032040c6021005d9a150b40da0748560340200244c19a51071450040c00002da100340c00700c1400030040303184602e01d0302c100342d9561320654180c1c40d05881c00e12228100400142c040d0942640e02014082c89407864a5005503003a4100c681c548a4a00c0e01e10f00000919200007842031007050a4016141c1c100707100b0070000d81c10201c509 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 985419298 1250 985418048 985418051
    0x1b010614060f040603050a060306050705130e0c0a050c0c06070c03141617071e0f080604051507020c0301021c2306040f02070b090109120206011a220f0513 68
    0x11442c401540100721016076149041c00b2a10f81c881c0b540c0a030007400f8550026024a16150500501c0e541c020002d1004503004090f003180e1607129040000c0f200000d407295640d40c1010000c0602503070048000e040140e81110a030791100b400000490507981c8070b2031040b00d4484009405104000040310255000a6944010600514180050100100e05000b409110b03048060540745010042000708064120419080842c5c0006100e080b0030008030f0043d201c1d14460841c001c03548180004925200320341280050545901e42d20790666040805020307a01103009000402126071801d0005004d54100488100a0150594203600403507841004190103440c0500351892120311046403a5081a41141c00040701d004165145e030081c4107190005000a142c2c104104e42c680040d8414460329004049081c2c5486402034100e0300e52074240603402e50424003107a00030802644401a24070340d4501c0104c2002c2c07000006c00c40d0a43c42c41e0f64030041c2c000316416010b01441c182215402c0e81050303556030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 985420548 1250 985419298 985419307
    0x5120307080703020f07060f06050f1e010e36060306040c03030e0303041e08060f0708071b060516030c020a0f26030702010203040b07090501020a0f081b01061406 71
    0x90090201c00060302100405402281030100007001c0c40031110001d9008004116100e011903841e4041e2a40e0320400f4452010710f0794908030b03801c00110510001e10310040383c45d0340348041e0700156400c0c3d0505812580001e481043c3d000b030740c044400464170000100c400c0314408540d0f2590ac0d0380107000109428000d070025024840020701005d42078003030b42c0d8541442c1d10303074520100c0030a03e18003940e40700c0317801000602100003049042c041d80b101a02c42050541d41d1955442c807403003030b580c1030965146001a14580010300e5051184c0b01c5901c014400c405003229454141e00c650301602d4040c0c56003240310186c011455200c0c1e4047c40780802407503040c005000c5015150711800900408020050800a40c485048403042403030304044010440500790325849040c1840024002d41084608481c11030702c20021030340300b40c040c2c1950300c1202c038164000c048038041e9581d108040702c407228007103840038001c0c800398101c216080b6025040380f260200006001e8a408084038203000c0a40c05c0d00c0c0902e40c2000b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 985421798 1250 985420548 985420561
    0x21e010507060908190c020a06020d05030a0b130f0b01020d090617060a1e0f061e0c02011202030a0b01180311060f0d0912120c09140105091507051203 66
    0x10300307603149103401080000d0300150710300f022410703889580171019240c050780c0030340c07100943c000e03e01c10341403402a81c003002a0743e250b22080e83c0d02d0030044001008100103200044841c80071303070050142084003804140805018000e484107440480402042943d15420b418110303590400440c1d100718014600154000e141190107014554501c942c003400d07000c01400121952168425603000b00345035503517405210103201c1200240801070285000c5070b5034080700010440d1007000c4460b20201da4002c3c0c010780c4004070b101a204a1410780c1c08905010624640030b1309414640b0140d0700c503d40500001c00d04040040c001401260301350250200c00241d00030600101d041a07000c500d44c0350050328803568448280001e01d242c0e00130b0160b44502c40d8200000d640401c0440c20808041c14441d884107030281e001c1c101d1503001d54901c010765100244001300108144600c80010070b86629040c10076910384203022002c610502841403d040316108006951020004200f0440c00507810720000709040d400e001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 985423048 1250 985421798 985421807
    0x60a080a1404080d09030905060c0f070b041508041a011e12050c220515010e01030c0e130207060e0105011706090606010810080d021f0b0f190e070309021e01 69
    0x8141403684130b5034911140042502824144021b810000c001d1034407020f00c0c8080c13035900c0303845094101d01c43c01480c4000403446400e8081d901a40c0720348120341c3d07280d01c40c903004a500ca01c009106840540d00c110f00e4511011001c0a0a4040c0c0b034490b50041307801800c0700400c41014820341c080382200504050140214101040600600400322800c042070300304507a5900800740d80741000c06180345040248141306500403d079031003c0100b070b22111001c1145e08015001c4802180244002c070725284281d00c11881d04a02d0f4068080c81c2c00c40040c24104161209012a103d07014030b00c66a0b9940c41c014003030b029107400c0341185444484000d00302840c159540300d440f40c10240c041410700c0018008604041d80040042c00030f80410300032510643d100e00c40080d9075000d0740b0155144200b040c0e5410114a01d00d0144448200000e4414800180200140801259483c0958216244010000c1403800401c4649401108a9900425108428010403c80c0f003500000700c1030f102c3c0068095140351760007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 985424298 1250 985423048 985423057
    0x11206061e14060721110615041401050d0323040308041a0705031e071202010b010f03060b12060d02060403031d060304020a050105030a060f1d100503030f0d0902060a080a140408 78
    0x6a90001340219041c5005450b8105070106c45286030240c0001c1241e03c040710200018030000c00c0700c09200c04043d142c00404024000e01409400039030604207080800d010304070708a000550501540455240d0305844215600150021188980d00040070015010785040340b84d0985a81c0342035625100315991540c0d9a031040200305400d405035051112181140030007540c540380d070092200d9141d4506c00310024001c2c010000d515020809001c0016802d41c464840d61003503581218825140080c0c080010b01220b100501071a440700f003981c09400142c07100c1025100a521039140e20300c0d0005030741c080010b00c00f143c1c5007150091009204100c056941c1810030b8040700c00070700b8220b81d245c80d651142e90250900d5080300c0442041e611001691441c01042c0251090358114880d0b142e40ba8801c0310704241c0781a200b100d603d43c1c03045c06201224070004e001802400c1e052500001d101c11030b5408101290848055440800e01c214100710f1620014003071241144d1000142e0f006030315095885001ea03015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 985425548 1250 985424298 985424333
    0x301080307022202040b090102150910150506221703070308250815061e130f090605040e030a0207180e0102161a070503011206061e140607 61
    0x1056840144041800c1d010440b0f94400c40c1c02595035a480381c015400c87da001302111030040c41503407501c50f000c0c1c034062000703070241e2400000f4101d400110703070b5010082d082c003403021215074007022800a220b03560700c0020082d2042c110a075000905920603032662070003c83c1e00101c11543c1c0607410300b580820210440d4411685070401035034036190095102190240d15005c41c100400340f01c1041109900600030520810040082ca5011404101030240750f002e44840d9038614a5503030080300d61011294044c00c40c505008002e107030035564400c14807030307604007591201c80b04070b545003130510090a29014403104461400300451522118a50080d507070038080c4115000c000110301072121100961b000003280c0c80e0054029034032a00a203240702c03200501c081c02200c950199500500b40740c12884400c3e4843d07032680d21014150703841c107240409464103000c001c071061075944902040d000601400d038658650002402c90104e42441c04584c01c071102621581e12400f001d000c801c00042c802613041d0810709 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 985426798 1250 985425548 985425559
    0x12040b07031425141b0120070215130e04170a0816020f0d1d0a03080703030e0c04111b030f07030e0a08030f03040501201602031e031e030108030702 65
    0x121000407a4404c0c140c4035604107a0354000384010381c0702c900760540003c0c20440e40003000000348010300c98501c60350719000c1800c441c0c0140000c1c40549065260b80c0c0140105030034041c41c0400d0404ca03803682080a030441d590400d010400d22040c0034544211384a088500c02c0e18614040d0100005007810310010400040c2400b001900403485100380400f21190800d0411981e405001e03042c003401441c0c0f20b0792075045010b9610350044c824941070640c0300c200d0707070409022450000c0544085010707050751114921603203c2c1c0700c1d0743c004584841c420303208041500800300780c54003034a001e181408a0032031000c544590040c8109c0340c030b030b05001c4103c4140c82d6041c01d200f01c4803c040701c00320740c1030a540d50205c880b5010121b4401100034002c0d00440c4076911030382c000c001c1e184c850080c1c016601034691003c0e002d180d0901810050b00306d050b0303905007030500003021200f1078403105c201044c0d14407203034042c40c1c600e410116000000318502035502d00c2018103810000e00b15070400b2034803a524040c40c000a0b1242 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 985428048 1250 985426798 985426861
    0x11010b01050909040201090b04170c0d0c030f08093622060f020d02090a060c0320150109021306031803030207030512010f0f09181202010212040b070314 67
    0x40e1f00076030181e801415290041134685607110181056074180d8000e51030389020b6a0881c51940c906582041c0820394801d119215890940e19580b0400010740c2086449150070000c0208542d24008803040ca5840120341c0040b40358a2000c84174025a08450130840d4003000c002e001405a054480e55640002030625410001d024100350001e8002d8503081d919503071000601c1606138100d0340017030185403400e03281c00c45d07202e6450300c04407a5994011800740010b00501422514060425840d8a002d903040c0101c074500d403090101413269600a0780b088103d50350000b00300390900304407620b502c0105100d060070041d8416482602514442d0311400030200765002848104041c01071080c2c601c0c154180041141541e1902500801d03480e0b14050342c0580d02001000040303200c002c3c0244042c00380c3c00022800c0d0500280e403005d040d1401d0780005001d46d5001c0c00b20740d16102c00b10701c400d0302c01c50013410044c8060400080180890344030700d030170061100155040089110610a02600814213804803810303d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 985429298 1250 985428048 985428053
    0x1c110a170708130e010617070f050d0216020a0b0f191107080a062d0917070605010f0801020f191403040b0f0106091d0406090b130311010b0105090904 66
    0x144241c11000300380b0180403420411400210341440151094640d0742941c691301c3e82c6080c2c880742502c4010000c070309800303c005500380348102d001e0381c04141035081080c1403840000341d00c0c4c03c1e03800200d00b00328091201000d0200390300c1c2a1000000401c6030094952402500030544e00ba08c0c4074151202c1221711421100611692150b5940703000032107a0f00c15a0045030301d9680090302ca01113400b0649205041001d00001f800d00300b00c0c88540b8240d0034000320045d1079440d1040000d03260002042c1c540048040d510b005964808008000c0305205010024040d0304044100b60304480d10703040034400345c3c4103029000c407079009002116402d0040300b62402c25200c075440111122210070200005842020090000300008415044e00589d0080340c0e1144170f03030300e4040c220b41c4118284a40c4000881840103a6250000800019000390068001249a010b55181d00690820a88841c036540050034031910070f0651100c5003c178032a000b40f0091010120700c4000074660700802c004a0302c10b14150011908 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 985430548 1250 985429298 985429343
    0x915030b100e070906020610050d020d0318120606080309220f1407110c010e1002070b1602100e090a020a0516050c0a060206060303030c0c0313081c110a 67
    0x4040c401d8000c2c42c60302d00310030001e1890b2814440c040241c85400085000d80710b0103441701040d00c0c8040d00c200c1139500e541d02040340c852031214080c0c0911030b4995059404611450007035020300f016522400340c007001c1d49031800031180e030750340003804035041030109500658803248020202040c101e158070211581180c810014a0a00c02d14403a907854802415900d024213070300c90b44500d8441d00c034015a01600132415880c0ca141004850001d01c001148400c00d1800c01034110b880011071040320369164880d13500c4450b6520200e444c040241c078030b1070400210b00d0000c0f464210103180d80740c4801c2c41a6540c0c04584203650103001c040c251a00131032380600a48c4200183c50b0790080001461007000072500307010751680380c0ca104484c0920342800021960b580000b86c81d6005000c058010340c40c0d03585264884645411481450000d0300040141c81c240c500e8080c1c501000d040c004c40a80401d010b00c4a2441e1402c2d84203054105104a1613140d0b080d420000c100807036400d4200c1c52445040454951080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 985431654 1106 985430548 985430581
    0x5060304240905010e0601090c0203040609060c1e030305010521030f07061d06010e0a091208060103020d1a0913050318031e0114010915030b 62
    0x207100c0040d810711038010100d101000600c2d030032141e072010b09681440729410b07a0f50340a00c0061142d50300b10b10130141d210040780001d41c1340600e00790000d000001e0382c0c400c1005200c01d5140d07081c14025002040c504603a00407410750740079034040c40c000c0d00400c1c00307000745230042c00e003545100c810b04242c3c0d1912141c12100c0b002941802d001d00e11102580c3e010f11011604a600ca5511084500585404011511490300908407541c140b500da865681c0005110403455410121441f02150907581d0783c4d2a1102c5070f107441d0101e42c2e500c0f00107030701a02c90b4002200d052440c004e0449107000c00450f00054189048884040ce40c0300c01004c103c1d12100c09401a0440d001004005088044020301514441020301a26042076035240d100161030b82940510900e41d4541100141c000703520724190707001d403c10042c03c000c03e60080e80300903071115a80c040142880b0241000ca0301d1080c6402c00403 = true := by decide +kernel

theorem cover : BRFrame.Cov 985251798 985431654 := by
  have h0 := BRFrame.cov_init 985251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 985251798 ≤ n) (h2 : n < 985431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
