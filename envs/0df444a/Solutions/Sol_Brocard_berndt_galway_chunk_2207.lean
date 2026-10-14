-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2207
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:59:54.123807+00:00
-- url     : https://prove2.me/submissions/b7e7f482-110b-4efe-992d-caf0dc3aaa3b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 396762589 ≤ n < 396942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 396763839 1250 396762589 396762607
    0x8060a09020c1005010803040305010e0a08031f0305011416020a11010e010c020a1508070804110616060c0518040b0f121002030a02361e091311060f 65
    0x50003402580342403070704032035400e40a81c828105130f60080e880040746070000201070080c00020301a42900c1021700b40200308400040c4c0e110449448018114110700020341d0411007504c894100700c1008507005030080c485010025103400701e5000a44404c0d40100c003004503103401c14008200c01c14201c2d00020001d04100400d001074035040c2c0500351150400c004010400d0040c1d4401452501a1480800c01c5c20078003145c0c03c4c06030000c1405040207062250020400c00050f80300152600a09416140c17aa1241a903c1d1040c180b51900c05008020504010000400c2540800580580401c1c2c00c0c0c0ca0400030340c10310600c82103600c040d00d503070313000904000c21000c00d0400d4030462501e11b603071004542121103032001c000b040741c109481c80d180c403d4001918020100b002c0d400030008044080301d1101030310600740d003141500d003207110090042207040c01115002c0c0000003d500ca54501600075041c902d4200000761205600300b9048401908800d60001c081c06c1000a44c0ca40041a086281c9400400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 396765089 1250 396763839 396763841
    0xf010207170a05010e030d0506010804080403020f04092306101a03060d0f202d1f0804050f03090a090e01020f07060509010e060705070b0a0b090c030103050d08060a09 73
    0x41c01000e04500c40d5800362800140d00344100d900e84500d08020f140c80c1c45060f0b0810058071800342c0311a0400008505210100c0c00580448003207a504445030483d08001c0d00c0418040d000340180034000103103030224003180c440e003020114010001e101c180c4a00c0c1d91041300c240f46c2d5160b94080c072070604201c0c86c24901424a1074000359000200141960500d0b6175941e0350314504c00b2118800c0710300c280c0c010b0000e04821039012003018580302c2241d0259410029885809202c00212000c580c1000d884820080c242c649100a4120002040b482ca60030402010041c080070717000d440c200d508d4403e0320f2642490a10200695607030780c90003000e031107415140a000e040540901c04036001103550800502820151208c02445194400c0320041040c0c640745030842d08403072141e03041c100700e9000603041100d2140d00004490040cad51000c0c00406603180c0301c240c1c100808100d50b0303498111407040300303001d040801a0055030480e841032044814115200400f00d80c0424255030245d0444100b5405229090345 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 396766339 1250 396765089 396765119
    0xc030c110402030705120703060b03060906040e070f05031204030c05010f11010513020f01140913020d023702030901030914060106050d060603050c0f0307021906060609050f010207 79
    0x2402038004a94404000181280d1041c3c8011010590000b200d240c203001c9001d05550108841c2010080f542c5840c82d294103501c801084e952003840c3ea4000210385544a40c8006d20076000d200489100c6522215005034000b402e0284903c64410000302c80419403010040300c0c181ca41c00172a5082c41c0c0e1800300150f550b18507411405060066200e86d440e00fa044c01d00ca035038442d08c003003104101095100e00500c0fa40321700140c1143d04001ca00418204002484012507880c03030f9040c0c6d01480400c2d103542a04000780181c080c628092800001e424400c900d1440307020780c07814104a8044451640107844840c1c0306c1e40162104003581044c462054198000d07401040340e07a0191030031207504c18014240c00d061400c2600031401141002c10b42c00e1526109105d154090701045c00c00b00502d051801c00c510860103180041200180c0010000d17a04910038400031005a4080c2c0010009204524141c005040c041c0100d00000d90300450000f0646407480c1c107550710100680160043e141485802c040b1425 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 396767589 1250 396766339 396766343
    0x40b10050901050c061f05270c0d0203040b1803040e040825050f010c0311160201170403050405040c0309030f030f060f03060204150513090f090605180708010c0c030c 73
    0x14244414801c481d0180440d5201b800b4100b41121a00b1104a1022010110b5080107014075190521201e1020180d40d400c00030320b103001402882942c40058040c0ca80c82803030083c18095001005010401400603081401665030716902c19545003911040b658a0081388240c401e0046201d02160105000d500200264080b08030060000e9902d460301411003501000201d03095401440703c008004000c1c4a1811031010510382804030480a03000ea4060303011f141c0f00343d0030860310424800c085a00405d0150421200130484511030f290605016045801c14465140224201700454410510a00c280401150f01d40c952150300000c03118101d008100c664480007005a5a03000820030107010101180214860030380582c2c0c4074140011200042c03000000d08050002c00d00a2404040800406100b0f40c0ea80200000c2d000310801c210348040d02c82e1000c081c0102e80784c44181301411400c92001c0b504181e07100e045400050340e03041168202d940d0841d484000441d49103410700040e03c00c50100c10128 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 396768839 1250 396767589 396767597
    0xc0210090c0b04080c100e150c0106030b011503060503060609130c030b0a0f18080301030212071a04030210181202060930030307140d020c0a060b01020c040b10050901 73
    0x542c540c8806a01503100c1e400c01000e55000704032a542c28a0201c0400340b1403030851811a0419000c0c1c40031400040002142c00303102c840100d00203402410950041d4002d542025a1050f04e5035103640c11980e1244801d41200000e0401d0404034580c20000f4100d4040c1b2409801201d4170343d9890405888294519000c485529446c080040410840c2c0e02c001e0058840c40d00000b24500c4039501a012103410300f8040c16210404200e030f00105101e0b009485c11282c0603180d001e103258a80e01c0391401d03c0e041c0d40100c60b404503540c400c22001c2e14003102500c107591080d54407090003890600c040c1c1e40c0c240d140c03104081040305c141e400d00c4030048c08030403d21040c0c8082d003c581031168010002d0400d007408200d55507502000348098510711821004a41c9000f0301b800514514240003100800c100c884e0703200210795950009421070010207550480e40d030b5818402c01c0d12031140807444c0c040050043c2e0787d0030a0040c071804a0380302e0185443d210b0b5000d9807900800481d100c280690043e00c407900b005d40414140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 396770089 1250 396768839 396768863
    0xc0609060329030a0c090b0a080a0206070303020c1903020601031a0906010303030c050c0102040e090d0c050c06130503030714010f0204050105040e1506030a050105010f0503390a0905090a0c021009 86
    0x4101000c205c018200440010925240e003200b071040260701503004500c568442c0b600c0c4809030319071504444010b0303054079000d6030b9214081001c92406200300c080c1c02c1c603038040700c0710101810341c00704000c0c1c1030340c1c81010610110090008100f10750002600d0325806c41c0c10100040001a001e54000014a061800c1660805850501b603508a800c08e900031405a203c0e0810032140700c00c140101042c4101c10309009100725850f0715500e545410b0414400d02030400019130700102c00d550410400140700080c12640e40f54910316003080c42566140c0890129803c00c1901e012940490084d5820303100c06a640134240791422007242ca1109026040c0800003070124614441602c0f0800254824608858082130a52500000521403000401440c0c2041428818003003544102e06124515012240d02e4406e03154011345210b00012845010018203480011500440e0ba00f114118046503811107a400196540e00340310000e03a403010394000010b8228201c1d841c14110036a00810500340528103101035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 396771339 1250 396770089 396770093
    0x50f04023003221205070b0304021305040302420c0c010608031305030a08041203030b030f010614031219020a060c030207050115030206030606090409020d0c0609060329030a 76
    0xd40d0f100301035042c1c2c5140211401403c0b0018820598000c05100a41016040040c0c541c1c0d5183e100d0703400752000c280400408a01556603455400c2c180c041a80020461410546006503135610f00400306075820704e60b82d100c001a80045007103c2e800c84005100e4200d40c042441000612000c000c00446d0005018804103030f890710240701d8036014140400045a545090000d8501c0c00390745036010b90300c02e5008810300e0000036010400c0d40c04481c981241d00140080600e4260090022000819090321580155101380c1405402010460780101a441c3d0000b01480905803140c5880080e10b0100000f000a40c00200f03014410b240e00c00242c0c4142d0303031804030640e030300015244c3c603d041e80c00198000c2111000d110007841012840035580c0c100c003408a03c2c5501180160000a11140c0724072004990300059450720703001450000d50050040c1d104403020300d0111580c1003503008050010350b0031031010615900070321500c6403d03280f40d020000784270140c8040d40200c2400b4030155405004001c20040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 396772589 1250 396771339 396771343
    0x6090501061202090114060d09080903010f020d14010302150a0908032109190b100b030a060608010617011401090504050a1a041e0f090b01061101050f040230 69
    0x70103403070652802e1081d010740d801000700d1414103800c5011103905d5100410040e070f5031002101c900e030080c030700e000c12403051600300143e1a01407111010b41550800f07026800c07112196004000405005008000d14016100c0000041c2800d020082d0800c00340d102d11180700400002a12640d075861502c400c6142d181c88900d1300710742080c10070701c046842c100085039240602c4a00f095102030194010302c00c1a810b20f03000580001005000b42c0380c84c00b484040303410314a620310f1000180000100090352410403034880002052140b0031100007804000020480d82d2081642d030007080031001400c10540d081240442d074034240f02416034144006290001000d0302c450007040e200e800c0b000b00c0014424450b003007e841c92052220564441c501d021201c506228400c40e1400008141000000c2c101d180e141c0000c0007840000406021041000c00024125a10200840c14041e1440080c4555158044040d10040d4207880083d03100030200000980d1041900040f03001811308041030f1110018000094 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 396773839 1250 396772589 396772601
    0x20c1e030327010e01171b040801020a050c060106090315020307200129100509040b030a0503031014090403050313081b120708040510030b130c0e0301200706090501 72
    0x2c0051000254044040d82c100c03450310b04018083c2000c420001d410890704e0460354004040d401103500c2e052030000740440b82425034010300100f200840d034481d03440c42c0107051904642d650301d000d44114400450b15505c00c81a02048981c422480f42410030200081c00280d080101003204000d401413640c0301220007400700000d9486104000240c400100d00b40b912030b5251881c0d9085502541c1c0c52409003600c9a100e12406010285800b684414440c0d0016028002149501d035045c811709014009001001c802980503d4000c1c0c1d810500035a50058005d0a00360b01810640c031400000000303002c64010350003158004c00b10001169101b039a5035030300d0080e410058002c1c100c2c2d0191a107400d102e00e000c01c291000c03c20b220880a06180c0595200400392282d0301440e40a60400b81001341010300a03045006401d400030a0b8890041d03a11703101200900500140707a0018050583d040c113030b414188541c00040d219615106503020070b40030a02600c0e40181402c445003903841c07115102041081c8603071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 396775089 1250 396773839 396773887
    0xa260604031e030506030d0e0d05070902120a0509070504052d01090605030604050a02012006010801020d0b04090f08090a0306020c01020a02060705030f0f06131a030d020c1e0303 78
    0x1115642c02c060030150070281c001c5901c00245407412081c001580d800161070403502903240340c4904551a00700c04180040c0d07059000a10520074000081286403c80e00035180002801ca4807090a40e502000c020275140c0076101009650410f660911582c20182c12240c0e00c000559403180842c4c02a003a030045805201d41c0c542118802c440060024284a0140034000c1104030b000703002d6828240c46017919810140002418403928465042c1c1ca103c4403010071010b0003050081d034401d5a900d40d9850302030740c090661018014a070222102091030540300c1d86044c0380d005440352031081c640da41ea0383c00a030300c1003030b4035980800c10050000010380280000d14080381150009030b01c80141510280c03402a0241c0301a05002060080100341c901a60499500200e01c540420340d40d220440422018031910b20442291070801c6100740c6c10001c00040c0c122803040550845445035010041243c48032025848160b000e8841300e0f401ca0300a1000090581e2244d00900f902d00e0b04107120f403080b1641e0b07001500 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 396776339 1250 396775089 396775097
    0x9031704050d0e0303040b0f0c12070803010504050f04050a03080c0405040f140106050903030304030c0809060c0d02060601030c02100522120e030a0f030302031e070507020a08010b0a26060403 84
    0x24060040790f200102d031940c0b0000b9070046041c18101860818140a125040a9141c1011620758100e400420031019044982e28090380e941c0340a041009455100340034032401941071201080c021028590030a110f01e420501801012807141c0e4225170240f0080c0000403543c0c420721000c5810b40c1c5600c5150301b4100c41e18000603800050283c0c40d440c0140c1680407105108080c8940c2c074940c1c9001c812240d22960500c1c00d8101c001e12032402550360701030800c41d00d030081d0011940750008038000604903184103403502129032641c0c800c3c00440a07281d03d5814840140c01c450112150750481c2c0d007200380c201088003a19080c508801600b01a40c809002055401c0d1410700008100070740c01c000080c0341d540040c0d01821b41201c803625040d10030b510411004040550000c00100e102036480c202c405010601000e00b0401e003000c9400804640001c8000e80c400d40c40d0760380000d00400140f15030030002030058505603184d0310707106613503852018012292600081003028000c69490901c085485540300b030715 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 396777589 1250 396776339 396776353
    0xf0918180a11211e0c030304030809060304060207202d040e0f0a03030626070b160f0809151611130f0204090606080702060411033c1207060903170405 66
    0x8106103031990340c10b400d6021fa002044140302042c15030044481d06a4292280780d0b403070b119468820002e100b0060b000e40800b00c02e1401e07002540c007042d9040f6000c2c4c1c0845030504100e808402e40100038074009100800081c442c03402c40c2050508be04442c500c0301c2d07084c0956452070354200803681410007843d4201d000035580e14043c041000351240e0740741010035409490b4410405916080d55800280c0110880f1000110720360351018008907005401c240c2c80007240e50f4200c100e10740175640da000f003102c0503caa03102d080042c1d043d4003050140c44940d040c00500200050051301d80d000d0301400f00f49015084001d001c101e10a451090040c0b0440350204100141d46902c0c4c2080b80d000c5501c85c1c2c105104000da0b01c410300201550000e091500070342c00c0700e42d035a1078400c1240003910705440341c058498511440912180c21a800003281c5080382e02440e10300310220310485000c0e03101c000c204c0c9105250b0000788041b50109286078410307282e440c4a41004a4685071582010032224001c8500f02c8003540412 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 396778839 1250 396777589 396777643
    0x21305010f0206010f0905180f0106080744030406110601120305220f03030305010302090c071e1b03140714150f0918180a1121 56
    0x9808500c01c19451010b4078441d4101100c42c1a081080c2c818203007540d0312200403405c818400024401128900300840703040d00b240c3c0d11050701074415407003001d07000e0080000c0065144001c3d0300a15561044850b038070550541022950424031107041c0028500c42016007440e81160100300030405004191144004a800034960a28200d0160499500043e125a07060006504802524a600b0100d182c03000da0941c004e02512003445a0b51020140405810300007050607015440703981a68000d03140403880f81da40e1151844180320b8460020044902c240319044000c0d003c0b9401d00c082d610034680c2c8403c1c006c0d45551b80f5070800c0700340c10a503403000441380c019910040c1041584010159000c0040b1141e160f04000340010440751854448090000f481e080c1020f1007a086500b5035000802ca040580c0c98a4030122801400720f81420f8a205001e240103020000007404c030300d10650000406942118000c2481607200190100700303540f2485c0f2618400700c000900841c408691082c1c1c44a40c908041 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 396780089 1250 396778839 396778847
    0x139110114030103021e0901090605040e0304030b1f030b040b090105070306060f0e0612010806070908030f040b0f211e0405150910110405010908011811030a02030102130501 76
    0x150406050080305980807094404071000d50b41100d40449904a5102c0103c40701c1b03090040c41c400c9298428020000440c82c12140c1e0b22100a13210709807001c203c019400c0b40615540d1280d8080581812600000590045e210710624a802e038800e0900c0d0920f140e690303aa0b210700c20f5064500300c44c50b440b40d1003080300c01c5074240b181e40d5001d0030303505d024803550349080d10180c12042c41c60b190108001805445505548980003111780264000964070920b6a5408905031a054280c03003010016280240006180b10008140c803420350103a08014a042d2501c0500c20aa42c400310804582003418048840b100d48007560071000c001440c00310b06810710701107040d42d0b00b01d510100e503860811540000d00010030000035840c0007048101c609031196846903401a40b410103a8029105000c4c14240c900038042d00b07010181c01100e4081e01c3d0001383ca07071660152820b83c1d41000c5188541d0940711200d401080300000d146640500180a075410001c1c16000300303017aa800058030750048624107008010700c3d40c0c8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 396781339 1250 396780089 396780113
    0x703050d23030f010e060d1e02030c060c1f060e0f07122901091a0c0d080601021f060b04091e0e19020f0d030f08150f0139 54
    0x11081e84510310320b41510304002e0082d041c007030301d0750604600001a001d40c886008410a0359045418124248448904004181403043c0c08a00034041c1241860a6040c000191001c40d41c2d040c0140000c0c001c500784a4695400c40c070400180340e500c4400000784015903101041c02070292203041c400610301041e010b4a51341e06601c60b100d210340f4050b5440c0c01101c400c0322105000301b048507101c2101c0c0b84040102ca201d540c80d00030090884d5a0034816071600c800c200148170101001d4203031030103409159019202a00100c41060140c0c00c81c040d2071001060252690245000d03000000690940b0781e134410311160015001040001c2d0b480d00390210241032080303101d030f00d03c09000c3c0c248003080035100402d8032002c1500801c0300c4010021030a07421580da010202c55a1000545030708807140c0d00d4100100501c01d040095000308134050080340103102001054050414054080c070205070b5200011254841600e01201100f45a01c00c0c030005124542440e00000f941621055000030445c10310503040c000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 396782589 1250 396781339 396781397
    0x9070312112b141306021005060f0114221202040b060c070515040812030f09160612060e04032a0308240d03081b121501020703050d 58
    0x210b00441094600707030034601c10156549400507400882e040a485240a1851a518101c3c41d140011030042d50000f8a00d0303010700001c4041c0120f0b11214140041120038020560000b40708514002d11204020300070201c0c518a0006104074007a80300c101e03a0042e0458021048a08d90441e000f015440c00740a8500c48150403595140b0f00b0f2000c00e821980c0e1881031188500852003681c01c07100303d105120648000b07003001c0054030340d0195400c95240041d4811a082440003d40c2000300314150400980c42030016154080381e030125040000940741460b2080e49048003684820021030b55501c10044103005a2003074507a40c1004d20800314160712169050401d290209420b5145004294000039140c1c1052180c0d01c040c03811418082090303036100c804800c0c1c2da041500c99062004040c3d000c5061842141d0013102c000401c620071682c4405442080a011005603100d404140251008452080350110500450f46d0046d0307a5030f5083e0074601d841c2c6607040441d00361014299400e00d001004903000d2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 396783839 1250 396782589 396782623
    0x6030706031505010f020f03030903091507020114090409021c0204140f0601050f04033f0804081317030d05010909031b0204021b10110903030a03050907031211 70
    0x556840001960150b40e100c1c0a04003d030000c5100c143c2c07070091082034000d04007e07056035901c1c50405015540c035031003800001d0040d072980c1d002c040900d40240565080d654169030348403421840c400481750302c0d0449083c85510176903c551550050f0f44111000103140300b034a40a83d154421030042100b266100c00c3c00340718112401080118050340c10354642c0d0311903030908245031216850300709005503006980000300920100304014810342c0c102d244a0f2054144500081c0c5031006c0c4003c00c80c1c031031014010400110f0041401b150000700c030710300030340f64032080204d1900c2c28550321469074401748280d01030110250800243e0841102c4103010740c5016101c0343c1400d22107140941d4000300301036000c0d00d0301040f00d00300c151a2000c66559030101c864880b0720300c1741c0300d524420110f4140d44441c49100500c0342c0a00c0c0ca00754200e6000d880068600380c11000700075508083c0d40c0c090503000752000a01040c000d00400c1004000a000e00b049039822a485544004a0b00f030782e00380702d071b1421f0752a800c80b40c450 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 396785089 1250 396783839 396783851
    0x1204020405040212030a020f15040b0f1f061d010302130b070f17030702190b010605030901141017150103230307081215030304151407140601120b0f1806040b0603070603 74
    0xbc511502c0216230882c0300e071003015440e41d0b582004a9086605144201ca034a514500b0004440343e01451582c000100c864110768010000780c015412882840084c0c0516250f41004100c0e03584000c01808243d4029040d5800c000003030b070795540c01041c1c4041c52140410000c418880d860368100b0040ca103000315a1a100e4508000380c07202c3d401003005102c3d900420000100003200c44032300307421508066949a0201c206410192009400b00f0407501503112180c181a6180c0131070303d00021241100d42c0c940e40c6a51503642076840c0e0a06c0c20344115115603c1c8883d945a96240600400c000c2c203405004400d110b03101d007030321500d14078540c00c00340032800b14070701c040794401d0075603404402c980495034000091301000c03c2803042600c061814035541d040709103000c203030702041c030070743d4269020080047d50903248140c0c0c0300c1561141d09540c0032409864039594800085078403200b495402c3c5c100c0e4074168010410105200c21070b1400c0022281114903100e003505101c664203040000c070003c0c0c081c5040512034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 396786339 1250 396785089 396785093
    0x10507110705010e0906010210110c241f080a06020904050627060102070f030506090c0105030702070302010516080310080601050d02061e16080901141204020405040212030a020f1504 80
    0x1310f559070003107940310f034030740380b02003001a0700030000c2503002d6221500900c4121000e1445102c0c0390000c2d0019805800b41595040c90306500000004101c1074401c929191078841c03c42005019410386c1d5140500a21208049941c0380100440202984520005070790303252220140b00c00e1301c4015021901619004440d07007050300d100c010025141d1505030140102d070780c4010040345003003103541c41484001d865010120a011012803454131642096084031419006840112100c4c80201c502c0c000681110f1406e100641c031440050120302c03c000044110300d149a1202c40142d0b000b51503440300c15805640410450350706001e55401858100e94864a101844d0041b420b00c0c4a200c00f04190308442e040b06410704800881070741c012017100088160325602514040b5125403021119a001c1000d204100259500d128100c0e10700d6111003140b01e105885d0740c1d0a010160a000c0d108a80c000d40007030780308240d141d00704040c1081c90141c1d40144818804d095005007080788046000c51340220301410840 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 396787589 1250 396786339 396786347
    0x3100f050f040b13060e0906011e03082101091e05060604050f0a03050d0908121911340905040209060904030e130c0e01170117010b0604060201050711070501 69
    0x3030071501a5000300d00c07040e403000003651241c2e80041d40f201080c0713445004030f02c40390388540c582c0c0b00c0c80f1703d4000c840d4280d886d622000c2d003140c000900742e2a900078804c0140005481d0002070712002100c0c0f01840c401214070b40740c0240b140303026042011580c0d9110304160780c0c021018500c096090417114100901d01740032000c202c442c03156019444c0036203100f640030291500c900e80154006d41d04101500e43c034601c1c908004000c04540d2113404130ba4820805450300340b08802c4219488002d01c03002011000d5007500c400c5c0ea81c24148031090303101380035a0919148000081c1e041c82e02c00000c01c10110300824802c030070410424181d40048030702600c0e1208100041c0c50f080500c41c5c00200484400e0f5259942e440d00b00c540c10301c414030054010b00306404140c580080740c2c110f18078207a03250315141443c40c8180011680c10134450b824040917a6072900400006030b50400d0510740003241d10001c81d250f10b00303a0101d2840d90084e88010300507035441d420041400d50007036030b40003000d032100c000d07090051402000030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 396788839 1250 396787589 396787609
    0x191406010e0409050f010f021e0301060c03030b0d020a03030801090e0601080a170d0f020301030209064905060108011b020c04020a050d0e0109030f0306030507121403030c03100f05 79
    0xd004a0f65034056609001c0104503440d00c20403480020710810b00388458001c081d400007446c031200d0500c5004080c200982c1142038a061340c240360750780007040300780b91405c80161803003442d03198000289140417000358461409401c040c2d406501e60820951608031b0300c108882d1a40010351950b080103005012406002c0313480c00c040e03030704105083c107083e1000d40e903021280714003155252000d2a1000b04001204550065412a4002c132007003243c6aa802d004c0c8280d40d8074a50307581010b40700c4c1c0a40035800748010090b03105050003284a0550607030881003040384030069604242d4036030780820010002882c09000f2682c00c140c40c01461520108103100295072900003c00d81ca00c17960f0042002d000d101d201c4c04c1a00c1c1210500c0c8420300c44610903041c50b134000e10310010709a0028090301240b44685000e8043c0504aa81c0072000302900361510640c07504100074500121480f038032400c4100489241000514060900b4034070315a900c2c10881008806181194481d01c40e1a10792079040182c1c0c2e0f04c1800d40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 396790089 1250 396788839 396788867
    0x3071b02040f0c0f0242010611120a05093105010305010e030f0d0209010507021c0b07080603030f0f120906070905010305070e060a0c0816030320040b0f1219140601 72
    0x110600791682c4c0944006171515115103015030b24680000203203076074000c8820038225181425903000c2081682800306500c03a000c08000415000c010b844a18280010ec001380e030000c1015084000d102040c4410410072034440d21301206844500510521100b03100301d00c03c03804240c00461410b90400400f031002d004090f410301d031403540412807410780c3c1d000c1ca00b12503104d540205030400d000c64005000101c102c071680161140d00312400002c640c2ca0141c4001c0340110001001036040140030403240d00158403043c2640100c1e901030214881c555405100e0500400c0e4610180c01d8525004a0007081a00030354001810507003840d060201c11a00250340950304a4241c03941e55440304003000c02e48050240790700003007002c400010045107003040246200a15442940e0070311040c21503507440800d40c0d0b144030599050b800300304400c020520004008051203000015442e04000c3c02c0c0c8250019030780d04959203108040c6a4423800d166890302d10808150500e0b0644940c000d05000000030444810580303c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 396791339 1250 396790089 396790153
    0xa05041404020108040507030807061e0501030c180906061d0a02030402060702010809160b1e040f1e0b040602010603060f200307030204170706110703030503071b02040f0c0f02 77
    0x101d030900c1b4060040c41d010756000208140e803500c0d42c0c03800d24024001c00840c044032200d14800f034040355041e03000300c031b040f20b404c040c46403011401c01840100c4220303800c0442254a5035442514009490b50045c08010002810b10740d4402490243c6816131080090114070010f10400c01c000040c0e40324002d5455a43c0c081c43c01001c56a00c07a0032107071070030151020a071000c2d910b41f14001503c200c3c1a005107281080f03148802005001039042d1314880c029801035141c14847c1d15010311120300051252840003104030200d03408a607a640600100364000e810150040c0d4480c81c05009000c428011507018241c010300408c01c00e00008064100312503046004060103100001041c0c110340f0a0701502c02901004031400d5240d051540203da40b80b0b014401c240100f00c581540581c001408a40c00003101d8041c2c803100d241d595210b10442c1e00c60b4040b04004580c10f680c0c190344000d62160300c6030100c0c20050050000c0e8500d100d21011f01561031460402046612000d4414480d10079446150900724403511 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 396792589 1250 396791339 396791341
    0x1e0321091f0e0108071b140604060c0201060b070c090b1f02070e0609060d020103091103012307020607020d18090e06060414010b07062309030301170d0e010e18010909020a05041404020108 82
    0x540501d0b0b803440c1f0b028840c19842004107100c180030300c80d40b018008001980080041e660759a800c113266004280e0042c1c0603030b5032007030100b040f413160790403e9502c148010585840482550440c4500340f074050031500060b8071a441c240704d2401d4491519070090001c49203015986880d01c0000c020041e003a00003810142c40d800440b00b0400031456052815600900030300c07251103409102400103144100c019100285440400c54448c000b1402d180241c2d2194054024071002480c1580c2200c0e000c9102200243c0d80c03000054042c24600c1408844a021409803900d401c0c020100030546140040c400c908110310001082001031010841d44510750240020406c40d02c000404c0d02214208071301140500301c81c104001904c2130110065060b60f1211004e100710b603034007210b215520104000c6e140042050800365000c190b008182c000943c0c10010010031850315a5003052407840b03801c2c0e00c807420769500d1744802c008526019201401410040d18200b010315092440070051280c06803000e0706002c0c0c400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 396793839 1250 396792589 396792593
    0xa060e030415111204090b090c09060a0c05070803030709060e0111280602190216050906010e0d060c0f300902030304150804021e0321091f0e0108071b 66
    0x12040b03030032202c56880985d844917542c80c412405081c141c040d452280b040c80000400038108242900c42081000c1d10081c1004c1e15101c00384c40c500c41c81001912140b08108001a0300101000258070480244d542c2141044c0750100c0642440d0183c0c0c052414498001d9070078451200002d103803a4014421610850360703001ca45004046011040c5c0c3c0581050300014841c0b15040304612030814201071942101e2803051381c0f6a01c0c0700f54a0b81401100d901003007540111b0120742c440c00520343c00203001031901034404199581c0d07100701c610b20070050340421403804100e4007031074219003410b1104516440a0042d80700301800c4c610f9230500a8241d01105542c1e0040005544041090303c3c060108003800c011070f1000000301400c03080c400c80f0124803c92001e0007000801d82c0341006c00c920140080c0081098015039080001520340281c0d00509000c0f0134000440b282c0d840030b4010312101c1e00345802e410340e1942007100500c02e04400e4085418410aa0140305405038410001c40c40300081140a2086413094 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 396795089 1250 396793839 396793843
    0xe031c0302090d0c090c181202090402040f0203100531020307031e050a06090e0309010e01020c10051b07050616060f020406051908090c010503040507170a060e03041511 74
    0x3149018000c4c02207403101041e02c245a9008020720462620f400b1180341542049400e09107650041e0341e05961003080358001420000c0c1c4060b0072510042c80401c030340644d128803c04a800c200c8140d000280f12050400071418045541500017081c1060310720200c210b0791a1094003072115482480c504d80c00800243c2d001c0c030a510412112500c00b4501088030040301002e070150005442004460f840c084000030912079a11503821482c2900010310308002015005592051100100c24154021407007100002e13074a541880000382060b031640b50701d03040c1c043c0400250b6000072455088a80c44042c013403040da6503040a854070140000e0b20344140e04072a1510314080d000c018400c104071030003c40d0120300c05400202501083c1c00c003483e40c000300304000a003103425183c191906d03c9950000742003413005510500041d54054054011181000e0755011452907032407136a00d09031070540220049a08006850140109240041c00110700381390400f05940c1c0403800b407010150074400803020a81c011401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 396796339 1250 396795089 396795109
    0x1503030e0a2d0807120210110706031a0607030e1005192007030308060105070219080a0201080901061a1c0f0b040e0105010f030204050c041206020a0e031c030209 71
    0x60105200010705802c1a405040c020910140d803481500c600201d0b2910000032010116140b015100e04103240c0380c2c0074010303000b514541c0c9104010640c000792195480401c944070007003405950018101040e00d01a05c000c0300b201035990b00c5117130204501400300b64410840444400101d032501d1342d0342d090341130070785003807140c01141c1e08048606440e2020064002c011907910212000c05444071101843c01541c0302d4000307001c014042900c000105040c1e5224034040d01c1c05070300c050000e00d5440569000c0591900990340230390b90551002d00b0000441d41e01030f00d40b98000c90800001d00006007014419400c840c05948a84015200071850300158606000144484080a0001c0000781040308003000600800b03008207024500700140382003500b0051003014101d800e00c0d2200c0110700e0660703003040040c000292801454201c20b10000c00d8507095aa00034850303d100d05001662020340c2000039050141003a0b0b00c41c8a900301c0100302d2002c001c0d910781d042d070a81240c80e0041c0d40305400000110005c075 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 396797589 1250 396796339 396796349
    0x50108070b0a0c0f0f03081612020a030605040203040c0f0807140f04090b090a050d1403040f26091003020301030b0f0414030c0304080106050303030118050403020102210a0507031503030e0a 83
    0x103480e050b11040c042013031240342d503107400303980c0c1c00925940b2101c1800c0310322300b9904280d0000c0c05d00d0b5900094005168040c00c284036040c0741c042682513565001070b0903604203980c15552800c10650030018880503442d04c4c0700034030b5401e01505140d0718207400c6500b10310384840520b0250500404003403a9a03a5035200c1c8018903072042c4080c0c624205080004d80d146105501200e00f0302c0381c48811540313640079401d60b0400341207100e855480d59540d41da0f5484084a1803030b0885052110001501d1810f110400501c5402ca0100c403654a404030b80781040b09801009201d00140340c410801803003c201035001d115404902c1f0341419807241c4403071604e140c003030009440103000703070202160107186004044000c0080300c3c0030790000d01440e925041010b4403072200f803260802e00c0b490404202044000354104e103900c58006e0000600b000621900c143c400308483d04083c442101c0751040000200c6a0302c210b41d0420100c0c83c0401c5280503041950180c40090301020341032284661b0291f070704c0e50b504030074000034103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 396798839 1250 396797589 396797603
    0x50402061b010b2e1b0506010e091b0915031002160b1b0715020d020403120305070309200a09020a0822030c1709040603030801080d03050108070b0a0c 66
    0x105401c2d000b8005084028498100f94079003040e00c5428190701316104100a040f4201181c107084240c070002c0d040c90000250300c0c92440030a0200e0000e105c0d4a00030700c0c4181822a10f49043c071000390401c10300d000c5075050210402e00001d05030311040740442c0c0c84040245110f04200c000d100003813625183d1035642c003009000207024100103141c610803c060500c1500034081c82e80b40d81c601443d40d0032641d0f101a585000030320854010078080d14207041020321503407005252801d0815107405a0380306410a07540803042080040700745515100d00756028403180b0301005040d6266540e20015045102954401c0d000540722a6136070340d44e100c0d407a008209e415801c564488001102910503401210004201205254060601503041d001900c60540c10342c0c80f52002019035030340d80c280c12004800c94a44031801c0c010004071362980e109010145002e5207555030b40c3d6160007651442c1201c0d04418408040c206001009041800070b080c00541e04030021554a41200f2034044540386000080074102c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 396800089 1250 396798839 396798877
    0x20a0509030f0d03063c08390120030d02041815030b0c03040f0f060f0f11091002010209060f0301051809030a0c02030712060b0f040603020603070305040206 69
    0x184900203411060300300f241d00c2c1401400c0e40d40340131002c46020300750303065500318440c5d035000306105d50320844407468000702c0b42d0b02c034420b82c035080c03024500311501001184108000054000200e4441054481d21080e04031750156280d06500003440d41c1c0d9481200281d84a2440748900c0c891014400e540c0303080f907095021500d45a403031402030080326907071200041580c64098140d0400e000741c8984000e698210341c003143c49032158542000c25901c02402600d4010400c3c1c000070000d0b10008411075014000c01d030120b50302c0441b01d05001160740511144280c0ca242a0074100c0d03e6034000d099402c8175000310b9101040503291070003030740603200301c942040d400b0070001118546e4401040c0694180c9006803000940c0c098921405400203109503485912680180540310905101d07030480440300348090f003078804241e5a070fa8400074400004004449240e00c82245245078104103081164509048400344074003895038012401c82d10024100b02d0816490345c00043c1951a024225000ca006903200304800c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 396801339 1250 396800089 396800113
    0xa0b0a08150f0303030f040f0605090c0907090510050d020d240503070b07060c02070902130608090a0c060f0504050d3203030c07030e031c081810020a050903 69
    0x45101141c030881d4444040110600a041c42c856100300304401900071172854503009040300c0520f200800c112910710803a1510070018a0b02c0c0642402400340100509001c031540003082285603004155104115650800b00000e90b50290b040f02d544526081066641070746904c1000644500240c0703076042402e1035960145804a1107608a4040101600340c0a80d900c2e03c08241e20340c20641f00c0d0b0328039001c0a011038004202607038050039442c04640103ca2046954074240426600501404060462000300412126401c004000c1d40290a0800f90400100c1070b0740300964207810740288410028010b0080035168002d004640180000030400ca070f5010b10340c640341491482043e20a140303418212002400084015004081c00070840c0142d402d40e501c00c94500d0741d031742041509604011038840b81c00ca445e1001e000c2d9654403200000b0380c000e1494582806010f02a000d4803800340051015658050308001142d400c4043c2241340c030160f0f030741c0b04200c01201d0501580131450b40c580034004c40081 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 396802589 1250 396801339 396801347
    0x30f080909070e030a02011209020405070806030705010c05060403082208250c0b0307091701060f0501050a020c010311070b10060f02010c020304181407030504030305151e0a0b0a 78
    0xe500508072003100403075903604022075a8454500308a07070158001c07102c032801507000c0d001c8807080c0c0100382c1d80001d0801c11500001c0580340d00783c2e424000310b0300e000f007408401d0400380b101c43d010701030a081a0240320440d030342c1d06565107801071010301041100c0011034080c2c0400f240220070584641c14010500c58030f8206a4101d6000564469254102011840782d00c030ae007082c01d40180303401065018131640703408210003c0d6807000b0115001c0181c401d0300440c0c1030042c0c540543c40380d43e403400005802d90601d0542c446d00b1480d50403680c1071001c2444070030007280c0d00203569205080c00b0b00e00440d100000707485506490183c004001c0c2658100c400300300881e07050383c0100089030320655904c1c401804100099080f6060b00d803082c401600100b0041c4440000c032903042d400113800c0c0c840000c10a0401c0400c0500e49801d0b5035000000e51a203041c4820301d6494050580c1008554440e035145003c104000388400f003024414002039400a640024513070344803a6502c00401001c02d0f0340e80d40d4041400020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 396803839 1250 396802589 396802597
    0x10f1403190b060d0f061703120901020f0403050c041a060d1505041109040b060f0406030b03030c07060801080d18092c0f06010b04141201021303030804060f1a1207030f08 75
    0x711780385007085c009003a48164000880f01d01d1550065441e1032418041461a210002c202034a190340810801750b440c16020000c1c4011401131000c3d2070503400d154200820348032850115440c03030403282c4c016202942d4003030454008101d480340000343c240403940100c40044c0c04d40c3c40380750301038030340f040103011300030144000c00d281c0c4c41c122000c00040346260200aa43d000e0341141c0c02640c0b00900c0140071180c0170303038800e4184060017802c407402c12185132061443e003006504450000781c01c40004000c65001041104c0d2145458280484004202c0c0c03005510300046204481213940c45080558844052030200b000224001061101150a1040c401c0d6151224148542c55104a0000081e405030003c191801d0721032804004202c1c1c0828010007980044000d02410a55400c02c041d651000703103040e942c0000d42c4a911280081d15150804208454000d01b801c0050b60401402c425880701d007690030041821b04072940c80050900004092a240054100405400030410440305004605000e4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 396805089 1250 396803839 396803861
    0xa0903021c110a0b0906090103060308030c13060306031e0809120309030f010923030c03041503060909030903120e04060e04060506030a0c03030e0117070e010f1403190b060d 76
    0x1a072110041c902c01d01c9207402e02449034000c0c0d500140001c2c071841c6408001043e81c1d020504d40401c06a440303071511801507109a4942ca00450006001d020070103034050600010312a0381010800ea0386103843c0c400c60403200d0901d80c0d04200611521804021400d020b542141402a00c03141d0017915032440c9640e41d504c2411340d1031081c4645103126884c510b05001c0c011020398800d5506000745c12000d402034888041040c500403074001400b00642c008001c10240000b0900c451600110b40320301c07800039048403140e4000c020858100a0440302180d00041440d040740e40c488009084005003500c2102c3c20b03031866a8031035220381008400202d10481c2070915015030b0041c14100507a4076042d08040c1c0c0c42c24003aa0007890b60079401000c0000c240030300d090b45d0034030740181088095003030003440c0c620100c8808c803103442c04200c91406001c103d59011032445111101c0342000d81d01c0601049000c0000e000083c25800301d0900004000c0407140c058000310251200035000a4a076000110050040c05400e406 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 396806339 1250 396805089 396805103
    0x40c080d0c0318030809040506010e090a0c0f0f021e0304180b0a050d02100f02240718140d0203030c062e05010503040809300f0c030c01050a0903021c 66
    0x1503d420640380d0200715048942c0090303070500d46402c8206000141c00000c01d814180018180681d20f280c54802c803507803140a0b82e01000415941c602e0010f8007403400310031840200407003000c0740003516400184110141d07000d03000ca0304802e00c0e81044a0b15510568010500c0241100091103002036076412504200000b01c450b00365084e201c0b418000780084400010354800003242c3c0e402e14590049801c0440c650b80751046d01e50031f0880014000300904002d00c100e00303c40900f810015001c0d8410041c007001000c1e03e5040d48c106280074030f072401d0301074404c4202c0c0c070400041036072400315942041180e2145881c082035961514250008000e81600544814004240b40900103269a9800400415114143c58484c210307180d984a000f0306800c2100c6054001d012040c2c80c40070b80b45010303451264402e0000400c418401101031650411240c5000c10741039910014102410b9075000c1031742c040020007032030f0080e00c4220146d0121803140300b5a2011790440d030654100740c03c680010f00900340650103448 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 396807589 1250 396806339 396806357
    0xf010c020c1e13090f150f0506060414010e090106030b030601060f050a0503061c080a0e010e0a2d080604030e01050306030a0b13080d02030703060509040b0a05040c080d0c03 76
    0x784514100d4400400b280c1c000344400104082c6004460f5030503a40e426007001454200a941300c002030020302006480d280d21144070b401c800400f030301441d000e01103a240280000c0c100395000c0369036070140e40a80f80c0c00c1644003400d022540d10421403290a40070040131351020396034600001d0014248012403d0107800f0303240021480500641d080c42440358555159031074640101c5080740d980d003020b006242d0084034117100c08021302484154039071081c09010201e545403074910b8058900c00148e000b20341444850390f00440c2c13640d16103419100315802011000380b20b460000700540c032500010301000c01c0100d0303000040380b03200c0d0000d02184958481c0e21030081004078940152291701040724401e5069112010340f600141c03189002940016005d110411610566507581c0e05540000812601c80b613404000c03c0700440e0706000f040014030055509020070300300b80d10740094803c00101100740352074445000c5020072080910790030003042511b0031b803440004a0240201040c2020304241c000583c891 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 396808839 1250 396807589 396807613
    0x7050d090b2712090a0506070302011b0c0b012102060703030606090b12070311040f120c09110d0207081201080a1703090a11060f031305011a0f1c050f010c02 69
    0x400c44880c60001040201082c1c8107210b100c0a43c0c0d80016003180c0c102541140005050711640040c05013513120350008202c00346426250302010003515052010811800c5000001c01c880401c581c0c15111941800d4410061000d4808013000c2c0f8024000e4100f21300061001c141039141e88444103031a582d558900015079116800e500c64010f841140c030060003000007007026980258040c14440b07101070101420540d44070070504e0300760150303031240c14021242049a01001a001c2c0500090078103501e040040d07941c0e103040901c25002d01900d0900d6250b0010b241000e11030350300240e6001043d041d40549040d80c64040ea6611024800d2040310a105c440c4401414625103000380c0b03124483c164000c10b1040ca007511100d05800305894250340205003080b20445e241e2140780218072070403000740b040608040c240380650840306c01540404e0301d02d50030001a10280c0d108054420020003c81d6642070312680b1450040c086042010014000d11070b13612500740808064228146c07032482a0240d132400000c40d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 396810089 1250 396808839 396808891
    0x80c07050603040c060e1f050408010e0f032a0703030309110103060501140d09060e07080d0504050a090518070611102304031101020c031c150e07050d090b 68
    0x603503000b401101c01a900f0300c800b40c4030f0031b400002c1c894000c150a080034000c0a0181180444101e080c0000e44001400e000303203030090003420100803200c5c0040c1038800d500610681c42e8041c0113501e00c1000041003001800c041c02c0401c0d61000329840090312181652031401030f006040403a0111100c00844100c074483d580039114007001c0391010b03101d08036141d0700b0010b1610142d10814010341c0c01c0c0d5071100341d0070214416100c0c50981e10016030040c01d103a802c1045551030500c40c9003150741000720030003050140d42c071140b02c0d00c400c41701c1554010407651a0549403c20a0701811810482c503c00e1010010b12580d0207100300e803103602c0346410384d80420762002c3c0c21003e680c0c0e5040e4a030b07a400074042503c3d0500740d0700000180e00a000e4503000d98075210450500c2c0c00d90b40061030664607607002040300159184007551150450940250421401504000c0811a403101d031007000c400381c2d10040000c038010f00540031500c0e01c02c0c1c1494200070440c03051405050b030320b0060328a00061901038820350001c08072 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 396811339 1250 396810089 396810091
    0x303070f0302070f02010e0112020c0115120804050405060411030721060b03040f051911040c0503060f0409050127120c0f080c15090a050c0a060c0b06040216080c07050603 75
    0xa04c181c8400361560010341d2000444040e40d41009185041d51020500500c051b0030310340381400002c10121121401d03004c03040b030f80c0e802445d140e0010400c1c050001c1e406108840450b00140c501003040d030758020026000300507140c102202c080c000000c100c176007680100104081d110324038508082c80304460f2264111589400313592080380b03003000800e0200e40c0e42c9000c2819603214400315804464214000c841042154000f00c0c2d401c4100e041d405000e01e028013508401c8038a600d05a419483e20800240c80c450301900d4860046a4641090040c001e00b0341000300b10030656648944440800d001d2014506074044058400d20329004245040b1807041d590b00203010f41088601180f009280c072120901d51006034000c0561164000c00180141c020907142d2294003a200a01000b83d030301d042150800d5061091203214958940042c440141c000c144050555080146581c1e0303030f512000850000e10442c1003941c04c500354a1507040801c443c21000740360304c103201016111540ea4860900c626800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 396812589 1250 396811339 396811343
    0x180609051315051005030a0e06430c02030f01180219050310020a120e03041208090411071b051e21010b01090b0408071e15020303070f030207 62
    0x141e080e8810304408002d0304090a10948140041d010759034400003e03803040d40c9482c0210200c1c44c00320800c00c0c651420701c1038003448004000500080c2c9020000c281483c105601d0b040b1210841c21991022400400d04252600e0750701051400302d401c040201509100d02c49004a20038400c2100607003200300c1c10302940c0e410f10700300c0d046070750103181550800c10711a100f004100c0c24a11182000900365030100140055110300caa8010380da0100c00300000d05c0310644008824165003858260b94150302c00100701e50403074074401244510104a450300b50f040c2d01c00c4400095005062000c441d400d1402c10b002030041c0351140302c1e86940c1c0600340361240030b0036404e403281e10340c84200c6402000c0c4003200015102c2031444003d141c01140040c0c0f500801c0e0548407981a18280d039550800d000302540c10091120150000342840344c28540b60a595698500d00c5000341035200800b407154207a8640f41855040103007620319010080400c200d84004c0da00d8000710365000001d0320303040b0b08200007806807084a03140e50f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 396813839 1250 396812589 396812599
    0xc061e060f1e0905071b151a0a031b08010e0d17010b030a0903050d0c031d010b030309040f0605060309010c03150302130e10020403050f06010806101a0f0a18060905 72
    0x5407610f0004001010000c0142c07007070003101141414880749240d88007203501c2c825605e06900051094030030301100d81c9a00c0d100044940c00c40e1075009542c5a140302d0007266400884078480b42d40d4040d6201d003030291540400150343c2402c82c0000080f1010071141c21414490751814841050452107140140e02849000c55100301040416841c0e1407941004038018001d090440c40c00d82c1400012045038021010000000d40d1810381e68120441c041c40700c1c00000c1440000d0000248c001c0010f6203d1150405952113544d803003e440ca4098010340102d0300801004000701e440e850518030b0180603024103010300c0006890200c138144440e4081205a0a4940140070a0302501c18125108002c004007005024640f04002a19510718024001000910300c1038000e403911503260720540703241500c180c010040d95081a010003d80043d165032940840300082c090003a00140841c1d11030b028800c1342528965400c000580b42e46060708a842d03080030a1310a0310a0b0b91881e9942412070301c480f86030244503442 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 396815089 1250 396813839 396813899
    0x6040b01060c1a0109020a1403060a0939080604090c0306090501060b0309150c031b160210030911180705090105040f0608060307060507050d0c061e060f 67
    0x1c1c51081c8602100030f480344407200c02900982c005031a0b2480242e0110580d41d40000d07041c110140d211a605841811120b4101e00b142400000103203103440034007901c1c007030325510803010714480c0000d0f500c03c1240b15001004800b030303045080000c1d19510403403004000710310760801003101410540300c2c40342015008a034618945040d42d560754041c1401c0c080541d455074130b4400c0800c0d11005d180043d4002c0046e074008040142c3c6000e1120780301c500c004c0000c2c0310048240101b103041403c80070115034900030f08600c541d6404503140060701e0322194450207504075407071500c00c03451650154455182e26020300e0105004e00225070410002c0c110402c0e00005000240300030444040c01400070b004011030504041c0c0c2001e031104185032a100603a4400c0c40000e0492007400002d05003403200b8800361602e45450f91600000303448290350740c0d02c103240ca2400c100e01c2d01808000c1c0041e0f030b84401c041003080e02425041d651001d603071070050410303401000741e2100c150f2800148850207611104003071481c0344450340d407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 396816339 1250 396815089 396815099
    0x601061b02060d1d01110414010f140a12050c070f030f170f0f0705040605070b1b0c0703140102182803050d0207060c0206070204110405040e0102190206040b01 70
    0x1100100d24100d812a80030702020052400c0b0703001e2141e080e96801e42c9442da419600103a142542d0703034003110b114042800c200c184080d4500ea00040c140c1442805c108c041040d041008a54100103000d2581100b140460002041640300c0015900d0360101d180500043c0c580305842d02c018402e040c0001c04004101c5503030000a8043c1c448550040a90b0600340c10815041803580c008a40407a081000003403038104000300c102444003020b070414160716140382045d0400401505900c9001c201800801c030b03140010750700c00b0a01c8180204912598003030f944a84091003078070f0f65103441f80000c5a003190720152012030800d0520a6409004c440d440c5203c10002c170f041440034603004a40208040150040711000c4140b50284080040d17218100070410380079109802801d001654020f4020440c09070a41c2c0d001d030391080d0035a00102d07011100003517034503400070b94450244a55440643c0007814002180f02d1000198081c10b1508407998140386100d00848080343c540104a0740245045418001404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 396817589 1250 396816339 396816377
    0x2013260d093f020a0801060303020102030a180302070b0c12071b050f0a050603220503180607080334090513060803030c03040503160c05030c0316091808070b0105090108060106 77
    0x102d140098020a01541c8034017295082d80c00c7d680042e00580e4000042c0500b0140138031848442481c850303000400308400d5a80252a6010b0b13114512011a0105030141c007080107000310120121004502580c03150300b85400b00700d06107503090101160b61f01c50800646420840048402c0d9000200340701682030500c2d0811105401c05170146040004901c801c190803403400c8206440a8010b2b8011a202c001c0302d104083d5080b58051340314007030711051043c01e0001e103c0c00b0035a03821000103050150240030002d078810b00c0c60b00c1e4518901d29111080107501180350000241000e54006440003007004464520300340c242d88041c401c00c4901d03841000050340c02c0180c0d43c081d580140c841d81c1500d03c0e00c5203510f40c2e812414a0381d8419a0005600c0348108100c0c6420400d124400e01d042d40507104407202c801c00c0d5413401c0c00c075204420541c2c0d00c130030000c0340d01400030740700c2c2800c998801c0e45c3c59201d900c141007030071a101003402254012205000086982c81000030118101d54066480e102c042c201c13200030300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 396818839 1250 396817589 396817709
    0x706270e1801090f06050f0a110a030906140c03011e2904180506090702150f0709030b09161d040f080702132013260d09 53
    0x41c0040d540ea4552038005810a0310500285014030401305240c1070062604429140280c85142081e00e0070b40045480c00d405826101c4245640c10000f849040a0a244016000b09107035451031030b48401c1003040068401e8003840c161148023849501c880c111390b4074842c09903c103015010000e044030b9400d00204803210203070380c103102c0304490043c14581d0354401c07480032400815280ea5020b8503601081001e00b850400709600010320f00c020250003a4504000d0512040540495650a441000100881d00504d03607600190b40c004030281d920f1410300c42898a80c0d0b080c104519210100c03140c0000d800c0100c4c000403008880d541c1c016001c5480319a61a002c000440303008582d00300c020302002d00942d444101d500d003103c2d452000481c144c86901c640d4201d9402c9003c500180782404c0c06014a500031a00055054804413103a404101807251080b44001c18038814020725849140c1043d15142e40c89081d00044500013408000010011000e40c2100c01c8860f91007415905200014002001503117194 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 396820089 1250 396818839 396818881
    0x150c030510081207060c0513060914040b010519051603030b030d091d060406090e060a320406142d0408030c070f083007020d1404080706270e 62
    0x8910380200010340c8c2c804036a85611180101d08104802c00004040b80150140d4903821601040b9510329100042c6c924014254603c0ba1051401c2c41905058050012140300003900d48400301a219540ba008020f401d59500c222300034001c00d040c2c40300301030203041080282d41d180010810400d16202e801e0070042c3e8002c0c400b03903125464060003d0000003502c141c2c0c002d8400340b80504007501d0b01190384819909030102e05c01d050200100c1010480038035502032641d501d401043c2098688550514001400c4100400d03510100c2040901031002000a00640a40e2111031101132508400c01001038002c42150060100b01e420400603c1c0f20316100c0040c90000c4c410b010610480c18035803100300c1c00b50000381c030744000e101111109605000007504400c402045849080e402480d0040b0001d4482050074450002d100204070313005004481942174601405601d021116001d80d0b502c401000202852600440c80c00d074407000f103500b1280b4200d60700690b0310310f8195481c81e03282c000420a0584800075a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 396821339 1250 396820089 396820097
    0x114180c060a1710030f060504140f0d0309030905130204060215070c020d0302030720011209020604030816080a0302090f120607050306030703150e010b061e07150c030510081207060c 80
    0xb0000035031b040045e5020b80d0040000240e0380c641890151250081c0d6040b148040e0b014078a4800400800900040004c19a00d030114140c501380c41c00751790110181d00400c1c0d02c805c20a41c00040b455031a805030044035100d908946000d44201024020138005643c01720004008145e01c10142c14030038000f4801611038811a4038100326511905003410030421010804c0080c458061810340e0700c5881984c0c0061802000c00070010b8a0303001071f4040c4105c1c40010a8504089990580304100d000c40718115074200c0d04d5940c0d51142e01900030700950185005a10079050300c0c105480d181070034583c11344103842600003402c183d1504d02094442c0c1e040204910340c144900d000110002c0c008034085403521217004c0c00418142c0180d04514217580b10070a0301da010b000d050040c01b40c0c80c1c010002c0104c0c0042202c440a90710180d600300614100501c05001e4409810142400b0020758180d100e14032810320040305c4064952108642615a41da016514400700001c0c8421070201e96958000d004c0520103040c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 396822589 1250 396821339 396821371
    0x15060c0309150c050319080c0c0a1403042c0f190902030c040e06040b06121b0307050424080102030108030703030209060903011806110412030c03020114180c060a17 72
    0x56880c0c03555010380c2202c00b00201d100e03100d21126800c4000540c108c4d03071441c9250f0800144041081d92030707010388070180401d110120b00c0e135190300342801285e028204541503010130200e901481141c4d08100f0065030300d01c44070700300011012400030401c140a03240030110070801c1242000350030f0107000d0410043e81c2c0f601500280408665842c403a01e031003100e035007021304100e00d020b081100041d0300040c101402401072030400c1030750050200c0c032601c00c480241a000b07101e82e544000b2a1804005820003900240f42c20810b000d00380c3c20007203a1142c0e003a40540120305a07120007126091303000a01c2286032981c018000d00740080d00980182640d4400500340034185100240000d013074890700031881c1921801070aa00c000d0280901030003c041c44a0b4081625080c030300010b0401c800030660000d002c0090800301c040c100740c800c0d0806900c0300003d20700180b040c1008500d00c15080da2800a1240d140b1375441640702900b00ba20542e059110f541d2949040803a001c43d44e90502d0100511969100c90515 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 396823839 1250 396822589 396822593
    0x807080402280b030a0c0909110403020114040308070c05031009021c02040209180603062a0708070516050a06020f0604020d0c080304031b08011a040c0e0a0915060c0309150c 76
    0xb00518070800b90140042090302010401030407608423500100a01c500b095020791515182608450071241e0a20342001c265410800c3c2070454001c41d0001050f00c000010071106009850840000341c820071001e450b103035a121001202210254440250031444c0c080700d021040340c1c802c402504a500180003d85001c881400064500c540c85804030781d449806030510070725040400066500080d181c202072082c1e0400c0591030410090051403440004d000500d01c2c0c06c101640068411740da601c40c040300c05079081d400144182da921070041c140104140440040c0041c03000500b0610700503c0e0001e020030740c4540d0240300005190302c4056030b0010b02803100060364182080244010350241407605141040707148242c1402d041640013080d180c0c14074081030003601c0f922001c603c030400201c40000780b802141c1400d80d55408420700450340b0620ba100001528203954002c0c8003003541a090714456180c4820080c0c8040c40c0d021406400030f11f6905051041013840c0c0c284030741030056418108614030300d82e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 396825089 1250 396823839 396823859
    0x100611190c06170f060d020d0b04111203040b040e1b040803040e10031e05190311061e150328110301050c0708090f030d050a080708040228 61
    0x500c0c03048a6022040c00d003004440d0340a14100401194118030f0400e41c28519821140e00d03002801c40b600c6000c0c115980400c40d43c9544400c1c5555600c80f065541c40d14041c2001d614500408810354000d400c401c0c0c218440e4140403040364241e4001c80d0105091908242404100308402041e40004d010091006019070b400f10b400742004080302802582d4850421070720002801c4c015107003201d0303c0c1d2007020520025002c0000220400f0350002c2950f00404541042d600e00204440080c044400907004182411343c0594030403110700303101d812945c40d44c40e11410452200c0d65001c0180703444100300085044050441e2142c240302c00c0040881d0200b008006800c4410303040703515506507402c02d0342000010410100c203140c408860450080049180600c00030102d8410202c000700400c80006c1c070707400071b40d69070f503507003444080c0c0a0200d590010240744043d04e564000624580450500400200398078415040700d84035540c040d01c9241c00f0440000ca6204a01c3c9010340682001d0340164041758003400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 396826339 1250 396825089 396825133
    0x6070b090d020d260a0b04060f140307080d050703090806010906150f0522031a0403080a0504051e01021b030a090b0403080313080f0307091a03100611 66
    0x204010300a0380001440207454005101c07581000d0000f0035203045107514140d134464540040030040031489941c0c942040303000740304034031840b544179140c1080441c100c140c0c1d08000050396400c20701d501c19002000c2c2050307034505441c82002c031164001032002840d10312032405841000e200f03017814684180c8402c50b20f81480e03000d030032000305c10399128070070000744408071070b0900d0710421400d1100c1d076003c136881b00820034030071070740c0d4100c19504850340003205642c0760004800940d00b00d80500c0b81074400c8500307042e0b070110a0720300340e0002e115600441c504088a00c1003902465000d80201003d03120300d50381d01c44030002a01200340c5558244800c0d445034420700710447c40b450600001e1350381e8094844000d13140901c16040384014260a000600c00101480c0480c1c1d00310350b0011800c2e001d0085460010b41c01d02c00c0380540440b107040030003444042074000c1003000c00d584441e21300041c7e0007070109100140380002c41e080a07a0016400d8200651402150060440a83c4009480910504000002603440 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 396827589 1250 396826339 396826351
    0x12030215010e0f130b0f100e0405010510080d0806040f0e15060a090e1b06040302030a15050601050c1b19260a02010c030f02071805041a090a1106070b 66
    0x10003041150041c01c02d11550080c4462910036030420b0b00d41765280d09040003401d00118941e400d000c54241140b0300f07228002000030f841c00411518051030f01c18081d180035250302504031541d0002003804200800c449122040960f2070b4a00303036840c48108000b03080910380c0c0a01c02c0355a251800904d540600000c4040e0742e954400e501c07941050b20500440c1181075218041880c50a404000302c410041078107090443c0607052450b00c1009000080d0640c071469100a502d403045038120010070960b40d04844900301000c0c020071007565040c0c0103465030701c03c208042d80760fa04101030981651003101402a05040c0141000183c0e0300c0510040800c0411a0029401d0b20754018a950943c509000d9640f0301004480103405140d4007540046d04100c4098802024880c041c160100e8044c0308103c000000c1220047c540d450b16041140b041c002e00c1c00755415241c017880115210f0401d04419492401001110300a01154189c0d81ba001075100070300b01103641c86041000301802203441c4c010b9050040d4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 396828839 1250 396827589 396827609
    0x13020a0311071101140306031e0106171c030209010f050c011401180f09021518041b022406040b010e09150a080606180c1b1c090f1203021501 62
    0x80c0343c140000d4291740c10803440c01d902079000c20402145403000708100304954940340350305400e04a800d004501609c284d81200200c5103061050b441c200c60000354050f501810103003191011448010704400340d100c1d40c0c1700c0501051030081144c00e103e1081e8018011543d900c400000c4541c201c3c014841c0000c001e034411840594006c8400c100c5c1f81413481340006c155a110b100b00800c0d100341e40841c014161507044001c00d00303004141130741075030b01510b19690401c5005204108916458208844075070881c1e141da40188600e00c0e212000ca0b6054035038404401130303501000ca4680d69042000040c00550400c541000744c08218599980c45002600307005144009806826911134402d0008082c002c1d40111502e62282003401010380f83c8805100c0110100d03055a190340d039840c00494418400c03500c0441c0c004980e0034540b007001034007040b0700913000d0b0380018443c100d030710345641101c4d8401e0701c1c040d5500480d105101045441d101e01007410405d44a40191203004080c0156114682c8003640309500c04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 396830089 1250 396828839 396828863
    0x11205010b09120f1903050d060e100b031009020c0111070f050f0319050d0b030604050a0b360a0c08010204030c0b0a022d010e010f0f0b13020a031107 66
    0xb900d00071003030021800c4000b0050801c420760700c0c01d03e540c5070a10317104101c02c00d4110038100189440352084851a040158003840147d542d000e8005d08900102c503051ba0980c82e0340000309108007100205ea004003e5040081c01c12801d2002e03201c000c0d4045602641c01d9980e4030b54002040078850042c1501c0c80c010603034084620b459040490411401c81180d0007190810440d10301e8005166046400255a03403802d2900c0d410410034110040c81441c410a52607c602020002000000603210321a144242404c0c001c64407103e001210a000c4281c0051002c00000503080d060908126003c0c1c1041c414412030b06100b5041e02c0c0d6000c1c0000320340007100030740d4002030140140600400c07541c0042c80b000c6200c0d85040d0801c0d0f0002e4071000c03402c80c014054040000501800c08050301090a04c5000030b0007000f584081c614003c0c000c1089603203008180c2e013000269464a0000e11484c1d00c40340c002390007800e1070142c0070035060003944079881d82003e1603030f02d100d62204149544040c010580c8034280d00824 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 396831339 1250 396830089 396830107
    0x60d1208092103060a0902030c070339031812080c0c090c04140105040e0103020405180105070203070c0e0c04060809160303050c060a06030c0501050702210d09090c1d011205010b 78
    0x26640c0175811076152680108140001080c00c1c0084034022074140c070b040c411364912010100716510007400e004e28024850081030b040d03241c5c015125024640300392603005c541e02428010010010f00e5100c1c5208004003540340c200422107000003800484c200000396030030340c86401e00042c2007182c1516050500c10000c101803002d240040c1035440100300c2420304504007443e00c0038141c00310105000007805143c03101d0204022031100190a1a1210400024802c40c68002c0c0000d650343c0062400355411086181c00240700021700d6000c0d8010342920310110f19003400d02506540203d00607090389124801d035122541d45801c0b0100c1a00514885d0b80d41c19a1000400600740c44c0450180c0034140c40b07480e11204100181000078102c046400030309000f03440c0c61082c00001c40c0d40b92481e80030040360b5941d804c0103d08a00102e403109480125450f002d400a8032818048100d8a50f01503c80210b00d031520350b02108801ca6405503000341051401c80d910510302c00d401d5080e2102039004000b04840401c080807 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 396832589 1250 396831339 396831349
    0x30215030117150403050c030d0518010b010912060b120709060303030f0c020a03030e01020d060b070302070b0a0c030e1c05010c09080d02060103171308070608060d120809210306 78
    0x350000c04100911118000200720f180300080500018144840002c1e03c400c4400b052007039a040761b001142c04c1041c0e281144494403000c980601c000c01c107501c1c043c0c3d03101c003a60007250700740280c075845044d400806500c2c1d6541d01c020159203d60b5070740081400d04106d640c41c0304101410180c09a6080410380e24918603001e001d175480305a00031049414412074944080d4001020f4500c0d0b5094075002c5003c0454404c0c042c024496000a10401030170500c01160440390039005211162107942260b03001c0795500b0322207800f4003840303c0c0d50002030303d400c50740c10220748160101c65107148018640b00b44000700b036400e00c050b081705140031905c594480c190600000d4000d61a1001080c2c2e5102500b6544e590b010001d45950301408001d000c1101c01c07648980c00004442aa514482c003110f1203101261298501c595500b190711071030380060407200004085003010000c0011140d070043c0450342d004185101520001c40080030b040c0e0510682c0c500e400c0c800c0032400c1d03500e0364480307464a0a650381800d10901c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 396833839 1250 396832589 396832619
    0x10b0405070c02013e0c030f031c0207030509041b0311031e09010f060b0d1a061b0a05010f140a14070c0501090b01060503070e090c031506040302150301 67
    0x4003070102819052001d40d8100c1043c03511201d40015000c40380050800c0c00f178084200511500c1c21005e03d00e12140012000203101d0b0001504904a68040340d212280761f1b504d1080102c09807040b9607040440b410040c10383c0140c01c1c0e03907220b410071600f040c179554041021a0f560044000c0340742e41c07020345088015054815403146070001c0940900d1854440740c0e409080c40500a000e40c02948603000074803502d000e60100200d606a09424492241d4801b4002103d400441d40350720990f25121a500b0700e03d070007030700641068402614a6081100e0020140b11a480301448115540641840d510000d5028403417513600001c10100007a18002041404110300c0b0300820050085140070300d8540c943c207144190a41c403491030702c0c0000181c04a0300c1d125014040c104001040300307aa80c0008100b10b6041409144601c0312030303480d445240c1c088001c000c240b050035520402000383c1000842d0001e00c10207950b00a03900301030289450b0075900d80c00f191727000b41c0a030710411810364040014403035180340002e04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 396835089 1250 396833839 396833851
    0x50a0309050909122203021215010603021c090f0c0305030d0b0303070b0402190f03210e0a0510090e09030c0606010f020d0e0109150c120302180d0203010209030a0302010b0405 77
    0x3d00c2000c103108030f05192071080e0b00304c454500011004840c2175040528958015690182039031405690301000741e590303100445441c880304800d1000208000c2c0c840e00c06c2d203410207252048a01c480c103a444041c0010300142c2030a9814a0b50401d5090214040e000750070000c40c07180703000b9a80c2d1641e03900c82408445884000381c1c42508104034000104074a1041e0300c2e0841d404540b1303070f00c45c005404e0040c01c13000929406a00360300301d041030000510041c080b0301504080104d10206401500304002c580c0d29281c415001d074000228a414421403d00c216030001c2070541d03040100440da183c0d40d40d01420340c011280103615910001d041c0344d49403814841d064000c3c034282010500b0007120f18000c0d403507142d920405020040002407003402d0741c0c4114083c1d001840c20408043c246203400c0c900519054001c0b000359036a4840e08815090b843c402e200f2140400c1d120f06c0c4035219804240204062041e4410059074959000e0003070550030740e41488101c030054843d400005540e001e44043c0401c1e00c0300140b80c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 396836339 1250 396835089 396835093
    0xe030406091511060406060807050a0803031501230423030304030f02010c0804140306071e05090409020405010b0720060406050a020f06011202011706011b0f050a0309050909 76
    0x104005250300005400e0a4030000362103400e80c2c9400380c03021a5480701030f611200c0d5502c201c10610040c000a5800304050f42d40311030954010a4403082800f8460340c40f4410380203590700800000e210f0318062104d480720114145420110300d1610560705400b01042c2001a10071480002c2c10408001c4810f8414402c58000f603810412000241c0001e8030780c01140300103442d000c2100348046c00c6a02c52030009801c00c4c1e03c59042c0d40c9607516081d00140586002c10554060702c00c143c04244080e001e080807040f001a268010178440d001c0d080c08441039000380c40b8054009444416100c016588c07030040501800d6911950740c2c81d800b2904200441103502c505c0310242100c0c1200d003501c0c544406049405036110750030b0890f0342d2845298128030f045200200c41c0454041c030400801d4242c43c0c20580740b6070078002d0f80c0305610ba1090440241e41440d0680e4603d0206d0051600041050700500b401d0000c14002c94000c10301c4403c58541c1d0b41400c04100048000034044c0030240300d0361804003000340e000904580 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 396837589 1250 396836339 396836347
    0x1e0504120c03052a21030610020f0a050d09090204060203032221031401050f010f050403080313031b030e040e01110c1006170c040903031413060e03 65
    0x4640d4a08003003003024004121100c0390803070501d4007a50445001c41110380762245940000e48020080881e40d00202d103041c000c2e1400c60150041c0c0d045030200c0001880100ca00d90b449079420010317003a0300b030450141540103e6001d804858000c0c44010b00b080e000e90041c00c025a02c80000801d80d55007900105911071042c40180b01507a80001038a0340048040701044031001301f2042c00030704102040004041307040400340704551548281142c003a2145685090101c801c04180500844a0074043e403600080c84040500d03c0c0d620408010304000c00034245245002d17180d490300d82850f0700417642c48800b1030021150341c0070150b000141c0748070701d0003840c0030683d1001c10fa0b070002d04544401814502c41d58540d000402d00d03007804e6010f10305081c2941040d0380d40d141402c101b182c80d01101207184044038941800052021505154905e00160240203811028290b4007003000800314001c041c0c04050340e0f40304241074a2142580d482c0030744258140140c3c0d514040c032f40041070750060032800c0a00c1d00140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 396838839 1250 396837589 396837593
    0xc1a030f0106031a04020c151b0904050703110a020601150c08090409050c0a2c06030a0303051f0b0309060c040803090f1807050c0f010b130c020106030c091e0504 71
    0x40103a041d248a450041840000c1d2421340442416803500654041d2000400b00c1644000184025000b0032440780c513042a81c6481001caa80061203506001d680c01c10094031101d032400758007071640309030b1364140022928680d016000d4181c000b2925a400759014200620034810344184032456120a4a85103a41d080203541c0e80d610340c0200400305000700e40300e04104081220502412104540150140d0b0b0255070f074904034401140d044118103035404488910807189482c8401135482590301400802750500e9a80e4114020070000304076035018035813907a00006500c603a0f5034140040080096803512411324080c05802c00e94041d010b5518041d04020400c5180340120581e002103004458407541c2000817000714007800c0110041e4890078070081c5c10000c2d8a0381003006441c1c05041482111098400300803420f0032510307200004d9a00c0b480c0501c18038603c807507641020041d1001c602c00410455525581c110300c01c075044c5c00001c0402e8460100c518850401003142081d0000320400b841241826 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 396840089 1250 396838839 396838861
    0x6030b041e0c11030a031d0f0601230402030403030203010602060708040b15040204091b0f020102040602120904020c1b1816140c0d030204050f06031e090c030a0c1a03 73
    0xc00920700e600c0d921005800d107818010420a20000381250a1300d55414100c031005004000c40c00d00b000c106044155000380c00000041c04201c5c143d03401d00107000316400c00c840389106440d51600f42c0c08040c100c0003507404036100c50001c0c0d80030700d2282e14050f0b129410658040d040000040c0a1410002c0240400010070390364442c080e0030501c030303c0003120032040c140040703406480746810088000d81814090a21101c05496215040700640c0e40c0850380c00c44440d0072402d0744110300c112700060307201c12448014040c07801c0040c1611a40104018902038020318103e042100b20b20030b21100c1c2e007a0b103c001c1e41c94201022510700b1100280703d6200c07145010a00400a91400b04d5040e04110990811020f05101002181d0745042da0380111000a000b03003400502940c024051940500d45201b1020b0050a08805aa02880c3e400c00c1c08080301200601c85801c13800b004000341210b2042182400f1140c9050102d060300d10b000d0b41c0185c420754246001443e00300b07034220f221050741004008200301e0303d040c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 396841339 1250 396840089 396840131
    0x90c05011805060306030109061406180c03060603061c051006140d1b080f060912030105130906061a09040b06040503060c0706091a1005150f0903030409020f0406030b04 74
    0xb0484070070b130300d03500c0e82030100780144221741e0f0080c062803424504440c40c00d0000c40d064405c8500312072460901d411130300e44c040808070580f021000080c040c0042a16458841d010b56800f039070141c69083d030344681c0e02e603d4041080d495015101504205812039a003a140e028002c041c5c20188454400120b80c0c82c04555413040000005d81482c4554a404941025103005640180312840480e095610101440c40e16050186e50054140c4688129000c840503410b098a0481e80010f04840c20300f0101c503200401360451250031a02580c0d1114042400000002001c10388031420686c1510350240701c090200b1551081692881284103110800c1035550001e102c41e848048c0c408965118202860504060320594800400d0a1080300a08401c0220380850600c134035260f1003802d000381c2e682d20511030103a680b802011800300c02040454001001c3c0c5000300280c0c0e0003c0c0803680303800d5481c070061040340c0061002000c426030010307081010740e80c1405010320284040710104445441300d14410b4103010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 396842589 1250 396841339 396841349
    0x303051e07020706033603140a0509030708060103020f06070503160b06040f112a0706051e03060604090e0a0609120f1103070b10080a0303090c050118 66
    0x619100025201022031440c448444821240d0521504003400082d48910309030081e8070002e403a00c0740d02c0c810040703501c00e80401500d00c0c101c80014080040713108580c125000d64186d0500452007840c140d04031000f07008208980d01c85d40d078251140e41060405041c1f0341a540111819400f0f28014405030345d400c403420a550320100c401e03a944c1d88651401900314096850b0002c0c100110b52000c10500c580111518401c0c03008850805c20640000300d801e080356560319008403200405d21404100755642c0c09514807110b00b82d03400c645107001080c038183c0381040c180c10040000c2c40104039100c0145003003000030b10722071014000714118904040426194004d0703114407c8541e0300c8001c1445250340c140501c500d0580c02500603c140d900c01c0c2442d04116003403080f10f60001b140b03c10b87e030002c039205170b5807030b0703461120180550301d4141103884080c200303400548071810728121800700081c544020040c01668034800d44010424200345e08014107405000d038801410310111f0042d000d44c08150302e2043d41592 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 396843839 1250 396842589 396842591
    0x20c21060a0c0908120a03050c030702060601030b0a0801051003051c0e220c030905280807170c01150905130312060b16050f0307230a060c0302031503190303 69
    0x34011800f10741c14202d950002c1241d01070b15510158a190607401401d5140c0251000c1c0070b16100c2c1d090802d280e210494201c1c00682140300820255032180d000142c888100902c100030030b030340310440c0900311031007900c0e5002064401e0a0800400200380945050071801c8405020380900c0000054882d00703501039041c0c880c0c1e1206020491101e40001152286583c50b07004002d04500c0724005001004550400e6450388160780303100940080314051241c1e800c251070b4007076500718600e40c0d8410003600000c0040380c1001e07003011100d16180356600a01403000b0298000b08001000a550007010f25090300035410751420b107004c00049401c031081c00080741c1e51510f03140703683e640b542e00c46200804668001c0200c0390000540e481244000d040c2501c0000e0290003a50003821110b803140d0365a2286940044c030161800c41040507204125035240f02c150789100613199520211b80d100700448040610030004207602206000c00e0100012908412510903002070a4901c02004008500030f90750400800701 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 396845089 1250 396843839 396843851
    0xb28020c030a0312062301021501060c030806120132010609150e060c01020a091202010c24051311090105150a0e03010603050c0312040e01151e020c21060a 68
    0x209003250300420040c040c40c000c01d44c1e082d6500a20800c6c3d084441e828074014454a00c1a01c02c41c0e4045401070304880705610b920311180c4e50340e1b03800d45151400070807141c0d229410125000a00e0028060001d490ac032004244143e11352404a5081001e024003003212950710f604018070203607411002d00000d403803202018224950240304100c1c0d0360340c3c0c0c0c4006c062300040c0200e00c510701d440341500503040e6400e264641680c0540c403854a6041160862000380c0045c00081214000c07a41c0740c140c1c480e80001101642500c1d002c1c0510707440c2070741d405850b207107103090104002d48180001070443d16904030040390b6000e040d525010010700c490f2182d01803003010780400a0482076250085a00d04000c2e00d01030002d002040d524100076071500c4840c245107000b070040c2c5c0400b144c10f0074401c04a500b80c994890f10110581d083c420880b20b46e0391101c54440074881c070740000644111107180700350001703516540141429420a41400600a08100c0100706e0100341a2000071034040443c445600c00c250702c00c00500b07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 396846339 1250 396845089 396845117
    0x60e0102191e0e0d1410050c09150c060414010b0901030b1803031b1812010b1314040f110d0b01210317100b28020c030a03 54
    0x920444040350540c46041c8841001c1c160400c0380d07001005424005164a614408419900400c100b048260f0148505091000169074160500e054602070b00c12259001e90a0100e00c0460b20240c45403250500d011454000d50300c4c2907a28111340240a01215040c103811001a0740c0d180c5000d00000c1c444030501c1c0c89044402425400281c1da0600200030f03140c0c0d541e403403c00c1c101070741c401da03900031840309150582509400e0000c11a40546c0d0003c0c0f043c0e40b081e94030019154590402c545a8116601200c020502c0c1d60302d502c1c042c1890b900c0000002282c0810030100f1901c41c1419400100050800300010030580ca44031200354031540041e003a811951036890024440e440014109520105400c1c0203424403c048040b203043c1c4203840c00246541400c6c0041e4041804c000c9170040020b1030300f0410501694a0341f00301a00405066601550303a5164800ca00e01d6030003807901070512408140000d49884001d2200d4007086e08280040c1c6002d940d0f2a000c030341c5841c104980941400000764172070b54 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 396847589 1250 396846339 396846341
    0x108100903051b191a0a06030302030a03020d0b0a0803130f050f04021e030907030b060315041401060b0a0c020307090614011d03030307090608060405190f02070503040905180a020904060e01 83
    0x4c002d114545a01d1281c074800c0c039001084000e0024070100750101c4500203581c5541b5440740c40146c0e9019002581001c83d001401c0b0040d41c044000c1e002d09544580003182c40780c807200c2c0f480307001e031140350081e680b41e500b245000e660f12121740e40100c420f02003040c4200000c0d16a10105008484255405a51001c039414400c100045d1060026001d050000c10400f80410106441007500d100f044c3c180c2c009c1e280c800c1090398484c07003015841000e08521000c0f40c005070391015907906603a4510004181590340d091100c440d40c111111030800304c1c10320302c070138000c603d01807084c04081c02c07220208100060800144020802c00303075440e2814000c101c80104807044a207280d10140321002000c80355285003400004005030030f50300c9200c2c0400ca03050040760841c0380c54050300d44100c201c3d0f1440d9a0156641450001500001260741d540c1a400c20445012034001d100900103829211804980c50900c14081e00c1e11820b040048500c0d83c00280c204070040c2c0d52400c4142d0000d800120116041e210500054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 396848839 1250 396847589 396847603
    0x80f0c1c02070804060509030607140d0c0219050607270e0910020f040906090b090a0c051606061a04150c0c080604030c02010807180e0a060b040e0108100903051b 71
    0xb07007a502c80451300050b8580c2c00f07002840da2400980654800e9201c4800c107403010b0079010074004420b01c081c031422074201107035031103942c00050034412030719014011001e591050b0a40b00050b03607540c120300104002c2c95082400c1c01d0501c0020300e500b6600034400c80301d0040e507000a008401c10b160800c804075213500020005900c44d4000c10900b1540c078502c81404000c558890311584000e60300780040058202c016214184011502600c9540305645403220344000385a44409501401002c2c402207000303c45102d100f0342c00a2280c20001412402d10042c0320070202d240f041c2101081c030800082c0448840000480c0c44c0140b507080540d03900e0118540210340c0100d6400c004058810101088140341c0c2c000c0741d490280307001ba20382645946841c10b007101c020110504400c0002402601040708034100481a540710014030000148686c4410014801d94803a41c050300b0817428440c0103022202c0c082c0017040d50543c211400f0030214080c3c0d5405461802000d0b440d10a010600140c0101044284020703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 396850089 1250 396848839 396848843
    0x160e180c280f0915270b0a11010e030301030317091207060c1403091e010e011d0610030c12020307090f020d060f0e0112140d050406080f0c1c0207 64
    0x1440088031400001c2c052003210b0900c400041c0311080008030300312810342c2c600b910304142c1e80312007070810138007913120710403c02c0c1e24244038000800600040c06c1c04110058098008035a0768101c8070300c143c4031807509484a00441c5101900704100400000c1e0300103401d8044403080c8031401c1555654000c034a1700b411034040c100c0350100350000301c40c1d0401c504c540c003500148490745c03290340841d940c2c425001d08500044402c0081a400b040d001030f202c0f02d074a00e100302c400c1c0c01140081291486912041d0a481e02c00381850984806200801101001070185d980e02500e40c4414000c500e1440e00c4c0c000c01c40a0511494142c0f2400444201c250344040c0420b50141440c01810b11403401c1102c0c00c18000d61024007043d0801d854904003080010000000f202111817102e0320200c00e03400c1902140740c1c21124802100c1d440040001003403288414401c444c02c03107038151140c58072580750070005000c0560040c00284480012410803c01d40281003c1d5040e5094000c14640781c0c40d04030704080000c2c8038050300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 396851339 1250 396850089 396850147
    0x312040f02030d050307110d0e04022d04030b090c0112050402031e071701110d0b180f04030f0e010c14010207082814031f0905160e180c 60
    0xc00f00c14a1300200294055400c954600001c8892040040d8680720040c035288001103402c801004603103020b4018182421202c1d0741c6800401a036014102d6440344054400718801c000300381081400013660000383e01c4070000d4060100300309400b00090001c0d882020141c23081c1e40c1c40c0042820b5440030071031022020f40101060725241301841401c0d80c0c405c0d60b80700c2d06440010b0505018421201801103040c07818011103034a06082c0d907a00322501034210700781d05c1500a010140080310079410420710902540607140c0c448003504083c20010a000e100241c140305000800c4810640381e41d002c1c00d02c904240e00051220b040c10500d01c901070280c4a081c4001c0d1520717070042009000c10314102c0707040382d4070140071413212840000c8030806c0d1580c1c5410041c440d9401c00c14000900044008103080c0c41d6420029801d6106a450314102800c4560643e603450300c1d0719a20190307120031500300c1440c0f15200c000300c42680c0e110440d20343c56000200020b01500500b6004204100b840301a90f488107010144010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 396852589 1250 396851339 396851353
    0xc060314070c1e02131a2d03010216060c0e0d080703080c0f04060917010e0613060204050603040b042006040303030207020a050d1203140601050901051b03041202130209030312040f0203 81
    0xc80702c0130f0304c1200c1e044215918103007010381c914a0114080c0541800541d82c884090b210107447d0014042c40036080d0381c041d502041548540d480d0a880d2410003849550002504c40020000400200d40f4030f9516010f14400090f89010803a080140c4180c958140303032020362696451000c5040b07006010010b40b6400700860080f0b41b4642264594042d00d4645a1002d420418045414242c070f14980681802d50400d07408190a040c0c0d50b4410440796000311409881e0513510404101d540e13004840c1070300c0181c110f02c280300c10410785e411071100300c603120200c0035030700c0c034010740005c40910483c403000b814164005540c0c1c04540700c04030600c00820000301801003140090030000300c0704c0ba5002c800c9001a1a01b0b522240305100074030744501621040c1e4075182048411001940d0310340c4090440c0300804000107035001c404a0400c010009000003070386482450070244103002c440c003070039807d02c0c000c54010302101080c0d480c00800c0d9062610103910011080e2500e0030a5039030100012400380d010b0140c1c503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 396853839 1250 396852589 396852619
    0x2070c030f0312020c07052b140304050603010e0f15012703020a0303090602060702030c0d050307022505040b060309060c1608030a0504150b0906060a05160c060314070c1e02 76
    0x1c06c01008849090301c00e16140c0d03100c40394030084100400302c2034a0702034488461402056100340015400705a0720101da01d000d40300d4001445c1a0001d0740003d0120200d00d040281c00c0344600c4a07143c01100540621941054010000c1d0803000021194544142150120031300e0b860b80000000007560054812086681c41e0704004100b120039018420240c426400420640c2c0e100004441d41008404064000c05181c4081220781e944050565401c620420040c0354421041712aa09480c1c08080c85000c0c2003440d000520065a02000002d03100750710501c1003080c1c03000c0c08615594031080301c0c2c4095036202e01c6650b14407101c40c0c510501614040e4040100720400005604c44ca00450141e100c60072040c0c1e03a4800f8a00703445400340e0446d00540c409010503540d00340b10020b084000074606000e418100ca000000074480c40b11582a18541c603520300800907240c0510400000c08040402240980741814001d0000340c8200390003400d103492011454610112610200d1040e54000c4c540030070b0382065 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 396855089 1250 396853839 396853843
    0xa061406030c0111120f0c010c200a0519030201090b04080403020108060604050105090d031b0b0402180105030303010b0906041d04060e060601020a03120603080c07090e0102070c030f0312020c 84
    0x2150190301034402c101d62070440c1d42c007502000402041040003006540c0b5100b414440c1608900442c0180703000621001100381402e0042039400303041542d030001d948010070b0051500851140701040181c04c00e040580110300c01159044008500004806400e409490200c1c0102100c07900070300070301c600d6004c0c041000900002441201e0003640c41070083e0301d45504200c8184554400c483c041003040002c46981c1c24100240d4800707901906010f005080d00d41c0503400c036001120303001c4940c400004200011803500f070114848800d800d400502140d8104004659248418068031600040102d40e11040346e5030113040780c1c00340a40d1082c00740d43e41c401d100901500d1600b640d040354000c4c01c000c260340008c440010545c0c441c8405038001c195815032a103041d20002d1101c03250301100b640360340e0084041001d4000a000103401c140040400625249451084072500280191141d0041041c00046400f05007000190b0342c11040080c0306c410a454281c840700000303031400b10414001300d0000400500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 396856339 1250 396855089 396855091
    0x180f0b0c0607090b12040c0305010c0203040501080c12010605130914071b030801140a0b03250e0109032910080106050a0302061b031606020310061e050a020a0614 71
    0x120125401600d034070500f55111001d0740290108001c0c203100c0700c0c0845d99204010b40c0c010303000c0c44960202c5604c0342c443d40d003501c0b4050b41e80800b5030700c002820442c80d40e202810070351240780014898100050303c078013001c26507410310690302002804500700e0b102a17880e0320846d0040003824020020b0b03c490110003080c032081103407044040f900b031031004001420311140351040f544e4140d0b07400415a09086a4851681c142d80c0703460741041c0030040101d08503040301c2c0111b001d01c071640104001c0711603901d440c3c841f9426507030380c0c1c60801000741c4030000d072640c00c64a10320030740380d108e07400c0c05080620281d000384007a2000040c440c42c80c2c4c12014044040690100901640c04042c02400455296018455030b400144002904203008201120b040141c1c4180880c0120328041034030301e031045900a04407449030f01074042c2e138960340c00003e1040d036184280c00b00001703126a040400f0200080488030020b404502d4460080c07140016911103004c1c0309000f007400c41544082c0800c080550400d100301c800704 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 396857589 1250 396856339 396856357
    0x614090c0f030420040528020d0e0a1118010323190309150914040e0a0804050406050109080307030e150f120c0304051902061c020a030609150303180f0b 67
    0x45200f024031141c24940100380c801c2c06034060404d1108003c06410387c40000c0e1041400300140d09210901541d9003038020000226050001030445000d5070404500c8440030040851160441d104440300008051068904698008242c146045841b000001050008009032002c500844a0113480d0b200708030040081d89020b60756103d07600b61a0034a2451402a0303407154404550240b404000021441c0c2468400d01c0c2c01500c040740756180c1d10b495501e0480d82c000d0846044202080500c144e041c140304084c010300c001d03e0000412840c00c8009a1280316000000c0c041203442480e448440d1120040f0400c003002a0603c2c50b41d03140481510059600a0030165903034000c440085200d410301d0100340c3c1e0250781c104c0701500744004105034000380e83c00760404c101c0c2c1005007444941d41c05000e081c00580203210034000503981c0c0d10350020084c110398982c0c020300820352400030100040000e489024080da41c1c10308201c0d481c1203c10308100c07040701360b80e8852250540d030f4020100740100da40019040e660 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 396858839 1250 396857589 396857633
    0x2070206040b1c0203090727020a021f1401211203020903070801060312110c10090603050a0c0516230a0c0b04030803041101030b03011410090614090c0f0304 69
    0x101148120030f09a100070744500035140e207c00300074407040058055228106101c1c9aa071002c030401d86001c10142c1c0c20001090015030805c5008501008820855035001c016144007008404000d440303110300e03200180500b805a02481c05075010f0000300320510b500c09600059592090491060300401943c0310300c200718001e00a4035000140034405001f04030035a58400e0703600c2d140024200040300c10b5aa1078490300f202e0700c0b40e01e40441c11912500e0760040306562a5480c0c49956003080000b405441b0090f10480e031003403804019401099004065840c111102004220401e40604050740b40044038050a1400404498200b038104000a40c0e02c09842c42a1243c4000c25545c13800441540100d11001e00f81500c00c200050001d01d007100c01d034010700703014180090103030901804282194049600500100f254009010900d24140405001054903a0741448507074200040e1901c24190264418043d4210401150300c2c416101c041d60340300c40c1c281840715102c0c58682440c4c109002d20802d0382c0f00c3c01d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 396860089 1250 396858839 396858877
    0x40c05011205011802090307330f020703080f070203150610080c0a05070204110d0e0f01200306181f0e040b150303130b04150c0b01030b0a02070206040b 67
    0x200c01c840c082da0f812250840141221845900c4007030f0082e500011100d541030140003408104024603450b103185041b19054082d8151040c1c003a00e00d0300c3c001d1880c1203014001c01c4c8516030307400c3e60f00042040681b5442014140c9031041d10103419124003408030000d5250203050400710380f880c0b44143c46403141808982c5080464080881a07418540030303103409260340c0c0100505001755000d0401404080d101401c00208403008088098060704010710280708d00c1d842d0380350f0015401042003081300c16030380c41008002824000d01e04d8400203070365807010201e404000c03000601c196184130301d0051140250301084601d250000260300000d1810188501c0e1901400022071a00075001d680c0d480f941e440b1900500e40d440b1054050b0140c150007102a61511080007820b0070383c568041035400070701007074401039281c5040200c4006071800e048218020496186160310210f55921030032030450303401100403040d54841100150182c170420802035040403000800040c0200180700a100240c1401200200 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 396861339 1250 396860089 396860117
    0xc0f02010e0a1508040c0b0301030f1407050d03021b090622060503010903020f061006080f0402042c062a0a1202070b01060f0905130e0f01060e040b01080f100e0a020306040c0501 78
    0x400c8c042808003070500b00074241c3d080000b0f06000d418000300388444c0100d034843c0b5078a1000401516100304200e0041c0c000c2c046114403800a80301d0310145040031200e4081d18036041010601e0400450081e03400d0100391b00000e0010030481d0300c1400980000b500a02030f9024608010790f50b50581003c4407003501c9888000f481a1a00002130701c192a55690342c40340d103450f52111800b428502500c01c3e41e12907a9807001000b50480d07080b8103540c0c00d0b003020187e0720045154030283c4c18124024a011440c4a00901c15605152007c0c070f40b14002c0e1001d100c0c1c0e81c4815803c1412030f81d100b58000d444442c1c610000b035150621105600c00d0781250600d07610968510b00c6100c00300d0b0000414400c3c5600402501005840182203421007070000c1042000c450140e403001100c0d40c2550481e9008540c101894821307c02400011501c20780035100c91802007000418541e10203544218091503201c0456646035889010768042c41101801a002401c888050804d0306250102050074411180451180000700031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 396862589 1250 396861339 396861359
    0x51b0a0b0a0c0c03110c0901090b100201020c0a02062a0a1509200609041401050f01082a070525060c051518030c0105010905070c0f02010e0a1508040c 66
    0x80e0341d00c5070384030f042e540c82c1076400380c03500d98029010003400d00500030100aa030f25041c164a008010040011580000100601400d61910314415045900400030202c0a40000810500c11603042e948540d58421038070b83c0003808410500c01041041440303030f42c004a800001800c0004e10301880c0e4183c03410113044480012900d0380701000705409150986014802503402d61141ca4030b00c0a01504d1400060000180c2240c00c400c0c20040440c42c001d0040c0a030f4100907189508030b0030300f820030614a040000103080302c0c80340c0e540c41079030551004c51610384180456040d2101c060380001251501182c0c6010000c0001906000120600c42c5000c002100c5118140c201400d680180c050a20b54242c0301c00610381c00c0c00100300907122001c030020300380c20306010001044000c0080e000018503505100c080300c10385002810314820080380301c2d04000881c1850041d100220780c24202029000302c04004505001c040e07a20000da500c2649891040240c4c00c015414840d84c4102054540c490301c50710102c0e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 396863839 1250 396862589 396862601
    0x1e090901020a021b0f130f0609020403050609190f0303090f0503121f0611190506161409090405010f180506130b011e0b190e090105130c051b0a0b0a 65
    0xa41c030a07117180810106003007600050600c007a040c2000b05401e1180e800c0002542c00c0e170343c442034055a00080c10002c0c4001030103600d4000d42160302a040301c8484440941200030000782c00382c84141c0e940005803c1501941c80405400e0344442011030380003c50030455166002010b10700b40b490814800218038203201e030760600307001e28140c0c3c0604142e070a26000b220a1103007000903000c0761040c1d00d4207a82e0700741080e0364080d0b614842c030024445450100480008503080707801201c01d00c000c600007084541680c0094032442c240a40e048045655182451030141440d40f0060b02c03004e00e031814140e0405c0c200d0080d0b01c00c1d50b0040c400c60301c140e15064107400744442c240034003038041c8901200501604100c0000d51803c204002c0741c883c0340a4460281512550100031990501c07000300c1c4000c003006400c130324400300c28901192100c21a62610011a040c0a0320104071000281d540310420b82c0f11340100140e800003c0c1610121034420ba00c2d0346102c1da1b548115901380c1b50450050002001b00c442e6000389 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 396865089 1250 396863839 396863893
    0x506100311010207150c03030b090f010f1509050f010c061e0b03150a0e1f0218030d0f0e0a0b0412023d050403060c0305041412091e090901020a02 64
    0x1828410b02605c011511001040d81c1101011348074041c001555881004450242d203900b8920b960f1075140820f1000001c2440e4000080c0c03200781d401c0000e1040c0c000c4500341c00c5807815110012b60f0000c00004a5074074000d07a0703008245a00c0c081d03400d00c1102d840351080036104a00b4004114038122a010103030b403405500e1901c04034a407280b000503010403158001c021408800320403900c0800b9030107542c005c0c0101c5210904000303035001c66400d040c1105954013a860307100580103444a1004000c000305004414005102880314031000000d040d00c410300e6640c0107024240d0700544898a91540c03412141d003184041c1c0c0320b50a10a45400390044801841c1918003001c0ca16102c6000e20500580c01c40042c00b68400500505200c000085412801500600c10090f80c00003078903c2d191602c004031100740c50044200b0707444100764690510112046078050003044592a9441c24211415030504105004681d00070342064240150881c05401821000c4000c1e003d440174000c411041302e254081252413 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 396866339 1250 396865089 396865109
    0x10b100e130902060f0c0a02240d0b0a09020408060115090e04030c02030a08071b08030406091406090d0f060b0906011205040c090608150c09090c0c0304030506100311010207 76
    0x101c00005a075503100d40c0c5190310142201c2e06021691032021055000068000380a401800c044403c42c540311201742007a000c107854280c42c4022074048155280908000301808907038807119583c4660394101004000c0403000c1085d9551a00d03240c0b19a00d800b000e118030046001800400709055020b180c450040e28028014030f1034541d91614200c1d031020b6012002d0343c044c0100d4040d04040f9840b10300402e9628040c02558054952180d054401514607a200883d19002480180145548214a9000c88a403080c81c0c103041c0e030700040001c1151150004480e0300c50a801303100c00400c0310030441c1901260052030100311001e80041401402c1c00200d0b00d482c00100d4401040082c030940342d105076003040c01030408100d040d03118422102211041d80100f80940d000201e10109040441001981b000d1103400c0c241c2080000e80c04a05903000c007510142a403c4042000d8500c034104009880c01160080c0442d542c900f8a05a032041c100740502080c0c80340d42c0c03031003050740d01c550000501a04a82100c2d007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 396867589 1250 396866339 396866359
    0x40f02060301091e0605061909050a170f0c0907200a050d121e2d0b0f04090b01031415010b0703031109011d0d0f0813050a080c13060b0705010b100e 65
    0x80102c0030b4500c01102d40007840127402d80800c0039121801804003904014402c050020401c3c3c2a6a18041041e4945000e55111903140c12417a10340c1c04001d43c0121b501e0500d0030152451011304002800114010404c9115640080f01405800100c840c4c5072a06c54403403d60390f5148041900c1607841c40f402017020f6041c4200d0b0780c0d40861280c0c0c44041a00c20301c10381400355500302c1a45240c1d03055400560308005441d288400e0340c62070480105005840200d1b000c01080a1541e03405420010510020300901c000c070b40441d04c0213009000c00849110003401c120159a1501d21580558024010650001e407400155240910b500e00031210a0f10058503829900300480c031841090303841c0c10072041d400095902240c4001010399281c0303159144201c0400d5107a000004142502040b40d40c002d80c81500140c2040000f140042000340f031441e81a81c10950400c4c000040d07d0203050240e10070b40d13011100144100c10f1002c19070103800c402000302c46088180c000400120f912240362014150300100e105 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 396868839 1250 396867589 396867607
    0x30c030509011101090516051905040b010c0c0e010807090203010305101d0d030b04050f010f060c02030c150c0f03031b090f0303070b010312031e0203040f02060301091e060506 77
    0x340c0a0154000305150412280c90255603079429101420b03c200c4113980196032000e44040a01d45001c0a80700548903180014444030000c034114125210b0540206ea56a07807903280c0b41d115000788030b19140c000c1401c81c03407540e540e146680e45040902c100e68990181042c0410300580310b0080301e040700c1d000340040021560074403441000f00450301d40744070700207418100c43c808480180034421807483c1076180090784201d104180300940d60001d2a01084400d55001401007aa40743c42c44001ea5481b4075103028021903620101e8513103030515031959481103007036007680007600c084c100400c1c0400481d8184c8030300070700c0740000c00e5aa0009407001e20082a4001d0681015105c10025103405007000b04120300541241002ca415540710000c281c407041039540050060002c0141c24a116501a180801501c100e643e50319001c00d481c0701090707a81d01e400002041c140404001550300a03500200b0311581c7e943d41e40405001000054110341e00441c40440101000102d44290004c0707410181c4a40d240042103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 396870089 1250 396868839 396868847
    0x8060403110c0f1207090509031309060b0304030f17010f0306140721060314060618010503060402090a0f06080d2a06050712050403020c0a080d09180605090c071e030c03 74
    0x4e2031001c11034402c044002032040064040c0500039100741026503502c50040d80c3d82c4e122009150050a442824030504006401175401181d90083d01442c1c00180c0c10300c5603074129103c2c213101d1450050034005c01d0001c03402103070105860080701c1c1700700020068076a50401c0d40b400a44221f500f18042003512a00e4206103000d44180c142e5510202d030005245c640301d55800c4141c04529282c410a40d01c807004000345d0303081c19944c400211740c111620030703e99854600065600d0074010030081c050f03402c15021a04040203500b1090001080030b00500402da21055466500e0603822a0140061324210100c02c00c6509450724040401c190540001007a2035501c800000c0c12018002030200100c2c517a41070001c03281441060b0049110740d001d000a52285800c00c5580c203c540c001007140d80100b1000c00400307410080e104129081407102c41800903c4881040040c4000d902c07994000560804000d0b14821080c0100380b180d20606a590700e01003c00404050169024801400b00b025010880007107401703 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 396871339 1250 396870089 396870109
    0x230109090b0a0b0c0a060515010e0a14040903030f02180a050a0828050601150314160e120a0c030b01080601150c0c121a06010203180103090c0b0408060403110c0f 71
    0x100c0d100310741c0c02101c5c03660303141e0884004032484405140c4040328601c4d2980d002d29600c01c204000c41c2e1513281079042501c139200090618070000c0c410369a0b40c180c082018000d0304980420440090b046458940030903900c8581c0d2550010b4501c1600200404030780c521708502c5007810340d000c1200034141c0c0c110000e1055418519183c0c012100b079020502540002c03010003216002c1d11580c6010684008441c44c040c0c00d0b200b0b2503015600d0700c040070b41007103101800203c5500d20305144d4940000b40c10b0491000c203403c130100d1070f80b44030f080c000d26680400b4441c0c85c0001c0c2c0202d034400d0320040030a03a030380e404903505d488080c0100300c841000030540710901c900c21004044114011003171554180e903149659650070100076400c58030440c5030064100098075201c21143c0c0030310300380040c62807c861b1542c1c2e50003542c0036000250515554521410030b100d899440000540726456003e40da0b2511110405e5071003008480480011700080749000d080c00010880f1031844030042d00300035160107028104261044 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 396872589 1250 396871339 396871357
    0xc141306060e06160606032102071d0402040603050105011217090d23010f0e100b0604090e0312091c0c1106070f0b0703020408011d030f03090304230109090b0a0b 71
    0x20404810f0004111030344511b80c01540714003000c01c0440e840ca000340c0100c0345288214019504100320400840115a00000c01c10260600300f940c2c50351984001401004190030141c4558030306400407452502004500c110140502142e840100c242204110640b04a440070350300b080386944000700090030b42c1944500119410740740b2030400700d9000c16500f1558060142d00940340c80f844c0045180f001885680c3d8070b032038190414014420302002203407031031040d4461019800d986d002c841e080b1101c184280d425810181d05403400c0c034101810b49951700d1140d070701811981049212401100c40c06803040744001d0b40d01c41d1002d4075005c042c10809c105030300315038000c0c1d6003400d96a00d2500012440600c051045850792001a2624202803006084030880740341090310019000c040c0050301c4001080d030300560030000c2641da50b030781d0f656a040d09500032540211890303c0090a00d041189025007030010780e0200380c0e44e01c00015075440003001510602d0646079044000c0c0d040030701ca01c0d8003100081000305 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 396873839 1250 396872589 396872617
    0x121d0a080304051507060c2c0d02060f07060e060916080a0f03030f050a0e0105060607050a0b090106030203060f09010c0e0d14190b04050d030902030712020109030c141306060e06 78
    0x32a5846e41c506803a2440742c000c00040c003241000440303494144a0400540807034107001e82c0014404042800803403490750207072003600042040502d1445000807034042aa10600c01d100d4110045203403580c40384107980341030b15030041c030f004c3c1809c0c0c0d40342c1e9030700c2d6044038400c0004001c480155143c4043c03546024000b44c08140d156100d0504084987c082c081c010304c00490000358036101c0e002d4450840340302500140c07060b4820809803002c1100044c50b4150346401c011074078496200d268000b80185150b5000070340601444003040100500c25045600c01c4281600900c44409100401c41d800c800c81104154446207450b0301a02158524004440c400448021103d0750900140d2006404000300001ca540031032850410080105c18018081c00c001c0320b003428440c080051780002c0d02d5081c44e0040c0d44040c0030741c501541c1560300c41c2018400458010840c210340d1a116039420721050382181143d40501055681501c0d40c004500c80c0f40202c607055991445d00717410480404c5801c0d030100d01002c13011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 396875089 1250 396873839 396873847
    0x1e0a0f0f090e01060c0507060305130314071205070303050604050c04150e1c0c0509060a290d050103050613081801020309100203030601090f18020304020d121d0a0803040515 76
    0x4240782e0b6034103a01820517a00c2d00d241c0217151789480c1e460604030340c021104250402007480074141c40c640380c1080300d96145c14081d21010060107119054020041c01411009021001c90601500080200038517800395509014941e2440c0910054030020340b914028a1010002002401200340100740620b1541c13904290424041c40011000c4040a181c0c409200d41300c0200c01c20040c40c901000014202030312440c0d8980b6041c40082c02602c06441109144880d110108110350450380012000b84c00c0340d08075507150064a04280300030802404100c0d518820a400b1803c800c0807120340c6030760181d1200880785040b00e07031030600c41200c0c0e0108410781036100600078100943c0e02ca909105941419a00541c0c0340d2038040f000500c2c40030079a210317030b034540c28120701480003c900e002c0c20004403034a100090380c2c9894a20201740f200071406405001049807400c11048079030f00a920303214040141c0d1140400c21840c0c0c08020500000d07128090059000300000c002604003140e0001200307640e48107103414 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 396876339 1250 396875089 396875099
    0x204020d0903050301060f140409200315040621030f1803050102030a0507050c0309040b2b060507030209030604120215040b0714071a190603081e0a0f0f09 68
    0x1510100507046010400c0030005000c05540440120402c00c1985041031a0b4244921401442c0c852405008101a141d561800040080c0c50f40703910081003c1d820541d507840c11060301301003204205203d602c200e00f004000561030080850145030200e07042201c0f00f01070181d1340c00b41c3e00d019441c04544240000c00c803040300b0701c5032800326000085024500160740c03458002080001c981b8020660828008144210402c1c40000415241c1c490f605860001d440a60040020b20091900d21008444020401c4100214400c0003459100f0b038440c005c05d100c13a4548480540507405640b800740e03019402000002e01084844c2002010516180180d500701000a001300c0c2c4440d800311001c1d2607060906091242c0d8551100440c548402c06503215800c140d80ba0f5520b02c54451031588400c0400715000210b00100145121000b0002c0310030030400c501c0b0355902d401c91046d08105450444212181000d1044480d19011039529848590f500b1780d90040e00d160035114200d070500510700300241c044021074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 396877589 1250 396876339 396876341
    0x9041505131a0102060f0403030e1903030f0506011d061b15010816050112020d0617010618020301080703020105031b04061e020708120a0c02042301080102040f050405040204020d 78
    0x500c0d080588404038242100303181d00c1040981c40c4141d40c3c11540144100806840c84501194006038545004145542030b220700c00c4c0f520200303c007501030300304091108008140d0141d00849200918040c00e000a80e105001510300700c0d502000311500d00400364000c001440c0400061000a101404011410310b03006440c601c1c1141700710119027000710403001404030a1041002c42c091a0400310080c0209040400080a45c0e500c3d0f154103160329000300c0c829174204010b4000c0350180043c0003000c0b400c080c196904034080c0155101e150170341044800c1c0700320703500854002c0368143d03140c82d8024880c07545154011500b643c002000c0034030030240303000f40242e2109203400801c0189081d5407890120124004059a0640c081e11060203560100304200081100460f00d805000d25403c0400c0d155155502d081c0e0380000c0c4251f00035401441c0c4401110401840e41e0341c074192034600c1100744400d0380c0300c000c0e65080340314074003a011a0341c1e12102c0c00c0100d0324080c0c00c6a0340c0f181c4050b0005d800d21403c3c2c0180d04c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 396878839 1250 396877589 396877609
    0xb0103030e1504080a2d0c061101020c0a120221120601020a020d021009050301020c0f0d0c0312052e05090a09030905090414030a0302030103050709060b09041505 71
    0x100040d241c0d00c410152442e210400546001070a4000c0f03280502d402102c0b6960250800c00070711010302130121520500340300700c2124000ca56241105100074107898020608075180c0a100086400c03242102c8540205100b55500010040000e090303035070310750b20b40480100c5180f07000001c5216551208000b10803042080111581c4580720946031401d0701c0b4404001100104440e0440d84500000c001607520708041072081c603010368910024000740c050440e404515a00704070340540c00096540300340040010500300d13445c83c120a55036940c00304141100d8a5031410800341c0020b00516000c040d42665612068020807050f52080101c6088003a40014000da11808200f82c064040200280c6c24840405944001c810300204070042d86554041c007510718030300400b0b0091001c200003604218081e10006000c14060045036203400d081680100694000d001c00c82d035a0142180000c2c19281c1ca0241c042034070340740d101c10f50a00c00070006120040040101a250541d451100040c0e41c0d100c2641d11 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 396880089 1250 396878839 396878843
    0x8130b0a050c10020a05030610030e0102070c03020a08060c040e0c1e0304050714030d140702060408060709060201020703050a0c050c040609020a09050a051c03050918090d030e03090103090f0b0103 86
    0x902c2c0c441048420440c1018041e00f2924001030040091070021903001c0c00b22544031408603513241e031600e001d1004400410003070aa001d010741c400601031090000ca04203140c12240308a44510340151030b1903209031580c0003680c2c00706018034148030500c0036800c208001a40660904282c0d41052848203580080c80760440701c81102d00380010a03c0103000341404000083d00014085052586943c004030355a410070a0884003005240e200000d1180108000c07100b420750020b041035111078454007801d85809080c2d68260105541d03240028a8074010b001352143c041d010380b2110b042100d0000191840c0710981750817102406544540c42c055070700c900c201009000010001a01c541d0784980180190307043d81c0020b031003009400010001ca03511410500486540503044004c0121203150580d00d600132030030745540c85a170900c86000940c3e04583c185104084200071200344080b00d4a0550803180f5000a00c2e40f140c0003003100f103045501980207821060304c80d1582c1052034401c0e440d0b0780c04c000402c0c1c01c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 396881339 1250 396880089 396880097
    0x9160b03150d0809010311120115120b01050304240c0e0a0b040308040902210717070e090f071101242705040c09020d0c0810030b010308130b0a 63
    0x203124040060110750010000d00742c0b1074030803500240e15001001c1c01140d094604054aa060741d001080d842020b541c1124038150144546c1d50315040701c44040007030f440c3d443c400960a10b11246103044540140c00340464103840d29403841e00c480e1a050b48801d15016070000ca0086480f1031110b103122440b4084100825683d21030342c0000d00c0341005040559540452081002400140040f4804204840488544c1d420050340c4954410128011148840c1c040382c80070800d00c10880f802d83c002401d05248031340010b94480130796500c4810364900d08800e0041e5000314610707000440d400030400d802070700405a030400000200e0441c00540c21f54001004010041d50815280c4070400d041b00d0640c0080d1000306000b150441c0c59040c1003e02d40310b484404480c8680310b4011405106020a80300c028001070f52041d5a50340400746241c01a05990043c040002c0c04100004c40404894410509407035000c64401616441c6407030305040c60708004543c0c100c00c0c0002c3c100007a01d00700301c4010a2030f035240f511 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 396882589 1250 396881339 396881341
    0x106050a0b280212070f0209011d0406090203010b031b0a0608280209090a1a0907050f0306030102130e0a1a0d1e050105070e15090904020909160b03 65
    0x40c080844110340c8680c6507980140810445010702a0700d0410000100051151011a41104034500b204d40008048107800008030300c400c0c40000710f41150518000d50b048501a40e0720030f41d00841c003156040c2c3c46400581c4101040005416400101850340000e001040001c581300c00641000703091840c82480040d04803d00c4500e05143c6078950050144e8180b16140b0300c2e00002d14040c108400048161070002c0c03000103014080c03a9410350700304a001801545140c070740700303404500504a900780c51080040d0001c40704401e04c0e041c000b040c07040c01d0642e561820010380c031003e6805604040c1c03c09178107540900c0024030420024400c140281401d650701500e905140211808807201030342c244d0103064180d14854001e0726401004c1d0040c60b0b000c03189451410166482050b1107006a0b8014100e500305818441c0c60f940c05612030418500840702049241c40602c0b2545891141c0c0440681103244500054003520b081c03541140d129800c1c8040d0b23881d026419801407285803654015000d05103000c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 396883839 1250 396882589 396882599
    0xe0105070c0506030a140c030c030f070c060c1709010c020c060702130203090303061c0b06060c0f0706020f01060608010513020912030309011b020a020306010302060d0b030102030a0914070b03041104020f07050106 93
    0x440c41c7d000b01140000a1950406520322143d0348001031901905100314404150003d106001c541049034000344100480f0064080040c5101000f1403905580340752040030403c240c40c18440da50900c041034000746074082c42c2105010f0b460b00302c108141d900c0141091004400f00a40c00250b1003402c42c100515940c0c9003280030001c1c4c0c520a42c0c1303546801825010a84001201a080b143d0006c0007102e41a0300e8210765007a40c0c0c646a010b0404020502602c0000a00070f500010f203071000c0d0341103400a0240340c0d00c400e002c4440c004248101e0f41d0050a8096a81840181e980204822000541a890f90001c55003100d855540251206c842d103a64429040b4901c41d5100c9580d00b24558603c0505102401c0c0e800096480d10107000c0030b84038440000f281400e008480d131003a07403080405802503440703103003400d4808000d0055006c15908250414681c05030400003140381780a43e8426880d003400c40d10342d51101c822041101c1100ca070401d600b0050b040f06401c500c03018100b40c5202d0380000c11058208 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 396885089 1250 396883839 396883871
    0x702150406091a03071b080706201804050403050415022506020a150609090b010e070e010c0809010504260f01050112030503060a030b09030409060f03030e0105070c0506030a 76
    0x35030100e5040b050305003c000200c0c060301c040740d400c5100da00d400c0e01c0540401c0460005401c403080014205000010b80c00104a42500131310300c850010900700c2d90a60341d060403001c9a02c20f1541188079010004422a0a072170964080340c3c20a0103403810380c1c20310351105035250084100c0c15420015a21007100b00f000d4042c05110505900d080c2c120182001d450888069900c208081c1d000300b024080c203d942d261104280d120400038640b2080c103000259980c01c040d85a50002e014a10741c43d20301c2c0c0c00103004640500c2d0a1015480c041e503d4144014094a901d40d540d00f1212521b030400c00c007000300080e28500d000303004158900b40d00e9075242241d0071002051610505c030600509a03414a001041868580c26000d18640c0d01410295540d03504d03070303000801d2260a600300501442c001070030310420740400409001910200300d01080700a03162100030480c680e103444010b0004070403c1d84168130754864000f13895601e100e0041c0910864075070000440f0b13034004603034154a035aa262540100f204003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 396886339 1250 396885089 396885107
    0x11090a0e09010507090f05010c06140c040501031a031207052505030f07060f0528080f0f0c040902180d03111209060d0b030f060a0c0306081f0c050702150406 69
    0x3145c246a86128540540824070840310320903203041c04604d46111081c498140c00a07190100c220016025034501941240429009400340b030340082d160141c14a24810500001c109900c0020000c05004260030500030700e0341d0000c503040751140900d6007040c1c4030200c0c0a040e034861392001c00000b22618102030506241c04d502c103141300d01d583d001403000c000064000b45072240b040c616140040d5941c1c10450626480107041e01c1a41c0798246207404285c01680c0300299034003d10b14100c003261551200008580240001e031031500c50b0031000c104c1000301001550050a0816100342c0000310f000d405000a10102e80c0c000054020810049011090030814020142080c1c4440515811302443c90301007000c50003005000c025282c1d0303590b4000e61a030b40400c40c00b01ca0104100c1200c11514000d8044005403162100d25008681090004144110081004582f2494402030000e0301101d4203d288060040c41c0d0712141440717400c00c18440035860307030308500320121307025010266980c0c54a0030080c03003d24 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 396887589 1250 396886339 396886351
    0x100e1e090a02180f0708060a0803040b131d0f0402270a0606140d11090316031104020f090d06150b040305060a0504020102030a030c2c0a0b0c1011090a0e090105 70
    0x43c00c00104544000c0d155006030b000741d50303440c01d00e40b20b41d0340f24041030f00060b0607084a149440049000503001c5040360007040c20000c2900002e02d807d5881030210011458032400b000b02d01c80c07030400952002841c10a1070350150000304421840c800c0b01c2c42c035540b00039a80d40c01d4003001d035a81080001c0b94180340291030061140d454040d580480c4a019450f0038041d000e91030040a4403408403640d40122074098800381c0e1402400e482c0c41d1401400400e240a071503100c03c981410440000c821a841c00f131007079401001c54242c00c07d03c0c215111007000b0b0410582c040443d261552003180000e100341d0203e610b405049914a0207950301e0070740c1841450000005c0044036018104402c020040c0d0380070094032150401030401145014100c0b10640d00031818004c092920410404641070f0246a6802c03040d171104240e908015003600da111131600c80c03184024107411030b4400401c1c8105400154000003100f00010300950629036000005083d4031810b901c0448940a510103000954800f0700c500341e04a1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 396888839 1250 396887589 396887629
    0x90e0915060915010c05010207140307050106080c0927011b0206060d030e19080613060e150c0915030906010806010b0406020601061101022101060e09100e1e090a02 72
    0x40f82c0501249103910240003014100400500b0440400070250141da007816031140750303000c420071519441c5549801404082d144d540c240078001a0240021500c4400200054485802c50b610310300700c648042c88a281e10a4041440c1d8140513202300203110342c800e041d40e00700440180c074449800003450840c000d0401c078840c4d448150100c0009800210010b1040019254a800000c1101c190030698850341d0202800f8081c010800040c0d024103a0602156445030108105030a41e040000e079480c0d298103011034085074140081351014038180044d0072002f01c0180000e0340303201d00300c11003040d94100740c0303038160036501c040010300010500340100c50140c5003d0b9222400e243c5401d5000f50742d21010700c02c000c103001d02c0481c0d41c80d040f43d081d0100d4a140b1104058581565203041112031103010034070401c00082d5084012000c0303031030a210300f940958102030074401c4007400d15104c04152180a0020109a170380b05e84100d201440c030488140c03040403010060481000f4600511120240102001d041c0c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 396890089 1250 396888839 396888841
    0x105040b0901050f2e080f0a1b1110021b011107051216120207060e010315090c0e120703060b010503090a030c0c0503030f0c01060f080d0f090e09150609 67
    0x60b07244d43d064800d042100319146850040e9148102c801c42d01078001c202c0101c0b0b5505a820340c1580c100c10114080c0106800000380c4e591042c00f0308040301d4144280362002e8148059804510740f044103504070380e0100b881a00c81c1c1c601c1d0f0b403040004a074082c0b11010814100744c2e1440c01070f00000c2c450150b51121a48284e03150414560fa6141c42d01ca2200f8010440c0c2c40114880300c00300c1c018000b503140d01e9446407048450700310130000a560340d48107215140001d103071044503a0351035119004101038100111100b6440f103007000000805807801101c0d850400450a48241180d40d0700502d08502800c500c015000305403c5091102c10b07182c030b00310300c541408000c106000400900080c13480c07500b03415280a011080d11440d00310080080d69114552604c00841d154a980050600901c1c0400140d002004541c0c1d0700e95044424030110b20512240e07803c004400c03181d07107016000c0c207201c08055241c00800d040e101da40c0703000b458030141d42260715540310307109109504d0b100d41c07103203030b02301c0f204480ca0001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 396891339 1250 396890089 396890099
    0x612030c0f191a040503070b13061b12020c030d0c050a12290a0305100f0501080c181305100c12061503020c0102070f1101120e031204140f01050105040b0901 69
    0x8980341d110100f50301e500c080b10005040c420240103480070f26901648480050030a1800b500c171895840c2d03000e0310580d01d0002d4a00005901d11401c40411005032109608001181c000900a4110074041c4001c1d01042084c000b180c0e039a481040301c0440c954541a44949200d540180700032401c41d40183d0451404182c00d168000312100750481081079001c01e624814070b8008281260801d43c0020308910944900d5001100c29030000c134100e6040740401c20080c0e03a510801a540c0004e01d5800350000301d082c400800c48500400c000740d0241c0303d040740d12034460096980e5885c2000b0500718242082e5109407654091380c1c0903031034103084680d40030180aa41d003004103080111401e039483c441416030001d0804d403c0e450070340686986540061407503000c04514201503000346801c0407141d00054444034203880421682c400e6002003a981c0c0c005506181c2c03409280d0740f05002c00350040c1c400ca14024000384800a0030019500c2050000f0004103e9503d001c090000b91001d4040c01da204110201c01445 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 396892589 1250 396891339 396891353
    0x10605010915020c130e160e060f031f0203241513051305040c0e0f010515041212020c150d02130f0e040b0c0a0206040201080612030c0f19 61
    0x4141c401c000255010342e00c004800b6450200e0340040c040d084204440251400200b507071003901140100000c3e503426841c13010780594400c9581c01a440125903003c003080751420081e5405440300c030050110340045100407020824961b52400124181d5000800c12920f4030005110319201030071840355101000740c05000030506803e0440815602001080410b401f44a000b03e007401030001800725411540b109400b0f002401c000c5400707503040030a40100241100d1441c9005100d0590301d05000120390828042100c00780d026802d0003c115014840440d007030150010030607259100b41e5201034011450710b4007070b08041c880b5961034407482c0020304405400310440d04403a00034074642e80c0180d03114110700482e00d42075900c0d0010155140c241c900401c1c1f03062003401d824021800340286c00b5003682e50900700b0704248a94401000140c210780003060041d4099007585411084c0144042c0341e501602c0081c078699000402a004030754404a0080c940000230701209150461340390200c034001070580c90b012 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 396893839 1250 396892589 396892607
    0xc030f020112060e040b042f09010e0408190507120c0b07020f0a0312020705120717040b07020607060b06131a030f0f0a06031a01030b0f0f0105010507020d0506070906090801060501 79
    0x91b104181c08000101004816418400380c0d503034281180b030b29004824800b1070080781032500e541c01120b030b4070008150f0f606060b00303940c491548005410310f04103c0b40301c280a4002c0b10002102444020f00c0f40c0c42c0000c0807281035150149075651810480c0b581e600f0001c0c0c141d000a40203c065400c503100c081e894407c003041441450341c140c10080c8648003107885071402880755243c040c282d0b005003102000b03046040c2d4000d00301c00c0c0c00f81e4a1800100180950b85d19648140d118001d10304c4410002c000050030180040d0602c14050800003407104240008603030287d000002c245502d1510340802e21905c88800c40c580002020103104905615041840490140c405051320051310640d50004044d8903480d00900301461f4082005211010b07a060361070840f84003030004403601d508040002c1c0348e030012448030510034501e040603088280d103420015a00d40e41b050109907003001c00240c400021880401003140140c1c680d50398014420b282c07440003003900c0150f402040450b410044100000c0e03070310034054 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 396895089 1250 396893839 396893843
    0x524010309150e070b04030302070f1401020c04050406021e130e060306060904171206090c0a0806010f110712021207030c05060306060d0509060103020a050102010c0210050901090c030f020112060e04 87
    0x40162086208504c0c1c251150700c420b80c042c200003400300825502046d80c2003154a000301c0f044026448241e0000800707164040036006901c045088038683c42c5c04d400668000740900c6c0010320f003002310305201100908940c0546010704000450303a110381080c150300380040000a140010500346800001e80740d0b03c001d03007001e10445520001c01c05000e210240040000c0660b011180e403110b80100b4030340060f4084070150f00c50030700040040ca0b9420060225091a0265600c0e01e60941c0d4490054800d1402400490100440003a04d2120001c042103030301c7c058a5405150840b0b500c4910400507805244400300701c098000c4481000000d0f42c1510f0362003a550100c900684907603450003c2500c0e4002c0d44400c840450604090049040022038090b040c1e83c000e5034061030081e2150f00590a07100b4074200c01c40140e0190703003c100766064641c030880d0086046800410b0141c11502c605034042c2098209590303544807107218104560300300110307021101030715130148a150325011051a04903802800 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 396896339 1250 396895089 396895091
    0x60106170109020915070c030b0c0405062a0f0106050915100302071b0e091c12020d02040302060403080d0f091109190e030705010518070b0705030409052401030915 72
    0x2c4d00416669111002806103904d6521a8075905142000f480c101020f02c000c1d50307001001000701c0c9031442080202c07410798102421071490454900f0b280c0451220001d030b043d40c0f42420b540d403100589002d114840340c0d0368800001103801801c020400c243d00d600a84140c098080159010006881e8007540f882440005e0400680b69800d0f030801e10314119901c014810740c028160804036940e82c1851038a801b13040c0d00c004076040380300035003098070b03500e541101c1403004100b00e5411040301c58002c1d0010702d43e04000e080c025042a60701d90105140b0303081500115031b40d00012640308484c00e05403258400b03c1d0580c0c01c0920030fa241e03580310b1070450040a840c081c0900e00040010380c03501130481c020711805c01d0354142000a1040605070544035000440b08071169420701000c0740e00900c6030366000c020401d851001d88202481e0049002c116805100119002d000030300002856580318400c05125034000419030401d90b02040c02d030001721a15000703803810305250510034004140c000748010100441540 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 396897589 1250 396896339 396896347
    0x130b1908010b190e1f1203020f0d080a0902030c0d060606110d0503010302010c0305091f0f0302030f06190e070c03030609050906060603060604080304170105061002120a03020906130806010617010902 87
    0x14540017030360043c1e4140703c0c001c0d000a5000916036001ca9204503000d0280d401d5030990840081e0b1203490b114240e58010000318050045000d040d140d500c5a00341c241700400311041d82d0b0345d0300080b401c0c60201100030344000d55905c034104011600a400110903946680142031078200720580600300c1d0106000c00790401c0650703810402054002d0003100d0b10000014908420700d0080225820a0f51141c580000003410555a06402500900907640103411800c40a1038a40d41c40080c42404680041d0701d14008030803200004015103c40c0d0320300d0081466541c6d1420740c0c04182006019180190f001200291400707003000703a00000491100d4002130203c0f4141d54a486070740020721580a13039001000c107804001000641400002c0f5245901c881c03000091203203650310400c100c2494000c18a01c40580c1103281031f0207a1710021030041140300314900340141482c03022400320321650000c03842d160321131074500c0c0d0611958000700640c40c0103021601c0d01400da000d404240d800d612106208246225030082 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 396898839 1250 396897589 396897601
    0x10e060a0b0d1e0e0a020319150c05190807090e011805040302010e0d05030a0b0d020603070813061a0406170c0607020312030c030a0c0c080306130b1908010b190e 71
    0x342c80b5901003000e404080c00112413007200140c4501c40e40f00d04a1180c4034031f06483c0c0c0e00e0545c241800010320381000c05a242c86000602c02ca0140210000400411904104504542403d0110242d648a0b55592003c080c03810f24000340c000304c01e03a00445014078550004001c0c440c556400d038014800c100070085684d4542e40b4090b805004000c402d040140031f84040021415400000307980f181503106824800501c6007814403c1b41101c01030060341001080001503c81c50265080d079400c410b00480240300e041c85625040112140b40c80581d130192400c010b0307055245841d0003013401401c1440e518003981c098592159a440702144202c6000c0c010200720002956070500112020308503401e0311316030303038a0106034400803580100c2e0644d16481c81c1c4401d03c030b50588075002840c1c00f80da00921322490743e110081040790900d190003e140138140c4440b1050381a4558103080924541e003940103515850410164509580c0402d421900404c494101c14114074407020100b070488070036000000240e1224 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 396900089 1250 396898839 396898871
    0x30c0c05310e0706050a11070303030203070e030d0f0c0201050f0c0f070608040b04020d060b18101a04050907021603030e0112050f0103231005010e060a0b0d 69
    0x164803460340305410380d2849440303808019055070540034840400d1200d41541401204848011007410483c0d444800d0900516000700020403c0d402503041c96504e100812001903c3c01d01140c0080b0300094000c41480f0109400458400c141c000890250480054802d401804800519660000c1054028604080d64003440468034500c80c07607008142e0702d541d1040f806646000040f41c940c130707a02c40d20f580001c425101d0003c032070240b0f81c4954450b00944032502044000300103880d0503104a80e448841880a03550350106d04103808098006084514001d411403040180642c0803070010b2566200c1000044400000c0ba400d8482c04c842c800300e039490b0b4150807031820412001ca40d0b20303032111110100078143c10000346256614240e0f1411f21850300c00c984001600d01c142e40204501d141d0500500c0043c4261081281050202044050500f21034040342e140001c00100c00e8240b07030792000184078040400a5144c1d0014095404110042ca810704031156842044280c1032400c0d5505030344e20b2000d0038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 396901339 1250 396900089 396900113
    0x90a0b0607141e0319080709050306070807140a020307061d06090303060406060f0c02040903110d0c0507050607150e01110708030907080c03070506070c0e010b0a1d060304030c 77
    0x1c440018415081c2c8416956a0301a00d0006459421074111070350321081c00004803001c0d085a4041c1c88803807400280b003954140c6000d400740c0284105950046640d880c104911482040780c0c1da1942914100070401604400044d5140039080d034040014100043c4c0010480d4110741d800200002d800540c03e0500344411380b02580403180b40588424400200000006507009000403035041000a6a4000c00e544001c00c82c90b0100c00b1800782c810000143c41c0c568020030b003c50290400d4503020305002d01c140d0034003800181c0b200104143c1070031401403040400c410400340c04180d51051500174240c031009509101820300c1c91026072034070700c00000243c00390407130a24820303001d000f00c0d00c0310700900d001506600201d0b400c032058400c10300300007001d18001405095100c3e028002d0150705003403001f07210303695105007819590060760b4480081d484900081031802002000350507902e60890820041c0714194507200031004043c07070f45d00306005603201c0f41201c1d08550706040031150005c3d40d00e080d40714040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 396902589 1250 396901339 396901343
    0x6020d1b051501060f02010b090103290a020406030f02071106031b03010b030f16080615091009180c390303020c0d0c053703020a030e010c02090a0b0607 67
    0x65510900200a801106103060740c40545a6405c01c80c00203c00300d0813584015040b5a101003c080104003240122800c406091084540c0c02000030305950100381d010000c0da02000483d500180c10005160700d40701720004104c00a000307528180154680c01500900354000c40d200b51000804a0705c000c18521050808030f8585810340d07165a074403200007446c0d800c1180d048141041c0d580c00140c001801600c2e8440c41d40d003580341c1c0b484035100d58082c003807004d807031a00442c0b61090400c2900000c0c0e40b00090601d08100700d50fa41c0c08040c1c1031103404e04500a402100403002d170708000c000080c0e290032500d04030036400c90302c2100310000401e0300301604010000c54a030409114240e0310f1001d041e8182c000708041500c0b401115420780d241142143c605c0a03251010b000c230341044444108028080b04d0f04205c00346629650003016483c2c104004003820070560032409a032201940760304141e00084003444092090030482c0c50768450b500400c1c0c00c1c0038010300081020742d40d076101807500c2d03540c0001d03200b0f055 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 396903839 1250 396902589 396902593
    0x6010b040605130f0824070c03081302030715140c0a060c030f090f0c1a0d0b031501091a060403110d050120040806091612020a15050a030f0606020d1b05 67
    0x750f910000720351903104a107000c41150141b140300580352a10307000c9290090082c0d13a954240100c0343d4504840f10300d00504001d4118031504151f07800b50782c0800401024003044420300960700c40d1808060b0007008a042610b840ccd00c0f0521002e0b001940204504180680284010030004401e18088005111000201940d649040a42001d00c000359250010f0944142c940c0400c0c26100e035201d40c28044800c041c556183c10411102c1c1480070180c200740c0b5649070140480c1d141c8682c1006031409000260064100c0f190303a03116120030b200f264000951007035801d440c0ca0340f134181103484907035411000c4140320f80500d10b80990b407810003400b54001701c00350847d83d429420040d06082d00105944c441d00c1030400071303c00c201c0480c029007000300d28844c40d52080d6070b9181d640391401007038100c503c14004050b6484154480f001076950341611003004060700c00d646032661844c0f8150040c1c100c1e40c030009400c011906e004001e11155400080610b40c18403241003940011075040f032080461156400010028 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 396905089 1250 396903839 396903869
    0x81e060106090b070c1d190204080a06090204110f07031b080d1e05180601080c0616082701030e06010602120d0618060305060708041a041a072006010b04060513 70
    0x1039980e8040a010740c0c00361509052120207c0c03120f00c16801240a60095600f002c903601d80017079040d90010a00034070140c00440c0d0141d00244400e1584c0103010100103100b00000c002041540c8110f4228000150305821403030b0014584841c1c00ca4000c150100a9072552004640341c1c080940349068440d4080715024440c610b071854000d00d1003e20211018010310a8a0021915000200740e0742c1c0d8031980a0021420705100b5084503000c1403400d0403c1c0ca40c2c1400f008074190100c4803c100e5100e00f07402c80c2d240584100004001030803107404c022000039641150005000c0d1585c042805910482d090080315215105a091200100400d500500c815202175080104202041c0c0044007240c0c040c03415a0016134034200142c914101c100e8000702030508001c0e078000c0c200814402c598000303004480c418030900990f5840c0c00c581105585200114182c8081019000d130401d541c26158443c0601420f140e51608041200d540038038058a810302c1404141c103105000005164001040044442c0540d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 396906339 1250 396905089 396905129
    0x5090a03080a030e0f030901050a0c05010c050414030d0e0108090c0a030c060e0303070309030803100b1206030d020a151a100816030c02190305090307081e060106090b070c 75
    0x40342e4064000a8003290800c80280a60b4402041c00b54121005d072029600c0c241902004503040d90003c0c04c40b000f40011200d01c440455001d120b84280c0c0180c0f91150356032a0308001901f803215a0034a150307031007503001001c5d01038059446500300e02030100c21308042c402ea40768850f1a5040c0070401001c581c10807114440042444541c00c071104c2190065260240030301e607030310185500c900c6115000b5000c2001d502c820800541020011540000503642032047c06803038403015030b456401554001c1510590b2402d00440c2d02d41445140100245800100100100b0355203101c2c2001104446007a001c3e0340d9000111980952201010f03054001001da1070404a135040280421400f952a090010320324030500d2000790103481380046c14459500286200441c454180c88140403400045041110038426400c0302d440401485028004080c0600544100240311181a02c406441401140c0c003001c010420182c02003c164155201b02540035039400250500150781700d1180c1c03140202003800c101c070001b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 396907589 1250 396906339 396906353
    0x1509021012062705150d0f0510060305010906060801150b0f070f0b181516020a06060902040302130216020915060d060509070f08060f01030b120c0a0b03010f051005090a03 75
    0x8040d1070300f0004201c1604d609109154030304002c001942c02c075640030390b004041a105100702c1e000b07038854000c0315403020b0060701c0503042c2d846503030040b1016911035440800b04400c600403c0c010305100da000700802001030901d819001c50920403d01090000549041d5401c5030000300c800b540d0304a44003000c544102c0c40c000807440c004036103103621403891005103c2100c101080c0200083e14130002d804158840e0310f42a42d0741c0c40c0f603a1200055206210b01340d000601140104802406c802c000141c9403455401400010100400a00083c80c81000746e0500f040040044003211038040d580c001151742d4210219400e001c600c2170302507005001180b9904c0f00c40a5030000d400751002034a6600741615404010703a030020341e103500d10300810310060020304c071404c00c1d484120101d03505240201e020f9035164041088132604844801e619005a0710080203402d25002100c000c0080c444101c0c955172402a88100e40e0061307006040c41032400f03100c100000c91260040d191591001072681c507070140d40f884c04203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 396908839 1250 396907589 396907649
    0xb03060c0c0616210e06011715010515030718090f11070201020601050427110f01110d050f040302120105061e0a0b070c0b0a020a150902101206 63
    0x100d907110b054002031298041d040250351025403600d803825007110f596030b1482c4016040e501180c000342d03a180d0010440800b00151402000c0f500c0314102050615401142403101101c2071082c0040a00010042611b0b101075070030910305107101c52602c1b502c0c0d4a00403592a4022803649403080e540d41004074001c20349034860040422680d004000c03408001d104441240185072010b405604807034010030903030406030451f903009600c1002c040a9107481c01d03018020b0208222041c2c1c2c4095800c0c4d8003000b2070420416100b040442400c0400361a81120f003159034a143d2104640204a004100d1006928070a01500c000d140e0041541f000091041011802080210f8050f88195469411295140000d201c040c20740c0c0300140a81e0700c6582060020710041d40031250807101040811700000c0c0d8000c280c4041d12042c242a40900401c000a044c0305072845222095591264500281000140c0d00d0800c00c0001c9070003400e00d1008900410780c7c86000303005580c0b105009944442c0135058009a0320601 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 396910089 1250 396908839 396908857
    0x10b071704092702090a0c0e04020a1709031207050c07030606120b0a0213060e0d0609141002042412110a1b020f0d06091e2603010b0d0b03060c 63
    0x109110742003005003c401203000180d0814a02400b144040d030b0940c02120440f0740500b40184041080c001203000c9034003041e0844000b8610400024080d108040070036044003060000318103003a504240d5002c042000b4000d8800d0160028007107800c07280600000f401141c0041c2c0c00c1042d60f5890b5011002c4500c0008100c1d51154060b0015424041ea44280d512201c140d6464081b610708116044e200c0c0500c2003480703903004200752410400070f0140d0095141052281110142021010340c0d40f0340340444c092a80e840041c0184401c2c80560541d0000d00441803400300e8108140c0b0803a4030a603a40d001e500c1c040b420003424480307d000398809000042c2800406a600c01b042210318940f030010521015800960281021802d007545142a14401020b60300890000800c5c00c8182d0390700c0210001248034281da1421450800c080c402c6042e25502c100300000c0e542c0f0b81024402c0b03c0d541181c40140941e46201d00e003c42c00c141840031540c8203200003640602100c8142c10b0182561900e50050240 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 396911339 1250 396910089 396910121
    0x3070b04080105100609090903050702090a02210c0d051503060405010b01090503070509010b07170d0c030c030b01020601031e0611031b180103050c1908040203010506010215010b07170409 82
    0x4503016203003c4064a04440c0c036586c40e40e8645050400000251128103006e400f042001e008510140c3d032014200b5004220202005a440031800b020101461010384981d110110b28410403c011506400b180c00e25461400000341a83d10030b030f50103620744000403095401d845600100010030805502c102e11481098032272070345480d5100105980c800707490181070b801200c010010848207404e003018055281c4200790080c00700c40d07100d081a03915001912240280c80d142c07290100c00d2901803248820604d40e038982032240d0442000041e50307403041848018043c00040d11590b02e0850055001c81c0841c2c2e00c0013051014109600c0c0601c5581c000307442c0c868045c2c4481e407948000010600440e1082081b806100c410030340c20000640003040b0007003110150b544104641410510403d0301440d101c3e10079121982103090500502d421901c008001c607040d07610081000c84140c0b110f0151304c0c1100c52410b001c80e9590664540b00600c0710142690342c144000100c0c003c5043c01c000c0d000141c0384002c0c607131 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 396912589 1250 396911339 396911341
    0x13080c071e030f06020c25180204120b07030e03160b0915010909020f0901060203030406061a0d0905010626010c02010c05030c090a1802130f0b03061201090203070b04080105 76
    0x256500071103501e00c00181841e101d00d500000080184c3c000d49580c66400d000d58150b03900a002c07106100c107000d80100b143d070114620500c0050800b0000c0c04074802000800c6082c11b05011142d008000350582c00b9150680c2940021819440b036003255000d100d00d0800d498983e14600302d004444660041304482004040002582402000801c41d00e9500c43c81c42c0c6614691800c41288024520b48000766042034040e0010035060701c54008041c000d04150740295aa0b01d80790a040c01201c05d41d412082c01d90400ea00c40041c0407100310280e912021b01e45000290000107864a580101150351015110031080401c0e0381000856500b810b0400359000c0c003c0c450b2640480080f801ca44443e0301c10004510140081420508000050300c16214041c02c080c10460300c4003015941d8001000c0040b80d07503500000d488000303270f4001b0800d40c000c4c4611210104480d081c100750010600005101501540c0b01e0020000074540942151003aa40c014068481c0740c0c1d100c0320036099543c81406040300641c00c2034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 396913839 1250 396912589 396912629
    0xe0706030605030604030c0209070c020904030e091302280906150206090313030b062404061103070213050c19020a0c0501020d080a0c120e01141006080105040513080c07 74
    0x1181d2a8405d5a041e5210500c0e9030041d070820580e41d00c090f00001c1000120140c0c0130040c1c8500014500a6000b52603207000c81d0158801c01c00700c030b04020908020514000e110000586886007040c1501c2e49075034036401000410703850113200300c07030f194405a403c606040000500545d900c12031381e5410495401d40b02c159407450000c0307940b8401c03000342071002c0d040070b103040020644c50b400c0d158002030010a440034100e40121285d101072140c420f055001c0300001020031089401502007246114140003031800d140498001980b02c0400141d001d209503144c40c002100e03102120110740d0105401c204c0d01810365244607000750782d072000c10740485031082c0100b4041541d41c000201c1c039400f0039590344c5410155a8240100002c0c100e203510910078804d440102c84a0310384103000c0d0f0900c0d40c078004000265100101d9a43e0f40100b0007a144080c801c2c9941c2060010b2076205080505440b42501c0210310f03a2201001c0c100340380007010b0041c01a5501050900b80c10f140401c480c01190741e103038141802981c5030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 396915089 1250 396913839 396913843
    0x706050c03150f01140a0f0206060a060504050405091c050a0305060d20010516050312010e0601081308070c030f11030c031f1b0903031b020d030c060605040e070603060503 75
    0x40c0c8040e9001107041c2c1c1d0030340301c501e040c2252022444040c546030100302062004c560305500030903140c0d408102c10b1145030740c2c4147e04111060b40b100b81100c3d1703407074010302d0f280c009012486030b40100d0303000f540c6500000310900310821802d2071b50f20028224005d00d054800000707215400c4031a0040010307081038040f9040b072401c8005c8480c034503080700345001140c107880d03840040481400304240c11700c01d060140e010381c4607541000104243c010707005540e030780d070040c4401060345505030840100e0550309024031082e031f6801080380e607000c2c00c100708101445500d802e00c1781c00c074094a0401040101a81008002c100041015003c003d1003129401108591081010340754940c0075001c5416504c240b45540b407412010301e0a0a43e00c06203000041c2e505d511a02a47c51180e1649010f0b02155803a82c0c104201944201980e61040c02050402244501507002940300c030b500c003030302404000d071210b034080910a041c2d012400900d0010300410900b1903285040c0d444440078440d20011a1619000148038200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 396916339 1250 396915089 396915091
    0xa0c0f050f1c03030b090c070209130f03050703140409020a110d0206060f040e0102043b06062a011e050f06040e070b13030b060d032102070510020706050c03 69
    0x40100b150032004815101e00565034880c82c0c0660405450b0b022050154aa40c41494003512599442660340e8843c4c0c010310440c484060088001c003d5110020408543d400e000244d085904d882c046a85035080c2c10216240484005281c0702001d000400044000c00780d80100398424503515031940900d103803100c0b551240e50301080c0c00050307045040018070b103251803010b441f52100014400204000011030003422a08a1b0300003600481209121113076034100040440901d118640c030708895100c0e000c0400341e640740301a120501030400410180c40240409026804418a4914000c41040300d5084940a4070a201400d0100c42c41c0742900d0820300014004e83c0e1060004030340c82c01b156200c1c1d609100041080c0c40d5a600e01740250400841d107030360600001c0940e400001c044820050840c1040ca000f01e034090003051151011000c0d120001c2d0f0003580c07003009103900390848000c803e0b02c800303044040e21600600600500a14480d010341000e2540900415030291400b00318980c0d4a11403001c0030b03c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 396917589 1250 396916339 396916369
    0x30c0705060d0e100f0e030a0c0b06041b120e0304060804080a030b0d0f1109070f080907050d03050301150f022e02181f0e150403050a0c0f05 62
    0x116840500290908000402c405034040c5030000750340c0d5a03007903440c1c00d00e40308500390400540c507004242003810050203003070901300802000d1803815050f400c0292110040000003091454103a0001d2069511544880914090790342c03d00c420959a010061803110304c012071300d001d2490310000b44010172002050b202520100e03181c12401d5140d0b501c2c0c000d080d030001d003036030b904260312240030142c2c41d120715032040800e41c0700b20440074840d034591400010b4201d000d0321340c5001d03140040401000c964001c409003408038160403e000e00780c8504a1450070080c07160011600700c80c46100800405038444025812241190f01040d0b03800d02c0c040080b5455a81941e82038010303407028100c034120074600303804021031a0f0301c0c030b61528400003607000d540e06a0304500c0c18101c60300026003402910381080c43d51311062007001c0c190f046410350340c14030281c6a0565000d00d03c0c05085112a100c04402038582240c01a60308a02100c1c00c44400d4600b5203900c6006009810543d200c01c0707800112070030101c0213654806c0d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 396918839 1250 396917589 396917593
    0x2030f011a0d05010e0f0d0f1e031a10020307060b0d0803040201080a0b0d030f0806010903020604090903020c030303090d090807151103130623120411010513060305010e060102030c 79
    0x10080001c00c5201d00c1003990030780d9155a65a14080170080421509110b140c140c80901702a080589002c0c11940c3c26406400520540845c101e0944890030300030300c00b1b0503041c1800103082440352808a05031201d40750240d00514492030008501c0d0b000400751a550b840f40a00f8008040d51806014100680030402400c0c840c0034008240191301070b00b040369101c50364510002c0c0e40c200320301c0050400c00707500b441640440c800e10708803e0702c13640c040412a8400740030300301603038610315650100d0310344d101e54421a040b29665600d09410513200703005080040b48000c0c21682c03681030604006458402a590403000301c0d011840000b803261002c01c0310000c40320610b02e40d2500791203146003602c854064100c42c0f0080d020422070305400c800c000c000300300a000d140e6185e1205038002120440c1d050103200c00540d07402c0c024440300c912803401031111035002c5d60000003101c09100160040e1a0ba01440c28440003002e140c0602140b001e0f89a4001812120040c500203c6919440c0c0107a132a4403034580e00306c002e9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 396920089 1250 396918839 396918881
    0x409110c1b06130308070b01080c1e011103070b010914090a060b01032309061311060901020a170309060601050c1b0105040f08011505270a0207060204030b0402030f01 73
    0xa1a84a20740c241100c0203405180b40c4003003050400c0c5800c4294108a80282d4003168000034820821403590141482c4130003400c9240c2140c00281114200c12801080691345d00010405644030b030301a65251808542102d0301c80c1c2c403901d4640c0340c14a0034020020035503d4103111050034683c0c024943d00940400c0c01605592181d03448800207460152070050505407a40030814154440540c2c181400709036211994950030150116410010094a03d16040c003910311f1000106075402500903c0d45070403500d841d501c01c07aa90041c3d09003410000094001c0340001d260741c1402554200175032082c00e4010940308955140d80043d0b5140c0a460f0810449074412801e24042e00c00020071400741640504110381482e50741c4140603980e00140d0442840342c7d446000110102009041d660301034002101d0304010110151850003161919882c0d118180d00b1500c003154640f41c0540c121000f064000000755590383c0c403400c24003500101510128001c0c45034480030005a01c062040f01418070300d10b8034100780 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 396921339 1250 396920089 396920113
    0x50304030c0b040c150c0309060810051e0904080c0d02030a0c14150c0c06100605030f0a021303080307080a090b361507020607020c0409050a0c0303050409110c 70
    0x3003a9000f042151429100400420b103a1810480c012500070540c0d24525692030320700d40100840c903954818810301c640101403011146020807104140c1e142514500380d005d100b0540d04140c40c48100c80290021804810f0005110b00c407001420148160821520494000f09089a0303d100740611000050301940051000801082207440c1105050f0f00b00d5812501c024010f420054040d02c3c1c81e007952000291001c50043c091150551110208a100d02c400d807900780c000c2d1083c40024140d69160034100002801c22074a80c0c140d980a01254004269150710707480c3c801450391058842801040b400c60001e6003c0d10640520490954000c0e01013035261035010480100d0310444041c0200300144402200341a02c6032855000c10242c010000c20440c80f211603d400380e80d2000d082601150070103801c000d41184c00007140c00444005940014185246041642c1490f02c0140000c0009103109400001d0542c040b01403c00e441a0f00c400b000620a454900d185510610169940d0364100c1d07459110 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 396922589 1250 396921339 396921353
    0xf02070e1005010c03020c041a0a14060901050703020a08070f0b0105120d110a02130507090501020a110d1a0405010b1c0b0c0306040603050a050f16080a0b1b1c0c050304030c 76
    0x120f14400d004031031709481d5030300c000340c04d80c1c0001c483c1d180c1040c40644100927500e03200c495140107200e074103008a5600c912002095041c42610b5583c1c1c180100014040c040603c20088200e00c59000042540c072002c4903e000426450303505802c4c0c2e2104aa4030000c1348514101c0c218001246414004010f0000980f105440b0700b040c46020071340e02d004001408000d80c6036515034007041032404130700040728a84210040d100b001660410340c1158040d0310704200240042014821030901110104181085490103600c00d0b544440c18540c200705140621003000b00c15000741e1a141000c540d0a0243d05581c41120108075803590054039031001d10000c1158000c80400540d048000544003150041d180d4640c0d5141103040b040c11615a84085c038460324164080c00288014070b04072135599045071070008100e13501c1c11595006460a0003440100300b010034000520510002c0075101903865007415442911803104400081200c00c0c00d1100c0c0310180d03849081200c0c170a50707140c0c59600900900da00c5110f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 396923839 1250 396922589 396922607
    0x120a060e070b0d0b03010c030207020d0602090d06020a02010b0102060f131b050d05070e13021f0c1202160902030c03160e043e09040b0f09070f02070e100501 69
    0x1500c1400740070301c0400c4480e80c1d84020900c11501c80008142002c01e0003d140c03c440c90600000201403040c0009070069403600d5003c1c10440c0c00c460056160540c03507000502d40b0000f144014442480000ca2805403601900a84101c8100341c0a03221160350b00c6e403000c618241e0840720b4180017039050040900043d600001c0070042060015420045038440b03000c1500c5040d5224191440c0c0d001180c10014420305200d4035600164a003100f10041c040780c1e000c18040800001c40c41c0c50024031242d510391162098040000150300110420000304550401946841c81060100d0b0381c62421400410110034900840707001d191026a01c91075a5a41e40413180701100c601c40e24000c12240c9100f05032507540d180290142c003010b5001c401050550401c001410210b44201070301100b12001c1c0d6420034038503072425143e89071419034003c580e0080120015010101c44440c0039440800c03c000e0004082d0700210300b240790784143d0221001e154482020b140083c0086940c0d0040d110200c10501240d44142d94203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 396925089 1250 396923839 396923861
    0x80106120f06030203030c06010f1401090b09041e050106020709051e090715050301090b01020f060c0a050f070b1b120105100c0614060301150f0308070f02090106020105090606120a06 80
    0x207905480c4d500180c1190311003400944690701503401404810580c0c04208010701080902916000c040d80000c2c040c070499100d0f4400c0a00081030010454032030fa0010a90103042d0b054121280c0b1981040340700424003806083c1c01481064000b15146481d0302c119409880e40010803144800d910781e1424141c20300038101400f60003000c00025400c107101035210b034203000e039450342c64072903040c8100c03103007150003560596046601c000f400302d2142c14085642a000740c0c0309008075607241c91100341503032140705403985c01c0491000010088103100f8100300003402002004070b8028548911104051540500d05441080404400042045103071a00c00032082030b40304d051039204ca201301e848442c1124440c1007400c084c00340b041c1c2004070a03e000e118201011f031040031003040c030504002c0e146c80c01c8400360000400e50300d40090014180400c1440451600e54010322004056840f06030081c064602501e841d1414815080410007501d041002c010f041402da00041122912a48550000c2e1041c03180c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 396926339 1250 396925089 396925091
    0xf060f02090f0d03050c030307050403030e06070803070f031b021f1b0c0302010f092613060e0307050301050916050a06050d150824100b070312060b0406110c01080106120f 75
    0x401400301b102440914480e5801741ca070603071a58030350304000e07001c01d981c810304a1140100300700007000956507070f05498001c020352400f01a90b00030300d44282d0003001004200c4400782d2552442c425034560004552a500d0705001a817403188410101c90415541c01030f40b40e03800700c8008100410310501c00e100e804c9100d4080d10000c00d47c2c9000d900307044101c40c01302c80f0a844d00c1090f0302d9019510b0058141c3c400303002d0440403640d07140660170703501000001c9007030040100b048026942410547e400700149009848020000c114900385000102d0b91040d01d441038074a00d400707400c000602442c001c0d0302c1000b120040c2d204d00b4501249101d10b400105210305140b44d20010504c408226040100480262212103c590388807400410360344120100c4001e004d0f84082e80451414070081c00c010080e40c0d0055814100900200c000440c0d85010300444d8110501d00400828001002d075440550003900d02002410303510000c2001c0011603141e41e0034051200815402c0d80124940034007984005800b09101e40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 396927589 1250 396926339 396926347
    0x1305060708040e0a051e0402030304050f031f02091002030f040e0606160803180a1115040314011b0f09050f0301111c060e04030e0915030a0f060f02090f0d0305 70
    0x200300344181c1e03000c1c0c401d00021a030710420002d44616002106d00c0e413400100c800c24441c9000d50002e59a80305600a05000f000241c00600e2245c90801c042030340c88a04410514403084080500340081d00b114400382d200d078020415061101c4c2c00031040700c124802203d045890941004810003104101501140e0060010800e4140c0c81c80e4502c0c540d200e00d0300c50309a45070b403400d100130282d0844144411301d0440b50030092040340001e0320180c0440042c0e00545c0c21542d090302c2e180c03400c922402617600150464107841d900115410040d40414039800ea5043c240303018140c8000103c554041003000715012400609043c401413611003180d19800000400104947c1000c89a5041e6500804003418220340f07805128481844d05005800290043c420010283d1820b034800a1404030704000303050241d414000414190410884458000e4030301400720f0303c998800e440c1070030381400a24002d40b5003628120031032004200700e008945038010010440706400c0300340f900300500364002820071400e000c8104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 396928839 1250 396927589 396927599
    0x106050901110a0609120e031b030a230d0503041e0602090604060302030f0108010e0d030915060b1e03070906050f0c011404051009080d1a060f07050c06130506070804 73
    0x4000004c3c070611010404213550311300010000c802c050f0050a104251042c41215240010f0381105402e584240400b50103501c00480c0c2090320f0b14202504144503041240307010100942445062442d0788121018441014411945400283e0f40146146450303a02003004080c0581112a4103004460052a0000c500700040d4154859482840441e40100400c240741e50740312016801000d442d00203109080450040e95155038403402110181581c45511406002a442c7d142100c200303050010084584c660740c000c0c04941201031840c0041e001005603c03006140c3c41e003564010754454950804071410b00310305543e19000010800d07484d0005210340c25644c542401145114005000c0920317050500c3e06215041020b00b502030902c05041080301d4000030484001c8604902c0c0d003030f074006400d002c181424160060410600c540c484400704e983c6075a4400d550044c200c59105004607140017014405010041c0038001c1c8030800b03c4180f0108202c00d0502c00010302e40700e4403605443d4a42903c40c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 396930089 1250 396928839 396928843
    0x61e0111030d0f0501050a140d29090c01021b15070501061e06031b03110904050114040b0109050a0b1c1803030612020931050f0d05040b03010605090111 67
    0x20240110800d4944801c00003021181c4500c5024200640320840b01038203148d01c1c01d5824070030a180c0380c020100013032441c0920444100054544541c01c0c210a8401030907581003e100805466190345800f41039400c55856000044445184044480800e804000002000790500da042e0f0010030000c420848000052020720603c40940001c40b411401004006a205650321190300180149440d02c500d80c0340c41944071040d440340200320f14020400e081c0d2211084694020700340360075009030401001168581e041c10322059a20816034040020140d844c0c01100e002c5a14800e968110035150028403548007000c0080004001e0600d5034401101404990b23800c403241c4c1c1810311404071400d0071460815900d80207610081c200000e80e68480c0d40340d500054030442000d003e000c007514020005441ca1046102070b08181040c0c001c041040c081c95041050301d07070748462940d2030079000716140c90006034000e0080d9025510704400c82c500316824410203582c0c9602a811550600001c841c01e44089941 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 396931339 1250 396930089 396930097
    0x60105090a23010c0b0109050c1b1e010204050a09050a06050d0b091c272607240305060418060f0617030d05040c1a03010f080303061e011103 62
    0x180300e00c4a20704095418200900d140b5030002d040051412400001c10031240e016815102c1c2e017080091280caa41048041500c100d0400414184030700c0c6825002b084040b41c41c0c3d0110201180010748000384c4a00c0c01d080b0701c074038000c40d40e004160302c4051000511507440541d1201c00104000348440d152000100641c0303811100322011030810b0704114404800740aa1841e81c40f510001040360f048460300981102228585030000c508142c0300d000340c508114120100030900c081d45102c0d00000f00c3d0400c1c8081c0c1000030304901620600314000740c2ca0020052400b403502c940b11280b00d2143c8032401c110b01a24010b000641d11a40711200d0300911600002c81c041d4082c0700302c000050754801c1e003070b0b0f44d07059442d140c2c0306e40120701c02d4100c400301600d0040116580400101c03070015065441c0c0c6000c07038280310311b9080a14000c0c0000300210300802c4d14002541a500e010703945c01321302c540d5a05950780d07070b1004a074240e8102039150301154a07038105400d0050b1348441410013001c10070301215040e20f136400c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 396932589 1250 396931339 396931349
    0x408010203090f010b010215060f150c0c041b0206130606031a0603010b090906070507080d050c090102060c0a0c060c031b03020307030605030307020a030b060d050a0303050a052203030203060105090a 87
    0x1514480f4042002440740400c40741c0b080c006496101002c0c1203143d421040149003900415112291588559489500c6882d05000b900c4142e20381c80e41d01100e903501d40180340041d00031854222100e4140c07580701c0140440e00000d07401040b441d03981c420b015400054050041b40d8140d200c0001000082c03822141d100c1314080d0b503040064500e480740c100341c252803095402a004154410502c031101c2800315901d079100580b400d20359030b2203605182021081c407231a02c00015030342c03502e003e1042c8030584d203008011f0280e090b4202c94072a190300380c102105110b4409800f020402c60402400007455a40024541d01c189043c0060310f00c452081d40c480d900506190341000030703030000801040f82d400d403107030301c000c0c140c1980154203001859002c035084002c240006001c90035a400050559521403070b501c1425903110702a1807040d1803901d0050064076041e1000580305040c00700240f10f15041c8074100300e101c2c00031504079001c0b540c00c0d1020b800a50000e4004c1d8100a802c000140954858401146c0241 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 396933839 1250 396932589 396932593
    0x50901140301031b090504050c0f13091505010803030106020c0f010302040803070605040516060509131d032701050901030b0303130b0403060f1401090b010c0b07020318060408190206040801020309 86
    0x400884240a002d51301074118250481c5884144804520001117504400c6810b86d0000700648241e030018580700d0385488296280d03030070908a0401c00c410018035400310256601c1c1407096988502041c1d0300c0740002d000300c1005901000e9210058945080d45940c01d201c10b0400624003074841204500750b6000c18001d0b1800c58681c41031008000080003110102d0408441d00840d0f40c1c20000d00518510911100341d12614181c20021703411105680000481501c0260381800c60070300c8003110751250411407000307000000c13031030146003040348110100f046043c059503680c1c58090101e0040d0700030410842e605805110500c01100c42082c83c001480c00b6107007185155844901e0b503e048000c1d54103010405142904003849040315a030200707000750560321010004500c80802e00d0049440503505c0401030404483d09052007032841d0044014940748003e003948943e05d907080c10a02080340715a00c9408540d5010103128410300700403c04c40e04100d44010405860140c0c0c848030942a6001550360000c26 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 396935089 1250 396933839 396933863
    0x8121c050a2a0504031419030804030207080111070605190f0603060515010509090c07020d110915060f1e070303140117060402060d0e25050409050d05090114030103 72
    0x5402082041c0951526000700502c6500d04500010102e000e98840100034100303458910010305402d009103201e0318000000c021032580b84e0f0600030090351054500b0390160240000c0410442c0c010b004200c5d03140d031000441454100542c2c1c8820041000810510520301503405084400703040e80129290480d0b94080400c229096013030000031190302522a01c22044400041e034003590f000007d8170000741c000ca50003001030351140010704191042000081d40303d05111040f0003042800409400d02e25401d40340c15200d5a12902c6641e940c0c50889111039110b00d05020701d5442c40c410358002c1c003140c01c0c500c6403100800944194440e072600240c43c00c8010a80340c222100c0042020f0118500414103603081b10410007010200b00d4503117102800180c0510000202010055507507041140709282c0b660403a00d10122801006002d02c0e40366051000c0c0c03003080f40700015207181034000c030040b05d504240074001e440512a01564540d000c5070070301d41405881500380c00000c216002843c02180545802070320 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 396936339 1250 396935089 396935111
    0x5060d140a050d020d1d100309030c06050708040c05040203190b0a030b01080d141303111804050f0708030f0909150915090a0c0507020d110d060e1608121c050a 70
    0x51844031005080c00c402e40ea1b410515241d941400c6220002040d00b0001a00d4210f400c04a07007100307072124007900445c10041413010f010342c01903005209a00a0381c102081039152020001a48019140d003180301d00301b21500342c007840465102520340e0000800c644e851982e80d03683c00040c008264030000d00c0b500810407842c15079401c50b52004400e1030454003140390520070200324003450107500010303103101401c40b1498816120405c00202d51505040c19807a5440c0034648190717600d42e010202842c80c0103413000010010307000010381d00c280700c041c1c01340e5007003800c0c000912244060090520100b18060141000c403611040b2172a40034034036500303222410200c8001030002c028005040a0a100e1512003030316405039001c0161544c0c5541140d4402c40401e01d4249079000040d00d40703145900032601c0600c5e03401c2210a0340f265400c0d180420a441c2420004104070506000512454149400503a440e00c080001540140f954100480082d62800700c048158811540226240c02200c1c0d55030b008504 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 396937589 1250 396936339 396936347
    0x4050d03060503120307050d0912020d080709120c030210110f070302010909050601181202031006050a060c0311060f09060f04120c05010905010e1f05060d140a050d020d 74
    0x810500608003803048601d85004265540c3e00101c1800ba440da010022031130081c415401c07100c8248800300144a5030b581410089560300c101c94818001d84122540d0551250040200303511940309915030507512442c108040c600381d160708108039940742a9541c0400146e85001194191040d40d039144501041280821441c00000c0c102c41131301c0d9406400f00f040140e074003030841e0041d40d10f55000462562901d20040e54401d404031030808100e007100401289480d4407103440b01076240201c0880719010030742c0b00c5910440e8039602400390000d901c50300500006008110300f003420391091512607008082004903a0500c1010390b8865640d81800b002d000c2001c1c401c03c03100b90000c020414001d1581490743d180c3c00b502500c4601c03101400403109035102404400c0d440359034481d4110000388013608500e0019621042148001c401d0110746041410301303540c1e580700e182e1040c803018140488081040d1148400c041400303100030010700c05c80051a0009505019082d40f108164004103c0e42100045c094 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 396938839 1250 396937589 396937603
    0x1e04210b0709081018050706030c141305041815020d050106030c0906260f06041d070315290102190209040b070c1406071e0f110c15030405 61
    0x310800200b12000d000450002ca00c40d5000140300d0000280a884145c10614500044c4006081030141d20000506c01d50107402c20030307040c035a603654036941c89545000c511440c0500c0c4110b91a504034107400313001d1410191300801085010111729802c5081594440e071441c1d8003501d085a20799000318071882c50890901516000d0500c90130240441c07052150010000c0d0740c5480b40d1010004290b00421407005070200240599803110030140091818507400c41d074855058400b180940d14146108002079049101d07110700b49003100141000620f15103488030b40154450300a20703420340d1190741718003c1038035484941c054000c2903440b14a010b144000a802d004100d0480c0e104031400f42032040050f5141960f060b0b2182d44001c000f03106442c0c035030046640d1481f10900800078803240080b801b0100c000600715102d1f5150b0ba48401c4140720000300d460144100007440004a5545c0c212180c1c00c2d0302600c1d50074182d0404004541031080d0380b10000d02a10210200302e0400f8400206110501000780912 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 396940089 1250 396938839 396938851
    0x613110109061e050904020c011505060405030a240906050601020c06030c090402031e0709170312180a05300703020316031e08190b061e04210b 63
    0x30203129440c01e41e024003191552032040d82d41e0141c211070061804d0048050307400c480801741085480b64809801c2038020440804407040c2c01500380000509441e20f28221f43c00c7c2ca8002d00a8410a00c4541e22250f828441c8240021020034081c3c1c588d21003c040d10901500600034a0080340c1828100b00190030100d0302074209000750020820041e0038421041200c06c0507200f50b070700503960380d260079001203c9845010541407124609050000907070f07008030404180c0b4030112034a01c810020300e00080e903d12075151204041c8200c0c00015003480d03034604400d860440d070001900c0002c119691f4503814256003080d041c114120f042190703039010600b44015012194442e9003e8a0450f281e24065581c1c015444006515807802100d0000c040c0702c3c02120300081c0c085040c10345a2102000c02501c440300440750041600043c0020200318070160080c1400c000d400b6100310318082a8400da907110075081c524241c10190100701c0000c43c2d4416040c584800d00391060314002d040c085242410f124640a0a1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 396941339 1250 396940089 396940097
    0x303060303110105240a09020d140c07020108040b1512030c0f070e060910091e2715110c0d020106060203041404020304150e060a0b03010603030206040b0705090306131101 75
    0xc2005074a841c0794030303484404401500301c503044510390001e94001c40b15004851701c1c5002149c5602260300c0c6400440c071041c2c10003e100915500e0184894085c02075800c0a40010403400c00300340403540c20603c590308420000c0124003107410380c1c00070410301911f064012038545d0001501240c014000d005c10303070160f8918000340c40c04514005003204051005800c6034820210080441c0c0c1d08092010000020110b0110030700101140d050075082043d548480115601c0c144524620190714000a80c2c00c1410180c40c100c40014140c4c403001d00c41070b034405a0510503581c62602d11030454018002d482015900d01c010b2464034840c502c004c1c20350f070090784010155070007840306014015200c26001d00c814070a039001038480d41c0c0c0c0e00f8110341201350700c1041361010f854003009900300d00c8041280c900c1007103400e0040c41780441000034135081300c400e480b0142c01a00318101060000d21b8a41495402c01641e01d84681008220700c00241071031406d44451807400c0c0300c240c0010400c050f101d01740c4025042400c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 396942446 1107 396941339 396941341
    0x5062115060604050d03030c0e03030403060504020a051f030216020a09090317130f0f061104030b2401050c07180b040b0a03080f031b070303060303110105 68
    0x21501140003180000941e56040c40c40840f412075502401e0700038540f425440480c02401d000b1880820004032040f011926541000a4800b45015007030008003420107204000000000c0d1b0b002e64029aa0a550070541e10210000c440b00d03005507050150340c03801c3d40c4129015801c0c0c2c42d0802503200030074a0021039010200e81c401422944a5291048203203c00300b00031603516030450300300102d12070005100e0b00003015408803154561246110003005070269540c04191120710035444240c80d0081010000e20146225a6400200c0b8499640860f12991200a8030002244500d4107101001a444080c00c00400441e4000c021000c4911407018030054010054010414078900c13844c00d1448545d0309160122102382182d5018440c207107031403182885008d658100510240da2100d00703a60111103140481d0061a00d18440e40d00091141d00f5850044d14924025050803507a0b85010 = true := by decide +kernel

theorem cover : BRFrame.Cov 396762589 396942446 := by
  have h0 := BRFrame.cov_init 396762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 396762589 ≤ n) (h2 : n < 396942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
