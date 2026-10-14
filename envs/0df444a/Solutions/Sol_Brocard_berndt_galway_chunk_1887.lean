-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1887
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:02:18.653071+00:00
-- url     : https://prove2.me/submissions/d45cb032-a953-4e8e-846b-214d471061a1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 339208633 ≤ n < 339388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 339209883 1250 339208633 339208651
    0xa0b0c032101082a01031d0102030426130302040f091406011409010e0f061503090303010f0509040c0b16080c0c0a0f18020a0915030606020609030a0816110303 70
    0x801d6241070101c3d41003030800d03142d0244900610780002e051a00060311804000800d0030009800400321003680700810362900000499880001071005000081610001800c9400115014180c00c40d42651803400b507000c1e1825401c410810500c01468260020b51a0410125001551008907101d1285c1c84460040760a100d401490043c8841500310750f100039030765000d0703825001c03035403400d807002070000c000803c40140490050701150b6a580c0f904032a203c414541030716281c507410b1510550340c1b80c3d40203100e2900c0060541c07200041070300340600d0452003150000c802043c0146000c0301112a64080004005e110b440d5003020130025013182c0c054080b42c00d1013401031000c00030040c1808141800c0b80c2041c4101500701c40200b1040301c990210502404807000056200c140350b09003540e0345641070704903d04031004400207601c12580f5500040481d03c85500310b46050711900d40c00340d280d01c9101000f400055548000500b090300040100161040c14a0400440c803044590070b421364105603803640c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 339211133 1250 339209883 339209947
    0x30d0903061e0c0914010c050618030c0d110c0405010b090904050c030f010203040c170307060f020909070f030606390206030414010b2d01270305120304020a0b0c03 72
    0x341408003041105c0044080c03c0542c84400103858096031150001c00341520140c5c01c1e450052040f6091060703032041c24198044030810848540080c054070f0040c1c04071400f82c03040300c460540300d00c0c2c18018181200c1038140c020f0700e0800460103100344800010f00c1030714588a6090f1404882c5c4003082610100038450340016200c1c10f140c50140100403199101c415129440d0b01c01c008408000b2044860741070f40304400051001c1441c0c8850003070b01850301e1031503003c00d180c2d041213440c5401400031b03a11001d0a41e4204041d41d1074507004d031034411440c081400c054040c10380c5200c1031f003294a0010000321301c02c65500f40481c041d600141d100d900480d400c840421040d0000d4045210034081d54013040740c00c80d01020a020022400e111001c0e81a00b0300c480c80c4580f40800095034014420240c0d000025006a01c02a1000c03404040307051b00d520040746c5074801c00356031102c082009010b0328000c0d0390040c00c010302d5902c1d10080303010b95003002511003d0be000c10080929500c040c000181c04a40180d50011 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 339212383 1250 339211133 339211139
    0xb0c0c0102010b030c1f09080118030305090106030309060f0306090f060f06020a1511070c0b180306191116120909090b062b0818030d0903061e0c09 65
    0x2400e450343c141da4203000b0740c8000c01c0e590107607454102d0040d044c00c1210301e00064409002c0b045640d440f880e40248039651a03d10058000c3c007000a0101c22540a0b440503c80307501c41c88080d600b205c56500c0041c000540501060043e144141c0082c40b06501f00e1401003800c9885582460445610501d5900076a070744134020014041c140001c00010007940c00174000e00c0c21203880da0340c0e001e541c818482410701d90b120b60100307032170f0a850195601540c104401003c000d81311070007510b07680d02c800c281c9040c030070b007041e810941807030009244c0748180e600b600c011076000b000140f048081e00c02d03a50605104041800300e8080d060300c40f120844140d018601c00b80e03c00e00440806462440e054005142c1d840c03c148024000c6030001d8140b1740c01c990150b9200111410503c00d02500e403402184400b0300f041001d20480605c060311025003d003c503004110100c0b00290340806076a0111202944c0218002d0302007000440d4141d4808070001d80359199032984402d22200400c2160307005444c0c1004201920018 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 339213633 1250 339212383 339212387
    0x20a110f01061a0a05040b070f06091b09180b041e110114030121020613090509010e01140f0402010e06030703020d060608090304030609020a0329090d091401090b0c0c01 74
    0xd407684503000741605281c013105441c010114070460080c103890041c0014407000700203203411242802c9800400800c10a000c074904a03105220001c103280110402100200352a091442140c0503092998400c080b03206940d80d0700925032000034021b60301c99480d413030110807400420042e0201c41c1d128a003104082a0003000141c00c0c0c43d881c520008500209100511507040b9816654001d40d0b1045104401d003100c3d48006002d40c41540c42c8858100b490300f400040c0d0801980020780982c200d80003d004121041114908071812a40076440c10300b00940071810b0214109140340d085070040c540358840c7c00d00c10020409940c4103842e03d0b0006540000d03185501103032403103080050b1810785001c9400d401e04c901030903502c0c041c60001a020300d43d250307003400440d9102c0f05003178021a4441044000039100303c502e40b5016080b407d4040303400c480c800c00682090360120f0140c2d49201e5607100d0610280c1402d020b0044442003035001418041e541201003404000c0d00060300204c440c980c000d200d012028400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 339214883 1250 339213633 339213659
    0x40503061006030f0b0d0b0402040f0c09080118020102061902070b28050c34060e0714010914030a140d0f0504050a171c05191b06020a110f0106 63
    0xc0102a501d0103007200d03450b58a00302e24020a80c0c00007c122510b41310ba00000b070081107018040c0e807611340b400b922400740a800910207401c8407407040c020841c1103447c2d00f02e990403a240501c000d0041e0000400190446800262110100b009420050521126075a0407095100680348860841008404051104010801000d50500c03800c010701203070410510b00300050048005099886414204003500d6505040107031061212400c1180003000050034007000a044921951805003d141004190712450100080d1005070680d2005030647c80c0125000c2148072502139154180a400705030030120b0111a106400412550060408803190b1400079041003401c401c40307814080c09000401990b516204100c0488803031003101080031070401d80003400c02500f08d40402c0c20041d452014926554448041d00c400c404902d1120780c20040b42c4401d5551130559001030001aa40840b200005441c41e0003512091282d810301030385d00308008c401c050502c0c2d80c103040b4000742e80d034035401004030b0801c0d280 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 339216133 1250 339214883 339214901
    0x30503030c280f27030b100815012705041a0603010b18060301110a020703031803050d0e040b04060305101422030e060d0b21030904050c04050306100603 67
    0x81550504041c02c0d40203403440110110403018424000c104444102805140e951010001c0c5400c0e2451a12450721075a451015500b2460b009408903010420080014298100b6401c4000e1019540e20f80f07104581550260140c00702d00100c0c2321001d440e40c0f0701a00519000d04d100d1903100d040314044682d10560b4541c014443d52007681070004401c3c558955101c0c11455000c0c1e800010065501c01e0301003405810114204120410009400440503601094020640c1d01c2941d410541e0484145184a40107513800040e1036600204469080b450050740c100c02d0f01d0768083c102058002c00c00c400141120001d0b0700645940d00600d0021041e50790320311810302504d40401c000107040c141100c031002064030030200c0300d0044240a07403801c2414003540031120501c40c020200d44e61201c4403980980684071240e14507000d260b8140000da01008140c21103103151000030003c504160104003000302a0001501c16003164104000100b00d82d10f0034005941f040e40710b00a201151854008001e003180c0c9040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 339217383 1250 339216133 339216187
    0x12020303070e040c050f09040e0303010b0a03060608040b010b03040c08070617010b16150902090c0a080f0f0a020a090306230f1315020d0e0f070506030405071e030503030c 75
    0x41c0101c61340e2600a4180e401d403070780f800c8015440c1c050301404100100b821103d11142807001100008240503c50000c00f0789180e44c3c1c1d42403004694451081c0d078400000c1e500200344002400051102e034038160b024540c41030150b1810710b0807541e556043c42c10413143d5082400010080c00c00c041000303141c5a05240108840081131f80740c0107800d2002600415500001003109600c201c25201d2151190030030030101c0d80060001c0503e0800e02080c009690000f8000400708211000240e102d95107110700c948035404504001c0c0fa150b44480d5844001d600002d12441840120322000c07000c1004c0784519040d10f040606910398203450642403180191008000702d0b21800034208200440c120389018000740c85d40002113440030041000500d01034020005280005443c04510101e42840082d800f80506143c1c815031308990b803079000707101c0b242c07104480203841d582c400d1b035040014030f140b540440c80c040c10701d22454101039143c1c2ea03000c0c02d40d032080c1d840c80b096000204072001c1d9040c0200305582d50340645 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 339218633 1250 339217383 339217391
    0x1f02150108060a0c020304090c0305011d0f041514040501050906060a151b0f050703030e120601030b1b0d1b05040302101d030304032414180a12020303070e04 69
    0x10509030760703082c004080e0826152039079025080c9074000c00598014000c0180213000d08510007900500400e03092042188030340c4895694441001490405402003546495a480300c0d540c0d0344442c40c001c03060071a1420000e940b09421038041100316007203405144102c00200395410020700c014034190300500010322604544008001404070030030500500d100c1d50400c0c0b00d05100c545200030440006440180150340c100c184038040000102d40142600d00c40e0319064000d160f401c0070b202c044800c5140407a240c0c1c0c890b40041c0041081400314660001c4ea0140c40104100584810380301900003014200710b00e901e0718204480e21000244202604842e4a030203402c1c10310310b800113100021034480f0603050044000c846207001c081e21841104004c0f0103402c50303035180d941c1d1614070706019a03420b104c040b44560144a02c041c2400380124818400c06005000c0b6980311040c07181a04800c245100615104e001d98181c0040c03e400f0000c6460300d0580c014585038905040e01400ca4407028211610941c64 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 339219883 1250 339218633 339218639
    0x170708070521160305131212020706140f0412050f06130804060305180d050d050606030402030c1002160e04110307030b0109020c0312010e07110303060a090b010203091f021501 77
    0x41c00b042d50920a0a040090b501c1d5145040079161481140800308072025508030120f024003095068110441c0301e8040440c01c145c464000f2a22449240916030002c3e100c0d0350812882060940a840f800a043c2e041d9840c19076189521a0003114494048070319421207030300c941580b83c040c060b8035841000c1181b83c903305403140d650171a65100700d005807001d065645020900361400201d9042c0000501004c4075049145030b50040d207190803241503040141d00b00700c0000c1d0307076003400742c148c0c1d00495016006003000c0000d01e04105c25450110071000451003206890110181000802402041c0f110000412400e207803d00351289540021940d00030b6000b89400c00c00100841582411078051150068440d030001e2000e44c00d520442001a0082c510040041800d01c0740c3d500041c0a02850b85646034405000b0305d505840c2e002c03c031120340c2d00007101101040481c0c0c443d00813100071001441902d20f00740c560000180c03140030710080f03800c203982111703035409501c1d40400106e0707001e420b044c54007091b640c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 339221133 1250 339219883 339219943
    0x2070b0618010e04080307030b030706110d031e020307050d0906020702040b0d02180c090306010803030601200607030b060f031512010209151b070e1006050c0c04091707080705 77
    0x15001e04000d007179070000000030300014865405003020210007015108210380d01ca1000780400f60400b242066405210340200e0032a0107442480900e4426141d02c0507050f0741c112002c0002e420040c0100103100c0100454449010745200c0c003500d9510410700161200c11030b0050000b101c0380d0110032030142d00d82401410259a0361405584045540750344140305540b0f1a070798130340d90b000304030f58107425200f500300200306408003001640c071643c0207a80d0f04040114030040c001180441c00aa0340c1107401202c0808c103441d200781c000180c0041c003c1c04682c40e0000e41c61061085500031100c1c1c0104802c0c3d04010012403411200c40031105030702600035820b0060500004449c0078100001d28032650380010004040b402a461201540001100740cae1081c0d030f503034490300000d04412950790740445224940070856902078130603070f103a21440c50020304031b07000110244401416650001d03103100c120228004c1c5100403c0000b000c1c40b1f07105030821515079035640340c001d2400380c0c12003400100310440300000b82188 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 339222383 1250 339221133 339221159
    0x50612040b06130908040509060a0303050d1107020a03050a17090f0919020301030c06020f0706051b16080a03091d2403010c0c0b1b09041104080102070b061801 70
    0x103030007440c055078944038100000d42002e07688000c080c40318140765240e018020700d140500b04648050303c0102e43c1e0707a100d00c2080800c140a0100502141081c400c99001d070249a100200030400c40c03444619124143d00000e081301140ea00031619580100b818008000d1029103c90100c000040c140d0b08100e80c14000500e030322502c5d44540d01444080740061900703420704144640300c21044008554a5031242025450090980030310f1001d84034445680c80d1a140000f00c00c801c40c0e40300e54980381840707803480c281403035100403c8100045205406c0b5082d880a81518040020101c29000380300460052801800c205225404004034040b030060603400d40216501380e0b940601030144110081c1c1d0001203104202c0c0c0c554018540540c40c2100c00320720300c1e400031102e1048034020640582c041c0c0d1140311111290149140600d8407140502490380e003824140c008000504140811904198a8013117013401c9800440c0300344c43c004441c1043c00b0050a00d10040d401078001c1015241496040004500800e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 339223633 1250 339222383 339222391
    0x201150609060e210303010503070e060607020d151a01030b041422050304060905040f020910050c0a0b0a0203010312020703081e0408010c0206060a0f060206061e0904050f07050612 79
    0xc0555881d4000b01550744c81d900b05015520b0309811030300c180c12500f225070369070002d01501d07010744180c840100351040e05460340392203003100410a070300c0d05405d5800d000d20660110350031110b07144000801007074060140124021055a40b00c0030507078454002c0010191030031402060b009601e440c25010001c107070b403106e2541c40501d4040c54501c000b20b03580000031a022207a0040e00d03500010501080c3d4076404105c4000721002150140b058182c212070107002c910691800b607502410b80003019001e14065030180c0001020401a24003566680c0c03112859017104403030043c402c9500100500801c0144501d4030f506a48034802011001c2c199aa401000d201d68840c5c58442074400026618084a41c0103c1d0041c020940080c0b00850f94100f010b0b50301c11003500c0d02c9200c2d00c20f544011483c20b02c051141c41c203d41d6140d00a0130030b515030000340300324031030042c00950254501c039880d0030441e00d62645c86c03801030344124001c03d403025066404509125154101c50f210740b60401c41c89805511406003c1c0e00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 339224883 1250 339223633 339223637
    0x612200105160818060f090312040b181207081e1519020405060703020a021302030c0a0c0606050a0b0406030c0206070f120b031902040f061a07050106081507020115060906 75
    0x14641c10400d007089850b04070200903034801c0f000541c6c2490100807602030324020105070304850040c00032200e1208280694040c2c03000c015401d11420000d0160f0503c020030040b8042d05400c0c020200c900c130f0604101c00ca40042d01154880c1c0020f92040c05507a841225454030030000e0411f0802c01500f109008201a1806501c4505183d00105000702030b07045400402c0000c0c00030b81e8070481450b0180d140d1440200a80c0324110804030b4140c086034a0003201c0c4203140702ca540b503150041d9183e045c0c030040900c07407013612543e94805012a642c1c0307540c88610b0203840c113800384985451403c00d00500b9205003000490840d0841c50038884100d0700855030074149001b40c1000c1d1442d16a40d45100c00074903070310801030f5040c4203550881c005580381000c290555402550140007121441e2001c2c41690114800c140801d10a80080c000340351900c0007034a541c0b4400c2001240c82599550722070f203820111075442031000f401c3c00500c405247c0903c9502e01c0003e05080da50301d807074903120380544044c4080c841c1d002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 339226133 1250 339224883 339224887
    0xf1b0b0f211e07120c030f0e07050105040b0d02070203010903020a140a110d0f200102010b090f0f040f08070b070f0c0c0902030c040801060b0c060618060409020406122001051608 78
    0x207512070103603802c0300740028603144c200030604403c0d01c000c018208481d00e152040b403900d600c01410440109a00056941c1a116075107014070301800110281c3c801c52207040c52550a0042c61b006030380a000c2c0d210114042e50081c100500c0ca070401c0c40140080d0146a6166405060700c4000108104107040112504583c0c02c40d145060742000085c440b15003000500e00e911202c411101b82507840900350094100380d00800c0540014401d0001d6500e090310b5004e6003d010000141c1e00041203207426a002d032044121545510302a5218a203a03040050708490301c041c3c1c9420042904d51211180c1070541c0030b0325141d0b40c580b0603034848041e651514002d0040468000001441c1c00c610341c1c00f1507000b8201fa1008000f0680e4603c0d0540c40c43d00074800c103080340e0058502007492864159460352780c020f00520703c075241e5200c031410000240104a01243c01a4985200040e0f007480c0c1d00c0d0200a660203075105010140500c00d41d4810328444444d46814480284076180130501810424079040341d004e03034655 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 339227383 1250 339226133 339226141
    0x14061f030f0e030c07030b1b030a0509011b0201020403061103130605071812020907020c0a06110a0c1d010806191503020607080a0207080304030f1b0b0f211e 69
    0x6005030801006502883c070000442c031468507400140d00080724061030384100151145a050312410392440a115401102440450144901c2d41d110310782029803640001703008154007040a80042d15006802c0240c0d50129081080c0b200c01c0c041c5540700407035240041c1c03452800e44030b040000010300c0000350029688000280589024a11120307464911038018816565200c450354195803503800708070b004000a6011841071400091078a00310440144401c03141c1d424203a04403840d0080c2d5210b005e180c45030360401c0c00490356101c007070405040b5000e407191a07d4040c00342c4005600d81a401040c90341e12180030010b03045074102c0e02c0090b03009001c4020a80b48034409000400c001d458001030341c0031304005880d900300300c8810000c0640b418180c00f5280500e80d41c130215500c9000390311001e0030702d0039204a444002101c2aa0480c00b11042118503003450b600c454841c9901d412580343c2c0c41d401500000ca803003902c015103111250884111210480503c1c0561a104043c4d4012941e03106061010b8042 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 339228633 1250 339227383 339227411
    0x308280516030c021914040203060306011710060603050115023705010614100306060207030609060e010e0d0e0a0b0d020a0c0f2117180a0c030614061f03 67
    0x1400307141c0d400800d006115180c01002511003aa00c6c81040f681000c410f421400505040c000e4078880c0c080103010b0700441e8a854983d03002a00c00e00100200c5010303d99200d0511405482414040c2010396070004066051070040710f02d49684030380c040c0c19540104c0d484840540046500030034518500c0d12a44c80c200b026602e8040001d2400f802002d6509214000c1266901d0403030900034010125036010481410240c150704440c01405600010707040b554052021907581d0300071089030391044000091280d80813040501b1501c11400100c4070742c204840340751000d40c2c042c2a505007180111501403804d403030030046e90b5440c4191000340240c02e8000c56012110340c044d90301c2e04007043e00100e1190301e0402d2407500701c4288070075501302110310050004204c04507105400b05402690107032403508503616010070285450300c80b403050303101d40d02c1801e6040001500c00141507000b94400d07400030461030603070005044c1555000b080140108200383c007807103031a2800d841424510f01310303090002d26400c101c020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 339229883 1250 339228633 339228647
    0x20909280b251103041205160509091203042102070f3311030a03020304050114070c03032708040806070c05071a07060603150507020c0d0b0c0d06030828051603 70
    0x11b010914902c41c3c81c0014000d01107203245218011521100b00c003038480040050009040d540c01c603040d40000d00d001c0b40c88482400854200e4000d040d1201a8241701e05890407550105050a006800a12081103090301c18140c1c94050003215192080841c3c0e40049036100b0300204034100d61420703000707441d03105150003158100c40405101c02542d65480c0c00c000c01801035403080d50122004d6190465004440d20100c0c2d140d40200520758038502d92424648040380a0201c1e818010402c1c1a80d59406802d040801c039440c2050b40b0a45030b058031913142000240c20040024004c5041c00f415908010000d540465440c0c2078608130000d090031a649901c10703402c00d0084100040c00c1504d041c40110030300104001d18140b4508000c0c060101c1c1e50744041c220b031188925100c0316000010a101c2000040f080d49226030b00c0880c0207101414074000c88140019107015170b2007a039020000240c86070303090202d140154020401040100f0807070700f1a50340200707a0b10500380d69100c03500d210f1580100305413040ca130f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 339231133 1250 339229883 339229889
    0x23160206180a17130e041502030f130507150f02061806040210210204030210090b0d0e0a080a271d060103020c070f150c0c03020909280b25110304 64
    0x40d01d01039988401210080440541b01590050100c019403242080035008880c07088000080703581144c0c0300c0e400100038401b08440b048600307001e070f600085410701400310a0388002c0341568078810a00000314010b0306140c405001754800c0c80600918040c1d102c40011520b801907410380b070700d42c0640209002220340014004207041070014600c94030720703024410b4014000343c90080303648075603050050406556240d403e1094400e80c501c240105104070b07106900c44040c0f450303200161500c200c001e50b03e0000b10307803118403e072f004240c0009030400700c13045a41e07190003c07450044015440604004188090040030502a040c2c003001d880052050392294040c0c1c1d840036062801caa0003d52076000c940080c0071540102040144001040042c0520445a1451468021043d908001e040d5000d0000560b401480004136101c0e00700c80d818006030414903426211100340c85800702d582a4500707094a0320000c0c0140450800110802c03c0d061090b80b0041000e0865042c200c00d5120341410141c218020b540c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 339232383 1250 339231133 339231157
    0x8090307080609030306011d0901060e0604091e140108030f09010c0203060f010e2d09070f030f0b0114060d09030905041118030106061223160206180a17 67
    0xb0180900320100002460007010709807030312160314092100c0518981c082025041d0700c40e40003401008054005d00c02601c02c40c1001e85180d2900c0d84400101c025500b00300100d88a188222141941c0c104081c896026041819915101e881d454204429680e000e0b201c41c119044200241c0f44000343c1c091030102c40b19030b50150588601d40340190717030040c22038024403c2c441981000000111040340e901d161024108294140300703400c09008072400c0c807003800217000500380c2c4241e0101083c08074940c00f414000710301c05c45d1400400e07607442ca0580391000c0180c1c09030307081d81d900b10707620b814a42d64581a901d000d0400200056000d00504007100c2c510ad05900003a0050b2508891540240da144006d0802d2605801051a0b00c00600103040c01c88015102d0080007902150b4030031001c2c181c41d005510302003103100e10802c92040103800c800c0008410b039046002d180d581a230041c0e10755014040154000d205001280c840251105110f0f100c403000348004005000a0b948034880003007901c15248041044 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 339233633 1250 339232383 339232393
    0x3010b090408030405250e09010b090405250609090b1f0c050105010b0f0f030a0f0f060e06040e07120218010f0e090729091203180d0f0809030708 64
    0x50510142d994015241950107004d0310400800e0b85020008202004000419100d003661a0884080680901910b604200d540310700818070140c0d20b42da0454051070040c006003502424a46800c2085d00f02c4070b01c454540c02807502e0411116410010880480d40114801301ea98480c0c0000a80040c1c14080c0c81d000c6510b4040740ca4580d43c0c0d2200810990b00c3c07044000700001c1c0d0322452001a0360040134030f40f07502c106c02042201e540e240c224000c0c64004003020000710314207900f1480d00064034041c0c9581c0c00300340d603191010003c2d0755203c18425040002510304000c0d80301810701ca035882c1e41080c007841988550009150045480d074030312940007400340d40118240b0f561a07244603400d1150030701c2003805248440020485004000c00c140741144d100409050f205200e8034001c0d0f040301e09644564820820601c200c185503140e24001c0000200180084c40d611841c051003008881c02a00111740074411608500c2c0c0000ca0101d07406468941000d81281c0b500001c60001e446c000c040c0c1c101c40868050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 339234883 1250 339233633 339233641
    0x70501060f18060509010b0f09100e040c0203030112060b0d0b010e0a18020d03110c04060909050715050a0e0d0f0c08060c0403050304091119020718140f07050f2805070309090b03010b09 81
    0x8003400f22f0707850020454060055075003030074080380e4901080c0a41c00d0106005105100002c1c05980004003851010f0104240f00e4020780302e0104443d0240c1c0440e403541e400030200260300003d4450360400b000140d540c5c4d40301306035940101e203408681d1003000f01480520401903142c00010803040b01d00d450014028081a0345400d60400a40740030103085a462003441408542c0c05243d9081080b01c2c5c3d21540c41d07034101070b100c44045452080356180c1d940c20002e0403e0040109000c01e10748250503004003100e10f60301c0d241ca141c540c0b500c90020640c040c4244180320902c000355002c0201c500312544500c0225001400c3c50100c004c81c4582100b01c01314400b02e1984090490b000302e03440d42203545a0040b03c01d24464495010156075050081c2d0b0041460038000030b4907600d17009032240d0000c2251400310b081005400700f001256000b401c60051a80540d10700e00c0e9445000702c42d003e030b5181c8a160480c100009642c02508980780c6000d14066161580307640006078800354001889204020070315045410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 339236133 1250 339234883 339234887
    0x121d0304030605010b090612060a090f0902190501020706210c02061014091306090b090c03070906030506061c020607111903020616030302070501060f18060509010b0f0910 75
    0x8018070044401605000001603100409070a403140700340003a016510349507090001c080701e90300052440360700008c250401b00e0200d880c3c0c444d8241d581d50200740001c90708128010040d04101e2100c0141d411020703c1c20038096030760701043d8401143c0d12400c00c502100e083c21103113516100300c42034402459180c1900029040d50006025008040c3c0b400703d076504c2a15030110303290b003d1394035541f15080521000420003200503038865510b0180201c0000a4040850350362804007031081d22040815803001803815000d10342445180b0042c4044101045074600d180e80b00703621420300510303983c49240d440c40741050030100c05052450300e80e80200070982d140700c43c0c54480d0015509000007070040c6501910040100c0340c02d50b014040d40d4008011038107009107500c40b444500e0004104804158092010400003242402010048e1104c03808480b102401d050242d0080248200881051410b05004114030349488445505556a1003980c90f600e2402041d240384900c43d4207519034000051082d0158015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 339237383 1250 339236133 339236137
    0x14030628110a08100b0c03091315030c18090224040b0f03070f020f0c0402030c0c010609090218010e040b060d080a090303021e25050a030302030705010b091303121d03 73
    0x1464a40800207081d4844e05c0d1030300540141d441c1241c241e4820041c5241c6d510f8810020103114401c81e4001c0345180e080c0c0365911215010383d0046071440840101404920102d00c9440341c0c4a080c50010000300440360005920320f5900405040904d1003804604241040d40c02190060456402c00c00c1e44c401010b1204c0046030b0044648600184113a04110792681c40440d424040b04d803418014459511940100402540043c0000e200c0813001c01003c50300c10000e018000c02481d40700000107000b00140144610308103c01400911191100f0051190f59981a80d4540280c6c01c0205144141c1d203000c0403580c0344288480213820031001040301038509a1000200050b680310b5030968440900f0341c07442d000c80c42080500104d0b43d4000001802c901505c0200e421007103403030a1500320080da60f9001243c18503981e42c005400507080040c0000601c01d09028400d40c8a8059441d00400e143c9070325400d640c1c6030070070b400808101e1401b401040f49001900010085903d49958903581c04407404210341d01c1d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 339238633 1250 339237383 339237391
    0xb0a0903061802010225230a2103050703020c0402070605100501020601060212090a090e0a2105090f0d0b090d03050121021302040b04060914030628110a08 68
    0x680c1844102d0402160790b10360009807a0f410303001400c003501008580c1180003040b580c5400d803e10440d4001540c0c0500c0110200f60a0200e4000c900d040c40d00300501604819541000c0d034454040c244c405912511442c2448074507070907150803601c800c0e4920b000c03410031a00048091380940041b41d890140402c56000760f00961084445225580e600e0005a8480400344100c0c005600300d40071852003800580005c01d401c43d002840d00742c3c05601e8038414001c66207085515034003680b00c9140b510800c54800e501d02e281114485103072030701c1356150b20020403d12403184014010007101205001c99185c0055817a00701d070744800030085518000c4144d039a9080c8020b030020020341030500004184803148080d81000780403441a02e8441c02d90b400b48040c9074108038120000c5a400c03c800191500044040d001800130381c2d0b41c001d002403802d000711420380f0b20b6142440c403a40160302802540306504811074810f209e541700118003820003da15170010a941c95461406250006160303a0155001c8503807441 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 339239883 1250 339238633 339238643
    0x807150c0201050a0b0a050103150e0406050f070905090c160507081b0409050604020d050f060c19170f0a02070b0c090109060c1a150d060f1a150703090b0a0903 70
    0x3ea900e03c0d000c9420303549264403180e00881c20309404d000d01d510980200c204030000d04885d040d2980c0d925002d01c8205030844082d00c10a5449090002d0800c080380280d4004086103860390005e800c1c100012600c3c100a0110901e403040050703514290004200286003180c1c01c10b00791524030342d80c0c0903130325115004190701207500c840d034800002d440d19040c42110078660b0420000d201c80d41c0c43d039083c480e448601407001d540346c1c828014410388603001084402c2c42a01030240e0a40c40f016549c2d105000d41c0070035000354007407180c10103514030400f4000d004142c3c80301070740d100e40a10351581c4001000030300c60144054440c000d03040c10407071030204900007410182c0f0300f80c0e992804ca030703581c0d402166500b6101000802d178215044c0b00c0c8280291403902a40c1014090000340c8401c031030100010003140e089081211a0383c1c80d01c02c40c00c80c007200307480382001c400b0329010300d180700804070000a1000031000e80078503080c01001c607500007494851a074110241240e100f000d07982c1d1960f80000f50140f00248004c6403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 339241133 1250 339239883 339239891
    0x30c28120609020f040308030a0b06040f14120607080a020c10050f0a051603090305120106020c01090807060909020d0b06071a15130c11030409140c0a020a02010c0807150c0201 77
    0x1829040520882d040b0b841c511301d1aa05160569448034440c0e400548030340d80d07850312400074100a40d0ac03440200000d20b40021030080b802d203040180c49442d02401e4225104030000300102040c6000411400c1d842031162800c40d03c166a0207030200020700805840c0315551044152a03e014985540b005000741100d40400101c1e03500e030003c41c0241c44088420041c030b400601425600c042c000d40010748400d110741811400c08481000728034120700242e01000043e03011000c680c1d019600505c040000d0f10112020744a041c0c00c01d04090585d10192050400b110b50000b0079101230703030f00d681c0401903003030b07000300350030364882150614091a50300b80070203e00318000b090201c1d660304400304041d807120a0203003983c8400780d4005a07402c020f03c0282414400c1c8034460038403070980c0000348014070107007060a40005801c0c50b4ac044500c1544001420408140c0c1c0c108088004150009500000c0320303824680204044010700e400300e954012210010300e4441d02e0075191004100c1a0419080c184003503000300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 339242383 1250 339241133 339241139
    0xd0f0c0f051e0f0f0703030e06031e040309090f05090705061309060f080d0c020f01080910060810060501021b310f0c030506180603011103130308011703030c281206 72
    0x1601d980179480000c010840380d03601c200f1681050400303543d1184c40d40c80d03505c40d002c05010060000701400c58084000a110610074400c16200344070ba00503d2207825010481d92405010780c0f03980340480d0103140e11600001c600c480d007202c003651800f40503100100d028444946c0c0c901000001d03122a00504c5003901611541300d107014400d0032141c0d269600240188914141c040040d5002e881c090650716841c05601008004e40f00180111343c02401c00354001e00302c6030b074085201000c40e0455002141190440021524900280041c0c87d84100044880796001515607480400030714510000c4103125002c4d941840c401c0c04280c4c0b0017040b03000d0f182020b111841500c1d508904031034044403025802072262810300885c0314110403003a070080028000144214007504d0502003608100d99240e4940b281c6c0b4445410590300c0348581c0c0c010130010721460903807540402081d480e40001007280c0308110b00400c0c4e140d0069100500b01c0180510400620003140500030014440030f070b104030b0241440d003400000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 339243633 1250 339242383 339242413
    0x1020c06070b01050d030e030604032f03030a0203150d050a0510021204032a060614010306031e050a0b01031b0506040803090f0a090e0706020d0f0c0f051e0f 69
    0x4a40072507100112480070307030038482004a85243c5110507010894007100c404515101000b5080c0242e010352034030100305403c4180304041d040c501000890260302003841110103c000000c0d65042904800c001d0307280d41c1c4800f900d03540e108071000d40d142d116900b070750600c003440004514038034801d00803000d82e0440c07070800c0362003c181d208820b0401100031000300000c020921131481d840c508107909060301035562040c40c0c03041d105072000e9020740c0e08540e00c80c01048540130342e00c0c0800302d041c020f0030f003030200c42c0c030b1a15004241501210381c82c10500c8c4c0c0000c2601001020300c1a103804070f52007100e4005a58607806d020480508040054910013494400860103241c681c040e00c0c211100c0000962901a4240900080b044044030701b035085802084045800115400340b022b08125180050019502d051002840d14403285100320074088020040386405604c4a004001c0310340184014106801502d0404c0c80c041203030a8880289821074400e54400344041001d002c01c8440d4811a12840d00340450 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 339244883 1250 339243633 339243637
    0x1209011503020108061306090c030b03010e03070f0809060711130519020d021204030309021318020f13090c06020f0312071b0c090b010909090b0f090109020a0e040201020c06 76
    0x105001010411001c200542c8544c041d070354000e80c0070380001c40907055200c02000341c400c41d802c50303420b241e150f180118420754144500b441c03118040b002407000c410901d921645a20030400040d01440130840c614050000120480c0d00c0190082c1c9031594a8009040c107000c0300d403001020700d10502000c004000f018105000d01ea014221060441030f1000c003c003203240003584540c0f030003485c8a400b0b01130b62a0081c9c040d50b25a200c0c3d4000d840114401505204118005a007506a682046d05e80f542d88030105070068078440f131080d410340d20b07a034020750010005228a042d0881e170000c03580c2414600c40030042820100003c51f0102d0302122440c000440710251a0b00800a03018100d4911000041c240d503c1001c041340c001c00c1c0c00304444810041a1a017040e80c0515400503a0155111510070495591082c035440c02860ba18008100c40c40450342d9510107118040d0642d4034600d41400450800e240c298802a001c90f03004048902070b65607241d11910307800040b2020303800750041c1d00d0100400d05020f02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 339246133 1250 339244883 339244901
    0x906090c02120307020721061409030d021b061305010b030c0303030c180a0b030114100e010c330c0806010507060e03070b0702101b020312130512120901 67
    0x2410380c2d08403020b200d000903040200800118807844800041c5044042005101f8410702442031030380f11082c4c213004003507800d540080b07241410309000b0080c1081000c000c2d180300c4494041d01507907400e45200c1039103040320116228400d034014601070040607052205250102e40c0716000034001030045200301a21500c1c211440e5405400400020b03608014002c020320220104081d018442d4400b07402180702c0c55610341019000e1903000005200c1815002406800c07820201c54058207000c0c0c40c4801001450050b070402d05101c800004081040031064542c0390031101e0303000c01d848400040040035103009040e010f00d0f09503803400c1110b40e14a8803d034501882441c040e10b50a2034001c166032201c0082c403a40d18000d4041c002030000c1c8000603c50b181d498000c0100d40c0c0208240300d55130302007600301d0326402d80105640702035196243c81030b600841074443c01043c4044c000c3d010341e2040a9090460704800b00204a0b000d24a1860a80c443c40b074080c040c00c4c484030140d00416501c020006080702e400c21 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 339247383 1250 339246133 339246137
    0x32a0f0403020103051008030f0a080f04080a030c120c030b120a0f0b041a041109070e030717070308040f0e1e060d06090f0b0105130207120c1704030c0906090c 70
    0x41c40036500030340099400c408101004ea48003a500c504250442d040782d0b0750848418400618018496407180388560441118050a1940d04041e9503808180c4603410707100c803d058440c07140c0d485140c010000180c0d4000c030142c040c80200512040140209980d6598034071a50008519240280d000604010700c0c550224180207a0b041036103c03166091402071085501021781e22a40c1c0140b100450498001c5200d0b05000440754881803c0052804d0001c0c4034004100c60f96040c07126540d400034031001141d04d4070b8141000700c1d5140c1712250a01c031090304081c006003000140003449180700b0340400c04030382502c41c49185a032a0700c4408584915810b0011040c115105c01207411481d1055081d41501d02c95200002d40040701c0c0ea131505009078083c0700b070303403c0151300004202c182040c4080c158509009542185040d95507503c0c01c8142a0703404c5908200004c030000a002c11020384891150403041c0249251160f40d43c0c540050003201d940240e010150506000140d211040e000d03180382ca0300d0b69 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 339248633 1250 339247383 339247387
    0xc06051c0204051309170f0d0f09050a060c020f0609030a141603050f12100302010207060509061803030702031507030f1116111002010b09060303070c120302030f032a0f 74
    0x80560340a0440f11900b55410148609240d806c80e00310401003684500b10042d280c7c075000d503003007020b00303c54203826004100b9060078607078000184081081141250701c200001015101c405040745001006481105e480c0701d07031014004428000005040a0314155407040c0c00410b65a881151328007605491826100c1e042c3c0c40200040d001d04080c080000d010f0f0501c90a08000e132110b241204425610b03c8070242001900b441075586c1031041c607000c0c000c0ca0030141d1a2a200101040d41c92060b0b164041c0880e280100000050390300b44112243c040d001000c0300c0b850349100c051400040800d5441340c001c42c2c0ba0010405011242d405000c940841c06504a4104441007400d450721171041202250140c200392000790a40e591640102e800304111360002625203950018880b101c0d1001c1c0260b1721a078418003e10b00010703040c0c04e581c3c041d01ca005411000810440c075060f883c40c088c40b103407000d07110008010481803683c1320200210861b2100c43d00b491440043e40011514418080074030303081102 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 339249883 1250 339248633 339248659
    0x1503050a05130c0603091104020a032313020f1309151b08010e1302120109030e06030c041a0f030103030e100309030e0607030c050106030b06010909290d0c06051c020405 74
    0x386e402119800d02501500d9640000100003a00b01d034000c4000e80c0c0400c0d99041c20303140e00643d6080d0342c40b950300101040102420548102c01a1031030140000b40b1590080200e41c0654072060101c4400301f516150600c5180c0e5940340c003142c195404410a011246040050000d41c0042500710301c00d8940c82e1a043c60036400e0243c442c0e44030740014030801060410810810050711032038540f001243c1d03144000280d20500307103801091540346180091007001d0a0060041030601042100c080b20a0590a00d0140c0c203182d061100718081c50082084a01002c4000030500d070300300310a0751400500719205140424286425800c41d002c100c006800a02000c280c10131a0078144000c140943c080e00b0320707a02010441c0d5801d800d442c0340b904129400c034211424130007296080303032400c000b074100c10009000308044242d10a840908400040b071509450900c2c0c220152951138880d400300e81c10500050884c0e40f20303000a0055030016100030031890440740e5040d00700390288244c80c1034480c01080240c080e05 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 339251133 1250 339249883 339249887
    0x1e0f060c030b09010b130902090f01030c090b0705100b0612010e13140c03010b0d050c0607081c0b030c180612070f0e150a060c021203041503050a05130c06 68
    0x10300440c2250a15595080c11180c503901d502007240200100c0d031200e03641e4901d444071000c16240b82da02c0407280c14018060500c050399641c9d82120310030028a07000805490144003262800c8541d400111040c1002035040140400807600c2c8070142c1c1c1100d001e01610681105000380c0c1d103d0b914140c480c001503a0014491010b40b01e5682d5004010031070701d0750180020303450303d800e0381601004440050b801040034143c1414280a44486503400305c1d07125048c1e4080c0d80b505d03a102c0f0741c0200c1541c420400000c45000304204142a540c8160b0001054007030101105200d01c0100030601c000c52092040344803d41c0f081c80c00007011824144444010a100e03105c03003003441031003806050496054001e007103020603465601110759006203a010652103a6003442c40c52a00c01da1026445117004030f1410200740b149640101d0b03144445581030301e003100d50844110949003140510740109030402c881400c00c092059241e0022030207141c51000421590b01d881e400341c00001c400c840c000340b06120130300007040454 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 339252383 1250 339251133 339251141
    0x3130b2127030f1308010b18070e1c030c0501050a0b03030904090f02030609160b0a1707090e0109090b060910030f0c050a1203110d1d18010605071e0f06 67
    0x300700002240c2c14100c482520b80c5254000340c6032250310061005007000407200901520030404415140810102e02810364081c524600600590038081070503003509164450150070782e14004902c2881d030803e0714510f4020300300060000180e59560808010076404a1540704850382c0311002401140703040fa01c0414040038100f4848190b070700303264151144001d41c405100452040100c68003500300c100f001d14100103501020780010300103840501c0044166500a0708100e000e04030554040e18a039109842103a0000182d0001e0700710340c50f4070000090113001c54022043c000e00c2800300c0811031703458038240302014008903002850941c07105070400c00320749074030740c418403030781c05080c1e8000055152000305507030720000c2e032200032006e0301045180c0c1070589c020b444c28408904000502245041e11500824906011704402a040040550050140c4c2e40f075031400d1a0078080050046d1039a585c081c0584640c01031501a12401d82c0810101d501607182c2160540a80d400402001541c03803d449a41c014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 339253633 1250 339252383 339252451
    0x1060e10030b040203010806100b0a17090a02181605070f020f150406020c0f0d17030c0d0e0303070306080721060b0405160e010c020112020c03130b21 66
    0x11680c1d600300a0b4880e220350008501808210004003010700700a6407071721000c91140c3c010904072106120324a21170740e001080403101074510008514540368500c403a8204a041e440081d4450440104400328030b032440b800620400740d4001041c0d0f210300f40b00054840303104d00c13a40141184c04c070795802401498000c00820350103501400790080c15403840c0118071a0b0340103810200240e8814046060140790240340f2081d02082903605c01e491140035920030110a000c580050301c20b620100019280d02c1ca41e00075140039501c9130318188003003c0ea0641e066280d500554050000900b0300902141d5505c2c00501e04084608000ca20726980902162001462009080403a4815154001c90303180b41e4032030107414090143d0060303d0781d00091007100a064440c4582905062010980c14500540c0e0801000ca0010259010159503030b21030352074184c1184120282144502c05404001c155000851301510700007001031001c9414510200509150410480710502e00d111213800240310b0440b4803040e2440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 339254883 1250 339253633 339253637
    0xf120e01060b070312050c040819050115061106280203060301021c0c110d09030b0603070305010c050304061514040e151302030c0d050d0f0216030b01080f0601060e10 73
    0x24241d02c8401c501d0060744240c4041e00080c040c2003070510403546070300c41c00360450850f02c403d9282900d04040340d030312480020f10142c03100001c0762162080c04029080704119610005c020ba0840784c07180f0b0040c01c0c00c900b50560a070a8801d00c800a020245061100e0202600007003004c01c10240740c0c0400000780d03200401c00341d0155020300004902510b0802a845201101c6002040e05004014001d00484d03a580303000413594803000421180a030803000d88d00c01c0da60801d1500c86150f45040100c1c1c038102142d80010000d40c6450314405c0c946070b003e40910300440c85400184004900207080c4c061144550103000200c0007106103101e450310f05a4080c5116100700000e413000c2080c1d00d081041415402c0300e41c0c00d40e0321141c2d01c00c40c08502c0d041c0004005504201c5076565901419221755999000c40f1020a080c8108108900440fa008010001c01500c1c030b001c28841d0a5200d1520b2192030340280328070001c2d031066440c0000e800c00d020074683d05a0305580c0c1c600603030300280001c00260014116406003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 339256133 1250 339254883 339254891
    0x80304021e060706020a080a2f040807090504030f050702031902031e0d0228020103090f15020a0806030f0d26130209060306130605070318210f120e01 66
    0x40c10b440d4000506000c90040d08010303210802c0382c1c4080c00c1d80c0001495052103074a016031004824040956080c807130802e0410388000e00030703101c003c00078522641e01304a00a200d40c00c80000c0102e01504018400e40c4642d8074141040305444050301c06004042000b945600481082e2000d02040035030b031644240001c080340d200110030454415413500c84041f03c80b40b030308812503085500e50100703c0040c09018408282c07550082940c062100910b0a240c024109501c500e01001030000c403060880d03a107a0014070510130010000c540c030000354450384030b00020840c8900004d21501d000304248080500500c060400b5900e51362040315460305145050030801400704101442c0080c1508242c03150529401200f200880c0d8010403a05c140000e000500c07a500c800c0400c400720050f10f000c0807206a1010700400c40d13881d18102500a044042d0743c6200000181040d0002d00c601076a4088080b00f50030362100c0c00c1c0c142c10350b0407200000154805800b24003501002c04a80d000c0ba80024940382d00d41c0000a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 339257383 1250 339256133 339256189
    0x3090313090903020706140d0b3007060f0207050607050319170c030103020f09060105130602060f0c1303030f020118030512010f350307030206070908070f2c090d030605040908030402 80
    0x34403400300c41c44c6114006a046107012b961483c0400c0000050302d42802e1100200990500003503680046000341c030b016003001318241041010030030503181088980f40d22200300000c034010090800070b104a910075840c04103004903400324001402c807410f0b40d4000d058024048101001e0044011015007114100312003003180d125454440c0889202030031060b40500100c2c02d00c2c85a048003080d02401d1410303101d80c1007203009415604002400100e82c0d0509181c000c581110074140e00601c180700f0002a030f404002400810075500900070040380444603422091a602c800107008100c08600445400d0318100300e58401904004210a5003d40e0800390740301c0d2981754030201c5085030451075048025a1005050007403087d00b10100310b0161204a00828641d45801c3c0c0ca41d044079000d00c61041c0f002c8840c207145103460268810f04600c0e100d016556803240c20071111460752017180d900c005000034600980403881e85030034059219426000311f246806c54071181c0030002d17140c0344551140001d000da5a401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 339258633 1250 339257383 339257419
    0x100605090d03030c0e2205090d020a02010c0501020f030705030a23060d02041e021b010b1011010f0e07060f1403040813090c080a0e0f0a060203090313090903020706140d0b 75
    0x40080c91400c40c50301c400c408001c50342e420558801810308c0782e19030043c8000c5d01840f0b0b80020056aa541c0910700024205a5420a240280304000e13040326100d50020400c00c455401038011350254061307200400410003182030881009884140c410303081305000780400d1035890704207103050026000500005c4c07142d00d0010040090400c40b140c1c0c0e80015004240b00d010128080b84000011207020000d20181d07e0410020b240403c42d642c5540c24005065480c040d10391342584604500c0304480c9080000061041d25259124407510482001455a81c00c08002c140700c0c0762075a0074601030401d1241507403103c0d81d41341040d80000d6171034110001c000e403001a14114030300600d01d200030240c644544608080c4621419281644604001980310043c01e803e000350004031140a280c201000580b45c0d2941200203045104a416030680d0360740790b00f0082200d1001d0781c041101d05101740c00302c4001a544120680b83c085540c500000799020074040c401d40b41c551a00b180b4181e000080050440100300000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 339259883 1250 339258633 339258649
    0x30e12040e060f1f0807110a0f15020a091206020c070605070b0105060c1b0a08100e0106080601050303121302120a031101110403170906030f100605090d03030c0e 71
    0x74510220680c0a00000303052988400ea44400c056851031269850b158000707041000040700d0038100a010b0700041c0851703100e544182a142003103020307680703005000d081403140741c4000c1105850f81c815803a03005420a24520803100c0d0510584c1b502c0c0c03135991030102c0240703c0c1000c0c2101910099000c000c1c01d040c081061008002030030182d103d03180c96074480d04103240000c0058104602810701041034503042c0c0d0001413140001c038082c429100040e003641c00400c0324150a540700c415244100b13503542d0b0108059410810742e404401340200282a682e80740e5564a840a225142c1c05400801c01001812a9601c48584c0b2080c51001c0c00c950380c006a01041810280c0d500c40356603a00140c0d680b00400d03900c0483e03150781d11045802401a02032440390000c00f4400c1307202c0103154481600d68030000951000941c1d03129140100500e8580c60030b80b030000d00010045841040c0b04069400114559000f03130242c0f1480d56001c1c0003513403000003554090f0000c0c40716034010024803000f0f0021300000d42d02d0b0b4403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 339261133 1250 339259883 339259889
    0x30b090307080a0917030418020c0a0804171006030c120314040b0405100305010614090102070305060a050124080103080d0e012d0209060d020306150408060610020102071101030e1204 80
    0x10344c040b00b00c1e1808150b840218a00b401c0c1d1403503a00300700003c110901d5100180d41001c2070300d410040e43c41c4640700181d440c003c00e40030001c00c5c3c01c4000c036000440c10035050128003d403100c0416100c17050f119644500c121015400000c0420310541c000b0710840041034204150140300e400c040300ca40c0c20b40705d40000141c0203030b0301100c0300400c001414022810078021280340d00c0c02500b0140125410404041c040342c103c1c034164190604003103400d5009a1003040301e2001190000169405401c003034003100b0103820240990800302c000221802604040100b0101031a0b003140d82d0307a8100e908503511148194041e8203603c031084c2e241e400c141583c20081c402c03402c1f600e5604c80e4054a43d2407552a001242c0e000d841140071140c41804980c05640b41c5004070b92130007001d0580143d49035203040c00200015203415a4525540c3c0118010548070000501c8a00542c411035180c85070054002c422030a030320600e07a000301004041c40303298100d54000e80203c0d00d0204038500b03541008806501d801601e81250f4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 339262383 1250 339261133 339261137
    0x51e030a120c1b0f1d040312090b010314060601050c03070303020310180c020115030507030b06270f13020105122e0906050103020a0801060e010e04090819050c07030b090307080a 78
    0x15908000e45800040400c00a1a04017004c06180e9000819a0018600140003405100325041c0120803005941c1c490a44981e00400c0c424080d6140c6c10016580448000069520310900c00401c403158000d43c240c48100c540680154a40b80b0300790b03401c402070341003e81444a406201e00000ca9500c0705601900c05001d2100741c009846240030743c1c000d00351007001e12400c0d08ac2102c2082400800c60101d030766801c0c4d07500250003904603194113000c50101d042000030000695000c114a0000050811400b4010b440c04258180c094440c1d118804d403081c6030300c8000b40490020001c1e1421f604a6542c0503521806241e00410306a254007151035800c14208041262030501c40c2081c82010b4a074131424002d49401e1a0450038001c0300d8201419607401805460300b40310100201400300c0c0c0c0300b103d107149900c030054800c4c0b00118a07441c15070400d4010a100e0712803162110b1103450706500c07a40983d480e14198a0040100d01c3c5107480341c1c822100d0161002c2128002000307a01c001c40c140070700801d4050080c0e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 339263633 1250 339262383 339262433
    0x1109040c030e010f050601091a0f0c070e24040905070e0a060306050c04030803371a12330f09061b0f030a0902040e010204051e030a120c 60
    0x100b88a0071181d481c0012404186028103100040c1d038030004c3c40b402c0d00c11001294812080403904c035130440c081d400500039480e800141410850314003003102c0c400c0340c552058801e0640c2368105145082d46408000360055241e17103000289074600740d00f00d442282c1c05407040d034101544030000d40b000f4502c00c894034000c45403940001c1040013410b21505500c00320400180307080034195540c111503440084c20008420701e00724000c4a02900d0f51050200e4090481042d0610040310b800c0c10f4060840c601428903070580c0c20328290228141035008050340c14603607001e882c0192030075040300c9250410718040c10300c2c818181490905449504486405541742d84490000b0707240031428036207000401016500342d55941d400c401c02c001313000c0c82a40c50000076084640e889564200910b0010310390204082e42c021f0409c8515040c1820640c001c106403802941c045100325001038003055550a590007803a0507900119064001c10900c82c0340001c0203009103000d01c2aa0003684440e8117070a89004080250421 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 339264883 1250 339263633 339263651
    0x60806040f0807050a0320010605150309070b032502010b10050a050d02030109060f1a0720040c080a0b1918110403050102030108010c1b02010f090b040b07020a0504021c1109040c03 79
    0x39241f000b003a0a003014002d2100c1e608020101703580010b41c409000c43c200000c07022a40d802800e00544018041e40d601c00703070b141d00d40b0307206042450035000d005442107540b45000704619132060180e412051405044400040c101c4c800449440e404200d524003005024481524110b025000a60003448131031000b088903810a225800111110360100c0d00001481d170040300c40410b0b003401e4400031a000307213405008140c40216200d403404036072030881d84580340610302c00050360007103007070750068250443c100500384c10002440380c104044401c5030700361504820100100601d40e02036090703014002c400440c00b4084110050030541141c0c000702d83e80d035004001440703402c00922400c1481a42d40c68080d2455003860300460405150840190410420004100f410360180401e8002000c04200d0103640341d81d5000d00849540010008a03c0b44d0000da0000546150a00940705013600c2444900301044c6606c83c00c81c020168032419482c159020701c542c0710301e66203d02c1041000d000e80d84000c210b0040c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 339266133 1250 339264883 339264917
    0x7030f05010b01081b09030a0b0f09060c1e030604020903011b020d09051503070315061107081c0f030906050a0b0910030b060105090105041a04080709060806040f0807050a03 76
    0x1c00c2ca010b1604100041c000c00040c90100f1103000c08240003003001d103075a1503505010a0131b12882000180002d411201804a25815500c41d148140c200409807030441d211264600a43d110b000b2005820781c18203100c03464014802cae0019500003800030700044c5820904000f09003920080d048545d40e900803980400401034040c403c0b03000c020300074a060300c003090412001035141c07400c0e1180c0101c07440011000404a41c0294480207019440812126142e5940e92006181c80e144c006030250034047c07d800081c1c0e1041c005200c402004081c404010070000703600c400c40d0b0b010740c04c203005010141c0310040c80c3c000c1313405881081e0094898907000b003003071400c101c1488125280a0040c0b29104e051800800c003003441020b200740c004c682440d11a5507240d06000407542c40c0a250080035540d0b40c00c0c04c010810707111503002001100c0305c007410341d581a82c0d910602d03030407140c05214011440d0410400200002c86d0034240c0321100c0c0c402c4050a0400d4001e80f143c524104070303840700301c0108496030359441c4524 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 339267383 1250 339266133 339266141
    0x10b091216031b0b090307210c080106151713170a17061c1b0519031208010e0103030e1807030f061406070f050307021305040c17030306090403050c07030f0501 70
    0x401340008003481e1551000201e41d80d04111b1281e41c14000c9002d01480f52010526001c3c1c215681103518003900d15110a0303403038000d020710300c90b200300726504034081d2071041d001c4d61115032035080040c0d0813491690f40351481e00420b582e4a0044417031140360b80140c21002e00c000050004048a556043c95040130020108036000c00034203228170600340712010440b5280304005224040b6070000108480c0d52140d0160b0342180045d400003603211031800022089000c170101840f0441e03018026100054840400690b80716200307001e10312500c500c00c00180042401800c81c204507260103482e0341c4005c1029540640740a42c19034140380080d1701e4580c440d80306034040c02400060131400c116003811031a0700000802038461311a0003401c0c42e8503550341c042880800e1064607140394000d003121080912030b500040c0200b100b194201d0320f211102c00041006183d81e0990302c1c00c11860001140f460f1580401c2000e20b010041c0300f02c081090801c80c0781880041401103400440c840c503604000304485260140c00e407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 339268633 1250 339267383 339267389
    0x611030c03160519020f010f05040f11180906101703250804270c0c0b090f070803120114010e06070302010f06060809010e0105010b091216031b 63
    0x4018010321510394200c0d03089035040944481074a6242058120a55050103003199151080c0381c6013813803032200c58020030b9403140003031410000c004641040c01500d04568040ea409080e089650607a0000500c2e081d000c0582124020501c218006050741c409072000c104460310309041c1c0120044c0581202c0c0c100521700a014144080c00f00d40490300360503581d9004020a01e228560100e43e24003d40c0c417005001e001c00ea4000300d07140e59a544400608000e25004e0000c02e590840c0d03811420b032904030510481e00411140d03511034004c0c01d02da0300c580148000240c01c4900d2030080102500040504108080c0142440070255854a200e0080420060710580c0501c1c0001076900320500c05a901c0402289030700811a00581c8030b4040e41000ca00601103c0040f130310080ca0104080f401507006503900344544030b0500240702c603642a9280078203a130828801d106014909010032180d51a2003140498103420040440d21404042c0f1680d00b03840b44140e0007035600641c60702c94004c0d00c103620b40080d00a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 339269883 1250 339268633 339268661
    0xa0927090c140409080a0c110301021308062212031404050705030c06090f101e03060302040c110d081e040b0906184903050a060303120c030207050d0c06 67
    0xf012081d460707855246c41041c002408103d4030b00044c008104941d41505040341000d8021500d40d042d4034102c02e0540d5060113152014030036000026405044255030301c10140549141d10328505176996010210308401c040071082c10341f501240c0100036808407110744181d0081d001002054a880d0500d420300c00c80c082d40318040d4038100140c1400b911017042c17040443d07000740c1d94103d001c82c810303404035200d841215464407110414a840d405007a4960400707000e9a000321010420006403c4080e604071400320301c08500d03034004d10075134004640110620790340510200c41207052110741c0641d550400c0c40c210380449512601001b48004080b0030400c80798043c02c40950f1000700f81c5a1304159a5614810b03400550707a01500c84480800024080b403022000c0c40c0300b40e401c8045c2480c01000c1d075110100309110001074a06000580d01d21251f0203204106c94240d12407059480c0e0100982d0080d01d042c0010000349a003c0100c000007840070030001d640d40c0090740d5600700d0740707119291501c180c070010428000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 339271133 1250 339269883 339269891
    0xa1517181b1c030815010f080a0c0509030a0602041e0e0a050c1e0c0d031a1216290f090105180603010611120a0927090c1404 55
    0x104a0100040400e0100c1802076855400000c000c0000d00051000049405401000c0240d0080603040b0341194010782c0d00101025054000000456100f00301000e01000500c100340407801e00788065002d210b44040b103103411440c1c8440f40000c0303403030050f02420071079025900050803ca0403048154010070074501c8100040b0b12454000c0000899030094004503040f03940307601043d84c010707505013154004d41042e805c0c00311081c44036203086526004210640b1203800784242440b00d2a01c41e05c81d0b2030481c2d0440c02e445a6800c1b90b0070610500f14040900400c45100b414103502c2281c1d40c50401038010414414203200d602c041400d424448603000d42401030101003880700407000952074003503c0000780e00b880d0194580c0303c2210301d01c0301c0e0f80320121150f070000800000403940300e50140c2c20110160b2044115040982d5101051407984140ca1030721000540310a004c1c06021980815000c002d880406500c412014020b14502281c54180080f00ca846415000308800b01c1c8266401e1145101160204 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 339272383 1250 339271133 339271171
    0x21609060e01180605041b020c010f080c090117101509050f010c02030a170a030c09180507051b0109120201051506030612150603121c0b0a1517 63
    0x85041418001ca580c20450200f00a00181c0307698010001000002d005000e007810010190342c0c50103551070041c0c0140580c01203001d6650040c4808100301025565121040d80e230300040c185c1c0d541000740302c281040000d00480d60640501c0c020070f03000d1103000f601000c070300d0715080c0001603510800c3c4000c014002200c0382000180d94544100c0305a100a01308071a821807a03200081c00c0c2807070618001c0000010f105031408264003034000c0c0400c544251010455041020420785102003a4410008002110000d202d80694960041d0b6003006003401c4c601d08102c240d01c1d20034510000003060380300300d079034031380613502400121842d10112840ca800204158100305040c414000d90510201d80507202c00008901d5035290482082094020710003900e0401d800c0d800d060070020b601b070ba0300310701c02d01c50190300c010201f04500c21102404100d442070310180102e4100980540641a5800c1d80b00d00c1072000002d411085040004001c00c05540c4c5140e00c00b07903840000103c03c005000000043e07464030180d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 339273633 1250 339272383 339272399
    0xb0a1110051006170a110d0c0f0e03070b090d021c11100509130902060c0313091103091e07120813090515040b04180818061306031e050702160906 64
    0x55045041550045406e03070a20040310014482c05200200c00303440e200080c0304059111402400c401c0703003070703440f04c049400141c2099074400550046c403a1340042005901c100380b502d1860030f14200d00c084d105504400c0000030344e5900304462101500d10103000010000345180500b400c00d0070030700d5801d1807814040040080351056001501ca01d000350b07507a0700c0300c400b9540c8100c140c8150243c0402144c0c2c0d5040700310030b55480e000c0c880c8207540b455800d10200e003020140f07040589100d001308000404001c8000394506803040c04090492005008801c0041410052080e02c0c240b036500610034243e0307510204800c54906201540051b900a16010905c079041004002d140c80505048601265000c85940010010180d180c0100068002c0380160800c0003042c002900794001000343c608000c41c902c05c107211680c410300612007003110302c60105009240c02a400b0400300440c100c007609403405400c4100c021900e050314005c0259000f6400c41c52110030300265000a85560842031042e00d1422800b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 339274883 1250 339273633 339273677
    0x405010e06120703050d121401051c210804050d020109020102251211010f0503041e054308101e020d090201140c070b0a1110051006 58
    0x1c01c0d0712a0801d940511842c0900700112000f845d080710548101d43c40740302003d406100507103d40103c850500360b401000c9001030900d141200c6003e00003507100e1010800c101004400a00c0c12550702d007902c0c01c11100480d001c030640c40d01e0500303901d441101e0f041c1820302c0c0b40f81c4404c8000c40320440e03042810000061343e012038a1549070329050209400205aa221195040c004da0050166221210180c4090080007503064494000c00c0c0c8406c032842000e28000c80d41440112800352598401d1039003082c81002002900c03001c540540290398020032440c003418146152981c03290b9966406448040c902c0482c0d4009900300121507044801a900d80140c15842c0e2100c1d51201030020b542c0e850307c0c2c20329010001a9081800e800300215503412101d00807500034468a402607001542105a0111441c0c80204644c02c0701c58500c02000404d28100700c100c202d0303000740e84020400c0a40c0d0654812400100a100c01a07a110200464603203000030400800401c2075000b00200401c0704900e166060039511 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 339276133 1250 339274883 339274891
    0x20306011d0d061e0504050a0b010f060f0f05220e090102071e051c03020a03050a0603020d0b0402061b0a05060601020a0c03061107080d1a030f1005041401090c090b0405010e 76
    0x1c01040114500b0048240130b03034008074260341c8a003003508110811501203018200c052058016402a0b602c600c1d40315441d01131405080081440c061301890458066141c1580000d160300c1c10740d2400302c0c1c5180300c6400c072024001d14500c0c944030b55014810b000c00f800e000c5a1104840c802141403d40716110440c52084444480c5841c00101d8201c205002c424070a94621480b24894540e21150300c001c0240294400b030348110009241c08085050354681d4062030b0200c0c2c0d00100280100c41b0355450b841c0c6c0da594041c004a0348032a0400103c00d8200c1007107016202c7c520108041e1a00c10000e00309241007010040250741150001c503860400110040b04030020740e90480320000b46028078886a2401e80306a42014200c2d20000c03681079959501600a00f449841e803040c1076000503212803d066940490310045030b5942c0180c203801009e5169503003c50360203402019940b4444841007645421650112002c1c0d030b052456000601c42c4080038001c2098030103042e54100229803401c8200c04120b08090 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 339277383 1250 339276133 339276143
    0x207020f060a0e01110f0d08040506060a03030503040b181917041212020f010207060c031d0607030b0301231b0306030d030921030e0f03030c18011101090303020306011d0d 75
    0x3000e201c45e00f041141c0c3d4050b5102004455801040000150580f041214120740c0c42c42071f02c0005110b41801c0032540112035054070f4036804d5859542c4c0f070f2154904010020743d02050110f40c000d407521401c000c01032109140c81283c5c20844c2c45424149010410301c443c0362464103040004009805d1288007910f811074104d02003019600440c1f00403828000b003400c80390055030010580d00d05000141e80400701080040d2420440d01c1c0e01c460942504518400d000c0440d41c20010006100741c0c081d41081c0e2407080000c000107000401c0400343e62900d00c804280c00c10810300a02001a2140f079040400703d2400c4001c4c50034110300c2c1c01c1c400255110b1110158030b0030941c440b59548100219440804a0b034000c40e400004500700301d41005004007608000c608007441201c001da0040309011003244d016000140550385040700854000d40c10300c2248282d40e04206804819413880002803081418152103039801503035074140100014400c01c0c180c50550040c8001e544852925a180040511455488 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 339278633 1250 339277383 339277397
    0x60904090203030408060a050f061807050d090f080a0801120f120c1a061c0c050f011701062c03031215150301030b070504030b07111006090207020f060a0e01 69
    0x40c400b103400c0d4040c0e544035400ba0300c1040d09000d1903144035002107208d036244002544c050354810307041110703010001804240e41c509000201d83d81a1055004010050345440c0c085808130035a41d40c2c2ca400c6020041c10b417101c3c44046100d20890390b0000b5220b0041138282c4c90281f0f954810707100d00c000100d1004006098407544490403180900500c1840480c40e080810718610511155218800c0c8108032092449001c0d000b04114100c01509170311481e003500600c0d103000050030003081c01440041c0b0440e2a042c408403150b01242e0701c40305c450b01400b0f48170356030301c45d4800d109004017002110354403a00300702c4250300303520750f038105413800810359074482c2c6000629840f90700c442c00d24039080400c0280061b00300070141c070481044104d503c0114108c9104448080c92607071107035400c54480c0503d000c002c01800b40d0501088405100f00d0314104c6090001c0203403070030032011000100844d0407a90007641d0042e000705018003545401c0154406c61081580c1c068a008080c0400522030b803d0742c2400740c10303c401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 339279883 1250 339278633 339278651
    0xf060917010f0608010f0b01050a09090e0a020d03110613080f0a0c0507080c03072102090c160606050907410d050414010b06040501050a02030c06040b0610020705060904 74
    0x2500003090b20310303680404002c803586820b50390707002e0039188021130100c40c01e01c0d0040c0540c0d48224125102c480c80c0355145000d41d400c011340c0710f001e00035118110900d44078500c01200569102e41d90068054840d80b28000241c1d40001021f040c248010050b030442c600505030440032074189001c4a030a5074440451a9503245854825100a041610050110300c0344980c0852050400140980081c03002c400301c80c00f03142d8490381c6484407148103210603036100b0b000d20001c0040c2010807100ba00990000e07905804e080f802102030185500401090304c1964035090200b11506003a4a1960070142ea807030602c000e09880c00740000c41244098010201d200d406210410120039080091501d40c511009250344e40c0c5100a88005400181d030191010f0364400e201e1400c08105105021081c100a0300190405107041d0040d240c9800000210096000070030008285010921030b40c0d204a00c02c000f000c001d8100401448030f0707880703001e03030803000c0d540101c40c02d01c560707a100c0307056840e980c40413a4003040c4050307 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 339281133 1250 339279883 339279929
    0xf03050307110627060402030307110a171f020310140310020304150605010215010303080618040309031407211b0603091703060108041b05280f0609 65
    0x752018091815009201c1403103590141104e015a002039204001a000b25865140f55200e11054070002e504d58030400801e000a84216a07002c00820028440c01456036200840301190401c0700b10221720390031421815459180c5425000b1aa04100c0750850651401c0b90806541c00d03140d004844080e40d213520401050740d810881c086180601d4a403e6440c0c0c10a4509050010458030001075000d00307024001c030783d0b54400030301000b2050010301e044005900e1a00e0980b61403602400c1e003508540501c80700305241d010100d5042c0181e11035038880364650310b0340c20942180c100c500a800e105801100041003982e21140400c1c804c0d1041c5c10031840c0b0101d9030724010013000010b130b5043c1a540103031035000071200d80591201c1100703401282c0000300e0500c2610b004005210850b15180441c43c00004136011884840840200040e1101c12811140e2628009982041c1440314050100580b02500b0020086100400000c00040510100c01030520030f001e4400000350290007400080c60b004000148 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 339282383 1250 339281133 339281147
    0x160b0714012705060601020f060c031b0a020a020f010914010e03010207021207080f06010608010b07030c0501050a0c170402010e090a0902041104091b02071e030503030f0916030f03050307 82
    0x10000201c0100541030002e00700c0460701045030070349807409008005a82035001003491280940300c0c80203407480d40c1d0345400f40411a040a0100020099200c1002030000701c54001058595a160000c2235040300e1032042007401d1012143e03d81c1013080ba04002c0143c0086204440d98403042400d02e00034200390000030a00a00868601030f40c41070081441031085400481c01b41c0aaa1040055640c3c94200c079510726034884084c0b0801000072025401081442030480280c041c80e44030b443c5c2055130116a441e103c2c00d41d001035030808030300f6130382e1005c148290740c1203001600b0400c440b141c10306140c42d20381c00180014500b0f14085024210400000d4980c07115980f0a500403a8018410809203882c4143d010458001d0302400500a00e40310403810851301c0f0740b00d20000c48140390b0040511900307249404001501d04800c85001c010600707004000204203001030b51086500011507829880d2003210709181031000305c01d061058090171000d2011903503d00e44101c0e03954160506565945400404031854 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 339283633 1250 339282383 339282401
    0x1020109020a09090309060305040f0f030e1206070207061b03080402060d020a090e0f150f040207080f07031701031502071a09010b040e0106050d0611091201020903160b071401 77
    0x9000880b010496058a52200301214025690403642c03d884400603421103805490180031001a0581d0b00c00240104c4640002c0c0c511a02d0301d1580384903044e001c00e011010000708000c4a8104200b00020b99904000c1c2e81c0003030185240c00029259181000c00040503d00300103800c100a6000180c299161082241e601440d8008110340d54000e8000061101600740160040407c84d9008030300110080100b890080051110b4049808408070400c0001c5110010007900541c0138031458012900c042d01401ca040419403486d5500c00c0e051800410142c064010240340c01408001480400c2112685500c100960080165200f0050610045403007a05180d4085040481308000d0850419004510710760415102403090400445115098a03054083c1d2030700000703409809004246907070000040000c900590a02e480164004504607407002c6141240e6690006014a80c90504101070045580c842001500b800e04104041e10144100d2002a00d1600c3c9080b80ba01002c10a510072a11 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 339284883 1250 339283633 339283639
    0x20c03070f05010e0108091005060f0a09140702070605160804030210030c0809030306030318040b090705070312180f020a15091d0c1605190605151e040b0102010902 72
    0x5500d5803100210011807090141c0e0340001c401c490f5000703141d400740030351600440d6000f01401c0e110304400700d05001840c2c000c042551040c1c0d500140c180e603464208805d0302404c0740007004608082c0e00c544442076220040c0100707045521461040080303940c000b0541e110988814400110150305050090041c0140c1e000030354444c0100c0f0405a0542e015802040c0c644a1500c98201c0c035603e015195480e0300046842e030350107810400848601c4405c004202a202d80c004200244001c14031001c5910941c0817110000404c0c030018090040c16000884620288088001802183d4086106030050750400d100200090340780780068003155121080c0d880a401d248100172240c100381d80c801481c1c06060b2089001c0e0120303182d0141ca0300680c3c01c24103407007084044405031a0900e098901040c0c002020819602400781501c5030044924045091018600526010070a814880038440040c0c003452070191143d498840f202d40040c0a040c820075405104440000d40c0c6038071180145d014000c182c0000f54 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 339286133 1250 339284883 339284893
    0x120a02100e030606030d050901030f23010611010504030f0e0324011a03010806040b060a0e0106020c01120c0806100e0301090f170f0d02070303090b0403080103121716020c03 76
    0x10352140e01c00c101036800c000c201c040b141c698031004e0034980c6a84450215800094003004500340c15402074100342c40e110500c0100151305071b021016445280003040030b04480c3c80382c84004205c603d5002c032a1001c101c5000c8002c01c00d80c10f181e900a84a003400d524407000340106440c48174842d550a00c001003001301920310105100342c104500c005004801d02401e070703148000203107110f00c103000e03d01564181c507085c1008014036100c545480700c2403000200b1082d804220800003083d0000000701240c0200b2881d001448060801c0001400701040c0c0e8408402c0030345040f0080741588da015206d142c108205850100c87c06201c400110740000c4103402d62030701582032045090801501d440c040f56541d00800c1c40c03004064202103821103038861205614500030341805040310700d055a500415070300e4440d0400044030300c03c0780d0f2200c0d683c210440e000d401080b1681300404c14002c0c880710940022609150203030032392042d02240c0c003101101130100c00c50740300b0580311490424001c0108448030900282295 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 339287383 1250 339286133 339286159
    0x1210b0f031903021c02032d0409060501080c030402030c010807030b1c14030a02120d090b1f09020915070f02120609070801050c0a0302130906081509030f09120a02 72
    0x10100c0c0010b4070100e00510032501c142c01401d4110440c150101c081d54051407408030310201d03500d51440f01e089000905c04103901250250b008040080004100c83c402c0411070600d00000504032850041034100f072000104200300c01130b5808115a121400c0034244648079854204040780105200945c1c560840024954603c54030780038120f80700300d684200301411469000e0700d041358590054101c4000540d0180e1415400c40e140703e40600b100140601000075032501c03d1301ca080c2c1c0c1d10025100e507540c1c0360420340301443c410280042d61002c0d00441b03c0961a15022002003100c91040030080c103036018020a02c801081605050b81e85c40a4000b8000d9002601c0320b206961100b03800e40daa81c11612071104001000d00045c040c042c428500042480c2c18281002e009401035446401200d9006651030004514004c0c0c0b40705103005840c41900500c03e001a101c1c96400090028156240e10b51050001031319540983d01200c40d0358005446140c82c542e01c61880300e1504401c601c000b50300a80c910901 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 339288633 1250 339287383 339287413
    0x806190306021c1d15040525090e0a05030a03020706020904050c190816051c0501090e070605090d020d0203100e1b010507120302030601050c0a11010e01210b0f03 71
    0xba110366801c00a007000810106451940c0e400000796524100d030b00111954074842030740601896010b03000e2002d8076a2300d64846002800d03250704410341c0e10310050030541403041500c2c40c456400207080b048000c0190701b9483c0c4400307130b0700c0c095a40c80170101600050810700304900b03a01603540a20000d4010701003824044103012060b0002241150f0001d201da0000078885c0c42100305501510074109400000c820402040320681e00038640c03e009003034051207a06245840d881203500030401350710009400050451928201b0350b5035070010042050600401010743e40e6800c2d81401140e044590300e40c850070078800303c0c0c20300c3e046080f4030802900c0d2013008a403071000440c43c12402c01e0b9101c9120f109101e10401900e0307902603520050520605984c10b03410550090f4029a084581410a2400c0c008c150302c0861500502c00001c4400c12280500503429580140c2c008084d00b400342090f240d03c601e54400244154040b55404283c243c03500c480105a4566030080c940d032200c00b80507036200c51a84000d03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 339289883 1250 339288633 339288667
    0xc09070908060f0a0509071401030225030c0c270e0703080406030b030705011d09070908190510020307050708071a041223040302210703140c01020a03080619030602 72
    0x1882c41981010009100c03054045007c805030f891096074403100d02914030044001b5000854005605502500706030900910500380d0f08201e840790707541200d0000c1601d84448001c4165100742028482c0c40e054400444500e040241001e5010700f0014591120201680c43d1000982c009814402c00080c04600c060f8503802100360b101003034088800146d034440045491440e41c100b405402d80180441d40000e02d0040e5800303030044020b240002030251985640e5003064813082403032800b803a0b000d514600b0080103102c08030568402103800c60840c901082c1c06401e51140d0000240b0b080f01c0010010704100c1103645441e40c4071003043c003403001c0d40b0b01890128007010007504120045000100d60f0707a0b131000c2c400d90b00910140741c96002400c191465081c4200000c588024911840f4210703406920850700300400c0b40158003494208a140c07078031411030703030800c0314121500341190803444582022035045400d0940041080d2003009a0b1903111030704601021080d00700400e030b0380c000200c5513a4900f10b944 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 339291133 1250 339289883 339289891
    0xa06110a030605030613030c020d080a030c0905190303050d0e1608010b0a03170d0605040c091d040308070e010c240b1801260d0c1a07020c09070908060f 67
    0xc00b000580e03120350416507504002c40b42c042404049403000340c00a4411800005441c1c400b504520940c80c40b40d0f6046030b0780c0c2103c00c440d400240e640302280c0e002a4040041c50040c001a60102c802248100c188640c45d41c86002c090180480011014050360ba075511002186100f07000b0b60b00b0112090b420300528410782e01c103030003182d0b0801a110344c080c43c00c0b41d803c004582d8803021040c442c0125401c1d002c046e0304601e00d2111826519540058203803240d000b03540740324101e640c07111111402c1c0b0001c00b4a014100c10002c0f04c0040d401d0410000076004080d0a40040550500c6c0e20201c0800004a9403222100d00081c17201c0258461200b000b103000d1105035510b001800280100308401052082401080c480040c1c50316000d40100000880700b202d1150b180700b030b0326803407041c0e071010003280b4648800400400d00003010401004280050360f110b5048112801202c01c0c2e0078140a14025501d46d5800400b620035a100400304200502800500740207100f00001d0b6481c602d010041941400c01c119 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 339292383 1250 339291133 339291137
    0x210213031b0e040b1902030702060a11040506070f0642080d0207032d0f02010c08030c03070311091f1101061707090b0603010e0a06090515010f0504050a06110a06110a 73
    0x100f8030985d0711a0350095910440303495008041039036821148001900042081d0240301d4030411010074039407100d0b001041d005010f200ea410324449249850401c4641c550035840340200e05801c05200320759542c504420075982e4605100c030b003610080e8181c8a010845d44142080e115440c9c030880b4441c1c0124007001164016005c3d610041c80002e10405801c809003d10b040f4008480741900008014060150f101e60041c03512191100280d0342c0c07c25180d0050702d900c07039480408410081220f51500071700800d4100306883c1410951903a0101c5c07052003203004c40c600040d143d0702d1300b042c0c03c1c2c0c80344490302c910400d0480244042603903400c4c24881c3c650b10348100e48c802d0050103004241c140450188460820010300b480c0d203940c3c41c0407406c8001c1c2c0b030050032072040d05032200c0c00051a40800d0252900030324900150b41c1402107018005801d000c404c00c42c482c103000052000300505d503075041d20103040328000e043c110b1034628101020703810300303000c40c0c402001c2c140740100c004586242d04020f007000501c20707 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 339293633 1250 339292383 339292411
    0x4062a020c0a0b0f0310170307150b090a05090109021906031805060403050d0207050a03090617010b03010b0a030b03030a03061503020301030c0506071110210213031b0e040b 76
    0x188942d80c1c0302401540a40c840812100340d40880c41d400031507115842c2e9085045480d07c443d4140e070501f8001510120960011802e4018440b408030a20144a81800c040150290b2040400d0555800400e015500d541e40c40001d0500c0700d0a4008010081e401001c440d01008102d50703824500b0038502945000030302d000030340140ba50a554100342040d0b08074000300400d86d01d0b990220742540c4904000a51581c080c00240c000600c2081f54400307080c441e89410300400e003030140c014401c0c1c80e01c2c502043c071081c0e10710041251400d008112410355041c0d00421350340c0d00c40c4c0e01c02500500740c4910302a4062100140301024298164850400d607148064401d00f44100c0c0d50044003079002c00e00001d060900e1092080205180c91002403d03014803d07214909101c68501c0010004401c4181c0800443c40b62007518040da1003c1d145400030317514000c1c0460900104401c542884a100e0100038411070160714200c1c03d0340c9207180d0100003054000c450301c903945002d252900301014251080c0c800b0301c0b12 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 339294883 1250 339293633 339293653
    0x50a0501090b0604180c02071203020109031403061509040603140a2f010f090905070809011104030503160206040b160614130b0c0d0f1a091603020304062a02 69
    0x403a400310b504851000960801c1c485ca00300a0030010054501010194845c881d00000d02e846a290300c50401e130701a800025515003541400f0341800000e10404110500c00c108000c426620096456644581400010b450b1640d040228004000c61340019124010701901464a030394000b4284035074500c40c1d2602c400e001810005e0510004650190107006c00c07400d0641c88695110700e00070707070b07558080b032402801c078a41d152900302c211101a0780d0940010045020080f00110034045c035681c00c5180f5440b01d10309403031511480e883c0d0051911000d080050190440159650007082e240a400181c2010f55194020b804a08000562501c110f130b186080044070318141003101c203da8840c081001d10300116071550f58039650031510003044003450f030780c080c0320303100c60f403111880f82142c541d00e05a000030307014000bc5144103074440704804c014072030750f100c204010b495280300c1c1d03080c0700c0310402c2c0c140946c5a072240d1400030007034101304d10784c0300f00c8100190030b26030030302545101400e21000940a035410029 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 339296133 1250 339294883 339294889
    0x30322090c091202011209080a0f08060a14040609060b131208031914130302071a1b0f1903080a060608060f06070b090304030506070f021f02090301050a0501090b 71
    0x281c01d040110210300368820030440c40d030560b403000b90003902c14500304070034641c40003040003203070f111050070f951152003c1490080c1581080052030030509505050550f45403883c00111054070718003d118030b20410b0a80c407003a40d1a550000f9010b817200003818495280c031621000401d800c00d4a004001380c8641a00180a0412080c0504110b4022480354030710f0340e4a40303401e03a0000000c3c06003002140e450800e07100601080103242d008480140513134100803010300b8002e02d810880e4200c0d0707030320050fa29883c1c0d0038010341d4404c45048030044406580074104580340d00381400f0840010846600585801c1181d841d070030242800e03040c2c0310341c407407050325110410010100c40c100d021b8a0301103120513001c240b0526000b0500b28204500034561803802c0d03150340d1501c5002c80166a02d50f42e642c0042000c1c801c1007000c0c1300613a4400814502a4102441030800030340d6440754580c8295040f5000108034000b03003140c0c0441c0c0b10194081c00900160800c0d15140006090920075400e40038a00016100320385 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 339297383 1250 339296133 339296141
    0x1e1c02010b33040f09050721020406090504110d05130b010b0d11090d020402160204020c0c210c2403100501021c050d0b0303071211060114031f02040503032209 70
    0x34a448046449181002c0e04480107200107080601230160000038644903103c0a28082c0a1b050710501c0542c0380c80c50000080c142e140650812880b90781001a07040a040301c59043c3c8400a0300000c02003590780382c2892242942e9a01440030b08500c1038100081950201c50b401070071110480c0e0000c0042e5405460b00f805940a00c28206034040d0455072110050314054001e0000c01428810000c0582c94683c000340880e4403009000840703800403080c041c0303d440c0140c40000310311204014a501031000c815150307258003840d1110391256000401c03403070900c01c9683e69255485074040e00300d41d42e414007070341041000c0c9161040710300611490140800540b003205d400840710752180c071268240788169414401600e6a0a110368040c030083c80124041303a80e0703568807107008d00390303840f88070001607010140d9083c000141c0106440c04000740001d0b02d15100011809140041d81e200c00600d8400070051501903c500d6102551500c40402d0301e2840341030040c5010100b0ba000c4400d03405c00c0d6510601c0a05072 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 339298633 1250 339297383 339297389
    0x81005090402180c04090c02010f0605150703050304050a0f0302150603030415120b090f0a06090504020a0501030513050115091b09151206171e1c02010b3304 69
    0x340c0007005101c401c003c030070074140c0041c640c085007030900e41c44070040c2c01215280c410290050303445c0c0b40c050480040a1103004040c0805644145030b04540900201e44e0b0310170300200030100000040040c3c14042d06001075070480f50300101681d001f000504000f1b607104800b95049080c809000085240d0786000000c660031109005240304041184e4417084e202000c0c0c9100c002040303030f00c81c40050381c00d689422406100b02072240b251031550a00c550002d04440c0c06801503940103113840280409030351507120704c030215882442e02054950b1000c1c41c02c000402d40e04001041903007084140c15101c8008040711090b42e040c03006c20411039038098080381ea00744281450300b01080500c6001e0000300e0845650700c50000c1c47e41458907010307520500303507812034599610451030419100d02c0442c4040d4280700041d069031005111590200000790300d01d455100ea18001e01121424130403100f0028006e403c500e4010b5001880c174030905a41081011042c0203582c44904989001c038902c003103079024503080e2000d0b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 339299883 1250 339298633 339298639
    0x30c190309150e0a020d0605010609290d14041112030301051e0d080f0301060f020607090608090f1b01090503060108060a09150e0a020109060203040b030c16080307081005090402 78
    0x2041c1510005009a4030704910601580d1002005600c92140443c1d01b0782c8120800540d641c5024001802c1d0146031300600904c69412000d44608411403007803403900b0b0010f50549a4504d4401c8040c1c00030100403a0a03035400301c1502c00c1000344142440d402d5540c04060390002c003c52017008025840b4030003401142c0d4803e0194030303d1096013000d0981d1b07800300f500240620715280380030389500070301d6000307007501d80040c100000050060580c03008640301840c550340020110b0307051181c006041e8042d42d0158004028003100081d105040030841ca00404190030240c0d0342651480345503d102107209003c040c08550f04c0c0c000041c40d070030f002800750704a415200160a40d900e50b01c1c4214054845528240d0f8003141100301804082c0d41442504d1500c0c0c4414020140455144009814140a5402042550401c2c802080704107a400700b125884211507000070307600c1600030000e031440800000c01a183c140003204100e12160040500c90003042001d44102080303544100b0807038103c600302da000750 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 339301133 1250 339299883 339299903
    0x3021c020a120317040f33090203010f020409060e0c030103150504030e0405010605030601020609030c1b03030f031f08031603030b180c04030b060904020a0e070311030c190309 77
    0x4a8606202d0710a460703109150001c00152114280c1c208424151003d441c03405c0650805030401c0940c209a00c0c1021440c6250117246900000522440d098428404120303500d0303103c54030840d0340039400700000c415004000c549072915450320200812050003a00900329840011880410a85050300e040320b50112500c650140500d1800c000782501800c00c03024000f5030080a800f507500d80c05010b01802c000c0e903d0399120f140c04c0d000240f40c044081d04503010398204000f480020704c4042100e040300e810a1301e862680d0021480800d2661240e604455a100ba000c428402405089514107009110402040d400151207103112a240d10480d07140202401241c0368190010740aa0032404442000520701481c00c45019600c400040c011984004c0d40c0400007824000c20042002d142d170800c8098642e040c0030728042d0301042c40d907101c80c010306504201440c0040c44085c42030300041c09142c160360380c5030380b0f0f030400e048588482e800c84541c80c1c6145c05d001c0075000300035100c2d200c0c1c0d8080c02e4224038401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 339302383 1250 339301133 339301139
    0x18060606130b030705030901050a06080705010e0a090f0e07090506060901200708010f0c08011208030c1b0a030813022101060305060c04050f100903060209040b0d05010603021c020a 79
    0x355640030760000e5003122140540042c4542c0341c503014601c40c0364030f40c960541c0d0f890042d88285c02c441c0000e110441480c601741080c0007038600064440103444003800c01c90000100c003400142c034003400b90312445100b800c1a840000e00780d481e4001119030103004045900c0140c4070340c5030f14160340f411942d464005d00300707104e200c0c842d600c00c400c0c3d891403044605581071180038201c4200e0400300c49400c50700f0644c1d103410100d05902440d12038203010002034a03100f1119410489048166045800b01500380382006c00402c0c82004620100d0700742480300b407075000c2100d45450b081501c0302644030040e00410305060020300e5902144080454195005201d1100d1915020003502c0d00c508407014203100350340e15607001c00001d10801c0580d000b202030300c911907211440c1c40f041218224001003d40c0c0a25403003181400401d4121401000742ea03403240016845072034102c0810300503d00c0d00200c0340d11524001d000c2040c002c042d4030050560303000343d80304580c442c1540140800012500070081d0044a991010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 339303633 1250 339302383 339302389
    0x80703020708091327110910150e0108240127140a06020d020312060f06120a0b030d0203040b0705010b12060907120b04020d1a10050108180606 63
    0x10706101d0b12402245040c001c0e0071010420301d9007244210030400d42d88030711801d00d803030407500c003d4907045190b1000d081c00d01d00b607074031481d20306543c41d0801d0041103a940410a040001c0c3d8840d0083c044400740d00169080300d8400800c00e0360702041403404240b200000c101c1d80808800250070b029082a6145400700c81c0100440700c44080c10700640b4024159544000340500520f106030040c0214508044004000720030003540103d0766110b0170079544248590541650044141d54801d41841103400e81ca948101c04581d42941c40d500051b44a180000c031001001004001d45000e40c0e807942c1c0402074000300b070301455500d500001c240d00260f4400e1208008410950008101d8140b0650000c207542c64000081111031450803001300c5950404020422aa201017003903400620030710342c05041c911859102e00c1c20035180030308068001e000c110032800a0000d4141d100c15820422a04510140307010502c103011070300385000e002d0004081c1c8000c584001c5040d41213401e00400c076000340020b51505010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 339304883 1250 339303633 339303637
    0x209011b0204060f1715060907050304140604030f02190b0a021b2d0a0f3e0f0108090607051c020703050a0305011205060103060b042a0906020d08070302 67
    0x4100e82c010303191140892510404c411400003007030000364251200e8071050065040030b0070b5100c400740100350305c410402d03142d82d40c40d07400e60086182d09109580c4e840d281001000d01c03400c081501c0c004d200b000140000c0545c0501c01c6820b00d6410303402da0342103400c40c3c4489441d0b4205010094130503426880030503022042d5a0040800e0072102d80440300e680c41800415080016400c1195118440b034489600103c0582c101030001080200140402c46215940c400100581e00c002911110003c5000b8103460211080520b440000314a00405510f4400704c3c1300503400c000301c000d40280860340e000c0300c9035400780f4095030190800c08007406190f664000125440c0c1c00184201795010524254224001c10034401825003500955481c0d9448003102d0707018081e81c2040e0b0144140780c800a1400022441c0402c509054079840100426040000c1c00001c01500c0c07500080105c0298906200e10180c900e03408400006595803212640b45a66400c00e9895060400e59040031807d42e40000744042d10941c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 339306133 1250 339304883 339304937
    0x30109182003010e010905071d07050a0f0e03100603110109050603150109030218090705090610030f060b0d0e0735120c0f0c1c06020f040905101701020901 68
    0x200002d80c403007604581c1381c00d4544c07854061b01c040c1c01c00d4009102641c0c200c080c14050801c50000001d4a040c00c000050062240030720f036504214060900f41c24452146000d84401a00202150743c2c00401082c1c050042100c0c2c401102c402c0040c2d01560001c2d4042c00d0250111000102810f0039603403044200c00c510060510030904000d051203001c001a070f920b0304407051305c90515a0040061400d010300c245044480e03007010707226021100800000341d5030840b59145903c454900170481c594403c1501c0058080d0390402c00f004640840d00c05031000180d402011456280c00403100c941e580d507040c000c400f200020060121341040b01500d45c1d0002c0c2d60002100116000044403400c0100103810800c94020b50002080740d04035600e0840701320001c00400c0303115201210f0001c820340700c040034060308200075800105510303004540145010708403001d503001000241e1007130000e40341109031600403c1560260850b186880c1030310b00046c81051003568000348044e100d020300e030712440c1006402100d881b0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 339307383 1250 339306133 339306139
    0xe191d0603010207060509030304050d0201140705180915040b0a050a1a0c12091206251808061e0408030c160606060305010510030e0312040c09110301091820 69
    0x903100041c5c1c00d2045074071551801001c1c544a0426103016424494035a4540045a0500b5850703140e48680e0300100b03810450608115a444205505c0020180955000e5a5000681e003013040383c541c410f24442c142591040300d013005142910307410050804281e00815411408205040c0708a1629081c031aa9040280301c2650400c140d0f00d120501e400500c80440700070034801b00f80304045003410a03c90414011000203401c861600d80100107900a040224103150002c001e000c03042c8138020305054a12101c28103441c04502d482d81c1c2c0d050398607001a11000c03506a5001620201825612800380c0110391000c03200389551a00c640d11340c182d8000e4070300307456030100e0503c8003000111507104140c0180141e88010405600d0b0130200003100c1d8011500c1418075050001c0c1d88802d034130200840e0800c15a8801e1074440fa265410825000482034110ac800d151401408101c2d040ca90310285040361b0008100b480310a18101442240c40002400207000b001e0500a1490300000c201800949003406 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 339308633 1250 339307383 339307387
    0x403030e030705031c0513030c200d0506040b010f06020d210203040c060206010b12040b070504030c0b09040615020316020121021b0a03020d1101020d05070e191d06030102 75
    0x98890b9425580003035804045a017442c9843c1d09001a14014258880e5000c0b11401060134a501d028003030094501c401070103024074181c58201900c8851404028034005000407404442501d015540d4103000d4030b0170ba9610f030044000040303240071002070000f511074660103030003584a224001d440284110824036098600414810b4040300c952010358402e900035001c6e040040d14050000e030404106030031103c80003504000c61242841d40c000d25681041d8000400d6000360f5541c50102c070035005a81008090308409000010700c1c00002020f402030b079030101e4041144568031200e181171112006210b03c00f50701300b4800707241901041e03e8000c01d803a0040c1030100c9110301600724080c584003c0150103981070b90200300520300240d00c03015044001ca00c81e00038910407403241c41c06941c1d406c10b06501802c00c10780b24100b041428080d0181d50b541c24110409003c5070909000150108807a0000203000703a0900019445004118080700b084604104009030b00110003240e030140e20310020a807540540d02 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 339309883 1250 339308633 339308647
    0x4061805100e15130b060702130902040e0304030303110406200a0203030406020304090b040b0d022106070e13060f0603090f0b090a170408120304030c14060a0c0302120403030e03 78
    0x441031030b10f44a64626101440f075441c0e06010040140c1c600d4801100c11840c01a130494241c51742c80456910940488203e204c10071007050030400340031085c0000350020f0a00b070728036000300c4000001d8400e0317038032a0f2801d10a58a00902252680c0160f00c1208001034441882e2811506c030a00107049407000042910a44240c540220740785034041d43c088801031b400006c003004404a54030986100c0c01c807c43d01840300d456003000089080c400140043e1046201180d583d503100c0115001b51105e02c080d0307080d112241b81000c1b001d4103070707005e4200007409030340e402e466507450310a0b52042c1e4080e40c2d0301c41c401090207428600c040780103085491007200e1101c45540560085800344c40d9462084c04168002e0031042c4161030f00c0c5034805550a8803401d04001840144000d1a001c502280740c1c400b585096901c941d51418112400c9130b580c0006850420140d0040c22803101c08036000e441115602003d016490703030080c08404130311400b030803458008903000114000921035001070059103005000c5905000b1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 339311133 1250 339309883 339309899
    0x150c0c090a1b020721020307061110090b040201091e21020a030602030a1104030807060f110309010506101704260406020604031b1a1803040b030a0b0406180510 70
    0x2980d480e02c0b005680808800c00c115000d000205404e20300490000784171011a502199076175890b40910424050032030011103540c80c003004806080c5078403543c00e020240b150b0810680c817510980301680007c207405008291142c120310043d0078a181c05402d101114680381c85103014040107881c030a100220320095402591364540000044c60003403400591f01c0c00c00c0b00170007046035024602d20810b03003024841040446c1c03191040c1c50205420060105101040c4550341c8000d05e02d82d60b0402c3d076180d011040c4100c2903015031100d0311418041da802089045c0e203550690300422424210892804203800240014000c0c0031101c1d41c41480c062204600720b01d1200d520001d810540100c170040e03000c1c00030401496803201c45004135146071510b04403d1100ca88036006010b0a1070002ca803144696008140c101c003224502c83c182c603221000b03481d1a00d4641600441035402074542542c00d070304002c0c610301503140c184602c4040300c00c014481c40142180d11621006888001e101c3c4440c0c01c00710200107052a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 339312383 1250 339311133 339311171
    0x61a1215130506041a010212091c1202010501090b0f04240314070b0316050304020117240301020a081308090a0b09010206090d09140f0409060902150c0c090a 69
    0x10144540402c140ca4000140800c4821070750701c2d45080c00c55115000d1050740c02080380461081e000e1022a52840d1220100d914a0307200c0b4608402070940d443c40500744641500288042055a030081c03203540da0307410090096401102c1040e0703100b00c080460700000c0c601680075222080b000481881e01400014012010f0303200c50703009a480440e821103070810100c051001c0000780070140901c80c114200010510144503007000e0600074440e000021506682c000c8c0100d3309080c43e2480034007007a140c03030b031241c0c604c4030320040315490441c3c038440e100d114603d818002e80e08a00a15940e001031581c9411102c0e04131030041c5419212014100149600c6842c0c40e9000c030054040741c0c080070b0351960340e400024a0a100140b44105070340090005a01e40b991000c100d6084440d83d804a14407822544c0004003842c20561195034042d19080c007000030070445401c43d0344aa4000c445544140802c0d0884028503c18140400d0441e0890300d03106245160413129550841c800c1e00001802601d200790a922030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 339313633 1250 339312383 339312409
    0x3060317040317030709050405130609050d1101020903150415090605150d03080c0c010e03040f0305070e010803070f060e0a11090603070317030403020c1909061a1215 73
    0x8080002818000d028241010409002080c1c143c285949000c9000528000d02030003440d2050380c4810114164000d807400303041403550400b200b040880d00c50326000382e0300e100040012012590b216903007841034506209489426a0240140040225201c42d006091000910854803074500c001d140003c46580d03c901c000c034606c6554006468200f0558410080340456480740c802c00a801c0c0f0f110000340c1c1302e007030640c1110401c003942c1d45515203194000d014010244406945210200d00010759441c2c400d20002124010002e44440980354610100136400900030519240e204100e14800141244441010603000e1907000881c4000070341e810b41401c03403c03d402d941d20000c20310b80407018505a540a504060202e00030500c03189580c0e0382601100303802c507641d05403000210014050500903c900407252000a1000d040c412240200d100c1045d20780c0590361941d807401c4004039202c0c4242c008006240e043c0e4416500301585020040b503490030040c003000e50310031010f01d04107640c0c0381c2414040301 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 339314883 1250 339313633 339313673
    0x10f0b12180706120b0d0f020411091201051501050705070b0307050409050906191802040e031207050c0106060f0e0609030109080f0408010e030901050a18030b0f04060b031b040b01030603 82
    0x4618034030360f2002d045d2101c0c06192481007441c150410000b9543d0800207000c82c0e4140e50200740c10031101034030b44d8123000306d01002e42c102d0a10010080100b03410b500451045107100b13030002610103141c0044842e0301444078010101e82c040d01e02400300d0b140d81c002465108406241c168070f0b050311540b41005440058640401d00da00c480d0500140b012602c0810703801107800e01c010080c42444254014210b0302c6000301a025665401c0b0081041c00c040c81126140c44a182e0a03520b1070078250b000500c5580104440402e5520b0501d01050091042040001c0f110556039100345501010701040007950004042c113500d59a1030100100003003048020f01124800c9541c800d0700c451604640a003501d403040c4901d100e070b40042041e42041d07a0003505541801d042407403d03040c0c1003400c0e800081101c030300743c0018002e200014200000c85000c6c80205101c2e51086c60203000c56000c59052680e83c0310442d4580042540c45640700889052a50284d5a403640515022881503605e4460415100c020303000e07811 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 339316133 1250 339314883 339314897
    0x11805150a030f0c1202070303020c06040507050306091506150d060e0106180305030414130608011514130203220c031703100506070c030524010f0b12180706 69
    0x314990103200f10701030b840c0807100074000f101c100c901c000d1801d44a0341c1022500c6501103040824148281c1c15140251130f810700302c0d01c007801e150a102d6a109140d115541c4280f08000004500b200040384d41c0e40d00001140d0040c06503210502000480c000b2032900d581000418490310480952501401d030013440074885d5080035504080d0010030a0034142a01140da40c11101c0c10400210000704403030442c4d4035000e8424404c00d4000006220132041e03148040075905050340800d12803810b40c885041d84c1c6241c16004c2d05550b4624109001a039543c400d1035108190740c020a491040325001568841d900c2414141c0801024420781e40e40300004505645110600c9801c2c801c001101180c00320802e51074803810305503c2e2012542c0544811801b0b05402aa03010864400f009102c544181c00b441d400000c0d00c0e001c04007884465024829100303141d40c00040706c030002030f00034410303044401500e0021800074034002c1806145401f0280c0600310085801680f030f00c01001401c2401040080c085d15a1451 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 339317383 1250 339316133 339316147
    0x1050d090b2e0e0a02160209071d0405061809010f0903052d0d1a04020f2a0d11070f180b040c0c0f0201020703140304050307080c0a030201180515 64
    0x10030b480b80112040c2890000040d003840324005101c09660b0004084502607079901c0d00018024582030b400c14000d4000d8410b60078071007500e42100b45112500c00b40024080d55800c034104000179100291101500014036903501981418001d011981c00a003850020801030001084542156240d040580c000780e00441e00f0340461034500700741c1c00c1032151154031442d50042038958107014450031504650482d660440701e901144070301144096000002c10443d11445c40ea02400c05070380c0b2400c09141c448240320010703c00007074010076400350010284000c0441c507071070460a80c0e0141110040c000d07e40f0481070005604000000c044001d00166a00300b0380c42c0390750250364416034440c41d240c503116500b00410107002c1a030047c18040e4003500150042540f600600050b818018940c2018000c5454520402500d8600000402c00c0f910141c00320b5138800c0d078444c0d07055200d00040a0441e8070442d00da10070009503110702d8506511040e080d001c0071025507260001743d06002c0c00c2442d180d5041002c0303462 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 339318633 1250 339317383 339317431
    0x601030c11031803060903180919050f0603010b01020a050316061103010603020901120e0a080d020d09030e0a0f030c03060209061b0c1806010206011703040b0f1911030901050d090b 79
    0x4550046d140d42c008504100300907000408060601c54032034082d480040c00203012540403941c0e8a1811107811742003265040140b107101511404403100d900a44c02c00c00100b40a500c0051880d1201d03030001c01543c182140e860608044580484007542d0322510358401c0c0b50000c0d1001d00035802000b180d100140da410052001403c5090840c000c000030901e001d42d172890400010540e400b007254410710352645e640d00d8003005c000034000d80440f684120300d0444c040d401c25405c21b9203007800300d90450b41000001e40d41c2884800c01304107800024080c078140c0d401040000c6458000d40504071009150b5804d0170111414403480040064120f140c560007886070341003600f001241170500b02503480da017601d1841e03c0e01c0041d64840061180c00d00b4245d8400341c0140c07080040c4181c402030000c1a04155a0303041c5103021035603540207041030100c1c0362503180c80a1074042c0242e000c2d04603454600081e5062400300001034641da0042100d0003030094442c0340c06000568001019072003182e0306190504850801c04107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 339319883 1250 339318633 339318643
    0x18020402120709081c030f020c06040f030809010b150c0a050a151a010e131b1d01020307030f0503041506030510050105030c03070509040f14060a11040506030601030c11031803 77
    0x1001d01c070740d04030300b1750611881000140c102c146131060501150901c00344100e080203200c1d80c03643d4042c41c081d00741031100300003501c0303200c5043c103000f80e40c0d941c0561a41c4402d20300b01c5514001403580007580180410180c2414005002500c401c1c00a480e443c140d07646a460500341151030466001c215100c400f0034000e01446028000301520031019490b1400300d002805500154207654807525115032000468905504961110304a0350401c036000c0c140c403100a003000490341409112145003c01c4440d07594400402e0341c03130080c2c050350f4002c91050880341c00e885952002e0815240008501c015510300c7d44140550b800540c820b0000748027441c01c0007100400c41e4410b800403442904480d40900c0c1603940010050290307082221694859201c600e807040f030004900c84010565401d84620842d494804103803648107244014051010410f042c402d0305251085000d6180c0c0b2403002d00200d90b055100e540b2000d017005180c01c15521003014002d00924541100308804901031300d0702c1100c034403030506001e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 339321133 1250 339319883 339319889
    0x106060906050f07230c01030612021c03090906230306060109090c03020712050a020d11060711030c1501090617070501030b011202040e0708010608071218020402120709 74
    0xa4910409401c0100041c414403560b5089001118045903450900010104801c455045001d42e03007045e10045202c40d441d03642056003e80420b03e08200003031283c1c495051402c00d9070b4000e050100320b07030b40700840f1100c595003044140c003042024000400c10100074810308003e400e04207a02e02d075006c200c4203c5182c407400000c00758041d0b0080c4040c0b2403180d80040350101038405061010400d40140d0000300e000703029a48001d0212915900411f150541110013402d0040300c590035681e00d40744e901c03410b072140001c4240104a0341d00010015221302e103d103040d014030720300340f809480c944018140300f14078140f0040a1a05910003601c0100480203040c400c410043c05409482c00d090104408501c1e01c0703c03100c1c480e143c14507466203c0d1051603882001c3c140b155a00c0000219120360b21401c0b0b50716010b1003181ca21010508400002c07a0040c041c2440701e20a250941d03485401b02006803108001c0c2000074007581c03400d850700c1d91080042ea11030010f00110520030701c3c40c07181440c12410003805161a54 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 339322383 1250 339321133 339321137
    0xb070210050c0301052d120c0a0e01031a010e060f1f1106090705010e04020c071806050102010c140a0f021f052509121106030901022221050703120203040602010606 72
    0xa0b4019655076480417074a0090b0320207d62011803941c0c040c60203030130100f921400d1580081a4407021505c003000c0c005d46410b0741d0086201c144604510102d070300b103003c402e01880281c1c0481c1d600060b40d600c4c0c00091501d4104000e8031030b10410f0b58102e901c60b14103103202441d501148a0100d00449100200030991380040f0aa000301460f0f464400041c1000f003c09519501444d00003510a01c0480c0070451034000b800c03400b040881900c0c0d00240300e0001c040e6030041a00650800401e914601c0c030032555068000002605281b4122802e1404e445a499060580341035004d10711070302a081000309001ca40c004000c0b0004541440d04401003a00036050341d034007090420010030100625a80610000103640c04d03019009849811400c003942050071089102d58001d0002007003041c2c920f03064001d030690196204070f107155a40d01000b0000c1e100785501881c50035094070007a0911050b000718100303004500840640d00c0c0706807a40c0755682c0402002003443d015903c001403c0101650901c2800e000701014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 339323633 1250 339322383 339322429
    0x11503150b04090e1507050705010f14010e060d06050a0911030d050f031f0609060e040902240906070b040b101d0403050903070e0703270b070210050c030105 69
    0xd03a070744031070b000b40d01400d407402d41e4804114454580400048940d11400140c549141c6003646004095034000041190b49508207044005680f4090003260350485e000307560062141c0c20114401150b2000404096210003502c0b8410f010071620301ca0540a080c00344004100301da180d06084e0a40c40c0015101d9010707a10060b1002c3c801c0b41d10000783d9074071450214000da40e944400c4110690840c804010340c45180e219200041d505400c0380ea10f604646a94441c0034407456100c042008031440c414003c0e40014038100c040454854444e240a05d60303810712141c40c14107a5a20210310150440082180c58104800c1408240031a9002032980002034908a0400130b04109010054100f81743c080c45440c00403d01060405001e801904caa180c1e01904650780c841d55034070000c150300c80035500a00401e240c49216480840d003017211860008070040b10b40e81d5146259500121814020040d00440c0100d90f1405402d01181c000c0f5405100c1680449449504140030003844c2014403514080e03c0720380b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 339324883 1250 339323633 339323639
    0x9060b03010506090402031305070609182a02070b0d0203090715050d0b0d020405090706110729130315180210080402060c01060b21010b0d0b061201150315 68
    0xba0504a07284d1900c2640c004d0784949031400c0c60b495482c0400c0009140b4000d204c4d02142c107690100b5150200c07014040c0e20400070300d0030f156040483d4801c3c00302030928031048a95808000310b9040092602c06144121259955550341c942c03441c0e01300b55007042000380c0001c280b29000b1400c11620000d003200c2c0704000c40303800300c0341c4d00a4078a124100003120b665844403610007140d510780c500c0030a00f82e00940148590702e06170350a03c0d2191114000c12000c80d9040e003a003240074400080b03101c04e51340d110148821101010041401032a07002c90340b4106035a0800100c03180d010b12801d007200651140c0300c031201852054000d0019280e1041d02900e100c402d024031000540d070350781440c0c9402107003410328100c25100c0d8000302e4218814940c0410f629820000c0c0010310f9580c0d00f00034903030034000031013404415041440300c0b030010b2001c0c031a240c0440002e200e1b29544e011151f111144448006205624100403a00401c4108409034002004121a40842c03c54240c05028075003210308005101150142 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 339326133 1250 339324883 339324889
    0x6020304230402070f0501093e0324071205040b010b070201110609150f070534030305010311150f0a09030f05030319050603120c150f0109060b030105 66
    0x84104829881110600304807810303612554112800350f90401055007615502d0700702140a040b210b0011142030300403000d0a22201044003410320855031600c545511002c0310419103031140d203400d518560600400207448060300c07042c0d03402d015038800d004441801d8070b030a11003e13041a03881031100c00301038141020031002840c9a18103606603049103146540b5038451b400100c0700030b944d0104000030f500c103000c284000c001c0300107091a007142a61403048a20b548908c4490b002103415510500454824040320050001da905124000070340c02c60402c0040c05240b10310b8803003030503100c6c1c180d000c030396104010302c103109803166a4101c4400a517007a09807a600040b18450724805c2664403895a0307030108408440b04c0c41000da8000464110220018031001402c215887e40e00980700c0600c401c2d582e98401c2450f50b2203000c0c031446814020b015140001c03d03200c24000c01d9111405a03841405452f404030140810190640d0140318401440316096050420000c100c0d0050b800041d030700d40c018001005960303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 339327383 1250 339326133 339326159
    0x9010324021602040e0114010816050301091e080f21060d0507090b04090b0405010f0b010807020a150912020c03010c0c050c040b040605100512010f0302010e041e06060c050706020304 80
    0x10b03030541300002c03400541e511603030051103c40c2503a01000c036108000648980c0000b4062401c00c5c14603207513400c05070b03100101802c840c045003006201c85080e5a0426041e5590f903128003c150181c0c5041c0c3c034150842c01354444a5001c0d00c0352181c4d25600958210301400440d01d160380c010416266240c504009403074480e99070000c1c0c411000e09548989494100d0389540e001003030071540c840042c014a052600c0d019000c2c104a081c61000d1600e0300180c200c0381d6104815090280003103401030b1003515040c4d1200c440c69040c0101000308940c4130b000c00c1c00092a80000100aa00035a01034040400715030304150030758021840b00c404204180310a000403810108400064200c1104d0015884240344c001c5009440c050f440740fa80408102000801a40c00c100240610303c2480713a00300305a078981400840d008424000070f0300062006164080d40c2c14954007459150340c88800024036075000c00584001d44020f9000b1400140000d8030903000c0060030882907010707012600141d402d25081a405d072440b0303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 339328633 1250 339327383 339327427
    0x51522170d09060506030607050306060403030e01021204060809070e0c091201230403030e21090f0307060504030314030108030a050d0b15030609070309020306060f01020c0901032402 80
    0x50686000c0c0d814940c8240032540c00c03440044060040342090308102c4000c1800301d540d0b50003030041400042c0003900c58411a0b100702c0c4001c06090800c0d0039602c0440310515103c480c2c0c0d0640c880c4c90034943c00d104407100076000511140e96800c0e80c510344420b6860520390941e001204200100f02881804164203050300c1d484201a501c103105590860031850241403207041860341c0307401d5601c08890105641d40304074802c07800798400f03216403d402012295100003540c420b00300103403002c070f1380c200202c010801060710b132030020840017140c1d10b00c0c00024105401603000901040c80014200200b5030803010048031a0010313080b20303003551324202043d42ca03481000100c2d8100000000d501c1c0c901c0310150b1004030015805001700342c540d070444503100003d40c4266125881074180b200001c08661180c05040d4a041d4041c3c0900941d4407440180504450044009419400b03100503035000c6031540c05d4118021805610640b19001c14203a600e07440d050802d1030300045500400900900340c550700164640 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 339329883 1250 339328633 339328643
    0x201050d1a04051501080907032f0907020601170a02150a0203040f09090201110610050910030204110a170903070201080408040b071505090304050a0e100b07051522 72
    0x1410000000101c21000c40c906460792042c54103060000450028044115141080e29081101d0300d410a100b076407501c43e4880181510403030000d41e030310001c0702c4101d555000c241e00c0007229504040340015007980c03c12280c660040c0e20040040210501c3e403200c900400c0e1021000e429002c40c2500070404480010046800c2601d00148a4080c0d41c420001c850081140710044601d90b40c84070286030140014450071ba0005003540c1c103a80f00c030030012503014000c40e040450105540d00e0042800756010303006102c041c849010000c0000541c50780d01403074800448061025548004d0343d00060042c0541248000081d59a034042144016000088401941e02400d11003c180d50307070b142510051049820001d510100400c01d8001c000d0101103081c1011003034001807140d036403001041541da001d503101d020b40c07003801d403041040003106a580f05900310019030940408962603682d01c00c80c50340701c0501101c02d0b501030501003000c880c20380556a0050301241e400c4000c011194241100d0360b0780b840021704 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 339331133 1250 339329883 339329891
    0xc06041e1106180303040f05010806060408100c0201110408071a071e0c210506090102090f0d050f01050c04031101140712021501150215070212160606030609050f0a0201050d 76
    0xd9000f401c5036a101e110000307080b240e45503140d050908056050340326450118164501007801840d2210695099070100402020041d4142480b0710140904410b400c0c15551b0750606400a41d440400601c090300b0f118004120851401000c00201d00c0060f0f44c818060703405119007000510180d24100c0d0920344007141c0741c042c035070a052104961009a0140341650150403030101c58855410100740071743d006406803183d542c2d034104900d09034403480028690159925405211520f0400c00410507180680100c6454031010030034142100d40c15104403514510108040040010200c82900008070031b10b010180440c0011281d4a00c2c001c03280010103c3e0300320140104200c0c420840c10b030200140041d0b41c0c45950b951101910b0a49040c0c49403401030041515241d490281100702501079540c56008020481d503205500227160030030041609000030010041000c04e855000e141d000c0c60107940002040442490010729081c118254510a50000510407000d41c1e00441901c100480e1240049 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 339332383 1250 339331133 339331147
    0x206030f07110d0e01082401050c150703052a0301030b0c1306050306030f06010308030708040318091407021609020d060e0a090203010e060f0705130503030c06041e1106 74
    0x10b161558054045055445201c031041420b691115040c0100035083c2c9410314075884200d20210721664401c055036104242e01d036800c0841d4401e2008104112004040c0d98002d01400b4102e03024580c1504e080d400a0780b11010b00032803860001400790340c100c046119210140c00300b075072581503000500c4054900301c4641c00142c01d07d1512811990b806c0b1030369820303020385911400068059001500d906000348501d80a42c48525800500e9505030381d0042400d80c1141d44000b13080700c42c004010b1003241003014280a517a0b88003914501c0002a009044020660354142d4119202c0181c00404550440d80181201008107aa00c40070f80291801442d005d41d581042c0c6002130080c0c08268003500c2200403d008010114070954030192100707100701c000340035000c502003c141c0e8500c02901c0c07440404902c040031034101800b0f0f90041072860703180502e0b0700e20a59074a001a0454000007002001a007105040008201030202c0344c803e465006c281c1e14070901c10fa900c40013107040c40d0023070540c020b0600148034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 339333633 1250 339332383 339332387
    0x1602060f04020f130501060e03030a120b040e1b100509130902010e0d0f020f040c050d0b1c141e0a0212030d06080f1005040b151302030709061103070206030f07 70
    0x40d007402c064404c800d0400340056400c0203101c2440b8403c0041e264145640e180d18001c8112001c0d00d003541d0b19034840801502c41800100a000c940351b500c140e443e429004079071320078172282070340c2d0958501c2e400745000c1c030301d00b0b11003003000f442ca800c41002010001d50b00d15075500c00d02d61a0004440400003000d5255100580b079800c0306011150788114001000c07400c22601c46000003482d03200b601c0c9030f4201074245c17080c00f0641d895a030b1080c0128005205008045546a01020505038010181a0741d668078082840080000302c40944004640900011070f00d4802c002009643c10b000c040e11302000024955291298a1580028402c000800d04c4543c1c1c41c2080040d10107a030180c440800485a58000301c6070707208640020907000d8003070740300d0000c5d45041511946102d03a8114a4040c030913500c0348880400c0141038041a54019601300c0c01c1102422207102451003010640c54403240d01d81460005070185c011402c0c1c58910b41d108012280050300c9001c02c0d43d41014000100c143c494550102c2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 339334883 1250 339333633 339333649
    0x804050a050106080a0c050a08030f070606050603130201170f01150504051c0506010f1d0606070b0403080723040b0f1905191e110a021c0b1602060f0402 67
    0x90700e5582008000b0921540205503004080d108072540a126681c03801400320f20302081c032a010b441e400501c5122b800340d00c1503009080301480398000003a41521440010103a800507240c0080c042250407110045503040402c009111005603a62449131230b0030200b241c284003050082881000591110031083c0780a40b061310081c0000811200b5541c10b042d002e40485406440f043d541441100c00000d82c030a20301d05888151400e0908084000d03c2e500040d41c92207002030965900a00708100c004085000f00c01d455008038032940d2200381d1410900001041e03600317240701081c0004511100a00002104411901100c04181c502912542000f6510320a030148082c4c40e00007022107440d55128036070100080c0b0800d108070821002192a01707000300c03080443d02d014070170001c07806c000031050300c1e00419003514502444000c58119080c0e41c1d010030201d517964200c01120402c1304004030308101000340c4541c0c3c0501068030308521080c0085009545800c0600540410324410010909640f26159 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 339336133 1250 339334883 339334903
    0x50703060b0415140103200304110109080a0c0e0a060b0711150d020c1209010f0c060209180603150708040f02030c06071407050406050d06111303080403031403060a06080405 76
    0x5803418080c1d40d943d05800708070744c800700c025000916100d90b0b10a4041560041401c4075440744486080d40d86541d00c804c4420017203100d00d4180181c2070030008034a04200641c5246620400001400c04d01e0003000c1c0c8030300b62010301001d00e84ca08007401801003080d00800c2d42c00c21034000c0341c00ea4142000d00085081c4440e40f060811710102c0000d40b03480c00c04025002000c403880810304417002c2210300f859140e11805102c0303200b0300140b0304a00ca07550491042c6010440e46003c0c41c00145010a007900180c844c40c0b841c204130100148503001c21480340b4092085e0b404803054481080b40901d00910020702081d0000d000901e003001189039102903441c10403d00c80e0304c01c0090240c07540d80303800c0d082c10780e02d92640c406152078600c640100810f0034182030045200701d5078040c0441c083c01110395240005080004c0c400c079550b0718184510900014076801020045010320805680d0782e0460030001c01d0303140c400d0708080c400320f410800e012594480c85107403001c8502c03a26011506440720701c0d00c0d031706001a560b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 339337383 1250 339336133 339336161
    0xd050310080a050a050705030d0504061d060a09060905190e070320092715041b0503010602061005130903053105030105091207020a030b01080c090a0504050703060b04 73
    0x140b04502000000500112100e0296044072580340e510010959100804031980d030006e14140070411105001704031081e00103140d1501181c0c0c0c450168041525504485820130009003281c00401020b500a4000400790805440c15440301440c0101e08541ca00700c0d202e42541c4008040001792400d103e94415580d9400048084001102190701c0304003507005501d8035441a410f4900d03045004119080c960b20040c01700b200d0f20404e42d20101500c40c407000010b907041c3c009486107003554a1403d40310b4010b0081030592105916541440360081c5440001420f07105d2a1400c031703406000d15920280000c00d00640000e012502c22601c4c5821203840c050003502c000d142380041110364085500310304103054080c4e801c0d102c54846550300c041500340c81054070b122400b604080401186040c1c0310f8014618940007820341445c55070303039580780300010109902115064002060802c0b0a24140c5801a04081007034414417090509848142e2990402c1c0700003032110b5903d1024076019100c035006103604250750 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 339338633 1250 339337383 339337393
    0xf0f0c060306030c08240703111204060c0c1104020306010e1314060103090f12051c1e020405014d010f0501030f0b04050115080d030b0a05030d05031008 67
    0x8000c00740103440c1a0004898002c00e016000c1403501c00092102141050180817906c60600106088a040300243c241c0c010191030700c61600c0403e41e00f80060880b0091304044000318074050a001048410101d12201004100811720010805882010048000c1140c005a4903212070005907861030010b004260044003007500b43c0d0950b0019400aa0b00190300c1a88603025078812004400703c0e0310f42c080c02410104860900d501140800600b144800080e0274098a406582019210051849d0f940c4d8071116840b56510440d0f0704000e5503000703812055010641c20f2904000001e45000f901c29400c1e0790f881d401000c505180490309003180441c10031748000f18140050508814020412508100000d41c20001e02541c0c08059100705070480b6081703004058160300941e107a401c2020058030980e210340d01c4841042d80d04c4042d6018800a01c1804020840c907004048040e040d2500070301d05900c070314a07a1b80c003001162030116440c4c814154502e02030b5582c0d0744403820b80d00f52a009810a01141c414 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 339339883 1250 339338633 339338639
    0x40f08010207120e1810030f08070c05030703030f181715012411010908040603060503100c0206060114040e0109020426070e0403120e0c040f020f070f0f0c 68
    0x10641c001c041180c01107805412140b0000400d5513a54043c0100a0308415814006514242084907035a04528600d191407121603507621400510726030034105039110740c070014981c410041d81c2102c15006000a802802000c3c0c69514040c0040c03110302d0088080c000a0420041c2224002109901410a0003602d0800000744400300d80d40382e4881e02c0740c00420003080b0002c516a1800116100200c030660366000c0d00c542c207018125940c0c00481544a00c1d9900c1d184003030005172071071002d000036103156580040e000c0d00e4a0100f505d400a8850400c0d815803a080c610240355178040790b074660295080c2448908200c0c0080104050310581c2e0102d5458070f2540000700e0100d9181d001407080718072180c501c085200448a00d054100c018940c0c040c2c580d80000c6c0100a80b6a56001c002e0340a4041c2c107062002041c80c40340001030b180c80314500c840c10b8000c41006005450305120304224006084003c500304012010b64403114402c0d00702c05081894140c1c0d550042002c0e000f000c045a682c005028596159 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 339341133 1250 339339883 339339899
    0xc1c14070906060e0604060e1503150406061701090e030c0714031c020a170c03030a0e0d09120b090f1606141804090809030d08060f03010516030c05040f 67
    0x103090194020050401d8800921140705a640d4014080024062031409181200a4500c9680003030402d40009520000801500041003c1c61090048581c00701040c0c1c80341d41008104c640030f410860521948202c504032511690380d80c40e06549142c50b001545640141da85403950260422800c01c9105210002c1201850200c01301c03100607081d002c880180c0b840c800c0d2585010000066180143d100880380030220b100303804840d9441c81d000c03003140d14042100d40094110390080781c1d400703013280d00d80c2c0361a00b1410080001d00c00071540d500c0c100421904010510544120000c009841240060041350500c05c040c00110b140010700d001311803a030351a1501210245d00148100b4005c0342013074044007903d0f83e01004070b409042081802ca0034041da10800c0100a0498041c00c0d240000b05000034130054070200100300d10120340e82c9a24580d0b2070300038100603501c0f0500400034000d03410801403010031000c0d005001d89445260401003144540b06100312500d000b02d50000c40030300d1051000142c0c2da1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 339342383 1250 339341133 339341143
    0xc0c02030105011202010203030f070c0629121504050102090414010e091c05031503030c0127050307030c05100501060f0f020607020723180105130501080c1c14 70
    0x1482a002440103070b0381c8101158404c0c10f6800040d0140e00b0030800640405800d02c3c949900100c1404c1c031085407a160384501f0225040340030400c11002d1041b074064000e448a818a844807035040361038500e04501000c0e02504c0b11041c4807054071019401c00854200710080d0162110302401800c108016000b9160402c5001020300c10342e001c001d04e2401040a201000c1f80c076601041000504544c1608411070446013a44001c180106d4013210340340c804282c0e0b0307092004000d0218408000f0030700c83d0300c0e1701c201c3e0b0494640d0030380f1410014109070704400080d808000e4a15454050400650440643c1009428424956040c40c002d52501001050141c0c000300402032100c0e2070b075218202c0203920407003661307203003001e5646c0e201591112a0400503100c0140c1a0400c2040d41400c1105000820000c00c01f0b180c000b200c181e01140e031001c014846418800d90907807010858a20601065140c46c0e4040e071a0003581461500030076120044629159583c021110401d501895590000b4001070580d5107032 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 339343633 1250 339342383 339342407
    0x121b070504140103030813080a080910060605031803040e06060304020a0909081e07020a051c140a050d02160e042d11010f020601170f0708010605040c091d07020c03010c 74
    0x401d06c040d001c2542102c5101c070011299a204410030b1500c00c0011094030a250002c00030b079140d1080035240c3c10070035034501407040282159222151241003040220208100c100a91f04d255030003400f0401ca0042c1070000282c00c04402c0e12015074a03280d50000c221140e050390440300000d810311486408020f542d400509004205010310800f6030244010041c0900c50044040d5005410798000d1000d03180c81040505480d404a14034912807250b0f0fa6140b0350341d505418841e036282c101c60703a10740170312a0500c0b1003560a1120b10190040d41035092800380c4c080e0960003407020411000d000203040103481c400d2613030031f035001408124031141d4201891141c4c5101443c00c0300c3c0c5200780100d80006d035019100302419038402d500a00a980c0c00c3c41c00c40c89603c580a050005d2901c030f40110044560300500680c0c010b08a007500204d181ea06000500c426541401584000c008144804200045d0341421041411281c0c0d80700480039129510304070301e02030301d1300803003a415460070704501021074001c50b040c106 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 339344883 1250 339343633 339343637
    0x30f0c030403020f040b06090925030e060f010e0106030507020111070b04110f010507083f0c030601091e0905011202090606190c1a04081b121b07050414010303 70
    0x28212183e01440141c0e0300c0f00090640000082c031180b248c6207001c1c90000c0e400429400404050314108601e02c510790b00082c4400b0100782e903010381c030304c42780400c0c09a1540f00d0f8003803621001551426100c0010040144a41010180d030b440c04291002e100f900710103403038400e0340035854444041c1e04180010400c196411070b40d000b0075150f80b207000e00702289d20080c815016100c3c0c50400740d95448444407580000d040c0704200d603a0b90014000704d031070300c502c01114481150440c1c00008110114403840c03070340505221b400040034030400030749070707448055042511008031a220440b2b40400e04040d0324865a000048402d042c000089201070b110403804007401c0c022a426081d644440d002c3c04810b2144208a6100b210845600c40e17444d4090302c0b044c54000d2113403544102143d044a20545002d4060350100c41c2018002041031151010008102008415038081c081d1808000540103c62180d1402ea04808421311010b030840c08082c85080014500a0414043c0713280c002c1c11102da81500340000c0300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 339346133 1250 339344883 339344899
    0x3040209041511280e13061a0702090901152607060206150f09010509100b030c070c14010e040507120608030912121602041b020d0201230f09030f0c03040302 69
    0x100781860391100b4424813640d00e41845070000b0905010b1b0315410041c0000f8402e0704c60f0300c00035641c03000f80c8451112414101e10039460f00c0c01e1348100925008050702ca5815071b030400c0c0743c840006003520110f000303c401868060310300c2000e4561141d0200a200406042400303050400941c0540200e440c1d807003140303505024028078050000b0000d641d80c1850566420546500c0140300b542040b00a883d0030403100700c83c2e00061650f581e80628107500482d4400c284100c00301c0c02d4801c0100700c0d280140a400481050807002580b000001c00d140b410801c030a104070345801c00305a107940541820305550410040a005041d21808000c0d45d07a48010009805090740e155460390000010410184200a8099007460502c4115a00280444154040e8bc2c4980d0750f8440400b2043d100168a44419481c2c016008000460030081d0840f0740d81c040e40300d800b00181c001ca901c00080c5041c01e035809800c61101d0595900e03003100c070520710b0161400b410074081000408241c03294001020b40201c0f1b2003241c1d841 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 339347383 1250 339346133 339346177
    0xe063607020c0406030b0a05090a1e03090b04030803040b04020a3302010e0a060f0213030303090204050c0a0c02040203100e01060503160e061c0f0f0b030c040b010503040209041511 79
    0x203c00c40c0c407a0320002c0e007110081008a600a20755801543d000a0301c002100c0f00f1245903100c0b07070702520700902e18115500d4418054020150030803406030050030130b460b1180c285403841d111070055210051008102010325400201107580782d2404101400d0f007801078040480fa01d03054552100c4c14094840030960b05081d8804a0510501400e0441c00482000e0304044800d03033b039404044c0440e1005061301540078422070440105416154000314000d42d404900401c187c01800200d40020748034150b03c60b010404a0000c82e00144003e4110b0b41c143d6005941e5a2141d542150210302900140b0340c0750b18070740000135150380c0308003d180548143c826038500058034510070354010f4401001c541e041081804002068a0001c2481070300c600001000f0440300544505001100c40c1c407105c1c200e20a51780e0071038006600301080002c8900300700341d408005211845001030303c07500000300000d103d1040c80000504104000641c03c11a00030301105001c500c6960344403101c1504000f8003070700c0c2d020890b0060307 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 339348633 1250 339347383 339347389
    0x1a0a03200d0b0306090a1e0b0f01031101020c03031e120103110111060105030d05210106110f03090d0f0f060f050402120a0c030305130512060103060c05040e063607020c 74
    0x68040c017181c4c4001c04c0c1c2d0029607504c4195040e03007031608a8815071049413000102c2c0b03e448203580309a00410303400302690706624015840700c414a04840c119804012410b800751800402c4174501802600c81c0c40b1804107502d0050f45a00c0741c02c0d5080711081c2c40c2000042003040e01000c2c1d641c1e108003622583d02c10030036025800d949410074400c00d54154007101c641aa224001e900403c1e60304003000b1451103403181d49c1c00c03c00e0000402e0380030200059014206035642c100502c9440c20180031740e0051450485028009405554482c0c03000c0c1004440e1681e180030003400002d070107a0103512090a00c2614102481c0e44002c11044506034064800c00300e2420a0003404118900403580c4031180c61122411500c00312440c1c1c01030b4104004040704c2c03460120745a90f90710200e02036030f202940100255030440c5040000e64a03114441d03c20b0000601082c840030000b81100c1e50700c0b110640b0b555494441000b1404041c26045680c0b000310190010a403251060781585e29215400f90b408940c5110904028 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 339349883 1250 339348633 339348643
    0x4030c0317180105180301091208070e030307110a150815010801122a090504050d02030c070e090c04050910200706151a0d05010503071a0a03200d0b03 66
    0x1540c400d4800002c0b0050880d13000c0c0f0090858444038600d5907000c00864000300f4211000c0c1881030f81ea0b0414070030807207c6180c1c001e1815902088038034100c060180c010f07012a0341c070300840e40b00400300c03200d2076005a00e84d01c442c0c840d0401443c20795036218440120f85000b50040364243c58820900c0c00f4400071220703e50254501d5412030322500c01d80b0203601881d455503619010305a07403085c03c2003042d810540d81c4410040c0394a0281401d0013000076981458a00145041080c6c09242d0940d002130000b101400ca0108071002140c2d81b2003540780f0301c4d43e21007501d80d05140d03007401416840362900c0244094003c0001307101c400308809900401020b0300b0800540001464850404007100c010020100041c04540200e011400b01d043c84400503611440d15101c800f184c1026038582e6074002c5841401c00e101409001c3c0104000d601902c425410052440c01c4148100c0a8009034200054954106ca106e503103d900e200300c0091040c50003081e180728005d0150310248002d0b0407107040002280180c41d001c60307 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 339351133 1250 339349883 339349897
    0xc011103100e01031104020c0a020a0b0c0c09060612040512070f030339110d0816090509040605130204140703060f2405070f030201051806100b03060604090204030c0317 74
    0x9440d815504170401000080d6209058000c2c080c0551005040161900065000078040102e6100e4586c08200781a43c40c2401c41040c06210b610000305009442d144c000031600400300c0404201c00a175030701c2c1855480c100c1c0018091081850000e0214148007880064020441c0710b030340e003402138400e05022a0180707004e007008068100c11101c103482000b040d04111448200c050300f40060176001500019003001c60360b9a460002c944a002004503102d900280440700320300302d08100303800780c0c2400080380070034100501c0100007070340d40d5000c10507840080c000c0e00f4807590b0092051080711201c2031048040c00044c3d0760032001c2400c2580c04925018130402e05001d80709100d58101d5003524440e034400311007a0480300001031040800619022580c1011080c1c1c40b1030098001240350704000c03140d01000022070080d001d00b13811807c207010a41d140c22061401301c9403000240c580701d8a034607001803038912980d400a80c2d002c0c030003c0c0000420025010a404030f0b4082c020080c019030b03a151480c551486451 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 339352383 1250 339351133 339351143
    0x30e070b09010c060203190506030a030e1009050d03110106170a02040b010504170a150c02061302060f07140106050607170a0c020d06020702040b1c0807080c011103100e0103 76
    0x14014406000054007400500c881490100c00c2d492440d25075108980c0705a4084401c140140784a070300410250140f550064010340081105c3d98554500921200700808403034400d40101c00007164403449815014003a00e0018003040c1d4107016890013500d980340840e044e40e61542414400a40004280303540210480200041d00f0301550f50346c2088000c00c07403100803c0c1800b0043c400841e990000c10022141e14419600401b280d002c1c0e0708240448442c07400a8901260074581101d41e0b655012032072070b030000c050317040c50410305d9814400103900740142e460704000724401080d81c00a1140c5801000b404103207110080107913a4030384091003070328032034000c1c003074140381d00e651079008080110700003094100c3c7d0b20b2034482840107156001541c2c2e1005c01d441078440030380100301d400a61425100b0708030b03480400c0707441421126684120002c1c84209100240114601080c0381090100e12802c40d503523003107440c0080044202101001c0c1035a0016603c0b6080c50010348000300301d100d0500b5059040c1e0f5005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 339353633 1250 339352383 339352393
    0x4270509120d020d020f0c120f0904090302070305030a030b0a080d140d09080f0702040f201c02030103050703050f010e1c0e181801180f050312010f060807030e 70
    0x40d1003565550780310700601815658200f02004c076070021803025248544040f0580380d0740f6618202001d103000044c2c60a0a010786042003903120292281007190b0b0000819240452400c4190a00781c1c140000d076817000c0c02d140000203410f80717060350661050340454011a012040c8075100c0c0c05407903a6507074041c205408218951800d910850342c00b0040c020341d00c588803010400d03060640e101c6503190003003030942c40800740c040343d850114030300342c050000c007115890001c0204000ca84540c4280c040304000c6603004080004009000c0c1c180a040303002d100c1c510500a5542c1e5a4918250f03550f5003051000b030302c89002d08045100e0b8038030b040c0103c0c0d02180101c001040502240321080e500c21030340c2c11001080c40a20300c8103072820340380d0341c218030b80700d49038000988200c7c6402150024101e0014041040691500102401c0d00001c1646031850a421603044480686c0f60f103851455803180c0d40c4d05c5600c80101a0000078440d20b0b01d44440b00b500d55a990b001d51649600e00213505464a41081e80c02c15004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 339354883 1250 339353633 339353653
    0x901090b030f070b070f051606020d1409030703030809160308070201021213060e011e0207060306090603080d09240c0201110304030815040f020c0601030512070804060302160804270509 81
    0xa15506e141418000c0040c0c80d4404a69a15a07140d01125408000507030040c940400600d40c105420a640c0700c03c0442d031518002e0100d002035168203c1e0701004042c020110003007005840100030200e514004071100c0712115071241401e96164100c540b04a0061083d000c2c4543c090780d5210076507940070b0b18010155012410004203541d0910422040c0d4100088c04044c10400600c405d2504075000054025000d220304102006042d500d0759002198220f040c20410400281130900300d401804846d131000501100394034100841d0000786407424130405400440d4000c116180d40701549451068001b00721044219281c546903020894010b004106000700140e022800810f0100f4510f900a000081c08440d000594040fa003120418095075030111006200b084170801014442c0e13040103440904040059841c40094496801610101a000305241060882c00e014505500c0d920001680c0c0360707070301d0f040ea4800003054a00006007408a0052004c82904c1c070744501409000d5440140c00d80d01c01c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 339356133 1250 339354883 339354893
    0x16030201080c0a050906030a090b0f09120915130e10030b13062405010e04060b03061e130b04050f0705030703091b1e08030a0503040611090901090b030f070b07 70
    0x403400110134850100900055942d41c000214030440d04502d000580c0001401c001c50003140007041c0703507004c910780f00078000c8520f00003581d1890a6030f130003140c030359501840000c12841460f8809520958001180e040c00d00300e029240842969280ca002e2945959071010194030180c4500c0090560360914000c29080c51004100485c01070003180041001e1002e0150030083d2061b010802c40010014441401103692090340c100c003201003124148500c43c20180c406036688405044a4410110000a0720001e002404003821190004003505d4602441c140841c01038103084040318440c45c5010000307241d40708080500340c010f02c01e07991694115560b0960039802400384030703415901d41291455407000221240c203040b0280030442101c4080b40702e001c0071500303000220f4100300c00541040c08003410542d404026207500c90b400c41404906201030280340b545521801c81119005100840046441c000369040342c1c14084041d0100c41d800424410040e440d0b0559002c1d9841d000c108000d1074010917 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 339357383 1250 339356133 339356137
    0xb03040b1b0f090303071704080705030f10050402010c050a03020c1c03020703081b01061706090f1c0c120206071202180d061b030506040b0901210302030903120403020316030201080c 80
    0x850090f04a91400c1b0f9070b600e41107611007804001d400f4135900002c0c01d0180e20000c0c085007000b80300640c000d01141c084814850346401000c003c80003001d550308005415a8810714a050407240c01400340c07030307492041381002511194840c48003401010020307201d048502a203031020700781d20340580c081c0006a040d60765080c0030750300072041120310711059400d0716243c00d02072054134014214540040400f43d520107005041c41d400602c2800e00350422658056070480209880ca081a0746550001041c41c156030117840050125001900181d044a030314260b040d00003910a0064855494102d82400049407242c2603100740b403620702d00401e55024500343e41c200280416003581c0300328008285001c41d0101c010b07020803c44102c0c0002074a8100740480b030b051501c5200010501511a82ca9940c1040f858000e540b402d2100c6881182500403104107140c42403068460240c802029680014511040021242c010740400c2e44070b405040c492040703001c401d003600d0045036030603103e0b007031242d90f103049a40b1a5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 339358633 1250 339357383 339357397
    0x90a0b07050f0a09030615050a15031b020d0e030607021b131803090909120f0c1704031704140114122d01030201050d020c0a08040b03040b1b0f 63
    0x403040600500b51000d04640241c88510750326614801d00302d1031414650140c030f0050901105111020780d0500007034030f132030145600742d900415003043c507008212400c40041001b0800c1e001d14814500d03018480036408101c41280d101150f450000b42104541050f80310f2805a0300200568084d100380701c0059150200101c02603401844006134205441083d01520b6516002c14400c6840d0080002055004018100540f501250800c0550650340c0e0f50191480c140f03044405000105064030300651050503900422940f20426901c0c1c10301d0f80707980e070b01d240c0c0050004507095640f41000004115101d001c3e1001c4520344005441000032542c0152007107403080c3c04095480c00100412030780114440c1c40d0f41d000d44da4801e0780802014a4807104036004c4490012100c0d8000882c004002603a0b102041d140410002600180d582540010762460400e0506005041c88408500000c0c10000b07500618419030141c4803a4089548484220607820b00044042d94856000d000c0c14083c008010701030408 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 339359883 1250 339358633 339358637
    0x1020115120804030204050412020f03070206090913060908040918020a0501050f040825050904020a060305060a05120615030a0b011e120c0828111c0303061a03090a0b07 74
    0x6444c2d200d030081402d95800f00e80c143c440b01c0354a80c0300c000b203035810040040424282c00145007004407682c0059038038494400013600c56038424020843d400d00400c034201e2403a600100030006090249020100b58000c1c0c4108401c440c50302800c1c0120008122000790160b41c000c025a07041e508000040d40d29400807080f0a20184050101081440d020000d02501e22410600e160488500c20f071681042a03654000074041c0011205000042e165070f001c1a064591a050114450303450001040564200d40d109550002da0b03250000c01e44040410858094525680070b08500403540c0705140d039a4590a4004003c11501c000421412081c0800d0000b41d04014100ca5079940c0d507500702c0780b64505840d0003070780c51545418040113504000c211100562001400322000d103007860101c54049040c2c440d01406001406001c0c041d580e540502a21424500a044100c03c805038100100207040d80d024010500012480e078840d484503000503240709056079001000740c105d0740e54034920540300107070176401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 339361133 1250 339359883 339359887
    0x100f1a04090524040b0601090b0315130903170108060402030325120203030f251206050604030c1d130f111f1d01091e0905180c010201151208 62
    0x14078241040b41060110f2100c010f1014503003042e00308000702c03074006000301741070011038903040100c00c5200701920b44c02440e2251400c240c54519001c103041541006019030620710b8110b55000301038020700e41031403440c1d2000e645101c81c1e03210741d0801c1d981c0d40c041e2030213507042d8014410203804001c60204518100952000840007020b1a42c560300700101c06410f0002582012080140b5101e54844199000c505240c1c00d03203607420500d60160428200480c420100310924403005419a6103800283c010300d00941049d0340c5695a04041101131281e004041510100302c1d07114200b00d60070a4114003d4a240b1070b003048090f030700d556005252a000a0454800202050b04e09042d92002811914070b640e500000c81c4030441e11000400e0700307815104030454102080c40c18400c1380d038000074190541d1018220442e4095158111105030703001c0c1d03400900c2480c203010802031400c04007044a00820100800c03500304001c0f51b801a400d80e04001d10340c42c0d40d15800c079030400005175004600401a8082c0c0c00c228 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 339362383 1250 339361133 339361153
    0x90605181302130b0f01020a17090402270a0b030c090d051504050606030f06090a0212030d06090b01030e0105070806040507030e010f0203160f0207060e010917100f1a040905 76
    0x14064070b500e603c0c03451031550711850303520380d81405218414010001d2028207a4840540e0314819051031000c42c0c08204100030500c0306442d1200d41c1103c1c00740c6400160401c0845030400c0c45181400c1c041070a5001350350b4279000151002140d000e4070302520000340154188440e190500c000c0b451900c80586184c81100702135901e00322407560301c42c000c4c1d00860180c0f1080c03034101700381454031540c0d4075004040d92100c0104000c048001c265107480c281d0444100030603512580041c0d02d14011150a04d680d1450850001500304895220002007002038800740200f00c814440582210f0040700c114000c20b490100061452a15a20440e4004030038100000c181c403000000034215469100f100990590010a00a0f45602085002100b00b40c501d42103080e0948100002c3d107901051040806000b41800705c50b04e96030003040803170044c000780e019881d250a80c150600ba610140010a41041480c0180500c0062014000c95101d400b4000200501e00c03620750910000700b07281c04064480e401101061 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 339363633 1250 339362383 339362389
    0xb07050c04051b030916080a08190306080f0a05060a05010e0a0908040f1d0f0118020904060315020d050c2b02090d050601030606060309020d02041805100e0601090605181302 76
    0x1940c001c0c4000030003003e04000d000150014110a0380001181e80d000c10250b500042290049500c90151240320303000310350382b00406901400c85504040310901170360340c0c01d482e20000022201c1050b4041d4048400c95211105000d08981c4c0c280502c1401c1d640c00c20001c1c0c40d0000507000513083c0c91144000d245030640d900048503c0e501250809503020740d83c01260070007068030814058103c2088034980e0700c617516248070300940b080e090f0356a1243d00d07004980072400381c1c0c823948140010740c0c00c00c032030402c0140400c0d1150020350200482d0240c25243c01c010030101442007050303414000d054040200d08401120041124840d083d0540380f180e41c080010580c0c4c3c1c0c5842c400140c4c01031158004007150b5055107407039401d44400d500700030205442d00181c000582d54000064214503010b80340000d01c1225240824002454648046c00d03e03c0740320042500121580e02a10035074042c103056410a90300e0748903c50039600c65118280e0f100e16101e40c0103001c11400e2112540001c403006214080d00e01ca9804 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 339364883 1250 339363633 339363637
    0x210170112110301020a02060f0901020d2a030b03060c1b0a030903120c031e200304051e062a150106030507030203040209070813020a031b0b07050c04051b 68
    0x319010350307400721000104001d194481084010710440c001c2d4101800000004e555140c01081310040340729110120713100c03e03001e50484448507141031061048182c80d8003001d00203481c112200511400c030000d10394902f031091240190500000700070f01807035140e514000040750490f010540d94400101341000941c0f0301007142c88c90b103922030303100c0f081490301d5402c000341c00c1820f0341064030030302c00c0004d070ba240040d500c0004d19a001030590080b820300c08174a003080301c001c00307120500250000d81410f00100a00d0000140c400c54800320303000d881c410b000808c9194800340c00c1c04406d4000105201c5460074100c00010243c8400040700004010903034000c0942ca0b0040e0a42400ca05403203803801408090307858060564019451f007420f62541c02c0a6006c5604214002c0211081000d9400070030b46501c046004a004590018800040251603040120316040b004001503aa1800080001400310400c3d0607580c2c00d0743c0000c040c0c2008003250080c0005488020428000040804042c00d6482c483c800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 339366133 1250 339364883 339364889
    0x1202100f0e120d0201200301150309050316060b04020c15060114120403020c010503010b0901140d020d05010807050108061e0613080606040608070f0b0d0609020712020d0503070c02101701 82
    0x401040101da10f10300c081d084038003004044005a9044203281c1d407400401080b641107642d910956088010840d40450042414200040c014080003456005101502205031890b50191804001c102100c1081100b2071086940500c0140c10102c0c081000c064041e0f1020361101c41810404200070034000c40351420750203003440300f84014004052200349a41004449030b60b4800b82400d07441c550401001c2012030180401c1e5504010003454040000011081a10140c946101c801d41d02e07002e1052040010303140900418241c7d120b030101c0060590321510f011800f5500141082850a6900038010003c1d000038402c1508854100000a00d00a408650708020329061002d048a410204108400d6a02542c8000e030907070b100060610840c0507006608045502d81140107903109404003450000d0001039201c80401c52012a0030010b110070020802103805155003510640c501d090710665460106640f504002140c0740d10100060400c030340449042291411314900c201c09031700310f0f403030096000d030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 339367383 1250 339366133 339366169
    0x9010b0307030312180816150507050406020c0301020304020a051203091005070203010b0111031c0914070519032d0506070f0909050906130206120a151202100f0e 71
    0x168200c0d5840c0985e01c40c09081c02501ca17400b0038048400d8132811b240380240001960100420981c0c041040100903a6003410a85108144458901000050b01031342203441504098003a40ca00e0b059a403506200312881103a000f40000009400c220030700c40c8100703c2c1d4001c1402c41c8030411040322140c1d030b1005001400300340d07070f078607a551b4019a10505003599840c0c00900d061169034003a07084001030100c141c80e403101103805007500040c10148076401600340c0c000082e0002d0122080d18076140b4010644c8002da40342071724440740350482083c650380005890720020f03104160801d403003c0180c4c1784007103403019108031404004001c142038032441c3c241074042e01e0a03404030300d1065244c02c056401503c280001d20810314100014a0120000ca40b624401482d47e1a6104110102c00031940e4450640302e41c05942c04160500d45403034103d50001b484212390b03201400c40184800901c0340c4100308007400c07840d406042c034280c2140c1d1750410707036000c5401c12848090104e007003851000d41d00d41009901c0020a04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 339368633 1250 339367383 339367397
    0x1060e190e1204030b06040c05070f0201110c131a0d08180d06050906040c08011103041101050c030a0203040e1605120711010c0503190513080702011205092a10050309010b03070303 79
    0x8080204481101c06c81c40144541482b03140b020030250300d0f000484540a082c0400e0441c0c2d07007001e0300d0826007084c0da00c036440340c000303602e071f00c003641d50cd62104180c045da00d1900c04200c80c10b18100b00c6032200043c002460400100291024000b00880c840801c140c040e141e1160b8020a0b0b8801041c1d9000f1500c50210307038031010800042c812020003001c01407103503c0c020840045140b00b0410b5501c001030028103080403900d050708a0380d102e00116400c401221040d039480306503c1100a449610521425003048100404941c118400300c00c43c0030f001c015510703100d2901d42c00a981003040c4070000c0031103050021500c8a41c620300f070b0a01811068a0036135650503603034927020300d0246800c505008000d400034549400c0000c1284480c4203090080c0d0440c40d240d884d09214401201c01403000c18038440390a04003010b0144a4500066607a00e50001c90072403840c0d40101804150351500c1c40d5030580e44007103c02c0b44400e5090250300116080a000400840d00d00e0600c40480c4c604185540b0440c0003c0030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 339369883 1250 339368633 339368641
    0x30f08120a0f0606031a2e021b0f0a090b010c0510060f0b1207080c072102101e15090509030717030906220501050106080901060e190e1204030b 63
    0x307032241030050a800d0508001c03100c00e11b401d01c60841000620b030b90043e0146089003540c0380c1c000200c0d03584403588510519184a105800035202d82c24452204034451090000112910340050511400c0c1d00c00b40a828106240c8446640038000022500f41407155221402e400302e031040c0050346403441c003864040b030303080d1602648206008030342e03000c0038a480007880039404161118034800d80042c0340d881d24080f40d49914419003e00e20a9200040c003c031000894815501d280c41410302c0c00d0031540d020380d015103040e0503c0f80191080d828003441c10408050560113a841720358000301209005010740000c264403040b002d402c589050300e51a103690700115552040280b4445440d50b400b090000c800d0550400101c003a98902c400b4040a0009448803e442c0061315401d491441854010000b441703a541e4460003c0d01609086c0c2e2010515400c06402040402c0c1120740c080c0111a400320700f010a0b10141c6010008008281c0050014041d03010361041c4840b40001500c0510300964400d251410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 339371133 1250 339369883 339369911
    0x40902131b0527151611060c070509130602040b0409110a0807050d23010305100603050a02060307030e060f060f010f1b060605120604060b0a0b0301030f08120a 70
    0x144180903408000040000011100001d403044528400364100824100c0000d40022852009444140654500882d00c01c024840c0c0010504e95039004146c1e80e90300d5610f100c180000c0e4070480c944072a080e03100c044200860300302070440c658032034004014250703c5002c87e0350f840145c0e405580844100000440c05204421051003040c4108030300d03c040b2481c00301103190280030f03460014108000e000000c00c4400b420b000075040540c00702002da10604403035422203401502c025082c0400d50700c0d80b1840b038003601039142600c600000c1d650010010880d4504035800c0200ca940014400820161200c108004d041c500308240d0b0f014503039901710180c1034034100e000d0010031030b1001c03034550402500e250849185074100c1040056942080d404007200005420408058440da0784004c1d000100c244590310b228002144542c01680b0a01080c0001d030030340e10402c81c01c1c1400c0d004032040e00400700010000a00d20380f00c5510818802d2400c0e905006400c1140c00001a0883e001d00759076807240d540d0301840c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 339372383 1250 339371133 339371171
    0x12090b0f0105100903060c0912080705070b040b2a1603030807080c0a05160215070308010801020f030c0d09050a0b04030210060e0a090201030906050c13120f0204050604090213 77
    0x10506403850482c03000d810f14010185110351202504613943e0f010781441d03581c42000c991018084809442000c16110320745042c0716801041e00b600c45015041000c03500380e101d9403c48003141d4081000c142060400010381d044103c01400d50b100c0c140700c03586c1c0f00c3e41000c0d06200c1c0c0040000340f01007082d0400c2c80e500f0f0240c11114024217100c00c01807000200640000b000e004d1b500c45a005103002a02c0b00691070303071442c10345600c05c400b0f94040380c0c2c0d9218000b0504040001e003030a510035034507003070b299a9844507242030340601c1c18841180001417000900c501e84007400303030070f1118900d00003090b9902c10351038541c20b0031400802660b80707407815410002816010094181688001c00c820400d0504d054142041003a020744404c2920380c98040030700c00e5a20a820000d0416040b60007002681899040c0201c680d0101c0d8032240320344540307000003070045180f0139484100350b00b00d0030070a030410a903070800000700320040074154055940c425000140e1034400b0240e14811031404e00003180004c1042c3c40100d2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 339373633 1250 339372383 339372389
    0x504051812030709061d12030c010c090f03030e06040306020408010204060f080f01031101021e010605100f091802070605180c030d170c0405120c090c070b0f04020112090b0f01 77
    0xe49400c005100c90303564080301c01d000b12503851610090030441d5843c6c50003981440c00e0740070390094030001ba00c0501c0b90044001c01900d00508000c004061100d00282c0342c4c0040c0c2e1050101400d1403070720420110380a8603801521640c020b2940745441d461360740b00000c90b046508210708681d400b150070300807290440304c0440d41120600b80340140d4075060225056012050000610110344041c4001869000704004508080b5555107206c00c400007040890003400036207d00c1e441482d03c0101030344c10900030038100074020496541c1d00c440c07605002c50860b9000c0303000d900e14035003503080014402190b481e03c6100c0c003568400b09c1c0741d016040d038200d040349001c401071019480b9820441e911150309030031258603400100c081c042c2040e41e64072808a660b150103036078403850b0800b16004001d501010081110084000102c0791400603840780007044c500790003075403c01460785c100d440c0807401d40110380000c0350b071003881450114405054500e07800241e407071549084406050346000d2081d840c14504115001d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 339374883 1250 339373633 339373663
    0xb04081009050a030c060b18060a0609080607110a020d0803063c13150603060e0609060415050604060e030c04050f180a0f0b01090b030c0102031b010605040518 70
    0x21081d40c0342c03511a01e851441c1002803e01020b0301c0010104150b40c0c00090001e40010301c2c05410795824070310b495580e02d0448599104403001c610118089025450764401c0d21225401001c059031481420750703009899210104c01032044418050060f030395680710120a40c07140c041991613080c0202130203650301d10920900b9141e503000004182161402d982d48895903c0000044440100200882d400c1c0c40c2c00050107000c1420700c1140b00e940d909001d54402101c0341c60303a0411a41d541da0703014628000064400b0b6512851710004101d031803034650000070f0b00c000f032000d83d404116992000a0a19031240d407049000c583c034411003d006103000c0c4681c0c04810015a8144898035146203250342d5400e0041449461202407403210620840030840c03182307070320752080c2c40001030b0070a0305103d10451801d224101509040c4105059241004070342424010b0301a001182000b151207864591000040080291596a160005040e69460040a000f010a01c016035000102811000c3c02e1810441d9056a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 339376133 1250 339374883 339374891
    0xd030204090e0a170d020c030f0306011704020a06082502010b15030c16081b0309040b100e04020f0d1109040b100c12092c1302090a0509030705070b040810 68
    0x1040d460340b100402d000303181c80c04c1991003203201c0001c03009000341001d181c3c50344004600821602c1d007690096000d80c4003620358500c0c101c0c44203002c10001c00e04079402900950130b9201086142d002e222295004800d02800b0f07075541d000300b482c04000e000c80d0816140181c2d1a901030110604100c00e075025418030000c2d0182ca14503210a00203414030070040004444007520440d8814806928281c5004003104942c61118800b40c075241ca0740c0707400c400c0685220b20300e0032030a0440362901007280e000d454000c0e150b2101d80f4442074104402508292040d80f450f8004000940710b280d10380c8509516861420344131615030f10b1100900003282d040c804c000b03001c0c115090034440e42c00d4000b0079121401c3d6016010b0458907000754000c039440355456012403050303095070313912040b00c082c455003550080c4111820090141c0e5038400408a00400041c040d41182a00b400f02d0100f140d0394011540c0140300c181241d00d00a50350b03480782d150500c950b1015104000108060009180912585070b180d06091001c0c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 339377383 1250 339376133 339376153
    0xf09030f1119060905030307030501061205011202101b08040923180102040f0b1b030915030402030712050601090b040c09150201152303010522140d030204090e 70
    0x30359a402c010300b240380380d40c0d550300c003100401c0b2041d000082c005904c102031760b80700d060119018016200a00401d00411007511080c421140f80c1d11909040741d01820ba2080d0118080d002e215200310111010002c0201c001e018100e00303004400b4600000348034010390381c1c2d10f914141c01002229181c7d114605a1441150000202103002e4001364004c031a40c20f1154442100082d002d00a00c5280d04c1020750204030389001502198040203020029a100900c20441180004181c0c59100740554940d2080c680d030380e001480130740c03400a03560152010342112841e580b5078403000740140f4444021609d5500110051004135594000c0ba0854581607405011608081c20050022540d5000c0c89220f40d046604980c48540b00750003114141e411a500503042c5601c0c0d8213840c00c06200c0e90452050708010031000889420140700c3c0d0384c858401a003404500107140c20303204d6080914480250744000c00065045000802881214292041d645005980d13505d0580b4000640b520480a5401500464088 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 339378633 1250 339377383 339377417
    0x20717070509040b0a020c1b040b1f0518130209030708010c05091e040507030e0d020312060607020105120709090b03061b13030606030c0e10180b01030207060f09030f 73
    0x2c00e4002d40e0000011506554030506003000380959481340c002d41c8a01016840040481e4469584201058806101c07142e04881881121880d03c2c06103042856402c8248030444d204501030a10314000d804105001c1c1800c0c80099500310420b09141265a400036a50000345000c00c0140c00520211009000340868488047c10f98000e600402e0701500003000c011180000030351742c85046440041c4100240d042190004000307141000304a5600d1003909420718005d40008150b0311018510310224540340d80700300034800f050700251000c0341030020a00c401c091040076103105602c50021a580d1682c0c05e03283c10040415650400034480c0650040d8041c0274031030781032005c0120703100b5400d1101e40c1e541c08018140c6500c1040b0340d1028119034030300f000c044100700da0f42401400700c070900700c1d04a8541d1035110001500c0c401520032584c01680c800701c06d848103901034100c0010581c050600601340340c0c85449100546001d031444101c07440d511450ba41c00c15412090b584801a91840c00e01100c46042e0030b2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 339379883 1250 339378633 339378649
    0x50418120309060b19030302010c090e01140402210f0610050306041d25061b03030903180b0a020d020607020714190303050c100b090703050a090804060207170705 71
    0x3030a01019220144102031242c281c019100ca1030740074110741e4601c03000002409000c40e082c00114015403e11203020560344c821940b41058070b0203082c2d414016481c00d01f0015251341c80100c0300e600070f0b13004d00032024164120a82c08122200007081300e0311620300044581d00c110700c01003c041c070941c6052880300040c1d034071000fa6940541d0581c1c00007101c030f440f1034101c40c008100415561580c0320f801104210507030008042548011110460114561a182c080c2c2d0300c10341c101d4030340c8420240c81c03501c1c60109100f07801425080d4000d0421a5040b41007510701100a0860f030800d44141da00003506942090b4104110140000d1601c0a40f4460603c094025120701c042d2045125000c3e010b11040129668040b0b2031058801201c00c1d100d08a07030b20b107000fa056420a03042e02d0024020700740040c0c3c59800d2800380c00d01c400c00c0200007468951340d1210039401440c01405440f4001da413a200c01c00082e201c1c0c0018006051207030005d009082c5018000c510805035105031807415044914108001e40350181 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 339381133 1250 339379883 339379913
    0x3150513080309070302030118030305010f05060f1b030406090611010903050301120c1205011409030403332409180f05032104021201020a020d050c03090303040f050418 74
    0x900a540e6100c072650783c0d20308038890704041d40c15407174941d000c215101e282691480305840798800344007daa03540401345101ca190b00c9095040581007004003076040c4c81030000d0081215104040ca4042c1c000c001c0d492650700990028400b00d941140140000740d00011041601c084050081c0001445035900410b580010321441c120a00809003000070815030480100c0901540e0002c81070f03260301800e290f07000c1c26040d11010f403002c5007940801c0c0c110381e0100448060b42e4101d8009511010603080780e2401600c0601100100d01c42404441500c0220b4000d04501c5030f1004451260442920000c0108502542c0404031039890900e02080351416110034102e1507410512040075240641003540c00e501c61034440c110881c224480d5054404180d000d81400345000b500c1c4016030a051035040f038201e1040542642c056800702c0350400d80b040c440d20040000b05507000540713080c89105400303e0328682154002615245002c4010b1100c0d040c40c2c4a003800c600003c02e074025450f101902e804400100101c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 339382383 1250 339381133 339381143
    0x30c04020c0304081603111e060711060307080a1b201f0e0601120807230a031d0103091703042d06150f0605130801051003150513 57
    0x100e1a40c01d00903052054030300400043c01501c441101c92820207001c400c5a000803a4449490441c40c15141443d09400c2d1030243c2007031b044e80d840b1140008020a039048100c0484242000c0c070040c40141d02c1e110040d5000301101e442d139882500342840c0a9040d504142004c02e00d8001c4c0c04c90306081594000e5208414503c52a409020a440410303401e003044103403499000180c0440031750700554a50b0ba030002948004e200140c0b101030340ca1b41506182820f03203d0b03024141c14003d01c00c14001c1080d601c0e5a00c1c0011103070f02c6000c01c100c41406e04c941805c550610a80108106440c0d4850854410360007181c0c180342403808105500032962543c85542c0c040b01540504000880014104440c03014121040703039011461613542003903c00e130880c4140c04810110784150410000d0180034440c440c0349801d96596048041030141892800c83c0d441e08400e000e140900680c1c030b00080c80300c0083c4a001e0285140002e4050300b00d0540c107200141d000c0f50103010302118506400c00102c003400c005500c5100d9405 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 339383633 1250 339382383 339382387
    0x10b03070e041403190305100f050f0f09070e03060633160f0213090b010902090402160303140c04060905090c0c120a0e03070302030a08030c130e1014030c0402 70
    0x5062020f00b14092070140740481c8800944205940202c001c0307003601880d156814041a541e0384031000c500003a61155500140c4102003d0203546499029282d0504018042c14512910070001440307181c802e955820111703a0702150703050542014403105900c00e5094031401414203841506204005145180740001815883c10182110000781106c416070442c000b032007425485410100c0c070707400006100301c0c0309056450b143c0107481ca1500541a60036000100c602c00caa10707000c5180d0295000000080e481075080040580701d2a503c45039600341d50007598006441a0100c0702a0a000390180c0b4050300e809080c001049160360000c04079050310750030756440c0110748544000d000c441c01916100405c0b0300480cc0030521540762003015080d8000e8030b036103c2d0080c1215409158981342640000303901074004219110210b0304200046030001c1022402c9441e00b0350441d241c250503102c5420803c041c090726410301c0352540d80c010804c0003402a080c46080d00b16410b20000c0c0d07441301c5034000e6074061600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 339384883 1250 339383633 339383641
    0x60c111b040c03110d1814032820010b0a030503090108130f020f010509040c0315050a0608040f0f020d0308071d1e03120a02032109030715020403150b040c02010b03070e 74
    0x140341b01080940d0384011004148145191002d4482e00000c2010003043d8101249030720464880c2c00301d141c54800354880c0358840203040d4007100d14505481c002c407055900d82c0c2d06003d840d103a00c4000c10085000b213000d59158800040014082c04026010000c405144030924000c965900d07182c504141d41104c0c20740610f0b29400041c0c07941e000e0343d50300c5c2d41c0c81450031288004c180d8060b00316413004a9498030b5200c40c5611007041003298103060040500084d20440000c0c00070300000c6281d50454001e00b80d2044c02020f5500180e81c10314154021000243d10005211816800898a145644585440b030304011030320004200c1000741900e82c038101c1903d5114507291902c0a209000d1031052101c1c1c0a69601486400a0354075848002d064000683c00300c5040e918800040000b80240b4021001e145002c285445d10002e88011000e0a61301960030480000041d40142c580d0b0b454245024000c2160b484a0b000c200c102d5001c03244c2c0c0400d590514802540d5542d0100f14002900d5000e00049a6911 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 339386133 1250 339384883 339384911
    0x9040603020d0f0c050109120308090109060e070f140607030e180711061803040506030a020c0102030a05010e090a0503090618102309030604060c111b040c03110d 71
    0x51240c0c0042c0d0060501c1285905000c0e0055101c0311082c01004031402c0c1da5030310401180c40f03100910459042c80441c64000300003034801c0002982000c2403030000b0501c0181902e50b00212200a8100b01c510380c00f0600402c4803564001c001001400582c121402a591401c00700f180c500c1480d40090801401c0c00032040d19036a00216072404208020402c4003030701e08090081d004900340d00080003148188030000302404010120940407009000145081c103180c4024807403950006807800d84515000d000061004000340701541c485c158492010a041d40b4040041c4400c130000741500d10740c0c1c0c0040c8101008150008100e64914400317440d10fa46d22003020354002c1720301e8030b00e0b21005d61160b62004036007078040c0d0181082d0344001d00c9a100c11501c0204040000191041c50f112940541011001030007042003a4045400300c000c0c0e040409143e581e8500090504007419180a04a8003c0c0503005145c103041c451103c0d403420a05080281300000400e000981c001c054440380155225104143c02038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 339387383 1250 339386133 339386141
    0x190b25050c16081b0405040206070210021002131401021c051c021801020d02070f03121e0c0c1208030a021312061e18061a030f070302030c091b0904 65
    0x42000400c80c082c56031940d00254842c80490ba00a800150342c41c20007a20745044d201e4640103030303801000c0c18600341240e401d1000901081003500150f0042c09031401c541e650034001031201c0c0c04060850740b2040d060802d038005070283c5c006124119800401d0341d400560304030001410403586400c1494031000810701036100c2c0314060b03240c903604034004648244002c0e040e0130100d8901400340c003550a081c22010080340d5a007031324031808916102002c001c00103d90f40000c14518842c0c2c07481c10092901c203c40e961488109140c0c000e20018615911003001c1c032440d00d11000140030300d030008401c1c8406c0341d280c4a03c1800080c0c001e03d030b2140d0006250880078030003081407000306400d071300480440481e13040c07140091400032412224131585800407901c2008a204080c0300031014006074403402351035100c0700d0050200e8502400e003a0a01d2800c034485582c00c00c21074841e405070200a01803d0b055206250505403c004003e000d0107107541400600c108250716641d0410b44141d00b9a142d682d80c00002d8054 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 339388489 1106 339387383 339387403
    0xa05040b130203041b1202090601020f12220e07030605030604120c0c0807080a15051515041e080d09031e14190b25050c 53
    0x1c20700754060358002c1e02402000c0c00200c02040341c0003902c01650406c200d072480b0300443c4070451400080281c2d00c03401c20703c06071070264a4007107215074401c0c1b2000350030905c0401144c60708807800781002540f0206143c04a440301039035a2400e03807980f51800d4840700002800c1c1134000c14075040000b0400c0c0a6235000e1b101d00311600d0034100c1120703083d00041046030b6000041c0c1c00064803410410200000e41400d80c090100280d81c2d14182c1c403044000524040c00600b08000c100825203000c50030f0020714410358501d841b00c40100c4c0e101010b07100c0c54001118000c8420f811a040540301c1180c1010f2b981c08804468021004010940c0e141085100050001c9803080040c0c542ca88129001d81251348510f8181c11030602080f551410940300d03002a0118100c0009061b082c00010a1455002510008005030301080d00c915291100c11080086050000025a40803c91802c014811076 = true := by decide +kernel

theorem cover : BRFrame.Cov 339208633 339388489 := by
  have h0 := BRFrame.cov_init 339208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 339208633 ≤ n) (h2 : n < 339388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
