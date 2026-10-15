-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3809
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:44:53.614978+00:00
-- url     : https://prove2.me/submissions/d2d5584a-40b6-4e20-98ac-fd0c94bb32d5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 684892086 ≤ n < 685071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 684893336 1250 684892086 684892099
    0x1005010614030f0c04031a062706210d021b2704170301080607032405011202070507080d0206100302130c03061707140406052d0910080c 60
    0x2400842500c0058a41c0103001c05404095501d60342c1042284d4452504040c1005110102d44000405801c03111805131000362950380c07201c0c4c0c3c401c0c82282c0e2846050501919031140704041035140c5040100703802e6211403000012241d48481d0002032a05200d03c003030034096000740551600c0c7d2802ca407a80300403c0304c10b94040d88940d103160101c28101c01e8051100c940340003068003107001d008000d182c4079850701c8194000d030b55958490301840d9413a80126852000030342015008481014054246c6401005400001018a040c1001500c1c604064200101210341c00e01c1041c010410421a14004040741c4003c0e051707117018214000d061000080032035010310042281040141c0340c4100f4094200c1b400700000036003468101e42200a4151076220700040031082c00e802e00d123414081001001c40b207206115000d82c0b080c10090105072105445030542c441844010390f00c00c80442c0682d69900340b41840407a0150703041f0030020701d11000540780100d04040f4003100380051202080003204520040b00c24 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 684894586 1250 684893336 684893357
    0x3070504050f16050d090b2a04060e180103030305060a17033001080c0a0611060a1805010906270203100209010c08030c0307021e0312040c0e0910050106 67
    0x30b101c0809405008074000c15010010060241e01c228290340b02c0c24601c4c101401050110700b8402c52804041c1c13485410000c80c0c1001862400010f07c0c2038103400c550302e603018100740c60441d003607401c1220012002e03000200100c418910b040ca58003070501840c032941f400122801d118042c026003e41c25000304800d907145d000c9508a030600001954a07001201551900d4180c00c0d01000740000741c8929520314a4011030004140c19801090100c0e6082c7d043d80c100d114155a210201c60451201400c40050340180010406c4080e44d41c01c1000542414400800020f800b0746e981400c440031030700c0c16103040d951055464505c0c0c0c0302042c1200e81c2c6001d0006070442d280503800098540c495950b29070300c80c941c00500c806842c0d0051a00e0428030350400b41e104e8032803600000942440e4401c0381d42c02c00501480c10301f5032401c4615010044018040e00041d0b003007281000b1180c00400c07001d40305940300c00e0451800150181b103081c402e807064440c20003529602c0c07594015402a00c0701a0000420700468414 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 684895836 1250 684894586 684894601
    0x60f0f0c050f040308031b180907090609030b04061407080a0b0f01210b040914070f08033415052208070204021b0f0f210a1e0306050307050405 63
    0x283d800307684c0c02c0406285c0d01d071540400d10084241e0052240840c41000c500741c41c020025401e450300e0020251025016956111000c494608450080001143e01e010040c0f000c591000c0030140c2c01341c410040004d40341004425907940e00807c4844200103080241041400d941e58010060764480550384008248084c800103454010341000501c0c8960400c25488024800c603005000c038030390041d01c00c0204c0340040c180114008030141520780030f840b40101c0001c0803401c2c0d401100444503034101460601550301d14010540020b501c42c018411240703103602c08040350b81c024101350f06200c1d050464044001030b913a82e0999500070720f000b0400e40ca45000300c43d034003802c580e19641c003944000155540d00443c0300040090042c01982c9403032001102d100c501d0940005500e80c01001c01c0070403241480190040a5540d02e0f400e10080c5001b0051580c1c80c10103102034010b020818803a05205608120b40862150114001000000042c1d01c2e1541080181020702070500508419101880306107400031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 684897086 1250 684895836 684895867
    0x70605340e19090c020a0c05181315050c03070f091404200f0306090f0103050309040b030f0f1c080103020f0f0a0b27010503090607110a060f0f0c05 65
    0x911280034038642d00d0300d110030980d101c0000c009807401c884104055000b00300001d5840c468810304032003000e4a000007060b42e10b00044040406002d0741c148010741d42d6401070b014407200d80a5000c0307882d02e071150008103540302c860007600e00c030f1500144403e89901e0030500c02003c01c092014440305000400000b4400a505110040d00191040d03070003080340c4135019590028012500c5201108100118966404000c20700040d40642002c40385581140c88640b02600303a0740081c0300041c442d40c002c10210030a4106a00302d503044e504001c00340c4201c4041003840b1402c040b08080f07100f4180c0c1140707922061401115035003400030441460404131542c1554040f0b5800485100b00314814400d8a00c50269030b82ca01e1401e102400100c0c076400c0d11003541340a0f2040c052079070392440c510308a0064a0749225481402564454280b801c01402140c4500d031050760000c0322101c500301680110b1505501080ca03e002d002c4c04450079540024016042052220446000c4443d0800b046010000700c8000c5140c003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 684898336 1250 684897086 684897107
    0xd090b1e0c0903030f041202040b19120c12050d02010507030903021f1514040c030209130e0f0307050c0906010e01170c04050406090212070503100b0c0307060534 71
    0x41c2000340e031400b061000900d5805590705c1c11010450002c2c021540303403000d000000b2050310a84051060f0080a0200545000c02e480c0303440010003202002c00610500002d402242d03800f58115a9480b0f885420560301c039a0055016107d581c08031070080e561580c244111648a90030389000c200d0b8116580d8029142c80500100152208592180d210144280e501650b042403078a01020117056413030003191040e100340c2c1100da01c50341c41c2c6504e01207100d000b80200c1b00c55880c0180100c810b41e181d40724103001400204600f9241b40309940304024a00781c100010034080780075000a00c1c0c0c01034000e0800201c094003d1880c0d042006043c15400f050342c00c2000007003000b0800c060409690345d000d8509600780580d91050740e01c24201800050030072119401807000300d10082042049a955050603038448c40180e1381616183c7c0d54180804c030701d0120754003801c01800c0b6482968600362468440070151041615040450746c1c518031661825503c060050a5180f240000329086600160000d090b4440d41c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 684899586 1250 684898336 684898351
    0x181a06040608251718010e06090d0e061605070503010518011a03060c0a0212030412020c090c0409090302101a090f04050c0d15090501050108011d0a060c0507080d090b1e 74
    0x4c40b0007060a84120003d00c404440c403010080001c031034a0000d07255282010f40c0c59595070701031260900186882800b03610700804000d02042c0c904031340c2406034400e40f4991030080d22039003d50b40011545543c20b00409010709038000c12070304e048030005086400c45100901010240502d00440f00090b10007040c403503030100b503240340c01d030300d07101890026403c1141c8004003900180001080000304450070301c00064980150382101c14950703a9109208110340155031f18984414240020410702c0050782014480f01e2091054401c00c0050000b82d0054814500c1c1c40002c03003103d0f0042440da42449010b4640c8a04544440001070500740c440a0b290342924800312300584240518009205171400085400c000400c0c082181c02c03940c0c20841d000340001e0168143c02c1d400c6c00d0103000c4148048002100c004c0c1024042c0509486640d200e400070612440d5850a10106010550100d48401e0180c040d240e619100072840709640e2521900303214004201c3e900964080d0b8080000c034121040f0035a0007000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 684900836 1250 684899586 684899627
    0x30a0213230d0203151308071a07020c0906130e0a05031e0315060331060b01090617090c1e030d1b0f080c070801060f05060301181a0604060825 63
    0x103904e002800d04020312903007d060041d002421200704440740110819140402c6104500d64039088000c0ba21020444007480d8481c002d0008229980f03841c1d140ba800c404540c22000980480c08100c0505221405200707549540002c41d5031036070400d070b4001c2029442040b9849519524206801401c80d000c0c0d107103143c0c0101c00100010301d4020640c0440e0304800b55540301c804180021110704e0308180803106003158800c0c10650007100b95400b4101c620103498541c0c88807180d00c595489080b000c0c49008003c452a0702c01e02c01101c400707450b80882001c40030781e842c2603039025585d600185880c0c84043c00d803840400003001000c82101400304454003a40754401207031203225142d03081400282c0a6800001228000c5400020b032030703030055100004403070744600c8400700150740d601000900d0200b4490012914640f4040313820814072035009400e40c0059440c0224044001c0d400302e00c00350410b070400070121320481d05200025680d104881411032000068429840d2500401000301c810380d42842c10710107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 684902086 1250 684900836 684900841
    0x11031507020d052104300e06070606031a0a06080d0e042408070503190201080f09031201061110060f1503020c01050c070219030309050105030a0213230d020315 70
    0x400c0000c10004031101001390348032405c107424602c035115034900030303c140080b01c0c0701c05041e0740140c1100070141d06d010f40c403035680d66074465062081950143d0030485000e565a500070000481a00403040c03684000c5a12044034504840351800311030f2a50000189a403001500f440703103c1c4d00c034880c1c0d500341d0400e49000c81c0300c02ca00d54030100140307044403d4a200c880101000b1500050004104084030f20850403151042403442c90b4096814a812000e030014840c45c0c0014071989c0500381d15504403d0342d0013203e1400c120b108201d140540700303800120001c1d0030103c40000e048403c0080d52161070100600b000b40c1e5103000b43c80241c40071588642c0210b01407007108181c0180c01b070340c19192545000c070001d211a01d000c0003103007151791290208a10030060540681d03100303112902d1082c1580d82c59120b19520ba0708017030066030741ba00000d00851000f6001c00c50300c00c4041c007002c902e900034070311040800c13407000c210f440a46120104542d0140914821141200542e500140c0a01c144540480e13003903054 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 684903336 1250 684902086 684902107
    0x3040b07020606030715211a011407020405130f08070b060603060d060c14160b1e0c090f130519090b0c1e04061d0a12060b010e040911031507020d05 65
    0x7001d00c0c0300e1820307041007000c00a00c00c070f01076600302040715218180d6223800b04903802d00650b48000f0025004040d141c052060380300508043e03102c1c903000111216440e0308030a141d501d0198510860508483c0c01d400419a4000c100c3e20b001026000740048412509514000012584003504040081d16090300d0b400c41d85182e03400780521448891a883e4000d0b80e0300030001d015105000030040031100011840300003401034030f10249000340c40520b080c1c202040e45545c16240503030b0308100300440d40708068943c03110059403088c144840407103a40901082c03074501a018540228241036a00c1d80103802c20312280005645005441c0c0c5c03194500a14035101c609a880748403400310070b4a815443c182001501092054001c0400603840c01c103040352a2440c900003091100030603103886030100e4910078000c0080020102d0b04182c14418061500044d0900c01c0c0002038203580004405491803844070040b015603040c1480045400031286202d103c460410000c029071710403000704d20b001040008103404115 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 684904586 1250 684903336 684903347
    0xb06040603050a0b100b0a05120f100314070b04080d090e06030c12150405030c070602150c0d09050607031d0a030207060f050d0533010f03090f0209040803040b07020606030715 77
    0x10340f1306c0130142900c4071000100038144e42d00285200c045134072444000364000800c0002280300c3c440c0c41c0d03201011580f87d50b585088003007440c0c0484030359004c0e608001c100a4070741c102410041c40302000404951000e17000160030b40d4020740200710303203100e003c003005515200012292102c000c04e40300069600e400c980c1203420144000e56444040c1407071010b0000b4404008050a030468030301c0290b5441a55681f416640d8204040c001d011031260200000c9100c0340e428060052804000004103205226a0340c83d0306080c0100d4010b8046544d401070403840c14106103203c0000c40b8194024581084903403030103983e03200c45110300030810480105804000c2d00c55000c0c0c8811404800050140d8100154485103980e8034242c1d168000440822801d421000001070f10340000c01038444026800f0f02003c100c3c00b8001c41d4034280e03802c190582e420401070b161141910306c00c5000d4124035450b8140b51400c1d002c048006060641194801014480e003a0307400b00c3c01c4802ca4200004180310040c03583d01c203a07107 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 684905836 1250 684904586 684904589
    0xe0a08091e090a020a020714030604170c16060311040513020901051c0c17150f01020703050601030f02010e180a18021905151303060b1c0804030b06040603050a0b10 72
    0x8001c2c2c641c0090042d18041500600034583c420340070390f002c1c90344030182d030199081880422503160b413010001c81c2c042404907001540358085020311902d0303c8005c400f01031810006d0001c49085c050301100c20401b8603494441c00c002d010751000b030146481e01c1c04001a07002e211004c0c1e03403060280c1c0040d003000c0c544e014200f16080c0b801010403550155000d8586071000341000f196a0300880d02101c60f1000f20038515800c1c80c8a00d000321030f4108401000820310240010a00005042d449202c3c800300c04903104100c458001c0d40700c1c00400030450711a1000403c100036810016025800c1d00850035090143c2c00800d9610409024000544403010000f1030452a00b800010b900720300740302200d682d4001c0c501203040540d5015900c0148094920b00802201d20621802e0041c80c1d8408000b400052030700c1c0c00c1070400f050003c00c1c450403020810a40151351b03610001c2110800c0300014200304008c0310000d0b441e844281143d080110703a1840d2141910740e0b03081310004000b0755151001900e001001200c940 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 684907086 1250 684905836 684905839
    0x6021209011704060504021509030d0c02012f010f09020109090c0504090f0b03010b010e0a030b0603010603080a0f0306080c01090308160816030809061003080c100504080403060e0a08091e 82
    0x85a003082e09100004040031b80c0d0a80c0280301c004809800d41c0c0c0c040d42254011100900100b505244000045400c0010f42400b28104410240c229207010403803c4540b01b07040da080d00c68032002d0056600b15085681d50080d02507200e041440e0300300940c2e0450030b0032040b01c6500c0800f04030707102144012681440f850700156900c130b244c161194881c040380d910400d41d041e010380c020403002d021a4015145080c8072180c10b90b00c02a0b13a5414000203e42d520210341004020303001244107a2296210219a080403034424000344141601c0501c00f649030188070018840303c0050581c1a01034030008048084170b002c0900304010008503112410b540001c004411600582566200c1e82d81540e18469240541b80550000d8007840208110100104907d40120745032801c550b8450329690703d0044035044070300700b180350b4026951411012202d50190034032803841144c2ca240d031181140340c54801c03a45500b40c0031045500103011003001038646d90859425860071107208509414681560384400d4200d20041d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 684908336 1250 684907086 684907127
    0x3150b0307050d091b060e0108041203021e0304050c03060106090303080c0f12010806011a0f09010806030f1b040f050709050f060f1303110d0809010507390501090602120901 76
    0x280148031920017a0000da80c155520282100b881d4001100ea6940c141e0b0050012a00300402c52070b0a4081e50040c402248a0301004602c020321181c43c040a800842d419a01900050301030f07060780c601803101074050030b103605044200e181035840040011394018541691217000107404151560b0a0003030720484c0c480c4408020b1290385442001c2d4580a0a00c10707802010030a00c80601460705070381c1a64824880c1c126881d00f0b10b200302c00110340821b4003900c0160540181800013040030020b100d1010845024030070b480c4070103095020b000072a02034400e1034052078508001d100003c1c1c2d000041504a038400c5402c00364401c003140001d80c89205a40403100c40d40c400048000c204c250f11020801102e00448288106c01e103c082484049600340100a180020400c0394184640c000d0024040807405020030080112640880c41413800950b1070818600c044840300418031002c41080001070309081c605410420f1620390041c1d640d951502004c141e00c50041a81000b030791003608044a1401c1d03a170100c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 684909586 1250 684908336 684908363
    0xf06070503030a060e060a0501020312060103060512031e2506110c010518060601051b010204050424080d05070303111e0403032a020603100509090102090103150b0307050d09 76
    0x1c4070040111744102904091003400064007882d242c885201203801c1a0042c4d4074100ca0001400311501c00200701e030341419903440c004a03031625150000310302c2c072403100021940c031505015490b030444010718402c29003034000c0003130540001000d1043d8a8541501d000100d000581d803408501802c4080040042c4a9000c01e864004680541026000c2c086120303100c501c0c4801c43c2120b41e248c1608039a0740340451010400c041000240309003503130413a444e5500042c1425115800501940c040418604890088030113000395110300520b44402407503a00000d114130844444003510a004402c1c001d000e0558401c1340d82140e00a910072244881e00301200303194075010140038000740f0f4002c1d000580c005074440400a083c1e9030400f10290a25441090414410507103900304001503000a03c8000c00c80700c1c282c80042c04d038030b4a40f00c0d01e001d040110300140c1c80e0b40241c0001000c81c0c55010b076020b02d800e4810030412a0b0322035034007101d4002c0040e02d04181c0d25021085500040c0400102c02000c4c3e0501d02030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 684910836 1250 684909586 684909601
    0x809120109060510030c0f14090406021c020918090c040209030a060c0c050f0f0304091e050a0501080c03060c1603110601060207030c080610060e0d2109060810050f0607050303 77
    0x640c0e01524820f100c180e445c59100d80003c0d402a403240108441d03405a81201230042c581050744645c4540311300c90240c54180100610a110f00e4160b103001c1d50250041820100b42c6007000c0d528108005801c40229280b8082d2101580d0703014800501d400389a00158102841c2c4050054076411f94000c0801c1c480c101d1a104000e10707040003020f00b5911400340c00800040e03907001184c034a1090408074002c600f400e0505506100a0003a0100492080707a07655014002c8845401290321410030300c40c0002e203070741c03620b0b074680d0520501d9468a4442e400941c1000303004400d80090310302c110755a070440400c5424520b0150744c0c4d100c51076021b20300fa1181600000300c41c0d07800200300c0d098910541c000c442182da03c2d0200c50341e40e0016600144031090038501400894030482000d001300100801783c028a14a54845545440340381c45500c1490420b2251959482e07040700004000303105a00d06600140f8148118001034249401800d1203954601d07004d1419039620015605003682000c2502e5a030b0070401e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 684912086 1250 684910836 684910861
    0x30f2301030311150c0307200f0d03090510151809020f1e0d1122050709030209040803040501060b0c100c020316081c02070305032208091201090605 65
    0x4000c50000341c20b40f0b450400d18101003494121400203813020000f40d2100403c00450350001040d4070100300b000540b5800c4810b0745070076050019501406401c4035070000401ca030038000c0c204c40031424507040c00458030000d0800561200080000d2600041708480401144016a9207500114900303111380c80f0020591642e03400740388014800c48240050b4801802806011350a45d0718102030003031006030742c02080c18034a0080403414450950302c1d0010010100241102e0000d0321045036884180450300100203c0d4070410390071001c2d60526900851459001540401d40140300030030303201e0040082400c0020941240c0d000c3c10056100d541c0343c040440d60540c1e5031022030480c94840303042c4501226060700100031501c860030015500c0803100c0c01d42d140c0c12100d91110165513103002c40814a449c1061492002e000e20078400c0ea60303203640f810a030144030f0308010a14004102d40382000881c030006180d8508803a49d4500a84403010450400c0c1d02050042031914009403206040c001000400c101c3d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 684913336 1250 684912086 684912089
    0x3040c03022809051b0d0905060c1c0501050d0f0c0503060403121802330c0706111204050d0f021305100806090d11070f0803030601030e010b030607030f2301 69
    0x200c41580300950388940d0f003030a03a00c0a4600083c2c0d0f0070b002819402d100c90200060510071503003900031450590390355070329203085021140c0200d6040c02042c0304181c2c0c08085195649401c46107000d00480d4104000502e40c00c10240004100f07400700c499950400682c003143c9070051a0040071760340686494100641202006c070343c80d02e856450b0820500c5003442241c0101540c64010b441c2104041040c2c80c0c46010300b00e007051403a00901140808031011211000030012101003a019000c018503140c03028100b400c030400d1400c1c1a4100e01216040c040b00f841c03d4070101c40341103400441030b0720382e402c0c1515484021900650400c00407004020f4009207a04a00d01590104510b010380640d58212242ca40b64180c401d18495040020400f403524420801014170104550544008581d240e0060f0f8901c80a40c0c0411240d80001c01003160941c0c061048040d05036030382000f80b1814a400740007d8540c14000c1558040c5582c840803840003401c44d601401c550760031a4100e041c0200c9509203144403442c00d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 684914586 1250 684913336 684913399
    0x17040608011401050a080703051305240108070303171008011503020f0d080f0901030e190b1e07030f020d0c090f12021e01020c131b051c0203040c0302 66
    0x240d0b01c42d040d440303003080740c000300395030b59910809840300482103014010280040840c81240d424003004940f0901003a8801c4150140ca40c4151402c0510710701101016444540c080d080340c0700400c04242c0183c042f0346e1342c04504d801e011681d030790074400325200341e129000b0788a650b1801c5822449040403143c15010750b4000c4991244241c0031004110000c031886100400c29407050001141c188041c2c0c020b410f0001c8141070100f4015a03450b07525244c031012042807041c085541d1100c00c240811458a242c1042446070b050780038034a82c2c0d01a029802020308090105a9500c10300c0c0b0b0030650640c140c45003000000010b000410300390074001c00314102809054900c44c2000c20000f00d4840f500c00c0c00d268994045d00d80c00c580a012150780740d11000083d02c95041d406031040304103039035455604140381410000400141840302a10352030110308130902031030500104200f4090544100c0c0d40c000760301b803007003280543d91790b55904e00807003504026171000b504003051440940c41c12040c24070610001d6030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 684915836 1250 684914586 684914609
    0x5100f0b030a081e032e060507020906011817060609010614030703090827100207051009120b07020d05040509041e05070b030a0e070807121704060801 66
    0x1654024040380c4004211952691040400e98005000d03540644140014a0b8002200c02640000010300d80d00c100c96100200500c2d07403a19406200244072410207003280490404014103100001d4124820355401904c100d06a0001500a03886502641900744003c5203903102281c0e5180340c520302601c0940390510781c1c042c08000400c03a00344007000d075048131895560003000c540341d4103401d10769a1028000a08143d102c2e540d04002ca0301040c01007450001300c40d1010010100d0780c2501412034210b0200c03500c00d40c42c18590441607980000c4540c10350f00c0c2141c00d4101e0080741101a565103c090b444640003d88040000c003e000c2500c2a491045600307400740c446038000d10908590b03510860080700e600001447c041000700f00d000d1050010031640841d0720300602856124117180c1a5180d00c420b0400e0300000811265001c41d026210600310018010201b1608000303000752100994064016000100219a824018112840c014075071240004590751910340301c0c010714802d0709001e010607014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 684917086 1250 684915836 684915851
    0xd06020a020f241f1d0702010c0e0f03030705061311010c050703031805031c02070b09030c240a030509060f071b0819030203100506070c03140304120510 67
    0x11000c240f910400e8200da2104940072000000710001d00c0c8003502880c440d070b030302aa104030040752020303074000602100b600b0301030164081800c9240d50800100380d0411a4140345100c203416070450241c018054084601181c10011003020920303600525102820512600701442400320000240d0000355005540c0081b0340d1030700304019103424002100c01040782d1b04c07100081012911418041040c001600840e0f90005e039107400191030020b280050501405895480d6152180c0410074940203188007250306090048500000c0c0e20303107000913160f42c00781ca080090000c003250b0100f01a0452103400070303016140c00c21031074020000c1c102112416103904c2001c0100381c041090041c92445040d6541d20841c030181180000e1045401045040b10b0b0148e0900808280c817045640740c5510514070340d4010f0312490450100030070600d00c1c2c0c3c0300302c0c021001040f4180100302030003504c0c0241c0b82c003e0070380403401e03401d049a01d285201c0c581c4010101605520007808219012650318400c0781c1281080c440c02 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 684918336 1250 684917086 684917113
    0x20150304050607020303040803041218031209050301050c04060c23060f0c120601030b0a181e020c0303070518040f05040302011d1b0d0510020912071514090d06020a02 73
    0x30710080c0d8000c0e050758400d00015000400104008bc01528146090350766424aa01480700880072600219803c48000d20607880e401d502038540c42c001d103c02c80080c081420021803007101841107009480c00c12035102103078002e011030710180c0c4412621986035460070040e0041d00686a19058a262003d80c0303c410105060700d6221080e555266180d162307021140d1103480055000f80401168a80c0045600c00c3c001100b8518400030380c00e442c003d52011401e5a0104404030740d50640c000d00e91291031052006a0101e00c000060700e0303010070103043c40c954518a030b8410541d0702c1414100300d5445410050444940030464001c2070250303111b50000d01601c85451801c00d60072003044184400c0d40d124031205031046424000b06006150054448000c02900352100c60500c3d1600034a41e507441d4001400310802c5c101425403694110000d805046810301b02800b1920703e0940514403000c100c01030b00140380e4949004211800318030b0041c1194626561803078814040c2d0000c24400d4050301514a048100b07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 684919586 1250 684918336 684918343
    0xa1112040e010b03070e10090815160513120c0302040b220c0c060203040605060a120b0a05040201032301050a09020f070b0a2301051e0d2015030405060702 68
    0x554a140100030802c0c0e080c02c001020a0f00001c0c04102000700344140c070341c031903210010b0000b80d052055507060311481c01c2580461402944c091070400c0034060307404208030721498040b50b520a2081e494003135680c0c1c04c1102d40c3d00c100d80b01500002c0300100d090300c0e00c00800c000b400485045034030940c1c092261240e2482000401c2c2148905403040610150b9144018103455000e40c1c41c14610f420011902c40711521aa0100d803c100c0701181c039603548030700380041d624188600c00d00030014a0500c200d0903140340c2d035240c0d0084c405024a00100e455601040031a806904800c40c40c0080c440b06505034560f600001100d50000e1180d01c0c001c503076640c4e010078042014002c40c1e481460451640707240200075502c54003210300040101e40d41c640d80c2c40310f0041103030084440c50b89000441072803507800d504180c100b000d040881000640a800b13030744134941142d268220402521138105844019480c522101d4a040c00c81180409601c940041c21144600030210040c5020300d0052084035170b02d5850710b1059a4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 684920836 1250 684919586 684919589
    0x21c0501060b0f1209120c0c040501170d0807020717010c1103091008040f020603010b0a020c100c020d02130501090204081903090308030405010e0d0309110d02060a11010209060a111204 81
    0x4941004104414903034251340e1140d40c00013030340c0007140e22810b840040072540350042194501240c200c4400b252061030180a840c0c0909500581188614410000c0fa580c0d0b00c1d50706c64003014410f11000003003c0c54020301c0100010842e14500401841010a03080e009088401e41000460202d00050713004910000c20340c0d64a000280484042e00520300c01610b64440c001c1089503d10030a000d600016154200554001c010b4200c2e00da841d602240006802d0021002400d4000c01285400c0c100141d40003d102c04c0310340d0191031024900b4090300110742c01c2d40f01d2a28210020781410700012720483c040e0700900c122114042038607800b101004100c40b011101d490050000f036410348040c40429401c00007590898465800016440e4164802a0030030686d00311040110355507680da1000e0140f03500145900d0301c0219681142500c060740091241e0099078046010402550312180b404942581118030b00c0b4002491142c071440d00020003006a0800541c210b401d003e02c4040c0c02d81806410305a50 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 684922086 1250 684920836 684920857
    0x6020301052817010b03010911271501030207020a0609081915051e0411090108031905030a020c0609061f060f030b06120a0501080610030218090a021c0501060b 70
    0x108603d05648242804500c0180740c289561703400503e40e41c1d0350f0034450840070030b20810000c00c00407115001c01c0000011400303031003440f069208103000c00c240b40701503180d480441c0c11031642c03100050500482c000d0090313840c001d4010209960105040b81c202007401c040398007100854500f2050307401c010840100c501c20003071207459410340003d0041a03c2e08001e90245002d048003245d008401e40c42880f03171b03406440654010660881c000b0305410003021060140180740d00a62030800d00c1000a030f402528012003000f0032001001242825245030110344d00c0d034201c04100c54881c10208481a12030b02d09690508150203101d1801a100805100e240c048038410341ba81d900704041c1c03520aa0180007020143d50b4045170801a80300c1503030280440307a0190080034000241c0d0742c100410075141580c0604092801c03041030400301b006075a00031100c0c040d14228135050702c007510340c00e07081490f080380c4a600030340c000340c0a00302c4140c0c00342e00c03140700c3c02e120f0144000703201d865a504018180c522920342c040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 684923336 1250 684922086 684922159
    0x1501050306040b06270301110f07020907110a080d050f01060206130804030b0f04020f240d0e0a081306031a0103051b0f1201091104120503070b040602030105 69
    0x414902d401d92040144500c090b180b41e00d080303a0502070388a5800205003440d21280d01d002c414580717050903c5440c3c44000341401d80c0d0702e00300082c810702485002e030050082c0305a02150002301c0591080b8404802011100f0844158809170b15020300c0c01c1d041034011140d090701d03080009040d5500003240d103049440c250040d01d2951240b2200030031071001c01405841c00b1400f00000000101d0004c5407510814541141c9a6242481d204010b101c1c1c0c0c12440080c4600c8190041220b40b14010b195003640450918020b0707503500700003412b03102406000701c6281841c056055190184290344c170040014051303110240b0300a6448400c140c0480324804003c0348078038019011140d86501a9002d02d0700404205041d1203044044035032200941d1203903d010034604070100c3da0313078001c2d02c13031a070b104c0c0c0500055081403241e46030000800231140218880c02c14a024512400400d0020910807a000035810204034485490207003410b0740a0360089c81441e000d401003091003003200041c880100910001171010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 684924586 1250 684923336 684923341
    0x201050301360c1b0b01030f210305090c04050903040603020c0f070b04031401060602060a0203060f0d122307030c14010c0e100309020d031107050307030f12020d020a1712041a15010503 81
    0x3460154502c200e011a00c4148001445401391800d0403a4079042c0b0881c0e03004250341c40c1c1b80d433425040c0700f00b041d6128001c2d07081c4003d004041e04040155000e03944c1178a030068603952166000341c0340030a50300208200780a2210b01040400b000001481030381e018031802d8824050185140e800c030b03645032080c00f0060704120007040103074640f6001150080c4005200c001c089406a000615032271140404403986640f041404070900d41020300c0340045955040710403802ca807404020000352003000402820050881c109004100d400ca051114a1802c24006c001450240001030407079010402d11520a440c089024100c1500c83c0c061100c0b030681c00b4144c40c8400026580582350b1075890101d940c143d0182040100c0e05403010010f800c011400760712900071548603800e110340c1009040c0c0031901190460381c0404001a0002102016141d101c5042e10001c29001c015944501410525900004150050000f84643c050149075540394040884165880d00c2501030105020420101d0104109000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 684925836 1250 684924586 684924593
    0x23040f050619030b2e03180201090b0304060e071512060b1615090302250e010b0a02100e2b0c020904050a0b0c041a070201050301360c1b0b0103 63
    0x100c3c0f50490301600c204c0c020b401a52203a52070785c10596040050084181404440603414010b02980350121070415602140320340000340310000c030f40100c001c5502d0000100b010001caa90010842000c01400c0e40e40d41920f403140e24000c2c1c0c060b004900c00164a0b10514019050700b0310586085030720102e5240d10b880f44010400c00c003407648010640302039034950400c16241e1664068840118403a80c09010424040401040d40d4000e4098a0707010110104041c045c4008807441c66040d00c0410301f0213030700c40500c290100c0c1751044403480d03000c103207061071240003004000043c8120600c05400e10341c40e8500c4030140102208039401c449100040f092400c41015044c01136909402600a10940f04000002d845041c40c01209032100404c95500080030480e000d00c58480905070081000068500b00c0d05400082940c0011300401e55810701d090408015550914080c50140d9401400007501388900f00d00a00201842103c1d20081a1289084032185034000c0300071100680c00f100710501c43e401c648 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 684927086 1250 684925836 684925841
    0x40c0903211b020f040f020409110301030c030b0a180f0201022e0905160b091008040201020d0e1804060c1b05120a20010225030207090b0123040f05061903 68
    0x10b100342d030042855603210303050303485038007900d1510b08003e40c01694480c0f900345600100e42a50544121003241400180300061840b041001101e401140a1540340c8a41280c00020171020b0640380e01d1201d002c04090410001e4000076003294003d0702528080c0e8448410140c105684042590101445845140d40e0305440d61010300c40900034411241d0042c07000403145506891a00200400340001c01e1503d9103180000d0804201d200718604101c45090581c0040d40d21141010780d0000d02c850b16041c56010b40350b00c020050058610f1250502038201810a68001c00750b08034060001500b41d1100741c403003c1481048502c1e1a44280205070a2800c804001901c3d0444c545050030000c664003403205801706c20f0300302006440e008000580d541c80403940104c0781803586410b0491302e04041c035110003007600400d406048400202000c1544901040100d41c0c0c000101100c0495003030b20102c10007c416440003034400c2e1750415503005c2c2c100d42c0304c8080003194000d4240035900307025007545802882c1c0c1b098 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 684928336 1250 684927086 684927137
    0x2205011407050a23030c0127030e041802040221060a08070302060304060e061905061c1209120309030506130209160507021804030207240804020609040c090321 70
    0x5103c801681c2c0040c00d0020f086900c0f80c0210081b5070744550044e940c401e4180365002e0b1616402d154070340385104c555405000c1c0c0d5003025005202d83c5d0395503026410140d0541d12040c0240e4000e000315076520002d00548401da0040c0000b5581c03000403000202d4505100c0014810f40316403c0040844a103141d0030030049902c01042120b00c0390301e500020b41450003c00020303005217480701c01d0007401c0a00c0c1014104a5200509d01031081c00303110340c09203007100080c001d41c0255420901c1040e10340701c00074007502c2d007170f101e03a0080d01002d4909940794103146d4400700050590f481401071317031581c1e200e83e0400e8103c0100722a020358000c954502284410b00a03401c01000114039040c041e04180303d940014401244020034500301080d601d04200c10154107000080207031103ca0314003041d011542032004401c168101d2004240108000810709640d12501a641c040c00f005005101c031201c06a4005e040248609c0116401c07418114444040c0c41c3e40321a03049000315640c2c6045203282030560700458440c00d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 684929586 1250 684928336 684928373
    0x9090609050105010b120c180d02030708062a041d0405160e0403170118150506031005010f0305220f02090c090a0602070e0610052205011407050a 64
    0x11822800d00040080c02803500900d0859240d41e1a1080c8002014446600824405034120100b20b4040e44000000c20300d6802182902c0c0da5480301039a1000c0792821083d034100720f00d1407140508001862180740302460704002c2600801d0384404c0880b8000da410b010317038003d40444550580d0180528400010380d0365025004404030f40361103880c18455006007120390402d49011040900b0441490340042001d00c1c11040c0d035000c55820b626040024003000b86030301210341030a80300e2003440c0c0c41e50f1072001e11201030500104803d559081c06110240c500340c5074425a80030a65481d1226801806403042500c1401c1c10707000e084618100207100c1210042c41d181c2103402c080c42030b0601c000b40c0c84100c800b501c81c07032491942c0c960300c00d041d400f0000810a82d0340201c0c21540a20740034800f00640540590304850160b07041c2c005a4407c1009032802d000d640c0e02815912940c0740c4000c41458824076150844e0b800380c9403c40d4911860408915910460301e01074400d5200035042c134005201d2115000e0030464 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 684930836 1250 684929586 684929591
    0x603110f041401171005062b0f0b060313120915030504050106080d021b0102030418020a030b060c0c0d11040c0c0b07031407050307120c051314010504090906 69
    0x315600259000c0d04250845542c102d881c580b02005541c0000200072540c241140c07180d4189040b2520f0140c2c0c001c640685400f80c0c4002c50140d4100032180250109660080d45160845800c1d006610080048050700320031181007204880a80c208401104e0007100303d4001000c00300415101d00c000c81d404554180704015481800045900400c00c242c0501e445036a0041814201802c0160940c2c0031a0440b5000d50040b1302d668103111b4001881c0081c2240c020342c011031401702c03900140c0c1180140d501ca41290140300702c11503044401a4001e00380034040303440c2040040303a40001d1011500440840741920744c444c4004021919000b0141480644107030340b41000000342c1c1003c14240d4524002d24000b045100303440130108a0640304866200549250401c1102d00e88428541e0390903010b4011030a1020001c08209180e2051021001c3da011504050050070074001006060f548160b4144603800c59211011484200f4000c501456150585d107803410b00d030510301040000d00c0403040850b8910b0303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 684932086 1250 684930836 684930847
    0x10f0b07080f0f031f050a061d030a050607020a0b0703020a050a0305060d060f0915020c03190c1704360b0103090b01081e0309011b020103090b0a1a0901050a060311 72
    0x11840002188284d8005c240381020040840b0540c48100054006c0ba100d00c0219600744881079000300c07a00c4032205004004000d1503860030200b4140140c4000c0542140240c0703007000b4000e50002868154107120b048003003000d0740c90301170440072405807944072000030b9001c20200460900c070b40c20a60304400000d01140d034031040780c2d80308000c40744031843e41c40c0c080d5211a48032042c800c1c50311940401d0310044106602c0c0400f4a80041d44070b10611000c840e14001040c01c0104a9218004c03504203158002184084686040c508031016041803083e030a03110b90341c4086150781480c8484103608038a06024032440120b5801c0c10401034030003010742c1ea040640d10fa410350b000c5000345030707028000e0400c0d00c050020007803c0380309107020640782c03200d0400701d900030400b100c9580da02410f0440c84202c41074408000908030300c012806003141c0b82d4007404500204003444501107040c6d0145400060303174900301032128403400501c03211072400d114042d800310644e5410441d1a01039040f0080e000d010f02d0543d172901 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 684933336 1250 684932086 684932107
    0x180a02130303030b0a0806220804030506040503040302100e0109060302090f0d150c08090616111b100c031e0309080c010906140105091303022e05010f0b07080f 70
    0x448154000d4000a44400c140c2113281001104000548404400b42031546460b8543c2d030255480e5001c200401010380100205010340001600c01442e4010f09440c803a007464100039640c0e0b006030106074420310025661000490040e0340c0114640342c103848401429140c0036054009400c001c1103690009031a03040750005581d40710040d6280c92107002810f544005441d0340b003048410030007042042c80640002e000403200c00283c10395125101c2200c044038001070b04401c980600404010b0101c07840380c50001c4c045105031491940202c0c0c07050700c012841c2c1d254128102c07001000540003030b001c9901d284002001103100b011038580c101e41810007007100c010076035650682e41e010301318028003030f595108041d040100500445800160303105404076507505150000707030103803005092400a203113041c45040c1054000e20074031f0010800f40407241c102061101c680c00c42c820024011020b2149030000104000000c04400342c15508107807040c600305403081c0d40d0384c25540d0192151400d003001c1844a94441d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 684934586 1250 684933336 684933367
    0x30d08040209181c09090b0102011e0c0311042603090a14060909070203030924190b0a0b04090b061303030f121508010e0109080901050904150b27180a02 67
    0x81e90703aa5403003004186c80c00350144207d03100300110034116410480841507104d91074021210803400540009a0300c010000d0a130003c11006c81704a001500109002030385001420624007801e10300ca00384148480c002207450307220f2098091199010103229001e10001c4800c162962072294090b05d00d0b4035200504000a04103041100c00c04d00507030002041200f455000d22180b4400d4144d1001051300801a5110589400c802440349041c00c1c20500756032914120794005031f98018001d031900e40000d03140c1d6810b0b80550303c14099950441d0900c0341000150400c402190807541001e1100e140c11421558200c50301c0c40c030905030b1010400740c07491000801002c0e104e20102c002207e4035218a00e440e1104842c2941c2044407400002d92400039140041020241215075081007441e02950340c04603500001c0050181d4140059840c1a101c008030707060029100501d1007040407221106038001925017034032800c00120741d580d0003400c640031544244184820140e00f0080240c4c02504011181885008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 684935836 1250 684934586 684934633
    0xc05031f050603130c080a1a06010302070c090507031515030b12010204090504140d2f0604060213080610150915020703030306090b09180a0f0b06030d0804020918 71
    0x3a02c8130001e40200c10820340c00c80a200801a0402030000303c08036407107800301c400b5041c807002110f120030000120568401d80c11500d411b58004d0081032155140c036851070007407100b103890101082c13800301900340403000d4000704800c64038002e60407005203625160460181c010102c006800941034080125402400e0000e4406418010070025143c64a410140b4074050380c0609a034198000340704880d078547d03010031418401130746080f40c000702e8003020502a140c40d0180c14034461600030b0809200811400b030700184545d40d00c00001c4000c41da103440c1490b484645c00d50740061041904801000241c6840000040040982c10901842962a02e100d01070950075026000141c101100a004160b003510601000e4030090030308004256101c00030618206024003650f018007404c01c10301894180400020b07903000c2d8450481c14136683c19240058400303805584c220310034040c20360300003104c034800c40c201032241d50010401c040302e031a00c00c280520901c406147e0201409550000e0b98446d00b12020042c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 684937086 1250 684935836 684935851
    0xe090102180f03060414030f040f0f08010b01170c0913140c1e0c0f0d020f0f030717070203070b0c0a0c151e0909050115030f0c05031f050603 62
    0x581c0c410608950070011504820410300c98400010304002c191000120745921941c00103ca03205c1d1845034007424614010b640c2c220030302c0c0d000000c1c0802d0344032000c40800f088900d51507030703850284d4817920340300c0c280c481c030101076800601c0b0509600d9080c81c02f180e11035007183c0d402d9519803030900e1140104998000111410750311036110000c99180d1f100c4110300d039034400d8208d1300c600d0030440e000108034425819403255030019070011480c008040c00500c020024083c4000440c4c88203215540041d446e90b182c540040901d00800c030740c140e400074010007198015070b07004403100c4031100348071015207498000c1501030340c0502c5466000300341c0b1940350005010390010940240740241441c41c00702000308460b004070a0700d17410000c120300c8460f00086041c4c5244511042c49011740c03044d204c01c8800c05415070184c034046060000006079504501034005800d241da580900071301d2080b01075a402e4844501c2c904000440410024a810050340b1039031440d1110401d0791340ca0b481da135000150080d0425200d19 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 684938336 1250 684937086 684937091
    0x10e070609082b03020426060708090d050c030f120405060c0a0905100219031814090f071e0c03090b13050112020d09060501080601080d1d12150f1f031104060e0901 72
    0x40c0707e0880c04010725640020a4500f1008a01d0309594003529500d41e064100140306001c1080c900c404020b006480340301e40605d84564882d010100e09840303c44080c0c038150740d50301074240031886040821040f00d02c030764426258030f044203280a042c042100c1160f00d80d4000c50040d0440400c903544480e0101040324029510141e48103580c0300a100030361b00f42e2f880550f600310140301800c46134481100e020b91180c4c000c0c4000c9981e83d1036410070f5401090211540c2c2d506c11003502e410199540005410040c40d009a50743c25010b905d803142528588600d502119a00010b030740e04029642c80b90020b040e0507002380e1805414a0659040c1400b507445c055400c070b0b0f00c95143e00040c0403103481003040d5401001b40c14001c280501040c2da0190400c01c070700b40381c58074003050001c4162103030300c030110f4030800a21800115407140c80c01a03c2c2c800100740c140d0321901d0a856000100e04840310b02c0080829002c10401e5106440b461999821403d14041810a400c161940310003d02c00070305148042c801c5d9543ca001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 684939586 1250 684938336 684938399
    0x100e040e0c010f030207111509060408030a0e06042102010329040c080106090611120a020a050c04060f0909051c0f03151a1b010e070609082b030204 65
    0x50036140c0881c03a601c0805106100000c00b00707e410f0213000145a0684241646480390031001940d4807450031003c1d0444400100003556400010003884012800c0c1d03552503510441008000741c500c034910903107880694130001036032034000d000c0074991044d1050400180d00e051000031508502c0300c8070f02d0150042c80c00e203551304480c1003030b015000740d034222450807516960500c08040e02041c0700e07000b81390812020140c10b98050f0004c02042d4150313100b50b80030548407900044000e40c0c585509004030f03258020005105181e042c940500d6050b6035900381b04401ca035090410a400038500c680c8180c1c0c2510403844115101200c56040c00c114050907030f91000884010703800542601c0040f1003044c0b40d041091340400800c4140700070401c02c0003659410650b00d116441240d80381942001c00d44100e0f519202e101d00013844002184404c980c21a200d0f40301e01c0d0781d40d030b440c1622180000b03141c112200e02c80c80d40c5c0501c0716403000000030340055804c005007042c0c1c807a94034107000f4486003252100700129188 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 684940836 1250 684939586 684939589
    0x1008060901020307051213020d0807030e04090201082d1501300b010e040c0503011d0105090c070c0e1914040c0303050307030b04021216050711100e040e0c 68
    0xa52039000c10340c640254614200000010150310405101103112400c04003c5000842c441100301d5015800400c41d10207400c80e030401d40700e43d45c04800d045001c6290000c10303140c0c83c1010301030350500c40e4058443c10703a5651780c580d0650140860001c00300715040400d401c03001c10b05406204a014400003007501c0b1862003070308005009901924500003143c2c06103c0751100da00400040150741070b07203003903002c25103c26000045e5600180c4101855020b41081d01040c17646d0360100c0598100c3c0e04031020300c840d40b4072000001c0c0d00d581081c00384907004a5114000f0301c03015284401061000e2050b000c030000c082d919200c1070000d0805a600101004c80d22a03104070818103030003050b1203410460725048180c2020755456440c103001b0f02c4000d080c4000480000c401174025400b040700450042d0056541d2110b1910314282c890040b240c001c810000c242d682a0030038400c0e019190301d11b603c031114294190a1100304405c070251100200300f000320910314040c40d40c9440c02500d618443d801d00410340c00c500c520 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 684942086 1250 684940836 684940843
    0x8031803030415050a1419020714010203160c0f03030507060f0507021504030504080a2a030c090207020409021302070201020c0f0d03030e010216120e04150e1801051008 74
    0x14400d00c264001c0c0b0007404041841401e0001d601d0315418000d40e10120079100759107010188801c608680c4000c140300d034000801c1e42c1184000009a42599402c07920703181002100e81d042100c050050307000b030107003030014a0b8512041604c680250f0611075801c0d5206141d90b000541c6130030440000f0b10100e802402c002541c01094502b155909060005180100307000355550482e085941c0100c0d0200081801d1600410440b0701804a4006a80c8250554100080710b4410300300742c4404492510404d10380e0300340504011041e281d1054041c0c01243c41d184018000c1e410060099a0241c1d59940c204016a1a2a03004006400c3e150025071600742d1400064203080c0300c2c409240c05124210200222951a1640f602d40e942e81070070b0028072064000c2c103c5009008455506030f40c424072085040a10030301e506664800c8689544014485903000140702c10384203d482074078001000350a00b030009104041c0c120761700010070f040c140103d24160741050b0170342e00b060b00c0f0401000d0b05403005102818003071 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 684943336 1250 684942086 684942127
    0x203131211040b0a05121e03030f070c051203040b0a052a0a17040c1809050a0204021804060b0a0323040201030908040b030a0209090604150e060f03070803 68
    0x200c6004004500340e0700c41c1401800144a8140314a688125000c05550b03105a000090039002d84a04501c0003152221650b0b0311036074000c82950b0644601072005c4000000480c3d1182e03040600145054503000c02c16100e001c80d008080b103590084c1440d00b02440c1c1080040c0d40300394014801482c203400c002e0b0840003100c030003a004602d40c0d01400c076000c0c05183c1d5030076004e0308018500c051980c0c03180303002411200a9030508041c1151601d14091000f803000c0100d800b020f8444902100707003800d5003101000e0442e0081007000300142c01c009280c401519003640503007580555501c40300c0402400c040040c0c21202c0c240c000903c5ca07a404181840416411b200d440c0e6a441c2c00c851304414000d158102507909000144000e04064a40c0c616204000c0d0100644006007007400032a920307400c1c4212020040e40088403818000d28044000610501c0e2501400060b84406404113411314103105040900003070003001107421030245c03485c24400b034604020080040116034040c640310b05444070b90b0074944408 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 684944586 1250 684943336 684943349
    0xc051f0e060403020d081f030602181212210a0911010c21021203070302091804030c0b060a0f03030305010302030105060109080d030f1104140310050c1803070e07020313 74
    0x207010880029000142c001d0b1910050501034510781d81c0720b100550700000da0a80825081c0c510400000308041600070b07020008403c0441003081c074900c000c0c840b0740000108210850780c040c42010032401c071110020f200200326407107050441c680b0504440c80254040d14a103040550b540304400a02400c482c6000b844035003440c000c142d100040d2a02282001100703080400b91059a0118112070300030002c1c802501030014001da101e2609a1020b0300a410844145025048090303811400205c03019105100b903905488200d0302155a850b0700b00c10361001082e440d0480c1400703c0104076034283d8041a80154032a640c0880c4c950304510615007510720250a503410300441c44d0b02803088040100d580300800f1150300e0300103043e20b0340c040d03035001030400700813401184c840c00134021840403d00c1c44d0f200c040c04015002c0307507168407402040004440c0d003160356018400040c0005103090b60211000c910024008088622041d11800f000780f05141c2556160096440043d920141c0d05401c544100103002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 684945836 1250 684944586 684944593
    0x30f0102090607060f0f060b041707050630010f2d0b1309050c070311160909080915030601020706020307030c061e090501020d0b030303060a14010c051f0e 68
    0x81101c0801c049003d4403a00130105034031480d05241c0384410740c0c05800e0340017139904280841603855030b04114603030060140380021425140d10440f10f00000a001c0101ca10261039145858420200d14008244460991a054400210000b02d12041010240c064484030034900c8125142407c2d4144a042d2000c0b0009045d000300024008121401c0e0010119040040305542e582d45118030007040207030340c1e0440086207182809015911030108082d003d820700c242c503a020390314107641f00e80341d4071503248101011030a12200e0520811005400c49800c00348a140c0282c1402c00000c0000e0079400a0442481555008001c114031980c0c1001048014103a43c0091841c20b42d260f10002e0013480850409003100c0d441d017100b070780e6540c044140b800c80109984000c000c010150700d4040e02030340c03026447c01215401c0c40807802d0940b40c0801103d00411004001c0c2e203029190156003586003202c02142c5041c03015010190002c240d0078070081e443ea44030005004000342c2d1001030042250200200c0e5112a070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 684947086 1250 684945836 684945847
    0x3080619080a020118091a0f01210c110102070b040c120c090c05041d0f0a02090315070c0c0e0f0f0c0a1404090c03050406110903030a350402030f0102 66
    0x1401182d40d00c0000e40a02e4140008444400c5075201304a01e83d020003d417510b444070264840032496044500b0316000c407030100030700100030300465840c1785005401d0015080e00c004800301c0750170369015100c100240d06040018550780e950079400ca03081410203071681c8464400b000700304160000400040c05010b08650007000c819141c200d0722081c280030340c0030f001d56603071400c0c054180a1000d41d0700500d0038042e010104920642c444038241d802340d81c00c1d00c4040c0510301154406049000b03540003048041c0c02011004105a400c0c034894002500510506c40c1e86480e20b00406d00860504010b008900008403050803e09a01c0c0c403414401000d06400d001d506043c08025024141102c90784070341490841c201062002450320240704903481031104074034080c185841150580c1100f40b08901442007041001c40600000000d803042006aa605400812800826501940700c1c120450034038580020403250100c618050203104002a401c41c0c02c0308000c10003140f070704001102c005a4158002c0d410074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 684948336 1250 684947086 684947099
    0x414011806020c0a020a06030c030606110c040b0604120c0303080901050c041e260f01060501020a02060f120f0919050d110f0111210606030105090c09030a03080619 72
    0x10350354050003861140c0015440f1031000080020700007480d0000e003580c0f8941da64041c041c0042c00c204c0c40540c08242001800522035000d110300b1024011210054224412141c0c2040010214141d4481c0e1240080c040418446d0700945400342c01841200b01006031401c5003400341c120000241139030340b240c4c14001085480b0340110103680481e00305200c0701d0101124401c2a0500c1e0307100da002014640310703205c581035a41c00f015030200c1103442d00c0d0094a04138405518139a080c0d400a01031a400f6a100c1c40d10b550050601600818155240d48020303402d26104515280d070030181541e0701007035916000c0521017551800d11a5a40d892500c5094281c0a400c503903c17640c41e0f00b4000a20828041034980c02c8907014010b1000d102c0e007882580081003074401c0b40100322100d4100d0402400d001140c030b160300f418410b086811a0144400404650541c0c1c603240c1080400d4038010458148654180007001854400b00701d030341d00f510b201e43c48205051400c0c0040c07108800c410b01400d801e0008002040013030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 684949586 1250 684948336 684948371
    0x170606120402030a0b0c04060f0203040509010b090102071809020a09020310090c0e0319030f021204050f0d02130f050a02040506070605180708060708071706010f1103040e041401 78
    0x2480550380406500c1d9440b40002403e0034110030004c0c1806031440e04108010304000d0042c0300381d60315912100c00f09901d880b401c0b0381c3c80c0034500804d5004030020005002c03d50007000644451281481124000354a40c40000d24545110849044040d01c41e14654114a82441e003400640300651045007146007038010403040d4102489410560740d070703507420300c203046e8403506907600c08010190440301006c40c1805040ba4003850400e0503000a41a04c5200c2d104d2880440e05000400d1501106810581004c0401c00401020034190f07901901446402005855071043d21104458092001486000800d407004c2516801043c01d00c1152041006101c0c2d542c0d26001d0761001504403600150076170341e160320102c2c68212411403190900c1303180400100164001051440752503583e032a10010703240c940d426500c0c5040040e4a0a07159803500009120f544560324a06c00000d051620751010610040381c14110741c8150405424603c0080403c0300b4004071141840544036400c000700819110304a81a01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 684950836 1250 684949586 684949597
    0x102030f0109020903150a180803010504060b07051c021c020c0301050601230708040b19270608041a1303090b190c14010501090b180601050319020c030a0906170606 72
    0x801c4d100218215445940c4a0000b2030b0069102a4518155089c000c0341a0000d21a041c0b15a040c440d001c01c02c2641c44098401c155800801090706003541c9170100d11152034103413280f04511901c1e00018000d050890044540559900604a02010f11082c035080d140e00810590501060b80101520000d0703180118030080d08141d9504d030ed94001e45802411481144d21039111780e20085100620201c81c801f0a2103602d0071034542c20003007001ea03005962680910400b081640348508400c01c6000c0c040c90000d42e2003440341c846092510343c02031035407110000582d21103036902c0c000c031840310415800c0006040500413101110b4204654011130050291480f0f00c5001048a0103078860100424411028125070218000f27024640e1154280f00c0100001084103105521004580703100b100850b0a250140c40107039690b516565031050300803406002c0f940f8003001e09600b0030840440308414800360501c0b0203941e5643d04030b1490180020140701494030140c6019010805005c01030f0307103440880c2d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 684952086 1250 684950836 684950863
    0x70f0302091c0c0f1d1618080106051c0c05040b060c010e01050613090314090a0905160f09121104020c06270118060902210102030f0109020903 63
    0x5a94500c108082041d10700c8103030380402c001400c400d0107400c128914a01c07400342e844452000d103c04c0e981d040c10b036070700c030b8458088141d2000201010409082e82002c0701c80c003044c4107051000f5200009201410303030036040d80c0b1100c0d843e50346520034003540c5444030b1072500c4660001000180c1d007903d07480d140b0750075249105c0c06109695500d41c0d83d441e40c03030702c1c02641c1320000554000c1014000c5184514080c04080f01d405120f01c89240b441840e0420903c00c0d0708109405684404805241403045d45141d0b200e000c8580e170255400c0c0001071940f26a0040034456041c09203682c80808a002020b820850701134900c0c0305008100000b80010400e0030007000d65950804020301c09242c02802090082c8100807101d9a036002c0e540810221003c0000c1c0042914980100000c18440b405c6915089905088402c1d0821070264031070000314246811045a02c1d0008041c0400e0007034140340650341061042600c070a5035004801c10030140440c404460051604000560ad0068a030700001e0701d40710b1503100c12 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 684953336 1250 684952086 684952091
    0x2090a0c09090b1207081b0d03081306060b1303110a0e0c070602070b1f1707060e031507180603140c070302010e0303071205011e120809060f0c060f070f03 68
    0x5081c6640c45503100303a00900300e138041c0c451168642805903141c2815140c6041c03007030031009509145003800700303c2021803a01503542420359111070f4a020419100f4180945007291103500c081090039200c00181080100c03890100d074020b2440c581034240041c0c80a44500c01e860a0300e042203901036614940c0d82c03002d00d007041195640c166160207802805140d00181002d080882008100d103242c1030207040011110b10308110300c03a44c4090b5151800d100311510030280d00981000c101c01405201d500203a440c1c02005d50f800850520440480c1180484081380000d002040d017550b1004000c3e0340c08050aa00c4c5003d1000112045601c449041c01a141c207400c00c4000440c00c0030b15200b0f40c8407030705914495007640d0b600e041c45400144894030701010100010300d44800028010b001e1510800e1103e170b2120011141c903d81015510000300900c0103481c2e140007040540d0407551400d0080546440380d4041d9038692407119119482d10a0080000c00e04262030307818040420741288000e04040000d2601 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 684954586 1250 684953336 684953351
    0x18090e03070f060f2d06060f0f020c060a03050601140f030112031806080a0f0605030601031b09090602030a0605121213030c180c0224100e0a0902090a0c0909 69
    0x20320081414210b507003501072900600d0740b404101e042d004181c0504800c416641d081620071703000e080303178200e1081c0c2e80030030600080d0100c2c0f14010b100300b1204106c0b0b40181c603842c03482c034000f280e179581c0302042d04070000340d507941003100d00d6070801000140d0110910302282040d491300c491800a00c0180180b44c185410400481e08062040002d40c0e0300810f00221091a107564003809803558106581c8103181d10f092080fa40d0146c4082d00c2800c00f1a0300007002400180d107141c8034100209130011055501d181c0d900004109004e85019421b880d074800c400c0181d403072400c2c44554007154481c3e00110702c00c54040c40c400b4401c0c103001075419003120a60b08642c3d1f8a101e030340104096003502c0e500080003020751318400110365034902c00079130300400001000c0c49008000c8030704a0311006081c0040710400701c4c1c8802c00c81b4a40481d4000345d0b1006000c0c028016494840030b400e001d402c000c481d458a00e5460b01030348006c506000c07600350f4124103c2541440402084103018020800d01d0050904281e52b9180 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 684955836 1250 684954586 684954593
    0x302060702120a03020c03011a01021507180e01050112110720040905030d060f182412051005010b04051309080c0601080118080f0c0a08040618090e03070f 68
    0x1d00000e0b040042c011904a1041e51801a40f03403040c9800352071281d460001c802546410a04100300709000580c0605620342d500c2c484200404006800303142044050f40075810025400038007800a000c68400b10f9050750303d051300042806d10032019030301040e4113042d050190040400d007596038440c4c1c41a020040507006045c0340d2142c01c41c2e244002d86c05030034090400180302c0040b00401d196000c1c01c03814004145c07501091003074a1503070305c14480340700260903003200e0210142c0d103c400f142d11880c0b402c810800300c06034880b1520045402411045181d008034404100d0100005041c0d11a00c14081c030a6600d001e040d4038241c080c51103000d014824405010304590840d80c4241916580040b4058030b0340c01d034120243c2e41c0c210134003440c12190703e00852407040c000009114110340c0e5104e0406031070f10302e40d072203403c6140c0c0110501410f248116000e610002e916800074001900d01a41e88801014080300740040555903584074101881c46c01c9280030211340b0110840f510240c004010b40b080505c1484c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 684957086 1250 684955836 684955849
    0x5190816021210020a090b07050c060705010b1504090507020d02060a0f140a0605090109050903070f11030f0d030c030209060f0702010c0803090106090507080f0403030b010207050406031101030e030705070302060702 94
    0x1003441e405000d03038050102469007950140030400c1071a6a107096282d207c10022020b44144500540254482100480245044401450024800c0001040f031210400c080703048900350002441914a000c41c3c24003020b0142d00c0380310b500142030320091020603413000010391141409044d245019448a0032254032610503005043c100d0100352418040745000d007045d0b00101154091248500c4d0b01d8400090040c0150040c58003c042c050091480c04100f40c0d25090103841082080320900f26000f800c418a03a014882c011011032941c0103400121264040101242d5201503108241803041c02682020340350030007525820320b180f000455032500d9900040e100c0c2c0c1e41d02e041c010305c1130b4000000c0144c11101034011404a5540c0c80c8248803a4480340350903544a07600712001040001d8903800500828441d821440d4848818015900d580b074a40c00403c0945000350000e940701c01c003981c6101290f59140c0706081100550300c02031410f10096556050b00ca41c45072001034410030b4046118010341d503514 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 684958336 1250 684957086 684957109
    0x1c02010e030f060f070e0334170a0c170606040207030908060411040c030c080f0a06050301020a020114010b030106050d020906091c030f03150b030a150303020a0519081602 75
    0x95080b03c4081c07420b4840620381900407185040061101220b00f0450700b00018210000d0620b081d075030385d00010492049049500198000341c00241c00080081d50303402c020800000d41810754040c180029850030121244403071540040c0c03500c000c814032004040e10116500390008000c84000d45c3d22001d5050485a10032035421034007550043d4802d000801c908050000b403002400e0382c06100c030748000003042e81100c0c60303045071901084d51100007501c40c15840c1141580030351841c0000a0140d01da002080c22608207105070310140c0c1d50340c0d025070200200000e81c0c90043c10720900c064a59818400024543d00481310000d030b4a036008541441283e1f1424241c51000340003621a044118607216244001094010140c002c954a141c01608081c401d0180018070300803e80c425815a00d4003900d404254001007000d2030090f50340000c1c2c100744400f561740100940c025402041c01d0030941c10710703a080c0b401c00e0400051000d43c074402c501c00514800c040c1e4a0010b510000100c081042c1d00101d0035480c1e41 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 684959586 1250 684958336 684958363
    0x609040f050f010801050a150302011101060b13090b030304080d0c05010905100c170c041809080c012313032f0601080d05070507121e031d1c02010e03 66
    0x104402c0200b10151920154103d8001000034041900c0c0c0e09511400c03101c00005400b00781d00c11100c18000342d4000c0d01e000d011942c900c800007403440e544540f010255008050b204401143c0c4a00c1080281c0c0d540c02001d00041c02100a180740a1405030101d54403006c1102e042c040c030400e682044c1c2807007001e501c9500055008030995124819030034a0000924a00707440c980072682a11035200040c08001e1540e01c240e0842070594034081c2441400030701c0030b0107003255035007868a40c080c503030000340410b02811659440381d0022480005040d0194818901c4145140d2349401d02010021440c0d462425250119014245182c0d00f03070b003090a50b2203007490a441900d02c3d03540c0301d00d2600300140008442e4100c4a203c1c09681800d14a420110340501c5031482c050040d912500040c809503050704240303000144103030b221801d00742c00080d0000301c0119114040c0c000c03600d00342f4226002d0748103060001c00158110303070071000d092905d60094070f5070750b6040d130182c10400020003c078001c0d02c0401c50030041c500b1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 684960836 1250 684959586 684959591
    0x501180906061707020a050c0108090118150606050a091509031b0e1b120603030705100f0506121905030f0c0a02030d05040807061107031a060906030d05090609040f 72
    0x45800c0050701d244030f0381c8015440c1081443c0011402031000c210f0440d12544078003e0039a960907000115280d0801034407121155585074100b07489040010f00c10001103101c4c0361080c964154010045044500991160090086c100820920705900c06101025074200300444070b2907146070b250450304400103400050003007100c900140605480030803c00204c0d0101c0345681d16590742d1200000509a11400d03055441c00c0903c40520640440201c10347d00c004041d04580c00e140142d00d6207440c0003140780700e11855039076504414003081c05074014030340d101e07a040d075200345505060380b00665100c0d0b41920852040c50080d03017038420004d003072044807050b60001c222542c9420544801c1c50321410402d00c12407003441100460500c0341d0160342620100d54a031400b601840f880c0c070b0010381c1c0405c54004804254000d1480c080002401d101c6c0c80404141c2a0042101c1c62408105002011f031010f0302da2840307070303018555012003158040c0803140200e50170744e0802c3d00ea41d0319001060241c944000011807490 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 684962086 1250 684960836 684960839
    0x607020607032a051305041a010e120a0b01080705100c03030209041e020c1e060708090f01020f270a050f01110607080610030605010c0b060105070c15090501020c0306010501180906 79
    0xe6002c405000001712402c0000b00d080c0c0d9400c10442142c0342c103805c2031200343c1240c904102c00c0d07000b01509841e10901800d140c100c205500348003410090481d400303d6040014000610485404000e00c0707015100c02e40d0249140051003070041c1c100e1042c81001010542c000503003c0e00780e1925004103038170724003040c20300d848040081d201c10040d40145490ed4824800e04601145032110500b10007290700c0303104013601d21921069000c40340c4c182c0050000030320f481121503480e0260800d10081104003040291152240c0314908a0812480d400100d06880d60403041c59114035611148098200c03031049800c0208000680c0050700c1d410004090005d09000d40010001302035080004140710f500111291241403081ca04103070221513260040d18006220040700700300040b01024955000503050502a0401c00b09035039411a15055410462801c3c0c810505403a0890704070030700c040034240900141103c2c900210202e40da0b0700c070512070300c3c0c10030000d2480032100312003c902001c0a46201c607010300400e17 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 684963336 1250 684962086 684962171
    0x140712030216121116092a03020306100527010905040f02091504030f02060304030309080328091a0402010c020a0e06011806080a1e06030309080609060702060703 71
    0x25100d010f202e401041d4401241020030b100442c00068400034506000d94032414401100018041c0c52040810172010040d4407001080d00220440c01d000c3c0b6a0303016030f0f40d29252090182aa01201801c0d00780f0409002c3e42e1071140e0304e541c040c0c90860400e881c40e29409403000049448160f280d0015030420f14104040101014580042140301815a005078200c242604410110b00c100c1c84060220419030228038014074010380110b8100d4040d280c0490844540e4580e010030b0780c416214107441c0c43d100a68000c00c056024401c80100030038800030041c540c01611051440034504082581304450400000c0031a8082c55a5001407074015109840e200c1d26821525a40081542d160340071620021103a103d40c0d0f400000715050320790701e6880301c84541743d15002601503c1c21060b4841014202a0001012700da54480c1e840294080d90354084400d160080382402c2202c060f0180e00190041c0c820442c480341c0016007250000c0c280e20340010003182c810804144404542490303c0b040500482900b01c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 684964586 1250 684963336 684963353
    0xf0b1005030114060309030a081e130506070201050613052d0a060510050702010c0f0b072a050606010809011410140301090c0506090607052407140712030216 69
    0x16103d1202c0c0c00941c0324000010041d66002c00c94240209500030441c07c41918412010640c10081c29850303850030108201d003446160500b102d502c04074212a01c525000e10600300600ca802230014002017111341803040c0454080b049402c6420041902c820118290362001600a4928144981c0e190344030f0203180d024102100060350070104031400d0400c0840c0c94030b03200420405610301c0f41c0341c05141008a5006444142481c0c0d03080e52141c040032004004101c450400030b208403038039a1350701c541140410442e1074050b0000175110300c403042d01060f940015400558140c100d402401d1240040e621440d0a85c0588410079802450700070040911005c22405420303c000d43d0808401c04002e51255402e160172104000806081d0803a070300410001c600385803008054040024000c02d191100c1521903915004003030586002c0c036a00b515000c09048140d40d4407640104280c40d1441402d0b0203040c100c54107000c2c0700e4004c0c01c0b02e5040000303000e0842c040c0e4115006403464582020840101c4d080c01c080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 684965836 1250 684964586 684964589
    0x60603030f450608190605150c1603111003140c0c150903031b1905090103090f030816030c050313050c030a060e150403080a0f0b10050301 61
    0x8a1014400c4003802030158985140c115140030800340a032078510402080440c0c92001c00d82d204a05078401c06140d071050b224800540700c1900c8440040c00c0c400010441c0c503001c88070000c9030034a0880300b40490b03519030742e40c88400c10711560007030746400e5100802800e0034050703152800102001a40041000b51086c00444403581c200c95584c0f101400c544103405407862905050b80c0310701d120000036000300454000d005d150b07569108480009080150000c00c0c2201520540f000c2d034404020041c0c61039011100c41e8079510a001e88070304080e041171060201c036900c20303522014028041450503040c0d00ca688401402d541205901c111044541000781009800355000561f40749000714585000e07010380110001800319540b800d00d16a950b4020154002e80c1000480e018007454a000c01d140e50200840e520321406124009010750b120100c0c1031402c0f00340d00c2040785404000e010040400e070440300a40c2c1c0186600030105c1c0101a441c0c02000400980c211207a1010307100300380980e0164020065070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 684967086 1250 684965836 684965843
    0x21204171216061512060f110f04030f0218010b09040b040b01170907090c02060907060c0c050904020316060c03020705151e0f0a0c050c0a0b030105210a060603 70
    0x30080080901c0030300103803007191508100d801007800c1c014000f41040c0d1101004211902120001e130b500c4010a044005c1c2200c0291911615040032244800b0310703102d60703c401d040715040545080344011022100c0d0103180300191115440025030425900e4901034070f400c2d030800000c0048a5a1507040f20500d0360004081c130b6001e640750002050700c03801e06214205140b50140c40311351300c0081410340d040b440e1000501c1440303c0c1c0240c4400140e02c010500809030700d044150050301013440c04825a0781381030300030f5002c081000092001d20011a50002e20f0f0004d84105480581e640c0c0c1e40d9001103032511a0441c03c210a08498020019100368080c0d4a0418103200e0307426120f04990307e50400240b030003490046056032104100c82c1443c2d24207000d050f44000901041d041c2065100340c02ca2580d40c000c40102408a5075184655040100078440d00103001012130705000035500f001d00340f40d11030005004050081c50f490802004002d41d107030482c0c00394011981251014040d524001c0c002d00401e12085 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 684968336 1250 684967086 684967093
    0x50304120b0a090503040b070f060608010603032c0112140c04090e071d07120e03030f16090b090a030605101703190e040605061303050d05160f020102120417 69
    0xe000b82400d0702803c1841900480214105070900403143d21640c80140112a507108814112000030024014000100050000041c0451031810090104415080f08008103550f01d11000301580c0c1108042c06403080a103001007828680038107200c000c0c40d0140418002c031903c141002a00940140100141c0f01034400522000e0941502c0c00e5441c407440c0211030100990703200d800c0d110503221880944c4018140b414107001003c0b41301100031540307030304200d060a40001007080071b11140c9400c503942014803424490480803035020020403810160085500d00000040c070b04c40c0f659501c0083c0f0700550b812034401c10075410213029000049820381300e02c00c02c0100c25014803004000200556481c01400144044211110142183c2d503610319010b280d440f540d80c1c4004141a2070b040301600000003000c44031b040c5182182459480c100c201c21099081010800c04004803045d0a00c0f140d072003e0340091042070b610010300c0140c1c20035000800c1d01200c03e00102d0000785444441100c041000461003d6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 684969586 1250 684968336 684968341
    0xc050301060906030b0606070218040501090605072c06041502010b030c04020a05040306050a0f0606050a020705150913020c0a0807060b0a03031b02010314101a040e0412020a050304120b 81
    0x1010b0640f0a50321001d000c0d80c81440001305036040c00c0004240c2c2502c000c104c0e403092412500059500901541c05030b45580d500c07180720341007261901ca259082080ca080001c09940c107108400c4140b882d0981d241504a1260211140d6480340d109641c06010702d240c0c1e1600342d48815200a00038030a00c04482d1103841102e21410440c1003610850349052016611a40342c181182c980c03101502d4050080c58500e9078035603446d401119240300c0c0401a06a60b52140e07610113407540000d1070112180c0007280b01c3d09604000d06030103102602101e1400800f42e40d0180d00b003020318440e8000740110741d52a442c81c010108244d08001c280e000903c0000e214070340c108400328410b01448045081808020046207400d800c12410040b034196603c0c400f0b00c145070200e8660701401d154081150f0541c0d285a0403c0044800c3c840c401d0700000d803003144203e604416041610704041c3d11880540640094800c0394a5002c180d1107901c01d20548240c0ca0300442201d68580d500c000300c843d003a00001040c0c4440150101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 684970836 1250 684969586 684969599
    0x30c02061e0106080403092319052d0d050708070803030601021e010f0603080405030106050603060d080903070e090a061406130e0c0918150f011406040308070c05030106 74
    0x480109000c11105a01040e801c03e81c0581d54114064000e80610000b0a40015071000b13070b2600204a070121003c044495882805001880070741e25007810070202d90783c0c003d10058070754041407882c26200000c110059a01c25100f42d10960709451900d4020622039040ca0a10000040c044120340c68081210042a650080141c4a0106840850042c0c1010b2001c8203420001d00c104d098101d000000041c038407101c640048211131069000708c03103622000c10100858a02842028014841912a14910b1421600007242410300d030b13000a00c143d41c0410403804035101006418064a170407900d00c83c850620010050303561502140403140103061034241510001030840c580c0c01000c0c003401d004040c0b41000402c40107840c503010300c80301502c1201d0160b1030b15030320000064003440c59241c26100814a48000394140408405120740e5407203803905008448500340c101e14112085c0702052000c500300c00d80000d00501c1140c5c800b0b0f250f000041403150500005a0018017103501c1140200485d640c1c456 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 684972086 1250 684970836 684970861
    0x1805011d15010e041b030504030e03010e1906020c030c0313470a09050f040603030c0f020d0b27070602030d020d09020303040605030703200730030c0206 67
    0x16180c8031903080c240e40842455020300140c92420f9401400411105207441141c180c3ca0101c04c00c10300002e80b10030504c4140b41d0810030074140840190001d00240c480c0c1d01c5919614940c3d03103840842182d20182807004e201082c0c1c1552140920745003526a02e000074510a50340fa0410900004119802d92000132228202481c000c4469107802c0c544420031101440e0362450b181058808402a0141c01e071602e004504200400c0d0180558039001c45150402040c020000101b000b510b00403440d103d001c1c404a50800400d5034900e9002075454600046480411454160810010b040d4045101030168a0950405880c0f0882d0150300360a5010450b44940c0d40e115a24031031311001d0b80003085000b03492011a001001480034814000c240070303001d90b002ca0314541c0300b6408400000c1000c02880340b0310f0741c140110b610301c607503400180e4410440c1401000040c8034241c00184466403001e000c40a0f039040d500c6d24600c070200c1004500360001c031341030041c003d4042e02210b88014017400c0d0010b0310004800 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 684973336 1250 684972086 684972091
    0xe0103030e1801060f180b130b1305120703061401051309021309050c0904061d010e03120a0f32040506060103050705040b040b1e07150b01091805011d 66
    0x4032801c851070f0b460702909032281100c8070207050412401c101000300c640014681c86004204448646607212101c840039521410184c0080c5c241180401c882e02080307000711060342c1511011907030301f20008148444140b034400903910061650b030908254804100b80a200c2d20304071181070714013100580c0025107003021101c107208000c0d40b008440c00300040e500156400803500621900c102c4d18141c1c00b100005001d224119070403220941c490960308200341c001c050b2281c210012600a010001d40780400941324022807900e0400c4440d69800104c840c03803150070a0301e164600c0a020080040c82154090b03420a5203180030390100f070320310800303401241a8000244200d0700030002d8401740d2116001140600340281c000c40c108481480007240340c1c0c039240000e02c0108a005030490369540003034030003549240d10118a4500080c144050300106400c0e2004011390f824450707000030142640c6005841030282a004098044011008000705c01003e07448275040c1c943d0b42c01485014454000d2814420b0801c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 684974586 1250 684973336 684973369
    0x111e0d030f0905300d0b01020114040c030204050c12070c11010905131d10050103020114030702030d15080a0c08060c0309070303122316050307020d0c15060e0103030e 73
    0x41c01c0390300800601000c9402c116060141303640f281c0c1c0614070407000310f8004107516102944e464840904541e024460280809485a0501c0d054602902e501036500b01d6448041d00490b15400010200000c6404450f400c9440d1010b00402d420036450082240d400524100c4444501009182066004d010202c04580004041c001946000c1c42d0032409040d849803110546140e1071040103035610b0501c40b8001d10500c40000068661550000508001e40c40c5440c6400b0002041405030803503000c0100e48152240c440301140d000c02034503140026814542c010056030081150540c00c200c0010900021582107004469164440400c801c005100603074200c21641d0141c0401c10002e801540c0850500b031280e000020202d4052036600d100030201d11010800545410801c1070500902e607a2462000091800c01e0a5280c0482c000e0f68a080d031300c16090078040c0110001c0b040008119407140114650b070010300240d980e84280020000081c00f086000c21003908440c01e150400e440c200c40d00d00708 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 684975836 1250 684974586 684974593
    0x70302030c0714030409061805010905041106031f08150a0b01170c070c09020417060906010618050a0308030106140906032701050c04050f060c070303111e0d030f0905 73
    0x38296224091102110f04401c0e460001780310014066645100c0c0c00010644040d5030703016517010f0308110003110b00503004000c1c464904024000442c10052401a0088058410036941c0c6c480480c5004940d0b00c9030120000070a8440f000700c0c48000105000071000c1c1444040c1e42d4680701c0c41d03852001d45668001d403034005071281003000d4031609900b2116402c00002c1d03003002c3c5482165101c415103400a42c2003060a10740004041084050355120035031032540c142c5c043c0196040104074161101811710692003009031344500030300031441411590004041c01400403085d250341c0d1420550702e8000340301c0d020129900d40b50490056a402c400c49652a80040401d40395980740c0340286d41601820310a88202141d54800c024035500902c241030090b58100b09050f2664501000c00060f01000302215010f4441807104550081c0005214000e0744d925042411a034058002d10601e002845124500d40c2001150100d810650100f00d107600381c4040d60f014482c40741000d0084040c1e81c01641c0007000c036030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 684977086 1250 684975836 684975847
    0x5070e0307051c0f081209161d0c130b18040c0f080109270b16091d0a020f0d0603020901170c040509010608031314040e19030201090b0408070506070302030c 69
    0x5903048031802c01d04d84144c0344c06007081e011040d420106001200d4440c010b502c030f449180d01041ca920f06420040c444a00e410b02c0c1c600c036580c2190321403c00a420002803480114a100c0c032280c007054042c000e040e03420282a100c1c100307181800780c60540c070600c0034000c601c0c1c43d110f284450b21031032036503d043c5129110946664a48081c0387c00030212028000c09440150466000c1e80c4841c0b451115628007443c0c0700c20160902e03403100e002880c2e5404245091001440b003c0202e150300c0030400054040c01003030b0000d1641d9401e601406481403450b41e00c3d442c6000030311440c281c40542d00c4042564000d55040101e0383e02c40c6021490015008627440241d4011201304100e440d05400c00c070750142c2d00e034001003103c960b0780c583c452442c4c21040501042c1e66410b503082c8400a0b00d44840400ca21003100c1c140111640b00e0401e94941401e0383c030405c0224200e415000505000750004401603a10210b80c81d551300c3c05041c040101d4000c0e940c101d58a01464004c214a144680260381c01a9038001c18540303001e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 684978336 1250 684977086 684977093
    0x20316080a02011407080702010c0504050307060305040f02040e060711010504020616050c040e0c030f0c01091802070b13060c030b0306061c06021605120f0a0c020f030105070e0307051c 81
    0x81c0c110040c20011592100e654003610100904614041ca00f9074840d207105082920001e82501c600c0003084040090030301c001c020681c0c00068400c101c41c003d080021f81510b640c18032980c01c100c1c04070007030341203410104201004180000c140340309204c00d42c0ca001410403006900b41c242c490a8502a50011043c00b40c40c4002d103d1020065205204030110f41200c05903101040540d03ca045e8641084d41000105001da82010302000c964070144101600002c42c0500c00642150014069a0440c800c01d125260a40300300e035046859164214100d013074030703251083c0764841101d0500c004480c140d0900c1003545d480c50090048110348a40103000d0417955403800f0074081014408400d82e034400001c1f44481003c42d6462008201140860403503610b400710354100545024420814841403a100304a05840351445070140c17200174140d840c2540700c48185000080342c100f010b10000340c6c503500c1c000c18001007640001c002d04801c40d050301030700c1c0f010360703903104004444400654042045d4000301019001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 684979586 1250 684978336 684978353
    0x30b0901020c06072c060a080c070c0e0a0c0507050c0907200d110f0c101e030b010318050705040203180a0b07080c0301051c03020f030f1306020316 65
    0x40a804001814215821425850064140c40c2c480c04503601480c2d51010071501e40c02d80c01e6213026110310b010010035030742c08200a44506003440d4200200b200104405a219404403a1003035000a5620080b43c0c498050017100f01d002e4840700500c901e441c401c221340318010820b4414480d0000f002d45021004c0d001440303e0703018014903542c00c010100c20007000307501250402001004421004161210348508050290364448100351419406580146850500025000e0a0f03480c1903803a282080c40c00d0702e007a1a40042218812016412412048040360b450780c000481240b00b660103103c0390400509188208041d400040c103d40c008000c14407841c24a5001543c10031079016034a003d480d4600e40003820412880b03021070b060748a00080c0800250f200031659002002c80000034a554900b03000111300001c000c0c640008078980c24402c40a050080c04021031424840d4181ca80d24040c894489030254400154249104c00d00c11010030524400401d482901503490480101e004c4c054940307505 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 684980836 1250 684979586 684979591
    0xa03060f150e04150f0b041505070209040f03050702060a030c18051003091b0308041701021312030c06050a02041707030f033509010516020607050c01060b1819030c030b 74
    0x60003401c1a0018407441e0205c50302c40140b1890142c292540d0820f070312030b050940030300201c604100c0b0911100c070142c3d541c449002c2d0000e9104c81c661201800600c0c05075828061260302941c05080880c558001c1505500400c464419503540d0290499418401840315142c500649402c43c82d0620380d8204640640e02020089001d544000407950000b400800030001942045800d404041020041096100f0140c580012460000e60608204500707041380300003548039034003030681c048017a00705160140b10711a070501e8018209011900c0c0005512000c0d5100b0300c074054920046294008042401003812004d590303001d00c1c541d841c4189074908403402c5450a00e0b0107910013088508400b5280310342c035091400c0e81d103204072052070716050b1411400c503200241241074401004544030941c0340e001c1143d0354003c5e040d0400c6a220a44916624010a240c1d0056106880001a6040c1f417800d20360b4410034444c01121054011000d401d1001c0c001c61051000500e910000402480040c4c03050a055a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 684982086 1250 684980836 684980861
    0x31605011820010e0d1b09051308090402120a06150c0b0106080402060d02070b010f211203020c0f0f06091f021809070309170f0702040c02010603080a03060f150e04 72
    0x400c540d0a03140041c040300030f0b00303000f2502c1444581c6d42d000100a540d0701d55000345504001000316207030641406890002c0101c2c0101744030000030310211141c0c0c55505480c8020741c01c1e803c0c1401460203820a500030b040d00e0041c1d00401505850451009104900c03440c0c1c1c2c1c540c000044446a46401e005070303030000d000381049910000611000742180424070241214078013610300304149500d48078499100c2a000c1e00502c1b4100a40d000a0540502c81c0b06880390715640000155011140004220002c3c00348070b800005501503c0c0c030205041c50005654000d200d540d500340d81a40e00c603506010340c1c07049a2030700341c21002c400c40c00320b805210300d07640682083d01c0050064080c441c00f020000396641c0c4105c07030368004030b41e4a40c0200144481c13115540107004451808070701d0000d4500b403c000c240a187c400901c50740d190021b000c5854401e4101c1402941d001c11040c0e00c0700800103005d40902841c2c0941300208680c103000150945039481094031566143e1100c400c400200e100b444003400058600d070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 684983336 1250 684982086 684982097
    0xf03091002121201141f1d10030608100b100804020406090c02031306030510170a0609080a03051003080702190f08010606020c06121906050303160501182001 69
    0x40c46200240e000a00080303c5490f0940190340c149001041c5103c549680d9500921240441101170041003840411078442da0520f80c048004041c0050740382c003031240c1c0e180c0d000225008040902074158001c0e40680d000001943c200c5500203c0c140200c80e01490030503803200d02c0c011b0a001a9003e42d885540282c0054804107980f81ca68030800251080000c2c6100103902c000352840310007030b10022407030240440789010311140c108076011117051400e90003409400040d060301d100c50780808002189030a580b0820500c0140994100541c00707801c0010f141002c40e0400c2d0000e00d07410201c887c0700080d01d9100c143e050400516400344440c0741e403d1041c802400d1a5600041a16100703022880000c00b0303c4c0d800402d04904009000741042918030886c3d02900091043c25803403201307044095480714a001210340c1c09138070340026001900c01540701a805000004802c03191001d903529400c0320a02a00091208038804040030506018900003d803503100c17074010198043d1403121110000400502d080f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 684984586 1250 684983336 684983353
    0x117030c0d08060117010b1902030c0f03120915010608040f050105010b040602011a0609010309020310060f0e01080d0e0111070302090c1803160302150f0c0706020606030f03091002 79
    0x614540112030441c0404100041d04010040da408141d800010740c002c1610405545444040e4035075015484100c507170a9050b440d00081d1910810594488071502e82c1218128041a4951601c95009000c4900c0c0c1c81104000a40404000142442c090f103424600c81031703da1900c94210340c0301801a01c101d42c0141300c0143c08002c01c1003402090f0281c8102e41603184d4481c07400b000070742100c0450303140700d203440742d200000e45890392140d054600d440000c1c2030105034000d8520000703050942da41c100d525007502d0020701007186041c410f559410b6800038000060107980701c1511950b0352000245280001d68172160b83d1171203521842d50060501c4007903080f10701c010b81b80e40c00105100340450302c1000c0da00e4003043c1fa8004901040e404150031000f0f501500b02840e032001e081c0207440c12800003900580492075480e001c0c0001800301c8844003010003c29031200154407190380c039010389214010040c450003011a1442c40d000c039040305022400001940b83c051000b050080d0300514040600c11350090202 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 684985836 1250 684984586 684984607
    0x903030e0105100603181a1308040801090c0909020f0d02030120070606061419020c04090302100c09052b060c050a02061005400f0b0603040b011703 65
    0xd0a40200e003c19410703040715091103402012155010390241c2c8090b024a86140802c103400720300100401c1c0418210255910301004004280030050000c203803080000340058031000650141d0b411a101d070800380d401e03c0c1ea4041036403d40b141010f001c0d43c0300e480f400321034200b07180040000c3c1c0018809000411503210017089840350034610254070700c580c2d10000d0000104001c1c0c0c41810040d10751414103071259400008410007900a0480d0052000904558079260500800811074000ca0040060000484600d002500e071490120b107049000c1c1403550440c030903030151203000181c3e003014000c00c000c40070941c4607509081104403411404401a05800301141c014000c000d040c2c40c19848040d62145496030017031424000038669030556051510034019903036000c030a0788218840c8802d82c40700c404210502d840101c03024981841e11034020011907810711a5410031041c080051b0b00812060007c1014014244000c0700c00601035502c8000500100c110241c002c0341e4055010200e03410800c1e0100c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 684987086 1250 684985836 684985841
    0x1a25031e020a0c1415040b0a0f18050607080601120908070b01030311060a0c0203030606180a1e06030e070302101704110f040213030b0606070b010306150f0b0d0903030e01 75
    0x281c11100080904580038203200d655682c0e444c442c03603074100400000481401e40c064126010340001c0c601c4990f00c010038226003003900101c900181c0c04800700003851241d44041e0700f1050402c0200e40c20f0094500181200f4051080790303118900607142d20a840821103d000e00030035654008450340300c03060241c2800300d42e40a2125020310700c2500c030a44022070411906180413801400600c00380d003042d840071801c681c044141c85e04020709035041500d900b81d0080000c180c41d004550580c00c00292440022007c010700240326031141c500b8074003000c05407544000c03411b40300c220340e10403011b07480041c0c1000103041c4200e0354880c8208030b1402c01001107006200b1034a200342540c0c146c6a048901d0748404e072500d019402540c540354100c80c11032400100c101c500c0345294480c40302819501c1c0d00e100090300b90b141c2d8021115800d034032501240096849142c110300a1140104045840000c10804038141341c07030703100e00c80581d01124800b605024610103803201800c9221421001c142d11031241c040c2c010803d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 684988336 1250 684987086 684987097
    0x403230a1401111201140d0507050103050a0e032b09021804030e0a0f05010f08071704060b03010c03090501060b0a05040314031b0a020114160204020919031a25031e02 73
    0x10240041c217035140c81c161402c0000032040a40c440d229040f5041c00060000072118200c510a0070041001c1d07035001d10303800007015a0001622140000240446584945c091072499070540b0000341a03041601410320040702d2800c00029000035500e18541ca03030040b80f1900035441803080c64041070950000c40031802d240102d5124007138544150f8403d03c41583c201e001c0d424a40c0f2103107800d005901d003a001c002e088404000521801e800d4a60200740ad202e51500f188440f000c015009000e009403840001b4010280e035281956254a00100400d622840d001215070301c1c141c0750380f05410a41182c6842104400801c0c000c0c155100420201c0c0441c0003c241c01d0060700d00c1d000107061070a0140c0005440318102c0300e41426505400c01c5029003242d804610140c0c03107901681c00688541105000c60350030291a001c007030b4800d5100d8800400c20041041541b99210b103603204030010b0302c850b0b1300d0303903080104041d40107800e0300300c602403071080d40c40ba40c40203c20040d200d00c5104418078071146903003243e005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 684989586 1250 684988336 684988357
    0x509060702041b080403021c080109020a02071a13091b0513030c24030902150f090603010807210804030618060f0c0201110f040905060d0503030a020403230a140111 72
    0x3690100814903130141b0031232074208410180c01621459200d00240210014000d2203059030b070100d075040311148200724210140620044116094072a000780d0862030300062020700c01001c07002400b0a11007114021003403c51a100c151030b05014540c002503880e40c120f03180280303410040344400808111166802001040d26a00c2844060310041c1d042800c58900c0c0c002c075051506080309040182c4801c0246511a05000c412584030780c100c0d028206544a000e03003243d031008001c0004122814041402e00440d002d5603030715030b0804400e0380b002c220549001c1014024030401e00c0100081b8000d50000b52500c0c04844c2038207441d4000d03941c0c40040712030415407500240e03643c20b8038241541e0244211400d800c0c25520a600340048410280400e1107507000d00201d0396140d00100301303180c6a4600c0d0165113640107003030b2a100d142c03010a00c00290020711082d10440d0f041d021250010520f04443c0900321200c034050808034446444410b02d004880d01d54800542d82c0301c2090608070864405010016078 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 684990836 1250 684989586 684989597
    0x80405150403030c0e0f03150907090908090f01090303080c1c020d05240a0314010603020d0b06130501030503070b041b06030b0307091512020a0506031302040e0303070509060702041b 80
    0x30529801000982d06611603809031081b4040e4686603074001408150545011542450f5075548490003814800c807944013000c070380d007006148020000103001416034400240e0390100040c0051004507100c0802d440007802180b030100108040c0b002400003400360049a18000c1f50f116568003400040364071808840507195a07500600280417202c40001b03043c03d052100100b01c0285880c0000c1d100c00451000500790141d60740f0204c45041d01703400540003150010038000ca28072550501e00c10120045070768612900c0c180c0031406024501d44100da0580360400700070f50401d04155139106024102501c151001c400401c62120a000451602c0d00036000035030f000700750002841c09061604606400c940705103814a011442483c6110810108854403814050304d0055a4004603041a00d0354010329000360000041103d901c03030b10b0001880c00f0f48259001c00c041c0c2e050740c0020707486c5d001c2925502d001642c20040c600c207d1610001a081003400184005140b441200154100c000310303040d0940403c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 684992086 1250 684990836 684990851
    0x212012d1d0f1920070b10060804030915030f06090614060a0f23030103061a011701060f1806170906010f03080f0706060803032d010608040515040303 66
    0x4030803066540046581418009070304024440c81520740b810000f52482503a40c51001c20201c840901080c4000102c1004560303555107420419015102250122820a113900d00003500031301c5000151310a50b0180d407680d580d64201510b000a446042000302c0170103403100c007000b02c0c1c41861310841008007070920000489a14055403140c00300000c05000744219001d00034100700b5600131041307401c58045460820b100c0e800400002d25100080c80641100f424040004030400c80541d04c02c60208140204520b419880d60004440300031049009020504003c00104003860044101d45a03c000d03904004295050025540c50102d2050380705600082c83c2d41c80b0b0340a008400c0c3d108940204060015003255030410000034103020442c84001c100000000d00614804100400e0b5030303015900c5803040c420325a4840c00140d81e90415035044000c0e4881005280101700c0700d08030900f089005940b000e02c107a1800400347d500c01c1c802002500e407070040c41e80c0005505d038881134552080f44252070005818 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 684993336 1250 684992086 684992129
    0x40f0c020d02070f0e13240e030a1e0302040503031305090106051e070204020f030a0b0f0a030b011401051308010203010e060a050105070609082a010509010212012d 72
    0x941c1101c54010364201c007005005a00d8206695015901c1c20001720000e1703120902030400100140300041c5c881e205c040100302d01c1c000220208000b8050801d4244024144000b5140c0c881c454048080041200d2400302003c091520308011003079092400c00508103075840000c02d00307640c40b9000309070032040103440604c240c0c0352a046031f6000d0900d9207807907401e10441424504403048414508000c010002c00d01204541c0c85030112050351903114030017500ea040101d100e50103030413648100c0740b040b607429950711a42d041001000049a4001c608900306034038065100100704202046541001001c00085507085042c2c8400b800400260000590701c0d07140040300c0040b0701000c0c150f10f11892841104211a030391250a40340072640208000a016000f442c00c02d42c2440303110f052060720890303100034120002c21240c200c008405220000d1007242c1e140d000c1d081c201e205d1014085a841c903400c0050099141c2c60300032818183d482800342c80384034907261070031100442640c000c0f104110b022002c40c215 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 684994586 1250 684993336 684993343
    0x1203180602030a050d050402030c2205062706060706050f19061503051008010f0b01120902090c2d07060c0c02011b0816110a0608010b1215040f0c02 65
    0x60034184051424a1141c040c010003500c111022036510355250001b1905558060203071041074070004119606600e141059511074200200135000418a4240000e81b0790401189034140080841603000c1c822810402e40d4103111030142c0010340066051110000192461141134040c2d00005040c20003803900c1103c5d081c030048451070000c8801d00344542080203040e03007110340304946d43d04d04010a0b2a42d80f00d40d00f080001199204580a60038103003c00d02c440400d40c00b03c4103418003a41c0782c01c05046001080c00070354426401c000d41040e145400609599401000f814003074144110942c800600c00a01c0c0c091060841e00d292070350f8400003510401c01c030f00707031040f403800c49085c1c00c210000a0458002a010398504c0c0429060310300100030490401407000c08440041903803038200d00000b111400d1502c240140090351501038007115402141c041d024503a094102d03510300c03041d585402404000d4501e03104010307104650098a01039401c155a46500500700514210080020000f0500358001e19 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 684995836 1250 684994586 684994589
    0xe0705130c2705120f0601030b180109060b130b0303040e090f031305010e0103050f07030209060c030708070c0e131104020c0604051614030a0809010215040602130506030c0306040b0a120318 83
    0x80c5d1310084c0c4040c0100404031340c042c116504180010840e0355071113544140e041404042e0144e5501c1d00403400200b0016274056001800103403501182040e045000d0b00890711030034149a8942d2080c0030400c00c400000d003010f51f10000000541c0c20000301100481d14541041007030101340e4004034010300c1035581c01080400c1e01d03082480c051286040c1418030540c001c0700507100300100b42d000519441c05803600c004485022120f10103d9a03a00140d0404c0da03191780140c60120342030500501c0004001000e540128001c07420907000c411220001d668942002041d11003a58009400380070310f4074024802d004c4d00c0e1155010703401504811403410081c0400f600c0130b07000070341034480c05a10208581c40c0001c00c2e4140c0b5174460203080e507a0f40c5041c0103078903089000d0000021110540300f003004200c15038000d814203640d0411142c500301d480e0420419140812074a0500942c81400040d0851409401070001c07900080d044019450f01e5a941511090300010180c020490500340c000e82c0c881d01d411b0020 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 684997086 1250 684995836 684995869
    0x1201051b18120708030c0c0f030c090c13230112150e0a1d03040611061306020d0905030409090201080a060f060f020c1309060e0705130c2705 62
    0x1454984440050101880000555030180c100940e18120b00ca400300106800307040c80724101c90705da00c40da1a4880d0b65403041d00b140e0340203030300700c1010802504000810406410b40200001526510801082d140b5004201c47c641d400450500024030065039922150b2000401e0001400c0c0e81d08080c0050b206620100c0e100840303900d0808a0100307030b010a81c0c4401030346c18202d0805117544407803d00302d01504052101c010301c44d0100c4800894814000000d0044a00706c0e03e450201011840205464407000c03120201c418002c1c55280000070310b6940200200c00320f2500001d81070046484051a58000d0340003669041c3d41c448be040c06640e040035156074810030002050003841e040080300d80d0784c654144290010f01803c1c1a00340c080c1402840021110b11004d040340d0b032072660b0050a480074190300102510f1440c138000c20040f00703d0007c00d01e40d0a964003d00004203607054144c50200500f0090380d120304021800c1032042040b80f0740091b0050b0310100d4040d0142250130f00040240c0904171003500d8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 684998336 1250 684997086 684997141
    0x71226161505100302100f0e03011a030609030703141606090303050615040b090411041e150320090103020f0f03040b0708011a03131506080106090e0705060a030b120105 74
    0x82005a40c6d66140c42d415039000d1411098a0310000000e9544044000481e41e0550900420b0a4142c0310041c0d031541c100c004601301c2d00240c030750106294984c4220980600055404e0522000d103115400051a80d12503051810a408100742c8be05012504181d00c01c83c0001c0d2900b081c407526141580d9103140410b1840715891a013442c185004800f0720610b0700590007252200707081a0784c48403e4003954001d002002c1c9030400400070000480d019072755070041da00003111078103070640414441d1041d10710500d01d8107016100000c54a40080c1e081c0c004c038400c80c0c101038003001a040d050b440040941481d0041800e00394503030405140585c1d01d400000c4c03012040218500040228801030701c00785400720700039003003155251521105400000700c80000507055010309512200080d059510030811140404000c011454a4400c42801c0d900441e0340e403c2640d121a00911041c03400800400d1900c0da80d0900140e2041000d01203000001407421000b101e0b50b698080010006003007110400601880d03400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 684999586 1250 684998336 684998339
    0x215130f0506210a111201060f08090d0c081b010207060b090906010e06041112040c051c3903050c0a03150e010e060907060207122616150510 62
    0x120b180190b0810380c54010f41c092071011540229050707100c004074400610803995100305003400c07081c0c0310380b083c49090f0002c0c580d0200101d42d64403e181d1507005070b045802504031003841034422100d0000c2100c0686608200b0407040300340c002d9030900a060b1903280381c0096100c10050402a0450742000a114040c1d400c400c10006440d001240d0076064070303440844c200c0c842d198480401d000300880d2a01400c10640041c08110503030030702216030b04c1280f050188244d81e40d240c02c14410180e0484814000625140c441e81000614040d0341c602c00915103821444070064031608000e0210110300d4085a5100304401442401804d021101d180c1506490881410b880e41d6203840c90f5200612748a4215503503040b84503909902900310f141d4181d48201120280d050100030300b6110a00c0d881490094821040d0001d00c2c502c44800800089070000110200129404400410f00d03c02204080101004100c15044582c00160703414102e4045c1c200741312412140d5000204540004c0c19881d15000c0d00d120 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 685000836 1250 684999586 684999607
    0x6010e1c1e030215090a060203101707030206090f0d020301091208010906141e03060403050418060302131d0f0607031404050c130b0a090c08070807020d0c0215130f0506 74
    0x8092044652544d4980416601d66003514101030400c003009004500001c01c2c0028003c0305004901941c0002c3c524121004042010300d65410b6940304c0250444414090640340c2c1c5805500c0d4000300c8009000580a034800d03500007421602007880440302c1c1c2c42112a80701642d517014084a01500c3c00e02e17410460340742031465a1261640000c681880744014a25140d0602541c5803600d08030b40e405011154542064940544603822501402c960002103c00b202c04c0314440313004020417280c020b0300032140441910800800b610740c0040701a0220454a46c0c0b050024042045a600c0341c03821015000504040400800752071000041e95046054142448080303000459807031390120007181e202003142c50f40d0321140042c0c089410a00ea2101c2c0e085170015880c03403503401c20300b6121415600c8100f80d644420043e81c403010140e80180050740b1815041e0706140c040e8008111440c0020314140b0804400405281d1a5020120420358054100403c021007500341907000054001140c210f030030100c0740075 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 685002086 1250 685000836 685000843
    0x80601090e012115050a0b1813210c020a06030507050d0911120106090e03031b13030b0405030c06100815061219030f08010b1206010e1c1e0302 63
    0x40c3e1641d00d0348240385240e5144039040c10600940d400030b5419511500900c2c01070080008851510711642000701084251805c54419880702020441407002d5031944a018080521080003c8a910784146440a001c9940340031040301940255105d140b00d41851050104c0c021042c0d12031000c0c1030500301401041c5c5d03007060644166941d01c2c82d0020389007605042c00010414036000e2690840d80000b11650a500b042d04040103070341e209007051182c03000703060903141c0c2c2e4403088400c0300c04101c109404030040904c3c0c034028010503c0516045590f10303265112000e410700107403000c0b101903100180000c64402d080c403a0960101c0320100c103840c07503458210810780300c142001103041641d40c82c0000501c155a008000c8c0210107441040301c0100414407151003800c140c043d41a000710b0403800d14920902d1040c1900c1b410395902254030790a060718200100c846400c040c200d581030003034800784000b258491443c202d500c90113030280403045c1d843d942401500868800034100c034008031005000082074002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 685003336 1250 685002086 685002089
    0x3032d01060f0f0215070c06061707030210050403080f03041529011b03180e0712020703051b0d0e0102150115182421110c0a08030106080601090e01 65
    0xd0609080c14091140105d0500c440010803002c500c5030314083c80a240d0741f1160640d5460302c208810440d03641c0f90311210030301955010500d1101ea02c0b610052006050690b485501e005550414600346a1a587e9480c1e540e000303200080210ba5008c000c10050094509a4010725120380004000102c054003a803120031401c448040350300f0016400c40750790380e440f5038024080c0c404003460030480c50240b441c0003010f5008a58650303140114100c004541a51b40b294400c2c0110381603200d1200503815250861f000c0d41004500390103000050010058401e40107500350704103100e100c054030300c9100f0010003070803d440c20040e8604550010115800d0f4081c07982c801810345000742d071120404902c2041c120f4800e140900c14000b8107249a100050000c030780d01d0070303031a101c5800f407101402101445044540c00c44aa18500d2041c01c0200c3c2e54807003500b242d1100f01c4000a0903203041c907156544180c0c030f03e042c0c24404102e0341320900000401c40316a011400581184003441c001c1c840e20715000c030400400340103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 685004586 1250 685003336 685003367
    0x91e010206072a050a210206040609030e0303030703140c12010e0405010603050d030b010e0d03050d0b0a05040c02060a0b12060f070201090c030b060a0527150303032d0106 75
    0x41a512429101d09011201c0d0b2203006014500702c90242d29040b0f03140c00b4800c408a4845081903461007040c00c81b0350b0102d100d00d0b0203038010f008a80d00c684800010f08144642030303040c8031100d514650162401c2c0b0046200d0f80c03040e00d001c2000a5080403000c1004001008890031840074003d8102a070000d07401e680c11030f000d91a40040c00d848900f007890041c24240c1c0024024800c00503c402c8031601a0406000e1400076250b10701e082110109100700c07401c0700c00000380040d00411028004201c944d010482002001c3c00c4400307241e0326000410201c0d40c000e81001d01580c003260400c04411000e009610b0281e805807144100c03859079140c00e030b556007405002c214042c400c0400003142d0600c00d44c010f042070b40d00f003000740c0103080e5241099039080c101901c4141c0200030000010405007080302c1c2882401c00c034464000c025551054081652890213005802003180281410006a074100061030203000001c0f511842d0b0344000000076461600d44d0081104450030320010485590016210201c041c3d8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 685005836 1250 685004586 685004597
    0x309030905090c120a06120204020c03041203080108060108030313020603040f0b0a150f05010e2b0609022701060c02010e0a090e0d020a0803010315020d151502030705060c0c030d0e03091e01020607 86
    0xf40c540c00c1400c6005a40100f400ed00d481d1103481c00f4154805a864101c824a02c1556003d03601c6a04c010b407284421038140c000c001c520500070f0010700f0440000c41d07215000d51480b0402c010306541d103200801041c0c40201c401034441e00c44c1d003101e070440d40ca2400203002d00c075402c6049a1070400042c3c100c00700c03200c580380300e40c071020340ba003203e1030750030200b401a00702101c1110044070803840c050004000810b4168040d400810b40f04010315500301050004c41156640080140c0c070745401110113504400c012810040c048000c5119525001f00310b0b00500545440403a80400d140320003850001c6800c207150071540140022400300d50303c081260f054942040c1141160750380451014060b1003241d1a091265103030640c0111402001c1c0c51050982310981c04d040003100070b0300c40481c1c1d28091040090841e42208010400390499540105054580c80d01621f0610124203e200304070b480c503495084503500700180081c0207103415428070540200d404e00f821850420200000d41d01c44005011034140f18 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 685007086 1250 685005836 685005847
    0x6170a140f06010f0f080c0906040f0e120a0305100e041506030f050a0303050105040b031005040318090608060c0307171506130513090b070309030905090c120a0612020402 75
    0x118107001c4404401200c5080b500c0700c0d603407280000804040d40c0700d848220392541801003904074010400c0740d04014000c000401c3d98035040100401002c5c40098214026621001d80f40d0124040c03110308440080300441503118281e004c1c1c0074095035002004810310760320303840c002e10030482030300105da1f005600445401c0821140c4d0451100800543d00b000e440c20104040f00410001e000400f560354078030030f03607040c0701a903a1001444181c4400083d8141d054100d07008044902c403c41c3d02855009000c0e203085484459140c030751151340030701c035081003c416480e84400e00c0304950400440340c1000f0146400b92440c900f4032001420b24500440c42d6184118000116840300c40c0540da0745011a0003d01e410741d19206004220146e44040c86400e0103814043d0340948046001d110701d002d4250003507202c01880c1d035440d00c100c00801840104605100882c103002c1021744134208060720a14450103c84d03a00e1114107034038031185000070f15180c01c2c242800c2c01486001d00070303001e030300c8500e13410f075009a1981c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 685008336 1250 685007086 685007123
    0x50a1209080d0c20030d05091608070f05090c071e080a120e03040803120415180b06030c1e15030a0b011d100c050c090115020106170a 59
    0x18440140068280355010407070403650109940b00310f0b4101c2150312032040c0c2d4010f07000c0c8a580c00381c1540b60310b21950814441d1158400e450f0308601e622107550010b441d0180421559240303084056040100b01d540910018000d40314004020400390004840740c2c40240381000240e00c80d84140d081c020f1804e030f101c0c25400e040b003100501e40c07070803c0d5000031900e0b01e0740e503941c800500c0c00303a1010782c4415082c14411110b031041d5012003150305854100c4e002e585040402281c8080700b40c00604102e5440441700c0704105044c0d510710412425000781d0b168100c91941d40c3c00c0010303040101034525482a08481000c1c1017590740c003607541060542c1d000705001241c00c0354001a100300c68484a0000303203c80002007040c2d501c8a070b8868044104240c951001402d11204255003c6030b1140c1e4540d009440381403409142d5001e10030940226114404440700c1010b14004034110f503500383c1c0014040402554541303131a50b020f0166070082c003000002082c1c00c1c0300c400c0c503681e942c101c121409460149501c0048804 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 685009586 1250 685008336 685008341
    0x712050717010b0a0b0f091008090d0504030c03080a120221010b090a09110912010504140d080705090f1e0112020a0504121b06050703180e070e030309041103010e09010c050a12 77
    0x38070b180140b0203580070148d010080c24642c07040310714250b50701940301041d48190082040c2d6060300e4010004d80c1c0818150380e900352856106c02d11003002cac051241c0300840440c105000134441c1124002039a40340e20790b00d07070f089903451906030809901c9000a012444158413420750103011920384000c0843c0c0901880807500051140c5e0380c08039044a41e105004000840c150810303401244170b00703034007100548000c183d243ca41500e043c60b003000400f0311303000c51401486000a00200800140300d440640c5c000b4000907506007001c0c1e9090642401e04c3e000151643c2c1040d03110a152294160a51415180110081451040c3c4c040e448070700204081d44e00034088520321400c52484541d54541845444000c00740c056045100100c0000b002e8545c9502444c0212a8503004c445090992010a1719900000d50b00d141c03801c0900c41c0c061100b030000c814a5500c42c000d4000040c2100c40c040d650f0b50405880d0100040001d05800c0e4aa05040c0500302c0e259005040b01e110549600c5c000820300c0071034540c10701 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 685010836 1250 685009586 685009597
    0x10311092218050613020904030305101d0f09030405060d18120504080d02012304021f0903020102073008070807121101050601051b0712050717010b0a0b0f 68
    0x400924055401e0002d5400025440c0031078095001c071041035641c500503820300303400344c08000c1d0003100c60f902040001c1e0007500055003000800780078411898a60045403000a0031004400940300709134188011942c0c2c0b07040e0990403014500207940b81504003000f00d1194403a09180580c0541d549215003800754081d50080c41e45030740410006580e05044074001c0254105000c4d150503800348140310903420b401441400015000c0c04007022500e51120201610b04600801c16030300000b02c444000044141521840040703181a1103030115541580002450302c0c096411402200403221400c0500340f040190303058400340010001d0214905c146001e185501410900900420003c00ca032810407410011014030214983d40b104d203441d61801d1950700b610700c25600980451020490303034218005140c244c04540da102e8046a4415555120023540d20392040c00954581c0c121040c2400103910414101c1070700c0b46a00000d0208c0340140b00014510b18040c4036040d80c207400000e600407182c6030302c01541c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 685012086 1250 685010836 685010899
    0x30f0b0a470a0602010b031911040203092b1b08030c0304020a15120b062701020c030a0b1e010e1906090f0f0b03030a120903031107150b01031109 64
    0x200040c3d65403201034082c0250704251403281c0603440e410303d500c00d5000078204c0703290b0300940202c4804032079000348802588090940040ca000320801040100007004201c030884400d4031401c01045c420350002024040210300f80584502c0c0b14040c2c6012821001c1034075045608807030419903a0b151807001424650981d032144980c2c2c480b03061183c074400d030096054101c1403001e40c000e00c43c03452050100807043c03089071501c44200444680d84015460140c03c40f1074040c9040c0100c54581e07440c3c0001034507141d0300503011120541003c04110f054805141c082d8810318580c04c5158144d41001501c08219500401c0141358081a221462540090342c01079401081085020454100c1090720040a04488210710200300e0500d40000b0481c20008222503001034155550f0354406440500600902200e000035400c05490754010b111f8828040010a149072190800c020803045111401c4280c845010070305040c180b5080944140741011400c984001c1800c40780003821921440c102c81e41c01e0b0541c400c01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 685013336 1250 685012086 685012099
    0x15011a0c06090718022b0b040f05090c01020a0c030305130b0a020109110603010501020a0b0402031c051b0a030e1011030412110603010b071b030f0b0a47 67
    0xb0081001280d10300c15240745034180080d1004c0014080c0580c4070303040301c0344039801072014100c005040c106910b0208008140d8007140c0d40c411000040e01b034581c1491184c0c0021354031002d0003401c070410045006002c0082c0060500d84210341c0710a00924003d10001d0244a00041ca682c0000d4000d50f0102c090201502541e888191002c0028001d040302c0d542142d0a20700c80c020f990062400f00240c0b4100d440503401004d1502ca1581c546040c414040c08c126007612403106440100814044203110081490380c881352210a11202c101d01e00078403458101080e0000c10805c4080b943c0120484029001a208800200c0c8400f0048624850411031803ca0380004140410710307030160310082d14440c2c0500100d583e00b2803031b503080298a110a1042c0d49a201082003000d0000b601a00c1f940710304010075031010708140d42c0344c880d02c41d0315507401800c0714010084010003a44201c03a110f00342c11214283c0e4031515145461007848408405a03400743c69902c15000a00c010418514408540e01d40c081d00701c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 685014586 1250 685013336 685013341
    0x6030f0403050d050708011401021209060f04030602070506061e2b02030a0803071106010e04031b051204030605010e040537200d05030a1b08070c06080915011a0c06 72
    0x10306c0301c10280075500c8001901c0c01120015840010031220244a000700b0924103c10f032000c010407540000d02c0d5611981d024000000801d0843c8058407200313004d44040c141c2803400c0410041c000a400d02c0181491050f00345030310032900d5104200103414494030310003503c6082481804141c2c01ca54078000d6061040c0c0b403d010411a1000c050340c014119922042800058915000e40b501c000340030701c1d915030b070b910000540800d00c1081c4d040408409031100c000e51403c1a203800d030400b08044003412000100040400803c10760748078050050034035440d2581c0c41e08155070380c10346031011445540f0045203002c0c0b070909100c2d11000b00030850780102648071b902c0c2855140c1048842030010324111440311500c4004090b00b0711010003407810f6840f4000c0c40c40e020904a0036210501c0c0c1c200001303d50110312441034000b801c0d00b401400060f0191541c080034901d84200213101c43c40043c84002560440c0080741c014844658180381502c0b50420750b00c0070410201a10005801000384e0380b0864464a000e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 685015836 1250 685014586 685014601
    0x120c060510090b06160f0c0308030a150f120b0c1603080906090726070b030420010513030b040f12120e030306010504141518031b06030f0403050d05 65
    0x1c064045075841c0b0014002e05494808000080c0180000071801042004005001800325070610b00c200341310740c442185081e1241c442c1207080e001116400e903101da0f1104076418007034041d8441301c01420441c0260010304e05049600c41c00c1c1030803210051415002d0004164030f00100d60a0b240c8080481d0203181001c446400c00902c1402d007500c10640718010303200461a41030002c80d032007050f203158188480c508481c901051110040f4a0380c8525503024200002c1010300151004502890150600c407011000c4d079400110303c008800e0b0a2418040108104500340310260075030300c112500242640350b69079031420300700071110003c9030052100320362551410308141c0160810f840714003900c8081114806c40c0c40c28540d01d1200350350003408200300740010403007009102c0103100005000f03801500d0004510a01d5000c0786c10196440016100002d178940300790900300b00110070900e40920112f800382010012403414800a40f4102c2601c0350107000a06140c0034908659404d080b4100c01c100071f250118 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 685017086 1250 685015836 685015861
    0x2150703030501080105060d03050c0703021009080f0f10090206040506030705040807140315180708010c0e01180312050f131404021c1505060c01050f0105010207060804120c0605 78
    0x181140442e1a020000c944681c0500c079031842094003404e140d8102d10b49417400d1760160006102014944203c11012005840d040d10901d01e804650f00c401546909000d082401c0000b40740a00603141e1040c0000e040144001501d00700f4101444d1002813102d925002062440c071450b00000c1e0442d00003c00c2c403040c0c0394484010710840310000181d0300361a0b01c80892000c0200032904950b0b16a00090b90310800250035000260452900922500e1104101071b0442c20218194843c62869544194145c0f5464002001032800e150910781404541c00002c613010500045000281c40d40c800310480c0600f00740503100f1942400c40940c00c00e5203070f50028000e50400c00b020300840d400389180041e031700014201030081e20354860052407549095040402990010840000180400040340e503001900f40c0380c000040203075004190000c200392a1024203044443d00680c40f0301e04661108808108156010f00c078290403540c004801c03814243d0740d00040b14007040100c8080d2000d803801c011300600c0762548 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 685018336 1250 685017086 685017097
    0x9060a030512130608240f03100504140a0c0b1e0f04051c0f380406060509090a12050918040b0c13060e13180302060907031509020103090215 62
    0x41020440d0701351240c60846004806035811440e621505600c846031550f125903900c074803900549280000c0981c400000d00c1c0c000c42000408040e42d0302c0c1d0902003071145a50060103403405410062524103040e40e030b08550021a4801c501c034856003c6070b903402c40826101e501c040c500d078540407076442c0c0301c400c0070b1141c4984c0710744500c42c17090440310000c110103100c0e0018151400d030001090340d804500354903048224408014403050700ba070280025800c5281952414501110988031101c26281528001c1c045400c2c44d00641d103c0e03001d80040290722036000803e03a031096802020510b05070401d60702a0f80354003602c09400d6029003100200e41402405d00c0714144500d0082200c05519212040f140c030141c4241145040c40486c030040c10304c01c01340250007603480c1007409000c0768074980d0048403900032144038030721400710250703000855420301d0380c1000313415008100c1d03102922400b8650341c3c45405840c040e0010b4800d07240c4a204800a5a010341d1052900f181c02505c9000e280301240344403603240c1c2c440c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 685019586 1250 685018336 685018357
    0x1051b0a0b011e061416020a140f041406060c07240216050a051203130e0108071d0402041d0a0b161d01030506060424110c0f09060a030512 61
    0x1441085800d0106200908030382d01c0c0d8841c1c0d01c940e04080c0448143d507001c1d001490a51b60030044030401626243c00000003042d03d0403840c503000aa117403c1000708070908460a20842c100300c0c0c609102541d401031550404002c9883c1a44c070311418011508210240c0d110400f0080c80c4003c5c0c0f00c010090206070014105150b09641000280f6900000d0540203809004e0f04564030b050241b200e800c004c01039003c60520702080764100303415812142d05146003074010f40141240000108445201000350300042c0207103200c403800c00340098001440c0010000d1000c0c0c4210b84070300502c10202125031070050b2110004041e114404c103607080c841204082903d58040321000e00c080314000341c0c40342e02d22030582401518a40c0340103d50a00460190030085c1041c6c7d881082084000b0703860785078442410003e041c00100b452903980520028100e01d502d0a12182503801001004000760b0f55441d0f9000c0d000300807034141480f511100d0100d0006001500700038628412150703884200c90064014041d10410f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 685020836 1250 685019586 685019609
    0xf0a0605040212011a1530070921080c0f0d080702210a03020f040e0703060603050412111608070e1602190303090204060b0307030609110901051b0a0b01 67
    0xd81d41c83c6908940010001212004201041025501c0c01d01103660900724a5100e403800c050014001800026055010000450b5444070303101e11a104038100903440855403d10458030303803a01d5039200d040040c04d045e0780c084007a500c60540c100402c010503101c1604246044682c00d80d1215203140d80d8810900320000400c892400103409941b002848078012054010000c00000703890280421903002086644241a02800603807000240c0f40e01800003402c0c80051010641480c171006400c80341581c214004040c181420800401c92100d2001a160352501c0e04c03500d400b0415181038200300014040e501d45e440002c40002e10010b0000d228810348801681c0b80c180b0f601c4030040f03030741d050400c001c41c4009a0406485003401140002c8941e580e0b501a042c04a9040e4450780018226a480c0e00660341c01c00d00442031080702031b814401c0314060700140c4c0b000c100001e01080140700354041c001c611410403a0010344c400a181c42480508909850001124100c0000345416a40840300340101411140e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 685022086 1250 685020836 685020859
    0x106080606060f1809070c17040b040308130b0d02040f0e06010801120f0b0106050316030606140708040e01030f1202010c0e2e030c0f03050f060d02030f0a06050402 72
    0x500840c00500801c4001c02c0b0300c2c40d00c0c2a4030010b10081d08002501080c40d120085030301c0150b01c580040c0c510500c62550303168100c44462800b20f0035000c00700500c0e642008140418040c48c11894221001daa802c031784203d840e40304050948065106a03000910107000100e03003e000c0c44074940240c4103a4003056510700026444494650240004540c0c150000d00404010000b2405054802940d80c0c0248000341e40403009858203400d2400a0384441c001800010030030103580300f100e80078003001c0c1c801d03c2c05001c02842e11078020f00c04251201030030308a140c0001c0c0c0d4400c11003613100b210010042d17031101c0f030030542c2d40303091010360f2014003281980d1036400600c085251510620070480e20510702c0e02d0360a401501102401501c0e50428641c040c90f00c100e1100c1704101807500c210460700c2c031003941e0108038020b10181c024002000300c1e00e6017007894202401d00c860070084030802d59100f5001c4e11202c0340c071246800001e14102c13001074554142d0261300180c4c0c061180c0764018a22440c02920401a0074 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 685023336 1250 685022086 685022099
    0x1060807050315040b040602030402120d1206052706010507020411030105030c0109120f150f0603170f0409050a060f1509170616031b05031f060206070e04060306021b0106 75
    0xf84120307001011088000001400511181d02540c1c103d40050a6941541c40c24000b141c5001c03a0000b541d4042030f504a4645a002e40074090700340034020940740111141050140780740f200140050100e100d07402c401c009941640320300155281c03140c0040060258003c040001c40c481d074070078001c060203406045541d171860350052148400300c032915850450300c0c0050f6207a0490401a10f0f01c211605032005681e9095800c00c6c0c02140c0b1012050f490000340285545445101090030701c41600d03110740c091040298440210f025036040b03500800340802e080d62400c440700001c04054100d0f12041c009001c02040603500c10818000420f4240c8644064648400c8034048041c0354480040907035020340f0000d0321010041c820340d43c009426040116a0b4284076081707031180c81140d42c90000040001c4100b0060b80d00058075802112003e401040d4130074104207000b0b4440500512800034000c14810b02030440c0c8443c1c0c00f92004641140c02152100d03a061000310a0b1550212015425030030868045000c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 685024586 1250 685023336 685023373
    0x21030204150206010302060403060b010201090206030406020d060806090c0108090312090f070803040e040f110a180b0d030c031b080a030905011d0304140301060e01030f0210091206021b010608070503 87
    0x51702e400a00c1d03a03041620b10f9650308040d12075100e4080c1195228249080181c8170b1001071030207a44240d802607100c81540d59182d08442d15a48003180c030303910460a111030b511011601101d101c50030702c1c4c138000b10b0341c4c0e0560f09855403080c65082c089100d246010007002c140c0128131101c00f01b2040003624040d66941460a903240254051741c89000c85640110780080c0206d041c1844042c0720307142d420040d204000005080c0308080c0d002008824006104c002c10224500c103266040c0c404032084100e80c481c9031002003030781c00d80a0008003840712a0307a02940766108441010005680316003090344d9610310382c500030090b06000d68119220760a120200200c001c081c0c5003c05980c000b400214142442c045e0340000d21980c0302ca0a6405550310140800c9580c129200e8a000c0c50090040c01c1d0f90419610610184000d26682a4100b1940342d0080c841341c9a50040d0f0030b4401d400c80000f507125506030915045c81a601110700640e50308e4204000f2f00081c1c0410101d003140e000b01c050b1600003d030103030302901 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 685025836 1250 685024586 685024589
    0x207021e130b03010b030703120219050703020105071e1121120d150b0301030c12030206010e3705010605040e04080f0c0a0b0402090a06051c2103020415020601 70
    0x180444a51201040c1441d5a0b2181c111058002c0000c2040130b81c0303d0100f414030340c07183c0017541d6042d074001c80b5042e900e4042221403464480c407a664443ea0006846071740c0c451281c0d000003410000002507400a000a072001080c1c003500784126440000b109180501040090159441c091010104114909540180101103142c0e60001070407002c0b4148041d510740364861a0701100c81a55a40350f40c04c00c0340c20400343c601608982d117019549504608015440004542c4080241d000301d040001c002940800e40d40d04507140c030b50100da0551185944084044400c2d000d03540021020418018100c035000301a100e91204070380c0811059881c4e0504644d64411802101e0140c2ea5000c0030500203a800c50080003011001c6804904002c540360740c1ea13041c001c3c200c1094401002d00e10501082d8a040c408042e000700307214208000452070b05c00441d8041e07915441d22054031803c83c40480c10320410081505d10802d042606100003901000003030300940103030080c50140c0001c8031070240d400f40001001030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 685027086 1250 685025836 685025839
    0x30506010c23031b030c070503030f04030308060f0d05011a091b0903101803260c090d080c0d030b030f0c12030d15050f0d1e020f03030a030207021e 65
    0x1488001d404900e6941d0030301c0380d080036840c0c0b104110a500014141d44d10060154015002c0c1d96281002000c1c24a40f5500e80c0003240302e90010081c8810464140089270308581d0301d41000f0710150b991400213408081441000d0f50440064040d1000f00203040d070101c00500b6140285d1291a03016506000c00c3c90400c0301c507070a00c04480c510025370404004e016020303a442c000d049030040c41c20024100281da0503e9003604103900780c91009402c0540201c280b10300a8016002c8240e0b46a10420700390070540c000e40603104220000038034003600d444403c4441ea005401920b015075500c0441c4425555500906a810010340b4101a0003c14a008210340768100b03810320040415104110800006010040d0100601d208c204080300e1099034070b005000c14410403403006c3c0710032841e1206008290103407881d164499010801e01000091840c03030200b502c502035552181c1034a20a1012034907801070790744030b40e6040c840403480c10302082c1d044d001042e03c944261605410b00c46004070001603480403d0806 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 685028336 1250 685027086 685027103
    0x2206030c081504020c0c1009060207090e0d0e010c060e0c01031a030c010503100f06020a0308010e070f0e0d0804091d0a15051b070609120c020d061109090f0403030506010c 75
    0x401483c98190007400e4446000e6003500c2c44131985100280310b4980040c221004501d4118040000e6a014410030008044c404800c0c408030040c1c404042c0c60b400800750640c1800606148032803183d00c5614540c50680d80003804204000d80c2c50350f065030380d0824041040c0000e081c85010028003c0c001c4c1413020101000d070051038418410720054031103810040c190504040f060400040500f0001c00d4000100150b4015202100e1241001010342c80140c0018070010071010911003103581c002c4203900740603400c0ca090fa07000c0001e80002400c0490040d000703041450702150100d07038040380b64454242c601c024030303040a482c4041415a5143c0700d070402c02500c00c0310300500054a0705d00a80207140d105624407503580d90200070007d11a055006100151001d55030b8821100400c090844c0c0c0c0349a140d6542051301001d0b0702c07980051424012641e0041400e900c03031092540c0c4c0303e407a0051b85c109c0c48000b407480d80d0320300c3c01c0254015008822201500068200000b00d0b44035405484648030480e0010002c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 685029586 1250 685028336 685028371
    0x20f0307080f070b0c031e06030a030f0201021b07090e0a021c0507090504050307260405060711040606181e09380114041d09032206030c08 61
    0x11100c45810072095180390350400c00c20f1200007100d051100c0d1081c0900c4c00c020b916801c1c1160010f070024510420034141c025040f0a2080c0d56500080f075200705581440d1030f1032800da034000100d01a01941c070b411403003180d4584148403d21300c017040d6001030b5403100400304503802e098900326079030301070100c070103908070702400d04c2ca0304060341c0c8102d100c1d18203024504683c0e0343d03540c0e0760b1500103d810444050310980c10210703c102c200f01705224146048070104000140703603038409424504900c1248a61031103040e00213052800c002a51440c03580001c002001001481c0c0c2e2800044c0000c0a89c100d00709581d148a140403a215030300c803075204240000b105001d680b050a000c41c4000400301c081030b02109002c5a458504200000c060810004412000444400c015200050444505401c0f0405901400c0c4824001000281800e80d440e01248401350740ba0340f10030200318114452510490026000c070b8200210501c1c0d0386000408840c2c0036034003080300f48071003003081b034062a09513201d6079400b000741d40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 685030836 1250 685029586 685029593
    0x60c091409010b092b0f0b061e04020903150c070510140109020702040b150409150e0a0203060a030c0605030103030f0f120203190213030618150c050409050a1506020f0307 75
    0x2410311003c24000001010340301205400c01c0a00f2189170115940d420410003441044440032070a90095810303191110007111110721412141c1e1403410301400b40394085040c0c1225901001180c56801104c40d603022f0307606040b09079180680c0141001d81d5503100e4058483c40070007052080075110078004100302a52303403c2c00e441102a51205e20240ea0107070310b61036000119980e00400c2640d44140c04010b0340d0b22031038040d01d20240d4008211020f0032000400042011903101e10314150300856007080107070b40e540d84500141c206074103a00007910740f040000380802c00981001c000e60607039019407a1122a9a40040708403001c03034070701407084002242880c841030304110a8014603048405140c602041c1c421350a103103401c0740c10111a09085c111a6101003050003214401c400401c00d0307100c0e203035540002c0364984044403180c03202409500c0385c0c5ca00e80d0503038503803140c0241c401402d0510018004d074105900801d0140c0301c02c0410070a6070b001200002407950002880b54170000b0240041c50524400e504c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 685032086 1250 685030836 685030849
    0x408060c0301142215060f1403130503040f060c0606050406150f09120f0605010506070f20060d0e0606010509010909020c01090f031101230c09010c060c091409010b09 73
    0x203114400a00d0304c2c04012054000780c010580741050b85141c0e55012482c04000130480d28030814035106102070759604c107048550801c1280d43c81161891042051440740c038005e072840c0308680c00320070f07481904100480c0380e9602c01005030403103008200501c101603c80003081701316001882151501c000140300001c0290042c81014542d030010304000e488190740318903065507107042d944100c0d00f4005c046201c9080103074a03c105400740205550032420041c095441452080d0380303a030090085040c0c201c00200c01206a8100e0600c0c940c00350803d44c07034140341e8140c00050000c80340000c525024050014005500c81c1042c0ca0708891705944500c22245002200340082d80021042007403035490b200b0f000c012440c009010808030340702e56144130080d0041d544881c00c54801c4903040d0b090301001c1021000c244007075600c3c642c01031001e0880e0b50b038801c0c880005a819050200c0010403442c203042d10403040503049550801192400f5400c07989130038910b404c02c1005102402a01d1122009028101290900304c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 685033336 1250 685032086 685032109
    0x15120b01020a201e01020309062d1216052a0304082107081b0c0d061d010902030a11150c01020d0e150703020d0209060f0408060c030114 60
    0x40c0103481600140380c0300c400c0f54122190030320802c4000e1094808441c1089184100c904070020310000f540044500000e4580c4241c05845101c3c100200d5685000e44413205c0341c0c01c007a0311043c1c2c801c02d0b8000d0241da813031081d00711841503907611440000050600c0f040900c4821300d03e03500d6560341d281418101c03290512800b540d40050511043c00d80050081a0030801031000c0d00b0441d0052100c155150f641801100008007120000c16081c0b001500007860a0142e0365001554866280d1085500d800700b032904018540240d840742d5191050f40034000607a020940c410903218580740c0c0c40d400103682a00b0ba50741120000e41540c0600700c0c640c042840b5506060500f0740040071050340741c664800c00450b580103102a0030150354005440790306014244a0701d0b41e0b501d840c5e005021540c0c2c407e14088900d4200411423000e00d6000030b088414a00035504544200710b00604c0a0b03210350a00111f454182c002d401034140031311440012540203601003003603a040b41c2c8d15044000c074201103603080c003581d1440b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 685034586 1250 685033336 685033339
    0xa1701050601030b090603060103171204231609112710050a201f050603010b0d0b040b090f01020d0204050f0405040f031d090108060601020d050a050d0b0f1f030615120b 74
    0x91080002c40312902425a0099014a21084080d0880c4c801c1c0130101003113b0280d28150720012060b90100d07000c203400011a4200b403000901141880d4010f4564880c400d40080564000391020f84820f4032041424070741e110903111004c0d80d83d55144217940030701c641c100710808501c2990390040c2011024114000c210f5000c070607118a1540350200c9148134541009400110ba100c901300156403c003485880d90200d003c1301e403040012219201c0c2159803070050000380000c805c103400a041d19004120480c580c0311404c00071540d91014480d003c1c003e401c02c3c09100d100d50300c103000d0144030703252502445025640151840490100700c2c3d07000d0310784c402c007504c2c81c1c00780071207032403010f0f400d5564142d0311802081b0080183c0280d01e00480024101112201030000b840400d02c00034940796803100581d040c0e56414140056103050361400903414001c82da10b665404180b041400c464243c04114082c29180f0584003440388036200c40110806025a80c80c0c1d400203003414a002a044405401800c2c4d00b000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 685035836 1250 685034586 685034633
    0xc0e010b1c06050d0804030b0a230703062111030c0604170a0605100603050f27030d0c0f0801080304030807081810020d020f03120c0304020a1701050601030b090603060103 75
    0x26a0008207180b60210102030300d031841c0200b020001e1000c103d0106e030380480b6201c1d0422605080b0500c0307080ae203605401d100d10120314800020b01c4940698880d4002c0c041002903007143c000c8445d156404c010744141c003200ca18800310540b2241e4103001902d00450140181014101400c105404030030201e490501000d610824511310b002c5000e5100d40e0f8014400f11028455241c00c02c10b014041e50406403000e0000b840309410000160107010105042d01d441c049070500c910300188080386913004038010f140c0d01034074040c840030321300750403041042c0550541e44551030715a81c0d80032259105c3c082e0b840003900c040010412a00010281802440e2981820041455400c154808559042c07401e10040c8056480099803900841d010003e40e00c09c0e60141e00114581207041b040101c1c010b1000e00200c2c2404000f00101b02159114803840300a0024038030410141803660300729601816081c1e40a901081c81c0c000208060b09001c40282e200e400f0142c02403280d64690782d9002c0c100c00c45001c0c1000d1380903 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 685037086 1250 685035836 685035839
    0x8040503040f0602010209041803090302090615030c07050616050a0e040608010e1513110f060909070905100309030816021c080604111e0904270c0e010b1c06 69
    0x11982e12032001a0401d0f0707000580b619810703800c0c4030031248245002d04000c0d0464001c40d0001c0d1740304003041c09032030381031f40c0390007050300e40c00c000c81e81c071200e1500034081c100808400c0004844652028014440c043c03804c460140e11003e90f5500da040d03541c8450800240b007080721202d654080e0000450b400409400003910655901e02e0901b1aa0b601c05003c5440c1c00240361451008d960314140f90f08079030b101c104c55850036401ea403000b003d0829412554007811400404c02c400d9520380c820b90b0b400903c09043c0c24101c4c5040d250091042403d8081c0c0e41c81985e006060030b00c241c1c40b82c400e0305a8a40c0c903890b000f0850315521000741d00880003440010440c450071003243e0084035000c00d00c400700c801644a500d194203052041205840103080d5071280d00380240641406042ca443c462459803101404070b580d5482124049005411040ea03150880007003d01500c9240c11208003c0843d5070280401c0e61213141c854640d801c20400038800c05052032024030501900c004150b0400f590241c2c4040c0014001e07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 685038336 1250 685037086 685037099
    0x3030c031b0714070b03061c06151d0702030712180f231e2b0b04200a060516170408120a0903081804140603010f0b060306010804050304 60
    0xa60180400301e8000c0c51800f02d4003001d42003003104801a01c551422182140341c1a0041030060300b0b01c1072400800100c0005410034071005502c10b18885540c11984c03410a51100305c901d22928480c10346030a4011300707400240c0c1043c8048103442c1e64590102440143c0070180c032084426041c00036903d070700c074440808000303080041e1140e03000042039000c10400701038030424401e5150980d0380d10f1880c0aa03500d1a42c41541001c40821003010344003c540c030f02080d80c05416035500d506502280d643c02012140044030a00656000b81e9102c1c0e03100740d03030920114014038038200700104161074a540050503c0c0c000e0003024000e0000d0040661001c0316031601070b600c0c0d00d030790f034210a25140c2106000c20014061280c00404c1c0400c2c2c080d4005424407516024601030010403000083c40007814080004c43d0500403080c640e084ca5000c804010000c1c0b05104035030b90030b002c00c50400d03130b03882c0d20075803800f400f0000001d840c1c040c0f071150440c0141000c2c11552881d0054550000c000d0040307440d40420080440c18 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 685039586 1250 685038336 685038391
    0x504030c03111c14160503030f0a0c0c0e04061d0c21012f040b04050f0402281805060d0504030c05060f06010914060a0315080703150506060c03030c03 66
    0x2c02d0051080c13070030703200c0310303820b442d090000c0d2500300c1024900c1e541040c040754900104071100c161424001c1c0380d0724100340340b0481c0d00c1840e8110041100354201400248038900340702082c003441c010392080007400e4044c0c410580c1000e03040c1070410701380c200040035600c0340b410741807a10003860601081c1c03040100c044000c9086500955910020385004004604812481e42c03070010204c00d50b225440c68a03080603480d804901071480b4607403184401d1307580c0d0400c584130b54060304d03090041c3d10b41c0308000e50500b00890b10b060000110400000f4010032189000110500188044401c0500518070346010103020b034000d040b0090090307080c0f01040b030030440080c804200d0715114031a03481c1c5016680c01c1c01c4000600d50710076540640060b961000040016688040881c0c6891030103003400140039144000750491110103a008860b01d005148000090162007400c80848486d06602040340e036440d4000c10205008001003685540c0c030074030009269200100c01103030071105000c08018902c0d6140f00c00b128 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 685040836 1250 685039586 685039639
    0x11030409090c1701020a0c20090a0b03010f06050a050112090515010311040b100c06090c0b04090b0603010e0112050f030a0509010206090f0d1d1e0109060504030c0311 73
    0x400d40b0b0340042c00c011440e558080d03c0c000f514440001d6140080034140207207a02100b1501900101c000400c0c0f1100e00140c4010707074800000a482e604151401c162000000c082c7c4542047c080d50070f045a0101c0003c141c41880e0036200000e00c0da0700318500b84401196040c000050300c005090362151460003003034007000680c0c899607200355044103640c15031078041070b94203c03003d041380250305001c0e80705051350754001d03030402204203440c142450711644e080240c003401c521390003c0c10102c0861070105498240b0030080082d1050f85105100402d280307011704c001d9100074800c40100d600004014400081c604034801d03000e0b8040c10132241c10460000030541143d11180608021520020703900c005560144202c0f640b09000c0300c041d0001441d01200b10b07403100a034800700c50401c0a0040034440c61155403910404d07403c0054418a8607900f800c12005080302c140c44040e0228121000c0041c01510503c1110b003030b0ba9001c00b002480520710340c4c03404000000b84090300c0c2c0c050701c250303208211120074011218 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 685042086 1250 685040836 685040843
    0x3050d23040f0501090b0c0307030305070e12010605030c030a050303060402090102120a0e0f0402031b0d0e0106030507030204060e1b07020d02030a0c0509010f0608150103200706050105040c0f1103040909 89
    0x10b429515000015100b100280e01001030741c2801e100f50b180d90400481034980c19501410b0102e106d40d5400011681c10030300140c1e00e41e00203117405102036003080560140082c3c80c0700740d085403000104441010340c5c030b40d41e004004282d9401000094807a0805030090320f100e80c41801115244070887d05e650b11a40c2100800500194200203600a0351070044406010b010090304d085195081821a1690b00110072858005407140010200740824144c4e221060600040000700580d540f40d142a03a01c9807564801a48130b03504280707011034410312103024140200340c40d8540f030f0000c20745e24170042900d802c9004280ea01c0001d80d104000941ca05100341641607108101004070541401e0800203540010f0f04000010041e0b07171024441e158102c036426401503500c0400d000649240c2d40120701400a07011001301e9030200010041424810001070000c20784130300c02c01e0115a880e0000d01c400c50b05d00d2003030310002441180d5509071442c007407401d000161240d1030542c0e1400e0789070800e4134103444c0b0b2450100d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 685043336 1250 685042086 685042109
    0xf010b09060d1e140f0f0c0a0f06081902040e04200d030509040b1507030f17190609020c030c0f03030708061002032101091503050d2304 60
    0x240120300e4800030315940040c04035100b070a0008180c64854100c00d402c90103680841d002419107081c000845010039281c40c0480485003400ca8299030241c9900b46407110701441d1090420409103417501c001c0c2c140580e0710740c0600c810120b151080894000c5405090a40c036044000880420003440d40001d10181c180c1d0b5100c2901400c26150414040118a01c0603802d114407104040c0760ba60b030060340209941d0145043d9448050079400240180030fa00e0060f50320040c40d09581828000d2180a031210b58069228a506a50500c8041e10309016001005911046042c0022401c502034000c0c030f5217041d03a40000007032003a00c43c070422040384e01c42d0b2803500b42644082030108002800300046000b50300c070360b4003131400c0d41000f080291806002400c8103100710031114150340071520030803d4901400c485c1682c540034005c0da008001d01b004082c01415003043c149690780000c45103417401e03402120b034014000c18498a40007800c0b100d6200e600003c800d60108210502807400130100071b80b020f0102907004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 685044586 1250 685043336 685043351
    0x1703040827011e050a0c050f0105070801061106060a30031112090a0302010e12060708060f01020d0804080307090515030f01050a06050f0708040b0c1509010b0a03120e030f01 76
    0x2501c604080c4140210030f000c058010850654850156040003180b07003461800044146085070038400d05401607562903183c801003003021541300e89074904031252504c60711000e10758101c00c13548580080380c51541000b560102000740c0b07110040422201c50b14800184800740c02d001070306007104045402540003076641207150032021814002d00c07121070b03240050a45081c60030741c0419000d1203240f2010381030103107400d61074a40c0d807120b0f04000702c18641c88060310110315101c0c0c4054903d09090340d00a01411040349d88c1c8005500000b0002500e0344140c681a0580e0b4891381d64010b5031b4002046a000c012002d240003da40c3c440d130511802000c0803146154403031030420418403c10f030301680881c4c8220343c114020054640c0100880300c15281d50f04500d55184501d0402001910807684008082040001c41e6501000c0105407650924840281c3c0120340c0c503107080c0d19080c2c2d0022019207a0043c0000d004000144200d41c000c0900e020a041c030450b00e200c1d0788006420301050001883c22a51204d04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 685045836 1250 685044586 685044589
    0xa030309060e01180f081207030f060603050f040b10080307110301050a05060a0e090327010906030c05090909190b090d05030717090c0a090204060206131703040827 72
    0x1503031440082e2030000c0282044112031031204128203000600400d0011405e0814400400201e0f4618140307403107110340e0380c1049038000b0020800d869801c0841440c00c003000ca6194440c0c003c580c0158416403400702c168035152a085554480a030503600245200f8100041801c000d001815005004071000101c0c0941c03481030500350741000300f40e481a00d2401c0104280c076a62401c00100303907440052807050325a84c1d00034091640c42540a0f840c8500f80c20714030041000100201505c025400380e075a080d80780d40e500010360541d60458480e40c0410b02c1800031682500b04001082e600540301c4c0b00721500c0820804044c81107035840301040e1103000403402003044940d130400044944512030f161081ca5441e180307030000c0c481003510300300e94200442c0c0c00100382e4221042254100301c00c0010306446009076140c1442c0000e5005208401c09170140714002401d5a04501c1600001d81e0020301e101c0c0c1800c0400c000c104682c0c00104225401c2000b03005c013a10400c801d0300d04961061480e00c4500c0310680010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 685047086 1250 685045836 685045841
    0x50a080d0809031e070c030b0f090f0c090a0c170c030420031f09050d0f1220070807080c0601060801080604050703170d0534081b0c0a03030906 63
    0x40a61289510800580c04620303840545070240044940080e43c485c90503150000d01c10610380e00161040700b2050900000d403130002443d034029082c010407603458120700c402e901e45480e1041d84942e840800100010904c0c0640c1d00015548140c51a00400c440c0c00c440501d00143c0301a50304040c00040030040108009004031400c03c20403140342040c05039481100003a40d01c00003d140f40507a8601c440100ba08000d5a8200201656000059540040103000c0040a00c403070041c0000028072303d000c042c925015188103200d910600b100d0720f40c810007000040c1c01066400100202c504103410824000030888540240000d500c0c10405400c065160000081c0700c80410382000e005900510203100002e0b10000d1b0682c100e1358098201042c40b20211031131020303070248401c0503000c64205010090812030080e08148042c81306041050100640080d41c611204184c1c10070300492a030b00003140f0754035080c03101c45018030910b48044d858000384201c0541030104411007100825201d007034400400c41c050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 685048336 1250 685047086 685047091
    0x806060a0f0b0307032c100507090f0506130f0609080114012105030405060a05070524190920091f0302040f1401120b1e070513050a080d08 61
    0x511440d81c401d420300d600d00060788005404801895560303007181c030149500310f18140804032056807803c102e455440b04c0c241c1310461100c0711820b0514240001e880c080c06980603400f0703a402444814a814101802c0c001c050740100c418140d84031a000700011603143c0b820282010701200c0c0d5030b00410501c0c05a40e1800e484100c0075011000e207074000140000903000c3d201c2c005484108456441010f06810000d06520590304100d0308a080055a01c0005401500400c5600e00c640201c85c2c401440403032008030745031952000e190401d0103d000c610f40122101d040c1c0104141d000001502c14542c6d034640e01c00032050340996524105040c0c030b14841d454422040340c0d1001c1a650200082039030001754440400150000038450765031020390300b0700310903140c0c00719103040704541c0344d841c940d611140c005a404500706000c460089a43c000103e11080c55414005030b500d0041c24440d60381c035000d205490300d030000006500c002c45010307400901e0350380e000e00c1c000007810500080d0607030540c5502b00134041c2400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 685049586 1250 685048336 685048349
    0x21070306111204110d020402030c04050a0e06030a151812031506022104030b0a0504051b090103030807120518071e27020a050a0e030f0601030308130c0806060a 70
    0x307200c0c4440c0c02e01a801540da00552000c0d807030400a219000042040ca94140e0194106201000300a08d4881160041050392402c9904d0f0310400d655000c1c0e583d00800841d106505034109800c028006240082003014280e02c1d82e8001c5007401d64190710300181c0c2d000301000d03200300010341d50782c940c200c2e018803d0200311201c09500d0800039080900195542c00031411180d0003010348010003041806103c151000340d50300c001d54059508083e21920081c24082e1000d40c0e050140b903080c0c0c08424681c4601c264401400303070941c0800e80c69510155400e240061905040c818030b649003028240541c440c05101d107a409511004801942c6082d500d000c1c29170f00720076507420410035140b85c8048903407141411140003040510340007100c0c052084c02d07100c483c1c00c030502d030034004600d100c0e038150030201802101c034941d80e843d2005103c400401d6038035030300d000302c000d400c2d005940180301091040248030b5001150340f01b180300b1888550b4039201c05103443d03030194005130030036000e101c00340c5040c2d44603070000c4c00b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 685050836 1250 685049586 685049621
    0x9030a240b0405100b1305120d0f0512060f18070f02010e0a0b45010b0d1101140906070b15060c1005100902120703110307090303050921070306 63
    0x38070704d080c0d150150b0345001303020303000d000490611034410040c55402e01502001c0c200140c2c50421071003099441404050f00408a521022904140741c4940d0a8507070a504440e00000d46c1e840d88c1c01448800030200500f40d4214100350303c1003882600a10170a802862070750360312240407406160003805c59180035603000840d00900c9000003c1206c0c1d00c80f217174100360203141140d038102c1c2d02011100031050402600000a41c400b11180c2882140381003061841100320081c0718440c4110100803d245408100501040d01c22000001030752040f800d10041c5524503540038981144800021440d801141041310f48407985001c2103c1c00b80c41d20040500c10505849840c01d00040d642c2c140c4d20f422a0b07003404442c096441000905011041c2030780c0d80103000d079180466a55140410049a401c0200c80f9000400c0c00d0400181710130003c5030071680700b50f201c0c0d65085039a500f03564045400e13912040450342e0141100441c8041105100744d580c81034100c12005001081c13441c0b611005490410103481c01c0c40c02e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 685052086 1250 685050836 685050841
    0xa0507020615040e1606111006051e0f0a08100e0105150d05030d1d06180c04200309070e0c16120c120201020315030f1209030a240b0405 60
    0x50300c02080b460346070300485022858000902c26a0702d018103043c2d4508011a62900005010340c002a1b07907501c01c0304600654206c104881d800030142c8403584142500032500221000d000c1c6102003020003000c0d40144a48080031603600041c0303254585401201a6410040c2441c851250f1480391041000098000388141c2c5001003200c44003501c64a0001d00908580b03403003804100381402224510385504030104080440f000c0340320740c0d41c03170044900b451900c688000b00340b00081c00c04500c0030000b0018020300513802c81c40c003803001511803003488072003c440041020406e141d211f405580700344103002c0140501480d1a0707a04220070b1300a86038076600e01c010403051170018108000e900006401412014400100800456610881210103803070203c84502d079821956040d002140030300704001c41c0144e03540c8528201901c61901d41d00d04500c581c0901c1208482e0365001010f0a60080300070140d071100300c013a45030300e085036019030303039583c011800f01e850b1849281c418070452069082c190350412051 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 685053336 1250 685052086 685052101
    0x10f0c02011e0c12111201080c100e0f030a080903010b0603040f020d1406090a02030d030e0304171905010f050109111204060b0a140a08061308070812040b0a05070206 73
    0x42074181c1c44803403180c440c08a01c030058020302603945480b440c41000c009040c003644000301d85401185003034003441e00d031500000758040005018012762000030085244142400006d0300c00341c10705074070030b078001250400c0000e00e5035080c000885114011491030703595840304401c060840d0b0084100030700c90314050092001060b1070b16000d09240f40e0588880301c030044e03641820800b804190b62600414810b4038104080b035800824840903840c401d40441d4940c4001020a40c19034081142a60003a4001d0000304400362080c48201e021080450a0350710b00040501c406204254008c0c080e181c41e0f443e8801140400a50710030703a0f0040840013410003c005012210b109a80b02d420005000c1d0544c000205041c4039640c3c1c480d8890f000020502c5070a0b0b60b0758415000c03400360f41c401e414441e4002c4a40000d001002190751440f444185642d2142c403143e90392140b8003070700400c1007951400c1c41440700007031000126584030b0180d402020103100300e16000c1c1c1420140c840007000d010842d0804803d11191 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 685054586 1250 685053336 685053371
    0x110d080a080c040b16050606101710030c030302060121020a052718010506060403030912030c0501060605040305010f0e03030a020d0b06040b090901090513030c0317010305010f0c0201 80
    0x1404041e00e00000191038201c506001e50141d034114507040480015649032140e000c015070102d4502ca00c054404035035415007041b2098414181c0040403500407c541e01d82c01031030300102540820b240000000458a0b600e6081c1c1481a0fa0011009a0f0042005002c40300d0f02414480488055080360000b40c1200d80c00b02c0c00c0311004e41705450140415142d82011260110140ba1000100c840310211070f1030a1070b030040c21048802e030070610381d51a08022403035500380402114207490b00758450383d42c4186450819426280102e800ba8200050032030306600045081c040c0c40000e02903903440584443c02d42c2400c40c02c4074803a207a0b5140e030f64548201c0180c6028040107a0360301a03079281d001a200c141462000b405480900e450581c40900000d010800c214030802038002880c040d0381e420240d03a00c070300010341140e40a0325034190318403140c07400c0000030f4030454402001610031700d0107144141401c046107a140f00e081c1c00c125480e9450380980d00303a40b001441100c1c440003c84c4001c3c0300d034901e544a141603 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 685055836 1250 685054586 685054597
    0xc080402031e12030c220f0b031e1305030309060103020906040c0f0311090415030b0f01030503040915030b090706021605010903020f0414011403011515031515080103110d08 76
    0x200f511020000841d46409030041c0c0341d0032081042250000540054142619403250043c1e4220042003400441c007035003080f003988d03c64040703604c6402d2042d4020b614102029801088442890710a0031600005101400590f004004100003000d0070750652040220707030764004103a00e01880c500615090342031f40c401c100e220482403a0800048241091350608464450b840c641c6801c54200b26020f41c11040c1110210110b82c041c1d107940900e07884908044510761780c00e01c00a006a4070600040c45684056400004144060500c00c0c0a041c1c0e00e07038034000d00101c1140c0e02c000c81d4000c1c00d01007007010f8041c05200031023000041d03030020440c00d142c000b0f461050319020190003050014401021502e490380301e104800e8115009048940e540c0c090084c08000c402205401303035091286810320f80500d10a00025500110410b03507801100d004110018510f000b07241d800818030610009003080c800140205070892a030300c000d071560441c18590304803682151800c2c0134841600070f501c04900303403809072036 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 685057086 1250 685055836 685055863
    0x70b1c20090405040302030409062301090f090b010c170a080a05070207030f30020106140918010b04110d06140102192a0602010506040911060705030705010c080402031e 74
    0x10b0f56200c2d424101c0c9940038a0b082000018500030020510306802c100c0c0f0080a100030003c0d06940141030011105c01519224520a15905520921104449802054030000185000d03088036400d0b480792a1910501040007030030a04c00545004440d50000006030b101c01031501c140000e0410400c020f540b40c50510000c2d200004980202080100d003c03800c080019000070f42c0c490001500c03041c60382d262102c401c1e0b40095860148001031124440300b1240300710b80020604400c0d80e0b14082c0b03a9450a200b020398a020355030b030b03044140155440d0b1181c2481403000d81c1101c0d40701c3c40e48407407450403552a0b400190303020080075200c07410360783e0002c0c0444140c1628002c103000208203182c40041d1464010b401c4010f00d681640d10f205003004000c2032821105140d000b800152036207000e0008543c44120080c1030b03541080c0030104142070020040842c0391280d0708032840c0000b951142800c4a4445002038002002c5a091106500d000c002c000c1120011020a0203541c101c0ca04440d078982814140c45e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 685058336 1250 685057086 685057091
    0xf06030105130f0204030b010806100e0601050a0e0d062903030406030c020f071e15080117071d060301050601053f090106090c020f0309090405070b1c200904 69
    0x1100340c080c00b0740103c0700c4400540c1e0195140c40d00c80c40e14481b82e910034020840244605800030b01118581d01d880b0088995248030b4421b59100c140044038640e10a9071080c042c44440e460071246900c615011080b0309009000002d80d07034900d82d0340c40810540d0749407114071810070340f0410001c0f41d03408800c95080f41c4283c200050540700c154016401d202420100b180385000d0008001100d481b0003000b044042c900300841000745848260582c0f142050002010008900c4801131144074003554114013031006800407140307450355600700000000004c4010f502c85074128811b000306030409004458100800b400e040d41046102845a080ca05001000f04507452280d0800c0c034255810410444281c443d50310340c1595031030403601050180000d481032641789407070080540c0d81c03c1d01c0441c1031003400c020352018614120911082000303207000500240e4075030195120018500200c18002e04440c287c0c448140b40b0070850340440c1007150002c103407080c0000700c0c0e000d00c038845010400883d0f94080088400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 685059586 1250 685058336 685058359
    0x110c1009030f0305033420030a23030f19020904090b10081902130f020a1d040612020d03021e0106081b06070b1b0403030e09060f06030105 61
    0x44502540d1a4000781082c2d100ca101c40040c990700000840c420a1000311401002c111080204882034800800548860805501540ba68440e80881c241c4000040039550000700c90000320b410341c1e00110071a0003140c5500b00340c100010001c5c001c0742e484041041c41c1419484c140e002c103a14003400070101009404440b20000300540c5540c10381c5e121208c090000c0210100c10320301000c0700f141c1591417100103071605100254550000840c190314081c401e0110100075907a0f803d125112220542e2002310320380310702d0130041144051000c0c014600c41650703880701820240d6543c0755400807800c840385c0260300301203040c0160008106800c070021b0781079440c151002000e040403814500d60980f46d03080c3e43d41245031500e5000054118200b5240c01360b06444ca00d100b510400700b40d81422001141e0040750511070500820700d4501129400517a100814810740390681e11100b5a03407041d0004c0300411100030722000c2da400c201c042d6561044d000e4500003501c070b8401d0b0000d443e07800140700303a078030807486c8101 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 685060836 1250 685059586 685059619
    0x4050d080c010603080423030316080c010905030a0f0306050108060d050c2e0215070c050712151d070510031d030405030c032802150307090e07110c 65
    0x881e07042158000082005a46901d40340e100fa0f80280b0580386910503584d49000c01c52102a40c0144041008000750300e402c2d003101000c01840320102c0e09031442c04081c003000900142c01e018202003284504003842d82d842c01814050200c035911107150041600e004004c0c0200d0740c201d084290000300817100c261102d003039450b2a5182078403183c40c1940148180c02420068411074170022003c00704101c803820400e103e042c0880e81c4000e4100e0301010207119a010594003030191a40118113800b07041986c24403607d40300c0400c0801e42080c4200e40314010400c0c4409001c03240c7c41100740c1400c842c050300704466002d40500c0c0d81c80742c540c01b8441c401d1450190401e480e40c02640031141003180c403002040e240036a0200241c40c0d40182c0f00d041c0c060301071026205554500030072551002c40700d4000201c4281c00400c409560109128001c0341c00c4110308801050700c7d16080302949c4a035103950f03070f001c0119090505c40c0c1b8106601510b41c1050090020711000c40b00070204819440440c01c0d1500703a1910740042 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 685062086 1250 685060836 685060853
    0x30627040f08041e0f14010203220305070605130e040f03141e120a0908030a0b01090b030c0901020106060801050a061209061803020606011d0409060b0307140a0f0b04050d 75
    0x6009020740031400c0401c081c4803080c0d40d0303038100b110701d20310344110720311390340c003030001e0f4620174001d01c5801600104041440441450701c2010500b100341c4500c0001cac0d449540b02c03481c11109410050200380702103960300814400f003c2c00c402502058007005003508140e40e512900008100f0000c05102090075043c05205881080c0c402c4423181d600d80e820b120408410f5820707154403580051584010711030000715016554040d5645103944800c04920b13554a40e55404000c100745202d0078100405a03100040310718203540554040c0c0d1202e1019555145070100190071904154403180520941e00300400080c1e4501c17400404451803824010722a04c0e070402544010403a01c08024856858081c0f140069041c280002822603c65000c84540d030303d9070070055408900d94001059a51000100e000917402c00380c005d1845030f803161001061400d140c400007410254070341c01c40740600c11107565805242c600403010100520611400c00c84180c14440c0c80f400074821b40c003419004003e609042070401003100b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 685063336 1250 685062086 685062089
    0x50f130b2b0201121104031509020a09050a05070c02060a0e030111130611060907061d0405090309031504020f0f0a0f0e060a06030c0815061608030627040f0804 70
    0x9a514201c410045001e24241e8103007410683c005405540b8101d4040c146105004100825400c1541818076556a1045000d0310b40b41c0584102c0d250468000144ca61000900c00b4002d1203401080c5031074161448821510700a000404205901d5112005030b1141c01c21038038060340c10b240a00122943c0ca000c64050100c5022403100030000003074440207c440205010151900e99581c002114105c45041e80d4541046d620750f0590b4005001c01c010b0280200400e84a011001d20901c98001d400070000301101d070100c07141000342d000007a2980300303454148200c174032100e40030b82c81c0581c50919801103001c0e031102140d01c0d8000c155600c44a00c440d964181104000e02002a5801055454103079511030707000142c3c0d031a8003980040101140c801d00078000c1c0312034000e0039030f0f80d01c616644a51141c50303110100c1440d180c02c400b0070025000441c2030b84a00c90412400b41e51401d9403070030514180429504100000240e01f440f86032000350003a844101247c000e43c0101030700b000300a490030501041c6c89503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 685064586 1250 685063336 685063369
    0x7080402090c1605030c0d0809030a1d030f0a0b0105040c0c1704080f0a020103233408090705150a0f02030d18150501300804030c0906050f130b 63
    0x3c181215081020000052010015103401e0b915440d2103400269426441640c11303d055800910801960902c00c020440701c000c42068424006100c0c01c000c2414003040c1000c00840741c004c42d11402c1840410b0042a005103410364040242c500340d100014021000f040000b48031901000180c1c100308810820b5401a10f900704c00e41c1c0801208103100d40e42d80c640040c040340480c2c10003107480840c5a610000f0700311038400c011b10101c1a591400c4286d821013065580c90300d0403190b41c2005d910089807140e840020f803181e448140103400d001c0c3c0298134007040d640c000c41c4500c0a01c5450040010040d054035041c240c40e0800302101d0300307140c805a042d80210710000e00807616051b1100c90810505500c2409940101030104100c80181d401c0c109940c000d0085544503000f02003483e9080748034181c20441c0c0b541341900c2c600090340c00d580c0c10f01550700c198010f070b41310381d04100d0502c125541446030900408013110700206105000c0041585565070550000c14543d480c0429545030316a0303951000145c00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 685065836 1250 685064586 685064617
    0xf1306092105070b150904141507030204061b0206040e0c120406050415050f011a0d060e09120c10020702010519081605030f0f041b240807080402090c 66
    0x7440e000030510b810040003078411074440d6010403542d4400c14014401004040c008804d43d40d038036151041c5403510340c40c4c4595544a18548103c0b88038a018445000741c54540d005a59145005002054803c148140c0c0b80d207144552819070069490328211411255100144c0c100c0b5562100c545015001b0f4810341e0351180c000b40300704801c0040c00c2d070020340b240b845140007808080001a08004450040b40c5c02d5001030b0000005200c0402c42141b41d40d24800c4140e5040e00d40f44c64003020f0019541d65a011401601c0424148074040c9008d01c0342000e880c4c9004105410305034590741e12a554149000050065640000d00b031065900c1101180e0410180c2140d42111603104000205428412105190082c01c40ba4850940600c40e0003103c1c002e10f10809220b41c43d80350000c600b0203089002d40b0840382d078418041ca41401c55101c0c0c0c2e4040050402c4050208420000e1010210242c200302c5d90b0402c10031054208240150421a4140c10640644569080c0e0399454883c44e0280702d48500c6016210 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 685067086 1250 685065836 685065893
    0xc0c1e03140312010915121101110303070819091208060f040b0a05120f0703030206011a0705210d0204081b030a0b070c020a03170306090f130609 64
    0x18104202401140e1040500508418104480544900a20300c1e07004903590b20f00d004100d1a002500301c2030741c110b580d9200003c104d03511980c002c4440c0121900312811040801410425a04850b4840c004506000a14a5446d20740402004510024024008104203e0700d060074004141d020190340359101110881e0100754100c0500f5801080b078850348907081c0740e00755105508090140316035040015018101c1c6506000400c042c20020640700003080c0b0400c0004c00c1b442d0401c02044c001180207030007410195040a030075201f003000e0180721030103d1004100c80400035800003103590741413541e10125403003500d01130103030074441c850303680080e03601800442c0c0801e080710085170b220110340c003c03500c40070711150f65800e142d01e400c0511006444082407200150b442402000400c0095100501c0d08480c1c648a43e50300f070610a03810b040030110440801040305909050000790f0300500424040c444502e4001c00300007000c40320130401130501e5200d845607010841c65404140043c04003056501c03008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 685068336 1250 685067086 685067129
    0x51e0102031f080c090c09060301030803010303020d030b0f04090c030503030c0406031508120a0c061802010f090e070c0c08070902210903250209070e0f1804030c0c 72
    0xe4005031120146041c800b00082e0506088200c0701c001c03942044050410682207804010a90400801d42420460100b02c4040580d8500d00214040c5104084243d241e5045041c000d02d055400480c00061520341401c00b8000c0d503400c2941049160101da021440009510b8440b1a91100354402045488080b09200440c0c16690241094487c10f59003000240c0440b01841c0e9001240d2081c070500d504925555207156400400400c0d941c4c45904005118000f26903490041794201d005500c003000d05000000f00b190ba00000c07580002c1454a810105142003001108800202508520901400c8202002000844820300c0014101e280c180c1c0e5500d551180040046d50118001c420380072030403040014007481742c9050305d0107208600011804c00e411002c103d0340801c17040c140d030304820707200b00003400042e83c50303801c11445481c241d580d51035050007103418000b1025035080340901c11a180c09400100c1418400e100350301ca81c052400c54030210150a0580680d1459003003110004152041348400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 685069586 1250 685068336 685068341
    0x501120f18200105130902030727061407230c060408070509061504090510030f030201090309081b0f1206010608041203050603250801020d06171c0c051e01 68
    0x10360040b00490020b101d007140c01110140b080c02400c544d000c41e00c420601031008560b000d1648841d4909000e90b401c0c429440d42040c1580c501c03800a8503803079251060000710343c852180c441d0300c036049107928245041607031074891092440c2645481080891701010150030100a4241e104074040d00040e41c503515400c4454407810f03903000d034601400b4014049201401e044190790754a80710f401c41641803c1c14420783c20f024007005400c0c00c507064480003012000c02d4120b1048040caa219800019107140e02d40380103020b40440b03070f100c441590485a04102d0859070100e80303000420b81141c0e2440c980c0320380000a00b4a0490a0014915205100000c180c10350000c0040f8021030061000140900c04824203c00740d0700225021600b5810170246040c00704226180303001000c84946008103080d844052040c03ca811085400801a0b182c1c0e00800c0110001c068100c50901c0007405016000700d941c0d002c1c0502c110441c40741042003141000041030213800e000d1721038822006050441000c01d1600c0c001d01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 685070836 1250 685069586 685069613
    0x301020912010506120f0604030c0201020c091f090b0a091805032b05040218090a12052203020307050d170313020907080906010603020c16060f11070501120f18 70
    0xa0350f10170169504c1d8a0001459082c0d1000e01402400300350740f40e42e0201c41005c001a0200c0c103600c14015120020fa07110089548110561030a000741013070404103240b2807480c41ea0114801d5481c0c614800c0303154403440b1100003a12510240071581098041e0a08020b103055540a4000e000100342030130500d10001c928455440a0b03648007801803c52600c1c5401c80b0400d0302e0003580b202a03005480300040c81000d0407903000384040140c4101d2621a1030f03114104c003002024000085000601c0410300801201481085545d501c200b4040390465000c2940d1341881c7c0289413084145007000410000084008498604400500740d12030078070140203000d9140b042c4040784610300305000541560300c07850550344104500c100038181a40703002070550095003e05815040750181c481c0210300d05070103046184c000c201d1942d034a4034040c40f60341c006104030010310240740c081e08074000c10416683c0c03008051179950607000c00001c0350ba0885800000400110140d1101288040450024880911040d20 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 685071942 1106 685070836 685070839
    0x140f07080c1206010803030f04150606030b0a0909030e100516080c0609120d020d090629030109020112090f080c01020c0106050a050d030c020301020912010506 70
    0x181008016004202164800344114065040c10441c8542404000c00a080c065040c504c01da51207200207021703600c0c400e94040201e010302200c468a01444900f4810800101e0740c0c0f2040070b0041e0047c15a200d00c03070f40840500103a07070700380c80c0201d12005915a60300409080c6000410a500d82d49503610b00030050705004c12030404001e0b20340304000710300407110a52940724030500b16242c4a03006220300803e0300000403040c8400a03074003d8490b010f4000201680300c40380c01d801000249a2114003034025428464200034200100c0d41410b110a0410680348100d032002040c07600b42d588072800240081d00d04015115540f01661103140712a104011300388603d503d031307120454507030840c49400340c417a5030000f4200060b84d4248582e01c010101a81e410100c240303000001000f40d0400e41002e424081c0c0e00350302d00304541c0c00f0750442c4d8980e04000c0c85124500c01e0502220300030242100c0c8107 = true := by decide +kernel

theorem cover : BRFrame.Cov 684892086 685071942 := by
  have h0 := BRFrame.cov_init 684892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 684892086 ≤ n) (h2 : n < 685071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
