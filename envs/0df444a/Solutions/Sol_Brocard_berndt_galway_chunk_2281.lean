-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2281
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:13:59.766242+00:00
-- url     : https://prove2.me/submissions/81097ae8-ae70-47ed-9814-b2e3dd1d8702

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 410071942 ≤ n < 410251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 410073192 1250 410071942 410071973
    0x61a1f0e010c1b0f09051303030f02121801060f0e06130902060703080f010504090305090906011407050f06060612040f11030d02151b0301062d030903020c0402040f03 73
    0x300c0540c2081c0030a00c0c000d00d0060f40d1901d1a0494089820311340401c016410660003600d545141004210100c401034056003411030b803625000c1000880008400082e010b4040141010010141800b090a0328010308031084070403d0001d001e030982d01c0c1240c80740240e080c403070f0740d084100d60f00003d500b615242481c80d10b442c05048000409884540204944d0740240b03204034080b890290a000070b02281d400207a00500d8102d070240182c0a150380c0c0282680035640740180182003032400705525a0007040d40140840f1091240c0384c541e030300b504155944e0008a2410226400b414010614900304141140c841c4451171403680129151607407040d0008448000540e00191f2541e031582c4039540c18810340f61244c61036801402e4201c22540403012001000c0c1c58451204c0d980c0308080e00a0003984c080d2130440d0194141100000c1310f019131000107140c0030484049201140b66a20360301901940101000d5009508548061810600740012072055000b000d1203101c11210810000b00041c130504001c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 410074442 1250 410073192 410073197
    0x1e12260403060e0606090105100e09091011070b010504051003080a0e040c02010c0206090316031103040816060206070e1e010c06090606060816080f0702010209030703061a1f0e01 78
    0x405650791609011103010f840905074a03000007051100038501200304501410742107410300c0c1c024100d90701c0944209800050f8901400100001030180c1006014141404407010024032a4880356400b5050a520048045481820400021542c3e00706813003501d10074030103801d5080c240c1d13003180c445540f00d81000040d82d080005a610100f20340d22103024201d10340c00c0e00e400102d194004083c0c00b03030405400034021403290b4400e1084200b29030a4800300078045805d400c0030b218002c03140c2000c03400c40c40341c1c1d00401c1661080100000b041e4004007500c0c0c04a074204d034241c1d40365407114074046850b505050300742c41d4407682c141c0100c400e0000503070b0000210320050500c42841c0d07070680e076100161008144180e850642e20201000f02c0c41e00000d03031641c09440b100100103018140366024001d4503001e4003550006a0040005811034001d5044802c003036001030485101c55a039180480241500e41044105450b6030304c0d1841080c101080b281c1d100c4100c1d10f803034102c0b80c150304001702c680c400b82c81032300f604 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 410075692 1250 410074442 410074447
    0x1d0a05280b0405040608032a33060906100f020102091e03010c0f020607080c040302031005072304231f1704110d0201050d061e1226 58
    0x224801040400c0010304a03500101d4070b6625210400c42110a01d50080d04d403a0400c010382e140074400c0e04010000c050b01000f04140e840c24980c01c0616090b02000030004468052070b00302d11a90100d8050039603840c1d0707920000000c0c2d5491b0305104848506032003103500002d5004050181c5405046000d1040f6042d01c00141840581c2c1c0c000b50310103200d5151001010100ce02c200e000d8103081c01540c038941c82509002c00e00001d4800c0095480c64001e0000d0108506100070445c1035018104440c01541c0080c129039200740743e00782c071200a00c010340e5a0804a00c0075400190a1200100e01d00e040008402c03031181003500e4031503a1150f000c0c040d0250340c4003420010f8002060ba5441c0c1c1c2c40000e400c0311f850071a20703c1405400203054170050203c9024640031480410000031007400060850560595844000030035501c01030f24a4058500c2c64060503081c91404130795080e803120f50708041c481c1907881110b60380d41e40c002002095580a8054203460704980917208409800c8806865100610034051 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 410076942 1250 410075692 410075749
    0x60c06050411060d060e0109050f04081309050f09010e0609030417070b070336090207030e1c0b0615090105031008010603030302071a16030c09030b040c05011d0a05 72
    0xf11141d00040c0c1401140b035480001b8030540c0014139146004d40080320f01001603051458192a40c40d80040c00140140d0000415070780b8540c0907407809004200c031000c14030060902c4010700104034000c49004d80c456181200d4014101c600103a40d5000b0203819020358030300760500c3e84c000d0307003100390031401e0580307103c1c0c10000a00000c000f0000e00005001c1d40d0707002081818010404030010003110019a07110102030003001c2c7c0b84a0318005005c58001d1350300141d84214070310301915020224110190301c0070030883c201c966211a00094010640308400ca00c0103540d5050811128036030394258000c020400744461403071540203000843e0080e10014034200125558401c0da825901190411400a50003251000401259125203ea84116600503900515040c0c2c090101203001010300000c05843c1e4000140d018040d01c8200040c50708042d807070949242c0307401e1002400710244103d500140c0040704039901c401d41c0d01355414020f48002c200c08001c2c0e00c0c01080160b10180003141100120350f160300e14 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 410078192 1250 410076942 410076949
    0x1210061e03090519030f030c2a06060b0a0e04020319090510110a0e0409021e0402130f140607030c15110a020606040b010908030306040e01020906030c0d060906060c06050411 76
    0x581030001301004529100056140040003100480752100505040412050080d900701d14519106280c4801585020442c0602e0071030820001401818541c079201000c101d00b071490005200d4080301d916840061401c1c00c06101c200e00c0100c0300c17407040c083e44a948440d0307083c0da50011501c1500070700450781c1e50100c200c4200c04456a0a0b040d5201c0200040e02d80080e5410440d4043d40d1030040f203003081003100079000710b4148001100b03400c11072101034418150329550f644c103480385440346102001d007403610380f0524661000d42e801480400203003005c402086180400450303218a906a461509007502a40e0380600c3c954403001070b20040c0d07190103031001f490128401410820b41c06130300900c040e08102041c0001c8031200502c15041080ca12424082d901d00001100d400c206d00b990005900140312080b18024014008074030340c815000010700548804420103000b601019440401c00140d0341c0b01d005c0115040b40c4034030404184848406c20101e890f41e840140c0c0035000e209070701c0050941d034002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 410079442 1250 410078192 410078203
    0xf051915050901020c06032424040305060c070218220b04021206010807052b0b31020d1103070b0a17010f0b0c010603050307081210061e030905 63
    0x2030340c00140d00850250300030343e41000307808030413001a21b2103451400c1c800000071a40101380c8003202582c12138504500c6545403094110002d007540c80e014010103224060031000d40c1e0007403105450ba845000081541c0c4c44d03826046510460f80240f10700403003001c804200103003540080202ca01c0c840707002031210f052010007003106030680c032840111106160510401000313002c80c805003001c95200d540184942c1d54000340440556004440311244402c00c54081101504190501c001c140301d4a102d440800500807211400790003d05807411006002000e00d546500920307031025100013403521000c02600340340703403c0145c06000700300000100742c0f40c030003003031400f21583c4c42011441400100e40c6440303988910459640500c072202c041242d450203103000c2c0000c909028480403841c001541d046100c100354020310082d03900005507034481007141000c01c40c030b4112040b03024000d42d0440c00180400c840c4000d11040d1001902c4840722120030065916105040a65071b0b000c0c143e5171003004c400b02c0c804110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 410080692 1250 410079442 410079479
    0xb0303040f061209240515010504060e0a0810050601120c08040b0a02070b040c2102180c0d0509010c0914030a08090f060c0102070c05090f04080307140a0e09060a0f0519 74
    0x1c0b0000355605c1030348090071240c0003401c42c2d0300c05101c1c9420041503a03000085a04a0f05140303407d00c1d50800b6134000502e541c00c0c692207401e0354441c14241c0c3c88020b00395000f2500c00d640036222694a1424954540c0644d900741c2c1c1c80740002440c620000c0c5c000340c0302c404100c2e0801c0c0e101800600b025071581c1e82c43c102200c141d4090b110680b40c0c01081106185101c8800c04410384012802403981d016404034850480316044c1164401c10200003450790391400050300e20044101c42c0500c46424503014650080045054020019071803150109085010012400c08428050020182602543c5442001d50099242c00e91701c003a0041030161aa900c1d10050001d80502e07034001a50384045260200203101107030301150241508200304038910f038003840b44c0c5a100e50400e944580e03079626540c00300e03030380d8403070802d9001100c6012613a02e04442d4082108031283c14151401103041d1980010444610004e01c140c550215000c2024406414600c85540c120f9203904c00d4091416196006c0000101c0700c40b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 410081942 1250 410080692 410080733
    0x121203270d030e0c010c0203070302060f07051c0f03021c050a0f021c0b0d210302070b040819030e0c041d03030c130e19090f0b100305010b0303040f061209 68
    0x5240c194510f000e02c00001382013402d00303100c0c0f400407160340030a844146520010f44214008a04042d0218485c0c04440c49180e0000543e100110720390741c024017184860f000340001400108000003c280a4400c48540007400308028056030180f1581300c3c00341500504969446850b240441c840001c00d002a0294100106000303112600882741d0034212002c600801d8400c501c034803008404141049000c2004424801102034152030440043d00070b81724400006004034244000c0100313104407603015006406802a00700000f1030010001c6007520081007075410980c0013440c85041614055100459040c85002400c1c07a007002040b60908580048aa120100800056007020103c07061140d80180003030040926041c10032801403c15540b200c0910403409640309000c03c1405186500d030010203a10011b20001440c0a10b900040d41985100449056090100c0c80540d454084291429506502c055409072071801204880001d04036008016541d554803050010400c1d0722045080d909100e0b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 410083192 1250 410081942 410081951
    0x1120b0a180608010e032d090a120201031d071403070e0f0714070510020f0d06030503090102100915021b01020403050129150309030408060f06121203270d03 69
    0x10341c060075034106500d0101c181c2c00402c400d00b18007a0107c807036000340c0a901c04c9401d40041003203280409116207001d155218800d02c07400158011403108070602d140c400c0c0d90606c60084140c8c00f071a15804060041e080e030b03070070140051055145c00000c0326040300008007104c4501f0746d030b000b0b0121080000c1d035140901a0b598003c02c01704680180340d185c4501943c8090a00c0c019aa0711f0303441e10b8483c5100340c1c0d02541e070006100c910120020b000d90b410703000352403400c0101c296640380403a580d500481c002c0e40136010305040c2c1c480f00c40301c1c0d104070071190b03070020403c640d1304020406c01030003540300c0c50f221748805003104480c2081903005d101804c09548640c00004148417002c048050400b8000000140c111490404c030170103848901d0403071240070700001c00603100c0d212100300505500454000050700e00c100400c108031031200e6107405000741019200025042c481c0e00019464814181034201c00090400200d00440701d01b54148030f104644139010b10ba40555403c180741480035201e02500083c2d10b5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 410084442 1250 410083192 410083199
    0x50a090f05210c0601050402090604270e24040602071202101407020a02040f0b030d18090605010f080417030403020a05070b0a12050402060714030408070506030601120b0a1806 77
    0x1c00314014601e8070b0600440382408a51075100ea940c400502402d4091600403400700020746039142035902030000c0c000c030342c0440d01404c0d40d103802d6112f24a038411075550600c95044024a00401c00382e015040500348220710208401a01c070b01d80001801c00c0311056420854070b808902c41203e81c4802c40d4555010344003103480c03086424195110505609001d0050f841403009003a000034070700300402d078141d40c007061016030501c0001c010003046074520b07014084c00d10040d003030340da1100d1809400c000600c0200c120301e4070351000c2403c441c1140036040c0850900419402000c1c0105800e0342d100344196101e80343c0000d0301e10008190b400c00d80d411405640b1404180003004402d01c140000b502180e81c1d81801c000c1041710040a0001d142280250265a030b80482c082d5180d0008807403015410604015516400c00b01c803641d04d80c8503100e4220640210342021610b0700d4000100c1c3d00a010503900c0b01e400050704445a0010803512580c258040401940042c4441000d41c0060a0031031a110001c0c2c04c42c41c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 410085692 1250 410084442 410084473
    0x2060c0f06070f09030f020114220f0506090d11150306030f0a080d09060e0d0207050315010e1524130e010e0103111203121506090d0303050a090f05 65
    0x401904100030b000d001d103d516081540000e140701181d81180346414925400c0c0016141007112003d15104031000160018042c881c00c440c9110340800c0c4210000300b01d07514903184a0044103401413680c0f0ac5810030000b10249000c0c40400005401462020f400307104500010714031000320601554000030102c108a0249018025900c3c0c445100d0041c003080605c696801c0d0441c851240c0280c4041e503503422810900c00341d507001d421580aa0811902c071005a203001a40c0d8040b184281440380c82080d689803d600941240e8074101c4020031500034480e2103050311805d00d02a000409070b004000007203181415908402c0881c00f03000034200341540e0300d41900c1c01a94060b410382044142c00c540000400400c081d42c09060304603504004208001c140e40d5000440c4e1104440b81001d803803002240c4070040400310788105005a0720070005d00e140301503400511010307008110078a903210091381200c0000c0b03402608000d5000e520480b000807005d010f40da4801201102030b40031756a5500080d2011b0780082e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 410086942 1250 410085692 410085703
    0x606131409010b07150e031b0a0c060f05040911160f060f14040b0405071d0a0f09030e040c02010f110c06070201050c0307030b030a060e010e0606040218010503100302060c0f 76
    0x1010f811814035244041d251403843c2099881c2001045990300c102140c803001c28416a06000711400d409404140c5054089943c1c2600d05800d644d8079541d581e0006107103004002201e20800f164803482d060074a4400c042c001808440b41140100c00704012143c01c2211080318404a203208100d039451101050a1503c1155140c1c003800581c035180441103400e4002a503082d55000e0762069005140c0e03500c515089003004001e5001c2c000141408c00d80b018031082a07c5400d00c9081605003c020f001140e401000c01e841080ca005000701e000b4482a44032410550400d212140a60001241c2410305845841c00c60b034049841e001200008034890034a200240a2150001c006200038030103400d0120450300c0c0b03480040c086d9024541c4da00d031150002c1d1420302c502c0f140c080c0c01001c100140302010810901a00c0099031480b10342c003c0c0e00008816240030b03c2940d13603000740e032440031490342460401515958405040f0415400c0c883c0301c008010313901c50f0000c00100c0120000781103200200f950f41807420303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 410088192 1250 410086942 410086949
    0x2030a030b010e010e21010903050a020c09010e180114090a0302060606040f170a0b0712050612070b0a021606050a020d0c0f110415140f0603100905060613140901 71
    0x40440d003e038070140d07a070105000300314a800f1100c1340000f144140701040e0484071507100d41e070395500f450640310a040c4c0290150241706859002ea40300026140208400d50009010310000141c426020a500c00c10060356840f0b09005040002240b0a44404000961108540d4a031060740710000307500405134107200b01074000000f40c9400d41001c3c241040601410001e00800c440c0c0555010b0034000244208801094240c01c411205c032142001a4010300c40100360300c80c1c00b101c50812020485072706141030b075441d007040c94101500f0b03424102114801e81d40e01c502c0513582144608140807500916541036400244a541c4a09554110500003e410b28412000d40c0c8148200c100360400801c502000142c119640b050000a2059081d0006802448054442105202030b02da0125926032040c0c1d1070007804008440c2c0d645a0881102001010b2000300c40300c02c1c031001d80190401001103103400007504050f0042c0024289440c0c00040c00e01c0400c103610041990038481c80500450408103a0309024 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 410089442 1250 410088192 410088197
    0xa06030203010e130507180f1406090f15030712110913081e0309070504240e070c08030c03150a05010e0f060f0403150c0c0c0b07020d0b0702030a030b01 67
    0x45616080403141d00c0c0a00134401c0c1840012046000c04101c803e0100780b000d0807010001c81c03820365220300040001c3c005401c07042541c0745414000340580c0303030304034000384104001040d05200c1d596002641c01a1980501440482c1e0043d0104003116079040c030100002d0150103110542000e4103043c5001014030803000c0d180641604414410741e454040803902030700341c000e50b0050b600c100b201102070110344201410162140b001c0184001c0c444041031120440e00101d030184000100c00c0036014403030308042c208100300103081000304080c000e00d082c610f0b40501c3c01e040c0b03a504e5850a4880840c241e000704d42d03100341d15034000b04201c0b00b60450b00d0050416070068400748141340c145800a040080031001c164483d02409050f18a0342d900c21041365482800c258400b0f40340e0f9a40e2510726900d0b2003144200142501b054010a5580d1080c107101e260340340c010b000444424a030008041e0b081d40180b0060340c200400020305000b00d420340301039500515803a4029071b55182c80ea003004003282d80c2c05940504 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 410090692 1250 410089442 410089447
    0x6062310080708010326180a08060709140604080f03030103170a1d120d0302090102010b040902060405150d140f09070f05040b180108010207140c060301090c17150a060302 75
    0x38a03602034407090660307502a05c60000440c40141c120400c0d002000906e0007054000b590300001d40381d0100e030211a044c01d4951251007500c6498042e2a481c2c11a0260000741220408010004200540024024003c6e0207285080d4841c00f05a0a14104200650315980000010010480b04200c040f03080b41400c00507e0610054140003468429240010341000c060384e2440340a643e50f23180800c07941d0b04071208681d80340320403000241c045d40000140d03a015510703001425429040038041c3c2c3c0b0843c1c0c1d004205a151034102010006000008054240b071000c0a02c510280740710513104824040d0318100410300e0700d05d44160b00f4a2124801000d000c1242c1186504001c03680351511001c0540d0303c100c0b40410390700035010109620601440c000301c1399200303900000540901c194014a1014045c8851441800c00780310401d503070703001041d0b4294001004000400404440f68420702443c1d400b481c019511480c000090f0001d00c20603034a000c424141c1a081e0704003440c054490704002c291a003011f60 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 410091942 1250 410090692 410090701
    0x2120d0206060d02120625030902030309090705160c0e01060c0b040b1801020403060c081f03080306040209030307030801210203120a0504180e070905160c0606231008 73
    0xd4540c1c90251120f4024002c0305544021540c5134401c01904482c880201c0300c203454108080d01079181c081041f0f521492101c03001540c40e500c28041e002c0302e26000f500039490959010700f80481d00303000038019810400180800c50020820142a00e0424010f01c2468035060a11401154140f070681c094000c2c003508402e400c0018021046050340950883d861908566850485841d005d8001d000c1c401c41c1d500c002000b0040148650000086031016641e030700c940d90358a40706181800541040e02c400d01c95255040000406080c000c40e40044084c6c0050b05150403000468550b0704110740c00c034041200080140100280304100d001c0058041c00c0c0f14aa441d12600440d03212075035103104402c01c21700043c0f220303111406041101d009103c00c400070034010007401c000380010440c028121483d4000c94038005440310341400f440b0f0084800901118280c0c070303050010784a1355107070034037160038070386a920000b5608022250b0400e030041207085540d494205400b0000703400e032000000000e101e403809c04d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 410093192 1250 410091942 410091947
    0x9070f0914013206091201020c01051005090a0c0302130303020607142b0b09010e1503010c0905040b010309080a020a030e040c0503130602071b290d0c0908060a060302120d 75
    0x8003d594440d0b40f201e0707030030340b0a6004219144110340c011500304040b0000807107401d00541c010048140200700070801038403001c2a54a81b2000707841070380d5116080c0c0740441c4100700c281d440640014914140140340401210a086001195610503809a0460000c00001541200c0b009014040460b0348900d403120350f8090b4003218107466094189034411400304a00b070307150740e4000b40b4101c0000f4681c090a40c2d480c0003191406c82e0440b007006488582c9003102425007414042d200b040c8030540c94944007a8104020f01000f051810700300c40c1055192820b003804284081c00401001240c0c0d03024103000003980c02d0181000f1554800e60b40501d241610f058140b65100042c5d0fa0030100e1118031042c0c80840341400d201a006800700076020b812008811811846001003510440b02119154414810b0703840c003001c9460094003464164400c20061480c00c11607a034840042d0f01c105c1c0c2803a0003007584421704a450080c0072505441003d0343c0b00300a01c25840d00c44a0001c0c0c2c03540b2140104070b02c01c030f840e600 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 410094442 1250 410093192 410093249
    0xc050304060e04061205070312111c0203070204090602030702070b12010e040318090204140303030f04022206090903180f060806040207060212060915061209070f091401 74
    0x48404101407031504401960b00c50300454000c05d020242412050b5060030401d48170101803000f01c1e500c0001c0d03100010418002c2004400d9900480e01620084412002d41c1c983d50894204000031400100400d40c0141e54601c07900034079601a0400684034075101313802a00d000b450790869624040c050000d855203d41112106040d9000c0607001c0a03c1e46940c5000d40f0030000001074a55248504007000c0740c001c185034003500c11680c50032081030740343d07000a060507101e1105480100c003e0904900080240c10100c1c901116503800d4000c010441c2c1845000a04075003894021a00143d1954414000e00d540001101d0300441c02e1001c042000e45444503012401c1458484c40003402014030000d030703081d59140d0503141d28981000e41555500b00c55207003075104100c2180c40714802d100407808145055010103e0014112700a0b209a160100340c80c42c000d2403d00040010025100e02000400e1f410f0402c1c0b1800003e00c02079601080400c00d9140000c40305405070020541c0c0b040b007113400c03c0c00e030032403006 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 410095692 1250 410094442 410094449
    0xd0203100b01140c0d080c040803181216080d030203090d140d050a1e06051804020303160c030b01241d0a0f030b0a020a020a03080a0b1309050d0c050304 67
    0x400161001d00c01005840d8803d038941011512600400c41c2e050b90240030038070124240b00c0e41d030b03840c61940c2c2e002c0313005404d130066000325003c80d8400e20241c201100522075034140c50038000c00000c61081081025454000c0c0e1422065464401800810451408120b6042d0015660805500394640346c1b14841d5141d00c4001c00c5010000544800c007401c020100c1142d00c0c02030281814400392502e107401c20050070f00350441100c803801502c480d980200191181905941e401010302d07080c00c0b01002802484007020f03100b80e0f814002041b1000403200041010303401a44600840c2c0d070301c01d1450400460540c070590015690002d411022030044455602c06040d03141d241c1800500c0807180d80c046101010400a2035802c40c0030101d02060b1b42860466107001c4a115110b140a40d40d10700c1c0440081c2d0041102c00c0f00580d01007485031000074010418298040700d1100e001805204000004030852121442100095511682141481000d1103120402c05075030070076021181c515500c95550384518403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 410096942 1250 410095692 410095723
    0x1e09041b03081b0d110d2001020d0e0d030615050a0309061508011107050604110d0804150818060105100e0a180606094b05030601050d0203 61
    0x24441440d512480c20108003a5801054503502c0b0240d036100c030486481d0304426030b54184120020559190704c0780030241001d1244c0405005a20380c40003081c2c40d5070204642c800c040076030031410400300b14002d2006d031581004080d00131504009504003d4108006480e10804040c10054140034a12040d002030a000585140160f91a281c0715422001001b0a8000500980c10203104501c070503402c400c49400c0d1405a8020405604030402c0803006103c0d142000348140c02840000c2d011401c0b21008500b4840d0150050b07075041403a6403440429402900601a040320148232202007682c03251200b030b4810440020805060311000400703556120500c1402d120b502105540da01e804d104030044e0702c40f40005005240c81c1511204002c0031003002e0072865040902c0e00d035000030414415111b05c0d0445032548162840d81e175480c00c200c410a24600781a01d07081c80402c4500c00c4055108000e07030b888402d0200421820760428003010309040e0103a0010344120122002d900150f83e000c40c8070f403185421407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 410098192 1250 410096942 410096963
    0x100903081e0114061207080601020f0106030317180f2401030201020a02130b0a06050403140105010e043e13051e0414070e0906060411070201030b0d0c0f03021e0904 72
    0x40c0004d041885036280780c200503182c1600b44001907400611040c0116002d0302620241080e2074082422190300d0300c40030300040c00b02d02604d240c40f0100d03d0400d4119007105c444820039901480b42d1450591800c0d504501903110030304440c420854103c480d140d0300e0030b40300d4600300d5501d90740000750703141c80c44e00c03001c1d10510343c03a581c00c03044a01961002e06504405030031031040f940d42e140040c10b103400c0b610081c2c03408003a00325911b030541e60620500c0d050700d0351940c007a070701500c8980b00c0000c12290b00701c618014014282c940e281840802e440d005140220720b80300c2d40300e94014020f216100b008016448605410300092000310805101380500304036810100c10800d540b58106080b030055014010b00c25409080c1e00480c01890300d4050300d20408160080320345031780f244400d103c11580e0b0700e540101d05040c140002030040d88a40c201e01080c4900030259001c5901715100c01004203040e42c00100c601e01070a20400840c01d0510190a105003c11395403c1481c41c0c41c4040750003076400400c0182002c107031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 410099442 1250 410098192 410098229
    0xa0308040b0415020c06370f030b06040305060c031b0f0403061410061b0b130b01080a02060a030905031c021b1f150b0c070e39040503100903081e01 65
    0x8034640d40703030034110005030301080c0502d40030152040a0448d40c2e01c0000781400945092401c0240880303049035440740c000d007296039800103003074001c1c2c002a04441c0002518500365030301d050090f0180c5402107150750010340d500d146240c1071084500c2d60a01c010061000800c203c10383c1c0341c101c020070458205080000c0391560030070102007191003840c0002c100030204020300c0590f050003031100e65520f125100120700340c5d80b2011865600d8400342c000070f6101c3c0c804c00102d801c4074800e070040308005104030300301e07814842c1c1e6003281040034a40c40300c454040c0b1b5011801401103400024441413400340100904414004075507501c03e02000c0d4200110060f440300d04810303d4245004081c4010188050070039101e028411030301ea11040984101e02110101e800030900d1440088290515804442155441c80c5407003e9480070304064000c40240c41d0070b00340300000f402c1e241030143c00342d41490010002080e10303e81c40c02920300c40010700f05805000c500c440304c200c841d1483c2801410759280b84c1050717450740071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 410100692 1250 410099442 410099497
    0x60606030a11030f04060501080f0703082a0a1b080703020d0201020703082706120a150b1b0709020a021b1c05060703050a11090f0a0308040b0415020c06 67
    0x40b00c010640c1258008104404469001c207401c0c0a01d11651003480710340d0307959001aa446410f5040382519400030f40d0200002001000203155204d4141000700301740c00c10700c1c03520300c03045c03c1c142d822902da402c42c0005000b04194114041c42e070555111032420b000742041d410954400e520b00009014509254130581960f008018440045030301181003030382da60b1680300c0c10001c003d03000b560358200302850140704214505403013070f551500100350041e0901d664210b54440508a10300611401040088001c200e00d14008010a008c1c11a002000382e20b03040300843c640340400300e600042c000391044c000582029400701d10007500c440ca5849249981c62039200185000140d0105184180103500000c820801c01040c154418071403038500304a155203403203018007543c07035200100c50480e008003c6242d5030308d480180c6012403180581840d86181d100c0e510b070940b640c41a00003036800346011808000e494003041202401114030700c0500b801550f01030104069001c1d031019031842520030051040550b4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 410101942 1250 410100692 410100701
    0x301060f050d0e0f1b030d05030a020315060f0a1803121101020903100b010e19050607080f2a03090604030b07050913020408012003060105070f060903020607110609060606030a 77
    0x4103503806884e1030f01e8440d0200d0381c1c0c0d0150b0604510b54210f00385c550f21080e1401240c4005520030310f4841502d590b80708081c00009504c01054000010411441e03000e03d41c96403000f030b14801042c0480c07941c2e07844003070a0150811091a02c00c41030b03200721220920010711026106101c0401d07a00b0520464212142041c0c0a40603040c5041e41510407070070221718400241e040000e0f40300007070700d0718000030520105219403000c2103044403411007200034041010381004001081032034007900c24075080007104081c180c072983c040d02e185032805c481024030105901c031220042d082846080002c5280c0304004001c9442c0b40528400685601031160014000e640580c048818500004100d045034050705440040250400e000700307182d83d0b29240e0484c081800307108100f007074540e1506030303541190741d502e0044616a11210f0211000080d42258000049030f80c01a1319216100390043d10083c40c214030010081540c9d0051030b8200e038420014840e0403c2c010030b0b156040881561556526039a001d0850040c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 410103192 1250 410101942 410101961
    0x30c04091e0803010501030c0807140c0a0b011e08070e070f030e150f13030504050f04021c061a070201050703030b01141b0106050a0b030a0207020406090e030910050301060f050d 78
    0x42404a104900b0003040100540c140e9000746c074100145001241c08446085007111000042003442884582103407400019201401c440300c2101c86240841e503400c0c0c03090340203a22518814940c44081145c8000700c60a05000e0040c0900404002c3d1405440c01359042d40900f0600074005044010070300c291080d08004540c032851001c950514494044090410f80c08503000050102003e021440c1070307001d40e255020032038143e500c407420142440c3c104803140c001c1101071781d40070b9400c020000440100c1d400c1440c150304100000191149041407000344e524100141200c0b44804100e1080180c0e0000c0a42c4d0b071850301440d002480c0d40340800140c0e00781102c1000ba08581c40d011603403405500c1b5094044007038540d00d500a202266650013405170042e6039000700c0250383c5090000030140c1145902800c1c3d2240002c00108a00d0b544603e040c0c22209884050720941d0000034100d0600d080814900800041c039180c030f81e1840d890644014200c405049000c410420b000404000d1743c0d516401490b0b40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 410104442 1250 410103192 410103233
    0x306020918010315050601030509030f1c0501030804080f03040315020313080c010c020c0f01091e030602070602210103080306120f01051f0b070302060609190603032c030c0409 77
    0xa0b5840742404c200c00b1600550105009082200042855120340039441c0241803035002035081603076041003507216401c0b0010b442d000d400d01b101d072030b0998040c0340034680c001d40c001d11080741c1d00e50070009054240782c040c03640d9400c241e0041004000150165410603541d074041d03580181c50742c071100c04d05020000160005800c042c80411001410300040d8441d4403d11100c0d000c6400800d611002d2121510b0b0950889001c1441c81c41704200801c102c00902035802c9008001010140d142c0da10a8100d810011b0190351660b400700d42c5211030110010200b10b8a5088084c0d424551b02d1a95942c2085c4402409180035018088801500a074100801c40f001306404000380450304d0405d035500c01c0c000c0501c05000065018030070026000d0210000c41d054607070548c0c040c20f078682e40c01c1d040c8140000064008002e190506001a0200c1ca0354491031000e58480d82e544444004450128000c154010301c04480043d070028091811742e40002d0b021064a4082e200030030068401d04040316010b40c994005045e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 410105692 1250 410104442 410104489
    0x5010501060e0a060806100c050a0f03020a0b06030c030d03020d0204030b0a09021011151e090d0f0f020a1509080304060c0212030f1302040219080604060e070903060209 74
    0x50301604440b4500c0c090b4825079802e400240c0d603100031660071381c042e2641e94002c10628050b04250f44103204410010340564112810806680e40d1420b1042c140041500160001c100a900304150030740302c5900541c0032001000c8032805000080d840e507110140c1d450a140d40010108030b6440d1580581e00159000305010103030386000c08080300506080e03c000c80c4111240c0d0000c25245015207183e08182460310000c102c032300e61212500b01d4400c00901001e4800002114820501081181d220700c10003402001d48100703035042c000908600d8071030240300d040c00b01207001c0c07800c00c550010301c0622003a000303584003140c404100210801404540c1c80503100541c000308100030301149030440000001c02e9400c07100b00c85040d00480320640400e458040301880b0f40d401150809000c401529a41c0e400140010311b40020999070744d20820003441800046035401d010000585024451180142403900c44030f906407504082c010803950081c08020000d41c0d020404401b90303110941c1c0f04038160540d105a64 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 410106942 1250 410105692 410105699
    0x510121404021c15060b1803030412120e040e0f0d0e060d020f0f0f03010f060e10030518160e0109020f03061011011107110a05090a0911032b0908030901140705010501 73
    0x54803a80000c030b20007011218401c2ea03a01c123003030000444003266004006460001207641c2c61440d03403e0043c0c208005c10008003a111010760380c0703104070040540444c004040d080e9485d08082d0402840c86d039031400f03003c08140c401c84c05031284000c86030390100b039030801641c50396520b0b008038803401410a04070310b045000c1303002d00200000310019416075405c500004030403941e80c541203c11114040141d500458100070950103180a604015000641c070007200728004510300a082c501801c0c07614000c100c944294080011040d4807509501421030590309526015075003181001a200150400c0d008400301c01e50b007540d8500c210b00240d0300c0c00a40700240003215070f64901840c0c9402852041e00c2c5026150031203c1e02e454000d0001e022070300081c224445595440c46900000c2c0088ae406503080c3d5110900362902d40d400748030500d103400c62010074801c15101954411449161071000a051055459091281c40000000d46044035002d2030032003495000825481800e0081714030080056003004c0021 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 410108192 1250 410106942 410106959
    0x50c1e0106030c230402093c0405060306040b091002030c1c0207020904060c0306030f0c060f09080c0d02010909020d05090d030b0d08030c040510121404021c1506 71
    0x100d088030300a503240104141c0704c3d1003181000d42905441903010095018200b15414203802030240e0031402091426846028649003400c1c0000100700c41c0c41e469000d120010684000c1a00d0701f04c014241c4080001d441c0070404641d8032003025201800c5480d0460005030844010461300d80c6180480c030b015503c1c9e0403c941e101400342c02404030b10811072101004000403e9451003a03c0b1040d80060040e02d0720b4a03a80c90347c00040680494030310405803954800302c04074103080c1d58031052611404160403c41c4c5054401407100300c02c1e000d01c0303040014003842080b20010000d00c012107050300303e03a07441e40e03460b151005807000280e40e03010000c02c90020884080d200000e0780b0251142d0310781c8042d10034200204a0480454008292281e801820070a20300c0216040c003024584c08111040d846213426120350014030310001000c0c0d03a90020f0216003440c00c408001d80150707000f001c50804025618100341d80000d0b05140c0c10040044104140c1600c4024400c000034162106064004100005038803501c80 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 410109442 1250 410108192 410108201
    0x90b09010c15380f03250f0803070c0608010f0306020a0c0210021b030d022e060e0415050c04030b0702011b0c02041109010f050a03090204050a0f0506030616050c1e01 73
    0x3c484101140300b04510082c184161000600c86005000d01030300c03400c0c01c001503443c032030101030040c0405100c040072807031f0808844c4440140005100464403104207141000c071141081d0040410000700400401c0f0341000095590141d075401f010144c0c40e840c032548100c0c0c40340113200d0080e5020352024401c40d11070781c02045003020001404004c85a5810030028156200110340072600107074065650090425544291100b082c0610070303500070352803194604107040d1200b03904104102c2c2c541000380402c010005c0d500d04401009a441805a80342440c5501d4290003540300282018130300380005042e00c0d100303520180e00740e4500340c001c2400490a22000380301a0004400701c0c00f030b03403810021000e410840c00070340e110340c84140c2d9041d28a05800c4000c486035000301c0c8910040c15280c05100c4016135550044611642980c07100194400b1104a06419560090102e42c06070f004041401b0800ca1038400300b0191120a040c40c99450b40f100d9a224030740400a401301c0c00c0c1c106014246e501c0300324103400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 410110692 1250 410109442 410109521
    0x251b0b040806130209010524030c1306020109031d01111b031006080c060705030c0d0804120804020f0f12032a1207020409060b041b090b09010c15 64
    0x440b8a2961180b0078828586015180650f1085004004000c0351400c2074030001d50811182658441d03120070b80c4045060f0b081034034005601c00300803e8150303140ea801c0c0da00300010f20052000b03100d04011750b2800341204034508003141c100c040712071405c40130f039010312140d9040814100c101c64440036070a400c0d040c03500601d219a482400740d0b02183d20000d4840c01010191030050014003517000d079040c00c1102d107501210b8200c2d46e40c04240400c15140b5828400b20050081c2911402100e1500d841c00c5d007002e50300142d000d002e10004030f05000160b2100e014081140000382c5079400180343c0400010b105102c13510740907285100002d0746c0c64401c0e1041c04c8070505910300e01580d040c552010f00c01300d81c480c0004c02860305180c1c8148650b001625158104110707040c00b82d0000240c0c1c3e1080008942541ea96400380803040d1812855901c500f0b40c4a040302d40208a41c2040c070341090a40700c0020044860718901800d080003003070900d801c02100da44411031640719980503032503c1216a180022480b500f12 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 410111942 1250 410110692 410110709
    0xc07060e0a051305060f10090602070f182a050706180f150906090803060102070b0a09180e0d390f05150108031c02251b0b04 55
    0x39060305050441e0705005594005248401800020700954000c3c80020281548001e100c0134950701030700c030f000e220060006180d490007007043c1012806031030026180d01c0740403880440b0b03004105555010041c44c43c070310340e4090041000b403210140b61421591600e0807007442c0c0801940300c120300b81c00030000c2560920801080c07203113900400701c001c41010b07121009810740c03c0484006000030001100109421a40400098502060703240d000031a4a00c41003190a0580002809059a01000300d0401802c14a2590f490400a6880100b00344c45030702c64034043c0c1e4440f114100b82064940c02c8103214442c0d2404503070308441c0440b0020b2030701c0e01602d4600e400c49008011002882d00415500c0182070346101c4886401e80e49036544900b030103400ba0705460701c0c000c141001075021002c80380f0f40e008054000040d40ca6000600136a616410104115416242304101d6900c5e079a21000000c10f12a869080604901245040c080d501ea0102e4800780c08200454402103400100040503101ba181c451 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 410113192 1250 410111942 410111957
    0x9020c12040302030601030f060e01150801050a200c0a061107150c200309100305160806030703061e2a0309031215090905010c0806091612110c0706 65
    0x30303a40340ca460301c214000690190000401440403e01c0f9000391104944104400681a0a040102ca0031140e080036454403240b048102009204001d026440d040b6000c2041013150417a5442401000b0280300400e041b04000030808400d4241e00b1300101d400d940d0030900500c0751444100c0c00403070075400f9100c210b440d0741500200c660014240e10400c80500c0d0141c6959030400303d0803030000d0700c56a0080d0080e10b50703c42042818031903200d0f0b60a100b41d410007500c0114603030418081605152001122040c1049050000c00a0b555030028070481129000745000031400301700e025101755001009416a14030382040c4405203080781a11000d80841a0f8070044001d41224000407401d8841c1b5620180001e0b03e0204500000c00700d40d480075810440b294443c0741480d41c0c80c940d910540c1c481410584003030b5034440c2e8248500d500600c05c0d541c41802150030388003500d40b07064050240a041c04906003003007180388680b102d4034440d500400d119288030503a1038031550804441035075981e29024010014095 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 410114442 1250 410113192 410113213
    0x709090c060c030906200f16090209151803070e0a140f190b0a0902180301060803030a090f081603090b0301060509010806061b06070f020c09060d170409020c 69
    0x403802c05082c030b603150ba24055210700d07040301164580c844090000340c40703c114000a444000c01c0003804404107a18000c0c09607640180c4003a40200481d601ca0401c0b6801040990386a40d00c0c140900105980e1018031600d82e42d61322003400320715510603000c58161082240c0842c503051105c610701e1260794455814401803200705200c9202079003d0b18400f0003050342d40082410403601d0020081c500450b03500010b035200b40a80021060000c0e5408074002c0c50703001507007846414245011084800b0194000c0c0240ba203800380701e945d00e100090403107110907a1981c12104000311202e90144150300171100c540c6131042d144c002c4d580c400740c801044000c1103400500050100d48201034034100c800c251601403c0c05060740c010369800c603004080da079100d2410080c95480c3c104001d00c001c62645201c4c003c100c145070401010706145402e6206005541c01004208102c0e5640080b242d80000140d940c01c4809181c0d1403c500d43d4403107034800c40800100482c011880b00c20380e03401b03460a02c426404031440342c905c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 410115692 1250 410114442 410114447
    0x405210102120f0723091503101805010b0909090c04062402160501200d110f0a0c0311270603070b0415031d010f060e061801051c02030709090c06 64
    0x15103090400c600e44000f49846401000c0c1001e4611a14054652001c4851a610445c180da1044449d4540c50410102c140100b100c0c0304081c101c042041e00d41000f041d41000061040b90080400383c5101e25400d10000e41c640105000101c040c180180c0203102440c2c903a4034a0f0495460b594107002c10402d03170b80c0326107101803000030102906141c6003c0e03500d004d420a0011201d00d170404c8100030f0398141c441c9407214400404c000c29172020b460340c2d84001200c42101a91800d1002140602000e6880381241030089030401400404a82d4060031003410680071401050a1410f20001c8014003e8401c0d11a00389045010816104210440540b01100d444009551301405280a501146c010501d01449064081d6011000c0c480017880c02c81f20b054100528542514011002201074030f844d08410403c003810b43c417106400032022581710410044011120403001c40500c50948034510000500040d4141d031156015456009400d42c1d451644480c00700c00580609282111b6003130001200080b16403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 410116942 1250 410115692 410115707
    0x110406120903080705340b0c04080705010c020112020a0c0507051509060307031803020706080f060105070327030605040b090c0d0f020f040c0e010f0905060405210102120f07 76
    0xa52580301c01049455000c1d0171503407500080e9000c541e111151a40c001e0600440b00c1624400040072035602c02e624a034900720b0401c1d000902200c141ca5408e12080c0004800441c40e00189e40081c03802d80c461001a00040301c01600c040302d01071010b4400038484d22415409480039544500902c100c0b0345a0b81d45909000c61442d1f03daa01105901d0180641d00840c9000001103030051114074010a181340c00b040f881324540c540260483c050303446184100141900850842e60011910311220f40c0c600c1c000e400a0b080d03104883d8018100302500c094040c1208000c00710b802c420720f001900707071640394492800304020038090310151380a8203450002104510002001c002c1010040e15481503442980c0e2a00b800c8203201030105ea01006580190103261528460403261102960b46e5130403080c005000903290030010b01d2121f04126140d01e040c8017580b20141102c0c1120000c1e200708000000c690020b00c2e007505d1181140c480f030350000031080d150f0700315009214094a801c4c42424919203c0a4080c0c0b03014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 410118192 1250 410116942 410116961
    0x80105070e0109140607020d05060711010c08070504050d150f0606080901180206180d080a08070c05031c020f07051f09051203221b06050c1002160611040612 69
    0x40d00e160214440750030000d01500f4102d1019000230036400c510790f5003604100c411102a00062000002404525001d0103030462007081401d004072581401c060003015403099008143c081d044101c0d600040128100c1c0342c080d450103182e402c11480c85d461200744094081480351340e0016400202091500c1810720580d2154a0b4000c0400d05007840c83d400d200711600003001003e117601521401052548603000180ea02c2446402c4456031110b90141c00351054201601078410404082031480c0092000000c0310881501820108050707070510b64504041c3c4591103484e00303411000b107400e204209001500050341c0342c40711b516110000c3c01019000031683c105002602941c020703034010750118510802507400c400d00a4000d00c540c00e5400030400074041c00e031390455040010071154840981680604d501400080c43c240f4038006e000a152035440900b80c04040d03d1603400a02160014089601c289072203911200a00c550800c1d150b83c180c19400c03511650000c1120710030140d5014400c3d1140c0c1050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 410119442 1250 410118192 410118209
    0x1806060801080304140a0b0d02040e01080a2f0613030515130602030c040b18011b031d0307080706030e01051b030406110f0d0f0f0209181e01080105070e0109 69
    0x1024600303d411921702052003130349500052400c1c404030f80740c82e0040040c01c0311000c40d0405655285082c0c940c50340e0208c1640191942e8100190032000900054416020380082c82885420b81c01d00c0c0c80307003500380111440800c0c2c1c082000100b0382c014005010329141100d010360150303203901d41c1c0d0140c01d00b1200000c481b40345031000141c6201c0300250566020f150001000c044c410305040d00c600807080b07154050395400c106110528560f241c3c1e036900044080c01100900c85e81050b1a06c142d40107081c41159100c00300c00a0020580c195481d00d0030801100201201021a054560385110280041c80e255001200319401c1c8400281c210070b00405100c14450390100d0b0324607554880e100c00c80201101041010466010040c0a5041207044040d000d4803041d50b00002d00e000c00c0e008401c0880f081c00040403800c50051002c00443c1d9a42c0d2113100141100c881c02e40e0003695015041c02d0202112000a05e425091b0300011513000e0055120501c54031803601c2e4460702088400056800b9021445401c0303d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 410120692 1250 410119442 410119447
    0x7060f0503070314010305010b0a050102032a01090204050f2a07120c02030d090f050d0b0f0903090d0606080c030f061302030a0b04121b0308070f120618060608010803 73
    0xa15200e031005560060303907482c000a0210440381d460000d03007400e900a0701c05a458030301c0c0c400c4900d41710030200c2c02040c00340008d51824902030328001268004502d80303040c4081d44015510b0321482900072a030119070042007003100b4a01a50800c842c014140d52150014034080c2e0640c484290354001c1840002050049500305410b90356050f141c406120002020003245070642d034010b03207080040d00c41b040640d403103401c0360b2424840c8402c407809665220600c180c4005801402003103203000c45070f800c0344403e104043c8680e1a040352918500c165418560000b0400b0b03110030038041c1070790140741a649000b00350f0344454100401c0603521180d00e00f02461175005030011841d5822407030300d40c2407290b2003d0182ca01c01d00d029200c00059032011141075450b107038540b8211211540c058041c400c0d4424031a15600040d10035140204035542c010454020301c00c000c3d00e034240c0907000701000c00104030019810f10a081e00c442d050710040000b981c4d00c804160420700f000c1041d5004010850584083c0d500450 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 410121942 1250 410120692 410120717
    0x140c090108191416020f070f030201030905120d021215090a0e0f010908030f070912030f030605031e0f07080a0206030601090b030708011404054506100501020706 71
    0xa0114094260a00d0340d60760f032032102c501401c41c91100d100741c4ea4450203c0008241c01d0001e41020140190901ba0f40c100e0b03032051140041003045e81e01544e80a01e80007491038810310701a45000c4040d00c400020482c00b00c0d02101c02103003500140703280c48800207400341c240c41d10030214180c901242d60641c3d000080400023005061503900c5082482d0408007101c0e64500702410305400c45601c801d007607070b000b4400400c1010a2082c65581c907002000c628003103212501d402885142c0001b00900103040210f03c102c01c046241c4290008805400001c042e00e5001c05c04040c031861521100d0f01d203075130f81d01402c082c0c40000540404c84804950458016100300a00d81d800c20545610082c07905041c40500b80780414411b8024020310f200307007520b03214550300d5418612020041c8007900001c9201d1030a00c0108010300f0f0055880c40781c040034500c880601c41c1080b0703a42c0040842440c5150400644915410b0342e031940000b8064001c40d0f00c0401c450f900b03522a8012621055035010b0701d804100100c6141 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 410123192 1250 410121942 410121961
    0xd0b1302070b04020409020301110f0c0d020304030507061d04110c07050a050d03030b030f0303010e041e030e01050313050d030f060e04030804030518091312020f1f0b0d0303140c090108 81
    0xa1b0700c80340c401000080d40070842203103150a50094a000c120103007010815403450142040591400c02d0140001c5040918580d11559684158001e400801107405011100d0b080c1c0608005040900180240035450703030303072485243d60741120180c0030051042c4a00002c080c1800d032406002d0f564041c000e482c46107020740f000d8019064101420380c0605c01c004214003c5002480614060055502e11448a051904141c01c14008841d410781e2050501d280440c00070341c00941160321400d0a0a10907180e50320f00303164083c501e070390080c040c1c03540c05140f00c0900b1081d0301d035210002044c00c1c91700412140f5200c46445054041c01c5034020b000c60441c8010801181c0600c02420381d08940c620030b01040900314010600c20300c8103403003400311a10151900410000040e5020030946a00e00c0140300c14040705031416620b0f0241d002c4024800503070580f006001661780c02550241c2d0700a02400c0706800a481d0080091844001c0e0700452600c040100d00e0381c04013001121040c040503501c1c00c42e01c3c1c07103d04e420f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 410124442 1250 410123192 410123201
    0x60f0b13032315160f0203090a0b04090e07080a020d0f0c0609090b0906031507020a050f070504140c0703030b1323091f0509030f0d0b1302070b040204 66
    0x1100314000803035000001403440000d5041d104070740068081241d0b1452800380c40c010800381d4144000d82e0312004c0014010f100d000310640e02d010342ca00400910310141c1e060781140310740b1600b19000f00c1d1040000c10100c2402c001401242c2c040442002948545415181c0b6181d075400350648940000c00307403c0241c64112850101c00340146010407810790030350b1381c2001c080810307407000020911090742004130710000d00c2002d440c210306480340c03a1300d40f510700000781e100e904a40c180d1400c1403a03100070850240c130030803001c07120f143c5c05400c81d408520300714402542da2948d40b1a5078030543c2417010101d043d104200c42d250242010714011030a1130074968080c0c01800904001641000c0e030030240b00002d140f540510241e00c0c2514080007040d01503c0264400b06000030b000c00102c0e40220800842c0e0810900d004030303491301a40000aa43d103a01400302c0c10361080b141800500c19004c2120142c003040395011000d020340403120b0f00880c08480112506034011010040e001d10b40c500006009410320b07402 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 410125692 1250 410124442 410124457
    0x6090f150c110316062c0a02040f1812030f09060504020a240309050309330903122208060916060c0f030c0b071805030f0a08160b040f05010f060f0b 65
    0x1818000a00701c031000100b02041101d40c51844e406041d941c010350270709106542c454640e50386c6c140541103808502101c80c20441900925100000e085441c44521960099001c51440001840840d07201d0400801528080d5400ea1091a02d120001340c4044410420100340d03100242e5903905850001003680100701404054406000c1000f44607059910103c66183d0b0074481003155000c4400ca4900c000208540c181180190034100642c17040c588d40090910003002c5400b840903503c0940c58080c82440b5660b010103100205034080100e10720b440402d01030b02c9101172100311090b03506002c01d0913245000030710800002c44c04844004000c200d0130040564014000c5c1810201e1309082d0307541700355040c422107480000a86d42d0140c01101c81c801d0707060340001d2204400400301c1e6541001c0460b21102e1402e002064508005140c003802010080c0d080c215030b400441c001c8487c500380c101101150b40400c0211039a518000460071910124440d01c0f0a4130a192840b4002d14181501160f40780d10100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 410126942 1250 410125692 410125721
    0x2150702070e01061d120613021305040819020c01090b09060c0f01020a03140405072601060305010f0509161802040f18061a030406090f150c11031606 66
    0x40c00480d492440890460090131580d82e40c46221101018844d24130500320040c612400405450945190707000651300d42200340044813200c640c03060300c000b805405c2800946d620032404c3c001040140400a00980f60060407640200040301000e10102d84074074400c01102d001c0380708410180030b150707010b9000d41039840340500f0803072070604036180847c500135809260814a80d000121260303071603414011600c0e0007040420b0028107040540e6210385421150042610304606841c44406110345000784401d00c9440000800505443e400c0103400b80011070b208111781400c203804217603200300c00181c00c040c00440513280c45c00e6a080449440000c3c44503109028030580038080402c0d02600e80e9a6100140341c81d144a841c1c44c1e4904c54030303000b50f4620354482039005003d29024a0510340d10b1088961140d444800000ca01403a0300d40045081500180a420b01e2850b180003464a0415488210346224a4036000d0703020704d41014003540c1c4c1c45403a030040700900030620401c1c0000c484d03400500d04044003a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 410128192 1250 410126942 410126953
    0x513030609170c0604050d0c0b0a0c0311040311180c03270f0a0b07030509031c110f070b0108070513050603120a021c05041a13051504030203061602150702 68
    0xc002050503420840e11072aa03031308000c1c03e02081140421880d12030105606080041e100d2685600481d03640c001c0c08180e08945500248810a1007540485040303a03010301c450743c4480c0c07281403480c51a48441001401108040d00030700c560040c01ca00039110710342c80d1071f0881c555035480c0380c3c1c81c02c1c80c0210a07040c109000044045091f01c070041c0040003035101c03080f000b4040003005050400e5803250240035a41890b10304420f008140302e0210891b95944000f068041c150044c1c1c92010005100d030760030b0110680804a084010011594000d0100c43e008585d14007450347c982d400107403100c0c26841826440030072442c440070340d000c894101981c0500003c060341d400510405242819074001c801040058002e1038020000c0481003401810409251410609150510340b1180c45500320400701e008640001c03582c00440d0b5045099500505006089961004800c0010401c15001400100d21a006500009082c0c0705d1072000c503461050540d0041c401618444003070070540101400440450084 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 410129442 1250 410128192 410128223
    0x604021207030b0d05060c07021503090a03360302040b01090f051309050d02030c060109050103080d05091e0304090c23090109030503030405060609160f0f0207031a0405010b010513030609 82
    0x9106c010311412020140c01d540b07000e1841004000c000c051480b8000c01414828040d800c0e4000800929403941414500c405030307110301001502c941902c40d00d41580240c00302c0001d41000813040070044070b10940741840800280c600648500140340507880c5a86880201086180b40000d100c0700c030311201e0500000c0d90703400d5403200c50410085500580142e4400101d1148a1400304030300c500410305c40c0010040c6505540d902d01d414403c02c0d070700c400c000f44c45002050309004240501c542520601c1e42119008440701040c80d01c940251145070f140d9403402c1c0006c0140350082e511107440004143c0c83c83e07241100c0c203c4030a01508000203c90402140c0280800060303030400040d40103500420003403029240010070004c0010009110030101c0c003589140c5280c00d40c0000c2000b1160540b410100c00c2032062090880c41c10342c4541c400350800c1c00c1422036280980c00500d646000301e00a1002b03200c00308070100103413103910403250000301c02c0307500c07010401c007041b80d030760051440a00c12614071114100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 410130692 1250 410129442 410129453
    0x5090d050f0f070c0e090f0a11040615020d0207060e061614030403080702130c0e090405010e37020d0b040203031b0d170601050a0804020d05010c05120604021207030b0d 74
    0x100c000c444d015950380050180c036440314942a40b0010341002803468101000100c0e840351800d80d8002e242d2001c0c46030f040c03650781d01c40e000f5001a10414001c04020007801c0703c025503500d00040c0740005030003041c001050701482404205422070000d0f008900e01000b001c0483d551405144059a00c0001c00741d5000c030042c41800104011401010015103c805074010403114019180c500f2045601d0b0a8080c490703541c0044030072141c01e8040b80c0c091000da955041007400740507031040003d081e0040b804075000801c017141c041c1e41100c030b900c503021400c1503c2d02c44590050341c01c2c00700607500c02c61000c00100083c404180c229803192015040d00d0510118000d1619450301c468035440e10703900803051555045a0104c840004001c4a506400c110304220001034803501c03e004011040100c00b6000070150745810b240d11a05035030010007000416840c000c01010b030b806c0008074044861989010559030b140ca4000d848458003046010720a6072110300003540146048142036400910001c5040007254 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 410131942 1250 410130692 410130697
    0x19170a020604030e0307231f0f020106090b031c02030f0301030c08010e1b0d03020a080f091008040b0a0c020f12030702160b03134205090d050f0f 64
    0x11640007040c06003007928001d4100032946544034001e9120407020810394403402176401e614401d60011040b8401d084e00070600360035035120402000c9a2510300c5000c0342e94000c841c0d01c2e419026500800c142ca44600681c030a903026005640d0b81640464140d02c2c034420400070f00f50707111907607004483c602003540c3c14a031007a42090740142c403a19040c1c5010030400e8820b000b00c5480a259002420400c03030518140035002201604240c00f5480c0d4543d00b40c01c05001300201100c0907000b041d40c41c0c8070740540310301c2d10b556800105000e0052104e940000d0042e401091034501440e84004000f07034070783c3c0340705940380204040c4444070304604c6071090180324410180700d690514080d4030010b698078a01900040e00d410601032041d16003e24a00041000081c000e0940b6041031004000300d81040290400a5075a02c052046a03c2d42991481c070400000715410028040341302c89034181c20700140141c80e00100d03141190b4011031504000c03030700c0081c28450001480c503641d43c210310384c0c24003032814a1145942c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 410133192 1250 410131942 410131957
    0xf0703030c0221030103121704140304050a0e01170d020d0305150d051b24090a1701020403111203070605060a0f060e040f0605010909020306010909020a0807031a01021917 75
    0x40f034004010b000f48802c4506101103507030715040c03030744000c0c405400c001c20700400200b000c3d06014002d00680c5284401703001311001007000425407450390751100719a005801c1d083c8903d1840e00904ca07040002c1030408549098000c1181d0050f0011119039a000e40c05440300a00c004581c0c0300202010081e603458094a0710814013460042202c0b500485240b0401000f90080a104812003032001009905121401c0c008180d00106540c40744034420200b180c2e8905a00140c400402e030310b622140030340d81503010704100c9005840a0b0b0a14840c0d905112400700c1200302e8140a4108005820104005401c01c0d6000980545136150041d560b030100110241d06400c034100050071f907648400503241034010700c5000401c101d410043c1c10325120028165aa192040134003060b0080000b0b44168060207040005004111341550f540c9680b038070007800341070200c810001007031911000051080c2060b50624030701c0340c103800619403a440c47c3d4045080b2101c50f071003111a0514400c00200b01c0c82d200000d042e01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 410134442 1250 410133192 410133253
    0x4020705030a031a0307060309050c09010b0703020607050f0f09010e0330031e0a060504020a08040b07030b40090311030711010804030c0f0320030f0703030c02 70
    0xa80054001c0203094038281009203020700305034134040c90305070b5021a001044607594100060301090710301e41103040c058101001039103c18100f00005400b9144002001d80764401c0c0d090741c5050b41c2d40001680c6c2c0d80101d0205203604001446510094042c8000a101e141c805060501c40501c52000213450848a0450031005d08001c000206061059000c50051501c52001d01030961038000241c5122200040c4603111080c081800700310800510b60000010340809002556102a01c52001e007070540c007654100c5005044074005500c0510901c0384160180c4000c0a00c0115187d0b5044041a1130040c0512519040d008100400c00611002c040240c0050048081f54814640c10080e01c200100301c00d4413a030750001c01080d40003501031003111084039401d09003505251502c0c10b0850b24207142e00c43c001d040780c8460030483d0500d604001c2d0009694240150910210644011240c49001e591b069080e280c07414000368002901980004211200a1040710f02442441c1ca011a10b0b00d07010351014203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 410135692 1250 410134442 410134447
    0x7120e4303020f03150408190c020f090402010c0503040815090102031933150c11041e05040b011406120a1109060409051b0325050c0d02030c0c010305060123090402070503 75
    0x11201c0d0607800c090705a6234a0520211000340c0750046500b4401034011244202c0b00c540014086a009500709240607400404694807a9207608082d82c0d181300244941100c0c1e198a00091041031050003124403a84880e00d00c00b0b1005103401400015004004030f07644070203000301c2e4102c00400103078880055420800c02c0750060a15002d0014002d0001440d200100b051054030704021400094504581c2ca40075180010142040344c800c0343d101020311450001c1034280703030500c41803011903144541078031102c016330400400b80c1c004000451142d030040c000002d01c03150002c0c2d0b131500150b210034045108040324070b00d007000aa00003047d640c80b07078000c800c00940d01c03c103200d507503c80490850344240540b480c040c0386040c45001240d00710500200848540d450ba411541c915114009444001d4824401c940c0b0651030000065165005a4404071091080006100c5598820f004d940d00810041c2c5401001440014001803920b420000610f40e0003420407862641d61120710003841418003a1b4060342c1c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 410136942 1250 410135692 410135707
    0x209092e0b040b06070803071e0509040c0503012d0306060f0306050a1802040b0315010f1e030c0b0a0302040e0a0203040b0f0f07120e4303020f03150408 67
    0x41100d592001d0580202d140080c0f5844588580b0221500c01e500092481d44030765605d42c2c100c9054501d020b00c2501c403c0c240c4444044282c02c00003501403204119420300044050000407034090009104044483d8010000000a14105410100c6049160303082e41d03134503a220b4a0b0f5100740c80d0987d000380000b04024004005222051140580240305142e042c40070f8040344843c091304c0039018101a100b907039128490036055408000e62403503d599551810f03404e42e500d0802002c0b052042c440d42d20b00300c0011a003010710b0080c0036030f43d8081d20b50015008941c0c43c10a01c003a595a0040031030713001070550030040421490444c44070503105400480703000d070740c0b89032520f403642000740c01a007000c2c50b050007402440108004040343c542c0c40300c21854071510805003601e041015141408458490303005000b01003003829142051300c0c51640381d80d070003002d110041051141d40319140c03107a40070002c486e282c01400185400107a4000b80303007009045940480054406888429040e20120781c2d580c000140c04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 410138192 1250 410136942 410137033
    0xa0b0a051906020609030405010509010e18090f2104170a060f0605010f050c120d09080c01060602060f09072601050f070306050103020a020307060f0e0303160e0d0f020909 75
    0x1585c03054000d0061400c0c1841c01c00064494000c0342c00250620034004058420313521146004032400b400410382410905110a0b250b44070000b4101c0f4031168010b080b00c0030345152034141029403212054174040c1c039041c40c003000074620b50450f142480007070180c1000600420300500070000e80c904e100c1e50020380a881c0c03000140100f200694003c0074080305100c0081001808102541f5144d0700c0010681d0710102c447c2c2c020014019480028105900400c4159078800d0540c0300b542a80c00c107400700c44030741c0c0b503e0514030041c0404480c1c2c4409940010804c3c04050b0f200c50700f400c00c0000ca03d80c0b20404e03c045140d840e094031011903503041d03c08002010041150341c540038100041c14203003011880c141200c54002c2d1684604d07500540450380340c031160250a405540a241600e81d081d050700d48038201100c80300120b2001541100006400e070f480540305151844000c4cbc8a980d100f0980b100b42c110507801d2001e0100024003544190003144880d40d15118000c0c8480070641d4119281c2c04507100c0c1e5900c6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 410139442 1250 410138192 410138203
    0x1305010912180f080a2003010915050f0f010b09040b091302181b0708070c080d090509070801050d05070515040305070806070f0c060f0207150f050403080a0b0a05190602 74
    0x30450f014100c0c1000c000940c0081a01c0c404c1d642c000d40d05050008401465601d583c56003006150198a40300116040c8400280d03512102a44c2d0355060081340c40b80d6249a9964806540b07845049907a01c0c010001c00030460001d04a44070058000329034488840001011403c0c21141e8002c1044822403034411850a400c880040d000740072a01901c6007044c0441d94002d4030300442442a0f2100060868240403c2c801070f580c0203a48201010181034441d10b604d501d512140085070b01280e2082800701e403918054120383e220320120ba07100c1c6002d07880d100400c00740004501d02504d0601410300302003456218051002c26528022348510383c0d175495071070402d14015061b4021042604078070203115031540d1100340c10703220380d006160000c0030b0396031820030000926003058000595840064107a08000b40e0050801104141607410840d400c00c0a403040281c60b4103d4001340011206070014042020540c012043c00c040500102c1c0702d540c407840814a4803c8081e420701c02d00b04800340400c04142e04011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 410140692 1250 410139442 410139449
    0x1150206070804051c1701080c090a06060f03050c13060306140307030f020111030d05010f210302070605030a020f3903070204050a180f111503130501091218 69
    0xc0c1102d852400b40c071120b44565130651107805a52448240242e01481070608200500e0310f08890002969508051542c4003244140a402150544002110001e8604c80c4004682d0326441d589030f8500710820440003044020900b920040080c402d41107012549a02000a0000754400261140c10b0103050b010544540c000f145c23003580480400e00005000e90034550300c1c1542800d00010b60040d0005490541c01035600300050340d4680700c000151180b101014504440442040000025081000818050350b00c1005005640000e03020000eaa11500c0110f61142c05164010300f841ca00862007412036020400340c82d4041036090401c0da5822032003540d04201000d911011026110b0002e21585030b02981d60041c0c8503d654500040004072190003003594003089402118000455140654100311280000d0325011050000300010b81094103001600c02c0401c524541550345601880701540e68109040302c81d952560051000121030a140c02c1d80d501e015150405d00991244840e22426299031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 410141942 1250 410140692 410140697
    0x914060708100b07080d0e03130f150e130e030d0f06090219031a12160f0513090f020d152007020103020903011103011706060a050609091e0115020607 66
    0x2c1c00b04440c41d0050121008940c0c0718071220f0701e804044003448010001241d001005000014075070b5050042c4a40d22400d403594100300e400c0c171a44400350803961102e4a03103100042441030003405243d2a06007003106d2136290202005c10b01002e118007040c02d680101e000201c0b801c0d1562010011490300380508009811000701c1182400015070015030410b01181c003c005056444e0340000c0090f00801c80b400846002034103070000007040441141d80c2d00d0307224a0b48000c0009210000c2005000700c01000d04494005041c802c040d800b04031801d0003455210011100c24102c5c0340b0300b000584030505001c403028000d00f84100c1c0400d0503540703a0261030070800d40c440c03840f050103007200f115420041940d80c01078081c6801602c030100c000200707005080718040400c0c15900440006410700c40081c1c5c076056560203800b600d085445900030f00030701c0022400b54030f82c03022091049a002d0b051030b0101a600c04040810348104920a07141159544000c0c3c014825800007003801d440c2c0990100074580d0015a40d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 410143192 1250 410141942 410141971
    0xc08252009130c1a1207050c01050a090b07050a05040e0a05180c01020615180c09030d0e0d1205270117070918020724060f270914060708 60
    0xe640340500c900d030078010368480031507113400c0b40064201c1c04295400a50186022003182c01c0941015145d86c1042012122035820318001865000141c003030000c0d565401a0802d00985810300c00350342e242c1281d417021041090a0000103178002c2881c5184d8050000c41400141c21704121100c2c03400041120f00c0100d041c2c0c00100140c9603660300044542d44201141c0c41c042061407407a000a82583c0907035800301701040c0b45800e020014600c0c000a10003500f04808407085c0380400d0380240d07042080e00007180d9110500020890115031404402448201036141440c913004192518a4410a00200301d00b4070412850b480c140c5075802c0b1104a1155241855140b49031602d030070020481c40250203003684134000318141c4080c20b003464040d031f60307010351141000303150403151134031031035480c2c0b103c035603807007024200000081c5481c003520040e41a6100e00e0f8810300e07000015120040001c40c0761040c00401035480c9958004201d602540260300d02d040e0014042d00e04004200410101e809802e44200c840013 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 410144442 1250 410143192 410143231
    0x12090708031c020901201b0d050a120318050709060b0f090f010318030305040203010b091b0702010912060e010b010813060e030409020f0301030b01060c08252009 71
    0x2110030b800c00ca96040000960b403003622400489404a05c843e005030696112101c08003925000302d03103841907641d2109015903001e1011304000403085100f0010345a9004409118041607031403104804240140c14085040744190380d1411003184000c201303440a400c440c8040c4551481402070b00020701000134210b01704414000107903103d01c600b54589104000003440d804e840c1c2d00030740100303500410040815141e0701250038050080c01081368102d21075443c0c12040d101e1880c24060303c1d40522100e5a070800d03490b12204404030250300107481603040c0018000000740200c21079900c181c407a84101400325a81e14511115400d69403078070540340c1440700840030410741c1320480d0840700ca41a0003000100724001c104508034154031854116051450000030309d00d14072a601d4005504032441001105802e030380c1d40f00120350200b4401c80041402c90204080c02c020040300010684030200a5401200307400c0c1607450000c4000c030b89007841011440c4840b00e448504e0b001c109254840e0710500d0403503413a01d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 410145692 1250 410144442 410144467
    0x807021c0503060d0c090906060e040c060c050c060406050706050f01032f030f03120a061206092102010c020120030403030c0927110c07030305090d05031209070803 72
    0xca84424040120100c00a105a0307074207030b080204070350018803d907620394640d128540900380703909090b1241070500030001401e445040c115803165801c43ea540411a00f0721408403600c0410b500c080d0361a2244166048a6640f00070040c03000305096110590344000b00e1620f00140c800041c00d050300b6440800c0100085681220310620f00c4c0c424010b02e40001e0001c2c40c081300c0780d5240550a91701889042c0072407014050000c0144501603085680d807081e943c5480ea00b07410b88000740a8003400c10040c94095002901503000401e0051003070303a804000c008503400304546108090749140050303440301841c110040d02803048185105c200c05145c1080d240c100c11a260300e21001d00003d00b011390f5080450342d03071885550b0300070180c90b603010903d010410005002142040010161100c103150600000101d01c1c0981155400e04003200a042981d00d9610300361115081031b400d003508651450b000c400028400c1c401003c65034041880020b150821368030b180e00d07180342a0020029a0300801100c81c0600 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 410146942 1250 410145692 410145733
    0xe09010227060c0a081b0f030703050d0b030607180501030b0906190b03010b3f060301060b0706052e0e060f040903020607030e011104050402071e12080702 68
    0x10340a0704825070700c400840100e50284500c0840200c140500413040c010072850b0340040c202c0a6001504003d00080070552507110190000d90a500750b204000e00307800240900050300c402c0c5502d03580000c107409180c000ca410031000b150340400003002980c0c101c1c0c204507100340c040081c000138a000c0000304550004690400c101904c0640b01d64004103642c0340703103030708030030100c001e05046000d00d40c59583d0b42417400c2d15500320700100407072141a081707140c2d2401000c50356100b6030b01c4405046042c42650600181112201400341505952280408101a030002004040491090354009901e02e4003521035040071428200041c1e180c844d5564a240c0c2420000e4007505541c0c03181c0e824607448c0c80b0b030800540340040f58010380da0890304041001d014182c000c901d041c070401c400d4806210310303a40342d00c000e8200d410030020385030680024003082c845800d05601408850784540100b26540c128008098040d440300c540498910006100118415510090491704000a80000c0c1700721441100b00d6100c04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 410148192 1250 410146942 410146987
    0x10c02060c0f132d05010c0305090105070515180c090114060d1811281e080109121b0c150e0d050d020c06190309080f0a05040e090102 59
    0x46800301e03410309400c140142d00d000602a100c0c00022000540c0600c911100840444800303181c0c4d101c00006046d409081c00d29440e0758540d6030315140c01910001907889030810703a8252070301d10854501c603000d50900540741e40110084907884120521031354416291207103a01c5001d02502e040d0004000c00c601c400c454109408044a5681c1c0312100ca00d418001031000404141903100401e03900310034460b002e54040203809040c0c80f0808a80910320039101c0c00d1049205545011100f0381c1d0800940da000d11191501082c0a10102501a96103107518255441503205450f40c03011100f420700c4581d0050399a00600c1c0707001c40c407081911003645605000c07403c940f00e2103d0f01108240501500c038450001e624444900504a00303d40f00f084c1420381ea150513828514026100d1f407000901d051500e00103440c6080200e4400c070000d001400801c03005810340d41000c031074801d4288540002650102c0207031101c07510701e035202c9484916040c01c0d403001c81c101400e0604c0d9a44104110020754501d1541070005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 410149442 1250 410148192 410148217
    0x1806050403180b2a0f01052403010b031f150305030d050105010c0503040504110d150303030b0d022b150506030d030e15180724020c0307031401060e0702010b03010c02060c 75
    0x10f000c05440b85e0600d804540402c9043d403030101044415280140881c1d01c4580c60361074440d80c04290300c00d0501b00d41c254515180e01d507006009079654601031240040983e1100d013004540c3c69515400c00c546603c03035410481d529040859101c1c61450301341f04d00b074018002481c000c94204084c5e25081d483c1d00c218019103000b15218500500c1001c0c00400300c40041c82c0407002005506074a045082c1900c2030390200300e00013814a0780c948000d281c4120012409500103018544800350780c420b00c200905034039003801a01400401d2440400d850303840310102a40c0c1c801002c11310b8500302e4105414a060f0344e0440c03041c14235055a0302c2051500203405d5038442e40e040d0b0150210345562151a5076668040d2428129100300c040105d50311121090007095104592107049400000c0e102c240d0f03ca5604d00381c4541c140e03101d400200b01150080d010394440e1000d007400001e40e19102d045006080c1c1003190100c0240c0c2d142c00c8030b151301c1c1c00e091040c0030804d0a9440034005c03905291210031060711903401044d10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 410150692 1250 410149442 410149507
    0x60a0506090c07061503060f0b040b060d15080a0302070608010609030b0c090102010605030f01020d06091109010516060501060e01021009121d0604031a09030309101806050403180b 79
    0x3086003545c0300f01200c07121801a540416030f1703441c0410290045143c107400060030b0100c072508500b09030013400103840c4024480c50402501923031002c014824104040c000080ca01c1000481c2d210610141035502d001e43d0151103864105000a441c055046c0d0080f41042803c00003000402d41142049030400c50000e00e05a9400d00f500040380500b0041d0800c6a25018151898011403015030082860180340001400b4180c3d64103401400c54650314401105503204008450b555841240100002c00d00f81020865041c01d45d1103030320840300246c2044020800b20000c8206960301080140700040c18032105110340080c60380d40a803001a0011031300244030100c44e11030603030380015031600051100600059211070766400d210040b1f08820b0700c0325140f0504140400c683d00c0d40401101e03c500d080a00404880040c0020381c00200391050aa0085409141080d00021200e000383c0b07024a0003540da030803d00341c40b107550b15800011a407062032130500c01c0203001070075045010b0018105250100c4542d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 410151942 1250 410150692 410150707
    0x1d010608190b040905070906060311031005041518050a060e06030709050702031b032808060d060b030319110c09040b130507091a0405040f0f0c090c0809060a0506090c 73
    0x4000c0c2c000040c004041d0b00902ca40800c90b172207194403850032101c15503018490480000e40440d42f9201c1601c4010341c1101403801880f4900705500108002c0560fa0b1b881d49500341e44031444602440081e03000d4200c6910355042c00800c1d10280aa100a801d201c00082c81500784800044d940721803e10a0303011180c2c9a50016030384600900c1612820000351401e8280100c01d964155280e5001260388008070340c1040024490b0600c8099510341d030705e807035140e5500988441082001c5401c0900040300c1e80c5032203800440b401e8400f031019040d20070889001080100f10703240c01400200c0c0d59610301d1303152742c885510b12076243c8d14015410341041d0028081d401c692582400d5042e52140395802400c580b107000c1d0001740d80ca142e23512090b0b25500720065002010a400c0821003503c90554010340102285030890010420107210164094800d412441d00150b56602c500143e98100800c40041500c441c02c21540c660140010742d800400128108030b98603182c00060b000302c03c098440c0d540d0714000304095 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 410153192 1250 410151942 410151949
    0x90105160c050312071214040b030a064410050402060904050f040b070503240a0302030d270302061926070314010f1202010512011d010608190b 63
    0x508405002d5030303030b042d60b1810007207079170351100704112604288001c07403144e85071180c140c8005041040c3c901600e81403030220343c54050740000d000596001d9441d131000035100d100d2401071a6401031118011010040785c14580c103200340b001c104640321500c800c03c0c0440a40045103800030768920900002d1551202c0c00410114003949083c15045032911090120b803151026605110f50701c264140e100c80d1742c4804040b0f407940030582d4440740710b603407407600e80c0302d06c1c40601d80c2d008810102600b00c1005941c1c94002a1070501b800004c0008141d44400d03031407040000400030b24041d448000103c050314035550115801d07100390400913105468100482d00803a1094000c426030003990469a1081908851045100001560001c001c030745404066072400911290b154120346034064200c420f580303000d41c00c140401308040300b01d04024003003090306010b27010842e60070302070110302204160b1040810258031001006030000c02c01c1c030a411040060a4040e900350506c45a08000c020910300c411343d010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 410154442 1250 410153192 410153213
    0x3020d0c0305070b01080105270312060f150318011a0402091201050702010506010806040917030a110c03030907050d08030601050f040b0a030f050709030c051e060c0c090a0209010516 80
    0x44c050403190000054501c0c054001c0341c02294088a8104180e0103c803e2010004210355212110303042030000c0410302d00450310480e80814041d0107980f0404600c0001600800d070310b040801440c801105100702c2d0705222041601d07005000008000980121001e8a85111580103480c400ca400162034511516000344000841031510000c0c085801c0c21080607001c2c08040381c0040c005049a000601c19240c18001e074606c0d5a002500124100b540b00da00d480143d10080c81090b90584035200300c034481300100024a40c2c4034044c0702030342d1030f81802e0205038100481980011710402ea0092654046014002140e0b0000000d0070425620765030384000440c5805036601c000441c020118032841c12079010b4000100030441c04c4020000781da201102542c00103090700001e80381010724030003031200e4207010400a240e100b68003608514510a0070000c0d503240d0080b0904040c5400035600b10042c2d04ac03000941e500042884002d6003058036081c002000c6010740e500d0504050b020403d80028041e940320f0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 410155692 1250 410154442 410154457
    0x723040e0a200c0c01080c030a0518031b240a09050a060c05090108090d0c0206030c0d060f0e0c1204111305070302090a090b0d080c07080715170403020d0c0305 70
    0x25650104005110b00c800716400c014400701080c042d0a001410b150710580e002d0b80f188000800c1141103890380c8075810003c0100800100c442c08200501d0802e03117500f000034041b21f143c4804844409031060b58043e041c512101703003407200d91568500c3c0001d0b050102c01d0740c0354016081240000d901c01e01e820001d142c50304485025120b9485c003152440c120f94400020a1003100070317250780a40b5214000b142d41c3d40c09000050900041c000c00d4a2001480c0030002035411149202e450381c10112050308083c00c486c41c6070b100403001d6409560400411146121a59024519511480c20121221909019684020030080201c85010340400d42640c1d20748004082003600c8404212601d04050054000d5005c1004540b24104120001135105650700851000c03003c00b600d00c0c103440b90940e032151000d40024a1041ca80d0185a078003042849082201070024600301040e0078070f80c841d0520240180003510808150325410700100404641c000a444109500601e0b088600c10900d04cc2102c032400b030030710b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 410156942 1250 410155692 410155721
    0x70911070f03180312050307020615090a0c0e100203040303120c1421090c04110f09092805060f0910062006090708070e070914060417060723040e0a 65
    0x4030111702c03640e00c80c2c003841c450b2425400b240e1540d250103101000341200c44011640c00404140000c1c0001c0d80e50b0444540d000403410030f0b06201000500107044e2040551054006a10204d400c0080c542e11845400c86440c005004004050001304020202c1c8451429580307a907900040b60400d004640e60f52507031001c0300821000c840e0030035010b195100d450340102280700d2401c140c07503c18442949411582c45150580b02c1d2407a040c0580d040c0002800020150805141100c148109052130301001c04241001c5031030000d600e1400004222400062800c5240540789040800c0500200603a0784c600780c1d5442d0500c158080141c0f46c80c83d42810000f030000e12035008000900072003c07400100c2c0010795a0840a6611498440d907407406203890483c0d0178000140820020071000b820b04020362070303505004c0c04c1e4501e0262500c00120800c20028801b601039030004080280e01d5600c41c0e11500c0780c07072403040c0c4407400c004121400b40140c0114080c0d0004d1010200c042002040664030581d0403003201d9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 410158192 1250 410156942 410156963
    0x112080a2102070501060302011806091a090a1404110702060d0b041805060609070e09040318230307150c060f09020910150905010c2a08070911070f031803 68
    0x901c4c0c464040c2c0310b20311049010443d41c03001d11010a11003401c50341070703418580e561032a56140c01c141d0a12080c040700003000d800001c110b5031080d52034000503840982174680c1030184884d00e80302408111002c075140c10003820741c2802510016903810703040322411642034401259454102000800502c542280461481e0480300c0840c200300c0c0201d00d25214000c02c5640303a800b5075440b0400d5480d10a05411154800200710000300003a00440c0440c80315078052820f1202249c403002c46000660006002418026191108a00340d15003044048041d0900d03a0300c00c001a00f01d0305010b003542d031700d469000f441180c6504041808910302da02c14800c864000302004440e05000030b1000d10108540285000d205044090b10744842c02881c820089030010fa4400d00005070316151020b40e0312a00305141d0503104101002b007022500c40303030001d015200204c06440103502e03025030b0a0803a810450303001e01a8005010384004224400b4500e0796454044c02d08040003d80385d440b121248015810081519408 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 410159442 1250 410158192 410158207
    0xd020a0303140108060f0a110f042301020601061407050d0305040c1d0a091401110a020c030106050d120918021209031603051b030706020c060112080a2102 68
    0x15405a158069207003003200500700045035100010034010b456096102d80046641d0084d43c00049a000d10b010900060300000300b008400d5692028460100c00382010070705102a8441e1240b0808002e12199145020158040081d40fa4181445114180b0021507504004482e2400440d00c4003a884410783c2d40590b584500980201030a480654083c000100045080c000c1c00616200c118002c07005c0411540e540d19200300505140c0d403045135855407050400252540c00d0003110b0755000050003281d2130302c045040092a100304100c61501c41d03810403204010544820082d02c0005800c82031505018190601c01c0d55410907550000c1c0e0020502c02c0d001014009035400380401c0030b01c0c69013008094542000700340c0c1e02c1c003c0c030140c401080c0c03042e44260b00107030041c2c0040080201c03c00403400418440c910650440c0c21009041e182c190700004d904003210741c00c0c440b45000d0a410f4480450590b0141c644001e82e0041080074000d0201411810341c070501c1c09809407299505062096564002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 410160692 1250 410159442 410159447
    0x112205090c1906030e030304050c0904020f090711010c0306060e04020a110318040b0409020f01032c03180d0302120a0c060204091e0216021c080a02061603060f0510110d 74
    0x20320312503c40041d241000c40314945c45c0120840c0d000300e40100040085e441c03130b0300c100400000c1c0980700300d902c40461114140c454031044c090703a108040c030303071900e260100c91011890b09440c0d14841d480c1c1010300d405403e101540c3c00403110f00d40c0540135a00140c444d04841c1c010f5810b042a415152800d00c80820b4a401d1440a450f8030307440440300382d5040c42400c403c4d80610041c0e58405c14001c0d8401c22072900d05c4115482a8820500d048201c42861502d984444012450a51041030318034a900002000907800d060148070181803c1c059072400ca036010a52030003905e030000e290400c4030740d00e070005000034800c0c4591082461b50b60044000c65036156140c5003c1e000300b141101401d100110503d40b182e03440d44d07610a036020045042d0b90f0b000f60011503800c120340018045034400c0030007002e001d1a80400c0e68880a0600c645243c1c00421060500003080f503c00c0312004060b0040604001d420301064012503000c800301c44082e0340d014030106030304200741c880100200c81a0201e2141941c1c1503c1c807036 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 410161942 1250 410160692 410160739
    0x18090c0b0307090e010302130509010b040218030f070605091509090106050c010516120b0d06020f04032a0b0307050c150105190f0302090414060106020604112205090c 73
    0x70b41c15140d90128542d5002106600f4000f4400a540840551a01c3c2c1511046402c490307030107150040000b48101c2c511000404903086101c000d210800c508110300040d050130040600d600040800410181b40741c044014104d100e4102841d00415100803200e100318620300581e003080700b000700808881d6848000003002e640100c0c883c410b85600b001c011480d0022000c1400311020155698196540c0c542496040039103d51844c40b0381005a5511f03040200b4072610207005a4050300b1b4419942d075241d070410385402c1d40094140c00441641090000b070b108092400141162611480e6580300d90360450142d44034002d000c5200050300404007403111414290700034a060320384c102d40b03c004295402e036400e21072000b68080c00204141604050000d41341032800c99912074860203659104888218915003030a00a0f40319001503440401400108400e035404101309400c19601d05101e991100024506003190074604100ba55559010500640040c088030b80c8205000d4207120040c18541030249a22 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 410163192 1250 410161942 410161951
    0xc0d02090123130b0c0a200316050a05060322020f090702010c140c1e070b04030c060206070f050a0f0504090c0e1306060c1b0906030b0402100207060918090c0b03 71
    0x91414200c04a0402243e0090324000800040100f208007181c0d910664503d51f040740e41c60310744920300035800b560303074080242c4001005001501c1a00ea454078050003040215504054400c0f002841008656000c1c2c3e4045d10b9042d541039018840090309001040c103030501e118045270408458003c1019041c0c0540026103103400541c1c1c4c592401810314049090f80c0500d088400094008195544049403013851135900c0121120643d505141c3d00c19481d200d079440b0398001c4466007004203080040b903806010450b4000c019003411001c11f80858002051380c1300c1d5980e90400d202d483e0700381a48084c41181510080c01d0000030420900800341c4020740b80660a400b010f01c10356451403d440070710214000c45040320615190400c013141e1565070300382c4095058111003a0103091180c0068803400a00a000086000d82c030480144d040c180107016403c0c0c840e8481405661000170704010560340503180c1002c603024030092a510001030140130020b401600000340140b07154000c041a61800800114082c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 410164442 1250 410163192 410163217
    0x1606020c010207051b03030a1d030105160311030105011b0c0503010216060b03030427090f060c021b0f041a1905090703110a110a170d0f050c0d02090123 67
    0xc9402005ea00d07400c04640b00e030303500d406030010b1261300c01003030251b0300501c01c0c000144580c80d0304036410f001080c2155000c4880115a40181320141a00d58251182e81496806003444510715030405002030500315045107185400840520040700740103202443d00c000d00b00050003995121880741c2000c9180324142825510f1624012403802c0501c1c000045404079624130200c0c044000301c00070045c044912003441c41c20034584031001c0034002a544501a43c401d8407c41d0b0019500314401c034028600a20088100c0c3c0982c0e444050baa007540d1440d0300510007040458000c41d50304401d001b02c1d05c3c500d85214120740c010034605a0748204044c00f2000384142c4d001520000400c0e40c4200c000c030281c4085440400540c402040b4041e0100d01c60140044039001e42e8040715441442c03079403510b8400100380041340c41d45d00302040c0500303807601e60b01a0090303050250206100e54107140d62400078503c030b115018100550300044240c5030b640901c0d0540442e82d030006100d0b0840c0c107070100222a0f42e0018641428 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 410165692 1250 410164442 410164453
    0x60702120c150c0d080114010c0f12120f0c090509060f13020a0318030905011b14010c030c0203120c0304170307050304060c03061401080c1c0603050c0301050106141606020c01020705 80
    0xb4845c0b02e00401412215036042e40c00a4009850056412940321901030b903c200124900c03001140050023a03000c41f072400d5642c140c2c1000174581d50000c40c1c580c1422040030303c2c107142880c0155503000608006644045a44603501d4480300d000421004c00280c80761740104000c400443c6000c00355011b0140c0002d1910144401c01404002482c0c0300d984040c01804100140e000b1f10241d4821140785041c2c8402048610080215855001005407101c200d0003203a13468020007145030b90705015941400384c07240010350401700d52a500c01c1035138000030041400b003c4048005018443c48010703c80d43d485000d11011383c0d900340004010036503401181c0682d503440c113040c2d000205070303c648074240440341d404140e007002c140c41709e004648903240a424500100030905c003e000760b00030081818498004088005511407540c0b825904100c00c803030005100e6450440104580c940000908590400031240241e54541c140e0404d610010451400307004070b0b10100b958200c0b03400540c0181011b41c0588211807 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 410166942 1250 410165692 410165713
    0x1020a1b0906180b060a0c14030d0516020f0d090303030b040b1005120f10030201030515090106021e12030f0c04080319030e0a12050d0204120305030f070806060702120c150c 76
    0x180301d4000818005141f50b440038000c01c1042c010012a17000140c2600e1408035400f10340400d4950556884000ca0000000b9200c083d804011100e04d200c1d808000e040180711180300a0620951440054141525952040300d203a4459110045480303005052280f0340c1c03401803008000d81c1191403907400b46c11500c000324040062142d0310034455416400740300340450540d4011000b4060240200513008003000d081c80031a0b40b0580c4450181140d9401001440c80340380c0c0318065084030340450340f1203401000115112180020071282c2c000d842c031050300265142d01c14403051501c00c503402141c07280000f040c007500700015500b0140326000d9079a002c0c40340041c6609816201c40480000030f05100c08010380c00b484502400240c140b4a080420040c2443d54843c40000303000212501100040d9001082011081c100d50b00d01d604075a141c03400302210329210004c600b1030710910201070f1150900d0722aa11400038208414200790402404030315882c4c141001c801c0032a00b10b0400301c0d0140c050b099110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 410168192 1250 410166942 410166949
    0x30e060912090d0213050108030309010624030c0c0605070e0a06020309090f070c0501090b04120c030903021c2001030f0e101d1c12050601020a1b0906180b 68
    0xc8540000c075510301d61400000404002c00340482800072600800b081070942c200c0182446114020031580380036643d0303440e00d0b40305942140c1907a00190084000c031418480110003045c14181b080099080002703190001880503500c0110664009010a00f4403082042042c1d00210b0320488a000350390140b0a070b074407254141e8490040c0030a42d90001d0410000035103d4410030841c0b0380080701c40c10104440c2d5501e444d00350030b41da071418040e030300880c89109010400c40c0300301d0b14805a1045140000f900449603031f00078945a1280f0020303100e04003004d8102c601c5000b01085070559a4840c18281070015071483d4070044403000e511242c0801d240410036104115540611b000c40c59000c00504a40d1021030083d1006080c3c102000207003144406610803000401c100001c851241d441669200c0c00700040e000701400703032000c0d031941c0072414641070100607600058640011075001c45400e0740f8a0362015450240d80c2d25a000c29911428828005580c600b0080c1281540b400280180b15031521203061 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 410169442 1250 410168192 410168203
    0x6020c01090602211605070e010501050309060a24120213050c090402030c09121509190f0f122105010807230414061c0503090f0d08030106030e0609 65
    0xa2038050380144613001303d07280341050f000e0241d441040d200303810444c9405549400c200007000444060340164010300254001c0701c1b07580d00600302440d15a113185400450700c0d403103c00181041c0c2c0555240c960101d1030362051116100da9a0550080c5014140d0f80d201c0040704444415040e0701a00028040c0a003140140c0a41e600c00c44010304403d2801070102c00b0b0100030f520003444207640d0101840520b8082e992074103c840e84014600c002c03c0e10f421003007950103800c440580544c00523407000a803801e040c0070030b0f54503a1b10641c005000b0005550107081020000235000c9006004d02d02d00f811002c20303550041c100c03c80700603511a03820039410b40c040d00c4104454081c0101d1020350301c00c0c10308120035091001003a01520300c00e0401c004080c1d052010030281c4200a40c00d4071a461b81760108079a13030030074a0850a81c4564104107040110a6882d650b841e03104201c0d856028a540f030180350101c0e08c0b003c9403040c00c10740c81241c1e650b8079070b0758180080007400ea14000070400d02400b00400c0084100140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 410170692 1250 410169442 410169449
    0x11151017060c090d0c0e0108011514010e06210c041509050d14070b0d06090e010b091801290a06020d170717040c0e1e010e06041407030606020c0109 65
    0x10503c0d040c0070000300144240b40e1035007102e203580c2041d030100e580782942c00e59500800d21240041124a002a085a90303080e05800001c1c440011804030b00450780d1044241c211044141c81d02c1d40d9800c20311b440403801c0c0084140405482d02103501b44003084500c00c0040003100c90a49402d503688004403000c45003540544103140d0300a11140260010071107901c8001184174460702100c3d2083c0d0340704154945600150300c5650465501d800c00c001201c03171402000c3c1c01080030002001500080030005100c80805451000344000c0c01034034041e02042544441e4002140c02c00c280c203000d005000c030f20624601d007652030780900c00c507442c0010302e140000341e0780d20700701e005403200d81040d070307400c0c0020034105c03001000c940030807041031904545510441c8580c0e010f94041e1242d4a00141080341d524010706018151072544a075113075030b880f8003081c0c5241540c1558000280c1c410f140e01c81c4c800040c050020040d444c024802200140080b058055004004407546a000d03282182c0c155001502c10425074072 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 410171942 1250 410170692 410170711
    0x2060106140301090e0f0607020a1208010e18010f0e071a070314070204141e091b120703121d10080f0703110a0c0c080a030f1115101706 60
    0x401841001c1290700495800c0c0d450038202c0c0c201c3c000021b4602e290140544602d000b50f040388015100f404480e4907581c5a00d801410101059403401c1000068010b004201501c82540f00d2405200103000b9042044510782d008000c2c0000b00c0c0608034207441e8555445048110074110f0001c190b643d8a20301909d541d580c140c0c444820121140d40c08242c15071110504036402550742c03450218071503003043d0312802135100b002501c92905041c90303080103038000900140b169038000d40000b445c090312201c0154205806640850b410b80d84462114076068282c0c100902c003d1503400c4000d0005d511070000c000e444561403030b0290700c216410502c031100900c81140e400040d599000510351581c8041400d03080222441d00040ca1850f02d030081c50990005540785000680441900d0240003110711503074050486603005d400e030303950607540240407400c907611002c092140b10a14180c001c141803041c40c0c0020614407000556141034411001014007a00510701e69084040c3c00c61071a040000744070780f080c136101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 410173192 1250 410171942 410171947
    0x30109080405130e03030403030e0c2e02070b040b03090d0905010e28031103010609110a0f0207081006030c091a0f0a03020d21020d050d1107210206010614 68
    0x50500c40029148511401e5640d1135050000e1050010030046d0f100f14040e5a000544054941025090001140005114089910b0080c110540302c80d0417801204614150a80603003072140103034108002a4401200312201050006d81c822140c0021442613040d10292400a0031156059841e60040c6c00b88030300107a40c034240c200035400e000a082501c04684082c1180141c81030800c120300f145182c0044880300c5025400e08018242400703042c01820480c0010300100819102500b060f00076090a20b0410010b0003580c07035021b00911080001d0501c58054918100a141d408400741c0514070080302c100038000800142c1c81c043d4400c11540074629600444144400c100700310b803851089140315030003c840b007400030050b80c1c0c1210315021300b40700351020f64043e00c910012100241c110354111040d5008401499080d030b500c00d00b16485c0031201200007403500340d0201030748034a0241640080c60180c1040b20104001003400070517000c00180d0382215030503a29241c04403180d07000c900b10003d095406 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 410174442 1250 410173192 410173199
    0x30509010318140c0103110702090c030c04050904080406080109060806130302011e0515030106180e0109021008041103030f040b07110604170705090c030a05040f022205060301090804 80
    0x3500300c0b0814024484030b00c4222280303500d9580079080c41d0812019590f1060b00603003e0b0796014010b0705c015841f80000641801c00c0e64001c54000e07030005052116100c0000001441032340c805007030720094140a400a8050300e02031900f030866500a014602c0401d6007000005010300a5000300c209803904000a400240c480c03071580301400746007103822810355486007100040f654038506210b000d25000000400c05080803900c1006041c20502d280b030180e410400300740800030103200a0180201c04100c0080c03401070b8511b41a004007219040213500c80c5440c10040e01700c039440000d6600450146a2a0b20824080400c0590342d100d5280c08020a01040c40104081829100a0403906000c0c0080c2034a28807061f00184032a403154204501c1e041c02041c0b00107075101d0804c00b00c8054501511040c61604058000c1300c00c0c0d000040403482059220000903003082a5490b0843c140e650282c00c00000194105111124030b400c16546048507203881c0c0081d210345014020207a5168101c0f078128941800c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 410175692 1250 410174442 410174447
    0x1802010804020a09020307020d0905040e060105121005130b160e061b070308190306030c0902090105121504110405280f06030b0901050607020a090221040b0405120703050901 76
    0xc02441640e20039510308001501201c54002107110388030640c041d1200d8440c12402400c1450360b078001034040d500d03240b0034a241210001d4500d056840485414501510600c02280361682c01c0d40a0040c02e0308103410300040e42041414a074115101e035452400a80d07840225012419914100200180381b0505046c0c042c107004000f450102045545002400c1c01010b25500d03000b01940110303074882d000141d00d4032241641e10b071010103d02c0d6250611644d86991034100c004101c41c021000700c41e500141d9082a68080d40447d400f100781004940320314a40480c2010100e0701d80081e4a00130343c2405031502c0391a100c1c42c00c51b4203841004050030303580b29204048483c155070406824111640d1600e02068442c0f00001d404010446030740d01042d10001d030360500c040b450040c0c1c0914041e040c03c0c041d40d80180d0703030003079041d09480b0481d10058490540880c0e0406242d1074800380180c002c684000c0c44180b02694a01d184214001e008a070303030038a04240450814404c040d8080c002440500042801e0762 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 410176942 1250 410175692 410175707
    0xc030c08011812020a1b080d021911180f160201020705190c0b0d0207060c0507031d01120e012703050d050402030c060a030c090b0f040e0414060702031804180201 71
    0x100c0d104450b0171a074207583e4042494910400c00c0601c40380f6110400c0b0604d4100605c000b1001e0758405424021140c084a550140010f44000c01e0504502b404207265100c80444400005450442d0291800c06e804410704006041d190700e0a4040c651107822002801402105e1001ea840001042032906a40b4229442031084a04072441c494010001620880100c05400d400c0000040180d881c6e2041c5440411189216425006c1c094144000380101ea0002c2010400e1031101d01903040c185124001291441030f04407a20306003501e0070f90301c404440c0d015401032840360350039604040981e20100895902c0d0014920040c00078204020100b40c0d02815005550490f01c00b40032950040074040008030a90488021400042e42e11400e80180c6548800c1120040c000c0003e800d00d8108001c401090794130540c00380b801046410400300c0c2c100101e000c2c0c004004c0c02e00c041030b1215401d10500003500c07540034859030840081c52000051240c60144181401040440e003400c02c0c40c42c0aa005540c0e52 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 410178192 1250 410176942 410176973
    0xc0504230f030f060702010e0d0f030903120e0d03060b030103020904080a020c060729040b1b0c0102190f08060f100309061a01230a030e16030c030c080118 68
    0xd596070100300e803036480070403021990102d400b024020a1038a00c07402800c40e80c41c800451410b0703102c01c072300000098002503007207084841c41c50003080e039048074242034a1501504010991951a01002c8882548085040454440507035002d111160740d840a02403d0300007800060b500104c90b102080c0040c03110300017001c1c09440d81c0140c5400300c00550010703640e0b820925054802c41c640003907040b020404481540c002c120192615000c0c1e05240e10303241007403a00201145442c0c080c1c00e00c84a165111001500d2640400704025940d42c8103031580d442c440c0c4014226600811809281c1002440c0221000c9110300b101a05002e0728644103000c10204803400b40c404400d041e5103607000d41c04103601d401484c24000711008a509215020740004180705800103c818a0b001c5500d90108015281d0080750030f075a01c030386804110120611441418050841422001c0f02003840000040100e151502c0003106d00400c950500d40750b0310503045080e14511011410144000102200026111401d44811 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 410179442 1250 410178192 410178199
    0x10e010506071406040b01090b01050703021203060a0b0c010c0f050a020c0402250b090f0109020a03060c090b0a090503061b0a180f030602120a0c08071b08040909060c050423 76
    0x1000c1036003403644c00e003002603c081e150840b0700b00060100c180c407400307444444c42c02840c081e4604a0ba680b4020340340c152024607204035900000100e9900d030f0724094900003034880103c440360344600ca400024020070041007880003107088107840422641c0544141d0344001c10540242001071024802c100c003d500c83c1e0354001c8880d01c100700101a42102100e0100711920a142005c400d08001201c145000c5c008200c02c0e0711a81003040800043c2c5411050074101c279032000c00461030030700c0e0010941d0f00324201c1d00402400302300407419006459100c1c1e8008112001601928425141d2a84400b46440310500303003100b00d00d040000381c40d0944980710f09108500721080b1070301d201d9250038083c8440c03c415403003035500b00d4001c20400b4044a40c0425070f40c0115115200b00b05406020101400d110310003003803041401082520700b400c07140750290080e0f40c0e80e03011861a50b101d03210850840200720101040e100c15240240c00c1c02158000d00444003a030381d030904540e0400c080343c1e0800c14144184046c1640 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 410180692 1250 410179442 410179463
    0xf011208071502190e06040f0308070c050d1a060306040807080a0e1009061409032e0203041a063a0204090f0318060806040e1c0807020d08010e01050607 67
    0xb03025075480a8070449108071070a6010748034002c002002c0317499010309184907501c1084100302c0803a145002d10222584640c805854600504003d510a082548890b400206401c0e55004015186901d101d181d1030f40c85d01001262520400d240c2d841c64101c1d001403a550040001c400800c40071406814045424034041c004a94071401152032810040502e001084241d2400c1c071100d5084036264842c4285030b00c499050030f042000003540c56074000b81041c5c2d0300b01d44803007061640245401c45116591140029566400c0501d071500034034100d040f0b030410400440000c6985454503012880002d401c4211407104000f800708905840480d030a0450f6100c043c2d09003240060b19240181602c45007c0c85c884005403c0a09010300410300001d50028055034220f005c0c00004d820401041d0040816600024803040a10300301e40b4045040440c1e814000c1d0700c1c0784403064a81c0c002c4080f48a80015800d680481c0c100c440c040d80c160000380103420600d42d65500500803400c010029240d1a4080c0e0103118 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 410181942 1250 410180692 410180723
    0x606010503132301060602010519050c040306020c07140103020c101e150801050108030c061302010516150b0409031b0303090b10030303110f030403030b03120c10050f01120807 77
    0x83d2041100e5040ea0744502c03c0c203203030351249420b1142100400f2580003e011516003000c03198203070100d89401030740c9150389001044541000701e0a88014690002c021507460002081866503106070348500461085e281324100010f502c64000d94031440403540080c01005030480c2c545010700707458a403000f040c6100c804c40040c03030b801078000d0210311240071203c091200e007812440307402d46105810542c0f20f0750042080a140b1a000945031703510403074101c104080701040e4401200d1a200703003420481c1002a111241c020320140c1c402c07004511807412020000d45400b001404142c42240780080d020907682c00070085154508c49401c1034003403007807500003550707030032540c405100810076580d501c2030400c0d03468280201909845440c3c02c002d2720814031030516a004042c00504d1000520050030580ca5896a42a5440800180150b42c81442800d030300c3e0050003040d0740ea1144842e8207204010304041c0450075500d40c41c154681a00c0e146154809010415101d210040d4032241e400c032894209150000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 410183192 1250 410181942 410181953
    0x270a110604031e05010f1113080d0831030f08070e060f0f090a1e0f030804090209040f020d0c080f0402030312070903050a0f0b1803160c050a2411060601050313 70
    0x251481000a0f5501d23205c3c07004045022125800341c104200e2136000000c01190160440007942d400111071281ea000280c0c200a080400300c0c00d83c840161010360680d24404154001001e510300c01c05681d1942155074503401c00b02c80c1c49940b0354050790404010020450052050320007810380203070b01001c5601d00008000401d81040e0154010400808030801f1116107902400002008000040c003950b8541c2c25900c40c044584a144030b203d200c254009002c04594845400040d404184008215140e410200003407002d00748124440c8006503000e00041c41814101003c1d6010340d030060000c0d814401c07440020104040060f01c040c0070b00442000020008608010f0103841c1841079500c2c0012000074500380f1108800509910358288802074022540d100003c291041602104a0b420103036000e070918140da030055820050304600320750b00200388002680c0b04000d415039240c0205030a4401c125088a0f2071740c2c103080304411908500c010990f1980302d07c01441d002080d210902d0380c2c03211540c0c0c80 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 410184442 1250 410183192 410183201
    0x8041211061809010b090a06030b030a02090108010b011101200f07050d0906030b010806180601230304030e06030106020705040b0f100c06051305060a05270a110604031e05010f 77
    0x808440d121980b0080d20900b043c91503a40102040540c0b02d040019480004120300040d01555041503039038802c0d4011030b9810400543e0740354010348040d6040d40c450481901928000c103a1501140043d5070042a0410500c510344030403080c8040000c180b00305522205880d8070003543d500c10010180812000b0500510100f9980f8000703031a001800c510f032120103006d4604400110341406540010040640c43d26100c200d4101c40c4d0200310441c0360348070b43c01a01c03d42c40069000004108060070310200b8061800114055800380e00c03000000810f81c82080598402400f0300d10040e04801c00401c50703410950850f0700e0501004191908109040c13021a000e402c0d5035940d100090481d040f00360601c80709108a5401a825070103058400503240c840c0c56031406d001d41a0000745581c1c80025403e04a801ca110401d4000c06103010040d0000384400d542d903900d03110341555000c00343c150300c600f640b5040c0101c40450b50b100c03401d005003c0000d102640e00d4610a40142d40954a4801c0207085091034400c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 410185692 1250 410184442 410184457
    0x312020a1202030a08010906051c14031b0705060c19030c0f060222080309011404030506010609031a060f010f02010b130212010801050105060924030f220804121106 72
    0x45032600c12002d0024285c500c181d00001382c3c54030744101408a62184440f81d8182104a420b01000f6042c3c2e00e0584e1145690002903000da001c00300e0800320844864800031a480c192100319001e664441041050a01c540b0303041d030402d40d00c03100c2c0995414803000d560070016402810101a4003a00c1c2c0c5031000110055101220304030740c006031207900f00c01031074480b0039250103c83c8003008560421214a030349200d0034882c141881000c1c00102d5002150740c0444000d50b60003810355800c0c1d65502405400d99000340021906d40d040d02100003408028504014071510000700b44035450700140006660f20b0203420000d004554885010038550b496141d00070410110085d40141c2c1c80c030230030301080366803101038010f1040c1d0b9041000401103503569009840b8044401c5405c8082e5144000c1d081107007401034640f0381c05034032011080209441030290000e101d0030301303007c90800c884000c07544c04400d8500813600900200c41440240650401c000f1340760b440c07074440d021101c41002901c0014030701e03820404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 410186942 1250 410185692 410185697
    0x807050303041a090a0b0a151d0711010213050607080c0715030e010b09011a040f0308030f07170a05070513140109050a0e060d02040b10020a1704030305040312020a12 73
    0x24000b22005543e4a6075540300741001e0290034108140d076264403036038001804480d0a20345403250301940007a070f00b0a950082115100c551060821440d031004401d504846480c0415512004400811018001caa14985c00c03099a5086035080030104142034200365025122480207020320b64610200700501c801400114412aa0403440e5000080607549500100c90181e41002203c4a075070302c504034924151250b600c82e1081100c00c286001d007203070056503c40382d00440300841c000180103255000310f000f0310030300210002546d00e43c401698420104420401c6803001e02c80000c41d02443c65110b41c1c1c10031007e19010786000800e054603a40c1d07801c1d0360030100d6164041075110125603007211ba48002040c059030003018041c0341c540c092600b40300080c02103010b00c010785014400c641c1d0b154410603400a005080075480004c0c0e900007035456080d41c03000c43c1c0e0000446480340741c50300c002e0280c504690340350340c52624060441e96009119400c4201103019841000343d81000201040502700c0141c01a9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 410188192 1250 410186942 410186963
    0x4321005090c0111191e0f0b0f0108030306040903092310030501050303040b07020d02130b030d0e0d02040f0e062a090a15090b2709070c030804080705030304 69
    0x4942550602e01501c40700c40c18400c50074802c4840c4440450051a40134070302c440c015140b829401d1100807106100070729031a880c0c0029902c003c21010158034960180660741807907003542d420080303001c005400e02600a10f80e10070700000e04035140c190041080288a460000c10a55464000c603102c4101356501c0004100300c1c0c0b40720800d608004204001c4c030309142c41c0c20f1205500d41408641c0340c0c0304a000f00c060801c000540801551200b481d50340b00c49902034000482101540c440d100201881c2450602c280105070032881c1942c4200100e00c2d001e03d004000e040000016402c200c01841e64855002500fa18ad64100c0d030300107000d00c495071003092410010390040c10200b003540450102104c90020103601801481c0c0d0340d849001544003602e0311003403201440f810500080d00c82c0c84d05544451034502c00010001100401c403110120031441d440025140d07404000d040149820046a51100040103144c2980110703206020707498105000b00c840f07620f090783d1501d40c0d0b41103a10465040d035105446 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 410189442 1250 410188192 410188201
    0x2030c120a06061e0311030a0617010905030306120c060a0e01021005010b120a0b041b1d060904020f0f03040f02010e010804030c031107080703060614010804321005 72
    0x2100310990112041c001004420304005018081c1110030902e41d95041c000302207007038650301039444601035182c03a4815503283d00e0715038101005410301d409207a18031a00c104a020560b0014050714641540c004091070440c0d40b500140078140ca104074038601a4030481d85900202d4071980000c024290303055556036130601c9070701c002920b41070706d039070200e03940f41e107002c00400c040580402969200340164411352200c1e20f8031030308040039090201d2803075409480c1001072115924034140304180780307000d81c4070780e2800b944130058000c02c110b1603016160000400c200300c6c1da492800d41c0c02402c14032891a0900d0600c1c105515000f51604115401c982c0d40d50b9040c130b01400c1d9a0041d5101c14030b001c003440c20321710382c0c0703410760b0000c01004000500501b40888460311803c10481405000302411544048411443d520b050001c0509128801d5030802c14003400401055445102e0b0240f00b960400e09651101000900c0400c89944019021981d1481d01c2c19284500000f0710080500d0b4440c1c1c4008104c6081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 410190692 1250 410189442 410189467
    0x1504050304030606050a060905040f0b120703020112021c0209040207050304030602070b160210090311100207061107200a09050411030601092912160e0105010c030503010320030102030c 81
    0x13a500480d100e14030000b02040f06503841610001070710403c2e02c02041c0024104100c01c003503c510a58180d104003e1900d080072820001200000c681c000d0342c2e004045a42c00200a04a220ba0500d00529446c40d141d01619141250010302800802400040c40d1087e1516102d040d900039800464486800080c0441404003550340150044280001e0030506c01507880040c1d541d8110741da050030241d850350103140034140200400000c0d0340d04881a180411100c0480304000d6104d850100d0b665858040c1040384050007001b541c0005070700400f100d0030710030348010800401040f0b100a40c2d112589840c089810f00342d5005440c0103512510654064900380801c044c03e1080517004541180d103001401110100b200c1c29030394800400215804041a468001c0f03042407010721702d040d049100e840d220200d40841b4180715412524980803045281c0d0f25078004403003183c0e480c6400707030010b9000e20061022a449500041402c41421123000d0400c030300c50007190030781c0c00c200d44000380081d011a50360501d11 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 410191942 1250 410190692 410190701
    0x901020d110703080423031f0f0b030613050f0d020601030f151506021519020d0906050408091203090109031719030c020d031506081801050f01030c090912080915040503040306 77
    0x42240540284420303980303210380313400d248002100c0b0036271140c0340c00703020800946c08006d101d107024003501c1852504442c02850751034620012140342c8101c1c40c40c0a1000b001090805071142654050020741e403035a1140e01028601c03180c183c514442c10200954043c42038801d440e00620724008080040c1e2a1080181c2400c04041d0800c0101c00040e04018000110702c0744c1114811103028011303124030380d58075103030000c008003000240900d1401080c4010b01819401620702c007542102c002d01044028140300340c80303002d003080460206010031001c0c00000c18000d440d400104058a0301400c0252003101c0301506083da84650300032030703503458150340000c6c1e041c841034084010324141448403403032603015034500ba61240301d40f004100911000c6035065000f1302c001e40c190081440248928101040c0c00c2c20700540a03c0200c89121042c5c40000e259031150140c88481d030b4000316810041540d0b0002505d091500409203041ca000e0f00f0044619028000021805103000f0001140c49600b145803020455 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 410193192 1250 410191942 410192009
    0x50c0a050d1d0a1503090b1801051e1603090206031f090c0512071407051c0c030c0b0c040909030503060319080f0a180303170a020901020d1107030804 66
    0x540c82000091501c3d10940710b401c40d04d41c0c58408108801401003240140303035039a401044a09020144050070244003060f94200d511800204042c1e1a400308101c0d080100e00409407503400300d00d0001d01c43d0041108260400c078490704010407540043c3e030008100d503000716460401c1f0039031000b240343c40c0c50b00301c040344015040c1c0080411048150341e602404078010050380394211001040081d445c28840c2c0f501e0001c0c2c181e003c82d0180c441c202e52800e5034440e42040524014005030400c400d03451486100c48030400398141d2a080301014844d11404120300f00188601c8905004100000351580103129900b1b10354020765900f9143d003030000401d070a0111002d1500e0303441515600d400301040b1200203d17040c1d103049201555507580382c01c2c016903078140740c00d004035211550302d5800010300d50041c04106c0c2c00e4040c504641d5250fa5401c10620880c011000114011781c0705074520902a40180388001e5a15556002c5a883c1d5580b0780d500b004641c0036801000c9a5001d00c00c0009001060f2000749985 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 410194442 1250 410193192 410193227
    0x1b080601020c0f04240f031a061804050c060c03040906051017090106081b040507031103010b16020306090c0117010b030703091110090f05041812050c0a050d 69
    0x42c03020701c0c000030462002020b24070302c260341d14030000d8520301041d80d08403205100006500d4a60b0f560f0800c01607492010b1006449140f034010300c85410150207002907200e120002c0601456200300b915511521400520031105441400d00c2014079075650341c05804400e0b0b141008540d61424904c407230094031034980c012802001110900c009050f000f0030403110442032100742d001d956907230b061510b014003481ea00501840c00303900b803403e018a403071490011400d201921306011075240c062089045800100c0c040000030301c01d00040c80085240002049100088041d04070300490640000b82040c0d800d0700c000d2070702d500142c1c00e1140c03540c0254410007400149038251055602d00113000c105440010300ca08201f5942c0c040701c03002c109985c1040d0700c4c0d001016203821000d84072800c015050305d030980507588800c1c0d90f200000a01e0300d01402654060144480c2c07640007500d0907594054580c0140c1c00b80c0090120601164405120070000c2250701405072000f4a007001503403034050258044c03400d03007170b00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 410195692 1250 410194442 410194453
    0xa08030a0e030c030a1b0b0406200903120901031103010803030103030207050907020303161407120801081603021912150507030b030a14120c0105090705030109020913080d1b08060102 80
    0x101c11404000c1e074084040c1820506c81c2ca500a08403400e005c0c40c40a401400c8031300d01c0c0c080c0420b01050b640f110466019a446004613846501d81d02400c5005600300e199045d8401b5554542001040d8050542c0400606021505640340141040f5a030001d81150001e42d01c00300040040c1036040064030010003003030364199900d0a011200031748078400207159083d03ca40d0301011545051041c14000d00040426149507243c1d02c40d482c040c05020441211a0300140b0001c1c004104a840400e2180c4c8840007041c00308100ca1855083c4252100300306400340790600d140d400050140c0244981d04c8051784121414802c1c590803d142c402110320246c01f2000309850400301c4071181e100081c02c401c0003074101b030404e508203c0c04501c075464043c0c07c1503840303c2e401c00494404400403054001d640598107850545512079241c8060500b2036154480103548162a840801c4911034558a20030b015806441c21500e000d80140c01003007907420b581d2000039115080c1d00082c1c00c40380d103ca07109810960900c06031a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 410196942 1250 410195692 410195707
    0x906062319051509060415080f0f0c1b010f020a02060108011107081204020f060406090f090e0c060c010b0306070c030e180619080105101d06090703090809030a08030a0e03 75
    0x400207103440f9100d035002c2400141c289025600c09040d14020000105000c0103086040b6005015880c283c03104003002034008045201d0f681ca0150f464414828003241a09115881900200c0d5040b007007940180c5550300c0d0000d99400320940000c01040e0000c0d00104000d5240c14245400c581a445480040210a01c200000101d4a00c00c80348400324800d5040856200ca0001440807262110841d41c00200001c000404580003882c050480d4140d0004102450b60380c0c2d000001d079000640751055607080f182d50700c0c40724500b4401500703010410100005584265002003071030702c0c0f002d03185607010480c000c00c1a002c15601c88002c9400da01c041d10038014003a9142484428401c01404052056881130440c0320070f4442403100790700520740f00009014500385000c40c400d050b01503000342031040001d01c281c440c081e062258020302806000e41040f20907502d041c0d084005208540c401c031503015040060301c0710b03680c08005202c04580503007078295070790400f60809400c9803200b07080310400f50014031218 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 410198192 1250 410196942 410196949
    0x7020309030a0201050315091614070809010f02030d05010b09040b01210c0e0a120506060a120b0402060d2c19060504080702090a02030601030c080613090606231905 72
    0x2500c040343d081c01c029403691184059650118840031019811440d03035030800102d55203101501c2d08071035407512028107620381e40107441d0302d81c450b0f1900500158030400c000d014a5214070180c0c40c0c0b0480e0b91040ea0b00346103400756500b0a8034820392000b40007003008104100d40e40740501c90090411070034280360800308072981c11582000d601d0351641ca030207035a40349007048560040365900c01e0900c00030419000d440e111400e56180d0303100d980b800d6a01d4412900019282e00380f001011041c0e45140d401654110301079a184022141c0c020012604a1002d1040020302c2c0700c6800355100808001000c6024484a402c0003141810081c0300c9801e00d030f1200349014a0840c40b05078001f0356a402c42008503035a40e4038249882c241c0300d200402500720b00b500c0d08000d181c1c0d0aa42c045c41c0114000d9a00740031040041108881c02c00307041d201c283d8880c518482120300d40080d1360000217040d00ca0100410595070301c0d075042210101d50806850220000340d481032007442c10141404100b28030700c25800d140da0178407012 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 410199442 1250 410198192 410198203
    0x406080609061f151202041706090c0405010b03180307080712080624090d1e14070b03011203021e0c03010609140105150d05040c03050c01080f070302070c150c05060702030903 77
    0x60707005000700100030b1440b101d40342c0c041f83c02070100c1e5118889400c1024468075540e0380100c410203200c0c081c6040003481c074905406800d04a440140c00c42d810340d12200f0b0b00a4100d460300151540300e00c410041c0400050140c40606503107400703560075849060030340c200a0300d05070300101003a108035484800084405240008640e045400420054a03403100320003042030450a904041d00341955100d501d0607540251041d54801449003981031000f1040c00040c0790360b005240500c4681c3d0b44140014440320040c0c01c2d03000c800e5030007407040303038650002213100007005000340303000054940103000a0300050909005480040c68544420130501c0c141d50302005041206015030380c85111021030448041c0f400d13906642506111902c1002141003070325103818489100d110413101d030302910ba1860300703640c02119410312a081041d110102030b41c1d101422802903000c8070003110b241424540200f581c1c040403030a0120840c050302c4180c208c3c035690410500c0e00000504540840d40200545105602d0200c0c5c07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 410200692 1250 410199442 410199479
    0x3030809060c0a270f080d020109050303010e0703140c09180105030c060309030d020307030504170a080103060e0f07090507230703050307030b060711150a050f03060406080609061f 79
    0x400c41d4039101c808915031091341542400892490941d8000b040b62a100c40059007124500000c0325040402c65030240d0990300d41c104c0c06041c0d504148010001c00080c14802540140e107403500003100341982c1268506004291000503514002040000d1241440045240381c1460a44450b8040d898000080e96034810842c0c680d0240d00e020010400c3c05204000b9500701404c1f8820641d124031f00381a0080080104481c262000d4090305031482c84030712410200d81483c4066520070303002d45e003952282e10140042400800b002d00c542c56041040c044244030400240104c0000030400f400c0410000f041ca240a02c0101400f1508400f9865007986803011101e080e1381c1400c0c00b07503d030341e20500c050f40200041500150899000207032201044500c041114484804a403807443d48004010380b45a1405200c11040105104000c0d0079000c180b00c0c400b540d07000000a2000c2a44c5445c1c50409003000001c1d105524136512840a000d01207944800400e8400c010f000360518440c6800340c0c40d5021001400d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 410201942 1250 410200692 410200697
    0x10030308181c26180c03070303081e04030e090705040801090f02180603031806040906081011040501020c010c1704030b010e1b09100309051903020f030c070509091609050103030809060c0a 82
    0x140c6100d03120a1000c000f9074040282940d4000c1c8c0d4a08000d84103800449540700c4400d03582054425640f42d55045030701607070b0907549401d084030511042c446104005003e010520106000000e1403180900a4251091049000c8071040d42a40705110221841e42d1070218202c0581041052545000003030781c2c9d141b207840107540c0c00110000041400d40c0300d5034029800c49400d14502061844000035681254000034000300302003000440200c003503004a005013401a003100f082001207621032031000c09014000c9403000c002880c0c0340940351a40d40541e1084450201035001089007981044043c0e90003145c149041c52000c003038040805c0c452103480c0d420703403144030750320140c0c0e4819100e80d000f040044c4e441030444004e00909614000c0d0103224110407001841621011902640084161101c03441054003c00b2800e080008200b84007800030b010042038802c81e502015000c0080000c03400424030304c4000106135045040c000c0041600803d030358900d43c0504180031075008001d040318581d25151 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 410203192 1250 410201942 410201971
    0x1021006060e15090612060f040903091526010512010e120304050f010f0209190302060405012d0f09050f01090302040b0f04090501050105040e0610030308181c26 71
    0x82643c014034001c9940e42500b00310003040840d8000d4045c40c0742d9002c0d0200329a401c0340728558030704102c00c0d1110380708001c0004d8028a02002900402032000c181b502003410480c1d02145910f04001c5403a286a1010040740316501c010000303401c1c072804003002010080000d10044840302251503403040358240303072030305440b0000000d01800000e204100a010000c0005e0120014001214010f074100c10310182c85046980c2e0644100349040c580701d01245d501030003007404c0525010040d55440180404c000e18004000c3c0d241d01d103519503c45081540f01103864851400402c6000146184546d4111602600c803100460299a800403210803ca0740d0403900820061410800704802d0400600840d4005003004401d201304403064200d41e05a47d02660204040c040c00d11800b5607500e010f0310400080e1900510500c0424490010550300003080d8a094600400c440364552803d44480070307039000005c51121070940c8a510031501c12042c00c240245a24540060305120302808000d0a100145501c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 410204442 1250 410203192 410203219
    0xf0b0708070c05071a2715041a03060402070b0f0a0507030c080a0c050f070807140606090403180f0902030a0605010e03120d090f0804091b0c030e12010e030901021006060e 75
    0x41800f25005041c1d032a104580e280f03011a0201c11412502ca001ba203c1c2066850902c11004140151400c403008542601c0c11081404510009503002501e001d810070340802010300030030800c0c500c036401a01c102950002c1440c1c0070441c0d004540021707000100300b5003484140100b2940c04a10143c00901e1007038000344150800030280d582c0c0c420392551034250300000c60b80d003040c0201030006d0301400380950307004c14840940815040d03c5000032a100c1c4d92040c10700000c5404a40301d800c505080354403070f82840249a89501742c01c0001d00752680940600ca070004200700e11440307503010780b400500081c2450103100020313000080d11000c1d40c4004a0b211640401c0c2042c8103046034001080d0b02c1d401c064215048903603810040c1c1194418012501601d0401c002c546104000c0080d14904031001c2c1e894203421100c55508171070003598803128541c8150342c03000d0944030302402e120f1074610103405d0005642c0c0d09034902c000390800081c04281c54065280c85000c000003500004034100d25501101c012030030386603 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 410205692 1250 410204442 410204489
    0x30c05070209010b09180709050a05060910050304080403051903020c040e0712050319050a11070f050904050102190201060f080307020901090e0f070608040309051c0206030901090f0b0708070c0507 86
    0x180040e0000d80c0d0f40c1500b81308507e60044588000e41e00190341c0061195104e905004141c402e0304803054000460310707100380303545200e00e0240d5046849070721620f01d465039070303114603150550103813180c8604050504004105901001540200402a20300303101d044494411561600c001380300784009880f80c0103000041040034000c8511013100981c0d0f00c1e104020301200100250092a81c150114410b102540600d81c00001c0000844080344400c44401d4100014003496840c00ba00454141d03400b07202c1d018102d03041060384207900e000360f4000203a180c40c00f44182c0000c2d15540c4540d1203600104140e0015888804c2c600341503880c00c42c000b02c3c940c4400c251284c60909812149030040c0291100440c032a43d21408175402a4000c0da5201c0d50143c4400811540b070704110f60b04c0f05081198a2100d0041c01d065000d194007140744800000d00200139162280ca60507030b1401142c0070700e00c480400a0143d000491103070868454685501003034103d81d15181e4912041c06054012480007821030341a45 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 410206942 1250 410205692 410205709
    0x90903080c090a12150509070e0411010c050102070f021c0809190803130306110c0a0312021e09090a090b040f050321100b0c03250203010912030c05070209010b09 71
    0x1250400d8010201d0b070f402e0104803100c283c0f901900490078200484c7c0104000510b88040c1c030a540f4483c045034550390349503c25108e180d001c5034140080b451103040819820702c00362107074902600c1001e04084c1b0610401260f9003a601c140c1c80405024003404c03002c11010740a444555100755440254864001e280314001c0c040d07903000040c00d101c001514805014070010388007c41e8803e03107051041040e00c08001446010780c1c1d0359004c8580c0324984990200b4810812420425140000145400081c074800c0b4110f150740c0588030302d20070380000c40e070240f4100808003039407100e0007580030000c6100590314802e000c507004d44042e045150111000c07090140a0040304c0c0318031828030700910115900340307070a489400100c450b00c82c11150040c0000c2c050181c1d00132a0001d017070980c0513503c4c220700308100714104886141c040440d400c0e090140001a10240700b4100d038140145200c0400284070341c3c00800b9100c50000d46010407005004400050302d920724958152001c2c4007545803115506404520f809 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 410208192 1250 410206942 410206949
    0xb090a020d1202060a05070e04020a090510050414190512010f14160915050d0e0d0504050a0f0503030414030102131707050423040206070c090204050406090903080c090a 74
    0x810841d480002c01c1485444901802c0480c0c0a0b61120b960303034402c1ca01101c1003203420b42d001c80d1009444c0520341c40c003079000f01285652410714441c0180c58001142049a05e1241140030580002c0c0a000d0b02d8148801c01c602c2c010110349070f4021208182e45040007400c544a040e004084100c041090b5035820342101000e02d5046d20200078000908010484184050300d01c1d203250681010001442442583e281040c1ca00910410708c070b0308444c40003228558802c0e80c5c842c000950f14502c12945800a01003841d0445980c0c1d07c5c2c3d6140c600f440c040004421440d4499888020310f030710208034588020003074030215000c2e07003624820038014101181c0a032240201140c0d61492992000c100001d8a40c03074100c0d00d02c110003c0341c40301074980c018082200d030001d0b4400c40c8402c141021100c03030544005403640c082d1000d4046810f1a989a8404d941d003c22a0030411120380c000c0340a000c0e909041c460b080c01080501001e01081c0c9071038402400b902c9010380a4504001d000030303130170442d40315090b026004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 410209442 1250 410208192 410208199
    0x71a0a0c1a070309020f0913030809010b030304080706112107030c0209040c090e0c0904060b0303040e16020115061b0602090d060b1c0b070c0312180c0e01120b090a02 73
    0xd0780b411030700080c020a8039000481c800d030484002c0240a00b011000300348507005860342603c122300c0c1600c00392502080100b000c8041c0d901e84038004000e443c28005000102814070040003c14188a400b6204041003080e140e03095005050084114205040c810910344d84602c080780e07030f041542003c0b1621154880003a400500c0e1a041c0700400581c030b241182100c904400402000040c0400251601d0840010782d038004810400304000c903049600121511100a04691030f099669180303030403c410840300496400640304842d0b00e0b0580a020315403415000e848000d00c854100440900341e151030450015120500410020401c2038a41c11107007003000040c034400c0030381c1d804d03e40400074103a0504041c0c040c50406180001c1d03d0f8080c85148005640310412040540e00c81c1001c035070310510100c081e810062104030000c001c030120310542900040001c5030000294060520030181041903100004549004004003d5801c203680880c1d401603000d02d00c001280c444003419840e020030098003039030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 410210692 1250 410209442 410209493
    0x60501140a270c021e0712080c010617030a02070602120f1321031d0307050105161a04030e010f0e04020901020304032001231902030705010617071a0a0c 67
    0x70f00503000548440c0160f002c001d19407010719508072058450902d841803407030034010411442c00041d4180c01415801c10640000281c4954600288184000440320300c3c1560700000b50703c400030303941405454083e0a442c0004c10281c1c80900d00d842d150b10400200c03064415010400d000c9004800c42d06030000c0030013810111107a00004100d0809001c145401c40204240014850303411a1184070f517441008000c000e058220300c2e001c010b42d50b03a840b80414800443c42c1d000c02d00c00040085901c0c0682d0203944c2c0884040e40307040d180140809000445540c140b22520044240d1507602075400006c02c030042e50050b89400c4081c0041c0d186000d01c1e00300800c004650750009000c5080503400070884070099859454454520010315075000182018095040e420080b0401c48440c40000c0000107034584101ca1420f0300e151a4682144c04035004101c0700c004205000301c4401007008150003501e4146106241c0045e07507441071815100301c461000600142c500c443d01406042c0e075280d0551307411401a4074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 410211942 1250 410210692 410210711
    0x50121140c0a0207050a180c0c0c0305010c09061e0e0a080105040605070e270c040e0709080c0f03070e07110f0c03070909120e0a0918060501140a27 65
    0x840a03000000c2c0540140304149001a8500d4404070b0002190400031f401d0580246001e080360140c40050b9140303081c000c8010b400d1002441c19541900214064400050410231911000380400d01da540220100304420703030312107802041c00e00540d020000c01d0405507496148000414801c214135072000b0340552800c4200028031034150456841000a40c4d120b520100881c0200030035520014411002c80b0014000da140388040f034810aa00a0040b200c01ca040a5468007101100354044442c0c00010702c1c144420070441d8001c00801c044804100c070082260420100800c0d82c500b01803003404082410791000ca00c2c91402a0307a80350144038034906482007501c88451595842a0511141d4002d00c204070000800d100e840c8240714659074031003001d1031600303c200320803190703c403501c682c032a44003695010008080c1014410300f040740882854101d941603050404200b101e02c164801c40d8240d0740040c03003100d07d81d2035580b03a80030b40700c02e80d83d0f10304125032002e8814840d081c28202a0295417070100c000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 410213192 1250 410211942 410211961
    0x10b1207090e0303010305060a0f0b0d0516140f0105090d0c06020f060912120703060b03090c01080603060f04020105030c07052e060b0414040b0603010f150905012114 73
    0x28140d407801001071003210240354006680340b03c00d20002c0c10540242020030300e65140d0b9040240c000046500c081220b05494001588101c410482120554401c0c9810441a41d814491078014100204407001ea0b01050011484605211a507103041010000301e0108950312409403158158200480c0810b2586030764010f90b403911034550140300782c41207200082c2c20b11000102c0714003054086050300c1c1008415007075100e5001c0060f080505158659801003501440d50000e581f0410012004081c3e1002d8100058102c1f0346c05401140a03400031410068584580d11040d50815420f01e06031780e4955880056056038017800e1002090350060888001841801e410b2441c0000c03228075820012104014014046613070038850b903c0703210003c8c001088240c400340c8e0082885003000e0b1001c100307205184006402c41e4400d0300448100c490440c030a0180030703006121010019a5400e00c041c0c054204000a0204691144050320000b04040d180007659003540004d4610010030902007070904105042c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 410214442 1250 410213192 410213203
    0x504050303100b07021e120a0302160b040e0c0a0909110a1101090506010e1009060b0c0c030304030305120c07020306040b06272403030708070201140703051605010b12 73
    0x100d10542c82040004201103030307a101101d0107140e0040030401d0880a40b0074421000b01c508408640c09100b070f85880040c444240a19030a4601c61307400303400e03c200112070020f06210b058202c1c886000c024801031149262481c009500301d21096100b54660681034000c441120712a000080312034100350183e010303403410a001d0400b0024035145c4001126041c0302050072502203140103040f070360005004112040003030500b1030300301c00c10a1030344000740e0311051400140e80d41907201d600400780020301c140b0411030620228200c030a040b03014500c4d06265880003401c50103075503a03142483c003582000c12030910350b010031115070720350140035a8214034040c1000c512013501110258022411010491803002a80e402042e10030b4000c000540d183d113601c11104030f480c1d81c1c45204110010302040e40707911698104050504580700d0f5064580da00c44d03910005000d45040e594100c2401400c4c80103d00280d0402e0649070b1a162032298030141c07a5117814040e000d0055280c009402032800f00f066070a80c07501060 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 410215692 1250 410214442 410214451
    0x1008030f0702040b0f1e1c050c13022b02041502150a0608100506190b0d0f02040f06120f0507091403071d07020a080a110c0306070e0607080d0504050303 67
    0x1c00f08041c0c0c81260034080301380c5040348401da2241c0003280c4104011010686e05050b0b95024110f00c00840201c6d500b003141d01c4545000340c40301d5100c020b5010076468541191034000d5510f500c158141540e02d1805520b0318038983d88010042d0015850351303d000203560590b001000040051b442145012001a488840d48061030260000860000d5050001806407600311003c080040a4081035085200010a4090401d0f03a10501094407141c0401200e240e8101030702000448541d80c50b01201038008481d94040501d07013590051004000c03110720700d001a0201e80c2281041010282100e9030040100070040904011a10748802c2c409140d900c0700880081e11012400300d01140d104904050381c0360218403600c240d05455100c881c01680f0a2100ea80e00703c1401d00455216411694592503240c0281d440031000806c1c01a4000003900104405005010160087c2c1660b04000c00c008040d9103070808014001d40e0001000320401003040c0894005220100042086061626166490386d01c180d6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 410216942 1250 410215692 410215699
    0x1b10020d2a0624050a0501140d020309280f0201111f0501050112050417160605010b1c0c0903060c090b180909061009050705121e1b0708031008030f0702 67
    0x3c02202c0c006110302c621050350402821501203510348801158881d1a103a00c0812400003480301046504583c0007940c05500c0060152040659141c8841c1c9007000c01041c0c0716066034105140404103030845504d444140c0c084c038161003038203040c0b101903240c500c1e4000d20701d05140411003d200e42100650105050300d409a8070007036040044c0280d8820703101d0594014050380400008180e80d10504001059105001030040343e420f00c4540701d4030111002607010610048001902c3c0315115010f1070b4003d01041b42c920104000d01005e43d00800e464001d000052440380c1c0c801c40e103c003071400780040700d00400c01541c015543e030641c800c0c000040c01c0382c0b41c5107030300848448010410140c03010950b144a0400e03203a804207164503102410b00030f0310300a020035081c003500f0068100643c00314544caa10454500003000c040004103c5800e05054008240c07030380e50066403404c0f1131000c01e120111258950000140d40d22922900303402e100052003075004049501c4000b500540c0001c0070805040c0b000c0c0200c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 410218192 1250 410216942 410216981
    0xe060f0907090903050f07050a050a050a0c0b0c06060906030102041a0c06091908090a09061d1005030a060b120706120c0801031104091505091b10020d2a06 68
    0x9510300400c3da080e0b600000d0119005003e500c4032204000060542c807030266040f0781c8041810b46403541444e19800f030a448070f400c5440f090302400440002c6000604101e07d841d450101c41c0c0c0003068440c6006015540b04141907404a251070340c0c2501030724080c001501c1c101d043ca4144c2d03e600d04480e4440100c84959004980020b03c81da41d012a010701d0125014080c01e00a02195035081a16404803c1c00340d84030650b00800304400c14070b4450000a0200e107140c0d61050442105a43c403898802011011000f82d1010140b1540d200801c0c900e046961000000c902000d40a0005040c00078144020a0600c62404005091781d4170800220040c0070440c4100001d88800b0f80440d12002c00b4040a417044116000b95011b5041960000802034080c201410b4844440500070003600e40070b0f141c0341419071040b20f4001000c0b142e20704c2000c03a03460440b0346140b00307190b070840651074409240c000000d00c1503000c5400e01050644640e202c0d40310a50303a200308110034034a4510000c088200318140c07665400d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 410219442 1250 410218192 410218199
    0x20913200a0303200111041d0103050c1e1003021b0705010e130222050f06031902070221060103030311030702070306020c03040b0d09021c0c06030b040e060f0907 71
    0x88021800100380640907000260071514251000c0d0010a940041d101c000d80c0115403403403080c41041250200c1000050352245003240c4204440c070b543c1080c15034444c01400400000364005489655540191070841603000c0c5101075840d0302c451107082d10740064010301c00c88c40c0d059259008080408501c50003182d010701100d55155220315030701400d030106201200301c1080d407030081d13203003100c045038148050724000803544500120804045403a2001d40700240a20152400e502180c66590703055681c503081d031174001142e44a8480d10358040d11000d500094036415511038100648000c2244d800108121042030003050750303107200b44401d8000a1a11b20403100b07120810040303a000306039903030040c4112400d54403210000e50100002e01e41c10b2004010001c0c0800703102014102da1481c1d8140010b203103c07540144820440703461003100301821020314000000740801c0880c8151450f9107400911030701d0300800724008140e158400400c0f03100b00b10400c5801e6104a02c0b16110396058015142c03000d55 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 410220692 1250 410219442 410219483
    0xf03032205030306040b0a1211010305010816120302010e030f030103110405010501020307110418031205060103180602030705070b01090e0d050c03070b0411090106082a04060c020d020913 82
    0x40345001041a0010408501d4510b03003904000c00300a001410640456610701d500740e05409069401c441e16800701107030303000541e0140719940c0104550310142c10888c1c01003503220742e41542c6000d02e40c0a48610200d540034941f00b5404026080e1274201129520324405140012541003444202e6541400040c01a46420103000c0c00e41203c0c2c0c1a0011401e081340c5603203105055080894031a0003030340c0d41c0381103507680ea003d610451102c0c1c020303264182e0344040d80510000f80c0e0fa00502442c1814105010071103c3e00000e00e07040b0845801c4100107032070780c859078404c42d103901c14000040c1450405c900081160701107540144000104607044402140403c00e00355101c3c09049072900d520b030020302034070012aa42c1e40e0b007203074080e100b05100b200511914000840b5820280c20180029020004114031810b02c81c0a64003801724078110500b2005000368400c42d0b0380b269010320010003081101140440d1079006649100a500070092806442c0051802030380450000f8283d035904c05242d6084e18500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 410221942 1250 410220692 410220751
    0x709020f0408012405091e01140f0a06050a12060e100e0a0b0f0f03010207050a0507080d0801030c14120a060f0c0e0904021c050303070c0c061d1009080f0303 69
    0x7181e144c524900140703014100702200000409807030703242c00905c55000f0b0480303000b8016400f801c03407034105000d140d083c4400d00c40403440340076a49000c1c550f81c03c400c1c8140e40e00042034500b04c205902e00410344542003020080580a16404146818007000a0084403401c1c40751000c15070302d008000080c99520680e03400282d5005105582c0c114080445002040c105018140c510102c00780015140c0f400e039036a142e242280e078203401d8800b50001c0400f400520400e1014610340656451321070342d01e50464071100080700d524400c0120900f00c40d10040080d803605280040a00c080400b683c0e1490f21a052403006403458111940c20649010800306800d40191200418084068000b8865a0795603092000c1c1c21240980840c0b2450050040300004504200031480380741c1a035200103a0301d90525003003c9406142d084841800382d00c0800360424100c5454480900d6411980c00203c0da01d9442c050301e1040d02d036044003034a0b015160781106d02c13080000080d401100907002c80004201040201b88103c0d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 410223192 1250 410221942 410221991
    0xc060f0a1a0d021002071215060605031b0d0b1306060306080f10051b040f0f14010516080d0204081507021207060506010e0a06030b01120501050102070302120709020f040801 76
    0x3080b50010009810101281040c200413401140d240e00c0e19000e0718100e0715001c0404441501c0d08048134071038142316004440c000d260701d0800a042d401d200c80070f00302040a0a640a207a242c0100d402020412207800402c1c3d120006042221460081720091300500214016580070034101000000c031200300003150910301e00c125021348180307948928400d0103444040d0140702103080c28180400502001d80c0101700130a0928400c003892450400c0903035501c3d203568800d01060340791415030026039801000712404130300041041a48040280381c104414010059001d4405201050206411000180b41400c03c11903001036600ca070f5030316004981e1041c4000b080d078080701e824022100051150303000250070401c141802c510310310302d0070041440c800f000d50109000a880c0d18403610196000050400300158000c0144440d41c140300003c0d507900103a120090240c4510407886603a100b09024110103800ca54200355650000c4440d6003d480e0000d005032062941380c8400306080300c4418147c0c480d503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 410224442 1250 410223192 410223199
    0x4060c02060108030a0c061b1d01090b18040e010f090204110f0f1602101d0d02060405011d060c01060521060c0a0c0615090f05010e010306020f0c060f0a1a 68
    0x2454443c0104683c43d00840e46c1c2150a151109924106602010f000003024485541c60f04151800820610400b40007405403d06101e80d00d071061200300700c07001c1101c5e600201d000c81c4254008907000440e00505540380c20061952908401030440e004607009a2510b5008403810b02c404038a16908807040d10a03c035204070038400411142040b050502d0190139400300607032090716941d20342d07000f083c40c21101c13003140c4c40010b01101000d0000c820b12100ba1402c4e00041d10182c0d02c01e0f065030f01086040c4541d0007084d050082481082c0c034800d47c3c0038810380c101b010142c0100c1e2614a0500005d010305401c6c014140b00d01c085460041c0e2110100015949400d4180700414060b110041a00c95592041009504221034880000f02051807030042d1100c0d040120f6103d59218a0051070900300d070352300e030b54103d1f40d80c2c1848010000982e200e0071660541e90400c0f4016682c0c2d0300900a801d05100e5000b04010500408082041180409003a24030615078500107104000c100d03000125100040012181e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 410225692 1250 410224442 410224447
    0x5070302030913021b1f091b0303051e180105130306060306140108060408030f06010e091f09020c070e0a0603050a0501051603022106030f030d0207022112070206070602040e04060c0206010803 84
    0x2101d141d590040c404041c01821000723000c01c0a42407440c0350600d1600290081000041c00880e40c82440000c21600c880440741c0c10300b0101050440c00c540d5501d0907641e0b040100201340300640c42448a40341c4000c6900000c00c10020b9900d2400350003034110005036600c800845000090803400200d4200e00c04c55000345820710319501d0b03d0749200c40c11409002281004000701e5450810340710403100e0340c09200214000d410f0101951400302d100003440d000b080080c3d006010700d040e84000002d8032015901c880c0541641c1d035586500d141c0041c0102d90000e0050b105d0b441c3c080060000660000740940c210048800c0c00400c648015001d900c00d40b00d040300c03a424299003400c4211149130391250081001801e6900c4d10916036141460364102c00d400020440e4005159401c500e040d21611790710780c9049403082c0a07410440602c540350608082d425022440000f03020301195125021100e6070360b0b0044086480d15201c030b00703001c4d84013401c94084540f1803802d006542c48c203000099840c100d4002c00003c52 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 410226942 1250 410225692 410225743
    0x11090108011515020c220506300c030102070c08070504020315060d11030907050a1d061507050304090203010314060f06061b01061706070f0e0105070302030913021b 72
    0x10341403c48403100340214000e0a02152240c0e988111814003030006520744112410043c1c1404200c1d103000e000d4503c101d0206500c001c100020600342c0118100207411202442c0c840340c192420040031601c44d607450751001030030004000d20284002e080d1100304048440701a203440034402284401d64883c1654041c1c0c100383c06140c0303481d0004144080040c0b070003161030700f680d1140c80ca8a030010b9440380c0c250f400c900c0040c0000e080c0080034800800403c40d40070150364000d825010090310181070030b402101504d86082c80340201c2002c40780d0050340442104d5a45903150142c0b4001e40085c003003101c1e84c503800d440a2628140c0002c44c58040c084140d031541868441d0b02c20000103074400301d60300140702058269840e162801f031090000400f080d051901002407000203c0307040a900400c0142030203041c0c4042c00c03400c1c0d4041d10703038a000340c800c0c00c0142e9914140e041c1031f40b542c05a0060b55900451441c002c0c000d02c01c3c0c2c0d8001d40303000e1032401e000c0d40011560910480d1070386101160310148145401145 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 410228192 1250 410226942 410226959
    0x902030606280f030207020f09040c03051606030b0f030d0509010c02090903090f012a0606030602161112030322141b040501050f04091509110901080115 67
    0x210342280000380010302e45008650122040400d4400302c89200050b2104000010341000740307480c81031900d02e01140740400a80c00540a0182110003d004149820000d42001282403c006c081c40d01b2104803560820040640c0144115600854000a003450081d016034180008a12a0b82e07400070301400d50440c04a40c2154540c124802c030310304001c01c88203464056282d5040345402031a0031805960b6490700b02040c46034106150039118100601c0c40d0b18200c98140050955120440d00d04000841c40c0c040c1c14800050300305a0009001c0303a200003000b000c5946c514180d4140540701300000402980c1010420180d00b0010b800e821a03030f00f0402c0000c0701c10074082c440b4410480810300e0840c0c0c0302281e0303d58103600240c05451602c0c070303484886075084154840d04030a02060342100c0a0109604140109121914259072140a03503210f400d11000c0200c501c103186882c2d4410042000314042c10300b09100030054480741c05008000001c00441c0e900b0301030160105c818541842c1c1d154140c03510040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 410229442 1250 410228192 410228197
    0x3040315051509160e031e030405240403110607150504171801050c120301150e041a13060806090a022b0213090605040822030308150301060503070303050309060c070c0902 75
    0x568940942c0c1c508201001c1f001178038504213950a07000b90348841c14142804681109400c20700300d00b038034a841c66500d40d06402c08840503039500540c158910b10725500424401c1c09100f00080150441124200220800d98800351145014800c039140340e03200350407809070a105140c102c40710700325000204400740d40600028100c01c403600e02141c104c6800c10461a81e00d0300203170440031000a41c80410031003aa8080403c60a001e01102c0401481940d6120720300340900b00b5040c035001d641e00301640c84103c1400e90040c0d0017003801d902034540925100c15401c0c0c40700031055080b13120324108c941c800c0042d03245c480c015003e040c11800d107000014880c0c00f00026003000345011042d0b2034940d1450000502940100e40c02540700e200b40544641d080c103501e0280b1324941b03818880350910a002040407a501c200f0240e0000000b0001c11083c100040100e805003d041d004a609442880d20000405034408020341c443c4507081c09450303480c1c0310f003100e01409200b5004042c1100d1900307030062001e400140d00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 410230692 1250 410229442 410229467
    0xd0902010207050301090812091f09031e0201050702010c080907140d0516061d0a09050a0e0f0f0c01170a1d0d020c0a080703020a030b090304031505150916 68
    0x40b100c0d001e40d103000180c00e4520310315040b40c001c04c0c00710b00d22001f150000f00d019000300342c20f806044090b5007042c418802c00801c42c0c8000a140d21043e900c01810702440c185105c40c044105665410182900040d018110540e11800158038250103d682c003441076400c0d6000340e50f0b01d00a0320543d86086c50101100510400c602da0040c08040203400040040000484030049681d03c60b14462401c50007814641d8180740b08001101031a00075140381d600c0e07903080c0c0d05071080300170000341c1d680303030410090010540500140300501c5001101c0300c5103180021140325004030300b011201c0000144d001140c170880c00b00110b00030041c803030300803540c0001707681c1128a14019211040a5030689038022500c1e11200310341100141e001446800043c3c140258100050a03040006120310f525641c04604154510700c0040c10a030b50712808110941401c0c01110021a00300c0b482c10600c0c04513243c968000c02003511103120364076405010755018140311140511405220090310041e2400001c00e54601e0744906 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 410231942 1250 410230692 410230697
    0x70503030c07050c062206050f030f0714070b18150f0a2307030501090b030c0111031608040f08060705090409020f220b0603060a05010c03140d020c010507080c0d090201 74
    0x2c808403030540b6245d01a0081e0082000b54504000d0b15042d64403100105800401c1081005c210b40300d6a900120304607604542803580c0c205540d80c440c0d204440442424001410791700000074400b0a029850034098003600c10b0b54061401035550760002592134446003075400021902400158200c1100040ca0794420400b41002c074240780080d800c24800406034040011016096003444985980761007554091f010b26201004400b00c600c0019581e007011b8000141008401201d020040390306105030781d001d82c0180c0035561051000d1602c400b01da003180c010054203d00c580703c0055400d40c0055034600410b05500d40070314100c00d51080c44060014107805070381200d8101c40343c010310b17221300c943c5000a42448055520012088003190251001800901d03c07414007403041c4801d40e41c0d2000060101ca50900f002032214050b881c1c1601e58070307031b0341c0401140703010045081d01d001e18003034008014401111008105594070000d051310301d50340a49114140382d505000728901c0b0f542560000c4a200d0050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 410233192 1250 410231942 410231953
    0x603030906081b0a03060e06030a03080619031b080f0303040f0f02180a05070908010605090c0c10051e060405040f12020106080a08040911190f030902040e1c05070503030c0705 77
    0x14100c2181c0e40c0304e800307040700096907034604001010800f50f420303070400740c100c2c0030301040e00d002e44009201741d40141407503100d4080e09920070b00d149140840c0d40021580314040000c28074024446000314501e5204d08076140c0107611991401110110440e0305c03646e0b020b81d030078094142a403920400a81c0c1c03030074100c0c0c06c20071100b0040e800c08004991180304640d80803020503580303400c000003011030b07195501c00c0c105c50b810040140f106507560800154416058680c1c00d4540c16204501468002c0313590304166243d2802c1d081c800d040750044080200c8650b5102c1010311038a2b944140720440d00c086402500040f0160a44c1e4006450540007444100d040d1001088454a0f0303850b03681442240c0b04101c8900f0000201000f001d03000d07000d200320340b5a0380c0c030300b85007861045d5008bd07132000b04c9559640300f01b041e02154240368a009510600f04550080d05c10021048100480d90f903507840c5200d20113a41c10448030806905e440fa0048a2803213038088065400c503143c46d01d2000194020040840d02e230b0048 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 410234442 1250 410233192 410233231
    0x91a04090e160503010b0a03060209180415050f060105070f081312061109130506190b1c05011a03040206090909061503150106230a020d12060303090608 67
    0x24061415441d00701c00c0507040b00038440024160103950303640418026410510144415500c50540e4002c0b00e410400160742e0303146034000900c00c003100116945020300304005010900000c3d02d080c1a01041e5040704000c00c0d20f0300103c04000400465829000500c200b0074070380000c0d400d500420015204034502410041488020310a0500e150891648146860f42c1c003024130003d401019160b01e4040030483c9040c2400010441489003404440445c64403280810495245c14198039032000c10390402c42415503e901c5d04022a038041e401032251070000d2452040040b05a119490490f540c41c21032244201100c0d04084068000a00c240d90080040c081c2c40001e0301e80c1000c06e44240c83c418040c0040f450640e0700305410034483d40c0528020f500c005c100200750b021806210b81500d010341080518000a21000c0481010440c000c20200b14040396100c0c105030000350390000341410340c0304c0d036100f100700d04049002c071089031002500051111404101c094001c0c049143c1082075040c10500b1140e9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 410235692 1250 410234442 410234459
    0xf02070b043308040201050711211606050405041e050403180e040b010b0d020921010c0e0d0305031f140414090a03031d060109090c0f0303091a04 64
    0x60740c0510011031030031490b20804003000e2a5020226900c40c6810328400d80707010020480d0000030f00003410310a00103000300c18800031100ca102442c0c0d0040621651178a4410740345079001e039901054242d0700c9101c40351141da41d440000803003543c0720707541c8940c20a440c2008000181890400e200780d5200c210507404000c4906014242c1724a00945941c03c0055800510001c024004c0c1e01ca11041c9020906100c0041c84091407541102c030540f440382c0e00c03080160403842c000d100343c0d800c0a5100c01150300074001482e10500a00c04a011000200140300d8180f0007600c0b6604254005070b4045e983d0300000c0006805400516081074142c1500711499070746600d010b80010180e00311203030b10ba680646814183c542030141a06000708800c10b04054209003000e01c0d510003c50310700805142d101c104004030711740e21002c1c0c04081d440d010120b482c25651101081c000b0701c1030410940e50303600c50700c0002c1691040a5090411250b15a0303840310080d00c1c22200248c0254900400d401c0c02c881007000241005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 410236942 1250 410235692 410235697
    0x10813020d110a1e090b0103020c101b0c0b0c03040507030222050a060b0a1d0607060e0601091104140604150206190b01120b0d120804051204150f02070b 67
    0x34803410500803084014001c000b0644104d0f0b003c03002c1c950001401d000780000340f11194003111410343c5d010640b04107040040e0060f0190f2461900d1030700c00c03074030103a19010003034101d050bc544210b00400c42200802408503a40c0c0d0f13455170040c01c0c1e030080e42d010038003246914008652150282081e141007948039400240e0184082d0b02108281342200c041ca98150300c180f04468016200260400000e442d104d0390410078003c490b50907040c0100b4058189001c04030840841d507101e0001c1a0568a04c1c2d80d24101c0b00400c001094030245201c0d100020800c00000c0c85043d02503030008409a080529200080c100160042446500000d06200c0090340c00000c7c119001c40404540242030245841000311501100c00700c0d03050306250404402d010181d0700304501220f014451180801e10091400119503000312490340101807000007040e10102c2139010300958007591080f02540d13000048080c0845850203540600c042c0f1114121012031f01c20b00400d00b81098202600546401c6540c41d0000011074 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 410238192 1250 410236942 410236969
    0x7021905030d021006080105060d0b04030e09100906141c080405131428020f07050f07150503040b31030906020c03060103051504140d0201090b01120201080601081302 73
    0x41e1300115240c0203540309805007002400c43c000081000e840c0c02c000080624445103030203080303200c0b24230109041c54882c010003058607101906900a5040400054407076040728880c941041340b0341140451449200a61707403101d400b00400140d4003003a01011080103400c1140100c403054010000081e498860f409584c1d60209000ca000544000c03d402400c40201300406400e040402250f0400d40304a0841c0303807459405041e800143c072840c01c80108843d500ca030340405041c1e40714000c41c0540c0c6040010392681610303100c1d40090030f402402035041e01e5500080e85c000f031420180400103080049026a8030b00807150411402c650346450001c86112144900010b80000f410144280b105e1901004058800c501c2980102003d40c5151523858540b6007000f4280c0d802c02c44400400e05001d220b19038500310703248a000760740000c000150080d009090300d040840c1d0300810031000050300030407200701c10503080c1c040c2c441d4031542d560300b4011201c8000003824040340d100c04200c440003603144c50140cc17014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 410239442 1250 410238192 410238197
    0x111060408040509130506150a030c0305030307030e281e06140603030909062e08010501020c100f210204060801080c09060102120715020d021801020f0307021905030d 73
    0xe49090409018440000805458820740460140f4002500c0069071f9a070001d02d9201d4900f03504da0410009500071815400a045400c1c659404028400c2c0400118001e000b243ca01300074410641284585500b0341e10b40d481d000c10300040101841c807485040140d40c0754810115510500681551200d03512041802036a10f40d43e0f910010116030a680240b0350803200032001141017407801c400040740c044000b880240940c41200000c200102c003200046907003d41c8900110495040050007801c54209204984c014801c85000c00d4890524a546140b104080d550f0480c501a2442042d41d105804c0200315103255a00c8210303550003285031002d0000b0300840d544503001940760540d0f040c82e105291402a20604a010520005a800007141d0940700764030b40d070091701c803c05c9041030300c0c00302c02d20704084141c20700001d540091440c29500401100c00b0501c142640180c052004903918490b0451140c4d1503401040300c1000751414200040241000040b1140041c0c1c031400820304002009000340301 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 410240692 1250 410239442 410239447
    0x91e03090406080313051c0f060207080a0f02070b13060503190c090e0c1602100c0506040c0630110415030c140f1803010e010903090501180f140111060408 68
    0x1074a00c1594000d070000c2c14215211148200050385803104187c0d212001422440b86012a40c200031082e019181025000109035454007003000c0060400c0410381034000c010300075500086690a641420740e240c1042c1881d001e4005802e001d002c0c1c9075503001401c130078090226140b004614003900e01400f244d1807050b50b40e03500304a20f84031280b00b030790b40058594002e0b4107081c42080050b03908040013440c0160101d4004545002d2500240c0c1c0f6134001d140081d00300d005410801090080d906010001c8820a5441c0204800c0d111007020881c1c807285031030765030a80ca6140c281120320064018422440b546408203103051303580c0d45004c1c0314201600c2000c1c0441e45072080943d800c1d070007040440300c802102c4100c44c60b0116003c0c202c1a28030421121011407079050b0420300c20b685095202912400c6144002c0150050074100030304010014420540003e8061145c01b48150000c0b4103402122901303e4403800c9641042d18038030301d500c420b00703415040044d110040b24000e0010030410307000b00d0003a00300f2a03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 410241942 1250 410240692 410240707
    0x402010c061e021305041b260a0203180a0c050f0109050301020c070503070b25061e1a06041d0c120709140103050609040312020415170f091e030904060803 68
    0x131040032a03015900c210301d025005d082000c00c03d6000c2226440d00d190442c03e03090168110505080b000d409900400440410000084075990003140590851403605108054102c801c40c2e070b900086a00514400c104001000542040c12000c04224014186080603d40305c0c00440d003260001080d048055100d114208502c0c242408914064102c100c1030518015805500090034a4150b41c6400b01900104404050003096804511410908000740c8190708001a8510213001c5c801303115100140407100641e4503240c07201c200c604a801500c6110341c0e4039060000704655280080507450071a50802030410403590040340305201e01350300d03110030b0101c1d814605d291b80d00075901c00344141032524150505c803071540d50016040d0b001e80c0c1440c1020030420038986881c00b0703008903488440e16150305564907440d2034110710558000e4040300c904410556582601c0e049a850a440c16655504152068840070014026a000130100c610840b89000b0010007c541240c0881e482070030240c10204600 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 410243192 1250 410241942 410241967
    0xb01140a020601052b0b09010f060b09151602060702130501032a03170a020f06070f1106010e0408180a14100206060306220501090c051311030402010c061e02 69
    0x98005420034001d1045c4201040b01004408a1144010b0422000a0001a900c2ca02504500e0100b45560424030595580b041000070036000200c1c150f10503d41500c1c030140d200305a0040d82d20015400281c81d541103103c0e001c0c40201d90000b00140e0300304100502014100c20503000c1d042c0218071802205040c0c0003561200041c40c1c601e504010b1014000010420100784010700c101d01c0b4100d4032501c507039a035908008c01e901c2e0115680003080580242010411019049200d40c03404600544400ea05488803a00701341e2118024014500060038010100d4041007240014109400003e428940c0d444804070005a1940f11a44180c0b10782c2420308202c0540e0034800040ea08407819800240518184900000c0d06c03440018402c074200c500030100102c0d0b400d0341d400c440c14600e41140007000700c10401d0070030a407200c0c010302980e4050010304000450100441c0308000d02c00c4182802e02d415500caa40c01144d41c0701d60503d00740d1300c807501d421180219810390901c12640c0503000b180180d40304540d400f074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 410244442 1250 410243192 410243209
    0x10e090d050f070321090c050a0527060d080304060c030f0203060f0f0123070515010f0b2b05040210030b03031b07180b03010f090201050d0b01140a02060105 69
    0x40001c0180a00c00c1022200e50841901c11540c2d041c18403020203a40703543c103890b1045881ca0310003142070070903590340f00740083ea204503002d40c0e0007030307480f80d828a8a680c24007001c030858120340c08000009004403035003080350714003050f0042e2009200160030320090329a980103400503101918840e0703413403001034200d6826105242c2c02c04060542942140742c0480001c40b46a40005090b02483c03040040c000160700c120000c0700340c0c805102621a00e20039498060480380c01400b8102d40e01c0c881e1003601d0056074100a00b440c100e42203410012138250400012042580240704a1340c2c04994907400802901107044a09a50703034050030303000a42e031034140100a22514103c01c050107161401070700e402d0b180c0f8040202d5504a40e10b00050414030b404500c1d29203406032940c84440ea8022854062003c9285600f0003035010004070b0003803081440079803605045440c1004001d01048040080d070b03c01103041e401502891a050610602d41c000003442403042c0e9100b1950040160440f60040c0309501c0c00804 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 410245692 1250 410244442 410244463
    0xa11010806010c0f0f03140c1c0311030703090c09020a02011a0a0803090114070b09160e060f040e070f0b040801050f090d082e03110906010e0f060f03010e09 69
    0x2464030f2500f8868450310702d60b40040c0009400c240c0c803c5040c000f41030103090100004000307174440c1035852698040590300c0b540c040c1131040c8178200c044500b8503028407a000c0c80d4001c0310310690461458136040300c181c000b8103107901300300d8250791019030025507149188042d1207444450340005c20550841c01170056450f5140c0c1089100712038203c418440e100d0000240c5071400802c0c202440c01a0a81c4e20806190144031801400756820b0020082c5103000880d403130464041c4485078660321070f111000d11140a0046491030381203031003c3e000407250700c0c080d00020031f610030380d101340d0750899128030407500040c3d4590050141030318002400c01600401340302c1d2580c007100320f5140e082c013410b140440e21303101c0552081d00801c0000c428082740c000e0420240c0b1400844a10003085042d002000b50b91002840a1006480441d210501d814080c105550301d10b22071030050391a105090320003410041006142d003042a000003083c445071202c00041030003103018005801c0030144602d0481c501c14602140c069 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 410246942 1250 410245692 410245697
    0x3080d0204092f0f07050a060e0607030c0804030507140f06060307050607020a0303030e03130e070306080115270501030f021203040e0103020f01050705010f050702011a03100203090f0a1101080601 86
    0xc0c0f001071010b40d500d203071040f01c0c840c0c0000e8942d550000040c004035030180c1e002c060550301584860100f0084164131141c00507003004151100307652004820b8048030595850000800c2c0208005000288244014401c55101c0c081007403520b41d0100d500ca180429840350a181c580c42003080c44076500d02001108011700c0c0441d01140703400110b0703000c980c007440079200041c28035482d03d10b0000051828003c1c1c0d0340c80d040005107040c01c19a07c85880841500584000340400c2c03415502140d081e00c180511102c0c03840310f40040000501d04012108106101d00d034500d21980c0c12146010200c1207070080c140214010640071150340e00600411500e010308084241d83d0b68003c100070042014800c12300340c112030301183c403031409001000040e15140f051690040040d441e06030000d9491416601c5203000e041203074000c112800c50308202d82d08015442e41520b5146c0c0c80020f4440380d1a105800560f03003d550201130b50301451502030389928040c42c080c4119503610160058104079607200b11056884007091 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 410248192 1250 410246942 410246981
    0x90708030c0c040b040905030a03050604140402010f1206090c05041a1c0f0906090f110f0d1b05060c060115091406090307031403040302121506120703080d020409 71
    0x581c0e0650b03507100c4070001600494840000700641e641d81c0c0c0c800e500307944d0424107407650382d5101503000b002004c0c1202c100c1d200302c0c0382c42c0e045000101c10f192014400c07035040c0c40e18940102c0c43d81c2c041d5804110403c0340380d5032645a0b035001c181d0710001c0c01481c0180d042503c84070b442d2030803c1d030440c5c0390010040418000380010700c4107008050b00620303102e4128021441c0041c6070118128032402500e5101000303001c450400580300100150903141e41d80150040e8500c0f042ea0305800100800350400200c55984600f04103031540106e03012181080c01030646003a01014150f5540201355190007400f21900700746c008000411810340380404401c0e0110346458192000fa042405500c418007860f000d00d4040e42010a8000c1c3d1a01c041005c071004d503800c0703008001005100d980142e50f030707841408200e01801400c8a040c0c0038480004030440c1440043c000d805080d0389102c00d000711403030408000601da1180b407030000040341c1ca2a0003841c0800100c40050f945a0920069030140c41480c0140d88820159 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 410249442 1250 410248192 410248207
    0x60f06020d02100c1403090a05030f0a020f0105010e07030b04090501051501091d180313180b0612130507033c0203060f0901022214150715180302010509070803 70
    0x202803100e510085c2050101d80320385803481030a01d4001e68401c0185544400181d480c21255042c010700707040b009036800c071180000690310f0340d030036a042840b07000305031000000401c2620340687c00c01403107031001400c000f5210643d900d405084d1442501c01a0f85e80809640001c003030b50f0f00200d4000500001520404901c28240e284251440024070b0f9025281440a910301d40714000e0003201c071079800d003440c039810042e121140c0d074001d05540385440b18500e20300540c10400e801c1c10001d8071086242802011100d544c2c50700c030308503040a0485c0443d220b00420102000186c03c140c4111102c4c0d0501801c560041c0712910740c2c01344207025840c170035010300c400340c2c003840143c0d40090305941c462401c01c00c030070840d140c040f1014068083d00c014407010047c10a2044034034412003000f0307411190030403140408070418406000300750445544c81c6041c0078041200300d0106003400c07000c503d082e020b01c500045c0020324410103824050394010480060b510ba5041c03120b1220204150f10142c4200806545030084 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 410250692 1250 410249442 410249447
    0x10b04031a09060a09020a030b100602100b211903030501030209070804210306170114100501020a1709181014100e030703330b090415060f06020d02100c 67
    0x44c64132158a884401150071900c0784060007005680c0301000070341604100c00050500c0d8117a000e100018441c0007501d40c0c41503850701601040340d0025200c101c00ca50b200880c100884100100301d2500e11604a10030072002001080090741e5000b99000a115415841003000c05400078003d0010402041d090ac004100445100e262014070107940d400420300e480c109501514040d0701013020589500001869240d064000d1500314051009000703d5603a400800b0074064a117004850050707003d2002d080c00948000080c07010340c04a05c090906000d40d2100290310003d2504d03200740c9015100e01844000750403455080c02a00c1c070420803603003548030200420040100243d00170304119401d5204040e544040c000751014540001c40021204520031201140c2140c500c001c00117001e002c482d007035104a6030300c503440c48010000c05071582c0e600c0e02d89410114400300c11075501c0032580e0760350002e5501040075500c00141019000b50900c0c2600d9080130341441ca4201c5012a0320741040315001e080d1340d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 410251798 1106 410250692 410250703
    0xe1f09030e090403020c100905030a150c030621060f050901020403020102061003120e03010e0f0615040203060d14030c0d2001020c06060f0f09010b04031a09 69
    0x40000c0c06200d02c112080b10040c006810080d400803851800042896400c401c0707140800390386454200090406140c2034007107446944000104540c4200d40c0244142c1c441c0a080412640d4600080c440c0c00307134045400c4ea80003451012a803000c00c600c0340d206044040c2404c074200040d2510241c0d8500031741c0a170100340d0152003440e00084a80c0c1d0494040000e50790310034080c0f208450305450a480816110207100d9040d501c0d00f03403072002c00408000a0000c0c4a501d0000d0560382030220711055844140c01e03540b80a81e004004101c15a00d0b50b942031805d2991009803480c103541e0f143d00050542c081c685500b003050044450005005900c0700082e0360200003100324007440c2006d03844c12402c0384a401c0285030b0703503000350300020410319000181840ca000d0103013001d01619030f510000307400502c00340c006880b8040041018810310000d03c400031416040d51110900d2402c100780c1f4941c1d00d1 = true := by decide +kernel

theorem cover : BRFrame.Cov 410071942 410251798 := by
  have h0 := BRFrame.cov_init 410071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 410071942 ≤ n) (h2 : n < 410251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
