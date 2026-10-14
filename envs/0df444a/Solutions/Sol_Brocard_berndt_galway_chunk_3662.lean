-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3662
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:19:21.003171+00:00
-- url     : https://prove2.me/submissions/5d9e87b8-3d79-4025-a83e-3ff1495ea6e0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 658453237 ≤ n < 658633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 658454487 1250 658453237 658453241
    0x50901150305090a0c0914010b0c0309010c030201141918030923120d0f02010b060d0c050909010308041a04050f060c0f0a031206150f030c0c1e0b0612030301030204 72
    0x81c0340f8501481103d1107080014807000300c020041c80d42c4000040e48a5000400d0b22029106074804036480d6000d109099006002000b101c1d620071090a002041a000d8a42a405040710442c0581a040c84a08000c1c40350101e00c0800c200300b402032401c100003000c03414040846d042010f409000600510380601220460048002c05641c83d0b00106014900c0040050802c40c4012101e4034030ba080138803517125180d004955620603003030500080c030103141e00001117100b50041441d4a0070054a03814205002400b40084620109001d0103656803581c490810748055405071280e0454007010412030305050a2090aa409454000b0b221445a86000040001682050618000d83d000c0c3c15402400d01c10100801540ca034460348490740c0358100349410f101150103550107c402898000711505110b40c4c01420030080ca405410002074007004440111258060f00c0e0008014240c11000b42061207802c0903841d050074480c00301c202c0c80741e5891027402202d03918840d0080b1154010302c0140014609a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 658455737 1250 658454487 658454491
    0x50c0405100503192d0b06210606030708070f09090204060f0312081e04030c0302190525050918010b0603040807050606010519050c210301060801050901150305 70
    0x554001d6201a8980700000e042004110382c0e0049050003c40c014100806038103141c541d0602400004414003003480103891644240c2070041001420310000340c0680d940744040e1041e40d12440c14098100c0e901640c0f1550b40c030040c2da01d1440385c0f15042000500300f80016051065071603903503080c24841c0c50072079a00041e101c2100200e0740b0580f1200040754241d00800507a0046016016440700c00035010f00c080c0c502680941b110030103002c180d544400d0a01140c1007a07030800c7e0b052502c24507000c91814204d013044c4000440001c407054452420301802400158130384010401800354001c20b403414a03003021460907100d01a0072031801030000ba400f0841d5107000c2c110004010003c11000007003c001401d561084034111407080002c542310080c0320080107601e078050020300307002e0714100494418628204202d90601e041160016500000e65024001c2d04401d210a0078902e079000b0000541d0364841e0024010b060004148800026a506c1d1010030507040f1507004000c0000c00380b100c0d100324050100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 658456987 1250 658455737 658455751
    0xe1b090d02030109081201050a0f05011d10170f060d1707061103150306010e1306060b0403030201090b0a0b01090b030402010c020a080f1b0f040504050a1718030109050c0405 76
    0xc0c00c40e80030160310300b0f00454203500c0c40b9013101e640d1507188107014111000103800035802041503c5091110840d4041c0300c40554809080c02c1c20b802c070720f40c400c40d0740b4104001004c43d04520300c440203850b8a0742080e4046423540d510201c19040d50b448031861049217000315402ca41c444030585c05400403c50301c816601e004105040f05500c0e28005480d540141c5010300c0d24154000c0d000010040030602d8000301002c0801b04030041c107541c0d403500f06140c2000001408100e040c1519001e94400c20484d03134003e200403c0791269044d00c4d0f40c0d0700e0402074020b0110350301c190381d0702c034100c070025405400354410744c1c00001058450300d20a5050100382c0556800c0140201e05202820300c6400142e952a9148401006100c00902900521401550070710715400010315003110701801d0060b00e9900c0a100c4d0781030042c2924000f07059540c5003030841c500010500d02a14044206140b110003844001c0181034801c0d0305014944145865400d01d400c1310740d610400741054201c00c1d808880c920b0650020740d04010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 658458237 1250 658456987 658456999
    0x9061303050c0709061e0302030c01143703092a0905090303060a051f03020d020c060405060f130b0a02130902030a0c030c0903030e0f010912060b18010605121005060c060a1a060301150519080403090e1b09 89
    0x144450304710b01120403e454810300b075070011003000700c00c0c0b5040d00f01c0301c09004103440103a182d582c49840130141e1f41c00c0c448808180b43d0080303508001091940d055a07407801a100855a050030181822621044260341d0200304045d80300018012200d0002d094580340d40c0201004201c2da02c00114030700075041207001181400038a40006038043c1c250003c1c50280e070b006000010800300f0070f10081c00b210880c1c160344041c424800000c00110341c101600b42c11450303055823803400480201d8012102d64090743c0118001c020038041170000d0140a0b4000d0745c0e41642550100c0c0c101e901c20a180c8180d46091060b940054000c0200c490365406000b0040d030050f0018020381d4850340c031813002503141d8104424900079540007030100444010f00c1c0c0200c20740880300c2c4030505041302111011404504c0140240388882491203550010244140101c8417a01d12100c2410381103113100000401c00c0206460580c0003c000d03e41c046458231043d4401ca001d00d9284904044c0c0d00d141140c0025941c001440c0942c5c848 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 658459487 1250 658458237 658458239
    0x9140a0f080705240601020d09050a05012001090309030614041e0f02030d02031806042d23040e010509061303050c0709061e0302030c01143703092a 65
    0x682d1a003261a0a40d44c400080380c090f1070540300091410105890b68020803251041c2000310740c4402d0350304400c1e54000e1921043e0000300d40307400028007039900002c110a41c030740000f0714107059004000703100380c03407148900380b103131010281ea0005544402c0da40548104600102021201801c0d400c49090724030405012400c40e1054000904015090400001681000405034a014455495010b02c80303001c8904500f0a0f050200f00f01410044501c8000c00030f1182070301c81d01d8005006200e4000b407983c44c55880300c00806813803522000301d038001854015400c080b42c800720018180103c52090302c00f0300050907150f0303130000d818080b103040000541c1404020852502c1e400018071441c8081e10740303c0d1001c580c0310f1074981c00400c41c4140c80d040c0c200c0c02c01c1c024001e000582d4003144204400b08240303020030030038100c150714407000e11640b102c3c5c0d0f01d0000c09007182081400c0019100e0b00c6081e00c034110ba1030781e5419042c29001c1da07200540050907060405c140007111a03800981d4003082e240c48528000517 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 658460737 1250 658459487 658459513
    0x6030c011d09041202160305060c0a1209050c0f180a021c1d0f060709140406150809070605120103060504030e090108070f1d0f0a180609140a0f080705 66
    0xb0306050324252064a01400c40c010710301e4040011041c03074401781d0b60360061070f850364444030340302c02e0042c08041c460f2100007100c0000300d12900754040010b404213410040744c1f4842c5400307030340c85403811110760003007009800070f40c1c06103400401c10f014404100f101000d6541c40c403407410002e5011032440808203050341310480e00100544034110201054540c041036041000304080e00c0c1c010b640c0d03040ca5956210078200315210f0b601c284800304550129a465441076898400540908001d402c0038803081500c030761780c1c10709a0707001d141d00d802400c01c0f2050f0b50034a030f11024110f540380700e050300d0396900c000300c1401000041c5060b8495584280240750035841c4508a0001800c2d60100303a018445940c0620002d025050340540594000d10b0081c1c2204031901c0c0f0003440c060340000042044000305d80003070014503400b40c0341d0800308107004507000342c3d110341002c0c2c0b82030401072040c20b05c01c0d03603161640c8500403c0354130009202c0748143d800503d03082c0108159a2110210350181200715054000c8482ca0254 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 658461987 1250 658460737 658460749
    0x1e070c11040f060f05030f0f0d08060102011413030917030f03060f06030f01082e0e0f030c01020d18020307050d030306081e0c010206041e060e03180a0e06030c011d 72
    0x35021542214410602d0001003525110800310000c4688c0c00c0b071048002554000520841c2514280c240203141ea40c0e4200180c0c010b2a114109100c2841c21004000204642c40d0701e8a140c0c81c440d40359466465220a2148240d4401005007040e0394020400310940e0306196005d507a10501c001c107201403191001010484130b030400d841300c02d0000c0740b00c0c1c010f0050100078070040040074240c010720100e210400c600c0c00c880c002c280d40ca150381d40f41e80300012028090240301d6170071844081d8084980e0303064209200c500039406803550551191070103090112904543c5900100e640c1c00034001c100c00c608000803c841b07912a81c8048003855652180000d4602c2c003449481c034100007100c007103000f506050124908040140d00b90318119080b4000700400600c0d00243c400504082e407460003035510f03151800c6401485224501c030310b2884045005000d07100f015400c90009030b01a5156000d00d566506031903c00741d82500d141e54907402441c9a100c803540b040015405030000c2c028450b40441040340031541c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 658463237 1250 658461987 658461989
    0xe1905030c07081509030a09090903020c03150a06050607080a05031012030302070204050106170403030209060705011506230f09011b06060303260615120c031e070c11040f06 76
    0x1da8200b07043c40845a8a4813264a903c65802d5020790302e414555031004040320420300540315103550b00c401c10704c24580308215420032007e000e0212118041e802c1c9003a108000c04a554041580c100807020a250070400c1c1a1605039600c200c55a041000e801c10a88481e000140880174050704040000760f0400e2091082082078000d440c01655260a070041c4000c2e160142c2000c0c1c140600c04080c140c0074100080902c0d03010f601450b0050f1242040c000154036403080e80720203001c0758205000b0142d03080700c41310760900300da820307031a8101c070307201c00e590b11094010710083c2c2034510a00910fc0c40c0745c2c54102d44000c103091001403416402695082c00f002954800c820400c0c3c8040303668031801d10405411505070310814224650510104400c0240e04605c00401001a4040c0451280c2d41408801d210160f407450447c03059180d21914110780858480d820464407104020201141d1100c1920024211802100c9540d0741d034551803469214207011801a0122540081d07580c1d03000700111506201c1c40c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 658464487 1250 658463237 658463249
    0x60f090106050403150905190309090908040509011a030f0408040906090f2a180305030f0a020d05040e070f02151303180b0318010b090c0901080a0e1905030c07 70
    0x30740f1142942002c500342c0c40d11a06803c000c900e03101852020407030000f8500300541c64443c0c584620030b02c41c07804450206450340600b0040c4c1c00e041c644401c020900f0090000c0d01c4060b202c0300c0407685d03110380e844d1001c0a04840c4040d102c1e01007010948400d506120304d54401c1c00340d03d07030902d46551160b03843e044a400d507109141e043e568100000780310045000f541e40c3d085404c640443c1e2a856180e407242030068402c0d012080c000304060b502c1c41d207200000b04000440d04101903c0d219401d1070501c907201c0e40010032200050142c0062905c0c5140035109840984100d1041c20b645943d4089043d2026648504100d00b58402c0d59500c00303003404103212203417284403141840c3c1030607949444d000d0801e0700b5001032055610001744092000450340000d8980c41041e04214407c241d4495aa690041010343c1c0515000f45900d01000700c0c20030300308002c106c4c4040a90b81c1001070740e40e008e0850202e070f0714500c680e8070381c0c1c003d41915501c00d005410601d40130740c041c100b030b00d1500002074452894021958040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 658465737 1250 658464487 658464497
    0xc1e0301031a060915130e060105330a120f0c022b0e060408010606080429010302040e0c040615020609030307210f0f0b04050105040e0a060203060f090106 68
    0x5008000d0650b001e1000400c07584029940341c2841000100c10410007040205610f804010500f5a0f03030301c1d807218200c2100da9000c100011400045441c3d00c1d041c0901817207019074099403030440412040b0082c1c0c2821a4040168411001907803896a890f500c00d001130741c100b2080e200402c0070108588903401041c022810f0008040c44841da01a007442003121003950301a0000082080300c00802c4403400f00301181d454960020314400c4006629800390350040085036280200108050341c101d0f0b076050149009041c44040c10301c1d402480c2e00e292031042403226614901c4401080142000d4014544013036800003aa008200c2d01c101140403507141d40e01c104a400311080844101d9901404443d030071001241c0614658a04510043c0000304100701014001e03403c05010b5082c100c031580050811005107409000600d164180c1d540a40b1444004070f00c0ba5203400000140f900d404d00c10101070010820241c803080350151920380094000a01c1c4d20707000325030381c7e14102095640076020b0b80a0101030f01c031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 658466987 1250 658465737 658465739
    0x2120706091a070b07021204030308070801120f06200f07150507020d0c0201090b160c0b03090712060209030106030506090c0405040201051c0e070801090209100f05090c1e0301 77
    0x4010941d00c8103500c44103542d82c00c100000381d128030000407916616085080b003021610391480407884d02d91503044922400c20089004000c1560281d00203000b5109556004581c0c0d895803205074851076281c0300113203030161103000c000000c0d060350400c0c1d0034008456130049551420401c41ca440ba803192041102264000403c082080507603003c444520840740e104201d98500a080695140c07114001c0406000c00311680004581c4102d507802f014203c103c1c54607403500305414201040100d100c04c12130b4124420b0070080350fa00401c0c2c003503a114410ba030005111551a011025409426913082a00e0042d002c02a0070301a40b0709000e8400114420002420a80b9220445506082e0303031a42c038610940c2170900303210240c1e82c48001e40f0681c0203002d500039803510007003c81c1d50040000301224030603806194400160840c065112103007080c02640c038004d00e81d440c0225078611850300d0049018008101800303108900706941090340c84014980e0381c514203444a901c2c40031682007418422184240040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 658468237 1250 658466987 658466999
    0x15020d080a05060d2303041202010224010b0a230301050a0b040501080c1803070b0901170f0a021b01020f19030902280509040c0603060602030301140405040f021207 72
    0x60390540c0090107450811a60411800251440618110241c0802942425518140860380f4113031405045081241d82c3c0d1942e40105424108074180141c2c007600405000c10b00c101101034840c03499011200900ca4182e00b4901002041c4d00240b860034108540f00e00280e1800300a01000c0540701e28215003142c80c1c4d032502d420014107282940000c0f800c04402c2c4000c000707590300711003280d8000c0c11048002c0c2d00c41d50b83c61032070f001d410070340559268184203180700084c6c05010800149205102030f0303120039010401601420b00b003001903c0c0c040b40c0d1100c4c50009000b42000d5805815440506181a80036054000c203240c2642c100c5102c0c05020b1900240071039070900c8076007048100c0d100d18141400745030300c1138001840301d6103041d50100fa50101e862051141a211280442c06041c008042c80494106801c01508041650007081c02082c50188003240071400001501e0403103d507150508101541e4a0501003c0c2801400482c1c02881d40c0350a600140e039035a1031000e080d1070740ca000b841c0d03440c6440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 658469487 1250 658468237 658468247
    0x702030708130f0b0c19111e09060a03020d0f020607080c0c0310090503091302040902220906030209070c051009110a050a05130902151209010509070e15010915020d 72
    0x5805441222020001c5035000800030134003060580740c8030291548406c0750b04105141e13014036110700b1350202010a140d818050748400d0341262a0f41603980700b045681d01802d03c8a85a001c1c00003a600240d9a11000700240102c2c00e901985440601944c1c02d000c07a0b6078500c180764004142415031508100b6141c80542400c00205c291000e8170030080c07080038115160700c3c0c0c691088040030383c041c1308402c000130075011040d01141e00611016004554a41da004410281c8400e210b81c0f0b0b00c2000c0b880340c0c0006000340140501030550b90018050741c01611040401e580708903103280221168040e80c1450603a4071110300c10340003e0f83c022186a11000000b03801c2043d03070f841c030390482c07031180c0c90f0180705116076158100101540d00c0102030005c2c100b034050000428003480121901c4107030b02c0000f0a0f8141440408919006580d4440280301c05c0c4c98084420f81c44140c01d01600c000114184002190715410f03500101d60240c1c18144122000e41301c5502d14107054410314200c000d640b009040002640e402 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 658470737 1250 658469487 658469489
    0x120709080d1d10020f10020a0305060a05011e092606090114010b070f05100e060106020a03050702130e1e0c0303131419030b0f01051008010e0702030708130f 69
    0x40d02d80024086081000c06400c80784500c4031a0050b04656840c900d410b008106288214000404641903050400b2517000a0f6000b400c1b81e10020781810081081428541c00070410703a00b0513107580d80d1080309280f44030002070b0050382c400204100c0b0440007440075801d5900d0f45034000c41803442c1002c2141401c0c410f14240018101043c168908903090100c80b003242141ca0541d03860344c030110355590041c00c007040340b0320aa007400b8000740224030304144100380710340c040c2d140701d40c2000c10b0b2034403a0b99815003070f030700c541544802401103202040360000514000e604000103481c0749000041c10360003a1a003910b080f5403c121071078000000140300c02104000c000c1c216014034114019890803651250401100041780702e410403000b070701c40a100846c0e4504000e202110004000c0007081c40c1d907420042c1000d2016a1405080226440045403504000006c03248041d01510307a480103919001c0b210a02200040035181140824840c0c07400042b490700040000c1c85041d1420a03d25040c56041d6625140f5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 658471987 1250 658470737 658470763
    0xc030b0f0f070e090709170606030106050303070b06060714010e0a11040b0f12150405250509060d111512060102070312030c020115060c0605100f05090a0212070908 72
    0x10201c10400c0b000d602c00c0c810700c080383c400d545240258035000400c1d600000c050304500f10b035910709507100550300c00c0011a02d1150700e080340203010569a6405040d128459050064582003c60303002503943d040c1800100b18840c4141210030a110000f0255800c5039080c81107415950000200c0c64184080040c00030700f11003040381d003000880c1040c1e00055043c011000031902a40080359240c030790320410303c10310b1420511001d80c05407038034091420907120000e0004001800781d0000d4051452044500460241c0d0310240119900ea01d484082100c01d15604030110f035540d0202034a10700d40e0b100d140781c1040c2200110001c6840d002c0010110f1034102c0002c098604641c022002040801d00500b440122540142000a9121002d10049000d064401404123180f50b16000015483e5401003034903011a004220030441511403520080d5024103500c00c209556102900c240040c2c81c0184580c0d4008010040c01483c0c000c3d50301c44281c400c5c0003140c00d18081500d500d03007082030090070300481810001c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 658473237 1250 658471987 658472011
    0xe04022d030906011719050a1b060e1c14070312050a0e1e150409180b061905060406050a02011805100b061e0a2a14030d050a0e1b0d1e0c030b0f 63
    0x8203085004000741c0d08505400d05c507000e0901030010f401c0e00e203640c5603a5580c2040440820f4003003091403076503c480c40e2100702c9010c1c130503034900340b4451301c81c10543d04401e8043c0c2c0d400f001e0b07611003010404001612100e075048682c0c500c0b41c42000780c2c0e86c8a04109880306204410303071624a8a00c10004803805005281c0f2260250207410000450320080c01e40c1c03110b4100d503105a00010030004618009450b00660b4000c080000c0100e480781e000b06c007074000e82c13103158028404180e1102203540d05041928009240c0d0744100220002108250010620010040c14141c00c0c000340310101c0d001d030389400d52300c03050300000000c4901556601c0360000704d01400c05040b0501145003050400d40150380e0b40c40203040c2805913000c01e62013100c140100c4440c0c4010407802c1c0004e0a081d0700030070003040d030a2014007141c4200c21403286441501c140804442d0b0005054402414460302d40d5034440240340e5030030100713070761104c2d4800c002200c154520028600032030995400e40b81104015086550260056182c51 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 658474487 1250 658473237 658473239
    0xf0506060703031107080703050702120a21032021190b040b030d2a02030714060708121e010b16030e04022d030906011719050a1b 57
    0x184400007290909035051800080c3d0f940031042d684a240a81480200301030000562041419440780181004a00071a01807019035051002560f45120341000280340b802100c1400345102c0c00c41c018807000c013010b8180421142880c405481a000d18141c44201e0654042100b0340000900c1c0c0303083d0041070340c6443e403040f81e0421100a42c2c8140c0a80c0c0000c6810740c60300d50020003520b860304004044c0001804440c00e001c841440500701c2c2103c0d00b45c07500021090150440c0da4540180e0001505401174040c1c8041e50400c01306401490200401d00e400c1101006041d000030f180c00e0042c4900220410701c40307080d0400300c00da20120030100b45041141d03041d030030050200305100301c11680400105107a010b2311403000c2c5010f85420b241018100e600c03c0c4013103101011160303880742e020132841592807505580203552861742a24002a19a203d03540d101c8401800b03400e5030002c0c0900e00304240c600301d61206009000e05102c04641800441e00c5800c11380d04601000b0140d071000c1000d00a01a140002c5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 658475737 1250 658474487 658474489
    0xe160603150b0903070f0b0306042009120a0c0308070c09091a060f09090a060605030111090907110604030e0405091b0103112205090901051012140706120f0506 70
    0x740e00e000380c501040d40000c803003466036030401c606030045c00e920260284840c0d81d00d01d096000d07082110701c01c0c021418014001c029108050041c0740c81c56034408141e023081e100e5400d00c40e9a07030380800103c0c0d192045c0402c89000c84c00b22208800150b100da031310580d03034400380d161000001c1029441070f03a000b81005810070010b031001d111071420503000107585078542c0d03c1000045c00040c1c1080c1d0660401c03809800d000d549400415082002c5d801901c0900c06c0c6660b502c103041c201e40216944044d20001030110341c0c414a05841d01c01e8000c3ca00e49464141c1c145009006401d2650a03503048002c585020007003075560a0034020180c6c030108120160400e009103040f46400b82040548030b42c105603942c41c18070005503a0105440350108049514503591801d981d03181e112072000d0181c1ca203d80ca40000081c1d54040c14014242315695848020504500d40048032449000c90300c0100c0d00038500c074000c8110740b001004441e0062089903030b80c90011081040c2141101c5040010950071403c000800c855 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 658476987 1250 658475737 658475771
    0x12060117010e0c03091006090c140301030c1a0d0c0f0e0105031915080f01091a13060209180f06010909090512030c0c0d020309010914010f0f120e160603 67
    0x1103c509192101e40d260307980b03400d0b507051041c0000d405400c00e18080020030300001035441050403442d5074803500e45821134003801020741d0009120040080c0048c1d0014050151304c02655500654102481390410b81110301c07100a492130201e1040c0007480c800004005550f02440d81e4034800e1302030178924914281314400215000e880c000f00c2120a85903500b140301d07642a005141c1c01404068255142d105280031118042e1201c0d000907183e030b03450b890389501d5100140d1402d90081c00d47c00c043c01a200010b568001c0690400c0e91081d03403000b40f034000300c0c00d44410a02410301c18244561012503901c0c10390000343c814502c0750441140c0600d4585940001500007442420b0300320b84000c83c44d100c1d980c4603403284140c45800074070b0826025603881050007070340000c054100428241c035204803554440032810f40c0e4290074140e4500280d198045921041c0c01400c000d40c1081d51458242c0e03615525000180c2640c0c40090307415002e41c0309021180001c182a811603002e4119445d0a016880c048100c01d85 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 658478237 1250 658476987 658476991
    0xe0402100c0305190207170106080d080610030c030b0405090d110f0a032a050330070806010903080c0d110d0206060907091a030103021c05100905010f0212060117010e 73
    0x71400300b104504c00321483c000c01c0b40100500c1e4a000080101e88080c800d030780640103a200c0c0030310354840c00204030306032800740b02540c2c450000070780b907a81142003234181100644401500e10050540d11502c50b1400d071201d0041c0707480341c602040142600d80418500038160141c03c1c802ca400c07a0408401c01c07402e10004100a2001e5425103005414110b030903912102c038848843d8005240d06d101d0782d0003002c00030080050803200c1c5500555130400500306105c0c2041c030b00c21001d44818001c11800040000e80903020640c1c002c001032400003115922075030740e0000c03540166a6843c46512103000408801d0b4408122060040080c025201c007001500c0083d55805000e412a841908408002007169201c2c03000c00e0010111103e0500d00702c2166060100b940d4002c2c002a805820142410b003580c1c0e41c01d485c03880c0b200b5403110062146810041c403c030300034214484221495526004080c00214040c00640080b03a4094440b441e60700300040003401d0031750600550710300856004010450101d4141c040c0b6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 658479487 1250 658478237 658478257
    0x120f11150f0d0e010c11120c0607030f020c0706022802060a2001020703360b030c1b0102040906170c060304060605031c121802040c03020f03010e0402100c0305 70
    0x80d00c444050b54200080d15040240c11030640c0390181d6008080c0d40040794450003004036055500c06541400c030360840e481030b10906122944a1b501041515100b940417001c0e0003541c1c58010700f05084410881c0c10400c0710b0b0720540043c3c0c4030445040c502150f003410341500b000c14151054240e072a680c04204d5a00607a54984c0034021526244010b00143c07042152640581c3c1c4000c555a0800d4903025000d00c00040b0140c81e803041000587c10080d09007003488500305481805850382d6842d01d514141c80740c0c8001c0003c0b00c05401444801c0f503c44500740ca44214280c0d00c400035841d6400d1050142c12034489611001d28007a40c02c02120121002090700f803400c0e10f00b40c0383c42d550380d45c071800d0141c090030f01548650307007510640e14901180718614a030010015050761320040200d444010490941d081400e9101f000b00c1d040033040011b2910f46c1c0280010403c40c100035040c1000e051020405810990200015442c00d50822086103001c0d0b50310450034503107042180c1904159100205140034148c030300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 658480737 1250 658479487 658479517
    0x30c03020c0c0f2202070c06050c060411190b030f130f03050d0b0a030807030f030e0c0d02120607090303110d1d030115090c0801082e0204120f1115 65
    0x501c407a41c65242d81e2041081d107010921300c014136001407a0b8002d60022600303540442d0404c2000c90500e104204545a0341442002008036440343c0e140c2d229a084a10038450b80080ca11507440d0f0021035080447e0000c1c8010030745940c4032710300f54207405401d4200030b00411500000782d14400020f50074400c5d1402e026018609640c880c40010808002007805190465010342c8040000080000140003024498441c0d0b807029040d030421102038090702c45031011990241c00900c0302e40c0340c03402c00e9900c4c0c0c100e9038001000d504100941c111542d00780b0005640403000980404014002c0c1900070200d80441c421180c0104004454244018030081005195807034544210b513500140f941c01750000c54076520406074141a01e50740300e8404000b0300302a071007500031034910700000542500c0840c050347e81070181014441d140343c2c2c484d004072742d03000101e014903a0650300744804504485803010203c460b84c403425030034500e80140d051040420900d4406a0300c61005050030705800078401080e502503104141803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 658481987 1250 658480737 658480759
    0xc070e04020d2402042403090b070f050d060e0f07140a142b0f0605060a050a092c1501020a030e01030e03220503030a081302011b03030507030c03020c0c 67
    0x40164060a0a10220b01c00d0f00216010950103103030002d41d0304860000100702103900b82e02c1b200b0340a58185007001b41100391060b0006035483e0103000c13003089640c030b985080307031070100103405003411103005800c400038007803a44081004120040e419240c000032103040c00484410752203084426441040402410081300d0b5104c50160901941034803041e00012001c0c2c0c0310a0131402c1c41119483c502050640d40d03a04107000000c54a010b40700d044183c1c3d0000e4050380c9003417400f0601740d515902a101480801c2040c16000410b9041550000008401c0400d10b00c0083d4811581084010300509080311060b85820030410030b03a0001101544c0e02e0b41030800801c0f003211100180d009040751010b01c0319038000040c0c008406044041250441011410206002034a40c000d01d6500c0c0140d010400c0031800d00008140e03010390821051008034414900b81c10b0b0075080400c0100700c20343c8000100c011a8076081482800b94150080760003017a003900d400c60411600c902601c0c2d556103690100350003172800b510 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 658483237 1250 658481987 658482023
    0x14090a0f1b0e16180e061c0b0702030910030b030a03110304082b0302070b010e060d0204020c0105190b06270607050f0706050307171017030c070e04020d 67
    0x1085a00074824010304110340d2400c112003461061503490614001031648129130301200005100c401a501e00f40c83d032000b180c0c0c1e8141071000c01c008408600c40542c007106601d00010321100883da03c50340d0315034040c607100c0c1c2000050001c08091018001c090501702110642036482c002011001070b0341626011511101100d000380c10751103160408039141c0611000b8607811614010001c10001c00e1040100d00c0004890084040740100d210007049240d100004102030b020400e8003030b411520003011a0022006980027604903032042d910116241d440f001040640d00c0a4031000b0543c0b560300b00240900802c90b0001407040c841d003500b03440a24168903420701000b4a918404265807005084240d48000504140e590745054105411142c4184000401c2e0b481c4030b0000e13240103196546a40401c440740f04c001a00e000c0004103002100b003c0003c0000e000d242c820003000b00128020b000d10313920030501240c0f50034070321140c0207240c895444c02c0c28000140c50b44041c5a002c40e801c0140041c43d031039901 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 658484487 1250 658483237 658483283
    0xa051e1503011b09080303040309150302090901122f04111b1509070e06010f0513030b01051201022107110601240f1d060f0c0114090a0f 60
    0x6035101c1d099840e204041c001d00014014a8039a40794907101d28104654400c0785560700c0c402100c0040025420301001c0252943c0f10880c0c10030312505040250602c08500d02003050744a00b64003591040d408100f800d01446103010b070b16815500b040b010305080060381c2200000d1210720350b00c494011a40c1c6c00945000034900d4007a01c1120303e084003085010820200840d9681c681c080c5000d05404410021840c42100052190300700c404581402c005a0f841d1401500c5990940c2080c206111381008103000000c1c03441c6040d005144281001003042d4184403d04c01003164140701c075007481e0700c10000c02c120b41002c124000003901601c20b0400070307070703603841c4c01100c01b00729504400d1064862500003041a006800b0b44c4c2508021101d0740040688071900201d825242c84d18442c408149661078441000c140c1000b00c0c146414003911992414a52020407101a07010311022000b99544030321460740e8032a080c5026400c4894040202086509034482a035941d80080c0014041c0303c440f000383c01191020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 658485737 1250 658484487 658484521
    0x10f09050301050c120f090a02060d1409010c090501050a021b0a0302060a0807031505180a061205031206040203011802030a061203031a0319080f040312090303080a051e 74
    0x2070002e000701c0c03c0002c462400d0750019000350b0411030020b0005583d41c14101ca50a110b02014001001009519000d00c401c80c2d1003d508202c13410348407010703112440c801c044403602078011040001400c0c44500c0e0000c042281c2e5801c15810090308110000c0420741c00100d103001d613800280f0401da05145040010741001e42507000940003000424200821900494a18030902090300d05002240a4600b13405c0851030b40c0c024207511401da03021a1081c3c070b410704a911b91003403040f00c00143d0f164851032086003e61a0000864546d400001e041003003404403100c580e0401e07000d031015030555060071501c1500d00c2c0801910492107a01000145402a060300081c0040c104c503244851103041d07604004028281c05516143d650300811036030b903620300340000c4001c0c60022a078401c208014841e07480e00c4113540108001103002d5001d22021002ca000480b43d968030074619250b4100c16807541ca4090b041010042c0407005d114038040402840f01340c2080e00c108482c0003814501c40d255107000031042c0354800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 658486987 1250 658485737 658485739
    0x180b04090b0d1704030c050a06080103080c0f0f07050111070e180c04050717160e01030c090b030702061009051311041401080c0f030a0c0302041104080610060f110705010f0905 77
    0x742c006810040380300d000b13209480c050039101c08810740b10000d0090060080c401c034000164250010000704840401511140c148002a18460a4414040f40c074044201101c29100d8100b6503041000e0340e040a4803c80140b60400900300c941c1c54024041034111000700018050b403140020301020351000e00102d015040e00138810451410440f5008041811801e40160750340c0051004c10300c0c24a0304642982c2551040d03858094071149200114050a5100040c00610104e9100030400e1f80440000d103101c0c9006500800540c034010b40c00b0001c03107d82e6030059480030306d08000d100b01d112107404e82090068002e655095402d0021011030f008100d000c1004080a03001c02c004525000003181c0c1c07071300c2e482e8101c9952451400300c0040584407098050700038618004074200b040141015001404815902c0d98001d0420790755014960a0043c1100c4402405800c00f40910246410840040c8050a10319050b6500b00b01c0016013541c4840502810381400a0350036800c1e0124402d0707000300064a0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 658488237 1250 658486987 658487003
    0x1b0901051c15050f030a081c0204090f1d03040329090a03020c03160e070c0b0c07020108100e07110c03030a020105162309060d0c0c03180b04090b0d 65
    0x42545409801001407041020030000340060010f12841c194041100c0c080004019002c021404e942c0d03100b1aa1040c2010f50903003480c107084402403000c03480504002d22141c407010500c0c04c000200d00003116041c02e56980108415038124200d404008113680136240d000d81806461030155854030000741016102002c00700900c002c000302d255003c40c043d05854880d8080751590032401007003540324000180102020180382e44100803e00c0001441a001020b07810112079103035054132171840b04c200441c2c8c0c651611030005516021940d101178885e500001d000b030300033402030038460004060b81d0301500d080b04100c0010704a502c0010284281504a00d000f4100c80e0b03911129640640a030604a034051005030945140d081e0705030043c00754a5903003402c1c2c40207900240c0e405c008003c040c1c00203032400740c1100f01400308085010f1035201710b030849501d94442091100b56403230005c01503a448142c0024440800804001c060010341c1514191403a84101044550144001c82d282070382c41000581021 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 658489487 1250 658488237 658488277
    0x12020604030f050a0203010e01060b0a050715020a080f1506070212013309020a02032203690f060b0901121203020a0e09040303020406171b090105 64
    0x12100044c8503580c24070071340084c02400651100c20b822a520361080000300030041181d040081d209200400ca410b109044130080301c9000b00c1403d089801c004540c0e000f0848040034008090b0b8030440340d07036204059002030302d400060040828114000c0c0c000c002c0c05207048143c08000200c3c00e400001d440741420a42420421010460151402e00360075a81c1c100c0c110701d0f0700400d10044a0080b244045c0054004501d4080d980c4000900c0340340c3d92811a407441e41c4080c2c0480010720164090801c107804c06005504040314450024a04062103034a403055548208140300502d00b9a1020800001c1207001c0090300c01c004201c000a00e01d2380200810126112940408001442d440f0003c203c1064482c4242e580c0c0354103080201c4002581c002d00034201c01a09540e4ac40d20940003800000320914244120301d168001003002200151401c4000c04d4001c6002d109041c0c1c48401d21840c01030410f21184507091424070049070102c607110381c8036062400241d07200964020002c803050350b4a08400d0134690 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 658490737 1250 658489487 658489493
    0x1b0a02030a150b0102120306190b040602010b010e01032c150a0204080715090b0a0912050105040b07090b0d020903030702030727091e060e010f050a0e0a0c12020604030f 74
    0x1030010b03941486441850701420810b070754400121b4800307182404000c82d142d0345070b0b20200010794024408840034801d01e200c0200362012000c0140c8002e00e05900040b50289402d00003400130a2064101c5041600d40554980c849115400300b00135090b00b4800302600c1c031052104075040840e00c10703002c0d0002c070480081c0310070b0010f0355009004503078814069a60b01901c610901f0b00d030343c284d1200440000c801444c04e0240700307000d0380100306044032800c14842d21552050020902824214281d80c1a5501c500f04030a01c9000c6039050380c00003951406e00309890405107040c82c5401002c590080c101d6000c24513000a03282002144c4046400408507280d040d034078484003510040e41200c0100d442040401d01d0b0203128103003c1c1400d0580d100c941c154021100300c08001594058a00030364204d911030365441c0842c00b003841b460410326886a00824507141c904121015168185040c07102c0c0d0740141c4d1084081084201e03c40c0c141c0f242003c0d1064200403a000003040d5000303036000030300850058500c0b0010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 658491987 1250 658490737 658490753
    0x1b090d080c011d06010e0c0d0e0c280b0a0207090f060f321003090201090e070f350c0d06181a0906130f0204060201060501120c051b0a02030a 62
    0x503c40074081201e850360f880c0c07103030640b00b00c8051743c1c0043c042500307020b003c103422150b411405580d140901140c00320814100001e91210b0403080c207454031031083c1c5540d110035403075a603440003800c02000c4240c23900c410350200a590340164418101031a544245000144581c3d0b00500014240700d0210f0031015125020514102c50342d0b42460319101d410b08140300301c00d04803400310038145001005122160512442a400b41603000740480c10051102804207001c0d18a0001900803003482d605c0b190030820003000500b01d82d010218200c020720001c40c00c940c07500c4465484010311441500c40000f01d07141c07480d402825000f4822160421410204081044070710450003c1c0348079080e50050102c5001c4010000021041030b900c182c0150015000448a013840109440d50440301400000c1c2018019803000c120303045a00180c0044c0d4591208020320760307122860f410301803014a42040710400c0428003820354452090404040424100400e22552041c070210f2406900030303050b100a000c0c04e00e03003148 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 658493237 1250 658491987 658492031
    0x301050403171e0a020702011106040813060206040507090e160618050103050906180a0b0123030304060207061d19030b011203080411120f030a081b090d080c01 70
    0x741c05402c1d80000c2c40341c00004944030001c00101601c159a0344901c000c1401a43c40036400b641800706600c0c0400030700b401000794911541c000e10410380c13101102101d0000c5850703035601c040d0841d8413100030701010400100710030040720b600507800508a5060f000c1715003803001112900c501042d092800141141c0c001801600c07101c407011400350080e48520041d0308641c0c090711032007200e900c0500069110f101120b40030b000181f01d4801c5501155950b40c40c000e40c84026009040341030303800003005e03880c415088882900351070110048c509160404000940e10102c074811103040002c03c403002d564104e0700040041103c0750150030001013112070705901020381010b00c4200d60a601c08800001c0a03268000072040050f890303a1041460784a9460b010b030b0006146101e180c0c003121040c40c01d00301050030081c143d400844031018688074008144040c0c80140002e10491070051075840440b1400702c0d10044860f86a01100e0013042e030006410301950034042c01155040719072030080503010801003244004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 658494487 1250 658493237 658493267
    0x1e0304080c04090317070210090809030c030f0a0f020f0603041b05040209060a12061203021c020604120804060f020a020703110612040305071103011406040f06320301050403 76
    0x244611500da003808203c0d10740610107400110900b0310140741c0580c04000942103081481203030300d60114501388a04a40c0754031400c4450307002c0010b5921290500303102861051104601070110320002e06005612002407240081c142c0340c0b101d00a00031581c0703103a40c201500b0000b9204603220716161805902c1098800308507580c1089500c800074961505000301d8600007000340110307043c5a0a40820349081c610344401281e45a01c1e01000320318030049038010040c0d83d0082d4024041e0f9200c10000385020403062911808641050701040045442140210700314101e03403070f102a06644a0500d88001c0440380c80d02d140b89800080c40d04035550f8001294015280510240f6031580702c90010081c80f8400c019030304440d518007400080c04a40170b20040c00c1618020b80c5506000a203400c002801c43c1ea07400d410500d501c0e0038805106450903e07100e10701502d0400300040103400d0400018150401181030003101c0404103616081c00308502014020b41c0480240003031041e414140b034007400384015a414a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 658495737 1250 658494487 658494493
    0x11a09090f031b07030611070b0a060b0717090a0905060114031e091006090906050a05070903140c0a0b03042121020c0a1401050604061a07051e030408 66
    0x100e000e40030007066a490003803031038000b5464500c11080d0700844640d0300c8406481e44c0603080001000c03c0c01801a02d040c2901e00c4040356442049242803080b414024104190306440c1403410b2000401c084100d890040c3c108002c0750190003e1312150403103218410141c2e030424500140080c030315035142c004c60f02410b0243c0b00c222068a040c030780703103050303000407600d85010500c00c036040c1204403441240c440e0421406400e44601110f0301a403030094a20343d51241c00041d5a6006040512900b8426903402c50500c000c24005030800307000041000d1250700001d4450b86103c003514031317075920400400c042c10001078416480780395501414045600100c0c2c0903540f0b403030718400d4407560402c0041009107050081c0c4607040d15a0b140c82ca10010102e00420944e00075908124542051804000503450b4030702c0b980c0543c000c855080007490035603401604481c026800c020b001c0c05940d5801c10a00c040c50006116030fa1142030303e041181c5486c40c0501c081030034809840c0c040d80740b060040000d0068074514821 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 658496987 1250 658495737 658495741
    0xf01080102090d022b05060901060f03031e051303060504051005071b23160902040503030913180b04060c0804080301050402370206010b07020f100c05011a09 69
    0xa0300742e1042d1403480342e00030803603071551005184c0140d010740c80341d40d100828980c060003412442c01c2c0101a05040e1041e0b403000301008000c3c90300740074607009000010b41c50b0400f18034550303002d00081c200d0b00907550b0b50210411200c182500c100d0070b070fa03040e08489030140004c030f42d24140300e00101815101a035a5000700e01c070446001545000d5a0f0003980b070350369405c11480100001c4403848d001c401086614001c0030385101c0d801c860180d601409092801d0140004001d401c0b03200342080f003542c0c0580d640e00c3c0140810010340d500401a20503461064a0341104202030940c0d031001407424140c8091101024803c00d428000c01502d403902c61841100c0400035610001015101c0410884004110410402c014082d9041171f4018195800c0d40784901020f41030304201030900a00550049010100c0d14508040080e5040050a00514540821a2030b0015035000f08815049036010103000b000c10803c10b50825114401c09000c1c0c5801c030000f00f100907448540d003000046442221803161040d000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 658498237 1250 658496987 658496999
    0xf05011202030c07020d0611040609140916030c0e1e0909030708030103031103091008070f210b0604232704031803140a050d0f020706030b270f01 64
    0x1c02c0783d00824000d0501030802c1c4503070b800c0101200300d10034101c078002d881d181040140c51902c07028102503e0540c0740c0c240510304100c603884004c2c0a42c0400b9104802041c188030f90340004142800505045180224240a03185020345200084034101034010381014030b01c07140c4444440c1e40300d01e40c0c501140c05103030390f07140d1101260b43c90182080282220408000400000f0b00500001303802516000641741040a40b500184c0300440c0000e0040c00b1030000b000300011a94410300c00340d1b41030710504060b029104070303034105103141c5110240400c035503560b40d001140c030390b4030030090701d0007071030480241020684140d2860b1144000d600880b4082e4003032014000c84520505642028421000580c000c1581c80c0d0b10104c5825855070a842550a00305a0110228416580240220307140b00010019a0700c9860154170388000e00c0d081c00304201481880442095022840c1c0b01250005d142c045038003145080068031101c1400607001540b001c081091000c0805098814400d0140132860801130303036109 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 658499487 1250 658498237 658498241
    0x302011214011a070b01231509010309020d0219050907050c0c091b03130c0b0a230c0724020c061903111603080a2f0c19050115061403070c020a0f050112 67
    0x1d0304818a042031082d21101e51007584840c335060b00003400000404015004a41c10440366405440d04e012409020b21060815502042d04014176144c1a8940006100025202d42d03c00d0440351141c20941c021030f0021035007070982c29489000411690341c0381407003010220340300ca4508080300c5032608980000f44030b02c0c280c400c0da481c0104035110f914074a040a1803402107229070489001c800c401c140000c04040a040200030040d0a010200d1100220100310903004050302d8103000c8111f500034121100107840b000c05076484070407596001450014401d2044c0d01400c8000346000350b5000109608512446610001c003080d40280c440c1c1311141c13038200140d025030710065110750f01e0f510032800140801300070314210360607241e0303caa0980c1422400c020007030500400060340021018031501c0c04043c000e00b03118152240c0c500803261b80509252400290000841d0003003a04a00004030001d10005c1c0a000c1c8082050390041041c40c0c0140c031600940e1824034035005040c005540700c0350300103000102e8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 658500737 1250 658499487 658499509
    0xe27190e06010e06040c120b010909020a09170f030406110a0605040b18010605010e0f0f060d0501080f150c0d09020a27050c0f07031202030406060302011214011a070b0123 75
    0x160342c0340da06440d1f10802600141203840003050421508410006910410744058000c041c000d9030307140b0a05103010748031040440340413401c0b4940c0d08001102c0304400400821901198420305040003214200903525081a41ea810040c0000e41020108010040c0c00000d0a00c22150f001503107080c0782c02044803030700725222402000c1c0850241c52400c5200c1c034000642c0e041c8200020444201d90701c00c43c000c5101600403000d40d080503600d52005020b0403506100440b040a04040141032007540c42d20082108403020b0b200c04040c0200041e0b940c02c0003440d800c0103007501c0c5c02400000450b1b55800b052440080310040c041940145c000071301c044000c0c6402201d0044512807812420208540340c0c031000e40e4081c06045040c4108031040c142c2034100d60000d18483c6001f141f0004a00d0b28600026090407210320740700d00414500038094045884008049040d41c0100c1002c0c01c003002c241e40003080a102d0075030047d0141a4100c00041c0c0c07407014441081c504410b00101c08140c04088043c000880f2207 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 658501987 1250 658500737 658500761
    0x3030f0c1303030e13150501020f0604030906030b0a080a031107051e09090f060702070501030b010503070c06200c16051002060f0a061508070e27190e06010e0604 71
    0x1034010402c00300c0d00c80c0c8620451000000c1104142482c01c0656408480b10300000303010440902504008541e0180000010550f903003020701224540307940c00603c462500d000c6c032000e141e9558a18a066241c411202c07029001d190103c1c0c00c20801401c000c0d00308607001c0c24140961003400008541810040701c0c1a0f8020740c845141c0380d00401034401c100c03100d01c00800400c03280c885c00811600c01c03c400c100141c01000e0301d030007400b00342e030400c6d00041c01d03248141041070500008000b406581d541c058098180f85070441c000080031a2810104031083c2050314a6000810f03012444280b250300202c0d81600d525602c001b0320f1162a03480007031251802070030441d400980c120717100082078003100701050b5a200b000200e00044068540b0b00c03020320203000160740300c0000c40c001d04000c80103400c1464030010070703c2102c1d26580d4403986048086a012040c5031081d0009030705001c50704101c000d442c8000b4540c0ca0b210288280d441c101451641c40c8400d20910456030b411b50080307112030609204a0100c01e070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 658503237 1250 658501987 658502017
    0x2a0f070311040e060c0a02070b09012a15020d0510030f03110a02060f1815160302150f0f01060f23122a0415080403120e03030f0c 57
    0x491a1a00140003952645094010391640f108210900c0d082c042c0360b21400d031902c519a160840600000c1c9400d58a070850010b40004011400c040c1e0b0700032180380c150840d048425494146400143c0d03603107078075500008112803c4400d6101c02c12005802405101c8594481002590360303c018000c0b0009503440041e00818a00880a02003449182108007030440c41007241c203950003a82c00714800b9400301d031505041c40f0300811031300c0761555080c04260341980c04a40464050480f0f41440f500c61165815150b007480f4411440801c04d070082c040003041980403029400249001000000e90800c12905000741d5010500045036050040ca0300c226440600c1d91844060b0001040040040136184050010444240100c9812000360443c40e8840c00c4000806400b9096004150005002191421b0042d42051100b070100510040c8242c1040d1070500e03104007a40c940b418207903134504012074058482070424855203400200040110300502c101c10be0b0440ea0368404600d00046d01405000440c240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 658504487 1250 658503237 658503239
    0x11403070302090f0408070b090a0606120b011e1701020c0607020a080306060702120f010b030601060e060d0218150307090504020903191b23090f0c0a03060306022a0f07 74
    0x103c3c0340c4c15409441181400d00d0115a600c0300d800d03502c1c0480d02a202c660008000301e0810486020310320013444107100003806012155035804035020140102c1c55200e01c2e42d81c40410062703503000141c0c000c0401103c42d42c10000003c0045001c0e601182e800c1801d4032824000c140e0309480069801032540c0c0146166042d40c44800422407113500c4068142d900c0310007041907400580c014088810044114070000030354010030000e150400005030702440900a50314200203003902c0c0d4200b10f91a40900796001a642d0400c1c1d4078018140d410080c1c0c850300310028640d14200044810000c1d401052162264074919640340d0800051b0300c0f800302019010b0700801d41100c41c81c80e0382034000c3d000d1072190314910244072540d0105001100c0540c040e40d86121508540b02ca21440b082c80e002c103400d800d980c4c911061401920708459aa0003420b00744282c840051045507203482644004040d550040b019545d440401101c4c045c0d00303844124202c04083c0920301d000d60110005001e2040b2a4204041d08800f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 658505737 1250 658504487 658504501
    0x405070207080a0312060e0705030a0c0519200604030c03120209010f0309050a06110406030f0c020a0f051c0f02100c090b0d020f07030807020d02010605010c11060c010609020301140307030209 84
    0x101100250b840c1c016210350b0089101f42444403040d00c29956a5180340d02d03032600b41c40e07180c10768603414030200c00c0c040100308400f0583d50850f15694403600500300340165002440740c1080e40d4042400c1c00d80c8a002d000240070405a0183c484d440407802982da042c0a8502003040b03004922400c50a28045004418544807040c0a6042401c0007030203201600e142c0038454a075079050710203102c9100300440c00010203015454043c030400341424079500381080b521403042c102960b140005031002d0519a0b44260305c4040140410555010b03d800c0803e8507022003200d04040c0c038820080d800c0b040503001c4c0040d4512a40c580d4895503189403450b0340e400400d9841d241c4042640d6104c03941c0c415203580c0030081c0a142491140081482d24841c1d52052024506040028141010031040004690502e01c0c1081070781c5c1d01c44d0800c01007070340100580c00c840c2406c0300082c3c10741c85808403142140d42801c00006880f100c07039016504881c2400c01e24000ca0310000c1c109078644840d800003c1d40b1101404c042050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 658506987 1250 658505737 658505747
    0x30612030c1401150f0f05210f030d0c0305090303040c031103070b0f030907050a1202010f0302120403090305060105010201140117070e130c090207080703110c1e0405070207080a03 79
    0x1240d4080c0d503030856a40354000ca07030b500390313070303407101032141c400c12158081120082d40d2440d10010300e03400d20320724203207814480040c0c002d00341d84210403440d8100d04000c0090000034486440c5802c2c2e000c044aa40f03410028010000d0003018140e440820314002c0010041d10011040341e00c00d5500a110000303850940c2e4038520b041481d03400454061140da60003044007200d600040c0068500c045041d900c80c90161000c0b460040b0301d800660107010309250400900d03075042c846c81010f40d42401d0070318481c08036040c03c400a0098101260411110406010501d900410400b0540b4012000c0d180309070f89807001039081c0e40c0030070000e00504d0050801003043e0100080da07440080c02c1107040d9233183c0ea0314500c082ca8a01c040d646030100109001c054804c1100011410004203080c2c402541001195201c40c00540118680901403110094180285002c00e008071811000000c0c00c00302000700910030032540745100000c0c01d014514000c003150720329000040b050304845000d4020310302143e059030100e903 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 658508237 1250 658506987 658507007
    0x420060405060d0e210304150b0a060806040906110c010614030c1e03031c050106020d05040608060d0b180127022806050c0c0d02010203161103010c0c0b0703061203 72
    0x202502030380d0452010241810045c4410250701c2a6903a100e003424201600702c2107090b032380e01c001180303041880e5206441d00080710045504d54204003072a95120000328020307200441004110a2034010050840851900980415200070008015450b1034030092240c00310307a00e0000b607040e0301c8402c05064074540045040d01c01c0410a0420540103403480110745190400b41c42002c1c140c80c4840002f00490003031061500411031440200840c0d102800040d26a1080d8014201001010400529075407218034600d1445948a80208058600441c6218603810a00d000f900c0701d50070444a03004074442c3c02c1075a00c1640c4a603003040015201d541c00c01440801c050801c21640000744404510540d500c61a04010030f16070716840d6580d0743e031005241c00c01d0061801785d84511442d10b8024050b0f43d0000580702c90008010203004060100d05100c12414400c01d941c076415030801260b1790400e42c1c4914510400d91160140d04d0f00c40c0c46000054041d80c0c07803070085541c8602c0b40e001150100b4031642030f0340c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 658509487 1250 658508237 658508261
    0x170702040603021504080d050906041401021c05041a0702100309051629071104050a02090303040902130b070317060a030b15100203090d0f1a0420060405060d 69
    0x81c030556a03a0101e04600d82900380d586a40364042400c1103801010b03c80d080c20500607250a6241070400d40010780680114022070070048140301503c8845c2e4000c00c416503c03140411582c640801e01e0380c40052280d801350192150491a40034031102400c003110980740d0300781d402440c01d1402c40c1011003c500900d12040b007a2414810950003824540f02400307140041c00d071100d6941d290740315010310444211100e0130f07103c4c8094000c00030075010039801c44000101f100704842c0402e441c0c0710607840201038018814000d0b450f01002600154240c3c0c5036006003000c00c14400420465942c0e440c0320003840c01a10000307030106c0c3c07680d081e480f100000108025408400144080342c15602d03911090524502250085900d038103010b0140500d19125400700d01e45104c40c4011450480c8080c007044164585030070040107004032100340c41c00c000100b0310041249194500c1828140b030300b0f0410104541a040380220100168040074403141840e03001ca40c151040035080f1445c5c04070400000c00200002a044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 658510737 1250 658509487 658509491
    0x3030d0e01230406051312140c03040803090a06090810090615080f0606040c0905010c02181003121b0201050904060302120c012007030305031b030117060f0417070204 73
    0x1445442c0041915240345082075800301e0520303251500340c04881003d0140c03140e014031804101c0c0010030a000c58212440145070003072020010158050310742c02030074110103840c00080f07404541c1000000c082c040d00c110031254420942c1d07a032501030f00e04c01503034006c0007441c0c4c2106110f070b0340c8919160002a4018400e1400099584c0325010300911984141c0002d038481e0842d105411244070200701c0b43e600040119410000c03c045014050007050580c0f06040c141b03e81c40c0100030542d625119001004610344c4040f00840c5421043c042d2003000034002151103840400c00e078202548a40008600011650689100b4240d43d4005440b10f40149410550203070b2265404801070700d54400c03c41c8650720b01c100402200d4500310026090344182a1030210042060b04c40e0301c0b40d444001007580449030035090455032030b125a03003079030b8481061400c001c1040c2000000024420301c41240004d4103443d030010f855450300c5109444080e02e500356806040222491181c2e8614982440107041281c802440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 658511987 1250 658510737 658510751
    0x3030301031b0306140708100503071a0c0709150f060f0309020607200a0902130923010605090a0b0309121606051f08030408030d1d1c1206030203030d0e01 68
    0x880c3c059440005c00c107941d200f43c0c10240405070b03412551070758010007100c9500c1c00d41400c00000c81d0307460049100d08141c2403041c007580d079245100b400488900b00d1180050340c9480b0780340c80420700a06809181191003004001c40010121844407580e01991003644d602030101c3c210410450107030240d2a0240c0c1d0280c400c105140c0002c01014500305c6807903903804910300c4c6a01c0d210401c4000f000d5a03101180090040100540c0b28546900d58070aa40418100040212030140165031500c0d00ca20fa03881041310030300010036905e4204001c1c1c0021101110910005901c0300c0300341006000546141905a205000b0070cc20403070200d002e4030003540410b00440800081e503d83c103007031700d8083e0788111407581072030b01e500d41201210300c1d02400f1702005001980b074a840c0c4042d460752845609440003d0070750b165003c400c030381c00b8404610020903890003110a02000600c10002100302e0900f42800329180c0741e40100c100388140a5001120b400402460501040204280240400009501c0c81e5580da1039 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 658513237 1250 658511987 658511993
    0x60f0a0309030e130c080105010c031704080c07061215030f14032106030d0206040c0b25060209120c0d03140903030403050f06060402030f062e0309060b090603030301031b03 76
    0xc1340350720b00025a8400b251400c21800060701c26001a04501d04101002000f0404030750040a005c480702e070784510903403403a0b4a030b0030f000c00c041c000c1c00e00301d0041d8007074040f000843d039501c02c030140c201000f0044100705d142c1410a9410038265184070081c044280038443c14042019000318120b40381204064074070388038810002c22032003002004036201140f20007081c09032038201000a807851001d00d000921030780c106a00c5551340141315110b02c01c0c03450400200c0c41440e210000712520304c040ca144030390b03480000710318040b4040e400020346503024800030790410149a034000795016140001400e903082246941d2800c0b900b00440081c04034880000f00446003203901d0030030040c401180950081c0200c00c070101103282c00d203d03024100c6803041d8010710a01c281100c85089482d080602140d806081407051110003542454100c01040e9400d0304407480c81c060b0b0b40540220001500ca40b03405c001622510080140030304d030654540e60154018001800041d00c03103820201004060301e007500680c0c2d625a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 658514487 1250 658513237 658513249
    0x2090612010528050c160302070510090905090601140f0103180f170a02031917010905011401030204030807020d02281d04110411090d110f060f0a0309030e 68
    0x620400c1c82082e4043c15021220700f03406021403a080706240500c9a810407013a030340b4041c01042d804041d1038004507241002c042c020080d18000700005000941901c2c800c8002030144062407203580d90a0341840006411460b0100c0c0d000c0c1030b40c1041c20b030100219030071824429500ea07104031460600d59a010210b985422521140c4c2d002481005c00300491129807402110304091036028054a200030b2180520300340d008010395120200d140040c0301c00b400e4101d4120345d980320a4060002940e00c040c000f0480b1a21504401d042c1c5401181041b1059410b50044040384502c0c840500b23002d40a004001c010700d44040109040c0b0300003003200707040500341000722040140001c00b14045c03002d00c841c1044131068100d5540312241c0075221a0710030745403e8032400c032880d0309204502e208075510554041e0b203138005001d03130b90b00c48009400c08010f03c1d41e03860000c00321008450039a2145c4205065450140703040d0040740c2c11703920040c0c0b89d01c1c1800c1d140c2a0650140000310000c07424001404400000b079281d00e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 658515737 1250 658514487 658514491
    0x60403050a0b06012706050f12192d020f07080d0e060106080906040212030f041e09020901091203020a0b16080709060c081303020307080a0303141003020906120105 72
    0x50090b80105080100c00540350382c030100c1c0c0460a01394a403c610002150a120400844550b401c16594850301c034a210780c460b10071222a65080381e421400d1103040081c2d0310f11001d07a41e507001d508209201e1955000044030010310003100403115408140101e01526401500b03020081c2c01400341020055a034040301c5800c000c00201d600da5603010540711000c800c002441c0100198100f0340010b00346402c90a4036288001c04c00390140218040700c0a50321401c00480d80342581541d41c031a2034a481e40c0a55205101c4214a001e0f03c0c80c6c0e090011403801020310032600c0d00da005864444e5400d00c4c0041a8001b2804100180c065010b140e040308046001c030303114180b144003640c107504000c0e1030a603800323094a88090460010071011110500c02c890f00159000401c0b0340000315143c643c003d41502ca004031410740c1009400d8003d14000248044002070901d000074800e4905028a104840c2800c20a85003100d80b000401c030260810009400d04406882c1c00c004041e041401465a13440340e2400e440741 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 658516987 1250 658515737 658515743
    0x4180902030f1c031109010507060e0f160602070819120c020a0b04150201200c240912090a090911040e07080f0606060415180e07080a0e0a06020306060403050a 70
    0x8150f07900119031500c00c1d8078086545070005400c02c2d80c0040000d20b140030344600101003a135034468107001c02c09c041140c0c022128041048902c180038002120b0140c3c1068800e500141c4035861020404038004504103070170226011b4124040c1c1c160b81c440611680d042110501445800c0c81e80130096210f40480c0d078040c19408041b10754452810086880d40c0b400083c43c0b0701103926201103814640642001c500b1500d5070261b03403c0c3c0b1070381c010121504121544003598200140980f01e503107800c0000d1121440344c03203040141e50680c09911901e058034424000e0791588075090740303000d010240e000d80c4400591b038000d9420109282080020800720362800342401c2041d13000341c80402100c80304114120011500c2e00192803103061010200c0c01601450107101c89040128000c80d0a0612611041d59030b152003007841a440da641e80f0080c80c9100040e51860001029400003600036040390040d032100703444420040081c0030140d2241002508050812a80648104030000100300c08110001d440c0340 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 658518237 1250 658516987 658517023
    0x915020109120c111e040603060902040b0d030e130b031b0405070207060e0405090a02031009061a0d1b0503100f0c0809100c0c1509030f0504180902030f 67
    0x100c5040c01c490861003603840300d0400c6070018104000504904139610b1101c1c003961100b503211100c20301c086003001d041c00304075042803401760000103000703040c2c200c106118020340c0e0030400000038030180180c5680d106c0b005404034550780701102c082e091006243c0d4200c00c00300c10002d010220140003900306070a64421039850580083c42c20b2051806128041d0484518002440e41e1803400c000a420301c100885000e00c5070b80c0d5103001942511060140d0244c042d4001d007510f00c2172801344c0d0320000038184c3c00c406840300fa1800c0d411020499903800d01004001c4010315142006d8100c0e0344224040240710190f0300c0030107001d8000640794604005404180f200100049041c0c80070140c40300407120820b0b400d02c1042221402d0280f140b50100300e0000400001d0400b0584004031082901c02994082d001803400c100314503841544803283e4480f102a40c40390742d81064841c180082200da9014038058a01d0080300e0380842018158142c0c40b02c00c0710b41c8003805860110618105c0315041a00b00c40b02c0f001c180c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 658519487 1250 658518237 658518251
    0x121020d1b0f21050a0609030c1214030406230712050c09060a080c0f131503050403050405100c0807050313060c0b160e102015061009150201 62
    0x4824541400007078080e075160303602040e2812500b0040f1036881e024007002143c40550304018820140514110141c200c507042c4400101840c005007442500c00342070781c0c03221985081c2c2c84443d1044045505480b8680d64403425a01c943d12100000c000c42c1d0100c100302c00030010201c1980000790051441110036443d444280d21a007204581070307441c0103201141070034041229424990302c4000391128010700345031161036682e030300400c1e68007072007403078100c1d69510404620302d84900b40031136404050721026805034066950205040d01641e03020749009001c518280310078400b508003030901d5103c6411514100340400141d44a600c40356200c41d0781980d03583c0000800040b0b0303645141c03c400003051503185c801d00f000da8686429841c1e44026000500450b441d9400742c000c0c0d48110175030800d0000c000c00c2100381c400911005842d01c44005543c8004500304040d80003030840208154020410561100c0784650f101020002c6840e210242c0b24140311141a0218004001c0d9106103503a82164000003245 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 658520737 1250 658519487 658519523
    0xd140601030609060e0705030712051302040609141b0f0d150e090d050a0e04140105040b011b0204090206120f011d041e02031e0307060e010903080121020d 68
    0xc0c2c2c1c12900035642076418044200202c43c4480040d981c0490140b8015480780c03175401c0115200318100250850440c1480c0500940d5202030389500f000c20310844041100580d03c83c5a201580c200c20076106031284c5120004019141c070f02018402030000d00c0f0401e1406101804020450b002801c21050040da030b81100861143c070301c11414080d14403074803402c460349082c2e0b0078a81d842011580e28410001e011401e209610300483d075080c22039000808c2400b901114000c920410082489041d106500b0043c101c1d040d0350168504800345000c0c1e4a8601d16507046400b0302001e400074140480e000f0750300700808280701c01c07101d02041c015500c00c410b89503294500613011a0103617800300380c00c070505185401e000020340d2080802030854910062184080c100340000f070b0510020601c1800300044c108104005410084000c1c41600e2041c54204500380c1d0f044409422242107240c01008030711800014041c26140001540c9401c1038805152a450b01540c00701c1c02e500800602101e40341d103000b1a403d54 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 658521987 1250 658520737 658520741
    0x30308090f06060312090409020a06080f0c090303070215090405090303042109061d040c0255050a06020301090b10021908041502031b03120604050a020d14060103 71
    0x840e070300c603400501050030b10900190300c03464484c100070030b103840000d51344405031243c0c4c201e001001e40040c824080d042c0d54010141c074030003084461504038005c1d000000c00e0107091806950b08140054021410f121295081c0403d10518444e0001840020300078065107503980c2c00f900d403240a843c0091a200d00301860f06520007641f20b8248080090f02c20680c01d0b100b0750011492048581a1424510756103d10400813521300150804a4000c1e0070001303240340c5260001185e00b0710082d4401923615200085980102c1880d000034140b00c0c0784850700003500d040503a1405a4074000300221840800d40706a0303103151500c002c1681c11224541c020004002203440e5101c0c48002110039100082e0b00407195500940b50308540030306141d101c00b03501003002130000040035280a405000c0301409840502d03c006962038101d1580030607005c150102001c081003001c02502c48064140b14404006d0b21500100b002822000385401115a4203000c11010f400160090546c4038074200300d1524141011400141 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 658523237 1250 658521987 658522003
    0x21b0a17030606070b130f03030c110609150606130801060e06040e0a020108090a0b0f150a080c060f07050d0810080133030b190501210f0302031303030809 68
    0x1404003400d0042180648800048400403540041800e40941d03d0071404549002460000b070300d0004120021802c15400d9070014035942c00c0e0b500e4000e00036080107441035940400321f80c6910923030000c00036840016a52500240c00c102d0003054030f42030101824000e03500710283e900000c19603449103420414048051881d6800600954041c000c500381c042075141c1d6000301c0a40281004115000181c001c0001d0107016461a4000150845800c020b000341c0c2c030020042c1c070400e00c521400241144280b070003240e1141150410400750403428a0401003062542000c4120701d0011401c1100710300103581405464440500c949840d0341904003e0b8411099016641001000c0c3e07250012203007a022101c003654a41c02c1054490b502c2a0910000102c0710400f13950009040c006040280700403407000640750303214411003000030001e603a80c0d21304510407503880307400c01d226020607500308101141082e1031044c0a50300a0048914100b0268140350360854107510a60004050b0024024940c909001c182 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 658524487 1250 658523237 658523273
    0x313060501050114121918150203061324150306080d021b0a03020907021c02010212060f28061b083a0c03150608010b0706021b0a 57
    0x410031402d285515044ca2146104050354662401d000034640c08040a012600c946603600900801405d0600720341640410350044896800300c01c00309400300014400c0e40d00c1100c00900808a024480e02100001c2c1040c4200f080440d0300c031058010b505100303001b03040040000200b0540030440410700202114415040300b4500e0304140c02140b16640c0c002100135a464440c1c2c000c143c0c00d03111038000798051445a000030b41100440701004540d0f40c0110341d00306c10069480411141140c3d0350012400c0b0f225505803401841c0708030020500600700380d50005106e200c003030b01c1d2024200403408a00c1040c18050548026040c2c001070500009030f01844121202c404a00801c14000301079031b8002841c015030700c000c407406030b1020100e100417016801090070842d8100d01011240303490883d90019040c603140d40c0020a040c40c0006035201c10509041c0f0482e40d465840b55016401c080c07134000d8690094100782d8440340c0134042c1003d091054400b480c02c00301134078010205c400700c0380f814032a81249512a0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 658525737 1250 658524487 658524497
    0x7080103110d0215090d05011b14070b0f04020d020406091d03031005040b180906040c0510080a020d090b0c121b0712360b07020d110f030303130605010501 68
    0x40c2c00142c59041200352880c80a00c65a0b4035921903801141052209003005401903080400c19045190f80c1d61075251440070715595003c50368003a01c0c8908452040030401071000c28807400042c420302140d8486a00103100804140560b40c00350001001e0701d45581000c000580e4070703240f05041c05c50b0344040813511505e030005581145448640a8407201013072148902480d104c9100c90f907155502c03030401c446584940700c01003480c1000440c0d2503a80400700c40440c2ca003c0500360219141c600006461a0000d9583d298401743e40c802c040d82000c0c1d00000400058136489401c6080020403074100e85d032040c85202042074840c0710008ca01c9000c07010180001c03030714042450702170007044c111000b112034054110044031981411040121040c20341e208001c0341d07200403801640800002d41e40000d00c6000902e010000c41c84d1501c41d084594410158000d5011108944850000c4e030300000302c03c840c41004103055110b100394008241540d1040b80c0350750404d0600d02c1001c0030441d080c420540505420302e40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 658526987 1250 658525737 658525759
    0x120a0c020f19060b180a060501121b0c0611040e150901030b0c2b0902032e0906060f030b04050607090f05061e040f05130903140c0102070204050708010311 68
    0x1041600d0341c4250024040641351070403003c01c3e032545a000441c024001103440d4103490a0400c150080525025850000b40003004240c03119400c2d0140000a000e4050400c4c490084542d054860031014241151419114950500d901c1c4500c006030009141e00c220707040d00c0345440500c2d8040c43c10010f001a03c40c002d40d5005102056900644590080d034284a9a03515400240030b14a130f680c803411200c4a41d01031503503421a0031029040000e05a1083d4100c43e604603a8000c40c3d0303030108540040b03800c116043c1c03000e021140e4182d000901401e004035400101c294032404008058081504151650300c01d9205110070440c00b00003c07a4010b006103055081c031424101e8100074049180301c1c2d0b0b4410000820300480780300400e0308200c80c900ca031204880d40c4d9940d0320b810380840d00d20741c424140b04001d28040a004d080380d902440c003070a58103942e0041840045810324a2541100c4032100c0950b5081c005000161201d00c260380c050720175a1074408541d031552625494140380350340102d000b84003c003c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 658528237 1250 658526987 658527013
    0xc0112020c0601420e0405250905030109081e0301030209040b1e1006090906050303030a0c020313031112010b010c080307030e061303090e010b0406080c120a0c020f 72
    0x180c1a03042d42e40c48891340d80010500e180500107400051030f100d26010505103e110320480300040d12450200315100c84041c101e100c410070044a40843c0d0861802405000c515880c03d243c1030b1510000e401070030455800368682c80403900b15040c6240890304003078000340070b100c507107007810144807401502d410541c550360540e808184806000b400081a950b805c10204aa034040802641c02800b48403000c104103141204c2d88003414081c40c450440800c00e03022001c03d02440078018802a560040e00451a42d100d2101002c02420a000d60300b045000500c80900c9004400424500840c0143c000510400908d010003100d0014010000842d80c504110610a07980080b05903500740e8000210707035269551134505901911842000340c5840c00741c84104104d00d05001c0b040c0c241980a030780e56208440c0c58004048c0c041c0801c1c02039044d800010700c010016070344130b1103089602081410f1041d05100002c10f0070345111000b0380320680115110b403410400359604002907010a0320410003840d00b000d41d00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 658529487 1250 658528237 658528243
    0x41206051f060c0f03051b010605040b010f090e0402030a081309110a0f0c17070305070c060201090507030f0303060f150e01050924220e330307030606080c0112020c 72
    0x4014000303404070584400b031500441c140d82c00041604041c1f803c008290011a00800b803501800c0d10891500810385034035485900700030481032a82d01d03840b410034240000669901d200400132641407040b00c0801d00000d4141300503151000d52500d000e9001414000220240c9000549400d625017044c0920140e00c0e40c003145c994074403c0541810080d00c403044c2801000040d00046c1080c1d0321800160480805600800030444503000300e02403584d0a843c0c00341242600e001e00310203843c0380d1101c2801e001003907152800e0b40c0316502c00d04001903407a81e21142c0c18421819540941500c00b510701c0c07580040368200007040b04120092070040e1616000030001128120b8035007003460900c4103082c1103002e44c03046c0030464500c42244070303043d41d00440c01c1c03440301c0030f1000601498298081540105215a92500c84100c00314004090004404070003420f6a0007004c500074500e5040c4039031100040070404510070390014042e0300014001c404050700c005071865a104c400c0e0440c25204100c3c8041d1400c001c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 658530737 1250 658529487 658529507
    0x1101021309020307140313061103090616020a0605010e010501080f06150703030207021e030d02010903140307020a0209010e090115080304062f0601150230041206051f06 74
    0x40801030b16621350050481d43da0381219401241d6240000c1400014550500201e450b584148401d0010b464951148162400143d541508035070102c00130442c2040072080740b80480d5000d1045503a6416a510380c002650b1080e032002c0401201000148200d50740b01c02c070954042c542103487c10542c28080e012070f12a04113925440702501000c0341c03010805100341c04441403550018040301e4411507000301d904104060000780742c4288150b4690480050040c014607d415415803034001000f1035440c8883c080b544010080002c40c01501030300e8006070b40704a1190b02811550540750304a01c0d25020700740c02c40b6480100402c140c502d80100704518500002150259103040c5010410241d582c05c91020908aa0301c2895a0402000c282c107542c2800040d4981241d80c0160300214544540c402640c403801c0e0f0300412103141081d1144100010900200405400007180d8440c1c50160340349200c900b002c0b41e680b01154910744410600101212001c0d11603400c2c003c0d10000c111447c40c20760050700c42c0241d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 658531987 1250 658530737 658530749
    0x1203120504080d0b091b130e01081612050d030f0e030c0109110f0a0504090305121503060a052a0c010213080c060a020a110d0c06030b150c03070b0a1112040311010213 73
    0x100501131f2045501c0e02c1e40200f000b0000400d80c4e507160061303292a043c0110540400030400c003000130b01c5401d10390000b00e800360002c0113050b01c102c0382c0e2000c901620039450001c4481d0348030307c0c0c0e460080c07004000804154054500004065016240c0a0915684410828441e0f690340c400e00350780c0d80d1041c1500040ba101103500255003003813031138140e4141c02142c0103180b8422105081004608440c990140703558402c4054441c0d07982c1e0b5040c858201e960903140b161120000e0301001d460700c00000e0704c003a200c2031090f80d154101100d0802042c2641d1100032100c2d81142c0300f150410203200d081140c2030014104903141420990708000082d41d030038805102510b17114696840103c40d40300c40c00b02111040d04031000092441e00d1700405806000c44038442c6004182c04602040f042c1e940e14240c5c1c0e0a80d901d50041c52a20700c00d526130203042c1030007525885c80383e580c5228001640d400c0100501851403001221034151400c1c0c14050000350b0602e00b4280c180e401080403c0070809201421015030304 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 658533237 1250 658531987 658532041
    0xc130801060605040e10080613150c0c06020c010626072c10052707020f070b1c091113050c04260106031b0b090a1203120504080d0b09 59
    0x45e41c840a15407001d070b150f100107007600036236061101411100059000703440c0504c0c400d81b101c0da03485001c0ca0071200d10305418000a802c400441000850640040c5508168140081074081d11468142200a603501c0d00f041d180d07503681885000c030001840080001e0504020101501203198030a454011800c24195509000c010003d2501c040500e65030000d00400b5102e881018881113020310340a14448580c5102c0c05c44d040010311940c030000d081a0220f405e0701c00303441c00520344072030005550000e000b8010507070b24041c80d072a444940c1d803250442180c003440100d45942c00690500100722a10044000c0c406e003884100b1140c12428011034048400704502c00000920800341003450785550b0a0070030680d424110008148009030040b96034175205408803041d1284d6a8807507045521902000355007000400700208521200c03840c4260000b406800e1603541e8180e1094540304440e011102118082008a030500d000c005601c91407a07003442c140c988034140d0822514041e0701010b68020810b02c0c0d5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 658534487 1250 658533237 658533241
    0x1201091a0402030f01020a030507110d0c080a051209071706041a0c0706020705060a11211b16110901180b130c08010e100312030b180c130801060605040e 67
    0x514104a07180740f0b130a00d14002c640720000b81100801030081683e92100054801da2142c895400200f203080e101c1040b03440303c1100c440141d491129a4000e65445001d010003440980c0507221144980d0348915808006090600e040c0080c9601c007050b04c107070118995200404000c0003030344100c4040c54140c032106400c0744669540407000d05922a80500414950000c40c012007040000a041401040050006d020209400d101c0040341d01805c92507112803003a942c1c0000e5207010716000303107402845620340800c0c80200c00307429098070344c040399007036030f0202c00310b84c2c91b41c2482175801e540388994000300d40d82c1c442c5501d054916070090401c1d20008200680c0e03200b0401c0c043d039460400b0004900b480109200f110000c42002d404860248074003500200c520700081c60046803080c072075083d03c2d401024551100d1602c0406c500178007025540760340001c10140d001c0740444d0003001803485000880c41c0e032680e400310101c911800b800d00c0d80c06841c06238140304080c019250030105a41c1542c982003c0141e01e6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 658535737 1250 658534487 658534489
    0x503070315030204020f03040b0a020a0210020d15080607111b040b01020a0b0c040305060f093f18010e09060f150f07140312180109050f07051201091a0402 68
    0x341c1190b41c0000c3d401131001840301902c40302c0c40c0155101d00c2c026120501103a80f60b2255200b030b40320b10300c201001178003d5090300b18940c1c03150340900080c0507030704400190640304610402d407071011030300094095440f0700100400300d9400300401c000a22004081c040d80000c0c84845071805d0070f0344e040988950780314901010240d1080101c0d040c490340244252409050007400010144c0c058041600c1c2801401c001940c4201180d110317901542c441802800d00f6451034280760040c11030114042c8401200d0658088007001e201485c841c84020f9180f00d035500c074801004d1400880d03100b00e455040c010845c0c1c0e40d03c1103940342000c0a520200640d5400c544048040020304103d0311038038003908440001c54840511076400002c0c2510511407981c1a00c0300002c4004076940e80110780100c078800c03400400290030b446038004030240510700c000c00070130100d0b215a1490f060041c0c180e020031581c0d208a004001c2c524018280d900381c442d11030000c10555030103032201422220481801c00305461084085421 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 658536987 1250 658535737 658535771
    0x703090b01030b0406180c080c06070c140d05030c0106170607020a12090504090c09050606040b0328051602100212181606050d0506040b091306020412032d05030703 72
    0x1054041400c1d006c014083d61604800356a1075015140311881091001401390400301c003217a010503008441c103000765250400c4d0000d4201070070203031900b10024000a0002031803c0000d0414100e491002041150410706044010040243d412800e0340c05102800050303500401c0303030950103400c0400c5500d010040f21003a01c14200c0e03035100c3c64003d46080d1000d4140f0551a00c200d068030b4074544188041d440340c0b0304014150140d4081d1804076031081022030118500418141c000c00c03802174020703006200319a02c010840d00100d441c3d00c00c03005007540d035541c01035062226070085242a2421030800c21a12400c2d81100340050076070303030100481140320540c040b003045074100048070300149001160319200000c0c02c9800c0000000305240c28800841c0041c64140107000e040f01c1c001d00182201d40d1041c0b154186c2802d58103007914219420400070407004599030007110482d0180e154070f4880e4070080781080f003c4541c0c0700307001003040340b60804043c040d507c10110713a000b840e94903007c514910b0001c00042 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 658538237 1250 658536987 658537001
    0x8010c080c1b19030206100501020f03250818040e0313090b03030d0207030207170a150203150901060c110a060e150d0614130c080126010e150703090b01030b0406 71
    0x14210051070740d01020145c1c0040c80c0d038400e10304c03005c81c00301d02070b66480160394501903181c8034a40d030380003405011407041c103481d44141d860040c0e05d01070707541d60019110820b070f50388131107074a955240e41e007031403031800b42402e00902000031080c03001149070041042007460b0341802409180084c9496040b1b5081c583d400f002a6035004090900455840145103400395075212144107580700e006510314241090900461070f09116900411303219210261410f011009500c010045200100c0e04543d0028684407948603502030100f80d00c900ca41d450706070418013410302d081d01c3c4003803140f4558081801045e03072140d20b20b005008140c0383e00107031020f0340c220000e0302c0c06410061380d0400d26080c0000b40221455403194400d400584205040303d001c00c03586e03400d5a0403099a98042003000c401000002004a041c01083c00c420904101000300368500a0039918641394000043d03014a0701581d60062556907290010700d5410704104003501e5990301807145905100240039005101e0000302442000c0d08910 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 658539487 1250 658538237 658538263
    0x180201211409030c0d020a020112050903130f080c04090f060513080d0c080c030403081504271b030302060f070309021207030c0b0906030105060a110d03020408010c080c1b 75
    0x71051a100e81076942d2034014190098107485030002e18201c0c2c40c000b2030207104c07803070301a034400e80f201d20042c41c0207002e004007a090b000c40744410000344140000d5150210042c180f0205000c0e55a0314220626243c00a201101071181d4a0106441c0c0082c841c10700f04040c003039000c800030030180e441440c0700501d801c41001c00743c1064400640e0300d42040ca203170701010000003e5240e400450b100c00480050324001210014080b80021000c80d1030b031040f0704c1c42d030b0304025402440401d20a0800c030b4140c5104c0c103075444400000074800640c204005813008000c1c07086a081c0c01c51010039103580c4000f5600c21003d080000c4210a240114110b01d219401405d00e032500682102800504010340d00c0c0c0d901090b100030b0382c05000312a00401c0c40081d080450344900c2000b480306080d40d0a0a00300030325a44820303e460180100c075120242804c805020701d0407040c946840068130b90780341001c0300f070070760360240d00c042c0410203401c0030403184c0d050880680f543c0041740401d00e04004012280d03c1d1501c41c3e05000c5c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 658540737 1250 658539487 658539521
    0x9040c17010608100504020306130c1211100507030c1101091a0304020108101401140d0e0f0c040c050a05130906090c11060103020a0303120605090114010318020121 72
    0x140340032a605400401c21039968408954010764001c08000894406440081d03040e00140041000e10800c01d2803010201d00410400111640e5058640310081509500b00c0d40e0008404220701c3c03a1074090030281012609040103407405c1d00e5039030700610f0080c0d8200001c25241c1a8403201025920442d0a9005040e2840182c0001e90401190075500e030001c0340c0132800a25202e0010b000d1800e019517010032102d04207000c001890300710006403010441e40500c600781c140203010380000c80c48140522000382c080076014100c02c000c42c448240c149500a00603d00440c1415100c030310050703002085404c00754803840d02c80d4488a12200d44441c0642e50f5001c42001c0303080c002c01052204180d40503a5501006484812815051008250b00c918091001940c40290041b040000c1b074000d000368080300d4030007000000c60380c0d2604c00040a801082c0c000300100038440300e101440d5601072162810b080088400000c00c02810350008103110386084042013075843c0c403125500302060715000031a5801c42d04802c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 658541987 1250 658540737 658540769
    0x1801050c2d0405100507060b150f090f090a0606080714091210060902180901050d0206070206040f1410020c22140a02090f090f04120c0f0312060603021809040c 70
    0x402170154100542c01d44060749048031007516480d02c2010079040b40504c0307001c3d90803d81c0114502c5003030341000c0401034020f039180c00b1681803a69288070441c4a0750031a44d000459504101d4028090f090081c0a0720501544524031801745d0302c1c1a06a48207210101c2d91410051003050a641c02c003c40c0031b1498448500705440851000c18540151000d01c61248101c5a09482030042110030301d000e215994000c4461450034015052880c0140707138042c000380c10b2a00d003c0da555132a03030004109600040c51103129504241c1146018104038128850f00c5c801017840c000d0aa00140e500d845030700309603406a01421141c001c0318510b8100f14402d40c083ca5002004e0300c1d01c0c84a0300040c3d131080804510803451000c03164400c0c54440d0056001f00350a040d4400e480c0e40702d90700c00f0002503041e4105424405201c6080000545000010191a2080d900c1a030a40d080007211000d45201d90025018117005010308410140032002d0302100c0f510484984a25072190300b010511681c0742d40043c0c00c91803561038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 658543237 1250 658541987 658542019
    0xf31050105070f03150909020a051009151706010f121e0c090305030a08040c03080f1321030507060b0405100e06011715040b04051801050c2d0405 64
    0x100891142d5156124590307144000e140850803603c05a114070b4000c01c542d4024031042c486684945020391011b003500030241d80340d40c0020b854a80903001d000001d640b510042c448091940114140c1c0012410725503d50070b24000c0302800000028420f030f0401410401c034013603440c40381104182850300d8401c10000c41840541c801c4904401180e43c0e2000c40c1020940070006108101a00031a60070402841c18035800c40811034070b00e01e001d041070341d0740001202c000c070128a00c00b0007030524034042000e2581d84c07040303c1d5080112269a51206800c1d0701d01e202e4503858189032034509150705074103241095580329145840d13070080c030350703410b865401610f441c0400540340d00d40c4080310305480302c00740c005401d0755a80e001180ea40c0300d03850000c1180c0400c0f50200e1180c1541c1d021651174204000c0000c9080718084001c038040b19401c844410251182c0402c07020b074200b0a1080d1502311001004040c1f405074946801c19600f01c0304d2038260704802d8190451302c100c00748641506d0141000522640403242018 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 658544487 1250 658543237 658543241
    0x1050d12032c070e0103030f0f020a060f050109140108070603090501020d0c0f2a030e0d0501050c04150201050105030c09040201180902030a05060105070c0b1c0504290f310501 77
    0x4010300d1030074802c900002c0f804041c42c00203a41207d5142e69140600c0c0c52500b02244c413000580007200540c801d4441c0c0100091300e41c020320960165030500050700d507142000c018240c0342d01155401c2c1c00142c0704010303c14048007042403016603400d8100030800c4d401a00c0c21600900c588000d42c58000d1070041ca807141c1036802410340344107450b29038950b801d01b105d8400e03000604d0346481082c070000c041c003010200041d0103000e540a08a000528507401042c0e40c3e11a2425203400301c1d140b00f0504800582482006600d8800781c0500901e48000c209543c10040466500d80780f41e0303e0184200484000075086a00c1100b4103200303048941d611402d510b80e1212a003010350415038000b04840c1c00c100004207154894410f5500b6150000b03440d01401380340c000030900960145855031a43e88d60400c00500c01001d03030140d01d0081d0321800c141e040c800020031141c9100101c03000341c40f80344480e420a1140c00720140032140e410083c0a044842540c20000d54503804413207940d010104018581a020148039040d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 658545737 1250 658544487 658544561
    0xa060c11190201020f03041d0a0204080613030201110c03031b0403020a0608091c08070315050411040305011802060409050705040e09030a030501060801050d140f0a08031e01050d1203 80
    0x4c1e0201d03480340800e508407984078040d5005803400c1c0c8035032845c519600d4403a405c8154208480c600010300e8240c503a440103051502c11218060307450b01c045040c1080660900c2019140001c00c22624100214110425201c0c80064401103412513031030205400030705041d00300d400441c1e00a021581082d41c80e40041d003590340071101102d0501650000c4014550b0b150400c007402e01c101d82c0d84041302e94032040c040c0d0003000c100700c210036101c0f004440814503407114410b0400c1031a541042544503440e51611900399028001c440410f24080d1481000603182d09090350151869007801240a40e9000c4c02190b250113194840d050070202c17402841603c410200c01401003c866607400e1203507a8a554054403808020300c50503170070680e03034411741c0e0106220030350011a190246080d103940c1c06541c04030328644011584203580124002061045031000c95a44006252260000218942c54880014600c0304d4100740540030b200d5181c1c0d2481d410744a42d001e10b08209280150320700c41018506032042e91004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 658546987 1250 658545737 658545739
    0x30919051f1103040b031333050c0a1b1106160203100b091303091d072c041a09040c0906050118150507080c01051b0a020a060c111902 59
    0x841e14041840302e4000c0200e4082d102c3d5004164556160200415401ca201c0101a90812010345031810b01c920b05606504159042d404595a8a000010000112903001c1d00c0c0c022502020049020710341d03001484c1d0502160421b441e05600f6245042c503101280707480342c500d42d101c400040d281c0041141c0b810240c01060003581100c1c0403265942070003003140d2526040c0e0754014050000541c0c441046072402d40500d11030328000c243c0568465015020740703030084000e000110b100c8104140c1d960300081c4130018030005c1005400040341038504221100c2c030140c3d624000c1d500d42e400701c5249011a64403010900001e44000001d04e05400c2111340c10321180100c484550401c040000c0c01d612a4042d004416800c19028031a545070000d0f06022165080400003440342c20300100000c114100c02402d42c02c021003002041c540341c80d07a04005141107503900601584014006001803550016920300e06a0340201e000441402425083d00c0700000f4a11401c903502c1a2813500075041c2d58250103501440c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 658548237 1250 658546987 658546997
    0x170a0c05030a03050a1b0e12030409090b15013b1e0103110913051b0309060709360e0d031b141207120203040303090209060103050702030919051f 64
    0x280b01030207034001b429224030710000070003640980c1810300d003e03030203003a0250344d0100311b034a071680d504001025640c1c080c00c00d4487c910050708003c51a20000c0070f40004020901c1d29101c00b115102d5900c80115903c0d0301e107101840c41083c2c0701c400c01c0b4401489101003e004050165801c0690300765401e14046a17140c0340080d050410350303406c0907601416034201c1c1030000c014507610390400b0000700c000c013001441d0200e044204480e903054600303981c00650042030102c002e003030940707001440030b8041d441c1c0d507002034080310000f03545c0000040e940b00849104101d04140804400c1400d800801500c19410056a2802000025148950590f1050402100644028002005090f001c0d1840c1c4545000c0e5040300004100c02c40c400545142e80580c018843c0c2000031000300c542c5043c104032f80003110110007203591003d00c40c0030f52508034405a440a000d28080c1728510307000000940301d01400f1801ca020303043c00c190742c002210307807000d07070708c02400003d404408070310385c917240c100c4400300c040d160200030036 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 658549487 1250 658548237 658548251
    0x1180c290d1527150605160c03062a080c070f2103060f0f0518100e31110d0807150c1803050d050d380904170a0c05030a03050a 56
    0x41312811010100d900d60340b80e075410301c1c0700b000806000c00803046080b00c505013000404400540c05214141442c0851200d5200d58100341c5d04080b403020b42c80d108801401241c00421032603032410b204807000254032168248028005161082c07024a0030041120241c0b9000c0910404c00c0d850762040b81182e800b020034501180c1c0e85c0d130303041d80070b00c015003d86908038180321103051100d41b07070302540f07600050429406110300341c2c1c2d590648900c84e816101240305002e8880740c440c0b03140301c00e005a010600b5a100070358a0b00000d60b00d480482c0380c03810200d4000c80b503291209052050030380940f0511074012820340e800c07843c0900303110b00901c03117082090b0104001c00c040705d441080c807004a006890340030006199048629000f070301c080e0804040c0e00c0d01c054403440d403209000b01c50b5044111f0b45144410600501702141500000003d080d58018000c03a118410040490803984c1c4280c0500540750801f5038a601c2c51100321000c6042c45c1c0d001d40341c1d1100203560894941e043c1d20040c032440c4c600c40100010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 658550737 1250 658549487 658549511
    0xb01030501150f1707030f060e0f04150e150604050f07020a110d0819030b042a0e0307170c06040b09100201180c290d1527 54
    0x103540038002c80c1ca110344104085181607000f09100e007094a0307503060550103a10501c0c1542d1502e40c0440c5c405d030000351981400303100c8080c1805080d0180015525801c0685040d5441644405000300080c040301d42031800d90900c00303003551241c0c0d00e8009020039260344502806a5061006042d10b08074043c500e8000012030004070303585142c2c01020140d010b030088441645400c0b9609030003120311075100e856180e616001825010080a44146d1100265074803280c0c200c0140c100c41c04a40340e1f0380034604103000803101c2c08001204d4129185610114685014140811100e01b00700d423200b070381c041c41450000720360481541c18030a0001c1c08a0122100c0181050034040c0ba80207900c150008440306000840880c03030507000040d00d2600a200004145030070660302205840c0044054440741600b11003407105840f03005084450483c03042c071800c10440d900c3d0700321030248135000f1945c5d4079a6981d4881901000520311050042042d2841c085001340070345401d40c1014601010811002c0c500049810b413 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 658551987 1250 658550737 658550741
    0x8070e040b0403081b0a0206090609071a0d0f090c09050c2104021210020c060901060506040e0c0f07081b15190f020c0c01120e0604140a06060b0d0b0103 67
    0x21456010100000342e03150395034190b501c26005024040610281c000080c0d88200200181607089000e60080c074903805c260300f41c1da06046d00905940401d8008800078480e034410040348182d403050308440e6175651011101d0300401005030340c1c42e08400d035003440340078010301948280c60b03003c3da00d00030000c020b140c88240303c03d001d034801c141c1c00403d9584440700319140e092a001c0d84030391050000e418031101031414014103003001d4000e603c2e809201ea0124100890800820141b50b218403035000801a07541080c002560030300651140580380d4184d28005210500e40b001503807003440401c0400c9899504c9440d0440c11900b01442641d03e012a54102e41d4034001700041c0c2440584040744544200d44030481d032000030454070b50030400882d84849003051180c0e6103100808510010320090b00e5000501c1000400141d481808401150f003400100e505200700400c3d4990010fa0211184900700c9950100b982020b05000020340214a01903000036810a44401002c5924401e04200541c108901c01503003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 658553237 1250 658551987 658551991
    0x6020403151509020c0a1a10120503040e090316080a121e053607051012090201030b090f01030b0c07030912020118030c030209010e0c16110604030303020408070e 71
    0x103000c402c0c040400c0420180d034014042c00c217048040e2000101561590712100421012405440100300c041054500010002101a200d4660b8488041c889602d91950b680030728040c52000a42c2c2c07401141d820314081048501c8500074803100441040582016203641d00301888540201d9003c20350f2203d840054441c1d440100820f117802d070800c01030221000001c2c03900500c141460500d80c1745d40e528032034a101040c60050f40f41c841d22240041d840000b68200b130728941c0100d02858840e0004040e407a08201a1880158500c070002100c010b2400100d0180c40ca200040b030704074030200140810400c0c0500c1d01c5060328000c414050643d140c1c00b00000a61007900d001400145406000740440c40c4100f0285034118014500b140107206034000c88040c40c0f44681c0211421089420304008501f0681000341c010010301000b8007403031405883e820394600c00c0c0300881d250808074030f004004002c6250403003c640540a0901e644542d100d140141c020343c031600810034640b09412000642001c00c40001d8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 658554487 1250 658553237 658553261
    0xf0102030709050a08100e070b0c1c031803030c0e0a1403010c02160e041401020a05071e030c0803071101050112060e01052a040302040507122016030905030303040602040315 76
    0x80c0c4584a400c184011f2a51606544032405881c400056100103280500312041c280809400428601d040204000d002c0f8881401494241405008008080240d1150190301400c000c28901000a005c03280700380190b11042d0700090a03140031603080844c90340704482210a5008020001c16070006a07694400c2110035090100a0441400b030980c001c40140e4000344140c04410a00360000b007040e00b6038115000000000c0c90120300c2c0001c0c0801510b00e0504800440c1c5c00341041426900c000304040340041d0702800580f000000701e02030521514004040701843c1d40200b14550b1584005090030708800d0090701c04505144030200118010b01c209401448054600541058041c020701030348001d21a0710f10080710180000030150b151806180e10903892540c41d00c003031100d090b21190440b500d01c10f20314803141b804c11804104000b0396003200e24928451406249070030191900312030750801900b1894160101005201c1000059000340003900e20441e0044410742c004030141c4216041c848680c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 658555737 1250 658554487 658554493
    0x60f09061d070f0b0d06051f08100e07030c18090c02070b12010e060a090212010609080a0b070302090f0d0c030311060c04060c060b0d0308011401050c03070816050f0102030709050a08 80
    0x40250f01300460040148000d0341d040425010343e030310009111a1464203c809041c0e14401c240c02c403065120907402c0e4445c0c0b8064100d040320b400c1802c00030001030018800420300d96205101140140506000e1036410f6001c42c0110302603844425001c00f070046858018054850003802103000c524a009469100c8100031000d80b20ba0710f01002107000c01000f07040e143c0c07c40000f00000c11000d4040c00140600b00e000c08a10301554900540208480c803154840030858002c20040c10005124400c460340000c0d40c1d10b00961140c51504c0004c00021f2000e02c2c1590089001e1b0410040009607003c05d02180d00944030549140351040c0900d4039032408a6034040c01c0d03001084180305082c01382c003000c6010f074022100080c02c4880c13140810504040117205030080f80c44130004000859103032402e501d44601c203181040c24901a10103950380c90140b802c0c0241403443c0070400924030a0a880030b403c0d441c0d04602218210030b0107842a0b070007944180c4040c0700081c50050081414207000701090b0440e6011030003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 658556987 1250 658555737 658555739
    0x527190f1107060c05070c24090305031c0f0e0714030703051c0c060218030d02390319050606040501050916111b040612020a030807060f09061d070f 65
    0x10f490083c22004040801d001061140ba0080b485c3c031007111025020500d803040420546010400310004100d00c02d00c00c01c1030b080b0040c000920003200b90b509940c2c40c940c80b0001030b0003c2074010007030b00c80d07021032684444c5451000f00e049940080d0038811107076801e45031103650101384249500c42c0c0e00c5010140403944242c9101c01c40d02d10594110421040c24541552481c0840c2d4440059a03c04429000031501c245000e20080c0b0707060041d2800c600701c0b40010500c072011078050302248910103900c0000280c0e900c1f05414204800000d400c200072008003660000e500d08803100c0c0b82d20a03000c0084d5002e2096100040107400c0c2031240358141d500c0246100b60541d9450744010041e100d49220800300501c650900f20948003c1041d4994503078180414000c901d00d0400340000c842050788406040c2d102d0700001000f41c0c48600148069941103034055564100d0350601c4070141c146056141e048919005401c0300340041544151040703890b030a8019291340300c90107044e0380d0309054000c45c4102544c1c03406c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 658558237 1250 658556987 658556993
    0x211b050a240f020a06050406060303260c0a02030f041e0e01080a080c030c0a03081905131e0f08030f09060601080f060f030303090609120406090527190f1107 69
    0x1c50581d84565500c100d5507500d01390394840741910829141120b802d621810140101600006141ca1410b8150305405038035448450540301110058202060301c00c00007000c5d90341030b1090003128150004094069550355940070000d40380c0501071820310502c1d00d031500205071501c20356034090407a00460300401c400842034641180aa03c80c1c0c030806014031082084803509039051100c117403001d0080c6c40720a91032401000104d88581c0702048000414904020014184e85003028144020b800030541400e4807e4461a01c0c1c1c1003440100240c44046812191803c00c170f50352004500c0b440d03000401140d180c99000c2903d60715601903ca203404136050a0000e9002c1850004ac194000f800601c1c100109003817001203820740e03000381e54007190342e00030804118500d034041244102800a8422283c03800d898058009c1c1641d2250003002c0c8203044644003100060b502c0040b65620b1100350700790360300c40d041041e460703d2041c0001d1003081c0928108031420303004c0c00580c4100c074451540e8800c00742c507142240e5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 658559487 1250 658558237 658558247
    0xc0709021303020904032109020d260408010c1706130b040f020c0c0f09010506030a0c02010f0f020a0906020d09030204020c15070503070225211b050a24 67
    0x504450078001400001580e0b035042c90500682c06074544042c40640f0380c0c003401010f8010707401e000c130003030405110000580b142908903800300c0d0440e4031281d80c62031484000800d884a21111400d0035008180860104019844072000d0245030b184e406000c1d1480c01c210b0511344048603000c0d806846401508801d400315080181d0168000f03000050a000d1240f900e0103d82000300c0004407a0b0044034140020308005100368a8220201ca4541966140a0018446120042c03144403015201c0307507450a0756000750003125420b02940400c0c05440c86102d110002134001400c003c000400e94007000451a0000c5502030064620f550f4003100d480c2503800b0f00c40a580100300460a921a15070300c0c0404281004c0f0b420301854080d90391a9a034240040b0003490002821556108101c1c0b11005005580a515800d411209080304004644544591022140c0440c500103012059030803074800340311485000101c140c640490303540341c42139103421811603d024403255580c02040713079040940140c1d001c4e0b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 658560737 1250 658559487 658559497
    0xe070210060311130b1e040b2b0c05220507090515090d150501081011160201110d09150201050919080f0c030a030c08160e01050c070e07140c070902 65
    0x1071131020814110190204020041c1c0c1412400380c4401ca8040172201c1c40c19014680030b002080343c0001c15999030003c040744410308940520070107060305003600e080101c0307003207001e0040000078484141000303007011450300380c0d4480c84900d1040d4070b000006400c0d0740c010f96540090ba103004d80520780d0107005500c001030340c3d030080c01003592014900300c0d14030001e046c800310101c2086280001142741c2d40340004051821092fa000449402e0400785e05c01007a0007880c090f102000700e869581481c10f0b0702030005a444147c00644414103000f41400500000e4215500b101229101c40341c008480d654414120f08860342902c0840450700960f60000c03254804200300140c581c0503030155407604c0001e1111244542c000182c985540d0000302c1d4031108a60140b181d0f40c1c4140700c038107200e040c0707240c900d0403200ea21520888940500180d1110550140d10820664880440d803004964142d80c851402c079400c50003c03100c8100060f1100340d80590056014140c803410301070800202810f905000e45900a5002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 658561987 1250 658560737 658560769
    0x903020a0215070c1202040b03030408030a030213080a05060609060a0303020601121106131509030807020904060e011a031e031b10090b0601030c0518091902040e070210060311 77
    0x40c04103070085244c01c2c04c4e000041c070a8000d03034020007541c0e2060005440c00c40f02000c0c8240c0081c80100065000801103a14100321031500503030302d8089040c2840e07007031996000143c1c03d1044005050810a0003da11406410221601c034210341c0c03441d0810024414901009005800040040200c80e815900829619125042009007690b44402040c07103a0482c4c60b0011030080380c1441040341c081031000c000640302030792503c40701860541d124680c0d5480781c41e40081c083c0c03021400103000d2250b254032908038800900024414018001114008103502601480c4070f030060414080c00312403c03006003411200068003550801c000c46161000640c0c0c0c8035031680d028019424541d00709003807446031149251103080144800c0c10100001011100508203502c00c0c000c0412950807a07090b4041109004401207600e10344036502c910300c0d4021f81011b1514103c130745001003404103450100d91040f511070303246a800c0b50188038002d11b041e02904d499101c040c1c8100c8201c02100e6003070070040403540786804 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 658563237 1250 658561987 658562029
    0x11104120c080f1f1407180504060609050307050603040f030f020c1f1b0c0b0d090209010306020405120a120815130e01060821030718090204050907030903020a02 71
    0x99145100c0d420700e103904401d44015003003400108000403013414079203401c0000003020440030048283c0d004071024003400c1d006c28043d45050b440850040143e81d0400360002400503c42c99990300c030081c01c074480c18000c3d18860f02583e00301203901c1c00e00800b90b0b031003182c207d075821103402c0c800c1d203054801c0c0306000603070300860052400d0054540c480007080f62164151107007030000a4000d080042801c2d1001000717081640d0f10704410408602d034160498241c13800003103051b80d2448000808030060101d0040290031201d6407000000b84805903028204850003a24005981800c4102c80b5449140c2c5480c024001c0350004c00c558800c52140108692020265010b03010241128001440c9200d04005041d803540c0c40e4144100a400c007802080c0080031000000c0c4007811400ea008680d43d031400c500021100808800540c45610034103000201c800d2100d000c1c0c0c842a100c0c11050301a50103801494015000c180114070758070b00c00e100304000300d40c141e409070025000f02e9081020209a00001c018102 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 658564487 1250 658563237 658563239
    0x10e04020d1a0402040c11060c030c0d15030b010506310815011a09090a0f090c0605040f060503060612090309031014060a2306040918060e011104120c 66
    0x341103400b0803680003203030702044000303450188100001d079440e5803100801c20180500c05144030ba00060690342141c002811580c80f540c0c1d0107518041070042c51080885103003000140e10310b00c001c031409501600d00500c0807200a0380c0361410f201891040c005040344101c1d03540454005201c08220000003101c0210b00d44407030542d200b894901c1c21042100b46410a1000c1c070040103000c0343c2c28000c820026480103450f04140caa840014501c0714003c01e100b0190b0f8850701406d5885249510030354401c0e5002c00700070b0b2201c1d11404024101e800500135108043c0b191840444c041d800b58007524420040208480e1400e031818a0a640c3ca402c05808116a40b2040c4140c030003d5405024507000f001510600281d1500d44c0c0020626514003e00007034050b10110f107050100c1025000340012100280d001d2440800085003c65106d118651059130494540410303408904007000e0640e400b140075001c04e014440b00c07a4640f500700c0c1d108800f01e6212280411042080c1c03c076502c01c0c0c81449000740ca1240d501 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 658565737 1250 658564487 658564493
    0x50307050a05130e0a1d070506070809030703020607030503040501050601090b0901030c02120c0a030e090709050d050a0203010c0e100f08060d0204150806061e01020c0f0d060e0c040c0512010e04020d 87
    0x600c190b1742c0040480d150001d0b402114690802d800149144038020300c0030900d000086030441c030030403001410109001600030354607102044500000d40e8040d00071507403409641001401d81d0001d8400710741950a04020651641c4510201001e40b20070202c80c510301107400005400800558102d0001d5024109a0b880070501800c0507241c02064100540803075645854010b080e6100d00030701a10800300c04050060850b8044804030998400f5118494055102e051503450038502c840001e60560a00c800410610790003448656800d1003610234903402001050700b03807400390b0f10380b0500300052202c1c4006041c5150002000c22914009040041c0e2032001e8481c0c00f0b051030703441d080410164040014400780c3c0c20440c1c403903101244900d04504250f840100000e448034121950517200d0410010880102d99803c0079112600b41d02c084100926071045c000035840d107400c0711810740300d103284c20f036040a000d00034402c0b6024508034204424480c3e081406c0b03080000d4001c2e001341d8000000038110000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 658566987 1250 658565737 658565759
    0x6051c0f0b01020111040b12090f0d030906051e0f0a1107060c0216080a020d030e1002010c08011502100903170a02030a0b10081503190b16050307050a0513 68
    0x40030210362011805850010019082d20441d021046698208120030440700f0b0407482541c020248040c0841202c0e00c420181c3c0d49441c140e40c02403840703401079188003004290598421214103206031000e100640e1624452402d20243d900381704048220030001540c3d038107500042c0e41c1d00c02c910304000030b840c14024016201507003100100303c40b0950741c0c1454240320340e01081621808007280850088250400c082c0c2911030710842c40c024004d00f100007286003014040c80c0c0f1891901006051000368406200c070003800b03400100b0504011520aa00104081c204075000d907a00009513001051020440c0440d04000c0114440c00d5007048440c0440ba100840c0c0603410034040da0660b4009038a138101840800b003161288180240b0440d0b035600041d4031150000c5030b03107500c082c200e0b21003410000c921b400f19007030010002401c0e40146a031210030003002a2003500a00480403802c1040c002c00c0d190f0000e4070071f4842940c800d000300c0c10900c004505103200e68014252120b0343d0082e200e41036920891450 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 658568237 1250 658566987 658567001
    0x16080a0b0714040303020f1606050412080d050f041a061c110a0e0108010e0d080705161502273618011a0108130c05091602070905090706051c 62
    0x140c020307080f9013504045c200123000004001c2991400040e142c1800a0258420380c8125a0201120b04002041c4124801a01d140c20a1401d05020740e180080418152660403501150000200e914141068400800c034910a900180c0042c141c0040c1140c1d100c0340d4418424103c070f540400d84031041503516405442700091540e960b91001d00c2d4100480c2900b980d0b0a02280703030f110b500003412900031030b0740900441c0e081411820083e40e00c03040d601002492000310040944080751840e07070074201c4003641e80149100101070b40b0042c030222320b40c028a20401c02c1040f059510503034021210000340f00c3d1301010603141540010310402c0006203941c1280202c1c0803200107404298180c100c5e400c1d12401e0280c0d4095100318075481c4155a00c2c07000203050078070054203800d03906503040c40b42c00401c020380c05494058140240110072528007034810760310302c0225810480060040d604009000030890040c14000d03614400a01074031401c1c207004584942240f1900c9424800e001c1007990f0520462140c59 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 658569487 1250 658568237 658568243
    0x32a12020f0d2c0a03080403032c1f0506030d0e1f030606120e070b0a030608030705030a180b180126091c09031103010b0604060504050316080a0b07140403 68
    0x52124080700e0305443c141075402000e41003034004000440020780d000c440740d0b90103981418006002c001609000c0000c01c0c511095036408101c00c0900403000b9030018080f17034a040342c07032580000c0b04002c0030034100740d80703060b9040e0790598030142c1c00d2980360b40202d4000415101c0601740c0c000c2010300c40d0400e802403400407841c40110b50344100901006034084440f010301d8040100500426404403052555a0b000b44510700c00c10b00003041c0055440e10940002000741540400c89499200e141051500c80d44060382410120702e0b80e0108007042003106440e03d086070751034251103082200740991424841c031541020760410080007020191800e0100c02e442c0b40040c2e00c4280320040c900072001034580403400100e550030549803d40021007562181c45102a80d6000c01c0a014001072607010a0251076032140d0954400400b040c0490141d9200303019101b26803080741100c1c1440c080d41c402a1008155000360303c3c4c1500700784a4a03010415002045801440c141341c100300089100c014000383e6041a0011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 658570737 1250 658569487 658569521
    0x904180f08130b0910030c092c0a0605030a0b1f080a0b0601030e1b030a1a0910060605070212070b0307030b091f0513110703032a12020f0d 61
    0x11445842d10340c6040005005101c011510384070081c0001009603c1c904540c1c0708254a038043d0001140c89030099100a10b02e0000d50000e00410505120032003001180104240c0c00c00ea00240c10342c082c9003e51001c03101c0140192440c0f0056884403102404024460395084084003441c84000d45495160030081010070082c00743c6000a10f8000d400602c090049410103041040701841058003103004681504000d02c400700011000d00800d0030016950005403084d43c0a1039418441110340c0206031240c1480000e407017100d80710004103022545180524000110140075400050919100310000c807044031046882155603a88403100782d9100f00c1320130300081d0310b40301503940d0750900c18001504000ca4880042c9000481444410801080c0c07190910800c280c01e01e4140f0103080e5444500c1d0038450003000b654441060401801070142e00651890f6501c4840e1100c00c1112101d0b40d469482c0c0c01c9079a000144840748907520302a401c50640600c410804124003040c0561520414034140665040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 658571987 1250 658570737 658570747
    0x41d01090c0806030c0f01140301090b03060c13180e160f120b1b1e0a11010219030209060c16030b0705120604020d06180608010f0c050904180f08 64
    0x49005a8101c4501d580034095403800b44200d0355000704101440403416508a681260304000494549440c507550003000e15002001042007045900b01170586c010030740c200c0340d04c1c4e1a410318a00c01485020485201c05002b904180140c0c48d449460b400f040070718000100741703140d0354108542800700c0e4450310740310007c1041040006820b0002408003c1080152441d10569251101e0b03030000d00040924162203000382d2103216001c56032083d03030f4420780403101060006843c08124601c0f47d00642450700072a5100c9121503500b00705000312100310f00c035074410445450310b014064000e5000045880da2000040c0049510704c0310030400213070606406a140310b030382c42c13660400021a245c00351050013006800c200100c100c0402400a940110f01550016a81e005005252008000982080310400c0d00e00380f4044500c0c14079041300c010b8400c044003c002e01880003200d10100c41440c0d4010000c0341c002d026110305481e00394451101c044410f507440201080760390b10343d00403d08090f0121003800d00442c1e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 658573237 1250 658571987 658571999
    0x70b15150a1d2b0c0b0f07060b042703021c0207050f03030301050a0b0c03091503060102070f05030c040f1b0f0908010618020c07030503031504050f0f01150302041d01 73
    0x400381004400507625412039940729071a1865010515449145003420240d03e0b0080220791a401801417501c1403003203480d04000340a5550b0366200d003800b83c8026040c881c0c11940d500d00391160b01c50200106d141c1d09200444501c0392554884102c006800750300500c0902e02c042c0f54411801480d518280d40900034290604041080007550004064001d034400d0005014a407541040349094440c4410256150303040c1c80c07126441d610520521f9078020356036003000c01030003500802450107401c00340c081e114803a440e143c80c500e0780b80203071040c0d581c1a4080c0140700601e0800d680042d00e07040b003001001c41d81502e031130090102c000c5440400780c009103080308001801035000318103401a011a00090040318030307250b104c02103200c10b1011000b132254000b42e40c0740100f004001140081da841804d0765101d181c0510030000d903000ca040d0342802030341007400080c140d00d40c1017001c620941b03000b40e030310030b030390742800380d00c041d0740840744602004e05508200100d00d414a0081201e411b08203488090200d60403c2c2c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 658574487 1250 658573237 658573277
    0x1104170c09010f0810091208040f080d060905090f03030a0f020403141e03040f031509200f1f08060d210e0f100f050d0f02130605070b15150a 62
    0x40d280e02c81951030301c0303008000145100080d03487c80c540e62a007020303280c86a0501c101628407802c4001d00314400025103020500c9140c0144003242c2c070071401006645d403041c801a46510010300660390f2504100002011404d859000d5100c25200d0000181016140d0703807100031302843d404002c04103038020642e031080c6e0201c00d41010b00b40c4d03000101550030b2a00e0700d04082142e200c68000101b03a6008400355240324030090703018514854000c190807441c2c0003140d44811800814000301e90140d90550750310341036801c0500454580418401c2d80800400c070f80d1200722500302026043e168001d01c0201001c010402c81800e420001400d400040301071a148480500903030318000e5007901a40350054001314950354119040c3c120303010ba090a040700d000098085031f482c8102c1c6400120a0303d0084003107000301c0e4942c058840744621186280700d90303803a1710050b00d41f4010444020700b84450400041c1560f180e911480340040f002412800d401c1180e6403d04410760042016003001824a92080b0075000c081 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 658575737 1250 658574487 658574503
    0x1e220207060b09250c0213051008070b210a0b12011a01080c1e1b0f0f0606090a0905070b0a12060b0405100e120a08070b06041104170c09010f08 63
    0x10300e40d0222140d6250040b1101040c06400b144c05000d80340c2c00041c19500c80c0c00c030300c1502d80380611042000e4507048400740c10b02d035882d0080300010300c5003040114240100c0b9040f1104a601c0302c4591200100002c800c8140840041400e0305482e2100c0900c0b40e192030300070449004034000c9002140c246c0710401401c0c000440050300504109040052110012a640c112120404074407a48810020f44400c64500e910907502201c0d810380c0003c9000c624400c0224071a00e2540c400d00c15030311000c2e0719031682552a04c00b5030b5559408000c0601140030030709258443d00c010380c82141540c0d88160307030751005000c582041641038003284401e0044d1710304015034868140038002008065044c1070a260214441c0703c50140c140d0144400f46c010410f0f160355000728060034101100480354a001545000c1c48103400070a0200c1f14040414003103040c0d4a850b007d0008502c24814429080c28a020b0100300407040005152000780110103107220a0303243c040b541806400c0320a5100c4a0526001d00c0c03501d04500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 658576987 1250 658575737 658575751
    0x903030114180a09030216080c0102010e390303040f090507031b030e1c050703110a0206181314070e0d05030306100203120403080f061e220207060b09 66
    0x41ca90482d012240d200659400000000000030031508603c0e0030f07498617840b0312650a07215003c2500059021000a0130b00c8103a4003a8000d10145414510459030340c0c613108141c4000f8503095a8419809500d0100d03040225109080e00712811200c1010a0440d031054002158110241c6410b1210111034040d0030b0f08070704607240801c0401c1c20050003c0144204c40050000c060b1036281c1e103a00038000b0062403062052041c0940034202c01c84002a10961020300214080b9201c0a000c0c415003002056101a99401034002c503d08500004001c028600340c00c2d40a500807510f041c424604021481140306a588210b690021401d144202030105612003880e5407040c01c0640c0541c000960100959410070800c0e00c040f00030340411102030b13056000f0740301c000081681000412040c164404a26401243d24000060054561100740020740110702c203860000584015003c200303080410090030788590300c1ca4014100741e002040d00c016a4001034082d01d8041e250b4581201c503250000f00142c201070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 658578237 1250 658576987 658576999
    0x30f0215060f03010f0e0a03080f10030201080a0e0102070c090e070b071202030f03150103051602030712030605060d05010306050c1603030203040f0602030f09120309100902040b0301050903030114 86
    0x110402041010303210060007a4021410b141c0a0003071034070250840c240f811515076050009810360041c0903901d0000701e00503030000d030141c4049540b220003030303030303000d00032802c21099003000d07400e40c0c0041d41c00c0300c005441d03901c500d661003080741e030044020b03c05000840e1244c9031100c0114034003041c40c020303500c040d0f41d230781d2154125034005c02417000c0d180c01700c4180950081d0041564203035007900742e003140074048110030034010000c200241e6440c2021400c150000c00d132020030450300e8242112014805086281002d603000f000204d012a511b1458841d4003c940d28001c5603890f100e0011540f079030040c03680c840d00c1b41d0302c80b40180200210303401000d52041d06176101c6401d100885423000c0e0f083c8140000a828540c0c0000414184a51078020b0925a82c108005565178204500c000c0300c0e05400f100c043c50a80103504c64001c3d042049021640a020a1001441d00d210303c03403101301c0204040d61040368060354900d2a455161820f000e0340340301d010580040c64803503240981d0b41e5000081ca04180d40304030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 658579487 1250 658578237 658578253
    0x306010f020d050d0e0115030f061401050603040807060b060d0213080a080a050d060b030103080903190503191206030605070f02030a091211032a120a020603070909050c0304030f02 79
    0x10394420305480c00007902c9040454400d401c08170190041c80703ca01d01c411010344405c0c0c04401e1000d200301c40446907100b58820000c40e407610070006e03000b20007030250560110003040810b020801c02000391005600030030001400e10b600f02c0014146901c550005180d658000c0f402c3c0700c80054070075495005041100180c00310288aa640c14200d10404036548140f2502140003600d0075078561108000e04a8a4003041c0d4a50712420001048c0e0440b42900e84240706004142d520b14200b8541f18030728a91140c011400d083c2d1b82c4d001c01d00310381c03a000260f800f0012044011a8410b41e1801407100542c060140040e1506280340010040d04c4018208810356108008101700260b108083e181101c107170745149504017820346442c4e00007149810440740d062045882c0380b1103156044100030070310300300c5556640d242c0440c0e9083c06100c0351484441e80a0b03801520b41c04000d814454021944030b045072802c4c1c0d120644540c8a802250320580d4041c600b10700220810040640100300640e1701c00341800205105 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 658580737 1250 658579487 658579513
    0x1201170106060810090e1006090614030d1e050904020708070506010b070b0c03071e090e100305030d020708090a03050106180504080d1509020d0b0a09090203060403030b03031e0306010f02 82
    0x12132014400c205000d80ea0305400d200a1905000610321031400d1078050022070f075140202030292001d4051000c05200c0c01450307034101d1a001400c03144401043e19055058104c070481100d02d8107203010f41405120040011103595a124401803001a101e00b0000c1d44a080c242000351804130142c2050078210b00030804200070900074000306500c00180904240d40e59a81d500407110340e50700c4035800c0c031201e442441010580d034100f40303d8000e84041e00403000c0356035140031001030100210700c0040c02c290402c00400e0341e0400590018000035004400035490203400d0b4010031b0511055030301c2074945940d03c00f024407100740705003c1030a040c5000a401e0010b81030a40381d0400380e00c115284840419a00c1d9420034a40240008060040120070401c54603090801500b1010781420300c40c43d44982081c0b00c0c0400c1c8080c0d41d225124a0603000380003448580c0c0c0341d6600f0707070082c40c6803040650300d80710500007011141c940c0c90b002c1403094040c480b096140e05007400050503810141c070140003990045100c40c442 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 658581987 1250 658580737 658580761
    0x902040627030b010b1801050901090303050903032109060c03060901060e030c040c0504080111130302010c030908030409020c0c01081618240f0509030a030806040212011701060608 79
    0x81180300700d81c0c41c8455903034900307030321604101540000c14915140c00005141c0e002200a007000d610882803540c1d400c0003840045910348030301c545150210341e0707510341440800d00c503c010344841c62014080303a01d230010141084903495021101ca130100b991450030060034000038441550841c444401e15411130034400001504040140600c008004200d80c0d5a03040360b0b000c01c116100100050010000c0c61407089000701300340d019000e030244035030a0500c0c00f00703403640040c221400c0e20703100031040301094110b6004450a04003000d00340e0401402480124000d10f060009100514651100598030003010021038101070101c0c000c40e041c810781100b04101140d1001664070040b07141c1c80c101c010b01d100f06082d4018041c003134008180d0b102c2100c41603003407000010003c1041010544030f22060103c1248121414840d440209805820031501e200c00a4010501560402d80081c409402c00c4e11907521040010001d900c810030b500c01c1c010540706d8400080c400d140c013030941490001c1c00ca280c18030a40c0d803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 658583237 1250 658581987 658582007
    0x40603020366130506010203070f050c0a0e0402130e0708010c0c0b1f05100215041208011203170403030608030a0c060b06070c03170702030706120c0f0206130819051309020406 77
    0x41c40b5861340000f8035560701c01e204071070515034002d84a1003400d5583c01c01e541d0319041110003502460260300c02140c1180310380c18043c40341e40c0c003c0c001054011424203140242000141ea66034621074a070001c1400303182800b80c240201515900e41d10909140d00340101c55031400340408e6141c00782d1030322211072103084811000030348405440000c806c0a07803a400700d2400d001503c0381c1104201c0c0714144020440341c0b190803403414444d5070303902440da45c0b00e100366140d09030030400003000b1030720584507100d040c0000011580c2c414002c2c2000070720141d9802c502c606550010341c40034001231301e2403940030800025206800300d46d282900c124ac20101541d442845494460002812004824009201e0383c40c5070401c840900381e000d400d443e8500e541e41c00142c903190b8915030381c10506041540301c81d4614412813624030004419070043c000d43d10b41c6895055405040c0342d0030b50b4003400400000c1189200e0450201c4181d59690740d069458040d00c840814011040d0800b031074440c0100010801b040e84501c20300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 658584487 1250 658583237 658583269
    0xc0302070f0b060102161e062a1b060302091e030a020f1c05060108060a05060a030210090306060f09060f060509060f070b040b0f06040603020366 64
    0x150740b645510005034038100c840c01100700e40c004048000700d140010b1085004441d000c110491203420b8440368151107850300ca080d50580e61004801e001c0001d108004810f011900680b04c242c241e06541c0c1d80a03412030b0141e00000c1c0446d8000485000e2400c103a0b000e00c4040e801b400520184411401c0065220304000101034412094480540741e070750340c3c5000c8a940f4a0000c00d200403040351520b00f0a0b116036091003001401c3c040c61000174008000c1c2e00802e03100e400001c001e207030310505581c204041030840402403810803841c4d039404400140180701d25400303440a80851020a49080408020359085410052501c40c00540400c40141c0003010b030b40c0c0e804002c5840725141c4020740d0b5048454000c101b000341c4051712940600c020f1098051a16002d01045503001a13290350b51f10500c015102584002034166000000c0c002001120361000b00440c3c1c6200005c40c1e515484000b80d54110003c100c404500500c01c0503540684540716400d090340b0300d002d14206003092510303000503026002c2c036900c0b4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 658585737 1250 658584487 658584503
    0x10807050a110309060c0604031701150c03030f0509160605040e13020112020406030606030f0203090703020415081608060f0f0a020d0f020a12060518041e080705060a0c0302070f 78
    0x20b010200400d005469440c0380141c20b82d5100c0d8207442100c0d07601c0d0800c0d60301350003013030078000a64444080c09040c20b060340d0007850450320092001c1d074102d0740b010841100b5803c05581d01480c0f5260708640c05021301640d0001e0080620740da44410441c907204c903641c861401e01074108410030640300c11041c0564090908117135072980e0100c50006a40a960090320410454400140130800c1354055021006a40c0c8640d001c0000c1188046203400b244015500e84a659005002c1040144380540021000581c1b0012546881c3d42c0d81401c1d03845c210000e8882d81800c0c0f042d02702808104001c00c81213030f2020700a010001241070040407101144406403000e88540d4002400d64940c03c5560441e43c0c0c0c002c04034600b10350f07404802d40c0040c48003104400d82d01087d81030060001301440c0c10500d180c115894044c0550003038403642d0718400c00039102049001450608040e14000c5003802024107082c5000c0c1014255916202c1c03001c0e021188041140001d01d44140080c1c40480d03544070142003003540c04148 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 658586987 1250 658585737 658585757
    0x130f020a1d0708090312241216050d0818131107110d0c210b0117100515090907031406071107030b040803040303140903070c05030105010e0412090306050c0315010807050a 75
    0x1041f0103000c2c030080c006c0d801c05401c89031103501c010b00040d412200808846a02c40158803502040381d00c20b014030014000541c240b0a051903201d003d9403c42c5d0305003000300103400020181603524140c0b1040000c000102d5400b045000038048d6180c1c0c00c4881044c11100c3e038005501d1503039200000d107220300880c000c2c0036506807000c00d040d04e03a0501501c00da400c00c1d00c10340385680d58448010180018030400840e801100d60802403109039014547c000c3e9581104440c921030f8110602c00c804030000c0c1040300f03e200d141d05c002b02180c05040240d0307543c00c1100140c550b5103480710000d807032200744080718080381e8040c280810112307001041898000340d0000e03101c1da40b9200c90800310701600c1c0d101e40761300b06041034100380840d0240000c003c2080310b02c146910580c1658510030582220400d00c14011a00001800500080c070310070980b800042c11420121242600c075103425040b160704850302d09040030008203120803030b20500800c2040540900c0d0584081c9001c2100500034003405c1010014000300180f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 658588237 1250 658586987 658587031
    0xf060207053f061501120c080718050d0807020a120f0303020d020903011b02010c08150f060d02130311031b01050a09080a060f0b09130f020a1d0708090312 68
    0x303101a404050b00c044480328100402070052214844401c01c0c0460111800b54046600318010481d0b640d94540701c0041d642c1c0e40b00003d40e41c1900c610903991420849240103d45959040714402810b40903101058954100b41b062144104c0b413a00010340304410443d07a44000340c081080c1e0b10005501d454003689403100164000064021000030355410350a0000980b010075041c829111480c84030b500901c00300500c1001595008400d64001700d43d8016a05806a2030506000c444c0c2e191001070415498074002c100440103c1e04032800020380c80f040c0c41810421700032030064408421000310082c007000c401030f10141150f0320200303611074184900420b1007040140181e1070340c40104103003015502c01d85402d28007000104140031103502102c0c5081c14041480c104046010702c6030000099015140c203036504c80004104030818100da01801510b000b0924a00380f150112850f4014400070a50b403d083e07001a004c20401400f0381280d03481480041510f2411f1030340d10f07411014455a115040d901c0032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 658589487 1250 658588237 658588339
    0xb0403081b0a062009090f04050708060709050a14221107051c0c02030601030f15020c0d02060a0507050706051909030f0e0a030b2e0f06020705 63
    0x81001002030103640802e006210854201d80d039080310090406140803000c1c0009403850260540c86a0841a04030004144200254809400c14001d070304071a61141d440d0031052074040111941000200b1000042003d420911100d001a00b0700c91000d1140303411038000720310780d80355414081c082c0c400c8081406001040c030303511110002c0002500c05545541c242809036607200d102d80720045400c0804120000c09101352918010154000c1c00f42a140e407031901c415004141c1d0702c030203441b0400391510510400e5036030303c024110310b403031040609121000014042c0c01c1500042c18207400a0030302c0d007008070fa10790000c100c521f01c0358400000076003502c1d5070038100c045540190324084921f150038215010700d034000300820340c01c0349a03503954041e10140100784408007800d440010518051840410742074450402205201c0c021000141381325030b1201000d00f000e00003544008803c1e20320001c18400c0943c180b01150180ca0255400380105800c05500138221204e0304940000314029035801c603062a0301 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 658590737 1250 658589487 658589527
    0x1030b0f0301050703020a110f03160c05090f090d0e032d010c0509090106020705010804020402030604140117010c360b0c1005070c0302070302011b020a080d030b0a0b040308 76
    0x1e0000c0107546488180500294414254031000c203d44007070382d03d001400000c41da41c180700504051410407441c3c0c0d0b9a01d4240c09141c0b02203030341140301c0e01c0104036600c5281c05c0798403558000390480c2d050b00f00410300e1401d01002e80d180c034040060708105802151030024000042c0b84040707a00000c0400d40507270b41da60303c04642004406030350900b0311112107298040054400c0042c21035000300303181d994082c207036a160428414280800d01010000d001743c0380c554099503000c0d8010b4804902107a01c44840c81d4590002d03002031811b0b0b46401d902000e00a400d1084000103203180c1002a44400d0940000d030404c21001101400b03603103c4001446200582e00300c000080c40d04080c607941b1030701d0342e0254903160b080e201c0e900e1418500d0000000c004a1181d010002c00396056006448003038199001101c03810300b20040f441005140014030340040e112418140c1c01440070002501280040400003415a440e810324148130b2180c40d18180a29a440000c40e0100da0744070000c0c0ba9182c100a080304450380324 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 658591987 1250 658590737 658590739
    0x4090e0f1b04060b03180715020d05091c051c0309030207030609170313050606060a0e0f0f0d0302100605010504030c171c0201021804200711030307030c0308060301060e0601030b0f 79
    0x5c13081c041c0340d9840e40710700c0c85582c95500070380700300c19241d1020200c050b07031306020344005030301241c04061604d001d50010008000040c00029076001e07426004614007051020031280f0350b201a03440030500b41c002d05440c08140c101d2900303000500d01514000c0d581c012900020780043c0e9280b482104019803042085102c0b400310380b00b5603c03450a40d8030204d01e01007a00701030b6124020301d0005161450030314120342556a40b80ca40515101c0c00c05c040c0040c8444601c405500300f17040c803403084142ea907600c02c5c0b134440324030a50062400c002001090000c3d548107500013810300c1400c2c4414400101107400c1d040a85006242000d0000c3c040c0d90660f10b421545a0004480310b1101ca4600b031040d41034008112507107a4000344c8551008840030700045070134028108410100032400c1d10b141c2c0000000900e9114000c0f1030317001003544a00000f03425603102440c1200801c05860301c5004040d0441c610701d910400480007000030618240000c0010318000b00003034105662410180c18981d00c849034100f801c58 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 658593237 1250 658591987 658592009
    0x3110306010c0b0907030b190e03090919110d0e0c041406010507170a1706010905150d1d0717030a0c030e030a1505100f0b071b031704090e0f1b0406 65
    0xc3c03108c1441c01c92032003020b0500c2d200d4288054040340e1480002146c0c403200001c0c1142101c1c2c2e903903101c4a90900d5a228449401d542c23a140480c100540340406000d42c00310071040011408481c800c0d4034504094038110601039070824055280c00440480120360102c42030030010f503682030901c0c0045411481040154503180080790321075210340e10a41c0c1c05481c46000c10b05070b000351217405c0103491407001841150f03882060441c4005d03418078000d0241100d02004000418803031110048030072030030318218040342550700c03072300d000c000b400800780585114101c2c00001c0c5162141242004084c00514200901401204d022000c1d0300e171800c100e0014038a0304910043c110b4841442c80c100640700580c0d1841e00a500c601c3c000c1441034059481c070003218032503100079103003c9055440c41c200b03182e9188030b602c46001c1c000300007011803102c110070b130344d80c8040e80d0303119907914200b03021a411070340c400708000c56039801ba286200f5400c0c00001c0742c4060030303400b001044400c0808000500a80312503040302c0a086 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 658594487 1250 658593237 658593241
    0x31505150c071d0a0b0102150412020708010e030705160b1204020a0335040f1401020313090504021804050a0201030b03031903050f06040c1d0a0f060f03110306010c0b0907030b 77
    0x100c201ca000b640a600c461341c003800f481c07021100490740e0300e816001801ca492484000300d0000350403640c56070440341450040c0d50015a65056035801c50383e4601c10303092944c0002401e402041424404046400740341c041d1900001e091015042580c01410950a1760541c0b000105080d9603400442c000250761003009001c0744c2c1620900c11040d9041071f0300340181c3c100400407000550721040181c03000c2d00c030240907000c600c500c0c205609005841c201e0f8814194042006800c071100c140c041c095000c6c00202c440480c0a08041c818003004020300c036409001d90103214203102c00140045000741190340c0900c0c0100d9100d0000700000d040d84106401040403140003802d0440442d00350700000e10a07080c0070034160090b0740f00c40601c416500710160420014610500580d000c0c150301104640e44013000c0c1c85000103c0c4c03a05108182c60599402c140042012400c03104d64060b40b50164600c4600c1c05035410781142000342c0060211150050300074645038050000403e00c650030041200256040310003480c0324 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 658595737 1250 658594487 658594529
    0xb0301030c060311041806210210050f0a0509120f070e0a1b050a02010b130905060a050609040201110304050405071e0f0e01051809040804060f09050a120f1a07031505150c07 76
    0x1100010b030100e02a19002b02403c440e1030141b400d40701c01429034400c2c9032030850f01e08801c40300c0d9070054034100e5004209001d04401d100003081420510b40c0c601005102d07044c02c01d420003610010041c10104400d050060a08030700d043c03000c0d40c045480f403d017040c94541c541c40c00705a015001c950740841c0c101d101c0c0607003070300700c940c0b01d81181d03a03514051001d48411f0303220403680c00182c8104030341980e0040455400304005512030800d5100c410b0203402500d00f80354413140080c080d07840c2a40d243c800149407089028400c0c100c00780c0c81c03000301240d051006034070420180250081c03020440943c1885400700d004040c081d0100e400c0d0b014000002e003d841545080d14040714947c0290140d01d000a40000881c0c80c098000d0151a054480042611b14641d2600711840c000440c810070031141c01031422201c5000820355841c1c0c144111030003610500c5498402c00050840d01180103941e1440c241d84000c028a0311750744024950810f03603181c000d5a601044940c0b40c0b0f818501e0f0301880c148800514450f0078 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 658596987 1250 658595737 658595789
    0x3050d0b040c05090a1a09091312022404051005060105090604030c08011107050709110c15040b091f0207081e03070e0d11011d0a0b0301030c060311041806 68
    0x206a084803007400030394468031107203c03d036481c65107018404410000d440b1f1924080111030740c00004290040c45d4000c1d207694a610f94030f0101ea038a80583d000700411241c219668540480074151000003c280b841d2030b07214240d4034045807207546030456840000c00c416074800c80c01c1302c01801c07015002950b1644c0d6031500140d05011403048007983e529181d80c02543d0041c500c1250407484c5c02c40010302c4c91a0504061900030b28030700d2000303ea0b00c3e0081100c0714032644207201c24031011004060172125480c0c9821304070746144008105034519006a010010031f010000341e082e50072004040016141d4000b45031401c1d1501c100784900c02c4244150800e840b401900400541c0f00300942d030f6890889800300800c0c81261959030307000404805070744070040c9465100c1c00c0c800540c1004ea4180454840903540803540d0031074980c00400c2c01420000050040c000c59038010401040c1030b2801304501c51314440c0102881c09240124407055880d444a4076928950350011005000744106c0e108089040c0018044 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 658598237 1250 658596987 658596997
    0xb0304110f1309020420070c12080711010504030609140c030d0f080402030c0904080c2b27090606020c12060f070306030c0e0106020c01020c06030703110f03090f1e0a03050d0b040c05 80
    0x188c2019441011420b84900c805041e805680216282e0400d4041d944415544980900c1e03541000020308c030020102d4041d005102c0d0303d83c000d510b0324510a070190b0000e4200303815900894041e40c00030100c802d0b0943d0003620400c0b41d11141c50b1102031601d6501c0000c0c185003403510b040d60301201100621040c001c1d400028035503100c0080441d003100c0c004111380a03d82c201d6207003440c242d005103a00314100c1c80c0109203060078040b05014010405503003c4012210302004e41019081075a5841d090101d07580400c620451050201c54210921a0528480341d543c94001c024502407403401d0301003045a40240c000c2c1000d15484a1414072994030b41405402c1e088013481041e005108428031480c0f00d50001c2110104480080c100c00d00c0c1d0354400c030060b00a4940001b42d018007210410a4140c0d40d10b4140145001d0b490b1600030700301044038009450301e0324800025024100034110500f0000b010001800585030341e01d824101d17255031135800751038002c01c0020300503a0424240940d404800780e000000f00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 658599487 1250 658598237 658598243
    0x11401020c06120115170a1805100509010605153001091a011e031503020a1202040506221a100f110c01091e050a0b0304110f130902042007 61
    0x150901240c500c1140e0180286c51440c1102c0c0151300851300000007a0440400d0a14640b01c0780281c40160765810310b003c11001030301c0389140c4e642d0b0902c40503440a0003110001c0c1401c40e402503002200800c025913a1003541c1c0c00300340c6800c0f04013401e40c440c204c88c00004450b580c9a0350100b025a5a102144040c280200900f102c1c10300300b00f0340103001d40c094005118070045200c1240740e0181e81c584180c0c020718464000d01c1041d0800c1c40008016640e07260b9000182418041c4840c003c1620b20500080da54081c0ca100e05c5880440d240100800044a04003c07e0101980c0492204c02581c450b060a005085400c0c3e088886041e55520b0360f60000500b0f40c040318103990b03244100440c80441a203640c00c03e20308a00150307508100300000b04800b4080c40244000c0761034018001d80d80d42c0050f044090702e51181506400c04000c000601c0b0790350b841019900425503540181501c4040004d0302000c2c1042418900d03070f41c6482400946d00e82d0342c0401182500c240c0d6003110f010001c2081074094000030401c07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 658600737 1250 658599487 658599509
    0x2161b03170c0606090606040b0703090f0611190c03060203040b06010f050a0c0f0c08010c080108070504090b13060b040203090c1309080a0804060f02030a02042c011401020c061201 79
    0x10032051a07000048400c42288000a01000e84a4208010b9240b9000d80b00c182c1c0a40700b03120206044034004000c000580c4240ca0352280b141c6400078443c4034821703562141050083c404c420070902c0ca0049198010703450740c15401c000c00700481c602200c0c1116560809058288040100820231240700102070165000762100804c02c00701d0001114148903064801340003a40240880000500c8425406001c2c1c0c800c0f40100407094503411074508441c25420780c08000380740803004001256051000c0005008103480c1800101c0564590100100340640100308804c248194a82880180e5120b11210000108291f5903070411000780d5503524860890207214a0454050020401062103800721255104000070700300300d01090306890300c0c4402042945d22644500f000c405186a0b440190b00c111600480161294181007948402c038440d070300c04291900850072003e1050054016450441e0301380f54112407030f00c040e000100e04042002c121150080f1001c50501400100c0d0079889060b20720801d40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 658601987 1250 658600737 658600763
    0xc0f0d05061804050d051608210a450303051801060f090c0c061b030e0c0901090b0a0519080f1516031d0604030e0406030201020304050402161b03 64
    0x41c010290107407402441036100082c01c1a40501801c090144c26254403a103860b506a90748858006500013051195030f000c01040c0240b040c40340901e03103908140b50800820131201507480b900c1c040900c16021100202c1211690750030410440b102001c0070346c081c219800750724bca9150280180070181e645a5001d034402803550f40034201440381204484d040c1d0003840703010b4a40ba500f8001802c034040e02d0300810003508100400701d111805003d0f41c400001d40c8804421850101c024115500c64842c3e05003a08401c118140035030315250a039056070095240010382c1080400050a5640c40341d11850f08034900500030403071200110011411501040191641c44040603001a1264140f0030310300d140388040b03004074080840903410141018528200021005017418901605a80308030100d0004d5000b20700b08410598400d40402c0700580c01d5900b4000141158000303502d03401b80340600c90203190301082801503210b1a000f181707915908211301046900d4ac0012601e10f10915020a072114400188 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 658603237 1250 658601987 658602019
    0x10f0606020307030503060409030c17070308150d1506080f01090203070b0301050a060e030a0b0103080a0f0e0310231003060c08060904021c02040f020414030c060708030c0f0d0506 79
    0x8112441c03031340d050396164910380d1064104401003190034000e07010403c0300d0514000140942d818060340c640494042c0b5143c1030145801008000000c00344000e0080e80d00d50942c941d29058005ca00d1030b80c1c04480303481c0600050742c000000782025840490948104042c1c003107a82c10660121204500030381c283d0b12600d0711203042c9001e41c442841140e802c40c9060104018041c41054004820f403801002c0d5866100c260301c8203000080700380c0099941e040c0c00602146416001408541d4410340b9082c048420303c811f000103030701c0d800c4054464100544844124001d5840305010249004108486a180b4100500010641c1c05580001c50b442d178a0034580241c800c1c01407004500c190002031140300e290760b50368288201e130744100c0e250002007200e2090b9200140e840340210442150250001070b101d525141e40280010f003c004124003030707000a002a04951584012503c403607402c010425a240c8070b21031000813a00c564680285800c40224200d14000340640145002d100c04651001015568007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 658604487 1250 658603237 658603243
    0xa020a1b1404090b011512060f0e06090405030a0c020a0806010b1c05011505091c0809040f11090603061503071e0806031c020c06030108030c0f2413050f010f060602 72
    0x2502402204ea00801044189045007007100710412915140d003a5207036248034001501c41c039402104d42048041c4040c001260212900d80c3d0047c400c0703403501d0442c103254460507240d01c00d158810007041200b001e1b060540d181e40000c41c0c0145288000c961444d0396610580d40c990300800490006d05054001c120500026800b07554180c414130070304e5040c0041d10103000e03a580da03c08140d10381c20030480e074075094260380d00302e1030006090b001e6044c055a03582e88100300021075015030402c850711440c000740c40d508541a802580d80400341903072601c4d075a46030700f070000303c2501c1d4466103400a03c20000400a981b6400300d002205405003045282c42341d24900000c0e11014402c80b4415003586c882c4041c00c0c00641c0028048400c1401c60040d66451a103405c081403440c0e0090300f000c40141e000181d0307803607501d00030001f43d62044205000b5000c1c10210345281c03401000b18040410a0030000701c0844c8080580e031564251070350f444012201081c007007410389406801011010140c845c07502c44001241c0d8004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 658605737 1250 658604487 658604501
    0x60c080411010e0a09140105030c03071d0603012d14070c171b01020705070815130201021c32040303050c010f0603080c2404080a020a1b1404 62
    0x209450001c950203160044405401003080164048249000040c441d225885004002203000450484941c182010325280c1000c908810b40280c0c400c890401c0100761444907c11a40756808e10f0003070948a40001902409191260364040c001214041ea1030145c0040c0382c00880349440014060400d43e11001014108110382d03010124262031044400038040d100803910b0450f94403281d030f003000c80300f00c88500d81060070701c14804143e600107004000e0050810140008042100080c05802005051326003c040e0140000c1c85a001d5030180c1c2c1c045a00911442410891b000103200c0e41d948402c2d4001c0080081480308940034240007554105868043e681c0010b260391507800c146031518550703003240c40340d202c41c04115882d5a11004a440c0d0710790303402000c000b980620181c0c2d40340d68560103041d0604450800c250028045041403101c80380c011003442d581b0540020700c5a484501c1c10005030304001c580c030001000344500f180d22000306d02c444002c01c030690f01004030301c00071801a5400d000440e595 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 658606987 1250 658605737 658605743
    0x7030c0f050d15090605010b040617010f060f0c150614010816180b0304030f0906020609070302010e010201020d050901020408070806190507021207052b0f051b0601090504060c0804 79
    0x1c19804a202030100c0c040c100e80c0c1c03290002e20061305484000450303c003171700f1240c080440000c0c00c000b90b95001400401c0080c005407140d00035450140d902e12014070078810141400340c0c40c601e40d030a0600903240c10050359040350b00e0b0321580c11134101e484001d25081c012110f100c0304011942d0701c5540310780d000360710400ea004103290840726540070942c0c08889030f04603826044045800840d00075a0b040103140a18402d48610204070311294001e88104940e070400d0045500a404200000d5030015080c8101c1c1d40a0804c0c500902100004038068810142c00328600790921062080c0e20405500410445c0da042d4251505240c85582003034541c5020784420400c080c1c015941e2502880590005030041100d00407601d102801c04010001608440d60961b00303070f0400071515001c12241c0000c1a00001c00004e00b00910754a08005082000c0c0751120302c0c10440d0204040030740f480699200e8900c10140011180c1039a9200d4181d00505811102100e12a052025050301d03140200e0200380134680c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 658608237 1250 658606987 658606999
    0x603021c0b0112150807090b0109050d05060c0a30060909110402280806010206010f03050619060b0c03030907062d0e0d03020f0c1f080c0403080c07030c0f05 69
    0x1981c1c80700f84024203200000c0d01c000300030310300d0000303500801000320200a040c402c17001300e881206080003501441c0380354012402284000c007003900185001c40c001e03078800d140519944e10341c406e41000f00e51503006c4890700f031003425110480c61414241c0d8213242c042c0c180944803d020003a282c220000a89810b6800184181596010120303249800d4025040007401d4543c84070f09600c8010304400f0070283d401ca80710100304121305000480d641404143c2c09481d801c1415801c41e0b1039541d40a55462000f0859983c07295034610780c118010740307504103800910809001e940c07602120828152aa8416524504180f1030784200040340d80c001c10b5802100b00d503000c141042900807030340410b0301860361540001002403201c045485c3e6a0f80090250a16010323030300074848082240c45080c50564260400c51050101d0f43d501d81454588050880f2035104074940b03142141c4445958401c50300076a00700804080c0701040c0820b00c444001000341c01c8074055008040070b155110004403040c0182c3c010a50881 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 658609487 1250 658608237 658608257
    0xa0c02220f02090307050d1a0f16080601410d1a030c10210204050306132003030f0a0e091b030a0b1f03050105030c040203010e060d08070602040603021c0b01 69
    0x104d007200291f4000c80c0203024094480c031003140c0c00703000404201ca1101c001d240590522103050110b1001030b002480310305001c4054140350001a04a02103020040e5540c03580360b205645a1141c0c0e4443d42d40036100c400e0702d407400d550400c80d8030f1281c0c001c100c40c03a405038508015501c54407805580c0702d8070b03d14054050203103081c4035024407094036402e00c2d100083c044441d15007100e110001145008a0004090044c1c5887c14a000c050030108050100118101c0906681011414254421a02c0702c180d8076021141154500440d0450281000c5404903050100c0d40b5103125411024110b0150710850341c03a0b2041e9100e6402d4807441101a5100c1c20001040c000100c0c8103203958001c0218060080044103103a0003118892803209030301c1402e05c002a10b85004010034102003201c1510031100f00c800f5400c541c1480e01c030400030040101a14420350110725981d0a10000324111104941c01580a642c9c40d500c580018000e90301c41500340074036504101c1031801e0310305a4480c401e050312059450701404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 658610737 1250 658609487 658609489
    0x20d030f230c160f021815060d0b090a020304020103050f09060106030b01030b040e1506011119020103020f070b01060212070809010f0201020c100f050901061a0a0c02220f0209030705 80
    0x15100c000c1102502c04402c11142e5044060420701c102410322642000c00e04c942544107001c102e50070500c0d1003a00c54081418024034207010240166104070543d800c03030301c2d8406107800102500c03c0c040c0c8282c0003c03003070081c00044c0e0010303001103202c0c078000c0e2030500c17094440412400d030154045421b1000b523003242c40140442403090f0014080c41005160200e090078050700050112210490003c50b19808140300303078280c07401d4000e0b40790700c244242441060707441301640380303525406451080068413101400311021a80280e040d04c44400e07000e10707030315140c0029180180001000303003d43c1e030151051186d031038180070b40705040b079001c21740c412812424100e0101c01562040310208025055540038040b0450305c000030031404121003440a0041080809000c0c540d00b181c4003d4010001c590500c181481107113003119100d5050b0110b01c444994600844101729000b0f4242c1d0002948000400142850302c0340e114031005a05101e41400c11641c00041444403c0344241c080454042e00840c2042040d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 658611987 1250 658610737 658610801
    0x812030c0f070c05090703020c060604021903110706060b0403051015050f0f12070e15030c0105070609020306040605090f16050d060e010c110d03020a08060d110907020d030f 76
    0x2d28480d0141a400c40c0e101d400255075540106d84541c0001d6010548c802264410080e01c1e030000300640e800c600d06442180c0e0700ea0f000040c003280e182071545421400d04420510012107a41e00d4002c801000019120340d80840a58058841038490348030b841101a1625181d1141d020710305910502c100000b0b207441d0030302145e00c0c2d4810403140d00c2040c00c15040001d8548800124144200178007034800d56040240101d1a01c4000d0040208401d110f01c403040291000112112082400d080039915040c42d0320b04480176000d4041c000350076015980510003001010b4120714001c42001e8140c4507004071920a07199200d60b00c028a01a03007290400800850420a00f0307148040e010f40d01c0031401c12107103006d181c2558080c185640000e901c0254100344144180100c045904940c42c00394600b02010380c004201c902c003e04070b42c1c8214151600f51007042405481e008134040040c102c0c6089180080029465424001100000c2800c1642c40b000302020b82c4104074103d542c0101c030840c011100303959244 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 658613237 1250 658611987 658611997
    0x3090816031112250f0f051c05120708060307082401090b030a03050a020f1504050c010c03021216150c030b0409020d0b13022e080c03070f0207050d0b010812030c0f 72
    0x607205c403500b900e940030800b00321180968a001d180240351b000c1d0341d80301620300d404941300510308000060040004108001c06102d40140051a12495a80303803a400641088096401440c251107003030415070226410f10390001007010301e00c03100842c0d40c0e0f82d4010001a540d103014800d600d034009180b1040000d00a2002e0081486584100c030081000e4141c4180341c01c3c503602c0c5801c05134203508100302c1002800c00003c1e483c0c60083c0703404480885141d80180d540c0d18500d602150090010480e446c2400020031410030091b009140010b64080c0e504200e001090301301c070000c0020b030a11545030124142070081c5140190f0107031480b01785007010f4964144020740542008200c118003a0010301580c0c50b05441c0d0f038000b400446840d0900000d031038480d40206803900035401d10180c08200096410094141e03644000c00e400d000e02e1081d4580412400d00c16a600b2159010050041003824060354031120fa069695410803603400c403030f509501c40d0b210300040750101c490080c1040b217845410b0b14103001d45 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 658614487 1250 658613237 658613243
    0xa060c0311040314010e03091323190614011b0f0212033402060c1c021e070f06180e04030c03030f09050d0309081603111225 55
    0x341c5000700880c600303000d40c080d900070343d80e41c0300c00319403c50b0b901c400384180144555110300542c0b41030b03003400c045070340e82d40d0384103500c11016912194049a0a98a0103d5941c3c0e003880303480040500c2e000c5903d810700d5010300d45405440745049404150058500d00b02c41c551034050315200894000b103007610f07042007076407901120445004c104503001038640084400074581041c014540725448401684c003100041c04c9050600e0500710320366484022414403001c04250142d50003540d880f5821f15230341ca01451528080b006082d01940e4102d1a50301044650b035803082d040100d6080f00d21411010b0313071a481809500000c0c001c401c4108005801290210741c080306403220b40d98915555040030294010031a01507010501c0d05004030101036042c403500c00c88102000042100da0340c07548031030f030f650000c5035611001e041d515684201031140c030380e003502e000140440001c404440c0c40d15005207014980e5050010b0343c0304131404c00382c0c06000e550954404041c00b49141004013107041d8039068100c50543e060b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 658615737 1250 658614487 658614491
    0x305090d022a040f0912080114120309090405010b0307080a150e1504050a020109090c1205060301020c01060f0f06080108030f0708070203011a1002070302090609071701091a0f01020a060c03 83
    0x2e24603460700e01130314415034060301000680c03036014100a030706512801168810070511800601c507129001d00140c56070b41c0c0c00e4034641d041c58100761289207548a540c3e80e4581c0180c11000700420002e0541056403140f0007981600e189595810540c2c6d07460884903001800b02045460342040c645c026480521101d0030701080f1100c00d1402035600440c140c0a48040c0d03500e03006072802100355600440c0b075100078900241c007003140c8411100300410303804203100d40900c0191200d010503601c0e030b000d40689214140c2031000b00704080c3d80320440b070144070091003441d2036080170b0600010114003400c480d604864003000994031f0310100761131035180b42d03102c054112903041d01131010f1400750328240b150a4440c43c0700110361005800e8201001648606032a0302c00c1154003c140610060312188007154000c50300744c5520106849082d000d8410884280c03481484d80140d500010301d411658000d4120200400c861004103030300c00d01030002d0421081c0314075000d60701c211078280c00035485903c580c154041030303d80 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 658616987 1250 658615737 658615813
    0xf150f0f0f011b03050901030506060406020a030c02010921050c032a15120a0b030105070f0302030402030708031c05070207240e041a0f0303120112060e031204030305090d02 76
    0x304503045142010300364001400032400d00306c50f5806108041d00f050f0700322040c80c14076181c244000d543d0514610300600300300003018004216401a950354001c3d100f01d89028660300013040c10003103a241d51507804e030342c2841011303912032035400c010442c044500c1c1000070032001c507180c0d101092240d60168403415080140b6014920b0070842c0300d03003d0170b450171003c600c03503005042c106004c5054a00100c40c16200380d142101740400300382c110b8908100c0721080e081c0580c803603442c1d00001c1e007030881030390080025000018400100300421250007900703508014003040a034503428000c903907554a070b0140909071000e20115204028030480001b503565403600e0401c085100c150042426910309100a07040070203541c00d40b609910b80441c105207400410f070011800e110002d854108440018420806686020305d42d100c20300c20250031464108d280724003266600d401915641030a00b9003103801b503000034a05808224803e10110385084090704079401004500240600743c1340000c40c0c01e4110318061801f200c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 658618237 1250 658616987 658617017
    0x270e15031504020315090c190e0f01050111060132030111091002010b030a0210020703050129010c030c0312230a1b0f1202040e0f150f0f0f01 62
    0x421224046410004100d082c9841418a4425000308042c502003a200401ca0808030001f500c84040904945140845d410284811590059500450440304a040421595094243c0d0303041c122082030ba521414580c0300c1441c1e5403190302c2801183e216100600407114440c040303403104400c111a000c440c0d0b4848081100207403c603182140c1e5800344c81004541c0c55442c1c5030075a1484658501400240050444e010000c2e4551600020003441240000b0391051124402c000c0c800145902c41e008104603441007515090752041010003e03022400c0601510a40d40b01d02413414802358551100e1200c00210343e0240e86180c280c40800702880d44c2c420f9054201000340001c840b1000075440f03080041e0401240d0f040c00e4611015100012400007458441c0c59680041d5660326241c90340b0f041648862224110030280c803455000000015160003070000008400c02c0e5103000341700d40e651070201403440c1410b2019040044003c141c0c005000e20007a001414041c00a28228205241220740081800703 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 658619487 1250 658618237 658618243
    0x1b02060c10090b1806010e07020a1a04150c08040620070f0b010f060807050c03130305030a09060311160501021e03160c02090a1508030d0c270e1503 65
    0x75014500194440903088140054034000e160000840c0002c044c0d000820f40c0364035502c0c0c2042c0300c0c9000500c00a00041c2240307100380b041c6138220f41e0040c507050400c1c00c002ca040700300e80c2d0161343c00d031340700035144050a60100ca00d200703071003080d01036403100119a540da0301c6082c002e20104003011020105030508001489a000003041c032148100450307100d0303140b181005240d00505802020032003044500610140b90426113a542c40b070568640655564400a2194214015414201700220513420f012080000200182141151a03500d01100a550340e104030107a0b88071080501030b80d8001c00c44a901140b4140c0081200740c00b0300009460040c11003e101001200600d500301c85e2103020051102c01c0c14110b034240703d000301c00d10b40809502c4594001500036240504a81600766a50100300d01c0c442c000400304000b007807948103076a11024a03c0025014185c10796492001903000d0f11405e016603015000d410818403064a040000d5041c00707031040e00e0440140260010081011003202240d07410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 658620737 1250 658619487 658619503
    0x240405060703091a0a0917070b0a0203011a0c070f0b0901020f0d1b0302070b040603060509070e031e0c030d03150503030c07090b150301030f0605070c02010206060f060c07080102031b0a1b02060c 85
    0x15030031381d0303c04107402d0009d08a1350140c070003040d10340108010011f105c3c2d00036205200742030303001965035507946e00180d00d480c2030303110342c0b091054101d25040000c2006005003c1c0c0304101c4280c003038500e2140d0068240d5104e048940b0801d0102e4840caa000411031183c0510100d40c522034011264059211081c460107034109034001c40000b5240d404c10301076800c008103411340140160900f4100b4224110020340c81d00f406a2500c1c07076180c1281602041c605040140754031881e0082c058560402a190b402809401c4a52866080d03111154000a00c3d0400204981c50154500d028180c81070403c0d4200025051001d03c20f603208480f0f0b0900c0c070401010500950003580700703514005045080b031602d4025154001e00c0303082880a22884900580d8010461552155046600481e02510f50300055890301070141800800e2140c004007042100055000310702030b541c40440841d903641840c4030511203100701600307100000e0390403108201c00380c558000700c59180d2005059605000301c03513001c00c4c42c000d09 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 658621987 1250 658620737 658620773
    0xc02010c11060403231c0801050d0c09020c1c0c02030a0b1b0a0909140c030f0a060909051b0f060f0307020109060207060203060414100314240405060703091a0a09 71
    0x2150b4440c85e41050402480c0c07403800003000b0035480310440500c0075241d658148a614080c519807400b95007007102e05001d07a805404196011512039028803055962050901d0320403218028250013100d04e50700501c404295650700800820000321580d0364030240c140c0160401042c40310703d411002213441d180c0080d006040702561441c401500d0b02991200303452413011300510150f189030521510030744a00c01c41c1d81c8500c0000c10b03a00191600d0040c4070040415500410344246001854020040080340c403024006c00c91240ba0700c0c60800b4004c0014803152400080c0e84003000300021011b01503c40040c5501c0322184c000050f6000050715008140d034000354088a585600100b003102c2442c1c40e10515805694880c000080ca1800d4030517010344504c18040030784040c20903088411481030401000552180d01e40381040540508224400305034000d65080302c05001e030b40009800140319109003001c240d040b410808110308082e042a0610300003230040c004803500d03415601c01054101150903240700c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 658623237 1250 658621987 658622033
    0xa290d0902091e0c030609072001110403020f0a060503040201180f06030204170723060d06030b060a1508070305130f050706120905030702040b0123030105100c02010c11060403 77
    0x10101c07400d00401c0030010143d1132580b009000303000c0d00b070b200c80004c50342c00400782c1000724007116a5400071120440c082d115038915030810a10a00c0c8030303408009002128803d8a068880b25a03507001c22103284070500407403000500600c00100590710594036041d8000c040d1500c00d0702c154407000c83e901001d00b035411071000710360002400c011110b0008003900540c1d480002a0030a00e0800f00120b0000d41440300110b180e11007281c070044181d484c00c0c121048010440001c010080c0e0f00d03c1d101920404c1107403128400c00b80c008000408130f6080c500b1144018281d500c00d80307540e070740703100c10b030002e02010340354015140d4800002c00014038445011000240904001d0800901d40b160080c102460706004843d00341c24801903800199002083d580f00700c2c0e0440f004a0401260f2004861791451001841d0402c2207140c1c10b42c00818902c0700450503034030241d8003000c52409400090301c0d61003511034000e0001d01c5e51a82040030501004a244419138020240c52501d90b403038440003003c0c40791020701001c0b11 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 658624487 1250 658623237 658623271
    0x4031202011a090f010303110118291003240504030903060b0f06040306020f28030b010305090c1e03070e270d0809010b06030405010b0a290d090209 65
    0x82840320480c102c444007154090385500d0725000f01c0303240d003506100c0101807143c286040100c021082d000000016a01c1d1010141603455080542c04882c1042c0104074a260041c1196040c0c000c0d20051840342c08610b1040c12400c2c507558803030369003401c520043d4080790362020a020790f10b44680135240c0514000e03503401d6550f608509040c4202e880b14100c0c1c174450041000f6400740364641d0070039501142c0e002030b4016160b1203481d4a101c81c0303102d0949441c1181c0110358105035a482d000803034142007801c0b0b0381c04100e00d012001c010340844006540b0681d45502c01081d80600d4078041246072002420b181c1e6200038400c004011030315013141500013000e14840c01c000c20801d01004888407000b41d0003070590707107600d0dc0e079035040a4440d21078070503200401000304009502203009400c064003c4502034070b00c43d0340c2c0c5000c1c20030500a100900724240300b2071552100080d140e205042c480e40c41c01c2d0060301c00301e00d203200002560f107079408604210121358455010001603900d40c0391481c030912071102c5000d0a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 658625737 1250 658624487 658624511
    0x6150103060302040c03050a060b092b080304050708060c040f1707050406120303180f0b1b03010b190906080a0216020301020c071a16020f0303070b190b06030405210403120201 77
    0x10721490780062213103502c103104580e9a903480c0b003c03030000307a07c0d330013264504585912204400d01c5607540300608a1b10000040c0000c00070300040544c100c40481d02655495110314290b40143d10981c0308400900da1b4154043c0b1a400604400f8500340d10203204440d40342e030742c800c00704050310a03e07480181380c6128001c4103000c1c1601030040e65140da0641101c0e4624008941d100801c4000011019208650100002d08e6103e00d01ca01550b410385030030400fa889680d6004000d0941e440745040b181180000321002c0d601c02d010f000094140c030b1494031252084da4070b85031218001d40211801c000c007541108150000758a00b0306c000d214011955010340030300c506010a8941503510403000841c0990100b01845111007150343e990340007035045038041c1c0449900c0b00002d02c2d42c00b40c0c4c1d801910f25a0a407087c45500c411141004041e0071420005104015141d01001218002160080c0040e00805c481000e00c455244140e91003000b030252403814161292038020340b100c031507002d010141c0c0d9111030403824 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 658626987 1250 658625737 658625741
    0x150406170c01170c0c12030907031110080a0b19080a030e0604030f060203070c1a090609070e0c03090322060e0406080a1b2c011706150103060302040c03050a 69
    0x70303000c82070a080008407414180c5100c941c034010200d84c3c803020085644640002c05009000c119842901125142d0410700015a00c4411030b110480d1000070b50b010243c1141415900c80c0d03600181278403140780503652042e241d40540a0408001e9001510001c1010342144640c0304030060001c24004100d01e00742c500d8080e00c40300c510200948110b1080c00200001880a888000403607480f0344092703200c0d160000c0a44115140882c01060117a003480010a4aa24483c40511070b4002d24212601510341c00091034581d40180078018208050000140c85104800020758111820341d04603890800812040b8140400c072840900b001807035404c3c00c025150b8010b9206511500032541000400c5c909511250b0311511194004c02d00310010000d03a4140e8001c280700001041c0d50340702040c0f048260803c003999502c80c08480e4031308944800011440c40c0708014500b400e4141003000b0202034603550742ea10101e14880e43c000d4100741d1207503004001622140140b030440300c40f80d2804596800e110a090003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 658628237 1250 658626987 658627003
    0xb0720030309030304030807030c0b0109090303060b030603031e0f07080a02010c0e0906010804060902040c050c0111090102070b0d06080723011701091a0306040317091903050315040617 81
    0x88281d00a2040840039680030040760100c03130b0700201c0305e40e48881c3d900d41a03447c0c0040001c003404000d8144000103440b421504410401c170b01c0381e03600700001c0c0d8480c40d40200d24001562100d0b095881448915003c040c085008200c00c0c61040000e414840c001010801644c40210f01f10384409000c134040c400f003502401a90541902400c0200c040d186600101d50754010062140e41000140c0c5c0115007400141c2e4000c950700740c0c001d44148240c032140d02e00a001642b01140c003000701c1d864045041e40c891050401da4115450503030240050702e290103074541c00b81d002140c450501030780e42c08000078009010000000242a0740300c4580700074900c0d00952210fa02c0500e1800c2c140509182e03030115010b042001a8151840080002806030798001034103080c0d00b0300e00300c440e0503119400034882415000040c03020311483c28070b4001d0a81e500c3c0c041e01500e80c07401c62116643c1e11626240b10000a000b00040e5a01040788000300c240e01800c0c0001506895144d802449c90703910b031242d00c5092200502000e5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 658629487 1250 658628237 658628239
    0xe010c1d120a1506032d300504081b10050306011803030f0f080f012105011e0506100e1c1a101a030a020a020109020d08030a0f050106020a060903090b0720 68
    0xe502d0703003450510681c100341820080851034841d1184000e21f00854100c0d00c48010032003140c03255412141d0207442a803190051208510030721145090759142c4401400e04502e01030702c182c000d845132580c00d80c0c10341c00152948e03044c00b0708500034842900e080e002400086010340e50f07101d128800700c04050030100e036010702481008071071803c00010084012207581150720140c4604004052102c1c055189001803100031b00d994280040036622079a41c8420440070603109500304015251a0300300100300a10b10303201e00c041600400492454985900c424450045450180c2200841595100010a100145c1c02d50384041c440030300120b000b00c9500345010700b81d40c1e12928400011b0030140841804010300294019400051090003617100790014042141d001e00b51810780d0245103821442c0381c00c00c0714600e402e42c2c90044541c01880590044504a903500d40240a0707200c1f16440f410050010250183c050205c0180c0000c1d00e2074000e0000c00080d4094154580c850740c8010744106000e007817201403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 658630737 1250 658629487 658629533
    0x2090a140106080402011d010e040c05041a04120f1b09090512130b070611040b191407031b15020a08061207180b040f0e010c1d120a150603 61
    0x50343c212001e0010000301050240301643d1147c0120b4403884c21440e60354006042a001014503508403010b1310503103d20480e140c18182c0f068203a0003071801603106030107140416441c81c0c0d020803401c4040c070004034002c102d042e1040e1072110300c0d030740d03c50020740c071101d40540d442d60340b0001d014044c04075022002c449000c6602e03101c2c04a100c2c5807180c1207800f541d01c418100040002c00c20100d1b50088100c28031501d042d503103031030b40c6113880400d41d0090700320341803018075002c42e00061900c07480601d081c0c182d507115401d0034000030362021600014505035500204800302d42042c0403943c91407103589403255004000d43d1fa941140c0c0000d0a524010f4811802040b004200c0c0e8520840802d81a00b5151401d0005445100740700440c00a044084c2041e44c002d840c2c4150020882819003101144410010081c09081d040d45800c0310400ca0b58980003555000c1c1d0700e498040791500b0310181d41e5404582c0100ca602d04616102d800340300c0180503002d00880d40d07070380040007084004c00003040003000341101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 658631987 1250 658630737 658630741
    0x1506040f03290c0919091d062202040f051603060801051e0c0d110d060b09130c18170c10120b01141b06090109030e0f0d02090a14010608 60
    0x307521140b01c0070384400148480850320751155115000501e10aa5071564818005a075a40e4040c00410b91402d10324105540282c80c0b4182c1100054045d024012201c0d204000d10200e00b1194081f10345908200c1e07001d43c403802c0c1d039001d041c20780c000c003405030002d002c0c80d41740b49208887c094100c90303496024140c02e0f41458104040082e40030082d01d501200c1d070035207203615500c52594007858420b40c03508403415031401040080c4920f0b241c003d4103102d1600309042007040c1d15030846010601502040070b41c014100c41010090304069005042500428140319008100d05040c1e030403140150b4204c601d0781c1d070303100c81150b00c10b12081100d83c40c003141c15100b46d0000501600d004040c1c0381c076079440c0c10f4001e85031540019940d02c9020a840011f9660024a4a480300701906040c80e24040c0c0004089108007408030b55045010320603801c0060b0f0684485180c8d012100501000c0c040030480c80d0340c4021000c0391a009611a00c1030144640b410803c0011f045540c0c0d031b00500d003400e0603003142d070811401c081 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 658633093 1106 658631987 658632053
    0x3070305041109270f010c03050603010b180705072324010b04030b091009122a0b0a061e09061202090f1506040f03 51
    0x580d040ca002c00d01d03402c21074809010741e42c2503100720711820102040724440d45403e02403240f580c00c0d60030040d41c0d40901821a1f0b03048501c170000c07a07226402c00526107000c4c481e0f894584821038059218559283c1110028400145241e0038010005902000e000c40401090f8940030718007204448582200206030f1654603010501888080c2030400c4d00d0407504841c07956050b034041440302400d140c07843d10b0740081c00324050715088842c010300710300701c111105601920a000740100c2c8280c10407030301048000c04120400000028001c500500040d0017588519803890598001401c2451902c2c1c00b204940103208a130322240e425135140300d4030079241410840803412101840410011141d07580715a10790820818402940b00c1801400500101c1030425101c1e00310941c0d02140c484e08548030007003040765000703810210307084400e20010000c0000200c44407141c0e6040031007156008400d10 = true := by decide +kernel

theorem cover : BRFrame.Cov 658453237 658633093 := by
  have h0 := BRFrame.cov_init 658453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 658453237 ≤ n) (h2 : n < 658633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
