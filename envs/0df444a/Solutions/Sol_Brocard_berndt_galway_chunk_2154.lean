-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2154
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:48:41.396157+00:00
-- url     : https://prove2.me/submissions/1e50aae9-c0c8-416a-8c66-2c7b478a6452

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 387230215 ≤ n < 387410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 387231465 1250 387230215 387230273
    0x60a020702120f0d180e0a05040507050a17100b030c150c24070c021c1a040336090e01020714060906070318020f031005071701170a 58
    0x180740005080181055500c804118040184c2207690110005c4020180004490418515104500015141400c0c195450000070b06001041c040c0710044c001c003c18804083d0b98035240e040c0620115100c090080c00b9806814080d14003621035a0340244024015041da690050100184d0300d001244a5044031006c101c10004400c0520106840c886011003003070340d840c0200315854020304000cec0342034140202d0358050700250382c8120740e080307554003054040500011245080019030720303001c50503407107519002d040c04105908203240305042902ca503d20382ca0781e04800211000341c440c2016110000010365801d10890545422030000812800c2c00545050110307900d081c10907c0013810401180c01c08028410156028000540c2050061809114004203541800903c0700e00c250028412034030101000d02584040c0240240030f000300200300301c1d80c549084041c0141c0035950004450100c280d00208900e140f00c0b4003c99a51452401080d10344d070240c0c1c0f07a00f500902242110689911201c0c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 387232715 1250 387231465 387231499
    0x50f0f070909061e0f0f031401020702060a030c030b0907120c110304150801150905121908041a031006050a0513080c01031424060702030a050a0b0601020d02060a020702 74
    0x10312001340342c01c210704c26004038628400702140d409a0071031030001044103002c000302100b8204100560b078011201c203003070400045456009101e49240250481000300700c101e1403680580c4060304902048e02c061100d100c840040181c00f80d021206000030804955034108442c0c0e00d40d2003003c0313160a43c108100840165444140381d50445d9025101c5a403c1c0708050311700c0750380031411074010015180d0350070300b04003000c401410b1007640340581d501510100248803113041c000c101200701c421109905e80c08881c2d0504110550368001d00600703a0025514140101e402c1800080720b118940a104090a45090103000c65940d4003200c510020050b0030700001003600040c00d04c000051544100601c0c8000d0500005000c3d2140008414211143d8904000300000c014450980074800030031030041707002c10b0380c000400c2401501d8019416100307842084081201c001201140e1314054486a0b84550b540f000490b03640c0007201c040001a0400c40c0425000450b54014111944c0b0040c0310071205a03910074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 387233965 1250 387232715 387232721
    0x30a1d0406031703270a08090f061305031207030509040c300c0504050f010e0102010f020c06040c150507110a03023106080a1b0b03040308070e010201050f0f070909 72
    0xc0e12200c0326000000744030b840649071624070780c454030f240006664100030b05d03a0346072100714140e40604031070b00c0001c01c516266950b2400c2c0d19460401483c890b280c0f0300001d400504021a400fa4038000c0c4503521b569030400d5800070965414a5060340c40a03e800c0381d00c0184000f4214a242200a00c03002001c04c3c0742e030340e0440c41a0040c07a9122107250600c80340070040c2074143c034000d222100901404000038003041d00d910320a00301000d0f00f801c042c20b01c032100d0f00040340145006501e0f5002d507031001c281e03003100001c04104640030b2405040c189030340c140c5078480481801c510224800114500b080f4800000f5524002100c980c40d0080005045660f20f40118004480c0030901d0310520605d81084034080d4554592503100e49908103041000754104120207030380b5032142d2401742c40d0300458800f45001950712940c403c0540411072000d916800e00b4031f00605015800d50b2254040340741e02d540f244080d48140b00f00d0740310f0900036684050b03070b07280d0250220800ca4040c00784402c01038100f0002ca03850a03140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 387235215 1250 387233965 387233993
    0x10209030109050a03020d090f030f050c040e0c01020c060a0801050d08090d030c020405133215010e0a110901080405010222080d08240a0e070503010512030a1d040603 73
    0x803010b0500002681790081c20010f09001c29824080110300034006080c500510380180c1e0340c80590b180040a1a0400c2c500d000b0032a03100c075600604014603001c00b410082030200b14000c085c2c00301d82130301320070604214040c01342c80138410004030043c00405c01c915014060038145801810f20b2850580a2804243d0512940d1015000305400c0805030046090500c03c0c140e0250101c0b60154810074680c5d21192200440400b44407082d41c0e1110340d482c2002c1001d180141c0f00411011544803801c030044242030390400340709a1000030104030016404128074003d421001e0308201d00729180c04051001036590f17400242082d2444e660034002401d030055000c034a8000c16102410700341c5594900300c0b00d00c0c50034280e803001a041009400030300000c0b001c1003040c012810b848032411410940c403174022500f02841c130351001450b07689050901060542110055069601c01d99942c008185900d81c45075503440749103c0e0000003102012b00d8292034109041d51244400020404149240d40391200c54120303450f0303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 387236465 1250 387235215 387235223
    0x31090513030e06040816231f090e090d020106050a08030a050d0605060d05010314281b03030810090207030c0605060112020d0204051903020108070e0301150b07060b031b04020c010209030109 83
    0x802c10300891914045180358000b00e071401400107d000390200d018040f04e83c031801c11400b07820001c0080e881c00741c00602d024080c050700251172482c1c80364000342d8502078201c070301d030155203003c501040d40d060690b03150080e505228011481c0140035401160907a00c80594106159525440480d95a5179000200b44a440c40c86000c61603506505150140074140d14100300640e1110074003034800c20740c11517509541d95040d04001100303000c030304000381c460b44008695034035511032000c04004c0541200000d4010784051030340c400096120303168801248515000540810315182410001900e241c04c8282e208030185401c25002e848a88080281e0300004000240316802003418412801c207406a10b040c03485201c0604904da1941d000030b8240000039001d5420414491401021514250481c20040407003615000ca0140c0d11904141b1903080a00b00300c0c0c0081c1020071280d0980b0b0001440c11000e0300c102c0800b03c0ea000c2c0c0c042004001d5220052804295409100b5a059a03074203125440d002800703 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 387237715 1250 387236465 387236503
    0xa06020723030f030c12160810050d02121203040308041202030a050d0515030708010608010b09100510032705060f041101050703031d0c0901080a0b13050331090513030e060408 77
    0x113807c4081c0c0345800043c0260200c1464030001c11260380c91518140318213405413201546c030400c0640300780c1071501c3c400144172411000018402090391001900e07200742e01038000e01c038584600000486e00e0348070f8041800005001400700304844110307540443d4101400d641688014111100841d05200c0740d0350002d0704595481800304070802003806011b031f40c50021036601d20700d480d0411031940c001050340259401014106c5150721114001e6102d110300803245810100c50030500c1040001010328005c044445000b2036000c107503c14010140540200c1d80f1102c420301240c4480e004613029003064506600705a10369025131711300c0400e10031410484c060f44018102c120003845c20701c0907142042e8094509944080404408a88260f10807034100304140b43c140903000d8182001483c40c0034108045410003400c04000c0710400c0c050b588080e9020380d04060f11103065981d400382040310000c07903060078540c402e0b84090001910070340f0300000101000b032059042548512410385000e408070254007810107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 387238965 1250 387237715 387237751
    0x5270f09010e2d060c0a030504080f041e05041a010813020a0b0306040507050c190f08030a05090f071a0f1c0c0905100507110301020c0a06020723030f030c12 69
    0x56184034200f445a1080040ca1a0300380510243d03513510820640d0410159170301c0202d010400c1407400c6900c00c0800075146510703a41c849040501c01c0149443c003004456806000158505050141d01e003014048400316200701c0c00e06005544480c0010008a00300c50140f284000580c1c521120f0005480c0c3c80d020b04d078884c6890350034441180d201600e6001400000d10410b42e440c0b2002500300b14412240c1c1040d0341140300c6103030028100c1082200202800d10200400c02e080000382d2215100311151011106031090400703400352030300442d00804000e05941ca02e280000000302d00140320103c48107025034944038840c1c0104400451015a10009640b81c90a0510b019804070100003d014100c4910b000c021b07040d45c018100d0b101d0040c0045c2201304a011000aa5500794180c0303101e034080c0341c191810f01500d490f019000b58862202210308282e01801c001d025601d10200074440780f45800290718220480140e00041d400c018601e20080e0800c0021401c90a52030389058019003144140e9a5541 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 387240215 1250 387238965 387239023
    0x61109041d011401080a060b1f0201050906010b1306051b030310060207090c08071b05030d0b1302072a090c0e1008060114070206160b0105270f09010e 66
    0x140000500e400c40d0fa0100005102840010a61180b1264010400142c1c044480c0125500c0c0038890000103102c00c207204082845030b010341020b4031400405050f2420340e078031103036044854007558034000c1d00401c0951040c000d02e0b006500600c2607101c25100300d00c0540c2292803452039603004460030003418000840c100590f580401c54034029007010398041c01181c082c40c0c0002d01c1c5d568000d1030a810020032070286840c011102071941001d5401c6016203640c1d000302101d060180200d00300042c0940203070540e5580091441c0b09988480d540480c030092000d41c40002c3d4104401c81002c0a80030340c000203000500c1408902c00c03401080c0356522444c40d2407000d6000c0289680ca07015040301803108000c1081042d0703078050410103403e44541a003039218011400890000d01411450f070f0005803a1202c0b08040c4200000041c0c100c0d9022a500109000041e9640081c07410440d110b41262031180049071a001200c1c040541c483d8118000003441c1900c1250103103403501c000c1d00b404c120010140c0940c410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 387241465 1250 387240215 387240221
    0xc030b07050a05120621010b010909110301120314030702061b03060102060c0307110f100e03070503120a02270a050a03020f5401060804061109041d01 66
    0x190070503034145000c03068007920034800d4981010b0100f000c00c0005009641d043e1700191144e807059000d000a203000f030140d900030b24049071400d020400e1003d00241007400740c041c1c228051001d0b03001e10305503481c2c810302180d40d01103a8030840070311005091040d585584031001d98419081540140003504000e20311082101c1c002521176410203003001004802c0e60001101c0d904205401403040e030326500c1641c1191656851a040006801030b20014030070f0b003000044d031800c1180016403c20000d2504000f40f546ca114041c0020611341003401400d400690003000207500062415003d407400500c803c0302ca900b400245203825a5058041800b903050501e5030f4110090034066400000c1541503800088420700000001d922458106141c961100058400d940340300c02e1691070709002da010800d86580d440200310b8074403183c1960000c00e120f681c080c041d0446c101c1c3c038540c035003000341d46503525454083c0951300c410703031030328001000303c00701035111071064030f4804841c04080b2070351005201400d0b0079 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 387242715 1250 387241465 387241471
    0xa03060b0301292d0907031e09050c0613231003020d1b050d15050904030207060f020304060e0d06090c091a031209060c070803070b07020f070605180109050406030c030b 74
    0x10002000d142c0c030700e030941c0040d0051008081142d0340382141d5680d101c00c44c040d20415202181410812152823025212038000b20700040c0304005840ea8820710308244007290241c003440741030a85030a0700410008800c0d11b0940c004150340b00d8520741030f4021501007110107058003000c5000a60010798030000e481244105c800540745400c102c0701c0c0324030040000b00f0b54002d0b250030701c141c070b640d07895100c41400f10010a2002400c024110300c01501d007600700a51141d075a842958040341c1c00a400184040c4080300311004d03102c881d00e510710b182c41c1c0c1400380000c914140c84110780650381d5004540120300c10034050b0004203078100b808265181c96440c10985003910344500740c0240c0c013a44988804140100556030b0055054a61a49500450070309601d06400750f03203c0f080c9030000040c0c507003c1c4083c4030383c00d522964150302180c445050035010030703590300ca00744500c40c000f902c184121070f440302d00c1004002c1984414034052003800e840340d001500300da40300d600440308400d25407020410413100d0801c040d8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 387243965 1250 387242715 387242749
    0x3070f170c09011b020303090402160c0801020c06181e0f15060a05040209090c0c03040e010b0a030b03160e2e0e09300408060703060e060d020a03060b030129 69
    0x704e08141d59000c26a80d001d40e5008500c141e4007c076020100c0b2000d0318a0f00650ba8206480f88441540e40f00c2c924000d5125069195a84c045d00b000a01c1e0814119180d0f1035814103240141000c00c010113400350180811210f0496a0007a071341d078020300d020104103519860017500101c00c29804c1503400c0100010003a40028002d42c014081211156a01d2a406034010080e161055071100d80c0390f000c60841c40382d50082801000d000c0000b00e801c0140e00c014000a0a8980341008a105000b00305990742000001c0c41c00b40d0300b4084030521140380c09429198115013040d5a4000714480c4002169140e945004408042ca030079210270410350341280001d5410803035003c0134000103009525000542854050f501c0b036841c0c00b07081c4000b9009584c00c2103d00800700c00003681d005040400005020303140714480d10b0b01003100032000c6400341c506089401c40c0c04e94000e1042140501d03650b50b03240034101080328079905540e117108981500140b400c0c603810758180c0004820400c540e4100b008255014008800f03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 387245215 1250 387243965 387244007
    0x30e0105192f03030a0504170304061a0409020303160c081e06072c010207090606210c0230040e0103030f03090812040c1703040303020c09060603070f170c0901 70
    0x10ba024031010003181d4228900d2200841e0780d5a850a00813085505641401407041c0000100000e000740b17039101c507002240100746c00d82c090f40000c0800c4165145e622019605401c10014038103111261a890744089104902641140381d403182035508010804880120003e01d804104100b0503050041c02e40c000c005040403c04e00480d00206000c00007601d5286401c00f40004280e00c2d113030f00070005540201401e61044c440c540d10307284000c00780d10502c96480c10001c0803590900018209014080400720154010160100f0701500450306141040b00845441406c448605160405c10000e0011384544400041a9455460300a0807295000608010941380400340000100500101e0356907c42e629010780c0300352198108440c0e058066446814801d0b4030380005400d512001c0050b004403030081e02510306c100500014043c2e04e80702103d143d5071100c010000180c240b4061071030b042c41c039607241c903004001c92219129940d0025041c0d4600e40301c40c0d8042400240c80d070b88031025528240b2085842c07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 387246465 1250 387245215 387245297
    0x603050a15030201080c0c100f0c0906020d121401060503090f0706140c0f0109030905040b0109032315310302060a0506150712020d0c0f030e010519 65
    0x34041c40064000241000309000219039900703541c6060b16100201c54094450350f540c1d65889800400c0500301c084401c6080c2540848464000d540c5a402c903400398015000440640d03904440c60411040b0243c038807a074a22031000300b6071128421b0b9000c7c0032143c841c1580c90a0091401e403400864000801c10365109110521001d98000000c240342c1c80c9020b08280c84a1004028a041416125a00071250f280c00300110074942d02004600483d101694200100f2020000440300701b00c003400060074032036180d4519031a0011075032030f0550000e049002d035a0031200140b140511050140c500700b203180264803d00c1c3c81c1d0315041d001d110050b900c1c010b0450a14840303030f40c042d4888030010403440c0065a100c0025074030392581000a401d03440c0c002540d9564180b0342c91304040300c68006a41030010311032900724042880c050350b4981e65213504010b04d0740c15120180d9048801c1c0c403111004504002050200700c61302503910f1307100408030140341c85420450300320408001558102c8051141054208051 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 387247715 1250 387246465 387246491
    0x4170303011d1605030c090d0c05010f0201020915071b0b0c010b040203040f0f0309080a0b090706020a0f112407060c140423031c080703021306030c1403100603050a 72
    0x8400f0304003418100359459175180701e17002845004024405820120801041c0c04220080c00040107440c000d8880302142e01c66600e04038200d01620007000d40203445241c0c0710f43c4250b01c41c0e000e00301075481444c03400029050712440300c0d40410707160b10030513044101044101c0164000c1c047c0f480041d0701030b40e0440c1145404d0701c601c0f003070000c00f0101900c03000c83e05050109051007101006d019110030401c40d040d010062900c6004520100c40141e2280242800400c10070300c04240080065080318020b04108102d84580010b52000c08201e58030402000300750f802140002c00681e40c44800000c06911103041e03040550541d54403091503001c21940903c585803128084003035500b91214107113104071a03e1150021001c041000280c203500d44141058035007064180c1180705c2d0000201d035034040700c9c4d07111010241c0682c00344a8625007404080750f800d1290314880e50110755001c00500e031880c100854000c04002a50040c1c40a60060000074070a102c810b425000e0240c00c40c86550080005000034a5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 387248965 1250 387247715 387247741
    0x81c0b1c0204021c020c0a0c1505030402120c0d03090e0a36050a08090a06052701021903030b01030623210303070305040c0519091104170303011d 64
    0x1030001e1003540d011440d49081d2012600d40400300f00801130071942d5407600c0c0030311030341e481401c40c040301c540c0c462080205005407644c03103a80b004407481d181c1d141541c895600f00305141c88807092a40702d0b4413032030344042c0580d511002c0404625019440340300402d400d0815000c80204010480e01d0001d00300340a0b0941c0034082d400c01c405040c030811008006c60340c0b0500560114407080f4001e071a41c4505400c5c03c092007280b00c000c00c0d00d5042101c80d003226a90700c08055982c0c0c010164000084c8481181103101807042c01c12000c0303079101c1441559107400c200b40030044e4207128508140c0000c1e42d210030304429541c040c400c07140130b4820051142440800f0010303200d41011584440340c040e0f0380b4034002c190038201d91013422581c0800b010a8903128a0401001801440b0888040d02e00c3d072810100001c403418558110440d0a080701c801c00e4600707007842c12010240c40c40d4203803410140e008000c0004c204401c00c40100c01c404031070380699525450800c2d41d51940e001620580010b90f544c07401d100145a020b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 387250215 1250 387248965 387249019
    0x20a020a0c0e04140f06041407050901032a06020c060307170a091b08100c030b0603040510050606070206090103090507080a06020c0c150a0e0a0e01090c121a0d050109081c0b 76
    0x8c24081d5030409041c221b0b0703040c1040c0754482c94006800c200080100302a1003918405510b10b1b40040710040700072070480460f005c0d54441d00015170829401e1804604109004550048403410b02107803c45801140307070449001111101c4680360303910401c13010842503102d154070304806001544180e9003483c2c081070310f4102c80c6ea080c504540d540c0040030426406504141e45105008011544a20709400c2213515008409141c02207686020001015407800200796125160007910360340c240200400154006c001154090f2540c0c8540c1000080780c200800c4290381042c4101405600d540c00308a8070351504184c2001e0501c0740d003100b80600c00200c8420180c403841003152030310505d0100e41c0004604469016003004100c03482c1200040788400c002d810007060224a0b030350b41ca03252121520f42108503241d44808200e08401c0c24841d10392840c3c00801250301038014400000c107915155150f0840703034403054494020121014590301c1000f0588120540c0e00e00a85600b0708145d21043c41e044d9041d144 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 387251465 1250 387250215 387250223
    0x70b07060b0a0303020f0f0304030b18121603080c070308190207080406030e0c04060302090a1d061006081807061d031609110913020a020a0c0e04140f0604 68
    0x86192424000d0341d8001c511460300150a0712100c603100c1c00c00a441c0c01c201d01e680da80503c42c600896144072800400c03141100d400c11485005612046294400000c1e58090307246c0310322640d030001400460620040000c409508584643c03a1040e16000d010384000901c0091004400d100c60400710341c0003901c07241d0207000480b80e22003440b02035100c00000d010343e48000d00740380e8000c1400304510b50590b00c140b070228122411034242c40305d07407802c000c20b540140c00025040b4176000081400b03a0300e40c0c0c200d04a9a124208031501c18030042d040301d072a014049520162192408074204079075600f0201c960380001c030340054071290314074051045544160a1241c0002c001c008402d4104030714499695a00c00c180c014103807034584401d00c0d070342821070500b4040c9080c100d00c1c4c90f4034480e5803035009044503039012000e480b0713864028020140c0002504021402c40039402050070b100b002414590342c2c1c00140008441c40f424604013804e08181c200c111003214189a80070350107001042e040010b1140c5e125a01c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 387252715 1250 387251465 387251467
    0x605090606160c0602010f05150f040c030915020a0e03060f0f060f03100b19050102120a0306051207091d0604021908010f020903010c0c02010801030605100b0301090507030e0f070b 79
    0x40c8001c0b40748052004034098032146054101086980d0f040d0000c0c0f10300c980d1044c0900c0707103444800b010003032206241542c42e40b1a031841c41d0100f0070300b416000036041160301d08000400c5005030b00d4032103c003c81040d25a000075800504a5100368000600076203841c020707401000c192400da03034104002100948900707a042c2d40e0070000780899452411108000700054140d61450a5251014003d03010780043e8522406002d00c0c00c00c2c80c840311246a90856105900504603d0310a4000c42810b50050500303404240e180e61012030f07140c17035030f40d0f22103401c0f00a8001482e0541c03400005004031800c41c0180100d580442046c4111071600091031500250119224020760304110b04004d16151903500698855007080c440042c082c0b001d03405010f050000350300a200491095500325601c0c081140005c0c08681d0450051010960301e03400a6800340e0040301d0500c05a480c0c1d01d104d00507800980c45100c2e01c03500c50301080400350340f6000311030b05e82c84407034001c00c0052a52b40110b41c50b0101e60003201d110182c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 387253965 1250 387252715 387252727
    0x20f0f121b010204031e05010e0c06040e1009020a120c0801050a0501051b100603170406082a0f0301140a0501080117071a070b0f0c070f0317010f0503100605090606 72
    0xc0c0a504a81c015030340700c40c030820244618601c91b81202c5009605440951034489400c003209030101d00050703501381c000c0c2070328a02400d2552000a01c400903221581005103030a01007181501031004000c42c41031a00e8a1124101456481301a0f40c8964210b4042140800041281d625088400c1c000ea940900b00070340c82e01007201100044d5070070541d540503140b080c03800380000c02081c2e92180094034099940310030004e050000d50002c612440c07242100280045002401a0800c46560090089140d1054603c288000b190320005c1e08020440d0080110020040142c805407069041000d07000b41d540d0710b0824a0640040d148600511948070201006031074107188043c2402284054040724103440200541c400c080283d681101c40c04644951413000800c0c5590b04040c015482000d201c04214500941c1d5686d40d40c86c00000705c0200d060104a09480c81e034020080c10340b60282484c08032103203066150004141c5080c1c00c214018846915102060142d0344a28000590181c1e058412a41c0c5070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 387255215 1250 387253965 387254017
    0x60f0703050702151b0f0c240a0e01030605040b030607030b12010e01051608040b040201120e0d030f0c09033f0507020108010608090607080403120c020f0f12 69
    0x110442c00001d6001075a000901404400c580241c0150344d4a000154070351a000340380c071a138034000284200603651200b0102c207580d15205440d803004124800110060800a42c900c5000390415000c600200e04444014540395a0501c501d90080600311000d00c8244401d8011a4039000003030124420503890742ca0a40903611403504c9100d00040d200700070052403035150b400c0340c002c0c40c09a4510001e580c1e81e241c4544850b100b02541400342d500100030340c0719600c3d540d005480f0f1601c07410720031f1005511003442d400705c00401c0c4204a00f4020035200802c44001d07800d030010495407807180301c0c001d01c041c1c1d144c144082000031019241d10400e88040780d00b4000400340b5100590b0a81220b01d04011171102001326084d4804043e050f800d100b03032501c00a80c0d80300c031400d5a8060085030001500d512400000b500c06100705403494000e4003070b0815a61982041d120501a101003004c02000342c0e20601045400c007000300201241e28070031001804203003000d149000c0040c4101c00440303c0750a04c01c0306150b00c1c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 387256465 1250 387255215 387255217
    0x70305131a0903041a03040b06010905060a08090a0c230a06140f0c010e0304061115070c03110f031317060601050f040906030c17010b0102060601110a0b0c03090708030702060f070305 80
    0x24145d1503681482190781c901a0b00d03032a52007100c044600c1e504010100d501540644030351801e4403001020301e03040400d80d820854200400400500c180d00c5107070402c00100f400b98409c00c019044401e2142c2100e0481c400c5244000c03144100140580a6214104482540128034070303003603080100c5156460b90001404030460007001c120707507195403034408907030684400000284100e488a0b00c40c5034000441111603512690800800703c036078201070000822080c030650000d00028400c0c1020100315550048461806416401c0265284d000007503c030b480b400c0040e8000024140081c0481c0303150021039005c0e88442000d4409070502070301050300e4040100c5081910058100c0d00c10030000300c2d0b44c80c20204542c0c5c000744650588900c3d5481c0c14081c106044c002c0b0299150706030018101a20703850f00449046504e003001c445180940ca48031000942c40c1600c0901070303203419082589a003010f4a48608180c0030381d01c50b40c2264410082900140c907074074103a80c2031240c2184200d40326074481c103040d87c4c9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 387257715 1250 387256465 387256469
    0x30a02030105181209010f0507020103091202011a030c0a17030403050d0815030105090a02060c0705090408030402040b1f0f110d020a03020c030102090105041707180203070305131a090304 82
    0x205500386000c0240d0788240015481c4580d10090490302c0150444c0154146842800c0f07200340080c210201414982d401080100000ca1040c1b50001c2c15400750b2300c0b06441c030600d01c07402c3c0005035150440b0b022000e514034030f4122407980840c007800f44001c0c88030000750f244401d8032808090b48542954450540c1042c010340c4c00840e000400d803034298120f090003c120080c12100c4c80e5600200b01107051850605210300d91003440210010700580465808014098205503203941d600c2c410700c400800d040d22201c0301503001c0c1d40b0400080361a07041620400055418140c0d81c0c5005401940d00d84003114680181b1012441050034800703060826107404035054039114200b0f041c01e114610710f000c0a242c0c00940d005615000c1c0c1c0c25031f20b4520f60354040500707034405c0c4041a07000400a00052042186000040d24648200c1d400c03690050390b1034444c1a02c03000018000c151965002c410010096050301601d980400602e500301c00f078115035a2010791800500341e1034425000080000f5105801c10011540 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 387258965 1250 387257715 387257719
    0x30509061e060f18280203240415081e031903020c01090f05030306031002030114060904020c12040f05030a0f030c23030a030609060305070501080912181e1e030a02 72
    0x245901e00004655442d00f10491400c4851710112900c0103440514401c0d03c4c061000707441100c0508504d04880c83c21030340151340d40350703004ad640c2441c0c0c2d102c484c000907000e0081100e040031b0011001c101d410896800c00b6003a810b00e15400400c4022500d4054419040180065003030068036105103c5040f4010300310403500500d1544200c0303444050060000c05140b08000850803101c0c1c0b070a05c80340d036801780e0000b03100c0d00c4007040d0710940098044c034040b000b0303210040c1e0283c001806e080d110000e5520701009216403d110901c0010203011160306075445d03a003c0e2205034000e03c03030600b5562303468540e08112035002e801c1043d008406d40410081c1c0d005905500b200340428a4110580101c99803a170b8410071020020a15001d0b00280d110b0003401074400320307504623015104c181d152100554180780c2c000c1024103d8017881110010101c048d4014000b005040c074041d5615114180a1050f43c5115541d0540703200a040300b528040d40c1c69948100d45c1c0d80303d210007201d020700d944000c41d00e80112400029 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 387260215 1250 387258965 387259009
    0x2a050f040e040506090a0b0106050702030f1b1804030e0904060b1002030c0d031107030305090708010204140a0603150531140f07050301030b071e030509061e060f 71
    0x2801e034081c1004a0041c2d0144094448580b40c0240c40f96840580020003495803229200401c0386501600140210703e001900342c507503410f1800742c118200307082c182c0d480c0041505c1c40c2100c02c0d0f80c00d10f42904942000019500c0d41d45081c42d8030040c0c803000c0b13450400c80c418441c000c0002d041000ca500090482e41c0d01905c65240419180780c040d4990300005a01126445200b0180320860b10074003d43c80c0c06842c40a2151900c600ca440803409000d00410810891090001c000f40d20b480900c0140000d013050030030300c2e0a4200e4842042a8150540d20500415080c045459515070031944580e00b2500201c1e000c0c5820026036a0b20406038007543c9806070040c298034100c40d18003411b9081500350f03070380004203072480b55036111220000d000300b551054001030050005000160144803047d82145480c02c008000d21031040510401000c140c541400003510754051102001c402c0107141d4000c41404030703452150340380c6100d07140c5880000301000c1c4505124000701a080e1a028001c00580380074003925 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 387261465 1250 387260215 387260219
    0x3190c1b030309030e030a0f021903020907020c10050301240e1c050705010804050303040809191206061502150606040506071a010e160f020f01020a11010605042a050f04 74
    0x18004029003e815004148004181a001d00d070204182c42e002c0e40c8289540c4e0345546a03001e200b910305000908010380300b080d170000320140e905d031345400d0301c1a80194014959400e2880c02c0c000d0700c4050030110014414180014400f02d820388181803454031134030300c20b008003001206003160050351310400c907a000402031b040255900c50001c41c0c1640140541c1c01c0382d4280350768400440d120034046070041e200d03800500101d000111a04d0040ca02000700400d080c41c00c01a01d5600c0e1001040c40d0b20411300641409103040030402d2070301881c0000c00400710200c929032040c80001e501c400e04290881307403441a020010710160b468000740c502800001e401c00b03884024625140064289441c1e40f410b00d88980000020f100c40012100b40c4984400000e000301c41d20180b4058a07004418096242076002d040740303078084031400f4405048032448903a02c03102526190b0550900311461034100ea0300581c1010301100c8802c2c08451640ca10b0310901c0008e0b000c0041ca900c0c201c5031740c007400c20300c0078803182c1c00200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 387262715 1250 387261465 387261467
    0x9060109032a060e180f1f0308030106030504060b0102070e1609080303010b0a0215060609100c0f0803100f0e1501091701140114030d0e040b04140103050d020303190c1b03 75
    0x42600344d6541681c41e544054030351100b1800350042190409001e0b83c28200051500d00300726034006004800c911511044c035101d40c2ca04091b84c02c02d0300711100003940e4500300303c01d004050252070204c40d8280043c1c015241000c0d40803003640c27801404da450802450340c440011502c6281c107030b0001c2c00c1100a0302e4032561603210244460741300c040b00100502c21411000104082000c025005020003041146080944d42c28000c01d0208100c000c814402ca00300070307801080440190200b11403144028555910300400c204001425a4202021203100e8ac14103100c13400080c0b1015802c644644080c2600725820300040711416529040380708100781076040003083d14015000100358003008800c40c69540c0c0ca80030a1b40c610701842a0442c1d040c1d000c805e40d40b080c20300400100600384400b61010884000800100d02982c60b21b00065428041000040041c410140b12030400c15655202640c40c2d81000282d018402201141803410580e07115254143c0f28011040b1006585001800c03200312201818 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 387263965 1250 387262715 387262727
    0x30b010e0316051503071d13020a0c0c0b040b030606090d150e0607260c04050a0b0304020906040902010801210b041a0601020c060a080a09050313080c09060109032a06 73
    0x4107044c050b00550450034004162081030f00d120703090b5507607280c1201d400040c20407502c0501000154020f023404090030502881800108092056904c528040714904c0c9442c00500d58503510420b0810424813040c495000d81d0320449420680440d003a913244d6008070001f803c404072444000389030140c401c0d02c0d841d4680ca540c000411211741c0805981055403000800d856070086180c98292605030f10840540440c0c94807641342e0403e400c1201c3e81e01b010b8407040440d4074100f460308480d81c00074000c4100030031403410049850b8840300030750b000d200042d25a800a07019030018028030510740d00030044071444560b02200340c101d15400810881e668201401c00e640390349000c0700c0e44404001104000342595000250303200203a200a00213034079004010030115140c5030042d100c0d045103902c030342c80e1102041c0108060141d103a151140d076600ca52a12269a2511719001c4107a80502424001c000081e03802c00396110031280c0004c0d00361020003c0300e03181d08000f100074101c1c282515045c60301140460f4020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 387265215 1250 387263965 387263969
    0x102120723100c0215060d0302011d0a0605060406030206040b0715020a0f020c0a0503030d0c09050a27051b0a030b09040b01050a0e01030c06030207031103030108060601140a02060601030b010e0316 86
    0x20348100b1100c50030440c101c2e182d61740074604884d0f4226000c0800d4003814002d46100c2c040e4001d100004034040c0340b0a50301074115045000c54030701d0744003220740402c1c800188101038000004841c10071025180d9400f00c4d000c0c2c00f40d4441c200600401240460a0010405103011518201e800856580900d010003510020840407000010300c5200500080ea00f0203085050907240010000c6007011100c1440d035000c0c001e02000d000c10484610000902038a03051481d502500d01e4031035401940701100c21540007203140c1c9000350100ca04060a0004c8416120f614104400840c90090380c4d40203c400150090160800000c1d04503401c40c042109201c103000b4100d0503150100c2c1d0290341c0c030f070f1f0314084504040d4081c08081c00031000050100300c080d00960003407002600c0b900705088800554894a41141c009900c5414a03402410030000c0c19030b400b110040c48081c9040d401ea0401401200095980500801040c145030791500307421440da001d0b1484040364600141102c201132118050741040090358 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 387266465 1250 387265215 387265243
    0x20a0207030c0b1c02070f060f06051206072a15060314010b0109080d0203090d1707030819380303070c0918050a0b060a0306060b13050604050102120723 67
    0x5010801e981554000c50352815041f08480710b0161154a90b2401800d104801104040d6103c40015072902c03031a5545030300603881000340c80c00c0e14110001800f81c400400700207036004011054000000245085051a1500300b0188001b5182c80d01a000051205410140c0350058240c15a2185401500031a00e107030020382c2c448000507074400040d950389440c0503d0b440560000d00c48001c10382002e40300a416140a1800340812000b00c100801c0c0d140d000348410760024080034100150b50140b400b03041c03030712250002c04104801d400210103003240161100c0800c1d0320354420145121500b9a0714000183d04005e0607265515240e103090b002c2c01500340302d00940340b410040011250881d10b40c1500c0310fa90010302920100a140e940c86a10b030000804882d80b00180076004404658248507038070141c02e8150503240c0e0f80405900c011000009a07006a00c9900d003000280702603680800c006009100316145151106e0300f42c54020500c042e2100003581c002040800507846000014400f040c4401d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 387267715 1250 387266465 387266497
    0x112150b07111203030601140903030d14040501050c07082a011a040b19030305030c07050105070806011b050712080403021f0815030705010e12010912090905011206020a0207030c0b 79
    0x8072003ea5183c1c0400c445403404600c10b4610303c4100100e07903000305540a0010142d91034a486a2000300c12900c040c1c00b2943c3c552591820402000024402e00b40c010742d080301400e08149242d0303150341d0103226035406982a088400305245c000003845c81381094085150300240142c40c00262225140301040e10a6403203142000c4103445107081007400b200e114020b002e1002c1409003540ca05503581c1d030020700000388502d030400c5020041042849802d004810315950554182804000102407504061500138500c0c480700c02480050000205082101c070341d03005109140f401410840818080d561000c1d4005c889210307841c0136404100c400303031001103880d11040e0944d1101041a0020502429036a0305940648000e212079130145c0340c403101184008000303070011240780c4d42a42c2910710060040701e140348041e8210301c12640000c0b4500280101e000100490b41c5405000c7d82c0180d503400010b4600c66001070305c3c00300701d8800c2c0543d001454000000181c142e0b51a101c06100e90701a44451040b910 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 387268965 1250 387267715 387267739
    0xa0b0408031509010f091503060203010b0310060e010c061508030f031815060603040809040c09030311190b040512030709260307060f0e0d18090b0112150b0711 70
    0x18182200764142c0c0c5c81c000400e0540d904115001c0c00030801000c85001e04c0f60380080000005500c1c0c00214040c00d580d5090390b03220705000d0314560009409410001c28401001c0d41481079036405451686082d0f0007000105640722806494404041240c100d2140c03804000b90250000302590001c41c041c4418a01901c0301e481c900c40700d20380300c06501900d00082840c080c049102442c01c0303809150030500800d9214a0081100d0004044610006041e804190703000400c01c140f43e0816281c05511310400d0251408405403074150558500d540e000400702403402000c0b40901108006c2860610040984a940d81c200071720701070418650b0344903003000740704444031050a500c011442500b046645400650400c4003036a02c2da0003501c040114415a1a507400600220f62401c0200b494010701585466501e1060700c0e00a0a404016800c29010f8506091a014003664070125081d401715903d1000640c0158103103071000c0c00042540b00140d032010203d424414403119800e10a08500100c85400e030182c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 387270215 1250 387268965 387268969
    0x1e02070302030607120b100e031219080a0902031e0607090b0405060a0309061a01031805060f0a06030b0c030a0c08091f0e0a0809030d051204140a0b04080315 69
    0x200940002509500000c02140c0c0041c02010710f80003c58001e8001b241d012620030204501c40b040d046140001407010480c040e05007030600a03c5041107400c881a1700d4014442000c0b0704081d6100b44a50402a402d4001350401d803060303000152407980201a10f2a9062481e1070200c8030040b80944092409002d02040381580120b81c0481100c0101071060b06051428081080301e03040f80452006040e141c070290f1001a801d4030039044281c0c802000a040c00c03420a00040032610240000305240322080c042101180780000d07002e0b800700c0151040c00707051307444013030765000b505146d400202040088401d12040342400c0300654403504941c2001c00c0917a07255a41141d50791800c2d6a4811203801101c40c840c502d0003420b000411403000c0310004501103158050540c58418502c41c1507500e601d000c61484e50510b000d020102490055140140c18005007124032181e03e0000392005001c5511158248003010303050203020301998010b40030844510b000d09180000744e0003116461181c00c581c1c00c01c00300b24 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 387271465 1250 387270215 387270223
    0x103050f160603051f0303030203150307030b011a0d050109140609071409150d020d11040f0501030b1309050604140a240b190509060409081801050c0d1e02 68
    0x1141101c0c9086140ea28000c0150b00400e005054261142c2c9000102d880c1000c55406120045100b650016601e1030501d00000d64846884d46091198004410400c08501c0c2d0034071450640d4000c1e044c0c400f1500300310843d9200d81c41112000c58a0b07509180001401ea4229032100031914400c14042d2620f94482c001c105452400320350b10404952481e0400450b5a0074001502c0d8840014000c0301002601d6000c1c41c48075009a4a04007605400081c01901300b40207010b02002c0d220034501e110706107810202c0000b60500c4500540d4105503451a642c495070383e440c0e82a0110005e03040080000314054207069845120848056070b140c01110500c1d00100000207004030780681217464001030700400103080d500e0b041c8003042d4410345c5441e003030f0f624102e036a40100110310a2910f228002040d01d40422702445030703401040c45220b10315061080780403414a20480d41d0080c4840c1c0702d001042020001031b00c081c02250b101480d01d100d0a40100202e681043d606000d80070803c80c20b00c00b01d882c103d4103c3c1d403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 387272715 1250 387271465 387271483
    0x70608010902040308030a0b0324271906150914090d2a061401030c1d0a0b040f020d020702090105060306060703051b1005072c0d030201060504090b0103050f 69
    0x80410400291f50502aa101006100c402002c1c5d40c99004004807021922400006541340300b82202c1c14010070001c031070001465281908001840d030704a680e0007544541c2c40480096104021304e052038104403190780030b030a2803c0c1c85540c4041d00c2d038840090000400d04010000c26802042000c1042d1007000101e0f00b85c4050181e4800721b080205c6100240030701c41c602c150904201c80b100034040060036078040e00044610300c0c1b0038002a5851410085209452544035001c0b8072403c00c001910500d03c894956030000e01c1000c0801d0039405036010400074000c0100001384144041401c0c203889074070b50002c0c07032410300854003030301180d803500c00f0051184000ea0303010340c0c0500100140000680178201902c1e007011415000d801c102c43d240b9003182080c29034010f0614003941e4034208041c0d1034000340f0400380c504103c06102070003111408001c0002000211203889403080c0e0071880c0800d4400d4100001500008c3e0043c00510f0092a140c2c0a1300300c00e000407035150143d0200510100340024024003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 387273965 1250 387272715 387272723
    0x40e0406051504060b1e04080a05010203190605100f051908090c011803020103090c03060509010c09060c0c0608090f01060308071109100902070303090b0906090c0607020102030d0507030219020706080109020403 92
    0x1c6807503a42c0186e407000c0140301c603c2c408520780034840002e0002c402c2c4075007004240170b60005139aa203492806c220384000d29200501d801e9207012070501c440c0d220301140710000b14079070529440000c0ca0340703415507440c0030b01c0c1140101b01041400c0b1852480d4080d214501580c511001c440090110400545000c10114002d40c9045070300007003000950f10a801c42c544050081c504040116101d450b5007091340c2c001c40e040001c0b40c0d101c4038402c14641d40012440c005120310f1602c50740315807099032451008003461054904002881007ca46a03110030300030564200070207802040788681e47d00c4c0111860300700d0030040c1d9a480c240340150b0f48904000c85030324402d0415140603140c441c28401d1907002034200300c101342c2c200356680701c0400000f151540c040780070300400d600805442c81c1403c24580b03016204451540641380a010700ea0050743c0000a48590b81c2e030390540802c8503078a1520031402030150110b01c5000301d03801110040216008140d1038241c403942c0d80e840e00316a8a0303c0c402800d0f4421480010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 387275215 1250 387273965 387273967
    0x60a0503160e09070305040314211008011d06101212020a06020a05180609010e1e1f020606011b020103151a090102060906070c0209040503040e0406051504060b 70
    0x16000152680c220003051600e05000300c051590101042c0d03c034400700e640304042942d507014001803581044000c01c04103c2155070b949000b107552010342c15500c1941030424480c880320301085291006900c100d0141000c60020440c0604588072070268500d058107000f001d0051202152018450300840c1c000c0e541581030b0090020340c190343d0100c0609043c2e5880c01140a803640040008034540003e2842e103003d6691f8640f05c0c001c1c013080c0810050609565031103a13104001041042c0d070040c054140031501280d10302d260300c1040d105644d04c0001c045a00d948600718450302c045800c0341c1035100d800380d2442d500719910b558580005482445030b4880c045030103616020304200544c869000920004e9003580381c44001c40c0d940b491542d200822041e2200000c0011803020083d503410003442e41c1c0300c0c4c0c5000041409080041018184c0001808003a008140e014006130031310204008840083c0140302a8465502d400e003045002032905582c000c20701c400000030a0728914140c0156000e9038011814a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 387276465 1250 387275215 387275221
    0x1321032f0304051606050a121413020d060e0307031b02090a0f0f050106020706030b0306130f0c0e0a020d0c020606130c0e0618094506130c05060a0503 66
    0x8a03815800050045070b951045100d1520030000c80c960300301c0140070a445c1c0545070b043c40540902680360071030306014210328100f03030300c0c0346810387c0b01043e504032840c0840d8120260340c900124036403501e10380300946005d0520411a41c00310740000200b450364003075503d0a21a0002009400044c1c10020700030b540a002c58000c40c0180904c0d6010519811700944000b41e8149100c240c00141c98090b8894409a0810541008210340502914118040032006070507103282c0110344000c151006000a000c508030686102c1c100071410307500d00d0181c4108040c040161a01e03d0901010303500540310420b2050520444100050000a0340ca002da03100500344c800aa8031000110000d0050211150802148036816025a00c801d00200f1000e111104403804190402090000d0450041c0581c07500c030170020401c6d001042c2c0507a1900529512000c90300c1100d030f0707400100050f8146940341300390502859040c09012000050048203642c440e400c103040060780c44017001658081e00fa01200460307010400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 387277715 1250 387276465 387276551
    0xf09030d0f09061b140405010210020d0603050601030609110d050a1101141b0c06091e13021b0706030506030d08040c0306060315050108070308040b03132103 69
    0x800307240e06040303000600c0c201d081d100d00003a01c200700d02c074010211011320070b80282e80c0c1c801030705081462030040a62801b40b40800007965a455203080c8140260f0104070714001c151a03411200003160404211485075031203081c4035000b401050b104071070b90300924110300c51500341030b240d803126203812001800d92030300c09448140030914100e00840c10040302c1d1510745a103202c00c2d005071101110044c2d107610318154041c80285881281d40616104140521000c1100d0b59510385178060200b0418020b0301c2d1030020804191946c101c1c014807880d0341c0c00401c0d240314041040c00841c01c41502e07401116117142da51001901100c0c010345c1c13450f130542c100d00740651043d401403940729086032150452580c0180c0da0745804c400c551140d0070480300c258210003810811403550042501411164001d0014640746944060031351055100d0030010200220000e0039203002d80c1c40d810700c0e440d00002c81c44517210750002c00c103070011840500b01c0042854440030081c8045140c01703d14903002111400ca03511664290 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 387278965 1250 387277715 387277721
    0xd11011803030b0d05190212010515150c010501060309120e2d1512010803041508510904060e030f0412030e010f0806010f0c05011a090f09030d 63
    0x3d806401c88540c81c00100007030b5080290752140e040d60216610301c8146841000b400d01c0030110640e12580c1030a0610208103000807003034503501c000f110201801500c2d00d915001e107000d280a0076195510303040001070300d107401d40c202d24002c51103070040760f11540144000f550f80d083d800300102d8115110880446044810480043c1203200244004620784c01d100c1c001445100b608507040b5520070003043c480304c045511610f0031b015054007000f860920742400020000c40420780040701c10401c010000c1401c550045940c0c5513480e071040b500d1034000058440540c568405146001d03211b01490103614040340e10300d042c0c808141d6000b0450031040e10f458640002a00c120389040d00035010070801c4840e0b50101900070720080102c40d04250a201c40342c20080d043e1544640c01a040c04408040d95826551150902d5070220003400c01040c0319014840c120340c03e82d070307582c001445586048440c0e44045580d04034898168003c80c3e070184259180c4c107000703000000035980041907a105106c510340d50740160f0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 387280215 1250 387278965 387278981
    0x3060e090a082110050a0b0a08060103020d0605060a09060e1012050402010504170a060606080601050a030e120c010e010b040605031b011209080a02060c03130b040218090d1101180303 80
    0xc8503450705a80c0716503c07104070080c1a10360840b8082000b10030401070030f0110700c80340105995100e050074024480381c0640143d400820f10b40c1090313800600401c6c4214140d000502400c40540003d03100d6001c600c0103040c188050080102052818094001c03500d85444124070325055540c90716201e80c00500781601414019004034140300e0700740004501003411400030341521110000a040040490031701c8d2080b280035070800c40400c401d80007082100d0b6042030865907000600d20b00090030500f4000f005007080c1e80501e0000c10104005941038203280b05401000e00103030480e001b04100c08120003084101c2d110741c812586c0640002200e4141040400100400742e02b0604010003200050000001200e254110840d03000380e0204180903d80d81c10041103501c00e10321000d55185085c15100070300f070030310884001002c04060304001800c646940d807480d075580441c2c010356100e508128071130310381300c52845101c400018249a10b06400710014012281d403108005010130340c6100c01c1d1000c5003d44001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 387281465 1250 387280215 387280237
    0xe070b070b041a0415050903070b190603080307090f08030408060c0a1214091e0c060c101a19060503010b0901020c03070b1b060108070501051b0a03080703060e090a08 73
    0x1103034190022203903c0114521403131003407040138000142c04a02400b100d4016000c1001c40c1d00510901001558112065410424083d03100542d030a144803050050429600000d140000200501c007045030041101c0c026140b01803040c4088544072244113a403401a4410082142d000101142c15001c00e40006c0c0850030a615000f56003001030203484054915114004040c0c0e2901d00800c4000c000c1072080c0c0485080c9002e21554040c02a042250743d49011101c20703124403000504040c0300d150070484030000401591051208030724500b0303040751103441c010029004641c002800c01c0f41040e10f010170b0054840c981c54490840c0d08180e0011a9500b2a103c1c1e24194403c00030911800d9800704141c000a1202034200d60361a02c04040d1220212000608a001540300d000103001241001c0350b109d098803005e280140e25405048100c1000c6104003549481a009003082c201c18180d04c040414803c04d801d48080c4052640d4000c550064a822103000c1a82d03001400742c400025610301c02082143e800d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 387282715 1250 387281465 387281483
    0x11090904140703050d030b0306070210020c0c130c0e030f060103030e060f0d050106030c020c06090603060f09070305010504180f12030f02130305070b031911041d0405010e070b070b04 80
    0x2462641ea02c1d0a82c181c106442c50780c443c0c10071040041d4140a0943c95490903405002d650608883c082c3da11440b038074000041c03a4010078204040ba0302040001c180040040480d0396191141210707000814a07482048001030003401c10156505002948220900b1517900600c2543c0c6991801c40e1006070080483d607104104220055002144202030040c035814502c000805500d0b145000c0c00310340d83c8195180c19504250507038001540d0365400d40d0800503055900503030782d40e140700c005108101242c26640c0e1200b0300c241071240c1180e05601c000c0c141e0740c007034030700b04400305060801c0c80d80e51981c035400501c2070800c0a628400560000f40001c0d6174200c0e414041a82c0c0440d110000c142c2e0081d07103008410b442e40602c10001d010b0204500c00043c0072080750b052642c181000c0c20400d50300351100c40c0c49010384500303a03186d141d15284104c070001c00300107c1049810844440241c070002d0f007681e080c2e440d0360810303031003042d841e502241050441c1c0e03d02000900e01720641d900c600500ba001001552141a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 387283965 1250 387282715 387282743
    0xc0f020102120c01140f130b060d080f030403031a0906040221011419081c1205010902070605151e0102010905121e0408061803070f060b0f030111090904 67
    0x34070180542400241c200002c1900c00060f060601c8006004103014003152801d014801c130b1f2104800b10f1f4032a140c01c00c0344480b0b143c0d91000440c1056240000081113080009400c010f49038540b009540100c0c0702c0e50b03050003001c070003500030701200d03035120740c034035403112001c80410414038181d40103141e0740e840706440b044c54030400c4990141042090b4412801c2110a90400c1401d2505030015116846e00702032082c800c60400c00d001c3e80d01e030000d04d258514601345041c5440c07001d0180c01c07021a00e410002081c02a5a19140700c02c01079000702c0320480f5140c0c10240440e1001642c208199000d90b8044d01501c0714403078805a401c0b40c0c2000304e05290541d5603481d40300003c0358040c4400351041d41301ea68400e07940c056078401c50700405441c850607040050184024000705e00040345054018207001c4550315440a92340701c01d4254030410000401055120190008001454110a0054108039100c2e640001c1d001c00b4182600c50b20f500c13041210707008101003811864904402500f2501a0321001d070030355 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 387285215 1250 387283965 387283993
    0x9131a010617222105120103021c0f06320708060607140c03061e040b07120c020c1f0801050d0f020303041d07090819030e04020d1e09030c0f020102 65
    0xc04091003960003c0c4c0f0200e0706145401d07840012540c1c1c00052514a16244960180d0700317462106000003445001d000f80c101c801d500c0f071407448003803944d0040c0010880300890300d00713000280003801c40c1e2410b00d49801242450192000c00548545032644846500355855a00440b00084028882a4040c40038040000410400303a441622010782d23200500104100104241c60130800038100d040d0170b44032510405100200f134401c260080d034060b0381c582d610b80b6201d001382d54400c61b5840b660045072405c000c06a54503400111103441c0841620440b441108020028030441f0006d000d80003c200a18010401800c0580107900418002c291900001c01c10307030f00190855005510924081120301080655010249107103601302d1880d0a1502e0400e1404030001c0d01c5000c90344140340b4001d40e5009000625024502910380480003c000f1503803000105050750003810341c4402441c0ba0345908c04420150440c9108640805800d80c5541c1c680b0b140d5a62100200d090300b0300c0880c1103018a140310a845 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 387286465 1250 387285215 387285271
    0x1120509031905070c050411070b0901112703011b050717040f243617010e030f091216140415031e1109131a010617 51
    0x282243d480568034107060411105120040d00514031440c54404900c0e5201012412581d40c5c59204210100541e03a0700c00e524014101100008a45c0c400040c0e641c0d90040f800c428075040242d40111000711541720014035088801c0064140d1456480c400f1400600340030310003401d0711502c605184800e6042004001c0f543da0041d41c8001c0542c81d1030b100601c50b40d101e444002c09007a10701c80054400c510362540c000d000416500140c504181f00c09c4020f20544e499800d0300c0f516801c805165980301d9030b240b14203803540070a1005a403a5502c0c11110074007903180032088850010349022450300f0040080108002203c0ba90100c6003a40b042c1d0007207401c0c000140d8002c01c0100140000d0f031076201004001c0c042921a40060800c5c090010340c42440040c1484800f290407482d41d4000d040c41040e0780c43c00901d00c00c810801198007480d0075003000300d000912850707141070744d109115141140c030403ca03060822603070038050b0f0702c0400d284c0c100c1c01904948180001c0e520107595505e00b40c810005005115031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 387287715 1250 387286465 387286507
    0x10501140910080624030c03060f04090b0a0b060702091f03050d03020d0b301908070c060906080a02030a110d0f0b0a06081503030c0d02010603030311030103020112050903 75
    0x1c80e80003c100035491500100c802d400036050f0140c0f544444120000c0c054038131000f0003900c040e00010005c21f0b0303940c84000e88880303020005403003009450407a040204002204407025000c490500200c4603d505248041e1031420750301814460482c2c90305c4000042c4030251610310350460038980d00c00408108108140c1440311f40d00d4800594882c40203410f542a05c050040f40d41c0510740001c0740d640c0b400354111001c0c100781c0210842e0034128000301d9110742008500c50140c1420680e1030000410b02c030fa00d10060844501c1221000e90280c1d8480054581810511412003c0341f016000940303c0d180c3c40d0015940f01604400004522030703683d40c2d4405982000d620515800d17a207200113441d00441d03110b1244100c0c0c00310783c0314812500e040c4000300b03502c01c003e294038190b000d00c5103141c5190300c041040c2c070111208001940e82114000ea4024000d00541c881a03000a003403881d03844180e900302003240d0589406949a40308044c980c0c011102418016011f510310b4401001514070240f0742c0c9600d050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 387288965 1250 387287715 387287717
    0x607051f06140901060f0c0303060b0a05090a080105040f082d0901030f1e110403120c051011030411210a03090e01141e060d0b03150609010501140910 66
    0x600e4a052601c00542c00003007440450003507583c2001844801d401c1482019444c24524022614020307519045014103140d43c0a80030364500480d00c42005500500a0909c20710280c0720310380d00542e94030016081e501d00341c50203400d00d40040324010210300014020960030034020030708101040c12801080742603880840d103018681c00820b0510311503a06000c1d00400040b024820700c0b58041500010401c00340700d50380712861650f0396080010f43c0391014159802190003d140901d4461a00c03800b41c6402c00b410001c64142c020341e402030351100110b1040b0b2500310a401c48150031030f40c40703544901002d00d00d04965548690300e8940b001c13080045001081540803a2400750400e4030351454042e08000b50354100c000058060401800043c0c0302132075030303061200100c07035004450b203c00080d800d90a07049480c030b58201800140c10b88810750150031610b540e59017036080721442088940389140a000a5030302650001c500c200401c440d61084016525240c11011250f00e0031001a0000b8101018030b80458 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 387290215 1250 387288965 387288971
    0x3020c12071217070c020112020c010b0a060c051504050f07090213060801150f1103070f1a04031418090f0115020703080a03110903010c0e1005180607051f 68
    0x7004000c2001e0b0601208074040c1003a0341c000c58a183c4846050300020018010000c0e002100c1055a01c40c000c10801c03109115821983d1302d20701101103000e0000c0c3c10150340500c001000010341180315071036003840310703070014060909075011400390804c094018000381c405100c0c01050b0360010f04280400381c0100580e8000503942c80a0312100c5d8111340c015030001d0b0520a580c80100a40b82c50444010880656498009032555810380b09903440e00b42c5102580441c40049540010040750303090600c440340c024402c00c001248604509242000100c800400007003881840d00314484021004c0d2030403101c2c640c0614100755150300412840b51084412000b070b00903440c010001c0c907040d03c0c8694600c0d21310f840070b000074606549405040f88108000e810070141d440f01c1201e01e1151410503614549030040080c0420440400001c01000c0390f0810a0321515482200b500c01601400c121411a2042e400c00304901100d80704000b0f180c3c200c0f000c156214060741500e49600e00703041c000c20087c0d0407031030400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 387291465 1250 387290215 387290227
    0x6030a0608191502090105180a030506071101053d0510030911100813020a030f062a09061b080309060f06030c0d0b1503060a141f0303050a03020c12 65
    0x1602e14164000640035a244c8100505079141e40d001084401e00d80e201c003500d42640040c00301284004049920183c6140140c0043c0510700f544070a0280f12014004001d100796281c101070036940100080b1200c01040c4110022803446252961103040200b040d8281d4004542d00c10220f5414100c4101800c0003c1e03855142d54104a580205004030031410b940180303101c1c4030110081c0101c03c0c0600960942d01078150040f00715500d08240f100079540c0510161003080240c07520f003000d02002205000700c0e0704480050f020305a140001522380d040785584500140380740c000c0030b070fa07140740c402100d0028080454100020452180042d406118544014450761418551090705408045d2645100e504640303590189595020410340c45543c000761440c0b0b66869a9803d8468404058000760300340c00740384100711400213150700c126281113140c112045156034141e41c10703280603040c134881c2000b14001ea00500200e807084001c0c04403100c40e401e005141202076016286042c20302030307046200d01000119 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 387292715 1250 387291465 387291473
    0x602030912030705070b07080f0a050c24010501052809030c0e0c0304060e1c0518121b0613030f0303180b0c0901050f0d060312080f0606030a060819 65
    0x74580c031801c00001d0b60506445a40305900d03031541d80704810074110045000c46c180b04155003160500ca641d120403550316020080c010b4a5a0000141e004a81c040e006105031902d808640712051100340c4008c06200d80e0a250041d1429004000243c640c420b110800c50704002c05030321544c1203000c0c00c1d100d003144c061440c13400f1071a454881d00304080c8400c810051000e0300b143c84046da50000d0340410046150700004c00380070701d451220b8130100001d0b4000c0d03403a00211504040100401028010074a0300424868244540000707022601c10303150740448848002c170b0121483d05c032401200102114508400c0304200e40040c00e01c2c0e0401e41d02c0142c1612201c0400d60148901c0711700b0001d4210400e1541d50702c1c0c4a00310001d03c02030100200100015412400740e101e00100c80c0e549408412040d1108101440340d0b004081902080f18a00c10546000c1d100c517000d182801d02c102d41c4070b2144085c03a070722802800301540000e0002405135031500c4020880c0c17801480710028040803003450f421450a01c1c20 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 387293965 1250 387292715 387292729
    0x121d0a0e0f2217091008010305060a0605030a06050603070b0c01050910230604020d0609061d160f05070b070f09060323060d0506040f11040b0d020d06140106020309 72
    0x41007190114036114031602d5200240c030304564075600401008907103c54515014650301c5809074260340001882c040d9a60640c000e803401341a40c0c015400c5034036540c5c0784802c50003103c007503024503680355001080f4070000964540050f680140c019083d103c2c465030b90250800360707401454048038181d4440c010003000160801c41c494216803002414090000f407007406030700301d01070541c00040c2e40416200046842e1603640450719044040c883c00c02c4120381d103c000d640104054012030202c287d00819084403842c004545500520030380f0760000d6041c03400002614220340c80c1000c24244030041c004600843c0028281c1446840f494881841503071001c10020003144140d0040d50516281145a0141200d001e000c8440b000740604107949913240c0070009241d83e060008002d00f03500c1428204810016900755681c0d03100d00c245580e051b56451070003000150f41d507201003903800001d0a0501400b501e0002040903100d8012080000c1400c4011041d080c0b08009030814000350f8130005d45410f450400170 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 387295215 1250 387293965 387293971
    0xf031804090b160809060105010f03020703020c0a080f100504082703063c15130204030602190e03030d0507030902030a14070b070503120702030d1404020901050d121d0a0e0f 76
    0x5400f4244660502002070401301404048104150380070dd580c001f018020820302d200c2080060130203801680e1002d80550b210003006c82104a030059081c5000d007801340d400343c140030301d912868950810b00c00d0072201d00100c1d481301d040200d03070704000702e400915142480568001c09040c121034981032420380f001c00ad51050840501d103004011a100740f451414138141070381146540c080701020003809000038441c1d51003400b81c0c561040c800140041008420750051aa803407101c405280100001441602d00c01c0020041641607042000f184d450b00e0541e0307020035408142c4d81800101c0c0f40280c1c01092501518050454903841c41c01041480b01c841080250000e1164208483c500030690b42c3d11a100d0082040b009402e01f00310002c9044580240191030721a0074400c8200101080c0c00c2507600c03004030039241a4002d42e0124001304280c00c10841c0f5403a0030f90014514a060041d07500c00715480b80b42d01d0b9040503504016015000c1c82e1b81c400701380a00400c240060100981000311010811510203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 387296465 1250 387295215 387295231
    0xf0706021905030601120203060a0b0412170301030507060e0d1a0105030f0307210e1002010501260604030f0504050301090605180f07290d0f06080f031804090b1608 72
    0x10302c04c201c00c583c3d0102d0110401c108407503015880e5207031000400d03100c0000303800c541c1c10f1510220740070516000c040c0006402501a0441c8803c01460000c102c007284030a020251940e00403141c14400280165445a20074030003a1409288900c01d071200c42d10010b9580004e02c06070525801085286002c0244411f1000c50401840c0781c0341c01039541030842c00b04100c01440b420060803414040d00d00400c20007905680107003403103285500d440fa0090007410300f401020400d070341e030040d540d1902c540b420064a0f5032404000038a000d032140e441c280c0c3c009550300c186800f040700c200004100740e1030a004902a0078401c03007000c030b0f6904214100041c886e080000500e500d9020074005208400d001540008031084080d9190080105254910181c04007151101c019180091203844500c0d00e6888298800006d01e020032100d80c40e91200c1e80c07500c2c0140c0132400f5a501c14048034910302c0155007080c441040040c00040c02108a540b66074580300202c07185000200c820500c5a00c050704100120b0b40301c00340c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 387297715 1250 387296465 387296467
    0x50a09090501290a0c020f040b06120109050f0408030a0e0a080c01150e0402061b011119020d0914060a0306080f0a020901150801030b040203011514120c060306060705030f0706021905 80
    0x3010200174100302c03280001074820314045400d83d2868076a036200511110b000342205996540c14404424280428407560820600d42000102080303000f1403d24002d40d44030303410a00e1030b140c08401e400a0607001490f50500c0c01960185000a01c0c690014005050340b80b0020841c40140034a4012500e001d81c842446041000304110040c0c1d50002201c800b4028040010ba03d18040a0405c0c014256044140080407000a42d09150702c04036410404082c00b940c21900600c8460404a0f1190100e110b00d504411080080c980c00d840c100d00070b07100051240c0340c00545e07140d44e406c080b4940706c42402202c0007a00145111025030610340e1609000d000b0139500031503030501c00340000b012440144409002c801e403100c040f900b150303006c2d0031540d050500c0d50156200c0d41d4982c40104c1604411086c0f1500c90241d074001c021400da40401d4031003c103240180118195910b04040c0441940301ca2400c59088c0070800140155005035000751540a026036001a205c5000c81c40545c1d10340c40d01041c80d014484 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 387298965 1250 387297715 387297727
    0x91507090810020906040519030803042004090317090a06020d02180a03050309010c080f030f1609050a03110321030403180b09041509020f0304230607050a0909050129 73
    0x1245000c0b1007c41e40b068811118484814215222503150b9030401801810700000340804d0100c60078890540504040010000e180040e04000491342d129000401048400b041081d10780c940f20040c030f03402041d03a0159100320013569a05c5040341d1050717440004aa9002c00c034001e042000541240c42002c00765507000fa041e045403602a564040c81169a0421030741110780c50401050406442c4012082d403e180d84a04002c40f80084e240c6c0100c0744840300e02c00340d20315041d88178842c0308020211100904010905810b540380c80ca8040c1040d01540d416104105d030f102e440d80388829030050780d8020045c0144d101c0c00c040c1380c000c1c84410032040d01c3c811400303c140c0912203082c803d82151100380d0101ca00040e1210800294400640203a02545003039201140076250038240d01d00030340c4140e110705001d01007503c40090408140c0c00481c8001c2d1a940311800146401d0b0003003000b00012082d80c00e0102e4070300c1d03480d500d65041d500260010903000d641510b0100b01410804000380613810801c022a007420 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 387300215 1250 387298965 387298969
    0x6050f1503060f101d04030305061c0201051b030304050d0f05280e031c030f11040506070309030203010914012025020307061707020303040201050702090915070908100209 75
    0x144082d10002c084500140400e0710040074450000092170309036100b030045a0134005040404008450580201c0e00b0706000888502d854403966040141308014007a4404958004450a80100036248541061500a015948c0003007014500c0349205400a081d0045003a4009048013030700301e41d0000344041403144445055640e01c00700305100d60b03a6408000016442800c5072403004030541e103505400358290080c5c1000c02d902c50131501c4200c50700c0510549580812034021101000c1d41d08143c01d2080c0018042d82c9000c0300280001d81c001d02d001d24540d501c90700040e003110003503442210186407800340744000d02428045d0802654142903803094141c2d001c4186202e41c13140d275043c0c103004d414007000110307200044424403940a40141c106c9030140c1d25a84060000c1e0b0b140d84400c1303070300c2c89020002000148004200c911442d0f0603511182044103070342c00d04c100d501002d055840ca50086201c1c1083c42d564644001c0c0c41081160788012250f0300e070010b600e0900481e9010212034030f004105415480d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 387301465 1250 387300215 387300223
    0x10909051c1209050a06110a02070f05060a030c05040906090915020a02070b0a0309050102030906041b0b0a1404121a06031b0d14030c07090b060306010c12090b0706050f1503 76
    0x40b00d808501207401207151602c02d04201c10014014a1a031600000f0942c5000360009400f0f011035903000c82c1d9400fa100d0820844d580480d12440b9841113042000981d80c500c04c2c1c0201000001904220f41083e4a6081001c1a110300343c10200d01aa41e0701c1104044c0041035042c100c003007425801c00c614059103910000d4a4074036a024a200103080014000b400078420381c450003030190014000c5440e070a11400351070711002c0c290b40503240008415181ca4440103031b8901c120859080918407850001142d00985604507040228103403000103100000c1c000c0c00c0d0881e02c96840744242c0f40c80c44410410100203802c1d240240c00c560295100c444d01c200d054400d5519048614000c44502240000703901d40b4480a0144080300d803400d00001c0380001031000e00040010668021080a200f0001044103210321404125207080c0012000c007000d001140700c1c1490390030515564034104491a84135480400280c0c032844003111501d07980c500708407160309694451500b00101d01d070201d806140501c002591 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 387302715 1250 387301465 387301487
    0x32f040204051309050c0a090b1002150a150e040503090109081605090a02070c0e0907060e010c0602160204150e220b090a1203020d0b0301052e050603010909051c 71
    0x198640c2d6140b84c10034040208150010107400809010049459486080180034000a1580668000f905a07658140042013444241204001085940e900c90308080054007030b2402c0c0680040f43c5450205a050740b0302d155911441c0150b0007150f803500c1810004144d5589580901001d070001c1e01c6540d02d404000c0e2441040711001c848100d5142c0381c200c4050000d11a150703004240c44601c00000840e00d2070021800d100318062019101141da0701ca13810344110000c02415030010b04d030086501d000800f158060112840202007070880000560701080850701062600001564080420000c8601c212009540000b070401d800c14120030300400d0300404203c10300001d0074900c600002501c040d00c02c1010b440170681202c45800b60b8002c683c1c0243c001c0d48000205185641402c114499a080c1405901d0264500700004d58110461200f5a003842100810210302140e07481f100141c156600d0006d18068541e5910001c0c0c010500d00d0305500e0019485a42c490401c0584840c551494102c1030501c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 387303965 1250 387302715 387302749
    0x18040c081321090509130b07050d090b010e060312040f1a0c0a1b0501020d0818010f050405010b030105160806060d06080a060c09051225032f04020405 66
    0x100300031442c50b2921031480e0203001c052251000c03541401e00280d020741c035042114400d42d411401601c5d0320070220810002c079000504882005404111000e01c514000c00d2200d40300c0c0c1000032420b681c2e43d11008141c00a0b8445110106c0e690184140b0780703018080302990101e0900d20f5480d05180075808120107605125005501c03d010707184501190258040b02c00d43d403411700503102070800c41c4c90b2409051207164001160500c0401c804900380d400041c208081c003d0326200c2c0e581c00d9940d242c001016075006031036425a9502c0b444d0321170040215024450080b0300c604004150500213030103040c2140c50082100381c0d440d2808c5030b4040c0d85600b2001098002000762240342ea6030511034150000360460354841c500703510076015040c0c28040076500c02d0007400c0d0785a4485800715076034030402c0308030407140c0950301e00c0b030701300c0002014000c20109102d01d0010440000c00981c036a00e844000c90502d0714803da05100e10b800000d141c0007458500c21903ca9842254118101418400403a02c00d80c2e80100c185 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 387305215 1250 387303965 387303991
    0x1609060f08160c0519150606200f0a050304051806060d020d091e0c0e0127090c060801090609050106120e15100303020c0312190507020d060218040c08 66
    0x30000c03034460f841442455800c00300304c03041051013440203180760012540c162001402031101507080704440c000d0400f10754983d5540800500c04494060b00b83c007660000f032003a845900001458918244000003441d40240051900c4a15100a001246608980401c1d010301c084042041c00d5580340c080d5003500c00802c20058840c2c840580f0303d8014062864050410100030000760790b442d1030141d142c078030140304888410240d0b40d614035800c0c0e0f100b0b003809840c00200c8140166640e640f01120b00100d0803440140101b5130030710503202d864650703400740c02c24000900450010300040c0c100d80500c0000b4021064200560742c507141005000000100000304000d40750741920300400001c200300c001c840428140d5000c00e04010880315800515840200c0150003004110700d006e14010032134004542040c1e81143c0303091a0000d500e105081d0442c0d090040c000705008050150b110220111600742c4079002c0141c2c3c40d843c040500d00d140ca404075407503104906001c0700c103446035131244c64150012030181e014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 387306465 1250 387305215 387305251
    0x6070503040c1e03060f050606030106050903030d0203090a02010809190303051e1501120510030209040503070807030c110607020d1502221d010e07051e031609060f08 73
    0x2121482603507486508202c800b2107550440f6480f11020340c08482c0314134803c0140f0005591400181d8108071030050380082c0070301c010048280036000426000c1c0700201601d06e0f004450003850101e810688445c280c2e54443c461240031940c00c0340505821101000c0284011051400c00d891211050180241007645400200e502107000751066150002000c2480b0b0b82890100c14201c0010200c10050380001c05040201c3e2403400d89108140c0110b0b6040318040d21181580c00340200444058400c41d802d2104000e1080880d148074040d00d9464401e80e02e09440d09200d082440c9505003503546680301e04410003010005a5880461030b4081da40004903522103070a0f01d02c01d100a02400c200080300d170b0700d0300c80c04241984c83d1080303d100b500c100300c14100c544c9903581500740302c0741404d001e5010181003070b07004a540103000d00007504580c0300c203c10130100207501c00510000b80c1c00507210018a04c0c04403c104131080e4010490b107001d00075a1610700c84445050900411085010305001c0341c02e0030306204 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 387307715 1250 387306465 387306473
    0x30c0a02010c060e0d0c05060c0a0804060209031f0603060615020c0f1c030309120302030c1804110f031005031612020f03030a050a022415040f0f09030e10020607050304 74
    0x15000b100304c80080e0b8203451825100500283c400b0841102d2030302400001451140c90300c41039442c0b6069903512909550350b82ea95910082d071100d6052589032240410083c41c0c0701c01008840850014050003080c400c0c55031800070140d581d1504100591390700302c0803140c595503000500500100c4100c075007803111303100400411850011880b00ca2860905200c04034140f5406030000030200f03200c0d0f101800000e00e8424220308074003041d00d12007000c280422241400c107509118100e411a0014800078a0b4808491000415406002070018059010003044190041242c0b49401000190050a001c00d040b190071006041079000c2d400300034010088010641d25000098565010041c00700da80d50504848050800e0300240700b0b0400510640c003003a8080585503544840c07800000d083c10450f500c442c1d1680e403040c01c0ca00016608150384080c512034a401e580034400b07030310a40b504001001c075000e0600500c0e90b05c5051446000b070002d01842404c05500050a0394002c41c00d241403500cac1c1d01c5500e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 387308965 1250 387307715 387307721
    0x618010608152d0703090312050124030f05040f1a0c09060a0504080328090e04080d150308030a0f0603020d03030c0c0516060e090f1501020102090415090b03030c0a02010c06 76
    0x10f140c280440301902000081601039000b0740206001c3d0f00d5280e00380c10680c06140a90307409004582c094850040b80c01008040c2c5403240140440c1030402080d12158100700204941003140c0130f49840380500c09020620003125074801d520351002c0301244040c03811010909080c41401c41090064030b0026040d11650f200b41c00341c1e00600b411034182c80d61441039100341c00400101c10702d0103c040c90f0702c3c080c0c40c04440c050122401101c0311240c85020641e21910b9002d00e0381c000d11000084076441d8141040145144d15015014500c64100e031500d0b800c150355a44100c4c3d29664148034540e223001da050000d40c0d10006d01024080d414540460803256900e0704540711f004034000109684601141800c950f58081c0109040d50030b035230380707080380c00c0911410056101d4060710007100708024500406d1200c09220046010108180000b43c6048007050108089581c0c00800c000c2c00c0b40100e4081c848110b071401040b80c0e42e2021801141446001003441e070b01c40400f000300905009a541c103032010400c05030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 387310215 1250 387308965 387309031
    0x151605030d0203010e0112051c09120c08010509010e07050d0f0c080f0606011b060c02030c0f0601080606100210020d0f0c02150c040815090f061801060815 68
    0x5000d8989554204940304081d42084c000e000300d83c4550000442c5001948580268850700040285007203024900c1c44100001080341980c00c000500344049040d80c004c01041c0c2c605c41c49040303006d4900c1c1c9802105401c480001d1300c80509a41407070f401c110401800aa00000d071070048890b516a18202c0c034200c90034120b8076100034030710a0100000901404085400580059068280d40443c1d8032100111b640d50503402450010104d42e50f000d1022925642c0407501c055241d00407603143c1f8500c41c2ca10b03031400807a001c4210465202c04010300c20640c0502500c1d4020070140d52a041e83c00100901035151040040002c449a07808610420391140c15000302440c030401001c00c21014400906c02526440c60010040810345000c02050b01c08000804880c2142d0300b24000d081c0e0200d0860b03010b011940040c014040038851005100d8000c0020302c0261f0150651400401000d48119112402d42d60382d03500c6407113581c001040d54650785481c500065071001142001c0324610b40c24010740c801c510780407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 387311465 1250 387310215 387310223
    0x6010e070909270f03031104050a0b0903010905060901290904121b111e060d0e0111030109060f080d1d01210b01030b090402030703061107051c1d1516 66
    0x140d100f40c8144001c40c4d1a100b0315078000c3d030b42030180c0c0d5040011141140f0a900c10b480e041010801c0810003000c518000c2c04000350020004a5500c0b02c90315542d15094041c1c4050506035910104814480d01c07400e28220415071510003101d92103808800142e4030400100094601d000c1000b8414907a442b9080004152488080b011391f04032890070510761810090b450306019464002c2809400ca040c40c182501e01e0314001d110500d03000305e00d0341660103032080d500340f9036240d92660140391200d100003010350301130010180001515407a18101080c5010035074044040c1d40c00c45021a0004c940c801c0410442c219070003a0000403070050401203d0a10308056070004003003004814004c0c155242d04281e5205100743d07810b00140c800141040380d00f2a00fa42e009615a001d55420000a84541c00c441c00d001d1301c0007121400c00c0d0058882d541428a200d4510300d02c5811340014060b03880d00f094074100f0040f0b20310341c1408030720800700101d140c07101c1081201a509402092644005036218501b0402d5540 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 387312715 1250 387311465 387311531
    0x62d100c050a240902150a020111180109051008010e070909090b01080c04061809080c030301030305070516030506060f061e030a0b010201020a0f23190206010e070909 73
    0x3d0a0032007a01d021692000c01c0c0305841c1c82c070107480c40000e01940207016001024035280350440c0e031943c08103030b105e07030300d142c0641d5281c10002c0b0200900c0303806440ea16144850011041c00c0302c0000403c000c185410191088c800400450fa0040e484215a419521040c08004083c1c945841c290340c02404c40d80194541030800c01c1c00d800b084540b0700c0242c101e40410003252180c510820030407007610303518001c80b05440c0c140c0b4520036102070b440e081980c103540a412072032716041088040d181958030036041a40482d40c0044c0755810030030f04009209044903020300d181456400c580c1c946440740406003405108032421025650266a0071007268600c00c0c482000d0a031410541001c02a583c02c110303004c05940b85040e0140d222035006008641c4914800e654128810460304010758000c0380080c115072421000b0340060030808008402400b0110241800003040e260a00009281040580101c00d640c0804400c0c00384041d0010401340a440c090f04021801340b01300240e4030302c443c020443e01d1354401d90b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 387313965 1250 387312715 387312733
    0x90905010b0a1a030a110a030f0e0319080c210108070b040b070b090c0306090a1416183206030f060a02090105120106050a12060b0a030915050f062d100c05 68
    0x380540c098002e0803490a81402505640ac440540b6070181c1080c1000d00b43c9080c501c031620500c1a2001c03640850080102c904045c1c100c0b40d000314403003a06000b85101030421006000e407550802c151002009003e80c07091516092501801c018012904001d200c4151040801c054607010b10101e00e2044000d401c0314000c0c90b1040c179155032098004c50036111124cd024a0f141941c50218000000480300620800201c2c50075641c060304101d2400c0000c001541c1d01e0303140c0d074041001c0d03045240c62601c002000080704003039280c3c10360450f006042544660702408403517844180100e00f10f58803603055030006850396010300041c1c034244240b40281654034015000800c01c590484081c00307055140eaa100c160072682e041c1000708440d10b03401103000441e420700690640c14800c0d040f04654621602d02c03045040303103144540741036030380507140c016802d01c0744030820002d414005008004051007800808061098941d00008070301060032090040c24424118031010780103500c0c3e070001960200444407016 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 387315215 1250 387313965 387313967
    0x1170705060d0f201c11070b0c040e07170121080d09050a0804090c0512040b040317090105010312030c080c030a09150509010b270709050604090905010b0a1a030a110a 73
    0x1a001510a81c10f44004000d5040b245005d0300c59804184981c40581d460401961a1800f0084004001d503000140401011400c941109980340c051b034056154155030b245a002d00905a01050b0804e003100c40020280d4072040ca209569001525004180266503403140940710300901b076007038805016031180c500c2503401c00044c00c0c010b02c21500410010007406a40d0542165a44100d408441e804001c010114002c5850b0000c02600113110b8280303804017a800344070010007114111102481039564400400038040d400e614100703019139a03d420041c01600b11b4000c0c00c006400b500105a61401000060380c1e0000390b030008079000d400c00c02114000c00c080a002e006031804590603030b00340d42080030a60a41c20508685001d0a298080003107507030ba0204524190078600401e840e040050b58440081c2c152a02c034020030141450540100f4800d0060500a003502d030b40712429801540c071004208103000300080c494090641e03403015940d49403911580000a4140070b854135085040008c0c000d8074007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 387316465 1250 387315215 387315217
    0x7030302101d0d0e0105070609060b03060c0a0f0e03120705060415090c050402070c0e0702030a021209061606020706050106050304050123060f1207090501170705060d0f20 75
    0x4201035220501005070707184241111007464140c8042a50f20101844966600071095032112581c10b24043e42854210388580050360402c00040e101c0c00e90307403c83c034440c605041c0f04d031980c8090300c5141c0c1031404000c010014a42c0080342004010070428074218025550207008881329100c0f0b00d11016101d154504040f42c0715001038034100c1d5201c0e856805203210b000d882c0a5440804d81190074482824038103410b00010350301c0210308458107111203e0210715804400e0f80e860048006900540c0c030762861a801920701a41003a07034407081c050034025154255075400843e440355020074100d1014611502d0b00d64064041e020740200304c40c0c1040c0c0003145d15644040910b1046010b0002400492882180e101d04549030600c000a040303800c0c00003c2050030302c50001101c0040180c140960003ca03400705504040b00c64001788a02c07600d40004001c940b07444050680892803a03405400343d989048002256803084164142103261580744070360042c44568000c55407140310507040c1c0c8801c0139043c41c525171 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 387317715 1250 387316465 387316483
    0x5070f0f14040906031b140307050402090d020a031212020310120305070507090504060c0f0212090a030c09050a1b0f120605040c03140a1a13020f0f04050a1a030406050c0c07030302 79
    0x1103ca0304190014010062814a180d540c87c00342c0076143d80b030700301005d00000c5d42c041c00d803842d00000550030900058482840c614011030007032440c5548003210308130044c5813003030b400b2048084600600a03c0107108401115800300c546050410790076481074601925103020300c40c0040c00c00e0084810003c2e412450350040c92145119001c10070440260b0b410a031102d03004500c88100590009840031590480703a07001300310420b0010100c8180036680d64030810541d03003d0b0803e6880c42d031a5014007599000b58000c9000800e4081005441100003a00040501c40200c60322001c0003100c07405823404000e030703078480d402030303c00035006008181c81c001d80a00502140daa1580c089040032001503401d4116200d0203000b02c1c5494002141c030300480c01045504003a100c0700d030b0031580d400c01c0084070f0264620001c00c0005c03810303911591954034010800240000541c480002034080d41c06400c0884501d10460b40c0c80b90384110b00081c10f880300740c046525809040c1c203010f218030a014001c01030580005928807 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 387318965 1250 387317715 387317753
    0xd0b01090b090115050d1e020a0c0c08010605091306021b24060f060708090603010f080c030c0d06090c030b010602010603060f0c020d0503070e06030c030a05070f0f1404090603 77
    0x581c0d0744c030120003c507408141c4142c00060310620400c80c151810b034101c6800403070b0141d804518268500103e40032684a1b0034044040b8001c00c4038207081100b10782e09a001014420000c104003423030400030490380c0600420a00c0040010007503081000803e5040c0d038880e9403800c2c0707002c41402041c0c0549507a4448070380442c60060303030035481c01c0c0c40c01c2552085034030406024103035001140c03014050142030b810030030b170854100209101200c202d03103c00000c1e40c0240076003001d010a140c50402400d042100005d002070003038010710f0604525488004240c41c110b64001000500e61031030317007408022240a03400040c10b03a5815000092007960540241040d170f80124010009405548003034000c0310203880480015030800c0b019103020500a0307000e154011410f05000c207082881600060300b9134000c440120740ca48020003030103442245441030b554008507504002c003881c1c5a031070010f003a5026038101d242c104501803060000700060882614001c0488400500c070040d10303440c01e51011111035203114 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 387320215 1250 387318965 387318979
    0x90e062d270705210a05030c0105061903080723010c030b100305130305071e0302030a11011509050a0207060e0105071b2f180403081b12060d0b01090b 66
    0x480315400800d0380707030480f80300402001d40d60020480c2d0005002c040400505903004140441c4c0c0440c000784010041400b860000103400e00e000e004105901d54100da505000f100c007518181b002810f15001c5548013030300043d152501c001c0d0303c55030440e2440d07500c3c81c09a00e5401c007511440c51940641140b01a900203d40c80f14030b071111480d00303c044900840d00d40649040d913200c0900400d0003103000b0034502c1e010f402510315540300607184083c02c0d1410801100103901c001664880954410190340040e08568000d1040f19241841c1008980c554051802e85695442c0480d03446002c650485403140e6103c1c009010300e40149082500900301180c0100101c3d10618258075000000c0000001c1d1581c40178180410500400400c900c02d6802c070100c0c0c0b6805402c0306142c8181d42d071241020740074402200f0030105440c0c2403400801a180c054440780707002c41c1050b10410307041100010b03180544110f048a0300240da0709030015040d130202c40c8019211581410022403000003a13000b0807040d10054600d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 387321465 1250 387320215 387320281
    0xc0e01080606161205090a060507030f0e010f0e0f0d030305060f03070e07080603011d0f100606020d08190905060106020c0625170c070f090e062d 64
    0x20208500c0303203440c8450103c0c0d8080840c0c00080e5040300300c2c8a645a180b4155007014143c00c0442c1071400581c100c60041400861498200f5138000d1003044400010f15200518203105800a400c4550224060741804144517000c0540d4603041c2c1d24038030050006207080c00388805414081d004201c15140a4021080340e00c01a01034240001c00c482124802410b0281c1596002c00c00c5900c2c000250140e40e142d501d40074a584050740e003413003507120401440044c0c03c0200406407000d240c074001b0413140c0c24080c280b40042280b282c020a51881e41190390a01c40c950b41e45a00c583d08411407000750346800030f403030103d0030000e2140018003030703041e10150303000ca80c444030b50f400030400c8600070302c4000000314450590b6130940d0354028030500680e601c200b40c1101e0304c0c4940c00500d43c00d40c105032401c00090780224010029200c0d5441800004c0c001100308008804150300d04545564004020200703014049041c020f9644100d00380c18000c0c0d0050a410449083c02c0618001c0501c3d400400c05020500e07144e4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 387322715 1250 387321465 387321469
    0x1202011d060304030818070b030a0c080903030105060d0204170d08070e1c080706050703020327061b160507030209010905092d06010305011407020a0809010e0f03010c0e010806 77
    0x1035401a01001032200d4159503459404a07049000206083e50800020301d8215810004010318405000c420714190b0300c9282c004580b80032035450044001c100500c8005000143c60f011089074195001070318101d43d1804c07800350300310107407160317a0251104040b8149901061503000c10074116004a659401600c2e440310102111000d007044103d651000703c058080b08106550081c100406214600282c10040c1c1e47c1c440714122241241c1d9a80400e0b00001009040c005035403005100031070b4103030200e4411220703220031981c40100034500e0ba50301e40c030400c4d02400c601d070700c48c203036804d1200403e505200072020340381103511989140b00c201d0003944c0c00750022444044500030944106210401090b10110042c0031310000071502101c101600003100110030f09070824848103028500400010400e024090103001d40c0710002801c4404641100580d4000945480112070404000b444c0208005020b0000103100d000da04050b9079056103085400861150440001e0b48002d0b000d8a40050568074802 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 387323965 1250 387322715 387322757
    0x2205010f15030c2c03060604180809120a061e0203010605090f0103180c0f06020c0a060c1e0b06010e0604060e041802090123011d06030a090c120201 65
    0x900100c2003009810590341c203120360b01c5007154504070701d003a585458542c01041d0a84084901d03000c03451000850741c10907400c1c03c00000d5000342c8241d804115230705107045480341c8403184030310040c0480c0c1c0004081440303954134049040c94030443c81c10740c0c4803e075652424800400426621070585034a00d80e04c0e041c190300610075641290360545459240c40c1582d010071440d108200706c22414140c2d501000581c06486800031402c41d031260300c90f18015030814080c0380b50041d039035100d402158000c895001d100c0c0c9900e4022803c43d40241030818468010b841c00c11048600e25004039840181c41406805014506003220f00409083c0c981e41b00c541009400d00c541886540205004a070164400081504040d0300a810703004a4612150303142c241c0e0b50024581502c207921003121706001e005211028892040c0104031ba0b81d007400d00c0b124506070441240c4038110b42d00b10309407040101100180c4845c40766000780303182c41d901568052405440740e00d00788012000c1d40c416030009514916072a84070060341 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 387325215 1250 387323965 387323969
    0x1406040c1e0303050c100f02180402030c070807060b0616110d030f11010f0c09050102070e040c150c0c0e07020f161a071e060f140408090607022205010f 67
    0x40740001c080d401c5440c10784030399000360340c2c1c50003621400140d2101c81841d07100d4030032801e43c808009a9030f400c034260001d07003c5000c031050b00d200d98030400a025110a810342103d030000d5001d50751540320145409c00c0c00c0103100c04075a00c3d03000480044e15159148081c03000705d0a15205031000304540b0750311400d2201e80b12013160018041042a00f4081619014804100398088100001f044120403070ba03074032003540e09800c0700e0004140215400e0190f5038051040c8405408144200c1b1a2031503e5100e402d060040b03407041418454040c8900d6844620a840709180f841c0c0040480c66805d58a074190f2500440403a0000010f01800d00d0300c400080d00890100c407110400381c4034050507401d04120012860300a4000d500b044410080100094808803254840043d80e004203220540c2c1800e040c0151440b41804595081c035040c1035105100a030081550000e402c0f50328a52100344840c0401c0c071522031910065401130b824150104039010040c0c07034185a112048050181e6640c8500c004c45800c054 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 387326465 1250 387325215 387325259
    0x8030a02100213120b0a050c0f0919051c11031207171308061611060411040b0d0c090c081e060103020d0509010c0f0509010f0e06071406040c 62
    0x12855a203000001c98003d00744100c0c1d0600340081044c1d41d40c4c107080e4440c00e004002c40f0a074004804000015803d88036080c0d12a102a0740e203407401c1d000555100040c441d0490302e070b124203061250f40c881c000d5040c41c690003414018002003081c0600a40c004255015403008a51941c00300b8240061421f0219810b40015580808a8141000b540e2518220040c442c801c0810301428006004800c80b00d5654070b00400040d40502550b0400024900c072001184203042c081c000341640808241c04009a03969020760010803c0c018541403600180252080d0000c450748004440304c000d080c0040c020a490840380741500800440c00068000d558082c41103d25140045e18074050000c14419500001e0384184145001890605a402e00808698096138813000c680c1d9240340b044259a048210340700c0104441c20304a09140300c24000030140441484a2001c200040c1c18042094840b4401d81d0031003a804031801110000003482d055030341000301c3d01a078000c407141c070000804c45c2c80100200780b01854 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 387327715 1250 387326465 387326473
    0x210b0a0302041808030c1902210d09231905060622060335030105011103132d0302030705220501080f10050c2a030409051008030a02 58
    0x356400704030090500e012990640c0c08500941c2000548060003144110907114031141c545007801404000c80010f15646001d55001740d0b02070550f00d220002e80641103c0000900f50350b000e501003488082d11103d04001c09541044128070054110085003d20103400601154a031100c2804103070348641400001a11581102c00824480d080071041d134400382c0c4000000c001200c499500c58411200705034000d9a4000c007102c0e288910006a02048041e4501d0020703808070100d0901c5409010311041c0b269906000305581e00711303020b120500c2a544564101110910215030b211111070403402c6035080880215660745083c00c100483c446107209480d00036004210050500742404060100190b4080000d81110005044030429000d29800b03010b00d503028115904000002625080e1040d400c0c550440c289420001f41c0c1d8041c1003564034905c411908038008000880f00000002c2032028001c0e40c5003c0001c01081020464019a02421000003450102c586e15000242c60307024280f004401a00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 387328965 1250 387327715 387327719
    0x20c0916050a091805070806010309020a09270b0f0603120909191b030c020309011d04021c0e070b070218250c0510060b27040606210b0a 60
    0x2101e107010700241011810003c03035081e1290210000b150102546150040d180e104100540764008884c5810410070b0078148038455980d80050700c5503940340203281d1040d56500205404e20350304a0421000701101d010380010006900740804089001c60b18a0601038003a008100c150500185180b00b14402c2d8a09605008000b010821071042c080c1c0080507056a603454120369906502ca40291040c1116080030b1071030610002409a0746079a00070700c10340d0014885ca010710b90704051084440c0144009660720360081d070000600038020411441d918500c500710114550782c0a52054480340031510403200500e0b6503001c0b145c00c5100398400250001c0c05404000d00260750105125003141141c8181c10a0080720140300100a03d0520408002035101c9614814030405210030369860811840c2401194103258540c002442222080c050903503c4c143d000b0444055644070f450f0b1800700030310078402c6583d10400241400c88035181030f007000c001d804002e6a001410710170380300c10403405881045014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 387330215 1250 387328965 387328967
    0x22218051b0f06070b0c091002060a0c03060b0f030c161b0905041a040f060222090501060e060c070806070c060507030e07050d020402120c0304050d02070305030d0903020a0b01060f020c0916 83
    0x113801031b1500d018540300340f140604a668906a150005110f940181a01d15020303a000342034070314447d2a01d0900d45081814414040b203074080b58481d00008070100d0b070b00d448134002ba00441c0704209441c0f040304c251402500401c0500741080d2030900b0644480340c00103441c0d8840c20200c91044d9402000304405942e01c0317242062054500743d005014a000d81400f00850f10f40d0b40507640f01079454907c01d000e980f0380a51828412448002404a11401b00050340c1017000c040e0020f5032050440b440b901010074104160740e41040703070700081c000c0c0700d0598015007084400038021001c862400c981300340c2001c0010796040d2091140316100c448d150010a8000d10f05411b010788810055004d0380c009800304101d42000940044250046000c1144542d5914040c1043c80c200ba280c100d401046400910307040001c6440001511900c0c2c1c0c5071100050194072503c2d051303150000c000700080807030450300000502070380c00c04007103000420207809a85200e00e038641000b285250449001d074107203501c0041c0c020b080b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 387331465 1250 387330215 387330233
    0x209060d0f051b1c320a1505060430080315030d230c030c250b07030302030a09120c0203061b031b16080901090909022218051b0f0607 59
    0x407016045450401e820600e8002a80455580c000000052880c0500003180300c54441c040c0000100949085554241400958680b00314801e12807000d0b082081d0210321002034bc0c41d0400031203190305003030342504070345858080c5400460b000900c000c103044901f84913003000b003004c2c03000305265500c03090300207908c81038185128800e003840b08070104103001c5e15851100400040a40070751580042001d082413400c25100c020410041e0f4141054104040080c00040d1095480b0180c1c182405601c6c1d41c4c41c211040010b014528010f080c2c0f10080d03144802081c2c00c04415090b050081d000c0c2c84950f9221402c10003100c9102c0080e07410301400700b00064100c04802c00d4429004110300940d1700e072401e40901d0540f0108228010b40302440000384600485da000300d040740007010302c60b01c14441d080c0c1030f40001301d0039a14050203260038401c1c40b84030b1454503c2a4000160380140c1d0a202c0c0711142141002555035206081e10000c0d52030301000b03803216161105200741054002840b55203408100d0342c5e10702107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 387332715 1250 387331465 387331481
    0x2010c050f01060303111c02030f0702040912080a0b0609030c010c0812100e0a050c0f13050303040609050306090309031c1b0303020705011a010e01030209060d0f051b1c 74
    0x518040d001c0544819082800b6000086009680b00311224082000446c1003c1c80b1030950514403c0a180442c120354010065500120400c11002d4170b818050000c00d018010142c002003110440040000800390030460160140a4848080190003846001d208080c440c024000e64103074030851100d10030b503200380d0106024a20411080d0b04094000001014041c0152840322003000c0041082c0500174912610176401362411130180100d0501040594051090300e0004080090000c0c008450190a401e410700525010301165a11a40d40c4802481407050f4000c0500c40d0040300045100054000300303842286c1d000401801c028a82046200c2c0460b1032440301c5810b101d64601e25429100c1070541941e0068080d46015a40e2280d0b0716003903003160100c00ca414204400c0128801d0b2599101003004003022082c00e00698450720040080c2c1b544c0190303289090458241084d2100d480b40a4101c82e01954502900311a0b43c40c4100d403902c41c901407890795441c040003800844103880309075000400d03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 387333965 1250 387332715 387332723
    0x406050426062805161b031403060d1505100e01050f040e0f0304081018050618030d0213030309050105030403120b011215080d0203040b0d0c031b0306030512030402060702010c 77
    0x10000f8450081070080e61001c0712140d06820071500308906035504941020302e000301149203070780105d042c1e03600a0704904080c15411580c51000c800143d01d52500740c2c8011060383c0085071603002c0510701201ca40a010102c918401a000c98440022466640200c0d18160341006144d113006809000c240402851341d0883d025451140385903984c117042e020300080c806031408038040d00d860030f0040700c541c042e90407500f42c650302c41c0003412503540440e001041c50760700550b04942c003880d154418246a8610f00542d941040e000f84000794021007a07480441580850f0b01c603444446020f5a10b10040d0f402d8001110042c01144001150b007102c03240b5980440f1110005051640008240203c02011142200d003a88070320303c2054810310150f88100070b01c0c0711262080c0300944c0340c58142550003800307020340e407178100403952241114540240650001c90700784860111310302c501408014014060583c07440162030705e0091000200c124080b0f102142c1c403540d0060000b51906071290b004642410764290191 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 387335215 1250 387333965 387334021
    0x1504050d08040f140f0d1505060105130609050909030c07060e06040f0b09090c0c0d1124072307030c03180801020d140f0402010c0f020402040605042606 67
    0x114800e2100403c0c000a042c150440302500c0907004103000300441551400d502c00d409101090001802c20544440c3c2845e040f50003280360344030240107890b98000c03101003031040c10940700e01091481d4400380000481c3c0302250b448a4035252124441c5e1a4800c06405101d42d40058006120f002d01440251040c440c0152a00d0301d0715556001c00f80b1000751036040808013541c005015441440c01c22191034000309104026031a0001400c5075542d034060b034149050511400e840e46920907081880700a00010b050880a00100c01d11a0180242c000441d00c202c049840d11011503640e02c5081511041540f00e00f90051828005803410f41d02009050412002c10158407403d8504004442203400204599000544c440ea01c18490030180ea100d1070641d039000c02c0030001c02c86d500644051494100350203007020003020300303035080c071804c001001e440c0079400c20f000090000700168000020402c03a400c5003043c54813800c501c8030b8000e800d000b00e1200c1c400c41e8005408a1348294003130145d12401c0b01034495072 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 387336465 1250 387335215 387335219
    0x20d0804080d030b010e0406080c0111010906090f050607031b0518030a0606090f1e1508011406040c0f09140a09091203060b0c06010b03060612040b04111504050d0804 73
    0x96141c440520360010001c0d464088913001541c0207520030780d00f008104c0302480640d007041065030b42c404003000303500c0c10003001000340300b400e15003035129a8400b1380100c418080c003101d40c10030822203603058a080f40c1030700c200c000240c0305a2082c810300c015004086120a201020004101c07156001402ca40d9114400b0307001c044080c1d0b40802001c60038600c20300380881c1a40c60901c4c080c0441b00102083d0281e541007803501c03029031410381c8001000048250b000184449115039941d00c40c40e2580001180d50300c0c183c00000702070340522034280321b504211001e024a40e20000202c84100107130b403003000422709c62103041c01005a502641100d0043c007030900403a882e902c4284205407486420140c0315a0007071104008202da05010b020003030b29414441a00e02107074640c941780c0e030b40170510038203040507000300204503180e58420454030500070001c08440c403400d250804034220702003a28101c982958400840e2100c1c00c10121a22071400105d4000703041c80e01c0d10007072020302d16264208a821150400c40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 387337715 1250 387336465 387336479
    0x5100e10021501060203090d080a030e0d0806030105060f180601030b0d0c0f0602030906040b03100506030c181512090703080310061202090d1b091e0510050a03020d0804 74
    0x11968056001c1d80244852810082c8020401d00c040c0c100c4001c6410410000081d03440308035800502c01d42c804015662108840b030110300a2504002151880c00313241082e009091780480341138054001140204010346540702044009001c081d081504600a00c4072075811f81e055940c078a85c0144181800300e2400a680c00013420107545400444030305038440820301640c01d201e00d031040a0841c5000962905555000088090050348246409820000300050600703001c80c41600042c000a00b41c5518ad050500e80380804d500800c019400c0034003648850f5000303240500f4030b0140c10142c02009480d26004c1408080081802801100688601000040054140001544540d0b49041c00c8440c060801780c1c0101144141d0141603001030052018000c559141511413008960003450100c01e814072251420170b9030001c0e440140325600e002c01d844141a908090481e074614401d0040025a4803144448007c1e810b901405811041020044c00141448000c1304183c6003e00c95181c109941d07050303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 387338965 1250 387337715 387337729
    0x50a14070f02060609011a1305040606110c01090b041511060403050702100810061d15041806030f06020c0307060c0c0b090a0b0f060415031b050a030c05100e 69
    0x4100c0005001040908181a0305120103508003c08a501c40c8080d450460500220440b19007040320102d00052a401a525159441401800003a106011441e611440502085d1b0b00c1c000e41c0b0303602d01070100c019401d588200c0c1400f06a94001c0036a900b42402c0a8800504216030403210003880340c3e0101040c00358004101c440e20031882035072403541d00d550038414050050005294a014442c03100c082c000c5541c1d42c4c00f01d0400303a1b0014500f103640c8207040b180b05d0110a110582e140d40080040c4a0300c001d00c7d001c0c00041054600310f0203440760b8031002c465401c08827000e40c03201a00c03e1064a0700c950021b14141c00170705e2945102d004403800c01103103071100070844d8a1200d252021a45542000007046034080c06103902200d01c80150201e041d0350b4581c5003074140010002130401c08040001400f643d03d40e80003031132106c901da481e000f10f551a480c102d003070541c1001d849042d8422900b80014149800c07180802600e40c4103400600e418a840305014502d4602c001030800d000e901e80303007050584c940030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 387340215 1250 387338965 387338971
    0x1020c09010e150a0602100c0c021008040b01080705030c060903070b0301081b060901021b0a120515010b0901020d03090309050405241f180801180615060c020103050a14 74
    0x1160100505101c5000007225940f445114055414a0b00410440d90049901c02110301c50100200b03120750b0681040702d5440500b030000f944481c44644000a032a03006031110310462081b405016240d0300c440c3e050727966401a100d1907a156200502191842c14041c1c007900340380d41c0103411941219152083c00b0501c1d00246c01501c000e9000e610320010040e081503202c2008034080e1601450058182e0000707444100b199801d403101115100041c807903072120230034003000b0302c00301c200024544820b107071040e158407502d1140c41c0442d0044002085041050046500c8460160004e0803031101d068030035405403011550541c24030100000001c2e154940380223042c07288000c12095020388460b105c0c0e034405078014040007806000c40d0047c800c1c1c00c01b00c8038140791082c02a0b00b0480c0c4002c0d07240246203417143c0e080c0c00c902150350030310841401298249030b207200c0031407189030180b08180caa146000310000301c1d44079210006008980c128091350090344000d40101e0000c8001c2800002d072003a44502c00010303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 387341465 1250 387340215 387340229
    0x204050d0f060c050325020c120f0114010803041503061805070320030c160f0507050a06030207080f0f070f0308070e3304030611190302161101020c0901 67
    0x1c0c10020841c0522580c0003600403400c1c4641541480da81e2068207248100c030880b1500112007010032241c0c0200001544140001c10384510b90b040c25003895260b045040c1c1c5440d1560805555103049018980c07003d041c0c44e0351030700550615189c10303060a10085030407550424542d5600003c05c60709090484903201c22100700d004103071400d00030740003003c9549062007800c04441001480d50300840010440390420001031401d030300c0b400d280440031a000803000700246000040c84070030040010114020040303e0084800d024001d549140c15003e80c41101c50052054404101c0c1000490051016140c1c0710404820079040c5a155500d0003007004112000b84d001c40e40b000d041042e1181e108400031032906090701c0034586411140b6465800e10b102801414180003c40c07640821075089505480003590807050074000181d0075562207046d0b50200d00c0480e1031002c50800070381070900a000f2070725900b040c4c1e104450401d06d20f0300c48072503017089059400c2c1107020350f4104040507030300c2e550302502074141 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 387342715 1250 387341465 387341483
    0x30a2d0507140d020d0b071403040b060a1d04060c05040518090c0a140d031e030203040b0a1a190b0a0306210f1106120a0b03070806060a180204050d 65
    0x7045040c074882140b40328014403038164510001c0060710380c044502d1816500407503030b105549030300c03070143d03225402940d0303800b1b0140c03010040000703000b0b150310f001c1d01568054940344452a210042c0780c502c84491212010204280b0020900080d02507008410107040b0b8a0951304090f03c5100141ea00040543c03498451b000900c2032004c500030501240c0c0c101b4900312005441503280c07904920914082c03924652054101d00c03c2102414010180c00802c036411000e549510301d0b01084c00b42c000d40043d41c0c00d4580031181400174035203401341c1c4100e4001c2c4c4040c0151020a2104a003006103c9410140c00c4007403581007200003505050000140051503010b403008241035042000b2900c2d40c0c030482641c01c00070040c000101000c542e00d004101c610607000314030098002a000003184003480303055101d4403060400420030420910720350180d415000e0440544008943e284a2690380b410b09644160707004214400c2002600782c45102207801d00112000541000c2d614800900b40c050320306010388142c49 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 387343965 1250 387342715 387342719
    0x504111603170420090702073b0a05010e040b0105040c0e060a02010618050c04060c0302010e0304030c06030e011116030c2003150c030114030307150605030f010b030a2d0507 76
    0xc11240403090307050043c5c41c28076186c0762045009685002c54401c2c0c440b1115101c40440b107040d481e40c031179154a070302c042809060f2103e04801c40c0000908840c5010114540000410313880030b0405901d003d55040b2421080c940d00389000c00000b01a5140c0d024203002d024988404581c6822025003007104035a000010b50525000806100c90100c40344c0101c91442c01081018103103c0c6000c2d98107031680340c505a00c3c170071464136046c0d00404842150952520004c0340000400080300740c50b0381543c44c3d503601402190070340d502181c00c0e56010190744181c19000e0040420300115114030001c4140280303402c2a80305940c0d00c0300e8070110308034138031141201e528610084003403d081003040c01000040d0f00040030392506c9513200000b40018001c0c0c22500180c1070f0b0b441c083d568108142c8070051341202c00b0100d02c03042901280e00070083c07403207118000d024048400f0720b090703010b1103000d00915015003e400c500d1034668804a022448001c510b2030b240b118070720b240c80a024040c0100040344a0b400800c20b84d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 387345215 1250 387343965 387344003
    0xf02091e01030b101d151804150c1d01230c030405010305071806120e0607080405120403030804020405060a260c0904051903050903030f0d050105041116031704 70
    0x50250401042d90810282144405c1c81e00da042d10743c072010326280204016102c01c0003d00b03401480c186036003d4484201403006110800032204c185c0b03ca45c0310100200c2c0d03001c000c01e40d10fa24200e1300003800c01d2000d140c08071155018140300d2000611101f4002c840042040003d1902c0c0c000840300c2459034008207082c483d550f018401c1d6074020710325080110202d00558020811080742d4058502006042401003c1c015036903000800804e8108095400c5443c0011000f8866002128155190721070500d030391140303403985012a0240c1e0341540c0c46540c183e88035002d21010b40302c042c7c0f0060700300d000c01400040800001c0b07082000c401501014468508031410350764030f82820344020b40e00c41c008642c1130000066000a641203900c1d00e101c00301e12910801e0800340d6050040380c04c51501070200081400b86061030f08020a245206402c08000136600e80c02880110380c80700d100092500d408126034600c18005846c2228198424608041c0700411450b00301c0e401401580d045404200c0055601448 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 387346465 1250 387345215 387345241
    0x41112070b03010509010f0f03170909180d05030907060507020d060e03040905062d01120e0304091d120c0304050411030603010c020a030f031503020d05150c070f02091e01030b 77
    0x10158139200c564090304140005100c4029880014a50b62281021410140c00041a00d1080341300034104009840c001cdc0c600c0d4080c4000842425241c01465084620a400761090ba801440f6507001084107034206041590303180e000940c20707a400450318214000103043e0380110301a05000e0805991241e141c8000082500d0010340f4007449504400303c42d000b08015034800e113410186c00607103000714011040040c1d41c5030300c0407000f850106052510030218010000300900442c1d084003810804010300d10b0040d44040b11040078026260000d1400c84404900400604101c00d4030300c0580e840d003941d400015040702c0780e0000340240f10340080100955854288641c0014070b00d203001801c0105a10385e40140703440715002c00e0009055950346042845111038000710301441d80039050028040c600e0a00a80d0343d5241c8650321710107556a0009030005401409591100e6405036514452414507401c000c00c400d401065124004158840008000e41100b01e4038021401020120101d0422820003080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 387347715 1250 387346465 387346469
    0x106020c130c0203070816021807120248060703060801090b0106140715020d06080a0c09020f0c1605010f0509090f040c080a052b0206041112070b0301050901 69
    0x200c1e8900204003580da03401000320760072240d101c40040d41d80c0280c0c03240301041580b40700d40a900a00442c201418032442160014000d0300a5150703840e01c600390f01034000c1603100390300944510102c40740e049a9240382c01c03021440080860b00302d00c000301c440c60030603d612442e415404106603105c2d0040c00300c910341521500d03000d004044000c0c4205d070706544400541c9403040c841c05040081100140e60003059032000d135007130168020364070359006407800010406504000c0008503100d14000c0c0000d02248001502c43c40790344d02142c00c035805450144403600030f4000e4103504010002c104000b140b102d005120b03255000c00a4010424503a003010001810b5007008036009050101c1000114065500c1d95009544a0000b25001000750307a189000c10b4100d110f03038801180b600c6158417040400c480814075403075024489118014151850303200d5101a010350b4901c901580007000030070086840b2040329240014007814a624011620100705e241c0441a4800b1007a51000700060100703240c01001c040c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 387348965 1250 387347715 387347749
    0x120c030906090e060108060112020a05040e01050d0203060c0a0c0b070c05060f0c042d0324020405150705160b0a030501120c0e040f020d141c02030301090905070e0106020c 75
    0x180b03242010441d24141001500d02c9040c000c40c400005d840303038030604001c13001234241c000554032140d0929010706190810b000e512044007003a0b0002c44c85007483c10b409032100760011b000740314946038081e102d9441d6000e102c1210421902014410114424405660060001e6034855465031f07020b052003820900e0107090041865081c509010121101c1030944090700c0801001d02c004000401c818510b00400d90150545120200c1000050180d01800084402080403d0000009040220404901c02d0b0f000c0c481e0301c05000107200030340403500400f41c44d003244100204c07000d801d0341d2801d070b03545c500340c942c484e052102000940401c01d547c5070060500500c040c600f5025190002e50740d011820000d801ba181c005514840041e0034025011150180c07a030f0098001480c00030076003420201613083c05504d02c807901c10000a0f821840c050086c40380034900384d81c05941980d0810b4a6100500010f000584161054180114907030041380d4049000b84034940091070800004001d20100c2ea50000c2009 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 387350215 1250 387348965 387348977
    0x6090501030e0c031f020c0115050117272d0f071203050f0f0c03090906061e03060a1d060f010f09031e050a0c09180804030f0f120c030906 61
    0x4469440000c2c1313034610400707680c9117107402e0044070303420304024000d80159030070560921950601d080640c04241c81665000c0e030706d40d95007180000100c14855015035060104114402c1c203001180c5544049030f000c20f800f2810b032403d45400040c4008014800c03800303081021070041c142d40c007030203080002c62900c16843c001b03403085500c1c3c880c81d1200300000c4100901482000500c2c01d04214040741194207040d254400c1c681c4400c0d501380c0241e82c0b07030014121075024000190100720302c0d20f040010340e40d005c000c0b12940780550500400b462000e0b04017811150308049001c00c0805ca460420801514032031001940c100c10740340400070051003202507105181402250801303040c0d0590702100090980707802282c03100080d45414216003560212410180c0707180a419586400c000410590004440640c0c03010303c0314040d41998030001d611400c900420a00081204000103000001d203000024000d0103803014621150315618820070300704410500007000c90200000f05a000b1174507002622140c5411 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 387351465 1250 387350215 387350233
    0x40606050112090215030429070810081b042009100e010804080a0903080a050a09060206010506040915091803141602010309020d0c08010f05090118290106090501030e 73
    0x4213a2442e0040c0c040840500300200003814852200c46808e5070060090141010409100c034050000100ba02d20800182c4907201189030482d98a26904c1500c80300b50150089014a1450243c08400301c1d6109401a440b428210010488000000e072103511200b09642d0b41c005441c10024480c0400c505030052200414408621741d0f400590240d00a038461560703551010f54110507600f03000143e20040c01100c00288140c3c845d64010080c0403100d90f507031107080c003498903864141d80b1160240540f907000201032004000c007401e40e42002000f284044040342c1010f80322400181600d03a001844203c0c01180200901050342c0b05c21080b142c860b02c020700c036081c060303598604955109004400390401d030711901c4030300035540d807452003c14141c0c0c800400c10140d55140580703806400040c0214040358a000300040c03604606009848101600950800c140c3d0441e656555010b400d101400401100b00048511041000e8040764040c09050720340410680c07610000506a455000f50350041e41c02c24561 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 387352715 1250 387351465 387351469
    0xa12032a020a020111070909030c11040e120f040801090809010906080601090509150904031211040308030109020f0c0709020310091a060a02010b030613020907021216020109030b0406060501120902 86
    0x19100b203641c240380040240c200c2020940c600051604031411070340c034001c492810560040c043c40c0c0b000e441030454010303891010381080101c44012415101603000b69400f004403106e8000141030710246602200e04040e00e81d01c200f400c5490b4018210364074800041c628000f0b40e003204010000301854500300c1510725011000070001d0617648201400360b52060042080e1070f151840d42503880780c0260440080e4645030400400813000034202600c1c0c0c41c50400e0105082118004403429650800c2d00c8071b03e141d1904062070002d40c805c000214441001b40b2140c845103505100c03840c01007074540d40140e16800d0583c41120086415484252840d2400d82c540b822000d10020348007880604854098490030300308416030161a5008009038540107100030040201010560202d12500944220f4200e5803038140c20f0740d482403940303518060729000780502442d1649140c2d510900f10701c1031400700d1038541c1e00d542e81102401c00f50307070840c0c54588406082c801540d200c4500c0386401751566041c41740d01c0c03c40d00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 387353965 1250 387352715 387352723
    0xc1704050102011d0a060b010903150609060b18092e030605160221090a0e04060c0e013603030807030e0c010e09060f1503041515050d050a12032a02 65
    0x2c1c0007440c280d100c1700c2591f545d038052420b800003107410450186000101440880080c117a5000b804a803528111002c6002380c541815620b000b21030004040c0c2c40300058040000340300004110f0303a0b24a180d0b034540d010348010320454280d04002040081e54403403c5146c2441a5400202412984c0255110011b04240d0003d1420105208104102c1c40d4101850440c0c0c424802e099402d600300035130b02030000700b414000d000148100e0040b203080001004005040701c503009200c41b10f0f4001840503040c4810402c403170007440c045558002801920442102400300081e031503034030640218410700100000c03030b03402d0b000711440190b0441c054000d143c0d059001034541c40c940300e00c00e40030705c0060300000c05944801066011447d0000c24030700038400040e2b00c24409034400c44080b201c03605241d8881c26440b45070b0140811080400f400194903a080c0828040001c10042c426621071244084110120b0715024036070020382403544d0003013420444c015407086488203145800c2402480c1e401e5074241d03076034041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 387355215 1250 387353965 387353983
    0x9050303221109040c0509010623040302010522050904200108040210050c01061e050117040b1501120609051605040e13050a20090c0c0a0b070c1704050102011d 70
    0x241e0142e42c0e520f40341841d05c00300c212500b040e0341015959002007803540d003214402c4800110140c1c442118807500300c81c6031b5079000c2c5100c000d012882c1440120404403820250301305405403012a008080d503280c0004034002800e030b03829030b81071040d120f44140b40c101d61510803086200070f08001905052660100d40c0200c101001c09080220110702c100303050700290010380c010800466850300329008000c05030701045c00c43c414913020521600c00c0315960500c204c0303042d12407a005450100c0d9981e0303000701d150590311003960701070410102c4250b50388408a0380c07107003101030402c84500142c3c9180807848440100541400001030000500c001c11550581006196000400c1e200c107071607020207444c05900d880c0c40c140005040340300c00c8000029400042075290783c000320403a1940b80549902c0c0c01c050142c8070355000403109810175a25280800e0386503600680282c0036243c80016520a03442d9040c03e41c0075507408204402c0000340801c0b072581c0c240650544010300d13240102e4004507034155981c0e90900a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 387356465 1250 387355215 387355219
    0x10e011d04330f0c09030f08030a020d150302040b03030f190c05060a020306030c0406080303070315080a150f0203070c030c08070c09020901030e0607021504060b0301090503032211 79
    0x8800801d42d9448052250404000d0054400b5105558140860240410300b6091921500d4001c29500341482910010100c81e00855082ca17003040c07944a922880e80002e040d00c41550b000c110640c4000564400e1902003c4103d110010f014294410441030b41e9214036014840d80c8144400e444200d404c10481d142d868501c0380148140c1420300050350b00082d01e05010302580a510100100f14446400542c030818003101070f1081c0c556214108021034215000d501c10a50050001555030707802544403000d140e040c9400a9150760f81c0d8100c2c40c0c0340111101040310441d070403601500000000d8002c512208004040641c250720b4880c400508090b01e00c0000790420010901c4182440549801c594004d60040c500c20f046030380300c0100d0400b0b580100c00d0503001030314196641302c1e04400030840d540901210741c05440d2280c88800f12001d1000050301c1960019541c01140803156424401c20301c40c64803d4002d15142e01d090030914240c948442d4008a0640590303a6440c00640075055a060200301 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 387357715 1250 387356465 387356483
    0x60114120a060308030702070f050102060c0a030c200706031a090402091b12010303020c0102071406090303090d230c030604061a1503011e050a0528030803010e011d04 73
    0x10107200d00050901e55001901a400c00800d1001107035000c1041415209411100611950380d07000484c0e031141c0403504801d4100040c00360740c0350f00b88280c1020a50780410314082200c0780b484805040b5008100c28001d0780c43d44040c20410070b00350180a14070701c1c4240303c0c0c0300c4240090442d02103441d03004010300c000d11502d04c0740c0006101170801e08000c2d055624169078142c03502400c200d070f41c1d0007040c00e020940152003890350f903c1c2c2c00c1d840080d202e810345000c002c0e4080906000802e0250303641159154552500040c0003e210f0754a0b6901090b821074080c0c0f480c0d9035506064464030102081c290700c02e8080790440746c0101d101d80c0300001c1c0e0f19046688141c00241c81682011422550850728044550104010301030300009004c001c05141a2040082c1003056000304180b07500014146100d8980c102445920800482c40d00540614040c07129403159801d603904401c110b04c1c20702c0d4035042111030550110045c00341800c6918014054207520400c00d840f40d0004540d41d1010340010001011061 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 387358965 1250 387357715 387357721
    0x100c020d060e0105060108090a050a0224071b060c032a02090907091107050c120a1401060f1202030c1306091107050d0c02010c0f0303020f0714010506011412 69
    0x450060340882a5000401044900484500940a06030940750f5074000386061000c10740b10600402d8100c240307a07000b8014000c07034080d9400d2002120340b0b1107000010501030075400711038411030341c0200986407040f500400c000c2c2d481003c00d401703413009400810401608000500c0060340120303c44104602c0200304101c048090841a15284041c1000a40207136030032060104400000501000b038840c5848288044080e20310300c0c0315503010340d034070291840c2e02c2010180381034105200075800745e48402e826240e4072601501e85214109100364202d405a5582da82004114a83c842d03410181105030810449080c580d00029500d00410714050320411805a41c2c2068500c1070b40050000d00035003406210300354003000b00041981205005031010b006204401c02c110348100100c6541e5981610740203007150158807442d03044441c0c0103040702450340c20403003800d19501603000b4000c0140301d0030815181400c031011060079070f1405040c07141448031000d650403000280324103503a0070028261400d91180c1e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 387360215 1250 387358965 387358969
    0x1303051606060902030702060604291305010e010612020f0315030114070509041b090b030a060306050c0a1701060210020711060d060f15020c0603150a060f03060602010b100c02 77
    0x551499005000c03a02d0040c00007a09101c070380166104052a4007915450340c5c0d400d0900059401140f0310200e8851a21a8145140c022100341100c402c0c0140c01107840440200c03814045030801c0c0c000118100e2080010800346500034840d103a40d011107102903081c44d480c0441d5082900018100c460f060341111144400c030b80b0254400e100340d4000e40c00480b074906000101401c5948584400c5014904060800342280c8521208a08130145c969034615480d207001c1400e505d0b900b002d0840d816085d01c071100000400e1541c09040d000c1d80d03489121327a50756901c000d00a014500c2094094140c00c0c4a4001005059008a80040c0c8401c9080b4090b1b6103100b98a00107035110045c041d802d520001c0800c0099410401e0b034046000d641c44202c0c065001e070b4803074a4ad4001540d00122300c2005900602d40c04445090600c042c40d00038007091800703244c0c15181000500900100c1d044140002d0084540105036a41402410300404031030008105412220307010891040e49c00c000c11092005241e120700844d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 387361465 1250 387360215 387360247
    0x60702100f020c030c0901030f02180717150102072115050402030d110a02130b03030313020f010306051f021509101a09150f060a180e130305 62
    0x5a402014422000d03440800a4422080940c030a00144a914030351941e908002501e0600d1110081c02c0389401e0707107540c2e00c681c3c541111044c08c98010864005c06020301d0055001180114542d0b00c07109665520b225118001d254020442050754150034405c000a917000310305041130354070f04945840003003280040c44140700220440244514014100c00321903007100d600450245108070140d640007038800401b02e81404070389034824007a8000ea101c0c01c00501d043c0e4000d40a1f40000e00010a1000503c40081c0c2150400c465024101c0e110034035107001c51400f00c0012045407800d0030100a41400d00c40804e01c0e8605610700a2200170a006c1680c0d4103078020482c0c005501810000e0032242c3c542420300f6515520440c15a04415041400c01e42e00b10090020001105c075016060903c169140382110018442c1d050b04144c0000150381041c280347c4480004044440d920f840303621603100d113003a82000e10108d9a1200010f444803c040c404c1014501c0c941c90011a0980351007520380301250300940c40d03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 387362715 1250 387361465 387361477
    0x22020f01121b02010b03060f09150712020c100e0303010b0d0504110a0b04030611030f070c0614130c080714240d0504031101090507270204090e1e031806 67
    0x22a11108082c0591a0340c15001081010030a40c10768116032604030b00400a001c007600d2824268000c111441000480d03202429803048291511080303010aa0400f401242c0c4a00010003154004e400100783c5491640a24003c0d200914000c528643c0340c5100610180600240a10b1198407007000c0740500140f000c41c4451030100a0a440c0b070f02d40c0c0c50110918a40c02403200b281d0031410700c0300b8820411401d90070341e0301c25552201120070b207503903084080f01c003250305020440780c050743d42101c100c41c6844101d419110f4240c25400d40354a41d2941024034041411360710144480e40480c105004d1800302c6040071303401c4001a55024001ca0030000400d02d809061504c040ca2030501151900b6155051f40005000764041c2c0c4505600d48000a2041d0998440480c040c004c0c0c0c1c03214a00300411005c2c00c0e81310501d00c0b000e0f9500c10340100c3c001b0241050380c0c49035000c1495a5256003541c5074160040c003140c0c00c08a09405070340c0c0740710f83c80340301c8545a002d03810724140507a182c4180c01c98661295421180 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 387363965 1250 387362715 387362741
    0x510030207081e21010321050c07090b03190c0e1e151003050f0117010f020d0f0501120308191b08180a020109180e030a030522020f0112 60
    0x80044482145a4941013041100d42080c1101000803840040c1401c2c0da050325009200c8010060510b441c0038280801889040100030003000792941c3c9031b1080c090000a000c0070500800d0340807a40c41003520345000c079070400a4034a002c0428000140b00760802204036000740e000c1066070b40c3c07404201e002484c4e04005070040145000100081018411200d0003030741c00072030300110710748600c030740407802c07030302c00325a00c52800c7c000c180107002d242151050310521120300000403805840b9455481d00b0381c0c1105d81da150383c007038994042580702c209900507035016207040b20f01404820003646004008080180c0800c00180c0c052078002d813440f409401c250b0340101466a12900c0d400790310303401009100111a09817443d03456040d221298080030500c0780090307070140d5652010504101d0078070400c0d0302c907001c08441c440c0d486101d98a01c2000303002a10003240f8580b00010170f4600001c150315100100740718a04040e52040d001801641d50380c03030b103c3d407140003841e000d11800c03040005000100403110b2005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 387365215 1250 387363965 387363997
    0xb21190516090c170c12060a05040905071a1204080a030f05070c050d090501020a060b04060e04140105060906010504090b040b0a180e010203090715180308030906060307051003020708 80
    0x425000304503000b000c0b01d02d8044e038480d4044000707400c10650b1004240d90b02c400b8070740100442465000410b8860f82c00800003003040c440d1559910009084035803911742114a600030b40b01c104070f00307030450391880705031910b69403010b00d001207284842c0c1100c40000c2c0300030045580422840c0e006c40c0b10780d009060300700041c1c00030011410b192070040c0520400960856080c8104541017805038412000001140c506800800e100000b036034400c40030740420481185c03c42e56a0703000240c4600f203101030a00a0307000e84400d07192080d29150300c0d400d5070001007030306000e0180b034030900c059644e1140480b0105d50305448001030011010000801074203402000d941c1c007200c90305001c00c0c0146110425034009111034000c00c12240310f100d60320b0a03804100d0f000840b81d00002c44c10803e0048000d4524442803040c5040244038410301d151035030280c101e40040d40c04420120400c98145003c01145810681c11030040000914120024600c100e0000b05c80e400c05401180c280d0411644c2d0068501248102d050f030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 387366465 1250 387365215 387365219
    0x2d020f03010f03021023070f08280e0a050d33060f0b07020d1a0403030b10020303040c0b0a020f010905060a0606080114040218060c010b21190516 64
    0x3007410b03200640402ea100300b078141103a0030241d0103140e06580403080c0e512a84403100982082c844560003c020541d400e140e0381340c460300000c140b5802442e511180840c14030b000000b0349030b000994518400004140601450081e00c02e43ea104040d03402c0703400807a0000b00064507490280d80110440c40c1c0202d00780182e2004030882d20a40d04e0f00340055000700f404001d510b51301c01d0b2800803100280310308072480c40704000d04030143c1040c0a818072224051310340c0d03841c0c0401407850403c0b100011541a80003d6a0382901601894150030010709901188000c5055003002e0b11003103048041031050141020000540300340c03090090003c00081c1c1c044e113008019040c05401d090b900e0700000c075130319840c5034030304440410058051582581038038406030b0b820004450003420b100c001d43c041d1480342180b80019182010b15580c990041500140681c0082004882481400180c0c00140310840400322000e00700d1040080c0020ba030301c015403800d07442c499074402c103040690610280d10680d521512a001c40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 387367715 1250 387366465 387366479
    0x911160609020f030a151a090c070303090506040308191127030a0f0b090a20010215010b070203010e011b08040c0306020301240215010e060a09020a021b042d020f0301 73
    0x21704442103000b6805101c0d00303140e50410b503249060182c081c1d6008c075845010500106c0e011019200071807280c01d0001d20f0401d2601c2c2c00b403601c481224102c1c0011450000c206004804810041d01704001300003d10081440580c8000740d070050401c9a01440003446401d00c00b0b18030854046202880603083c0c03200e10b05a4200400085d4070341c0016910902e10301c001c42e040080c0094403442d00c9030043c030f94440c200920600f03072802e0b01d01060300904500c00c900e802d490709400c0075a00c500074030074500e125035210358504c141829500c00410018060345007200c2048501c03201b070075088138a001c40c60300d0041641e99151506d081c2c6084c0d0030150005d840880085044039280008004031103070755070012034001c503802040743d60b0032401d00c2d280b14010388038004000c0d10012101e07454009000a2010350010b45a685d03010072030308450310020069001e02c1c1e04003a400c00c800861240071348140c40911041c600300040d4500c0025042c007400b0000c111080c001041c80c85641910f1001011031a015920f5944043e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 387368965 1250 387367715 387367733
    0xc0a030f09020915041a0f12010b0402130312080c18030a0b0705040303090b03270109140c01030b01031503031103070507030308010e0903070309090507050708070605010911160609020f030a 83
    0x69114069451b281d010b02420b011038a880d02440360082c80364062a000300140007400e0003994680c280c0d0340d220705e6146407035a240e0000e4a882120300090f44065440c0d07081c1115040204208001800140310522100380980300c00c54642089075100c009d00d89030014041783c680440c2c46400f51074080006c007800039082d4010300400c21240603580d0540203d0f00e0b060800d207a0b2105a807100c80390500c0d075480c5240c03140c2c014080c614543c0400000604000f4035200c6412100e0300c4004c0c004943c12842003160f1a40c0c06110b80b0348402d0080c41c041044090180810400c4411800040e05110191140d110554410400c0360360340f55001c026201115643d18002d0100c4400707004041c41154048002107002e00f0010903645020b40541e01c5540030f51030306003011300070f02000e024081049410001d44000c11880b0004045291145500050755072520705204110384803000d1001c0d580314100241c00d1030070190260a13440b40d03009a00001d503905588002078030460252801e64144c01402c00c4c800500403c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 387370215 1250 387368965 387369001
    0x20301050a0e09030a031805160e1b18060702060706060e070c110d050709020f13060e03100203070315090b01020f0106050307060c08071403040303020f03030c0a030f090209 76
    0x41d400c6902107484000aa00380c2c44112a04041c0741e101307003c500c0781e10744070f40c12030310104002e0003c1060103aa642c403218186402145880a4940c804078100310405201548540c0540010f808070258015443c980b0740f14420100303400c2c5141c1c036403d0083c0c3e2a076100070071942c801d540100820b94a401d240740c140041c1c030307040c40b4000050016000242156000340b8198003456400141d6080c2c01c0310700010002d1070304c448441a20184242d8a0200740d81c191032006000700e9000f41c0d070380c1d91a80d4407841004d48040b00c5070080420409820001102c070b0b2030020ba214100c09030414007507226904c3e20007c4000380316084c0070652542e030381d100008040c68180c0c8000038580083c3c4c00d881e249a6140740c000d007692040e20980b501544a04010010203100e004905559403150020391704e040c1d02d6480342c0000001c2d50040d80d10315003002904004054041040b510041c40c0c0d82e01030b6085250240c00381d1024042e160841c0141900c601e0007905041e0b243e0300a5818030342c010300c90701c05424805040b00740807000d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 387371465 1250 387370215 387370219
    0x40f030f060c0305010308040e09070e0a1d16170a050d0309020405130c050d030c050312091c0206010e0c0d09110f040506030a020103091a1f150206180307080d02030105 74
    0xd040003489620a01604c0d060f60b400c21303001032a00b4900306006030311000007402c690ba81d0044000c0413500b001c00d00300f42d50140340c6518000c54054080e64a82488501c00702202d81035a00c80600f0101c2c4c110ad04072200708690104286100714030010009900b800700c003840044c40c0e80520240d1a48007509a84842e14142c02a5410042c955800c810980b13070465504000d03012003041c1c078003000705150000103006020310903d44040b20319220b03560340345190001a1484485d078400010002d080c40c0801110140080c0388114003000c402d51507001c1d45418040c002d20911118180000c2c5007a00004c0884540e800b400c001003007180513500344800c2900010300d969204210b0380c01c400d030183c40d00340650703400349030300a01910141d0070a40c0150010818200c00f1240389420300e4400903010012241c59200e040e6803050482413103841d0001800d0301645030030492446000034801c124055000a034260301145054251450114040284d451805000401441d920700090340303030780b11820394000c0c0d8101c0d101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 387372715 1250 387371465 387371471
    0x807170c0a090b0a0c02040b030304120503041d0c070f031421011409010e060a08060c030702012a0e0a0b0c010e0f010203010b0a03110918090c010f0e01080a02040f030f06 75
    0x64501103c80c5105626000d0002441220150013524003035000603a520313401400c89203002d559402d00c0b01c10340000e40302074819800100d800c01043c2c10f21202c10491840d1021a214541f401503100d02c8a8002e410018100c511140510410180500888038810704050b04031a1502c4081c0c1c0e1140100350198801c20300394511724000500c00340c1401c040c4c421440c00405003071383c580c01d00b83d844104400061805601c0510803100059284084c4426401040c00c62070b072503500d20302508060300751070842c0203110051444203850701005810a806009502842ca45048484c0c0444000340180c9483d402c40303104440b0002d0264520b640551001d41901400343c140c4640c8200c01d00c04074202d0009106441001404019a031440d6220741c1c0142c4aa000c00140e40307090107451000b1031a0a00a0f15104543c0e680074404d0109140b410400c68404c00301c01d103403680d0550901e03000180004060100503050041c1c00000c2503460031550140c170003800f120303124545026500d050000403c02070000079a5403501d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 387373965 1250 387372715 387372719
    0x15020309010e1c050f19020303100e100b0702010c0204050a0605030c0a0605040e0c070b0708180601051507050a0210021507090803032d1f06030b030d0807170c0a09 72
    0x2c40e03001018607100958069201c60800d06603000d5204808861708501308011010145000007480c4914195070350082d500d030328008120540e43e040541080ba41d012507c000c0002d03131401c50f019001076480d00e151240d00d540d91440103072036914003900025802801c0c50100f04410700075621180494100328100c51411180c0b1043c018a09154040c0c28000ba00c2000240419444040c42c2c9410810141c85075140160700e403954070004034140d552800040d01c2c10306100e1460303100400d02c4e0740b500070000076181c0341d4134001c0064800903c1440b42101058081131400a0002c284003681c449030300501080200700c1d24034802034031101c0d45c400c809800b12810010031f0295200d21005c100707444000c4011803035512005074144906c540b250156042491012190b5095402e0880030307030180e80300c5501841601c83c04402d64000c0b8055400c41410180350181c41c1410b9940014003000c81100f0b400c0050198907480c00480300c42d034100411005140c1082d040c03047d010b10800003007031100d00594650803e59 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 387375215 1250 387373965 387373991
    0xb03070b07050a02121b01031407030b0d050604231c1809050f040209101a03041515030203010608030906032e0305160603050f0403030e03191d030a020604091104031502030901 77
    0x50f00c420270700054005c03200f0000d00100c2c082c1d445422070020080c5070070140c6056a607200c2c07038003d0445084a8140c403152500c910071022585028543d510034000c2c1c041c031002906081550781d256961102003104401c00c090801000384d04000103060311310000e1001e440c0800c0c44010918056070700328051013201000601c030b1120041c0308815140301d101b50b00b00504102082c1035980e040584242e03513041400e002e040c944905403107034101f003504803481882c8551440c01050300b11503040d4002d0031190000c0084004603940c440c02c0340d038030076a041603100503200111300881c1c61b0501e40c010b2044044000e90702206002c00019280242042d0020810a040d180c840482c191340090341c1c00b001032010400840c002a001c0d401542180c03041c482240d08041c0c4400100945540e151020700c04140d505c060f80581138100703114801428400c1d0300400d048070080c0d001c52003c0c800d80c8140d6062980d6441d6442c407104400040301e0080d0307007000c80c00d1002c0080c0c400b118029481030f81c0f008d82c5503103002a0b560440d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 387376465 1250 387375215 387375221
    0x305031005040603050601180f0e0d0f08010810050c0c01020301030807170708070303090f050d09081203070509010f02100f0204051c02030d030c0908030a0f120b03070b07050a02121b0103 82
    0xa80d0307011000e00b86da0303445c11582c20203070442401c1708400283c44a41145002030700784502c0c0403051102c0014030a1410781000604111520041c2c0810440d5010040c41003400018200070000b08455000031070341d1b11800c111183d4020b0403a2000030354000800082848500c402506000e8054882400181c01842e0079114501c1078040061000e0b00c14801c5d0700c0464040e41c0145605401194101c2e040c121660300c3c107040403240550360002c42c0d1742040c20310034103c00b04001074a082443e201036255003850603003e04507000b10341804c5d04000907440c408400c54801c3c05845100140404144014840726031043d0194105001c2d51340206091007a03500584119184940d1007600a000303050460160381e0f085028205951a0314180611108000f448001c00c000a100310042c41c0c0e100714a03091642c20007010384200c43e06001e0507070300300500d1040a940c0420110100c440100503141d440c0d44615040e410b041c034614000c0e51203500302c00e00443d00880864425402d401200e132046080c50428015021 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 387377715 1250 387376465 387376469
    0x150901060f0303080c1306032c070302090603030705030324030d08060613030b0108150f0408030105210102071515060914010c02101205010510120b060d060303050310050406 76
    0x1010700c514040010a0050345001e801c641000041d03490007944a00b00c01c403d1480343d20040009503505400c0d0400b00c820426151890107807600450260f48940143e0741c0c2d60034070300000e03104141000100f085d95804200325210140e004044d0398a9150443c10040e0f0141d0741d00c1b40b03aa200b1020265528207140c04108030b00c000496480e4005e0076200d00050000c1d40d002420510840c84034200c001c0041241e4400d141d000b8400d05008280041c90039070003421716a80a010304000360500c0f01400001044030041e00e055801c2942c010b5910740c80e001081c080b010214501c072031254030001769181401882244c184c0010070051091101c0c90801d100e09103820b100d40725800000d0340100c01407100400c1d02c405d4640075441403420081c04003042d00000ca5413281d1340c452002290307500a800c04002d138240034090050804840c681031090710154017030079464030501150040ba640c1c0703a035841541d075a1810788a0002503498100413490312072a010705154070549215101c60060100003d040ca03180c015042 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 387378965 1250 387377715 387377729
    0x606050d0903050f0d090c05120a030503040507091d010c020d0507201005031509040209180f060a0e100203100e0a1118090609091b031e15090106 64
    0x4a45640302581400a0018000403010042c0811041e0410801c241c094008802c4030705d4000780d96656031a12038280302003940054001e04001580440da51800300d080d0203140d0b0182811992662980ba0090410300507400c400080f03854503651030528040800e00700480140c890080100d10100c88080e0782c0c80a5540b80300d00081d4040000c0800100c0b68602c0000f0f80f011100031144201907080000c480360410140e40c2c00003203022041104503500c044486040c1e140648885103107003019008a110041d000345440e40012010b20b0005031365004102e102d003480c4128042c1d46003800d200c0840c602604189400e03a030345104502c0015090b09075482103d0040c011990411111031400900c440c0140c1c0c000d11020945542d1441842d07400442c400800030348262a060b5040240c0d0070040148403200682014041d4441d0b004010708c5182c00150311207a0b111154441500d85480c00009240150140c0d80000c89408400040ea032810000f84c045016410800310b00e59554038210306500700c1d0f82a10401c0c1f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 387380215 1250 387378965 387378967
    0xd110111150c0904090606060302030402010210090b010e0c0702090108060901141302150c030d06030c080109030e06180301021209120304050d18030f0507030501050109021e0d140108010b13060605 86
    0x980000407500007000c03611400344c40400e8504941c1c480c80100c031a50f51201000c660004100400c5680c1800b0040809004840802445005031900191244c050180b51360701c04070742c404035a80035078003410346021a0380103040d82d1a030368580c0c0d501038941c00e00740c480480ea0360804070b40c0148606501000c134490b2805032081001c5003019000c002d80340301e00301c9048149d644200b0201030403440a100500c281d8a41b41c4c004544146103140070f407800242c5502080550340b4142001c40007945c84880200e8488081300d09940701c0a03c6140036440d83c015444041e410340c40011188188140025181e219184110030f544440f107401c44888400d2000312802005034001c00522040e0600522000c082c02c83c441d25034210301a2650303945075216200c64002c0e074140e8005c52081040200901845015140e014429130800780c5070010025149410003004100c03882c0401c400344841000d60095009034005405041296520132903c2d0027803040806141c0940111040c034102e00100b80140b43c102c0b17100f0303513450b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 387381465 1250 387380215 387380221
    0xe0303070f11120c1c12230a0c030e0f0d0b0f0108070e070503130c0303020307120207080309040b0d06050f011a1204061812050408010f060803030c180d11011115 71
    0x2040c2e01e0031700c06681303124021030715486010403511150008208019252402880a88280a621581350f003d5003400741404022030342110350f00c080b11604c0e1551500f441008210070034000307140a09180031140d0440e41100d151424403940c45100f500946c034054445c032150740ca4041542c0c44a019008200011100c000424800c600c50401142d10038070480d907506d022491603540c88084541540242d005900200b1600c050142000800540306c69a000500c8054500b40745180c50b03000d8034017040c0c1700d1a5100540c4802d911916100400d81d548500c080203607181c80308010030010400e0041c0541710311100c50a01031008400d044412400c2549030454a81c1d94540d550000b803c03480114102c4915a41080350001d00c444401d528511810b0f1640c0d5152814401d00b00c0c21140040b1075440b00a060040400100c1e4001c821a03401c280c4419100e940ca0f12a010b580e41c4500c03c168080d5006805c200c16a814001a04908204803100342c1e07a403400150000440365883c00205800f500745103c0d6008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 387382715 1250 387381465 387381469
    0x30703180506041a12042f0901060f02030c03190f03020307080f070e030d030c0f09031208100b0d1505090402090609090c0a090b011e080105010f0e0303070f11120c 72
    0x1000c0760716060244164540300d028962107181c1e600c20750301201e070381f030414459559170b4845d00140d035029203030815892400c4005000260f120807040c07140794203000741c4100e4505203902c00d00c1242c5a805c10741c42203940d12100d040c1d48002000807a1083c80005800724100e4403010300c24021203009050940d04c000c0e29444072001540418000b40c048001e00c0301ca040040c0080e14107000d1150503450a0b100003030313007110040018181c00485100e0208002c0a00b0051000450b02504c04858600926145400303540b03142410314071810640103250086c02c003080d0710211006680000c4003241107076221a00340c1d41e0b103400707100a44800b620020f40c4050441d0006000d800e140442c030340d01008490031035a00040301c4c404602003804581000c03c143d03464002d00c410550b0050841c0c00c894000c2c0f43c503224440d6203040000e1141c1410700904d410007072a0030909800c60703c201b4203500c4c401ca006082d139958452500d06041d4070300d440002150300380240341e02412185400040e01045864402c0500220425041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 387383965 1250 387382715 387382739
    0x13170909071b1b03050d0309020909010b01080c0d0e0f060a061a0a0309150e070305010606051903050c0906040801051006050f09040b0d1e030206100f0501080603010e03030903070318050604 83
    0x1030350b0950220850b80c0000845d000f04421354110943c0d031800070300c80380c031801800680000108010740ca07a05059607065580d03801a07180303500a02810900d6120f400500f4200c3c05009d8401c8001c880d442599000443c2000c045000c1380925241c00c07040040e01c0e521509180700640c0100001c1c030400c0c0520415003402d01030b0f00401e1001d4840c01c40da1518403034031702c0003c040f6000740c0845c020325400140c0c00e104010003442008054600d40c00d08505144280780c0d01c07020028241c00903401c1644070404030741c001e010780003070360a01b00c00141559204d58940d00014000d200403500d4400e40300c0030b1031f00056607a008404441481d480358070301341d00e0500800d0600001c0e1640044031904500204650303000308000007200101c1e015403003181085160a41030091070710f6405080413545404180d01041440c01043e007540031102c083c00c22500940e100c500003030040c2043c00001784140400000c0100340ba0010000f81200b9100c0c2d20740c21843c1501d03420312920300c0c0c00344c040d0a0304400b04110510000c1e880c04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 387385215 1250 387383965 387383993
    0x3030c030609060b0705010e06040b04020d0f060515010e0a0509010618180204080601060512010e0606190f020d1103030606030603160801050609010902160b13170909071b 75
    0x10402050055032022410112050f5078881e960300540030850390308010084c095240703202e01c1c04000b00740303030305041e128040c608401400c002d20440105e0190f004001504101203030a94201400308503d10301504081502c0c00c0ca88081400503807070450480c03892511440700015214040c2c004071145e820244181c030804050102c00b84d030f804102500003050540f160f02084403200501001d61190b00c0c00c2011850610180c0195051110900200b2507901c100d040c400e044a0b00003000603981c0d154840071a0903445195140c1c040c0d44041c80000c080c1d60340100c1e00403c145d5081d42203401a10a1100c00c07505005070030740c9070341c40750010404038031a854418095504124010190362280c1911600085001e100f40e004d10826510341e8100402881c0c41921350f80108240e14040d0302d8103000c3c4841481c00900742c54020f020b00300b0540483e080403010520740100c1c41c0e115141d210501403100c6616465000030a441d031041c4d411100117100c0301d01c14400c56004054071040c02880d40d00b142e0710700300c00442c20 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 387386465 1250 387385215 387385217
    0x14070816030e060915010e0c070303090f02090a0b013509030c25090912030507030204090c0903060e030c070b0d140a090203011a0a050f0607080301080f0c0306040206040303030c 78
    0x2e09060700748000074400503000b0b00800c1c1c01484420783c20110914860b02c1648250b14040503a010090743e070700c14a045900c0300d58180b500140d00c280d10b181218152000210185d0003143d01402c2190f000c030325a0018000807000d03210b00001c642080d10078240301d248150291040c40680c0802c600f10180c2c1030441e0b400410036030075a41461030300c41301d0500c0c01241702034202034010b0a2400e00c00600b01d02c60384801901800b4000e201d10101a01c074100040c1003541c1103010103944500040001d840703581070754040c10400b1014070040c03404000c0288810131900003600c200d0f10f0b08440141c4803000104403500104405c01610441d8502410030000d13401c016102512962074002c40700000c030b0754040051207100d610f240003a0981c0140141400c445442e02d102014a21403044506a036660f0001e400c100c5004460000c0c442c0180d0780469142e018044008141d900701000101d041b40020800d800e01103a405d0896540345445010541c0e650000d80d0b01035001038042000344003103440380e00240c0c6d0100d03607 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 387387715 1250 387386465 387386471
    0x306020c030c010212010911030601052506060602010c021b0904080a110102040f150f050f0a0905040903080f0c0f070809010215090309100518010c02031c0309061407081603 76
    0x500c0c8802c0d42681d100d50b010501800f40701005000b43d110030300c030741204880c0441d01d644c01d51400c0c00000e405813050031001c1c4034903101000304104040b01010860001c55000c0c01c140300e81659007001038060013400c5030747d00141c0902c0b04400350410200455000c1c00000030501812a02c2e1902e17815456230140c4059001c0044100c6040000c3c0000d0009000608041c0e10325a01c0e10f141a5046040d040440021420004400000c4100075170240c10740d0204035580f007050741e4400f9240000e07106821141d000c05e40050500c9420300a1640140216115890b469041402503a4081da00305072031060030160070341443d06001c2e000208810741d01a05201e0018011911910b03c520342081413680104e520700ca0795400045e48800900b0203419200124005040860410359400045480c19884080315810001c2d10040903040d036030f0030019009010440c8000c2207034500c403242c0080190025400a482d914203210b050104c02e00c020151911540a5580742c60164031544852410403c0c1101e01c1c10405407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 387388965 1250 387387715 387387727
    0x1603030815034b060402040b09070807030b0a050409080a080705040b0d0213030506100510030903140d060f080c030712020f040e0708070e041b031208040c0902030c0d061a040306020c03 81
    0xc0140f004403280e401d88010441ca10302803040100351200400100d000c3c000e401c1c1840000303500001a5030f0004410b04011440400180c040345400049a00040d4058103041c080024450800300410b0b00030700310758810b00d05a4860748284c599110754412480300c004100280401c5a1441d4050031710340d068080c210b03034120303982e840b000e107020019101407151240c6680c2c100840d28101c0d0181c0f007102c8107400c00f4072840480d910083c1070404d80b0070840d502c41c003000552440901c4d480c1d000f40c029180d55035501102589a00f00b850741e840714110540d0103071068041c0418180b240c103a20000d2180d0040140e200c8010606c1480702408c041044c400507841000000325a24106101e1000680100d41c049100f500c2c1905059030140701c041c495440c01c148a01e01800410801000703440103103030a04001810742c42d80d10701070344019815400b0035200351002c0b00740f0034030210b400f000b009203c1181c8000c1c400300b03459005130700000450400030403c0040400c0200b0014455401505e4090080d00a03681092 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 387390215 1250 387388965 387389083
    0xd1418031204081615140a0b06120a0e03030f0906101401030c0905060301120201090e0108070b1809040b0402040e011e1e09030e1503090c060c160303081503 69
    0x3c09104001d4a0984601b03600d203020050405643d441560200140480050400420354620940850409030885000000c2128107180c103d00034808161044981c0c914001d00c00d098034500507541007000f4000d060110302c1010240c0c8150f019660101c24403003c4c1a0317064010740c020425002c1354818040208400500d540d900d00c0031318024102d12000302d10601861000402d0b0fa1840d07009240000c20f100300500c041080003900c80300f541d844141c1141d480100d035898626a0903c800f895501c402904108404c100900c06590300841c825241404240e080e40000b174240d510b401c4100386103911151015460002541002e4450032541160140860740364680034207941d0704c0c45e021707404954881071a00d518104040d030042c0c1510002c1c031309411820803001054880320160700941c071413400030407054041d00061080c1d0b5400e0003014451804542e072403401412000045402c00070744000d11107051004e041c0070800e900a00d0524011007450340c440c041c247c0420280034540125101005c0d000d00400c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 387391465 1250 387390215 387390233
    0x31903050a0c2402030a0c090e010509191e0c02030a020d050904060f090902030c1912060605120f0f010b03070e1023040507030b090406090302030d14180312040816 72
    0x74000803500540e803403806c110a6400e451840254808014002c1c00402400c9807180305a070540e441210f40d02156180c0182c10302c0c114000a01c405411403500c5407400151030b61031a02c145807092010240400d00544400b030743c03607004049003400540c10050800c40094403c90040c101800000c20009800303403100304080c1e09040b26048a11080d42d20150310007589810801043d0a4200f1141c0003c4180fa80019000e446010b100c3c41000c21402c40d400002c1101b940c00080c05400050445c07051050f05400c600c0da10030314441c01c0c9003d40244440c04e004ea06060241c0c8508a001800410415152078a40214803a004145c0c041d60004035502141041404815200326200114071071980701441e01000102c9901070140c00074103181905504403a220584c407980d0103038001d04001085d2600342800e80c207601c146100510814a84400d020450f0040c4030700074003410ba03802d00075281c0c809405080341d03a48a080d0b0819006101040024001038008006105080245d01c008082d42c07426a610004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 387392715 1250 387391465 387391523
    0x503073504050f031602280e04021f1d040b01171009092a1518030203010c030f051e04080304050703020d080a022506180f14031903050a0c 61
    0x240b00030008040a500d07080c0030310381d1451510301e03507400001e80c81c1926200000088c0708040c1210984030004055544140c00d9461005a03d420720324078500f2140c00400700c3c42d042d00f040310b00007407890b05400e00c2d0415100c1c1034039400040e1200100100c06010400d082840140700d0089102d031a0380114031172800e80211110503200b001c0c0c0b02000c030f401ca0f03007a0010900300046031207980c090f084100140c210500d43d4200d02d0343c580c101046a40054850541000c4040c0c00c040c0d05503007859104d1040940c1544160010301c00d0740020482074440d5040c4441030340032510fa5141c000081e00205010071503503001550454401c0040b60754041d80c0e6404a1180e0044800565a044003c14160030300d83e01404140503091192680000d50071502000d030303000e01200d026540401685e48000300042446642c1e00d8058003507110745444041c0c0d600790000d00e090b0390305002e60090041c0c8500020300100c072001031416941c0b680b521070404d140424200c580b80300d0b00c20203541c07480309052516520480062200a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 387393965 1250 387392715 387392737
    0xe0a0908130b03160201090f030e181009181208180a06050402090a0513030315180e0c0a0b041202060f030703090b180303011401020a120503073504050f03 68
    0x83c503450100041c000d00d04070039400c002564103095600300024a000c0c0b1140255505080040c802c01e90b40c40031400900c0030340400120350309030302c0c1801550005003060200b242d500c0034040c0072820300304051416074007002d100103280c00c0c08100c1041c55a806100c050f41c0c022305014103d0604400b0250030303464105c14181c01d884a40c1c0c0c0d5020700056062052106602142281041c040e40c03c0200f118120740781141b8002c2c00300b5603034602c55509100748c5c00d080401000303451080c00d8802004100c0100038103400c07078808194414207070a0b01c010305106501d0030440704d030b21729a2410702d441c1c000c188502c1c800320074040380d00c9001004168506440000a54051449560300064000561401f05c541c2c4602500649080000e44140b01c41d00400000b100e0541340d09902c854805c00350a0b0040c4d1402140340801010300060500b04d502c4107a0002c0914801c004e16507602d5508007500300d03440060049121041c0c0e030010303421001114003220524280e0014418001c5540c541d203d621050305541000748030304 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 387395215 1250 387393965 387393967
    0x2f0f0a060507081509070f1b03020f060a0b0604030602070507030602070b1006020304050607141504030c050105010501030b1e01140d090201090510081b090303210901060e0a0908130b 80
    0x10650f80072112650000301d024140241c0c1140c1000210300361401482c400c10041c8002184066903c200c8095002a000400303100c40900c60303150294071646510801c4140e4442c0c540001d8103072515001e168558140a41424a0141903071030b400043e50009000b9203492003596800000140d00e48014640113018044101840c1001520701a004910354000e00455100340000c0c09507030b68580c00c0364105541b00703502018070103100c4401814800100c04113180d00801c0f500700001e05421030004603131240300e04002c204607030b20380c4019000c44d07503801840f0b03400802c1c80c10b1681c00f002c10140341c090164414103010551501c2e05828890b6580862141c41150f5207a07600c40c8115600040040041e09048070130b01300c01d000310311005203007080041030024140181d9400758100b0248004580040501a0559546074030410740e5060000e0006004407038442e2800c0000c59100b418030809040d501c0302c200d0481c540c0c40300000e01c8081c064001050722a42010403d1040003004800480c0050a0000140e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 387396465 1250 387395215 387395221
    0x1e050607120c0e1c020f03010906020909070c110d081c0b0406090501240915020105010e09060415020903030d0906060501030b1929030901050402030d2f0f0a0605 71
    0x2180940350034a1100040c020440361400080e6110b141c1c4201007044e2038403859080180780005520114003291641c0c16500c0c00729000103000c201e80040170032031401ea40d42403080d220010100e031030170040d44003d4030300b0032072031440505490a03c00010b40340b4001e05545040448007615200e200e0030000441b0f003819034075505250141090b02072000200800d810070042c561604140c015005035001070b882801150041042519008108580152025aa42608418603d41c01a008120078090a01c10702e03000c40001e0740f10840000c80b248100d030700c5218004105000d501c08006500b000f011141d043c0070500c00a0600311007441000460750240030086001c0e0301c0c007000034085440850031280502003402007940d204c50041091022602d6540c040340b8021040d41c0d8070820503a0020b1802e4800c80c0c0001071007a041c405400440c080c5000700d05403551595840029288039100095000c500c12415038035058400b0364244445000300d24000761029000e840b0909810500b00c40d070120ba1840e598018 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 387397715 1250 387396465 387396497
    0x7030b0907021e15190908070b100509040807021e060c071403030702010203180301020708070501092d03030b0d08040b1801030c08011511030a0e0f060a09031e050607 73
    0x1c0e00e00302c2d43e010001e4400d1050329024120441c6000300540404041003512072404031080d80b041c1c407441c0c4c0001c0703650f4a80403145402c201416007910300c002020360a48002c034036480d1901c42c0030301807079120700b450340b400905a00f4010386000010f001c4004881c175000b0410551500c038018150b10205402520078203052071140c070440240b12082e54040d44c410b011260060340c00000b00c0784a080d4080c0ca807408164442c0001c0d000e842000c07401012904040788100801405420010b880c1d413280001d43e10b0207071094151010101c0420784840c1c0c040214a0032000710340030341d01c00c140c180006090301a0004090f111a80c103075110350300c4645d401c2000206d0300741e01100c400c02c55851143c01d180c10301409480c40001050030206004048051a084c10740c404103500400035404005088030940f62116031032000640340c8180d8040c2d5902600c441b00c091003080c9450011140040c00507242da4490500b15103e800e0382e180541c1c004080385030324510917404100c0401c0f0580c414285981c4076091242c503920 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 387398965 1250 387397715 387397753
    0x20a030e010605151c0204030303020a080a0b01050306040f02041502071a03010e040303050c0d240e0432060a0518031305130902060c01020403060e060c09060307030b090702 76
    0x118800d110791500609210b43c2c0e442e000843c00f0400da18100c19250000151040342d00110984800302103132002500008040c1c03da00907013080c200b00d8035900c0455482c402d000069500341a1101d002640400004c0c20a14180d07000c92032000074180c005051a40f1800c80c9d004a00b40d41ca05400942c0c0714000c00c02c050030724241c1c10540f10b11412031403421945000d640c00c4000c0000b43c40101410740754400250385010070801d454800720442c2051019100300001f801903094121111102e035110340802003100399011070320600650744400c1c03958005894a82010000d00c2c1c3c01c000c0f645180326010401d95034402000f50300d029981002c0c00045c6410300c1044c0c9060044101c2c40072903160801e008211492040842e05401c07a03000380c400000101d41907021500810714100000c0d0700010108480b203010340154094400c5e40d07c50502000010880c207182130361070f00202c1d000300820f01c0400030808941000d030051a00100715040120341c107103200d400140700d980c00315074550044e44605138401180031118 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 387400215 1250 387398965 387398981
    0xa0f060b2805070b040201031a0d14010c05040305100203060303090603011e050904020102060402120c030111040806060402070215090a15030f1b0c08030c0408060906010839130e01020a03 82
    0x418143d01d056000d5464520001c8028800380c1415a151401c078201254030304091315000c00180951280422881e201821014054a03100c06610384442c3c030003403c1c003820448003a00d4001d0014103050304585191400b9500003492641c06001c01e000c0310480d40c0f114009140640340c02d003641130002100c02d01e450008011588403d2140310404180400750340c000c90410342258041d25120000401c40340401d1402d1245402c2d69059881e02080141d0921174502070025200368509446003501d03014100b005a010300407020b94031042c61981d904441d003041000308008240607004502160b91507082e030402403c20201c2202094031a440c204000169204071481c0c2d8200c510b00c402c400f0f94000d001000b20b030800740001e00102000000c100300018200030740e4001d108a0b000c9421078a0400c11054a400080c401e1030b82620070719003070040320000100c050941c1411a80c601200810303051071907076086500031030585c000300103508003011078045016981c4403c106070b001503919085090002c0440c3c20314 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 387401465 1250 387400215 387400217
    0x140c0c010e0c010e100309050f1525050c070807030803150d0b13030203091f0207150e0108180105042009060f0d031b0309030605011d0a0f060b28 64
    0x41802800580e0441404c1e402600e061303c56051021011905500a02c01c504000c0c042d481200a5170042c20000141c041c0b0702881d440b59940651a9504181c0300c1c10460a01000540c101403d000c0c102d40c8640080d1101c0501007088504141e5251211414171044d900700341c0315039900108000142c0a5480c8001504500b0703503031020312101c0c80d2950140b80501810031850040070046c28004e16100308240c41e0725000040201003071001078014010401d155110300000b42c0106200000c91000185460040c41e1058a55601c1003000500448140d8002441b00201b071030300170114000b00301d0074400c15210314891411031608034041103540d6007da810200300740c49500c186d4100a600e4464440503c0c40c0c410503500c0319121500b525007904c0c01d80c0500d0303006400600e440100c0d400e02d40d00c00f0900b02200e00660381001280d0f201d210780302c1001080f03140401c0800100002c6a550046030380151512024114006007032611415030586940c030008214110300c0b47c00c5101e0300020783da1085904900e0301 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 387402715 1250 387401465 387401473
    0x311010c0309030b0a020d0f0b010906050a0507061805030d0b090a060303091802070506090304090506040605030618070f0e01050a1508040308060d02060a0c15060602030f0d140c0c010e 81
    0x59a5002090b480c41c9000050022a6003c0841c0c442021a0155a0f01401c510300501034050462000d84c0180840305166000134400c0d0000034403603020390121f4941c0c03151696a01d00d001e1362902ca84014041551148032303903268042c01e00020541c2800036100c1388000920100c3c00351100400c100110382c000e0200060686000c070104002504500c0340800c5608841415048a0342c03039200600901130343c100a0032a000d0082004040c101c04001002030b20b08562080000303484000078001250454000c0540561111b4003203250390316200c41e255507454119048841150f1912080309400e26a82d201c01c0619a207400103121500d4000c2c0800050940300e10180c1d0043c1f810803004041140c098405028080c641010a4a0342c0364400b1035240070f50054103955130f4103120039000700a5901d0417002e43e0a40e8024408062a000b41e000e00411904a9030042d400c08019004024180c0d01035240459499039505014030000c0c110548103100f084c41001103a02c1c0c11300046a5421348009000d030140340c0d00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 387403965 1250 387402715 387402737
    0x90a0f05011718031201030c0b03460b03210405010804140a080301170d0206070e0103020c06010b120a150603020702190e060f010201060b0706050403020a0f0804031101 74
    0x6032100302100d41e00d03024020b4258586501c8482089807101900044550100103254006013294040041c102c920600340c00f50116519208003145001c02e0300c00945c00550410080c40714040101c0540804c2e603500c050f1604a87c0e0860624107821f0007100354080d0076140d09410074940303020b00c002180e44103106015018030084590000992049002e124140485103001c50240146424040340384401903048a199950b90700702220590001d22130101c461222040c00208840007103007440104000d6001440e06440b000f406841c542e00480e00b03141010f40c240b10302c69004104020322402400300404c0e00385d403242e0b001c00c0071094141c02841d5445103400e002c1500102c030850b146403000c4580501d0010b071074103240c4c030000c0c13540c4004090404d10003c0721039000c40c0d20098051801c3c011041111074040c00d80c000d8005900769002c522400c1c4a2041c203014020100d02d1582103541c2c0b042c46403050300c80700e0080755240d072840b60500409856071140440e0a00070050402240c1903001000d08110308081 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 387405215 1250 387403965 387403967
    0x3030903030a090312020a0306092301050402030a02251b14100908060901050121050c0609150307171b031612020a030b03150f040803040213090305090a0f0501 70
    0xc4005882e0355511555503aa100a041c460201800382910750b200035036980e6259400100034001c01d004140341c00b4a00800301c1c0160360030340c1030407415030500070f064081c0d82c1c41c0404000003500010031800300c00d6020055040303c6d60182e24042000b40e6580c2030b002d000030319070a08014003e148489486e048500d80f0040c4001c014075034046422560886100c2c9442600a1084400d0143e0341d00c140a42d20951081c843c0c01e000640105050362020100381002c0c0aa90030108086580c1d510080c144e07030040081542a404c002c001003000b103001412144007201c0084000034aa80115940c2d80028400049800c3d091281d90550b50400b0b40c1e500e80110107000141c0e00d0a01c1d1101400d14001030f442100070a40311070065400d4001e90660350011512081071210250140c103180700020f101e40200b4122401c0000003165890090100c0300200c8140c0d5615521000c00303520242c020ba034050071210341c042060001d4000c01809600ca540c1c0c1c10f849a50074001d004001d4903a4102c0c002000c00201c0a100b1a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 387406465 1250 387405215 387405217
    0x611120a0b1c03081b03150105070602071b090e030415030b040e01050907050901080105010605071707021519090b160c0302030601330c0201080916080c030c010203030903 75
    0x220303000001800301d1034000000c00700c40300350b02d076070a03007a907281e111506240c1c00030b0000340301d0000e00400c101d100e005004036065511049a440c800702d003d40a424a00b03510039000b50200300e104800041c90b102ca60303240c41164003980681521105800300c414003208105002d1807030b000e110032000350f00b4282403001084407044541c802a040554804900072150358540144640d040c803c0d008100d2803c202090319204c0155008241c01010000e000207545001441014100c460942c0c0307203800c060156445016105c0200710061240b04148100f43c05662810b41480b0318130003801140781c0d41c400e40c1c0c0c116038400c0006022441440100c02007040070400f0203085900c0303501001030310700c1201410300e0500602200d42d00043c0d0103104030310001c80c2124815004030201290340c100c000c0407007503c41910307044035144618000090700481c4904010b502505540e5003000c9880184d480c1d104000c140e08500014a60004c0b4199204040400305814140700030740900c14207101441c42c503d0120003140d81c0b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 387407715 1250 387406465 387406471
    0x309173103110114090a06021c050306032524120b10050f040b030412020106050a0f060804080d0507020d030e032704021c0509070b09091906150c061112 67
    0x5001d034001c504c54003403045038212008110001e04070000240c44120083d91038450000c02030400d80c0c6502c0001c01540100c040e41d200d840010001c0c01841527040c00c1114900361602d034000c1c007800c81e0901103804e6042c00c0100c1084802c001c2e114220031a1220b0084c1001c0702121140001441d08020751683d07180c80c070090307000c0905ca0801c3c99a03800c518040020512030b070341c0b14204841c0040140000c0001c48140c0c403d003202c60754002e0201d10f40343d00800185011520402c00161410341007007248901494915034460f0058a00c41c0c00d14048980c2030050300e9080f102280140c1100841c3d5081a42500c1003200402c085002981080ca201e447d07018500b0305812005001c45000302144084e5a13240c044541c02070313000c99a034610024910b0b094015080544100e0300c54000d104002c128940940160342c210312000781704c502c80b501c64162003070040c2e04101520b1000380c0c4480c00400d80c0e05194400c4452402c00756240ca69075141401c0030750486100303404401c0c0c0250100000a10503103950301141d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 387408965 1250 387407715 387407717
    0x8090706050720030c030703060f11130e190c0e210706110102040f180c020a0f060b01020c0303040b040e090105042121020a081305070603091731031101 67
    0x4001c101e0f080003e8904180c01680c160300d40304043c404010000b240c0c01c4a035070240304480a00441403a16200381090081d0040ca000100b81e000040180c21342ca00b07042908400e040e00070980b00303038101c0c000f10306840d1007102a04c0481d00c580e10021850604040006003204070032012411814484111611000c0c44e2090303600304100c9405031116041c082d411540101040740e03d080d00c981d95a40d8942d810800310710b0640384246808030705001140089401c8030080d900034000315080b2099507840d8010001d4030a0305045110b02060310a503902c00f0401400908050781c440c607200c92604075070119900b0000c04c21916039041400788400940c0750078103600140f0b5801158072080f80030090498080d00c1c20400802d02c80504030418411808550080801121507074900060759562000d03940c40080010005059600c18002004033340e100740d000001030b41c8580940724400303846062802064101c0034001010066200d07220712425009440907003d51040766a81c80204c0c955250f0b0704c040c80700416403074 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 387410071 1106 387408965 387409013
    0x5011e09051002120105010c0819020616020c090f19110702040e15011a0714030310060c03091e1502010f1a0d02040f110703080907060507 61
    0x9202034403840040d1384280d00e8403004640c501c90300d4100b56104c4000b40520000c001c00e4000b09400e01055500901d00c82c1402c00080104040381c21441c82954050b00030b0b412580c480c00d1100d0351001c078090403081e141d50f4080000c4101c21480c50381c151076516003072186140300c5844020300b015500913a41041128845032203107540e0081d650090040c0c8a85d500100118400844420402c00245c1ca1072818080c440d5244080c26503510400c1303850350008801c00c0030552510003104001c0600749800b00c08103010381c070003610551407402041c2c1c29100c0080c1441c410035491100f58020980400140c240061400d4002d0080184180051156040850200d401d0026601c8804161401001d00c0d61581a41d801c000041200c0b00d4010740941d215910a0000c0072030f94080c01c000303070080d180c80116290a4140c1e0342014150b40007001404030a101d4107000c200c10320345103104450141c4201c = true := by decide +kernel

theorem cover : BRFrame.Cov 387230215 387410071 := by
  have h0 := BRFrame.cov_init 387230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 387230215 ≤ n) (h2 : n < 387410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
