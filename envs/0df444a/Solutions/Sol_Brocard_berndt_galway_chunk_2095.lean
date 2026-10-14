-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2095
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:38:19.650476+00:00
-- url     : https://prove2.me/submissions/d03b3dda-d10f-4a8c-b659-c57ae0e76ee6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 376618705 ≤ n < 376798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 376619955 1250 376618705 376618709
    0x1b0608130501140403080114061c0905151003020411120a0c11060c0c01050106210b0f1f0806030c0d06020a0c35090603041101020316051024060c020a 66
    0x5407142c03c0b8100810b0550203030505040310340c004a203802d217000440034040540314018240710201d646444010140341c1e180e11026019000f10141e501180c2c42c010319041a05042c1d42040c2c03032001c0e0610500540c6064410859081c078107004141c50300c10100f6117030b8182c0d00018680c484c0556942c90445065000e0400c0340640c09000b000c1d59002c1c0307044560304004d03070054040c2000039841c02c800450000c4c010005402400c0c40306054002000c80140000c000d05002c4580da40c00c00c4c14040351800d00e407202000300d00000070000c1d0080720b42001c160001d00c500d0300100074921a90000c18864000c3d202d680e1200203003504441d001d6a07070815440c0c00c0e12035458401c00148004134200c04900192202841d002611842002e503010944500c8102e00003805803040140d4440e10400202d00010b55000d400710050b441801aa03081c00703ca02c20705a00c04041120603111034104420100360390300b042c400c2180b040b076892070a00b081e03046203500c03044a9069028900620560100c00e9003075554124030200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 376621205 1250 376619955 376619981
    0x110c010c08041809110a05030601032a081506040501050f13110304050f070e0c03130501060b1803070803040f030b1504020a030902010201150b0313170d0501031b0608130501 76
    0x40307243c03007101e4010440c44205458880c004c03030403030b400c9180400d02c15045500c000c2c01071080b80d0958032404030b010900101d03656103a0300c0c1c1c1034800184240c014107100420b4840040c001c003a00d8070b80c0c40341c4d94030b0008000c140300754a00703c0140b016030350380d0700609424001030f2500d0300a840b42070040401044030070703681c4190100110410003008000103501329031507500000d8540c0a41c5e10000e40a914400765100c00641d2014800100000d224155003120140034100101c1c800c0c0c3d44140e0840301ea4040e4100d1080e602c4003400510710784c10300b000308900500e50300008510781840c1200d03203403440266000062451549101103402c001101400130340c50480100110b548100c00d0b4405002494440003c03805542806c0640c910740408280d564100d440000840d07185036101c2c07201c1d59800d00d42080032200a5103030751a04265000c07060142a001a099200240135411420440761020344070301d039800154508032092042c0c40c0d006c10203d8116401c081002108600d07032618034050540290402 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 376622455 1250 376621205 376621229
    0x12070804030c080c0126150402070f06020d06240c24020304120c02150307030f020309071d040c050913120f080a020c031e0c0604110907110c010c0804 66
    0x21034900000b00e55900e51390380076214082c0904030522111454905804a00d52003520000040d120a030b480c0c2e0380344000c41c0c3c014001407a2200303581d1945466000d000055030820703130101f013403078000e4503074400e190240c40341c00d4846180c5c00d01c100922a40c1c000c042028010400314034106010019031608041d000f40307185030101c01c00c140380300b0160001d41084170151107201040110504070390241c101e10324050f4003c0c094032101d00030a0800d00703660f40040e02e014200b503910130f1591512126440618081e000c200091705d006860412046010343c030781031405014507807140034000010250100c0d4012500183d603091215610310601a20181903a27001078030101d04509102c242c50303840162110100210b84460000351a000e007060100d01a483c8200f05990080050b001c4d41d10000400e8071403070000c02012443c0441c404d80e250f04040c000d803001c803070b4a05144c41078162491300d40f10060384012586807603840c030140032140c580e807030900b0702c1c070141440a01139121083c03010040031900a0328900303600f0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 376623705 1250 376622455 376622459
    0x60b041e0506030c0d050303060d050f0a030512060405060d11060708120a060803131e051504030b13080412140607090e0108012f04080a060603020f100212070804030c 73
    0x90300c080c00085030541e11038041d00c04168440c3c03500320050b81d4100d4019000750709503900c810503c0050380c481c8805030b41502c6201e9150f10703120b00401803101403e00c603544498403a85d1603c2c44c2d000b115006441c0038420f5051100300422911440c200360030f000d40100c00817012540c280080b41ea070f0700c40c40c41d0150018500041d205403c6d005100c600d4013807400b0342402c21149950714a520788034000c00303103260010f842d8084204910a00c446460303a81c2c102d682e5000b0045569440081c401040d400c00c2680003402c041020018403040207900c035880100402c1030449802550f07100086446140100000b5840140078007081c496040d51000c00500080d04440340c9082905000d02400380900c81c034041c108402002145a60040c0a58078070400340700482c44051800c6a40e0b10070140141c000440c0031441807100040c1001c040000070111805074400140356401c42c01841002c003010072001c1d000b110a400d080d00000d42c00180034410302010002c40d900d405003071500d0980d5114680c0003504503c00300c580 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 376624955 1250 376623705 376623761
    0xa0e03011103150904031209170706091202010c02070303050c01020d05011e140d030809120a1d01052b0605040906020c010c1713020109030b090a0c050102070e04060b04 74
    0x190b0240c80d80c1c10605a0100304002040800242118000c00042d000c8003d41c542da050b64112804052103445010707032781c180000d10341090b900564400d4030701d59141e89180050010180a4003841005031000f4442050060300c040e42d68145484020200040002e404c85002c07001e40c1519104180700c2c505000ba075940e280c00e10750229100c008049a1401540000f8000112862440ea02400904101ca81900d680c409589130480241090020b0186031a180d280c076051200401001600e6200c152015100c1c01c00c2d5556034070003550320303818004d040045608a250100342c10000070f40c0c00c040381110701c40c2071f2802405012568821a000b40c1005054420070400d50041c01c10b0001d02c100812000c4032005007203654820907546044280d54040200c1c060000d2210003540300b03030043c1004401d1903545d82d241c1002e03000c122401c101ca900000140c40400001d003520300c008020910081496a0400d50018880400a0001080142c0d12428107400340c50b190003110520b82000151821300341c42c503103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 376626205 1250 376624955 376624957
    0xa0b1815100909150c09061b02010e091e2805480f04120218070314160219060e07061805100806010c030903020312090427080a0e030111 60
    0x544e500060900d95600d003124401c082410882e0b03915a9040d503810780c0c0d07030b0003500d0704020b0000a03030401242d4220300141d500c654883d5409110828240c0c4d130741c510800801a00c0940c090300f00e012000340c0c840ca808852517403018080c0c2c030300b80c49880010241c6035001d4040c2c0b00c0c4500035151442c1102d1068000e40c0b410210035442e1518a01d46e5212004070003051100360354881c42852884002d400d10052000030100a0491242e0348090043c010340c1001f44100c800003c6c007158480002920380700000200c0ca80041c0c1c0b5604160b14020805842c04c5101002e5291305905c0c2560011000c00a02182070021940000607600110360170307518156112036000740141e01241b1021410240c8450014076400d02074401103000000c2c0e9101200c2d03484800045684c0490800282c08106140300003202680d002e10200060042085405076aa0f081100344420384408106051a030340700d90b16886483c2c4048101201025880130006681e03d00b00c00e003d0b84e4a805408840790190b01e40140c840741950760310 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 376627455 1250 376626205 376626233
    0x901090f080f0f010c2a1a090f010c020d0c030203090607080306100203040e070c1104060e0a0e030c0a0206070c08031603030f0510140a05120a0b1815100909 69
    0x4000d41c1c0002440400013402c0e0741300c0002c1480020712880b40c0e0755084071007207051680509980884054a503854403802d104054418000b01807518010901c900910b04000c10380302001e00f80000d0003103034070744200030352187c880c0503030441070245040e11f110425100344126851380034001e10b101d8030b4a5240c1030001c555042142d2240c09002c009141d410400c0c0000156804c0324000059440703036544001c81141e0b07406a00303c1c00c80c0c02004082540c401036030343c0d008101c05400301c8103820125250003590a02540d041c01d8200342d0359042000001156800450300c0e02044d9019076405503a0502403500504514103030340400001d00000c60301441c00c001072001104d18900a80c1c0a02255800718443c1b81250740c00d0b6502084101042010000034050310101c1600301002030690b002e4550310004180c07882200701c603040e020707041704035400d0411440b41e540d242c102424004401c0700400c406541550342d017044012140200c84580025400103984644502800d10032105000c032000354031b00140200144 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 376628705 1250 376627455 376627483
    0x7050913050403030b152a0109140c0105071a0903070804030302010902010f17161202040603050f090f100207060f091b140d081c0c0909050a0209060a050901090f08 72
    0x100b8800c04031881c203070100400082c0e001d0030309842c00e4940c3d0f0104021f0000329a031140055010035100029980c08c0c480c00000d14003448131001010224004d050400342c01440090510800b4000000420400000ea4030b120b0100c0700c0b04030071502c40c8880d461440c0640d0600400b007130b1000801000301581900802200d034803e80b00c1900c0100080001d982c10101610b50240541560001402d0308248000c85001070509007480341c3d50650316901c6400741d91103034111002180d103e80a20100c0b10117040103691010f00b44014001c100d00745c04850b9140c084c445000d410254010444000b44001079101e00795484491800300704401c0c3e90300d0320f103560f010030901190380c0012440000a0b40c00780c080d0b4500810134000c040b0060161743c7da40d43c03a10364201c0c40005050560242016060728103911440811234120f40390a1491864910034105a5000500620201e40180a1403100341c99410a407031124100781031564072001050300495940075281d000c0b150f44144031400090410780410504405801 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 376629955 1250 376628705 376628711
    0xd080402210f010b012d14040611060c130308030c04080601091406040902011b240203250c0206071a040b061801030c05010c080c030c03270f090705091305040303 71
    0x15202c01590100c0f0b40140903031162003110400e0100c804040382143c81c643c45403c00c247d10000c0c01403e4025a0020b400800c00710303004030b0503041e40345002c000d00360303020740200350705450100700d0079000143d2003a910009003856000300c08144885881010344000d0200c04c801c9441941c0e5401d25079002d80f40c1e03030b104034810400140108400d4106400340400d030a4068590040c40b4030078000d502a40141280c05848134200c024200441c5517980b2a5400303d107080c0e43d00962a803d0500505e2100b00ca140c0c10f08082c0824501d007198019000400c199a03140c040300d089484a00a04103030501c1d070744098203440070350f80d00d00c00c1000308030111100324094070040e50840c140b6030808043d90702c2c0620a00000e0200c200c4035400704050740c0b00e034110003044c9104070121824020b00c86411480c40c2c0041503081c9541e000441c82040d100c940310450132a01c081d40c020603c203100c1e040c000c200341035400c4009501940c040300024401501510440741d4449000d0141501d8445180c8900700911b001e68080300043c2c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 376631205 1250 376629955 376629971
    0x1b0f19030c171003080c0c06030412080f0906011e0308072402120123031501090c0e010e450c070506070f0201060f09090303050a0606020d080402210f01 67
    0x140e8150218843c0040708020440c103402d64440d0f80b142d4000d080c80807a503110f944088070050320380390003850040b07100d08100709104191078005049160300414548141e00c84804110404c140006c43d83d04480741c4000f290380c400310a24000740800040c0c0c0007c0c0c40520001000c508000c10014010660313450802011741921490780c115080c6d118502c070355141454060700611000d03840030a4140c03400f460401203504aa48240801d0500352401c41c88603400749484d0040200070703d24025401e030780c40d05182c58200d41c0400c1c000a0300c10741c0c000402ca80500d407140500401c0038045410502039207032440d6a282c02201c21500d022003c443c600c0d0b841c1003240b0380408600c48050050544194680c84009810710b50b480c030070112407020030b9580540840d0340b19000020034215200218002d80740c88a800308902c01039003001360035038001902420181d031078181d081003015800f0840344652405464410001e03107490002814425030f0340c2d10940b565000b0342e24003c00840016185103160603210003409680 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 376632455 1250 376631205 376631237
    0x20a030b0628140409020a030b0a140417030414060c07060b090103030801030b090a0606062c01081812130602070e0403120905010f0c05090301060b031b0f19030c 71
    0x81c403040b6440d2002d0035402c10700035a8188040704404140207800011001041d800003000c0e20b2156000f0b4519100c200107010300d0394218090903401401c118900403890070555108143c1d500e44018200c0d400c0804000300b02000070482d880c25811002f40121003507800c280c922342000d0381c00843d040300c500340361800c896aa4204080311904994043c0c070355281e039a1039510b642c101c24500a24000c2c01d0b020b0701e40220001003080c4142005450f403641d480003241040c152244500640d62481101e1240440a46400303030b038010601030f480300409480d40501c0d8086121103190a803407071030f030340e4140a01042d490a0400018888000c07a04503030708031440e0769600d00d40301e06641811794010b000600a120480f1880c4080c2c1c02402d4124410360000485e01c3c00903815208403500c612030000000c3c000581001186402d014000190095204244c45c60134040040c400c11000c40c080c403c4075100c04599100302d0402c00050380c101d00038040c6600001901c19500074001d16000c0f00100101f510710004800c48 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 376633705 1250 376632455 376632499
    0x105010f080705090f0a052503090303050a020c0a060b06120c120c0406050a0309030c05030a0c050c0f06090d0c05090a0e010507031e050901111605071e140d020a030b06 74
    0x14803d1021400140e0306e400040c440a13250003001a510382c00044100c0d4402ca1902c80e114505480c5a50002015071041c0750081c250303034001c2c21004c1114010f00046541c01c1c40880e41d100301d9680b1120008003281203101241d520b00800034480103d81c000001c012400342440000d00f11040556030800740c42ea0380b080440b50302e010398018407000800074401091264043e0f40107611060080c00c1081645145039a844d00d1075010140d00c10019a4840390602007010801c0b500403003e0084a04c00030325507502021802500405031b1252146054880020030302008640382005000c010384a05070501e044181c3c40c0c0586600380126150b03610b84400108814481d110312401150341c0c0201c62041811042c02070007500d0f02a014143c19542e840d050383c0500c2001c80181031220b00350034007105021140c24a02e080030069400701d52584603407450400c5e140c034004c4004082d02c000f482098100f2800c2c4c40442d41c80290008025008640c02c4400720511808004041c8034100440304844200c0b1400103003502 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 376634955 1250 376633705 376633711
    0x30103060f0c170c1306021e0705010507080d0b030d0503100e0c040902130906060306050a090504030e1002030d0213030203060907030b0a0c020c04090809090c090607061d0105010f08070509 83
    0x2030403840f40c4000301c140c1d9888107400800800c6000c0c1081c0701c001100e0360035004c51b48004056403142e20760007280410382481c807503003e11f4140542403280c5010000b810620940c0c200030301d540b10004804401118a0b849400d10b41e1010b400c03074504840c02c600280840c1e00988081c21171440011000a5080c00310704014400c90480d80f0f15410035107001c0c140708c080e400100c1c0d440c404c1e13a90202d001c03030340507150302c1013000400d882e550110b81c403440c2c04140500c8084071703004090494104401c0001180d001055000350070f80c140c56201d00d2062100e002c074214080c0d0f00c4242801800094020300030301c8142c4a00d82a00d00842c1500d10760789441030000e6594885100003001c4120070000508504110b602c0841312181500644003100e10010001d03040700e1500c03070f08848440d000701d91440c450030801d00b850f0b802081c4a8800e450012050001001400b4110009003144d481d11144103510a00c080500c020801d118000c0c07041d940c4800644010400d45d0058021034400d1140014141c80e1514103540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 376636205 1250 376634955 376634957
    0x91a090303070e01030f09050a12110c090402010c02060f0a081e07080a0507020a0f0b01080c060a17220f05010c02010b06071101020f03041401200c04050a110a05030103060f0c 77
    0x602103d0280c015400b400d100841c0b8002640d881d082d44c40410400d1022a907418810080801c0701c90399a14060319081100340d00091541c4040703481002a00c507004110307005038090811000c4800c2030310006991f4410410841c06070580415444185600003200710302545441d281020380b0300344059180c0145204075028000034400070049641144c1d55402940c0000382d40c0305440050100d171b00d4401070407048030402c0300d8200101d0010054407109114801c0300c1c40d0100c480710300c0c100d5141401412071700b8480c00a280011404040f803c05d4200800d610300300c1444107079091664242d03060861481445036400d4449500340010100010b1041c030450410045c010710140c00c11005884010402020080160540c030903850145051041007000d4401844081525030100f89840700040542d050342905c00551101a0064010481c01080d00d054014094900085640c0c8000c03151024004800468054660000e009401194440002c40c181e82c0203110901044503650102d10440b220300803035134 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 376637455 1250 376636205 376636217
    0x34050402090d02010e06090a0b0315090108030a120615030212070305011a31080705030c010503070f030b1c060b090903030609090a02040507091401030908040510030609091a09030307 80
    0x2c01907000742c0c0000c08010340a000a030505048001240156602e904030020700c0601000700074010003503070900ca0543e41c06841d88031142d450401c0c0c10b80d5a026010000041c40b40c0b0398415248001c550384030f0b000078800550709585400d0b003003001134000d6024480c403403510407040001034501806805494122200d929413031044403824907104040c2d411481d204507250030200107500c0c640c201c141d200d6200c0322000141c468110300e01860640303400d0543d4842406074010540c2c103291603030000243c0f5400380c0681401840d903440700500320000c4c00d4092805034007902440e0046d045090700c6030141121441810304020b40c1c040e40f003c001070300008844120890f48104001400c604002c44c40e1030300012a9012188840c2507640094143c400407101d08000910440c1d0070410941030640305038003080c007824104180442a100d0344030350701c2140651401182980310310182c81d40700b544003030024a81d00d0010400381800c2d00d840c542c151000c81081c212034242d4000718401c48400b004484c09070300c05407160 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 376638705 1250 376637455 376637479
    0x3050f0c1231090e010605031510090507020d1b0b040305030a0c02030403021f17041109160e09130204110a021615031a03060403020715090e0f04053405040209 70
    0x28002901c4403011510255486003000074070340d01d04000c00c1c9c50409407030341000454641001100070021440e8003003c0d18034140418031103400c2c8c010803c09103c202918182c00d007055007001e440e0f0031400034880100038003144410001496480005540644702d115428407803d030008070100e035a40224003010754802e20030109440c00a1828151800c0031720749007403450032200f40c81c101d0f080d401401c035805d03140031480e00d5140001d481c0031102503502c001113080010411040d800001c000406564655015024040210342d601140d0134110040650051090140821004d00e044a0303405c1803600801510900380c6802e454000d8420203000e4410038050780b41103148098080700075003c1901054009107107007500704020340341400a20301c42e038040e4000b8410341d0b160810b203160002c00e1060720802c10480030014004410b050b40c16542107040d11420386010744403814014105032105045112601c01c0d1500c002c03a0300d6401e5003003d115241e10800324215a65582840140d1140c2600c680d07108015001d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 376639955 1250 376638705 376638719
    0x711180f060d05070513060806040501020c01061d06040506012001060317090105031b04030609050a0c0b031e041b0e0106020f03030403090b1617070605011d0403050f0c1231 76
    0x41b010024150b00030103d0116600c08840741000c000b9503042d42c050350001140015401c0c02d00900c0001c0541c2004c6480c003483c010906403805001801e8248503c0e258401f09415a10502400388107080064100c07c2c240951260240200014070040381e07101e20074540c01c20070711410029100c1144040c0c640314656940d00600c2c40401c044072590001103d000d003c0030021800d50b102e0340c02e03641d10500003002c03260b14608210f04040360f10b50007d4402f1004004211079040c0e03026025a40c50b04408814000703407514503001c403280843c0d107100078012111540019040300d2214446d4100c440c15003c0d620750002e82003003146c480c402258060302041c1a8030b010000b0741c81e8800140070300c0031080103110100f40c40d5922250104580e8074040080e00011400701e00b40406442020700508001102000700d00c5180d640c0180707400002c101034180300b0f02149000703076003213407408444044a015003918135140e28140c1c2c070152a0015441031004c001003848032001d83c800b501545c103404146424a0708020303d031940c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 376641205 1250 376639955 376639969
    0x13020c030f0a09030506040b0a0b0a0819020315090624030c0d0503071203021e0705070e0415050103051c03020307230c1c03141603020711180f060d050705 68
    0x840c00c2e003042450180040481c4003444a10b008500c03911085038181040101d0000761070f040301040703114840242042208a40002d440e50909000f4076900c5e440e20f800340001307410038900141c074078100b5003140100b05502c10041080e41c440c0313014420343c0717082e080b5200d22000007404c0e0030788cc036415030700210300c400c406d28002115002c41c920510807a0712303120031980c90b0203000c0181c00044e00842d8000c00c110712801003200c0d2181c0c0c5003601503d45401d1000c04e840745941d8021910400c0102d800070360108060120500c0c9000e100070000c0000d00243d40e40c0d1134000c0d82c501c280c403800705104402840010046219000b103c0c0039420a40d904d21500103600c86e00c1d000740304814500d01e040242008141046641030200704100518403a0101c000345080c00d0260554402c00090108000c0361410056003045a82c1c5503282079200c0c0c5401a00c1303501c00e2400b14805041c00d506150312400d102c0740c051a05424446580c4103040783c1c80940b03c0381d1140c1080c0320064201100050040d04865030500060074884 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 376642455 1250 376641205 376641217
    0x40323120d0f1b0801031419080310080f16060c0b060f060d06240c0309170a06111e040f0302091f0303020307060606210c02010b1005070213020c030f 66
    0x1203001a084074940c1c040e08550007000f0000300403461580040041c844441c10800c0c0c0c202425000d450002e1415a40380418514040001e007000d502102042051808440b03c50107014003408036844000c40c400d0b02a650511060707005c10a000c2c910011802c144613205007804a070b4024003d0805884101c20032400e001340903d2250021070030f00c0b02c0c1c0f1000140d070003004018095207500c56070721072a888602200c2c207a1503070548140f02d41900f4081c00282e112081400f2116429003200030000c0c2000c00f142440d4400001074600f0342040100034104140c00d004014511900301a05224807061200b510603008501c40d0801c501e0001800308050300302041700c25072180c003502109001e440c4810039050000c055810030b0b00113901c00b2410a040060030700c6890064100790070f1000c0d803070b4101c0c0f030b0310b10805600410580d4080c4e2580401c500f018000d411043c44188001c3c0101054043d502000b0003035004020103038440d40018802842c1e240e030034400c8600d0b52254401851070600c80131090b040d44d502036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 376643705 1250 376642455 376642481
    0xc08071a0a390201021507021908190503010608100302031b011110050f090105010e0112050f010f0f0c1e111504030201051e070918060b040323120d 65
    0x101d080603402012201c184100c88440100b42442020315000091500100301894025140d400081c40966500000c52030075480100100e0044a1014586102680525055030080308001e405035260f158000000d10b0695140e5a24586c0c00d81e01d0700c0e141a5502103c0c8800b0350150094007040c0c40924161030541d4248006040015540141ca40350f186007052440101d200c86540e24184000c8486030b81c8199000100c1030b00034007941d410103441903001072061240f90601886003100b101086002c3c401d15480e012414020050b0404001218000d00100e8075407400c014941141c0c800c515000391540340040d81040b2180d131030241e4203041a2000d014a20b204240d511800360a039922124001c030b024415842580042071900707042c495601041c0d407002c2c01d04110980c0c01e0822007642d43c0103209508565555980e203a5102002c1c02180017462550003c08800c800000c021051041030804038400707a00850400d041010010b005540b503600082d0703d5070600c00f0030003c0b02c069405603080012210a5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 376644955 1250 376643705 376643747
    0x30e07050307080a0521030a0b010e1e0108060a0308040b091908210c03070b070504090c17070203040b0d09050111030106030e06060f031f0b09040c08071a0a 69
    0x103410000703140007400e511880c01c6134440142d0204025043c00030f050343e15104140c8a60340078621182e000e407404020400340c07205584050410880c0c5c0b01300003090003010040d14010032210209a4407000c00043c412a0b804140340c6d03404201c05017040301955040307035001102c0c5401d00c0d041c140c403030025038414601d469002a02c0d0444031b5450491030f28201c014100b041c02070001d01d0700d18140728180b4460100c2941800340901203098030010100c211090950f211141e01e00c3e580e40c8000070740302401203400031554185448248444e440c1c2103c01003e540d8004c110302070b8590707904e0000302c1c0d8034807440c0a0046048010702c06184068804e030440b0407018401c400208082c02c03108401e50442e0000d81c07242c03000a441c0d180f09110910240000c030340186094641100584444020070f90341c41d000580e0082c83d80421001d481f20906d10307808101414002003c1100314107042c20403800c17800c05405104c8080c040c549000a904a000500505003003810841034180484c05800b681c070866811b00031000c480c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 376646205 1250 376644955 376644959
    0x50a110c07090e34090b09070f0309060e280f140102120a0203250f1107080109050d02101a0d140604050318040216060c170a0f0c0e0a06030e07 63
    0x3c1c4401409071034a07294052011640030321121446245600e03401080d02e11b2402c52503020036181d0f24042640544242001c204208010400310014258050064100c0d8641810007a4189010501c81d01c8040c0072101c00300180c0208200c1c0c0221a0300e0b1100620281c07000003402c2c005046480001c3c10010003200040c104912520351140d0144103c0e91803051540c008200004659114000104200704072002221105010f4010f080100400040c2007801110900d200034000100a003201034800300c0020b1000081518006640740c02c8002d0603005405201000313002c00c54684146421400c01034442c0311509011428404110360114007919008211038800c0a940810040d407030245200700c000715030701c00d00f851000d00516454402c49200350f004001c5800e2008441d90314210803600701d100082c158640318020303100c03541164030600705203240c00104281c03400141c0c4503014030800c14205204000000c103040791220758640013680c0c04a1001011301540c0c3c8070f5401601755000c2101129a265 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 376647455 1250 376646205 376646233
    0x403080903071217090109031409030712300e0112020c1b090c0901020709021b1207110a030221011107050f010605030115060309020a18050a110c07090e 67
    0x31000814080421130f480f030250750101021340040d9214103860002c00c60b4403100c0e030303004000c01941344840702900b07030100f03c0c102c8a990a0210302c00804c894408407140d42e100f80f8107006005000b4031201102c42c0342d03001c1306400c41c03000040b001c890611540c1d003411011040c1e006449130000789400c0c03141c1680c02d0000001e501003c01c181c035030718007209400031440c62041e401c100740d000000300080e848a00c14000711090303076000500c08054485000780580c40d003009000c1c00b95160344000d1b41507814030424000c10710510070000141441401250220b0100391040c0030300c20034183c2407000940001d2012856146402c00440c440d403030917200310000c980341e003051240f0811500041c05c00e55080d0050400030701292401d104400040500f5002441500d0b02d80c4454150807620340b2542c410b06440e8000b001c01c660302c245100014000700c0c000160b8019924540c11f00416013202e641000c2d500d0f094850b0b48a011401c1520712400340791b4010074030399003400286000742000e541c6540d03041c825080f84148032 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 376648705 1250 376647455 376647473
    0x706090f03030b0f031c1b05070e041103010203011203081b0414120703020d0807080f0a030c080906040b060f030a02280608010506030c03061c0602040609090203010e040308090307 79
    0x740242d8010a80079800d0b810001c07000f449481a074402e52003070f01007290808441d490180b062145041031400f00250841a44240440321001445401401400300d02d101e141006180194020610110101c90201c00d150803484203010301e10b80360310340b01c6c0100300280c071409005900c0034052002110080e200e0841c04030070703001900825810f250550781d059080c108000905880c0480900400c851451034022030184c0d081001c003e481c55070001062414084c150003100d4006506035021981c82500d4407004000740349411110002901550218503015030005642d401950014101800303600c51404100d50707040003040d81901802940d880e031016944816084441e0303484100607100d0b41c03030802c00010100c40319410410030b0080c140c00600058079014103803940489a400b07115a41d440d10000182002184088144144441d0241e5002c008064000e042118400d07100d1420142d212501041030307010900441029954110000b800300e48543d8290303401840b800240c9142c00307002c0c0c88480003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 376649955 1250 376648705 376648733
    0xc1116050f0609092e14010e1809060f01291e1305090f01081b0f060d0f050a0207031704301205060d021908010e010506040b040b01050f070609 63
    0x30f9601e400c41c209a140300070020b0359200400c0c80035a85846e0621071070089050b401c06599040003643d000005d030035115451010050001c02c01e542946203040d2407201d0b56403130200c3e10704407241e02c16000024039103440c002d0445910b0904005200400070101c2c90300c151703001000090201c04203007103800c20100c40c1c0c41c0213045884d8224220481141003000b8805400b0001e00080306030300c02c90004004e04000421078041c2212440c000741001c089041c00a028404c1c0e0601d05d40c0e0008000801c03185600d00b0f680700d42c9145406640c10300055583d1100c2104030f014100016002c41c2c8440c0907440d801c0d080807901030f4814401c540c00b50001d026501041c0d04015607600303489a090741c50111103410368000e45000d139506000b003000e006900d001804035100352400003000340120120340d010102e065200512902a01c00c24008008130002c0d05207450117031005540d098000c52404100702e80b603040074016000400011703141c0a2030020407000703d003040d41c004c4000f640c4182d0380c0c0141c2c80004142c1488414 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 376651205 1250 376649955 376649971
    0x20f0a141009090e01060f0e0f13080405132313060510091b030b0301050714070c0801020a050403110303030603150c0f040b070b10030b06040902010c02040f0c1116050f060909 77
    0x40040c1400c0021f07202c01b01a1300000b1a00c0c40002c1000b4500028120803076204090440314100d41e030071480e1860341070081d90000e0398061081c800041c55000d030341d400346e044030f050084a0004a9006540c00c0e005041c00d85070082422040d5111802094454000c190442240d1011200c640e0781c2c0c40500c4120303a40c07900203000c6402e002042030300466040c081c080b94454110020442420807a02c080e241d0300e0b02d43c2c103d104548011500c50244044104104000c001c800d0082d941c1d2030580400a1695003d1b000450b040303104034503445087d00b80041500c0c4a240d000e0000c10210400c43c2081c2860600101109801003041101c14014000c22000d00300030074840d485151582c0003450b0440038440010480b08440c0d4107000e041011404001c0c41d2604804242c0d000a10b51065000480729041031440c0079403c0340c141800e502240000d07910410501c410f60b602c00041251210000c0d0301d07100c04600c2640f0050360b0b182e042c0b207103160049070001081001800640b808512030040344511a045401c20 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 376652455 1250 376651205 376651211
    0x50d031e020a1b30020315010821030703090c08190c06050324010c0209010b03061011060604180b2406040303120b0604030b040b0103020f0a141009090e01 68
    0x2208000080d40184880c41c4146404150242404c03030504210b8440c502915400c480c00542e00c200c80c03072011030100041e80280030344021450221200040e00828440c3c80310510038600441c001d00300c0d480c0f9050104020446662a54030b500c50110040c201e1414180c5d650030400000003a44c610030071160074451103a0603a076000e0305660814071f150310703000c3e4084028060100304200c0f4003c4c100f6000e0072241410700082d40b421019000480c3e182d5210000250401d0b08040086000840440030307612891007215488440724401108036442440b107503c1d109a07500040c00300b41c040c0340030707000303101328180c0038001d0110340c681c949861100c8402174481083c1c0c0050310403800880d07580c000c41d2080c400c03c1503031a1440c2c1850b42d0b81c014441e02e240c90401d0140c55a40a407034449940311011100156003184001c07100c0d09103801c2c14044100f0a02c0228411145425499468180b04012400302c1e90041b030000e40200b0300e44244081480c1d08203120082181e41c0b2400701d1003622078070600140c040180000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 376653705 1250 376652455 376652473
    0x151c0b01080a050906180304080d0e041b210b09040b0403030b22180f05060f010e040b0106050702040b28050a03080a120603020604030305032d01050d031e02 69
    0x34100260140c0002d40745401c1004000070340000059070368028004009a440d0b0007404a03095007580a00d400026450049180311003800380e0001c80c1c254041c0b412a800c00c01310f4980007021081d82c04900c2d03010b0102d508807024200f0440c0e90b20118070381d54400ca0003c074140b0300820004e0355210040b20200d076011802c0c4203100600d580340c86103603884503080c1c1c2c48000448461003608480c00d0344c1c0703071340703410840d2100c040180d000f0900080041456009031400c140581926100c0e44648044071050041a5914000600e0b0303120703006501d0046400441c3c140c0a40d0820600f1102988020416038119459540c01140c80e1984070b20080d5205002c0c00c01070804003114160100102e543d4025803007450103200078404903c0074001c881801d071090174010074419148909902600d0260300281d4421004540007091580050055201d03451030f90850461b4072842e81c1d020b00d00711224805866010480006204034103129245101d00f500a0078141e84480880507803400569494845c000160015464 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 376654955 1250 376653705 376653707
    0x51e090901030f033b01080105030303160e0901090204030512031b180910061407020f01030b0a030503040b0a1b0f12110f01090204050717070503060625110609060306151c0b01 77
    0x190305c0c00c14007482e00c01c0e50381d4900f00002c0d43d2400701801915450b28000e28006100b07002d00070544a003d000b40c298800c40da9500c0f0981c0080d001032200751032902500700f24080340759120007103d100700b9105408000060515203a4900f82c0c025001e030011140826182d441e03035503280810f181c03103400c07080c1004a081e410301e0030042000170243c0f01031803545000d200c0400180e03a290590303864040d003880c00040e0042c000d80000c1c031194560780302a04034000000c0100e03503000d9070310003000522640c0e100c001c0140148070125004c0680500c0181240c910300c0300881c001000d0131864059280395140104000225a04441c28055079408480d074980d901c65038070701182820300585030b0229460070030b415401c890000000108400426460400000200040d00f82d90303008140e40520011038070444d0804a03c010a82544819010558480c00482c0a6030030514014007141c288030009000c080c20342c0c44960521030181c0d6107602d040c4441c01c092080341011485081703d90307120020078002050b11260600 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 376656205 1250 376654955 376655057
    0x10e010b0111010614060d0902120a030e0a1d060609040f09050c04050f0c0307120c02240c16050a05030c03030f0609010e060d021f051e090901030f03 66
    0x44102e02d00c0e41490000c01039402403060340540400140c540300d541b040b032480128002d044010000b940819059807003018140c0c0000d64000c3c451003510781200070702240c000c000320710840d4030440b903460030f01c035446210087d03002c00d035640c2180c0042d040b98249084880090700307541c041d0700b01c0c41070550344110680902408001d00307103003400c05543c00c1000b0708114140b0300c2e02c0d1400801c0c04221000020101d40074034030900e0f01150910341781c2001c00413011010380094560003007610301da1040304990048410000e020354003e0003002134007170240c54000101009000d40030745480039103083c0500d000c40c5001c01e8052006100c54001c080156640345480c030715104c0100c034041c0415010790190801840340388190344129030480d90446034001020076510000d2040031030508800d403007041c0d1501e4044603503081405000c68005031481d060600010408243d1140500c01e0550742c00b024040041001c29100e0040c00a024000e19280c03244c00000c00c0700c9407484040c0c41003c0040003a1201c000c0b04c0c805400e0b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 376657455 1250 376656205 376656227
    0x7020d0914010509240711010305070206070509120c0d03030617010605060d050402060715020a0e01030e0a020603100924050d051e012003040203010b10090303030518010e010b01 78
    0x60082a20030000c040000c103d40500d0020354041c021030001400e4900010400b441d110f0600007201c0d03954005031400069100700500041c0c0400e0601c00410015800490800c1c4104200daa4640c104080e450822070304106030b844613003a600840030440a035403500796101600c240030f83c0340442e002e4035080c04907205210308900801c15902d000c000780030350b50305c00c011642c5030800020085100d0302c2d1800019654807600074000d00b101c41e4030300c083c080e0003060b401500d00c0c0300158540803c44469a001503094076000c00300c611058009088800061402c94042e41c0c00c14503110240001d151640910801c90365004104035400c2055202080c80180344031420014000a84500b40c1c0c08900e640d0701070340c4650401c5041c216400107080d81008810940c08140440e00708110342c44600040341403402d65901c00d071001c1e806942091141c03039850510380b80e00110130106541e00c0d0080703442c644046008150251100403449060506240c00540074040c904003c00c50704000244c540140c400580b040e4080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 376658705 1250 376657455 376657469
    0x403090b030702061b160605060301050a2a03090c1d1015030b03010b1c0b060d02310504030f0f080c0d0207110303030408070b01060206040209180c0907020d09 70
    0x810030002c1e0507501003200c58029142000341c5444110180540005000300c01da410ba80c0041c0480c003c062100f203030001030190005800800443c4c90714041142a2903407a89400d02c03220f1416680c0d58000006900c02104490a150004144d0764540c1c450081c0c0480340c0c06000c00b21031507094008031101c030041031900708400000c00741e00cad00d1408080440321030540c000b51003410b80d00d00c41c0c0e0b060b5880a40008c641d0000040c003c4080340c1300e0308114101030b1980c400c01c0d02c0781c1d024500092400d0520030300303048981c0d07001098440585500440c00e185500c1007241d4440402c1000141c0c500314109001da180101d00c01d490b03000e50041310b180300814185181c130340103082283d44018070240011039000c954003031425030f001690b652941e0818184600c44c40d085d01d50903100010400c000e01525802605c0c0141c480d034040d00d096640c8940c226960310080e07502941c03002000c00452403604100a5104200085906541d80f04200c000050101481103030440096000003290545195010021002130800d03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 376659955 1250 376658705 376658707
    0x204030c08013218010519150e01030206070323030906070801030309260d080115090b040e22080d0c0809061810021c051e160c0203030d050403090b 65
    0x6103840c083c3c0030511040300e41080e100507502080301c1a41015a0012812111000788038909141d00ea04a00d141102d0b1080c00c040d1400c824200d13495000c171102000c07200b003e010701001c3d90854007000510b5104980031070520a2143c40c6035400481d68411009854060090030740340c2c41e10340d400e1403e00c80018551400c0040320801400042e0b041003607030060b2840e8903156128100f841040705044102c3d0840c1d02c00a1041d642e000000b242d100d15840c2c1a07803030000d429008001d040b901030f034141c0704c280245100000c00384424001d000302c440c66035901510000c2002e481c0745d44003400210003c0750240c00c1e1251800040c81e82141889030141c03050f4910185440c4155140c6407143c9920748102400d03001004e0049681045d840c0400c00c8030044010142d20b0844d554070720881c5c2d0b209400c501d040400450b5081100185200150700450000d01141040c0f80109548403048411214020340c1404c040c84072502c103601c0907032002c01c090501d80041040004a5003024227000e03108422035030207808181c030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 376661205 1250 376659955 376660001
    0x501032a03080c010e030301140102070e0f060616060f060603060f080c06072a05011206121403160605062b030806152b060b0702060c0309040204030c0801 68
    0x1200500300c076003003000b40e42c0b03034444041118050700001c25100f4061002100206003030018917001c007020b1809030200c1e881c803992200c25030310a8008660004441140b1400294541880001071001e010704010110009602d503403160122841d4044a0b20907075502c242c103004c05901440360402802058a455070004e15101002e903451107d001c62f58054540440e804080082601c2002111030300d250021826915116900005202c1d620440f0b0010b0f00d09075280000d000f440c81088190f4001155041c4489540d444410b0346100b03c07112000c5900c0100403040c0f071044040422070b0510302c41c00300810941002c1c000c20655a01821040d15080c26030394154422030588881c8003101d5034107003808040341c7d0302c580000700078030301840b200422000c00168015900100c03500c4680c142c5c03c0402c04015079203040135860101c50140c007a1828082040054001618140c0e02600700c151034041140e1a00c40e0390320100d070690300650b000b199554580a82449001000c0c000c15820088002641007901 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 376662455 1250 376661205 376661273
    0xf0f2a090c0d06090e25050a0803070b0709030f0b0712020c030c210319020d06030303020702030615091f080304060c02090c0720120610050102070501050702031e1f050103 75
    0x1c4021001151b4281207450780c0c80114071013004007801440300a000d0840541e0702c840081e02c80c1d00014086a0000b401d10010314802c1c0101c040c107007a01d411418607078164040365111840719001400a5040c440c0d42ca4822012207203d00081c03000c0300030100a541c4400085801d54600201c5000e610150714031800e100150f180c0382d000f1b49504c010b08660000e4600c00c01d100c180024420003460f003030440e04202c00801810b8260700181f00c49407007682140d4055503200062038245000d003254660204281d0045010051700040c801220078007401811202542c6c4c016031460341c0e1041e840780c00419034012180017585000180503500c242070080d6145441240d43d104040c2d04203802c0d0340110140f403035082d824241c84503515503004440040444030b480c06c01081481c1d459460f446920b0040c813418a000c15154410b2003680c1000340e019000304400310441516100c0000500b410815901c141c8000d0021a860140c4030900c500c2950000502941141000010000300f07400c441ea1030020b03056824051 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 376663705 1250 376662455 376662463
    0x9140f0d03051608040309090f1a04020a0807110712140d080906010b0a030609021b060c0405011202071110090303020c01080405030a030c09050a03050601080f0f2a090c0d06090e 78
    0xa0748138074021260fa603461509075005c81140c0c03c55800503240019010039041d03158080800070100340c2c00800da400e046030400c0244d01c00c074440c0b880056545400301e0b41d098024102031100040b690b084d03451291721ba034000c60303101c12444400e48030180d032920302000b510001d004185014017203260104503491b2083c0120740d03880f010311410259100c0041c0781c070160b81c401d501060103000c000ae002d5607180d00c441c486145455207000b42008a0142101040c08008100103c8040720810784030324111811000c8090000e401c2680d00380c82e01d48909040c008983c0d14001b40c82811b00c8261140341f04203056041c001d05c0c0c6041c4c107140c00d0510116406020106400009a03607000d03030030b8070780070814100500c2d04031195000341c0e00c01034111710174107000b0040000204116041c0c54031002111110001135000c1c5d6501c0038000d100340b0107504421a050091382181441032100480e6a40c2114058400c8001c0f0703509020032910a542e4107804100440540c940d802920010030000c1000e02c5000780102c6070b2525 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 376664955 1250 376663705 376663741
    0x2030309150402060d020c030705010c0f1d0f0405010605070c05100c12030e010617010f02070c03140a120c0b070c08273f120306030109140f0d0305 65
    0x30000302100060840d65413030215902c54862007000d40d2600610310219980390410b10b02103071a9400c00740240b910034841d40305100780c02c00312f80e00e10f0b160201d180d4400285800d5003041726000902c146220040c0e4a0368000d550007051036a980c50382e1a5081c0c10f2291448910b50001d500c00c0e2042d030160356006600000342030405800003502c8001408051040e002014000c01444080d420f1500005400071580e85e9007100c000744ca0001c0c0a00404182d0396412880707040002004801240b80c00e102140351043c1082651111004440c072404d2545c48a001c81400201c140c4000b602c03031000e5404001d1803e5038a40c108010342020b01d06803038160703105c0c0700c42e000343c5216940440c0e200c1061000720058005100011601404142004089a240b0b40080051040403414501141c864490350a40c44032500d480032205006803290702e8190306240041d6001400381507040d03485141d4003000c1040b901d43c0d451200b010400510810407060429800c00301d020306494203243c0347c00100a210000800030f0341c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 376666205 1250 376664955 376664983
    0xc08180909010509100c020a1b05040e010605090c090303130b1c02090d0204050a0603080d020307110601081002090402040b2a1614030a0807030f0801050d05030d2d0204090b0102030309 81
    0x24170406c420604a203403038a6444042c08170084200045001d01650709a5415110207075400d01500c00c0c842d004509803101845003580200c000b0340000c2125001030054a06a8401010349190415103610902909003d40144108080c000781c0d42101541080160184041c203030320540c18905d41100060313040e0394002004c4e010b10749880c005060038034280e0144000c0d41d40210482d4079520040c54080c020341003152400c001c50303c0c1c00d250210480000800703504852005005150003541400c0c007101030341000c10200c0c0c01c203401380008940c0014030f80242440d00d0303445501508003c08445070303a0a050350105200c0442d000350082c64090340c10016440103581304007000c0a040e04004c07001c2b1386010300e418000303002c82601245601c20954800141280480165034a84541e600d600c00c010504070007c2000301540e008200ea17002102c0390742c0014808c0c64641d1b240b051140c22001c8481b0405006107001d00100c0c0e030004044c010781c40144950800c0310400e100450540c0703080381c9035a668000006a500c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 376667455 1250 376666205 376666211
    0x40e0a0b10081b1008011206020d020405040c031a01030c09031e06140106030e030405060415110106090f1109091b190e030c040e030307030c0c0818090901050910 71
    0x40e0a510950710003500500340a01242c81c6107a40c48910060b1510210206204010b9401c200311311910034844075060f5010100102c0c2c0319901a0f036460002d41c0203c42a200c400e40900000406986030b1040060b4a605c0c0d48000c41d4030740e8081c0680249110700201c85060501e402c1110700c005038481c5803a0700b50b941c020403405800e80c643d181c2c540c40001041c001083e2234100485d030113020004905040c101c1d07181d6101400204068043c681c0c690146002c0c0035004081400b0030001c0c3c2118450106100c046801e140105c0b1034041952800d490700340d006003400c42d40b608902c0e4030419543c0320b03079980b01d548411032034140040c1030001140c03d480908034030801031072484042c01c6080c40b00308031114060880c1d6244003d80b0752035030180c00c5403654150b040c4a0702070aa090012428240101540301007500b016504d15901c680c0142e0052642100700b070700300f00000300b000000400f444020002030301e03140d451800690140040002010008020140741e90501d024099512400035060249407007048002c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 376668705 1250 376667455 376667461
    0x3051f3c090204050106031407030207050a02010804030e03061f0605130501050322060618091110050c010908030a060602030c07060e01050705060a050106030b0f010c0803090109080c061005040e0a0b 87
    0x400d014254004020b03600900d00000002c003640c060380240358681407015910082c0d61106400d6040340184e003405030203904503810800040d84900602d56101c0d100f406c1c288020010000440d142c59000c07245a0000c046003a100c100500d032502e40c5e40c005140031700d8541d14004499210002404583c8141d5050142c044003080300003142c00d071080c6005000303001d01000000e40e8140100600303002e124804174002c9040c0101d84c8415980210703040d42d50800385240c04806880e051250303035031500b4130080802606110f0070124607400c0c0203000c0c8490080a03a00c0d00e03810511003440442c0c1c00d41d4469001d650081146074007601e40450310340100c5a00d03017010344014001074016207291051207802401070080e00304001440c03ca6500140c10f90f0141d6804012603980700d014400440000109036011406405510300002d41c44030095a02030584c00011a00411960f2aa000d9801092884629402030420801e60520840d0103a004000442e004c2c80354049094540c1d4803201440e101070100c807006000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 376669955 1250 376668705 376668821
    0x302150a03060e07020d09090b0609120c063106091403031c0c0201060b030c090d020411030708010303180e06040513020a090204060818030a081003051f 67
    0x440001041c8030083c5212034601000029154081d45000364040744444c440440c0d03044140c4640e590244000d481240f900034108100920f100396a11784010a203d0307400411819241d83c0040d16101d440d03036515140d180300c1c1664002080075802001040d1111400e020004035030301004040490b8210540e0b000c402559802103400c42c0724030321030191a07844214080441644682c0b00c15034507004c5900802016494112400b05031000340e451400101003800055600c0c600702e0a204441403004100150110344140004402c0d0000c0714520b0100e80c0040042040c10380201181303a084a00c202101411400c0c01207c04103c0c070040d0215000c2c55881c00040d03c0340031016a54089103400801d00d0710342c96920300d20040a0b43c05070241782d00080c6c652011405201c0440c1041e8101c0b62002c0166041c42d842403800c0b154100c000b4102306803d00c9124000003c641c09000044d40180854034103017840014030201d0341618001d003c12644811a2503030071086081b0488108020f0480440c0c1134084070548903 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 376671205 1250 376669955 376669961
    0x83a14070f020a0e090c0409030210020d090f0b040b09010b06071403070b09100609090f030315120b07141204020f150f1e1c1d030c0a0201030f060302150a03 69
    0x201c0290424141000828290b142203070192190140000f183c243d0201401400203981310924020090390002d0702e544c0c0e501425401500e01c40b600300070005022160f68440400700141c00200780c42030a500800d010a110385540d42546c040101002400031084800204a4078422001c014141c00495081d19a600c4003c2c8215552250029000c030700f641000c061003501c0300e503561031040c8090710703101c800200450140079503407c0d640c1148428070860420340303058002c0e008050107212901001c000200311100240c40c181e8980d4042c80d1903407030501d04000060103020f5154000740702d0400922010803100c496084181c1e11a0b4140d07a11040c3c02d440380041103003000c40c482c031008103007800f20f4401d25614a60303010340015005105440408071400e00d0480c028881d82c0c0400002941c510116002e0b9542900304c0c100034001c440803a0020045010444d003103410141000c0000d4212084070000d56900d40070701d86e0810b2000d02c0c1004102c2c50f550000c2c0002074014001034503c0c0c00404c1e00b0401c58001e80c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 376672455 1250 376671205 376671233
    0x3030c051e031312020606040606020f030712210e0c010e310905061e10090903020a0209010e18070b18030118030503010608070906050301090213083a1407 68
    0x31110b8020411341e001035281c1c00200d41042c0114500140007520754400580310366440c1c17403080a035242c0030b255103401345070601c1a288502070000d02000c0c0182d202000704100c0360281009000145425288a2141040740031908181000240b1500280903583c03000c0c6181c042e01185c050221001c402c0d41d00b000001d16080e00c0400700d40c6400b50041c180704021480701c2c46800080c0d038451001b11720f0003006078000c2e802d0f100308040010714041031295001551110724030500a004590780724000c0d0340016080300003604145e55080303402e0f06000a401c020081e030542e40080d02c0250081c0f0f420002c1d410710f180540314101614443ea010560800c1c0c03429404190b07892401082203035155080c1c2000303045d40d8801c4c407800c2c0c00a10a880020320a078800c0380e1640a9070226506c052440c3d28051020b0040d4112407044041a0011880010402002c201030440c602e400030240055001d12441c07504100040018819502d040300d9682c411b165000003821084a00d05072442d03120f20403820140014500344c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 376673705 1250 376672455 376672463
    0xd0b15030109061406030c030f130f2307030302100902060702180f0709060806010c0302010213060206150108060a2702160c080a02090a1a0a1203030c051e0313 70
    0xc00402d0380b2145400c050b059030319864501c0c009551030400d002042c4000c44420000030414004144812092044039401182010180d5610318003901c2e010a0383c10703407000c11624986540b1a061504003100c0c0c0030001d141c940c03c0034085003032860b05c020b91142007000b548001c46586800359403c5654403000c0c0c80903a80c0207031083c00400c24130111200f10003810b07034107100d000320f82c4c0c8000b030841e910800d520415148a03030381324899620345100540b1109280310048041d55028054261340f045402c842c000207101f607600422103410120300c401c158102c418509410042d6a60070041c450b1034040b0b01004840b110110301c40c1d80e18862801400c040360b044503e4121a000080d840355042010500c192114043d502c80b44080e41c0d00c0c000c507aa0340c0c40990001390020304403800541e655a85038442051781480e140090350b0f0500c00e40000700005040d4001102030f5100b828808145907061107244072102103801c2080c41c11400414034451100b80031a80410180004000741510f1004880e0980c03a541c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 376674955 1250 376673705 376673707
    0x60209030a0609121b0c060e180405060103022103090f06040b0c060123010c02090a0e0a03110709020c100c02010209130e010e011112060a0e070804170f0d0b15 70
    0x18504124150f010b041c1c10000600440d41e00c26010f848061042030055011b1540300205181c11020360305528110000e95105456803820000341c010242481c0c490ba104201510300d660442c8108656150321864a03007030200c142247c06c10b5484004100d41c00710703804071200d21074021a039001445c144102d4208802140c0041052140088009491030603145520f80c071007820301c11901c9022881d8400099103000586850444015003030203580103812000403c07021036402e25513002c00d4076002400c00200d0000340b89150502e20480103100d0040509030b810300652405540f1f41089943d24050040d81405d607a6888944410760b00035411510340e400050840c481e4000c428580318020031011302e0341146942007a10f00d200c000410301c904c11600c10000c011030304021402000d8000b14400a20094110001c5440400e100e0b81000e00d841c810603450b6a1a440e900c2d1030b203049014000449080c94607030340184038041c010304180f003d132141080340440010f841035181c80007071400c103000c1c0094698010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 376676205 1250 376674955 376674971
    0x10e12010c020d0f0f05031609150c030215060a060809030d05180c0a150c0c09021b0d1704031119050c0a05060301030206030c03060a0306110d0b010c03020703060209030a06 76
    0x24000c0780320f01029a49440d1050306400800007640d00d440028011400a80100002901c0e001003884480d662000c07860400400c40e220421000b00d4a404280c103400304000050b10401c0550420160108404180d100e80407410000c01290b60300d410f6004803400e01400d0300000d81e1111040040d5603031480181410700007070800148000e05640003100300c2e6028000c40b03401414074140b0514150445011401305041c030308030103c1c201da66040d00070080f04c0703042d440310000070170010030f002405c04840c15594407405031a218130715031b14180c2241ea865045c0995800c1025000350030144242c0d115070103003401c0c03210360b09803103840e401c00e907450b40e80c00083c4116002601c00d008001559050b042e00a480c901c004a80304c0d402c009480c0800d20000754085410400107608070443c8014541000000c0c2c40991307120740340d41d944419aa00581c00300880c4801040b0205100c0070340c02081205c41d020b084c4551284407a88009454403c00d000c081e2500d6000a50001252410800308192640019081042003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 376677455 1250 376676205 376676207
    0xf02031606030c0909053306120718080d080c0909090c210c04090302120d05040b06040608060406092a08070902030c0406080c0f301302010e12010c 65
    0x2240515103c006503481c0d03804945601c46125160081039000c09920080221000da05600b801071b8202c00c0b1010400c014100c1e8940307542002c4c1014290f003910b0b613034050ac0e01e008001d02d01c8500e2620882000740006003040070355004074061500704210320b0903a080d55540c09e040010380c4100035000750026044020030107042000700710028900c00480d25071400d404098440202c5001c0320b40060030541244186010902c0c1550001407000d100f030040d116044545c02e940002c0381c01042e111b040103622081007000b0000312004641e401082110100000341c1800307030341c0d80c0c2c80350001c000418050340c9404a00520646400d034031540d41d100c0c090a001c00e000d0500b480505809840b42c000d06100e4440049500c10302802624030403a0043e881c0b41c186032030702000b11414000074004004040b0100401d0000d813041c1d00c0141a01107082c0341c03540581c4142e4903034200b10039404803c80089098481844925a00000003414058091178504000010a400651003141910000c50a5071810400301e80c82 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 376678705 1250 376677455 376677461
    0xa0507080c0d02010506030102040f120c09051008010b0319030507020d080d0f061409063a150b0919022a0d0c2303070210020303240d0f0203160603 65
    0x500e040f03600030700644d10791006243c20b0340240e0080c8001d09240c5101486640402d00d03040452a00607a401e0381c5490b0345440400c212541501c843c012803002802c140200c40d03090041c0070024005400411680d640840c0341c2000095008004040000014000041d5503811800c00010340e0089043c80d6248011350300c060061111038000c1003402d013040390000300081c440644801d8400c0c0901885c80c55a14003003048540f10704840210040000700e482d403409080e0b04000270f10310803615140c298000c5001c0c102110840c50b00500511401d040ca00000c880707885411985400040984040d1002d10100c04042c000c0c0c0034460220103d210029000d00310b9190030760051072010f0300032054a8a042e0110300c11206aa86904080c0c4645003644c0703407402280403a403040612003611b0050b20b00340075503540080c443d0308c403106913000168404000d10450750303143d0189a0301d00c11080640c00008030400c020440c3c06145030b0700a03050200403d071980640d10244810039460001e1140074004a46810014000b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 376679955 1250 376678705 376678723
    0x212070206010f080309090109021c060f0501030f0527010924060617191107120801120c0312030b060705010509060c030405061b0d021206040b060703050304080a0507080c 75
    0x84020500320001d4401c0c2e0110032a4408030780030705500140c1c0c0c20038012001a5100c60003600705040030bd451004200314504c40c6801031702c4038503000c145075807500c070004090700c0c808440c0d100c80525240c24880c0701320b24070111148807007142032415017002001e29401e005103403000d005062850070081c20524034503110703401c2d0080c10602c081009500d8031510212450f07180040d0841c01c83e030389000410802986c881403030140711420500451040d90315150024541c001d03080032a02095000300495480f504410000e0140c034420103008028441c64841e140050410b00c809007190402068411606100ea004003004080241505650b1141403034524020300c0100c802c80550b015410200f03441c41191000c03240190740180c0245420344905000c00e46068088c0032080600c00100640225001d80c1e0000d000b600c3c03102001080d0b00e2500030244420345051750105882030b40100001d400103908241500e41060300080840d44480704100b00303407491322402c500a801e102002c110b52030794400014102319 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 376681205 1250 376679955 376679969
    0xb160f140d140a0e010b03190c03020a080307022b021e061b0f0105010b09101e020c01090f120b0705071707021914040b0301271403031e040303021207020601 69
    0x1c004c2c81040c500908030303035842c080a945900a905445006800d1140b00521540103655003554185e513507000480c855500d41c000c01c050781000c0303151701c01d40c070348102c20340d820101c40d41e1a540541030654109081e100d80300c500038807071405c244044c0400084a81e003881040805040b07642c0e01c2e41c480254180704180c001200300d561003100880211000180903081c101d60380b50354000d042c4001c1008000c184c0c24108003800c02c208800207400e4500c2507205240b0074207051500030f09906029000010002c18076500300317001e00e2021b00020440c44c224101440c400c00d4018001d2095511103060490341e912880e90050418185840d02440c0341d10080000d080c824404c40d03828a41408502d42d4203140122885a4000c80381e107030400c00e03011300302500180c24094004000003139100104940400c0d80c000401d008080c210f851003a6010405400d002d00d40509a4000540c114901050f50b600450b601c12a60003807055140c01080416000e80c040d40c2e81106442100599840c042500961302c403800d103e151 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 376682455 1250 376681205 376681211
    0x151210090c081020090103020c10020d060801060b09060c16090c0e0f030705010810030b0f04050c010513140a090207061e0902060d090215030703090b160f140d140a 72
    0x640d6582c0c1d03030301c542c00843c00e41c5248041142001e44c2d20329115000a03c0c558145502006411001c28040c00344d40c41402d04a000141c80303081224500084800d0b03900061380070b0b850110103100c140106010766861030000c48480b0b0369400d500000700c1c18520650b10303100c00c000f052000401c4070341c1c2c1c90b0011040c40a507641d9500e1107403000c1d410008180a07a21a094040e0043c001c207000c41e5201d070410582c00449000000e80c1c02e5941e59810010910403036021901803080303010b1004106060100c20305240d000d2900341d0900c6e80700392200c00e204106104000d0b030170300d02c0c203040000ca80f01c9004400013003401c100c0440d11540c460600001900344040c0300b1181e40f03081104c2c428101c0d002d1107000e0300290044d20803070505c0d41c0310142200600e0003100c181d03408000158088a96407a64004502c581851384d8003040c1075100345040080c048000c0c00d000750b20704818041034030b06940a840d42e08903104030b00c6c010465103280a02ca407070038441c48600105850510f210450082898203403a0b0045050900030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 376683705 1250 376682455 376682473
    0x12041203030c0305070824030a060603020a051503180709020f071a09030d020d0b280509060d0201030b011e090807090207030f050c0c040606090501080f151210090c08 73
    0x3c90403a00d0444402000c1001400072487c541451002910b4503080b10040c114840c054070006850540c208004a800c951034200610842c00d1840e002030080c5001d48001c0482c03403018500442d940402016140540f900b86540b0124641c2000b8110040c03280403000c6607150b51542c4003000960040c030090301c4c0c00d101c44d044550b060100f50480ea10411324100594248810901104082d50104a40c0c1045941310441110660380e41200c41d840000078245038040140e601e40d58840400640c0e12982c4030301c000104002c107944407000750f584526070900e030019125070301c2001664074812450112045c11980701790f040841360001c10000c2901c1000d4100e404255861100c50300b41d20400000600007503074040b07400d50380790291000d0540c00b016030b401d0720b03030041c1c401c800300d012250f1503801200042c0420f0b408010558201c00d60640040e110420440320386000180c045c0d090030303640e2056004d03880500001000746001d01c5075259221284c031007400b400516050071460100c03d4003507848280654010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 376684955 1250 376683705 376683707
    0x5070e01060305340507050f0d0522080d0804020319081803032502060705010c0305060f010309261209100c020613030503100801020c0106091503030c021212041203030c 74
    0x841d140440888513000c00082e5008003200c4e607070040e0008a40501c11281102c181450510600c0d820254030b5a84c203444458101c10005001d04071182059101240344c800d10040c040410540000741c15070034042c80540307440c80030a01e0040401498140c038101c5000072410820341a006040b4031000603420321454030403008043e164403d070042e1405410ba035034110036001e608215400540e50009181a00f0003885440315400e50700000505400070381d5a408202e10f92401c010801039a507020b03c1d00700320303030f240c1c075a60040c82c0c072448a0b00345440010900e5000004040f0001c4440d001c943c480f102c001820802000b580d43c0f0107182950030a1818110300d45401e0381300060341d61184081d90240e40301e0b2036003918143d5081d400680130385c0040150280114030990240020b103010510b61000080c2e45142030250300031504c00c1c00101c031803400045001c00100351f100c210702882c987c045600003008a0b031003065501e005e080030441c400e4800045000076000c640c0ca080f00100f14040d0320b050001c40c8034040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 376686205 1250 376684955 376685011
    0x21203040f031e0803090d090b1207030e010209210c0405041e030c0f210203031005060d420501051b160b0a110c061605070e01060305 59
    0x88480610344010204049848500b00369141c0d031110075001e0b1031400b04d4036072002540c4103e40301c80640c0e014030782d8155010360000c0108001d08001400c41c0c2000c030222a0b103180824042c1030001056116203400d202180203504442d40707480300403c0360304580700c2c0ca0315514058007010392000541c01206001400c90425002d054403c41e4031140e404079801c0781c0410942c2e0015220b01c01c0c1d0420041e0520240010119014030b503800703025140340c68915040c40d5203980180c0521901c6003c5410502c28081d8a8040c401410142c031800c0304c10980343c9218901034801090042e0702316141c100000f85231140d0a80c41d044c501401c8804c0801850300500000541c244800148111070016608010861154403000c4003d08800e90030003c1c0c0d4842e40d041c40540403000079a03000742459070320005041c0181a000050400c0f40c000c1070020b0a03207440100d000600d14003503a8100480032540c0b1100a04010702030219034042e000c02d6092401d03d5841d40001401003008884108083d00701947c11942520208 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 376687455 1250 376686205 376686209
    0x506040507021c021002040e040506060d08090d0212010213150c1502030a15090b18010f0b090604080d08060a0504050f060103020d020c0601090c02010c080c0405040515030a0501060302120304 84
    0x1400a040c118243c581000341c2c0411000e003142180175a200046560700c040c00140010700010620746280c0c1044c0c24220304185014020612821100078003100092041e0140c51640c0d4044a0b80c2c400d40c2091f001041d403d0000f0314107600c0c02e5100080703c0c1c1d503080ca540c0000d41030322a400e003540c3c9008200c2109507088000341c14003428440c40940907030101101038000b1540a584c55402264007440322084c20710b6101030f5040703801e516403922001040c41c03c010448000002c1c3d0a2100c0019515168003071184003074900401c094990001000f010380c1c1c40d0081220003c180100c00c9a10300c81100c032009003990340544045109810701080083c0c2c52605014a0303000300140907241419485040044d0002c2d4060410044859000c1c030040704c9502080c0511402030055450109441114540003800c4990081700c04050108000a001c00c1c00d50308020f841c181c0724140c42c00078440d00e4508807401c1c449045035284e50705100b08048042000010742144080f6442174940082a0648205407a181d000d14 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 376688705 1250 376687455 376687457
    0xf060f02100f020702041d01150b0f03070c02090703050f101d06030f070621090804090b010516140f03040605090411130e040c0b04060804060b12030c100506040507 72
    0x40005080d001140790b00000741c403012034600620702000e941c0400c0c02d4800746407440701d05007507603c0f80c049050401c0c05201c415016a5038101d12440c2042d414152078004e10389020310011020000032885030041200d190b030310360020040b0f8021700c0c2452004007d03010845055080c116040046540740300480d00071000c0d15074040d08801c200b080c1e810500e0200c60001c0c08154548a0744000921801e018041d46000c0c00441d920b1400841c4c034400010650345d80600181c01c1e183c500410000842c03440810f840580d80c09400c0851070084a0004a5540c00342c10007080c0751600403880e40c01007040700f00030008105444801e9580c2400204001520782c0611301c204408180700300400d02884c81c040c0e00041440e1403030103115051808c8070388940c0d408565034218040001480040c041403142c2240080018400d01c0b2801c1d1801d0309150f001001003802800041002d503e80c0280301d80f641d035903115001d01c1110b400c00c513500ca200c00103425a5502d030b01c0d546500450f107001c001c581141041c1c014580b1804803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 376689955 1250 376688705 376688713
    0x71202120712030911040501080d0306080d080402010507030c021309021f0e19030606090c140703051b19060c030b1f231611061303170d050f010f060f02 67
    0x4490b425005005001411111050400c4180500d66900d1141038080c04607030004000b080c1481c80050103c0710315421544160344011150012243c0c030002d11a4002c4c1d080ca046911020320780f07000d4900303000801740250300064440f00c2c0d00f0a400303a5400081424000c450b06039041d072242904110004840300c40000140c900807103580e00d410075032500030a201c14100e000e00c1d01e80d030381c1e1551001c443d040d030000207a590b100d0054140690744090075a2104140c2c0d224103140c0595a40d001e4940d218541d011041c8101c52000200f10b0071003803041c0b006c040400813003070302580400d2130100c2c020030070481800d010a02d0862030220a042c064400c009400080240b409245403048042e01d626010142850200c030201c55040c07500c20b401d60103808240f110041d01414134255182c0602c0306220900040d018450038010101e00c0036480401004494118614000000b004c8160550900c00c150354100d4003404d005c14000445030b603030480f9049500034115484055140d5204540100c2180c17404001a48 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 376691205 1250 376689955 376689983
    0xc060c08151c120219050c0906031605100302040b0a03050a06080a020922021002030909010b0f0304030f050c010204060c021201141f031e050609011503060b030a02060712021207 78
    0x20314800210303144811401240d1100a19517865000302c034046404881a030440702d03181c0075038103181c01219004101200034002044255213103142c075002c1442224420860418000741140c02075045402901569006aa031148940c4026010b0002900e80c0d070000c0789001800103100701c000c00ea4000700c5070300400000464441350440c41101c081d0f89d000e1603518141034400340050751000200d070840d0060350061929010410100302c05018140d1000707034074180802c24034007116001011281d0265150810307c00c46459514205c405000b241c411451540c80000d0115145da00078100c120890710869007440d542180c0100c19090b1052003552814550316507011403001c807840c40c0303982c5214802040c038812880e0390781c0300c2950f42195214280d121280384082181400000c0c400264040b400c0f1b030091101c011143c0e100e21a040c83e5100c06404a6542c1030701100b19a41402842440c46c2c00a01054440d20b01d4240519650301403078401000d4801c02c94001061603e40040d2a000d980020101c000c3c5c00e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 376692455 1250 376691205 376691213
    0x32e060207062105040b160e10120e07080703061506020604080c010b300c091f08010203092506050412060905060412020c120304150c060c08151c 64
    0x80d1010034800a03042d943c1c1e10490380f079880381d135104502600c05d051705420450b92030541c1002c61506c400410006000c592910303140d007030107a9460b8500d880c026101c1c0040800ea0001042c4488400c10030b4041c1078000580c00b1400114101580e00400781001001d202c111780c451004514440d8a0140c1c00000010303021400302009002900d042100109000080e5030000388011100c0c20071316125121085612058140c00c00310580c0c418003080241100040407000445c80b15008000312801d00111402c00c40290b100780301d405c028040c180080d501c80c10496042c6440d9080042c20703502e2011511807000090b0400c2c0c0c103100466000e078441500d000e082c000303141183c00d0410710030389001c2c0c0c42d002c4080c00214104500742c0300300d001d100900d07641c81071804001c4c01c00500c1c082243c4100c00c0c020f52031814030400700488044820030208154411040642a1104019280b01400081c43c001625030020b800c1000c591087d0514060a605400054100019802c01d509400128035201410034002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 376693705 1250 376692455 376692467
    0x6020610090c1206030309030c080c03071802040801060b07120504240e0d0609060b030a020f040e01090f050a1205030103080a0e030309040e030414010c0203150c0d02032e06020706 79
    0x1c0e920300f4200b0304001803082c1090380ca1540c0200d00103074031102c2c100306000402e00d8000140035044090941c2400081c0025039030310480c01291030304400b09903503001e045c007a40d04440040070481d009002e12a941c1c080044a0b412030030040c1d030304c0c00c0d0f414000300501d4414000c0307809441d450051400b0804154540700d42d5001d42e80c8040084c0450307940443d80a40c0d45010219402c1d1060002103045030441c600709055583c03d00d08503000e80c0c031041c45a80160303504511414483c2c0266000241c40404085960140c10010030142c6001c45c84c20203c800e01c4000b007810310341c46004403551131041c07034490811240d520003440040c2c6004028003243c40f4084c030500341801c0c1c02400504480c205011480010116a1882c02e0f0340540d038000a8100b0040d0030003004005001003d08200c44150a23035000300e1b480300c440810342c9208502040015040c4460f0340305507481c82c18616001c64032461328484004114003407a42624104151030f05900307000340039940383c6059540c01c0d4007400800c3c3c64010143c80d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 376694955 1250 376693705 376693721
    0xb0604060212071b1203021c0c030516240b0f010906050d0e0304080109051b06030f1305030304060f150f15050c16050108010605120f0705090a0306150602061009 71
    0x4803110300a00c0d54040c2940e1307a441c0540313640790120200900724680a403a1000368071062000e02da14002036090300341c000b41704100064150520751303901c1c0200c807101828042524002011046d858030341218078010050040c070408154042003100120350020007268a940309000307070000d401d000d01400001d12480140960030405000441c0d000700d0140d0782030171500590889441d5a41d200c080c8000d108042090207181c103044200c002035900094081a110b02c0001c0c06d2110080c0300c540071403d203075003204c6080c14054201007940d840e81040c0c41c141c40600b01c0c13680120b01c42da041014411042c0c43d808405821140e42c101c3d8100c0191522400da0709000b1044a03034001e1000c2400603031071410090004003440880440d14220250410700054520401a080b46042100030301c0001e038805500134559800031101144070b1300d140c1c0c842d03004460b03070b1096180d926009181c1c07450000402000f80c000043d107114244280302203d4580c80c6c102d0341da40044a00000c0303200960010406828a5440041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 376696205 1250 376694955 376694963
    0x901150b0c03090904030e0112020415050a020a0c0905240d0605070e060c010609110315131e06050102010c03480f0219030806210f030301090b060406021207 69
    0x400c000303c401c005241004211419008544030703680708001da40e0f0021410000c4038100b042103040609003496404070742c04212400041c0040000c42c040018001c0201280341680704950201d00d80e203612111000e0401659140e1110302d0b01d0402d405503200301544c4544004016050030020f08031515440d004d03000252480e010301c800e038809102192103000003072040340300010000c546203107800140001c40f0409800d91f06009018400d00041d49100400051450320031280b00715065849205100180510188000a080030913000744010000340c0000c005c64000360000c04c090407100c7c0040e01940c8076040495000d900d000e0710b0300502c10541400c0038040013540860045c2011601001c10f21100c06003455020803040c1c0c02d507021569040107400c40d4a542c04661901501c6166000341000201404d824440c00c8080c040d0394940903450440c2a40314414011100c0c141820342499440f61710038000c0403080390070900c915895003080400c0382c0868038241d0040801102800162035950401c0204503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 376697455 1250 376696205 376696207
    0x20120061308091002010b0909300f1804050105040209010c17090d05150c09090a0b0316090b0112050103021f0522050111060106021209010903060e0102120901150b0c03 74
    0x3160384038a18007036213040b0301d90000503007040c90800700900080e000707002c81881c0e4003000c2040c4c009405000601e040002030032062420f1000f801e1426100d006c1c20541c81094140841d4044c40b01c84001d41e02e91541105460411099880341c06210603440b4000b41180130401e42e0401d003001078440e4200480c0303180701c0c0942e18140070401000901881c51140b0a4425920100190040c0d10b0242026608840380c0c00b44103140c4803282c004607081c01d40c001d00c4580e44542c0c0b007800c2d03125614103100c3d45641d14043c0001d1001642c1703500e400002000c0640c0000e000405000000e51407001910509041c3c940041c02d000700d48a20540405a0800e1840318104100302404000c20700d240f000d00010000602c01425013a1504100006280400c5084028031030384c80100100700c61900072070815810640749029070369481544005941c901071075400180101c0c0340c11000d03000e456040d800350280b8400050404020388414028a00340d5502050100d5031280a0200b0412a2900e0000300900c440d0341e0292 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 376698705 1250 376697455 376697467
    0x190c1d04021e03030429030c130e090d050a11060f010f08030f07021c0b0901020a08090607121a090a06080c010903080409050601030b030109030807030b0316030206070c1e03020120061308 82
    0x41c481640023520002003031040481c5800f51a856160b40601620440310b00c810207181c603a400d55560103007220b10005211000400b44c0c401842030b0340d100c1e0550703a00b000300c030558240340751031a402040900c12030171540c0980e02c0101d210403021040fa0b80b141e01202c05142000502d400b04424028003400012000140104100020700508280c81c072a4051000050720f0300240c40d0048c24903407000709040542d8000004100c030040c1c101180400300784400200040c076000d42c503440841c50b464030040541c132961070700410040e01020303003007482a12211b0043d18254000d0708015600c4881902004060070820b100c188081000c40c0d02c002e60000b0f05240c04101480c44001207421903080d21810b800182d0047c0420a1389501405410364400e0103400800c001844c440004020243c24000203110700c0300001e010040c000c04030080d00241c0554035044240443d41d440038000b00c251444120b020500c0500c5031448030b59001c551406d1030707030341c500a0581030f41c805980d400d01e2203c07040125403400041c019 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 376699955 1250 376698705 376698779
    0x3090705031006030501050c04030b130213020c03030406060501020c0d11010228030f08010503100207140f071a0301030b0a0903020708010213170a0302190c1d04021e030304 76
    0x50b012185042e1640011454218203209003540d40062440780d18810420041001a514109582d80f007110120103402e41c190910000d030340412401c2e0700d454024004501c3c080c02e400c01000450080780310300c404201c0c0a0f5254016a00e4440d001c4c07000794410022810f44012a084018001c41440b052068a036128817800c0e404880103910191010300d540703205010810107800c8403804940f100c250a14100e84d604d0507000a680e50703464407442610f0394010130341c10100000501c800010091030800c1e0b0f02940540b00304195038181c603120300c4c0c007050107490040c0c040043c40803c50b4142d94210b20714810603590300e51b50402400c0306410480461084400010700c10f0028806042240d0098140b0b1550300d203890784200c0d690b0a04a51030009401c5a9001c0b40082d4000400007654a0700d15940302902c0960301b0082c140c80f40c80e90045003510110f961000030900b864082c64410b920840341b0442500b02d41c0d4001d2801090007990343e8143d44100018802000c4140a032200a0101005940b4060107060 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 376701205 1250 376699955 376699963
    0xf060712030e030304030f120e07060c060204030c080a0c09090506130302031210140301061503050c0d0912030c020604050a11040e010e010506040b060307090501120905011404050f0d090504020309070503 89
    0x5020346c00248100b00f200303541507000e158074000102c2501d06220111b0000b0195444584a11a11051000700f5200b20200049278041c3c500030b580250394203031415500c50400c2d0f100c0400c01c01c12500f62030b2049000c2400b45051003a000300c00e80240003000c075541da007040101005003180082c0c1c194070090000003500c401001d03c1070300ca14031440226042c5071406808000c080c00d030004051103a41040414000001c03182030813a10340c2040d1402003110b0f140d0245c190024880c3c500302d03103003490801d246403091020032040002a020b0544e42005094114202240c0760182070b1070003403240c0c0010b40154081100e1511014290314000c0002850011900140e07003124201060000144d44800c00c010680c9400d11440710400c0c01603642a00d1803600070030041515885002d1a03052086110140e140500d240e484072102c0c55003d4020044448803645200c0c0182d012038003102c00384141c8094600d03c4c01c0c0800d546010310460b842d001c0307016080900304000ba4200802c001290b05c01c0d18800101d03950204 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 376702455 1250 376701205 376701211
    0x103080717030405011a01050a0c081303050703050102040816150c1e050c0f040c20070512030909100f030201030207051005101a03010e011205010902130b0a050f060712030e0303 78
    0x1078802a500b0040c5065007801b0a21030520005100e58000300703400401060315541c0c00060160f50b606000e0301058203014541000c1d10500c58035201200b003020560040060b1880c100840c1d001e8226490041c10800550080c00000c64007650034a007803901a050894482d8841c9400500070b104091500314106496001074450354425000000c040c02d1042410900030019074051000c4c4418a401401d6000103269100e070b940313016031030810495400e000713110207003600074664000181b40800d101d60300e40007100090310603014030010401440a00200104445408400c01800c4d0302d1500158025040130314246c51a00600c11010000760451007103511840504a0050425003000e0b000d00481d22240c075507094101c2d0030030060040c00240c80b00340b81128085000f00d43c41800d6490414098a00c01200a4011606045901c2510b00d0f9400c001c000c03800c03e80e090700c0520742d10010002884025500c0319003007041000424007103011030402c8000c41200f81008500942c44850740c42c5581c0c021 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 376703705 1250 376702455 376702463
    0x304200604050405091f060f08030a08040b070e1302030a050a1509180803040f0308090109200303130806070e220e0f1f241e0b030415060b040b0301030807170304 71
    0x3941023400303c040d008044101070f044d0f031300c021401c00c1403196014140c184c014001a140a890b00300084403188078400c1050060341c060135098800f9520201c04011350426103c0c070740041d050030300081e1002140e10615400b602c1200b4182551490668400c1c001d01d034000600020041c0443c10001180301d410007580140d105000c4260000124103000340740550240090100d40d0403d10b1003408680d5034030004503110202c0305102d040003600000286180b040f010072062601701c201000071640008901213104100503100c5400b405800030401031031041c040c1c60840d100d0705074103654402c0030b02c1e90301c41c80c002800c0d00c0450b80f0090311959540d280520140c42482c5441c0f00e4400644924042d00502d001e10481d6aa030203104201c00c18400b01446240c0241020441c0d040e854407801c03240004208000e02184089c0c0307a8034102400d00700702c02221004c02007407841c01d10b1030001e4411092001c072811905401c000390704603400c56650a1303003035102d8201680c0000030a8400304020b649c910080d4055881 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 376704955 1250 376703705 376703711
    0x506032e031704092703140919060801051002061909020d0c0f050405040b150118031118070903060c02070e07080a05070f140306030a050a03050304200604050405091f 73
    0x10b0088102c09845c090310b618030039490540e201e2801031010207014044180d00d81020100404402c03a208103031300130610a1039010a00159007900036400c07036468019070b001560b80c0b4006a894005024183c0517210305800117034050000102e02400e40860722860480a00c40800c84038401e130001901d220b1613207426a200e695a540401c040e59800f00a03000500c8240d405000a145c07031303114070178040d00090029030904070080c00e056a0341e00ca8a90303160840c00000420510700d0f16401c0401c42003800456640c0284801c0d0313240d002c03450102c01131503c11402ca0303495100c003d08558811020f4440c1c0799803441507204e01c11000c00e8a1084000ca1486001d940da2004070914001b640d0409990018064000303201842c3c101301e05495014000d0b070315546841444035500e0300d0303a801080c45c084c00c40f070300986030f406170200341801c040c1d000000350302a502542e9103905400318401003040d1103881d80403a980c010003c000030402420300d5042190305c50040016150100c841a80580c15a9a52280b401c11255 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 376706205 1250 376704955 376704959
    0xa09060e1006020c06030105100e0a15020f0708061b041505030a0b0a150c080903010e0d0215010b1209010f0501090605040c1b23030c01060f0506032e031704 69
    0x101001c48200202224401404030002010204060344418005c6a0143c0034170b026007045d050003140201c96201e0050080c0c0320741da640da0a2081c2082c0909500001030003010502c00d86150f0010b0640103a80f01000a0015604c603144030b80c0740c0d200c0034804401d0f20141400b0000301055031000c04e0803d00c44070381b281c03580c0c0c0c81c190780010101d60000010034071031014100140701c4403201c46001a10b404c1641052040c01c4668100014580600b6141c25855030034080307000800e40c0d001c40c072005082d416400711000c00c40e41e02c4c1c0061070400d00f4060701c0705a4000b03000c240c40f03e15651803855008070100f00002104594500d840060719001d03008071039441d841c1d0b1410003050a0510450404d8122458100c2c4042d4004000c039035002c001030750241c4104039880b640e803211018800b020307030012549012640d0360010502c135280030f01954801c241100c102c2303580c0040c050030000100c9104148400300d5448101d200d80307082c090f0f0210b06420800b0a03010300008800121500f0303260481580f55852103403135038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 376707455 1250 376706205 376706221
    0x601030b0a020a120c0210020c100e0f0a08181926061503011b1205071e200f06090f010605061b0c0a0306020d0f0c050d0b0a09060e 58
    0x21006091480128410009002c2d9242d00000b13032440c1c46090040410f5171085104200d14051981030040e02c0244001503c0c248a0360010b03042e034106404040511030b100d0708145064442e800d4003640801a08040d00e0007000620b2080104420044061040010001c540114080500c95000d07039000081601092011942a2040b91030343c00710b14600384002e41084141b951200b074003901080e040075222040380c0b0281c0e429000740b0115007491007035401000341041700801003a4601d4104103c2850b000c045a0032603ca1000d411000c1c1410341c00b05003006256a048074009100c0360388a24280f03900b000320410b04418031200c05548026001420300e030600115071801c0c055141030b0041c2c0c1742c1c949601080b01c0d1b151042918161584400070075500603605100c1030809a8200c07a0541c098a5080d010040054643c050407400c440541c0410034001c428606030111205481d944001c6a01408802c400355501e400c00e02c40048090f146c0c5141990310103000c3d040d11441d4005040c061928001c0003580 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 376708705 1250 376707455 376707473
    0xf08040603051f0819060212070c15021801050304020a080304090e010b03010c17100b03190f0504021507050a02030d09031709060703030e0c0316060f05120105010806031509060103 79
    0x24070f071a40060740054642180b0307030307550011a0b0310004502103c030044010b10a681c3d05540d809800e15030031003010b10384000003d10002c501c907000c640d45990504c4000030880a0710a80300755104070400122a183c140d0015696030700014002c031792101e02030001203826541800640000c5c000d05401081d040c0c108248903007505c407980c4030340307000307030700d0450f1011281d503110002c0e550054200c0045501c0c0d8a401c0d40041c048422500124088600042405441c400d1b400360211903c1e1007400c02c100515140e0713001c0c8140d68058030701a6100040040040c10b440c4090010301c408e51143c011629003550542c0860300b03040707207096903401040581c80100180321281d44103003480c512000b24546454080700c000707111400b42e840040c08142d0350b100309071a00712080201071242c010040848220303010303002c1a202140c500340507050005e0003000702d61407141c4c01142a00c04102c007240081c4126802c01004481c011001400c45506220704241da2030b1100388850340b00c5c02950004013074103c540c19030a0036152 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 376709955 1250 376708705 376708741
    0x1050a06120809010509030a051506042a0e040f06032003060108150a06080303090a030e060f1603032702010806100e1509062a0a05030a0302070f0804060305 69
    0x1e141015441103000450201c00c45520078003d0038180e450f160a43c000c81d18024010760700500d00d110745041c25020603044405684107400c02c4a060201c88111140c5072543d0400c91400c0c4e40140301050401e0105003c1e42600002c10b501a20000d200c0400340c10300740903100254000c0d034002201c0240700701105c1d041504000403400540050580703501d489003050341c865803410000059400310b00842c2080d00150010801045e408040303e4803800c103000465140c50300039034203c0c0442d032040399403030036414420180c8910509184d101c5d401c00074107001c548122681c440c4128105980c581d994900d152500c000503d010036a0a90400980c07034502c005000e424024111a1040c0706810462824035840342088240050640c0c21900e0750040d0310811003540541148258013100101d0075a003885022209500d174142c0543c02c0d0340510781c1003c16031307440314241d60340900240c20820464443ca40240c0091000c1752264a4040e07410f48148c6400300c0603041a001040020307181c0040c8081c2c641e030101c403401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 376711205 1250 376709955 376709969
    0x2702040c05071a0c0f0d0c02010b0913080c19080a030e0a210e03010507030c20060732270a140d050601080c0a0e0f150d020d0501050a06 60
    0x101d45103264444148800e080c0d03c215a4158407440020200c800c0002960b10501c022040103440d40c00c07039101c0e03d014044500c2004c00540c03a00140302590318218916500819000c0d245080303031811503c0b0f400c01365000401d0800c1030720540a0a00c00041c8441d10360890902803041c0301d860b490625001800d9880820000700305030300511642001c12001d8590800c1c10b050740d8602c0101881c601810382c0d01d00442e1681c2589940b1781020080c00b07540640061401e101d099446440d426119180e000e10740030344024034903641c0d00c04e07400161100e0140104411008800d0b4041d0003450400d60202540420446143c0c00804046402d010300e42d628400041440d2034001401d030400641c1010882d594180e01c12402203243d02c441d51282d5881d000c0b90043e1880c2c1020070f42e00c696840e013100950710b100300b040c180e000c0c1a014000044c10101c03054064000d411107110340341c064690b81c0e003030754011091003e05a44401d10b880c00100603036540d811084124840d4001040620700400b50300701b110300e00c0e8003200d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 376712455 1250 376711205 376711207
    0xb01060503010608061201090213020417060103150b01090e092404020f01050d110c07030309060f0801090b1512060112151e08030a030f05060f222702040c05 69
    0x3200d03d0340c0000d04164083d10565103502c812105000ca140941a0800041c0d0844004003104010031100d40050040d40d03100a419880700003c451240d030303134010921004d0100000c107080580480382d140c2054050660524000362816110a000d103031441050390040704a604c0340c04510b0080c1200c0c080381c0071100a22090380360702d01e003e802041245401d9012039042100001c1c001c0920b480c260301203698031044c104102d48441c00300078075680c0d89031603000a0380419048000018a01d01c1805107450010f01507a44600c00c3c3d02c3c018640001e003585001c00d40e48801c13401d50030302143c00010040c10702294504003100f483c2c148000050300041104080744000c6041149400e40e1015101040080340c1c011401c2480c1241120320103004807125810080c42c038000003c0300d0242c1e43c0d00d80c00c081091840c1a8080015072140410801c81d100000f11075a00000c0c204540c0a52900b1003080c01c1403008258804542c2d1401042211010082071b10b400d03190740d800c8081403041d070a0030702c201584443c0343e013005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 376713705 1250 376712455 376712459
    0x90a050607080421030f0606090e060f0604090b0f040207050c120303070906120b030a030503070e040b130c0e06030901060f0801021e0d0b06030f180601031e050304030f0f0b0106050301 81
    0x8000400100d8482004e6942c11204103815107100f54460440b86903c02d17420004582c440c00b009016010600c1140740c525203500119100f8a0003283d050040103000385101d01d4945800711320009000712195043d442210741300850415140d500003032100f544140041d1108924000821030f10302e0902c8155803c81c0d00910403c1285504440180f06807546400c02c915016981003040d405804c4091213143c06000b606800010560000080e5005c0c0e00c050712220385210340c030070030f100c11030341c0f58400d265104015108026900a850b440401e5075030307880c030740030a815a246000c1422070380291030300302c840c0e95205c0041010000700c00503800035040c0079000303526113400342d480f560580501741981c0c1c0701920700140411103040a640100c02504025142c03d440b4a4080d54602c82c0403004c032012111240c84194030b0f80031860200740541a04d41c070040f20304c003e140d8610842e0b64000c60707400c12140c074802000048003040071540003c01252081041c445407410f540703001d0140c440c043e440f0344d09000c001c2c401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 376714955 1250 376713705 376713713
    0xd030f150315021813060806090303091002070224030615090d110111010908030601080604090c06050a0c0b0c09040e1c050304020d141606020703080d050901090b090a0506070804 78
    0x40b5103003482c421100540c0300d02241c201c0c01e0350010f400d1044d40d406080c0e1102c19070b584d00641c10110031074075042c00361200e55440900c2d0540300c5c40304440140080d0009201100f1200050b4003502c0403600240611001c111003114151040503c6030800000b05000b00420441d46441501c9400c1c0c12505060035041180450205002034440480145003580002c101d00c81a48500200403243e03d10000912072209503080004440d0b03c20786150340040c0ea5440043e80908190181035401941b018560452030b10f00413080b0b039540c101c5c00302c603401c1041646065001c80c0b41381d02201e006001d90480180c1e00e04040081004403507040c2c0e0100c003203401c503100c00b9610030315588003850f48468130f08255a0320b54880c030002e9a12401858020b100c4031b400c1a8090821310002980202045100803030002651941ca00ba40d42d00b58921008103040c804010400c85035205810083e0031183c0d0800110780a40c0da566084100348040324503a00caa0300845c203010a00c03c0070042ca03038100a45080c00a80d604003525 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 376716205 1250 376714955 376714973
    0x180706031e0b1c0b01090c090305030a0e03030904150905010611030313030c0204020304061d01020c030a1107030602031609050402160602030601021c0f031109220b030d030f1503 78
    0x31950410302c0e074030b61441e030080e2519420504440401c03901d0551101c0f10b4904001c1c1c9200030b005484070140750070222a03425000d040c4002c2071f60740200045003020b80d03041088a0004860304a682c1600091085020310703104d40c00741e200c2c541c0304c000304103084d10b0030302c0440821910141c1c0f1103001c00caa807100001181c04007008403070308082075600300010a02a4242510320080068009400510000401080c01a00e41c4400d8807401c19480045800b069011502c1c00d030f004141c00d80d20542c0003001a401000e00400d04d0850450240065904c1c45a9a8440303c1c00c81e0000c5842800d50700640d808142c0040d401807500b000b0f4001144c04600b426130300c120a00340c20f40099801080950f0000110744142e008002980c00806001c0345001101c504281c02843d549203e20720740e0100e4108a20399002c0c0d006a425120345a02c00f41540088201ca20707c0301580b050305101c11030226540d41989822034509004e243c600e4400d40c3c4002c07030454000ba03401c00440d0900000c500684070f81c610280002101c0e0a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 376717455 1250 376716205 376716251
    0x33513080c1e01080a0213030809030c101209021314010e0c070b010302010f1107090b0102010c03020c0a0b040f060c03090c0602060402090406020906090a09150e04030f08180618070603 81
    0x2280000240c0d4450b11711000901c01c8403030b2201500c1c0350200010411540340000c1440000c190305a442c011050428420034642e001d42e90804100001c0711084030001a070300001c81c40340000c00410800c9400b41ca00821a280700c4406003410100034011320503c440000d000703400c020f1140384986080e11588407a000140b041c00001c0c1084010000680e0140c07040140340c0340060124103403500141c1d2000e03d04000e041c50107102e8050b500b44904c0302e155501a01c02c1d00c040441e0503000e03103245401c8d90740b1000c032588002c0c003c6511000d903056000100e1094410701d4006105524009220001c40c00d080301c11840035440001154840760411006031141400f0b507411030340c032500c00b50301c600701c2000003101e9000368204076801900c01500012201c4c400d800035103030755004114a5140e41d84907480651528005c0340e002e0085002c003000c04ca9094800c1c041e041e44002120b940701412010030a110f42019800c1d600c407960880054100704205a040c0300f080c000b000f283c02c0401040c1d0105181821043c3d1503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 376718705 1250 376717455 376717457
    0x31c0b030c1e04050f070c08160515090610030203070302121e06060109050603041a07050c0a080301170a0f0f020f041803090609080d050708090411180a033513080c1e01 74
    0x1c00c0c02101c0603040300040701240c0c0c0c000c060307440d44207505080c805071200407030345a330052040c2c03408140681d80e20407400c0140c1350084c0141000d10305503000d01424181d54400101580300314020030680c00c1313004c00c034050610250409080d039820101c0004000308556000507114800800c18840068001e1a0705102c1188000c559201907440810a03a064001c811135440c0380c2c00b520604000b000741070300055050340c829610000d014201c40454655400010100401d00100c011030007010031440d101c0c07c82070303900c010912210147c8a201050981d501802c094108200d1494020101078209100802a24091609032122840c03d10001da43c0c0411a9030102440f400084160601c40c10310100d54140e030021788107000400460702c4a00d0242d1100c544560700e035504080300412482e00050440480e6040350504680041e100700c0e851030154940050318850780780c282030380354421f02c0b0030143c682c040c422160319001a152549460400307100211040c03140071404034503040003e0402100d019040d003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 376719955 1250 376718705 376718707
    0x60b0405060a050405090a06020309070602160305030f07080c0102070809010e030c03060c090112110c07120203060411131109040b190902030c13081e031c0b030c1e04050f070c08 78
    0x5041c4086040003401c1fa07015107445e00010400120794400298801114816070848642030452031454090485030300000f0315a410800a205900c1224030140c0041d9008d86401c41c9082600d10a180c22030380103141c200c27001100440c144c040c642e00880d040d03880c05011740290551001c0140002c0d142c03080204a0480e00740e01144401d50341c0d11030300340c000d1840f180403006c02580702d0400018400307401042a0070b403144030b054000b103010080c80400c0c82e48240c2c044c000f0485610b5566034003500405101c0d4945c1c100c2003c5000d1040a0428012040306641c0f880100799203445001c1444195502d0008050003000a8500e117112805911058002c40780003c02c01a240e0300c40b240c0300384003440b400400a40080c1d0313450020030180404101e221421007510f0f422096401c04811858817809075050f0542000c401502c40142003c194200910b60b000040c10740b144d50100900244100c10340c801000786c4000318001030106400c15202e9141c204803205d00c054124986030310300600e003849080c002400444 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 376721205 1250 376719955 376719961
    0x150c060f0a020d06080c1c0c0b0f070503070b010609052e0215100806070f020307110a0f030305031906030f1401060e01030303091208090307020f06040b16060b0405060a050405 77
    0xc29a03058503e00c035a50740d42480002c3e503d8000c3e5594040102e10640b003070880464404241c01031182500c0d2440d44110307010b0500d4500b0300c80c0031568011094603100386030304000d000d00144080c0028107640307100d100060083d50400800811031849074104501800100e0800d405c00c05a2040384d0720908480c40c588042030781c00080480c240807032070140000c1d445d00c0c2c9080c0491401900d140c40b098942030030840b81d40d580e9442e0100e5418030307074817410b0300560000c1042c40003180101c08140c07001400a001030031216503070b009000713411210380c1c01030340084c101109200d40c03080039082105003505a58403d010450460319015011003030b500004086004032101d86680d09030a4100500810354800e000300305696904015020b041320520884281d00700c02e803642130180c020742045d4000c92108c00118100a200e40c24046001d04403149141c1c84141408009011001003000341280c000c84142015021014030780f08060321031104500c0e10a9080404015607516110b18a0044075070032100412103403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 376722455 1250 376721205 376721221
    0xd0209040b030f0d030506010305060a030206130b180a0807080c120724200c1017070e0a090504020d080d0e120306101125150e150c060f 60
    0x1035080715940d014010b80c2071070110004003103104200d05056860520142c2e4441004500701c400403180781c2c0e0b0011340300c1400d00c00360030403070702808039282c070154989081d9032240240070558024801c0011382cac00c0070010b824400c0c288561340000800410300103082203402c000c482c98481424540c0305014003075030700d0306640b001002c2091500034191652200344030b00788c428507102e04944c07010f03589012981003003c000c50307a043c050034801da5101400181010300c0d4240304001b2040111140c03041041142c80c514801007800c0000c0034007035a07041c1c45041d5140310000611042d02c6142d0b01c00020a0300d888200005a01c9068800e4a05035100f9001c943c0c40c2d20400d0108010070140004942034800c1c030002652503644000103500550045840c20183c020782207013100c0040010030ba5140c160400694024108869070000040800d01c43c294110181c482101d4005c00d00c481030003400081c880c940c00d1641e810b003001201d03040b070040920289031403a240703006951902f0241100c5161124400050071031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 376723705 1250 376722455 376722461
    0xb03041a10050406054e0a0605070f08070309021813020a08010204080307061805030a090f0905010311010810050d0602090307090b03150c2a0f0c060d020904 69
    0x14400e918400000e509200041401200041c040c2d180030b1881c0c044081340e2490100711141501c0c924000c104900c14041406c503410401e080020401080145030480041050740c035a02643e00116005050b46402c0781050825103d015003030343d09100c43e80c1c0b450350b421035201300665403094090030003007002015480820301c0c5091b80c10300f4084141c8260207010658280107140c04440b4000c4400d0074501c4d4482c06030034203d00c42d0b03110348081c65004018203400944183c101d24200c45240b4100c0c5c2500c0324a44800b42503610002690b0001a52294180050950000000e0152034500001c0005606540e107034042d44040d0050302e410301c5002000280f042409840b064041e000140090010740f139513151150207500009601c0d0720070b00401d036012440e500c20b40b00d00080700070006d0040625200c2c518a1020035400030301030481d421010002c2900c0c600324015100302152003480c0c00215007038428205804c08005c800c1340c0103142c11020550706695210002d407020f0007101c1360010396450043c0001401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 376724955 1250 376723705 376723733
    0x60604060f140715050402010f0e03100510030804060503103615060207080c18040f060e011e0c140a030c1e030623060a050304050a06060314070509040b010b0304 71
    0x400c3c12045100303c20841366400a038002d03407003a20b440c3c0c0c3c812230310710050720500391024546816612000b41402c0d490f0244c0c11140d0043c3c1c0321701c07851204039140d0301c5840860303019400070800b1030000402d01507641080102c45000703164030b0300040c45985103650030140307885000000010051019164020909540d03005d08482c80c401114800e003030759202006511a0000c1c460385199018503c2c0741c0c1200c2c200012600a0880b18003101d031072696803541c94100341010000140c92460390f986103140841404d01c501c4003055914480304414150310420031054078090400e000400006480c10403c101000b4181d4004600505001c00c4202e610b203000c80f46c2110661100c1c100b5030315800014071154041c0e021a06484452400e0419485081801c0d00c21201103d110781d0041e608004035440184214061034126114000f62a40c200031610307100c041c0c2e199170b082603c10502040e4030b0415010b040140000402098a516840d0716041e00c03032040c25070741445024000840000050300b0489440b4117514 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 376726205 1250 376724955 376724963
    0xb1302130507031b02070512010204050a1a040b03010f030b09010b1e1903060207060e0a0c0605090411070506060a060e0a050d02060c0703030504080610050d020f13091a060604060f1407 81
    0x11130344080c0341c8000d5449200b84a43c502036000c08121104600040c0212002d40380e0284c00c4464007803408410030803d07041140454800c0b40c0610001c100441e12100444c0240b060502d02070740700c2d013541040d1442c40000352115025030b152620200c00c945031101c00034080140a00341c19004100000450802c5010341c030200e01c40d000b090307004010881d1030760203844198001c02080200c0d881402809a40c0d4981c2a0003501c0c940001c101000014410801001c110001500101d04416822031290b029088a40115900c3c0c00c90f0080001d1400c00fa40b4880c001c000d40c0ca40100c80031451070208110542c14040c40340078100c017210030300035074a07000d0454280d80700c20313002c480c1c0e856580c1c10001c00a81042c001d0017040e001d800d002c24220090000a5016500000c1c0036001640596007000640201441825008000520000e12804141c45200301440c040d1304429555810401e4a205042d030040104d0301c54403050105100452b40101210310142c0700f410082e5940a200003920528012958010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 376727455 1250 376726205 376726241
    0x801020a0206091905030d020d0f110c010b01081902070809060a08010807080d140306130609021201051f0522060c110a180f020f030406090b130213050703 68
    0x501000ea0000d119031007085030f00160780110a207031a4005000100303a8010b021a80148031180c04995290300074100200d1094001411012001e40002641c055101c4e00c00b80780f0001c10704141d0000e081c0226003946e9000d01e8910b01b2480e2500a2260342189d100d03c4a0446a011405008224120742183d40c10b035001171040da15400022030062420502340907851b040c0c01403c00001d4a40780001306500380c0d5030151103140c1240b0326201c200480f81c200401031503101040d0400702c203207061380d03100d0b44024014441001d61707180800710038140c01140691120f405500c100144880041321120550041c00d42450700f80d90740c200003c006500c000b501d070208090f0300c403000000145240c0100c0f160b081e032480740840901340b040765800c01c10003080303a00c81c40c410141c2040c2c6030030f01500e280d80000f9284100340801801c1481c00016060305401c100c41c2110003996650750001441200e10b002c0b6804207008511289800c3c0e150b02260200c1d004e111b4416282c0e45800205903050300903009140003500c032403d86 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 376728705 1250 376727455 376727467
    0x50d020d060326030a240e07020c011d09101d060f01020d020706030e0307151a030703030507030804030905040c03050103060b0d0c05090c04081c120204050f1306080102 74
    0x40081071144011038642140f00e050f02005a40551041d6900c14003821440c25580c4d0b800c42075015145011185506410207441c43e0005031000c580e54014151605040d5010b160500340a45880701844800d0b052050440c0810807035a0b00c1d03503203688006003d469812140e101c0c06114041d503213450b00300b81e0007540f4050b103d0035400010841c191060004880c0da0212001220041e42c03280c0d1203064040060b0041542444076502940011942c50110000c491038510903032030fa201d00c02d01260796a4503c984900c1d15100e2412802a41203880d501100505142461998040d00b40e00c01e0b288014207104046000500780350080c6014001080043d006020b010141240180100b80c2404202c030b10f503103403ea00c0c40362820807460580210394890000312400c0d05000401103007000007040e520030312508001c08030729014240f0100c1c0d1616440314900000704041013002c0c1110400d01000703070007207106000c10003040c0d80704040911180d00580c2c852191384100b030b61a802070b060903040510658000660 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 376729955 1250 376728705 376728727
    0xb030a0f02150f0d1d01110903010b060f04140307030f0317011e12141e150415050a0b04020406020703110901030b1b07051204170715030c050d02 64
    0x1103904a14400c503120000c0c2c00821080030b895000f000d010304602c441c1400200442013042d4800380c0c402c040d40f0308080b002030380c42c10034030309554000c01e103100039560100e0f0507182c505017401b0301403020104454103403e10000311074401e800d008621a2012070000e00c0d10840032038800b44080c2c070165400c55040c02034150340e41009414001084e0400c10040042b00001403040e08034164107201e00459044e9040c070a1400040ca8404804400b06035681c2906103d0600c44200803c07404100301c41c0d044444420b81c1441c1b8440d400c0c41c0441848400c41c003010820440092195220b0ba00741011313076440052591181101503004003d40c45060390050b01c0020041042d036000104901100e200341c0c504030a01486105121154a084c4001064001c1c0e09000c0380303280485101119469410061031414440d80e91682460524454510000c100c8001000d102800c203c000c540782e016000740c000c044192900301e03441d41e40300c9010300034001c02d40d4800380c1c07914140c0b0800854004180800c420740d00d403000144 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 376731205 1250 376729955 376729973
    0x150e07060801080d0309050c1216090e06010902121308090307060e03070b07050601060f05160c030311031206060d060b0f090a1703040306020d021207020a060501060c0b040f03030b030a 81
    0xf8612040c072070202c101e941d040c443d01801130ba0a07404006051003c41d03000038402200d0355800014040d010f90380400328258040342016008203070403240131450f414001042824500182c001c100d4032030042040b16410590195480d42144443d0305804985609050000440c050203003910340c140651580003411a50216045074120000c03410765225554600e00a0182c0c441c1c0310004000760070010040201e24021482981560080d00b0040d140c24000201c0c81402841400103c0320303485040c00038401d055100c00c00e6040d045111005602c0e1090510481d040068010007051003000c0010780060800d00030b070480002001e4011005484000ca40014211500420b2889005042040e00081c100044038000d503a0990300c04051450207086464140207035119204030340c84503408100314040e00d805204864810178003079010f071010349410318100341079030300607407000003000210803505010070311400c4001d03007065100002c603000103203a2500368080c1c0403039442c060f03140c02000c4000042c024085 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 376732455 1250 376731205 376731209
    0x60e0f13090c060801080a0308010e15060f04031109042f030118050606060a12110f04060302031510120b0307030f0c150207141e3a0b04150e07060801 66
    0x5113640289a88603001d03140d035030b000c136100030740001c5d00c0f407004124200c5408541500071f000304c00d2072580b15500d400032521035400754211581d00b00c800201042484000e50152580e81380c1180c41e00310070b0410303807070312428101c80c03481c000d203003d180c41c45004070840541d44003283c40e100540203201c844142d1015100f11580000196800e007d0301d07000403810701c0d001048600190442d20742c03d003802d01c0c00c60460b00401e418841149000d03010001d4200948014018000a0016550260f642c4ca000310000640224041c00140104440f08140c640c10750003869511202c60754480c002904c0d050340001038030b401115440a0290301c400c82584051105c540320760300660302e0503a41d00294010101c0d04907668180c41c0f2a44c1026031421804181500d040803030004214001c8000a00705040c2800180d040111314031050740c940410200e220200104070700b000303c0d85180849020354280c00c0c0d100e4101ea420001c1009110342e40c0c0340040074119955078050104002000d080721400d03600e4040143c800f980038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 376733705 1250 376732455 376732457
    0x1120506090303060603040b15090c0c0c0d05030a0528050c060f07023a0807030e060405030409050915040308040b0108010510090c1202030a0b19060e0f13090c06 71
    0x110000303070301007000003c49025403400782c03250745151b4940e143d590104d0f8010b80000000d107224100396440c1e030744d4103002e0b07805880c04c10f2140b66550002052a46010140c080c458041c0302c80041c01800300344044281d070056030150a206a5492412101c41130781d81c4240d0701c800c400301c1d407501404401940a005003210720a40d4045450a441e15218003c85001c12200300005078010190810040b00000d00700104a000307003601040b08010f4241c5580c0c01c00c0840b90080014500403c010001e40c0c1801682420009500030b000d450030b0640341c1580364800ca0061010700d82e2940c0201d140e44204000d94444414100000f0303c09040c5860002e00640003900c05aa0200652002044080044c4195402801e9280701e200d4210300e0070000a01800049200c6400d00110344125801c41c520f07400110b1248003280c3c000188a5001d03030400010b0380c080305402101071074480302880a04e41100e05001c5000d4100c0d41ca8034400d41c0d140008140d03581c920ba481c040c903030a0600410410500300c2802043d5203203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 376734955 1250 376733705 376733713
    0x40603020d050c1008040506010302010507030c0204050a0c2717120a050901170105030316020f0301090507051002120f130f0e0f01060824030a21140712050a020a020405011205 77
    0x4c0d50904690110003503c0140564102c900108010b41c048c100400d80c1e58841d040000c21441160001003c41d641180c8404050746c8a01011000d41e901a4444402c01882c1280040c0303190403407400780403400c2c10301402541c4881500c150940210402510700c015140c980407503507502d0100c00082450f00444c1d81c05002c90101300a0944036501c003070040b416200003074000c40c10421a4000009986010700041c1c0c0c00034015078110016440a00814104501503c01005030620b02018020031403c2c440d82d580441d04000301c8421803440810884041c925200d03112900c80103485040c420701c0758585e03c4840c00000e141c5000078204d0140c0025403280d001488101c40c2da07a642c1d03001342c4000c0400c60b00050082e07000c00382c2110680c1c3c10300d00d241c4a440c000d41104c10303a04081d0b5a400d44100c00307034004075820302403035410b4900c1580300c0d1345c540400c40c441480c2410965180d0f10030890243c55004c05060010100c0c5405103a403003000300200b40c580042c4180102e507134980b954142c1c0100d0107019541402 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 376736205 1250 376734955 376734979
    0xe12030409061d07210507120c02010606020c06030601090b070312020a080109150311120313030f1214070f05010b1e01120b06031b070501151d100e06040603020d050c 73
    0x4017030300d400340b031640c1000c202e0900c20600c071402400500008042c041400000074420031001c0b0b86106200a69001e600001949424040c02915120300501c0803480f4000c100104103041e640460500100e403800141651550040d20302959100841c415446980e0310200300d48406d19401003006048912241c4100010035040d500e002804200340809007280702d0401e040036840c14100301519030940608144e03810001c4580d4107645c005000e92054039034070103192149040c09480b1410300481003045c10103414001c07506076884128090324074050321040b0303900d0300441807120a420031110300c40002c06880a04001906a0a03c0c105803050390780020658030390380200ca800303031084100b40e0038003e01d0981156205140050740115601085046031428899100001c8090003055003001c445400c11640a08043e90700c080e00c4900f0001c0119498214103003c0000c040c1c404010580303803e410851250b903982001305003d42050350000b9000450081500c050100200e5041b50310030301210350042d801 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 376737455 1250 376736205 376736207
    0x15031104020a020601210b09030a08010b040602060a0f0207060e16140d02060c0a0f0f0b0705120f06120706021501080c010f0806030106030602191205070e12030409061d07 75
    0x8002d0b80740d0700c805030f880f040050140d04402080e0500c00700040e601d40036600703529035440710070403000e44200d0b10130350005c58050038164115840e2030240045840c0c9600b001c0c50061700079900e240181401751159610402103000310b165404a030012500072005105208100d65099030b266030b82a004101c0c04401c0c403000c10301088100e2042c910980c000c010f014800c0154080041c1035010f680108024403c0d440c001001542030790301428420300814003101100d8450070328a40895006100d001005000c10030401040300c980c240030303007080b80030500d40d003d550b51101162240062031080c80d014810f10b50002407030340d400600031071441c0d03202c43c8601850b6a1080c44030f96842050401d1404100d080805c892010320403109907612040041c00851410b0703403515503104a03032201c00c00003542d100b030002e03201c0e1450b0044803c1a08800c0c03403100f00a10300d00b94000070003a600900045c0e200b0452004416880c460800c10381e40a800820010030205036180c5152142e0b10014546070102c0e4400d1000030350507 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 376738705 1250 376737455 376737457
    0x1504091e02010f0305100b031f0e09070f030b0a02070204200901110607020c240403110108070c03080a0f0e061003120215010b0f2a01060b0301031110121503110402 72
    0x56012540d40140c240c188a0000802e0700700a00b006d540b070240041c0c00327a00b544e00200d200000c1904d92840400343c104054840d0611205411001040c00380724410400120103407002584504403c20041c1c68035001e100003009000306040c0c2021101c8c0c40403c462400d1800e1004021401c002d885524640c04c0c10701038a03484000440e0fa802c0560002c20740201a03050132030b1a9001c00d85288d1869074059503100c184541c613080307a08161125415041481020350300604860b81040304d90400160410321a500280960002080b11110980f1800c0441150840b500014103811250341507822618210710114604043d910041e0b441992071658540a20b0012803117100304180c0c0a4520141d0382402042016179200011405280c8003c10018180181c061903801c40c81108081d15070041c072034107080300d0170b45501e50000002d610b420801040090312401c1c0080380404265500c0c185030344100026a00345011010712001e69041451289101081d0a404000d07a031041c0b440107005012036084c0b0040f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 376739955 1250 376738705 376738711
    0x1b090b04050103080a0503090f150a0e0c03060601030c0c081c11040b030a18020316180606020a020d0206120c0d0c0c030e040b031002040303050903060a141504091e02010f0305 77
    0x2001c101088a175103000c0c4508011980490f9280841d90580d00307040040d458115501c0da9404800118000c0c0400c01e11b01e40a16600342c00c00400810240c0400b01c0005e0300d841e806485036052541e10b90717000303890a018910911001d07401c11866a11507d040000404514100101c40d0800d4901481c00700092031600070346d003d03262802c0c1c841b81560741c2c880741513008000d8001555080c8007400805001079404004180010188000480425162040b6402c210810800b0290100d0a0141c14842c2690000301e01000540444100e200704007180089100c500c50b08009004064440c020010740700c45c031100421041d503040c4010043c1d802001d00c21504801007810060000302ca014400c0d03800d2400fa001412401300040a46100603842c01801c0120781c01a8012070105901144818480c40c1c20300803070307612580c40c5000b800704110b00503000514050013046000f01c2d5035211500d035a10f41744d581c06002010303800702016540a440300c881d0000b10f50003400403400100c40203406083c1501c030b80501e40c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 376741205 1250 376739955 376739963
    0x30706020307060906021215040c02010e030d151a313c0603060509040506040b1302060a1e090f15050c030a0e030613110105030a091b090b04050103 65
    0x4104040b5941c2ca002520310781406440240d028040030304c160040d0300103103000300031040c05030000e00018401d00c030030369168848a5040d0b924052000482060200884a040c0345c1c6100000b6001c80c9081302891400761030304066101c119040d007c905204440005254049000780311666505401c103032040760f000400c1e880b1801c2680a81d00708020390500085d8004180c0000200b20ba082c0b01e440016801c41e45d4050380a1155003481041020541510a0314040d1005031400c078050324207600c0302070707580601800082410ba5504001012440c8126104c4c0743c043d0700415081c1d6031140b40c0030040110b100d070f42628807200020700c1003808190261450000311140d40820746006c600d090038119400c42c41c4a8504240041044243c01400703090005254100164481210318115541814505040105906c80020080c40b03e0390200c0c290399941c00e00c0e00000d107850fa690790340702511100600303c449001842441d1008910400c000d08107158015230baa41e4001b0040200d42d4800c01c801c2d90000e00c0701034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 376742455 1250 376741205 376741207
    0x40c08061b0702010e01110607030b12011a010c03090b0c07150f0c0303020306010c020d06060806181b130e0f0c1005120a0912020a1211151f080c03010b0307060203 72
    0x26006501a032040030500505040801c4038051f203039030305420050100c451000003030352049082a07602d0591f06c00000c071f0364004001c00c40d101d03981703414030056004a26035074103002001c080e02c0100f40c0b181c01820050460418107517190398001da2401d90700c851a004000500040d080701c0e119a510400c2e910580404039620000c0010b202d88091b0020b6002410301410000110b20107405a11044241d005142c481c1c0f10005085203460304603824450080d201154118140d6102010040e000911811046500c08030217041c0c240540050360855103404c00500c07003800d142a42201c08004984002401c81c004140c0e81c501c603885042001587d1000040400701d18244a011500d9182010490348044144000600c0191644440300441c208000800061f80308145803410000410f140286080e401c0c18540b0500221a0942c6e4070b07168810300511142049c00c001411911104a400c204600b403840410141c40d108c0036000d8441a13070781078190096080040e90400c03400e0005940301103e0035a4051 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 376743705 1250 376742455 376742467
    0x6010e090702010e0a030c0606090506060f0c07050d0303150608010602070b0d20030417031504021c020c0d022a100c060c0801030b0a09030504060e1305040c08061b 72
    0x3004205000c1c2035841107668030075409140c16400c1010302609806915a090880468a0000305841080e000b802015040c02e050101300d40b03c84d07050359400201d0740e801d43d0b02c542d0300254180c41d1002951055900c5210030b8004e13801d00d50103601c0302d100d1840003041156619250b800035501c0003800e10401005900c00c184c04c00503180d060002d40f01e00c2c1a176490201d003d444d4802c040781c441c407001c01c0d180038171480002030008200840c11101c00f1400791100850031460702c60141c000700c8008844407030080d600054602d0001e081d800f60f019511144542c115203030b21100e9a09a40ca00e240c8550002500c84e0307621011030b5035140e0890042c00c4da5080d0301000c2c3c2e503c280080c04598501140500e050204074020100054128011031001e4500c95a4044c4150724609084c0c1500d030002d04042c1015141885a070042544001220151030081c280b00c02d11180c90004941811503440035480001e14080a1104003c14143c8070012070306101e049444c540c03608509102402d640b8000c0428040d000c03c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 376744955 1250 376743705 376743709
    0x1a011403130507050a0602030c0d030b030a03080a020702040501141815040e03130b1c1b0806061b10050601081005100c2001120c05030c0c030702061606050f06010e 72
    0x4100410b00c03030003e88201540e5000441c60b4800150001d0000da000400c01c041144d4007002528a07078a1645001d0204131092000f19845039140381000d01000722100018040041070f404a440c1a41d0181080040d03681d00c4109406000c510000103201c0d001558624041d1380480c03030114003402d2103030b001048034981001000018061110030781c240d400700f40001c4000c0580c11382244000c03e007010a42d0754601c200c3c00d09980122010030003940d0300740350400c0410308902d018101c0501c5031060400c1c40407034407031400040e80d90041c9040f0132120f102907034000f140b5850104140b4502c42d480300050105444490040d00c40c6001141d0310707170400c035607980200030034030304a038a5010700ca9890801c1075501030640c8a20700c0c10207103008030140f14544110303017501c29607020086d14420a0307521010401c000303801c80000c12a200260949020803804a0880c50032441070040b1485c80303a00074406076a8000d07449108805c55400c0070300765030291401001030403006000d590f0922845050f5607030703440c001c8040e00b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 376746205 1250 376744955 376744981
    0x1021314040b0d080403020120250803070f11010e10030209061902060402090c0f090f0f310203010e0c1c11130f050609311a011403 58
    0x60001d078495110941d8150648465402c0c60541e40980a0a0790711030850002401d2029004a243c41420091f000d80380d0000340030400c0c004402600d06030601a0501026000d0020007941150441d0b010010b42c103c10490400303410315580b40308611140700303901c07031000550740c42d41c070f0148940d0003104100d03070907052a21a034014034290800a0806040916000780301d00c0780c068483c013200142c1e0045d414401503180005c030941d48a000c41c100a46442e401011405050181c03620032401860880e00307021b03c0d90b42e804100c00480340050600341d001c0000d50404030503503080240c180400d440c400404c21807030312a4002c8a059509001d04101c1980750402020340c0c56005010135042a6040341a003031440051340101f015403007100c200c46440c0c890704140708204050a50200211030841e0070700f00001c0d210308003076403001807007295041d20303002c04120009450030000c610007080c202a281d50071164401a484a603100031043c1c0300c401d004e40c456005540c2550b481c18100217030541440000c0322944104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 376747455 1250 376746205 376746239
    0x1810051903110712020c0d120e13090b0f0a090203071a16030203041d01150804080c060703021803030a091e03020303070f031b0f020d0812240102010213 67
    0x100c1e00144011594411151580000710b0440e10420f502442c0c1260540c1000040002c05c0c0407100c00f604940d43d507641e000203007a068089014002030382d10a10307041e6a0310740298002c07507a1001c03e0017a05001c0c5040d0340580d004492008034442c07a00003298840c2024440c400b21554040d00038402ca5003400800000c0440500b0701c200003000411455810b4200000440c00c450f1094008544580c2030142014185004c14040300003840400010400a0800d2610b881c4d40e4410342404022502c0300e0414594034858070203407060303074401c0005102c035240c3d056008010b100391490a00010024100801d45c90f441b400101e6000201c035603800f030086210002a200840c41513103e41c40c2440c0d0307640d01023070031500160801c2d2891400844046c081c94cc0010175012554141e224801c201c1c010395948861440494601074040c0302c44054000420020b0011558080707070005d4441003d00e4144090710b03044420211000c00d01500ea001e884095005000341c90f140381d14160300880c0a82003403244940c0c540c1c24 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 376748705 1250 376747455 376747457
    0x10e0a020c010e0c030712051221070206070905010f0e0f010207080703050102090405010509060303040311010c1e030f110c1306030803130614040f080702030703120518100519 77
    0x200429190450300f40302c0d890140752168050000d040d500c004045c10280e86902c0040a00203007650711000138004034402120400b82c0d5841030311480588001902d44050305203400c1e642c84901c0910020725000184584640d5003540c40c0d500e5161610011a0100304088803d000310b580c610200140d80b400e132420701038409040c4100d51780c4560b60080f45d4901401070b4000d84003a513000840c0d90003401c2c50700890b8058a010b507010b0503d410f1020120b0340d0392140b480068401011961065640da100302d00c85403c081e0082c01048107036860322024840750400c1142140400c0304e80740c840303071014011682c001c20420b40307402405120342202c050000c514900702e03074845840d94a81e004400250410040c60143c140a0a07140200829280c0401216a005030b070519a284110400000454107201d503602070750311850032926842c0b030740f02007443c0038055080100300b0040d1003e1903014984c020007400c044807004080710342c080384d5074040c0b0020400980503080021003c221a807200350b04c0c0e40c0900304100007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 376749955 1250 376748705 376748707
    0x80405100e09010f080c03070f0e0a0603020901150813021e0103020f0a200105060907140c01061403100603020d0f031106150109080102211509090132010e0a02 70
    0x26000142d140c403801d0308280840220440c00340144c0000704000412544182d0003042e03610704100c84070391190414403540060203014000a20341901c103070800c200843e80602009845d5031608a90b1580301803590381c03200020300c100d00007624003440d281d0b000003107900038021824810101035000070360502d0040e400e050580030440800344107100c0300144a092160f95420944108800d2003215003001810a000c1c168149000d021040d51002d94641c1c0100190400c1d5000fa42e5079189616140500582010300707520b041000201c4000c0e0f00d0450030404c3c81242912400c4124007560000c590340382c000a500500c44411010000fa01d1820081000c2c1c0642807c204000c4d031214170b1880e1410448401a101403041c240341e00c41e5800001076009000b0010007582048000c48802a901041301a0344045001e02c001090642c8907004d403041220901503c821031030710301683e404d406000050200c000010703c41071084003044156090300d9501d824031440c800542d103007200b9920103440c050608600703039034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 376751205 1250 376749955 376749977
    0x70c0f1502161101021606050313111818030c1209010306030203061302010917100b061e0909011d0a0b0f060c010507140f0406080a1d150a0908040510 66
    0x31406031100b9600d03126049003040d01c020702000a0400c4a545401038001d404034400b03101361504101641d60100640c1c210325040c2605040c58042d600858928903000360703911244070400e80e03007845001c1c407403514910012503042c07001d0b02c1e2503074a114882d6100d8203a001111001e2031740c0303079030384c02814203e034149804a0b80d01c2d281c1e000a414070409903018442040d80482c12411075800940b20340043c981070b603001c2640000500091b4035040390140b08486199940803450513955a441a80c0c4031400124045412170081f4042114950029075110300c94068400009004000503840740c02d03040f9501410300e029100e10140343e021b003142c266010341c000340d0020b66440300c3e2900e80140c0200403680002041504000c40040d014036904040c1d07a40500c020003104124404035401c40341269a030f4a1b00d6107060759126a42c078018822104440400c5111b55038680f040a40000c003914400c241d1500943c01c0c1e00ca024150040b00e40412000f82004000c1c4020080c6141c40c0c0e00401e00264541003840b0190 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 376752455 1250 376751205 376751227
    0x605090d2907030c020105011409060d06020a02010207050709061d09010b09070f120c140a14041d0903160f02040e01140109060501170a1e14040605070c0f1502 70
    0x100000075001c01c900000c0100300740241c0c0350044e86103c81c0680002c000ca54100394080480f4040b0400e0940206190008120f13962100507003c280241c100200315213032401010028041c0d400042c081d5014400c83c0d10200e029103051040700102c4407034640400b0102c80003a45091011001080460b09544c3d45220901c15240d040c1c81600c500500e03600d201e000d107500c0e0f02c0600340c8070320220007c00c03203403500004050b09504154000241020300c1c40700c0e40c49818801c001c561400158280c00319004000c10005045102582060000440e00f084c40c42c50b0781e079005007513507203018440845c41d0301c0000740c0003600421003650814002c1c07400a400450941074bc507000368251034200500902200c9040010808124980306400142200b4a421a90000b49a9145164400160442c20126034590544005400340d0180c11041411410140886054102800c2e0001d9040307400f07403034050030040040c4500d44a49210b0092641c030509100a20031592554143d400340f154001c0d90b4240e003041400440d03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 376753705 1250 376752455 376752503
    0x310f0b0d0525081e0f0103030503180a0f0506090303130206071e0f12032d0e1c1803050a0f05011e15140306010e0705071403030610090605090d 63
    0x10000b96100e1042c941010301d5548400300d0a0360502506813500b80c04d01400d03c0c006642581142d4040c80c0180d161b0319200c03000441d000018294800c40e1003001001c908100105000b0910540600184e890035507541d142136840b44012030b07100c0c0e49072081900010052500e440546240c900a035006040765100540c01500129601c0d01030b101d50034030188080030800008011104103c0ba4034050092400c442c0c0004441030300b81c401c04801825172080d030300d001e038140d9011700b403007503008012a03502c8080c00350600d81d1400707403482400000e0451031400c0703c0749810f004c0807002c41390300c000140702290a68807030501c1640341b02001c55442d521120520100c480b1002c00034a6108154800581c1107054411035804e100b07c1da01210034020406104000350b640402c42c2811120503080d2000503035105801282c1604c0b911000411030019100000403091000000e14410081901e4800150030510001e40c0e00c0321152080200183c0c00300081e070401d040c036018008900780314045441e044651000407101c170b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 376754955 1250 376753705 376753771
    0xa170415020a02011e1b0c0f02060f0703170c160c0506030a0b010905030c010824040f05010e0619090209120a05060403090617070509010203310f0b0d05 67
    0x41c0e448031120070040517110700c01d4140c45200c00041042040702400c94840d15407880e000b00c144002804107030107100c0380c0384000d148035500070060b0740d07254000000349010340c00204064000803600784003100c10780e86981382e807405241500d29441c10586600800d000ca1498a101200d40c03c1c00d0700000541a1508000740d03005010790000441c003d0100d8000602111007075101512a6000c0e902010840e60030042c210b401a11000266060411500020200030802d10505420a151071031421641440f41d000e103058801e0504500c034181c0302d61040158182403c5035203800c9030200101007248415a500820413040d018080f01d03904282002c10785d080c195002001c3e40c4923009142000201035100c00318001904007401c01c484c14081081c0c0c00350030148000c00d554240b0000103201c0c0705981c000c1080d036130f08800c4140d401c00c129646080d103881c500400714000c412080310140c0401c0c40e240003007601080e1004080c1140c10042c00200300d40103020081c0c9008503144006202d49201c04c1284d81d103240c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 376756205 1250 376754955 376754957
    0x90307030c18050c22030b010e041403030912090a030b1305011b09090c1229030c0d060b0d1502030106180b0a0309210c0501110a170415020a 62
    0x14409140c4140c69202c01000b062840c5003a142100f00250311a80c0d1041d01e07020031381d50145460380162000c070980c0d005110341000d04503003d110f000258580038080b0302c41c0324034850071114801c203281030541c0d83c4da804292900411a0072103200d0445619410001e0045021b004004c0803a40f03a0700d80b503c0c03410030f41c1a940f08081034007115600c014031109000d8540002c58041c0410809000300c41c00030850181ca00640e030040743c460340ca40d1425440f410401d140800d10b40c4c010894608040070302030500308142404009400094069a0302d1315000c82e0070041140041d00c0b03110b01c8100365881000074a00101c8172544540e05010047c040b491141001040c007007401d600581e00d504200d00502940c2c640040b54a0398810400103004040346241599011031711414045803130000d0f840e00040d2803980e0b0701c11049941d990305084034003680c492844c4505c240640020809050828103201d068800c500c0148082020318400d460450103503030805d9032041c040d0381d007a04801c0008422078241d03030041d49110 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 376757455 1250 376756205 376756223
    0x5150a09140603061306050408041a09030c0109120b0c07060e06040b060307030213150308160201030b0a031208070309080d0501030b06040504110112060e0403090e010b0f030c07020609030703 84
    0x11000a159030856600b004084009124502d04014101455402c2e84002003401d62560007140400c6890000c1d43c000c0e204103100301c01c0c1003542847d80301690304003500c0140300f4410085004125400350300300d5800c1d11407242411070029100d488010305198050405542c0c81c004000181c0402d0f158442c100c283c004c0003001d04000e082509010342d000c8800b0b45540e100750000c2e4070400040c0e41d501d1200b062411004004079036807042d000c02e000c01e21320960018042d01400604c0c004184510300381403061324401d0f2002c11004401009125101c43c082c007004086000c03103480480708a01841140ba4407210381d18003c43c0324040d5689540c3d1907040308030425005521540144100092521029840441950104454542034541031103440c4408910380c103000e01104801c1510519401c001c4c050511038100c00c5442c20b1900d002424004144107a8203454046030010450207901c404943c02c0c2010110468219241c01c8400c11040c3d1081100701c0c2d00101c1001a0350f81928144045001140262818 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 376758705 1250 376757455 376757471
    0xa050d111903020306100f200f010e0109080405220f0b0103060816030605071103040305060106030c02150423011e0b0607051e01060807090506030c0108010608070305150a09 76
    0x100700101c05400368041418014001c1184c5500c50380380c44914000e180c03504203941001c2500c103450907614600026010020b58135050601400083d0140020074144020040c2e50210f4a0541c01c803032001c500200005800c1008201c1454542a12100c0d000c0000303d1f64200c2c54009260801c0f28161000c00d82f860b80c9541c3c07402d40035a00751180e60700a012000c0504108205813070f440c42021080d001c0202000d40c0d540200d12020b225481c020383d20400c1004a03a40c60b501c03420090341c0c641c0b0911034400082d0400c20305121041c03003c50ba18100e40084104c014190301c0703030b90320800e504408840d114881c81c0444c1d0411880107090050318842002d0480c2d811440d03003150b40020075144c5003d40c1c90f0040b1070030070001000803000160081500d000c011030003d0300f662004d1050240845078040c04191140c04004120010b140c0c1c40385000e45030490450745000b80c0340006640c101d00034800c11022900e02400203110900a40106d82d000c4085a00904500000d50008481003d00d40010446507640c010b1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 376759955 1250 376758705 376758727
    0x3120903160c081903080406090503040504020a050d11122e060309020103060f0515160b1f0617010e0403030608060c0702043903060f0e0601032f0a050d11 68
    0x7004c807006403007525415880c40ba481c081d10140e000742000b80300b16581c24a01051100034802d0714054140100255034490314000001d110f600882c00304001985041822151180c2720411203824040381d148515182ea00e5507105031401110fa0700701c1207801107600b000c1808200e5002c014010304a9030f00c0c0081d00e0303034140c0001011181c907508890010304984c107043c40107a03074034544080fa0410001c205651620301900ca134500d00070b01d031001021074000e941401014102204180c401591081261400c160f071040704440d03c1a844c0114581d400c86000144a48400c850426a04c02d00906000c540c0303507500c40e81c441c508074007101d20085103000400c980702145410b010700c44c030480c0140011280550791814400794220080700d010201201b100000c0150340c0290482001440006001d5426580d200e24420030710340101d034114006860103042d201c400c80f1224144241030100c40c280d05400b9480450b619241d44002c90000a0000c24411504400c031117001c0c8081150007024041e8031070800c956 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 376761205 1250 376759955 376759963
    0xd180b03071d090103051903030914011d0a0804030b1302030f0705041508031801090e07030218031b13060902040f081c081906231905010203120903160c08 68
    0x1038034034403c650240042000c00c81c00921000040c0480300740000000a07407806600030000240c1c000c0c01c02c0b90249200240a20641c400c00145801c0e80c1c41310380f81240007007075540700c400c0d4000080600b05c2c188070900118180c042e00f26441554503940c031008018640000c2d1918071080280001a44400001d05c06402c160041100400c8007400c00c840382030a05d030003240c40740500d1481152881c1d20a01160043c0e2284980100801e2003c40c002c1e20341c00c0042c401000396209032440484079000c0c0703c810742c45040000e441a007100080d0b52081c000032216013041034402c110b12200250301d0310747c480412101c0c0107100900c0204101c0d080141c582c1e19140d02d003800c007925852000d011140c0c121000c000c07540c1000342c00781d04c4030180c80865070130344d0183c10f14001809182c0000040d2060040000c010038080700401d1400e820458810403072000420400745444a94000c1600580061190743c40d0218812842a007203c50042030381e040c420141d038500b400421800080c0c65214000200300120701041c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 376762455 1250 376761205 376761257
    0x2120d090b040302010801140102070506160b070c0b0a0b040f0f050610030204030c0b0c03040308030411130b010906050903010212090d140306100e0301060503070902040e060301020306030d180b0307 87
    0xa5071040c1002e1540d00040d00811781403060741203420340300d600c0303000d50381c802c2c01200090440200f85584907401010110b410801c050411592900020081081c150045040071381c0e003030340042c5100d92541c840c1e04081c00f400f50b18001d42d4210751030346c0048414840500444c0d040c020781c00000120752404808101c0c3c800c190920541c01d00d4410007051001c00d000707041c0d003802e8865800203035903110440130b24145903100326840030300390101c00310501c410419803c070f46894a040403284c54002d00000d010765801c40307900460980c0800c0640c0000c00030b182c0590040c101ca030400030300060819401410401c9200c1045030b048803a90003000d20f00c51301e60b0f001039034203030440c608010490440c80c0201c0030a100b00d00f0000c00c90b05210740300903a00103a503800d41100b800307001c0240c107a0f0039413660342003c00081c0d04030317019107084426500001a41401c0500c2034922512000707005040c8800b0101c0d0a49122a03c0c2c180104140c2c0106008a20349004100450207120140c1e18040141c00c64100040301c20400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 376763705 1250 376762455 376762469
    0xa0e09010c1e020c1c080a08060f0f090118060812040515030105030714040f112109032d190e030f070504020a02070f2c010b030c130302120d09 63
    0xc844000000d680000c024094540c00c1c3c1d94028990b4410b0401764007418044c6005010010000c0c142c0d00c80c0f5484006140100000c3d540b003c0782d6200300d000c001c4201c01c03681045401180c100010464400303209110391100100000018019132290020b504040702c5240c115107903240000c00b00000d041407a0354595000d000342c3c000e030440d418440001d448444c00c0c4a4507940407001400d0404e0760340c450b800f0b561031000c1300c0c0d0308000503000a810703140160000359140e902e204404601d40710060078040594402d80d0150099031074403881002e018070022440003184001d4003130202c040d40c04400600100b0301080c181004150389850700400418040aa246950103900708014400311018005018401d88070202c402685038a22880c0491030704800354401440140035100010b4281d01c0d54011380310850340000d40030100c5e2014021301d40714072404e1003194103a640810000e60341c805208040c09004400c001c0d54040b49603680c0020300d2041d81e860411116800400c1c0555006404c032a04400401003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 376764955 1250 376763705 376763747
    0x1503060118080304030602030c0f03091c1d041802060307020105040213092001021603030905030d0302032505130605190306060527090f040b09120d0b0a0e09010c 71
    0xc2002e040d4503802644001400e0390b40200c08030310409050310545101d1100744840035100c0c81c1158100d0b0f42e907170039903800f840c1c061800c400b14840c040c810004500c10b4442c4140b0301c1c0c0c03541c101d0320522004002018070181a441100004401699103000450042c0310380d0b80003040345c0c10240100009282c0248110300c000d4900810840002c0040b0326821514542004c1c2c010690644801070382400f40305d80c41e0f041d810586590103c01c041d003152400041c1d0300c080d41100c82a9904041c240c0481c80181c40341d11000d003500c8075080d0500b089224103600180280b800c0e6040c200074202407030a08920703410900105102041c41c071403101589621440ea49805c2c9402d002491401502424900c40c44419400d214280c80801d401619284c0101030301100160962a03a8a00b00c50100c0c035014090710b0440d020011100840c03101c4070000f40c03201d41d140d01003200301c0c60f0420308103880004108016406404c94001e4000240b001540b4820f103210f9640341c000410b40f1410303118010244a2103401e01c90503494 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 376766205 1250 376764955 376764959
    0x3010e0d08011410030f0902030f01020d0e070303020715090806010b0d0b03010b100c0206070f030e0108070311090907021e03090a06080c07060b0d080304060609050c03040201020a030e0607021503060118 89
    0x40c64110041302d05245080004050100003125405842d0b09200650544648419000c0c43c840550040c402031400036001c20540300c40e684240c1d10788020307100c041c005a00942c0c0030b216000c0a50041308101440d800c200c80c3c5c1955800405003000001d80c0141c0c400000803681c2e0a02481d680290402d0010440080000d846442c00083d01458110785a0b010450b41801d84d40440d1500c0e802c403191903401403035080d90807445140060004500103009800103003100040382a150280c000d402d12071148010590800503200700303015407580300510329421841240c401781e1040154207507101d00c11350030078080d40e551420f580602020f441709910410030040d114040100c1d801d0f420040e10a81a800003021078892903940015144070700b161006048010000203100400516070320260807264160000d01007503540300340344100c500003100c0c017a0150f000043c04000191180300101207803803005060504043d600d80115249496469211007104400000c3c002950b800c00b600e00c40f04507050100405583c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 376767455 1250 376766205 376766209
    0x10902120d12020c0106030501050901091109070c02042304050a121805130209030304300308060d05070b040b0d060e04020307030f0c031a0601030e010209031e0c03010e0d080114 78
    0x81800d0b5030740200c00d81c00f1400e00c2c6071110a40040d0002d58000d0024007150501080e09402020f41d02800c84542003581c0551459007400c0038680d1090714981c80b04803a6a1046d002e00c0040c04180c1ea034218007105812002c840714440c0c48806004030f000303000400c0564003919100c41c882c2c078004168018804003e00740481c81000248483c15a041920005101c11130070344614060f00414103030540c180004680491148184c45a40c540c0452040441000703884105009013211602c0d43c019000464840000d0514140203030002041d07481101107911180c1c0d64006040150855009211561800256002e00300d40500421014048160b6290320301c1c00c03c0e0f4002a61280c071407100402c2064407400d514280004820300000460b0003070440300502000200800c140c08040707840c240401d00d000d04108013080140700340d0303901c01e101900034076010303035544079004100300d01c19a500f000c2d128100c0181d031603490a004681d04100341c04c0042604155400e005000b808c016040b00c03440c46012034850303281d6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 376768705 1250 376767455 376767467
    0x5040b06030c030d1803050303130c060c02011b1a01060e0108010509130f050120040314072303070b0a020c0325030602030910090309091a0f01050f0d0509010902120d 73
    0x1c403210f030900175110f08030080201c038036800f20360000d41140408001c00020b211441e0b40300c001240301c0c004904401e0303101c54084d0340103031f403840020f07000881072070b10303c802d803048001c110341894041c801d45180420380c990801c100c40710903084900001c02c4000d4801075075810040150160504840e80242881d0600783e0b500c4000d84c06030064941000361005400340002988105001c1403c56071042c0701c2ea0594140d003440b68011303c0201c501e0803c004545240c8040030850005070703004c0b40b5108001c400c0c84e00d2100d4141c0400861140c0c140140c0342d000034660b201c000140b02c2c00304280c01600d030001d1003404041c10046680e1000360600b0881c613480307001c041e18255000c1a294041c2c801a140e032142d0b80040d2411000710031000d0717543d03c0e1030041c0041c960804011411a8107182081c0a500c3e0b08181000340319001c3c00c005078002a00104a0b05158014400360120380d00d40319243d0b003400858401a0b068810a44d640000c60355036000382801e5091200140c1c1c112280000100100b28002d6401044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 376769955 1250 376768705 376768723
    0x203091c1106071b0b040e091b01051803070e1b180d031103030f01080607110a110d0b0c040e060108090309010804020609040c021e01060f03060c03060506040905040b06030c03 77
    0x2c114070009400d401c02c507240d1441c1c40c024801c94007064403191960440c000d81c2c0d016008444d611121200060000d45000400000d0071f018000d8884030146200b0054503950031205d868903154030304070944001c40c0c500300980030043c00c074a0541c1c034240c101188c0071020341c01032003c154944d02c01001000d1200900c406805038003882660000040f05850508a6688a860171403400600001050126000a84255505848509066407000e40300c2a0058030020702c02909015960001c90041000c20120395501c1110b034400390400414062079601e00621400849540c002850007003000e001d0120f4882503254000c00031300b40b9401d6420210a820750324000e44050340d0402112000080454039544143c84071004080c10511500309514406500e9078141041c10210b0070404541c001c0e48281401000d0494481c0400d132010b96007151a03e02c080d0241c0c0c1c44050034561200c20014040e102c5100a01c02054030710000201818a803a206003072013405000140303c1d074844944110f580d41d0124442c64 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 376771205 1250 376769955 376769959
    0x15041a0c031f030f03120507111e0319092c01170106030b2e061e0903020a0306060612060b040b2b0912080906010e0a0207020406060203091c11 63
    0x50b045954048407020705000e4100501a0018250b00005c00d50492032001c07040401e2030003881180d498841c1103d44218002d402c120582c0480d1814454500d841c100c0d8281d40e0400c400d44e80f501c0f40250301d640da060010241c200010724481800c2040780c503d4003000d2100e1403445004035002680c041d10008074001030060381500c000c0d1100720541d8601c254002c0004542c418041420b501e05242c0c40f00700d490103d1400301b4031000aa43e5200708030083c41003007080e503031300e52078000340130b1031080c03e80e0740b1024585405028020700420220241c2d40c2d00f141d00b0000c620a900c00704107141071480051001c0c10099001000700d0520205010540c1400241d50a80e481d625031540c07120030480624010140000c4000714654a224400d8021080c5410030300840f80110b40300c000c1c2800c404400c98940320201d0715001282c20102c0113000511101090340c0d002901d1410260814005800140446040d644043c015900006c0c40001d181080302c4100070081c07a40080909122164071485009140300210718 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 376772455 1250 376771205 376771231
    0x1e010606021209011b1b060503090a0f1e0b010f05041a0910090e01060e130f020103050613050a0e241501031d0a05120a020c0f0a0815041a0c03 63
    0x11000d40d200b0100d0105c04c21a000800c2607910081c00e0030b05240500c406420000303044c001007c2a100e005800701c0f4041c000b418020b100c02240d07611491000042072500f21060000d40b10b5285d844624034001074603007401043c00c0c80340703540f52403810820013280da4840d5000d0750800e0405041180c24150002c6000401e4500000a94075040071034041c091a411034006545420702001a0f0341056000005132890000b01c02e8044c0c0740c5210441030b030318804500038080d0418404030300055220303402040d0020006001c0341c1390956000d4004080c1c6208803a2103540d103540354940d01c40c100c0108400e4070210307060002080a40c010b5520280403100c0241884030b07a01c0907032880c003201c1e442540056031400600e51b49081240300384a50545a0340210815213891141d0381d088450302100c64201c914445c03564004000c100036003c1400f205400c0500000e0b0b0116134100001545202404801c0200e2640803501c170b11454280740042c8141c0700301c15240810303041c40041010100244040303a41120120750a1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 376773705 1250 376772455 376772467
    0x16050103092f04090311150408031614120601020c010f0c110609031213060e090103030c1103031306080109110307080c0c0d030c110609060a09060b040606021e0106060212 75
    0x416101010703a20650418a04400030050686c41001200455003c01c00c3e54007240d16072240c410139400a480c003400c882c03010000704408002032000c0480b40d4100d41001b07003400c420240100c05541024a0007206450b210080050750341e414404184261000d00304200041d2138001c0041c41401e10f603034000c0401c50f01d506101d01540c3c4002c19212040360040031911400c202800c17005003a0840d8003100001100c0c01408150203024050080d40702d88054010030681e0b1a42d00c0440750403020180540c0c40c051243c281c910319882c281300070882c0108130803441c141c403407a0040051243c00d050740300d0a80b0f5840c3c0a1010a610790312030840c1d4001c0d00c01d1400c075030355440b030030083c0000b48120140004244101552f02102e41e800d034020710303001215511070700740c040190ba080070b441d21411651400c032504982c00040030454a03510860119024400c00078803260910b010808a400796042140540c0c0121300441103004144010001000100f000b0b1203514584500a559050640e4403116001008150 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 376774955 1250 376773705 376773773
    0x5030a0c020a020d030f08070305010501170402041401090204050f01021f0c09091a010905030d140d020408010f09061803080622051807090905060103080c0f06091605010309 76
    0x4507122590000c1107500d407130495250140100c020125901c01041c03801d00040d03815802840b500f0f04a41040e1500c000fa0340d504001d010081074000d00403603000d607540700c2e0000d5518501c80c042d0b02a001d5403900607501c505100c1000048030300203021a0455108408a84901940d110590698031500001090030103071510300792049112a007011028620349129450040907894107415080300a03211016215122802c0c941c5031919000c0341c0004c145d08200551001c0858001010200c003040401820251a03039142400d50742d02c10400d044442e1100c5030182485102e104042050104200e41e940c417086940e400707010000f00030042c6210f110300400c01d20310305040070a944c2d03072048043d000b00840c1ca00400700349985081c0c0a40c00c24135104003a400b10381200e041c8541004290800014466030f840c2d030723468030b10700c0e401002081030078090028840c488900c00c200c0940614a60405031499624400307489400600c0d0342c1c0018101410081000f0105400d202d2029441411030502000000c4c0800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 376776205 1250 376774955 376774963
    0x82406040603050a0614010b0c0d140c070f0e061804030503040203031c0e160b0f0f0c1504060e0606090f0402040e0609030406021006301e020f04050705030a0c02 71
    0x2001403c2801030071000410440c0591080741c6000312101d0307690250f62900100c1d010750141311581c00065200ad07401610990252a00c224040140c034a090f1810960300c414a0404100d980031114103554080700f0b0100b50300300241e01d5805002611440000c20020600f0141d030781c805030014092110000205013551010b00c203c4481c0b5a0242c100602c0000f2940c070040209506000b641040c0218810003450910b54010300301151960700f83c941c10300710740c9814540a50300c254116207048404100707140010030103104400d40034004c5120406a03150904200341511145607440215802400400c4129607441e50403a40104031840180e220b980c45d440820010030a005074002c05220794030400512800000081c000d072003080d42580e03001c1b11a4001902036a2481c042c41010805180c040100a01c000c0c901f280b08980f51640f200030f011058a52022251900841d61850100010000298101103840c40541441940c1c204100c0c034098070018039070700014201e214115103554142c000350307100300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 376777455 1250 376776205 376776209
    0x70f020a0b0a1205072f010608030901090902091804080702031c0e0a05030c060f22090c05070224210a0501050a0311041e0903030b09010824060406 65
    0x2a015110498450004160503000b298841e00018002d160364a0300211030b00915000780c940e52284104074010351060b410980d81080e0004908141041c88043c400f42406080014030609000d113a0300c9105100040c00416203030090760456004110701d400544480145040b030150514070344070079032103602c1c0401ea50300c24501c001c2c0d854400c109981141041e64032202c10105615100c02044000090a108011085114603603140d00130400f0003516040200040800860810b00300d0710700020440380b450590b4030071103c191101132000b8144008411481502004410390802c642000d02c1540041c139660f008180201080c001242c46c1c0c1ca101000304250390703100d001c44140001a02c14102001c944000032030f20729803041d05200001a050905542442c10399130000300186004c03072100300b40070141401c505032040482c9000310040c0580b4a510644030414820b980114020b44110104030203108180c001e0021500410001a4a014045451030f00301c2d198001d01c03080ca0ba00d4500080c0101402d17 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 376778705 1250 376777455 376777459
    0xf030b010b0f160c0608061c11030f0703050c03120c0d0e0310020408010906050c0c07030b060a090c08091b01020a0f1401150e01061d04050630061317070f02 69
    0x90080020448505800c1041d00c01c60b0b43d846c3c090340c1d1030000700000d5800840b60b484004280d20b900d44049102e002180c0c40118001e01201c281914800c507051034994a0391003a15160800c40001c010351500303000d01a07449002c0340045052402c240fa8064403024076946503010311098942c2241030b91818000300b801c4d4005008115120f40d513804009010301020b5030308541da01c0c40c1c800060303001400c072425159424074500c028000c4a040d6500d00b00604000307000d00360b002000748400110401c15000b0900c0f0f2100716958080705003080c2070400c2ca400c0c40401c0803075035800c90010300c00d1a03907400200346000641010054030340e0b103098101480d0040094042082650901d0440c8c60070300d2140a02c6c1e0b00729aa400107521090781d0742c103011036002000084070000c45c10030400e100851301d09504890b81000f8001e049050f07070103240036205101c075882c4e088501821104224118404420302441d07500031381e980c603e03032504010ba81d2200100c00354528649200e0101042c010180141f8010000c0d801c2e40c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 376779955 1250 376778705 376778737
    0xf1012020d061a040305030901210204090c0e0922030302040312020601030c091514131d0c09040210141210170a020112020a14071b0f030b010b0f 64
    0x841c1040c090b2280f0b00a25040c00303880410054001c089208480c1204d40105c084c500b895803540045036444002401001040307159003a014900070300340b00400080000e0100015403160207031000c2c01ea5819503424621a081c0c440c20899201c481003200034030281c3c0d44042d02107080f07280c41c00f41c000b80500c1d04041d00021901440001e429000038109040c1c1e8003c1c2350301043c4c05c0e581c41c07007003040d0f8120281000c0410103810702000100c850550403070042d40010b2200640b01c902941c0c400403601050b00c800b250550010303d0301c000ba50280646070742c1035419036103805c6c0ca1400b60041401c00a650305644100246100c413020f8444a08060710400c007032503c150243c034103001c48041c0103c4214054121055101101c8014460300082d1a002d91a03040e1118840320303e28103004802504100c50240c140455070303885502e080045030052075894070400108103050280ca900450314100e6800c500401301c141c0f54144049620994450b04551030409801d50300e5100412204131402002c42e84130716400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 376781205 1250 376779955 376779967
    0x9030a0c03050d1803200f1003051b090a0b18150408071d060415050a0b04031103010c0210090609080309030a0311031506090f18040605070507020f101202 68
    0x141c041925515503a1a13030301c0100403482810f8004c40c626191000425501e05000c0d041054010b01e1003401c92090f004090395126038050b00403444185814a031040041e5550082002150b4402c102030554410040f01c2428280d43e4004160005001d010b170854680c1d01040010100c02c80541d03244c00400c0140408140c030380e0304407401200390014040c03a440da000c0c0d64004101892800305d80d403a054568611b0000c8c944850090000400c90038048220a6400700c0000c9800d840c0c0c6114280100f0300d0751000b80c0d07510300d1030800d00402e16154100c684681d04148501940c8dc0d8005042c0c841030a244d07000003403815440c903000e0010020341c2c1d0014118440801000204c000c0400505040503041c0c030240514003045024215611080f989498110700d040c0102c00c0324144100a03144021025129852000040000905000700500704000600680f0304020800125005894001e601c07820801d0a050321030b030008100b0031800303448030700450135940740320000c80c807419a02c1108041c0c980d045541d09 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 376782455 1250 376781205 376781213
    0xf0a0303050c0d0c120e0c0f121606020a110301020c0601030b0c0c070b030702011406102105010f051c02011205070201180302030901090f0b0a03020a020313121109040f03030209030a0c03 82
    0x41817480d810f498403032810202c41600300d00425480c0c072507800240b0b0320302072400c2e074400c21200300580c41c08501ca9200e0580d00b44548910000008007800d082d80051a64070701501e400500c6c3d81c0351002c400c1c02640103000185414100181c90b5044d2948005140c3c02c035a00c040d1820114080d451051500f441201c800040c0c10f14a800298014130b42940207100003000c00c0041e1075668070a895007500072041010303102280d0b1080c0c0400c840350000c0c41e07810020a0411801c030090740c00030380280c60740c5811458108420b20b042100e840101d00020301150f0514465000601407031801c510300e60003e40c0702c00000f010381d40b003903006005403030314110440381c00b0590b0b04000f540c07600003100b05804240c20300030201d1011081c1011408580708041c4041c5070000703051048000c1c1d000406480d06501c030912540200340328080600c8060039260801d40d0180b01d96041c0404070303104090405000e40c03403401c1408081034240d25281002501414003595811440004ca0300e8207000d100302900f40d000d0060040200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 376783705 1250 376782455 376782467
    0xc0607030c050c060a061406090f010f030612050f210403080d090f1b0918060f0e0613060b011407140304050d060605030601050f1807180b1b0f0a0303050c0d0c 70
    0x501c04500c03a4204051f8008180a814403802c003005501034889812440c0a43c400c0d03803a400c03101004d01c1c3c0410596070380c8940b10326520100034102c809030000400d02075191420000c400c1c03840305040985000d5400800b0805041c842c5010142c14030200181d00541138106800c008111036100c1d0700280780c2199410720a005480515102c101c801184d4000a103485940c0210300380c041c18015016407112440e03803194010700001324112200c80d1161070010700c03004144a8648a14804500340704040303590310b0f0900840f0031000b0454103002140c0b2000a4826010781550511907012029181e1a41c6010b103d610314001d84d84031030380c4262059068020080c46e9000101215825011260f090362140c08100039040502c04045e0002081502c04a0828070078003c45d40010060605604e030040c4501c80341c1e07102c8610340154041040001d135001c010652008466027004442014002c603c14541e6243c0c0c03155aa107801800701a240c101044031100c1e00d10886180d020308000401c411280040e0252003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 376784955 1250 376783705 376783709
    0x303112119080c040b030919080a17040803010303050a200a02040501140607020d080f12150d0309170f03040e0402100903050d031d070807150201020c0607030c050c060a06 75
    0x91030140d610200c102e028000040c003c18074510181c3c100b5040c8a2012a81d420041207180740d80315000c102c80032690104c049801181c000d141c52990f03100034a0700500301d2654150301c0c2c1e00801e0200200400704007488196815254035252460361030081c200100d440d401d0743c2d8110307030740d8840405608140d14030000c2e00c4500b071442070310280a00e03a0307500d82038200c0302d012104242c2c2082003001404014a080d003c460720262141a00c80c1c05e1000c000c011311a00c0d000001d9919101441c9000c1c40b91520071040c082c0c000b840c2c00c80c4c1190740c0c00481e54009181c0d440d2840340c80820518454056080d1009100c0400781c0c002c0035040fa0b898079030301c108550451100340c409074000c103030401100c43d080f4811040182940d07004002000c1941450204400400e00b0401030300c0c6a00c0411415813034000309010040c010b003a050000d040150030320310303401c418542c0419903906581c0304010264540c0320104e00c1a0348041d283c01c0c0019503504103401503405209980451909014000800604288960100742 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 376786205 1250 376784955 376784977
    0x3110619080a141b07210909050a05072a080d02040608010501140f0906042303010c02010209010e0d0203031b0609060c1206042f0c0f0106030c03031121 67
    0x1420400c103c4062114065074034589005055445000180c81c0700014143d0521519030148091404c282e011a002003800c2c111000070f11500c010043d80c3d006010b02ca400908010042005050512010386810407581c042c0408804c1d0784000c0403018a44480c064440303421104690742c48102ca40314000135400b90040303001180240e0008101d0754031440c0009040301019010525140024281c1b034034581254034015800301c01000081034608a140d00c08481d241c44441b00340c03045031108201820749034070400c404116841804619920383c0e20580b00300100b80140c070000c9600401d0b0010904510850300196070210b00380c3d114a003079000c0050581d00c00e44c3e001c01170321810303105c0b00742c120f40030b00c101203c08940710f00040120741c0d107240c04c0e40f00810201c1d160401c0d660a1442d5001080700702040c0c6e02001d2005004950004524414884018401d503000e000300b05031425583e6480b103940d00ea00019040108111040c130b06d4030340811000d801e03400000d000c411a1420302500042950214035804 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 376787455 1250 376786205 376786211
    0x32208100f15080304180f0f0e0601050910030f05150903070b09060408040b030a0603061e05010b0325020f06040c06020c03011b030209150a08070810060903110619080a 74
    0x91842e4000c8249400d07500c209014500c0d091418104004140414501c5810160307240280c442002251007080c1402c00507050100700302a5100e0304500300301050344114040c02120040202c01c1a0560350103003900d5015110071010001c1d81001c9141c020003a8002c100c0800c1c020600506001c0040a040900e1003008991919036640070941d4403450b060b5002001d44106100a0007815220300c0516480000303180001045641c0340ca60105440f42c2400740c2252011400c009074405145014aa0140c20018031042c95030410951189101c0b000700c0045464585900030150700320310a102840d442c440b60421a40070781010b09018489128511440001d841591481181414180600d00d203110403840c1070f42211000c45000d80181d400720010590010030300d089080c5141c40c01c07005d090130704100e50700d41c1800c0c0b0b03125a024101000142c1203e04a07030b860b6504014440c0d00c21071003825a540700401d42030300b4042501144850242031440589504d00000c480f00702a4803146c0b1908c43c8103044428 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 376788705 1250 376787455 376787471
    0x70c0909020307080c0d06050a09020907081017030901030c170a1b02010e0604030e010207050303030f10051507120c0203010207030309020f0f151e16060c0908032208100f 75
    0x10503503801c0c900004031b800080d01110700d0f01041c510340c00030350b2124481c2c3c00400e00074600c1e800501604404c440032000310b03140ba400c3c4903002d09003200700c801400f4882e1130b031450350010b44070103640e07401386500250400d61900801d000701c0744a0916019001e5000d2a080903d0030710749010409040c02030400e1103020b07501d0b82e03e03c020320b2050080c8807460307406401070401502d858a048031307070000c1c0580380d9065218107800001e4a480400003140b0900c04503031040e580f410591044034480c40d05038440c920440d000d604c0b4041c411031000480b480164016071076401c0c41c2d0251800d83e103910542c14040d6043d44040364440925806400481d0000c1c822101c04030500500010003818860a00003d40c0008410354540100503109009007442005500410721000392025501c20702d0384981094070400d00c40b00307620f00810034907001d40421103c1e00d08200380725a0400ca1040d5403801040880e00301d2000c403207000c0b8070b03040003641500003414a000541e11014010301910f409001c0020505c5151840c003802 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 376789955 1250 376788705 376788719
    0x40f0602015f0f010609030515060d021309060609060b0a1b140706080703020f090105090a03020306270a020f122517070b0405060a0302070c0909020307 67
    0x244007408411800c00582d10301c0c032a031650500000418400d0b40c0d4408101d5412030355400201e04200768803100060002d18980407100d28480c200c185d0200c0144110700d1010b100150002c2410003030000142c014a81503620200002c0c0c800e60500b0002c0d40101302a1101014a005900000d000a006000a10540355903014500484005100e44e0341035400038030a03042484e2180120148100802040c000e00c600292a0001407010084110540ea8445c40b420003005820401c0c01e903010020f0708045090030070515501ea0baa101c0c0802486c1006000141c3da20319507915500784000d96000307000c5804920f00310704200f82d104188030314801c00031200c03030f403a43c44042d0025040040c01d901405280404c0c001409000d010769012481840c40e004003805500c2410a0340022901c405500360701511041c505400c0d00c4091030303c0c40341c0f41c519030003940051100400c03290486080381da050710919520452584210b0003400340c080c0c000d00403800c103040040d40300860381107032100754021000d407148581e403024 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 376791205 1250 376789955 376789991
    0xd0923012a03020a030609020408030307090b18041d011401060306120c05090402120307030305040209060906030a030e131a040e0d0c03051e2205100203030f1506040f060201 76
    0x401d40140c034004041e00c1d1100307109030050310b401d080b07500f0013241040d15034044100b03903001904050340c2d941c008400c101c030b81c90744407059038014240d440c0a135140075404840d010990301640c07030540c01140c95509080200405050742c01d02c10350400b0080050040f440000d454004080c4280d60009050800118456120380d524002c504d50044008903218541b50170b004544000a1051f80e100700f120320307042c040001c11300082c05928071036900052203241034410800203520140c60580154030740010011961000120301404a030541004041e400e104000140301c2c40c0075500590900c1d08100105031300d440a10404501410125400d01240c0f00c010748030341d03a80314440084000943c1c0c00c140000800d00440007816002d0180c01040c5041c2070b440d41d442c1382c07980800c2000480d24070001d10405003035040882c00c00a05422a40c40d220021075000003990703401f004c2c002c202c41031050300100b04d07d070952841e024040b12000c0e2100b41c0300c40d581c1d151151002c0d10f612944000d0350912103503080143c4042 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 376792455 1250 376791205 376791251
    0x160503070602100e012421110d0203030c03040314060a0c05190302300a06080a0209060406080607020d02120301120609060b15180402040b0a050d092301 67
    0x54020300300400e0100c1d441002c1c2004e0207883c0100c1d5600c0301c0c69448420184032459000c1c01807441c0802031840e040d0b010858a05080145c20145100d500c62000070310780c4000300309440001c56591041c4216400028110b100301180700c0003030304c0001000010000c0100001e144a0304400c01d0342d469a440200c5001a90541c907c100c0005000b005401504000f03140c000c402e080780d91400500b041c1c0da41d0150301d0108090b064220114010080002c11082c500d400305038082800403044c04883e141c54034107642d604c2c0d0b180000341300d0350540000650544466006ca4000d0402900f10380c160305005a0203519520400c41074070040c050034808041c141c00c500c0840b41200c4083e0300c1d1404864454444500034141010200d0f504d0752114294100745d95940c2e214034584c003051b01d00039030755058000d40003080800e40b200d81c1c0c0100d0042c80300704184503070702060b16080d2446050076641c44040c41d103000010281000010141444c9480781c0b54000d000000d0700504a000e5002008122140c0d03001d100146945 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 376793705 1250 376792455 376792457
    0x7090516170702070906030602251e022b02190e0402060706020c0d02010c090504050f0103060509030d06030305030412080f0c0c03040806040f02090705030f010b1305060c1605030706 80
    0xa2288101c1400316280305980c00300c0c60b4415503010325196400300040c0c03222030b0f0042c0ca00303540200304a200108000d07180d400c1b00034000c0619603204000e544000d0781d00c18005c14500502d85520a08041d510346040200d071041180c00d10000384900001c00202088800000f44d01a07107640d2115101a08669842c4040e604904124640d95449a0811100e42d000c0541121002c2c0c00f07200c0c0b501d2500c0c04004000700e11000c2c2e000450b221000000c001c110820f02d03402a4405d50a00c2c080c0704180c0c0090703000c203040d03903001600404d95564128131a032542c418000503131041890b000300002455841005140628441c5444000000006104441d81e040c261440040158000c1c049903ca140a07401000d5010640d801d032802c081e41c4204040c10402c04641c1510300045440c201d904500d80800c03225800182c500309a0b01b9410b1000000202c11030500070110400c00000300140c0884101100e03070700400e8014080c41c2d030780c4403941d40662203038440f01c01008882c84003040400e403890042400d201351030903 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 376794955 1250 376793705 376793717
    0x801030c0b070f060c0908060c1c11040806010306091509020105030703091b0b22210201050f030a0905070602030f090d0f0c03080c07090b0a120204060f0807090516 72
    0x9041025200b03600200d403c032501d6800ca0320361000510280140d0007603400310f1700c03001c2e011840c14a4803810008000e152181070541001203140391010740e42d400c6c5201e03000d048002241c5a119003890340a20030754006081500c10580000304000300368000780045403050030302c000440c1c000d41c1e1600c103880302140024041101400068492440f942c0001c1c240e5008440200d08001c02501001017621a030b0000c00300030300300180003100000310120088103072000c4007948586602c3c00e220b0300304940c41541845c2e03156081c0402001035a22603000c1d42c0d01e500031421120380d80c0c200500c603400104040301c2c00300e440b0b018021000131064004800d803440070541c900d02030315003529001040b1101011040c12125000f03100e8183c00881c513410a504080c51043c24810f0740ca1140c8000b01d85041000c6d48400749507828036804503295166048500125465900380c1d401620380c610015003d401d298201d1a03448110080024840b5000607400c01141d0294408125a40707941081c1080300b68842035100226103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 376796205 1250 376794955 376794959
    0xa0b030702120a2109020603010b04170a0c03020603070c120c0201110d020d0507080d090602070c0f030f030804050c03010911190f030f02030a12020c010323040605191409010b010801030c 82
    0x724280c14265030840b229400071704038005a0010b58190000e0300801c0d00c0000218040c0402c5a21181d1140038100820003803036000d0003561200c00042035030100034018035020010521590140d0007924126500000f0750184491424006098142041d426030008210710a010103c0b0313404078681d180c4035203e030301078407171802e00e4413060f61540e01100c1e048451907010040c08030040914410a80c20520410b0702603911500c504000d0180b403040e400c586810ac508080400000e0503851001d401a58103003001820ba564900f01b19003003c0c044030b8800e4165007080c064004114806801c1c1c0040e441c212207449110614080c001909280741c0500390005001103800d1000c210300b014101d48aa100504440c0c14442c0c555030f0ba462408541d41900159010344d460310382946e01406a602194007a00311407241204005000442c481c01500103051031740d1325004924442d054010b036203003007142003800748100030000e105400c406404480144c441d501e07003044414107602c41d1010300d04a03500407100c024030794 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 376797455 1250 376796205 376796237
    0x1020a050729130e10080a0b10080613061109041a01020708031602040e03093312061e0d080d05010f0b0a03020d1d0a0c0806070c030311090a0b030702120a 68
    0x440003402803c00c8203600300002030060410440c89501612581000a03241465080d800c1d03009d2898010452a4111750200035a111030304001c1d000322900720b80085141128150100c21030300c10b0444e0180c0260414518400300610003544100c808001c1e403c0b103c909036501e0030b46803039000d640c103140300800309500100c001d4034054204500300180074060f01d242c080c80000140c82004a00b050310000407080520b0f2000f040550250604491501d486900e020002c0300c0740308080600070100340c80358036128018000540e1004c0361f1420094060441c0c04009a607041a440540002e0002e411250810002003100f4484004220441d240c81204904044044500354081d4119801101900e683c0d04071002c80101080004005410a580640042e011504040004040542169005600410902602d40d501c040d0f80c401e0181c05150009010003150f814800300d104114919510a000c0440810b074059120029405016640c0131200e00003031424042181c0e0280c1c29084011410894900b1860 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 376798561 1106 376797455 376797479
    0x70f0603060e070f0302070f050105070e2d06070813030f06180804050f06040801020a082a0a0e01022a100507050c0f01020a05072913 59
    0x16150241015010061a050540c201580000c07500e041c0102380074030981c8a64810000d02043c140350320001d024020181101c0d1060f4051360704042c02503408512181050510301c040940b0100940030002c031038101c65026a001181040040111107250310142c0185100d010041102003e90404200703c588501d00a0311960310100d204001ca40403100340c0301210000c8555000003181d4501184060181ba40113045560000c03611206181e04a41050f00c11055140300040c500e08540c004c6110004d95803c40c0c0b0381003010040700e01c0c211700c81c07000f00c868504180101c44441071000300d00c42d0441c0b40001c00000d40c901c1e13880500064030b0004000300c045061483c149017403065985038a629403001c001d40a00c1400100b1407914640d000b40003001203260840d042c0c94885595440e050354080c4a4255072400f0f090343d030b40300c044c0210080250349400c0307070000c40c60f42120300b00300103000308c = true := by decide +kernel

theorem cover : BRFrame.Cov 376618705 376798561 := by
  have h0 := BRFrame.cov_init 376618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 376618705 ≤ n) (h2 : n < 376798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
