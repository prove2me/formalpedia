-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0229
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:36:57.673638+00:00
-- url     : https://prove2.me/submissions/ba3f3d82-62a4-4b9f-b800-104424aba94f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 41007198 ≤ n < 41187055 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 41008448 1250 41007198 41007209
    0x2030c09030a0b070f0305061f0306050a03140601060201021c150b19020111031006031e060602150609040206090906120601080a020a0902030705030601050706110d09030320031609 79
    0x8070000082418031100140086404c400810391002d02844014400c2c45140c2c81000010030340300c480c5070084001c02c545681d080807001810740da40070210301c590780c007541130005500c0f03869071aa145c0880c0076014184003041e4808019a03005010a020781260318202075011000c0500020b20184903203204410480c05500040003202d002074004049040354000c18804d08503070b002804143c00c550402049403004903460300d01103121080178080381d80b203500b01200c440031014440186820306000741045610079441000964409441c0032003104805080c44e50050301200c54501d1460660003280300340c0300e90107605102e03074098000160a07039903a5040760340302d140310070445070b0360342e15540c200d560b484901506038030070010164001041140c600890344202d00307a654450442d2545801542c898101290840302691034031006000d0f10b4003100580781c4201c0c0200c02180f0800d440c140a4100c5681c011900700a8840841000ea11078078441169049503120181c40c080c01003040040b55040c1c000d400c0b6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 41009698 1250 41008448 41008453
    0x7050a0b010b12090706140c01090c0e0106120e03090f0d060516031107050309010e0307090212010609080d080f0a0905030304050303152b0f06020a18050a1802030c0903 74
    0x30511980d80c102810340c031600c903000f0107981d03111207032100d41c2e50b0020321841d070010310048600d003804081d4101821034181060300214080585513a00110240c00e0341010400c000394000410009502081c0f604c2070208841042050400414141c1d445c0e201e02a11103010780f2042c002c1c000d90b5214442d070103404940022081005052022404003554500d94160b000070303040c0744401c6101d508440441c0c400690000045150180e030b01c0056400c50b41c0d0b46c0c885545809480030014050005000030f0200c200c00d4072040110390304141018004240c00d030845255030340702c40b1a104034260845196500310b01141c0160131a9651842128003070400c1030b40c0104103000101c14032003081310000c05180103a24100700e8010444200080c419071480c2d140b0f2108000807200042c1400ca04c00b03580c1411114000e500100071443c16490310005d0380d10043c07081000403922100d0040c0003021502a0010702411a14600c17000d00c4d000480928049580300960403c5e4000007244403075080c0d004441800e04041c0a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 41010948 1250 41009698 41009701
    0xc0302150405032506050f0909040c051201060501140301030b15041e09110f0a210206040e04050607020f10020c01020d050f04030e0f010f0509030c040608030409060b041a07050a0b 79
    0x104c02034032002c4000c80e03c44030030082c5004200c0c1400f0b141600c840560915881781400020030800c40070f2440a002550490320b401004240394070780e140c0c24002000d0340c5001151a920b0040010841150002c01400d00c0000340010301c0002c103054443e5401407000361600c5070800441000400500c0e01d0110317040c200354111550001034071135070001c1c0b5406026141c04202c0c11108000d2011110303030000000d0303015842030b00504c8000a42400b42c00410403c1c0079103103030300318140e0114a0682c001e0300b001151149403010002040300030001558010410310142080c09a2140c1d5555a02c0c0c460b660700c0141900818801142c0c4000d6054a5010324145800d200d00e0500e0488800b803107106031030542c0042d061000503d500d0070181c9002010300010b95400248050700d07902280d454026000f45a8980246002c82129543d10b00542014069910145686610b1f14030501c04441c0c05d5400160702e05028402000f00d1200301d40e40148419000302ca25a4a0302586081402d024030454010303c0c4030360300c10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 41012198 1250 41010948 41010973
    0x60806070306080106090501150c08070215121303050910021903110607030b0607150b04050c03180703020307060507080c010e060406060b0702030d0e0a05120c100801030c030215040503 81
    0x4110b00304845404008001440c0c5034000502a140c00740115130b030340e41801c0411501c0382d20480712544041e00a12940b820002e082d40010100b4030000c2c000342000f0300102d0f607400d03800d00000c1c01940142c01c02c1c1c901481c0700f1299074054454000c2c942070a11610364100060030003402448551a0400c0141c1800102d120516000e800120116480c21552140c100050106800792091200d42c00b001403c41d0705103400c0ea983d44500001d41508400401c4e00c811903440b068480303000c0c3e2409003d50340c0c50651a881e200701c121082c900700c2c0d03202007c2540550030401c096240400c10704155007085c03030429507880740790030040c040b4450f03803145044942c038008485403071640108502c1e000303e120f020305001c0c2d03941c0d50790700c00359500601c0c801a52540180c5003100105028862460362800051721900050b541d440002c2c50f80c68070004510b215801200200c07a076440c0000c0c801d192010075080500443d4155100c00742c0d03010003408004e01a030000700598030040d03004d0040d00e00410000381125007401b200c0707 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 41013448 1250 41012198 41012201
    0xe04051005030a060f11030106210216030809061b0f030402040213120210030c08131e08030103020910060c060b0607060c0c0b0106030c02031c09050706080906060a050d020f03010608060703 83
    0xc00f074400b01689400d280b9070206c40b108003164100d07101c0f645d68003107107200d0300200ca94443d4010805050f0310360801114400e42c414103004a0141e02944843d012450042200e0b414208020131098080315010100010440c0345401c0c3c401019010f909240c50317a50710b01c0072400038401e11400d1207440380b030100001819840460300024640c400d4400030052008040d0035029117070320400703280c0481d01c100c2c0000c0c130a60100c120002403e000356044992500b1550040f404550002c4007503074032010000c014400e5080045a982c0c01140301300030b46907450300e007034002084110840c80045c400d81d1101038a0110341d9940b810340e0402e9030002c504110b140c400c2140a8240000c1542c01c43e00c4d91034500c0002a554006e10803040d00030441d8000c1c500d44004c06080519050f400e4000c5100c09a40d410240e0210340c0c10040c40c0d01409480d15850b03641d041100700c4614080c130040c41c45200d441042402d201d0741d102c0b031086040f220b50542d0030b249160310900000f805072400e0742140c90144221010401c416a15 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 41014698 1250 41013448 41013461
    0xb0d06020309160503060c090d03020a0c0801020a030b060a020a02132004080c09090c060702040e070b0406091401120e010b090702010c0905030604050a02011412040320030304030e04051005030a06 86
    0xa1200766110300c4d0f5038400b41603c0d00801c03100d0200c0440305002202c5141066100340c810b061285c03040c1e03212a182a0780d070713980307401440d0022941694080b46450b50705805208080303c590045880d60308212070000000d603a00d886a000a000310b12000b003407900c407900c40e0032922050183c40a01d006803040b409803800c1c1900719200c0d0308820321450301d85800500f844e40e0f1007406096640c01400351180b44409000301a030080340208d8000d6a01d0806c0f020b50300092013410098106100c02c00d91301d500d0010300078024142c030340142140001d902041c4182e60707040b44e0500d04104481e10b0105205400008890051840085a64010500710200488240c0c10341c0184a2051a502e0321100301340c581082c03659440d811240240250f118991481c05036008075070b40c03040d040c2d443c00da09203486d1030304502d5400000f00b82c0d0201c0100e4000a903c5580f0504c28a901040d101c08030001c40c218607082e1402400154600e00c02d50080f90703648003141000680f1004440986405800c03140001001c1c81e003407009004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 41015948 1250 41014698 41014723
    0xc0d050a0813020a1401050c06040b0402030d11060a051e070206100f05010504170106050a08060f0703110d09110301090b0a060e041a10051203070c0801020301080a03030b0d06020309 80
    0x34803400035020382c012810304a00b180c0c000c0d00140b655410b1001c2400c62166001001d0f0500034140720049440404200b0b40b445140f00c0c42500c0700c40c1c1070903c1414a0664510303020001d00805130011001d6220004845074804032108000c03c6030744507950001c100c2c40541e6008c041a40340b400c104095541c0018030310340110b014600d10260a03540e50f450700d0a072107403802420f000410400c400c01541c6001c0342c400c0c409102280c00015255070b6040000d030601c4199211100c9500701c501004520500303000d5040c0d01080741e060521954124140f100081e03c900251303030310303003503036405c111401e001c42103041510140001d00200808100f904021247c22000c6400105147c10300308045103013910028168020f5074402c204c01c4404900d4804e000c41240c3c0100071501c4031000601c0012295900700c0c3c0380c0026500600556034654403800c1115500a1365007148909a0040004200d5908002980b10380ea542514000401c618490002000c0040c8107202030521400403051010605c3c000c0707000d090300716 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 41017198 1250 41015948 41015957
    0x4090203180c030a08030402041103040c0303020f070f050105030a09080c0c130b0f1201090602180423010915050415060f020109021c2603060a050102070b0a03020903030c0d050a 78
    0x80101440d690395a660b2802a805402118107a80042c1e644406150841e01c014404201c01e00d01d1510035616030402c540660b00e450003402c0030000d01d80c051102c01d0205410350050032046003000040903503c1c4141c030034181004030000029244041c01e03805548130781e134030015059980801361a03266980c216030007054400c0034804d0006158a00c98403d501d802240540a101915801c2c006c00014624000a24804d0354a82d000b0000140c1c491005203409503850900d66078a0070404140700881c0c111001c0900b091041ca0b01100910403500c14483c119842950085049050f03011400c40d0f040313942d81304a4202d401e040001041d9041c22445c1000d0b54503565808000654484e030480c02d071a0a07282c00ba4000d603191440c440481d140c40c813400b1200d03002c1c40e04e01030322800300007100c41d4045117021090f62202022040c4007036441c1413643c070702c028a0244010581d007030801030343c40014440e2000c4030040c10340c0000d01860b17680f024001d699007001c80400b6500c014600120103007460303008920080018 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 41018448 1250 41017198 41017231
    0x309060507021e1f11040b0f030103060e0307050c040b010c0203011401030303050907060c03120902091503010b041a0d020409050703060f0c0503090d180f08010605040e0307020916050d0204090203 86
    0x10200019802c00b8840c4080028140c0b2005680b81e030020f01805c070300303100640c40c208000305036185801d005240001c2c641d07400a617a989103040040803915030442c60000c40d0000c01040001c580002850480050110b80020b454400c907801a2400d1041c0d940c0250035500b8100061003940d0b030750740304504890003624244110f540d1940c8003a100c2c0c1e020700aa0011840c200c52503404207118290301d054024100b480050b0501300d41c0c0002e40e07143d00884a1283c000500d40102c040e0303040a0041c0d0f4242e04041c1e074184040100d14840c022508007110549010b08100e456100640d41c0d650030045c60349801c041074480b00c58817410b00d10064010030b00d0001e807182c1448480e20201c1d2090f0102c0e44900040000b030070440003c241c04607040e22005103107400c80d94000201180003504c01c08070400a2560000010b00d4a2801d030601054407076020140c42950020300001c0007507181c0708001907000c1c05981c0e40c9992820600750a94690007485160400b00740b0100700445c1c0d0b400540e0045003e4000d0104003542e6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 41019698 1250 41018448 41018503
    0x20306040e190b1b0c0a02010f03051009180204020304140d0e0603181608160801061d042909061501022d0d02010c090902070c060807030906050702 65
    0x4509050a011900a8a81c010309011a540d881c41c584c0101000c0c4286440b8014021000d8564001e84c2d8001d0442e0031102d0008115030b04015000c00c07a4209040034029454142042c5581c5440340c864034091070340310400d0707840000d40e105203409130a500500c11912070a01d810642c0e41c281084980007458804c070500c0c4a9850300880c0008960356000306a036146548202c0c03118508054008200d1092040c2c841a10f144001050940082c041c500000c05496619841000ca410350643c0910030592400c18240300314007140900c40900c01ca000015601c54840f0320788082010940c03d20401d0175400b540f0740d0a002c4091580b080d000c0d4a89e881121b60503140c40c181030458141e08100b15001d0f9204400035100f140702c40301c0ca00184e10060800c03612a40d00c0320402802c3c96506216040140d54a950008000ea0010400d0b07011700440e81c0214241400c030795a40c5035405080c0a92014044076500165100c2d2194000300c050719403020301404a030500100c065a1414429100d80d003000131928200320 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 41020948 1250 41019698 41019703
    0x3040602010c1d0307030206180d141501050a05060c0708010c080402040c020316060f09150e010510030c030303020304020a1d01050a060c030206040605090705030601030b01080c0612060f06090d0501020306040e 92
    0x25003d0000f030162002a10715401c1140c02c2e48008031500134000008008062582d40a84480805014560b000703034410017103d40354200258580c1403070540e56400b00500951f11007001c1070040d43c1c415105c465032113642144091420325141c3c400c0b2095070800d941042e00e141c3c0581c006004600c240c5050245031110002079071640140400301d101c00016507445400f065031900310781c03002185031b480028054801e4441840543c1d11115031220141c0300c444561001009100b05c903031048051100600701811684c1e5070100e14905e00c400b804268010011034190341e5401158402400400c0b1036850b41e00348a50b000e0a5001d09200c3e0b28412100501c00240b41c2d40108002c2d52040d82c50340c0503003c50740e03840e030b036071802444081c02d404000d2040540c0400c164408220b10f030b001c3e6004040085080d850130074001e20388501840024000c406c180102c3d0501d000e0a260690860421030300340c19840c14110120300da0f4001d41003201da0100259100d20280003040d4000d602880c0d06403024022242000260b96 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 41022198 1250 41020948 41020997
    0x30507080115050402040305030d11090315060a08060603061602030d02030109140703021303081e0a020a26040608090a120908010b09041101121506031a15030112030507020303040602010c 82
    0x81c0b050300104034ac8501382000c0d500111400300c1c001080d600b001002c402292038445a954100b03031031005e0314203008003072070000d901c48018080003000b000075160a0340842e4442501415a2840031105290041510300a0041e20b801804a0340215160f40e5615a00343c094040420303001e010300950b201007944503102e802244d0f449443c1111440f101d40c51a0f0311800340c0e42c0003000083c8650520408103841000140081c10000c155900800c13003480c142c1040840312035141002c0c070100311102c60680740940300006490446070b290614000560318030f646981011300824004005581328400340341425000002c0c6000d03289a074008201100d41b01c0300340002004140e41c083d0207241c040d0321505196204503003096442c000d00c0004034500d1072007240701d0602041d0360001404241c880b2000302d0b01c05030340044846041012200d82c2c6000907483c04100c120710040c02a00c02c56001c1041a10034503005034125141c1c25070160071a40e0300d41c2c0d1808002d00138408680700200003500d010311014844080c00604 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 41023448 1250 41022198 41022203
    0x10c0206130602070204150509070e1003020a0c0b09030a090603110909040201050403080403061e021602120703020904080d06170303060d0f0b0708070f03060305060609100305070801150504020403 86
    0xc09140c1c03a510150304090001c4503088030500d40030001d100043e00d41e40107405080520a89040a0768242800c104802800401c1207040140143d5a000580d4074801190342211080c100169074412508081b5000030500d18040c0c968a403203800d1040d10729002006006105403030340c4d40c10040e0307250042217054403400035407044403c406100c0041185401c082050b04213105040291501d80d80e0f070382c0e546168001d54420b0b560303580e481900034903104d000c4a03510b03c890130360042103182ca10316501954400b013024801901911241f11000107040b010041e52000c4c44d001482155136203000d240a14041c1d2104500701120b0382061800a444503100d800380988034059005581550355010038000c0c0070300500c40940d0a581044a0000866282c00242e4000c1410365605406441c00640140104c4035259040c401c1500c0c0090400c04214049103154000a0880e5451303940c1e10b400e03000c0c041c8404540c0010301607001c0c0d0000000c04405c158448029013913022900311b40690b4400400c0100d00403440003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 41024698 1250 41023448 41023453
    0x70306080a080d1401030c03030e1005180301020903030d15080703150c0509040204090e0105060a050a0b0309030c01020a0f0e041b050a20010c1710120c05030d0f030e010c02 76
    0xc0014410784003a10660f6080140010480740500540c0d04194080e0b005907841a14540c00b030050641c00310a614440764155151148036108886c02000d034410302c40342201d0624242c500814a0750290101c80e18400004d085a84400c0c41d881c0d98402004407141240000040c81e00018125201040000c01c90f508840302800da404000c164201070070100f03c50400308541084850303020f030707076510240001d8601000000f4104111002050031203c024120500c9220701c0c200c00c004980d2255072541c291020198000d807a501d800e0700051541c054420400d0655001150071080c60b0750002c2002d10400481e030f1032010303030703a100022301040350380c41011507204400311000e50380454003450040107401c0076494000303140041941b4010100621422101e00c03a5194180c0740071160f400701461003641c0710301c0b4054405082001f012048418148200c00898022030403030000d1080c0391940100038540038060303c200d085500c0700286020b81d902c440002003840d000072030030b0342a414441c1a1004589400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 41025948 1250 41024698 41024713
    0x9090606100318060204150201110a0c0501090c0e16030506011d01180f051306050f010c0c0306050a020304140a030e090a0e1603050d020f0a110a0503030703020a060507030608 77
    0x28081503148021004003415129410810707200340c01c0c040c2c3d442d80ca00440740107031100d0404000099900b4010b40e030f04110fa04100d030f585520178540c0304845908000303003485000030b055458041c0c054445142d001c2c29004c21010005002015181824402e03076100004045100340c0d1801981141c0c416181140050b0008213055a00301d00000000c0c003d11341410305040c452407581e200038044d60182c12042240da500c0d50b0800c00360030031030000302d88009214030500c00035080c44041100003460610180c10400203800700800e01c409078100c040a55048441030295103015505440a54000d507401c6400100c003d403c180619004540d801155502d0390303c0b80c1d1000568401c0010f801c02c003070042c0c0c40d1141c1e40c8042e003141d10b00401481141d085041b26070b06c255440e500740305040c481b410a010056410002c0d10510400c0041600d40d05540d001c030407028100700c540045030b8104800d801c41030f01480300144078810b0680000790802c480e4841d210521480e0340e180c134100d080c1c2e003c905c54400319920020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 41027198 1250 41025948 41025961
    0xd1d040b0109080f010903030506030304060507080f07020d0602070b06040b03060601030f0f0c0207140102010e1e010b0a09090c090e0c0105030903070b010609080d0315030f0201020109050102040603140105090906 93
    0x40045840300014540b041c803054481101c182040b06200406003269901d1441004040d01400741640c07108084010303504161806074040d00611036081c1c018031191f40059520b072003200d0002602c6410781c01412696400b8014a0640c0081d0310920045c2e4621040b00000307400380c5024001c0303280c03d1001501424003511000c0054014200d4091103241198580004444c28403d5200c1c40d02044901c0c1c1c01803141d549031484101c100d07040842801c1c111b904040407801d160708002080f03031317055602d440038640b20090a010b007401801205280f40d030058075890b001842001640103c480760740130340c480243c0180d80d00c048100b00d40c0b6000c00c1010315004543e41481543c007950186900070158410b84c4d241c603c0983d03035210102030076044100403c0c141c620500c00d0307003020405160801c006040c1084000c107c040e4103503804030940702c000c2141c85101800c40c1117901c03e4200c44040c544c0000259262074a0300c0025001d85280030382c8229000303030714000240501d806400b032400740310218054002501da40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 41028448 1250 41027198 41027201
    0x1404020a090b0103110c010f0605030d09060c0812010e0610020109030210091b0b07050f0706142a010614010e090105041107080403030806010318030e0910170a050d1d04 74
    0xb07403a16042c1950380082120b07055040c3d00410620551600008840200740902c0c0211051364101901070341c088019860b01036000001482500c8540c285580882854948846540703d030951080501d5068400041d1011034216124020002214103a40c040c55415040382215039003c00034005034440105044010096400048840d005038401c003151748000403105c00180c4940c0c0b10440400700002c0380350900c00c003030044800031113000d00030f051318070b2a01ca0018814460b0001d03110190b00006100c1083c0c2a1080b01444014000c039000c1055400d400c2da401d0003421103114040d100428440030b02d1983d0301c248001c3e00303e500b0080100500d40d0800050100402c844404000c1801c0708200c034070b021440c003501a000443c07003640c918103546824000141503810b103940034600750303101d603414400194100700b554110240a07103044c2c103d80d0f2107003c540c091082c1031f0f00618261f0140c1111100750b000100e50802103601072070844901c9071070580100c903c0ca0b02002600e008511b00350081e07145190a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 41029698 1250 41028448 41028461
    0xf020a08030a060b04120c1e0905060409020907031d0304080303221a1b12040210121e06060905060f07020a03060507050304200d02131103090708011404020a09 70
    0x40100c0021003907141c4c203006010740d109402c201c40c08104409106e0800c0204120b060141c0000c1382242c00e009058040e006c81c1c07503001e00500e0075407130315000000d40b962555032020610540041001d103842c00c000b80d0141c020f05000244105a80100c0440c0c60005400000c40d000c0f0b0303071a2401149540d54004000160b041060a4081907940b56110b641c00b00c0c40704643c020395003100d120459120f007802d400c13010300c1d4030342021507a00310001405116460030605030150351194050b01d001c80c0c1c01070560340031100b50340d00c0401c2d1036030f043c0740000100240800c519040d541240c03280c2d04200c01074849000781c1e0703101c1083c0f085640c008000c2085903008880e0070007400b8911301c0034103c1c80c15076032a0750340c59050301c90803200d000c0011000b10820081c4030b038030300c0a40381001034100e0030148580002c01160420351082400f90040001894180d101c07aa02e03400703010b0700e00c60641071a0311380c100300450f41d4482c045071049503030315802e0149601c0400003020300240200d80c01455881c0d811314007005603001e01503 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 41030948 1250 41029698 41029711
    0x603011e0b0d0614090f07060912020d0606080307020f09010f031713180b040c080a0e12030f10081b040504060e0d031b0309020d020909190803010501030c0f020a0803 73
    0x100c40e40341d0b000181d4a401012550310000d034000c0210b04d441254146005503c040600c6a40d00a1508228560b000076a100948000f404000380c158040c0c00491141c007254580102200d281007000224890b000c0054100f00d4801c40d00f80d6201012241007002c01d410038041c1e07520041090301c0800014001c498120220314440350003034200900d98140d284950401e520030380300781c0240081207180b40c000d0710400b681600110b90400003e2031200c0300605a01c00244500e40a41c3d54680c0301803018801c1000032200700b9055080c4c1e0f501d1138070504014284900740d070001782d000c182c8040400d07245000700c0d002c0521500384210148505e016404c0001030703c400340c410345019a40da006c200042d01c051210f00144407154501140f24030300b44000c800c40200e000c140104140c5021500030040e5078410208807455012940d064094a4480000703003800f028001d08202003038481c00b00c108000d0288040c0d4121842624101301c460361620040d55800d032501c1c00a0011780003c0500b00025500030f01131b5801c00b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 41032198 1250 41030948 41030959
    0x3050d0e1314010312050c10020f070203010510050109080303010e0a360302060903090a15050910030501050319020112050a06050303072a0609090f020904230603011e0b 74
    0x700644210411511012441e8661142100c0107100b8040c0103c0c4010072248907261851522408411a91b200e50800411110049e00042c02d06013040807003042c3c40445170020002c200904000c013040311201c81604c903040c04104040300000f6180408015603049504032000e01100d40d6500078803d00502c056a80c145100804140f0412401d9014220b4944101012203140410065040191070558001c0100d0401d134000c0100c4800d68485041c9031044802c400c0403d03034106c60411064841d40524000c0e282c2043d410250131443c0da0385030b040a0304958013034040c0c0300c5400001c00250582c3c146c108010307001c900c0d03036a003105000303003140e00880d40308150351000501070340c031500001d007140e112420964542e80301c2252180b001c4000c18102154030b070088581c002981c5172500c00741c5a00250b118001c45240d48559904000240350120780300d10400410800c81d0514150003100502100c2d46096035046501000681d64101445000c0303512003041c010f0044505040040303409011010701040d00711 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 41033448 1250 41032198 41032219
    0xd0f1205040306020a030506120c1c050708060c030a0c0c0c03110d0c0824091911060307050a031b1d010207030503070503040e0f0601120c020309031c0e01030603050d0e 74
    0x6103c82c40500000c0a66903000300303e40c208541088101e804030040154590440003890000c0d64030021000c03205030700e902d80d0000400e0141000e42c140880307070380114560300507103042000c1d452006004610580102c0c0d0200000702d140c80b02110840d020b8407000382043c1c180d03801400414460000032141402c020102c249100059840c00b181c03214030b81c0205402e50001108800002d00c154040180041c1d28488000515000c10030300d070380300301e16241d131034002001d030320410203000d00e4a0880c159032401030501e0b6903031300b008200100260300940d9004000f902d010800b60809210412140c04414a40c1e55440500c0000000711040008956814154031a5440000009400b0f002918070303540164051510340d0b16014001c150072200602c10100342e901c000400c1034503a0040011035070307030044200c0040d11032680310b0b00303030702d5881810a00c46c6d06200f2075104500e040d00018501c0d0380e0840660b9170580c01110180154140c03451808014820303003103c070001102038801c100c00303400240014594001d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 41034698 1250 41033448 41033453
    0xb0105010c15060305070906090504150902010219051c0219140f06040803010509060108090a08070c051c05010e01090206070602090103020403080403060b36040201020c0a0902040806060d0f12050403 87
    0x1283d816031302c00c07520364000090400044c54035102d85001031403c8a4140a0b61415698601100351b026480c03c0e81c460795a0f00038010b592080052458030314805000c2d007041c00507400e0031661000c545500b045600d50641c5079a580a1021407910001e03001c2c034030110250061566a01c40c44a1060040c0c0407511030400350540140d02049014010f501909044e03580703506050a204d42e0300c600401e4a814080c2560a01a81c0c01000a00101294001c40c2c416150141440c003c422414142e101070b0340004454003488840b0290803220000728821402000304580d0900000d080e60086030001c1e5104809124680200d90340c0c1c0c0040003a20414074005240548950324894190401e80060302c9035503803003090ba1000d08011116070741190042d011022604185242802d0780d0301d880c2e030a00e401810034408202164020001c0d82450b140040c01c02040301e48440304200250860700c0780c1c2c041c510683e00415030b14105480000c441d1034000300d660015601944442040c012180c1c4034908000301007000201 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 41035948 1250 41034698 41034701
    0x717070c0819050409111306031a040f0b010e0f0d0303020f09090903040807080705090c09030106030803150a12030f050c0c031f0b01090506160204020d090b010305070605070b0105010c15 82
    0x800c1c0b04030381c844903102d60402d0084021190015064404d80604021300c1c01052280c10101e0b080310020300e40418007940403180030030200700c03049820707401c1030500340460000e000b5a080190303102d0080e80c0708180843e503001080402035a6480054100505545410109202c0c0d00140010001a904940b0341802840032580d401c0003140c410310150004a4140100001802a04000c1116000030010141030400080b50750b0400b400b0345c0c2d8101400161809503032020f4010724000e41e0003210a80d101d107004403402e00002107110400d4440d0886010105112100f01d8498000541503550700004200e0178009840c0c651020040074810300c681281441140d9040214001000b2010810305090405405510075664186051810310642503800d01c415103482080e50135580122511422042c46800403600910504074541541c509000041c0280120703403d005040301c7c802d00865844950f6183e0480e4207000b030710700043c034004495004220540c81100c2210707805000b00e21030111900031288240 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 41037198 1250 41035948 41035987
    0x6061e160f05060c030f0109020a030b030a030809070609300807050102070c0b071a0c040b030f010f0b0703080f100504020a0908010605040902010c06050a0e030f0409050717070c08 79
    0x4501c010150104010000240100703034000008000241c2182400b005600040505004032485103601043c1540218441d4221000d0200b01606aa201803914280140030003070464001005200340100000c01d0341c880d00380340088800711081c074080101400ba1802041c1c0c2d803c85052030041e03920304a9408504018002e082440c4a03000050395082d40b0320300540c01904075070219003003c01c1403004030b02180191b0241c14070350012000308142a55604441009402640c1151544c40310200070401c4081241300c406069034408141000a140e94410750030083c4641c0c0030040c00a1581c01c0405d591b15224607000d90052402e0303102c1d4481c16182c902150480c2c00c07503018500012002481081460b400380b040c2409440140c409101c10056500003a01c0741880d40801400c050380c4a0000d02d8481d41603002915140301c03107080c5c81e602c1c20b02402d40c1509800601640f0b000c980703040041120103020307007001d0316032808507000503649607540c80f0255651a40213000b62098042003180c074000700850301449 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 41038448 1250 41037198 41037203
    0x20a1106091f082404050414030a09030b0108011503060509100c02101b0c0308060303090a08070305010c0801120f0609060c090e0610170c0f0723010506061e16 70
    0x3401003101040c00070b00d41c0b100a01000394a0316106041e41c0460903003003c0b1080d01304107a6000c82d907500c036858403510060100300369100c50701002c1024224075138019040070890317008540ba40031698131126850f08843d07900c0640e000b0240288010400180c8130307004250f1008151055506444415286506440c9031180e010010307004640e04294440386441541d4140d014811340c107c800c00041e2014090b080c07a0b01c8041d06000c0b0f200e00117043c80c0d5040046400580001d4044018595280310281d510345646c00204c40650801c4035454201d07108122080c1290f0880d01e206005204a440c3d4058003008004c0c182d038181c0d12800303000007040c05802150b00e06030590380e5448046e841c0c8a144000800003821051044010164a030045c9031301000c0c0c810800030f210b406405684440122100d0752140c1c90408020200c0400c01c40f0a011850740d5542d07125074500c0080782401c0001010908940044405540c84103003446181c9504019000e0040c504110294451420303200080e84144208460401c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 41039698 1250 41038448 41038489
    0xd050408030a0507141611030f0313090b0a030f030201021b100f0b0604140a03050706021f021306030b01050c030301080703030f17070c08040306020a1806050a020a110609 75
    0x180182e0031141d204065200d44185440044070013000c105510320710806240d21a401d840d0000e40003402144030018000e008001c0444440b1010380b4401512600001c2c0076180602d003417a030000714052103004207440006e0060052204c1e40c116078034030004071103015065007190341c01e0168240d17240000d0b010303001c00c1ca6100b0007009800c29440c2d20b201074500c4111103403a0542012034800c0300d912084140c0d0140e484440212010410481c00308120715130b207a00207040e42c4140e0f17000140781900860402c03030b01921213624500700011500e01d802a48500e4035180000c403003400007040036611980c041104a9014544a0300d0020045802c03403a5030420382050b00e050f007021074100101500702c2c45440c0001c810381050300134049048101c0d034000070018454014441020100c20802202904032030203168005000c64130b943c01110001c00d00341c074048413900404c0591402040d060f002d002929500e031000e50080413000382d650713500034003045030701078498001c1c0051108038503940da00006c4105040140a1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 41040948 1250 41039698 41039701
    0x2010f090b0c0c121f020706140705040e01060807080415020d0606020c13060302030304120302010902041d06010b04081b0f0306010b0d1404020109170f06070903060501080601050d020111030d05040803 88
    0x7002400d0500b030300800d5043e44000c1a0002c1c0f4441704142c0602039038018001621088903041c0240034007068110109003e00c1c880800c040c0e15005005481904c01e02c2a20b00340d16071f2501010742e43c002c0e05980e40c20114521000041c0054070101c81d0480d00b5082690150910444000c0307c000d58003550443d4015810090705030b000c0303050030f00c44211011070514091204500d143c01180d01c4c0d02c80ea000d803941e420305558051003858001d410140c1c805901400400c24003805000000b10a00307000ca1100e218001d4070f00004071500c000003950244e41e078034406008401103090203d01c560001901554204500e1000408030f035030207109090003890311140da0b507540c403503001700e090455000c0c48103040910001014400541d078002c004209880514000401d030b86184079400e864106c1c1c0317004800481c403031501007056250303110b1040d00440c1c0c42800700380020790b00c42441c00d4a420b8240540da800c81300041c0d10344003544c0304d8103122005044810640c0d291101a5203e481900d00840e000c0d10400c00010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 41042198 1250 41040948 41040973
    0x4120c0c06030f05092808040e0109060302010e01020d08160c120201020306011209080f03071101060b09040e0118111305070305150603040b01090213050909010c08010501090608010302010f090b0c 86
    0x1480b948090740345c0181c0540d9050303142d80000c0f034840345040720000e00341c0c280d44810003620004940240c030b91016024075035a910745a02c0040c0c07181d400120b000480d0801000000cbd4000a5145107801481c1c41e141e415a481041d0101b8407039400011000300b2006031a2980480c00602400d10410919800076940317240c01d0001501b402100c3c1020780c50207181019a0300454400d0050b130344040d24081440d5a6511010340403916506140a2401c070f80d481c04200180e410182c80052801c203009a40c140001f074502000c035400c98025070840c0301505c00400b801b0300082d01c50700000c040380200506c81c040002200d40d1002c1103543c120380900c0441d035580d0902030052501e8000d088002d070b00300c9000e4918074150b0b0328a5400201846005a20b54012030f054140740320501001002c1c000192031040c0701d07d8150b035814041c020b0759007614007054000c0c0011071103520541918040d20f01e6505c840d481ca0340303581d00440d01030b52400030305000c002071104081804a0500b0003440c0c03076070b40003004040700e85106 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 41043448 1250 41042198 41042201
    0x90c0306090106080403020a121101020d0b010906090305100b03030c0f010e070504060303120b1507031d0307082104051e0310050702100e010b06130e0106020a0b04120c0c06030f 78
    0x41c3c00800c00c1c030004408110020fa40040c000c001a540440f587d4840c1914003c1510b880140c44181c0e4095400840c11016803403040d40701c038907203590913070f185000c6035501c410544a241041c00098096003104810a074420640c0d088a2100f50001e41164941283c10149904002040c00c0d5000180d454005074141d4000410040b4040c000841e006c0202a1942d82e02500051086903221a05501c8401c03200007550b45801352240c10202a20306070b41e803041c6107002054003080d040c1e41000390304d406603001c405040002e1083e0a0380c10450041490851956211038084000c03984c211170084108004529034640071180c3c1a00c1441140f4088000c1f002010141000169000380000c585018100445644c4c0080e4884100740392802c0000d0120303143c07000314054801c415115070082400260352031400b00c5040c1900886000c080708a416988498080343c0302d03018580058074685403500420f010031041070910007540381300c0c02c0542c0e01c04a2903840b0a102002035003d000400da440408040700c0c1c209 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 41044698 1250 41043448 41043451
    0x6021201151e08071206080c0a12020105030c1303050703080c061503071707080303010f15090605030705160507030311070906080303040620070807021003050f010b0a050702090c030609 81
    0x180e0902c02501c407030620500b40150407254548003000203000116134000d00503080786100852814040c405240c4400056030380e0240150000d01401200c0000102208107004003090958141c6da0f80e0b2030768980381d50411440c0c0080070705400300d0112800000c005501048110000d600c21a4515220820144801e0070100c0050100d1180c5c004082003881654022800a058400400c3c6202500c00501c080d2071420a00e900301030510300c400030002c2110a08081e10b4422103055001100b40210149801c80b0621003a116002c04a5010310110b29624001e5025102105584103080440143c50301d03107a1900c50641e0040c0c0104401b402c035820244000d000c0c0c5005412145400d0024500c1c00242d03e0381c0e0311004002403c0d80381c1c2d80d500ca07200054416120341001110f02d4201e903d075925130400c412142c3c03280307000f24800c1080ca40003691050080c040c843c0324031908401d45102d80c2c6080200c1e4a1075000981900410108110000050391100d440502604140740f4640c1c46e0b207010001d02445010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 41045948 1250 41044698 41044739
    0x80a050106080f0712020708040e01080c0303040308040501052b0902040b0f0a0312020114010806070314010509061306091514030f0d1d0d050f15090705041806021201 73
    0xc00c1c1c08003ca030070392039146950801001d10344100b21440e49a104402406117080003408a04000b0300080c007065201c040c103041c2e5000d642503520b5040040304240c1d89124a1000401c84c00f4180010456907004402402c28a90b070343c0d22490821049030a0300112809800c8400e81700d680d0b0f0038050055042c43d01c43c03401b20250540c0c8884208070700d1000074a01d02843d00c002001083c14000f1059803501c00e4000e6450444008040005075071200b90301e83c0c98440454507440003914142c40341d850545036850340c6040302c1000d05440102d0700e450b000d01c070b203000300e00c8228000a03071140400900603905100d00300801141240c0002c40d81d0408001e041c0c0d010100c0b004a00c80c2d400780a02d00794024000c071390011100068141502a09020400c02d69220700c0a1510b9601c8a200c44821080c0700b800306107100034920302c100380d5410941c07202d907030180d00030240c2d2600799507405603400703003d07a0515a00ca0800003213580f4040b0310034a600d81d00c030026a0300006420707041d10891001000f1034881160ba030b040a14 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 41047198 1250 41045948 41045957
    0x50709050609031513021c0302010b0604120b071709010207020109050301020f0405190b2106010306140d11040507090302011b0b040f0311120901020c01050309060109111306080a050106 81
    0x4101c10001380c0d5a4078240200e0b1801aa06011610002000c454030310030590113000d555610b030001c40759240c01c00c0210400d50141d401c0034400451460b00b0340031203003a02d80c5015480042240c40d1104006c0a00050100041c841810100140020719055451140426400140e51000d40d80b00040c85500c181c3c1c00a4041c1e0b00511001d100e034280130701960161501a40c2240010740186c002c1c0c40c00f02031560000c10600b000040035076203a0010900c07415200410140e800b00f43d101c441c01142103030080d20981036884c0c080b41c840a41d40c54041c21145a03103004a03064070645403103000050071907105641480100d01462020001c42d60441080558401030075031507283c030101501c5428544000400080008500d5810b000405010782000951001c8903021100920030b0b000300c400c084c1e805541264050b100300c5408070740d50743c4180c044911500380380d0003411142e460018824080e0041000401c1c0d60032052102c03040b00103d103004100200740c16603c1000c0c0d400e00340000001c03a82c060b048a030811 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 41048448 1250 41047198 41047207
    0x512060f0c031b0f0d0b030a0b0103021003020c1e06012108090a0306020a0e04060918080c070e0403050406081302010f080417120a1406090f1e0a0507090506 69
    0x401024403031581c06005240300310355990714112400d078014010000070310800700128071644c0042c01903002e4410300450b01810015441403004050f07451003480c0008084c0c4184800510042c06d084200d503084075200d0602500380049400c01d107050010101c20078034080c0d80015194031001c41045070034010042035114a440c4010f41c215101ca1000f0741c20b0240c4400380020346440c050b19506c91540007150022011910b9081c00600100403d400b050f4141c401c6060a00104107803c19205100680200c0103400707941c602c1558034101e85810140d1121028060b80e18001801d0507682c0589104a109540d201d80c4e450508001515601000e4492803480a0303c0c41c2840c0140d80019080d10102e106040806841d512403401c070f07200310301c2e07120f5454402c0c001091840d034000d0b00c55200c50040c0c0041d02c0c14400303c0c946604c0c1550a1100b02c03004c0340d01c10112004030344a1020301d00c0300c5030000342040320000c4e62070240315034080d51201a1064101c00c1d03921410410341b203500c010100041c0604903007a6160 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 41049698 1250 41048448 41048461
    0x80a0b0a1506050a090e0108010e011a0a0608060f0a030b040308091c050c010608030c010614030c0f1c02090f01030515010506030c0c011b050c15090d030504080d05010807051206 78
    0x285402e000e01424060002128001140540c00a0000b4440700b07164940960b1107105260207031240c0a000301003036081a84600d40c5002038500d032086a100a001d11101764500801100d106601505c9141c00c40703003000300c944a13610f40e202c202d0702540c0112100070560405141c000c12101c4004c000300c80b95042500301d1811480c86c64204000006130b442d00b603440712411181103004000c0c540c031080c4641300011324203e811038190070180032640102101000000d50005040d121080b045410f680800d01071442c1030030b4640728008415404600201201c04266036002c6014080c0c01d030703800d45208400500410401100b000184c580301088010201c46501d014041000703400003800001070300c400420244074540c4258407100600400006030400c88681c8d07400034005030312055180c22207014280542c0009090740070348500a0001038001c050354208801c08030014080604110350404040101e480d5145a60003201d01130f10f101d40141440c940f8200807c980c44159a01c083c80c00d42103902007201 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 41050948 1250 41049698 41049731
    0x304031b0c09020904020c0706091a090901052209030c0c0501170610020a0c03061a0102030f073206090c03010e100504030e03030f0307020105061c03032004080a0b0a 73
    0x7207401c00d00003d1388520107000081e01a005920002450384540c1e04001400d907440202c1c4800c9440c0d1030381000540c520030643d161988100c24002d5040700f001401003156082603031000c0d0850b6224050401180349804219041e5805101c05400140c0450010024050381404031002800c00342805281e000026038252080c0d103004222520482d0f4aa1094107a94001d00403a100c40350b1142070096215240d1410b00e001f4050302e2070180001e6614861281c141d400081216503072000c0616460401ca07003649e94101416244401c8451407607510104500c0c280030252032086440400080c2c0168a40620000d00d0808403115042c841e0703051000c808003000011802030b1b04515180004102d943d51401c0641d855034171600c07160342520002802e18607040d0703101c014500820b0254001c0c0915104c0c901001400c214203c4615a80c034529160140001c0c041d81c4040c00d0440c48c400e03d86131640360401020782c0c0d6041607020070120b4108249650400000e0303403c0e92340c07007500c481d010001010100da00300d5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 41052198 1250 41050948 41050973
    0xd03020307120b03070f1205010e010e0703080c1005040303140a020a0e0f04060b07030206040506060d02060a050d1104080c040f090f0b0408070b1510030606020c060a11010f020304031b 81
    0x2010350351082c41000c251428010031000d0303d0010300401c103550b43d880c40c0001f281540c1c07105641075464000840300b4464180200300340c0500b424010039080d4155242d030102a8085101c2e04000c1c81074091000820801d8000c1038480d90094400049405a10078402485400204024200c0c2c1c8100b002410094011a0f038000c1c1e010b050b60107040b0203d820700031400401c80c5400650601d40042003200030550700141d0342d44118810390039140143c035448140b25841c101500000c4d4007081c2401000c41061040e40504421030b0707403410104441e0140140313a1400d40c0181c000d0140c5400010341d0074030b2404d050040101c4555120410802c95446459520205a50000003411030802d2404a0306000311070f0141c8072200d0300070300c2592085c10041b03604044402c440c5440c2d4004c070107030303110192a54000c1c410001119026000303003142c400711004001044c1e10040035003090040d584c401401c0d40400344180b0f14800340d4420016030341c0c149400c01074002c1225640408035400712038a500005400030038990b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 41053448 1250 41052198 41052227
    0x8060403052a2503230f06010501052502090106030501060e03030903071e091a1002010e0a030e2e03060512100902120109030f03050c070c12051c0905030d03020307 72
    0xc4031030003082e080031207800f42035031001c1c201e0322010300c03120800000d400d0044c0800c03411000701c4644035100c44e8a59141e8400344900e42c01300d00140000c246a00010315000c400244e0940842d210701010b600041140740c0c207030003d4001907030b034000501c5415003046501081b03e00c100e0045040041034000a6550780e0700d401191412235454891403108035440030680e000d0444070314188456010619181c0c00400704480c042e203d141e105441c809200d0062082d1011201f00a01501031038242c0d032001e54050942100d800d4003d524044c0d01c40d1203605000d030041d00030b4003550f0b001c641a1100c1000170151000364000d0342c441e0192003c0802582e4000035549115185101c000c1212291030001400c28240c1c0020101c0a5003484001410941d015040d2005010991003c202649441084829034010301000030200c0250800520403034904e000200700743c42c070803400c5545400036204245a91003420302c500d008201a90018031076450284409020040e0600c2d04504505d8100c4005043c820310910300f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 41054698 1250 41053448 41053483
    0x70b07050106050a060509030705040204121101050d0f06030215040e0109150f030503030613060b070f06020c010e06150d080d0b0d0c06090f0b030c04170708060403052a 74
    0x200010050203420020040c5001809584125550240502503a00c104107140c03003402401c0d0086254601351003944c040c3ca80d802d01c80b400407500d039a21104032a2881032001d050100500031544080c5503809604a4130188800120304a407542c818406e4550350750700600c041007800c0c1300c03d104ca512490f18550455507143c00115414403407800315954800107402807503041000700c0011080c0040000118016030f000e90f4501501d070789035001c401c1101d90a008500b450b480400840001c00d0a040b9013017859401803030010310b0b041c5041c0030103084a86101d4410040e4004c0402c00000c50f19000e9001d4150308140d030114042d02540d03490014034070540e2001012280c3e9419071001c1e0340c881002d260481c65101c0348401e140341d00d0f000064240035180c404e40181e00b800c80c41c007061103090301003940e0041e4503100031107091508004003102c55600000807400c0300c0c85004400643c1d02d4040003914041c0740a501c4d8995586071900c0422241000340030115089401458801080d4100150a0481c0d4074000d61 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 41055948 1250 41054698 41054707
    0x70614010509040b04210306080f070f1406090904050a03020607080408030a1113091b02010e060a0513051005040209061e0f010c06050108061005090c0403021905060706140702010608070b 82
    0x20003110b1140944803d206c100300d4280342c050400e8040c4c0c0060242d901c16021264080702c00e020b01a61102540140b000c45444c11908021007a008221480c528030020a450700b400a1080850405a81200c0c20383d500d0740001c03007407020b150b014408076401204c5450704111381c0c6003036182c40f1003611000d0f066440c2030340d840445114040b00a825180904c0301e9074815101c103603503071441401900b03512100d0320002d00282c5510605600511402c10f074600c184000c1c11a560740c0e80d80020007800c0060101035080d0004e042d4800186c4240082e4407000421b100004240c1064014042e00d9003004000902544007214500c00c3c1507072406901c40c0c0c0040803a81e07540d00490110040b1006212420010308031828000045210f5102040300c901c0392800c1e411003800245d0f95004c000841406580b4800c980300c04020600140c24044000351300b8441a5080f40d40190f90345010465581c0000b40c242e880f00d980315144043c0040a0311a03d80080c0144000d002c03490800740c0854640c0721074854050b0f842000603 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 41057198 1250 41055948 41055953
    0x206012d080a1505060d0203060a0209060712030c020d0306050915040b06180f090709060f09150f0306050a0506040902030a0b0406030515010815060409020409080d02070614010509040b04 82
    0x2030140050a809019100e002c0c01520b00314440c1c40c00321552184103400c2500080150a20315014950290020000c1c0115125114840002d520042d0b5090308402d04025060201d0701c00d003046640b44216aa001407034007418000241071401d2052102c0415052003810002543c9103926140c1080c40020301e6006800d52000140c0141a140c040d1904800c0c041501514069040004000d2881c2034580d000c40d80000300420124900843e02c003004510708050601505100703c02c4450340c081141401186251544403544c200c0700700406040024422504030300b041170f40f40c0121001020305032202070401d82800009005801b46008480c1503550101c0002e1a2500503004101d0607000900104061030700c81c24520707103c0303c041c02c0c0c0e0394850840c1800001c2c841e03000a82d501c89100c07036503015042d45e01c6450401019020740b1a00743da006440d18a4a808181c0003c0100401354040d0380050b592005031400200b628012400c0c03426511381507004002940755542200d5001740e11100210440e074442c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 41058448 1250 41057198 41057279
    0x40b030c190914040201090314160b0d0b03010b0a05040207080708040f080d0e030d12140702060a060806130b0414030711090108010c0906110111031015020601 70
    0x22840264440100721040ca100c1500d10040380599981020510800085418000700385000742c5000380000c1245500b003010035601c115050310030405e40140c1d6800b8107003c1c102401d0940b20781041c0f5488100140c902c540302041d1040d50380142c0c1c250001e10008031714500280403002144140f40c0078036000100c02040003020401c0300c500541c00360601c0d488940b901d03200e0340c000c03030b040c016007000340708986108660320b0185114001c600c000034003c09965a0700d4400701d5400180150503004191940324001c240141410194428203a9078001d06251800b0404803080d2000da612410340c41d0404018090309021072480765400b160010464525503c9600c1c02d10005075132518108000d020106056081040d80e21803400003035021201c560140c0d07280e042040c02c941e070700080c030380c0030070100c0a04200311405140081c251080b29800010050928215036109078022a503a40135803560700024845c2109041a15003104000c3c4000c1406604043e120180e80d2a46880640c1c0705d006001c10001e286280b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 41059698 1250 41058448 41058463
    0x801080f0d050d0f020c0303040302120310050123190f03060b030f040c0509040614100b0a1110091104050106030204052206150302030f06120a0b10050a08071a03040f02040b03 77
    0x132a03003c42d5603081760211903440381c009840031001030145420240d4a03500703803c1640e00500407050703a10300540c07501c3c00540e0b44043c20310355041c2564100c0c90081e01da4100e1005080080c101d01c5030503c228040798801003900010130f030f10006041c41c01606114000c1c00209a9a0204900c10101813a803900d0074400c103a20a1644029400b1140341c0c20001002202e07080041901008002400349480754003102c14000524015800044400c1c815010b00d5031091614041000807001a941050501151b62003542c015000a0b6404079401c9a40116070500e88a0781d0300420042c5011800d2174109030001d10040304070300c48043d031003807a19500c012004644e0b001c80028100a12100c000e003407603060280c007a4104030381003003c8402c4400002d00d0780c10701e00c00c1041042240307000307410412455551507044440241400c1c0300195100c0012030700e501c0303801c59200605011001060168500324819440c80c45420300541501e80078801d000001d041480a03505550303048030040751800000b4003086c40c2100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 41060948 1250 41059698 41059721
    0xe07030506071815050a030c090915050102060a0b0306010303050304140313030201020c01020c2101090c030303140a0b030c010503180106060f0e0405100e0403051b010203070801080f0d050d 83
    0x9001c00380b05800e42c028442e0040342642d0311100320303074958443d059031003602d0040b40c03540400c50800c03484199070705c0b0782d05c51034040900d82017600c1555100d02c070120880306030551600390032808080c00c3c031040d03030104100d5034450b01c0040140300f0b104e03040011903200c98044c44003c06000010001c6001c0080480e00c118410340d12400303c0b80c440c00c4109402c0c0310110207200990160041c800d0b9031440d0351000c03c0104046602801d44210303448a5040710110340340307078000d90000e55620854000000c02c110b2305c400045001c0da8012502000000600d0310071940603080740012850040ba40080d0f03200440d0700390040e41d09003005600d0303a881c1000d0381040310482e15030110a510f8010003081c0642c02007034074078410307485903245c07000642c1d00400c0c0b03c101c075400e13148090740d0f00e803104c410070504000e0384825074041d120386001800c100300c00c8034542d44140d5051103614a03940110400130042e03032102c00c503401000000018050200034528440e00c4206501c14a410081c2c00103955550b00440c1d00b1000b070004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 41062198 1250 41060948 41060953
    0x703080405120309010603020a0e1014040207050105100e09060f04030507020a050405040f0302070602120712030204080a08070203010f05060105190207080a0b04060b0109061704060b2206050102030c0307060e070305 94
    0xd400300c1424006d0032180012441b07410340a02c003007150171600c40030500c1002000c00111041e030400c070381c0c0c0007140380c1650190340c0103800f0040c86000501c20f0144034010201c2003145808581021000c20341e0580007040341555034030900130000021740741c82100790000d0b014206255201000c3c00426900c0c00280c0045801a04240c1800200f00b00b034406040168065402e480c00a621050201e03140c08404a0001c5008418400400031584514002e1404e5540d410300510f0325030b5481c0d45030304220507400103039078180002c100001075040a01424110b20700b506400c000c1d074602500080d10314042c01090901046103400030214150007045028080d0408104491180e1400d1608000700c07074049808803542818900b089001d035004003e8942507540d42d40314414408600004c03044629401030060f240107865070204100ca0b1a03400d0410042d00c90052083d05010100503420162811507105034110340c400c01c10009001004402e40c0e07400d69001c040441c0d4902201c20352803038400250405403450 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 41063448 1250 41062198 41062201
    0x3030815060412020102060708010f0522060f1406190309020316090e10150b031509040f1a0106050409020906040509130b01080a02030a060c0c05070801020306011b0807030804051203 80
    0x200d4400c3c01e000300c00c80c400d03400c8441a603600541142c20302000e11800f414203106440512062a0145006501c181402d6503140d6a1800c194490203507100c5078010408821007160030f2002c0f251a00c0401c9204a058424a00c1c001e4003000c003402d00b41c211412801050b07610f240041c210741c1d051080b10088c814030b6185c0007049490309940c90041940e803c0c2245031f80314005403008d2040b07040c010000d84402e0301c501c10180c80e207400b08801c090380c401407808403017402910f0302c3c107030581e9490f4049001d580501c0380c02055020031703d4080300a032031103428047e101d010311004211240c0e11004840545803050303009030f210030142e80401c0550045030080d81e4024103480070410280303400c5100c07c54960068522401590740d0b0400180c64410125000e90036420903551040400e1141c2c00c0500d40c1c01c442e01d09004100126200c2c64240b940e00d8001101a94000050002540e0301c44c0d030402005081000300101b000c070329070740c1410504c0754060040034011000001014080c050141e043c6100d132226000d9942d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 41064698 1250 41063448 41063459
    0x7052109030913060f0504090807051504030809010b0307050411160624120b1302090a1a010905011e0509091305071202060313050321010509070c02010504030308150604 74
    0x12600001c2d8118016200841058039105036402150b04984803882c0881102e414041400003038090040c0a0b12115010801c80c800510200141f10700f02d0300d4846412030f18140351030000c01201000d48408942ea0508000590390765002c95035404407402140c0004694400149616090081c101803034141014401c442c0c0c24800c10350001c1041c40600f00c800320341083c00304d800304070b074180c14050124000d16070aa502d0001d10385505440e04845036810009807815070707500192041e00304581e0403440e9921079452a10b820002100380032070b61000d0030000f0340c1a081c080000c1500c032140c00003840c406480000f090001d4000c502b1100e400d0800b0341458160300d0040651046461181d40403900303441a81000070b298003117280841000380e80203041524540b00c6510b17800d2000e90100c4195103600040003801c06400c44030310b8450012950504088166240004010032075000410140030b22440640ea600140e92110440b800d90390701d81000c480644500c1100130307000c1c0031b404501d5003040d40001c01085 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 41065948 1250 41064698 41064703
    0x100e0303010f0504050702030304080c01020d020706020d060f270f020703170f010308090f01120509010b030f030705031c0b040c09081b03030405011b020402070f02130608030307052109 81
    0x1a200c2c041c0001e2600c0c0e603282d0511040b0780c2c007101c0b058016081440807e0000703103400018040d00c84244005401e003e6032681c0407040b070b0b01c042021030f03050340d002840003400401c6003d48070040c8500105012018940482400014041da0040301e8010214480c0422601e165000406016002c50b003152254400d10700607150341c00001d0f0f2000194081d800180100d40c0000341345040c1c03540022510301340b0714004c050140450509150505105041007841101c603800e105062194400000125100c20300750b0515080410030351400742d0315041005090085480082240c8124481c00001a0007442e900301401c02000d40c0c0b414039030303c1030820300c01c0304031941d000134004161030460082e0f07101d1f1110701e031070101142818908260540c10a01c01040658002c114018141c00c0360220907580034120ba0015003240d10900003280e11505464507041541072800340c0d40d07107038400040e0070054a410144800e0b07a82c08000d01c060100301002414680180004014020300c40b900c1140c1055801c102c0380094 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 41067198 1250 41065948 41065951
    0x4060c050f12070318050f060903031e03150108150904020111071d0903130509191e05011a16021f031b0201091104020d060506030a020a030510030203061602100e0303 73
    0x140021503034000604148241070501c1d00b156001000307900107c40507003d004481d0840e032200796050106020200d43d01c00001c5164000446501f9555501e20b05490f5000072901c10711403041c1045812010045c20346981a0094903202c0d01b01d840d02401e80d100d1004803040d07049084540268003a000c00005e520301c004108280004c003400650000d503460000b81580ea00a20241c40280c621542040025080462070b150300308210681c04400010400c100031b003940e804680c003c07510f00b90000d105000001c1c034030405016101e01000c0111030040c284000034240101400c51540800c03041c1e14008559520841c3c03500c8000300b40c4400c00210107844058010f00c5600079040c4c5007079204821201c02031042c419942041c1d84400e20b0f80b00d41d0503803400d00000703410500c0e4606040d80d8440c00803520759141d00c091071013002c2261003d65a8021164001c0640310080d04545010301e480034188010380c0c0206405510403880a0010307403c3c00828001c9181c1001e0980520495242c0596581c14034004002036 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 41068448 1250 41067198 41067203
    0x4030201060905190c020304050a030c0e0c030f2d0f04031116140609031203040c0b03010b030705180405090c01080c030f0c0d06030519021f0504060c050f1207 70
    0x20084103582d00111429110100c0d000c2854500c8550136900701c030403c1e40010340c00c10652044034201500d9801040212109410950344404030800403c40d000c019000305070700550700c6d4491070031402c03c120009034000c4003034041d9100002091100e142d800381700080036a04626200e80910604240140180c0100107440607000100a2120030814030070008180013048144000708500614040e11188800c41c004500e50f40b0170410400a800b1740d800300207512015a002c0040d560382c0c1041d05d800080c00490b603204490440c0e0920041080d0700c0b144c420740f54410041c1c20b00340c1c1d80d003a81005102c481040038651540c828500014009400400500074071110b46c01e07261461035440300180400a40022104a507185d25004005610708000601510716205809408a0a03035144c0d074880381003e005004000c00340c075148180c0d80951130080f561400094850104408070040c000c0f00500610031400780c0420700c41400ba601d01045010840005d410358000b058414902458210014035803142805 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 41069698 1250 41068448 41068451
    0x102130f0509060d030e0f0406030803040819030515060c0c0901030606140103110306010c0f08120f01140a150903140d021c170612060a06031b0503070504020f041203050304030201 79
    0x81c0c1504000e001080c1e1503805440766060144541b04000c6c02039081d0818942040d200d480020000790150701450241303205d071902e1a02c03480b42c40701259031132150701e55000405d410071082c17200918401d090050030381c506603551a52110b24290591034900d105500c907070800840c0c00000284601a4000e000795003c02c0007c0b00182d501000440a42d40d017070b500ca10300c1c40d20800c0422440e60141e25403c0341d0901c0b0389044070690200d502c8a83c0d103a004800b03038409100b651020031051100c80b03220203000d0800710b560b50307407000c07402008070312002d401c1c1c040c0c9030b42001400000d601c0c140c0038224003002164855040b150219000124607110905940c4180243c0b09400058140c001e0300c400b4406450290358424105441c40042c041d0a90740241500e9007251035601301e0b0a80030700903c030f881d1040707540e01b501080742441c611b000a030540c40000790304e0b1804e0030707030b40103000350380e80440e005040b0341d800c0b20096295266140b00b80b003144a41da02011000d003100e140030080580200240d8803550080c0c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 41070948 1250 41069698 41069701
    0x405100c0b01050d03050301090506030a0203030d061401080c0d05060f04020f0409052217070b0406090308010e0c0409020d06050a03120e0a0b070609030c02040c020c040e0f0307080c0102130f0509 86
    0x50000c13016802c000100442c0c0144018081800c01d0b40c41140d120a005044580d40c240603008642940e21a07200326445075103070001805454010503070709492402c01c4c40d1083c100d00e49550442614069800c0c00008683c840011505541e52606d251a142e14010000c641d02c60400110045590040c801d40a500b420b1000003500754090180c404a9030382d40c0c401045e40200c0e60b594034030783d071b9181400c28050740038140b0501011600300803c46104500c9920001900c0801d03007006401c0c8201640020003500c070420070402c1003030503c800e41e021039600040150b10350404400003c0a4402a084946c0210102e100001404062107410f10403040320345520080041a40900401c540d0703502842c2200c110030003c90000600c10781c03103c2078803800392801700903120013540000d0903102c07000241030042c0d020300301c03e000e01d207028414454052000c3d0020008103130f54070a0513440e801000c00c06001c0800100e51040e80344020f4044070041b4910241e118a040c1d103407440981010100c4c016a8042c404c0c440 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 41072198 1250 41070948 41070959
    0x606030e03130e1b0f030106080f04081602010504050d060507090902040302030307080703030e06010f06120905060105090601050f0c0102041706131506080703080d0e0d090e0c0405100c0b01 83
    0x31075140340380c8404641c2109042810755000524058010542c40e12040100300c085072011380600051880d030101d00d40d40e9494844010708421002e490003030100c0012042c0170000e0005001c44009082510607480683c01d1800103071000d014507403200e5084031146400034100120340d03001742e00c80d854a0301d99200c0340340c0702d500c1403049014a01000390941e00c101310030004210070001418ad814800d01d0007140e4803003202c402905219003039021862120488600f8003406400805003902c03030030009401c01c0001c0131600c07065500e2030f043c8102409081c288011940303e07489503044608801000d04a90f9960410000c83c0d4000d500c0342c03060324038848030038100c01003079080428000d000302c61001e0300c1c100d444201c3c1c40d15410038121000b07948410755a040c00083d4141c05100c0c5400450003030101d1501e0b00210901c2e503003900c01210340c0045c941c0100410029140e0010300d490b080d81c540140344c010f40d82c1c0d03440c1040a644100d410850380990b88e40c0284a40651200d003041000340305003109840d030303603888 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 41073448 1250 41072198 41072203
    0x103060c090602030a050306041107030806040b1504030206090105070507062703050d0f030b100306031b0f090209010c060e0c040f0b01020304060c0606031208090d020a0312020a140408010606030e 86
    0x18010040140c00070040c013030645200760091604188c1c000c200064400c1a400c0c41d030741039072100b002203001c99040c4040000302e18041c03280005410f8140c1310350260010b004039445646c4610b01000348143c00c045030400740c903403040095415442d4003204941c1c40c9500c80c00042c0c22400202c0c201c0308000c040c4050a820603c0300c02340702c0c0440781d100c80241820031001c942551003e030841e040b4402c260b55901144415075480c230a03200c03101c0190701d00003045421402d0442c1c400741c240c80c0103400040340003010071403000030003080300031603104440060300c0700c2000d03004803840c41c4d1000c4e003d4541c504000d0034003580003001c2040c0c0e00c0c0d03400403030302013082001e0100c00e88213603280e01c40844d01580050004120160280d0118140325104000004003244c80b9503400440305038100401e40011501d03820030154003003c0107090302c2c0300414001004100c035207079401081d581c1315105884400c1d0b00484c07040340c603500031071100c000d203000b02141544036616070b0900790081c2500c2c803071603000a0400c9501500c19802 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 41074698 1250 41073448 41073467
    0x4030c030507081903110f0d12050108030901080708070315030308061e0a1203031103090c1002160611010b12010203060307140f01030905070b0408070f080d1e050705010906050103060c 81
    0x71099130042c1241c181c400341d4103181c4401100405000341c0080d100441020f1005084280950300d030320070741541c1085000304890b0144c1200d00b46a0040000401c09da8204254036444601440c00f503120390395221040300a442c50392540c00b540280c480c404420180c110100038440c0301c2c01d0b10413802c0e02034003000710308401c41000003058000440c02814421550044444035519000b8180801d801b40c21a10b480f00036401120102e0a5130031015020025181c44414180d18207494401050940d50b084c410f002001090b12130318040c0102c01d40821760055003900800e8203020001c0c042c00a00f215200340d94041d40c0101d82c29442805160f5020034421402c8440301300001e800351070010744000c02c80054009055100701540d040c813400380002140d000030301c01000640100b90261030024600001041c0c55041900403c0f011b400c05101e5413100b541c0440c40d4414504031034119202241600401d03142c510500d023001c0c206500b0010040244141c0e90881c0d4102d0788149070800c00e000c6a2081280d41000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 41075948 1250 41074698 41074723
    0x1c05090108070314012312010c17090601090f0e030a090f05060703021506040204030c120213020a0206060d06060504060b0c0c10080a0903030b090403080901060504020906040501080405070b04030c03050708 90
    0x131a40144032014000000c010302040465a52140d90101c1c00064a415012142c4090700d130344031007a16860503440349d1024101000c841c80c580305070504038800d03500c031b8a050140b4104036665140c91140022581c01191205007444182d0f9901d07082c9800080001006001d04c1d00d000007050400100c0341003550480f0095501640030300303118180c120120444030000707400c1c254003d401348004008681000d038010001e0004440e0340b000e809040c03041c00210304000c0100c40d401403052010301006d540204405602000c11500d00742814074a00c0c01300000c04040d04401d0b003007483c2ca500400d51340d2035400148010600c01045802070405802080740292007240300c0790004c0c2920700030071003040582d08031003122480303800c011407029416000705100f100100c0d001d4001420100500c00000c1080c032801c4050002680c09500d044003541c00f185c0c0314881c61140740d041140000001c1c041c04000e0141c800a0101c41400c070750340b10303502e0414101c0c1000a00069845010311440060040c4000481030500c04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 41077198 1250 41075948 41075981
    0x170403060c0305090c1906080408090a12050607090e0c130f060203130902090105040308031008010c03050708060414060d0c0b0406020c03070e0112110102011b091706040c03141c050901080703 84
    0x20301f0a502112040000b03407044410443c240072070001c5540380c43c026400340107070342400c210180c040d040c00c80c908080a09084140119030b101404007682c90040380d0743c05000d20070382654400361708075590103030314143d400741c43c0c0692806804600e6607400720040c02401048200c408840341c0340d6052000305c0c4903d500d802c1c003281c0108020000a070216019560052005000440455899441500351403440c2503440020350341d103042000702500b0144540d08010b0503101003201625807030001050070710242c5054403580503400c0c55000c010703200c0403010103450004800c0e9100d42e0740746800795031030852030641446805110f40106807144c058030381a040300c282c0410145481615141d00d00680c410a1a4034115500c541309c402620030311202a003501d158039070311311030700318074040d03100d81c0b203090750f40e04444a0342204090002044501500348140c0b604275a0800d00025104c09039032800d00c14070000c0740103003090b050ba0718003541c11901500701c9c0c840030f0b00d8000c900d540e885401c5048603518030f070515041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 41078448 1250 41077198 41077249
    0x130c0e0a0f0b030f06060705030301030f0c08010516030203090304120507150215070c0201030605061611040c020309120123102412020906040308030402040e060c0403170403060c0305090c 82
    0xf41d0191308040d00f061010f44120300d46441c1c2d8a400e82180c0c403d0f0801c0d6080f219003d520310401c007040c080b040007802911b00030443da091142c80d00d030740601c50500180c205500400800c103500014800c403030060015092800460074a883c001d901c60003d072068a02c0e0845106503034031035030f001244001070701d44103c00d00708841d0723142e120a4508201a4400364105035071070303001140c01d880d0702e0000c00b081c01180828007003223861840c00c00604506011460b01480c1405100303a415138000058605140f4200c40c03015001d4100003100740144100410030ba000442d02c803041e02070221612440b03000b619509940340410351122003a000c0d254455140d00b1030f50340e12004603a20144912404440c4007031001c03015241c084c80800160485d0066001581c00c0c540000920046250034070401c03000610400203400249400420344426000d41d10000e4241c03101c960300d81003107544e070300d048030040d580c00300c0300b0484d1f800b8402001740140004c50b185c540074800c10054048502d40000c1400c5c0c05a030340c90514411 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 41079698 1250 41078448 41078461
    0x708010b0c0715020313080f0a080304020409120c1406010303090b0310090e16120b0c0f090301050a0b120a0209010603020d0f0e030a02070905040c03060506130c0e0a0f0b03 76
    0x1960019119400c240582c03407001c034940d91101440c0d402d0001980c001d5840c0d41d800b581c040000c4070340b0f900803885c50340b041d043c0c4150b03990f0201d405880681c0101c40c8988a69980c0081006001216001007a41408203403030980d80781c102d10f00b020f8241c003602c054802208201c1c0700640d114030a0201a001c0345039008100030402d100310007140d10684020f002c03a1034907917074140030043c0c641c410510600f54000020145403008c40094540c02400010215020441c00391105645d0b18805004502c0040c0b0004280388862141d200329504184050000c001c107251100d4104024520b90720120310a4019001d20451840b0000d0051030316500140628180c0e4600b0303005070f00030b600c15a4802c4a007034680e2468844188644600c0305030b0b00c1e012003d0743d0f80e00c2d06040020705211494010130b1005107040c0c24840461407004a03901540d600c030f20001200d03103610001903d599072514041c2e0340a410b0001c039110207a4001c000c10301866090b10744514103034540d140c0d542c4040080c040c180c3c10f1301d000e0000480 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 41080948 1250 41079698 41079719
    0xe0c03010b04030b04060905070e0717010e0103080c150705070b0c0c060718030c0807060206060a060e0411070f06060611010c0e150906030103062004050319030905060409140c03070801 81
    0x70041d1041c1b6000030741c3c0c881669054205076240c1d02c014181c4401600700080c16800c040c45440d0313517034030782900c68141d070401740150700e001011300000c4c00100d400b040040d460303201004016001e1500ba2011000c610300b211004080c3c0d408080100e8000b0710300804140c02600142c207a45010000101034040c42e642c080003158034500c005201703008403810038000008140121003c03c0600072210142c2036090401001a1401001a000c0c074002e40ba151410407015900c04811103400360201c0340803661068801c8403000718024210b024014181d41000442040050381c040e4080b1000c1e070320b80100c094041d1003024226001c900740140881d151900130f1609160091180d07641382d111141580c209582d030004074619420980045030f203580e8032014205e03042c6140c00c80c0a01c2480c0803032214a02802c041c0800e889a019841440740020842100030805000d94900400b4000240c039040c2c42d00e0baa228014083c1540d96440300040c074111002c03070131000d0f4fc0030440303100b200750343c0b03c5d0f100c141d280904045 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 41082198 1250 41080948 41080951
    0x180d02030d0c0c0518060f03160612060b0a1205010503070b0d0f1b080906010b28030f180b0c07020a0611010209060d05010501110708070501050a02010e010c0203040e0c03010b04030b 80
    0xf80c109280c0c0c407020031955a207600e080c91550142c890540c007440d11030140040f240c3c48212152083d84003135000a0801401502d420603942a03240400c0d005407000a020013810304c0b5000300390003200124844881f640e01004060b01d125008105101d181d07130703500c145030300d44100c1e00601d46546010411040200010341040324601d80780e0034006000f03032251020f103228200c00c1414400090500d010b0000c01d82082000a0151215401c2c2c2c510f410380320381d000740707601584400100251550f40fa081303d400340a58413480c1e84203052403003070059200c07482686002c20918201110400300d14400300b420020302800b0744207400d074060702d0219141d05041c01910103501513a0001c6040d034003008441c1c52522408013910301c901103c2400300b5594181000501122049044100301e68802c40c01000110000140c00e41280d600303003440c550319000034500300c3c050002929015929824240003401039540000108101c0b9610b07145505a5240c15607540501d101c00e110715041c0e407106110a0003c148196080b5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 41083448 1250 41082198 41082203
    0x314070320040b0309070b090108060d0303090f05060703061a0405151303050606010e061201061803020d12021618021309050405010c030b0109260102070506010803180d02030d0c 78
    0xe2010355810000c095070b40b06820a41e00c0700008024010b60716800c1103a040034188000d1a1420243d81c100002c0c41c10700005c0107148200c40282c9a2010705009510030104981c000490004009041c1010b6940d55025602030000901d045400509c0c0300324841182c2e2030041d4441c04038030702840d00d410490861080646000d503082c040180c1d1004a015800401c004d5102c6c0000d00210303d40750b80098240d500034840140101c0c030400c08440002c9000204a064800c00d042c2104a01d11051060200a01a4100039000303008400e0983c1823008200c10740c2400384299080766002c0d62022861001840c40c0e10038194001c2c10228001c071000d42c250081c048040081c00418540d5a450303241e4015100f00759070a440f80e0355a03030b003961070003a03250091002d07040303081c2841d005481c5055426012101c210549840d6a03488000c91800510290122030706190004121611542c4a1408503240d52145260011780c0d00e4102404c80c4504081c070a8401d425001000381000e810302c070780c0598600300c0c1c40f0402c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 41084698 1250 41083448 41083481
    0xc04050a180f06060506030403050304062f0301170d05030a020306060d060308210105030703030309080f12070f0309120806130606180801050103020a03021005190804050d03140703 79
    0x1000001481c881c0d445401050044500000d6003422000ca4038160042c41c09110104200004650020102d0b038210345d000100190381000f864003c0c01e108050784c5000741182e4110f88603090040007401131070507903029080a505050421a11a84c0e40c0030010101c00030440c140000790021416502a40e800000640260b180c001c40a80480c01c461590300210769028001c0380d02d0351411015401140c084000718806101c9504103400643c3e1003105d48002020192120803980800094000f55074450940c102040d446009400b25903280b02000c0702c80030b002405400a80195070306c05d005960b103140c1c120a0340003070103140010840700680001c2c0925080302c0795001c490f10803c002d1203514000e00c80d9955000039844035280c41000d006580e070120210760304107401807016980f0440f0002c100d81d03044030014114000c09a040c0e606010b503801d14071802c0510381d2070015080e08514071500c01d503c40d13015504044100c039400c0d0200d0f062403c01c0300c07400380800d002030030450295201c58150990880d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 41085948 1250 41084698 41084711
    0x9031e07050c090106030912090501021e0712060b0114070804060c0f02120c03070b0f0f0a0908032107050307020c09060402070618030e0a060e0d110409050109050c01110c04050a 78
    0x801c425443c03c4c0e00c0f0500080d0703a5000e66041c0f00810060469810487c50501c0b04140380c0f1000079555044050400c01d82c250450000d40300d10005c014000040c5400c20411302041c01606208004107440016240498450398030865403112020464100c0c079403103140d81d81002c1c00c01900b240d10499181d000c50748181c0c1d80e184440542e0710209403903540011000284158070410b401c1c141080c6030755101010700d2400b400303141c5288c42e16a05a4180000b102581622410784010441d030011096006030b100c6d0100140c01070624425050003640f1345580070741d031241070f22560b104448a1204862240c01a040f151406040d031806800e01c03504072000620243c20b005054031100120744019100b04c0505003107800d1b40d010560803c0020224420444032914481c1c40c00c44081c140d01007240807640304107812404d0000b00141840114501e00b800781003000000301c58940765009005541095075103106000071784d1415071240555540e082140400790500d0b1204000744405030001a000c6d1040c0d98031402c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 41087198 1250 41085948 41085973
    0x8090109051c0c050f060d02030601020307121211040b070b07020f0d021c0206010605030c03100e01060302070c08061603180210050307080702010605010f05220909020909031e0705 79
    0x200321140d044800004060202e1041c9000b403481c201036800f05004610465010b6801c0d03455406032010500d445070056620358071800100e0451044a000401410405400e41c8400d40d00400b410210240c6000801c0041c030303144039144960007188200c02610318104213501c001101c4111035500080c02d80101c84844218000e02420907850100c05801a80049420342050202d400f80707545030032042c002390441e035050420082584c40001d00c41585c104001001c04e901d00840c076006802001c69072030f44070381540c56003402000b81d1700049083d00c04042c0000d011900c1c200c040752a60284980107000a010040b4041c1036000c2c2c190000903080c062484007280e00981c4402240004000300d80ea03c0958034035040c13030003070705040b40903000e241107a242100c1440030766000070f06a190000c0b5420081e4540c40c40c001c0d00001130b070780c0c4080c031840700701c00c9100051150116004849258422580390102e6910012515501c0c01004142044100303180c0d5011904100b41004084450280054540820307503031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 41088448 1250 41087198 41087209
    0x20109091e050619031202030c01020d0203010806100e13030507020a060f080708040f0305070f150501050f03030f0f0f0d0603030806010f030b09040201050f040e01090b0a0e01030f0809010905 84
    0x16040d11482191044040500010b44600d65102e0070403283c081c48407044090f02c81d000030060000030a041140480d0103035203402041a52200c0808078002d540d5030140404100194000f88200d01103440351601050350004001c1c1000140e40010b8100311003590703041c4840c49403400a00e404e03018002c0400c2b10b103001d82c0782c05925202400054a6240f00400d00900040c06024014120340402510f1403e203c0016000460251519050318183e07440729103604100007000d071200401400c40d8034000e60303811000c165411140c12100119041c1c10418808400d06440e0b10403c0a1141070403010420459103042d200050180300b881c4800090505601802903802ca407000e41051740840c20f400308110700341d030344403203107202c0c8d02c0301d40c0b13400d100300180c0f4400b01b076900d0b4002c2c0000b41401404219440c02c00038203025107000f841041c0aa90300d559403803100b84018840d0003581030040980c240d01044003d814404c1d14100d951100c1c461545a5407911804401d4010704c00c192b0420900500c0081d555560 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 41089698 1250 41088448 41088461
    0x9060306080a0f150204030c0906030c060c0c1802090301051f06020f070513061d06090a0b030604020d03050d0603210203040503060c130e1f0503010c0c020409020301060b070308091203060d020d02010909 89
    0x5089c00090b136030300f9420080003014440c0d010030b00b0088240d88000001c3c000d640580f0454009600000000b03800e20640c0000e4010138003240d406620b440300300030600408100709401d0b042107581450709541c480b0400c0b0703119180c40c84403060a50000c0c0302001281860700c1c40598200d8400c070005152603d495064509200da44841c103081c1c010b801c00d0141c42e14204000641002ca41102005040b40d01400320f6103440e4014030191190001150110905d4050030881d00c1d860440c0800b08180340e1a440e000307154808290f442c1c880c1410040201102c0c82c000130454081e908018010141a0307100308444076039500501d00404d040e41006c00000300b1100c8064028042d00002e220902c8060f42034031000900710043d484244668100560710681a4200d440c40d40d0f05074041da40071540301d5582c00480c0c09804c0c280e022000b04070000a403142455440742d44180540700c07020507600e4034a444020401d0a0105580841d801700b0500c0000c4018940201210031040c4103045c044601c40da5803207954201c541 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 41090948 1250 41089698 41089709
    0x1103070507060f1206150c020a090518060a0902010c020d061410080f01090206030106120b030303010e0612060403020304090f1805030a12050124050408030a09060306080a0f150204030c 81
    0x79403ca962101e40d000b450131041101400c1d410400303d07140072105058114807880ca4420700c0b0341c03c9403c005641703a042e280d901400c450300c0140080c0c00c5c911410502144640724661b414054080030400b212901e00906001310703016134503528400e03495020843c0d55100130344210343c056580c40c014040c400d840c580d030f64410b0081040c141c51152a00140605058103022030b503200c0d0349842c00b88001a6103c8040d40d05603102890300005e910884c940b800010702806c8912503152001200000322031034001d100c41e2046005071030801c4800000c09001d035849000340ca005002da003061000344000641a40f040519031481c1d540030500c001100082181020b5000081e00c0720b420006a002d401608260509005480e004042000350b14100b4840d842d860040090b42c07401002d06d820504031171141007954040c0801d082901d9568882d2013010f01442c0c603c0c0b0401010074107000000400c00d0020440303203142c5800c001c40c50994483c5640d60040c080760701c10251707101e903800d010110108041c001044081c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 41092198 1250 41090948 41090957
    0x4020c0a0c0f050a0e10090c0302120c0a140c120702061611030f031303020f040605060d0f060501050705030a080402121002070519050a0303050406020403060f020a0305070519110307050706 83
    0x50800081c4100301e0301c1501700b0310510a001040c00110381c403082c800011960020800110106800e0302103002e481a8480e41c80000d02c60b0081c441ea0140b014010a070340300281d142d045080c0c07410581c4500c0c501444030b0250050304010b02f00c4030031800100091014510003010380b40740072900403d0036800c0040047c00c0e074603c0103005400c0003d040c1000486414280a40117504020130902d403015401c066020007405200300204600c116143c68201001500b0020601030701c4544107500c8500906810b100000001e051120000c2d50b54012012070780a1608007004c0c42c6070444440c0705a50f1006e002c0c0c0102d1704000d1021100d20400c40c240440c494030403120f48056540e0456007850781ca01510070914007042412404c14000052001034a1400c19034517041c0802e0a40d48c0b0b0a001000340200d5001030400750032b00c01d4080e010328241d801802c9101c1240c81c00c0007140c890310011500307030241140740209003210300640d40e030090040340c1110404480720100ca03d00401a81d5050410085500040109 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 41093448 1250 41092198 41092229
    0x20d050403080f0603072306070b0115120504170903070302090106050d1508060601080a06080d050d0c080c09040902040e01090602090306150919150e06010e040504020603010504020c0a0c 82
    0x40c6024070140350402c604400406c940c9080040700c000000c3e004d903038044401708403020380c1c20588036071042d1282d003908003620b41803940e99020400d081000e80c200f00d81c00524100a441c03014809481124040c3d9006103131403080c1102c2c0b141d499859800340c002254148503040c400401030762100f22044c0644002d54440c0e0303da140d110b00038400da95031980b840007001c20a56091103520350001c0d144e94132060910f440c40003525101c6ca4003005121340d800070b0403d8000c443c4041091500040100b01e10342d25000d0030480303d94600d508a40e00a4199554000100100880909841d0a07041130f440c0b5400104002040406010b0840c01c6540c00340c0e0485040350003140110b01403034180302039a440700c40c8401307007601503200100154154030b0081625422007400c00002500003103607806441030640b20240182031940b12003c2140c0c50204a907098000b500d840641803150a0034009d090080381d003e8149419070b420030b41040080e4004003410852849403182c20030115100c40c1c0c104000700300260040440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 41094698 1250 41093448 41093461
    0xf070e060d0519120908010b06090405060d14070e07110a0311030c0303010e040204060e0403080c0a0c0f0302010609150f03020f04141306050a09050c1005040504020c07050a0504111903020d05040308 87
    0x134415651b12808035a49040030701c901d282c8400c41120f40c624011200002c480c0d80d2540080c4c40b2402541c2d01034440342003074902240c8400005034800030b540e458440d155840d03603501c070206c6200740c3c6991a000b050708804035801c00a80645c0070310761807038444030907a400c084c80d08034410b11f980c200364084241100d9640c2400107500709449484041d10704100007c0d1240b500d078030058003080340648075139050311001a081c10748a11804100c4035280c0e00080003010140e031404d009020b4901e0340604400c051510400d00040c1e42c1c020102011210b101a0b030072402c900d160204121118800341d042c1d08a900c42ca484c0c200000154201441aa940441e500c0c66002508080d41142c3d07004041b41d907101d14141c8040c0100348001103403d0000000c90b550340c84c0c100401011a80c0740a540d20035a0404c1c00842e40180340d240225101041c0e50064034501d80721aa40e10030801134070300101011540074810421070040080c0140150b600580c0307800d0143c90311014640d04800c80b20221801d400142070f1002344800d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 41095948 1250 41094698 41094707
    0x901020c250e0405030a1b0c0308070308060a0807030201181203110f19020d0f0501020309010c030e12030c0307020309060f030109052401050901020a0203060103060e0f070e060d051912 81
    0x3410150b8120061880c0a6443c16030740d2094490384801d01c0f060701c5004a0100c40e2100c159042940140303a4607880b41d41c0d140c542000d0700032076801c0300481e45040000d180c1c0c2c14179803a980c088500d010000c21541e841c54005491070442207400d07070442203580401040603004d2114203140d091081e03417000c40b02c440824400d030a08101602c182141d0704400301e0801d01241c1d5a100c184c206404031140c00700ea80440c03501c051180100c001c001c190b5400801044486075040d40aa80454281c0c0c9003404402601154951201440464070305072600030310105840013814400381d40e102d01c4070b0044910301229040040c901da001074000040c0e0900010040c0700c10b5441d809001c1e00914002540c00c0c00c0555880032481000c507402110b4100480418462503681c4208007a00c5409e070094103950080d41c403400d2403006454000d803180301c540708035100c1d15800c0200083d820101c8000584440a1b074440000300700308403040c103031309480510412600c60503610f003058082440612918041c1104495494041c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 41097198 1250 41095948 41096023
    0x20c041104080607080618070801150e040504080d060501080405030706091e050607120b01020a0602090d060509010212010b1c05060a09020a020c0102070603060302060f0a05071202010c031a03150901020c 89
    0x4618500281400780198100727501c04d0541e01070340303d6469080311003202100c800341c158015542c414184418003042c00104001089582e040030300610000c2e84075001501d811109580003440c1d0b600800080001c10b001e54051040184110981104420852503a002214080b04240c1d002e411041c02d01600c26001040f005034a4144401401040c0401002039210911070001920083e00044c3d0f100c0c6541e0340c1354050415039403180301000241070202d00705000f50043c403d01150b6104001c004120000698103503200a18400010241e546401c0c000401911010f490150022042d850204200949002070a82030819a0050030250017981c002882c2c0070b143d501ca44145440c069003480542c8035a4101c410241c85c3c1001c4a54500001d00704551034421950041e01381c0b06660102d002155041d00848002c40c49550103010b40721900340300c1c00d100c07a1101c00c0320394150302c074010924050303038100d81c203661200340c90000504281c0c00860807401c0c900b1600f101480c000303800d1050074801c0b00403810107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 41098448 1250 41097198 41097229
    0x10e0606040b0112110f040803040e09010612060221040302060405070e01080a0314040503010204060203040e070e0d0f0213020a0e031504030203120a06050307180b030607020c0411040806070806 85
    0xa000b900400700020b05600c00c50b1100075482600ca4110349440d080500480302400d400c1d04010341e85517038072030f201900e9070014042e0040e102c03c11800f0680502d014014001179450030080c81070320341d04e680e50703200c000d6000c00301c48020b880c0000403401c121402100803912460190700544202e141a140c250304144164208581c4800e6500043c8801032000600300c2c02140c1c941800c400044024005a1043c041c0da801703203500d1b40c0005008110f00e503011010b841241e891180c0486161540b140960308001050342e1281c1040080d4045004100140314451010340060040380e41c9080324160307441640d12020701c0c9070114400e0389c81503c480c101005003843c032420000281000c0d040c180d50094891040141c1002140114004142e41070300c3c9034801001080b000303003190501507a907450203280c90b000e4940500340030316040b2084950b04000c1100740c4103800c5940a0048c09650f401084014095280c202e0b81c01e100c207002c041a410b10410080d40569410745a0822510b01881045102024030248 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 41099698 1250 41098448 41098451
    0x180603060509061002100b03010b03030a031d03070f031202070b1005030d08090a11030f07030507090509030a022a0901030b041118150d1a010302030f0a0c03140c030609010e060604 79
    0x210307086074041149a200706d40c8000124041c84120006409000d0b81c16a1541c1800300042810506805a01c200281e030900350030318107601c018000e03a54070f038080c01c0300150400000078110400a4410080e4a40c03460040700c0050038241d1a0300c400740500421500784812100c0120180480d01d002c02010000c4a21450b24071841c1c40d0603131180340c58060404009000328150003a4007081c0d9030501c0102d02c112010b02c220f400103075032414000d030340d24000e00c90003440a161002040d0040804400c5030174a403242c1c0c000704642d01d550007512404c00e00074064a40d500700c03680a802c00a80d9510300e014021402103540c0c0380c450910f4240b03642c500310317400300c1588100240248807a6440d2140026580110321840b0800d0340c442141c0407413078100d86000000d1000b02003040c4014100c040c041c210b8185c034001d500311080c00c1041102d032070340c03024660006061a4824401040001c051041c50403000041c401a80c1e6110009000b09140400076121442c19135160b42070301052080404c00755a00c00f400704d80 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 41100948 1250 41099698 41099719
    0x102031807050d15090620040302040b0109270612030e0301050f090a080306030a0602030f040b0105010306081207050123010e06030c01170a0605032d01050c03011518060306050906 79
    0x440384c9180e0700c080c40d40142140c03034040c000c060001c01d600003040f031035200015440840116003440c80580c0a0b0008034440d81c40d02142401a510034840320060725040d04c44400c0516140500c401549281c1c840030542589610002c80e1494507280c4d58a6051b200f03844519400e13010004142c00d43d10020030045003030540504010300707400300265611701d268010502e6603981e200d12010070b0420040708800340046000009104c2e60012401a9621460183d000403407103980f16001141590301c0b40c4150b54540d80030403038004410b1642802003038018410000021000100050160124205c80c02c840141c4112401081800c94101c0c0361540064228050302c0050454400a00b048a816800c0f020345540c01c40060004111903001d88040c00b0002c017100c0a84203001c040a0194000c00d80310b004041c142c0340b05010607401406401c0c01860020302450450382000c0e078510241681940b200c0420840030442000c56805900003405850517a60100300c050402050003258a40509103030b0080c0311140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 41102198 1250 41100948 41100953
    0x504260307031103090d11030c0108060a1703040306060b0c0d020109150c0c0b04050304080c040e0705190b0d1b050901020a030305060307030203031206031c0801060c0c080102031807050d 82
    0x44500140c1d02d4284800c2d100d0940718058a1409500f2810307802034284d400407014450001030b251a5010220700b102c1d0200030020046131088800c0d60701030b4000c2442d88040c400075a00e25940210340800a0440703040a039a40c9030802170301c2151340003103038804c0d0028101d08040c80074843e0202c03c0d141c5c0d000a10213008503680d4500118a03102040d840c80b9918104c07c09014400d860b1100300c1c58008040c0d50301400c042c2800d585a600c01d11905800384904203401e42c482c1007501404c1220905000a071405901d040c0a00c82040d0320240c41c540e807011403403404194860001d024003102c00c008000025140382d03d071035420013a18a10a1442400fa00b808030000aaa0024441d0200c9516140c0405e140e240c01010910305600341e04001e41c180404035a40e081075030031043c001d2003031108500b10faa081100f001c00810a07100a0b10307803030006040b41c00610045024a5910700403501c5169070a00301c664816846007280c10903100d100c40c051406480c00e0740c000b0100b14000203004c1c1200d007203000e0300495 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 41103448 1250 41102198 41102203
    0x30d05120703051008011506030629030c0708040807080606060705060612190303020304150501051309020f0411130b0405210109060533010f0309050f030a050426 71
    0x8050300101502d071000941078444ca8005200104070300300c000d004900e140019058807030400d001d40c4000a241c0744000540a0302a0070481c1c0c10001c0e081d0400380451051030412450307000034000141c10f07804000500004044c04010001055141d014140c2c05003488812401d080c400780840b0f10800b01400060003191000c246140c00c44400c5603e140b0707600340050168100045c2d0780c80c200300c00002c0d02201040c5a017540055102c0d80c4a102e44a5140c019842e0490440e0000c3c01100d8210415821180701401c550340b2407800c103400180001a03070f03554100000c0c01c0c4c44124100240440300400c6000c0c05030304840540c806800c40380404c605207818600820b4422280381c140c01c140f036201403580001c0703120031b6004501c2c103500314070103000c0da150108074081044011031a00c07030007824000f4980810310f4411402c0c2940d050594070141034510641703048002c1c2c0b82006007554640030307035041e14100c0d0070200001d14090919032181c5442d58949030f01500d00b0b02c0f603150140400841c804100b100d40c28007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 41104698 1250 41103448 41103451
    0xe0102120f13050d0302180a030c05060307120207080903010c030e1f110f04051201020c0a0b040516030b07031505030d031d0d030212011202090a0b01030f140105030d0512 75
    0x80c010168034507a1280e00503442c21031940c5000e00240106202102481d601d0340040c01ba485a01c81403d1045100c401808003104c030511001d13000c0d40c0c94040a1080d40b40c804011504901545030500c07071420503004101c200d9000391811103500c1e00008010490341403c0c01848a10300480c241007011016003030105480341220314100040030140085106808032550148002d0014640860b45944030b496511115600c41d001e16407040500d1603210b110b500050080710b60000e40030b409455441483da46030355412002030000c4405006a21054008150100040300118060020340e40181803d080c064100e591005881092455040c0c0600241e10005407030002a04036140004105840a00c0500e40030134040d15840c0d03a0084904c0e2004459050300540100f454151904196984e18440080501110000207410140030740010b94644820350050f141120103041c0450a50300d8841807004032210118401a106000401031100c0c0c202080701d568242c15034240350346000381440314900410340 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 41105948 1250 41104698 41104711
    0x606012c0f04021308010903321c0e06041104020406020c0d020a051002060402032b0e01090f030b0f06030a02090a0b010c0b0a020d0c050301060f050f0909010b0309010e010212 77
    0x400345039480700790301c0359411940941c41a410324030f502a29209a6401b9041080007903001075a42d0b4210040b0040c0c2c1d0800c031744801da00b1040c0b2182100509641070698008042c03600841041d6920590105000d0207000400e64040010307201e0380c50b003031412080c42c00c800d0440d98041d0307206000902c1481e40018120154400031200400e0410891001400460403030b041142c00223a121400d94135241c0005440340138a108800740c600c08842c60081401d000800f105068180f465003800c140b600b40110b80c00300c00c41e1010300d441c030303401a01c076400300d413001c00340d83d008641d440840030030054202c003a03c2100d80c1100044002d01b1401d406500000d000413405042e181070b0f40d586115800c926806551200c03021340d03004003641e051b4600005090000d40061400f1030710581040041030b01ea0388103408030303810380340030303854181c001c040e211f00488803900320058040e95440c0070044030990359903c5201d18020010581110f81ea440c1c1000d2140c2550303240c0310000f0300c80c1c1c014407440701965890017503154001c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 41107198 1250 41105948 41105959
    0xc03070f020a0515040e060d020a050d030201090b07020318091b1803060a0b0102150702030a140f040b070203070602070b04030f08120703050a06050f03060406020c0307050d020606012c 81
    0x10500d00014000000710f500c0107030b00210400b1400f4002610030050301c00c5417406114001d40756075000c10300c045c2600d03141b0000e500c00f0300d000041c0080d140110000c03142501910001942c2461503a892803a444151034a40c0568008242140c1c1c03414035000149242105841ea61110304000e20140c0041c0c211a00164690101007154040a01c4081c0c0c0c01a400707200034211081420104908402084445961130050040a082c107002d16460202e081c003440165008524091880ca000c4903100c8a01e0514540e83c10100142da610240d080c025002910000c09032903a20a05807041500d45480355120400355000400c0070031920440b041a28112034100045020100b2603251004c0180701c3c00860303801411124003801900f03580341c0c2c4100d214500100c410000c1c40d40721410440c4d0b600c40c03980442d5042c4d0040001070700050542e00508599840c6008a9041404503a51141000050015040140d005000300710080d0f0f131020000143d0060304a189981280c1c0c42c009103150b40040354141e004a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 41108448 1250 41107198 41107223
    0x18140606030712021206040f02070f02060a0c020a03050c0301050906010e01051512040308010f08010209030319180b120109050103030f110c0a0b030f1b0403030f120c0314010b0c0307 80
    0x490080f403006542028111045607100140e01ea042e120207810ba0703615001b2443c1500e0700941d0005c5208885200750000445d080003185642081070716400310740d0300e80401c90380411034001620b8191980300954804c4016080c1060960141401c541000709455565400307240100325200101d040c00341901c0090702c04055142c3c1c03882c03240c1500d20030601c8540e9030041400c2000103040c1c0c0319180078103130344141040101c0380c0c1c1c1c1d40100300d00740e000e003002c0540e268004205101d07041110580e11136a41d82d807428040d071040a03852028040741d61035032100131224000a8440340c01e0103a011600d0141010500c101310344d5041d910b00503d041c910040070300902401d41c4840c40001810172000b00704d11401040903815680740c0c21000c943d60012b81302010821a11f2000c102d110300710401c81860301d010781138914281840c50f28100d805200c0d12650005002000e05058035801d10350080034580c04e42502d0126090385040700303010b50040140c1c00b40501180c107000c1c460f0034140200456140c16084800100c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 41109698 1250 41108448 41108461
    0x606010905100c03020a1401021b03030720010f18050d09030804090e0c0406080703061503031403040f0204230709030c060e060d020409050403180b0307081305010509071814060603 79
    0x400c01046c602401c580c3c100784900500741815002003054407400003000c14081c0c1d071030805590fa0f002c19200540414401066080c00d84108141d01f140d09001c0000400c45880c06100c020445195403c14220021101c1e10750f024004208060001c0e030400b454140d00c4145540c0340c138034540c016030195801e07054444039074114105040242141503003008204110007603558012650710741c00fa00c0f003250940d0410f07400d0422003981100000460342c042c4c480110aa1403a032104203070303510050048070400380407000d00c0090f0303d81b445030002e0303031aa40100a000c100100d01c2c5003203082c4010302d0380041003038104051000034100000c0e04101d80340342c10a1500441c290000074002e008070303144440c5041c40464006040c0300d01d034000380d000324000e0320b03a203050030003200c07000d41c0e42c0c5c08600410003070441c00c0020640c0307684500351041e40080712036401007100c080ca070340d014203681065a04842d198440c000030300064003c0001d0603456000e0000420002200001c0d000030303008000e04e02c910038000032000600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 41110948 1250 41109698 41109703
    0x612073f02070c06020d0306060912060903050c010f060e06060313140f030c070f0e010b070f08120a05010306050a0c08060904080f120a15080307020906010908010c02060402030606010905100c0302 86
    0x248580c0180c3c0a00f806440d0f200095680e03003030700141000641407400c0000d01034001d110107001d80d801d40c1c105030301c0003040d910b900b0082e0400d401c0460410008220751601c12000303108904c43c0f10740d58040810324514128610f402c4040240c1000c0c85200c04205010301115400700190850364441e617501040302c4860202c5e418401741c82c0302015140000500004040f0b00030905100f681c1c60402c5401605071600e0440d40d0081c07090081c1280044208007280201e203a06d8005140a80300e071920601d8100090780f150382c1400e00351454240e903501c6000501c100300c01400ba00394405151101013201d120b4640000349051380241000b80620304100108041c030150108403000d10443e1180c0603503800041b0840824000b04881008505140c11005003c500000390740104861800300250304014a0b84c08220302600d0192039603050041000e000036010a00303008000030351480350040c120924140c0141818442c0046c442c1b4100903035080144250366540e420400b19581c00c0c81d01120500c040c1c6004ea1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 41112198 1250 41110948 41110957
    0x1005101209060b0607030201020903010f060305060f090c060403060b0109150c1b03020607080a030b06030601140d06150513090b150703030e06040f0510050103030503070e030c0612073f02 82
    0x84d000b0200140c4042816015002802c002400b68000c1010011840501003180c440d400006c0c5641c000c040480c03048124003c0c00d0f038101050b2001d40b400001c140c2c0000c0c2595220b68001c4403101c0c0c031106804003035a0405c08003001400500b015140005078140001d00245003040c0041141418481420600d0580f07002075000c0c56000e042590344110500309049941c00034500c1c100020708040005480381005400d030303809410103846001c0c011240080082990704510411550250b4407540050b0070029101254141001612050741d11107114200d080d0b000c00d580c2284d8002401c1040c1100350b40c85a50802c00c44845096100344c4500203460101e010704101e44000006101e03800c140414021020440e031550340c464412141c800856a8510055034024800580466000c0c40018070740c1c0d01440c0c0120100000a043e03e6406440d04000350b141d402030344007000101c13007a00030003c0241d04144404090826124020f074100414014170f4451021000c203200d0654403070b45403000809043c0c0598 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 41113448 1250 41112198 41112221
    0x302090306180d050403020d03030e0c031e01141b0306030a17030f2508070203040305060f0601030b011103090d0c090905010f0b0a05010206161103030708100510120906 74
    0xe46080c1071040328000c041003525404441c5000d00f80c8080b20160040c41181d0442c0d50203050641806500e44003a4000c1c01e00090440d00b07400b030507039221025502840114200c1040c1034480f445030090344101030031550034a01c40c000040c0504248007010342c03503000102e4038401d010031946d925600c4501003400c1c0300d100d840042800280840900c048104000a107203d90600354042621380e584110302e4076040c61800c1180c20300e6002d0034141801501c01c00d405a80003095004407440c0c03d036650346140c542041201e401d002c15908006108040d03034140107040c4000030901e0294500c41c003082005491340f0550742c019204980440702d600400c1030200b030207030081c1340d000030401a8031601e0030700c980a04555181c84880501d031100700002441c10300254400e072101a030050003a0340c1e0710450145141640d00604052011200e610010544200f004500c5281e0715510500a801c1074400c2c8024a041600102d00c11400c03a14040704260344000185107002e80003902144008160a02030001d01d0000b190 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 41114698 1250 41113448 41113453
    0x40503060907060e180402040902040b060d0e0c01021501061b060f051e1608040512130806010902030f0c03040f0203070609260c011413030b0412030e190303020903 72
    0x20450666000704030007044503e0f41d1104500b8912440410600151100101c2e800d42464008500503040960110200e07a2002c5c100080c00c400300d000250450b003001a010a415486600d03041c6d10600500c01903503651000e000400340c60341e54001d240850035050050500700580e000011000c0300080302c40b04911340c3c0100040095010a01e8058094941181c4a45000315190310900c0d600702d9a040b25032040400c0c24490741003030078002086404c070402070016203062288a850f9804180941e0052000c408014006800c2500d001031150070148142c2c465403201c2d01c1402005101c0c401c1041c0c043d0300101c1c64210580c0c030b82c0e4030b180c003400e04541c40c0b0300a90140705514010070566084036000b015181e102008000f03420004458401e00d8140f58a060360981100d94285115400b4005002c0ca11000f480018240038010107031f140807210650056803041c41510920003440080160080c16000c946818088001144031072076840f1314415013100100c070211007040034103220364151005100300400303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 41115948 1250 41114698 41114701
    0xa02010908030c1b06060102030f0702010c0b0a050105090c0f07030c050319020106090e120a20101b020309030a0210030204030606090b0a05030a0302150a06050d0f0c09140a1104050306 81
    0xc804009401c0051a1012803113036090311100e26000182c801d125400503801545041003d9174544200c1d00181c01c120306004240071900000b40741402c0507403048803a80b40000b9258545001c03c05402000b078208948034404000d60b03040445044120fa140300e80500b021003940c2c4107494024914800e443c000019031001004080d91568190407400c1225841d1000b40820b1081402d05601c4e070f00050303070701d001041080021900b170a0142c09451940e4200c240340300010000b12010070304056914250f480340d184e440300b998445140117400310811410030300c021401c0640010110f641d0b054a41400b901c1502c85540c403c000d180701e60121005150300c9581408410355614000d802b428030580a548602e80002010030a404c0c0020a454400e8040c0e0090881141b07a0b26042a01000230340b081101c2c40d01c684000c10191281c1820310b118500c50b0781503010750f0b600c4e1f0400b03041c5d100b51a0044441e80d4240031040c0380185d00107007a29000401c40000140861440d14a0f401c5407003150b0055426000c0c160 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 41117198 1250 41115948 41115961
    0x10c0f0c150f02030d0e031b06070305010b03130b040212031206030f030a0906030c0e041107170c0703020906030304120305030a0c14070807020f060f2505120a0201090803 75
    0x40a03081103410021466803250003011050341c03079040300360001d801a4001d201c80e2152900640203005507900382000e0745e1410949a510104c4908010b002d030005074044828000101e90501c6060b00400c0d042107500d0440c02c1c0b80160700220074040d40c016103080140c601050030340d40c80700d001d0902d0003413407403c99548460001809901b840c0440308284240540c0e031600a108002200f101c4080286507501102c0904248069000303100a901400800103d22290801501c40744940120000700103003480d01c559240c5816195442580021403500006001c0d0b018614070015031001941d034103c8980c1c01c0d69071441e02003403440c0500e03030206442e940548007503010326070004004d500a420695092082c69060720060321246481002542c0b4104204054008940240007410240d4401401d410700303071a0440c000b40107500425040c012030305000071103030400619152070074401481c030408814a011241c48039516090f03000c0c842c4620101c0050346c407070120702c00c0d40102c0103294040b03004c035201c4c2041c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 41118448 1250 41117198 41117213
    0x1051b07170c01080108060402010806010c0f0b0408030610020a020102060c0a050702090703050405100905060105010e031005070503010801060503190201080c07060903051c0e060711030f0c010f060608040305040311010c0f 97
    0x5220803801300e80c2c500000300d8440c02c0410150311603601a1943c04190710f0743e00045a03502c054540960300403210b05002000140c4140046000c2c5010724140c6440c0e04004003002000d0a2800da4501558095330460300140d801050740c980c80300c804c6038030030388030510200d058580d4450950020b521046907420006881d40681c48207000314000c004458100704814184011202c298001400e541e0191004000701c0d0310a0401c0082090003905651001d8117a19424058400581d000c002098003c1f005001001c000d07c6450b0050000b10020525025035884a54042d48418070180c1040100c4001610003440d66003220301031544800100b04c04060307410001d000d0341050848280b02c40c850280665081841d014009031526040060017554803034000035510413181200203030b00b50005210a009528071007004d0304424864000200d8110143c20f0144111002500488103100414040c0008a68054191001d480d405101004000181c00040c0c4011603201c8d40101203c50141040e420030a06 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 41119698 1250 41118448 41118463
    0x5060a052106060a0f090c031404030306171609020906040503100203101d060409060f060308030a0608030c06070c0510050103031d0301060513090c08060106050a0909050601051b0717 80
    0x3000030b4504540f10b120810407141c059102e40d0000b40c0520000707003c00665a40964170b40101410005084250320700d5080e00740004032815004070ba52214104004946090118002040d503000f0306140d291a514041d010711046c003071407080a50115810a483e12020101d4028144c01000c55004a001c541c0240c0a54003c8440000302001410000340148142c60414000318141c08a00d055035940010b22005100028054400b1a00c802d0115010b15083c4166401b45005a003080e9036442c01300c100c04d0a8601c9a8003c8615070b1040156403200440450400e4000005d454052210040c5080051a06208907a0b20088a1410000004042d000315a80842e4002095858403000c403810070103080303c28a1146a40007203c4041c004034408150f80100022031041081f00103c60303c9180103072600d81c00340c01c10400300d1030005240c41910b400110b80401400035150600c20303880c107200004d00c9030007240311807443c0134100c00c042610741c0d1051160f100504090810b124040b4010060a60b484c0344 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 41120948 1250 41119698 41119759
    0x1202090310110906070b1b07020d0303050a110a0f020114060307180608010f05010617040203070b07060207051e060108060105010e090405010b0d0804050109060302030f0c070c090f050a0b09130605060a05 89
    0x24007414a0564400c00010380f48c1d035580082c4100094821030f1800c2d006082d00030414518503541c3c180c3d0802a00c1d400340501154409a9118030992002d010040c0c00c540c4070440001c03080a2010810001d554000341060075102d900016400741b2008010110103001d0542080c0751550030701006a040d40000c0e07101604272445a61500c0528200c40c00e8003460b01010344019405402024044c020500e0350401000200d104060040c0b5005c2c0d1900c6080c2490105038510707036216021003c007640304404000340c6002d00b622002030701d025454840060110341081c22054044c99500000800707208ac00c1d4001c40f400300000e8504074081125141000c540d620030f000782d5000c2068208042980341c07080c400e581c0b0484013102d510080791260030400f14035810011084601110151000ca400c460501808450f07000180000c00c540c1480164407080d10b00384000d1501921180d001c002d11502002003039020107070003840014140d240d00010074000d81c6c40342c0040350081400f4003405250401c00303008185004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 41122198 1250 41120948 41120971
    0x50f01211a0405090d08070215040b01030c05030303130b0c220e18060c130b0f041809030806010c050c0d0507030606050603101502030702130c1202090310110906070b 73
    0x7815030003080300f112800d58000c1e4159200e007a0480d0101d0203490165084011801201c10702d03001e0400c034100d101c0e801c40c2c0844106030144010001c201c15600c401c80a80301c200c2c0614158074060140d00c540d1425010007030b0520b203956020039001132040c01190550722460f030041d030340100301500e000400001440340f0410102d4420000e410440b04d01c3c8040031101980d0050100c0e07460302e5140d541c0741d42044104142c1c0726200b07600045c041d4040d4005001c2000e0340007002ea02c461a01200c40000a0038105001c0303110305140f51100080d5020084551140090174444100e05043c24284c0c40d100e01d002240381c020388441025003d00c0300000309101100e2003031000340121078864040c06800c0c001609c0d00c0702d4203403100c075042c4480304501d00d24066002c56403040783c0c1000299000600d12000f004038803140e46a540150201c0311b50b01160303010340e00c41c82050652400c07400b807021035a1020911002c04485680da240c501c06400d5a20031284440401403041c1c1d2a4142403c080c68259030030748000f00d840 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 41123448 1250 41122198 41122241
    0x4050f0d0e0a03030e060d0c020a140316060f0e060916050307081c0e09010308120a0c050405040f0b0402030a06150809030f03090c03010c1206060306050307050f0121 73
    0x2a803103000e100110000240402c004a0300e540c1e81643c01301d090f08032441e4410701c14081ca0502442034440c41442d00130340d0380141209075540c14406000040d05100780b81d6500100180000301c48510110360180750701ca580000c00c810302c0001003000700010300080905000710000d02140b17030000194420116400284080840d682d4802c16640759114410444150040c070700b525268503011600318a03030b04040c100001542c5d040000209190f2098101b15510380001c1400c841c240401070300994450100c050801080d40b5018024096003d24445d45100700d460304030f000c0c01d001c4a0740115031441c80143c07084d9101d040c04072503040685458051030281c26040c0f21569686071280080d2401a00d86c90091881d04501d102042c0e000c2c3e01c010105000c91042e610120398a8901344120701c248040c1380c1c0d402004450911000d17060302d1482e84010f003010308100b030500c55a50045403500480380110790b20200441440e0050345c0440b1145800e2031001107a2189400908080e005030350b00291014032210720 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 41124698 1250 41123448 41123473
    0x9011401030c091512030e01170403170121022202030c04030501050606072f06070c08011803091401170103060506040501050d030f1d061b010501050d0803070c081204050f 75
    0x700c100c4c1e441505004400d901c031400209015140383d010140041c0b501202480c00c51400108021050b50300b100001c2d43c00781c00d1500c41202180321070140c031440c00c800301441d103070144c4540c0c1e4001150029105a1541e0602500c070000c1350301071020100190000d5450303103465000541c6035001844151902e50a14001074198038203002287d11a07503100341401210800101c070360301c890031961010700104280c4070b1500946d81c0c0c0c40000c0e1280a00c01c02700001c00d0350400c110582582e0620810354006a0306602c2c00c40060380190160083d40e8a0041724402a118000100c0c0c1d05a40800401e80d41b81c00d060010081c082ca42d000a80b01d0002a601801903907030390010700c005891388190180003d84032404464255104407032005036044118111640750180c2000110941d01c803400d40c401c4600040000d8951410a005150062000321a584040601e54840c1c04503803000406034400c01016180345c80400c000c0b00c1c01e65030900900030311030380903240a1a00c0c60b950701242e0200034a52141880d900c05 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 41125948 1250 41124698 41124731
    0x1090c0b0301051e0a09020c0c130c050a0302030a02040e07020d030b1c02060a02070e101406090a0312090801140108011a060a0e03030f0706060e0705070c0b0309011401030c09 77
    0x100d44014242d0800580c025941041c840c0c10420b000b035014176030070340c006070342c82c03490004e408110a007401030840440e000e4104204155402c0000c054032382001c40300e4049980041c150b03241c16000781805030356991902c0b0f806c4c0c000d01c15500455078a80b40c0d00284582d444e4009064420707202c29807403c0103100f1400301084880c603020b1501c2000e074080070103807100604210019291080305801100c407141d803a64041003980004844066680010100401c07021480071b02c40c05207030100b84c440c9840c00c08080040f5800d4045808080d1921040300a000221032149844100a00c0910002c1203510409074050802881c00e05c6040c006609080c242e120b50b02c0c174074510245400340245118a40500300c001a110044200201a454001072080d500c00c4181540200810383c4204000991103050006000322040041c00310403c000702401034a00003454001e84406540c5d14080c3d040d12681c0350300f0650b02400d40b1a03240d02000150600010400480542c0b03801501c803113203001e22046010381010300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 41127198 1250 41125948 41125951
    0x5030c0d0209010c020a0e090111270a1203081005010f0f11010204170f071e12080403050109051005010b120411010c0c080d0813120f110f01090c0b03 66
    0x4404004000840e04884aa0700600c80d0600c107040c1000140655000500301840991119009854403800c00c40441e00030721580d0a940070486880d030030807071122212080d100905610a0f801c01040c58041419519450324000800d0318901c00c0440c4800ca140c01010f080081e92480c41d000525000817401e50f0150001504101c403554600e19010240101250400d805000703020301c55600b0000416003103451407084040e002c1c100001d090071100e82c0c2d0340310301e003d81d1940000104039040002100111104108000b168941503400400c42491304001000c0e00c02da0f4001022036103003000500030040040b80001172808425020482c0e84e80c0e45950301e415204030304610850900100010300002e081e802e201414030818034110410189980c0c07003100b5002d03c0d800c62000340e8030100c04114459031000c0117035403006664001240d680529030301e075009540c0382d08104040c02031009080403030a00c0744510400c0d00080104994880c20009882402042c1009058560484440e80400c0c0c0d200b03a903040382d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 41128448 1250 41127198 41127211
    0x17010506070209040602040902070503040302030c0f01050315010201060b0d0e0c010807020703060e010609021204060f1e020306011103220e040302060610050d0203070f0e03010b01080601030b0604031202060f070503 94
    0x40c40d101ca55420440d03001c40003801220403070b90900c40803590030514030283c00900c0c8a10000c2d9034403400c500406141c504e46640c56846202c61080d518490b0364804141c3c0d81002c15a0490100034000100503809170400d0307080003441c02404100269501e0054001c0001d0080101c00c0da00030301c089600441d011700c0202d5440015038021841000041c420340e00c803c0148480300b0000a07001e0300e03044440c0981e40642c0c40d40d10b0544406d003d00c0103004075849021191070b110001004850114144454902400400c600c400c523404000120348d03901071004e0860035030501c82620b80c0d0304400b070308145110301c0c1e5004009001a0004d03002c2103140180039044d0040e5055001800280e4400c02040344a884c850301c4402042000d00c140d501c40c1e20140040d5024410540703d020702d400030030400404032101c4602c100c0c80f0b6070404c0760304159a6005840b8941100c000e20300850070030840d2021903801c0c4035692004022100c9072902291070360740800c090707000d000320391225103031070720307200c00482d080d01013034641 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 41129698 1250 41128448 41128459
    0xf0506060a0f090e0405060403140307020c0913021908010606050906090909030c1507030c05160605150303040312110304030c3c090c02011109130e0607020a03170105 73
    0x50012980144000401441c1914243d070626455000800c00c105041d0780854140e0721120034402050b0708021002c082d10f41140c83c003811860121b80095640801d500710b03e00816400c0c2c0403030409030703c5d44100901c1c541c000d03005003402003900c0c0d0450700d801101d114164513540303403d002080841c466000c44030389210050006007010318007820409402e00c06000c0da00944400c21440d861483e050203200c1e004120011120362502c0c082002400b900c0d203c403e000f040107000c11501c855181c11142101d00e40d50001d00000e51781d540c1c0072200e54010984001154144000b2030000b040040b0250203015640d090350340c4508484032100000e41c0c9010300d0200821840c003c901c10710440440c81c280f40810100c8030f02c91944e000950216070710300070881c070401e4849442e00d41c00b07008012150041210780015440200032a1011a9040d070040c09451a580c0c42410b01c590986462080307908410f000440303240a54400e414000800380d07603485034034800c401080b08ac64408003000c94144249040b200c0c003506 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 41130948 1250 41129698 41129707
    0xc040213090c030b030d0305071e0c0605060a050310060312030e0303011a090a030f110303040f05090901110c0703031b0803040303020a021e0a0204050c0c190501110f04090f050606 79
    0x80341d000d0304100d075281c000c06070755118810280d50104111380e81541107460018907030070803500003480d11841c104d105507110204401400160741c80104210815040403000501b600e8000004258070302e554403155252181c09204060394810b13130b000d1700890344103040c0c100b400c44802005030b083c0e4200c02e07078100054105000402226424610340300e80440314540491801c0140d00020f640188a0382003503a004440f44003640030003041c983c0c030b2404031004900450030245800c2012a168055001da02c0c02104e4480c007150001c0c030709400c00e48030740b41c0800485446000300403130266980c4243c80240c0000320040d20341d040541403034241615440e0000c0e681e03407541d92551000c1d0065403100e00060114030482144680007008040040c110404900c003614910215004000680d0b201409030381c84c400d003c001400a03903600056801502e042007007554486100c50901e240180b02c61391440307a44000c000703103084420070081c00070003d80d0642082088482908900402140ca04a4260350070070810031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 41132198 1250 41130948 41130959
    0x1201090504052503080d050105010e01020a05060711030403021e1003020f120601051303120e0f030c010f090f09050103021002010203090c061e0c0a050f150103060207082503020c040213 81
    0x103071070031030030400341018140f140d40755119400c5904c40c03001042200e550302e00500c8650b0707001c0b050812070b00c000d100030b05000c802521825103c0c14080d001006220a6010380f003004641803068400554005103184c00c8161058411010740c1408200d140c0f01c1c19081e40084080742c046c0c402d40b940c1d403a228904a080440049c0200581c917030150005041c00303420700c5002c3d0050b00d5902d600014500c1100d5410b290806580c01030110241051041d10524801b02841415100003031012003000b02441d101507407111059041c1c0d120440b035041039031540100300c400b1501c1500c64102c1c1e81202d1080d92304003808080010100d00301d02050750043eaa540010080400d10b00d0607101404800c1c1200c10401c907030544411125006501409808129422003030700ca42c103106041c010380d020003850340c0291400c194031070005d5205d9401400000d001640c007003824020703c0061015184041032b0303540107400700c01c8643ca960b1100701c1c0000040f80140314004800c074050402e0f00950340d411a4600c02a9025810300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 41133448 1250 41132198 41132233
    0xc0105100b120a06180b0405010f0302030a022b0501050603120a05160809040f051012030f030207030302070b0c07020307060e01050d09060b03031314010801030201050f0a02070b030c120109050405 86
    0x500000243c40d00c9800c0800e640d6080a0f0307141c003409125400080c8960b5132801e1000343d5205034850303640710150b17490800140e280443c503c1c0c5410340c120360340c40c40c4c501d6544669038540003e00b0301454242c3c800300303000e04204055211901441044084603c2c0002d410b007032540c103114001c900000200240320304091010011074180c05030744103003501030904d40f07104045800c40f03d2400d038000119443d00c061046403c1030b080c3c0c00018180d42e01e0026903521039a20040c6c01544804070032010941c0c0000c00d40c050500c2681501c41c0c55601160002807824580c4c103a2003d900510b034181d10034042c0403c002895030182200078000072040c1c44940c1040ca21001c0306004100e414ac4c151485912282d02010759502030004040c1400480100c40d5218100003045907084052002c0c2814800074400520150380c004003500c00004040301d4241d40c503403030f44801300e04002c00d5a004008000002c41030006443c8048041c0103102d004002c0c8a40903aa50410b0b81c095680c1a10042c005070041d54807282d218092 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 41134698 1250 41133448 41133451
    0xc030305061203030705120a0902012a0618060506090708150d0c080102041d0411040203150a0b031503011103060402030705120c07020a05010201091a22080c0105100b12 74
    0xd002c8014410a654502e09580c81103400d43e001600028003550700001c50a202e82c1c03c40f41584007008000081d90018100c0c00703d0044480c204160145101018514416106e403101d41c40201070094400d0700d843c040c1e20119040781187c0c0c85081000180c0642801c40b046881102d980d9900d0200d61504120207866100c1c030000ca64001c8041a440c0e4003080340141d07100000c1560000040c0d035503140a03070310f500c620380b428940c00e001007901051001207060155a50480070742250011394986070805800c3e409001d00d49200d17000604e030030000a0310040d03130002c2c40c410320310107404011615001c800c16003200d134103410100380e8000c24000f15401d0b06166029681c00340440c10124948020300b4034020b12100704845144410340300003034580440c20b18000a0004060a000a05c6200081d1356080c850810b08401311148401240001e01c0c6120303004606051003048602c05021004a4140b034803650303102820404c22036007042c021843c00180c00c1006800c46502c003c0c21401d100d044482d05280590 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 41135948 1250 41134698 41134711
    0xa05040b0303120f0907050a031a0705070f050607080108010603170d0b151e0c031606110a081602150403080403032c0d0201021306050304020406120b07030e0a030c030305 75
    0x703020000d4824006601d0f039002d1210140048010703c0c0c12000701d403034070481c0d0300014012088802c04000140074000c948140c102800040c450596544d00304460600402001503c13506442c001c440620201040703c0d8010105503070341c1c00300c1d0380e00c82407541e080e00c0b00c5120007890016101c20001e003268140300584003400d150a0302003150f8040000281d04070001000d0103600001c0059070f8540ca01c01e100c00c0c006079035122810301d4100540f818509031240240d0b011020001c2b01d490105040001690201c50145050b6812a0715090200c60051080d10115031480030303a00b030841681c034520700005100592554440404800355070700d0307408072500c1c003000d08210103142e10303294002c40c8107a100d000719103c5044c2055490300e001994440c1803411030345882c0740041d6403040180c82e9444100c5010003040d90b10030305000340d403a00c6a10225009201507441090400b50030740a000070040d583d11828000c80c207941d0144039401c001c80b40c0d65107500b82c0c100004d01040340d8203000c00c0028041e42003254000c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 41137198 1250 41135948 41135953
    0x1401050319020a02100c0309020d26030a0608160b0403150b0a06030c030b040506280b0309010b010207060305070e042703050306030f030306060f1b01020f0301150c020a05040b03 78
    0x185100407500603a000050008050b07045803030081c40014140c403d40e2125400c61905006180043d00032030410409864085e05a21504000502d03490420311840c10086e80300c0b0718643d807443c000a03424000c3c0380601034895140501c0c060f00000c075440c1c0b010041a54016203501e0301c4d0a10359520712205800c5a0391908082e5180c446080740342d554144208002c050176100441d90031a144001412950080c0302c80d0b00c03840c984401d00c509600c03801a041e59010840c00100100c0c1130005580c02410450752140c07000c420004100640c140040d04002c0b400c040a800b240c0f01c0300d44a003c10390a842080b42e2040005110306408c03079045c41c1640083c040d0203400e4901c1e0400c0d10801550500d0300008071001d8000c0380d800400d006190400300040c0011380d0502000d50700b07604050b00015580e10948032800070260002c03031107001d03011070501c1c0245040d403144000c40d61440d03021001e00c69a082482001e0120218501c0c4000c001e004000c081100d40d4010304412103581803904210080000c81c800c2e03501407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 41138448 1250 41137198 41137231
    0x80d0804020312030403050918150111010e0a11010822060216020d0b09060709140618030d02100c03050103150e07050d2001030e0304030b0601180605030f1014010503 73
    0x40f142c50025405580255142ca555410300710600070603c4460b0901d264201043c400c11044860078000d00f18041024030385186003110500409026092511000100f4014000514100f21021540303103020402030300c8981c225990030390803644050f0aa4260f851114840c3c61010010f01301d503005218490001160034070008564000c910000b0702c02000700d400c0f00302e81080c0480382000300300d01a40031b040c82c5070082503182002c0c2d142e101303103131442c20050060002007103441c99004c03068144e0203071000c085c040303450403c4500300096880442590302c08410740f401001200d800c1c030a0045d80d0580e40c100703c20034010b500c031210120042089069100b00341c01200e1000c46d09550b080c1804040d01c4c01141d50710020352101400701440c2040c69445414146401d424001814011096904803a000314034444143c0c4c9101c0140d44281b07210820b0042c020a8100100e403541d00302c00514054004600340343c156580d04991464000390394021070142d081d0f03001002103a0f610500007075600c621403203100b0410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 41139698 1250 41138448 41138473
    0x30806060d0e03090109080111040303030209040204050315040c05030c0108040b0a0e0d0c150207020a030b0901020708030a0219092d03020d050604020102240601030207020d0b15030d020601080d08040203 89
    0x1142d10484941c0c1107a000000c140d8910340c0d00c017070080d024105c0400200085160113020300024401c1d448014145074010900d0101caa40d160305640080c01d019040e6010342401d07403984070b14218100c80c01c50345114003120101d1a8200028a80e0400c403060711034030440d85598558225068000780003e560b652107241c01505d0383c5040c0701c01407240b1041d4032480c0c0e444020f8a058814042a20001a45140b0501040c40540e40302140c42c0b040b6500b00d00031400c3d90300d5041107680a8070400c1000b600840000050150f0101142d0007000a00003000715001080c0ea0b034101225145014401c1e07800414607880e04a890643c1904003094160715012032509542ea41d43c0890800c2d103034290181c48c690001420482903580612503034038581d18030312130499010210040140c80c190b010300024101a07011488204544800d518595000d400001070001d51411807042101c4100300304030360b8001d006150050410728000903100d8103070b65910015001820603a4800c075010400200266414030528483d07800 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 41140948 1250 41139698 41139701
    0x70c0e011d060f0d03051603050711041406010e04090203160806070507030f08041509110301060b070203060f04020a03021201150609080619020409020a050306090601020613030806060d 81
    0x614041004401640c5071041d0740800d07541c0990548222041e200810100303070788150360b0040c07000003150341980a00f4503007000c5800d0f0282c41e0307072803000d503d2400b04d00307083c90b030007002422000307118500d1404c81c40c0c240070078401039502d884e0b0308003030034820400417803050b41c010290210906e40c06040043c0d040c0f000c0d00001d01d00043c080100080b034041d00d03010300c50518180041a8020b0907414910b01c0c000c070665009000d2120a0a070104111202001c2000c0080c2580d011003942e039090310070700c02d442a50a042c8c2c0c2d49804000410711947c60000002032903070403002540d41c0c00d60014058034040d070b1803403404846460000d0049030721900d8020003000507900d000316001c07520f62a000010303071071a01640503036180340c0a40001c0203002c903009003001500000503185502201c4812148207400b901c0103008064016504a0710b0140e00204100c03818541c8040910f200e02c3c8121055042d981f1401c0042e600e0b000107a90580b1400300031001e0f000801d018042d80c2c1d40123500503107260300c1c100800e0304000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 41142198 1250 41140948 41140973
    0x302100f150303030b0a080d020706050d18080901031514040b0d02030609030304060e06190c090315090302010609060812071b0e0105090906090717010f050717090a0201090b03090307 80
    0x100400d5580c04c194410f8240481c401b40036010f09801040b0700a229240a03586401510a400420500140130800507590350041c0301c581d6008001c0400150b420f1a10005035002030b07500742d0000b0714120a0404040b500120107040303038840c40c01007202c115203405000c003500ca4040c4a9411a10300d034002030050f101001601c6c0314070b08150242da2a41401e1030a0426901084450200f542c03205052003075440327440401150607039010310b00258000c581d0009035055242640003800c1c6580d01825460750341c149400444096100c1c3d402005003688500c00300040361034601914107981e01071001910b14007034280003044020f0161500603110040000002d0007440181c05c20034414810000401c8a803d000c4101c5c0c0d0480d051801401003840c15051856a0300c1041c815000141e00050400084140c2035102c2e800242d0b102509100d18580017502612551041c40c2e0103003060880f40000c1d194110200e50601c160798160f403289251132820302e206900d60030180c408101030204101c00c41c00201001e803c2c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 41143448 1250 41142198 41142203
    0x5100b0a05150408070e0103120305070e04020a110f011e050408040506092b030f020a030f0f0516060203060f1c0206031005100f0809030a0813080c0601080a0203010b06070302100f1503 81
    0x146d50940c198134040c100611007440c0c0c1c07000d060411042c066016046040749400c400e00381c80c010380300c40101004850040705800c0c07031b5420b800f418005180b1720301c040d004040c071071201d43c018000c1140d5090300101101c10440e409041982c091006005c14a0080000c05034502c0042035501e0410511030722100031040c41000c1410110440c074440c081541014030704070a11624009442003210300d0314060038480c00c1d00100000c102c2c00b2003101c2e403120300a00940b41d1080307280804500490b55403a00368000c0d032080da0458070030f90943c1260445440d004e07000f003413a400300c44501400c2d1b03032440d803c2c4074940d08080c0c0725a603e42015500442c5540340c500c1c01000b072031015079501500c9060b000024000310030140054045810400c040311403990002e1200e81c12903504244a03c0c45076490901c21114000d10346000800d018090000400340400541d8841850088008020411401041100600c5540d00040258120116015164449510110000c0d014003404a00c0b2510400540102d01ba241c104 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 41144698 1250 41143448 41143469
    0x9070f0f0906090c17060310090501020301080601050d020a0611010f090f060c080907120f05030c0d02160e070c06110a0c060e0610031713030b010305100b0a0515040807 74
    0x4029011103400790b0401801c02c00b604210407410514020070341e0404c0d1040940c0c80c3e10420100d07200b510204140c4187c1c02c50404108840845482c299020350b0080c480c445c028072403400081642d11b0015210340050b6401000c22030030914040040d60221003402c1105415581c41061644a03038040c002d02c805030b481044115590030992810104440f0f45030f5005080041060030000d5002001a092082c2c5a0381741e840e0804144504d07081c0303003da11307001e0f0003012400702041c6003070351000014007540d955070380d82c00303980719540700b80084000d075010344c40b41015060440b00420502c6011300c8400d0b69a60042c034012904c008121540d00540d4080299800002c0400f0225403d204240c071440f80d140c400d540160040d41440a03015584500700d01014006c4d10b00318810b2010059650200c2d5030040f401000820341d6980d83c00c29000302e1800740b10a031124025480581c42d4000d0510a00c0a019001041e412069007002c050005136109070840758481c00c01000041004070701001681c000b01200141c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 41145948 1250 41144698 41144729
    0xb0405090616141902010c02060408040504020903030d020d06030302060a1e05040503090a03080a030c0203070b0126010614040509160303050904110d050702120a020c090c0409050901050405010b010f05040e09070f 93
    0x20020308587d20301c080d240c1190031010602002892040451301140c804660240e01c403100301e000241184140618071100c144005050200350f00300b90020403c490280d02aa021a95600c4515085c0c4a0803ca0303081310300840049030160b580150f00c0141c009005104036424455203c010585c0300d805a041902c0c2d40402040e0b240210780e05010314401d10995101540c202401a941c5c61344507101802100c1d000036112044005d452040c007a022032500c5040700a000d0940d070f6480041008103194000381c0540e00303100c005003492100041c03021407581c00d190710251680c40c50300c0c01c0b0741a803c0b00f41102d510540312005804101d5141c1c0c0a0404103150b0130001519080080c0c01a02e001402c0039010740ca9801404142059900800c1e030603094101603d2001c42643c2c1d0140c0d0410911840d00040a91460b00742448040c0605600403440341c4d1140008001c0c9204040054546030010549040001d00400c02444500c107a12045900048054110f0707440e641c64400c3c0301024075880e04000068881001d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 41147198 1250 41145948 41145997
    0x20a020307060c0c170a0203070f030507060c080a030c0201020d0906050609060306041e05010605040c080417030c09010c0203010902040c0c0303110301260a15020702040b040509061614 81
    0x10400082c030340c60030940c081c41c000d980e0f8005504000d1082040005280c5400460800148002c5200c154000c2c2500c03000d90b101c80c1c0340282c0d10b07494002503d0314420341001180c2280a000d40200068004a1943c100710070008110060483e158802d800c5540a002e00014901c0c00e0040c0c6459a2103081d0200d6103260600a10207000d03c000c01c418400c0d03029000b4007000c11080b050580c01c081d0044198040d00310241030003800f50440c1c3e400144c202e0b14001c013001809034000d0416004522480e031181c010507003044680003d000664450a034000c2c04c10803520250b010301e8020000303a03c0a07001190501c100d80001e800c641509031118045000f1030b00130000c040e030502c40d0441c58045048a44e086505001d1201450008034403c0a115560188000c043c1d0404100440782c40d644002010045540d120002c4081d4100c00003c0b4007075424000300b05100e18181c080d0a100b81d0b4108000e145030341c1d034070ac0710060144c151024102400022400480000c80440c0241251084132920b580506c1d141c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 41148448 1250 41147198 41147203
    0x40302090a090c030f080f07080301060e010c15020901121a0112140f0601030906110c0c010302030108030d0b0d05070602031c0b0d081c0e0a0302060c0f030615040803030403020a0203 80
    0x100110450352801c09080c1c0050340f2448000241ca070880b030b003000c0c688403d1400076140c0c030400d0000302084401042c8001008101d10080d070590311030350394102841c10240010740d13561a80320402080f00325040d40356012000d40703a02070118000145054020a031302e075030910040b59228102400b4908100f295a405560091041000e00d14012002c004480920036101040100500340b01d8000ca41d103008541036a1013a0840c401e81c0da08040100142d0b1280b92140340380781c0c04400460042c2c005c1d4460080fa56020313100fa030b4100c40111028500c0d080203412810300505030410516070ac4001e50310520702040c01040201c0240c026074004503a101c2e50b40d0307980c9880107458082c80f0301060901d10341025540b40c0158003d0380e41d9003c0c81c0d03247c4030b80c04001d03400c0f0002802600c24419500e031480c4641d1113880014074032000fa002e5000e840140c0c480560b104228494844541000d103410030108401d401e1100d809420160b26000407802c0540351220341b07082d0f5009980a5005900c070490034030035498107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 41149698 1250 41148448 41148451
    0xd05010e090a080d0212100303080108010218090a021201092412020405180d0c021008090a0f030e0603010b0d0e060114040f0b06040b03090708060c0906090a0302040f0204030209 78
    0x4408030206854803000c01c0c1e9403002011001400b1007004200c2000810544e01550030a21300d07441060300b6494000c4034000c8580d242c1c40203a0004400c04000505400c5c1842250010b1811842200b410200e0b1410300640100150800d403945901b08800003413503043c201d506020b4405204041260708004000b0003030000520a0705e51a82700c2c40108101803082041c1ca0102d480e4103440c0810144d40c1c0302800c0c009003059407000c0c1203900800840e150020ba021a000d03441502c04c455450510481c520100d500103000c852441590b0303c00319444c80410405845c1c1603e142c481d00d45550800387c56404250650002e90040c5440a4042140b000d0003846008440111072008010b108640c58110035110455080c0e90080c041e5540e1026003110b21300c41d030440801c40d00042d01044d03440c5d60f661b038403807640d0344111401c0903517000c1e0109c0410400e002161b180e00880314445018101000f24040140e10780c40084040d90204c07180c60000016200d90182d0031a009419800507143c1e03240d4014000745050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 41150948 1250 41149698 41149709
    0x30602030c03180d05030a090309080d0e0111010603020f13020d020a0c03021912050708270a0e01060203072003010501060f030c0504031a040503070b10030614091506240d0501 77
    0x80340300c610302c01c903a10038241c960140c0e000c43c0c0408d26483c0340c203060b240c11003140c0040c080e5010340711203c030110b60885000c0085010a0343c82d2072105290700341503822541c15000007035001c04501c2221007146070041d000242c101c0c4507100145403008145000040340d0000420102044140003d6800e1607018800701c1e052211164030300c680e02c0002d0740d80c4109207000e00041d40a11002080d0340c000d10111105035000205100c24201102c1c40103088000300003100260544a035104c0d1001049004907141c4890490320150019420a200b654a440035010940581d01d8000382110a03000940c0d400d0040324005c18450329010b540150000c2c0081c10b0f5103215283c80c4c1070140800007080040e904280c1c11101900c1c3c45510211900ca80c60003600314400c4080140c100010032050110010081400a044071f12880e410441c80090309104c0303e50328011100190310750091b100310168002540c43d1683e00c0341006000200d491020447c01c0c90196400c0040400c1c003030081030285e610000c51050601512 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 41152198 1250 41150948 41150953
    0xb01050402072303040906080102030f0c070b04020411070b070903060608010b0312090105040e070905030c04060b16060e030d0f05010e06130c0903060608030c010515060a0810030602030c0318 84
    0x9545504003c0d10b050301c0c50031401c1294890b04000d00c1420700030740c1c0203403442880c1400f59a6503800f071907001c0c0d003090340c00d403003040181e0021a00c100c1443c82220605a0b00c030400c2856640c4039002c006c0104070180950f40415010003c541c0003691180c0300c00d204a5150b10340e1100c0c5819070070500d0446840390040340c1c040e071602900e544155000075404810300002d1510960f03540d1004012031b098002c5520804042030900b003132110803508146117206460041e0222440030f101c20041005446a500c500c4a020504000b405039400c40d40c0c2541710340d103000d0784001c01c80550b0032580724950390041d00405000c55440c0c40a22608205021341c07401081c0c0040764290900f00000017a14075511030b5049440d003030741c0ba695184124002e1082800071900803030304001d20f0307603a0b01840752a54441826207085510701400140b501d114504a901c42c0000540942d06086519030f061360340032006440000c05404045002000801c2800250300c01c51010501075143d0404001e040c9040c8440b02103032610740c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 41153448 1250 41152198 41152207
    0x6030106081e0a060204060c15060b0409051f090e01050f090c060711040507030207030206070f0e04151503020a110c010c030302090f040906020a1701030c030602030402011103160b01050402 83
    0x9000000e02c4016940300801c0030350716584507181151804032110f400030600b0b800400c0001d5502d400c9600d0040550080c0c407000f0150510603510401c686441c0a07000740c1c41400e100134008203001e503100301c0c1d000707885003800030b80038149811110001040b41d004c1c0960588801139103c6001c028080c00707411450300c90050780141002d01e88141c544400040c13030760080380042041014000c0d0300c49034801031000940104101c1c00c06c40c1d8000c01a51105030305030098401c0d4004514001e00c5160410007044c4196980007928185108120141110200c0791a1070001ca07180881c82001c501070300280031245480050303560500e0b00c00544044034810f215900c5070000000d08490780d0304007000d10f0350a90701d07103401a81ca4400700c0005a05050054107036070000d03d009042c108102d8180d00400c400d0b0706a441d010060036140c01e43d21030004003404020078259614400308009200d640246800c14414105000150010504a4555002076a841c100510324429007002c1c0034581c000b903801742005a4096203030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 41154698 1250 41153448 41153459
    0x14061504230102070e150a061110020904091b05030d020601031a13050f0d0320190314040b040303050711060403110f030d0212010906080a0f0305040302060c030a030506030106 77
    0x3a41d4030380041040191511a03a41d25a8400d01c00100030340031102d003008480c10091000c502918505601c280104031640e0040707405400f030110b9010100040d00140500c400d40308000b00690030021a8a0f000381e2103a1400c80040d200f075410b24501840280100320441c0346c14105403030207450071200015500514014004179401c0c603d21211500307160a042c0881d11482011103803011403000292040c05400584242a03401003404803180c07100e070750140030302080c1000040d00002c1d4400000c41d0043c0820114103184031341c804c1100c0ca041141400920500b1b400034040d0344207003c94045500c0004030701000308241c3c040c0718560304006245072010300014010025a074a01c030141028040c00411088920a000c007007142c00307074900c942e4044c1c81d1501950180030002e0b4010b1500c41042281300380000c12040003070301c02c0c0c2048424038002003030328008640340c1f440494102e030810742c00c20604000110141c2c40c2c00c070041c0640e40040740210755401c0c0741c25009045940141c003441c46641401410000d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 41155948 1250 41154698 41154719
    0x5061303080309190305120f0106091215150e090102040f090e0c060a030c140a020d120905070303090618030507050105090103021309090c0609031e02040e0114061504 73
    0x1a03941c050704640c0d594541103070452030f14441440d541d20300315211101e00101a03014001e00040608480030441d1070b103442c44c962252039824098900080d00020041040e03440c0c440d511a402c900800750464454004030b104400c2d103001e02d86c01e14183c0c5d54000100540c6412140403503004416030000c609050074001030182d202814400ca04405072680303548110448244110700d083e00c0020031013a51502d1000000d0b025091007280000844c003032008841c0c810811008139181240a9800303070800c107101e403006448800040d0007400510350703a129400c00041e01000f40602441c040e4642c0a0254640000105100c2e0254903200c004a000101000081d6000034540140c4130242059911911901c0c0103d000340240c3e2603001440d80c01c0400061016250740c400034003d401000508121a12624162082001440000c004010100c02c2070707a0342100301f2a50300054401000800c5040c070000c1f071142500d001030160303c05880c10b68140011445c000c119405142c02481e01e141c10f00d482c0c400b4498 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 41157198 1250 41155948 41155987
    0x2a0301180b01120c111203010302090f07020f0601030c0f1e060e0607080d0b032a1903050d03060906050a0b040306020a1e0210052233020d060506 64
    0x20486901e841084840768040d60020101289422041011824800d00100395010149082c6064014580300e04130545010088034103a80e006000c80801d620782c00e1803100c60080c010300c3c070000c5014402c58414401800d02640e0b009501620b48800040d0400340c65201055407580021800384014a0460b0161034071848041111010b0410b050b08081e8a40810724074883c4200007403800000248007299a0055400090080360940c112a00b00185400245078490a060b08005000d03441501220526218403541c100c04840700081f5069952661440d2600e41060348076008039071111810300004065201d00701c000c1c8800c03122192524900300c0f0012580c07082c0d02000c1d103030b150001801110305000d00e807034401c802014171040b0103031624104001d48071f003074441c00d070108a0b0a09010540e1510208102c0d00026400075000c030111800b41d907041d501142034015981342c0d6045445165810528a04d943c400c80c01d02c0e100541d032a0080c4007450704a901d51b40155102d40c00921078140d0702d40c071010409 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 41158448 1250 41157198 41157239
    0x50108060d0f150204030302030d05070f090e07020a080c0105071106071218020604032103140a020307020a0203070f03020306010801050702120706020f030c041403060f160e03062a0301 81
    0xc0700c442c070007070901c000c2c3e000999200c4a41240002070000801d90300200401a251914400308020b480d205000c640c4a5038219a05e000100340040900c083c2c0122046140c00844500485000c14820355a03400d503604101121095030350344100b0048041d0f0051500030380b68043d030300541042d1138201000340c02d007864418031302451960747d400c07103a00070204103c00759013640081c400c507243caa4a10f00021113140070450000003400c0681c5021919000b401624858016105d01015030341e03626800304029000180140c003144985203010001d624180203c0c0003611b55180d82044046c110f005040c6081010307070140f10b40da07141100700801194041114020a6038094000d640e610030360510300042e020720001104800300002c248081000400014400c1310200d0412666400c0903000b01600e60348203c9030050b440e020000012808120545006002410b508041c1403803046980440d00e0100d044032040300d80103200041200d20b9403d01c3c2c404203480340351807189195604010015007200200c8098 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 41159698 1250 41158448 41158463
    0x60e15031c0e030a0c030507090603020607020d05031606050105010e0303030c041208040e0f0105040507020a05070506030a1401140906190b033412140c0304020301090f0807020307050108060d 84
    0x40e10006104042d1075000c040000c0403203d00d15014140300c0142502d6120880d0307240f2404400182c24019405210f003220b40080185090001d65004e00c001041c42d103000b1109404104107160000062024441c00704c0d00a00e00028250b040000261000d0b00f161a1944a039100380300304400b00000ba42100c0a1b252031082d103070350560040c83c0620746070207990081c414400302c2004009225960390f0445048070011141802662071b5114242d0700c964a26501070000d400c4040d0920050601400542e04001e040c200090540f40307282600661074000c0e04242440442142404004d00c0c0440895400440494010076402048030b80701014503058841c12014043c04000222440d0003406001c014a0b01c000440210350683c2038103003620404a00c2c0100410040280a2000304c0c00d841128816030940840402985800d15180f46982000380200d9040d900c585140000070007540030700c852a4850842107448826030310405d4241100b9400c418100031a00081041030741d10b83c3c648002c0c0e581c01c10302 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 41160948 1250 41159698 41159743
    0xc060904020c01061a0d0506090f0f06060f120603010f021201060f030b0d050a03090603020a140f0c0d0903060513150203040c05040c0f08010b1317070e0a060e1503 72
    0x7105409400395601c180c40801c5c40290500010850a0040c046156983c90421071039503500104003e40e401a03a039040344101200c0000c1c46500c9600000d42c11100c000d00160070448141c600000d2940262240c0364040c0c1023106001c41c80c2400d006d042c040014050f025414540481d0f00b01c109118144103007400c12010205104025003c1d9001e1481e150000e0080041c514140c20301030380d01d0b204a80c0c21000a07410040001c0e10510070302c29038400a42d1660360344a41d400d840050145508451480c40400b01c1c1040b1056910038100034031041114551603a0b590b0a10758286901202c0c00240b054240c1001000c0c01070020300d0301a01d8148500e900c14005031030742c44a050459901c030aa80180b6042407600360b0a017885900000d0490b1101d22550307803800180e0f01c03003556101c1c42c011010103c60790784900b04280030783c0604d400e1301d882401d8500215520175a072401130603245001600e099035015600c500a020407103866007083c0c3d104904c030600c10781c040c0014001c2555182c202015941000c2e1468 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 41162198 1250 41160948 41160967
    0xb12070605070b060f01170c070b0f04020907080f0106180807032a050a0302130f06090e0d111b06070b0a0b040e01050912030a06050306041a01080a03020a0318050d050c040507020c06090402 83
    0x3001d41b270080750001035103031140c9401d249500c0c00d41001d860070f9201d56034040016a4403845403070154401c2a00d8140d035281c90340703048130a89408000404450901d4201c0ba80450340641c10800c10b07005501900320b40c1c050106010083d01b00b20401c000c00244880382640502151f00c5400c800411a075058030114072060b0740300080b50040400800b032030b004606042000500252640191002540b40e40030b07505c82c6050040142c032114058007291071180c0240c0001c560708006403855001c003200140c0454034004c03242c2e8982861282c00c9411601c425540c029400d19400d2901c640009482010001c2006003045001507070b07078000b0100c21100d52440080003d92292043c2c110400a040c007804031041c6003854500a6000d090280d01011442c12160000800c1403001600d55070103030305a00070b0810f1010702c3d10112001c1074900315007041d002801e440010300e5120701d04031183d41d034014030140840414980c100001e6030300c040d012130f045511801c112a030f56540c01040b6000749404543c0140c1c0d84c016107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 41163448 1250 41162198 41162221
    0x3130b0d0b10020c0301110711092502010509070906060e2101060e01051c08160305120103050f0d1806120b0d080309070603021c0b12070605070b060f0117 68
    0x107400454108038034480c049021500003407050326903d0708a00a01c0b541120100900c83c600903000301a000740b44c2281d40c0340c400c1c10580700c2a6001000c00341c15400d803400307001044004a03920340e60000142e54510400400c03101c140321003409007a81090a01c10a40b034108000c00d5804600c0e0880d100d02403e01c00941141c00d080c205000680d0408000d001c83c5903107944e1048101d03400d206407801142004030111503d10000448980c15038003011031424a043c698101d0314070703000b4010890502000300000b488810402c440c40e4000d510920060000c01c0c500721125080a0240c4034807801c3c00208101c002c3d40001c40400e2000351480703071500e02c24031085c560402029280782400e030354220076a503080c3c1b0203200b84480110301c1201c0400c01c0365292a0b8072071044040744070348031041c0b40005100c15600102e440c81d40200103141c40051941c11040182150a4108007a41c1d2100300400c1000801c0000c00401c1020b95070700600032a03640b102c4445101c0068855410304007202d4401c12035500055101440 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 41164698 1250 41163448 41163461
    0x5090c12010b0a0807050303071b0302031608010b0907081602030403120806180105061204110a0902090a21030c1a0103030c0209090a0c09020901050c0307060209040b0303130b0d 78
    0x244506400012240d03001d0080c00100700d11401041c034440041344103540041d5240c2241d8002d0015850b01000b5250b50001800d20103500399040d044006c000056034003003000360a10b131414141032851526001032107003104c0c030700e003050790045200d02c040059440d00001c81c0c640c0108010303d10001c20900d1031b0202d0862140307070001000d100485a8055129504c000264494101504c40f2043c800034038100e285001000d100d8580d11410411070080d10078194003409802078880c10841224042213000a2038240c01034100840880d804900b40300285450b03900c88001345101051020014100d0700600400d12108801505002c11315507800204200f05e424003000140e51101b205455849140040124013440c40980c40b4070704140201d1010725001c52245090b0340d110a00d61205032803d02d010020b03400c17451001d4140102401020815242840108410340c403d180c0181d0310301c1302d002040200d031500103070325001b64002d00c059070b003d01c4866800029541c11128213903d03410710b00501e01c0500700c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 41165948 1250 41164698 41164723
    0x1003020c031303021206010b030705071a070c020a120201050706090201020a0c030317010e07080402010c060b130212070504030206071506050a180b0103110a031a1c0302010b010c0b06040509 83
    0x40051800300080c00c4503004003e41c1d20031142024400000c140300c1d42d80700b0f028000e608400c00c0c10004948a98007032401480400d20440c1503030790031500310f805890180c500721869070108883c0800e807011854500515405029400701c0a5040100c540000380b450181110040c4656683d280d5202175a0003000a0101e0030790190202814a4913031038014030250800b9400c01080d00343c400086095802400b0f07480c4a409640d030740b00c0d151b680b41d4004680c20352542c007054804958035102000f240e00e8620319180c44800794500540e48080b400e8418050403030081ca0f41c2c1c10842c0034401400103a6451007102d042e031b5000004c04d40c030300800850400c001d190301e51040d82e1000364507030300041000a80c101200340005107081005288214001035047d1460301e41c2c1e110718104104612401140a640300c510740344401c01400c0c003580c071030f200850300f42c20200c9401000f007c0700c20803580809d5070901072210000d5007841e10340a04030306641c5180044074003030a600c0c455500c0c0d000080d500401040031086c41c82 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 41167198 1250 41165948 41165953
    0x60f03040312050a0b010e010c0c0b03090304050f1206010b0c190308060906041b030e12040308040509070201090b0103080705030d0504121704050d08090316060218040902030c1003020c 81
    0xe040c540504414000c005840509081000040c5442014030901c0c0412130180c54075144080040d00450b0902e450580803251a4164040860224100c0024600c11411240155651030170700d01080748048581b240540301c0d10018074240308500d00803c2c0303141114140190540c031040e4800c941820901c185580d0b14005242040301d42c281a07100d9502c41c0100c0c1d0035030b08850079440352803e100c03d8645031068600c04a02085c0c04e102018482d80c13015044400000655610801c0d80c90603e140d54002e52068a60360740204040c4103a142000145c0d400ac140c60008120102c2c09035140595182e0500c400342c80704002040a1003480070510485070f10010225007000070f8503151030808088104243c0c258000340d08280b558024103031900c2c595028903086401040b81c4101030600f2102c4000040503408680018440304c00542caa990700d080344148500b80240e1680040b1070340c040c0c907212007002e07688182d0034160301c038000d61004180380e110b00000341d50200d00c103014030320254080d01c1005000381991 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 41168448 1250 41167198 41167201
    0xe070c06050c03060103110903120306120f0d030606050a090504180516080709020a020604060b01020a0503030a0501030308070504121121070e060603060105190905060a02010c020609010e0706030506060f03 90
    0xc2c01c0300c0700944c13013850300f40c030204158241000365440c14040e8140c0c0e41c2c0c05a03c025034009908a014000c3e6900c69401488048116040100d036030901c640d880e003e4040e9402000404484d07034040c09000081c0c00289031081c28242d100d000140741810901c01d040c001c5968221851200c148070103070800342c58100048401440d5128031a00c2c441040c0d00c034172440d5008107040810081c01c64001c468099020f607008240544440d00c40c03100600c00b02d01d100b4158820a003134080000e1051000d1442601c801b500000c8562440c100a4021036000307000e4001c100c008c0000707010380b4440d210414040d07a0004001e070103600c400008550910000038103001c44850000d100c98043c4800100d54083c1c1e04900d068407803c0c2c442209021180c0002d0b589275010440c24030620584d0550900b4410501c0c03141d01e401500355544030042025540304145079030050b515040b19030300c03285d0100800c80d04080010000c125050074504843c0c0c03141120b024a40800d0746038004298180d81e0081942c3c2d0040342154011307501e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 41169698 1250 41168448 41168461
    0x106180b0c0d090515070311030409050c1206041104030311150a020705010b0f0a0b030c0405060a200c101107032306070e0303090402030408070c0f0503070801060803040e070c0605 79
    0x540b604544100006160440c0c00b01d12400d0805d01c501075943c82d85902410800d80790340a69200102000307a42d2144024480050701017004c1c0a0640207085844101d9a20280d10408583c2140000c0c0102e010300d0400b410358413030051440c125000c0341d825203000c1c521580050400c074144104e6203200401c08601100348042c00680e82d0041285512640003001a40c64030001d1010791002d13444a60b5029003a54020400d503200340005644c40355103042400d240c00d8480d0002065900b201050000181d40342c000d030014079480003440c203420204140144000c0410300c0004151402138000001008190141092019410001e010107168880240643d680e400404030f0070510000d1820b90355407040801051142c0e0142000480500c0301801a5141040010034000a588081e008440c0d880c0e08005213400f0458100e0428082d0090000041c0790728030300b008062504039180c01c180c0559141c80380c02c20144800100729000c171038030100c00b80c3c1d03141d0300e0310007ea800b4510b00300042d0005007400204003e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 41170948 1250 41169698 41169703
    0x20a08060106030c030b03070b0a0c050111030604062102040c0e091311010507031407020f06030915011d01050f03030708070302030910030207050a170903070602010209040c020105040b0106180b0c 86
    0x60ba1401e030390412004501e40d00450983e00d400191a030581c000a1040c00030f00403581c014500c001c0c1c0c40c1070030165089255990740c2142c40d04a40e83c6901710020060002500e4a4040c801c000c0c1014000d01c01d40e01c49000464210466100009200c0ca6680c04102070f468003d000f81000c480f8000c1c82d006203840c121080002c942c441250441e50003003004407601c0158040d009a82c012030b0150740f40010910078510011081d03100f038400340d0384822070400c1340c1e000d5910400158070401503103000d8060b0134002503444844040680240001c00c003001c070442c10000c07501801c181107034411184401c020001d01c01181c1503101e9408040c00d09640010140c00380740e000801080c01c45426170305034a803480540021002c0307000302100142681c00a0708540c000c90030010380000304840450209140c004100000380c940f24042d032010380540d40220b8041ca251070b00b48114100280070340028010f0746400d581d594162501405000e090040c0120f03c0c610000d208139030b510141a2020011750342d1415800000d9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 41172198 1250 41170948 41170951
    0x306190f0e1006020123151f03050a02090d06020f04030812010e010806010f06110c0a0906082116050c030109061b020a080d0b041404030906090e01121202010207020a0806 75
    0x610400151002035044d00c144902408034850039043e80f0503141c003028032242c13800302900c1d0110400030001c44110f1942c0710002001d0350443c01c5008050014090400360a4a4006000b1441940b041c00b094042d078840c150100889548008010ba4848910004500324080e580000d800c0da20003044c004200704080600b41c1c142c2c1c0180391254456030342e0300c1d0041c0d078890702405482d404a10341541000458003846204030783ca0340d141705a81c1555450408203900c14410341c08100c1039507d44500308008402441007100d5510050307507404c0880c10a103242d810502c42e40c06d0151004224035a035030b05000040c80344400b9032000500911521505042250151901c91152010380c1c3e11009400843e90001410f58400c5900056980c01c210170ba4004000400496801c65000703920f07200e40020400710024203500c03503403003034450903405420100014210001500014420f90b540001481080c1510894081d07441d402604884840c83c100012401fa0161100c000d410031003100740030400c1d180105040b03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 41173448 1250 41172198 41172211
    0x9020307150810081c0c23060f090c010e0414040c150201020910050903120711010e01031e05060a05060f040e0106050c0309060906071a070f030b0901180e120a180302060306190f0e 79
    0x842d403c2c9c6a40350b811150400941d0b422005a01101c03c07244154011003481124407001840000c515000c0805a00d172a0400c030740889405003100b609000503401d201d06030806c3d00c020710003182403884010203c0d030459034030782c00030092040101e101f1078141e40400040d4410101e001c00c0c9500ca507041d10b000d80076035050f0b5206a0219003107085006465129103c4d002601080902810b403114058014100602026007a01e4010240a0003c16543c896030020480505400c6610740e98510303000d0528040281030300080100a820001161005400030650b019910101c8003e55604080b00008415100f01080103010314125901403d00fa6171441103544540343c2a202d010310003808003230442c110755003000031603448030b8010010b120100f800c40c50006441c00c8440300280c0001c04400591a0150600c0409190a00001c0d030211607988048401e4281c400081c80500f901c0c07c6d0390000e460b03400000c20003070060510f014120200e504607041031000b00b09140307031782c2026515540b005004070320841e010b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 41174698 1250 41173448 41173453
    0x150b0a0906050913053102031908031f03021003020a14030907090504150203040b0103140307030806040c031d01020406031103010506030f04050109020307150810081c0c23 75
    0x1a40754064011038890003002000c5841900d1001c000300e0040c407000d4640064041c0c90103000e941c0d5101d421480d110740c2c3c80b01300150780c2c0e5411131040503e41084103490031707840e1000c0c058541c000b50021007034a07000a81c80b201035a0342d0b254040511241e400990001c0d501105010302d0a24064041d8000c14580c80140d950302200400c5000ea500544015a20b220300d641c0311000410021140368401f90b041131140481c240700030382020f1000280d13007054070b0030341c2c851141070010410040c924501d64840d412200145080c400c10743c802410035040248680d00a540303513003031840c0440c031980c00750b501e0244142c11070a0340e030b6141480f28001e40003400748602107490a2194854203d014064a049a0f00180903901d19501c64403542120300f8041c00449956403200c243c0c02c0107076001c0c000000545182c05e40002e4601803018006c202982c00740070082018545c0a06020150004c1030940210340306400785910010f00c1e400032a111160714402411172660b8800803180294800c40703181100000d6401c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 41175948 1250 41174698 41174717
    0x3070206090106080c0402070609020a0b04080f0d0906080405160e0a06080c09040f03140c060a0f020309060402060906070c12061d03120c04090e0a020901080a08091201150b0a 77
    0x71524200d880c00e0090700e01d5603200428010151805800404216108110201e86289640d01107001a045500b080015010108050001c2c01040242032108014200140b4003c101c0c41405480390202303005810400c89050002400d11404000c0c2c2c3c00003e0084803422081959072660404603031044c0e0304140081e040800000386520300003020030300820000c002a04648070ba640f400109100002c04030180510200341800e4510820058414243d0384030180110f8600996841c080314000381d00e03410114410320038040303292000680c007070f4015415079401da07544418500159482c016154010500001c0e01070209501d10241400d0303944a10a03202846880c490011213294240e0b180d910b501705078014004103440100c2c43c0070698001d62044942d618080c0c49035840c2c02a80c012180040c1e10307500c4007031950110b0a25406260040070000c0180c030b2900d8040d80d500032a8460003940c2441419220340660244070207610201900d103042a19044d0241c4c0c2e450580307071541203100c0b03401c0071607a801c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 41177198 1250 41175948 41175961
    0x506030c031f0e0a0c03060c0e0402040305060a05060f04062301050c060c09060d0e0a1a09150406060e0711060703360b010f0504050a0204030201080c07050a050d0503070206 76
    0x140d1001c0704000e02d4006041d5011248060000c15a15511603024400c619030200407800304004074020f10f01410000c104010345100142000343c03c0080d0318001c510400c004c00c04284007040043d0081d00c1ca010200722521040d0028071003045807440654010700c0c1c01c5c40011140440b4084150032048041800001d00310307400103427124012890300a140b81c00c05000240b031250b40000602071700b0b400411050420324103104190894113901043c04296000e202e41800f40700d5583c070b074064404c44800e5205000e00d440300c003c42d112074501c1d45000b04500101d01160412440342c200401071b00030040082c0700b5207031150380184004107070311f03207000b0501810000c1507006100c0c1c0103a806a20064101c3c1d03d0400c01464200c42d4180000601c02200d0300e451507400006290506042c000c010080b0310028403801c203000c00003154006030060481510401c000c00050b604148840d61124040c0405030311078085041c058100380310140d0091082c09800c951000b12a0407101442c0612070940c00c0701c001c1d9031500c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 41178448 1250 41177198 41177203
    0xc0a020f06030c042c1e33010e090a0506150702091605070c09020405030c010206060d020409020a0e010806040c050117060603070e060705010903180b03010b0d0b10030506030c03 78
    0x182d03003101c40c5070010801485003002d04030080170a402441040301132441c0802000d02c0c2610207803210b0003903c6151055000056420303000c10780024813014461003281c40a00c0d12640b111945202c1c05200800383e1041e03aa5a0050740c000320b1800000d0500c4044d890842c010304002d250849119200c1c003004920700c064040083c0a80d00c1d00c640c040c1c6402c090f0303101c2c090f0550610301541c0c0e084003006020841000010540e0118200038010a040541c850f400c1408160604810032032560466104508011060b40c0307150940c64100e40640d00062407500381d0010030505031032a0080a0100002030002661220004820344120b00a40407803072100d40368001110b5065011455440008448000c6241460020f00842e08444a41880305e1644203030030120f55030b9000410181c50304e95542c21058281078100b004070307540301d502c0242560b001d81802903009032804103005152a80002185041652410b544001c50b0030b0801016001c03440c001102c0180500f1088502c54080d00030709414203640e0400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 41179698 1250 41178448 41178451
    0xc050312031b07141009020a080111040b0a14030f01031104050c09041d0703030206040506090c030d030c050906030a050412050a051c0603020a06050c010507050304030c0b060103060b0c0a020f0603 86
    0x840d00e03004601c03a280d0038a80d034036008010281c40024122207802d0744a14100075000e49038010300001b19480299004004c3e2184d895880144564104015a01803070021012a003c1e0307800403049580707890490400b19982030b144200d116003c1070020070300a1002041502c1c40c100c2e0711804100d042200f00d541400309589058803070401c501e00602280340c9a01d89a01301c40c240305410301d1a441d000d042d0b090301340c0c50041d56500070340141c1c00034000e120501005101c200e60200c0403100410306d240700007011030341d14034000503604100742e540c1d85204401d510500c229008944001c02d41a100d04020034060014441074808403145480d4510040c00140210b080d18001e4102c0d440f0503040c240503403140308803d10552192020150354143c08001aa20f030202140980301e20350310280c4606101d828176003100c0780603040300b080c400306004100019a024804e188400e03801110144181c48880040c2c02601003600308002c01000400c210785c0183c2c0005a81d20715a0007114044a1a840581440280d01c170 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 41180948 1250 41179698 41179711
    0x2270a06051807030e070b0a030e0a0b01030314070b150118060e0f0d020607120f0306030f02060c15070f09090603170a1202070606090c0e030601030b0703060308070c05031203 77
    0x29034100700b0303219015800d600c50f4040d01c0303428081070191340030720a1401c1032a240c100028003080410389051445d418400c000c0c035903204038020003002c101134440b0032b41c00302d05100c000c04100e10b02e195081003004081c01e80c1c5c0f64a6011400c4900d0381040220201108140c0c0e80c040c0c00a108a90041d0440d00400b01c4107003141c1c0540c8840741501480c0040c042843c00500c4403a030090102ea15560050325107500034107180e4003c0d107092003c2003190760001c201072034a511820805050503014004668a0002140e04c940e044525559807070301240124240384c01054110307c0404003108001e900f54010340c1903a1110840d0782e6400b84540c40d280c841c011036080c0d0001034020340380d03400745d60040a0200000d0619040f40d00340300080d003e444d4203041c141e900c2590111021500d0392401c11040032140200c0c1c415911604010002c50201e01c0480d589a405100180c8454603140c08220385074041e504c008003440c0c012880503a075030440d080004152155200c4e2500a00c5129460300340001400f007580e003c0c1c00e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 41182198 1250 41180948 41180959
    0x105070f0f0c02030f010c0912080919031202070305121201120204020403080328090809040f06050d03110c0a03030f050703050d0914010501080c0307170a02270a0605 73
    0x200010480d68070300d90104501c2441007103584a405a5800c00460058101d101c00200e1040c41f06800100030808035844208018004c10400001a0107c0d0682d24210419100c2c4607042e00c1511001c81918050750018003260140c618402050707078042802001c0e2030007030046502c1440c00710011901c2d0720464106c0c4100c0c08450700144084c2554882150361140003c2016051a03240d4641050b20f0303000795203803030008055100040884800c007220810385520304008000120054444011a21070340e40039a11444d40c03400c0c41000c03040c8550040c400f034540a802c8800240491030050001026881000240c3c0b048107030078801490400b1020065950694440c2c000c491901010b0b9055040450700300c007804400c1c007071100002414820003203220b008001141c041b112143d4207900b11703041a0440301d8641c000350701072802501d000440008031550094810300380c0b40031054190074140bd0420095000301456200c08034105200c0100100202041e00383c19140c8420103040100d440d10b214054004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 41183448 1250 41182198 41182217
    0x15040f03030c02030f0303090303090706030c0804080702130218010909060f030b0709122003070308030112050c0d0305090a06050a140901030b04060b030709050108090c0409150608010c0e0102010507 87
    0x203446076404490461011341203c0c44020b000454030b007503820480341d0f22990b1b8404400c00032b441008200a1009140301d003010800ea40351810004c1000c0d00041c0054426600029450708544540219440c4030202c0c038401c544840c070844071560920100000e260000e0804d401c081070401503131041d841140c0b4841c03101d0b80c40c1d61543d071f00c801c0c924000600aa0600c4040c041c005031039070b09403406083d901d200d10802c556130242803000032910501081918080d038440001400003921404c12641540c0180c0480c071169002450071519082060011a4012000944100800d80c004005d001c044004640000500e520382404613403e01606000740e0010720904800e040200040c0c008008010040c5400b103140200c48010400366400d582c8140c0c989a40001040390980d403107600d81d80501400d1030031516500b010b01a0b15681c95060030118070075550380311036504000366890307010711200c442141405156a103c446a0080842100c03100100c2c2c031191800030a58410b00c40d403886205507888034100d5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 41184698 1250 41183448 41183453
    0xa080a0b06130507020303010306111204061a0607060515010f0509010302030601111606030b01090302181f0b0a02070b0a08040b060102030d0623031203070e0607060906090215040f03 80
    0x60320009401c15800c020200e6440748203007402d010f00c510075031a5400841e0340303501d10b01c2c004049699072182c4198884c401c0c4240315598000050050300960800d001240e21071808005418202a6000840d0710000010b5500304001d0351b40c110b244640710b10381038050016950401940d0303062042410358000750382001151030640c0030f64040c642100040c035200c04182d01d038a102a04c0e000181c1340126100340c4406040241e9076150140b049114002c2c82c5c080c41061459000c1100c07103450040600d4440062000242c443d5401000c1000790070014901502d03542e6175180458855201281440060158460104a20810030200d070303400c00095840c02d101c1c0c0e0361515681c0d206640501040d04500082094455016141c00f1b2400505003a26542880c0d81c164003110625105070304d103190098010180d1007219458950a0781d0380046582010040d134142800081c03c1d920807490014a46442d28005c48140300059001c0c10f003007071096440710242280c0c0c00c1d0708a02405984120300c01c0c488410401d000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 41185948 1250 41184698 41184713
    0x1c0b0102010c0206010b0c120a030e060603010621060e120417070518060406031709120726070f0f05180603030d020a030b0301050403030c021504030504050d0203100e07140a080a 78
    0x180a100c0c8015188d544000840c070020f1a403110100d1400039840703c4101c0380d002d10234000103403c80d4044001300301040c9072505180c1c4050b4505003c200e1250701c40100340c02c0c070090340c00105c0d840140000b0f6801c442d0100c014503813250013074007440321a04150204800101400124581500c10003000000c1c0042001035491049030f0040c107054000762110380010001304070310741c0786c604061485100c0d0348030340580092002102100100e50020380c0220420805c2014410307401c40002c03803c050b003d01e41c44001003080c4ca003034204d42c800769000400b500000740886d00c001c00001518022100000940d0075107555101003202a076005505820404c07a4500d400942d9004003400701090030007050841948002908403042100c09502180d241c107194446c845d81400045018140d22003202c85030304094400a24a0040d40079580c040c600b10a50072080d55002c00440a81d625070795000c0c05000002e0b035201da11901d4505c90041010107500701c80040d0b14081c7c040c0000c4c0c90400004200f0a940354a8444 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 41187055 1107 41185948 41185957
    0xb01090f05010308070212070803040801021209010b030d1d150309010c0c0308060904080408060a1a0607170708090913030e0901050102060402090612031c0b0102010c0206010b 77
    0x11000034010b1041e2004190180d4080f1f030540c000c400d40306d10780002238001c03401c0ba11001c200060003143c1500103180d0762040c1705980401d41c07100c10f18982640d042c02051581600b02c401a215030610a600c2c8140100100c1a0050b60064803400f04004011030003050560600000421542103001d0055055410451400f105010190b8400600d44100507007654400c4040b180407030180944c50003601c0141c2500001c0d1800307420420185002450340e800d00d02c610301035001c40c0140d589042016075060503000079441143c02030308441500e05920111040b41d00b0340341030003031034007644a17a03040c0c030321031104602e2554541a03c0c0c1009068810b00c2040588140003060050100743d84c042030745a00158199580039a61f1035210025011100c7d00c0e811082c64031007c00c2c200401c64260b2840050900300b4441000303600041300c0124240d640309010400580d1251004101034081c000090 = true := by decide +kernel

theorem cover : BRFrame.Cov 41007198 41187055 := by
  have h0 := BRFrame.cov_init 41007198
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41007198 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 41007198 ≤ n) (h2 : n < 41187055) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
