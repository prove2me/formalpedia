-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4953
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:16:02.749001+00:00
-- url     : https://prove2.me/submissions/36a3d4a0-49e7-49c3-bcbc-d3f734e19e0a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 890647482 ≤ n < 890827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 890648732 1250 890647482 890647487
    0x4020102010e120a17061f030f05180d0f0e2b05030c160501120c031e1a0312070221010504030215061e040216060f06031106040807060f 60
    0x58240c1051450b02c220340c0d000e101d0000301002454031130182d903580040d46100001c4940b2840c015030346950312140341100520403001c00c25010001403583d15000c617801c11082c00060446605031400b5100b406040041210044204a11059041c55190140c584880603000400c2c0004000005110381003a003405080c801c2d10140000c0745810080415581d40d9251600039500d500280052403d03028210700c10301d1003414814810200d51041e100c000c0e80c80c0c4409072290040000d04603400a16030f403601c404102c203a008829241003090342a00249031140c070b907091407100c0352000020388a54440e0486c607541e00e1409003503400a43c0e0540755205103006940720340032050340c0b81c04880400d620b840c0801052582c001600e0f15004459842c1141a03210382d01403110704101c100d54401580e1005101d000181800e41c01056101c5444d05107102d41c000ca5503c04050f500c0e00304c4454036454484c2000d00901600c031103400d070301c1c3c0001c6821516091500c0312040e10b070340281c800c44007840001c0d11044103c90 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 890649982 1250 890648732 890648741
    0x30706051602041103060f01020718050c1b0d032019030603080c0307110f100e040f090309030507141806010c0c080a110301020421080702120618010504120302030402010201 76
    0x107900610901184d01c0c00702166149400480b00a486000004035050320b650021542c05d00f5140c0e1712400403041d815207090b610151201409200c140c0004001c04454039845960f801d418a03d8007015080c10034036600c0003015280101c4c84024203005000302003601804010803100c1e04154140d0820118002010641c02030543c1e9002070200c030400902c80480b020084000c00301c0c1e61090000c60b40c444010f03024000c000d951024010b800245845038044494010310700c06080b040e0051000c5100e40c40d5180d11700130f4405482c011404164000810f100308031082c0300341d0000c0d00d848402011002d61600005100180c02c0114411001c10000406d6490f44a40d04140406420400703851800350740d4961203585071010b1800f6980d0f984140509003441c03806008031400c81d040910540014202c1e0049901c0c1c44030612030486030725104002510058452188229040f201d401c081c000610341000c8450007044015100301199140c6002c0100140141c48203000040704d0340741c01070f22960b0742d04c010707401803 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 890651232 1250 890649982 890650027
    0x1207030602280207060c0219081e060108010c020d1803061a04050618180a05060901050601110114070c1103010f05090c0123031f080a0c060c0203070605 67
    0x70300004042d400710740d0750800455a0b045401036200c55907a4040101d80f642c0d2603000e440d000600c1c0e08185005850f00c031404c0010018201159508640e0350340d0621716088550340c1d40440c40700101003240d20044180302c101d0051500b01c009100f10444264002d4840b9500700032a0203001c0c0007000c00d000d0a200090310000355500540821091640031449009015004000f920a40c00c2c000001d079242051103a80da03100000d9801d068654686010005c1c3d00035120303040b108544101c141c1000420f1007004011f00403001031000207403a007803650004029002a5902d013045a0512050403480410300520b1603000f940c9160051030315500749803030a9400d036100515507046d8240108400300e07440d0b41e40098004c881c2c01c1c04441c114030140c00150f0b4941050700759580110010036018000401000c002c5501c005801d49035078070607000d82e64905c020a0380350002e10456101c00b00c01e20400c141d080c1c00c140589018100b55075000955800a69915401c0c0100c0c0d0401c04040b9403003d02207034250066425 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 890652482 1250 890651232 890651243
    0x815130b180c1204050313080a11030a0b0402120a150902091003120f050c0d090510181703121e280b01031508030702150408060a0203090703171e0a0e120703 69
    0x7e95202c08090b90360742041d0087d901c200d1001180d0140e1f10703001958075005680302d03202d07044e256190340800840384581b501103665809501c641c000014002c044800c507a071020340c40010104005d0051000d1140d005002590246482c1c2c0244041003903629900c542c803c181c5001c40814000701011250f40c09050300314061072140110390756005400c151740805541e000d41f00901da06203011422a005801e00500d0400344124039403c1c0544004801000c02c10301300348003140d1410140d4042840485422610719030f07504a1450000300c40b45035400c03059044140c030441403000a41e050816403400c150500098016681d0701d1402000b64026001440d1007280ca00b405c0b2101e03651001082c1e102c1d4011070003244100d03130030143d0465100101064500b5206000000c2c84203039100412040290703c090b200c000c0c180700704030002001408008240c4c42400b0340c2e66440b5200c460070505a41132a0881c1a2031409180078402940c6c4640d004048141007030301164121034034844c1030b8400e0b042a0190704090305 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 890653732 1250 890652482 890652517
    0x110102010b090a0f47060d11160803070905090601121d0102210c040b030106120e010c030222060206060d0309170303011a03010311010815130b180c12040503 69
    0xc00003840c07280ca40b048041700389035a62803c0c0948504820482c40c2c14070640c060014010341d000103655606c46040202801409442d00c22410b45404c18500b01050441d020000081003041e95580600703480001d150589081c041c0c1e0074003000103000090a0428078500c40da071100d04145024108560660a0005070700865480b0000c8001485000312209030264942d10580824087d0302500110340445080c250031600350307401c00302c040b80c0e19921a450700112503220714894035455028032880c5a00d09080e2070060740d8034044040d00f9506000340b0807002c0e0007a5115000c0010640208445620090841e1040c0c003855407890180d8406d505a004051016079100c000045244004010350507200c6c0445240000402640042031910090100500400103001c0c0795025502541210b42c1140c08008403050195002c80450b41d441c0703000e07480d80d640329110380e801341d45030900101d00d4045080302d0304941414034105041d41d9141c403900d018066030701c000398002800d000d4203105aa004100e0001d8a80 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 890654982 1250 890653732 890653781
    0x308120c0904110307180302093c0402090109140c0f0d050a090318060e060f090d05060109050105121504030e0d0b0f010b030f2a070609110102010b090a0f 68
    0x40184c200b12105000700d00081051a60442000304e04001c41e42c0c010205640c6545031700c5011801e01000428800a82d40b5580190b841d1100c21001200108480842000d9241600401080f00d2040e800b12440780d28049030034280c1035000240e0755101481c2c580c1d5560754180d928565000c3e11800864000c06890030062001808082d080204081d00a0355103a100411007040001c4955403131048201140419419014031b0034500041c004d08007110020a08260b04180422144030076640111403a8001e41c0060020305c03001c1c80707000c0c0984016600002d1110b1100d900d682d944251810140313114120710001000c2512550345d040b65400c01903c20361040c100ca00c0c00c0700a102066079600640340e00c03d0004100d2018280c15644035880c18a03609416403500d00354130b4010b10400c4545494124a501c020350340c0c2e914100141850f80c410100010061420f0038002e403c814050401c50440e41452004a9203540b000c09680e000448c81030000356940d403400d1a10b00425040000e00d82e69510b203003012 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 890656232 1250 890654982 890655011
    0x1b0609020307060203030c040603110f03011502011a130504080c01020a050403060e19020d0c08011d1501050a06110109050a0f03020118021005070302073b010308120c0904 75
    0x11206510030380840c0c82c0c00d610303030800741d859020407140c0303441c0984140010444c13684241c0040d84c400142d00c12861401e0719203412040c180c1c0c0309030007507115204092100301c020b580c24400d00100340c80c03605100e09132501000029072805030072040350030b02d642c88102140c14460b141c0c04440c684081500210b42d01d100110028040e5046848159441403814101d8000510041042042c120800030222400718280e402c1020a8180303000917030300c4000d03440c00450108800d01c200c140904218201c000c00d207811014485c80c02c840c5e5070b0120b010006040041140d516140c5140702a00c02c031303050000364010700106907401013203034141c05401c030303c41c4168950500013014500d800781400b80d4000c0c08020282c4440c02c0b80b00c02403610094001c070034903180900c0f1500c00e01c0900035040c440e00c1a5081c280d5520000800c03600055819400f1012a0075500d103142c1150f8000341e4003882c10f4240c01c05540c50740c2c41f1016240a034202d1041c94020302000107220150010031500c0565004004011000da101e03900c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 890657482 1250 890656232 890656241
    0x4090303150b03010518040602091e190f121b03150b040b10120644070b07080f16060c021f090302070b0d050406050c0c030702090402011b06 62
    0x5445022071000030124001000b00100c90686102610441c01d00801a005030000309000708103a4040d136080c4055600781d42c5007a0101c10908000700040c1c9605450400c11210007003412423204409500d607010044814200d403000c08640160404001c050001d0809100d0031600c0701c06400c3c5299442c030b01000700b15243c0b0344000400ca02c038038100b0440e0300c03250600c01200c01d1600c0442c0e0001c0c00c2c004801c40f19215001001941d0200200032a03415a01c1c03e12005a46070042203a5507204ca204560040040f2051208503442550740380d4048560300c03502550b1543d445005801c0f12000c00141d0f14103102144003218500d609074104d099403184959003a0004103040d55088403064148140d00c503460344002544e20201c000035604e0003ca14002d088800180b018450840035401055800500c243c0303440702803e44c100455130301094604e030500e010310448000070718243c00f032101030116407015a40002a299000d0381500c803801103844c0c1740016900a000000403560360040210b0100c20051940c12 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 890658732 1250 890657482 890657501
    0x13030f0c03152a08041704051203031f150e180106030207051c02030a030209360901050411270a06030501061a091915030209091b041701060504090303 66
    0x6440f402102902e4a6100f0810320050b07100050720000104000c1020700c042e50801040c02d691507031070550746501051604c1105000500540c00c007008100154003001245c040c40b01c9420523070340c0000d007000704e9403403500d081038100400c0080e20300d00664141c80e0382007001d182020400741030540d5039540394000c0103135204840881c2e40d40070344d103a941c14001a64825a01152554016505110340940300310000e4000d00b9015910104801342d07803050111000b02d224404407102e0741c0d40504815000301000d40540030780f05800503071401c0104801310b19210100c0410071021107801c50090030788502000590840400b100150480e5070500481e500d544d4000002c89110344000c0c05070542d207600c002080c84d46025401d4400c40200207000580c5049034221852030794020840f8141c544a100e2001909003d54602c00400e5002801118a1404a0310070b6401316074906042c8440201548403403590044e8866a1900d158005141c00508001c3d003101c00545805801045022020300b0003c0141c0344450 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 890659982 1250 890658732 890658761
    0x1090c0519030803061315120b0f010605030a0b03160f0602120315010c020a0306050a05010518090a12091a07032c090c2b0b0613030f0c0315 62
    0x101100440254040c6022070f03401211030f6046548041c1800590444500000100da6465140421500c0396102d420050600a02c0c041d5290040d403401034000040500f070000c420710030780010028142d10104480e801420050045103078848000841d00d0108103c2c003220b0790744030200c400305250a03000b95100460341035a084900112030103014042d10f100607034034510215050700c10900254014044900401e1010308060034541c3d5980307403402220801c3d5080e00103680c80350010485850030702118101c0c44081038051205040545410b0740c0e80602c083d00400032501c02c0d0049000c58000e0b40114000c1000c0d144540211320380c0b4442601a5008800460204240046483c0000345603c0c4980c18440305851070048000c405040203c000c600a01084c205102080712a040410a043c0682c81070f264514000c40300942e9148182540c1d072000009020302c1d428000000c80b02d0202d88030604172504100e01002807582c41c01e100c46207100c075810242000318105a042807011481e8014119600940c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 890661232 1250 890659982 890659999
    0x213140a091e0f050f010f0c0e0306061e031e070948020d0305150d02060f041a1e0f0a1b021507060f020408030714010e01090c05 57
    0x404000e0071185541d030007a04041c0340129284068402008030b0010034015500749200c0000740e50350518110710203448483c1a512501c10f508072412a008009400440341007513040200303a0004240d507041e005150501c102d4a518080c0444d442807549091a80c001074151541e007000c240005411062420700c3c44a07502c03e00000082c1d01885100d500740403018811100480f4140d0110700d071446a861441d242100001110305c1d00708114940da100c60440550040c099003054100e0103422900d004080d5845c032100d0020010740c56885418501c0201d80c1100d440f42c407000c0318484014140282d40249404200158440c0c5581e50080c0180400c103040300222880352038507490203881030050358a4682da0000600c14070b803049000ea03602c0001c0503502c02d0210710b0100c0c5900050950f600c050000c40d007212001594406001090244a00c841c00d141001e41c40c05240c036030000d0b40e1b132051510240c4004070f0001c001d1603d502c21340042000c405107e000340311401c0c041c140302c081841984126403060900 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 890662482 1250 890661232 890661241
    0x31206060c0318030b040813050d030c03081605090402070c03060906020408060a09050c040509011808130801020c07050609031011090f0102061611030f0309030301151404030609020607021314 84
    0x84000c0c01540d0740005c810000751541c0c1d40310011500408000320b4059005003001c903a40e00e9440c0c0c40b01255019507074007a00b65040303040c06449a4006484020301d079411071040401e543d0024110360780b2030403d4030b00503911001c17400c04142840303c40d04000c2009040408503400e10150350040c0040e0791901094881c0f94556980760002c4558844009000740c0010000f040c0300d1609900c1300364411035a00010481200b240c1040380c0d03003080c14608940441c0c02080c0321808902d09810701000d050352000031072030201e4540e4a2030f41e0300190700c01d8910a9a000032201203588042c00a008034902441080c040c09405240526054000d01141400b54880c44040c54a40d071000a44901030307201e0020070781421051460480302050070b02101543d0348030801a182ca4076000000640c070410380780d03000c0c40e01c0b54103002115108049202d413040c200840981c100040b0f03044441110b00300c030f038003202c0010f444000d0302c041000c0e4020b00708040d40c403808048240454080d20f802c0304580c1202c100b0410b420743c3d103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 890663732 1250 890662482 890662517
    0x6010302191706071e02100b0406150815010314060d030e030a060902130501120f170a02060103110909060c0a0210091a01091505040e0c04091b0807031707031206060c03 74
    0x103211102170050744421261040d511082d803200c0240040900003085044d00c0f00c400c3d40b010451183c130305002556a20420400c0c0700b6104401551040920b001c0c0001800c50a1001c122040600900e1060150044031400c00d405604504030038880901924114201402c0c0310004007105c84003a805034500180003540c20b0858441d15040e11010741c10301e0055204d580320100115100300045902c9200501004910380c51180544034106040e40142032543c10b514000e86418200240c16014101942c14488141004205a5844a40110a01d48a41007060120724020400e46a25142ca203880c5080742407200340c4101804a014407071038500141d0741d0b032002d002120829806100d006001030360612003072810b070b0007051841c0e1b0190300b120300c0849800b000038120380d000c5404664501e80080d540c1012408000d40f14028600c1c84003030025030380343d519050454011801d550948100000358141050b0060036014483c0750701c1c010810401d0740f1000302030700c5051401d1042d404250f140058128004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 890664982 1250 890663732 890663777
    0x513060305101203020c0303030c0d1a1026010608090f0f100c05040b040f180207051518010606120e010902150a051c0501090507110601030219170607 66
    0x3007004004020742e26011a42d05003890b0302101324114043d0781d4294280d540c080010310300a049500481c1c0e0b586007c0c129800884074200701c86040d42c28040d81900090f0f42d0f0141c008800095805d10100c104144081a03040b61030066180d829018180c0000ca01a81c0c464a0329115207510003c5401155081800f660f5921282403034901c030390701415401c140d0340c81da600400d950411a050840c203140d15200d52a54a070003541084083c2280c0010401803208400c0d14409810500390302145401500d484140d1640285500031401440a40c0403a80340c0000c4400782d56105102c0780200940342c0c849400805036000504601c500f20f04107408450070317110622510030519802021603210501700e08140700d458100607030311802d10506002d0990480440031080028a00c1c00400042c42d42c1004810301c12140054082c6c2c00b0803000c1410210034a2000035030f18152a0125103c0c00c1e8181c5900388085803100680216407400000780600c615130b0300004400780201c0700340d1203040964004850051082 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 890666232 1250 890664982 890664991
    0x10212012403020d0209030303130204110f0313081605070303080601170f06010e0d080a0221120a020f040f05120d120e0709020a021e01060f14060d0c0513060305 71
    0x5000e401074403003080c040d0f0b00420032110340b07603405030800300e80000107800c5030011200c1010111420b007160b01146401e00c504100d42e40a0060242004120014084240001000084140c0d855006442481028400d503860648171a805900d082c900c0d160807929010a41310440100e10303d8000300b949903014030384211b01a100c60000d00b9407a914225007180a4002904903030503c01c2c40002302007591100d40c021034441d030003a401c0a03034401407100c000b85000c00c1d811010105030324840c810001c501000d42203842e8045d620b40414031039111039036083d0083c8648034045d03080c0100090f0010b07000c0220520030302107440487d14802034080d0b000c107064a858228580303400203416103011140c56441a400151408034140c121030f074080c2c9580344042241c0c001010384d80564040c0910b030ba0b0147c401d2480f1354050020704000c0c0405450403840115010040c013903190302d00d518001142036504c4580a90383c41d5003030840c0a100080d20590058005d9202d81030f41c0d001c0e03488540300821702030702902866014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 890667482 1250 890666232 890666279
    0x34051c1a0105062203080a09030b0a0c09030201080603070e150102010b040b0f1903120e0f010f141e07060519090b0103110607061505040f0b060f0903030f0a0201021201 74
    0x100b110340c0100ca1200e0407035603d44c085503000780401101059444000d441501c05a4840c001d10300d0550400d1080ea60005100740410b41c1000c0f07468441941c002c108004481e030a0924030100d0300c40c400042d0400c0081d40007070614802c90400c02900518400003030400aa0030703002041550760880901c4251102d01d03030b00c150440018002d1841c541085441c040c3c0c074260f180001781c072850b243d070341d994540c0c801c500001001450964a5503982d02d03100b0100715004a09092200d104061001c014200c800e80e541c103480c500c080403d2b088020100c0c40c0b1200d0722170a141c00c0c055030b031340c1c11840d08000170201074820903e51245648804643d4106200785415075070080750408c203a03840e59031942120910425402c0d0070200501084000131864000c0d0b5898690000d11514564101800d210803220406440181903003413002c90021502c2d018102c3c1d903100e800030003241c0d95a8001010078a5031141ca1410080d4800014241007070350307410740c0070303040c512042c07004a81c03142d0766040d0741140c0b60380340304042d500e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 890668732 1250 890667482 890667487
    0x30e01140c27180c120a05062b060c020a02060403150c0c0503071212020a0c0b0901200d020403080705070501120b2d031509010e34051c1a010506 64
    0x3031040d0b0b09565140d00c0001202d9482c170300101d10284440c402d01c03c1c0c0f24011015221014820f5503c6d00400700c04500c80c00b120607414550215a0300c0c0155207546102600315a176800e00c6600b8039100740090000c180e00a0308c05e43da0b5903943d103400b0850b940200141036010789400c1130030b8485031107180300c40d85450704440290300304413460b100c48060000c50042d050910070b074245d140d090541c4a00150980605580300c444c261030303050030148001030780200005000e9151400c000c980031210120800c0c42e20960101680f0f40510090740300091003141c00140444034042684c42c108036000074071606484082e81c0750b0719810500e00f10a020344400700e0100d6448020280c8910401ca031190300309000340000d10624a0000444000c0f80c02c00c5110500260100c0d0079201f00700c0b11010034041c080c0f584610300020103515a030210114452036582c1c802c40c1450849060210070b2608809044001d814007c1150b0402c00c440b0300c01d0742500468690868038a1070302d18501c1c81604500c18010304070b0300040d0000f072 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 890669982 1250 890668732 890668759
    0x8090f190602031e0a0902010e030d0207060309021212030703180c030605060f04020a050a140a02060c030925061206032d0b0903030711070312030e01140c27 69
    0x180d0030081284003d944d40030149011400002d54950150811050004405d0782500005003881c1380402941c1c040d91142c121f5028640d80014070008540145c5000600c403042840050301c044100c12900001d881030b040d0707030a0700004180045000b000991020842c2d42116400c1032403904155074003500c40382e050740c070400210742c41c0d401069000400a00c1400404002000a4200d8014011500000d03001003005280d480d08107034408074501c81e11040e1810301c510004001d50340c000003428140340301c0c40400480c8200c0d13405c0013071320803e403040000c1c984c0e0030750b19001d44185016548039942c00220351100c40c61004c1c20b64803440e81a039810001100c012800309080c0c405510f1510194100c40003440e000601041c687d0000c0e900900144001c0c43d520700b00550001c0c15402440d40c003d145801c042020030010f002000101380c01102400d000c103071141243c480500508281022900e19204242006240010100100504d2100b0000440f10f42045001580c885201b003040c9508040c0c46076028 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 890671232 1250 890669982 890669993
    0x21030509010201020c010e030904060501090b0301210c150906050304050c090606120f06040b0a0b0a031a03190516080a080903030f0a030b044a0d08090f19 68
    0x2009103400600001d0b280c2a8405200d40c04c45a5201000b4040d42000c20a111286002c0c0100401031009282001841c2d08140000a4501c410311641105034190320740c4c00304030324951120003035194008410362070880da2100d6000d2440d05804265000a03002080800c13400c0c0a4001e49008a0b00103008000380442d441c1480108a000f820b8240e1014083c0445000c18125400c42d61260921015122450500400b440f00f940c81c00c503103032440740b501c101003404a1601074068800301310480c9000300312000c40725210f082d00850308440d243c040c002e001c00714600d98040d41180b400036101c1c00465200c45d500b100c401c1403445950096240e2074000c81c2c5981d02040320703200603214805004003564a440244400178100d6484481010f0111303407189804001031506100e0b2a0921540d000c0c2501c2486426801c1c86541c1a004502c0568840d42001020a411221003000949960004030340007001a03680207000460204e41840180c070400709500840500070800d1014401210f030903198101059a070b1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 890672482 1250 890671232 890671237
    0x6180c090705130320030d080f06060403290f060d0206091201020301172401030311010e01050117070f030201090e0c160c0501230405040911030610050a210305 70
    0x71402040824400707111000c4444009100031482295014030311040c141c1c1a800349010742e0038451094100006840026400207012030784003404500019803030740c441c00055000d0007190405884015101c3c403081003812460340014011442c0b005840340f07942c1d900301c81c1e10410411102c00e500010754000b10001414188003030104903200811800d5200002030011342241c1003680803d00545001031441d40744032041c0000111000c03600800d1910f0008100000e040c4e40c030622005007001418001c103070351040b082d44100140c1e00d0500c028070280d650b0700e280321007003046500380400b079009000b000606c0c50740d04583e0004403a41a10f1b0360007154a0900030000c0c0a100a10886084204103d1840300900f90502020b400744105040701d000ca040100042600303100e011500300301841000e0801024000e00c0540d411190129004103488040d03240030440c1d03100d80c04485405220b9002403190391403900002c40181c52065800020284e500c020000540c1100d0540746140060400c034000464441c500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 890673732 1250 890672482 890672491
    0x30907120c051e0f010302070f05150601081003030906080717070e01090506090d23010e0d11030306012c130209150f07061505100903060f09051207110a0e01060206180c09 75
    0x8049c1d504a80740d848071406c1001d00c80d80080c400110404026041d80c100c601070740c2240d02021040b81807030860390050034180341c0e4041c0c01c00b800180d400080c00d00b031258421804030304040b0b80051440c240003001402d102c130043c0426011031041000891541089420346101840080036102d034003210380c5641c0e03400400300c86c40c1d81400c4080c441800041600740110490520340c0001004000c40100d40141001e428050715005074108201388002aa0300c1600b118181c12501e04c00008000c5801007980303261004040d07250098070103510303555003800310750203004060000c1c0eaa64031403848001500f0a01c0c8a0461000c652010a003c0c25012810340d907c29141041260222004281c841c4001000030004000315400110000414004c00000740241918610688002c0c032040d10300e507580c03d450f000740d6081c644480f90b003c5204000e1007440c0410001d802805044503407003903212140c408070070200b4010b8601510a990100d44c405d100c180c0d1514a044d0000c3c050500b22101c07108001412101a1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 890674982 1250 890673732 890673743
    0x4031a24032d0a03020f19050d0e032806110405010807030209030c04020d02031806010501050405150f0a09060f0c020d020d03030609020a05070201031401080d05030907120c051e0f01030207 83
    0xa5035205590b41040780d15003060194000b4009001111409490004c07103240c0075660300d0315100000000741002414600c0c01c0741034108104880c0d81140402d1030420f51401000715405c1c02c868107000104001d15041c5003d00603142808a0414894030100398801e0344620360001d8103110008480c10300c0396014040810005040d941c0f1004003a00040a0340c1044d01000b8110303034000309101001400401c0003010780c1501002e0801076250800103080742c0254882d460283c1094441c06107044100811900d0580c1034540507601d80d480d0700b400410000070340c026240880c034103c100c2958180240e0b2040078072030b402001c00300245042c1e0309012440c402c100b411028591211f00200f007252950015165000542e41c0712502c03400c0c0c500004040d0307050766404014964a110044c002e40b400030490400d464114201150f40740c5883e180305241981c964001c841c061a01301c2e41204014000700c0503011158100c4d00800c104480c0ba01c94501c45c41d000712820740c02000303001d0304030140d400717134029014032806007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 890676232 1250 890674982 890675053
    0x11e020712050a0c0b030a15080c100504171f200901050d0501170c01051804090309150201020d060e1611010f0f05060103053904031a2403 61
    0x40c0e079800ca00707000d585c000c1c03c035409010080020140701445940888819510607600300f62400189036180e5401d0041e59010b4540c28400c25101703070040049a004141810341075000c4451040d0b07154440c52110582c0c81d02540134894034841c00f5260051204009503401030a08030700c1d0800c0c100c0c440c0d9001401c0503052001c207020f1306221035a0b038402c0ca4000c045001800310700c400c07213009442c14082480301080c1800400c0c000c064591070a14411030104a085c0c0300020500440d04050310010305a074090f401c0035140b0070048486641c10b401070009401e00082c03d0202036180d80054410400844014881d4000900d24540c994420400701985e209188000100903404103001c20544216038111031205484d90140103040d6850b204859020441d40f00c2c421001002223411031a41940c2078408a060683c04540c0c008020908220b40045a0069816601120544080684010441c2d400b0008400f41c1d01d00b4001042c50b1018050601c4000c0141c186003040244451607401211081048103400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 890677482 1250 890676232 890676253
    0x901023c13081b01020d0309031407210309020a090605061c0b060412110a1206200d0e01200a1b05031b01050601140706050915100302011e02071205 65
    0x6114000f0082d03500d200c511064541c440000e40b070800d00750540303410545080409408241d0050201c910341008110040daa045241025184440840074030044c22030302c4200918500e4050303001031081482602e160300b0450307985a0f048115501d80c81400d4000f80b080044001406540c030310598005074468001a1040444000c51541c1c0c001da088281d82c5c0c000b03844c0ea20b003400001800c00042c40c10440b0a0400941002d00744059410310103402041e0310348861400320541e9a0365075118a0464034012191500c1d0b403071088034080e140c001d0b100c1c82c142d441d00500d2440b11090b000d04803004503010341031515207540c1040444840d108044024154141a4000b00c001361044c402000c802170b80400381d101001c400d01119007140e1018040394140001012401580c0c10000207032454590007800025807070741c0b08512203080007100988280304189580c01c20004444c5040c0b880f041d40d001780d07240b425001c100380b100503900c083d03000c880c005a032050320100320315a1404601e07480d90340f181042d602059031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 890678732 1250 890677482 890677499
    0x30b0f070c05120d060b0f042603030408030109050604050403140a03061d18030711010f0c061407120504020a1406160c05100e1e04090b0901023c13 65
    0x101181081c00303042c400240c6500c10100c1d4042c14000d405160386c003e00d008010340040c846403045128500d1001030100704485106c9030030075000c0382d1950f502c1c140c9550303160034134100803190310901680e11003a01d032501003202800c0c03500c00d03103200ea039050312680d610395882181415150011104581050f45861012540c010301a1450360b08005890f0a940607081110b440094501d49048415456106000b198045002d804454000c51000c0c00c042141d4104c001045603501ca040d2030203404c3e1030402d80c000611400c80c2c28124403400c52652606550203448191400b9900d0903103020307510190002040c09240040303612810103903c02803055140c20f40d44220782c40384c85034004003070ba14040d240904000b9401e00b0307442500f1030560381c505501291b416800144483c3c403100c070032444024801d110034501ea01c0380d40c80000b4054000c40361408174075050600c13501035440117121030341d41032480029070403140088504903000da01591118201c0d20702c0e10700d804001c0d003103000b082418140341c0800280d00074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 890679982 1250 890678732 890678743
    0x3060f18090c0108070c032a0f031e05030a0b121603020f100203270d05060103050106050108011d19091407060f020309220221010503010501030b0f070c05 68
    0x25540390010451400c1202141060320050205062240032000c01c40020341c4010030404060707040c107180c15529078076200505182810708040030010041d600810501810011000c0114440c0e611403120b010480d00e4007164003200ca2504000c04d0040c000304901e07001e80d81050040040c00761085802a03008500b45107090203201c0c0b881c41202016200307109608141030b55280b26a002d4402113a2100d0701d207002076403407040c0301651081000b01c406224480500c80014240c1c440000d0101e0600407503800c0984c0c6400e4203202c119403079807038404001015409800700714101c512041004102064508100380113940013030008074130700081d02040c0019001da1041041d124051301b04081582c4040600b0752420700c3d03681000080c400580c8166202d00c0d0700000312400110186d86080b0862901c0350320786405582c102030048860300100d0701640003010046020100d4104107010b00c0240d80e10001d00d030886a0a01024080c0d07407400d0b0020300348058003070345940c1162081c5803030b0344414400d854890818 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 890681232 1250 890679982 890680009
    0x60506070f02040b100c050f1906050414030418050609040309030803040302120304080a020f0f0304120c0e07023a051c14071101140402090606070515180d1403060f 72
    0x146c5901070302e03410303c402080701098100c280401403401c42c00b611151f1802051783c6070b00402c40c1e911600000d00308800b004076941180008411242c6841d1541061440601c0d2a5640640103180c08002440d61400c0e0000341c2c0141e0300741d11840603150441d120410a50300085c42502948240030003e045502c554008520990103041000c4d1a50305054000707003440e0a0300ea000307085a001c1b0268001207040441100d040b2a07000c0306024210009142240191420b40c2c000200e54482200f000090ba402050f95030701c06440d810445084a43d01d4006801085101e100f0b9007a10000d42c00001040e0140d402440c2d50502c406144140c81d07101c0690078181c80764001c40c041d41200d1102880005500201c1c0c40c82d0503003840009214865038210140c16034180140040c0c8540014804681e054580f242124501070304801564840c941600c0420048a01516100310440e00d50038130844040307010070000443c0c1400d41e81d1540074001002060129000900789030f03845403400d4292400341d03568590a50300b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 890682482 1250 890681232 890681237
    0x3102c150c07150c2f0105090102090315100902030a182d150b010507020303071a1608180c1002160f030f0b070512070804050d03060506070f02040b10 66
    0x1104030620300070481d410403842c41d0f20000e007841c0228044940080c0c0900443c3c0255039080592400c8810054002c01c0c1c0d4407541031154030b00400c2c44041c0790190024921090706504985040741800c58200c4a11011070b0341c030350400000d82c001e0103c035407541c000316004250082c002c10310141c4142d17070714050b40100030211400d4403500c841d10500c862141c12000651183c0b03460030410419904d84a141030459000b01d011071750358905032086a8002d8080e18000d94014080365211146840c25090f14440d040d8002100d0070702a00007081001c602680441410103955072644540744c90030540c0b84980c1d005421010f600400014007001d840700a40c80d42643d4007a07006006075400c5191403002184960070105014844002c188081132080b01c054007040d6011109440c03654a0420455650207000b23108680c0702d4001046c00510361f4405092030040b4001c0c0e007606c0000c80e52103002c0e81110003520450380c00140130f000c48400301e4100003a45038103a00103400031030081c031801c0000b40ca900500350140e01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 890683732 1250 890682482 890682487
    0x181e090c09013c05040b070803100905090607140f09040b0d080a090519080c091905180c01090515130b0c0f1c0c020904050102070b07080603102c150c 66
    0x7241c0f500a10000300c807600c0381402403901d42001002c165510031200081e01e02440000070580c1601c0c41000d24006003200d2004010504290070400c1d1920010342d104000140070b003084801d10030502e012075201000c5030030a14903125010341440090034684010a5200300e05200010114181c0c030018a030f0b05105035203204040382003608100d0070707802001c0ac0b04401d4500c000c06104900340005c1c40c0d00281021503440f200c650316940c11a01e10716120307a1000109080809104a060700e45008440c0204440c00382c078003010600740112001720b128414503074441300301c40c00c1e00643e10600008000c00c50084c242c2c1d400d80c90f10b81041145540c055100580b059003c1d110440801809100380c0d044d02c820010f050842100300c4200611103100118081e01c542041004101008001d60481c2d030016442186002585070400010f02030503001c403142c41c020b0240020410203203a4034071421103100c220018400d900d2402c0d2040c0c034002d0100c51614a040d106041c8440580010840c031180320340e448c00b0342940e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 890684982 1250 890683732 890683817
    0x306070801060f02150c03091606023301230909061e0405030d0b0105072f0a060c080309030c0609060105102c15181e090c0901 56
    0x43c940c60071000d84008641140c0e06880031080c0c0c0507401600410300d1221aa100d84448101034180640380400003001c4000c400c000030039903001305801c00c151440c0e0400c641c140400000c1101e902d0805030020884442c0c210040c0007410081210001d500002c0da03202d0f0f0420b00c1100402c2c11040141e0b20b60b10140d01c49000c01c442001b152072081000d10340e540704401103007480c0d6a138540ea80138181842400e15181d0311004016486041070703601007a00440101110445500911502414034040b40c5a0203181002c0d09440e00b04030078400d08484072941c5622104040d0f8840b42d203240c101900c0b0b01e0160204000030000803504200c081d00400e100c20181000d54074000401c00c1c100814080c0c00b00f400743c00c200c2c448010f01e280181448440700080c10004c82034280380050303041c40341c40340c412070014030210b05d01c580c070a1341e88800120709000303481c203903000e19511034803e450802d801c0b042d562041c0f4140008001030910000303041e0118040c141500c0310b03043e104400d038400c0030340290343c018486a03401d5003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 890686232 1250 890684982 890684987
    0xf051f050a06151d01170412230f0912010207050f0d09030b0f0406090b090a111f0c060b060d02071101031a01030218091f060305101202010509030607080106 69
    0x100405880d83c450428030366910010b8901c1d40060300c8440010707541030b112442d60f40106042d40011285c0d82d00c1c84460702d0546003160b41900140c15a200103110754441d42200704e124200140c032058011802070420010407540c414690008420682014069801048900090014040b5148544042c0c0058071900503460302d0040007415400411601c41000c001103420b03085890341000300b107141085a641e40c2c0c10314201174410282d00402042100301000784810780881d08184035440b8242c04c1d01e14807a09020000341103180280801e40e5011030402c246140d00a20006150501c9114041800003c44000440c0c80d0000c00c0c100b44038940020708101041650300140b88007990908081005003000e01c407000d8103200b0700120506140d40000c40c600e68401301d04040c420036100a004003843d107001c6003a0061900b048550340610074130580e0218a041c008d000b4a44180e000c3d890301c903511483c3c64180c0c01c0201c031013001039040c05400c10000c446600e080c0105442a9210341710b05c0982e503d0304000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 890687482 1250 890686232 890686241
    0x2130f060212031608060d0f0308150a080316140111070618050c09060301060f0b1e0a1d0d0501090311100e1b011e0305100504020304020d0f051f050a 66
    0x110b0104020410007200000011684400001034600102103903100d00c0401c410001000740604030101c0c100c000b03000c25070300098a6100b00071002c040e007084120201403288000507030040010700c0d041440b802484c02c5082079981c42050181c080c501d500c01c0c400041600315046d002c440014100001010024090705001c2c80c0341e0780005074944128841d00da00c9141e1140084410789110743c80f00d9021943d140c0d425042038018015074413004000d40e0f0784040420302603000003c1c45800c0003101c03240345c4200f0070350400e0f1a9040059164408030f1008a101c13120101200300c000e82d8411b580d41c502c5000b25000b4420300440b14840d403a86003040320904007003440c0c070a11221400c48d190402c91040710381a00400c101d240ea50410343d40b1007486000c280162081d52245503d420554021078072100b010360300d900010300840714030a0010001c0d8840043c13009038402160f01941090041340020000791070005000b14060050040c0c40e09a0a000c40544c0062002300d21000000d40b41e50a10006200d135106 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 890688732 1250 890687482 890687503
    0xf1209110a0f06140f0a0311091207031e020d0308040f1e02010201060509070c0f0c03050d020a140d2c0a15020105090307020a0e10090c091d010f0b0a0302130f0602 72
    0x80050a10106800b049170500c1010489010142c50751102e50305458481d068800254005202c101980d0014102c95500c41040c030050702d01c40f41e0200b5089450254582030078560703401808020100480d82c0b01901d00380c20140c0100d03580c00302006000d02046031140e0300040000c24401e0b0360480f02d190300009003903407000e8012a200c2c01ca0728091090302a080036000360842e40c000e410300c0600485041c2602c82002c5503001a083d8081d4890611381280c0c0840d03000803051203848140c030440340715030146030f03500364100702c180c0415040b85e030641c0d8008410301c804e10058110320a240c0ca401002000c110a000c4684c42107981100304495080040e070280100d5034040c1290000318105080340d000600e03202e00c1403090319507408044001c15804808803846501404580500b801325140e4060001e143c103185205800580101155001096a0307041c07209040b2317060041d16200c0181406083c401591081803031000f13142c3c0c2040706101c880400c600b80c80041c040203100206103407a20a010307081802074407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 890689982 1250 890688732 890688767
    0x2030a061e0609090b01050405040f02091507050c121603051606140702041509150f090c080604020c071e08010605012a02010333060f1209110a0f06 65
    0x10051100703d52064a110803102e1940000c11042d0101d00180c41511654004a070014208290b1100c03481241d001000205415908106006880b1101444070700a40c0030040c89901301742c2c0b0701002850044031b9091212004800c2d6188111000b0213074100c0e001d1a40200c41d0303500310031600907a9248042040000b40705c94144106a020301e01c0c00140e4900c6642c600a120703070341e82c0c031104948100b09190039001e0040d034942000031035003d8071981880007082c4524828012051000300d4103800034041d0703540c258855183c4c0001d5454010410001c3e40002429000b070f84658140003030030864942c0c092516080803504410141d0801400c0f500b5550305802035414000c03000300a85100c043c0c00d600b03400501c1c1c0c03207403240c11608180c4012005404007120400d424400c0d0059690841400888144c100d0f82040009140307035590001551610074058a0700c02103503180c12450f00f006110782001d000c0310310aa203141c1c02022402c001480c84046500241400005120300b403002e503420940c0901c510b822035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 890691232 1250 890689982 890690039
    0x603040303141e15010207120f050304060207050f06040e06041d011a09130c030b0405150103030f030e060705181c0b011707180b03120a0509011b0807030f110102030a06 74
    0xb80083e503240003034440e414205840d0010441408800c042c0c00b27002660040a90390380755502d8600079641c20244c00b92a104468281d000503552501030120350031500e40300301500e4140e4841c02080000c2c610030320f845488030940300042051003020711400c0f4a1205c9d0f060a40c12a18104040c444040c000803c081481d02d09440f01101086d0004801c5040740d42c40310a21a9560b0385141081c1455420f444100305100d046001104140d0040034a1400104942d8108611040343c0d42665075100c0c103a44a0002c18820880c0c4802e41d5540102e081b17540300c020300b000403c48002600c0c15200c2520a0301552008480b200604c2518505c51645454410110041100c6420482d4007a10713240e4002d40711000da076a0b143c06001c180c40902825501c241030031401c51715001001c5000d40f5540c4911220350006a0812503280781c1d038081e59204410a4020a080b810540306550a07134004000c44480c03010301035804c0c018044d10009000951007242202004552940341100083e07100b07003114601034203400c89 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 890692482 1250 890691232 890691271
    0x317010b0304020d0303020d050f040b07020d0905010e03030715140a061a0c0109050a12030b011103070305090d080d0c0e030a122a080a0f0513050603040303141e 71
    0x814040c1c9402c2501180c0c41001e503c614a8103600034800c269110024134206010070a800e415000c400d031203035009120207049561803c100b283c44038404d0f0039800118844c0841403003954450b10065800c040d000e02283d181c603031507444618803030f9401e030300c00a001d64581403103603601c44c01c8803001c41d08410380450a001c02410070950001d0400c201e0321058842c0ca01040070b1580d41802d4000e5110580c2000c15140210041d0504211120f018040c41000c68180103001109500c1507001a20714050080030718200241c9a030f046456621500003982c0c0200d2840c4044041a5104010103070105c0401000402c0b181000c0040c1ca00780c0ca00c40400d11a800001024002c60411084a20030b80c0152400c1003c2d03089440301400c40c444050203040603203540044490410007002c0003407a402c04991241404040c0c0344400b21824410343d4003024088c1002441041142003c5000c3c58000b4400c0c100418490034500580440c204c045626210301e1026000003a80c50b00c41041d40c542200304540800481c20b03c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 890693732 1250 890692482 890692499
    0x150501110a0b0c21070305091c08160e060309030a02070f0b03060d170d0906060b07030203121b0c030a0905010e0f0d2901080c1f03150506030a020403031701 69
    0x20b0040015540c18030008080c4240b00c00c1d00d42480000007440d1000e00c1c20305190342c00800606040f20780b202648604038901410400c01c0c010215400c585946110729551600204400001d0008192013072104001010003030381d42710000f41d80b0cd8400040155280d0301c080c03034000e02e010042d500803040345000040038040141c0060442e98400400d8a82c4629512989440c4252048018040000c0540420f02010303038501604012107003030007a0b074107100c415222002c0c20b00c28442c900700100980e00800403900c40c03051400002e81d001c42c1da509414005201881e2580380c80d40b0078040f05200350000110f00c900c05070480d00d6600580703400e01e4010007002480010032828080c0700301051141c0145241c0c4806c00510945a0b25400051620b0039030121070823400d01130040080c002d13461203004a240000040c24406111038448050850031540307000340210a074001c001084c84200b641070328090104a580f100401507016000c241c0d001a81d603891801c0c020441041000800c040d0a075900c0100803010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 890694982 1250 890693732 890693753
    0x13110d06060839181801080a030f0e030601090f05090a03090605092b0c0e190902130e0303090c0409021e0d060e030405040c03020a0f050903030d150501110a 69
    0x18103103c10610100e24801c1041c80c46581c110200b50401d80003482c03107844499180b80c00500001510b0690000030b00c20040220300409005100c404c1e40700001c000b01103445801d00d9140c0c2407241c2005010180c01c00d001c2424a2003d0300007230325071b5803622400510300b01140710f020b81c03100840c1c01402c0240d4550354001e02c41d0798644911020454003092801c03070383d6240e0b1200b200c0b202401c01030780040d0b070703040e5419011110f10041c1078032a000200b1001541030f28004500b407192042c1c40d05642650705c41d01e080d40c010040c40c0c0050741c12112202080da0f2115103480380c0c690302e407c3d0000864980c40c0202d2054944040c52100c94052401c2002450060301c400344c4404003150010b10416115500e04080780c2c000100c500e003c1c141505000d03404a103c0d07808001042521810394060128003120002981648281c8102030b002441071002100c22910036000f03080300180c0102502d01d0280c00681d41015580010038418100310301c240c080011f0b41c0c000b540103001c0f403940c0b0b0103007000d041c103503c0f0b0070200c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 890696232 1250 890694982 890695021
    0x50d0e040e0d1d0603091506010206040c031b05040e0a12110709200f1e0304050c01080405030d09110a08010c0f0c0501060e04050d090b1306050913110d060608 70
    0x101d0800f6400e604543c1568111601d110080d00d41030b168609002c9140d070300d1148400d8000980b11000101d2915440491030034030032900101a85100c52460b59080c621650502d0050205080d014000c2499a200e000722542072917110b009051602076800c00c2000340c000405424103114244c1a110f1004d0004500300d0202c500404000845080b141c03c40070355100403080008100358002807003e02011524041d10300f08440e8029a0000e00361255940c2e03d81c0701c19980580311b540083c80c220301640c13083e041c10b03a0046c840c2c2c066034100310b6549040c0d01558260041180d0400c4030b104005014201841003100030502c0038002e1110300041d40015250154241d000000c0102040b0745c4018410700b50091402002040c0003861710b40f1300b03420041d450780e04681c0e0750000143c54840005a03485000d06954400c501d85a0b54010a49000030070750f03407079201000460700082c80005000e100076480c85030107046111075400a0782c070f1014905400454403d60444010303c810b030f10902c40807004241322040302 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 890697482 1250 890696232 890696237
    0x50405070e130b21010608070e15010c030903020f040b120304050f040c08012108030412120c210b03060c03040b0c0c122b15080c0922080403050d0e040e0d 68
    0x12091340f000c0c80b43c00760806410034035041c031699500240050b0440729081c400c2c204a034234900d424040500440e10030000e0880030b0001944c11009101500d06510342c0040340100400015070550340c1c03000729403041d400d07410952445d0800700342040a13040110681900d00c100302d50030011108882000742400f20107004a2600c511080e0f10010001c140700043e003040b0360000c00780360f26480e09141031022249410304484c0003607107100c000c204101907070080242000181c0c8448420580c040c20b03402c1000014102c165045403100d00305074880d00c0900800707004400611405a4900c2c0ca81072000080700041c00c01c1c0c0081200300704034081180d0204803c4240821074149540e900103140d011449140010214100d03446a040030001e5035101c3d501c5801b1004000030540e0182e5aa8418140c45080c00f2501d20f4201c003d00b00000d14405865810919611a020504846c01000c1c0c1328011a9003241d0001c4949620425900d102e02d60030000d000081c240868003405100b5000f60444d40b80c1ca220a1781030107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 890698732 1250 890697482 890697529
    0x20c0a1403122a0a06090b040215090307030b0606041e03020301051e130303020c0607020106170d0512060a03080d090c090c0215091e0a140d050f090604050405070e130b 74
    0x1400030203020310f4104c0c507003160043c84090018101121668000d4038102e104081c4002c000807600e800c8003d4130a2540002d000d07000d454910b0f102d21600fa103000342040d6003e8030400c400304107981c00307449c0403402c01c81022a04541a003148181401c441020b0302d0354103090700010302d00031a40c640070b40141d800805500c040c844a60f1038a415006801500c002003003e000709410000200c0d415801901250074010312040d1110480710100c1c1c0300d024494a510018404001410f502d0200e905240d40005d030103002c1005542c1e80747c9841e42c4076041100e00c00d13071107900c0f00d07001400d10055054513130282c21009420042c0380b00503e40603582d002070b050100301268910340000e15015080c0144e11400b000800c601c441001c41e10852612002e809070101c4080038008400c165050700000d4000104501c3e071030700f40c50203030707122482d038007a401c600c0351030343c1c4543c04000c04609500c0320301985000d0007254a944064680c0300c01041403407403400b07002c00300c1d00e46001c0c03500302a43d1702e24441d518500d040301c0c4c1c0d620 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 890699982 1250 890698732 890698807
    0x909120f0702060316030b040b0303220b03010f0e091504030e010c0b010f18050907050d0c0312050406020c011d0f030109080304030203192607020c0a140312 69
    0x88441c000d800010358420004400c0000c84d01e0262855003c0ca0429a001c10101c941c8000b00300032030384400c0d40c0503016803041c00121031140c1803540c022041091250045041e5940d503541400d2030380f090300f20030201c007519070b07081040b00c6003902950b402c903280c407014105214030b00c0c4444440c500028805010000018040d480320390203813101890058211120710307195030f11040320000e030030035503c1400000b411880068441c00340a11401d40100149005081c20390700e0081040900c4c0350340c002c2981c022100d50400170003d0f130802d00b5013a1401e0305482e515111464444080d0512000000c4a410320001100c9204103c0700d101401240640485560048200b410f01090040000500080001c1c500000740018150000094480f02c08030364000344d902d0b80c6810003142c0181c0d4680c0009a221880d6206440304c005c0b09000030351060b01e40c070403260511280c1e4001602000383c1d80c04034543c03a0070b000c520000e034142070118400f00d4140304005458074068110502c0d418050344a042501c1000c0401321 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 890701232 1250 890699982 890700007
    0xe01140f0702190810060b0307030506030f0304080d081602060115050c060907030204150e041226010609080c090619050d0b0901050f0705190306050d030305010f05090912 75
    0x1d0306207640181c0303148000e190703000e0309986800700ca0251020a01c5030005080000403107004d40b00549100180017801c540f00d02100f600030301b01c043c20045e41405403101303c01268030108050f00c010040c0d08024110144500d4000d0001d40b0054410034001d40a2404c031041c094000031617504544804015036401c48182070304035602c2c06900c1141c05540504018002003410000300700c0d0a59008035010072004100355405280a4802d101d080285000c030320014002c00c80303007207c820b81c0d030b612410000501c0c41c0da000131a0f049901091105903c042040040c410b01c2e5100c0056400f43c49420001e00c08c0c0c042407400100a8600101060b106507241c503c07a00c40040000420b900404001d030030322081c05094a0013070f03205c04d070440c1e05140c2d962a281c00900c00340300c01d40c820f600400b481c0e1255032414486424001e22075404024000506450700800141ea0b107a1a903101103990080d5000500c1c1e50502c14800144841944102d1041450703009010368130130003292400c80150b00750380403503a505405075813 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 890702482 1250 890701232 890701237
    0x31e0403021204090608011109031009080f030403051905031e27030d0e0c090403030203060f03060c070303060f030308012303010c050c010b0118050d050c0418120e01140f 75
    0x1244030041c2c04540000e414005412500640e400a0002d100500c81c40c44c1c0c4060600500068590690111440e40e10800340c0f6804a11440d000e008250326100300c01c403a9806540c000e440490004800080c125055080d401100f0380b00b846a2500a1a40c20481c0f000050f800d1807601611070b00e18140b0100c0c50480c1c680041302504403512042c801c2c40744214110300c2d201c0c0c01c02420721600038184071143c98120340200b03004401c01030084c04124149c031142c0b8120001d4100416540d0030040035640101d86507000c0010341d1043c0c21907652241c0d0742c0351510b0000c0c25200503138060300d0401c80802083c00042d030000e81150654400c41d503441010380c0002480380307054403002d98103a01035280288005039698420001c00c085040300000b441003400f000c0044540d540b0a50804800a1400e40e0a1202e450041d604d0701d2118050700840d100064080009000c80304900035401e000d00661110004000d40144400c948840d603040c0201c100304448000b82c031090b2054682608201d0020381016148100b605 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 890703732 1250 890702482 890702503
    0xb09010f14061b0a12020a0503032412030a1d0915010903140601030218090d0f0201230a0506060a05160606080f011d0f0c0f0a180c03050c031e040302 66
    0x15004206150914016164040c031303c000d03030b0300c10704c480c100f00b000320b000007010601107601070029461540c440c540c24030403402252203448052a0142491469130347c14908a08041c00c41d0041c43e50342c201118060f01102a05941c05144890030840f800595078401e10b0700c4e4864140040e60026905803030040311111100c0e04001c1601c0e6035060241800c1000240d1a41079904c02c1c0d60741d2540942683c820066204200c805203082d6001d20340780b024603441910140641d01103400045002c40138903c0c01040f107848074070f140c1800486103040045a4105004641e041071041e61030740c2c0340881c1400014150310510401403115420305070050100401076002c0002800510191340c0134160300581540a01806c0c44a00354118400110961013280820440c280e5000c0c207004140480f824024000341e000c818140704d90100008000281010010131030643c10307000c24000040403101c0f01c4000c0c048901c0508000c460013414402c21a1001c0c45060001203603140600c0108030b90341d146001c80c5481104403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 890704982 1250 890703732 890703757
    0xe0c040f090831030c0509070804050a1b0b0f07020310090804090e031207020a150e030a030504080f030702031c050417030a09061505040e0a030203070b132001030b09010f1406 77
    0x800041400005ca11079000e0301c034111000201038503032440440d20b217001520050196080045c07400005500907a14940c260417002501301099940c41c6074100c5a040313004150f80c840700005400045140c1440300000310b00105d07104219000c11901c50110f140901d0188080c583c2e5250464800c51000f001980e2580b01c0b8903100380414900648005d4403494040300848940c0b0500a4001100c085400f403400e202002000442c1044c212000480c00380c000074006030b4000c0002c0100c3c0b910340f403039040218443d040e150003c594412000c2d220500307698048001c864054500400e10001540700c22185501c8a041d4040da600c13038803042c18800003050902c0d8010491890185030100340b41070403000c01c04032501201d04004082407012000d4035107010f114020b0058004010100001c2d010200d1540c0006038400740508407403881c2c2e078820240740001007080225030f51821142196916014a200302e5105a5400e0a030b0351410050314000c1005c2d008080c1d84518206450400ba260502969089070001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 890706232 1250 890704982 890705077
    0xf020706060611060c030a0207030e120d020f2a180103060b0f01140f0a1b03050711030c0a090c030b0603010f08060c0a080601030515040e0c040f0908 66
    0x34500640102010b2040030046040c5080d103510300500400c0591007200300390036152442c0d40d903940c510002c1d440804200c007400013444601e03140340c0b21310800c5110081e0000082402c1404400040d283c0031080d4421201503002034400b251a1a1050780702403c090590002400168000c0004900b1080c0f07548808400c05100000824407402d40c003d43c2014009980c100140166a07004480401507030f8092004203404000c1b5221800003100286041c148518122005000da50010105007400d050180c0009001040a1050142c0764550780170001049009113000b8016402141c0e40030384d41c0c800c41d80c0e842da442c49410032460285d0815820305800802090780d07582c4480da401305461040c051042e091003200300164441d601c1c038084944481094a50b41c403560380b07810044002e00001400c100b41070a003482942030646641c0107111854041c84040c160340c0b41c1700c00c184011900181c02040d5018202005c600c04641c101e422501c8824107821240103800c0c81d07981d07041495100f141030b8075031401e44 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 890707482 1250 890706232 890706247
    0x20d0f061a0a0602070608061e03030309010e0c01080412180b04170c0306040201080408031b07050c01030c0e0d150207020a0b03070909091e0f0506070e0102060604060f180f02 77
    0xc070484201d0064045648600c02d540759003089988540f03a009150200d6a2503002c01d600e80ba0201e0101e84444007103001a411005443c04241036030004e0f203002c1a242c0d100e1100d070149180500c4101d035503c20a1134070201918003a01c0303014204d00c04010300400d00a409501e0030342c0c41078005801d005444031080e05a0f0341c0d0b6503070340503514542e21a1800d00c0300d402900304071880c070701c3c02003522030050740c05940c0c220481c0c860f5210090240d0004e0000384480311501100950b101808000d81443d034000c0000e816000e218400150980c2c1d21090b00008000191098940c140d41e64810b41c4266230f08404102c001d1b8100c2e000c031030001d00c14030402941c030074000c190000345d403806100114820038403a51a401425621070395407083e103005203001800500c074010100c0d01940b541401075821806156017034200099900e50b907003040e900b0b640d0100002c540d030040e600380c5e5804000050704800d095a003000514900200d0040f2880c0c035019101800303504018200920070310781c11039014400320240841d902c101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 890708732 1250 890707482 890707511
    0x1a030f150a061215260c0a060806030105090c03100917070f03110109030e0105090402130902040807121a0c040803030a0f05150d12050d1b1713020d0f06 67
    0x1c40c1e0514111503030030402081101c8044400c3c410480320174010b880304203d4860100000c408110b124034442e0321600f282ca92055031114032503001008180c035110590304142d4181070079104002c0500300140d00100036410030b40c500003285020380b40301e0700f000900301c60f980c6854010041100002c40700315a0105c2c01c442030002c0c8510780c1e1000d52090322500e036054461414a401d8804082000c0c001c2800740726000c2d11540924020301eaa40c200600051a20740301d8401fa48580001e40c101140d042d07404903091000300c80800c0100080c1c40b0529010341c42c10610381e100c06100044825178010f000e080700200b0100355810080d41d01800c0010180c1e82c80740b0301580c0348001000e0402860704018101004140d006078450071110302480c015241001c0b207070709502d40c80720203000c0c2008801000380030802f2901c01070140c0301e90b0f02c00310b00c6214003030101800864001e1003210303602c0200001ea4110402d003c140c000407066400303a160f069441058102a42c1070160f000d4000000c090724035801c00c521400d401c030b03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 890709982 1250 890708732 890708747
    0x1b09030a060c0f110601030204110d050405010c03061e1401110a0506060301051b2b02071a0619060c052a0a060f020705040513050f0a0b011a030f150a06 67
    0x801d0351007412414a004013126140c00c0c0d903a001c0140d8002400501c090b041a402690a8004810005103040d580c1450303001116012030b01030300c0b50303550350800841181d414058000140304422440300709a51200c80e0701007200492091020302500880c404040d03074060100352000700120002d50b061714000707041c002e0301d443c012201c3d58840d51825001400e1940d01c080c400500c022001c10f400d041c0700c0303540440491404044c03036107652501c1c04031502c580d8000e24001404824801c20550140030110750380c9004100c0041c104611482d0840c4408150710038410300141140e0701840d140c401013095080650400010100750f680813100c1e04085101d0f1518000e044103a40016102141c2c0140c1d02c584c00c9075280302544000c00141c01c00e40041005107029001103410032024002550f0a05450703807080d180c4204001c00c5911a000602610244401c180303009004081c544c0010500017140440e0341990721008104001d6110160085000004d000d480e051f0700280140000a0082d15400080c1011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 890711232 1250 890709982 890710001
    0x20304140105011d0606030912040b120901230c0409021321053301150f0201020f0a031e050f272d100c0e040902091b09030a06 56
    0x350700b00800041c04c40602c2c04882c80708080180240f409460313840800c4220b901c0a00141401d00c109002e020003014200300800007441c0401919542d920a2000d07800c2c00701008000000c00d0b490a060320059101040b454014108a9189030800d640c3d2400d600f020b50059400c8810410b10201c1c00e0050303030100f100c159040d01d10440307500b54017180340c0b01104e08403200c0e10070003087d607003080e00440160303400b1500004000181a40710410264844c01680f09444241c0c840342e41001d4409000c0c0725543c2041c40d00c1c150401d184020b601d024145e24030030f40c2c42c2c0b241c1040c05080640d52000b1281c95055074800510a119846c0306000a08196584502a05042e0b9800441c400e05202d500741c0096400840b020303400309680505452010488503602001c0106880741c2070303c45040310042d564a044c054800b00701003590b400a0313030820184005140d801e00a0b901800b0300d241017070010141e600c1812080d4070188003800140d0700d004074a40d070340c1c0c540201015103416200380192101001115040150301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 890712482 1250 890711232 890711273
    0xc03140f0405010801050436021e010f0503100605090d1a04020301110418050a0209060d14100b1821060f1509070807030615020609100b0a0612060306020304 69
    0x156603c41c6c007000101c1e521210f0402001480920503248a100b011246c100c2807401e400d40140c403410ba40100d065150043c9100000d80320764035102d0038668000e42c004051000340c1c0b03801070452401903030b21980c0d507407180242000c0c010042804a0a65103841601d10740540c0482034503c000001d4000403100001960224400c5d400c0242c1100d98411210544040320100d40c280c0c214449000200401450040c03d0184155000c00c00c00842c1c0e1200710041c0b00000702042c00040d2986003500750781c082d0f10082e208886c0f00720051801c00c0400020006c0d104c1e5441c24244280c00e15004000140d81c1c20300c8200b0308048909210500310642d04045901031041580784503040c20f50307a500c54641d190811701c0807007a62049102c80850609441650280d030310209a040020b0302c0c80d1a98040505415480c0ca00c0380181e10071420815141404c2c04841100c04038000c1c01e100c0820b4040004002600500912003001505071a1010021003500841700541d0019000c641d2400e0900300042440c510100c2e1810 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 890713732 1250 890712482 890712497
    0x605150a080c0903030a1b3c0b0402040e100608010b191d10050925020105240315010605040609060f050a080c091203090406140901060c03140f040501 66
    0x26a60810b085600c5800010041c5182165101d002e444462400c012101d1054881c1c003d1000550140b60a10440159003580f0344828030404c600c0c202c20b00586c1c00740702e4003080340100000260380780401640003541210082044040c42d404c0768070703202c9400070036003102e800c00301e0000313081d8410752011280f0f003415240040b00f450300300610418110356208640040c541c805c6000380d007131603009c40313250031562071040d601c005076032140018201c0b1010340d004c61056030b48104080500c041d80040b91000c21450000341b200307150061200141c90400c01c3d41d107188001c0c545100d11260b40901209500008000110002d0350710703490018000c2d0824090702c808142a000d001c158180565000c4c91130201540e11207292100c0710b401101c1c1c0c100301801d071a420354028441e110a03941c0b0b68900c036820425610045403540d424800f000241c807240d61242d043c2d81c40c0c0e10040c0c40151910380d0700e03505441850a20590200c41c1740380465001c2c10301852800418408a00c1c0404000c1da040203000710740c0240d82d00d10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 890714982 1250 890713732 890713741
    0x301090609420b01050d0c0816080f070e190905040521041a0418090c050604030209010b21010e0103020301050c0c0a0210110102070605061003020a0f050d0605150a08 73
    0x1400840000b007128854030314500310388910003540c12a541804044c50040e0810f16900c40c4d04040d13440c5e046044000c50350b81d004010a0a0780580e444901c44d920345003807086800e0462442060590140c501030401180341980720b180d4441c03415041c44003003c00010000580e0700d5041c1c82c000c003002d0b281160305008294044078030160041c00c6a05240c0203504080c50586044030f8401281c11501201110ba8014000001c20201140101c0e04a0400c0d00b40460191031600c4d205030035007c141c0160380300310300c148002c2c03015841d000c0203541900c520701c0d0080d944040c1c15400048032034103462543d40c4000c2da03c0000c20506101c10320705040f80d101798005c0c04145c07260010b20308039000340c40c0080358030b5102e51813960240c5058002c0680c405011708181c01468030f82498542640d001c564242ca400384c0f82c0c1c1c1813044138103204241400c0300ca01490210308160001200420304007800760408100200881e9114510149034880801040028440d40d4140c055402d906403035002510208042410b410000c2d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 890716232 1250 890714982 890715053
    0x1407023001090b01060f021504051501090b1504060909150807030311100212150a0e090129010906120f050a0f230c0a021e2a0a0909020301090609 64
    0x20405485540150900054481048c11030b8440100300703440300d00c00c40300e504034001e00700c02c7c500c0d0103009007400c046035040c890410311940060350984071801c0d8508000030010541c1c829860400c0c0c800b01d40c00407034070341c000762221a90700c1203c0d007004505010304440001003540003411035104140340d2094805074a9480c40001c100c0c01010704550120003060001002070919124010040320003d241090039074944615003440c0b0740894038003c043c2c0d5241c008111200c04003a50038013180d4084000c3c403000903d2800282501c42d68400c003c14000609040c80360701c001900030305804041404104001d01e0003100c002d000d089080244d4610514110081c0718a0004107a42c00068121b206041c1071034a407609071100940c005000307241103020344000c0c0b04400b50b454112044601a6900802c1e140d8250500713200c0c81809540d0300a40300200307200f280c5d60b0361280785100048940d4004002001e201500100e80500310082000f4412032501450004102158004030104444ca001a101c4000f0b00e4291 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 890717482 1250 890716232 890716247
    0x105041b0302240c070602160b072607050111040302040b0d0f030e0105220518070210090f0f06140109020f0d051e0106050309010c1407023001090b0106 67
    0x10f0b4015140324458541000b1451000079a203440025007490f00c080c2c0c00300281011415007042005800007103c040003005801015030190810280d0309142942030343e40c0724084000310a9140c0c420710740103500c1c000b0f0000070040c4d41a0700d40005c000d0104040b078100c411600c1d845030000b240b0840c50888940c2c4641040480d90380420f501c8070b1308400b5140240c80944032206071340c8059040280402c0f0ad85810b0050443c102181402100d02c0d0911500781810400d19080f03005191407110044010815910f90000f041008c280c00d05000107022189400c12419602003103802a02c1c1c0c9407204601003c0292991150030184000e0500800c241d803542682030682c45441001000d900f821700c01c0507180e1040760300841c1c004044803108040f0705071050907422031000c07d9002c540859004403c001942c0002c0c06007491800592500c0741d110503420108004501031080080d0159220030221242d90603454001d003544207001a80f0201203e030112400d018254a100444c0c3c0390310007200015860b80208032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 890718732 1250 890717482 890717489
    0xc09270308063a0204050a02120c0705151512010e0c01050903190b15010806010c0803180601290a050f0a0c061803031a0306190e010e0105041b 63
    0x407031500a445140800048001c02d03008840d84100d43e080c0b1101d03900a00c000185000f01c110303110141c078110750040104850300100000301c424010805440d2042d20a2545075102c1c2841c100c00d900c65016082035407600901e454902480c2001800b88105003062044000ea0384104541c0d0010b04461400b0b042d00b44d46a080c09480d440e031104048019560140d00602000040074049500d101820003003500300e0b0b8048002511500e00810038440084244d812480c600c40d428284443e03242820800242a41481ca8003d48807510210110780c544c0080c04034501002245400c460039541c580014081100b48401e031544021a4102030354170200f05802500c070b0140c1c044d1100741c12b0440030066014640d00400111082000703003a1020b00060080c4182001c1410704814030090450078039016044410703400d0a400b0180760312602000ba940c0000e6000d502070b110072400101e403015081404041d2005e019884e009508040d5101c824502c154021446907000d00340c617075403034841d10200e8020b800d0b0700e00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 890719982 1250 890718732 890718737
    0x3061806060406290c0a03030605011d0108040602030403020c03070e010807140d230106090f0b1804080a11120a020c120c010e13180b0106050a0c120207030c092703 72
    0x42c4c10024052076601c0360341400004d000316502d000d4549000d142084508407084002c0f964952040c021560b010521402070302e00420316024241c1800c2c000b1703064500003400140b1440d00000041c040620900c00e486800001404a400c2da640741c90700c0c45600c0c00240526980e03482000700000310b214008041c45100070003d084401100720603210311442040a000c07840d5140e8a01c0b0710003c440000744140350040508160004201c196000a60305958a42045d148034001030141180010b400440054005500c81507060791481c0c070f0a810344620751401626100380c081c00404108803510b29005103a002411f6098500d440064000c0242c0d1042c003400c0d240030741d07100c940c4418807540208464007007540b0061017920030604070000e090588010600c0a80070041182c4903034100006511058003401480c203206040038000c0100074071204a240c1e024201701500c0350441c800034024403104000e1504600320008040c0c50300c810501070086010400d41d001955152240e40035040340c1103510080e810f6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 890721232 1250 890719982 890720009
    0x9151302090613090b01080a060605090135030d05180604081c0b090a09060c031a0f041103071808060609070320040909021c08030c0a0e03061806060406 67
    0x2c50510811880a14502c41d42d180e076111400080b42d1000000e60091410b00d00070440380e5001e207003010680d4a5544283d010f02032070b0005100c0380415032a00f44002c500c5600c100140481200780c0c20580c14142041c100d14000040c500003498810b400040c032698640440e11500c0c005441c585585420444000d0200c1c64140400701c07c0404852145507850344445000c500c2203100b00000d000401d041c1e8507011007665854500302044842e026600c144281820b00700031000740e1103140b0410024000500340b040c4050141ca446955496020070350441134090300e50b0712032405520180403014540031846540e0a521030024040f2000141c2d507225035405007801e19203444507041a00130300009a03507032080c180324801d40e0000d07503001009070004004400c2c010030804041d006200d4070b07012140101600680881c14100410090004c80b90040c1111041c10f59411400e10100c91103d14480915818000d071020f0180090702c00001542030340340c580503034071b083c0c8480d00ac10044034181c2c03180806580b41d0307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 890722482 1250 890721232 890721241
    0x307020d030807260103020118050603060111070b04270207030509010c110909030307110106050f0609271006021501090c090302030a12030636020c01050915130209 72
    0x10b032200d19042141800e00c031902c94540784806500000380c0384a0001d0390000801001550381c44421a004510100103880f0220304100c0401c1040c4001030006050106079400c079003c145040100c54000e00f080d0707468545031a160f107808090781625243e100300b40c030003000e9207082c80700851007103903101c0360700d0b0b03c81c245031803100b0005461704810b22500350781656627003001040540340d450843e48910031a9000d55a42d103800303035000d01481c010440003210b41c0e251170014041c40e1a2174000c200000d000f243e4050311621a82c0020300c11000c0700f00702c0080c40e0341c0000c0640c41180311010b014000c0c28414070340d200a0707882d28030881e42c03000c03150380084080c81e030800100915281980000c007004e8407854142907158413900407034170702180618101c5800305607030300c1030a544d0f51620406018000f90800300d091140712803980d814401c0c038180d0304554050404e1069518401d15411500f0180740c11000b80094036091031415103a2a4240400c140f082814002900203c0a174040d031000c280e008103284130030f444 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 890723732 1250 890722482 890722487
    0x105031e06010e041712040501060f03050312040c050d0f0201090501050a39050a061109060304060c05160803040320030403140f2a18060105090a05060316110307020d03 74
    0x4d8029203e0000d010003680b0440b581c0d1006008034404001c0d64000b508051410070b003110081d03407000751100807013201440000c5000c000c8a070841040e01c0000401e45441c107140340010182c1c0e2005070f02c603451554200400c0f0000b200c50070614001d88508aa40f030b0345a0064407d4403c1c2e420140006024140c95245040c0c030964007200030301440c02103007a5485c2d500d100e0300c0a46200758261079a9010900c0d180030807465010300c500c01c01d0100070060070f050004d800714045000c0680010700d0161141d4001c00803900c54011b03030b200151801d441000c0801a410410034560080d10190005008801c4c8044400070301301541c4540141c04005616003883c40c0c490180300000100d0742c9400e030207080380101c3d541704200404080100c603411403142408001c00c10840c1c482a0010503400380c000d4217846000c1070503900070030707034401d200b8200a90740b24207600001340305000316000141e007e40080148541f4040d00c000041440b401515400344250720410710030b54a016001c0b000f5032121b4a0084840020f1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 890724982 1250 890723732 890723759
    0xf0c090105010c05010f050712060f0806040213090b0f3907030201060f09020c0d020c0603040b09030d09060209040e0a11060a0c050a050109111c33050105031e0601 72
    0x74041c100019640302c06c14000c80c140c030000d43d0200c00140f00e0701d00d01d0081c8030141c401c0c40000c00f1030b1a89402d616107080c0980e501c0342002000a071003010340c541c64044038001900801d80603079006650340240d05d05204d220541c400c0c10346601846041e1505030b20001c041d08117000302000d0000f050280c88039084080c102180d80b119604400315521244009000081d0440325006002400805a101d0f0054560145012000c28508003154051031000b000c60f110f110407a40c0042d08920300340c2655a6100d40c0c40d01d54450000d142510910381021101408100c1d03002c1e2544c00d02c01c503001e01000890346040c42d036a11803100e01038041c99104000340c40b20310381480104250025420018074404050301c0701400d00315641d00580c2c10303945a090080030006659404080d00d041100c00c0c0b400c1d401c180810010f40d0300007060091404d210020304082200a1542c020b025900c00d0f0450f400400642c811400580780c2841414020310641c035050ba51000075403820101c04400340c0c028100c90703180103217aa90301d8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 890726232 1250 890724982 890725007
    0x161b0f06020c01020d0e0f0f2103280e0706090b19090503150426030f0402030313140319170a0909050a02070308010915090f180f050f0c09010501 64
    0x3e41d420048541701040a02517000d421400102500045900784a0755040c00e4860420150582101e07501d81500d40c00c80221890052070a02661b850741d40c1c00385104000107844e010550f5003500c103e0702e007802d03412942041220320403800a6941480d40ca0740160f402c24498060700071183d40c240420388aa03800c44491503000e036600c1c0303020700181d43e81340003103410140041458461002803008110510602221000030080c411880046107040c0c201c44d40003a00019020003556420500410123543d02041555070360141d0b6081a24907943d40d00d25551075034a2144407501038050008160000744c01c00a04260494214145650b002c800782d410300070350b40c441400301d003d010503454040f925070b49921074648524048100165280041d040240004c2c0050344030030222820070f401d1000100c001c0505030102c602ea4040854070081751140c01d400b40514244000c003458115001c1c00910026400750b8034130305d0148007990200c0d0714034400b150b180c201401e4401e4001e154003004100d5944240c4054404 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 890727482 1250 890726232 890726257
    0x10605060a11070608070e04090c031704030c09020a0c380a0513050c130f0c17100f0303080c070510061404090b01031704080105161b0f0602 62
    0x41911500000c0094020600c0c840000310004641c2920502c10403404014160905001d88180342030030700146100202c0c00c0312401a91a40d295004201c0c2030001c15010795400392031504441e62601d02502c080c0c1092001b61004ec2d00000e0004401206108079007148a16070343d0241c2d88802a01c802002c5c0384208502290325400090843e1500d10100c2c100c107800b030412035490403504040c0d00b05415a80c020382048100d40c2c4940a890024078000352014030b80000795032059010305c59580e014003c0c00c44100a003202d0b07040c40654204640e20010004044492500320301c1316480b000064070428095000d010702d41031040c034050010902800302e10380d2003412070002c986004600c0e40c8540c20001c0c1c8000400700240c0700c501c203200b1030b2102c402d420400764043d90b0810080019442d400d59040c01844050920401048140c8900d1010400c5070f001c4c0606000900581c180708032034503144108112120002000464040201e04c0b020386254450741c3c1000504e010107081e03883e00c0c4025840704425150 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 890728732 1250 890727482 890727491
    0x103080717030f160503060a26030408060610090e0403360302121b240412061803120e030c010c02060a0f0e120706090c030602190509030d030e01 64
    0x4855203040218441c00720b40700c10fa426400c141000c4600f480103d06244240134080c010802c4030b40300c51003560210381d0a044480b5003000c40a0201002e18144240f0751158080060b020900e410005075080c0180825500585c2103400c0d250210b075988403d00030b0322865003e50000c100409d01c5210100a1003018003284a650010080c00000042c8210404640c1c0103c0c0c1c0020825880c0405a031240b402e002800382007a02003003003500d03a844542400789031064003400d069110000706002c0c0c01850800c080b1150f0b070340f241c03264a00042c1c0c901c440c8084401c10704000b18241032140001200c86210b0345526212003842d41014208003900170030492198503c0207001d55202c00d1024011169640c08a4014201324140300c5110f40c00c0e10b809007504203484c0d00784400300150b070400007103603400509400c451944401261030094090200a603000d024000403400200601c06554001c0c036903902d4000002c00e160b1284141990b00740a07040700d20354076030001c10708240c0c0c440c0243c00a10032014131100005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 890729982 1250 890728732 890728763
    0x40309061404091b03141302040e0a0803040506010e010b0708030c03191a092406031305101e060b0a0e0f130c080708012103020f1c170f01030807 64
    0x34100c443c02244c80540e161407a04800a10390584941e0640448a811030070782460b0400807040ca091360250000e003d17170781d42c9107000d078000350074411040780070341c0405159502e00341410f156544003000c0c06080c4418000350000100102610200c403c110b42c440b4050b0708540e11803e207458940c00003085007840011003d080081101c076445100c001d000c1000c0c081d002510f244040c0300a151000307055035070322103031013801c0d0141035001071816661402c1205c0d00c1c4e07034907580c2e159003642c0c0600d00e0328000c003203100702c00d9136130b020780140e401280c4140d1403141c10401d41c6881107214030a46129201d07610301035608220320750103039105802a040e551400340070701c011489450702041c0c8102c5100403008240340d41c0c0a01140b140d1f4007102181d044001440c3c6101d55504050900c1c03030705003c0442d06000690302c1035061080500078005122291444025a1000e504e07516440d030342052a0200d060010710070f840c50311500c00315051360602400710f0309601e17901a804c0d50b031031064a6105100c2680e00d038107120b0315032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 890731232 1250 890729982 890729999
    0x1e0e2d160305130f030207061202090619021e0706110d09090218151b0d020715110a0c0503060c0a081303170408041814040228030506150306040309061404 68
    0x40344c0902c02e030300500c2011300e0044020188000000c00747c0031117004011510300c83d610b92060312490f2074410704101842c0d03060402030b072070302c60010021103c242c1c1001070326900240c049101070072100d00d07880e650041d00440c0e1140d0384481d01c4c01002000f05001c040103001c0820720790702611000c04443c035a021041c00660000c2c80d40200500250340d01700000440103070400030340209030601c0240c0e40c002d108080100e000691100514040c513150036005468843d12140303e18840003d0b03d41c03840680300b0492150508450a448c103020711400b038415140130400c900c0c1030302c1c00c440c40001c480d41d074440303da1101c0c06103800020202d0742c00ea080180442c1440c0b20015007520182c0240e20403d4841c3c0e989151417a001e0420411a000610407481c1044441550000703019090384030394107c2d400e2014040d1103c00000307210810400e00c42038500340b880402000310000304c8038001c0110706822081c0e042107400709559820101e80040006200c448100102ca00520410150003000300c041400e01c1d071182e521 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 890732482 1250 890731232 890731253
    0xf040c0b0d020c1b0310050402011e0815060c0c01050304050106090e06010305120307270b030a4a030c0303070c0b060307030b011e0e2d16030513 64
    0x76003810365030000c0e54050030074082001d0141e1402c818660138000140c0000240c40b00b4034800d4a0705681c1d15040014110fa02c1810400d1440702c0103000141c042a0101000741500710464440301003100c144002d500503e0048156000d230010300004100401640d8011070b02c0e030304050700880d1550340f43d0102240035059401240003901c1c0d5100188038941c59400c02c14035201d60000c162901c1d00080080c05801580404036025140040118845103140c240070344c07004101035884100c81c030f038021003441508009a0080e98030001f00c981d1403400d9802c525204030954124043c642855048100103040b80c48000490113510020003050720304022500030030b00e0460b4002c0368014000395040c00c40508021064000303681104041d0000c110860455454040d00700c01802450b41c115000034412104c0001052000003400010310070b06c0840c140f03815240c20031440304170400705c1d0300036540f0303259121415000c1880c03280c1101402070300320074802c42e07090b002000c0103001c020410202c0e150140205407200c05 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 890733732 1250 890732482 890732497
    0xb09270c0f1c090203120c0705060a0c0b0103030807032403060b0a21120e10050f0c010609090b0919200d0b150f03071806030f1202100908030f040c0b 66
    0x10041294001413040604000a0802c40154a00203200311900700d9400250301094540a55815559600001c3c0c15520280711400c02071081c0c0c1c6010001c0205540b0445d410300486c0151400d11203125940342c4200c8040c000c038404440186101e00401c00700314160040214214094410f0340929200c1144c5290442102c070740c9420452074004074401c200c4001ca84042024051400403860030107040020300388200303200c1c80010408045032102500700d440044402c1610104020001c050341d5110050240006540550f101125580054041c10b004225107280d4010401550310f4010241c2e200031103205e00d03105090900081f1210141c1c0c80e10b424a01100c95400b5a414645d01e143c020b0001100010954156001e5103a1a100d22200d40f40090f445081e1156182c000b0300046c201e008803002481140d10113005041240400e00a2010100e801c0c00c041c04180e0944126402e01c3d01c2c1202a1803000178010814070f01040040e068111030540b05130058403500003840920b17550f82c50346285402c0100c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 890734982 1250 890733732 890733787
    0xa08031e120c180103021206120102042303101b08040c030f03080f090c06040303034106040b060f130911120105030609120a030e070b09270c0f 63
    0x2030b640625107101c2180d03220f0300800d1031305500e402003080d1180401c8101904040c00f0780500c040308107208070207405403405440e505a885d40c900090b4031080c0c0307502404d808100c0c00f901682c0c0714822003400e01d000751011403980c4040c118001200f214201ca42da04001c00c25220350300103040100004003018a4078200b103001b0754410f4424100899201070039400500b40100a5205103c840f801e500c0d46420340c3c0460380c040c100041c03044030044000160031418030281d40b408000301294200744203001d6030003a06c1880b07403059001c50741e608010300045400d510405036100c0c8080c0114900700d504a4014404403441e2243c0240d000d50740d140d0f40c1c09030384400304880d00240c008210720448043c000b031098010f100490040803d420042452070700c40c040c600d80e211000d840010130341e9043c1d000b034001007030b14003034501218000c0760303242e0b2020030035040301103540e10480e40742c1e8100d111555802c004400004003c07914803075540320005c003480c0b213900c45564400b940600703214900c8150181070360090740704000e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 890736232 1250 890734982 890734987
    0x70602070c0e0a05070f0513090501030807120503060a0b0a051201060905040b0607080a230a18050f030c0f04180f03111c0c030c121107050a08031e120c 67
    0x41002d01e03000409041925151508100d08240d0021030070385808868102240e80352108201c5002904244d04100c2c561030400000208010b014402848481d0040c03003070301107070300741907400b115188403e440050b030000b0b000d94103104102c84507000700700541ca54101a440d00007411003801c80007009030b0100d4007140c0c41000c00c0229081074000c641d40031404844a528125050341d0703103d40c0b405040034071000c101000d164842484160025050510b94605c1001e03210200c1c079100601d6010888070302183c2c0030101c500080e0500304044842d11000004018200b0448034800f4050315407030407810150b2258076007030350540a444500004c02200d02494010365105818140640100e4041d07003001e460390312004113407554014003860020f5009562601d80c000e25107030704007100c101108a902812000855102018894000340c09501051600f401d071100190340e40d0800c1600320003440307200c0b00d0303030010021078110360550098000d040c802904c841d41081ca440140b4100040c049a403440d108000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 890737482 1250 890736232 890736239
    0x515040e03090603151504090912030509100e070f120506091f0f020d0203070e0901053106080319020c041a0d051e01061e030305090d0503070602070c 66
    0x50040c854a403006000841c81e00311082c02044061000810458107115014405d1419070b5808000307a0110030191032403a1155156000903008081d02c4508486034402d540000099600038083d4620030906440501841d9001202c698040c007080040c8010b9806020340105d0740c96540b481102c090315071a085840a03120301e2501501d0504060f104d011242d0010304807140c280c0c113a07090341c2401030110b90041207504140d003505004c1c1c01280d003400d0340c0500101c00c100100d5400344401080102c2140e00d0245a41e035842407064400000c62032010b01e02c421007000c040320341c3c1419940c1c154510500e002440d543d503485e02a08541180b00940b8000c01031880703070b000319941046131180c4e0b490100c1d000c01088812a079451801d1040d140d03194041c02d020000f103000c3c007809004840c55003c1c1c01190110715403102e20030038024051402103445854040b18500f04030800d054800701940c0d07060b100c0c00d14050b10001080103568070342c9030888542c4420450040087c031940068041c0e13a1090785645110b606 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 890738732 1250 890737482 890737489
    0x50f040f150e0c0301120f0c030f14150402090703021e030106020d091a0a0c0206090d111c0803040308040c2c280f1116021c030e0f0409060515 63
    0x1000f40032464041420f00040c405603840034030b00b070b040c1c540c4000010f180703060038a040030340c01c5c07541d500240c8108284911502400008550301010030554001d1b2009030140071540074071b180090380c0180d0080da250000414290080d4002d0641145044c0185030058200c208070400ea442604007800517048030110459940c0c12083d020080d12280820220340442600b80350081d0080c101c1a01c02c0210070742c22a415501c0d41c0007101d000c09009812034040200030b0600c003040041c8800c409004e060304161441e1070548451088905c658090450351a54941d92403c403000140600143c509410381c600000351b002c28040c00f4411480000071300001090380001001310000001c000415000220098840d500d043c7d035204041030820880010380542d403882140000e1140100042c0380100000d040717811070f001c40d075442400f6803080f9000d02902403c240c81d00a150b40800000f00413030b003802e0324070113503107030480f01d0900b20300d03000c0e00000b001d03a0141c6071034003600d80942c1c00c03800c5501121001c040506 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 890739982 1250 890738732 890738759
    0x80a050105011a0703120204090f0615020721140a03180506070213050709050a030503180a05060a08150d0b0601090608010b0f07140a080a1205010f050f040f15 70
    0x40040443c100e000a04000a45403150714001801c0050500c10705907210390540c144c8000c0e0903025810413141c1d03d0030440400506060003040000b82e00507080d881e00f21b100094a5055880c0e00e414a1000c1a06c00e038541401c2d00c40d4001160400070f2421002e1004004001180c00c00b400707503981008024554105424040c019000140601401c008032009600e6001070180b1070900205c001880399100d0108a80b50340321030b048a81d10118014000049c89400400343c450301081c26680d103400840601007000c1044039216041e0800406d02c2002d510b980100700c6103511a100380001c0500214440c00110003070902031044510364041001c1c41241e590140c020b0001d02100c2c01d103041c0c02e504003001000c560041070403501c900800000c4030010040030942c198045032010084480800040c50009002d03004441e15500140307081c80e40a44010302b60042a0403600c0d071082c0c03840c0c4203041400b480b41c050000b207145a042502c0380004c0300320600e540319034500003940c01c000400b007508110210400a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 890741232 1250 890739982 890739989
    0xe0106020c010e060d15081e010b0a17030f04030b01030614040804090911090a060611070b030f130209010902030a0c17150316081c030504051513050106080a05010501 73
    0x640c041d10301e855240e42c201220002441003102d10ba81c54806284a81014003400c001034106180741c4d0200003000800040d83d008520400c2c03150b0342d410804481c441d402ca4461801840e40f1000441c010800c554105011482d81d940350019a031503c17141c220040090f910981c03080303640c80144001041840ba81d403151034145000c1e164407214500b42500ca039030307450040340121381185a44211003420801c0d141d60260400c203019000095910300301c011070bc002c1c440c2e4456600850751401100840040110710074045c0c1c0c86542d0a503040d0340b02d01c8100086901d004060070700e1f2500c0e8444540142c0c0c3e410040310700805000c1030150f42c1e071400100300d00682e284c401501c1c091008244202c040000c0b002d1001d0b9118200340e44030110030384a0701c0000d213044580a40c1104249e100c1c007000c03130088400f00d64501e2419001d81c0705050360590210031030850718215000b8065810401c041207181903840c00c41c6030005c648024400500160b51100c0d401c4440a5100d410030790b0200200380200802801a503004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 890742482 1250 890741232 890741237
    0xd35031914040312150e0a0903030e06010b030114060f0c100609110301090f021c2004180c03470102070b070507242706051e070c0e0106 60
    0xb801c1603070340605942c803501943c040c0703d52155104040308055140c1c1c900205485900000d071428a103149000400400f4403d80000e8240010f00300c0c59080000c826049920741c1102e20b14681c6001144054449807a40540e445a400c0010700b82ca080f60001408031100c100740580310740c05806a07040f04954a80d0300c030380784e446d00b0240341c0015030800344280ca044548005005c81c0c1d014091425034002c0c03248012a420319035122101000d40d003100d9000c2c000c007401080055441c00a45130001042d4061841203100b00307100110130079030541c6560042c7c0f402407010b05001c0780b81c01c5070743c030004291740400c00b00b50ba41815a8426035011620300042d0301c41007606020621810910301c000075103c071028001c4210f420b0b80014184100402042004010310310b130020f841118804001540b55520105810000294070106900c440c2a48400301038001e0310803d007000c2c682e85811801c2d2200e81040e00d007004099803602b15410408408030081c1001403180003074003200d03410b000001466a406800600c01c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 890743732 1250 890742482 890742521
    0xa0f14061b070209040206070222050c070b0114030a12020f1006050d0f030903020301140609150a120317090f070801020405011b210e030c0d350319 65
    0x701c01d0100031180312540681d840e1105640c1c43c00454500e02c11401c00a410556000140c4604010025900070011007070001344451f44403016480d5403401081070103000c0240700401006200d104400c410341200b405000d42d50403905c10348455101041c080d004001580007800840c9901a091003e014211010042080b20604000114024030b00060004042d454100303004e41c18107014400c5140150b50040080c407100160382810b4140440a40c4c2d510300600d00c60700400e6076a031510440d529190800307400c1907901854504002e4040a044209605003e80d4400c1200c804480b4141c15101d900480700a10002580c007582ca1714110240d0b100d40003e074414082444560782c45684c104000c0c05940c002090200103003004008909680c03125803040c0fa0307071502400c20b21b402c0305030700145490880a880c0fa50101c00c06000d020310180000a00a211804410800d0840a0020820b601039510218030800d50383c02c0f030000540c0142c428080f0107000350440a2a480940504408668042110340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 890744982 1250 890743732 890743771
    0x230a1b020712111302040305010c0e091b0a030b06310311040507111f0b0a0605371e03020f1c0b0d0f05010b030703080a0806030a0f1406 60
    0x448405182c400142259010010481c10b9500d9140c20005903401a00841d42c45a4a01d801402000719100306c1010404c1080c04070210b00d880448148100240d21201ca8a464107441801d150390020480c0c100341030390f80070000c5658550b00d01038580f03000490b41c2c824144d24807100034022146038540381501000d01d100d0a10010314002071142811409490200300354590400940b21803031255000000ca124091040501c2600014185499000b201c010403800440000344400751246001c0c03038020a400300320754007900041c00d5902000c00d02070f400c00301d10b60071040d00404020002806d080002000726400c10403401e1409204800d80399942011450b0030350401e040e140e00c1c040d179024110307034141641684403002525000034500307000c000c0250100100901c1c040708003040c4100142c595610b00381400304503040014031601a65041101c03981014601003088540c4440105101c5d050b01462000c000000d13140000860040c0c802c0b903414981c1c0e941811164540600201410f944084200740c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 890746232 1250 890744982 890744999
    0x207080d0e100515010305010b130308070f050f07080d080106080402010f02210a030b0a0e06091003021f080a050606030115051b0a021806060d230a1b0207 68
    0x45510803202640441c0d03040d80c0d056900c1c1480389804000b01c032281014108101c0407525025019209401d0b2020401640c13644004001809440e2038100c1071120914240042060301d00a00005071203890031080c00d50199441d82c1c00c00e000310018010700e81c0240b4081c0084030701030224044081d41803405482a600d4040024110040940041d06100701c1d680141d00c01c510030b11140d402d002d500b40390010402080031012406e94005030489001a20b080c241441d585001c0340c0a5040390a4a51410b0840d11070b0300c2081800c1c1000b42c00c20390403003024000000161034010603003070f8424802245826921481034040c152100003000481942c0c600001c10040e69501c1c02928155a049440c04c3d11202940e41d0645491151801104a0441505a0704400000001c0b00c2c600170340300b074640c01d100700001401c40908040585c5d130705501c404c003400300e040c1c120090341c810400c80a144500410324100a05022620402a201001055240c28054055080109030343c510981c0c988020b05002e46816400c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 890747482 1250 890746232 890746237
    0x5070b1306030c020f06101701140f09070e0a05041a06030706030b0a0f0308090102010e0327011e03050a0c0f0c02062d0711040c020d1112210a020708 66
    0x1c0300207040d940d4801410082c420040c90150320005400c0f0350071414070704011010040f82e489103550400d0400c1111094070340600603120083c1e0070862220b242e0302c583c000d00d401001c00504441c0350741300b43c00700040c8124080190501500c1417040001341810b0a040c010b18060381c0075048c00380c0381c8039001403140548000444d0000c031590391134001000c01c1c0d1000006c0158841e9400010000480790020050155260007829108000d8000300546008461465120b016400b0408005020100041242c010640e680740c02001d051400203104504050f180f000301c14011007060000e503507103040040041c924400e170040300b406400c0003c0725000d5100002c280a2040784005d005007070202d1034104004c402201ca558025002580b040d510307480010003602504583c1090301c0c94900b89420074041d0502d80701e008000052507018100564881034180c51a0301c00e00114065172288580342e1043c100f26078054040310522000360403803d03400103042c08040c07001504800141d84100301074000600380307004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 890748732 1250 890747482 890747489
    0x23011e03050709080d120b030a0c140105040b0a030c17150f0310140a051f0b0a020708070b0424051b0a2910060f05130f080303010305070b13 62
    0x100401c056a80003011200b80c103550303004880c0c51140d90010f2000680010040c07164a0613114200103041c81d610805550700c100080c080c00300000d002040c0240e901d40c0002c1c82000c176040c10514a003a0b0fa0b04a030020300c2d4000588803001a5854442459980d030207100a0443c96111450780d040d03040c20640382000302030034a0b01c03602c20003020224801780c0d00d09012440241403101010014030580d00c00b101d400d4042202c2d520903003441c3c20006810300c050400020309000350b14142c900301d076090000c00c2c2107039400703840198254401c0000c0018142d808002c81800f0341541100e160312241f07800e1030221541e09400e80f283d200c40b040c0515441c0c1a910500703960140c901840c1c2130441500c0c858066091508000024010500e1480da070f01c0034207801c04000b9526002a03201d6803050f40c41c034855001028540c01940300082400d05004610b51043c809044d4555002c00c000905076580c171802d2a180c1aa54000e00440e00003000400034410107004900003000c810181d60b103000f4400c079611542c1c0a0601 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 890749982 1250 890748732 890748737
    0x12260a0207030306090c050301170d021507300f293601090b0f010f03180c060207050603090a170706050a060302031c02070306091b23011e 61
    0x80c03581d0900d071194100200030203500070100900041d20800404c00e5009000b10074000d0b80018100c100c16200162030800446031740d000c0c040c019401610f003002c020010b092f00040140304103030034020300304454440d01240c1456828007110022640d0410039180d100c110b03501401d10344050850801e1981000020040310805000382d40100da10010704885a411281011a801d0b0007445680b1000d01c843d426803140c00151810650384c3c0e0301e12070303006d54483c00e11503508000b07080510300da02d5004041030903100c1c0341030a01040e00c03c0c0844d402c40f00c200c40510180c5d007107007a01404212042d010701000001e0b081c1980c24034610b01e0031105e980e540b00c514160003440c480040c607040c2d070100728110903210490362020041c03116061207034031003029000c1800b0076031103402810302c04a00000d144080d14080949034018100301c51960300d4000080032030220540741001502500d000341105045c2e510b0151490171004903800303802d026401c0c84030481c00146410301000782004408015071440101092041e40b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 890751232 1250 890749982 890749987
    0x705030d093b0c0c0714060703081009110315090705120901020f0c011b030209010923090f0f070e01050708031308160b060414270a12260a02 62
    0x681400c09260440d41803051001550028410309080c00802000d5021304282101c4800346c9444880280325404610240d000303604000300c01c00640180000d540c05010076268454659941e41000240c40001a100b800032000104200b08540203054030320420409039951011b61400c00030207031042c8101c2400b04094a4003000145104a007501220325180d0348031501500e90f004d0b402100c0c040c064a260000c0810703070075400468401e12a20941d01d102a0503541c96801c0c034075215403230403c1c4564000705600340900900c40c10058a03142102c90080300081003102041c40c0482c1000786a150190504041240b03400e180e03659070b0f9004041d142c2c2a500040d0582da0b80e201c4110b0f08400e2610824014100d540208880041e100030000c02120180200c104200690710781c3c04010484200c040c2100880720054082007a001c0b10843d00ca03030320310040750f2003e2138101c02e0030424900b03d000c120486014115004000c6001d51013612240c4c03c000a2070305988100d020600820600001085490345d10383c00b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 890752482 1250 890751232 890751299
    0x306130c1a1b030702100e040c03110901030b0d020414040c0842070201050a15050a090e1603111804020d030e01020304050d06020307090b040b0901030506010903060507020705030d09 80
    0x140111103144da40144400b442c04010100070b8124407202c000c0b9882076103040c14010049009014003031900740c00384844c03482c0410380320041d001806926641c0d44c000e03500390060390040c0c40c0c07480340c0100b0520081e80590a850589131040386038000350460852900100c84901c160400c01e00301c02c40c1321020f4020ac140c40041c00d4480d03040d10601184103145c80c0d40940501c941150194001d40c001d40c2451030900c00804030009138120003c6134402c0c15000190100304114036806a484a104c00900c441510540070701200e041030202070075002642d800e500d000da4601c02d45000308109644034204d2032034201c145419000180c070702c10072a86c00350902c80300e11454a01a0310a204450103864024130b05c410307074405401c082c00250011170354100800d4010a000c61190107000a4a00b1521101c3d005803a01d0101c100440203400003420148c18000403000200000b032082c002c0301c0c46090642c6c020510f4600c1c140800d03140051003c002e1040c082c5000c2c0c1405160814883c1c0c9011241d403060030303c0a03403903 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 890753732 1250 890752482 890752537
    0x306040b12010504120f171b0909180610030807020d05190f1109010e0c09030705150d0c03020f040303210c09030c0905012d050306130c1a 61
    0x800308100501c5500c1d003802c010800002c034014450800e50360f92440c05404a900d030035299901c1100484100035003c0d00000e002d0580301200d030858400168111b030074080228049004410280c400c0c50150614000d04a0182d500300090707540950341c02c40c0010110318544030800c8030700c610040680a401002012801e125040251030420045040181030032001414003090341c0359400b00840308002d0502411110385070842c41d0700c0c1a1803c08030101443e4440d0b0003556031561281d1003568160107500344c00501c1d60781c2d411240303c00d00b44134442540c2d41c40103500c004040322880c408141c24180f040c0401a0302c01c10400607074080e282c1c1810540295254100300c28131940901155400017801d00d90200d403003903800804a01200d00c034144840e6040e0b110410101034030400d0242400000e0f40313400c400140b591100c1fa4101140300d020700e10212540b01c0c00420b0610004903012904001c00070301a404018559035190001e250500c1c0b101c913458a141014109849842c4d028840c4070405450b9240d50003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 890754982 1250 890753732 890753749
    0xb0403120642050d050a050423071203050a031b090501050f220501110f190201051605030c0c0a05030a060914010504230a030e09100807090e120a02030306040b 70
    0xc1c0b200b074400d14000d85080303009095a0000320207a08281c10030012403480401401000d000315400301e24941a10030342c140192084604126107840c6104d12280003c00c9540740e0320301c0c46540e009035503887c3c0d54020502d0180036908030440741c040710b1100b00b07030320f00f00303643d100c12401d05445091a01c16034541c0380c440072804038003c04181d40e4005002e404160800d200038260340c1c1c201c0303c082c1c07200502140126491900c818042091b1082a000f104922010302100b484100400344141895428a000810f02c1c046502c03003808111401d1707000041c20004440c007004000002e200460300417204506200200b5140c0942107002040552a100b001c4104900c80d40b1180c3d009030301070000c004c0e52506041400c0707500300c04a10801201d24000c1041115440852070707800040d0151107080403240074030b0070700031056001802c0c080005034509000c500c0c0d400c103000c40c03401803640c55800f0840c100d22342081030078642807402c8141401000c0150200e110f4001c03003500d51001b400c03a400208100900041030001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 890756232 1250 890754982 890755079
    0x41a03150d0f0303240f0501030605100815010c080310030203010b030a0302210910080105010e270a0e01022a0708070e090c0a090c030609020301140415030f0b04031206 74
    0x40314010500110094001003147c5003643e003804403640d10000e0104051741d03503206134001150100050300100a29401400e80b0b0300614100c00380d02e116031a00c007215001654240001c1c030000400300190324003400381c0142c4044c12000b5040380c00c0c503039a010b9a070f00308098182d81d4140360400703580100c54142c81956161349000c2d203400040c0809901c01401c0440900900f4046259a07034501090b00342464249110214194011212506902103454290005210760089d98441d041900c1080003800544602441044030640b8083c0c07494078041408411441c902403540454400c01842c0000242c03038086078138500e0341c0354940d250301c4001810002403010b1150070403402c640c00914140d0990140200c1406590104400c607158003002d000da20080c030840704456240b41035524586401d503c40703200c0340300000100e00d406540c1d40c0c1703640b045c0464500c107640350401c080c100001c3c1600100e0248001d42020010400e00c0e0510010904040e41d00c0318200d8004194038036072507503c0034060145844e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 890757482 1250 890756232 890756291
    0x10060e010f1815020a050607020a0f0807230102040f050d08030609100f03080a021606050315060702032b02010504021f030212090106060e04050c0a1103041a03150d0f0303 75
    0x401d030501d03c0607540d8464030004030b8082c458000010a80c501c0466280c1c0307159484120088243e645032070380c503a5a00300c460181c42d007080340c0100c2408041a44100f02010404400250b01d03903107003504800049070154401d0b4013560140c001c1da000151044101c960144046440c14804c0d103035001e40a00c041c100f9000b804005810503003700604c40301c813000e06100b591030b600b2a00000560340d040c4d210076110f803007844007048003840842c000100380c803134030001d042c03016016506240031600024074011034910016000401d00741c11502c0c081e01840d1512071641e56000078003050400742e0100303240b00b40c040741c40c500d1030100304102d8001a200c1d8040350b0240094001c0c650b500d08041c84141d0003010765115400c0490712825044040c0d0600380a45845140900384e124200303051000d05883d2110215100501c43c00204030120760034100071402440c484120351640e03140d1030b0003c1000151411284000e11480702e07090640b00090540392410f85e569417500e030100e080320101d0008040c014601d10403d55 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 890758732 1250 890757482 890757509
    0x31b0a02010605040c0c1a130606091b051201061407060e0c01110d0914031207030e0a170604021011010e03030402030106060e060a051305090a0510060e010f18 70
    0x18155054200c0000d84008031000c1202405440054480c83e101c1c20000b04896049001444400b00e407200c2281e20100ea0000c0140780b644980d0341c2030803a41c2079003064030340554402c0b440c595100091100c0405091a046c040c2c42c041055082000891051040100304840c00c01d1541c1c2528070b2000b038441c180c1d4409024003a40c4200040c040d12851188030244c0000d05c0d0328121908954002204810810b140d183c00c0200f6083c084110014090418181c4c1c140c0301d2080e00318188281440200340160195850010340a983c00400c80502840c1e0f2100780d0720024202524001a00400c0c25a00f242e4100d4100100d02e1810340180e8072140b102c03012101a518105020b22591000700013184500e00c00c4008204440d100c130000d44000c09101d00c8507070041c01c107106d4815140d0003007000f450030660700c840c1400110303590400528000004c584440c410341c0c480040c425801c04080f64203001d010541041140089038000003092640800b20b040c04100115440c16074049008502c0c00103000b05251400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 890759982 1250 890758732 890758747
    0x21011070203010b0f06040905090a0b090d02010c022407090b0a0c03020c030a0308011a0d050a060303030e0105071d0a0e0f061e0a030204110d060609050f0306010317031b 75
    0x2041500201410780c000e50038844004801e140222010700340100061140c0c1c1000e0405188100034800109030844070310a08000c8008281840d035068840c0100340000c00d900800060000d0940300080e000c44150342c8840000c003090b501441e12102c80440b180049061540c50b014112040f00d2286d00411010304001001c3c80041e50024001030294007c0d0201c0300b4005410701416512140d00d440500010034050040c8001918140008241000c1c0822070341444501101c51007202c1040d910340240f0b1790344003020000c00d600f40c01203903101102400200142c1c9080300700508034003d02000c05803e4508040640c085654618112025013141c030902502c80c074003076442885030134003958050303ca210310311211050b00c103403040403800703484018080b00f00880c078507820301014003d0b09000511441c814400804082d42922640c0003e001d5a51100185841c00050200940c0c07180482d5010343c02440040c03011030845a40365070180020010a903480d50795001c8600805902859034010000002d45030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 890761232 1250 890759982 890760011
    0x203151003021e0301052b0822080f0606090a110d06030614090d050d02070f030c030f1407120201021215090f041e051618180807120210 60
    0x2d2621000c3e2034098550403c1060001489001c04d01c41c550340b0144030340e000303608089028034946940a241c444c42d5022606039607240031907001560b119524800700800320f80c00c840c05005030780047c03070740c02d018044080e4040700c0f194481e280107181e14010b12020f0041039258240760b005041c00350310700c1c00690302c2d030a00100e40c80107040207100640e100b6082c990851156140c04500500907501d0b02d0007015421402a41038806400441d98542455828807603500810150600f12030700ea0311030364843e00340210710320b005003d40160030a010304100304810b6003040f940c106c000b101d00d030f60381180c840040c0c0b042e144001c90182c40b0b0311491030000080b13001803207003000040c035042e03102d01e0341182c845050b651402001c20800204807405000710403645003401c011500700b031150042e039004a0944403442c081100285401c0100e038020001d072080540000c10f4503819100341d15500313000c440170ba180003442d034807003c90364054140040c1031000201f4400300344a008100500c0240c18414091000740041c4008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 890762482 1250 890761232 890761237
    0x9150d030815040c0c0609170a020f0f030301080d051309060f0315020313021309020603151e0a0506030a1e0b03061b0d020a030617010209030d140a03020315100302 72
    0x2e07141e181100254159107180902524101e1140da603124241d212164503000044c100b00b010654000582024003034414031400000c0c40c080810360014482c248032070342003510f0080f803c0564400c5400074401800b8500c008544042ca046080c0f81c02c03629000007e1500c0301d009401da0004e0003161a0110004149840300d480b00100c900400c003100144141c48004026807000b00e85801e0301400790900c010051a010070310001c4c40c1c42c1190300042200b2240c2c00b054a40c0d20580b100c0f95180e0807400c00003ca450150340072103540701d0191010110280f4800410030b04403030381c0a5039110b41e801000060b404205076004120108d0700c26840d070041c005d1480300400404201c1d0a0070300030301514000402d401204542e058400041080030b03031820300701c0c1801400030f4100c030b0420002c0544401001410f242c1030b22405504240202c00140d41c0c00004040500d85a2810b00301800d0001d805003031840300c1e045a09440940a0a05001d41e4a5a03056400c0c08509907490300700e5071040c19042000105545a0301 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 890763732 1250 890762482 890762491
    0x8010606120501062f0a08041a0408030702040b0105070c0f0f090b1e0319110906180406090f29010603200f090a0e0a1b0c0209150d0308 60
    0x8a000c6981d40d41070030340701510424000c400110f21191142c0990614070f00c0c0d11000d8003c1800300d29454071040c510113080444071030b02510744c208082814007600c10f44c004280140964859010310b001d183c805c1c8076480f40074888001c4d10460b51000d1503a9642d0140d82120161644171500c0d5807060385450401f82c21601c0d074044c40b0007c54100300d011940d40c0080c89600c40101008000b003040c5030781c0b800245021015802e005815028a6400e000c80d203c144540c0c018407849280d803014009844401d100e0764120080c81d0301d10408003008074003c0540034014558100b600088081201161420141400c9460640040c4804064000580022107180c0b000300707115003040d084403c0d66a200f60840940d450800d0700e1002c45801d01c214840440705000170006c0131859040d46080071a2403002078946078641d4454400303800300382c0070801009490301c504544e81c0d1206202c00d41c440940a4000c00d050502c11009029090000109903c030b5020002200c8001e0020300c01d803203a50580c980206504410344 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 890764982 1250 890763732 890763737
    0xd210c05010b0108060d0b06030f0d26160516080406030203070908010e0c090a061a0705150c090d150e0f3a05040906030b01030b06011d01030b03150108010606 70
    0x2c900385990304c6941090b0240c00c0c01440c00c0d0024000e52a903600410000d01440d50620442c4903802d10303c5001d00107100700140944a24201d08203584441102d4203c0e0403810804489040400118110007100d65200000500e011510303002d0025180b00365040326813001e413002001180c006461907140d00290311410081c0e540c20f10051759821a28240c900d10001c440550f04a590301900700e00303202e841203901c5a03a081d00412019503c405104898035460720003404503000103109000d101d010800c5800350500c40ca0703021424900b940d11541c10703000d08205944a500e003005c41c1424001003101079013101c2c2c900c2c441004000031555407e44d60b08103440e480c410314081c810011401203040200d910404603000d0b0340900d0202840b80c1580c09030508070990701840000c1c000481d440b0854494000034510410050384907506600300b1007203031807004082c64104001c00c01145488d511260b00200841c030b0a0a0120b6210500c1002034200010113151b18070800704c2c0000046c00410542042c000c50b440d0340c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 890766232 1250 890764982 890764991
    0x70b070201170f06120c0a060206060901291c15050a0905090d030507090e13031409132c01020306040b030d1e0c0b09010b03160302030c0d210c0501 65
    0xea0200c03103a560220380c49119040302c030f40003503194180020368204540c110000d039440018080009243c020003030b0048001a4801010049207040401d4058050442003c980315403e298a030080d510744501911a2462a004100801c0c40e41c0051392541d502c0701c42c032405110310907002e00241141002c1e4411284100c1803000005445840741c807580c3e0140c642400540001d40b100b0070309502a200c09056102040381c1c0e4800003880c0310030030744014010f0019800001500195080040c10081480c0203101070300360030000d00300a0340d030b400c2c0e546281010030713400801c00454507103102e101d94030031f04590704410300e5441c070014131508103500441c440c03242110100030843c010014182e0319120084200b012420301d03244506030760000c05200d810400503141c861547c83c00c42e903950240540a442c0c1c80600e0391a80c000c40c203145001d0050300c0c440c3c50580190b00d900c0e0b00e15000030b0b0340c401c1848803413070040f51a580e2002c10701c08501c01421100500b2034244110100071070b401409404421030a84d05540ba1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 890767482 1250 890766232 890766257
    0x10504120504030314090607050303070201090501140601270503120405031908040e06060d18060e0d050f0906071a0a0c051303240f0c09080307050d140c070b070201 72
    0x18002d0782c09694143d40c4030035005115131500f051303540c072465605031302c000203120790000640108001d40c807030702c865400480c810ba41450181e0039126208801290010180100201079900010303910251400c001d00300f045030200982d0b41c400b20500c1c0c20094060007001013940900d0004d4000f081107480c150101c5a001c02d44403444c1000e140c4c020001421501d04110400c412808811040c1c0c000000030626440e04071030242c950111a0806080501c0034000c071042c0d0300b031002d01d205036003040f940000940322000382120020924807a85698042a00c404203a0540940320f5206a0f00340329404210070043d0f00c10b00400c0d00503500215502c1d42c03c50b003052800c24565204000b0384502407020b000c101d040d242140d03608078020004500070742e28062518031250328844903006800312145035407000a0510f0052200914600c003d412020700c80d4010801800014400100d41c10803426074030740310b900c16800c140c1c164010720988031200340c28480c5540101f0320400902c01071009034403d883c1c039402c51a1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 890768732 1250 890767482 890767487
    0x7031b02030a0908010515062224140f0a0c053c0c01050a0e0a09050a060e0f1512010e0714010c02010e060f0f0415030b180c13031401050412 62
    0x803100903901c03201210901140c3d040150107068280c1a0075909270f54100301a070042000c40c6c1643c020b4901003851a048602e1250b0408030920110007460120100040f00c0c002c0d21440c82100c280e00d60b9440002a9151020720600c0d407450020351150079241d00901d04403003110061443d044410b0711001804140006050080340407201c84d00140c040c02c4c0010780a00159a00d8220304503031010320100002c0044143d9844943e007000e042013000004d910705016419100702c4045030091a01c00e40c004080c00040c0710340510791030b031114902034100b81344030001b004511f100485824001c0150f0901d91009100c00380414550183c4802d003150030b4440191100441e84900c1e0804043d0114145920801c002c5c14458000c0203c030080034121031500d0560000340d44c403a0311070b5100c0f00f25842008003001610390716000e9130b0102a000c0700e0340b40040b51024202e040721710000d08114039612000800f441e0311f0309014440801590070904100b205a00e1450f09800303020111412625072210000c6580c1460 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 890769982 1250 890768732 890768741
    0x203150102011d0c0607030908190507060c020a0314010b060309060106030b06070305033103031a04090b070305061809060402090f07050d050a061a1e0a0c030807031b02030a090801 79
    0x4488030f005100d004640003d10081c4d80c001c0340c041c0d040250301d00010403c20b10400c0001c02032003044a04944012642c2000340c140420764028404007e0036912041c05680c4a80342074013500e4100c0303608030364140030304c0540d401050200c3d500f0341c1050001c4108200d440d0040340c194102d0303221340c8082c824846550108a0f6500c0b07006002000300b041803002c80d440d450850306081d030010001080e028100c000522080c807008034290100e00103901c40182c242c0fa491a4403606215032000e4070248040c4c2401c2e03440e042c140b14024408000c05681b81c0c0002c0c4282e0b034506000200c030700d0030031004003c0e0400c200c1c400e0300c4440445090380034450711800300c1d03032902414030050301c035208540d02d05080c420140c40da00b010b4a000b9010020b030b181c0390b88000c2800d1502c1031441015520350182280d4032008602194000440300c9140140e078070003441500682c50704489040f00140e494a8095860781c0d034101d099005001540d20142150b13407402461200c990000300030400d00410b0340b5a4502039a0f1944400d003a1b4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 890771232 1250 890769982 890770031
    0x40909030507150618051509090729040308160c0b04060f08040305091c14030309120405030c01050904020c010504110102010f05311505070e040e0607051c020315010201 74
    0x400d40c54000210707084582c2e002640044124503181f46d02c16800300020800321081d90f10038400d801c00740040088070032040003c410103000e94001c4040107130307114080710b04c0e015502c000fa00c100360008030042189a2100c400c00815840030074500c070540c598400c030b811740c0c109000d074001041c41d10403203181560160a0403841207a0682c0c5503450400703020b05000000d140903910700004030446001c0710004401c00c0c050064080214021510380c43c0401040d883c7c1249000303c01b1014400700000c0c009a100842c0c8880303135107800e080040c0ea409290020800a2180c141c1200195281c076050104201c0031030030070b03c0700180990092020b15201e0450320121034064504118254945004124100d0241881700c0d00305c2c000203021080070859140d05080c2483d00e90304200d026a10b83c02c0140042d044140000c1e18541603c0401245a42e0030442c0d981d0354026040f00107004001c200c1d00055103102c0c0105010900c095025034403410070f00e08120b198900d010f01c03203001d0b500782103065040058509102249 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 890772482 1250 890771232 890771249
    0x503030a2718053d18020306010813050604060b0a150e1311071e0209040302010e1603030e0f030c030d0822031706040615050a200d140409090305071506 67
    0xe06441c1c01c90101072400c03102d24100b0b000201000105540c821030305ca442c8541629016a503460010001045600d00600003003203600240001008108001400c0d0ba001e6800390002403840300840000c0c903004070300c2d40600d008821300d034024181c1d13603807140340c0b8194510245c0b2018480303010380c81002e080d40c102c0c01c0300300b41045042c803810004c80d400c2c0d8030203107c0c000c124101c6101642a6004540481c81c00c54060f00541e45908800885000801c402195807581303070342c90400203045a90040c0110824601184507030b000c0a07070b0b000a079800b40312a44c103d640040071a22506800c071005807401404035000e03010b8241d8505030400c04484500415500d84d072643d2000138101804401d100d405501814030f0307030400d545217004624800c844640d071802b00c0c15a00c40c0c9860318601c3d10024100700395215001022240005000b044100000d04007407042d00900f0041c00e8a01030910090090046074071200341ca5041c14494020325810030020454940220b41c0784c0d280040401030103003980c801e031088880 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 890773732 1250 890772482 890772541
    0x20a020103050604020d1407080603120405010804020f03061906081606050708120a02030114041a0d0f06020f04031a040506010905061c0326010503030a271805 70
    0x1036209038002944401c1c000e1005013840c66480402044400b0201c078507041d01c01344814000c0d06070f001000c003039010100301d00078525041c0b00607000a06000e6071007510305000001c2d01140441d070341c0c126085151500a000c4614030303d40f006031039000000e5a11110303e41c610701480803400560203d80164a41142003182e45000d2410200b120745601c5860265003032041400107402510011219034017441c0340480140e240d504100307180c088a1030041c4030038030a40c64211a01000c071007040302d020009c1022681035007408201d0400000180000f180141568800680019076048020140045d85e000d1180c14801d110502600a03400e0790030703103018003d03500c9003004105e114000d0f0403007544050f001d40801159480111000484042e00d01d045012541418416541c080000c2100e05009010211010315524210100c0c0d03e9108200214042000c003a02d12540c441c000044000351540c03c07071140c21190350703901440c0d4441c0c42500d440d40c07580f402d041c0498440301140e041c8403407a0f80310902024 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 890774982 1250 890773732 890773753
    0xa0c0c0b16120204032d0213050c070602040801060f0b070c0b09012109060e03070312050402120d12060905010e071d0316051203030f0f06010e0901090c03051602 71
    0x8080c66010052108028003624922694402ca002070401144101c0c41496508011505d1641000e004802071006501d41e00d151005a0b50f03607122041c18060010f00080d081c3c881480c0c2031454400c0c0d040290425000040005412005503c07031011200c1d01c2c003504003c0340e00c81c0c02c0c140740341c410404040c080104e17000c1300303200b05402040107141e1260141411144a00c00321403050b22240901403007803200750703200942d00900202e07004410003c0303c4000910705d8940b499030007400b8002c0d00344194419079650380000e02151540301411606807940c50480f00701000e04400204000ca101d0f100e0055181000d00020b14440d0f10b00030340f4141e61080d160310565640d6440b045510019001003c240b0046140c0001e0080c5c40c00c0c0510506c0000017802c68461504003810302222000b42c902c0a1010b601c20410400007610140380d0079003080f2036020441103034a90400484030488107000340ca5000c04014000035500c1c03096481120240e00e1503c00b400030380e440e494001c0b40000806182c0004d42c028a1168 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 890776232 1250 890774982 890775001
    0x4170c0f12100b0307030b25031104031502040801020c0303161b0b1b0a0c20010c03110a0c09020324011b051203010602010c141602041d150a0c0c0b 65
    0x101c3e81c94401404440b2800d540e600c030780c1d2000f00c1c1078407100303003075403100050180c8240d0400e40c0c110b044405040030b002c0c0840f150200901c40c070480c40054540c07941c0086c0d0210107603507501150300038102c0ca0020b544030b80240280355141d40c000c3d10f15002004190905107000707030060b1090103100c2e080783d44540f0006610f8550445850b401065403104407240003081c19444203110103020002c00c03d035102105481285880d00380c908002e20b40741c6654844091840b4103070307800802e9801d040da141c0352030142c20118400d81494180e41e080300800242000709d003c43e0320300d150707030141d84955240001c41a40301c1c401070f103c8201d408038080040c0000c86034100c50240d4245c41445810709446035084503440d850500f507030072594200303070003a000503510741c00c6820344281c1c809148842c03c1c0060000a1400e910454200080190300300020f0140e511120801044021070b400380722158240c0c41a100701c01d988501284849004075a07a18a29290801001280b8880c00381c2c503205560281107078520751034580c00b5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 890777482 1250 890776232 890776241
    0x11b0323040303090c0e07020c0301091e03020703060219090905040201090504050c041e03021203030f011431051506031317040803030901110c100e0304170c0f1210 72
    0x782c00303058603a80078038001035810400000901d075140b04142c1e030b800c1c40075000707050040009580c0c0c42603060580300f1010480c80120300d110811004040040c51005140c00d904029180e48080e02c0107101041e8400d8600016008149034180d69450040e19503c03048210704031a0142ca02900007104000e05010f50300b841d520580d000858801c985041981c0c911b48115025181d0f18014080606400c0801c1181080700e200321440400c400910700350b103032040b6240c201001c148202d1114800004980c1030580718007007403d442d40e107651561011071032500001118a0f403500d03008a0894a010000341600c0c02e2850607802e00803006180300d1075501d4804401c210500c103007605480e211070b04a4944c81031061a0003e00003040c3c3e903000785840c4d10300301149030700b100d184501c0040140030420039421a541c010030001c2250701107500c00620400340354401881c40c0656008243c604600303140000b52640300040b40c1c005807000300c0718041d55482a8082c011558074218447d180c96006085603c0341e600140c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 890778732 1250 890777482 890777491
    0x4060815040f020408212107090b04170705010801050d0803090c06040e0403180b0901120b1903062003010e0403110a0b010602160f17120c011b0323 65
    0x129402640c403518404990040e8410171803607002540d00c020010301c01650f2403c90100e0307810141403d2040030280c03040744544100c80c0340d5071042c90005442078007840424029103560a0710310b4545444440060000309030040c00c1e0724030712407601d001a86620840c2c005040c0c030009010040300401f80d546880040d0006455440c0c1c0c0c2c000c030b0950340840d8030f0703000c042c02c010301d0000320017004d904003418048e03c500c40c004105017408804d444103001944d9800215a600340c02843c1c940c84440b032603d0083c00610b04c0c44045a070210700702220210502000320347c042502c0c05181e04003c50444040700503030300f511615140a2a4030280010040c1842060130164068064200010b0900f5141505400e00001c9941210107000400040c015554100b00ba00001d200360020104030504140c5000c0d410841c503c9008026101c504400c0c0c0b500300240100101c40d10181210360b05c03000c0c961007890103003441c0509071401180344105002840e00c41e00400703044445422184110020345c2c0031801e2507800003003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 890779982 1250 890778732 890778739
    0x2d030e030d1d031e010b15040807050f030c04060e01150302130b1c020307031406030c090f06011b0c15050a09061209020607060509101a09040c0e0f090c0604060815 72
    0xd21100482c001c3c3c064480f0200000c8000036203646c0714020403590302025804030103854001e01003844a0100010601c00391001103c14440c01c00704040000d1515444950b403581050030603400007000010020000e041e5620412003d41610b8640b20072812401801568680560040310401203e0040e500a0400f1004034110a8010f9a8801e03ca01a80c1c4150350009c0004d41c2d880055084100c414181c507001801100980200c441c101d0000d40e504401408000d1612075a402042e0940e00a001c00e40201041500b100318100040c102980b00480a20502282149031101c8a1240344908220750100b51a9190202e2480c01d1800403070f8a0910818000d400f00d99a4140301d02585d02c410180c500d09105050124143c07518003081c2c1d003001c0c0100304802c1c41500744845650032900103007018240358000c2e80c0c1c0f00b0b80c1e0740d61410007003400491544050341c0c1e02c07503034018810300d0804020b109215403801011156002c03d03030414400a8030481c0700c1d10000a61304008036204090b40c0400c00d00007040103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 890781232 1250 890779982 890779993
    0x1051206060d02040807081f0e03030a0509032b0515030607080403030213150f1b0b09070e040f05010c0507021806011e020304031a01031e2d030e030d1d03 68
    0x1750704403031801030b29411101007544000596070703455282c20030405001038030321424404500c10019041c0e07a4040945810344050b262400600e8804040040e1503ca61406015a5002c420800040c01404400c181c1ca1003181c24070300001d000d03080f00845045441c001400408a541d90040216101e0502500c21010580c080082d034003030b90480c0b441c0791301a01c1240c520614007a00d02502800c81883c1c00341180078068281e0034200f41d5070030034104010064112400c034080d40d640100d21410a82d4071382084030800400410310083c88401400a00704910800080005c4c0240c0b40c03050343c0300d0140380d078025440784200c61a00c0e1402a40346407290003c5060602d10003402c03116803262010703512180d41c2c400590000c00c0c10000d01800f800c1c171100c41300412003d5005541540c99140e041c1442c89840b08180000000760810800a1441c410310072010040c2041c20120740c42400c40c00c0d411081041d00010f95016180c00c281c5000b056440001400e601d4130070b48400ca034215000000c1890480d981d141c02031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 890782482 1250 890781232 890781239
    0xc0603021c2a090f0b1b15130212030703090f12081c0e070e0a0c0804150507050f12040209090102090d02010f020c04020418050711101d0a050a1101051206060d0204 72
    0x880c05a001d404d480c5281d0b510744000140e014004080d0348040e40d840c1d401f42c490f8a9104949410791900440042510315400c0b00a00206112900b07900d00e1400385c2c40300107480c50905502200e01010756008010513001c3c10355414240d510b101114201034450501041214218440003508800160070540007052003006009014288402a888090307200e40480800030b07140e20300d2240307846462490918401c0c6080640310080908001450302e445542d8803400f250362680200252084c180c0f00414056850000a1450f611048151401ca000d4075102c000b0880c5c5070018000c2d164140d101410701210507015400440c0c0303a055440303811003940116800315001c0d40741d900061000d000c050708040e0203a44c0d21002041210002042041004900c90650700e12820201c0c1e0511142943c120105400d10b044040040000343c00382d140900340b2070911094100400441c84c1c000f8030b8084d00b0468143d4203105c0043d6120301c00c480b4040b80c0d4900500000d1014603101002c0c1050710144903006091540b07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 890783732 1250 890782482 890782499
    0x18061d0a0b10080103020d03170c04090c050304030e0f04020d150503070f0803030f06011b110907031b03050a0e0d09030c12030e090901090c0603021c2a09 68
    0x120549148000404410064a0349281c011600905829501240c1c0145a094024410300060000900c50001e00340b03240181445403400e021550701c400d41022290400404040682e0f2091180e1300c402030900d0480144580030f0001e072440343d609500d50844450100c800c0042d122170440c840c40d0301c150300b4410700c04400158483c40c0c4054185446042d202c80c201070405180040e0313588480b8804800c1041440601000700559822045960444031140c640e4401619000a884e41d50704210319240d0110041c02580521017068180c16100d068042c0c85c0c41404809540445009a00c58148501c1d00c40d0716511a0b88a00d51150f01e0100002d048103000316128200440120400001103a05001740240b0032980503100007080700001c14101c14446540260062110490091150304140001840c44500303401107809aa0f001e061605603d03102d250140c02504412851815106603134203440744502644140d402c1780c5195072540480000c94805604000207c03040c0c0e104102640800040850 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 890784982 1250 890783732 890783759
    0xe01030609210909050603010b063703091202061b0c03040e01030c03030822120c0213020c0c03070305150415050a09020126041101111f0b0a06091806 66
    0x804030340c0ca10304250301e40b004c04400d4400c09002d0504c2a49032074910b40b81740c8d403000d0480b4841a031034445603da441424512001028a204103040b035010007002035180c041d81544900d05007071003154001135402180c00100d81da4102181c1043d071048440759404103030040750001d0304003245500201d074a050788461191302160000c1c1d04c115115000042e081c4101500030554560000c0c1c8410460170f2a0800c200c5070040d0302c2c03d40c0300584010b0040000240e5940310307620440045401400555540710b0b0000f00100035480a13501d0a0240984040500b80c0d16021488204680d0890001c040244140c00124110100500300701d40e003102c0315120102c0300c0150301070307070344940221000010716203102d0001510004d812510741610b444d14000c4020803410414145400c01d400c0740340071102030a40801642c180e4426801007100b4810543d1781005484004840c04e110304440c8014001919081c0c1031006018080c02102e0120f46a000103000d940c0d87c3d180c200e642403040c0340c00499040ea86082111006 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 890786232 1250 890784982 890785043
    0x9070503070b0c06130f080d0e010903111b010203070b060a030c060206060a060908100917120402030f01020723070306061d010806070504090e0307060e031b0303010e01030609 77
    0xd2401103a051800d0702d003440b20950000d031500064000d0346080c0d641918251303c2c550007c2c42d001020030b104001e000a544103013864130000d0000c10164109080c05840c5510761f07004100c040c1700c3c3c820300c00e4501c544c5154002e880b02041e001141840d841d075680314842d5030000e21140d00a680b40d8000000708014114100c02465240c020740f0050402209001e078840e0160007010178040c2c0300300108103401000401d1929450200c900041c40c0950340303011905440c0a9107002c1c1a9000070800003640441e2032000d60045100700d0898068004549902d0b00f030340035020000d441001c413895801507a581080e17107a45012690030079151810703100d030703248011100702c0d820445e2011000e4030f4001c1201c9014010718050440c0e00c0082103e8075220200a04a01c2a801000c0a01d9240e00424042d00020810380d00c1903544490180031403458000001c0d034a400540304510b44404c180901c19071000040210380c117945144110184036800e5403208009040180003c650030300f02090240700e842203003511282103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 890787482 1250 890786232 890786249
    0x4180b190f060e030a0c0b07060b1201021c1505011d0411181206071b2319030206010e06030f0111040f1e090509030c010c080a0c030e0706080907050307 67
    0x101d4185100245592280c1c8416130090b8402000c40020441c481141c1040301c2c8054441943c40e4000c0c64170401405545410760b400800d8042018485901900139054651a240782e2090756001d0340105816203024140c21070310080c0421007808154425222151031250b69003866184605480c04282240c1215242c81039000d0041031304e590780d0580c0001454940011509011451501e030b0400707866100c0a0300f20010b1051240b0003002e114400d8010000741034218102c0f44150107002d083d04520320040031040c840d03000d800f03411801c403c1d040c211003003c1505540181880d0b0300700f480c006501d0344d028140d03d505100d05881c01601d604240a100422080d445000d0344076483c114244c400742145412a83c500c0310380c03148102c6620b4030307140348a0407285611008111500c60b580a903041d4403440c01e600c2d120354240a00307080d001e41c00c4041d2500504480340d04100e40c032034078801103040380c81f84040c038140368110000400045100340d1085402c04d5000040d650400d60300c2d070000389000c8140c2d005a12 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 890788732 1250 890787482 890787509
    0x92105030a0506030c220e031204020a050a030f060b010c0203010507020f06010f060203030f0606040b03131a0f061002030c071202310f060b270604180b19 68
    0x1074105280681504103400340c0040142c1e854100020714050701d2010850400c2c800002e0526030565540c00030318951001d441034071713552080881c0d0b0305100d0001300c40a0f0b00403c07161100207010700304200d40e003046075001000442c141480e40d950340041c0c49085403ca0420043c1c91a03000076079002e110b05400744c1b070315030018402d84074001141400c00303405a00241c1d9520301c0399010000780e07402004803076000040d101351030740e035588103800210503000c1d03900710b0340d0f2074103000c000c00484600c003014140307050340034480c000d20802c0e8906900340307000f40484542c82501d0109000c40c03200e040035280c1481424450050740d0412010949851509000f6881015021a5036041b101503040160804007941e05149030440e90200c0386070701c25041010940d0500c2d54a80ea8480101640400c1c0d1008014211404409643c0c103c000203548080c1580b200701c09404000c48140425031800d0000c8508940c6d0f00c4400c2c0c202c094901b10503000500989002070b4003c450382d483e03403910320341101210700030380f440303c502c0b42 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 890789982 1250 890788732 890788741
    0xf090a05040c0608090309091f06020d1e0504030f0c031e020405060d0507120311060112050f1c0c050f030307170a05010b121e04061a010e0a0909210503 67
    0x46009034642c456014007039240f00b80945c1540100448007862026502d0550b55229041d445007074034120300f00d07a40386213103200000c1182030f17001c120459003443c00d554103d1669506860086020034004129011403820081040000c00c104003a444280c0189003400e070643e0b50340c13261510400480352048070903103c401d0b03403801c602e00f80c410320360030038400d90f0901e024124030351718242d40301e9803806080114104404100d04140c400c00c0c0d1268440380b00e500b1f4400b01c0d607441d000c000081850324012113060042c2404410362080001d6401142e803042850303076400c0d040d05030703040e98035400030401912a4001c0c2d0400c800400400c000650080c05160349541d030036007a520040000c00700181203100d546080c40010007010320490241d035106500368044102c03a448621b00700705800c000c1801e031088049501c08200900c105c90f8800743d01b90150202c51662441407800444403a541d1500056010400150504c420901d5a00508601d44504090003c03003007400320600c02e5069200c45007000513000070402 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 890791232 1250 890789982 890789993
    0x908030105041103090604081605160302010e06130510090b07050c15070f02091510020706180f03110f0d06020c0c0406080303041b321504140f090a0504 67
    0x30f000d141c0070b00b039606086040c19901e540d110b1401400c0a046000f01052000d00e03e40d0500c02c50b120140e20004640e0b00010b1242000008500c3d440b040e80828910010711115061440468200c066107058062000741041d00304480040140b05071002c03c114020040f50340701c0b6000c01802e8990090b002001410581410080703580c40900840c0c03080c10007840a440015148002102c000d82d04070740b0070703405507100c0d100c81650305055203a01e43c2c005203400070701981540200711181036410a5032091200386452034a03880e0003195102d50507034440e4070b20040000c5034240c1315500d00c81500410084148083c18000307540b40407258810b403003048e4001802e140b04901040a003180c0102910306000c0140351505081c7c80c0d0200520280c0325140c03d0048610346000e4200c4040504111042880300d411a16410741d12400e0002c0194100c4501c00c2030b00d44146094101c001c80c0c1d40c030010450b80f400381000c480c1203580f96416481034002c4d640000300c51081d81d07010100ba02c1104000340000300e502c3d190401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 890792482 1250 890791232 890791241
    0x150612010e061804030c1b0b0304031206050d0b04081b030c2811040608070b091305060d0318050d1401142a04030f06050718080a0605070e0301090803010504 69
    0x920b4407a550490302c004500d03e15065aa0303005400d0f00f041103130600c2505150f0000850540c06010780b003010034000c076000c0801d00145009a000c0da88250400f5100c3c0820000c4810038020654400520303c2d84500040c030030004994050f118103440b80c18400c2805c41012010310003c40700c1141d8001080900c180c1070f040203811001311940304004403034001541b02c560842484640601000310201010440c0d8907503401071001404181c045507906a035410200e25250400d0403d18400d100c9902c200d120131403076001c1c690117200024140811041c40d42c0d425103810040d0751040c00008000c01000606640700b110300807249005110190410369140125804c441e030b43d9000f40e002c120030b80c2c00e100300401104041685080035032001182d24801244822003401035510040410003144100c1080003000e400150190465895030f0001d019480c4050b1040885405403c400d9400404000045260354000325005580c130b080c1403100c004114082030030344e91100801c0d0b0303022400000421460405204 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 890793732 1250 890792482 890792491
    0x5100e06190f2c06070f080c120f010f050a0302060315122e02120411030c040f0b120d080604200c0a050d05040b04050d0624060318020d0b150612010e 66
    0x81c10440c40d04c0a0090440206c40142004100c5082c0000b006001050103ca041024107804d0462070300d0121441420301d4424000c070051005450b4001420b82802c51005003501e50040000742140c0d00c0d000c41ca2116800d42c4a1141d1040d0308a0480380f003d1003c1c440f8000100e100003030f0007002c640d4080040c40d54141020b81c451030b41e1042024803420303a01951915000355015070100c21620114000a1403c1c0c0340d90741c1564002e02d020300102226a0030751042c98410340984000440c440041070702d075114401590501d0101300a0000a0941c0c41d05501c10345d200b0441c10700080352010219000c0d19283c0115581030101e6002c06016828800100315003080c07801c4900d0000d01c0c1c1801c140e020403481c000c80c803e0500561004102d0800c201c4603801507001ca1a401608503054200741e4226040241148109000b0a151440c0400b507103070105c00c88004541c0162403454044034a607222000142c00518000c10746600c0c00010740e0030359480c4024440c0075100c030007800c469410414003030a16000580f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 890794982 1250 890793732 890793821
    0x8070206130201020d0f11010e1c0206060a0b0913110306041a0d080f0c340b04030b2503090605180601290409050405100e06190f 57
    0x40394000513a40000d1020503003180f80b4010019002800d0180d91540151348801e44e41d500b8661051a402e038006500c1000c141d5400e107510000382e20751800d0303803510b00985a05800c040203083c244000c0803540002c207900302e405002c00358480002d0391600103c4180c246c3c0d040c0345038400414081185000c4c05070410000800c0319411030b4458400004520000781100204034540101d4820a00740140c000d035003280262005035031011075221441070341d0751030744440d00c0e01a100184461007500418880041650f0103c0041d91a05003162100b105040004100408803a150841d000400300820713021300b200501c0c2d031400b15025180780b81c00e0050701c900408011025204101c0c074030113004005403050449039441c07880c07540141d10102520107a890030080b001603200026000405c40b24582c07040d846140942c081c0c507602041c480c0c41400303407078030480b007a1591ba0090f00410303485100c0c0703000741800290303402c0001a4841f00700141420348010f041000001c10f0404014a6041510300949806454a8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 890796232 1250 890794982 890795011
    0xf0501060b032401020c120304050405011509080d02070b0c03220f17100509070e040308010611010b0a0510120504060204030b01050108220c1205070f0501021b0f150a08070206 77
    0xf280000d43e035807090346415200b05c3e0455448a45000107008882c09081c2c00392045c04150b844048942000300c00301240710008144050026007410082106c21b0284255401b4080d01d5140a04619640d002402140c60303d0004100308041c80b44244544d02c040c02150003207101c15450300b014200035880c181d00481001c0c10b0207824a0441c0804525100d501504540010341510f03030700300d45841d0003400d804ca0011142c040f0103002c02c1c50f8000022504980040d0b84016a044640c0f40883c02d0b46c0080f2144d136003040b004c04061095142c062440030b44400703079141c1a84071120380c007180e900f41d407000e460659236994001014410310044803081d43c0500428201280c0e241001400ca0040b05294882001500d80111090303081000c4140040300514100140001910351801c1031503c0d020184240c4024151038080007078254000f04400308407004180700d8003072070031416060280325a1021940d69010ba100030600035800e5810018025074000c6070b96031801840c28400203407900c00301800c41c0450030fa80 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 890797482 1250 890796232 890796301
    0xb03030901090e0a06080d210b06123d0b030708180a0b041401060609052b020301110a03060504020315060d11032e080c0108040f0501060b03 62
    0x71403101d080703e00000341100e140e50b40c0c01219006000740d07000390b951801000080c90321030764425141802c020304401c01e2014415045c42040407074010600d025040759061024418509600c08201d83c0100380c0c940341400780e130b001c2d0b26241c081040101004503599421110400f00c3d010b8141100c003400d4411149451410045406000488000e148403196000d903020001d50007000c0c442c0207841d65109159400d1400c00d45000740c00071400317030200f0030150b10701000080c0c49407184400c80c08503a0080c003040b2107034100c2c81c10340f0b04441c42d90000c03003112808011300d100144c0702440391582034206006d2a03174503000e0501004042c0e848550220341309900603c03d0100c9105070141e551481b040468405a580c641a115900a0243c5c1001c40c8100e82012080241d10001707400d104c0c0c150180821741c1090320303642041c1000801c02a018020b1340381d101142100095008102c0c80b50824020b00c40809010f80b944c2d00c090079180d0340d4014801821001c814060709450407490150100302021110120740031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 890798732 1250 890797482 890797487
    0x303021203131e0203013204030e0f0109150504060207060e011d1809010c02070503150615040f0603020a0305160f14160503041a04030f0308040221010606030b03030901 74
    0x840070b40241c1041503060100c4074450140c85907000700784d40a0024013144098080c0e01c00700c01d411140501c3d0750300c6550450450301981e03903034062140f603060b190346103540080c80a000d11214a000d000e81030002040c1c001c0303100c40741e011030314941d908595650b503540da0501c0c0c070003403c200d51540400300b4807480f40e5211186a030081003002c03041c0182d50385110310011800006018880c0c05001423034006000c030038881c4070481034020b004c014080e0b4080780d0a10380d0382c20500d0780d43c5110700701c01c500120650011961038a080714484014040c50381505050a03107981c9004c02c0c823990350344854042640019001002600760055075400b00710700d10610000b04446c00090080c0c2c0214400500708a90403081c06040400ca000391440c812440b41101030782d00d018a01a6641d5105006620919001030564610700c070104080b101501c1d44840d8000c0d01400c11340d419a8203c202502c00c0342e0110070841c0007115803000144884040c500e140c00494814078007800581141e045146c054000e800402c403444880c4d8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 890799982 1250 890798732 890798761
    0x3150d05150a0225050601080a030e120109080d06060f0c031e030f060e0103170306060a0c05120a0804120504081b0a080313091109150a020f0609070303021203 70
    0x101020001d480d95440c003803181c00a21030350640c004c614182c40d002d035014407049680120364611500440358266212141d5130b50383c80035202c008000981d9504042c0e02400c2100d100300943c2038101c0042089c12265032004a207420030302a4082542c0d80344001c0214590000356500d042940341070640281c051a200103100d40c960950483c01064000d0300140c100b07100f0f0380440c00c071001095041000c41e031203001307402c0000420f0bc4203907086440e80c25106070105242049034021503004204600d060200441031740c00c10307060341d8180e07600e00074250f1032039030f0000c46401402002819511040300307242c6894541c1119508a400b00c003000000d001c01e000c00030000a004d2185d410000480c2c000300c4059000a62524454008401c3c60102141d089100c100318402c900c107035004404180003005070080c00100c0c501440c44501d40c030401700007040e8020b1524200418102e500c51069a000e000481000b80c40c01c0e40030f80d2242c0f142c0d44411001c005042d03061248034074808840740d40754074500f8072242082040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 890801232 1250 890799982 890800003
    0xc0d08031504050c0d021e0a020744100f021c09020102030d0e031b1507030902010206010302010302220608060112060806040b07020a050f01020315030f150c04030602030a0203150d05 80
    0x1704d5001448080c00c80320241e070350352020072600c4e44030364801c5d014070000c0d218060b40c421004408242e520055200c18202c2d524050280b203030171222404503483c1100203000280069000082c01044c03040154000301d40a00d1150003074100002d665080040c034811000b03030f0340700c0703000c21030b40d2800f100c84005070f0b03001c800c5030104100741ca07000c10001c00d114003480c02c501c03401240e030b0000105241038180341c801c04103a801ea440190a140304060759140000c0c1e090f2400c400c030090050700b0100040c0300542c01380d07001d0450743d5a90300c0071051a642680c0fa50810a52507040140070801020070402ca640c0e0090030f96840400b10380c1c1c180592807426020342e5a402001c4e1004001c0c91400c400a0b0075117200300039118140344c04c03004554192241c070a01d103000f58015203410301e2141013656488201e06001800d030242c13802150040010f031a0102901d1421030016200140c0020104000004104140003842c06510241001603603814500c0c1c00e02e2481e684060441d020700003440b900c0011070030105115106 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 890802482 1250 890801232 890801257
    0xb1e0d0809010201180c08011410061805180604060902070203030405121903030608060708071b03050f0408070918020d1205161109070908030a0507050c0d08031504050c 74
    0xc841c03031840180c0c0902460301900c00d079081c6000001c414400c00d854204111959080204260403a0701c01c02ca003045400c41d55110b014002c14000c01003148900203510f03001c44411403516100703440b100000c020480181040d0b51040540c820700c00f091819206043c001c0100340c2e0308500e84200c60340070139241d0089200d194410001c903903641000d07503030074441403410041401ca24906259036107400b400034241809107907550710415002074002405110307a030340944030740d850301703001000030000c1030f9101c1241318400c8040081c140318140003040540094005403500d200942070541c14800040211500e100348042c1d40c926068241c00581c903225090b01d40940c03c105018403184408105851500c2a10711600b040c59080b901c00c000d0120100801030154412140c890450711800c108a40c140b030a4002c035456074008201a8214600030b40003071040d0340c420000d50744826909400a9180c000454050750154400010412000030000800380c82c0e907021034080100e070400103030345251801070f0034801d032a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 890803732 1250 890802482 890802487
    0x210105370510090213080d0206190e0a05061918020607030f0e0d0c03020f03070f05060a03110309030319050c07350d0b0f033007060b1e0d08 62
    0x155031500c0300144090840c880702599035100d004403c0d89440b81501c5200f94900921046520452010420364050b000e04406000d455441000410091400c105002f503e07104400c1000c00085044c8001842420744144150074a04000c1c410001e495640c8554024540d0038410500140c0d2820240c0b905c0542524049880000982086d01c40303951800705541e1001e441151142006881e8141d0400d981c426200178442050260503d075a888080c0101f00012a840c0c8080c400780c02c0c198082c0202d0110f902c0e01141c0b95441049004407984155140d5001e50000006c2241c805107011940342207140c80d00007000b162400c05080b91080c00703001001841511692800e01c07d0b4132008032155011461402e41c141060300010401e2400d41c0545d000009482c1040c00800082c03030401902280100c0180245c003149002c405020540e550105155041c0402c50300136801242c40e06015240c1d403031046400040f01e200b4002040800800329007110b940c80d2403a80c21840326200c625880c41c40560100d030898 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 890804982 1250 890803732 890803741
    0x30d0f0f140a0806030f0708010207030314040b010614070816020a05010f0905060f0f121f030507030602090105070b010f0306062301140d0c081b040e0c092101053705 73
    0xc0c10f007281303003600303044030b20400c440441d108c6010b60080401500c03c1d1000c021048046c4000700c817106003100c0150000803e0001002003a0045a581d102c900c0c880511178a000b2150f84c410744103070054034804140600e4082030707100b1400c1042c2c0540260209003091a002d21040c3e00061040c1c00074011140506000b02c0c018030000740304004e40b1101042d41044c2900e0b500e2410308140040012180307000001e4040701e0081400b840d11480300150390f00a40603103506415911a40b01139880000f13802d0400101300302c1580400c04042c0300c04d001e85600c20584500c2842d60900c0e0080e108a40c00c0302d211610704142c003070008206800022580d903c282000d040c000900c1c6011043c2e801441854800700d82080c10181c0119404410f180c0711b448624201002c1250384003450505004074051820000722a034041800c40e04e01001500c01c4000060a0841303103e0200340111210b0000c5405c55080c2c2e446009202e445070f1000c19003032201e02c82c83c8c1d0300c07007000041903520781800c0c10500c1e8069029a0381e50105 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 890806232 1250 890804982 890804989
    0xc06020c0a093803060a0b24040509010303120e03031006080709080d03020403140c150c030c03071a160905060a020c150a08011505040e070e030d0f0f140a0806 70
    0x4201d0215010260b40c201a803c0c03110f50190141001c00d80c400c0c014a400643d080c1c20705d206400e003200d0060f0a02e8803c1054122070003410607000409280001c05010004043d50346202da00e018611903030302c286c80640418411001d40b21540380c0303007080760024020040968040c080c003100316a010b05e80b5403003e464615040d40c80304070b5604000c14500aa500c90b2440325015001802101e20130160030380141784060810b030300d822410f0307141a0f11440403840e01800c503003c9005004011003d00031745c1c1c03400100c403100901e140e10030711080f11010443d420203200c1080f0301d07120a0b4007200141103041c28130416000200461000c0c01614801e0b00c0c04615030b0131040c0308002c01184960b0141c05850804801c001e00c1e9966042080f0840001c3c84030400410750b01421060030080410f0741e1036290030141000c159030845d170f60040c4254100042000f881003240e40400c0311719041c90540d11552080c3ea00804000c10a10742110314609000d07078059040e00310403a0104986070700c4143c1c505480d80d900c588000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 890807482 1250 890806232 890806271
    0xc05092d060103090c0303020607090608090613020a08010204030f020414070905011b020d1a240409060f051e0709030b0a0903230406200c090907120f0c06020c0a09 72
    0x74081700e450040c08000c260700003410764001d140f1a101c05030308030303900e040441d040d000450300000150440c101054058a0494216802c188014070650846445107074003400ca03000340e132003960407905c0408a40c05500b0715100700143c126403c00300b246d482ca80050060125000751042e01c0c100300e10407245054240d1425201c3d001c10307a0090801260f1030709428208025034468441da01021a174102003503071840031110b4130341d004c1000e001d50800c0b14403903401c004c0144445003081d1201c680f5111086050020b900c1000d2040301c8081d0b1070180d01521000310038800000408e40c04c240704008000f44042852842c185034072000e210ba010800c0c2242e46000c442240c50f605075000c4190080d03106070301c40340c50300001d0700646085076a9413401940c101e040110b4080c9100c481d4405401900b42c0d0380d150b09203500d031207038002003940c00c559005507503902e910300c62480c41000b641c52010b440c138010200141d00c0c8025000340040c1c40240381001c48013001031801200c5200d40e0440b10b5503603200d0060f007850b992a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 890808732 1250 890807482 890807501
    0xb010e1509031203060f0105071e0305132607050307050405190516030f0b181b03091e0d0e1309021005030f0708010602030a030f0b0a030c05092d060103 67
    0x20740d403014140f0b00c2000300540081d80c0d071a1141c2c401c0703210802c5a52150003543d54050308090911400102105480e681c420300c03503010381c20060100003401e1040082d1090303000038440003454100d683c2c692810300c40303c0b10300c20744030000580140d10200304030343e00020080240c8030304480018031619982042143c0011502c83c51205c24140005c2107810480301e41000c04d072075544c2c1c0b014003190003502042d104036000e070400c10b0707804840b2110083c8403100b205c0b052039004807120416942d035034041c01c054505030405c03561114035500140302115059403000041d030040480e440104405503840c030015054130241c142c07560290350807140c1030031040780e1500051075403a009841c40c00c039817030b448070010081c0d4011074090980c1e0710780341c0c0412441803142c80181d0488000341d0185040c00c294600842c00707000148004101281c40300c286c01c00d070307a60342229200114411302c48801c030b0900e040c0074445d481300010f1401400d170100c130045041c0140e1210072080204005c04851078a5503e050060b4020304a026 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 890809982 1250 890808732 890808739
    0x1140a050405070c020918060a021b2e15090207032106090c110627070e07090509010b09060f0f0c0105010807210f080f0703120f0b010e1509 62
    0xc1c400081d4003d0913080d4070900960305003207640e0315500f12400aa1841048040661100000401001e2943e000d004213985116548140304480c401c032900d042500c40e2411070701c40c60141c0b6244818410703010003441203c594000e00c003000f03038045090220092403060191503034001480c0810107100d8410001c07500c4002c2c500518440501141100a0040d8018600301038a01030a0140050043d110600541c00034401401155186551030003405042662032960010001c040d010340e00d000e0185202410380c4000a50051504610062002e5a10343c0403500a800c0e070001448040ca030441215485801070381c0140c2d40c1c0d107041400c180c0612444010003442200800d504050b02410b400507412584170301c040b10030680c2c4524106c0d542001d170b500b80724014580740e404500042e140b1182058145e01520100b400c0440441d030300103150b840070380210000707a0402c3e0b20041c111640d105d4040a81102030080001e082588006400d8083d69503055100d0310082020342c81d0f590130001110030075036019 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 890811232 1250 890809982 890809991
    0x1e08190302010e070e01091103060f0d02030c1002030d15030203121c0216060b0a061b05012c070e010608180a05030d0207060b0904020306010b070305071208041a010b0301140a0504 79
    0x10240305003445c00a008019005041480d0f1401c04401c0509a03030103244028801d44005a9802c1000000c01400308100c0c0c0501a82d05c1404290b5180800059040d10f0b5802442d900c00700ca4500c50121000c0a0509050341868082800983c4002400403d034013030101000b9915507032460140110b2a01d007900030065400094500d1855101e41aa080304511500c4107100d4011b4480c00c02c05000028050038000416074105801488010f59010705600c1c09400009001d0f80c488805030360386000c00c80b00f04801e1a40f0b81d01c80103984420400d80004141500a51000d0750510200402c4080c000d44011302c0094012840b091060081c8620f00d6003990080450b1340d41e181904809000e900500d00954000e454204010f4040c2062a01203226581c01005003c4d83e0b03003019407415898000c003405030308101046c0314510004081c454910040d111503254208e0700d180c140b4003680f1035541051611014a42c0000400641c0285130950b81915100035058501c42c443d003020405105a03507001a07480340c04c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 890812482 1250 890811232 890811239
    0x50a1b080409140610030b01030204090f05041e112b03093b040c030b0f1008010c09060f020a05100506121506061309020a08011e08190302010e07 64
    0x10005100302c40300c2050601240350201522503811508540f0140c100103020060345c1400c1c801e500c20300040d1014180141419243c0f12100b003181c120708d0381c070342c480b5546206100034001c80d0009890842810101d05043c50000c2c0d4a01d0781c4d4554001c402c2e40500920341c8514081c1c0185040807040ca0340c0100201c0c51342d27006090050a8841d5442010710000300c001981c100500c183c0140c295001031010051062545804030f404034600040c02501d00c0030401402000081c0c0440c459401100c002002e000c4c6030900174401c100e4040c142c4d100c03840c182c4c900804e0b01c03000340c0c0100c13403001218424206071102c8082840140e05003d00c6000041c500c3c043c0c1e503504154071203503511540c05240151821150544481141d907661090a0802101842d10a001030100c0ca40711005100483d801d5400340c900c5caa0351409482079801c03005c1000f001c6410300e80140111250300804541e071602c03817424006c100d86490041d946a0014000c0c0880c0c10544403000424103001350009c2c00441404030031104603981c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 890813732 1250 890812482 890812493
    0x311040b0c0a06060915030210050405060d0c1d090a09060b0d140601050105030c040b0d02040f0e0603060a050c160501180f0c0e22020102010f020a02072105070501050a1b 75
    0xb0454821a1024039211010868801600c40c0b80022813851440c2c0c801726095030200607a00980d95100e10400c0401c000104040d2504005840c112500c01c1007c918114420300182c6000240702c83c01c00040c50400903600b0581d40c0c0442c07182c000d089008001001341c40340c1054009845500d007250740060b0590040020000f8000c2c07841801c56002050b04da441e622000111205d00c01550010349a00e4207000c18088002160010311031004202c50040ca81551101494400070740c5074040c1a440c80e000040103c80d0606120181e070244c02c18078104118901041b0b90a00c0e8002c1005204610111112602c1000025840707070705c041d032036510322582c5590a850814010908604216424a9075000c00501c1600c5600c213103014100f580125041c040000480500001d903541c001c1e4115900e903582d60f010f40e54a8030052010001641c041c1842506000c00d60000b500c03502c440c40c00e07030600e2045104c08203002140040079100d003441d0030b0396107001c1d0b9802110303000041d01c0303001d100c5103500594408009 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 890814982 1250 890813732 890813743
    0x2d03090312051009060905011202090a1416020d03060627030f060203061002011e0c0e1302180102070506030a11070b0f01060815091503032b18120311040b0c 69
    0xa0f04c40c070081c0300198440d4901130588030b003032042c030f481504900c820000500d000690594070400c01c2e103000489035032291040d440020180d42401c500c615030300850000030307810f100304001d030003007803d043c09500c2c5403110007401c181c8030910000c2a0154040c0c850152806840d07490000d581090400400c0601420698025030003034a202d4420508200548101401070161455011805d01000c0064421113049000340c43c096080104008120440318020342d46c0342c114198a0261444c01a2148564501e41d42c40aa0584050f81036507c51481003045035103000846c0c1d4845820384000c02e4122259100c1d41c042c1c040c00e407000303040503071100400162000c2c081909040711440c1e580da4a080d1901500031003210b401500c1541c012582d41c0008480d82c501c4008802c4c0d00c20040c0c2140d14080000a80308080300611440ca01c1c1c0b0700d18132155007031001440c068145503825034001d40116a4295840c1c40d880108000001d06158941c00640c0624030444250340041c041301100e035640714180440d0f070362541c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 890816232 1250 890814982 890814989
    0x5091603021308011b080f0114040b0112020304030e28031e2319081207020c0d060b101115040203010b0a060c031e020d080a060f080307032d030903120510 68
    0x17900d40303030005041307804d0212140e0480d03c00f8070809c5845c103500024000501102409a41803103240d81144070003501500c002c51044c0d0080c0e0b1175143d600c0900c0e04001c22b00c04038661448000c940ea00002a81c130f060b185128084a51002c0d1001d103006403410303a0650124205d80241c040300d40102c1c24160a11100781d035034031243c64882600e00c4603005c180754025520041a024140b11010300c00b03200300e0441401660341040712801221800c0d9807440008442e40241a03088404c04d4449503030300000d040411600c0503c074aa420101104c1e082942d02c1e030307641d5110342e41042d003411104000c14155103003980800a441c0d80034100c400002d48440380540b081300300910440004200e44403c40e10705849600c02c240b440b0300359001d0101070031022070403502c3c140d0280952007007a0380ca23140050a000c00b0f5260b080180760f0280135545900b52030074060605c0000003d45030f402540d0b10a916a1840000c82da184882018100082d121503d410111a646801d07080c001803186000184501c4845440e00d1800300d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 890817482 1250 890816232 890816237
    0xa08060a0e070605040501031815200a0c0b040c09050403110d11030301141203040f0e09010204060915021c02160909050604020d050f19030905091603021308011b 71
    0xc94100200c090782c2c90400344107100000d1030170b020603c455842074100c1a0075400c1c0b85681985907009885014409003000300000409550380c1c4124492031095481c912241071004450741045041c00c000762820019440080500c0728010000d020404091400380141141180c200100d01e400e141c0a06162242f00802c6114031510440f043c0d040d2088003141d40703a4042c0350156003035900c1e02e01d4071140b000c8035a0501d40d0002c01d404000042c0c8030100090001050001030082c00d0b640b401040c00c440d503202038400c101d1a40108000d1015581019120f022244421240ba8801302c1d2031b1001c90034002c000d801d1049d810406415105c12581c001030002d03440b800c2d10409601c850f907071503030841102e81c4845e0050440d0004c40015000d80340c02d50a501115000c1c2d010740e40d20717000e4200d040d414422a10f11704406419500c00c003809040d4006148400b03044c060b9140d1070f890900004410011264091020406170005a000c0c143c050318680c0e90020400e080c003c1c804042e0b119420f0144002d2070b54103400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 890818732 1250 890817482 890817491
    0xa0605011d0f100516200f0d14100f0203010e0105060c120912010c0e0108090304061707090e040602070c05040905190228030210080c0f0703030207080f1b0706050d020c0c0a08060a 79
    0x4502d0301f90381190380350200505180300c101d4655101c201c1801c2001d030400c500d01075a0001c4084103007030f02407081c603407866a00040c0c0d01e41c1020f0f0300369164101038001a001d05024071011202c0d40700051031480038401d400f09a520303800c900700003400c08091708010070560f50078040310038207240e08400340450b02403003625003644a07500d030700f5038551381e000b81d1048100180188010031000008640c8482c0c20007254030701484a16264040103001000130365080710303002c2e800078925080c82113800b180d9001e4801110144100481d544540c0ea03100e0031038105151b45200c0d44030320402c55489030442c203035203003800c641c28141140c1d80030224074146552006a005510743d43e04211070740e200703051140c49013441070b18107820011043d0a6150320341003040301301c0601d68208000c1000c01d80a501404070b240c140350026540d00b1030403051440c0c4010614030390303041d0b0380005001d100c1c003a0401c040c0c545d240386603000140c591070700186841c5410f00c00000c0076080203605401142a00000c505039102d841d6400c001d20 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 890819982 1250 890818732 890818793
    0x613170f04150305180d2601030b101e03060c17011202040f0203070c080c0f070902040303020d0c0c14180406020720030a0f05150a0605011d0f100516 66
    0x810201751044817000e0b0700700c1140724000600980c828405051481d81c03010110072038443d401c103500420f070020b5840402c080204030030050301084140c060098550f40590360600200c20030f040603290700009003a50b0b201c5a0701c4103890b1181400303415440850740004035a5a403031465090113000007900303900071420300000c403500401c0740c004c5a00804060303441c480101039980702c100d4035400c00031504826018090b000b80c4400700822007040600440b003070059a8a1035850302170b20b03044200000304103010964032118081444040701034211250b2501d91090000e140002944450003040070590003e034020a000511000e580a064034500c41d40c2030700c4e019403500c132080e801d5180c4885d01c9580f55120107203c4c0002003085010f845450700c25812910480e44500108c1800714041300e99403500d59441c4c2c0100722641e4402801a2a072864a06844064600344007046000c411914690300480340d405a07070240500c1001110f01a8000c100700d108aa44640f6102e0502c00780040e40000a10301030140c035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 890821232 1250 890819982 890820001
    0x7030b0a0e060409150e0c0901050405070f05090315130b18060114010512090c0a060e06041e0b0301060315090501081005060103151d090613170f04150305 68
    0x11000d40d0075200760694569074100c10070028090501003282d840c00180d030000b02c00c07100ea000e0b030802c0c964828083c001a1001c1b01c00c1c0508944140d200d948964101403d0091660f00240009003030b8000340350140d41c950416001c07070b1600f1034081c1030740c05002603130b010050045089605811040d10544606029884110003004040c10681e4031100e0380e08040c004001e100076842e150000f60406041450510700c20032545200c0321403c40d6100d04541002c1c010104a1a00400c0100507028a0070900003c1e01a0380c00b0500500a6014a1100d510b04504001c009044180d4000003803000d0804141e50b580c6500c0000c01a00c0110210080440c0e203034008281b6400502585050b901c01d00010501c4010b40c1403410054040500a50b040c1586c0303590348400340a01081140241c510804100088c421194010700741e04401081c440c0280c21140610413103a1511500712070103600962280441301651524080600c6050480c0d481c0c1500082c0028100c4101c84440d1103400450300c04000c0c0c1c0d61680c259 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 890822482 1250 890821232 890821249
    0x603010e060118090b0103060902010822030c020a0323010f0903210b03030a0e0307120506190e06180f010504020603160302070b09010603020a0b041505160c0e07030b 73
    0x11029607030055001031210b5030646260800d052a0210041078103d03a503112030300b20707860a1304107803105a05c605002c025541c2241d009a0002800d045064880c410010400da6030b200340c01e4001c0030084a202c0080a40d6940d20440000c0c40c0c00c51b004c20829082c544060216111855516486500f49901503080941a104603001250103450f4211100c10001c0303840c0002d5100401c006809039545007842c1d031394030b003000a000b00440c140c85901886110708d08041c40c00c500c0e507111090720040c0b03c02c4500080c80103c0d085800080509080c12150040000c602c0a000310b50b400c15024815030040000607000d01607040140709080c005d81d880c000031f80d2506400d0b503604490181d0090010404200011180f403540d01071504585030040c03c000c0c1580c1c031410140825913801105070b44451041c0294900380702160000c001c0c005185181501e4511108a540156200c14041c014042041105280508000082c0650180d0401101512446050103200d01540c194001900e0142080302d0750401144 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 890823732 1250 890822482 890822501
    0x12090c090e0709110d1e091119050a0302061c0e03120f0709060e191202030f06150f0406260d03020a090b0f2101030302010c0512060d02190914060301 66
    0x1031161a200c245d41a0502601415042000300840c1c00d504004041071031081910003481849250000c0030b1100c10086070205043d4030f8800070380c60303032010000350b0780e10346a401c110390b8140c0e01c9603201c8040ca00706281c0000e40ea140f41100b50b04155040007004c4000c402045401d0240e0031845003910340c0051140040d02c03c540c042c000c6402c4104c00e0041500610084801c100010941940520980070308524442958049695501c1c1c40e08544114603042c04600f2400700c3c400d004140d09e107400f5908200d0005c00006950050008030a10350290300e5642040c4042d0a4151540c8108000800d10712041c0500c00f448802d140903034092000e48602c00e000703c0d0643c00a6075a0703e0b141c1400c0a44043e031a511a523150008068104400303002c0307510207401c0c01c090498080303406c91158910b00300030b800c0d940c401000c00e080110030410111200042c071150344d0400303010b0740c0c0002403050303c1c40031803000600640b411031904000900000c0c071a00c0d50b002007040744010b4000642648920341894240d810034203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 890824982 1250 890823732 890823761
    0xd29091204031a101a301306090b130317070e01050c1c09080c040203040222060306020d091a0c0a081003020d0c0503250612090c090e0709 61
    0x20a0f4154107040c1c414503034005150800c1c40060030765580c90611070740324507080315840c1180410350640e409071b88040c08408075140e03d0300d144175041007215184405001455444043c4c600400314040c0031030b6600082034184d2180f1010302e0350406c500413074440034011200300d0004958a989001030100007074050f00403501900c1d1103150b00000d500555550300102c5107041c8a20406102c081e0408039494075450310045500c0d1034417614245403041d4200b490442d00350b800342d401007041c4001a00c0d101441d2050812510743c00c02030760034038480e02c80502065800500028004166581c0284480d40481829441880b0915007901080201034076450112802d4440410600c4424152402018450303400310f4031144841c0f02c00e441e0303400074507106191201514921203002e006d2046040422803040f0180d480020909215008003100c0d9075500030340030751001c1100c0303040c1a00c1152410341144100300c1d4020b03a031125090f25184110010001c00b8402d09040c8100b030340000311031510744100005128003a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 890826232 1250 890824982 890825003
    0xa0b101707180e28051e0c0103110c0724080f0609040201090806010305060a0c05070c03081608071a1e060d1406040516060512060d2909120403 63
    0x81642d00030301c2020b00c4025a40583c2503050811444084074241010144c42c5800140640f403c0c20380c41c1054100b400c44103880c680b00550410100010481c42c4400246004500c40c03111032084e00c480e028041c0510054403c448011501c0150200c09032166044c40050307030070014000e04203e51244040da1500074150300540030400301c0c01d00328a595030281c010b05000400590716001c881c40d069090f40300307503020340020083c00070700020350140325411760307c5280c85401e01d00c02e901c0700c40c20112a488020131603a2300284e04444d00c0b10f4110326110f41e5412501d034030380310f500c2800c05144032001c40011508059440b80040d003024280c1180340f00845080211080c107070380740c0b000d000c12405400f4081d41e0030030001214191010040050511651240d800381000030643d1380b002030707010141d401410030701c01e06124200c0e0f071001607005035600000458283c0b407640894240040407007048000c0c41c249810500d442100501c000c01c00a0195481e05d044402c04003119986400e140220f020051494011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 890827338 1106 890826232 890826269
    0xb07170f0a0201050f25081009060306060305012d05150904061a0f012f01060f081b0603010506090114041514071e03020a0b101707 58
    0x103054114240006c100c000041d5580c42120070204040d80c0002160401019040c0000389050070041240c5074a07410111301610007030109554940c02c00141004100304c0c000c16009440000700d80e4006003c150340403201901026156100114040002000607558481c15a0140388a24400103da9075a0340410000f0035958070721a200d4500216840490390b00440c0490b003884103d035050301c90b4600d580c0030036260015541001500d600c1d015002c03802e510244a408252040030b0704071520707004001341d9403606404032105680c0060b0300780010000e0b420f10b00040c1c41047c405040ca0440f0600b21a1038403000e8002da031058240809445074800195002005000d01c0c4010009891609079591941c0070503080580c0d02e40d0201e06482c0d00002030620a0000d03541440e4030110030049420011001180c40480b0301441c1d07250030740400011044c060000ea00700840f0140d403403101d0711421 = true := by decide +kernel

theorem cover : BRFrame.Cov 890647482 890827338 := by
  have h0 := BRFrame.cov_init 890647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 890647482 ≤ n) (h2 : n < 890827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
