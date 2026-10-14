-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2825
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:51:11.801545+00:00
-- url     : https://prove2.me/submissions/4cb9cecb-17af-4ba8-8113-930fa85bb8e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 507913669 ≤ n < 508093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 507914919 1250 507913669 507913723
    0x9090106150201020705160b030613060b0c1507030c12091e1401050106050c2a0a0b180a0e04080703030e01050112050c12191b14091503 60
    0x540300000900c01c009800040c074546401c0a8000d40082e40c5c2900d50340940300410b20122824030964003a158508160350668403041c0a0043c1c0c00c12404001250702d9880d08045010300d014405000c2207003100e4010001c204480e0040035811201900680615040100d0011240c0d040040c10100800d10840000d0304036160030701d4030004603102503203d1a40391050790034060011750340e00c0900c8100400024000307a6a25001200c3e584100c018489403074200035148949000c1c4680082c1d080000740900301540e1500e003000070148c181c2c6501048400900080300c045901d0000c03009410080119641c180c440d14040c82202e401100610040c000f680004a01e81010300a40c0006503c02188008200d15a100e40e801640a15041c1c0182d500d840340300110461450803900410f00040c00700064034290384be050840b039448200402c00c80c0e008001c00c0010100320005013402005240d6040c03c1e03942940007909100760b5030009424450107403500529943d59850008400030241500300f4801d08000c851 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 507916169 1250 507914919 507914921
    0x1203180a0c0f260703030f300506090903180f03030406093003080c070b09010506040e01090807141c020303010f080d090302100909090521070b0112020402070b0a0c230702090901 78
    0x51004c0c0c00304800081c2941c880300a148c0312002d050b50030a0701002039407110010081081e80c200d420b46144d52080014613442440141400d000c3d0300054450141a100180000d0864010340c1001c3e0001e09200010030203403004c9101c2c040300500703404080170442000a0031202c404140c6501406118260b004540800b9442084440a90304036105224504081c241c56018120a5400c503200b10706055003144e25640601c12000342c0ba0b440315030185007002683d2410761141d20341d00311302c80358080c41c02a000226129041c810024025034003466a0f50f050070a1515504c159801040303143e40300c20003015400e600119502c0a03640c04481d02092112588030031150b03603109400030030314141000c81d58010003030f0005501100900021021004060032603c400741360040d50009010600210010000c0c2c0c0910074404400078000350000d07140c88034940b5402035045058824a400c0c4c0ea45001c1400710035802000004264001c0310b055501c100740701d84c0781c1d031140200305001c0d04c5143d810001c10002102 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 507917419 1250 507916169 507916187
    0x6071703070207090c1d0f0301090219030605010f06051c0e100f0c140706050a14090c010906141e070203011107060e1203180a0c0f260703030f 63
    0x1441581659916100600035100c00d414420701014a00300910010b8450080c4408010440c6e000c180d507113007003644803c0100701c441207000207405560750050040561111601401310140030320085852602d0741c5080d0f07044600590113000c100b034008005000160303005040318400c8010301d018080700d00300445444020411710f6034201e9184100705040e0311003c25a000b071001500241410001c1c00e40360002940d4070616010540040c0d0340030400100007410980c04560403107240e4000013460000080380c01044841034a6196131680204002d82040d0b0b072195401000e030190b441e00015000d00314102c14030a002d045140e42882250782c0b41c501d03411800c4026201c850340c00500a10400c010380404803066440a181031307600c0b5040488602c101040000ca11580740100c58010f49140e0340c0320f8000084000307514120149008841c9100301184012074014007410f0301500c550a0035103000c2541c0400701d080740310005105c0c0e030b04030400c41e2003201191200490390941410305142d08568030444174400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 507918669 1250 507917419 507917453
    0x601060e0607052b03110403080702090709030f08031512032a0a08090a0f1809060906050703020c0f0609070b091f0503040201110c0307031506090e0a03021c08060607 73
    0x90b4007100001581480c104180c4d200c0e0031038404101c9010b03418100709103449940406040300138100501c10040c2807401d040342c3e0145403490441419910ba9480a0003000c4101e0b050f00c0d203e1011081c021015045001108003680c112404003007841c215480380d407a80107400c107000368045c6041554171801040d003440c0c4483e060a60a84080c1c04061402c000140c015401caa80202c011000c04200e919100e01d9003826a0803840c540100c5001c5240c004c4090100c01c01c04858035a1200d4000c40092700328000c0c140218246e45000d030f00c40154003109454500380042920701640800e0130300802d00c04c041030710020390f02c0196040c1e68400511012424103810b2404401c10101c03041c20a01c05950310401850041c1d02c01d9030703100b021a5100b1981e5543d003800750903403a85600100310800010340802000c041c450844075001c58072580ea40090000c61380082000b100350b030000700c401c0080560504c20111100c00040c40d058004440c4c150041210000030b1070316001b100b001500c1d10034042200500d03000d001d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 507919919 1250 507918669 507918703
    0x30b0604140a0c08011203050f0d2403030e04230718030f053a121406040506040606120207020406050d12141e0f04080a0c170601060e060705 62
    0x2c100040c0c800001d0080c1c0c140800004d850000120b0001d004003850303d4019055902c40d410308081e525541126072004502c50030450766030240c1e03006464502c1c1402809418032140c11070143c41c5003006001d10280c0207840e44103030318048540002500058500a034448107448010b030a0f900d410302a00c0c03c4002e811103444421b0101c00000801402c11002c5160520580a0740c0500c880650049402e8a51100691a0030100349450f036001105562424910341e0b545080c031240000d40c4280000c48044080d03611039007002d40104a0b02c0c0c105402015009282901c0420415140180092010484010140e40140c00060030b01c19590b03250001400780c80020072000c841c0500e0300d00591112444040d00300400d207185d081d10354600c8100140c1c0c6072016201c4251a0700481e4450301c03a1320741d0142460302030b113400c00d00005c60450810811400594403411923804824200415a45011442d0801114603840325005028007075104c811000c00e60760954180f44c0741c0c00b591401609240485145841c81 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 507921169 1250 507919919 507919921
    0x602030a02090d12110a120c1a0c0d061a0a0807090506130608090c0f0136061107050117040203010219020c0a0503061608040515010803130b13030b060414 68
    0x40100e100313090801011070348802003e048040e44607a20b86125850260400d04241840680300303000700074101a043c0700d4040719a580407034060104406105941039031002e000441e01c903841c0295407141c60040c00c0c1060380c5940400081c0380c01d00c0c00b03202e00549401000688008241030600800800e405041e0040c965901e942d000821070101e02c0c0300e8440c40340003030544004120842800714014251400140c4484c68104000b00150703180340036660212564403280104e06900640d00c4c0c902e03149800341e1801a02034a280120007003106011450b042c80030b81069100b081281c1c0c0104400c100c854003410010443da0380c0d400000e0081c000d005114480c1c400717004001c001d04e5404034801d000e1010440300300358183d451700d05056440f541101d4030103080b00032019001c2580d00030040181d1040c810350840d42424114030081c0204002a8030a140c1603101046c0c000c40000102e42c40000b420b1585d001505000c3c0c0342d010b4802c00c08a1f0311000d0b15003441040492002e4440d50094102c50700881920449 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 507922419 1250 507921169 507921173
    0x314040305070e070e0108040f060216020607050c01020c10020d140f1201180b150c0f0f0303060a1d07031d1b040e0607020a32030a0f08130602030a02090d 68
    0x40030b0089414500103500417080160940c0201d03061406030750043e41003500500c0954540d8002d502010b034406c50ba102e48020000140e940300010b200692288028040080c14100003a2504c05000c0c542c1e0300c120800700c106800240e0000e41e09500d0b507164a400303205a02e00d84049101032082c10180348842030009000c41c0305e0715410240c28101d548000801000100741c0e42c80e101107038001d4a056a00150b401a00510802c200d8090081802054191101240d080a03100c0c50700541d62004c01c0590004000c2244070b1a010980c000100203074090405000401e07080b464048a0080010007410780da07030702c15070340407124400e07107480c1103c00b00c1100e00c0c0c600c082c009141880194000d41d0710450a140da41000d541020030305a008000d19002052104001d0755400035030040040c1c03042000540c40c1c0c80c05c12010f0368244051a000302c01d000307140e40c0c1c0d400b5040148810008500d080510860b842440f00303074003004d0140082250400030044c2c40e40c4810704c601002e0b03c5080b15080d03010900c00d1503501 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 507923669 1250 507922419 507922439
    0x1e0106030c08061002070308031e040506010305060f0714030a14100503210a080c1213140c0112110d1d100605010503011401110f06060307060c0f031404030507 70
    0x38451032902c0d007002c103a4942040150158000c1080300058118803c10400140a60301540d00300e4811044082030580e62002018403000c22101030314590b10000040060000500c11660042da4460662b04c0c0d40ca04042d01a100c00c8640c488102400c0b00040003d20701c0a0780e40c82150a850030030448456820309450045200c42c2c1c07801580d03c03a000341e040c0d031030120b080d000000456440c407500b854100240b03c6010341c0d20750741c0180411800c02003000035611000c0403030529407007030150b505584280301460a04001c60030b02c110005841e68400100001541c0c0c02031120400410241c101080c80321450406546501408210003140d9007081d410350f0400300405800c1000709500b400300c5541c0014051680c00741c880c64420540803400820040c0002841071610340744081e0181401c010080308081211320706030b01c088000c0200d0300580d040c021107180501400d0000c021510b08440c0786489505d5200c01c01c150200000e09204078500c0ca003c515240303c003910015a0841c041d1011940c0d41c0c45248 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 507924919 1250 507923669 507923681
    0x60a0509070608220305040902070309060e0402030402150f0d060308070201080c190c03110a060b100306030b130c03020306090601090c1407060c02071e080d21051e010603 75
    0x100350050540c0031034824031a00100d4819941d50000040d409203d9400720038214448409908002d010000407540d4081400205407440c840d03591407086a01e001c0004002440c1600300750300c0340d4010418040542c2e00c9a80c60031043d496020038a07034551480d0020305451260030fa00485240c1003200000a20400e08007520000d8000c1c0c9844200790390341503006d002c61182003810b00502c0580c60030150058850000c80140c54424200102600506002c251516405200459003191240da4048050a02030303203511010400c0e09080c0102c0d8210b0342c0c0c1c400d0303c04000340b0707281c0b04e10820102c540602c0b00c0e030402c0301e0007990081c05884071401d18070000c030b865541c00d000d056025420184641881031041002c1d2040e20244490f480c20726000d9034076480a05a60b803c980c04610a90801051031907440014004102488032049041c52506104c6404c00034904440c41c248034809100ca03554204001c90003442e000002000541a500c1165941e0f40c00e00d004a031010040da514008102e0941583c042 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 507926169 1250 507924919 507924931
    0x30f010b040e0102030f072601180f05010521070302040501080303041e082d13080c0d02010507261222020a14030106080f06010f0902040806150102010e060a05 70
    0xe000e81c0b032089010301c1c240d03c0107640c0075004040200008481340c1c410f05458001811410369000071800d8034421050040c0d0a80140d8210141240050405d200c80d129684003c00c013000c0030b000961410000076181601802c42c00d4441d200004140c0d80090103002c6140a160f00078410015941c4403051180d40380c004440488030405e400c0301104410041c08403410f40315502500340740c03500801c0c0d948080320401c5801903000302c030b4103024204610420000031701480c042542c20065514a080750003464001800c005900561002d002c0c0c0015036885021110035a4000c031240c0e0203071246130741c10b1b031161010b1007100141c100c001c039a03c03c0c00000c2d204164020981d071315070000c506612080d0161030201c01030000394807100c003102c10011154094061548208014000035095550344a0395003000400121742200d60411380050060040180e2105c025050f452001c60800d800c0c02d0130f040d41d5400107010054811410715110034a030b0300c00d401006c40b6449020503911030307080181d03204016001c25215 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 507927419 1250 507926169 507926171
    0xe03070f14070b070228080d030c030605031b01170a090605070f021005071407060504051203010602071e090207050d030506010c0b041e08070809040b1c1709030f010b04 74
    0x85401c0109000030b02009a60304005250328181c0b140e42000010245d070700c13001070481a0b039500748001080d00e0b480c840052002c0d0010f0039180c100d1890040888008902030f20034145440350600c500d0306c0004410400d1401c21514410607001c03080140c40207041d482c0c80b0f081e07403244442041250107482c0c000b0600903104400502c01134070341e031109503241c411194496005911440e10164400100e800c01c98100005040c901d698508280d200d0120360f1014209550381c0e51640280b204000080215401410b175024a280c29035050144c02520741680f031040c01281908040326441040b03c0c004030340003c01c6051004c550f01c3c046c80c90555140d0700701c036800d000464541000581030703501440c100d4081c164007025034845076446039074a072101490b4810011a9480c00030380b010026010500801c2264080c40c0b8041c1c03601c04c075904201c207071908100b0941c00307a42c070340901100c039070448000010403e9100080c40f5003042c200a07800d1482c010b001c0f5069251041520401e41d40034194400d032159202994 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 507928669 1250 507927419 507927443
    0x6031b04060201020c15040f02331201120507030f08120106020c010306090203010501090506160b0405060108010e0c1008181204030201230a11030d020301061119030207180e03070f 79
    0x1031a03101b08402200c02416107810780086100600e841c0d515861a5201289902031039003606007295005031051561405000d0b000071a4104a50507102e407500400000140369100d128076595a03445400074840149045c0100008070108030046040da1404080040d40482540e92410020f5a40c03201060f0640806d26001c400304000d8102d0003103030f05070765040c0c460a14051501c2d050189643c4841640300e8040c061090710740c00514505090350085000304010103107941420301c864210365030204805140d0340103400811880d1561840f88040000358280360149030388043d18030700316241c620f041c0c1155003c1e10b002901e64802c200007500c1900e00030398600c0d0f07510900740c6400710f120030006072800864100740803407040c0c13078880e82114201410740420740f414102215088401d03a0401e0300024003150886400d84000c9504004070510b0351840382400300640329a8501079210b0b260b0303005a42892413940d4110443c0c52954116a805034243e1040700c0e40c4e00118201010b0a020780c003402c96200c070b038030701d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 507929919 1250 507928669 507928693
    0xc111e010809122203060c110f010e060601030c0216080714010309080702040225230a03080609131406150d0c23180603010c0c1106031b04060201020c 66
    0xc000a50141c0c00a0f51407400f04165002c080c0c010000c0b141c548200c0040c40b0220018400e809540301030401510707040c0440b8400920740f420442007040205242c1c0c50981d801804074000900d50350041000c0c00c00003100105844100d0400800c03c00c94207003006286c80028040c0c2c0001900c0c1c00b01c0d10f090740e2109030710300320310300441c2034a5140101a090541c28000300707000d440c0560081403200d0078890020b103144804285056000c10903001594060505980b00c603071605c01c91402d958a00009015001156181c0d40113044d91101031701c890300411440b400142c040d40c0d40400420302507080113000541d01c0000700c4141c0c0e260030440300d0001c08110301041c0312075800d000e04400c0c400c039400003004d03690300e04000740300c0c1c040b00700f000e0074260703a00d00c40070b2480554440307084040003c20001c04000c034528185080c1400e40f100c000702d280420001c415110042810308041e00b0034060b080340c1a80c0c1d070351104041c0c0c1144080c5105003c542c0f0742d000a00156072074056000f006c0e4420403c0a80b22140d01030303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 507931169 1250 507929919 507929923
    0x30e040603030903021017040f050601060503061809070b0f070c08030f030c0d0603021002010509060606090d02093d0503030a20011b020706031a0a03030c111e010809 73
    0x41c0310003804144150002d000525200c090310601004518100181504028031103c1018050383c0c1510a0b490500f00c40c4140181445003501400f12410443d00c0c604000000c10407081c5841c0200e0440a01980132840d0484140034600040891001d0683c450002414404d4103902403802140c900042d6200040d45000110644200c80c2810380c40e542590f0b5100b800510640c403450b002148a039442a0101c0142c7c0d07021000f600c1040e07250300015a5182c2f40c0c00070780c60020085c041611500092201c0903540e9500d40820a82c2035040d0b507200669113442c8030250b0141c045800030050080e040c41141c0d81499100d612031135003031b035409005143c0e5507503d0a25490b031007011112000100155844440b800041e040c866038580c2c60b04c00010f800c054105003841500365000c0700300068100c13000811403103a1601500c0c0409005140c1c00306c18034070000015113418803621004040c80001c8040e0001d00100944a00e841640130f065401c0f6501108080301d103605200ca050381c0844d1240011403404900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 507932419 1250 507931169 507931181
    0x1410020c070f03030c150b13050f1308160611040311010f05091e010e040c0306050a3c03060c0e120d02210c01020d02032509050415030506090a030e04 66
    0x545c645a0002c40303c6e4940d00c224600c01c51151803201d440d060003400ea03840d0029401415800481700280a003005800840205070280110551541101143d0041112281140c14a4080d04c6441c500e880721817900c3e8026080110b1294104d800c08540042030001c1a200304462030026610b280e5590b060100c15182d6016a81080383c20100c28a80140401c2c00d24411420784d6a0506024404402030780001e0160759a070b80b034090019894000030043c90402c40b40c01e0001d8142c150103044c20070f0000b03440c2041806000c0c1e2107043c02d180d5541802881085034044006503400c582d091258021180000d4018000700840c01c2c0120040244004072620104440707152210541c060b01d8880507603c0305e216030300340f00309641004604c10402400d080d0024401407200c8402076a01584030720342010032403020540d8650f1101c004801781100903900b5444605d003016920304031400141c9020043c2c0503034100c4c129403c000c1580c45800c06100d1249400107030380e170313000388655039010020828400740000e49030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 507933669 1250 507932419 507932423
    0x1f08010806040c1202010e06071a09030702061206011b06090213060305190203100609061e0305070909050316030503040b06030304050a05040209030a0606060906090807050901121410020c070f03 85
    0x4100c0340c09104c110b82d070000c0071024900502d40310f24414262400245694440c05088a071142d500900402c0c02412a021a038840700311405107013016882e4010030344600c914100c0c0d1480407403400018580768011200d8242500040e1801078130074005113041d00041c00c0c2c1040c240c3c4161001955050821242e01405050700e6214000d8a421400324100081844194504a9140c0200e21044400040724406c40e00205201d210100e041481d050740400303201c10080000414030001c800c00d10100d000007514104075210400009089022410700d00d08502548060041c260a1603010740141603000020318081c900404101c4003d856034404c040d034038480d511401d40c02c1201c8440402091801d94060600c01d0001f07400d846003541c00341e4aa00481e20290080b0700410f00400c400e001c4c8075401094500074081100092440794205030003d5450b000500c212031905100d05d2a00080000e400b000b0503003010240304031107210070380070b074100c0103504480c0040e51284100580080c4085051048504983d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 507934919 1250 507933669 507933683
    0x30c1b03190b0708011415090a170102130509060306010510111005010503060a090b0c0d060902070c060f0801050109031101031d242e081002031503010b010f050a020c1f0801080604 79
    0x3c51800c595900c04d030464262345034420b4440000051100700c408424100d201d81d02e0005035243e402c400000c07002291070300104d001d0505001001180d84001402c1070540d5811198103088209082d41101c0d641021070440c611402169074204008440b80c20041c103a40d411010307100c2c95038aa100e0001296045c41c805095490700c2d02c040b98484054000810a44aa02c0130108034552244011420b991058008036115140c10030100711140e80304400600b110110303e000c0c07005502d000c000800310503007804007030019601d4680d00314590307000394052603c003e40d086d007405c104c151006859884112005107502c070401415188100700301c050710501e10800c03402c2d03190902d0044e00801d1031070091401458010f00e5003000302c0821800000c200d007100741411510301507540d00c0e15447c0c3c081d05206094044d40a42e041091420386130f0382146a484030b1000c1c40c6802c036100c0b50740315002c915082e000c0c601d498210300810880000c10340c64032049064144542c8800c81c2070b99940c010303540e84070700c02c0701e003e840c05c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 507936169 1250 507934919 507934939
    0x6010f080a050c0c121305060309121c0c030e0d0306081906090c08060a0b060a1707034208100e0309061c0b03030c1b03190b07080114 59
    0xa080d50740d114940145100700d0030f50504200c1c1061038500000ca020b0303290302d1500402e1001350f80003004034030000f404060360340504600b004181240d40d05110844080104d20100d81d40c0025a10742c080010407400c054020300020b030300d4200140051000e082d252100d805240c01e8945030900034002c400c08c03211040002e240c008503402c1070b0081035190901c201c4845450b07a2028006c1849002080040c10310324018215905210484c042202c03944a02c1da4000c5030305002400189400c12820b44801c0c4c03c18030421200e954501040b00145040000b00b400c840c2c01400e5000316441d9400f10444654640700c5181004607101e6400c02900030324030540d141507214144803000041190000760500708444210b030b06100fa140002a29900544800c00044003000d0304144800013600440c0c0c0d07200c1c82507001e149004202d480d5540c40311b04040c5268080c60b1020301102403501c1c10000c1c0380c2c3c420032104414503071003080d11740803114030f1050307601000060400c000425900e2205092064400c801070045010b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 507937419 1250 507936169 507936181
    0x302010305061201020f0a02070609180b121006050301050a0b0a063207110d11060f040e2503050f04020108040503130305010e01060801111e0d0c02010c0806010f08 72
    0x752000030401c582001002000d101081024001303000c089440990054030741c0f0044000900e0300c029503000c8010071807480002c00544c414424034040342550040c005c580103d402006c10106200140714400501c542c509050700d02000d13610140036102c04038001c1c02142c07a21420795040d1914819801d50041040c0d5041083c140200c1c1024100d4040244851000204440150310030710210502c0000f10000180b010400a00000ba04100784080f01e001511007016128808814501c083d0a1b01500c000074204101d58042030a41d0014141c910011046107800c1580c0340c80d01e4022211f41c0800380e84065800c845502078041c40e4451322081d03403070750700300e50f5a500111001100548160340a0004101c50031490041102e448095406030002050043c01d0440090031184141c1c040368059160045a00f02c4520703030350407a1540ca1918a074050545030710f40a442d65482040740c401a61403503d02c4074040c040d01034104119542c8580c03249207482d038030f210042d20501508064100050800000140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 507938669 1250 507937419 507937421
    0x18060512030a110a050307050616030219030b240a08060d1a07050714070510111b0303090306070e031506130c110d020115140616030210110c07081603020103 69
    0x7020348012000c40300c884004ea105c841c190b9001c03460a030303a02e4019504102410807044011541d05006290840c5016001c1c04800000d00d001c00b00d0204060b00d501c14441990343e001540045210f8600f86111914081030550085074004082c1c407022640420010781c0c607152007603800e00070343d0f0040c01042d00c1c12801d240007100020003d1118080c030805004000200e00803040d0303401840a008000c2c0002400c02007002580c1032010030400400800c0750510300d040310041192004680841c20001040441030700082c10350196915440e058800d800c100900994081d80d12126004c0503019528075184041c4c044000e440c0c101e90603500300e00d03100641890241c031940141c28504291515806013001450140e0030411410003000041c0c1d10341c95842c81c90181002c085000b040c0310222454686c0d00c50300820460300131082e41c0783c00014920301c60300605009000e000c9950751241000c0001030728101c103c4506400c450300c802241d128880d804101c42e800050001c500b154000b400111442c6543e00440c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 507939919 1250 507938669 507938687
    0x30604060b01090b030a0e0c2b0213050f040c0b0708070b04110307180501080a2f0405130302011401032607020d0524041a0702011518060512030a 64
    0x10b410000f2420000a9042c00703c005940a6070b640d540105807c02914500e40c9451591210184908040030010801019170f12840080540208801804520a0001800c2c440c001c0c1c02e1003001c00d080c901040482021046190b10a41c8201ca074014150b03255462a000e6000d1510001c0071028100010000318040d056840c3e0b01c14880c07044605c6500002d004039041240c0c90b03106a035403d052503c0f000304034002e13000e401d015200703c0000b8040d45045407500d4444204640031200e410189180703482e0000a0170000b4011f140015000380910309000c2c100030b48481c80c060b0b0a0300154030304150480106041000325040701d42080302032481c418405000301148041001d03505020004000c10030050720384e031010004003800b80000e04801f20003240c591210241c0c440f1070710901d1000a007088002440182052400001002d01c80740c03035610864183d0040c0509081400e1107070445c18009007a0841480401a0044001041c07001300d5455040c803121003da440401d03007076001801481c820902c40c0ca044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 507941169 1250 507939919 507939941
    0x14070507050405220c170a050d050c19050c0411090a0b0a020109020301061415070308070810030f0f05010b01090b090d02010c02180f0c0715050c090a060201061503060503060406 78
    0x2501c1d66100313484440e03044a030208030458003850b5501080100c8905052030002d880308581c003070821246240d40e16030b1212003c110b244248200813a01ca9000d04d001c0269031644000a0030300700b2103400e903003821982c980100050520803400e02582485e1404441d040d1802c0c030300301920301440241088078240b45500100d980e0411590703110141400369400340035400c0140b003040c000351040b80b03070380307040c813160000c0c04d218003a145030704020080000381c1c48501c107680b1611618090410f074940c490703061040c200591018000007840703d82c0005118115491281e40b030b200e04020040c04c01c44800669003c25988a10481080309000c481411f0a1a4012440841c8149021000c0511541c001004801110403500c0400c181504108407000c8040032960402c502c001254107150f800e80e1121001c00c01e84c1d603a0304c00282c80700c01107450000c650f41544d04403140109000c00d9079440f103400030300a160303a1043c002000209038280c0c0c1200d01070711850043c0c5001a02601c001e40d140d490f2900a41565422 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 507942419 1250 507941169 507941191
    0x2031903050c070b0306130606020a060902060d1a0f010815190b040f030b010501052514030a0f031503081b120703030209030d0315091a0306010e010614070507050405 73
    0x82c2c0b81150500421029140146400380c0f00e0401005008031618500031422a0500d007030420302659800081030b100150b404440858800b03e140b0204516010f20003070440c25a041c1503881c58500c1d02442220b50068055980d683e82c80380c2e50004689511040d1a40207c0c91401c0104c101d450a10101c0c1c0f0100e40c4601e0411080f0a0b0b403092681203ea000d07074481842c024074120b0070300800c01502400360041c00f09180c082d0030980c03510141c220780c0000d164500307168400b1100200c2000300044201d44c3c2c00c0090380950b40c54100c00c94000d0038140d03100d244c401c0007030b1404006040d140c00303400d804000e80343c20a003002d041100d8134254a040c54040c0515052920030718040c01494840000200805c500c290340241e152102d5409241c030f011030f20341141c3c2c10b041c02c20201c698180c0542074840121444050040f030500c00240740c2c100d500050803821901402804000b290f0084016000c1d412200307180d561608500408071146554000d019006146800c0304a0402051602e030304070079080440c06076 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 507943669 1250 507942419 507942427
    0xd0b0d0b04080301060207090e0c010e0423090c0d051e120403031205180a0201080c0d060e01290301050126090c03010b1e04020a140d0e100204030203190305 69
    0x140c0d44441041150300301c5a04000100501036103034103002e104004c00b60400188112107101d00b285865040c001c46542c104540c000c0007680a81e41c41d005038100702c01c10550509500801001c0c7c180b00c100883c0c02031414820100910a1410001035405410b42c00002410340c60344140c1142034901310400b070b0b4491034450f05449004010412006100a5101e41c844002d2605420002010b484004080c00304903000c5240a40c400000032030b001d8600c40e824078000215964403001034055001e44260404114a0540c0100e000c5102412103410b0354080005a8244540500e87c000029103002c0d03800141300c6c0600c010841395000383d03048a0685120b000060045815505054032540304a0300030b02c0325809607501650f01c2c00d0a00c100c0d010700801b51945c1c40c6402c1c0f01c00241e4071191219000500590340080c00c10034080c4610200e1400d030f040107160b9503551713062120303500280080c5c3c09040480c3c095503d607640100c0e202c1c0300321000c80341e001e0302500001403101c82c024002c41106900f038080c040100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 507944919 1250 507943669 507943673
    0x602010e0c130b030c0901060305060414040305030613020c070b040302030708071805041719030b06030601020a1401020d06060f14130506030901420807051c0b150f0904080d0b0d 78
    0x600d0240a411240c1d8000ac3d00e14001e41004203940762208400c148007880b078107100101e40d000c021a9032104080d01d030320103c0c40ca6111018000c0c860707000381303102d83e014489003c2000e0400742c00600c100d80c001c40c120340c6d04d561111815511403000d03114021482c5020401c04072031045981226a20901415140c01c05400c8001002445c0c1e103c5204038130117166201c0d410481c19010301c60509a69401d5030402c0c01c500d08070300040e5607600c00f11406001c141c4242411900d25400350101c505d00b00c4401700c103012071690380002400f8a9081080e903030104000400143c24804103400380c1e820f07040c601c0e94030718100d07181c54148041c0e680040c1c10500c4654803803461480c004840c05c0701c42424400701031283c03a114400c40225640404082c48045907a4000d5410405034200060304c0b403c0c0c0b0021190b50840144000b881e81c50340f02010001411588524200100c90b8602ea010703c2c01503030203880701040d2072071410130003070090401c5400500003001800380d0ad0442c941c5030b01040f00e00001401c149281c000513 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 507946169 1250 507944919 507944929
    0xb04240306030c06030e010c0309390b03042003150403050702090103051e060c030a1d0f061b070209041101231e04030f0b19150602010e0c130b030c 65
    0x20740004c400b03c1e403a40044240d2407002d22580000701b083c0d1604100c1075040b595000346070800c0c02c035040c200c0990003224a0b844c01130700350421802480002c045109564511040c500d581007200c06550900400344050440782594080240b0758200130043e03e10f03000450000114130001034001c0e010003805000182c01a15480c440a000c0d6000303000410704034440e45440f494004c540410548260080014003582c42417160030340e03802c074a003014045041140c91281511a401c001d05200041c032440082c8480d0550119100c0e0040003074540084820440c0345880e1000c0c0301e5600e009400c02c4201c00080c0c0420000601742008000503d00406294010f4165002c010300440c02021107150016000c14480c1c07201c101c0350b04040342c452035681407500c2c6031507220403620708200182680421500160380c00071028207204040403141010007010604d0307100050340b107201e4010580598600b00b10030820342000200d10380441002000444200128045070025080034030300290540b144800e1003444ea691 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 507947419 1250 507946169 507946193
    0x50310060e070c0c0b09060f1b010b010c032007080102040b03090613200303070804030b1009053705040b10120f02120708061e010b0424030603 63
    0x41000305055051084001480788082e0503036081c400200c0810700083c004038001400c40d405642c541d510744081c0400300d0194820000080ca0300540011340c3c200140b512260b401705c0c200d41c04020000b40304404019030304528081c4000c0d0101c0c2c400e1040c0340d4050301c82001030b40b52200c48030544021950354000e590aa130005e03080140004008030411460070800c000041e804101e41e55090703000300c204d888004a00c1c0c00766040c00c0000e10703203440050041e202001241c10455000810507506d17650b030300b40b00102803030030740d0f070100d803418107180006000c1014003525010381d60132039000000c00c010006181400c07429080600780210342002010300201148201881580a406942c0d800d00d01034880780c0d08103045810558605008615100204260000c40c6062540c1a14036138003031004400000d02d40000759025030394501c51042044087d140807942540180c0c10840189441d0340ca5800c52040b5001d45c1c052044522440301201040388030780d47d0004800c18403030800160700380d1242c40301d181d0160 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 507948669 1250 507947419 507947443
    0x1090f060518150a081005060313060b010f0906030902030c030304031209060906051c140a0b01022a061606020f04230f01032d050403020f2b090503 65
    0x1002207032261641c01031820324201e1403000c9540006001e895040c4010034002c0c199290b04012017040043c1103942d01c440410068400240034035201d1402950201c00d15103d4001141e000c1e00300a00000554003554a04020701d6030307500c40c0030700c031420007030218001e200c1d0000a980c90f1040041d80859601e06000500180d4026201d600b60030305c5206e0060601c8649500039010014440c0c020400149d028054a002c090f6039540100e14400702c0e4450005000a0b518074805840700409010742c00754076038007104506200380c00761078107400e4800401300b1460384914124041c1c201c01143d00885d1800c2c070024400c1c4032206111414140c05a00ca030300882e0010024400028400541801485500300c9a0309650507081e20072210030039403034041080e421040044d141496203034450030000403101c540840d00901a15800c0c001004002d01d4107000c1c5c40705a6060300940118030250005400214421800f2203071444415403080c503204c0714408002c0c2284502c0c04004100303a020905a40510604500310 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 507949919 1250 507948669 507948677
    0x4080d0605041404060b030a081e0f0c0c0a0902040302150c0316050c1f020309010f030b0d05070e0108010b0303030106120b0a0806090f1609090501090618050609010207021503040201090f06 83
    0x1280c60300e050006ca400700000944648d010780403900009080c10211120f6000010580a500109802c5484031b070040c200d0b0700310b2003100800c4207106c210f400207000300c110b101150030090080c0d48484c0c0c0f408034440ca000103500003541d080005494503d0100400d040c02c410002c0340c0c900242120b0300303200c001c04500d044417960414514002d031071609401c03031108500d40310004c107411441d00c1c5c0c0284d628400d49803044d060000c4000c00f091032600940c050f1a002d40d025000c62948402c80c5080c41c1c6403201402981c0802c0e46c03020012410110500c54003810079030141c01540346900304a0103032104801e43c1c0d00c041c0c00d99141e19110045842c0c1e81481070080400d04010480e50074440c080d00e09002203001e00d14001d62100460f600c01e072520125450488020031400078a400c21801c0060140140c80700c0988081d04104030440b8902039041c0206113a80103405440258940441b1503081c0c0c4107681c0c2c060f501144446868801c61100700045400610505103200e11756515642d03104240840c0d48008045 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 507951169 1250 507949919 507949921
    0x5060106020c060a050a0f0c02041112090c032505040606030603050f0d08011403070914100f030c0302060309100603150b12100903110f0106170105060904080d06050414 74
    0x440d010001082c038008201d64079030400411100c01002c60080307488100400500025070400b060161040001c4607401074024402240e6604001c041a448610262a03441c00072000070f5240c0d0003c10b01010119000303014025034440c01085150f4500b1051480d00540080000091a41e5451141100809072a2808100350f890750800904210410b1110b0b2842e810111481e050036a1029190707045d6014084041140100c640110b881c083c1243c10514003103181c50b0f0255051440420756a2017a03410a0b0100d0080e61111610703c1c2c9030386180300041980e005d500d001e0006143c1000a1644800d11781c0813124440c07a0f144c2104241c5089502c20f60b8080e442c0d481010004007580501020090141c500060450811703100390f55440c840300100eaa1160b5a0300d90301b00b05880f954081120441140c1201c942c001d1071005240204201c5c13043d080c010110381030901d401241801000c0c8120030003428845d1540c4c441e212200c059024055208100e983d81030041000d0f551031069204221241c444030f011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 507952419 1250 507951169 507951179
    0x60414191a010605031302120c0301090c0f0501020f1f02070b13030306050d0c03020907091a12010603180f050106050402120a050705070b07050903120f0705010b0a0b0403031b020d050601 82
    0x8507841c182c0160041110820820502c1c00c0c0440e0120082d5078140d80680c515003502110358282181969000d071b265003410380c050709006402018500b40c45102d040d000d10169170748010f80e9a03901a810081c5c1ca900300c11201c2210410203031204219a83d803220241c038001c01540d4a1040c41000c031060044910980f802da070605a0510822020388015142000e02d25141e0f1590740c4604410310000b40304075010b200048565200d01128001000c00d40c0142d018014182a5505550860800c141c0c03a400c035680005000707403090050b80c0f0403c1000344000d0b035848581c2c42c0c922200802205c150b40170340d00d4080c00107080d1158402404107564841ca03901c0b80d400c0c6203a0f0b0909641004d00001c082140611902c00031501580081e074008509007821662411100042030604071440d01060b0180300110b071202e0b408058070010400341c2d200310001c010710710051080000502450240000400d424441480040e0050b03601d915401c0c61001c14419126050b80080c54050f14440c08454a8100100400c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 507953669 1250 507952419 507952463
    0x7030602030f090f010e030723070b07060b0103020724060b04080309010201060e04020f011107030b04080315010c261c090312050103030e0616060e0f0c1206041419 72
    0x900461030b00001e021b12003100380d90325600e000312a4080c02d1031012070110316621200e09020001039400c5425035039010394800d100c0642e6082450107450071410203080c01c140790320030302c2144c4803560b018081da4020340030000b000e0b00d44030030502034581c20b540e01d0740040307039051068014100410071900103654030341c80f00c0002804d486040d84074810301c0e03c00714140401030340e506048030301c41d040070302c2c5c003900d05031189070742074501041c581c40609100018010310041c020040011403041e820b040c00040601c6094004580c1c208541001500448107580200c3c02003083c030405800040101d0035190801117000f2090702004110306040340c1086d6100440742c01c168015080d8040158110b50401513503146807000b806103450741100d14451040041c90300002501c040d8031381c82c0c4941108080001225801200c3d82d510110125400c41e0b102c5c3d02143c0b10289044022078859008890140440ea140c41d90784d402d69085403440d20f070707807070081402e01c090080200e828052058021080008108408200c0b00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 507954919 1250 507953669 507953683
    0x60905030604080d0c021f0c0327061e110a022103040f0206070b1009060b07030509060306031221010918030f030b0d06060306050a0203060109140307030602030f09 72
    0xa009401280c10000402c1c1808203680c88484d02180100b0011002074003203040880d405421185950140d00d446406107440e8005003420103662000c104d0144481d20210710400d8000b05500203910442c0c50f48002416900700410041d0100c400624a0102449450a403500540c0ea0300300c4150108400702c00c0f40d810000050003498006904000700b4407038084c60007030301c0010005014003d400011404544070001110012904188401c4290608400c1001c00400500c52030580030304102c1d0102c0c01d0b821600c110390000e035041e00e505107840801d0050001076000201200c0e4140510b0302800341c0d2130703c210000c10902d202e091203000080580081b864203800c06030400901c503031611a01610401048440c10626501404d00b4001091325800c110081d054010780150407a10000942040000c1c0c0d400000560348990000c3c406541c4080b6500c2c00c9000440c0c00e02d00103241d5603c20000b000d84450703101081500601500c800b540c4980b070f20016a8070680300740a90918010420905074001d12403c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 507956169 1250 507954919 507954929
    0x2100507030501031a07091511010b0405011d0405010b030607020d030c0816032a0903060b180f070302041e080d0206060a0b0a05090d050d1409030601180e10060609 72
    0x70042541151900d0f00360141e603481205202e5070183c089a03800d405406804000c202380c8070138001c0e00c18016002001c03100f0070340c51407078103600b84040901186400e0044030f060710fa041505540c03540c1102c64a14030100b004c0c10079100da5513074004c1c8100c035071030500030248902c155030000c049914513800000c0440c1c80083c0c00301e04000c164802d10400e01c0c00008114200b44240ca40400d590542110a0004240140c80080d040c1078580ba01c002c40343e000201c9a085034041c480070800d07038030349034140302c8040300c03181c844d010319115039000411003100001110b812204d00d03d0010708150300c4076182000f485007042e8511100c2c07c403000030007056004001280c81c1080d0b40c8068401418018003080e43c0d607106004103a00500d0110308503440394842c2003a07030082140100381041010301414091380313946103804500002480c02203c0800000540101c030050000600207129503842c01c001c4440d0400f6000440461640710448401030078410020703a852151054400901185400c0001d00580800e27405 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 507957419 1250 507956169 507956171
    0x10e0f070507031d04060807060207080c030a03180902120609010b090f091e0117070b040b0d091a0f090c03010b031005042303090f04060311042a0210050703 69
    0x20014190340c420709894071140d00d030512a50000280b00089009207507840600d8100345007a8000852900000d01070048402035000d0b24040d0303803516004d6850746d0011020a40507071000920301c2c0001e201f03048442203502001c10740b004039030311018103800307983c0b1403070740d5031188910340052001914040e001c0c90300418000c2000e9242555810100d4944000000aa4496107040001a075102d0a5514070030a01d0030b0440b5180856840d04800750300c1021101315491148689040403030160f401400b00c0e41601d40103046c85040920031541040900807014080322810301421001144c01070b61701c1800d0003102303c419482e00c1440e1080c546032030301002414062213a030512407001c00c1030301e010900700d243c600002c0c40854140e917281444184016039181d0760082c1801c0800303005c0b00c0e22010015200340d0b502202c01040a0020b8002c20091790383e240409001d141c40c94052500520b00781e400b660075200b849444003c0040660004103500c50944141303009030300018003880114440303220322135000e02d0390b0030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 507958669 1250 507957419 507957421
    0x3031805300312040506011e290a110c01020303481b0a03090905090c150403022b170706150302012006070c0305120f010e0f 55
    0x1900501c00204814808104070203a842072052540107103a11000c803011030f59906140e034000240c8050032107040d6520300036000003080400b04503988070404421804001083ca040c0020609202e00799002440d800a030040700d901e14101800203041072280c0794036901d40d101484a1003174205070b948000c1c0780c1107420800c1000721a440d074034040c400c0d0642080342c403044950b04041c951880f6200000c00e415201180f443c58424ad4060001045240e964101d545100c42c00c400500c1d90b1201c240c00b005011400c2110240702c5898254003943e80944010120b0301c1c05001c90010039603520030002c501d0700200c0300180a0065080100b40c1c00c255080c126203201d19800da001c600c015181c0424001480441603140b03170f102002c008019140d04a820030810001e40ca4a0010b400b4020414442213001c0381c01ea032508000107004801e122421560315024003420b64400703900300d0b071811070020100d003445814062a40090100c0060510070701100d40c254045506004100801c4103008005607241403600b4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 507959919 1250 507958669 507958679
    0x1912080a151a120a2702030a02010309030c0b270a11090402190f03020405060303030601090e06180108060109110c0c060d060b030f0a18020a0e0c1306020601030318 72
    0x981d400d001c50b14508115000403048503200b550398800c901040c1c44800a0505000c2203409a500c03110680070000b010341000c140816031000304425041001c0d500d40c204500b0300015502a0300300c10300c02846413074844006502c5665110151500b40c4000c0c0c00460790703030b40008480746603205002100704640001c05034540c5c255603080c414600e07108401d01a813200c2000c2021500c5014003d11040c43c4d080183c0100c1f901c50b00c1e04a251000c0d88402e038407840c144404284641030201c109d900070354040e0340340c0702c0d40c5041c40e50284c0f00080140c069070300b00700d00520203200380d41c1c240ca0b17407400307000a10085d08540d45002c080380241c4d2400354030f1000000040216281d86e990000340589680c80940d1455150800c0c0030031180207003c00d038011500410004104000d010007012070621a080306401046100c4a01000401c5984032060081d0841c2c035400061107580c031806100ca62050841e41110303c1e04070300108004a81c45568010805070388580014010103401c10400c03146044081e1010085916003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 507961169 1250 507959919 507959951
    0x30a020f071133130b030c0c10020403020f040b01050415080a0c0e090f0907030818011404080705090c070c15021011030a050a09060507021501050603010506030f091912080a 76
    0x1c0d880c50f518480c0001c4c0d003004889044c2c19100209054045640c40c0c1c81c01c00036000f9194051040b190300b82c060031068020071400d034030903035094a0b0094100c415141c00201032000030030102140c1414450240030001d0740b40e044010a00301a0001d60394003100c1d0a0015007a019030b441540b0b0741040c42144d410035041e0742c83d64113256522199030140364040c1d0f140d02402ca402d0840c10f40000c0c1c060000002c01c3c41c0078084888881c00807220a0b40c4800c1c0d040210310341e0041e103028030f000741c14280e08840320400062824a06154004a80c0c15185281c000c9030303510426940e005912096110b00c25030907010810360140264082c4601c034070f00c140f0001c504004007400c5840018460105681c1c1c40c0301040d00c0080f00e501198005500207000c005034101b040c5c02035070b6260700f42c0c055510400c68800100e1242021015607040b62409011203082d902c4200b4902001c02c00108001514815003140c0085026940140c1c4003042c02010410102c50804100034040740f002800c240c14141040d002d55081021 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 507962419 1250 507961169 507961249
    0x11010b090408120709150c11010e0a15120212010f1418041401140901060603060b04060804080c01090f150e0601031407180605030705010c1106030a020f0711 69
    0x40c84052280c84d83e949107080e6070b4040c3d6034100c6000344140800c4d840850f60420343d54900c850007102c46140d000c16080c01111a407450039462a0050500b01c000c00c10315201c03107032100e01100c060821824400c1c0c194200c6040fa0408a0b120b401c40b00c4010040140c204070b00840e00203095000740c0c2991543c040c401060f555210303407041c241403200341400102406252401c0e10b1280000000070b210359410040300e16143d00303043d0740c1d240d10b9510349100069541d0081c17041c2800c803105810031a007000c0c500b64003900c2042c0e00074400c2d54035040800014205481c2031140e501003510505641403440d01e542800806501c101d01c594080511700344001c02c1c0048005090b03411617500140480d242e181d0101000d08080141c0d200c2080c0301e00b282508030507001213400880130341d00d094040350036450752000119400e03412290301621100029401000c0390419100455014038250405440c1c140e0000349204294080780055402007090002c524041c038100308198101c20420440c110407040d89080c004040070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 507963669 1250 507962419 507962437
    0xc07050916081621051005060a0206010b0903160603020706050a050c0d1a0303070b0114010203040e0109050901110a020109140601080d08150907020a030f0f0906050a02010f0c11010b090408 83
    0x902c0c072958500c14811490f0036007000b00e80c0c4140c90304c0702c5410042c601030300c1c1c1602c0e101e0b260f451440d408100c03030424000f0b40b40410307400c0d402000141d1800d110300640340d1003061b40c60b8044c064415005692502d0007440700003040d0a80d0010382d0340c5080c3c02d0800807101d01a25203c503413820003052000ea45110020746980659030034001403840c00380e8004025039040000742d55014080482c2c210305104602828904035031070142f4286582500000480c1c8034400c50150f0409410302500501c89603190b40d00c040d40c40f0402c58000103083d140031003d4203c0e0f4100e0249140141e446440c0c402c10840d0188052a0f020407072030040c800c550625075640c3c2c5030b540c2405000200000000010034242544c9031400368840082c01014072801c0107140203444c0d44107004264081181501c013100c0241c801e481c0500e035140e080d9034a142007810800119030725031224003200111741d2600c607a00e44c90b01d00c62240c9040b0300c42039200c1e0f112403042034042c203003034400604900348a000030504100108803480222202c4036 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 507964919 1250 507963669 507963691
    0x30201140c1006080c010e040b0105040614040807033f14040308070c0608090a1a04030c1a060103230f0408040e04030e010905040b1003110d020c0705091608 69
    0x11841090051900b0390030b0b001d61190074280200080c01500100301d4402640302039850550384040c1200b80400d442c00090007a00090040000b008024402c42030404420a0360707610301c0c03400e03544131340e014a0104190070658040c5019070f030304400000c40817140032050a20019442c1641d00490540c0101600042c403c1c050020b8201500da482404004460186078030800a545070542400c10321801d00f0103010380000b054000010034004840052504030300c6602032400300c0b45018003140d8200c01c680c0a80110705020044840d400010800161f440c8055041503880d0b100c2e00d800800102641c603102001094081610513101c0d4081e01c01e1111030384001007090040d01c0740c4482c5454111fa00c41c66006440242e50b0105100415a102e0755108441000341e03140949103403102d04110858103a45c200300e910091088070542c1c218043d41002c9100b117000a070550502c404030b10001d0690740704840c00002d0350030490b0244207074901101000d0300190355503404c1c0d61000c969034010f41001c2001e002c00f01c4032 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 507966169 1250 507964919 507964927
    0x3020c041b0815040e0109060606020c0607170915030a09110a0e0f040201020f100203010603050105060f07030c150c1707020d050307030213090f090605180307150b090c0d0509010603020114 83
    0x3d600d507034020285002440000300031010b0035040400040096000d00340050017030f42c02c000d24914100f000c4e91007854122552451080803100c44c038410380d1040c0c0d941508080c1c802d4202641e0000d41014510074010140d02045074403141c035250115070000c6078081d00c148540702042c494110542c8449600010003541110030f070f1102c0c00141e28003010351194150f184146000d482c500146500030354125480354030b041c010f607602c503c1000414000c005c035003110076030f081c0040e0012a1080340d16021050040841c009152a413140302820307160500f11403401300300090f400f00c0c541080c54642a80c4490644043c107078010701c0200c024118440030302010100f5801042c80291241c01141034401448002030401c04003081c2d4100b0b1b000f500c0030b2001034848030300c1c0c2070000300ca84800700081d40203c03050f04059440c0c000c05648160310000b00d1030100c050181d0790f241407075891b183c010645000e0190b01983c1070702c2d014122100070594000520b12a900d07410f1800400042c2d800144c0a174038045103050310b54032 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 507967419 1250 507966169 507966211
    0x10e0c0d1b0803040e07031802010f0c02042306040204061b06020d020417010e0a02060301061b0203060c270d0210020c0405040c060f140304171603020c041b08 70
    0x7195400306410503441c03080400042d1030800100a00842d810020000291768400c40150221407201e06107607010120302080c5401503100b110b070f401c0120414146201c06901d1600403404880f030300c0d070f40324021111001d5801d18011140740b80ea40d102d00c0445080d49841d080020082086a14554080365206002c14902c02c1103840e40560b0781c18034004a0864485a603640400006c117484200300020b540390624000f040b510224040b407403035802420451450340703012021500502d030b510311021a18026851140182d4051151900403011911203d13215000000e05852040d41c40c0d80e82006003807400440c18280e283c9010f01e51000d030f011103514100d200b040e801a800d20704416880d90b40145001d08000410807243c81b0750064880a41d24032400c03145102e800c1e11040300303d04105405403020f00c00a400201b03c42d165955501014400d01d04001c4010740ea01940c0003020030450250b0000040c400d100d00701481180c3ca4540003c840354100940b001c4090080c204c0a007059520402519000304 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 507968669 1250 507967419 507967433
    0xb0d080c030d0513020a120c062109050714030f101d1f0515060417070803030f011e03080a0c051c030e070e040317070e04051611010e0c0d 61
    0x803040041030800d01c00f62610300c62100c0c40981c00e03001240311300308075600815400d503890003a2990320b5014035000515400c00d641035070018604100409100c4884402130584031072401620a494456401031428034109801c410f4540520b604190103a40081c4001e09041d9000070218908070400d6400114852200080706080300b04851151261107024070024480e120060700308040712003000208541d465208040310001c2100ca941640300301c09000c14001198214000c410555008040f1418655a003040350708613042202c400e035002062500411402c00888450070460179980060003285003980d5038114640207600c03541d010854100c0c0c458007004020050310314a050b0484003000e0201c02d041005020701190780541c1e0040c014090000741507445d60842c0f50103550305448002d080b41e1014214083c2c140004c01240403c050764500d00e189131500c3c42000d005505040220307074003a07410000940304900f2031140705c1c4641e1402c41003400d01403021981000c1d1040854503192441c016043c120 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 507969919 1250 507968669 507968677
    0x706050a080a240311010f0206070903170d1d0c030102070804180e070824040b2805070c0201080f0705040b0a091e0f06050721051309021c0b0d080c03 66
    0x10180300fa45500100c140300c851602c0b00c0c501c0d80f09981e2070f00c040da010030040b40c40d4070050b285100452070a40d810301c00108107280c0102003548244220741840820303050f80003554500084044d0303c0d03014022400380c400040c0700303104d840c030b00c00c0d0000d601d0030311070b92355841042c41039104081d186200c180b854400d111482e004055421010022a00059200d44603103881c4e43c240319024500c038029030180d0041100000c01d281c0702d6600100c8084045c4d90300d030070800e0307070059075203010b160134a40e4800c082d60b1a07150707c00c141c040c00c506e0343e50070042c0709588005004940050402180307a001803040200c40e9a200d0100e40589410204003600c40c0d01c182d00565a8401c142c110854141d0399001a80040509a010b2401c586800c0040104195903410640c0d040c46004005801d115004100501d18420100c0312001020070b494250702d0700c1d00131800104c044085812802125800241e1901280342c40d50f4290035000103240300704110100080015881d0582c1d241c0280901c60100d0041907004051081d1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 507971169 1250 507969919 507969971
    0x203070e07120f0e0d12140f06040e03040806460c0306030b0406091b060804121106100609050103060b1920030a02060f0c03060405060f040c02010b030706050a080a 72
    0x5c40d4511058080074002400502c0041c07200d03464540c00012005242c45020b00a201c100301c2d0103074039101c010610002e402040c1307800b2441d210400c0000b52501041004521422801c840e181c004461100d0f0f21401049200048a0121500300890b800103d080302040d0401902400028070065190090340030b09410f40c405024a4540006c22051000c540c000d02d941038800c940c031644081c400300c40c41c4402e0388580522400182080c000a0006015a612116841540c04c00402071010402031703d1408004681c000116040d1040402c400d68010002c0303c060a002d0905001e0f40d41442d240041d1802200b1400320340821602d82c5c03651031402229900030400c0c100328680107843e0221040ca40d03c0c0c0c00810188014450180020700303003003090110500841421495610759281c883c01c00024043c003074080380d4070145003a02c40300190740d039124601c804960303600003003681540c000405041101c1035100000748081040020503640e0b001904aa100349140310010b1460001000d204d2240700f82c0400c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 507972419 1250 507971169 507971173
    0xf021506030f1603021002150f040609020405010303030c0f09080c060318030406171509040b060f0306072d050318073309080d0e030109020604120203070e07120f0e 72
    0x103050380c20600703d0281601c2c002e407000d680d26081a182261782c2ca0000b10b842d01c080700c0d5036020510f904440f542d2a50024000d40300420340080300e40000d800c8030306c281d10840100345d030b80c60180b810320b0304031918207030000e580e0401041c60381c0381c000401c1c2c132554083e081a1241c01d0010004180350f8402c020140c0001024003207030746807900c0e2000500402c03405030181100079000b50008000c81c401d003a920ba07144801908081690f21240e60300c0140301c02c0a4a5183d0140e1814070108070f948040204a200b98070030750b112144c61107000c01c20f001440703840105200300740c049443c0441c1d00d40c0102c100c903041807810046d0380303424840c0340180703046c400310750001506460041d0010b00c1151707030364000d07140c0c040c415228040202c1d01d0b80310584045003533200381481e60300840740300c00e0014040d200c1784100303440207030012416034240d0380019014ae109411111943d180132045605604040000341c0c00340c140400f43e00001d040001001e8004904010404665501c0d807000c0d40301c00c0b0080d0801020710f0504c4003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 507973669 1250 507972419 507972433
    0x501030c12021c14100612080702060918010513020708030c1e190906050a09051302090a080f06011d060d03051612020c0a140906010e030a061b0f021506030f 69
    0x2a182e001c4d50303048081c0d004540318400f24030300101030328818041100c4100c201e041d001c03141c41e5550f00d2603400041d4140d0303118105121100c510b4561465554140d03241d6000c402156040c1402c100107841c2001182c1655032050005030700040b2507004132600700c444910000d4580030109400f12641500b101c01c0064010049028130140084040f4080c0b0780241d0307151800c1454031160100c1e100e01132000550300180c0030040410843c00e05580c0740c400e4040341200946000c41c014049080646075500031066a404100194408501444024054402000907030300031000002682d04980c0c001d0523881c45143c40c10f043c201014010340480f1104e880c00749803c410b4264600700101c04103003840009015009801c032074511803824412441c01d45091176103464440d15488240a840c0b54018480f50500c40c3c0c069042c0d0003a50308203d8050103612a98002c10100d0183c031040649000c0e9601071810f1101d03045000c1d00c400e401154444040e004200d82c42c003281c4d26480000d181c06240e0b20700c801907010f00701c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 507974919 1250 507973669 507973673
    0x3100308040801050f15060904050408090a0305160b030c190905100f0906090612050c070606081b1903060e010b04020408010c1803051e0708060c1c0501030c12021c 72
    0x3402c013034880c50100031520307140e0395100c118032484032070240360303950052040000301140d10703180d170040b50400e000320801c0c0e0900704150042443d043c1d454005640c1684082c414244c00043d004184001e804c8860043c1d0650914041256441c055803410101c01c02464808001080c86168200000c0200808100551800d007102503c602e2080e9401c200256074074a02040141c000c008040072940c0c00da44d100648090012207800901001e80b0b4001182c10030071200b8085030300d600918000d072603140080c04c11900e07907400602d001e010101100d801100c5480100d46d0607645406507104494000d86d000c5000d43d02d00220364010100c068200307600c5417010030b0116074494150f200c8034202c0d5150b25041049011001d101e180071081e4400202154810301401801d054401c40da40d0045100500f100d0f1720a440d4a110390500b003081b1090720b40140c0c04a40d8000d0910747e5004917030400d40140c1c0c02c0100d94155110302100790170500502d41400d0b0a56154011921032417880840d44101c0301c0c0e0014149054 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 507976169 1250 507974919 507974921
    0xa0c1509051c0503180f01090e070c050f070b0a020f01150b0f09040f0501050a06110d0f05130308120105010c0c060e0112020f1806280917100c0306030b060603100308040801 76
    0x17001c51501034554241d1050555000317044440c01e59030441c0c120080d030781d00c0010448800e200c0d44030845042c00b0380074012602c1c880c20021000a816908155529030381820740c0286000e020130880d0345168140401c2080b4003000d5103c1d6420740724070780401a51048103220355159031003508001a081351506440203c049450782c41a03040c0c400440d80b1040440d9140e20843d12000c0c22500380741c4c3d81d000342c043c0841c080c0c0100c098141d40c6126081c0700c1c2c1011010510410444062340c800ea5940f0000900400034010031502103014110900380f04e491200d8584950120108500809040c000d401280c0c03070b0141e0042c0048110544055425552902e02c6000d800083d080000a08941040030f4184c5e610b6240c4481a24242c0480c1004194540e065019014501c00194a00c1090054420000c14102d81c80c0740f4400010b002c600080102c240700000210440e1406142c0b0002c00d49896170500010745030507411a00144100c402c1500c03916642082a12000c4551000b8402000050002016001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 507977419 1250 507976169 507976207
    0x7020f0a111905131409161e03140304031a01060c0b070203220503010b12100207060f050412080129090f06030906071119080c100c020a0c1509051c0503 67
    0x1454007140d0051b00c8043c009590343c010007002c0d4025101d800340c10700079a0010403407a07010b6640c43d0f1003090000c2c0e683e140c2001a0010900c809442d41000905005000c422140c1740d002c0030a0341ca04190961400000501140d8219001030181c07002001140002c3d00c200190384800d03c0c8200b204000301c1101d0000c0125007810300c51503001c4d50900f84094510720301100e40c440e90844083c05420f601010884420003980081000c684203542ea0311440b800f60070511881c2d1055224035041c803042441010064010700050303003c10142030340754070081480300d50351201200d00a94200c2c8561030719000400580c2c00020400183d802040100820910010004d40d0320302850881d240c41e005040b00b0103d190302d60070b52400d0194405840b554103c001552540140b62145003442942d1590420321030100607034020103004801607101d18a00c0c0305200300c00c14448020400c02d03a10181c0040003c4001e41113010030302c185441100841025402c56500e4103198200603407080c00d036a6142e040100355401401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 507978669 1250 507977419 507977441
    0x60f22060f021002090f0613091a1f0219080403050607050a0f020c150d02130303020d17010302030606010804020d0b0f040c0b16140a02120607020f0a11190513 70
    0xf0681902001030b00452088529240025006041081050b014400d5030b0303100c100c007421130b21010308000a005015104520040e2904203845013420041c0c000c02001010810000c00c0d403800918084c14683d0300010011640328400d0400341c03002001d409d00075094040d580c8090450300800080188240d440750042c020340040f07440344c9560307135a80320b0203c0e1385000c1100c0c0d2039041488504142d4000703689101820740540102c0015241031100301d510724040c1001c2d4001c4001d6030250482c200d4158000d00844940366045400000b503624580001c0d5645501920a0f4148181c0c2d0008c2010340d2200320038850001d0300000c5000040c01c250000003a0142c0444090351401200d03140400c2c02401441220003c10201000003122000341e04d83c01811300c0c0c010702c02840c0c1e01c14121180010380720044440c41282c01d90f4041c14091a200f10041d003000d004d2003003203515800030741d00040040c5201d4400703002c1030400d441488070486508051158070352550006a0700080f00b12040f0203c905031303008462406 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 507979919 1250 507978669 507978673
    0x316060207260a0e0f0301020c010e061b030402100c0b090703020907030501080309011103160c030c05030d0935060414070803040b0c1002130311060702060f22060f02 73
    0x1c0014400125940c00b4216000301481c00300400307000381e0302c10103807022134103402003e03c815000c03c02c000070308a90004440d00d0042c1d44840c0c45541d01c0505001c0c3c40d5101e008039120717034000c52040e001d500140c40000d02c02031180c440f070011038245510841c0400e910300e0348401c050407182810a50b45689000c2444200d01c50800100040c0b5810320900a4904030f45a0500950030300000000642e03289601c0342c02da0007107100c14442c00c0e1000300c0040d11110018041e00e01c0084042c1541014449140580c201c00d000381c0c02048108500c3e90700000d80e4040f6140100c0455003851039007124600e980c2e103441207015101585040b4580c600d4046071030f0340100e100342c2c41c0d100c030b00914141e42d54443c4039610031180c20780c000b80810010414000020000c2d1205d103010b580c0c00940c6020341008981209401e080e20300c1d1400320a000300044610903e003201000c0312030341d017080007540c00503400340300e6000c100100b11008110224038070000d40d2155101c0054198500717100343c45080041c50403c080715114014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 507981169 1250 507979919 507979943
    0x403020a18050c0a050337020c070504020702030705010c1a010b1803010c080705280306030507060804080313060e0105070315050d0206070609051f15060513170316060207 75
    0x15441c0e00d0f040391440100fa44610342980d0311858201c82100f601032025500b20000722a40841d13800071488003000003003000c8016240c0e0b00c02c806491901e8120f400c840d024a10402c88000543d800003005004c4074024680080c8403025484c040078104015501121902c0701b0f18004078080641501404c040302c081c66041e00d00c10715050415003602c2d25500c0a5000c29007000100302030303030310600003800089036107028020203100c1407410f009004d00601c43c0c4000640d807400103104104051003081e00610240c0b401c0307002800c00b91a461200e2002400342810026280b0541d0200441900032036034800c0708a000b04454038100d40098007406418400007248510b4500218140c50a0002d00512940190a044c10900e50365202c4006003c00c502c29115032103600810307442d8640103001e0103200b030440c40e0081041c1e903c0701070948203c3c0e400c1c3c0103d030034031105002c11001c611102c40c8a4085880c0c240d0072031044030015108a0540c03113208040954442c01108147c1400010f130000e104052040c40e2204074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 507982419 1250 507981169 507981181
    0xa200105061315060e0d0515010501080c040e1609050d12030e0102041802030c0408060103030f0906030e030a14190804020a05060301080a03050705070f080a06050c03150d080403020a1805 82
    0x3c5907100c2452000a203400402440780300d2003003544040b5a040a00012200c9103070fa11454507110400b04400366a000110051005503806a4041e4001c0038215085d81007034180064000b40c003600503c3c05116a0b1825086134a0703510561000b0014100603102c3c0d1325103100340c02c0140b85049062611804030b420051968400e000c14421102294401100000301c07100480e0f00340c3c0650b2010305a500700c0c010500c00800c003500c0a014241c000c500c81d880b21070000c0701101c0d000e488000603610204c2450b02d0080400755160003c82200d50803115844d15040210002241d181c45008540c403480d402000d2003d010354481e002250302d80158003c0f04c0c0d0740c140c0c87ea904d04200d19403000b405202c10507004001e10741d00007405071002d003514a20440030340700466120881600031039000c1e880840310354018070024043c003040c0d01c10740b9080520340000a18510304003d1110482e001d041c845030290503820520390612030124140c0340030316402403c1c0982141d032000c44d40300c80c205000e1211012445c11001c501 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 507983669 1250 507982419 507982421
    0x2a0d1103041d1f21080f040e0717070e0607031e030f0b03030c0d262401090308030c0c0c1c051902130c02010216030f020708060603060c0a2001050613 66
    0x104591400b07110300303e101d4080c01c2c404511381440b0320860703101c0000d03c003082c40e02c4e12940c081e00151800540720580d030328003410001c04c0a0300407564038064041101c140a030690740700b80a603049400550b6096555051450210381040360003511946010214042443c0960b1540243c45429000e20042c0000c001c06070404d600c0c0e1161180118040c0d204481e41e42c40036000d011a2508030050a6030b0301040d000c0d81c4a18528103800702d99540c00320300007240490007040c020f008408c45100030700e00a48601d04507a05d00c16107200c094408a040c3e00c0c00f2494042c3e0300d00420024043c9140070349425000c02078419109032150032854200e40d00c0c0140919a0f10400d54072200c080010f40090120315400c0d10101c011009240107411842195001c0101408010112003141d180c0381c4280da40d03034448444130800905041491304800d40b5504080180051950b00054190f0414010f0307414607a2820046021344180ea03038000254101401060305502d454419400740744110030a4805501e158107403a100c0e0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 507984919 1250 507983669 507983731
    0x70605040b162c060408120307110303150f031e0a0209010e090307030e0402090306070c2d060f0b1216090b060a0c0c18022a0d1103041d 60
    0x300181d00c2807000004110f1403400140302d80d80090f21480c5442d8885541e40e040400b0180d901210355000000d01c0800c0c1c0d80f00c544c00d02451700100186086040007035203803440104da0300c521440307801a04070024140d94203010001540303408042d49501041c0c540340303650319808843c005910842c4240300002d003030f9101103400c41c42018403d014528281140d81e0980d045c24820303580c3d581040d800e0151718042e4504101c95409800300d52900d90b0a4a080c0ca8180740d82d035415509000f0004450401c2450b109041c06100e0b40a94441b401042031140341ca888002090340b0308409074013428100c80900c5091001c2a074900d6180910036408000703460340c18400c1035411b00614660404020424101220300c5000d11544007445460000382a650301c9078248206280220b0300e0625503170008a080a003900780d8100d144c00c603091203001c0c0303100801640040c1c840c0c01801150040c861925901401c13a0000d000300e0b8007400e411941890001c100907000c0912500403501c50002c6210310201142e0011030703814603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 507986169 1250 507984919 507984947
    0xb13081905070e191406041a0109050103050c0c0a03080f0a090f1b0512031c15051005120705070201020f060c0a03021c0212100605070519030203070605040b16 70
    0x10042c462038200841c3da25000240000591565100d2080c40d0b0440c90080c00002e00624500721818101013003004101e9808101c0c215101c4100c0801410030790b080854403085560034200011070350b07214541e48507a4400d40406040c0d034003d0030b100c1c804040c2c110070703994000c40b4103003a401d400350355400b5074008542040d02d01610808541100d540010480e00082c90b01510303c4c3c3c5408911541c0b1400b003914105946001510f642000c14080f10360400c4152001c44001e80c880d050000004910b504240d5400da4041c0d240215140c030120301e4550300030021164049071451130806c492502d050010040d07000320404074010300070707482400d00b41d1000081860149500183c52813605009050030780003540095840c0381d186142a21075000c6242e1032015019036080c40c5441902442c144428005c1c0c06e1313058014405208050024401281e400142c80c6410b41c9901c079441d5108869040c107a203940518a4014100303030404040004000e580e141d150b001d030f455014460450f090b03003002a0f950750405814 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 507987419 1250 507986169 507986173
    0x60b0a0810140d021906020f012403061d191a070e1011070305070906061103071106090916030f1802040506150c0c031207020904110a0b13081905 64
    0x5440c20900d0716420f1014200c0c8003c0c040c0d4030f40701c1a04000c071074007405039102c0c9002d41c1000c4005142020b013800b07660610107020300703a0b280001c03000d8404400c0d50110702020f40141d80e1561920500e02c2c48203090007100c0c940030120742140b07040003800c583c0a000403004451f881c402d900e420306118642c410060207481c0c0d945840b0f04000e445030038807003070480c0c55020030100002c511400300740d42c8d02031048001441c0560060000b003810040b000060711000e50068042203030500600d400400044152354440703034000030074281501c0b8070000072218010400c055500410341c0091056107912015075414030f82c91518240429000101c0782e03c11140001e91641c00040a00d14000c010b14240d4005d5a00c01d0000380703200003004003076815500641101d8043c0d00c80e40d000d1520240f85207030401c034205100401c20300b6103180020b2540403400c10800900028101d0032042500f0906a40303c1d40c503640030b40f600c80c2483e62200400300101c450100d29101e8500c0c68050036044070140c005013011200c3d40750300200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 507988669 1250 507987419 507987449
    0x210903010c08060904260403290f04060e0705040203071d0405190e01090807151113030803070908030d06031b0e010315110a0804120201090b061e04060b0a0810 70
    0x2c80c44c00340003003513005078026507031011506c00400c0e03480c001e03201450050b2060b0030840c0b1140e025288000c00744104401403143e4070100400c00c41c0e00302c0580d500c42c0c2d10000c04074014200030403844c80d1031019003005611500100c208003180c4d0380455080d009900241c6404515007410082c001100c0007902c12844400b03044003880c3d500e0000740c100004035400b00000003404201603c0c1c480d00d03a04250800c80e0040300c0022040b59507603a9000d640c84010041078201e1401100729030909010380103120040c240c24000c030005410750300441c3c044008241001c1902d40c0d8000d4460b0403030061142c0d02084035084002500b804110004c0c2d084107007a980101c0c05101e8a908507111090074080b960103074081c6503104c1d500c1505200c1d002010f0800d1080548540c0024181445d081512a01c0000d40d1011a854507400e400413032403104105401c2241541d0f0044804500c3c00702541050312140c41c281c11034209800010300840300001410301c0c1100f5500d205807501c3d69000101c500c920740c8540c21090381012 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 507989919 1250 507988669 507988673
    0xc37060e040b12030301060509120c03060a0902180702240c0a030b1c05010609050c0702012709020c06060108071b0602030a0e1006090b0117010b0c210903010c08060904 74
    0x680440e44041c001000d0500000f680d0050504c1c40d072091304510005000800c18060720706182c800e207285044144090100c0140c104082a52250010021002d26495814000954032070018144510604c031900c580c903403a19260280d0f41e05541070a8907051100c0441c5d610b0050190464240559100c0404a262440d0b6800450251141d0300000b0780c030108120b8410312040c0030300b0715220003501c40d400209080349010000002c41c0d10043c200c4140400400c40c410050782d10108900701e80000c00c1c040c40322450300a001c00700da01019044024210310008480c42c46600000e4041c7c8110400d0345c42640556910f1011079003031108803080071010300000b41600c0051a541c0142d50301400c07140e0001203800c40008410320b080417070380120050640d140400d2049011313030701542e03000e07450030308112210000c0751034001402c0c00140300e500001e45020405482414042c0b000c0203115008030100c41c200384d10030302440e80e00c1d8400011780b03200b5803a0204205005000c4c440d80d501c240001002c401310f41c0c2c0c6513 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 507991169 1250 507989919 507989921
    0x191a040f02120a0c03080f0405030303070c020108060906010e100509040f020c0d0c0f060e0109150507021006050f010e0d0204090515070815040207030c0b0108030403020111070b030402120c37060e04 87
    0x1410703e5601003070184001715275510300f0800b842c407940c0d59a659500300d42c52400058881400506000d004031041010000c0503600501c113018071001c20b40e04031000c041510402c139030318002d00b032006500a04145c10021010f0941c0c0240100340c2c6035034256808000d02e4002600c890000d00c400030425240ca8500b600461602d501c10046a0141e0001107290000f030b58408207023030340c000d4150101c3c542d00c009211007264100150108007100342008c02c201c50070000014517418800752014100450404c01e0541c548842c41380c090301e264098400d01070304015181c15621070000c0c02c0c44009a100c2c0e440090009480780c0328180c015540c0742d07011281540c0c68400c2c4806540040c20580034003000300c01040000b1041d4882d14000e04400c0e01031510380e82544001010b8010b03068041c0382e50b90001206100c00d02d0814122030304a46e04079010390744140603001c01030411900360b1441d83d0010045d100d1001000d9802c0008203030b45100e000700c1c010307403030185030801d01308010707019002c005421109045154201 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 507992419 1250 507991169 507991177
    0x807080907030506010b04090c020601031509020f12010c1413050d03050909010e01080c030a02030613212109121803060518120a02191a040f02120a0c0308 68
    0x100d40140d50403561603441e2103280c41000c0e4824204900001010001c0203800d00c10504410054070292000d940f40d501e4411091440a110b607540c255201d100380d0440da0344007009180500090315086804144030303626030003882d1504102010607031802000c882d07941c80000b25040c44c80b14060f0400014181400c4c48502100440120107002c41040441801d54592400a000f0082101c84819960405a185050048540391076004c0d612895901005036400300724107a105900708606d420803075440c03e042e1045001e84550380080d05c19004000200c682c0710038005061641d1400c0340401c000c8225283c42140e000307920103031000d96060307900c001d038a100301c010030404102500c0c8034209a44070748426040312800d88012000c8040e1000c00319583e042440110346c07241000318010300309260810040d440382c008800181c80c0b008801d11000030042244400c0c042100e411340120024075241c41d0800100c0300c44042a4450000d460080ca80140c0005103010015800304004800700d14550f2041d0072a04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 507993669 1250 507992419 507992431
    0x90103170310120b0402120a0803011a1303030c0209130f1104020c030409090507060306060504150315080120040803371206080102181e0a090905070e07080708 70
    0x1c1d9407070000f100c2c0780c24019030720014002c04140c2d2071810140304110802d0a0100e05104540044207400d01042554040c3c03811540d420381e0107010070803200d19140c00c52160025120f220039180d5808014141d0184050860f02d01c266190744094988034942608540e04010041041d0794204060700098885101c10380031845c058009401e00742c0c05030840b402e40e00b0541103550400e954850000502a003080650018012410204042070800b00c008201d03210758000e0360351141070411401002d61081d444040400390580f00408050786440440340038002c8100e00d1401a41280440b0002030303602c204840417150071340025840c01c0d404900e040e0b02d0b902c100c5403006013188a401418a01e9141044c6d111002115a4030441d07807481040140d03040350346136082080660700c180a035034014004200901d0110314102c44100c1d034400321b2058030404081900c070258003c90a0000003a44400c03a804c0124114400c00a88450a403249200c40002408035000c9000441030700c003050390a8050302546070840 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 507994919 1250 507993669 507993691
    0x50c0103050c040b13030c081005010b0a020c09100506070b190b01210f020a0806190302011704081b0f01060806190905030d0c020607171005010f0210060f03030e0901031703 76
    0x20b86d607444004502040754000a800e070005414030000c0f00c040e1140601410110196900f00405c1d540001d65172004003210601070700c1d01e640880c0f00d00d000031020400400000b000f8039503400f01403a00c190020f00c03c0c2ca826683c81003442c043c140700c0c4940d0264004041e03040c2e4907501c050720031401e0040b035501440c4d0000340c10351340c400021040003091b000801140c10079440c3c7c0c0072503041c0902446800341d40a00718091118002c801800180c0c3c1c400c0641c0c484907000c0340800b0203a01c4a041800c11403140e1854034019001090440b40030b124042400005007082c02d00800c075141d600c0b41031948a450803501c9003440d820101c3c14258461280c0e10104001c3d0080044030300f40030803845901d04462a4902d2400541e00140c00c20404070342c4142007491100d1000280d000c2c0342050340a240a0820034010f06040c0304505010074101072080241c44550040030307005100180d0341d001001a0458103000c140c00280c0004611100384c113100201604030ba520000038501888500500d8400342c0000d006901e281c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 507996169 1250 507994919 507994957
    0xb0f030a1709150a180f0905270606030c0d08160f080d0209090610020a0303360b09030a092102150d0b0406150e040b0d0c03050c0103050c040b 63
    0xa4032588030704410034030b04006041e9501d01c0c0301341c042c2952003614a0b0440d00301202c3c03800d0207091041108041260030546c000b054075100c0e0000c01c90691100342c0c0200c3c2c065145582071805a00004070380340100c600b07609403607440c0007003000c4c44024050054081d00300f0f0b000700100000c02d402000020b41c030728000d40a045a00e4684e50340c1d03001652102095005440e0040341c401114034042c0ca1850304600e04607019804129203403000313512291034020180502da0340706040d4644164600700211491400602050103100c01d0598100001c0030a0b01640d003600880000703414110000304440603e402034076600c48880ca0304140710300d1080c2c8503400d26201c8c068901c2250050f1036001c4168030303c83d0340e0702e801510b8407909980102140c4c0c2909045100b9030921000300070b0060b0f03405e0982008070940c50a851482400c00c0410080c040518a46030000000c05446091050201825003524410000c1d00c1d0104a46030046080d1942581c0000341c4007810042003146001c184010702d00301d10300d141c0344900c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 507997419 1250 507996169 507996187
    0x170c10080712021c0b041506030207060e0102042d0801050a020306030c030d05030a0e0a050a05030309070e1509071b050d020f01020315060c0a1401020702040b0f030a17 74
    0x11600010010004680010140050550030012005280a80c524114241401d082d2440003070001030044c07030051a550001c0700403e884641001c00d4659640b09045215603640e540100203600c500d4007910410704d0a0031001c591030040c000c031400c40b8024482000f203c1d0140d1a40e080700402d01c0b030003d500d03400040300043c99803001e009030740c031902070000010b82700d1070301d4010b150a003e08214042c2c4280c0001d40c406100a800c0400e0ba500180400000150001c0602a961a1001c0b045007c2d0052241c2e40f6220104140000110300c108604e01c15140790326a140e80118946400f514061584e4140008580580c00c02c15510759104000b071034a580075030300f85d40d5807200070524181c050318150043c00000030080d80400c04800b580300d000000b146149000048001c43c2e000306842d40344145c0300020400340000080241e000c1c040d4002c0e00e03001c0021b10041c204c5000350300000049004c1d60801d44103d0a91601a20800003884054040c0450769015600c0d4009035800703100c2e080b85e0031004d01044070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 507998669 1250 507997419 507997429
    0x60306061201080a02121501090b03010b0d061505060304080409091a040f0c1710020d0b180603010506010c020306070f1e03020c0c09040c030b152805060c07170c 71
    0x4003d01c51039010307000444250060200c4111080d420301d0041d445209046100d207a00d04582c1c1c111504140d000a0740c9003683e000a0140c900700c1222644545006508028000d050f8016540013080380682c40c0b44664a00034401513003c201d4020b0012582444204803d65041d049101910320508201081d80e6206040010030b40303050310f054684014040d000c804214400c0403007400785c243c4548140c819084055850f0740c0340300400da5159a0383c0c000c1200e0340f14a000790888071070138100420940c100009401e03a204d841400f12100e502c60760030800890059409428801503103900540540040e6892020035140d01218181c21030800240d80c404900d42c2c2c030100305000140c0801c0e034016a9031107045001d41d140040400620303115002d40307400e1000051341030441d902141e81c009903103a0300b595007100340d002e0032a128600a070010800e001d42d2a0095601e41c031901c4a0040710400660b480c0c85805000300d9008800c0c007507420798400081480722450b807180301401c20060004842ca00b554a2020071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 507999919 1250 507998669 507998671
    0x117040f0c0902031f082e180620030a36060f05130b090c040f0f0c03051017010b0402190f1403040b0a09020315070207060e030a020603060612 63
    0x42e00c0c0e40e000c000d1000003010303100f8001c1c188040940d2141030500f00034482d42c440c0d01902002c1d0365218400b04494502044d1070040d044d02614050421401805071703102c003035480e0180801c0b00c8452030314010032001c0c415a82c5010420341d03074035001d6086640d004044d41c0104843c5001d081c204c40b46680c12810b00200c007803850240c0b0030070250068040b0007032910205440405800f108882c0c00d0004102e007100314110361500b02c50700140904041d40f40d400502d030502c0c900b641030a230454100300f00b0420301107283e00040e40a0500003020000075500da4401c07070444905881c50056080800002c0103035650000000c85018407040c000902c0029001c00035080b6408400c5c2540902800d400450300542c100590040401e030609003605c40340c0c450f01142c645880001d000a181c0010100030a1070b0074016484208415405021500b40c0400c070f042440d41d180c1c0440b45a030040c41945400700c3c04a10a840d04ca41d0800c000d401004440e807543d0811456400091120350090384c2403042224070f014070307500c0d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 508001169 1250 507999919 507999929
    0x25060c02010c11070e0f0c0c01090507050918120918130209010b0712180b1204050c030c0105070b0606120a06050307090b0f0f01020c0d050709050106020703020117040f0c 75
    0x9503242e511100507143c104500b26050f00c542200004005c120b030042116940a0f45500381d04034a40c0d00c00d5a01301a500401c00742004542c078140c490030030000001071840039140708491a9240b40d4400c45034844da014259008107481d04000300001c2d0620413480074103084031006112410181036591409503807074080301d020300300065014200c019410034042d61809005903101140c90019143c03500d00d2584005c0d00508108117480104001141c02e030440c0d00c010303002c43c0c0c1309155501d88000302039a451005446c140d0300c3c0c0c091800000d4051400042c0d2503400141a1102410516151600c01d40480000d02058008000700401d001e01c1c02c0da142c00900c1500751035000501d0508100a02d4039061254100c3e0910a1400c03881e03000fa5038a0b20400c00f600c1d4001c494020303807000d0250040317003812100300d0081d40100c40c00034507504002001c5140c2041d6044c000003040940e07a944402c0b40d0f00c107180d10000c0d02007407001d000441c92643c407004c0c56610078000c0e0700a940032000c6582c0c1821030780345035001e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 508002419 1250 508001169 508001171
    0x2010e01020715020105010f0906030203030f07060216030e092a130b130602010e01090b0609090a1203020406080c09150f090a1202010201150e0109020a020f010504051f050c25060c0201 81
    0x1403008c44030314680100a046641802c005080c1135a0100b6680e2283c030382c24140700000030a240c010400c00340c0460b8449440c0d011260940b52840c0341c042c2c88c5007490010584035907064000a03129541d508851500d5040d0541c1040031440310418809180d803100c0542c00d2358011001c008202010301c44000c0104528150420348260b01e841002401c44034075140c6440243d061070340c038001043c65000d100e82c00040495043d0426200c0b501c019280401d8424002e11034004650f20200a680541c0600104e9829484081d8940d4034038104141c1e0b88100328160b07a108801051024411640c00c01508204441c1c013001c0e860000c0210005032524102c1d804800c078040d2444c030700001c550382806901c025485103500c4100103820080d45403000da405000f0a54865404218a54154404c0141401410001c0000c201c42e00701350601070b4545e0760000c410b8524600c41c07400080381c2c26591103044c0c820107980a506050400ca0100041907a130800b80142d00c0120710110340c800308180c2d07c17a03c3d003400701c5500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 508003669 1250 508002419 508002421
    0x1e0a062d090611060c0703050c0a0b01032117040b06180a1a0603090c091b120411101b02060d020c061014010203040b0904090b01230a06020a02010e01020715020105 72
    0x700081000c5000316040f0b4180d04201c042c810b04081450a071040ca5500d802d1564542207290380c621310b000303081c450140028a20000000601002d40180c0d104030b99215416049100c04200565030140ea8051003010400300c0c0c0b00080200c4d03d620001794000f800102001003140b0f0180032244000d900342c4008030599a607040d821258480d4800d0203040050603100703e4210729020400340e840b0502e4100c49070050542c60b0001d62980c40b0400a2040c00001c1c40240f41c5850004003455500c071401c440441d424803280c00e60000c00d203880d14010400e07032041c0d80d448008811140c2c0d92140584010802c9802c294180401c40c0e89000d64005001d41e89503900c02031a80d071910325015403c85100e47d101824403c000c0701d0101050345d01000325030503a03484a00f132660b280b03038003c04140203086c00710024104030040307800851034401c00b0290002c107102040c0091052240c800070003000a040c0d1250a0141c0c0c050188a4015402095206d4902c074050050340c0e03542d65904040c480c0500403100150050359960 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 508004919 1250 508003669 508003679
    0x50607050f06180c0406150c110d0614090303040b04060b01020309130b0f06030108100b030705120a15061211011107120c0e0c0306010507050304030c0f051e0a062d09 73
    0x211441c8070138800c460501c1002d19110f14829003180e050411000c000200d8038950502c40d81d0400c030b45018178043c11020329010b8508014000742a59040d401030421402d002c14035129000054034040c0b50082441702e083d0710b0f590f80791001004480c5041c3d055020900807201a0398841040c10000c1c000c9090100d0014040340070054200075881c10544201410310050003041000910003001d00c1410200182e24200d100000f858205941c4c04036503c0186441c00410800000c9880d00c1554460006070000030100c1030780e0016215a801040c040d0600c03040e580010070500f5590040343c04c1c041c14090543d0510240c0b003810005250090281c200e207200d410700400c070180107079034000c10b40349603448290f040c80079101c0765512025010f507041080c0840c00c44144081401228011075101e03480141e2250307911100c003032040d01449460700c100f03c2440011130740852811140b01041c0c004003240340310f070306218054a02ca841c8000c0518200744100c0382c129004001e40250b80c2005c410f07103400109907e04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 508006169 1250 508004919 508004923
    0x507060f02121503061909060b0d080a141e160209010906050102150609040f0512071a1f18060f0b0306041b02070302060706020c100c090803040f050607050f0618 71
    0x1c02d0580aa170000b0308000010740ea55489400c0b4100150300400e030100d60b0306000340581005403505031b1000c1902c86810812030110b000f410541115100e40c02d00c200c0041410a290140205440746004002240c141c841184402030503d840b803aa9100ca41e2041900030411001098100c1060350356a00020300a030340c0c04116841c1c0391040741d40410303010701d400804174403001c10203080182050030703071039000b03003000020320038111003c003202d085640701ca610f410008099102050481d031255002d00c045060b108100041e2984404031140841001d0f2404855460410850340081c020030380d21480802c2410107080b149009200980e086a102e00b411820082116850341c4610440c801020340501404d401241da007003200c1e01150283c1d150055400c1ca40c002c1d00c1822901c80300780c06120404e81481189a04c6140309290030394803141d245848003c800c1d564891806001c507040c2c0e5041080100b460102c0003000c5081c07046050702d01da1300180f00018940101529800b9032907c160317400807211601 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 508007419 1250 508006169 508006201
    0x70510062102060307050412150510150e03010e010603030e030c01030605180606070f03080912030702030409150b040f061707080c0a03060302030f0c04140c03070507060f0212 77
    0x10650101c80031003841020000c030055030020b025100c04400520060b00403000e8900500ea039441c0c0c0d49103c00c10b0700e403100704803044001e0003040626000204020303203080d1072180c003502d40c1410031060221460300c05540c98400200442d525640b9000d114801c20821301a07013004611a0315032640e0010310404140c20104000740301c070304251622104000c43c1e40c40761002258000328030384400c0b03681c49500100b109482801c80107800342030050781000030181c3c80501e180c802c940c1c0c3c0059440c00c0301a050102001c1c4000e07904031005074428041441202c1c1c0c0780e44484c041d0040741200290703441d42c501c040586034000f23a01c041c4ca0401c100b242002825006002c8070100550510500000e20b0000800703003071078001401c04407071240b000c55031040c5a4000d03030210000c1c54004045800c2d020401801660315152201c483c2e02450500c042804603200b40d9036034034021036088055600b565241c42c03040780c654100741e006680c3c581d101d071204501601e2620003020003031840400310314a480c042241c0350031410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 508008669 1250 508007419 508007429
    0xf1d1521040201090b0a03020f031302270a150f03050106290403110d05060108030912010b030c01110a0c0602070311010512010315140a02180324190207051006 70
    0x505100700001030380c1c040d038894155802c10070004d84a28218000b10001d0003500010f03944450000706210904402d90b054408892085030810340100400b45021006d940c05c41e0a03521003414000401d83c00d02540d0402d104140046071000480d0f07070b5820002c04000010b034800e90340ba96545405200035001d91280c0781c0541c1c042c0060580701203460322506e500341f1a43c030015040261051915a01e03a896104001d0201c1d000300880748296100c2d04130a85a03440100d820b8032456040189503a03500c2c040c041c0c008045c00040141401d01c40b00c00040d100301d5103203000c800c0759002c4c00c403420000446e6071002c6400b410050b0300422940d400c500d00001c410140404036814800d09000041c1c1c80140704d510382d41560740c13000d9908220302602e0022030251a2540c181d40c941d10f0380030200000d0390060307405001c8000c007100d2688032300441d040516444041c0c10031000b40c0303103007510040e0155200c0320300b4958100104ca0600407609200c04851800ca810440c030889254000002c8200740c00994080c85014103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 508009919 1250 508008669 508008727
    0x9060108090d0518220b010c0803180c180f0c040e072d0215011e06050a0504030c030b0403120209010909090c120b0a1b0f1d15 56
    0x30400001c420355414503910b154003004400168000f03800d02c00f800f8400c10b500060b18910313500c0c019282c201c1e90300340e841100b112518540380b40000650700ca0412601c100390400900e5103140c445071103d0800c045403141c0140c0e140304542040340a5210819200307152032844100c3d1083d8180301001000280001e018948030140501090080c2c802c03065410360048440e042120320b80190134417021601030002c403829014441741c00c020030800e8002c02c00d50302000800c291103103030341e0322078201441070ba80303c0a10010000d81404244400c600520040174080310078100a8105a62a5503a000b03c620760380045580c001e54800340010503400a141c448840c91140c815410454814002840402e4900c14885426200c10381c02048c400c8a2a400300a0076860700780b2038a2041ca41000c0ca11850309445580c00186000102143c20003002c8000300d1900c2c0c203a071000c040340c0d80b140007203509440c041d0001150125981d400c00c006c6e501c004203542c040d19070700703035135a01c82c110440144500311000c44449182 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 508011169 1250 508009919 508009921
    0x1109270c13090902060d0c18090609110a0503071202070507090606020f0c010206070e01030905010f0203090d0315270c031a0406180c0908010501060210290f06090d1109060108 77
    0x1170b5900c03c11350b940f2003a1070300001078600080a007100d030b40c1c00f940e5035051407c04031140890741241f29000f9405460b402d030420b1044041070b80e2005a94481d15284400142c401d02c0030078078191160b0102450038140050250810700c0e03d03180c807810082940e010707034665503469900f00041e0b0f40501c1107500e00700440000e040040106000070303480340c90040002040000480c2180043d070b0281d0310a40403640c00a000700403861801030200000e60096842600c1e0784522044003154620a01400c2c0294846039200701802c3c2c9000452003d000010240c007102c603280f8000300804000a2041d010413041b16078000c21010550140c03500300c40d912111490107141045010b111170703440d44051380c00340075244000081c0c0e100080b108542e6140e00c0d4109044650030034000082d82540003d00d50a41850007804000c608d0741d44070004040910348010321215590300362403001c0303480c0510f040e1986100281010f45041c1881d80021254001910100c80d13405003020000c000e41001c014095000c0800e0902c40ba003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 508012419 1250 508011169 508011173
    0x1d070b031605090d1106120a06140901270209040e0706030b0303070228030c0305070306051806040f14100609050610080408090f0a08030a030506041109270c130909 72
    0x780f1013214050420720060000d81120303200c0341e040702e49070001c50800d0100c3d41004074600f0080c01d60341c0301329004c0c418244501c070b0952034403002c6241259003103401d103a070300f098040c000440301414110310340c04a0350910190030300e038a807400748a001071207010140422a0030414043c0407075442b00e10142c026441031201200580314400d01c0c05c1c0d01c080c0008052001290144103090389240d84d00020404100800008204070300000c40703400b900d218034400d008590342c2540390700340841d10500a1006500640220340410341021610880341d004000f5003039000a10a22036107805090030700e044170265294010088070304140b0400e40c00450445003a2100c0f141044004c060807000360000d40001000203000c121790b80c9074003501141030b00c00b9100501c070942d64248944c072504884031900209042000050b0701c1e02e8548148520031403420b03007090030011031030184078440214025084803000425442501c01c800700300c202c4d228503054040c803907440b100100d820f2180401c961000c00c100d414000c050300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 508013669 1250 508012419 508012429
    0x1060e1c020a05030703150f05070c112803170a050a14040306050a05060102010507110618010b0303040803190f120e0c1002011b02030306131d070b03160509 69
    0x10344222000d10300d00030302100c0c1c00001c02c00ca22943c00541e05200303100c000800c1004004c40e500301e15a640600b0000300351700500700015150220b40f0800001d0700c45d000c600000d2841c0c5c00001031210043c10721b213400b00f50080352a4030788028803ea240c24507a81e42c010002c00a04201c200814852001040c0c1403240001002c0d16034003507982d21205000b040640c4464030072040041d500290380015060003281409044840203140541d5024015400d040c000340b400303801341c1c0d0101404000b0000411040c0c0d03c2c4020501070768080c114007040c03075417a6804400f060340e081014101421400300550707a11401c42d141955512050311011080c0300000c0707007804c042d030381181d00341103010780b0181b02254544a2092082c10705084070030b8298000060410740920b5a8158000011540140401c28020392218402d9035240000c44481d94802070010065259020a070005c584404d0303031112020329400d82543d03880c01d007005504000c40d03016003c400c104002c030300d5140710340c81610941440351034009208003140c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 508014919 1250 508013669 508013689
    0x603240601081801051e13032102070c08030910110703060f06080610050a1a090609041503050a12050309100504020604170609010c181a070b041101020601060e 70
    0x94103009010300007900500c00e003d414040031003c01e00130401031820743d4855410714005045040c1a4405000140c030f0344040703088200c2a10741646544036545502e022841d40e035101d0035050258540c00b8009140080c3c0345c080c5440282555002441d19050500180941620030780919010040c445d000e810344210040342100c26a03400c240c010848031004240d80d409400294030010041c032502040110003002402c0702401d40da412502c0010b0a650f65421412100d041d44000b100710303200308000401403510705c0091400c810702034004034440b00c0241c3c0214100c4056402034441d90420640b000420540007800c10380b81403a0708040c0c1c203600702100742130f55070009130a01c03a100c20f80d41d82c0070809540d100c90503100208004181c09180b0f0360354604503500c07248181d591442a47c00c0111010361f82c1c3c0510314a019000241c0103551501d8a859103407005041d205010301005d0078100304c420f006c102500c09040c8240e0040510745a10110038000a1815005901080400036140207514407980c42132001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 508016169 1250 508014919 508014931
    0xa120305040218250305100602030f0a12060b0a0203070506060a12060c0e040c0507020102070503010c08040210090b0f0c0c150a050a110a03081603050408120c0d060e060324 76
    0x1288143c1e9403038541d010004640c0351588035010a4450401003560701d504011f105050405200741480d42d00c0701c0503640ca004648079412032007010300020351280e1060442c00c000c0920154041101903695004041c3c41d80b06900140050704001600e4050200400205030461030a40718040708030b1510702c1800c0c1d41e0382c011400509482c0c0718411030f46038600c610440c0800c00c500038005c0040c03c0755001e01a2403039001c0300701207015010315080003410f45010720505001c16059214640d01e591194200442c01c2d15581d13025040c01029600441e280703240b14003520901c11a10440c0d0b90341c00168285900d000d4003890900d229914a00c22050743c040031609882d00000c03030f8200944c41c0c071001c560503035849100e041800e4a51244203000f60901d50303c04a03580c0101011104520f172400c0380103003201510003c03a00600306410401c210a1903102c298400365102c2011507071b15081c0b407000d524803001c0c0d8507180c4c8000700c00d6101400380812898207115440202c0382151388001c14003207030400030045000c01019 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 508017419 1250 508016169 508016209
    0x40503030a1109150405040c050319270807150e2d0303090d0e10171003060f050a0501090b0904020906061b070f0f18050c040b0c0a1203050402 63
    0x44142d01603014155010448000c12400101101218116140c1c01910810340710303c1c182441d20824038001d8048900545c05102e941615050184910000e840303e015850008240031000760490040306c0c4181c0d80721071080744003a43e20505410407000000c0c03030101104406141c0085140c01e0320380050082c4180e81e4074040b0300da0100c0d484100c044180346008943c8802d01000040002c00e1001244c0e00704482d00d2601c8941903400c82e50103015100001840101c04130b0380c501c0d503650226800d80140b960140c145003004034026203a81e01c1900340c60251483d1013001c1d440e0740c148448800c045c0292805800310f40d070100b00e00840c10b0005620b030307040a440a40100500404100203403904400c40e92042d0600c50305032030098888083c030303a45585a01c04c180035003510303080229450300d1550080084401552105c00f6111140204400804010304010540e280130040000c4940820010740a50000c4034003426001c0e5483c24a205e50760400d111400070985054100310040c1e9030b10110315901c401d8180 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 508018669 1250 508017419 508017431
    0x40e0601111204080a02030115180e07150c02010e3102070519170a050304060f06051909060f030b13050a0203010f051617130c090507050301031a040503030a 69
    0x15294180703000100042c2c00b2140028020600d1180041e003d20241e100350020400400302c40d5207000361003003602540000781051411401c021103182c00c13404482c000b03001920b820580e03d9891690b0030b6460b200070b20101d440d1462030000c0d507810011940c4000401e480088150029402c40b403001341031940030f1208070704c481846c098001c00300d0703040c0d0741940d502c0412107401507500b05a142048140300412103804e00d10000444a800120054031480d1400b515864190b803500da54490240c01d0591351078480954034480080c0c00c0c0d94001c1422900c0d4500701003d1550390409040b800ae8400070340010001c0d0241a404000183c078200856500402d0344000d5100c914951904500b41594250302a602d076081241d40c1c40084030550146004210b00d5040c403003a251710400907a00342a0515a01c000d00c1d02000020750103841066021490342c1c1705101d002100b0303484408680031540b05680344400924040010f00400824641c0c0319050076003425048898035081e0382d081da503840020300100361161100c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 508019919 1250 508018669 508018697
    0x1050409021602060304231504030f020a05060c030118060308070605070909020c070e22030e01020a051e0f071206020904020d020d0e0d0507030206060d0c1e060212040e0601 76
    0x24203030502c20303540213000c2c0ba070301d08150038441c415070600d1100755401010044604030032100028048000c99604c08024001d50f9582c60507115180d00b98904c1c1e02b90b01580a0f80b10004100b0b201035407042d1085400c154407541481c0344001c41820310100d41c018507103000d4050001c515103006640100b54444000704450b130356003208484049155000f24403aa002054491280b01c0115000054800511034070a2301d03560700001a000400052506e000d944200d5903000c0880c1c810b9410700c003501d42c10b00444182441541d175042c600300105190150700f01d075a18814031442002d104503c1c0c1d0010b0b40313009018040c2000488c1035680801c0000511440d40081c60214a80316a01610354102545400319143c6488460250182c105c000c501c0c40700d070092483c0702d00040e0050003a1420309406500624844d9600000d10000c200f100c0010303140c15007421000100d042050794000d8510f008075103001c7c42c2e1807030007034044d24224a600458954105c180030510100910000d00340d030081c1c00b483d000507850104 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 508021169 1250 508019919 508019947
    0x10c21090f030f02040c080c0316020c0d080405040b030d1709012d05010e011401030b15031314060f0a150806090a0c05040b06122509091a0105040902 66
    0x9a4007956071803850307410000a10025004101455000341c03024080110381d500f04542d881c100300e41c45100700c1c9040c000300303980300c020196020b00c402d0342d80100da02e42e1002c1c0b000100248500d54048800500000c1e013404981064041c0d401603c006400403c2141510000640b12070105002c40c04d003804030348005481801c00f5040009000e01c071008080c0010350307810ba643c00000703214280751011424040009a000002c0c00315a040301c03943c09942d11064113010044000c2c061001500340d0201d991213510030708480800003036001ea4528136040f0b007000003030b02c0d00f042e01c11840c0d05159515003002d01044458440c62000039402000000000b6405a4007031401842c640c80750000c02c11031042c00100441d0103c000f40300755030302d40070300441c0c0035980c0e0707d030700300029181c08448180d0800810f01140815001000c0c103140c00c0303000d105482c09400241c0050b1424603000c18072140000300d03400410014a4240d01c5400071001052000c128010386920000e011482544a0710070060341c0020032a060100e0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 508022419 1250 508021169 508021187
    0x3040b0a11150403090305011503020109050f0315010f0501090602160e1312030e100e10020a05190c0605070f09151202030115021606090b090a0e040f05060105010c21 73
    0xc0c1007840d10b28203013401c00820054660100b00c41e03640ca00008400038005081e055001c0b00e0b416034503d051107003407009114034603654401c2d040e010301c202140603504951031005c0341d010306070702520444910302d0000010001e074815400b000a5401c1000c60114a00e0b036900302d84180c9040034011005900c42c607054100c0813910b070b080601034000c10100811100e516402c101440b51495080300c86071540b0100c49001c032440e0312180156a408442c40140b0b040d4140c000c3d0003500c840f41001ca003001681c0f01003142a01400301003a0008540ea09040b0401080b0700c505604910549046240c91400c2940074021200718000c01901c3c90a030030795922240c2c0310f1641c9d40040c1b0700007034041d51a540d4814000466503070030903103c0058040d004104002c05090207040045400e2951741129951a02c07034480d044d03901c1019060342000d4202000b140041c16000380b40c1c01944500404500c1035218181740d4100030042c1c000a0402a03810329240c00328138000d000c2030b410421b06e00c3e4003262400314070094500040b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 508023669 1250 508022419 508022443
    0x13121104180206160c0f120605090102070c061218120e061c05041703041208060114070506040b060f01140306060712020303010602120f16030c0203120702030f03040b0a11 75
    0x1000811848407100715114001017807181e80c1d941011038894a20440c40203007401000c4c407901c1000c0342400403c00c0c9401054002c106e00f00010b18003a2030382c4410001e1210360308a00c01003030044011194400c000c5c8603802c01c10340041203650001c42c0f107940b02e500c004103049079a800c00a05040701c40107940c03208211443c0d850b9040c0d14071000e04180308404040c150888050710f002c0d40761a1050b4000300040110ba209951100c6509900d1402c0f94003511644006072015040051391414404ca00100c14018000c0c5400707800144020300c0e1904c5d1241c401c2c00014062401a58000e403008202d0344c01c21204584045001c0703202d0740300c2d86d500010402c01d004240d8088c0c41423983c08000d00f804c0340c000c40218180e03845503007035405c03000030607084001a21514929040c070f280b0420280d031452007001d148440035882031a20320344c00825074000034500104260303880b0107008000342c072104525040102e00354a6411101039402d203403520300405401d00a0fa81d030b450502c001c94010200003c002d020126a041d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 508024919 1250 508023669 508023679
    0x2010605090a090b16080f15030709021c09152406050403050f010218010c021210021314030307061e0f0c260a0f061802131211041802 59
    0x700c0c0c0b410300d150141050800a541a00150002c0750000c00d1064484680640742e8545040301d454500154060001c0108503142c9500c000070706403043d0364184650002030070441005a1101100c9100303807040741003402102d20781c910b03109042000031441d070a80a0841c400b1280081c0800348010400a00e480381407184401080440d408501c16070000c0160068a0284040b90505045c5903240b03401c074401d03100c00c099401801d050140441d07109610800d5100c1c8050304100481c000c848030a45414042d5079030300c01c7d0340d402184103241600500c0085004018004c0d0030300302010302401094403403144440141c0b1194441c1a0164042c0400324a400f41ca04103010401480c0c0d0101011030080941524503c0090402025032104440c074403107520303424910900c44a056100e92220f02c0003030580d016680030250702c42100181c0c00401c0c0c1c5407084504401c0300056919038991900322680340c3d10390000c440107007841220201040008851040c10041541c0001b0455403031003001c1c42e0f10100102c001d41c80 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 508026169 1250 508024919 508024921
    0xc1201090f1d0f0d0c0503041203120e1b030102040e0c1312110108100b12070207172b051801031518112506060e0c03010e01060c0206190201060509 65
    0x2403040010300c442d03030b02243c5040e41c161800d0103104030354000301000003610035481407105000c4070720b10465031b00030588130342010030183d810415404140c030458050000e00741c01070709003085801019030225103907040440086180500f03062401e0a5a01e0103051160340d0030007c1140c001d140e011103c40380141c882d2400c00c00300800c02c1d1a01221360f200600c1043d00141c0380f080450580070411000c001a03585455a141c107100d030345160701c091480d00420b070000310310504c800020a18060b0784100030144514000e880e900c500f451040d000c02c3c960103640c04c4808005a00c60f0301d12035010080c2c40345100c5820340506040c80c0c0100403009031124024101c490b01c000080058641c4144980c035204140f142c0040c0303d687e030648000d0f410350080b92036016803441c01a100780d02a907103044135441e07503a11032400001c0058840c1c4059903540001c58407142c055100200503c822048424014010310562615210106003540440d0b642d0048035080c004150040344a00e103214002c0d08031202600b8007411690031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 508027419 1250 508026169 508026221
    0xc0306060d061107061d070b1e0304171809161e090f061e0c03140f0403050106030f0b010f050307030209270304051005031506030603120711090c1201090f 68
    0x7164880003002c6c5103445419000240003000400382c40c203c00716004000300e017030290031000001e030303100030400c42d01a164640700d10702000100024007004000310254a010030030090a00200c09006014003440700050783c28550f29a600180280182c6040c80e80068003010b403c0e8117a50103032490300b1105044150f01c80c0882d2041d402003c440c0c3d005035030084002e0089402405031744504c42c1c0c81c00540010084100d9001d554402c800510441c241c0b2001c0c0361400360381e43c0741c0900b100c0407034104841c007088111104040c40703443c640b9107014001c2841034401084c03410002950f1605d16120007800344400b180002c11681c1001000036000c2d20807041d008007e8000c0139099107030b5004e03008680c844c002052800c80418807500903680b10311161150080070000b003000b04800340d04020a050b9040c440c56480c01200503221000d890403500c01c0c005884561410020402c1e0b0450007404130700c81e25030600c81c4044101081610504403051782d04000349404003a14002c0142c81e1400c40004105c802091444e2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 508028669 1250 508027419 508027451
    0x51f03020703121b0f0309030e0909070503100b0901051002071a12180f03090f130e0a0305040e0f130213320601030207120e0310050c0c0c0306060d06110706 69
    0xa111340d4541da0150000107000b0180c007100d40081c0040c00003540c3d203544030110300b0844020340d0030141d110b04840c01140c0d101d000a02c0c200003d64000303405500e404401045e8240320701c0d003a024140407614a000203208040080d500c541a22898060510740804440481500000c07912800140c680f0740d0307100c0c9810b150104502034250032400389403199501a0354842800320a50b80342e2800100f80ca072000c0b61a5003085848420101c0384000f055071a0501d0101c0070040044024892007030311b070b0302e4545140c4841c02c040e420340104402008002e035400c006011010202a181d040da0440f00240c0784a02000e800008000c1a20703c1400403094105500340340040c04000210300400c41e0850800f036860074011402d07406403d60050011100c0f0003d000914003441443d02040c401404075408440d5601e20842030780c0c41502c86804883c3e00007020180034805004060803043e060303004040c50308041000ca114041650006800956507000c40c0d414032100b03400b115007070340d00018140456012151804 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 508029919 1250 508028669 508028711
    0x809040912051c0513080c010e03130306060e1603021810030207060e121c020904050a0c0219020609040b041404082706030c0901020a140c0406051f0302070312 70
    0x80200c030103543c6840800101e40c001c0074401c07064000424008441130380d07030f01800e0700701c0034400c002552180f00b40e064800003040500911141c02e02200082440c5043c602c0440b420754121140301a03503542000b0800300100e0b03500c1c000c10103514005030f541d2000c400000700b040044103030b1035020f0098003401c0b9040d54590003600b2020301503881007000042c81c14946665040011400b041000c00380038051980c0e000702d0006501808896016107440c0f40c00001038100ca4040b01c0c030b143c64646d14020b801d0303001d5041020380311107900751208402e03030152900007a01384e0040e40b00d401c1c403c40c2c40c0c569038050f584581c1c01c1544450700c1403006401d681054a00407505800002001040e95041002c03124070792485601416001d00c05000645540c4800382c04803500c0e48400c600754150320880d2080b0000a840e8154500c1d82e030381c0c00c0090002a40c4020400c800e8481c19406548070742c0003030a034030b41e22025414611500c00340504005944044901c0c003610500502c12501c1c5415140040000024040c00944 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 508031169 1250 508029919 508029937
    0xc0916080702030a0e0f0622090e030c0714130912080901021206120102040810091719230a080103030906050f09040b0a05150d14040f02040b012c0328080904091205 72
    0x12b000d15030700d011000ea508d0060202846a43e405100d0800c003c041e01104462900d0000d00700044483c84494104113036900220110368000184100c1c0080c070340e10a0313583d60003040c400000e5140154606050390303017a1000d0400c610402d250b80c40d030241c002095040fa07004160300c20913100124208000f480041c12401d80c1900c4000c0c5c1002c0302e16800c01b1440c100c400d03d21038081c4017a905244030004664040e640341c52034400d00302e03003956160005840000380110b40b039207699030200f96055140080000748640e0040301800350500c0804e0207000c8680c2558850750341960001a452610750010f648074080f17600c0310b0b40000c4c606d2504120040e20380010599824841802d000300c40341c100690f60188001c550203040b105610420307500600d06034001080b0380d02c1c14540b04080b000e44150280c04a101c0252200035185180d1503c29142420700c000c4560350a064240c1030040703d054548000e004003044000e042600c00103213003420b80c1d82c5d036000c0140c0036003103c80100200f09410000e00603520400d52 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 508032419 1250 508031169 508031171
    0x19150b0310050a03050607110c0a1502070905070531240c020a03021306080d0f031401030b0c0318120403030216030818030c0916080702030a0e0f062209 67
    0x220303250416684510450703a016008012031f55070b006003120014142c0342d10070014080c10b00001c070983d455841800c003402d8078102815829104000103803604141c0e9001801440c106004c00160a4100007600c2c640d00041041c00c00d8615484038040d146c8000c000c0284641040ca00e010032040f141c440c0014660081880485182240350015928940d80c050029840f41103841c05000604000f03460800000b00c4150128a082c1c85808080c1400010303089240000e11510400741c281d0f50502030f603003440c40c07895440851541180c40340802800c000340744454905000011031441c1c0305c1c003810913102e00242070546510744110310300c031041c50b4414070080d40144120b040e0703036810305803401c4900c00f141c1d40103003028645085407120302980403440b090709526008169074407546413289a1072034802d01d2007a40080e8030f0207040c0006420402c2c0904810f0466005000c80c4041640025110100034000c03222100c1c400312003000903401c5c0c442c030340c14682403c0d05900c0101d1840c0b8105840380590b918440 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 508033669 1250 508032419 508032451
    0x6050d0b06031506031c0c0605070302090a0506040e041b0f060c14030a17060118030c0303140708070b280f06090b0108010e0a14070203090907031419150b03 69
    0x500f0300c002e110a56481d0b5143e048600800510f003071216400380e00c0051420180e5495005880c0c034411074a04891100101c0e4000600130302e14030707049400c1e0b070140104540e20b90520f4140410401c810100810060540040002c0081c843c00c1581a03400101590602c044145440d2003000340101e401460840301800311114401200c400402134a013002920b503144414000b85c00e07039120b14240080d01140c1132051050312140c510405103808000366000302040144189545030081c048c0c0789000002440c1c0301e080c010711000a10f20320469851070341200d0804c10079100c403c007401c0840f42c41604100c03c1c07400844000c0c107001d81900070840d000b40301c500401c40259549543c105030380d45070001c41d0000744a140103001040e400308640f60041a440d100051201c0600d0780762112140940d403140160b440860900454640f00200301da1041481c0303814454035071104401c64520401030031700340c0b072101a88441405da03111030344070310500c51074819101c84041d0b40755680d2a03954420ba80030491800000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 508034919 1250 508033669 508033693
    0x60412030c0903050d0c21090f0803091e03101d0c09010f18110f1e04050d0b25230a021504140307060c03050a1e020c0106050d0b0603 59
    0x244204040341d0b080300190451540c0c40104a1b0a00178240040719910360341d070120715004400c1c04d50300303e804100b51242d0300c10364200b640603564004036038004480e95008010074140c0d61a0104039000110100140a8444a0480c0042d09007241c000d10321010758680300a40144070018104035a5010041c1c00380c038941034030b580030300c91132507024001c41d00100c0c401c210030407205030300000d51084a20300c0c407000250143c420980110b00d60058075203542480011581480f01c080101d11081d1528585010714079140c41d107404034181040200e0f014010700034500010302042c14120400300108401110b41640ca1141c03030018204000010954103041002040d00c4403980540003120850110780e0000c0c0660100405d200a00c08001401160583c0c83c843c1011400d41303040024105491003800082a110807508004086a0005000c01c0c0d2050601d0850a401692f0344440e6006101c0d1000150f556515055110b0141c22140d21041d0400c01c400e0041003840701c41041c0c107028203011020350b14011583c0d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 508036169 1250 508034919 508034927
    0x11120604030e100c02060a080f07030e150a0b0a24080f0610022a010e011d09070c1e02010e030609060c16060203090609070503030403030203070b0a0e060412030c 71
    0x48030020041814145040d1040c5066070071030201e580c91303140c501030f060000c0d03000c034407160002d06c816404a02c03036100b400600c1c007a010005920070b031285000c000307010312030708020340e44e0000307110080303a440d00321300403840704100b94200002d00180500020006030b1f54007031040d01c040b8516283d10102c2481600c07201050f110b603083e64040c000790f03c4c0f406090344401c81003081d00103480060304194420020340c0258244114480301c076602800c10035034411500540054030300d0300021500d504120010014181c21130003a81e5014002c40c05940009140e6541441510103500184014210382c10368040c464000d22042c1c00c1d00c105038800c0e6500011030394442c06141c0e0f030b1030080e65480c1d0a07400c030800103488100c40c1d6018007071504218082294107116504c418080b40c2c8140c8079511b00c5e401400c104030740d0300360811036000204004e500843c6032500d1510000d41764014410010300ca10f10841c0414a90b40242e001a00180d082105555150400c1e24060300130240d400c0f5001301283c01c008025404c2805 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 508037419 1250 508036169 508036171
    0xf0806030c060d0e0114070203040608060603092e06030f02180c0301090908091f021e070509100e07020d0810060507020d02030106030c260705010917120304111206 72
    0x2010b4040380c10000504201d8000c4c0c8040d08104080b5942c2d00c503900351118002c03042ca40500710b03a030061542c0c1d43c10080010020080140020b02548042044c0807051740001030b80c0c800107180304448401030103d40b200759001f45080304c51614180c100140441170044840d11111101e00c01c03900e846c080420301100d1107040104942c00030084030180010441100309421140fa80b900c100902490b180360900042e0155514500940414842c108402061601000226001d69911151441300240001415600c40a5000b81806030b8101800b044007960307581e8540020700002c1b51036242510b0181d40003542c1e4540d1000c1d9900244980000c1076550801d090500291400d9079036141c6859240d4007403124103240180100d07095980d800780080480d150840c0000941b403440c0054520403400b00c10011411aa541d03d03a51139044038500b005181c0e00550844115241481360248001800d400c490034001400c42c55010790034008108010003180c00311030034803404112112104225002075080d0b641070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 508038669 1250 508037419 508037443
    0xd030506031c08041b0e2409070c020102070b030702150c07020916050706090507091103060d0b060303071202030d1407080a110702030703120e1926010504030f080603 73
    0x10080c0352000c03039648584001c80e48117010b030140d10201900002203101c00201640071048030f0403404144240080007001019969a174698040d000c50b00b44000a200e40c44060410740601100300c20000031640203001e18402001104200350b102d160283c400b07901c41848004d4440c003000c1001c000381016140d0b0056418240c1c000d04108007075135446003001d0b00c00c0820181001403140901c081d400288040c019680c01c4c43c843c00180081c0c030301c2d0120b00000d90f4500488210300391800e1040088036240c1021411070960010520925611a4000b290442c030030204041d01c0d104110004030021500080182042c01201800300840140311000b2129039038103450b0000080d00d410041a610a8680c10140c420148000c07294a0203003d540000d2504010b58000c50f5003511043c401d03c141034103c45490b9404c40144c4010200a000144c00b4290401501960083d0072036000c074002200c420241451840c442c40000b005076041c00e00b409800d6104520304400091110400141d01e4200411801040c1e4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 508039919 1250 508038669 508038703
    0x303180d0f03200a09030b10050303090d0f020306070903050d0908030d0903030213090501050405100b12070c02040c050c060c0a0509040b12010c08011e0b03191401080d03050603 78
    0x89542030701103001c2d01103000e059410003c441e005032240c031000d0b4000c1000c00240d031100c0d006540b861400d0044060000e00781c1e001c00707450f01401c0110740c50103c01c0f90503203041292807401c22092403400001002e003800020350544654800c0180d4107402c16545001c2c2c0703000300215100c002c18035100701d0b205840c9001c3c0c82c80542007031101c19104141d54020441c1584203081c094141080c02c00b0110400d20164403424074a03803680c0c0100400d0409101d80c54002d090b42820040090410420720181d100e10352a6480e00d00d030100010b15454030a030380b400c03401940200300744001055240d0040891b000814560618019000400c0212110104a481500407622110b080460b20400c12004201805000ba0031241d14001142d4001080c844c10704010b4241d01c9201c4039504000d41203082c80740800e0290425112844244041d42d00034082d41d500c401540b12500a110000017540080c0890014451443c81d0720000459211404159403081185641d42006596140d000700b55880d00329403040b4400d9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 508041169 1250 508039919 508039937
    0x11130305060108241018020405120307050d18120606051e090606070602071a04150204030b0f1f030302010c1205040b0c13080d0215060d0c14031203090303180d 70
    0x11000b0041c080c0e020100e41c80ca85c40041c1e9840421406240705190b0b400170300d0b030019080c4200e20b051482c040c01070601500460501d001d13030b540c039582c910003c0800800c4c016130b60544010b105420100c0c3c805001c00900300100c1401d2403805030060a02c60290303910403142580c40320305045620311841c0d0a40742c010a2002e1944a0345c0034850303aa40020b800380c8101c1e07000c010400c0412400145101500c07001c1c06051090301c2e280c10310180845110342c0501486004000c10400300309054900da0304000c003604104619119000c00240311000356403940f160352a101d100100345074040d40b001c4014403003500c5040225540e1200e003812074004071802003005946801081141843c03c01900ca880122841d0f00300b1162186035803490a190400d108006030302602c1034401c4490702540803600031200741c4203500015038550350b41c07401d4a030070b018415049c4130801207003240f950b007013242e40c04a070100044103a4a0418016464a0f03500c100c50990040402c0e80f03001d851450009107002c0d48214a03a11a003c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 508042419 1250 508041169 508041223
    0x7080a030c030b101b05011401080c06030f07050d02071e14120d09060905070e071d011b0501020d1802030c0108090307030c030c0c150e0906011b020411130305060108 73
    0x30240c1c0b517020801c44032600e90040300090001d02c1030117141c103180e503254801985011000342c94402e01c4108580030300300c10b0050054194007075101503044101400c21079210301000e010740000f4001c0301e2014102001c804034442c800d101d00400050001e0203554244000c0a05c03140403035442c0f80343d896000710040100301503140b9005d55480301d10000d10581010601d9441501c4851410140e600b000c2e100400407814400144c0d0010b11001c1c05481d640c280380c80c4441d4280020b0a46000074542d1440002c0310000340081241c2035040707032a6001d4075030081000308030305000c8200e40400382804034064030030102c01801540c00b034160302c3e01c031703622400041d0b20303040155800312b0b00e400c403050048061021040201c40000e2143c42e04101408102c944a50b040004030801040c50201c181c0c0d00b40501d030701109004060742e118100c400c40842d84451a42c7d1011035102140c010100099402503200c0d010464401da800760300c0030042240c1c05041101c1c0325981391010f680c0c13030b0b1401580038541c1c5c104441e0b0441c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 508043669 1250 508042419 508042427
    0x2030a1d07060302031024110706080708071701062105040503040317090301050a0509160311100215100602060a0b010801030f031205040305210103080304060209120307080a030c030b10 81
    0x1500410031214460107036036500701c00000c44486c95035444011f240500c81130f03646512003e801c07912050309004025103482d000014112280181195040058a00c0003c200b0780c019124100c5280655a0903456503944440c0186408003168400c40d9032070f0700024001001c489409014003a41d040703c0a10718143ca10364604140c8082030003800300c502800c0c0035001950354203105840c8588030000000c559442d01f074075618100650900e800c03a4249900505201141e90030700d40c81c41241c0240c51401140c1031680060745400042c2c4103100510914008104c00b40e0101c03039040f4201c0304140c00715621030701d42641041c182d940100c1307480d0014024800403c0032841d00e40400e0b403182c1c000d00700325503005c52008441040d41d070200e400b034011440004030f24801036004d8560710205200c025a001d55941150b4845e146071101030b00242180760017181030750640d85ca81240c181143c1c1400112640c41c4e0444c60601f0054010044130404030b481d040c001c80c1400d0090203421096003005149078641c294100d0156 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 508044919 1250 508043669 508043671
    0x50f0c030402030a080712090801020c0606120a051b090115210b031b10050702031b1203070f061505010c0312020d020f03250503011a1c02030a1d0706030203 69
    0x6070b0f1501c2240b01d00360201c1c001e0001022001c0c09464001c092208a55024009007001d606c0b4503240c0e8410040c80120501c0414000e801240c1100e03800c0e1136410810304140340850700c81c4081c0c50b1340a48000b0400c0c6180c3c2c402074040d000c0095510a00503030f610f42001d4843d100091319040440daa0442e02191040c078203052003c1a0940000011613401920219180c0084a40025520b0b460300e8282c01e00d03072608036200009549180b4050780ba02d4000da0100b511074080c01c0d5000e030321704030784400300f00580d44016030384038140c13956002ca0382c0300c00181c00e101c4400c4001c500c00359542860700344013410151030310388018155801a100c1c8080704000d0354040380c6e80200b100117070030f54541c244108035141804e030004000d040090003001ba00e80c141030b4400c030940741c018540001203d941c5400d002c0b00c0794002041c1d038115481a240c03564082c0d0752400602542c440c906495089071103800300d981041c40154080c40c0212001300702046162010f4a0f20002c0e40400c0080c0c5000c1d61200b102040b000388030360011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 508046169 1250 508044919 508044923
    0x1150c06020307020a0c0f0602070b030a09050d180f1214100203010f090e070509041214030709030b0f2a0408031b0d08041101081807151101050f0c0304 67
    0x4584546903280c8004903001500c20f2001030b0071031111042445215441200504a07095092041c47c0c07600c140a0750b03c2241d841b40c2e0901c00804400036010302801e074411501560400150740540d19442c4c002845000703464526270300c540c40d004000ca518410b0641603c15195580780301c40116426450ba00c5807401c8154041c0d981d4456015810840305460018500a1001290b51288581084880c80541d14401c107013a1a6a00c0701c481003225541d1401301c0b42d00076420071955038082c0c00c1d13140c08070741e520142d030504030907040000b09000c45a641702c1c50b07420449000e0510041540c46a0329000000c52003a41c14000445010700e00d043c5a0195400c40ccc0841c038200e11055140c2583e030f40c0c41500b543c12913a80e1410220031000100342429013031000700070004a27464a005107182c59a140c03000d120300110b03d03904120708600011086900701d00c00d101c940135407000321102c860fa5056010034402082c81110009080454810300c1103605003c1c00340280c0504015040c0c42e0f54010000312140c00007002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 508047419 1250 508046169 508046177
    0x20c04020708090a060e130e0706052101141c02030c01031503210f02190f020604030803040506160c08070b0c1605030d0c0519201f0506060408060115 66
    0x482800c6a0b20584204c0c02080d60f500d55404060b03c1e5420003000808481000042c2410982e2101d40603c0100364407064449905010351111a030648000c1c803072210080b8000c041e00741c000080749a9241d032048010360b210442c0c4c0c5422002c01003044444580130b110000790160321415000715a0360207504078008070140000000700d40e40e0f9075210081e540348040c0c500c203080210078988001140d40030040400c0903482e40001e01c4055442d10458017041c030300341d1000d46a18001d410440c00c6503154800c8400468128000f103459040c20308003162610401e9891a400a44070141030f422680103040364599640c000c0e0171641003400030348580390000c0c0001d10302c0d14010010449841c0c13440b40d0010781c0741a02e0080009584410001c05d01c48101e41d40b4041309030034030609128003145010b903415132040d4551285080c0c01c0c44031129090590312141c8602c0218140240c017041780301c1d0089004900840e4404507404e200316142e0300144901c0b403285000d680115040840140075624200004017040401403030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 508048669 1250 508047419 508047427
    0xf0f0f03010e010906090615050108010e07031409010b2404030b0402030a06110c0d14071211100b01031103250e03060a0c020c033903070b03011e06020c04020708 71
    0x60260300b101c0402d070003107945c6941d4544080c02d1129511486c24204000350048407900d08160020300441c0c014841e40c81c0600207040055419031194011201000016640c4c201c3c1d41002c18020340030b49900340049010b8800c0c040010102c0c01d01d19034a4070240d00d43c1005070318003819a00c4418918a00420981e0148503468a5800042062061301c2480003244585c1d52610184424241003401c0b0901920400141198081402d00b1b400201c90100303502c01010010691440c40c241c4402880c2200c40d10680070309900781c410004103410216500e14241d8041083d09403000c00d10241e40401c0c1c4000030380c2001000c000c031038445401c410401004090402c81000892000020728003070040350340b01c03800c5031141c074600103090301007000d50502401100a862004982248010f200007608030b40d640d88001d00000716030481c0c2c0e1507441d2003403050280a0f00c0b95a6114401d00700b20358000e11403031002d6402c2d1100314444425072440002074450690151070403071003550420001e504400c0c001d94007800200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 508049919 1250 508048669 508048691
    0xb0a020c0a0b0309100212062b0605090f0609250902040f0303031a03061b13080c0a0501020313030f0206041e09051005090415140a1a0f0f0f0301 64
    0x1030803803001441e100d42c0c0c1d00e03900c0ca844000c103801e20b04000748a091460041c41030384010380013071840c1580310301d0a03204400d48079481d40d000203080062071402001c0240e814a18020f120954100c140b040d1140350481e42d0842c0110354941c1e0302c0314103c0d000b9050350442884540f01c1b045c012048400314510500c2411055151100c1404070ba00c41d40c0607100e0301d1100c0c0c804004164142c001c001845000c1005d4141c01d40181d03000c00c0d01c615000740b2030390a40544201280703141c0f950030f055540c00c924003151101180d40b0b03032152550b14000400110310440a42500040941c17001080382c82e00340780d800d030a062701460740e40c0e03e1414880200d030480e0301500038171020902c0c81c0050307918140e0b09010890304813424981035000007240c00c080c041807075800c05503000384400e032118000a600568041494000c2d800705484400060480200f05c0742030802250030b04c9400304160f00316000340150038002c8840754120808026207450b4000d1115044001400b4038080c6140c40d025040c0c01080160000c11848005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 508051169 1250 508049919 508049929
    0x804050a170c010804150506061b06150a030c09111b0133060503091006150f020d140a03090204051f3008160309060224010b0a020c 58
    0x10390000c4000e109101100c1110710030400007155005401e082460702c0341816101c030000c002d280c2c00f070103500755103500201e0442d4540d001154026040c0641d4101c11000302e14100c0d8494400751624021280040c10100c20f91030141d0720441102d80c0200300342c541914005081c0c0140002724511880748100384081c1454001040050312110b000c2400001d2904249460000c22804ca10201e50019455019004850400810758003030740d185052040d142d5035000d401034541003420400c7c100a90810321300190107904101d0110b0406450713220780e800c2c81c459802c1246d5407502142404001510f95900020030000a0000e2988090034607022502c0d0150b6008101079550503104000558200960800000c0101402d803001c3d000713070780f8004010740d07020080300084141004400b2601c410070b00801e0030405140101c80b0f492800c2d6445c403d00101905020309240100e100d5040940030710030070860810103c102c2800c914909520720b0700d136030342405139580e010303000a880c1c0c40a5110340c0480e41895a28 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 508052419 1250 508051169 508051189
    0x705280b281e08040510150b09030111041202131116050f0a050705010906020a0c03020105160b040c1d04170913060b0a17010602060a020d020d02180102010b032107080405 75
    0x199100c0400d2810945006841d1410b080302c0d86c16400c0c90070981c0c080c1007c42d240b1140c00c4607801e5984c0c1da00e80c0d90490000b401032040c0c4c141440791500004000170080c0309960120806402140c1e0828420031196003070007955810301310081801b90410800c011009802e41c0e900160740902d040310900c007890701060f850401c0742c2d4819181a8040002004290b070310000703400c0039001901c0a054920500c0c2c0d02d4401408940c00300030b0500002041700c5035091003004050000725000040c10b04241001d0038102223110984c0a40094046216a40070340d0001518049000c1ea80c051000c65410317201c0c6c100c21005402c242091035102444c410013490032809030007510094070140404540e90f030002d0a000e0800c55207605d07024000008000104105a00460a95444401c0c1c0344050303590a46036106800912903054a00301803031020650702c0f820a148001007481c1340d000e800800c100e0751031030708050b590708450000001c0003003441c10081440b01141d02514070144201301060400d916840050700c9680 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 508053669 1250 508052419 508052477
    0x41b080115050a0609030506150f0616020102010522060b01120617100c02030a080403032d0f0621060906090506040308010b090108060d050705280b28 66
    0xc00c080e0034050b034a050a80400203091074244412400c0c91943d8940c2c980c0b10040c1032110b034030314140301c0b008240c17100d41e02d81c10004c10040c00300343e0300c6165060b000d00c90050310006034015840c1000240c00980c0b030408a4580e0041c02401100c000c5d140e076900005842110380f203904000d803030b8941e002a640b09004800140210080c0740182400040c00c05290001c2d9804108a5600744040740301d40b42d402100301c40046026242043c09a903850500b98080c0215440c08145880071848045404000c5081d20714041e00340e910910610261220403401d03034609020300100f003070f81c00040c0b840b0385400d400605940f510501011445410b03d480b50001c440388d1120581d507903002203007004105588051940d000d05090681c8a0920700c10600080100c2c10060019001d983e9412141d410b0000810540000301001421220440b4212011003110301c4100b4000b1210300d0b1030000030560341d280d44280c034000b20081540d08a00881c80c103900300c01ea0640c03100d4209211861034041c2130301080032605c2104034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 508054919 1250 508053669 508053701
    0x3080306010e130c08150603132108070809070806010b09010c140319110c0112291c0506060108190501080c09070305040302060402060309100e0c03010b0612041b0801 73
    0x4d40e65040250031400c008088404400000e4603800c502d079125000e407500a40d800c40000c140304114a801040c2c01540020121040c24190f001400c40c0c0e0b0142d0064417610311036558013215194110416a1070800340100390054012000510002c2100405801c8036041403404000080c00d540300c644000c02015060840c40d00700045c801c94100e40d1a15240b2451310130306e403040008064414081d101c01c00003030b5107030412004409c143c3d008a1241c102551f484c41841c800d100b2094080ca4010302c0020030b40107240503c2c0c0c80c49140d46003050280410b00c815820001400c40d40c0d482c10011206508010700141d40c0b0000700200803280309452181c6030180c0601c5000300120b6044100300100d41000612000405040004001c00a039001c102281c2044d1305a81041e00c80d20f0300c2d103200d0700303029910015400b8245801921860444002407650608078240d00030070000c0000c0082c41106d2180c501c0725850040b84070301190008001400700044d81c01200c1344008880e45580100c0d00f550f94281440b07000c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 508056169 1250 508054919 508054931
    0xa14031318050c0f03010905040809030d0c0b0117060a0510030b04031206050f13090809100804060e06060904030c020102010207020604060503150301051311030c061204120e0a03080306010e13 84
    0x40482c414982c003e51441c04403801c10440e603490000a100500030031400b25111804142005120000e5901110000381615901c100a200040c0550402401603c42180550000808001c0701c5003541c0300e140030130041c281640da544e0440d400b0300b80203802ca440c00170311504004040380116049a00562113aa03c50302c0d4801d10a20701c109842d01034100a00c10f494a01003035403a940c0301e0390380c00180c20301840302086400d0a810855a140100c68059801c442c01c1d200c42003486500255540c07145d0f10074681000a0101850b40a55920041310300c41d13005032585000c14003203030141e0a5014154414400541b410340d15602256007500a42c3c403000108001105000101120640f0340011980a5000300f201e0328108859000002c041000035003449561260001c298800703000102209801418142d40e5107458204228940302c1100d0507214050240340003d40948160420200c000008061449403410760f16402c2d020350010785220b05000c02400e0b903a140d51540a8001195125a5400588 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 508057419 1250 508056169 508056209
    0xd03050c0c061603030b010e04020408030c0f0a0b010303080406150603050402011e0815060c07030b1807030c15030b04050103080a0f080c0d0207020112090503030114030607020a140313 81
    0x307000d00c11200319115000034003041c1d0360b441450b8a00410a5010b180200b40b030707415080107a44600c1100007240d00503000180200d0010f200200070603040066004852401003d134104a442d8040031500034070b080b00450042002c40d10503a1303426046402200001110030468103108190203460344900046500e0f501044191744e04182e007001b04900084407951403688852008000749030040150741c0181100e040702c3c2d01c80d00c4580a0b0303581c0d040c07510100c03804240c6a04001050040440d03884101002c2042c4040c50800b002c9001021242e2100d422400c00d410300b903011824540249001c001c15540b110319048a65544c01494020340c001d44855644e0b8800410041000c10102c3c40c0c503090081d010240060003820400706c0312180e489240c0103840d8001440121650b000701030700341f4416804e154000c4284600400154101c036207403180300f01001040d41c14141c85040440e00c000241e006880082c01042c990a8060a071214020999142c40401040080c03160150b4201080400b010781c10900 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 508058669 1250 508057419 508057423
    0x30406060312051804020f09060f032e05060a0c020d0f0308070306180c020708120301091505060304060b1c0804080d0201020403050a080a09030c15022e15050d03050c 73
    0x50842c1d0035140003840c0c1951801035107030080d20074001c180256400a00344210f10301c2c01c426500407070002800c1d15136400f60124042d10079002500e2020501400504c5041c001a020700c1c05106aa0149107191285251504000d002e4020040340028011040780000040e51480310303030711a0303900c100791070800ca6245080007061110000d2000d0207152034800c0502007041c103140a00700780c034601d480100300201303148030032400d00e200e680c8140424810354207122403e0442402440c143c80100204000f1a0713448407900204110f070384280b941005003080800c02062441d04524841c000c0544a0314600951582102151080c0001550381003004a000d0012203401e026a68001480e48000e40c202403e5499060b195000c141c0d00a028440002e5664070041c05100d07050011504000e1012206640b240c5180d00e200020744494014001d170340c2160680a5440050b2001c282003030b10350b07140e001902062500074018400e4254168032031000010321681c0e90000540f801d8802c0e99403e480d901014030280c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 508059919 1250 508058669 508058693
    0xc0f081215010e0607061d0d030b0402180f042007050601050a0e0f07031107030914093303160812070302030a080c0705070609060f050c0705010e03120304060603 71
    0x201c007140c900d2408001603034440454041014225603a0707988203007a1030b200c0001c010154854084c1c4900504e001c401e0600481c2885540c21140c40a00c1582c00030710401c0203e00c540c0085240706030000c0741c0c140321410311025550ba11342c3c01410000e02d84100c00c030180104800d502203624401800901c0704100682400302500604003a07a11500c3d01c2c4c101411440000e4008100d0900204c4180001d284144250000074030203e608a50554032082418001c0484840740140c070b0040454503400d540d40c0c01c100b505d280c824604980c692b01c82040c0205418131510108101d02c1d02507850071038103011541d05000321482c2a038480703a0322110f1403401121a041ca0495441402040c80520046012030b030040100e5800400500d001880303540c52510b0b07444c03030380944100500f4038480c0a40215405400c4403090095580903114642c074000c100c0c000b20384070320940080c3d010340e401440b400c00c0341e5405281000c40180340201503420440b0a04000007443e00704440540780207460760710420030f018800e6015 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 508061169 1250 508059919 508059931
    0x60f080a08090405060a230405070f08010501030f090203100b1903050c060a0908060f040303060b0412080304080f030405010912030c08180c032b020703020d0f030c0f0812 75
    0x5400600c6068660484901822226500450301d40000610b260b035100c3c074036005043c0312400c1e03041d400724030400c0341c0018503105c7c41035004030320340000300c0e0286001d492400f50341303442c0e5507549040741e08280c0110081c0500c00380200400752101c0e0710100595060003645600501100f0000300641030000704000c100040e40100441c48040e8000d001046000c03503241500d20b02526120b80e11041e02030104c2e8608000c0c1e202c00c6c0940600c0c028403d218142001d1a405503010365002e0000c2621254082503d101d1846035681c510784030440346001031040400746900c54010300e880c42c01c0401003105084030358001c440c1201c8595545822100b04041c0c00b41407103000c001443e041101c6000b500024000010186c0044e41511401c0c41030900060b00300800e080400f0041e0944079098103109001c0399030b020762040c40010100c50300f94185d00310701c00036204084a400034440e500c0040c4688801010802090040d4200003103880c0100200e00e0303080344d201d40617115581d20742d6540b000c01400c05890700c000d00b071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 508062419 1250 508061169 508061173
    0xe010c1e18031410020a0f0206100501231303031701090b060d200a120b0d050d110f070b091305010f170c04150503060c0f0a030e011e060f08 62
    0x80c52040208200701a001c0da680030403062074140402000310b161140c0c24030004000c1d800068070f01e0409610007400e46d6105030380d800b140c101d0f480306040b40121038907030300401d800180030001c21000040c40400300c1d000300d000311605528140c1509009120985c00d0740042d00402d0b1405400d8281e9682140385d5070040100620802203d901c3d940081c038144111810b0008003521440c0e210780416208180d1061510b40c0c0c1855562818104805001041001c45e0405007618000141429003000015030302490740c4400a0201082242d0303080c1d601070810012a070b440e01c42c0240114031054200b060a000d40055411030b0748403040d4008100320040c0380d02c0410007003400c08004000d40803115180c00141e07400c0c0740c0d01d500c00c02c4e80781110520701161000055802030415450b078503d543c00e081c15405594003a4240c80703013555810484c20f80c500ca18002608450000c0140001d11840ed070700c2403801c2a0504004900c017070724005424505003444244200300b030703074401040048807100858040100340b5440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 508063669 1250 508062419 508062437
    0x2090709050609120c1e3307051e01061701092102010b15030105090f240a050d03020c0102010e010c080f04020d080a0206070e0603090615040e010c1e 66
    0xc0851482d003c0c079042540503c800c60240c1e00701d0103040c00000e4808201504081c0c0100790b410b80441d032908501c920a0056009240300320010f000b001440340440703400d41d181e0140c07954055006d0019400510181d40034020f400d0800038040d0015900c0c061103001a0000c15410b041c6a151414400750120b442c4041e0f151500200028550a03050726040d6204000e4fc0b00440d040b175010707030140c0f100001c13032948072002c611480120109280074505030b0708142c6560000d42e440c0d00c40d41641da0703415500e11050b0540c990a2000401e00c0594140d260a0042c00c440c0c11141e0360408500c0100c001041100541c0080308204140e50b42407107511208407102000b800042030440000d001030b40050049001c2400460001c0d055458210001d082e80358803858a6a4270051960025120f603c1500d00c0d0000608400075405246010b8064a020b80b00c0f00c00034041c1511340d10214051900301041241e005030320380c28000c0a942c030a2040403118480c5845210401d45c141e810000d000b00140c41d400b050044070740d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 508064919 1250 508063669 508063679
    0x72102010f0c091202090702010f020c011407030b13050702070302040e010911010f0906050c07031a0708070914210303131104050c160f080d0b120601050306060d0f050609060402090709 81
    0x40c8250b13070740650348007050361140d19040313000d400f406482c02c079450300010300d04048a10550002c221442c41080b030101c3c3e91200714080341078070301c903034100c56002c540d04004400c07480003548815009941c40c01196002aaa5130102d002e0f00e02c0c122001203565580c5000c803061041141d000c002c034010901e041005450b4170034010380b03030901e9402010301300310021a081001c1001004088091030b000307050144d041e607240300c854951840072140800011144408101c505004001100c2900e021851020000e103c40051003010f44043e171031280ea4149001003c2d865131000d000440c00703070b00c100020804840d02802c029100c200707059145130040c1d250a04203c0220024401d85000c4440000c80060b5158242070500362091100030141412030002015401100a5881058900c0007a50314051110307501a895488000900c5000e40540110001410b24074103103058000d4244903840d03843c03405020b600c5045c600031085640c010281c1c029000c5c0710540c6440c1c1e070100d40c0400340d8503041454034140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 508066169 1250 508064919 508064939
    0x7030c0203030c1608070c030507140109030b04021c0b0603010e03070b01060825170114130b01140403060c02060603061003170d150501030e0c06040b072102010f0c09 73
    0x9008090f00040400c01c000000d14944505100c01d80001070b59440d620039007040d04140c1da251200721918400c4101c00070f506068940200c0107048140c585078119440c586401c440b01000a00407a407045595000020034164510742201503400f0700803054140c81d00350300781400c507140103144060f650f0050007100c0004480e1030030241960200c2c90300f210140c070b83c055103003200c81c082d001c075103a0040041480c1202f55070201c003540040c00d8846903a003082e42d1350020b99000d0300300703803e103140c01400b803807400c240b00c2800f6045086680c506151402141e010306080e88102d410980040380c01c16115100240030340d07030400c22240c0005044000d025181416002641c1c895100e2000070030117070013010f1160050007018262903040c0b20581040c404503555440140e084000c0f4000c1502007443c0026442d40d19000207884020f507480034206074900f50078881d6503112a0800c4a00f00d4424844002994100000c228020302482150b000403581c40100c0780d00109035010120380d03004000c00081d04000442034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 508067419 1250 508066169 508066171
    0x2150c03192414010903150e070b1209060c07030f0f0509030106031b0603051014040f02160506070f05090d060605030f06070306140d0303022a0304080f1903050a3507030c020303 78
    0x444000000d090691108141c04d05c00740e94040f148084011541c5d102d4bc801640c0b039244a0703c01403041d1181559400d24100c4140940c0b24007500186142e02002c034500d0080c1111b0380a030860742803142c202000800009d00352a40c58000301c0b082d00080342e400c0d00b06031100c1c2d2104090621810140418900032905d0181d0000500c682500030350441c0b078001c01da4071580d0105d60306ca9010308081d942c0d0640038854003070900d19188102c8440c0b045c24000b8484611904215103d1110380e80c9440c604605c0d0b1040101152482c1d9040e43d00c2c980d01c01000030256000c100141500768603801a040e14501054041d04440c000e6019900210074811070070003694039407607118010307545800c0058031440050790107400c1031940d04010019900308800817400800c004050811200c000f0110750303143d100580301540300c46510481d40d4042c0c050100e51070000780a200907090060f802d1038140517904520548141545400100c004120101031898090207040a001070344180d030303800c041c80000c08210001350b607444 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 508068669 1250 508067419 508067453
    0x60c0c062a160609060b09090a120e0a1e06020d09050108070804080c100e011a100e03161503060801020a02060718030b0108060702150c03192414010903 67
    0x10000b5400c2282d0701c8555a203945103030000e4040003190020700c3c18100812080d21514800c10111000850304000000c6100840d030f40162500c02e05904810140d644140a400b550360001020401140d400103500c200b00d511503183c5d180413420361501c0d8006e42000c03170000b40e47c4104903000c1801c2c000d83c3d0b0018030954101019190120041d9250f0500c3c500728003134215424000d0003502d100c0d01c101d00782501308019641c84140204041076120200040c00001c4041d0740b6000f0113018880c04445e40140c40b4100ca15034003600362041002e42e03018a04d6240999040b40888000c01442c540303645078140710720000b070010f410086103081b1910001035595640200200200142c00750320580402001155000555005e640584203503110840c05403034040448400d00140305100003240701c41105112075020301c9085100900d15100e01c0d440502508460907030480c5240c940701000c40d6a114080c00c00d00315004000d55007041800c00035250041c21075243e60604000407102b05002141220400707400c011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 508069919 1250 508068669 508068751
    0x80d23270a09150f0e01080627031b0c0f03100203040201030908042d060219021c0b011d01050d11030114090c040e0606060406030b133908130212060c0c06 68
    0x5400f201d103400202d2703042000b10003d000102c0c030205c02c04507106047d0300e02850b400030740748091003890501c40216a95640541e1641c4000100c0c00042c03059802181c210f4010b2501180c10f2405d521448070b503521a500c81c0902e0715220b100c000d510f0310f40718444010b82244024840c965803800c607000f90f650303103005660b0400301e030000c03144030456613900591809200c3c1c01742c0041921007a8280710590080034070581800b002e01580161a181c40e002105059a41c028408422800c242d1204880e941c05182219090b40d80c943e0410600460b01140a100b000d00b00c0042c42d950204009110650300d01d509621183e44c060340900c2010f9030f6000941e82074458620340051555030a4000031007010420400c10030003403902d080c181454607869440c01ea044a244030070340c0000380030701c1400c441d044010211000610005c01048441844844588820303000400e4001c0c0c4c801d200b42d015051010035201564100c20002c0d00d60101a011f0000560044002d141e00303450083c054044a0a000425a5640c0355 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 508071169 1250 508069919 508069951
    0x503150d230c03030703090b0a0c060911040e010501081c1403010f0320030304120206070b0703020d0b0a050904020103090c080d23270a09150f0e010806 67
    0x168666141840606400c00540c004004803000c0d91200c84410074010205409040c011442500380001100c400c15030694444051030300d040640112500171604900401440d1141140440c80e5801032028643c0540300109034083c0d00401c000894040d00001c0e060707a41880f00401c1101d6000c15040b00c000d40c41c48211202d012a00d00440d983e0715610000ba2440350701000110700e8400d01c61074842a81d21591006d12140508540c0104000d15071010641c035600402060044e030081c00d4452140b2403001e0309640c2480c40c5543d50640300c0380e0458040700002d07804101201036840c61300604010260075202c5019450500d00480d04c2560000c10181c18940c581a9550820180408240003029079800303845000d89040d07402019205501e00503030080e06440f50f003588000f168021240d01a820507642c0c0e45440c0010b002c180c3c00320003006030660007000e002000525980b64021009440c5545582c00c0c0c1036800d11045a103241d0b02e5810141842e00d600740180f114607000542d19801004000580d800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 508072419 1250 508071169 508071211
    0x708010b2d15071a060114032208070b16031805031905071a061906050910030b0d0303050609010b040b221a1b0d0c03050d0b1f020c0904030503 63
    0xd54492030f20700134500c0f00000030500c0324190a415840c02501c09036180400c2e0005009510801e0005407144003100032000452283d2801c991088400c940c8100c01841c10002c40e6150030b2005641112044503106503501d2f00f1540503494481e03c4900c2c800300c04900d0805141b51180e5030b5074018031107503a0710f4940d403100e4400c0180c0601d041c1d40390302e075001c29100340326100719207041c3e07032400c05070341e494082c1da480101c2289142c040d425840990b01a980c59a041031034403410060015414401413045c0741e0b440d0203030b5402d612683e19100d512802900c0209007400d005003400b001035016131244042031014042805203200400869000544001404842d2541c0318882521450a41c0c00102c9001c0241400320100c01c49501514851990142c10070868520141d526103caa00c00701900000c0e5074020401c2c0003a0081002d00312880305424002514410000480ca80748040c011840d03500e8002403000e070481d64100480340340ea40080c0d900c003945040c2550084d00ea400050070007081442c1a04201c1c0c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 508073669 1250 508072419 508072459
    0x1030902120a080c15070f0e150412020312070c12050313060305040330020d0b060706061a070b060d020d0203011b0306050607080a050306010c050708010b2d 69
    0xd190340340d041a40c0b0141190f14019401da40f100c424407129014141d0140c1e80340720203da05503c611801c3d200d0403403541d1803010407180000e41018565214000000d40e12050407000054005014484040003a94545004051400f17102d1440300240e4201080104000303084040844200d50300c44280c106c0ba0082e900d070440c150700403008640c0d500c04460000140c0c055043d00403501440c080d8403000703c001c0201600c1d50059014250749121000c134a05161010b04181c0d0007030035040701c4504000b801c0c000b22000103a00c1d40c020742c0180d030f20a40f904014000100840004012001041807075850a0030590302d054052078000c084034442c4031042020303001d64440f82011004c07254014001c2004142c401e0350341170303000c05d05809031000138a0645e021401d030903c841143c1403d5003141800b41010035414085a2591008020a040000100711400001e404114441c09407a1520001c525850b4103000d20044040c5403c11007080c440c05c0d402c8001c80b104002038040b41040c1a9142868220b00e403040076 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 508074919 1250 508073669 508073689
    0x307020f1b01030e06070c150e01060f06030e0d08130303180f061d06060f030a15200f0702040b010320040905010501051c090507030204020d0b0301061e030201030902 73
    0x400318040c44034400054141c1405240615100341c07000c100c504440c1a0150351903030221090b0780402e03c0e410820300410704400e03180e044030010080214501c80c903104080e00399a296480140070b8890340109024541c4c050103000d800200340b000070101c3c030701103103001445d81c82c2c0900107805103a4040d907048181071282c0c110096105140290514602180c580220b413038000e070364155003140c0781c80d448800d95141d940c51410002640300040c400c5840b000b0802c410342c402403a02c0c80d0301d8481c141340c9800165210180760f008800388840020703080104100c0340414124441c3d03859a051042106800384400902039450054060380c00243c80050f6500680c0102400f102ca80317009905810703005540345090ac010400c0e0b1346209010301c0300340d13030714401943d0b280640d8100e1002400040100d400488096105100d1756000f4422120f0070355581d008601203034024858201d00703544804403c401420240a902e0051110000352110091115501103040381a404000d0416844400c03200c00e540d80d8038000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 508076169 1250 508074919 508074943
    0x604020d0b0c190c050106060f0504050922050a110307060512041b080307020f06160b0709090c08061c05030a0302090102120c010231030305160b040506061311040506030702 76
    0x1555000f62003600c00b50414030703c0f00b422a0298280003000c00c0462181140d2516110b581d140d40b4201400c0400300082c10300000c2001c00f44e02c00c3c9582d00c0c890703c20300c4611020780d140210058030014400e400c2201c0c00c41914541d95000360b103c803008000c4154840115900c0d08038007134104800303480d586040e01002034140e00b041c9480c080004003180c1004044010300365284200c0c2c0001042100c0014000240100c80c00f105101d00c1c501c1c3c0c43c1c0003041c140c0b9480382e0b05c0501c1e880d01c01503103500d0341c520768120380340b48035940005215a4104221801d026180b0705403201c8900c510000f065107076884c03564901c91010324a0805401088800d40399000300710b841c20008104c0000c03502d41c01a0b440c010f0007900400b180c484c24113840103510340c41a2101416581c049625001b00c0c50300d40c01c41c2c80c01e131580e074001300942100c00782411021000c80c07000786401d40154842c802800607410100c0c20008601245410b0118030f603d824441074140c0300748000c0700c04468040d1011360701c07031743c40203800c3e401d0004002c11 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 508077419 1250 508076169 508076197
    0x11a0702040c0207081e030318100501180501090216081317060703050c071205070312050f0103050c010e0307050906030c0d11010318240b03030c011a030604020d0b0c 73
    0x202c01e4010f9004544142a100800f0440e4045d01e0703d00c080018074502c4694044168008001080b15504105c030303c010b190b0720603000c449408000480c144110b4100364001c0c0c16030311060b52640b050462501074030340142591002503050244a40c0d5150034140143e038010400710001502807050003049101c41e0003007141d20b2400d140da8602c21901038903250b0454070200020701c0c080010752a03071820007d0300c2c3c00c1034119040440124400509441c10b500000b400ea041c040007503c500c0600c4614092a8481d0700c0800d03280c001549986030803441c00300401c0c44c0a0600442e0350131000c20b40c50000c0c04034200c07101294400c25076160500444c0c2040505849076030441d100c4000c0c0024050343c90b80d20f10039184281d80c200500401603640380440308407000f006011124114125001c510043c007000d15012030280d00240d40c81014002901d140e0040e04100c0e10769455203048012030344a100305c500d82d8002503026080c10303d0181c1c0014081c240021008204d00e00b1280400d00c1d02c00c031070050382c044050b4807003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 508078669 1250 508077419 508077431
    0x1030b1513021c060f1a0c10020301090209040605090c0f180d0305071e0201050301090510090e0a030e0a030809060f09030a111c0b07050d090204330806011a070204 72
    0x1c481c0b4001540b82c2c0c80c24550701e060130310005509400e180340030708032880c01c035001d0458a100d0859080903400103503c04161700c01c022100312582ca0520045000300f03905d04005944400400c18001540d41e9940050f00c40e44080c0b0400000d030004030100d42550182d0000d00d070b0344106c407800b82000c0030b1103d113855400c510410440020103070040020020940a215403650714101c1c00d1104824a0490340c0090020f201032004003e00031054100a42081180711884002a101d00d0a0412110b0000a882c40e507803054030384006160308151148a21481624410f000b9415500d61640307a104523810140580c20000700314070b0440032042500c4501200406072190702c142c1e1300b0210008039000c0c007403030b22410400340c2c0390001c80c002e0181514819404112041d00d680d403414180c031940c2003c88000c150b9501d400d03104005071740d40d206e20b4008074917504d09a030503030440102c000c00c0001017000712403014a0b02c54003840300e02c41c0000e415045074001030b0140100c540d0065001610301940b140250040c0c01c1c50 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 508079919 1250 508078669 508078687
    0xd021305010e0105091302010c030f021c031508011109090c07060612031b020d03030515040203041401050106020f0a0213060b0a0c021e0109031211030c0f0c01050301030b151302 78
    0xb00d100760407250115a4011aa00c52a88018846c004108001c0c04500351990700720000340290a169071524460064036400301c0b889002a810301c07a100c00a600282c0e440c4400420710070200701034005014002c000f00b001c0f02c06283c90b9003a6203d09000d01d8800c5924100088094103204103c402c0258070000900100c0d503140c1103040c2101a5800031800b180480d081042111f80007a420200c0315001080b14425403090b0b00c0076001046d01a1000541c81030601501d03041c1d03211400110f006520901640414a1a0b251040d084a2040e0031901c210740000110702c110b00d00000d10009405d0301190a0b2060466500301c50004198541c022240040c01240320740c14079800c164140d42140c002d071000030030161580c40c07882105050401040c040751140e10709201007099004044a100c1c103a09007a80c100303001030901803464110882c001c6680c1e12000079655407003024041c002030080f00382000b07402d55045950b2501c2d40000107254640501c860076044070396a46200039802d4140704010304554072131100c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 508081169 1250 508079919 508079939
    0x40503121801030b061204060221011715010b0c010f18022112300709150801180912031a09010501050a1805041107230c0d02130501 58
    0x180c0d00305001c0000c00450300c01a540a03001c1e5000e1208000c1202c1e1405c80f0003c070810300444040c005a660a500340416400d02c28a503581e40807140c880d40f00410b041d8542020f000402842e07284013081e942000c903040409a203600d800b181512040c83c280c0b52a100c50020140c0100100c2074014120390414030060f103400070750160448018004d44244400c0d448a8a1102d05404a13030a4a916079004001c507901389078040c0040c1290340d150301d49076840740105203104840103a2034215041426044424000c0594010900c3d5000300a80200210410802203004c0d0860005200318010200104100d4240030300c65481000c02641c0400105000545200004c0c002c110103004a00381c2400001500e00601e4a56103041c121441690b4503490110211011074100200c81d0700072040c4d0308095804541941d407800351040064038640180d44845150600f20444240d6a00003004c000b40e20b0f080500000b00401d180342002c0054500307290050043c4041210341e00382600720b880e8035141031b0000c15140f00d5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 508082419 1250 508081169 508081177
    0x1080c03151519090f0b0a170406151a071e0b0c090a090b1309020604030515060411071214070b010f050a15082d0916120b04140304050312 61
    0x3208a00085040500f0020b807840d1409014801c00f8003030b500c80070003540ca490381c01080801c059143c60b10000c60300060009403d003080d2004c6034025101ca40c01c0d07209880c40c900200c001c1c00c2c1c4c0c42d605030040c00c0900d4100c1851140110140c0410100d00c11900b001d9402d40b1410f010903070000d4000c0c05440c05038600c8800341c120320403007486584c0409002400000600881e501640020300e020200c2091030101001000310450403600854244000030100c0ca050142d40f03000100096000981e262210030042115940d90303034902012024808203012542e003010a140b01211400d2420703651107501c40c07c1e001800b41240007424641d003400045030380641418408101c80b801d640f86070190b521889100100980400d556000805250000c6c42c81810304940100010b0310011803038450300e604201c01000c0600312a020041ea00c02c3c10b0b500958000c0c0845000100490302c0041c0428040c2e544d4120200c001900242c081030911601501029003030040394020030000702150b50101e0444011801600 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 508083669 1250 508082419 508082437
    0x80f13050306100e0a181505040203070f030f0b040501020f181302040312050f04090c0503041401231f03030207082802120a0b070302131401080c031515 67
    0x30200415a402c1c10444424140d903c1c0303c075100c111790b4413400c1751710043c071041900c0b120a0020b180403001040307455941c030780302d80c492030004036151400340107151509281c1d9000340d07200d000d07002c003c00208107500343c2c451440f907001102c480e15480d14105a8003900650113100317002e40000030b0540e42118002c6540100c0c42060b541c03041c030240e0003510306040307028a2001504902c0096009007180c0e00c07031001030070040441540c85040c90741f1503070b41000300c802e61521b080100303500100b880148046444404101460003001744107480c1546424080c0c0040c0080c004d0029041a000c11560a50326400c03120705102100148015952414002d40d61381451162070a98028144111135805001807440c892644203031501840200c59800e0100b4040c08041030f59042c09031240d21000185200e038660b0140802d40c1d009070321b480541409007100f01040d44841154045031441070b48590b0410101a40180d4a4803442d40301e03540c11050900d0300303940c007449030f40c481c492008141d000e0007020084d00a00c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 508084919 1250 508083669 508083673
    0x2040302120309030a021512012709081603030e10050f10032301090c090e0c010519031512050a030e030c0916231b0d09090207080f130503 61
    0x31480007a44030311520301c1881c0c05070481c08004015003003100e6500583c00c04030541501d441141000108810420b03080b182c980900e20a202c90b404010034420701100151401c1000f0729400c680d01c50402e449441d402c40000c0198210613001d160095100804d91503015065401c0c1d140c1c110705000040c00300302c8201011200c0340000c00c12a1074121403120503a075000082c1c5015035a0390498251040d00c0d0404168030390b483e10003a20008a80500700d44c01006610804107903980005d6145041112651080c0d042080602031030301c0d500401000c5403080b00040c140061110808010b000542d1102c0d04621080c0c80b2040340582003000008658070590b0180c0d0711160100d241c1802c268031400f20b404085d074801003034404038400030b0b144950750580c084141400d594030000f088070880c20441e0a0510011010049908810280341b4046426207a403110b0150000c1e540c0c44401505010141c050801580d90100d641c0f0108081441201d02d0b0f100223100d090784841e182c03440e0141c0041c0e1400380354064 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 508086169 1250 508084919 508084939
    0x20901090f12030c080c1e060c0a05040905090106030c08030405010921030f111902040c02070b03130c120b040c081c233606070303051f0902040302 65
    0x14402030608506440e8002402e2600c80c042d514102d581c1c21803000d003522601010410514140b00410042c40c004c1c18452071400c0c00320031800141c0c00c114000b807032a00014801c224828520342e00c20704840c140d440c1a080001c00c1d455070b06009004080f81e401c000c150f4000032001095441c4000054000c6603801da0324210226250300910304100e01d40240d1200c458103036040403000a0041203496034000207440d0581c444e0751058905481e0000c0c844000c505200c04940090541c01e1a0041100e8040b06000030070f0081d181c40e507040d015201c0100b803224000034041101d000c20206581d01d00050016010000c00e500443c10452545541a50100d4001c031111000242080001c03520000000e449180d81c5008041d0402c1a1500f003032002548142940300c0280c2c580c0503010038050420712081400b20000082400c2c1c1005807958440000050b0b500d006034090f14555031001152509949460041b5080d142c5020142c13075451440308403214420781c0351011a0751074481e40600101d0f40202d80329542d0f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 508087419 1250 508086169 508086179
    0xa0c08070b1f050f062b020d0e0f03041d09010905030f030108010b19140310020a020109021201090c05010309034103150603041a0c03070306140a0e0601110f0102090109 74
    0x9040d2984140b9411540500a8601c4c0b00d600901546055021025111514803803030900d001f243d000d043e2040340c2603502c03003640700c1010f0100650070790b00c0c42c1c2400440c07915061285502a2007101207901c1d1544554000190601c1005c2d00102c0ca0268400101d03038442501e10328051081e0401d004d961410f610300f14000c0000d1802d68140101560024841603c0c2070400d80500403000ea9041d03240d400d44a01018154106110720003032001c0758a80c0c1c0001942c000d41d00c10040009a01442c84e03021b031b81480303d074402095007030346e17488204d072030908000862241a15055807401403a41c00300034500242c41c0f44070001c01c4200811088114050005000424400744030620782c04161b4168002d060300c141114020704090b801581c000d405a0507070080305411100030700c560714040360020344851020003030141d5190135000e020094050140700501c25410750001c5562003505204074502c100b1184080b420b143d00400c445032a07503554009903071001c40c054a8041c040d5101c12845400a0710070350000035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 508088669 1250 508087419 508087429
    0x612020f061c020309030c07080120030c030c07020d120801030c0b0a08060f0303070f060b180105060a030b221b030506010c03030e120301090c030507020c03030a0c08070b1f05 77
    0x4086081c2c501448024014061104002e41005000d540b952100300071800c840c29040040c84000d00c009000860305202c001e4140c500c05078104550701e5090301c188140321002980c9c0003503a50244c00070360703403d490311600c3c00010355841a03031f04041c0160b4510038040015591007242c0034141d0303021741e1040b682746503a60654a26807207052858000102481c01141451801c042506090701d00107040ba030800003141c071035541c81101725104656559480400e400030303013081c42c0d0081c110761400c101041950715001c08600d1600c1050f003c0402c1542e80c200304101d9a41d420034810b40c00b842c0348103440e60f003064550040010f141000c00d040110b00c0c0c03c20f00045441c442d018081c81000c2c113a50301040300005550990107000c081e484a0b14074001c2c1e401c00c0344400341c2c25001e940201040580494500345a00c0054111032014101c4c104540010100580e00d403030001c12641d04050910340102401c00c03d04011741d09004642002308076030455010b01105903041d2805404242e008810018032a07603902c2004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 508089919 1250 508088669 508088677
    0x130b120a0b1215060a1508160c0c12020307030b0a02090f040c1b1a070306180501031e030e09070f08090c18071b061b03050402180c07060612020f06 65
    0x1038183d5201e0390000341081d02d1031100315046000500a10310460700c410a03c3c141003a50034070000040d4207941007101e60380140f9803414100b0301c0d0b0b0501b008408001e4844d16140c035a5801804c1c10007580f0206d0350219107081000d20000e54200c1c003507401c07600306006848003941c411036460b40f040d0f0803242031541c5440d042c030460b1084a4542c5841802c11a9141840002d0b909881e081e100300c000c1041e200541008040c01e184071303141c0c0c0d5400040450030441480200801c12711391010041c40c020040c0000381000c0800b00192030100400d005d0000d0901e411181d80701d2140616400c0044403043c090003d03041040c8080d01c0c011038540041641e501495035586503007041c007003540701c0044100c0c0160300740d400d00e1654003d2000e2922040348113400c4d041441348944e0030403c813241640c8807441c0710070000700d40c1483c0412849240c107010500f00340d00000c941c1c1c070b50f41040385d00310390441c000714181c1c003071100846070f1070755101e182888456550100d04040840d0458140c3c00f4a030701381020750b15031502200721 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 508091169 1250 508089919 508089949
    0x50711060f01030b07090905040c030209150f01031a0303130806090d120b0d02100f08060d170307022e0606050a020a140f0f010501051c08030705130b120a0b 69
    0x2003101030780395458800c103041014200c00e0030300070308a0001c1f5042c402c50261b14400c034060480c0c3d1b240c040c658414401d0b43c400051144241400f2125000415034038200000880e2000f4600800d8646001040702045158020342650503c40000c4001a861844181c40b081300c00c3c18060301e040d035075059006a01c031000503101c0300c0000c1603034246503541181503202541540000c0c05401154116901003012200e4640200c80840c000b00e40c8445466404001d0590041d41641d900c2180d148695500b0300c04c1d4038640042030141000b01c001101039200300010402004501d070b4500c0d07041301c01d211144150105141c61103140d405c10f4000305003030740076030112030500145500504000d407490b1074480c01340050703103085d014a00520420951345982000711b190141002400081c0c0da51504041042c4002811a965285c0c51040082d4005c14801c0041e0781c3c0c0304141e41802c03651610700c0701200e00c01920a400844414801103103417030700d0244d081080e520a1141c81d00030480e01e001001001050300c080050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 508092419 1250 508091169 508091191
    0x2d0602011b081e091501080c0303070308090322030c12020105160f0204051e060d0f140c06070b04150b0a260f01090b011d0c0a020319020105071106 65
    0x70700c00014410940e165010080d540440640d0000e400420580302c010384800003540c4c40150303600e50b10340040c100c0c00c0c01000240020100780b5007120100391280690340d00501030020200006100100a10882c4d0800c04e00c5095200f40c1c004620b03020514444030b01081d00c200e180000003003010007140e4005400070b6016151241040c04c503100c5100e1070700c4072240481e215200c800454005840710b009090155201c145903120b00c821320782d039131100e0500c000c044611500310443e4000c0410b0100c401200724541082c140400329088030b010900c1c000c803003078290b030700301c040001d4503428058401c00d003030702031782c800e228a0802c040ea524109094420040312254002000c0300c003008403486904e400c44041200941010800d54902091420300401e42d401c80303180d9440d00001c1c42009150310500b030150140a081203d0f00c014081c0052203144014100080b00d000060030805460003001070f180081c2e00b2011401d548100303514024003814040e110080800c03190a448041010085103103485102c1141c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 508093525 1106 508092419 508092461
    0xa0b041406070f08090d0f0c03031b050c011812051006050117060f130504050c03070909030c0b18030705030a140403020108150a2d060201 61
    0x9400c40c0324000410078000007034042c0030503000582e00300403002d440321090130106689042c8130401170714250031205004104598100250180c0b4460395a0300607001c507d0203e40810301118030020916041040c03c5065544114452000c0c0070544248492042d5a480e030320f000d050350901e09961903040416013244030780413030003003800801007031802d210243d515800c2c0d428031f400c01a29a610038443c44900c1ca40c1b81d60380c2000d20740d050180d0a070400090519142c860f607100340825100e4000e0043c2c0c180002d08034513030301c43d00c0c440c41d41503201c0c802d0a0100355174410b0003000c001c000200954112068440b0742d00b00f0006003409500c10402560307500c40c4583e02030243e400501001c503018104000030f10050341c3c0301d000660006070102104024144c8140095224441904020101200d512140307104244549100582c0800840c01c102540d840e0f04c0c0c101c0c00d81d0850107035420b600614007 = true := by decide +kernel

theorem cover : BRFrame.Cov 507913669 508093525 := by
  have h0 := BRFrame.cov_init 507913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 507913669 ≤ n) (h2 : n < 508093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
