-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5560
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:16:12.97298+00:00
-- url     : https://prove2.me/submissions/073e7cd7-a74b-4eb7-bdd9-a5d118e91669

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 999820143 ≤ n < 1000000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 999821393 1250 999820143 999820187
    0xa0b0712020c10050c15070909090203012c0f011b05030403200d020c24071e110a0e190c050702121617030d02070201050405030307050c01080915011203 67
    0x1d10044c1960300300d0a03a0707001c540585000d40c40f0b0103400c0d030001e5203d0041900c490341401d0901c40c11000411091400700d81641d80e84100141d101d07000000140030b00b2048400420030342107c80f1a0303040800c2003589030040e0703040074080f0102c010f240014945020042c90700c50345954882c00c0403202c0012000360382100001401e0b41010304580400c0c882a4405503400312282900c80c0010301c5048840300b02d2810024003c5513100101c000c481008000b824041c800ea1101c62808080d4402d002030168411074000054800701e03e10b83c01e0804000009003400e10800010346051405d5462130003450105103d601da07989da65800c941e000e101a148099000b0f000c60a07884000e0400954403200e4a0b206100c59201c400005610000c1040d24581014060041d6042c0143c2c144900041d40142104a06000090001041c1070700c0400262043ca40204014800344944000142010401800791100c40d000080d09111946035102118112440c905111840320503504080324a0110701504039202c40c42 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 999822643 1250 999821393 999821419
    0x609020c0a02190302130203150603010f06031406060d0b12030a020304030c0e010b040303050307020709110702040b01050f040513231617010b03090a05030c0a0c050a0b0712020c 78
    0x9044003068420b07030700310b090358100e0900d640508849200080d4400750040d6500006c0403560080c1d904070360744010000b13154003000000ba04c65042600404040316820108008455240c01000c0190201c854101c030306051071800b1462501c114084480440d8131107150206a0b20703100c00180200300c8403020380ea180d01800c0d03030081d26a03100f03202c1a078802100d500082990611141614100d50070f40254078581031555400b036a454100401072000d5015014000600180714051b07079801008145c082aa074040910411044440c7d03442064100300c0107000c048804160101140d0a4540440341d01105d0342151708c3c608003412910100c6082c02d034144ca80c41d200d5108222040b4040d02c03c2031101d141b0031101510031121109445100041606c0300c1d001084014a440000d54000c804981955040c0c40c40d03071540e40c40c645c84a182c0141680c0000a40360a008420491038003600045444840d082d2500e0340588240c0902e00010304407581c00703451407001c28004c00c542d01c640030005d0004903512070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 999823893 1250 999822643 999822667
    0x9120f0709021b07050f13320a0c0e0d15020708040312020f1507020a050a030203090f0a0b0f031305060a052409150d08120402011407110112060902 65
    0x340c1c054504160742c20010f048070707404a03190007a01d5001d820100e0101c070003400c01c070f411840115120740865407000d000e0317031031509414110750607081d82c44250040720681c3e4148980700030040a03100020302d011860388486602c00c40404104104130fa4076095240c2c1c50808420600c0c0c10620440c200b4400101d82c000c00c02042c01400480780100002c08041503814802c0e81c0b1045191110340054100003020340030780481903080d03604080b00b40f0440b1903911944d40d0340c600d00035045005501603400440c1c2d04602e80740c140e010024864007680d0343c00083e40383c40102c46041c06000e200c8035409102100150301c400606224510b0250464101d0f1124113260080c1c40082905070b84002c03040f107241070b2018107106600303000850841c024000f0410f5070340f0403030f0138600d4081c1c20107055486686e080709030010400c040003030b1044110949607100a814070344005481c4c003400741601135071a81c05106000200e00b800000420040d82801c107040700028082c0654002c00c0d2903013100e02e6961001c00d180d107440d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 999825143 1250 999823893 999823897
    0x30c12051b2701080106081f0801050a270305180f0a03032606030c0907110a0302010b190f0902070206070f061a2413030c0312020d0503060609120f070902 68
    0x2141c02e00340d100e1150319010046802910034080d500c0800e00150105841094000c15000c0010300300c50005c6000752034003032031420742d14151241020700b0f4503014941c91440d801b032000b801c0b2a1251000301803114407a500a41a400307a03888100c9030304030034010000d2540b20b1081820031848020702c900001c5071030745000f8203107a00d00e00c030311410000549210200c1010421406000e0203004000f41038210401d004c0003803400d0024054010094088182c0f000048100004141d030352003600046444482d610034003001c8100e180c9075100e1680082e1040210040c8828030005031404004007603507a4882c1d0000ca5068032580e90300400b101c07007800d510f2090142c0e651200800e0031603010303110110052081040702c1d412034010752030225a1100012040005280000e21903c98000031404c0c18560f251111515240d05078000e850030b80300310f4031031405285d05000201154002e4141142981048404a1864010403980a024403046000b03896913040c200004100380c1c01240483d40c40700c0d03e450240006e5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 999826393 1250 999825143 999825187
    0x1e040f08010c030203010f030f05070e0a0609050f1017030c0d05042903220515071e020d0e030f0d0504060e0103060b070803132a06030c12051b 63
    0x754a0000940340c81d034424001c4030304903000c03805065000c60458449060f82160007204403401e110f640400a00002000303602489007034420303400a0391518203076090090322802401041482420000c0010221248905c001900ca1001c541c05c010780c440013480c0d00e544500182540184100c10550282d03640c001c0080040e19a041409481c4c0364010410410000f13001409818a901c01e200044401c0c81d884a03c45808400705d0901e14950b403280c41c2c10b4207010001030006991f000c44030801102039040300041340105d0f01502c850040e207281c000b000b034582d14040c043c48204094001150a0341e0b80821005c0340004c3d01c481a03e1070011901409802503100744140c401160003004845c4440d030281c4120822a0760130aa03152a0003040d49c1c607088958402041951b40080c11407034030011a001d0900c0c80840200794170045018241e0402e900348010956001804042c10814640140307a4000050301080c10001c901103000c0e2039240c1c0d038400c0740c0c5084403038a641c1140071405454003004005142c040c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 999827643 1250 999826393 999826409
    0x40b07080f0f1e073c0501060501031d060610030b1201051006032702040905250905161101020912160b0301080615030304030b0a05150405070c02061e040f 68
    0x108242a02c3c61245030701030181c0c00383c5200200840111494891001c000d00c401100701c03000d4058125441d5550070b8101c0d82c0d41500c45a5442200b48000c0d60544102196400b0800e180801c2d101410022036a400008090500038800300d80d910744454020303000b03001c051400406004001c50174120040c0285002c5034260403503e00c2010001c1d003240a881b60888440c6038500e10751301ca180c05d4858407058090300c14220b0704035944080000c04542c05200d803207041d41043c015209071440780036151100c00550f410030074000303180c0003c1c0100110302e50107000d000e00c42410303c110100c201d2400c4500a00403100303615004402c000c83d10742d2144000c02c100c1c440072001e954444003140c0312074110149003c24041c00d07059a00060105420381015050525210b800600700c07460035440307607280382d0070210640307001064645400904c179021403840010501100c003036408001d07178588034000400381c01440307a010b806414005410b00c12035030303c101c104000240701c000d09581c9030340d40d0020450980d003038482c0002c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 999828893 1250 999827643 999827677
    0x3090a0506010915090b0a0b2802011a01081005030706170f04020904021306081006152f070e012c0c0d0507030f051f050d08040b07080f0f 61
    0x80184692003026504c002083c8043e060600b07040300e21006044100c4140d91007420f503400025060100c000a0144c1d002c481480d83d81c800c00c00b456152081c0e9148014401c0da418000c0c00c1c0340340c0801000104400b042480d15006648980c24803180c240086d07085075416001c0c50b8004200c03590007100d448444000c0744443c2c403c9039107034250322502c04400c0e81c000b5805030880020402610b01500002144214000000346042e40c540d107440c0b80c00c507541c0c09907400c6034581004000071002940c010003d440701c0d042180b81c000d043c00000f914007013082c0885800601c00c1d80340e201c032101308000920140a0444d140300c40c558580b1701e140c0404411142d00c0c0b0040e100fa0102c0b120f00d0041d00d40d054080c0a050001c181000c240c1d602c11030240c00020807000401d40c2e0782280780501991405002d0103001003074000d00306000d109030102c8143c8900d8001c24002c0d0400302c2d12100040d00c48048504985500901d2610349001d4a08903a0611030150100e60911001c00c654180d01140f000a002031509490070312 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 999830143 1250 999828893 999828899
    0x180a08070f060c0c0303140f04060e010e060a020c060307020111070b011a04060e060d090b0412090906050d080f130608090705010305010617090c191a0c0307060e07030803090a050601 80
    0x100d101e03d01100091080e041c070407003000045e020300030190100c0755812200d4107200b00c0c2404818070707400a500c4100055001c5640c01125600682070940921055402c289861410300c0040d503030381144802140100300000005488038401c2d0300c06c40d00c402c2c00d090102d0385e0300410705000300144001c0c041c041d941c0341c01e21315a10765141d150080314100c0741641c07205000c08080d2401c001d42e03500628038480f511511001c0400014048015540c807035880b44440d07403020003410318010310360b100a402101c045890540148240d682d1203440d070f2903881e4000042c43ea505200f0507103a0017802050032810140303240c4032011840f03c0d00020b409205401c80001c0301c1c402599000114141d40081c0b02d0346010075030b2b140101400010014040f0750107001403044440c0440c042000c5090000c0da000c50050040c8484010f02240322481c4031120003032034050315a4100386a510f00c0c0f5881c0d1145510007030035907540b0100c00091140500044e0000e42d0446100354491070101d1a140e11000c0c4440c1c101d4960013914008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 999831393 1250 999830143 999830147
    0x301140a03031202030703090b07050d050a05090c12160b0403060b010e150d0b0603180f070b0417010b03060a060510090b040504020d02040e042f03060c180a08070f06 73
    0x5001101c2d0565030b010b0030032080d1102e030341c02940058a60f02c101511581000c01050b8a10b022501900381c0d41d88070b903034601c080c40904003222005010b90183c0390404084c8814200000341d90410404101d600c10403203e40c110100b0b10380b814980d00c400a2003004000010b5072032030312000d001101c0c003c000c18407411301100c0c011501008450159684000750511491007000038001810186217051000591155034000050058001311558440104403c00034040704000380055401e00c05080010b185050070203883c40070074000e0b4011030a04580c910250990142c00350041248100d015003959994203022038214060b01550081d81c0c05280941f00c09650a8410a2000e0460f028040d9241c1411706040412003e980300311010240c01c4c0d002d00022500c00b510f40c03846401184104418408015920f100c0d040311a00c2c9007078110300a0720010b80204d01e07103000c5201d41c2d00142100c04940d6480c03050440c0d860608002c2a0321760000b20804001c1015500002c0c5c00059400302400c442085a8603001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 999832643 1250 999831393 999831409
    0x6070f020111030127050a0c030f1107020105160f050307120e0306071b051b10170705030402123c0a02090618040807113f01020a0302030114 62
    0x611400d0b034000b00010040c2007504104405446120101e02002c1410030392040c05a03802650043c4182d40d640d0201d000d8603800d4813884000410950052010300140346104c580c0d401128070181c10f100e070003e40c5940340140500d6034a82580c0c41700040c1030300071170b90404503980d4001c84005c13120902465003110540d030089444085440f0020000c20560f542e0040031100c210349036016000c801c031500d0f44040010390501c4501c4000a001807060315101c20401003148809400d4016000d10080c40c85841d105402c038080142c0c8500e641c00c000340d998507a807010074205141904200d100d4051b14844101c1208440c0760030350441c400240c0c01e02c605960b0428080c044032441c0c45110658410340b601801805d1a0304c0407a0321800007000c0584e64019600c101410785400c0381c08803072540b0006aa60104807582a01030341900d02035800c0c6081c80d007580010456440820344079022402c0c1035880d411b102150040801034000340800a42d104c005988014000e500f0030700451900000c455100303445030a000030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 999833893 1250 999832643 999832661
    0x2070302030c0936030d1505060702090417070b01140a0603060503070302120319020d02062809060906020d021803060408030c0c07030807030806040506040e0705060a050c0a0506070f0201 82
    0x18851008454018002114961000005448407043c965044840c4c00510291210700030314040419822a9141c0d04400d00c030554002c1032140c1418407140c2c0c00b684034519403a9000b58041c1403296807a5a103020030869000f0148000c3c4108c04010001c90024181c404400030340400b602c41c0c050b81c9803101c1007507040d40e400e8001d00303030590b00c296000c202528201340540055282501580e10308420408481003104804810700c01503030080c4885480d55904002c0c1561200b10070390403403149040c5a20010500c8804440c00e8030894954a004041c01400ea0115030341a40c400c20440d900c0b000070b80e0700301c0650840f40b5005590031104181581e50f050224610788590750040c400c0d4611781c5c035605040c85607001a80003403503030301c5003000210001c3c44030703401080030500a0715203802c20300c2c0c260301300701c1610380041c020342c0103a0a0060201c0c40c1071000905000381c817402c54805407980b65218085615006421030801e1501c160700304501445404100341d4003a10141d80c0e1000c81c2e1050040503400c1c0c0300140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 999835143 1250 999833893 999833911
    0x52703061b2106011806080a020a0201141503100908030711070f0305010227010c06200d060801051e04120e182215020f0f0a02070302030c09 62
    0x40000c1d4194000360314107903190000c00c021400c240e00b094112812592400d490a52046100c003801a2980c01c010000c00040c1c00b0080c0e42251410034031b0090560a000e082d11070042d402140f403000c080d0003900030090290588031000352a00d4450100120702d0f000d0741540d8040d00410340c0060b40042a80202c4000c9500030406500c0d5032111042110480e1025800080034054101d0220b049040c1440368001140524005601c1d03000c1030048290b1002c1900c0c403c00c1c0c40044103418180e598100d07803110301c515042080000c03440e8501d4400c000c40307071610b81c455403004000658a05c455400da4808019202c03103070000c2105580c2c603444180c101c1d03011440e071050b40c0003520002d40018619491001002220b203400806618a0ba002c00c3c0d458404400400f121020a010011a20544544a03264011a266050700c00b2407680311504203024011070010120b400203941000340c0c0c840c00c200c5070100c80c280700c10343d910204244020f4444003140000c038424051415000d680e0704e080008a40101030716 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 999836393 1250 999835143 999835153
    0x105070f0212031314150a1d0c0409110406030f0606080304030f06050a060b03070e031b0d1506081e0607030b1e013e010608060c0c070503030307052703 67
    0x1c4c1c1c0c0c2c6a6540351205000300c5030b4980d0380207481915030043c0b02540300d0070101000c0038102d092200020b000e55030400c1c08250207195460903242a2540042e1070403903401c041d2000540d0010740e0909404149040382c3c1280c01c01d040c110000100b01009090142041c0038250401696444003980c0751030303215512024000c0c001001030240420040e602580e0070007188500019083d65510002c1510380088511381d0201c2e15580a0550a040603c841c140080071000c0f644203c10b404000104070141103000501039009a0750b5212582c82c007580800058104841122030080741c071a042c441c008100703100d4101c40c0c06103901080c001c0c0d019020f00300c26004010100d4422000d0340c0070a05c0307000b5101011504000031260ba5030006002100d27010004031009285018032195012404401c05525141865680c54090b0800000802150898010135022140c0d0358a09030700c260b4500d8410075803c0740d5414040013061011258000009102c4503d1005851041d40a8546840042e88000341c980e40c240d000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 999837643 1250 999836393 999836401
    0x314120615070b04030e0306060f1c02030a0503040e01080706020102090a15032306010314060616050f0d0203121e0402060d0e0304091a0603070c081e0c0105070f021203 74
    0x49580782108003620704960a090107503ca8892003507040e901034000c9085c0754121007044c14284502d0303500c040140c80030349130003048001050416007176500d02d0400030411403c12003195030a1100c000d010b03402408603130303c0d140c4412400241c1a001e11031701c1034510500c1000500c150041c002d490400d00001d00f540852458002c00640324007510b042101010341e124007021000c40446c101d41100c01002d29906558503200001504980300845100c80002d03a940401115917118030071524104008940103034880756034a40207180205d04100603d041c01440d03a0000102d90000290400f60911400411706890390040360a442030030300701480c881c0c0d903188005070240c1003c900071f100310302003d003001801c1100d00140e40c2c1141c000740c1240620303580790021001301c3d5403180b03144544284110703000d502e5814105000360506444200c000d08a2101043c0c01d03565180c20040282c01c40304000100fa03540c0c520303600c40f900802c01202d029000c41c10220b14054982c0c80000c003e100c0c842041401455511 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 999838893 1250 999837643 999837649
    0x50909031b12160c0909060f0c1b0206070809030d030510060903081e0f04080c030d0503090607120b04021207170907090b1306060c0c091104030b0a0e06100303141206 73
    0x3d1404081c1c4940b44059800594041981b14000002c1c3c010b0ba070001d820005114180c1c19a288082c4100821961010026140c00505840403003540c0c11108261b507401c07689041c124901441e0503d5515000c1d1844080166400d600144e115000042a10700f40540f01c4005072500320440c0405050703600144000d6064001b41c2c285000c00fa05400c280c03e05200c0c081080458039489900b008113203401064242c0228102045501c1904e401d03820720382d0540c50280440c581e40c160013011042008100241c0b203842d920740383c0c0140510b00c8041d01c1550b4825420b5418140c296060320580c00151441e40c802420743c140c00000c0d800350030154043c002443c6080502c0700036202030128154040c050b40c29040040c8070354441e01004104d15141d200e4020001e0030400c41041da503034410104242801296118052800111000c3d80d52011642c3c0c0c0d5610354003d048028a5071842c941081d129100c103011240981c1d44e04103007124800c0d5291404409081004280ca01030401031050380071205010600504d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 999840143 1250 999838893 999838927
    0xa030c0f05060a0813060617030705010501240819141e0c0324060d0b0102060a0603080405270a1b0309020d0f08220504180203120f04050909031b12 65
    0x40c0078850101f00561a00644161104000c0109010f41c1c0005849410003d082c000c40b401042402c00380c0d00380f1a050900e00700f50401c07094000042041450005251080300c2d50010b2110400b800100404c04c40e400200306070704829942003210004100081000c3c032034101d00e1920403490700b140607003180c641074801c005c000000300c100306404046000c007242a48500c00a051303c0041e915021510480040c0060b042000c00307882c042c41207082210500118003008202c0d0212001912400d1240089400c11082084001d40b4480c000c00404140031124810f9001082500a000e43c2e0103c0352400780c506a00300c41c95807000a400000382d0305283c010802e00c01c4410030a60140a080d4500003c044100c100d424120509106014411200b0300c03c60506106081251107640002e000544440e000680e4918400c00c80c2103285400103240030303442019005540041601408904841c182018450b8580d045190046044100c42c5a02124610300064000301c10324001280b51070320500d0300710b41c60300c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 999841393 1250 999840143 999840181
    0xb070b130f020405060d0212032a06011401090b070f0302240a020f070203060a0c090b0f0d0e07051903061a0a0e0402011b0b060301060807050f06090f0a030c0f05060a08 74
    0x106c15003442c2ca0b005a100c4112825034036200700e0207180e65691020640c03101e1090a1051655090344c540660761040c400034074541980c1401c841070001c0068040100d070000b156811045414201040e03480400074841900409903200c4d0b001e44403564a45040c03481465540009030304a1551900400c01c1c03c0c2441e40144101e4900c0f40c4111300d00000b540109141003c1510001d8001c1d030781e40c02c403001c495031084210000d040345281c50b0b0b2030f005401528102a0250321410038102c4c0c0d41d80041e010399482001135900803c0060080748291000d81054803200c68588403c0d900142030031014000c20b1300c03840d40b0340660003000341541407060400c90b1680001c030b4000c100300d06204071200c3e51001d10914486692000b840f80c0c441c0307012450180c1c145820350b4015030200c402507200303090900580e503507190340b4031202d0020327131b0302a41b40c0d9640e000043c0050b41000a894202c441400048140921440b021064a40700031500280303940e24014010644079400050700041c001001003200f58521794080380034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 999842643 1250 999841393 999841399
    0x3100e04050304090e16060c030e09180607030c030e150c0f07080715150e06100c0b0c07170a120504061e020a0e041b051b070b070b130f02040506 64
    0x8140c0c45059401c2100d00d02c2c03d48001c1756202d00786101d004044d100200001d082c00d03240403200d941d42950b01030410482d04200620a4180c080010700c44095004a02d40d0600454101c0704241044000600105810380d140b00010341004112030700c1c400c0004003188c0340110070001e0b144942da10213440001d5086803c0b10240c446081004001203000320000c1c000290250400b04600003284041808444d40724a20b0b4079414007040c401c10400c241d1656580d071010302542d01c0d2452101103402260a40300c8110001c008901500a20018600010290203d40c0c80351a591454412074016640700e030141c6100e45002920000c600314400045400c030340d07045807040300c000c00c03880450f01c0060800d0600f0030b01612003036401b060404071558000012080140140da08104103035020b004004103140c0d04180a05100c1c002030600c2410081304400412284040243ea1829440c0c1c8000c2e0003d500004060310b441300d5080c041001100c68034421044240d100c00c813800100041c4c1d0a00c4042c0c18014032440d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 999843893 1250 999842643 999842647
    0xe06070f081b030a05040f0909020a050603090a1e030908030310090b0d12080420010e060c0316030207150e0f0112020409020d02030420060313110d1a01090203100e040503 75
    0x441c0e041004c2c0a00001d035489064039541850b9108a00110316446000701d54102901200940c491840803c1030f0ba40a45815540b59108072003a850114450310003807540e0a104a420003211000304c5652090b41700f0340d02c001c4003c0e5114a2203a070381c0003d032101603511b00240c6041000e6002c5600450640740c0190070340c14103070300a441d02841342002d07a1003400456160400c102c2044119019041c0d0031004404a10041103202c000820f0380c40040803031030003424001007d5640440400580e002d1922100205903443d03c1303440d00039100d1160f03204021266111b403011640b03c5009041c04d15020001a11968042086c2d42c0111111490301c10340c00a4298200400302e2140c5140c001031007503c150300c0d80983d5905051800f1580c0c0010240e204084c000e906a0503081640d81c901141e8121462139481c00c6400541d013040b041d84200d4490a80c0d0180a2023612001c114000035500b10490401103401066a80c417200700c401c1e0b05c02180d034132520884d0003500340800c054045203ea0824001d00c100c1c3c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 999845143 1250 999843893 999843937
    0xf0f1c02150d02030f01051516111c050111070b16030e0706020d0e03010c0504060503040c2123030a0f09050613030203061005010e0405040203030c0a060b010e06070f08 74
    0x1c9070350703440261440710098002040048013080c1c0300c861401420291034130310004004840c0b450950103041401c02034800c0d2a00c514040c005648144024250000d10107242013101040314080c42004000444140d401e05400707801c5000300500b520801a04005000d00c1a5588450540102d10350200e00082c103540d10b01c082000d0030104000c401602c0e041e0014804103600c01d502900b0051451400c6200340c1c1400d0460312464ac4c40f0040d142218107a040c11074881c0c8482c030304411500d1082c4c10502401c0529206030024000c01c00307043e11480d001d0100e044240030b045006102c015501c04a40c0d409600420517002010f125044009140f401031403d5500951544002101a030019150300050b0f07000c80800c0c01545000e2002c0b64202c80c14440c3c1ea1891460840064440328040f81c1803480b5070741e508001015520144200c070500b01d040001c1d43d559000070716240000740301c8100c81500043c804015807010b800c0c5242194005a00152000d00c040315640d6120071a40c0702c01e403182c0c1d1407c0c80825030703 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 999846393 1250 999845143 999845179
    0x15090b120a05010537330e010b03040f0b0a060807080303090106060801081c0e210d03090206030a0c02160609060e0901290f13050f0f1c02 61
    0x9040307068416000071903035003080859081d00c0b4018060b080f07000d10f00c2641064081019403c030f40c60243d41c150001c9810032640604100300c180b070301030b00d540c2082181401e1005902288001c025554a48007401b0240d0301c50300314034894003044800411340814422100c01080d00402115800041e0030740202e500c035150b8451500f04111680078100942c404000d1081c460300078002d10015109514041c14a90f00d80001155503400c00c40c942e4100b14840302441410034840c4900d4907514030f018102014858002c011003801e0810002c03178440e20301910b005861254400d0107122402600100b02e1815502d961484400400311030b884bd505611681401001150001403504000d0100c0c0d141c0d003030f0746894450701a00c01621924541d10426000d0014041d0b00360300545100008001542c2d065503240c00142030000d81700744e4603001100207002c20340300b944c0c440600d040403c3c1c5a060f40c0404000480c0d40902c41582895145580e02246c6c2594050180e0400200a00d086000030705c1c400b108810b003e41 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 999847643 1250 999846393 999846403
    0xa020a02192310020a03020616050d020a020c180606040306050c0c0f0a0b01050a0f0b070c090f0b01020f060601300c081f0e07390c060315090b12 64
    0x1500311003a003889000300549400040048403ca003030001e0f04040c8190354000352644001020811020101214008000c2c8200b058440b070005400e4119550845564013950301d01080b1640b0748540c4c120003007c5051001b8080841c040c0390082c01090500d41141d5491001e8030005100b1421030700c041c0580c0c884d0010803c4010003904254020f0480c099480c20320100c0c0c100142c003c28000ca5207e0380c10403003050112056003c41ea8182c0e10161250a01d00c2c040149402ca0350000c107406003890700e40c003003428090380180c4001809800f01c40b464400340c0b408580303c1504480340c0303010450004c640500c3e502418840b2800300b00a1b0724901da0203001a9540048400c1d49000c07074002018002040162000d4030b111041628201d500794580d245403081c0e070780c0920b60041c111010000103c4859601c410700c065010000340d9a8640c41c140d00005140c0a0301c0780a0145041d03070210401c0c5c2001480500900c12800400d40103d040d89105040c40449000381c03001e05e500790f40050440d1040701207003406005d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 999848893 1250 999847643 999847679
    0x1c05090607240204080604030c210809010e0f03031611060a060302090c1206061b030d1506050c070e06010c0b13020a05150306090603032101080d050a020a0219 70
    0x500c030030098940c14410120300c01c00005a0344803c0c070402091080c0800010881d620550618000c5031002082c6049140310065a1140c12030101c0c50b0340e001c0640d0740210080d8820000c00d07008026507206801c41c16500c0c062140300f09020b400800104200c525034094215070b04409040240c003005215407000d242010032120815066070f2040c00b402185880c605803900410620a501c2c10044e202115201190307004d02445d10038100001c1f501c00480b004101681d42c0c88a59003526282d4103514030304005851085080050007510142c00308815024500303899500c80c00342c00801d121800c00360002700240024003004e0522654015100005401045d814414030b100992030340e10280d14814042a59217540082c0e2040c04180324480585003050240d981c041c204613030300d04140d2a0a00401e0541c030901181c0c00c520122100c00e2414581c900d08094103c800708000c503924101e19035000c4506004001008005030030814000d400351602070f14141611035011010501241d070b5046040e00041115 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 999850143 1250 999848893 999848903
    0x10060c081303080301090c1b150504020f060f0910081006083d060e06160609050109030206070e0a060c081803030a02010605040b0406031a040501090503031e06040c021c05090607 78
    0x804008407d5400844c00701d840c0d48140011091008980e206003e0030041010040341030750f1040010159655010700e0400402c0c050b0981e540c8210000245103980d22103c413841c02051000f00290b0942d110f00741140c800d0701641e81d81c004103070510328200d46048000d031a0044c1014800040d058100e0306d01e1200380d038400c0c1c0c48040c01d01000d18503045210515954012814401c0c002800c3e030403521007804903401c00c40e1281d0504c60a406502d400c2d4010166407170090102e43c40c0800003c1010707000031383c4602803003154542c451002d103141d00700302d8110054055500000c0c070a4012400017880301c4003500c0e1a80b103490900c010b102000000c40d10315000070820341e0050303449020030459420144100250307614240d0f4244211820741d1240b40002000801001062001c02d000409001080d07021214082c1c6c04400d49549081c05901c072408900c100003e8440300c02490041442403400313104c0c0c4450311406401619550f1003401484904002c1103c8450600208010701d035013507a03030a401407a04034811 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 999851393 1250 999850143 999850151
    0x90a17190c0b090c06041221050408070e010503190f173c07030504030c030b1b070b0117150a14091917090d030201090302010510060c08130308030109 66
    0x50410424200c0082c010003404d42082c034503818141c031810304690560300411400030181d18240b03005c00204401040341400c1c081140e2110b0341c13980d4040b004204031003100d003c070780003d5111118000c4c100360030f114480d816400598400c07411000e200075007013851b0090468903803a0b116a01d030b80d04071010459110044410024800100d402c08003403c5102d0700040600011131407141032032425428980b082c4500000000c0307480403c262180003114041c41d40404c3d1859545c1e034a00d820408014103807002d00c2c02c140d003008482c24200000c4241c0d0300c03154202540924a920300714a030180042c4200710300c4814015085203000300c1811071010341c094611200f000483c011010403202c882480075000c1c00342c681008845c10901800e202c0381d460b81070b412110702e0031070403942c0807010118400c0350b00080c0c108101046800c1450b17010751000380c2c130f607000e500248010381c2d400044000c480712901841d00411054450708003c10070000240614800d8805507808a83d00d80d1550040d94000b40e000c18680da8035 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 999852643 1250 999851393 999851417
    0x2060118112a0d0e0910080f211804110408030c030c0f070b0d0506040f180302010b1c03050711060403050d0e0603010b16020d0c1e0b03090a1719 64
    0x100901c400c40c0000700c100500826251203d008118141d05410540b08203e00c0c1e0204941024103014100180b5031001242c1d44140340f100d1498440b0760352030207240c0280300d850074250091110001c0343c43c020920b03040c092400c5007000400005111308400c207102400c00f4440842c250f00c1c1040146107029420009685404030751041c0d41c0f400c11a8840d07080150082041080503031030b0341d029541c6540f507840c0003107100d544000114008004020300e00000b14200202c01028613854041c1c9011640245d0091010002c0c4100303000c99040360b0505803480070b01103030040d00482d02c9200a000a184501c011240761590100082e15503000341d0000e5425400244020700c0d45a0003000c10340b003a040070b42d4018115890000d13035401e9400380c01e000c110740d102060012421503841ca111032400e1540180001c5903c0d440e00140d82d81904e041c20301c1003a94555000200b401072820094070311400050000340305501165543c106c1c2c044500c030320307503070111000d00c01901009c03003503020a6000d650941d5400c01c0707010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 999853893 1250 999852643 999852697
    0x302090133082205030d02070b0a0921120515030d261f0602030c07120b1f08100b040c2d1106090a060e0d0206011811 52
    0x407031150601801c07154908500140e039003020000b07038003d000e94140c026030f1414003440c1c0381c1ea4501d218001e201c4e000010303603407208100c90381c0a81100c1d8040c5034012043d82e81c200204c0d00305c0b8140d14015000b81032000c40c1e04800da210103060741001145103006c03e400b0b030a100044042d54000d850107075040049101592441c1410000103140c0c5516282c846825009a500c2955200103001488060ba00c4100000d0f14454070503103042594020721482141107640340e40081d1203030840c8040310034601035204005403411508010032641034003e80781c01d1180d100c404140041d00e1403950403a419814803c0d00142400d014040502840c840e030744041503503420482004100c0300810903960a10030000b41300100324110007010b540c0c4200c000b11040c401c1c403000109892000a10310021110300c28402008424800810300800640c80b56009010581411101540715038021050300d0042e88031340010800302c054500c2040c04290fa0b00000200d040c1c40213074152981d40000802160349140500540c0d10710 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 999855143 1250 999853893 999853949
    0xc060b01230d06170a2f0d0c0506030a060e0709030203120306030c0a06020303100506030906160324471c0b090a05070c030305091e1c140403150603020901 68
    0x1c2d003641c400001c110005070000031b807081e03c041c2140c0140c546c4041041003041c10810f43d0b0141000901c1a92245012590003020300f03018040c50754580d617444003003110f6a0107584a5415641d009016021300241201c0c9014140c00042c41160300d4402c061a240b842e40712001050041d1440380e01541e03481c40c159404141c40c940d10b5000600602080003004280300010500340d0304540c035180040900c4c1580907003100a449008c0014403c0140103d0003288480c92001000031150381c04040310034a96010014800000800d0600c0078191404041c012076a4000543eaa1801c1c0d9000005090581300e407042504511000390062010350713112071918507490565003455101011400a000c0d0340b40461004041d10515840141403685500104004000901c40c0031541c100100e600c09103604104c585a950f1002806c805508860444002103100c0c452030506c18244107031109a803030903107180d035440581d40002c0703503403860310342c2d42c45c404801651078910450080c2030a00d200104100c00c00c40e0403401e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 999856393 1250 999855143 999855173
    0x1a06070f350702010f0c06090204180209010b07110d05030d0609050f091209040908090301051017030304051527010b0f1c030305040f0b0103030c060b01230d06170a 72
    0x144070a00018006030b034880b451111405003454a440c00519501c0c4c44000341c107020360000d501904015091003824141000704090078000c650442999036604a018118411404003810403d4055030000480c1040060180c0541c407400c2241d1030940b04c0020309045070b0044d000805090b443d0010b00c203407014540e40d029004a0048003900c60781c43c40314210100ca101d888049030207543c41c5d000d08000d0007428401d0f81c40c0a10013900238410303494039100241c0f009640707014901e103400c81c1d50740b090080c0c800042070702e12403580000100030392180420380e00e6082200030000d0300c1c40e9403807048882d4490707a4181340c42e050b03054100001c6400008902001303d42c50074002400d00454008021024001e20707640c10045054050600140c1620740d81020201082480c9015203640480700001082590000340b14040711b00902040043c0c22028004440070118611400c0b131241240000700c208107400b0004107a44010380c500003442c0750755048900780040e00300c002045c0700d4100b441c110f01802503021241c1d01e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 999857643 1250 999856393 999856493
    0x20405090708071d27011a0f0f16050307050c010f1701090e0a12080103060b0402091008070e1011010f05060312180901170106091a06070f 61
    0x50b034600514010840128103c10001003012880d20140355282d84044584001d180e11903144074010384140d0326001203080c401e004246031000b003d402c0e00385840d010340d003c1c0d44000d0411468440c50b040c5d0003d540e04854507040b03503400702d9040b400014104100500d0040d1040010702010544080050710b11142241008180b0140410f10040c0800d1555114191003510800064502607a0b090070b240107555030700103000000203107074903c250b604420254102ca01c2407000b480346c04128400e020a03801420010754001240022000d00719002d58995507000d8842d280c212816044100000d004901c8800f42401060050400c4010b40c01d00703000740c1c0030300c0b02019020301990900740040b80c0e45280388406007500d010041380c801440407440320031542d103450041182c2d165507118000c0f90303000a0840f00a0003150300e45400028107411500644c0804403505001c100582e0800c001d110881c3e11603241250b03030411140c04207001130720382d030000030750600030b455901400503400b042685000c0116240d849 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 999858893 1250 999857643 999857657
    0x3070806071215121b050301020f07030e0111100204090b0a0f27050109061d090d0c050f100903170c0a110c030a0809011715091015030204050907 64
    0x4110b8001d80b000c0441660b45000055041c00d400000c03514031240e4004990301034020484905000b04d40385001040c1120701480c001c01035450007018200c0c03142c58020301c24103009014040102e802070050b840c1c05101810300c0104040d006046906000d41044040c0181d1350119040c8008550391007451980d260a403552b1100605040c4285100140c51140001d4180d0750034105c031a810390440301d880546000d9409001550b101d44000000d0140c030701070540c0f060b18020302424410130781d995041c0120301290141c810110181d01c01c651a1080710400d440a02c110014104270f12420805640300c04061100069000560701e801043d0174030b101d000d10f1040151304103200702826100d00b211001600740c00c00d8583c0c00c0704807902c10304010511000d6545070040744464410720100c9001819001b900342d075207001500d0304012000034402c0a0715400c005010b61040e46000d81000a82c3c6500000e03455402440c85603140001340c0c2511780c0107070280000303170080303010010382c2000744001d50050381501b8220 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 999860143 1250 999858893 999858901
    0xf011a0604091e0608010c1e09150306050a030524010e0606090f040e0718140a0b010522031a0618220605041406060d0303050403030b040f0b03070806 66
    0x200c050295000e00d0b640c075035680030503800280c05204510074407840400140461079494484500074007105042c1070104400550309501019105190250030036a921400c02c001d00b07000131256610001a28402850340d00e40c8082059902d481501000f50304c40c00c020720b000c1c000d4030740c124101421464003040c40480c401c0103000c846c40d0741503c1a4022015100365450b4241303030001030311680e40c45007540d8102e032800340f4600700908007050890981d9201c2c02c0001141c0981d400c4c0000f2540d800340841103410707040b0003181e0310448940040e0b8424005142c03e500303141c10f4003010f40d010040c014070183c1c11404a9020001c11000049100c0d00650042032645545050070200d1403009008071030f042ca090350040061100304902042c12a140303440c6840d5882c846943c41e19a00520040e00c0540d032000d4a10301c0a680100e000074214030070b100c06000460603490a40d400e0f030103854003070b10032000d1540700c1d516081c880d115403007800c1d66442035482c08291109c1d040240760411107503400c0011070381c002c13000704 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 999861393 1250 999860143 999860149
    0x1c0b132f0406090e060f0d0303020c0d08060d08070606030b1303090815010b03060a030b0705070c080a050d0507030e041a0906040b06041e05090c041e05180916080f011a 74
    0x1100b182e011395861009503694000080f800c81d07242104650140760038040d1000c0c1903045c1d001e0090045104100d860f050f40355071058507582030231076240d54403038420059100021015009443c00724410b43c004541d81d5203030380c0c54a80100c4110f60113411212030f40f0044040c103034400000c8005140c3d50000c0c220302007080c120500c101c081405400510040000880d2258039520401c0009582002e0100103c0c1040c1c1001070903684a060150b402269120b0081500791003c156800300c03a5005006041e9a5040c60041c0e0b6140c01111003074081c4102c43d40e4220082d120741c0a90903800f0410410343c0701e0400200d08104018101030121070149280c05100c3c00d0710344841003154140d55038200b007040320006140b442c0122001a80210790814005030a01c2001424580070704140c800100d4034090401e50202c1e101030701c68041c0b00326580b05c2030f03005800071311541c100320064000c000300055942c58588082c4075011389450342c0c031969041d441011060a07104080c440c402c134883c1c0710f00c140d944241c095400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 999862643 1250 999861393 999861407
    0x510170c09070203070f030e12070b0d150806091507050c0606011d0303040e1b0a020309010305061206070c11010e0f040f092108010504021c0b132f0406 67
    0x14980601c2001d4046245103008005607030010703510082c1c844c4403204c1c07460001e10780d9246044840c0541d080404100e484140071510030180c62140300c116081c81104c0c20007001400081080d1800c03981d1004003c200c000040c400e0501c203504050044c524081105425107001c50300820b502c080041c1031000c80b4503540e010544a8100b602481c140566004090034000c03c280c00100c00f6a0522000800107032000d00d807011184540048000b00749445180c2001014910400701410010b030000c0140c402c07a503009074080c5400c4500900341d04401007010500d075203450415a040702c04500c1d0861103d0402803084c1d11064810002c0c03030428401010341020805100d6101215480f07152103810402004039154010751145421100a1112401081180340c2c3d0b02107441c40b110006040310700100c9c0d03d06180c001c4a4a0b045609907008614520036881802860080d4106a010011141800781e08107a4003038401603020510f00c01d441c1501842d0f440e55118003156404015410600082100c3c64000d04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 999863893 1250 999862643 999862663
    0x60e0306100501081906080f0f1b090f0a0b090109023126011104060e0303070201050f0c0111180427150603050304180c0c02030309010f03020d0f051017 67
    0x18003103100405c2d0040d0380000d040150132522080c42070182080048800040c1040120298010b0f01c2e503444098000d003007100d102a940c03540005145d00480c50a0200080301c40e40f03e02007000001300d40518030001480c081c02030307022a5000c1c0d0085050703441580154440807400301d480c900f40e00c41e0144d00380714404600c01403040c112141170200448500e02c0c2684503514008200700020001380303281d26a800300581107402040000364420038400c5081c10000120750480d50141c607250b040c40140f4000d461075074400b100702001075484550034039409032400007415001240392000307a00f6030201e1040c041200d442da18180b50480020b42c2d0840065500f0303100100003604602186003c034005d00342003010b0501c80d0b100030114480001d00088207800100c40200c10809030034184060308505000b111500d00300d0308040d5258004001c0c3c52074560280e89424620007031400c01500300b008401c1200200c41d00142007904041d100c030204410040f00044882c003030081802e20700d69800c881d50025541d81d00901c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 999865143 1250 999863893 999863911
    0x30f37030f0209031507080702030a020601091a030a0b06040f0203040807260c010203010303030b01021621060e03072a0501030903050f0d0e0705040b13020d1401060e030610050108 79
    0x81c1000d48a0000e07804596084a02508880800c1c0529500d016588804c40b08000007503610008903805920100494012003000c1d0300400344c903400d000d2020010034601411080c4154402e0102449071424083da01445020381d007001054a03060050209940e107400140400600c104208070010710300005503042e00d034001000081c1880610843c584020081400b40340c00303c3e02103804041c55105400640c10303203109580030b010b2410b00b0001a6940d04210b000400d83d41b40a80341442200500312944040c11009046035200d00400d88030101211019015600c0d19000010000c05000c0c00c0d1903003460381001000c0340302c91107601c3ca26a1200540780e000d40c2c0d04141c0c0b1980400300f418426000d4640421010b8030107130b9a407101c413181c180100200020384903130f0f000f1100c00080074542485008a40c02024041c04615143e15070004c1c0207510407028000010ba40790110440c004029070240d020701402e854260500d8400401c251601d01e0060100d003403a807040c2014001a42e000031525000b0f2511 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 999866393 1250 999865143 999865151
    0x6040c09060302012102040308031914131719020a05010501210803060d080c0a02010207081c08101e0f140d0f02011707090e0c0301062a05030f3703 65
    0x70101c05d8043c3c401e81e400640f090401100b4024444c5403070041c03000c0d00f40301043c2080074021041c620b03003400008448071458a903805450b1000300780944a169007a500310840d01d880d00400426505035050141d01023401030f40701882c800c042107800d104403805090440301c6503c441107903242d91110401d0004d001000030700e020001c546991248144491038580c0001c0c0e1903180c40c0f50034015642c64012940c103038014400c40500042c40400806c1c0c00b01e503655040c0c0500340301110a2010744400381c01611101c03010020070700015407265000c16504500c0b038080c4412103294640101e11031520181e400c0648004171084401d90785980c0c40810410440e0b000c0840c28240140e8001030340d01c040c1d41d12203400c100d114142044125948807801805407200c88144d5107058452000c24901400240140c0010031020603464500c0c102021480308245185203810071a9007055848a045410551080d101c98402165103410901d0007001604d80c1c100c902d11004069000001440035034200c41c1903d004e060762 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 999867643 1250 999866393 999866447
    0xf061f0b0f070602280c02010e010c030c05070806041a100302090a0b300307050303070804081b0d120c1e0512040c03020117040b0106050f190206040c0906030201 71
    0xc54816600b619801c240e0441d199002d2094500050b00c1211141c00802000c07140018140d001d04098080c054040e9500d880d071428010040d50182c0c6c04143c00d40520022000f0b002c00980f04010f00400390121001502940c20285403a42030818100040582c440d4140c2c20014015071a400d0001200e80465041e0034035154410340e0401060540c900580080d20380c942041c240504020340304038a50b28850300c003c00b07500d51100ea034407800390040052203600704002240040b4403608101da0441c0c003c422603440c080e03a200c602e403620170002c2010b2016030441c0c0c078144610b94100301c07506490b42c00034034140204c10000d0300003811145a14000d07041588101c009a12840c03251040d140c0c0030600180c1c2c00d0850609040c03a403032024892000700d00107095000b94402d00740714041c0e190302070359110100f0380b441d034201003066501d03030028800c02210b01024001a50f1600345e549810702d00c518590054a500e050909000c4101640c42e080000b41c14101141000182d0b400805902c02c400914048422082 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 999868893 1250 999867643 999867667
    0x60c0f09061e14070309050307080106050a030615120c0305430f03050c040f02070f1e020901030b16050c07050405060d0501230a05010e0f10030501050106020f061f0b 73
    0x40380c003c45028a20021401c00205504111500280d401c02c904403000740d65074041441c07e0360740c1da0003800d40090305024100700103951600a00b101209c58450403803911344500c1150f0110031604d20940c0e00301d0702c40324100b0030b0000c1803091029130451074107002c085070307400b110440d06a1401e12100460814480c81078041c0700c1035160200103020054801b00149941e400e040703a607a03e2104c4a240f00d10f02d07100685c640f821007032084482242c3c0c000340da0340304c040860311560b101c00d01c21400d9a103840481c64402c2d0050384c804002c036020b54801d40328820301c0e04100e498003203404001d0520030248002040040b40e24000054a0000c0710022100803500c5d0f030b80c142c04110034904004006005d58200382070607401445410032118140c240d140e404c99560744800021084d14000c0c03081303aa075440c0c04c00c0032070102510315032001d5000603426000c2d5070680c0d480d13882c20b084803000d80c84000181c00c41440c1d00744258044c01207035040582484c0c69000d01c180d0f9aa094104607591140c0550002d000a55440c402 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 999870143 1250 999868893 999868907
    0x1509160c060b0a0803131202010e100c0f0b01150806030606040b0d0501020f0a140a090b0d150e0711030c060c07020a18050a060801020304110402030a020904020403060c0f09061e 78
    0x405400c190312a90713110900c1e542d0383c21860404110f0300604002050b55801c840385031496980503503c40c007040110364180305d0416140ca942608102d288800580031595078041390010920404000700c41703616190310844055903e80c50dc1d400c00c00ca441c00c0c0803080d031b000507a440d00503078101c50000c1c141d0355031000150f40d00d800360b000400c01d50001c101200c40780e50000180090f0300003034840c89150000d085040c00d441c85000180c0e008101760752420b1080700f030000302410045c00b00307a100040181030b0705403021103000d4603403200c804014103808108143c5d92044a290102d036200700194103103442c4503005600c8040050081c0c0805601180481c02d40d44c0325220300c0000c0ca11108944101180c0d015103070081c0000322449140c180c203203000050071200520882e0311650304160b4400b02410424204000395001a111615454090000081c01d40c3d4510040c80218801c0c40000341d01c54a0040180c040c0800d11059814410040070802050360407541c4040030090170b03103100d08860881d2409a07120 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 999871393 1250 999870143 999870161
    0x110f03010905160302100c0506041b17072d05060901020109081b0c18061e041a1203070b011505040e0408030406050109020f0906090402040306141509160c06 69
    0x242c800d526140c43c5000601a00c82e064a000781c4d0340315065070300c0c14825580800d030306100070103551020b400680400ea00703501e10072006100c03001824110340c0d1480341484070341c46a50a1601350300031600800180044980300110703440c00c118211200700b014041481e1555592064a00418001603030784100c2c2c0c801e40c030a0717090030382c802e00090300c0300700f08100600e50140410080c111803150001407016464004406d4040c884040c10410180e581c403018040c4141d2945041d07051810a4424030501d90398500401078501590402140030019900401c14441d500b0000101207420802c00c410114601f000c00034103491740c2080090404406040442c0c9074407030795002810809041c0e00380403c00240320015802030b8050704080c005a40c959a20800300d22036000d41d12080201006803c40702d081c08009030500c030a00500c01410256607495200a40e07034100c0c0f8050f00d00d07070240f04006420f50380303800100b51800c05551464991920041c4005900416520941409080c5030781204020440e0450088 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 999872643 1250 999871393 999871403
    0xb130e01060b0423010e310203011401020118030813030e0402210604062301180b0a0228030c021c06021308011406091b03011509090504110f030109 65
    0x3e2550f40d0803a240c191040c41d1021a0944284c01091035031790700c50130041d1400103004112420f078015101e0040d500801004132541180050f01032503000301c5c1c0e940301445c000e1803202c81c265195500403000a0842c3c00051440b9846800d0400c0d807804240d1103d22590711007000482810b1103003182c201034071002d010300015680b182c00020107103500400c606071500d80c00c09250302c0c003d05446507410081692814052440c0a035015001649420190002450042c07418142041c81c040078101c09445000181c01c00c81550100150000d80c0650400507414014240c88803215108030304070302c3e884040c1240398041c08004503504480259038908101c1d0341486010504d25610a6051030500042c0d041850211440001580c0c006503103541030003078000005a00000c94266966101000080340000e455004c11003070f41d04034014140007a42c001d40c00b801241c10b42c400801ca2420000b800900c1e01d401c1500110305203c240300000e852558078001c510303400c454404440d040000030038010078041c04080c00b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 999873893 1250 999872643 999872647
    0x40f08031f0f060f0e090c09121005091c020706030f0e030c060604050604060302150703050403050d0e0a15201207030806030706030e15100b0a080907090b130e01060b 73
    0x4511421030100d500f01c55a40d150981d507181c0309001680e03640c0c40c0c1c428440e040144080041c09184400d001061084d80040c00b80f115101420070b080c0ca084000606030102d159568140b00440800b0080310300c0741c000c104d104803e5a0b903c5040252900803d2040ca01130503110860000105c1c0240c0196446082e01c40803240c6540c03c50750002d80d0f50800f40c648900071854040410340900b0f0034010760b8142c0760044c0181201450303213142100c4540c490039060301004024000400010018012014105030a60343c940314020910200916800c0b60ba000440c6460b049400302521030f0001c82e1902c21503204401486001c90300000141011040c0003200d454640001d014820903401840b0349001c1c44040e003c0310714050b241e4a05404503080c14444c0809548280000f041682d000c840c001c1d448071006075011200c1d581c4820241c45da0b00100b2088000c1403103a009c06c0780004081004030000d01000b00305000301455840071540386002c2410520107652503588a55001c4001d41022004021500d50a9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 999875143 1250 999873893 999873899
    0x30605070521060909010b0609010c0602041d0a27030c0302100e070609170604020607210c11150415090e090106060f05030103020612090c031c0201060501020303040f08031f 76
    0x60000b07401252210311892079640031030440d9005205602d48410f0103000d00d40343c040c0210064428600b0800102d98840e02000003103240c80c10340c4030700d41095800244500c200d00b4140d0f910000d0790512041240c0c03417601d1140003601200903c00b44002030b901820000c0c00c90229082c12414050740401094003682080a28140c0d0b54001444200700c60135a99000798041d00c1d251002c01809081031998030a610030000b2802600e445001460010310502000c250a40c034013002200c10705054030010046007669100c0710911608050440b2014411aa00300110b40014203030651801907005140b541724100c291143c0d030a005951460141601c0c050043c5645400c00300c59001e820b84c0d0082c0300004880d42c045075007960045098a041e2a8010480e038281b03001c42035410f01e01c410040280b44184900500c084840d03d044c0a4007035524805008408100d0340880c001c1e003525101d511060441d0300c100200408a054460030400c0140e008058954940341c5058030b610300f060002110183c0c2c0c150744400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 999876393 1250 999875143 999875197
    0x22061a030114161806030209031005010f0906080a0b240306010315060803120103020d020d0807030e03070b160f020307051302040e0f0103050c0d05031c1e0c05040306050705 76
    0x512528110f07001e2440380080f160203d0303251811401da0121140041014420540641c0183c0200907019045940203800c0920000503030310203038000348100d10345c10028844c41c1c03c40d000e24030241085a009020100403560f0b0418038103c01400c24041d40c0c841310000040c43c0700d21764111080741c0d0040450703a155840f41010940c041c06080c4503c4014a040000140c1d0000030084c1c0b010001c0c0380080320f2041c3e103160244400144801c004a0740810401c034000e0009507198040c286281c003a954238003603c04c0d40b03401c0c10310b004034a800001d8806018070401d440d0205004c404072880381d00030041512a500362020034906102508440d03405402084401601c55007640034004072100d08070000429110700c9210705400750203020250140e0002590b03030543d03090204003040784d240b0907070499107410001d40290384c20350000c11000140945962641c089004244250340311a0b0210004008451044001500c0b0344124840180760545403000954050f01030f00540301450750006a03039110350909080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 999877643 1250 999876393 999876431
    0x30813140616060b0d14061003200105120903190e03030403021302040801060e0907090c0804060e0f030a03020c070902091f170c0a110607020d11011d0105090622061a0301 75
    0x603050754414100008c400b1610481c00c0002c403a006610284244c07c00580d000e03041600c20282c41c14040200202440301046c1800b45104086660146440320440819801c1e031f41c070021440c900704620000f941d041c43e50044200c904883c0d044504200001410f100c0c04007074000c03a40014403e5117003403000030f15020442807492040c03100c0741c141c1d007400340caa2543e9001c4803081c681c200d00044241c0c0000300052800ea1201c10207002602c12a0841400103a40701e207540d10131010301000a80105200360459000c2048402401104600f5820304000d08042040143d8858480c05004e12054180b0480c0b0b020300d000d005442d03c403456402191524064411940e8007035001e207400246201c050440b444408100c860046001d5030140c0341050707440b1821252803ca00a08080d1556201d0300c461728135894814008039130140c1000880c01e85003c40d403070744c1000802416025201070300c0c45c1d5600182300300c0c000b21038055800940082d4808010300c1c03013119401c03801c0c0d22542541c644800b1042001d03c0c3c0c04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 999878893 1250 999877643 999877673
    0xf09120806011b080306040b030109170c0d030e0d21110403020f0f1e04140f01090c050403050706050a0912060905070b0c06131407030813140616060b0d 67
    0x752404001003c11009200340342030076024001d01c0003440414041d00d8a5044400024001400814500030981341e802e81d03c140c1507100d5100d8800000c8400c081d41060144c259110810b040410444c0c160070b0702c09454507c51003401081042d40c900b2643c078140c0c1050304203a00b41e4941c408120f014000c0301103181c568064003040c0d215034400e48a120701846c101040301c254400c05015030382d041d40d0004211205509026066600641f64440448000000e006541c030810040c14102040e51401003480c003161002280c85080140401040c004181c0006504003242c40600d0401d42d03410302c2907003c1341e44a140e074100d0030051440c1d0f050309050240c107070405421a13009400760b42645950341c003811043e110305070f11441107130041d50000c0c10040300f109060451030f000300c0c070f840305480403040d14a0070460076400480343d900f80866440300000003015014090400f1002d00c12041003c0f0000940c02d0044003c90010328400d4440c80c8108a00b503004241e4000c4045c1c0426003505042c0303011580e060f07a5003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 999880143 1250 999878893 999878897
    0x605011704020d0804270e0c0d080c150402090105040b0109060f0e0406030602070308070801062a12050c0c0a1211010c0503040609210816050c09130203100615030f0912080601 77
    0x7400524951900d0310070100242030711002060b005a848c0b0902c054101007000c15102c0c03d10601c00741942000c284002465030038064124006c6140c180304000c6184010b03040345000b980741c41061061a42c0001112080d90722504041d98620f08c41e00c0c046604036507211030345810900340000041044255005065800d1298903540b010b503551403000c58890100b407192000140101c880321601d41010b003003004400e03409107100801000551641c00307100f26048a0320000800015070940c05120600c1b101d05032580c1196079200c3e0526107514120559048000078142513048a40030000b6030049003110001607001d010f032074846a035282c010702019602e104c0c5030280c1c0c0d07022150001246108000d4504903502032421070401d034847c0b10320034981221940803a040d00c2049031441c23265032400c0c0120320901a102080c27040182c248145400e02e11b4180f60200c0b103904080c018800b024541d140c0606004081c0750000e00560501c410300007401c55007101500c1400c0124030161202e60000c40c0600c940744c00c2e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 999881393 1250 999880143 999880199
    0xc030201020f2b0c0804170d0c03083c010f0501020c100f0c1b0f05040e0a0210052701020d0507150209040b03100b01030f0605011704020d0804 63
    0x240000b41c403442600d01c1c04100c00001400945500010f1070103107618503141c0303886103c02149a5075640c43d50f00030340024403110300b0400103d18000d001c0041040707503810352400f80d01c082c2240d03402030a403040140910406505030058200a003d00402c4000110b00362a07001c20858411514104010028080e94119038000f042c085825400068214070076500035188181c02040c0c00300c04c0362180030040004040000001552010480d84000e103011000407040c6219150728001e00d40003030203019846503001c2c42c1043d088031b600640208021914035010341394a1011906461708982502c511a0440100786070055059203039804402d407090803603801c3c1c003141c170a070a00b5031301940d250003100310003040311000e03c2c40c0042c01c0c00b03107401601800c5805400400c12000c0800080d003000c2c45910300e0800295a15451003031340d03906000e0312082d0701c0c00500400100c1d0030000001d1562210031040901100d082d07021404548a0f0717004940600d0300901015140c0c0d4507003d011003600d00d09030200b2010b50070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 999882643 1250 999881393 999881413
    0xa050f071a0a050a060e2d07021507030b1f020f0f0714010c0503030403180909210e03030703031a03070602060108070b0406171504020c010f11030f040f0c120c03020102 74
    0x451045e1000d842c0a1611054141d49010b0011501c4207084011006006000b1040c84464100261180120081c0d00036244c3c0510f650038001903c0d1000344100e04050030107486480c40d03290385007600340306c40c10400b1002e4407900d03800e000c3e443c0030000d01c0650b02c140f00d6004c8420f6020302c0410780308290781c680401d081e14a00c607d001100e104d849070001810710b4008001280019004a144e42180b040300400004426030b00c04042045030002541600e60059045500004513114640d0442d02c2100b420b00a07100704101021039a00d02410100800381680c5d02030400c443c08090781000c29a020090441da0116180d4400030b440f92401e124401e203a2050f8100420f043c11140d007603500b542c05c9551a0800101c2400c1c0400702e11078094480f80c801c44920001c0322141d2640d0008040040d0520300118901d54503279850b0080b601e603111b44200c9004144180019181c100d01e03020b801c1500400800703802c14490a0104160038158004207602c2800608801007000e40c440c16011070b4001d800303807003040761 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 999883893 1250 999882643 999882661
    0x91906050301020f03130309080604060905061315021e0d0605090901020901020307061a03010507020c0a050a050a031218060c03030f022a2406190b0a050f071a0a05 72
    0x165002c200782c180021700028450050a102000040e40a443e00c2e20300c0a90700c0da82c80e410300306d0030765050300c0b0151508081d0040c00010080a900012001d9a440d44400107440c1c6202498420803058000c0e5000a5203294025810411079807962440c107240f0f56525103002d040008210f144941c502452910000034211a0184203131021400c06030061490420346989940041824204d0300808000d2a0201101520248600e510800068005002e0701c40d64100300286079589900c428814645c0240520044d142c0c00035032000c49500c04601c1c00e04460340c410649081503c0c00c0400201e8003070750400141c0f940e104600e24161800390b1410040312040224403002d80c4501d4040310345c0c0300001a055800310318059000c04860a5203402d0318103010040c00c0451844c54501159109801200144034441c40d01d500d60003401c2c00005c1c4120800340c94408081c0340d500403440e2160601c00d01040c1c0710a20900b9408484040b944803003c024240407502d4000c0707450805542401c090751808000800903d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 999885143 1250 999883893 999883897
    0x312010b0715090f050a030c030905032b020c1008010501090e160c050c0406031b0e0906070c0807021503070305010e0106201510030b09010b090c0a090509190605030102 74
    0xd40000804031428440c0182c40040c0c62107040455a5107003107510075000c0b80e0180000e40b826132095a51240c1c11a039802c0092003014030b0380006210350054076400c015410804000480c00005414010303048041c0c9809900b803480c2200c1054209010350309038000590f0028180d03040e600b0036240e0380d205e030362a04800d00b1501401c80390541304000d21601d46880901400c0c0009100e441401101d003900c05000c00b00702640c905500465100600405059030310071040e05580142c01c09011403c1035260520800c0c5e03450300c015003c0c7c001e02c842e0030b0003402440042000c950301c481d0054408030300c481d55a28030100c0c6510403510080060325010003c00c5540c2e9a8217458120340c4030f40c0ea1081807818030b030021000d07100c240110034000d2007021540a8012904070b1181d2060100e5140740180c580b45003014440301e50001c02c40c042a903d08081085d0554075001c201d5005940101200d498034420f03407080c0c0d136584043d00455031042c40c44042000140c0c0d600c00c03040155856400a2000c00c1c1d440c03050500b40c1c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 999886393 1250 999885143 999885157
    0x2150c0d03111b10061404051b030105190b030403120515030705040b010c14061906081207030c060f0605040b0f0604050f15070318150e091b04080312010b 68
    0x100522034201d4280a284400381c2408410f54400c44c040818900440e0032541c8940d40c034141c442c070064028905446526401884801c40c0341d400409100c00340e009110501032184100c940c0394034103c1003030040905002805c411102c0c0c80d03403030902c0d0601410100c0e5890300705c2050780c2803100040d69500c1c041414138100c80f028006000740c034100010040505020340495041201c000009000f040d40d5a18122507844818080d1003a41000e049c11a4a1080c2d420f04045690a2002c100090f140020f010701080d0342c440782c084d46a40403440c0880d19540940c1024140a040560407401d803103080c2d10403c01c54104440402c04c400451060001e824090051690f0114081c40b007000b1a081c141c00303600c118007004069101d080e40f010040c84036034104050980010b0103012101951410a55400f00030380b8200030b074018205403aa0004004070001e01c500c0e801003d208000c5510310198904540e030360500001d1141c1c45a03103600c40c8513503d4100a02000d03620a09800014004003000121856 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 999887643 1250 999886393 999886421
    0xc0f0a1d01020c030a0b06060c100213321f02061501030e03030f040f08070c06141603031e0608060a15120f2d020910060f0e04060302150c0d03 63
    0x110301c0e06e44801e0f414400040007140c020500f002481c9140d00140318114001034481c070f0040c0c42d08001c01c948180e010f066000240e4006921100060101819200e010160410004443c0342015400401c03c208005160403da2a4540c0c0680c90b00640104080d4407460004d086420000350107401101618003101400f07031141c1080020038030310900d03c000745a1050161100040d0301c00036070303903110b601d03031141d0301c1615250121141031000c280c0c4401001001080b200d0401c0c10311000030045c180d5040304407030003020305540304074600311141240e9020960b05010141004000e540b8001c40c1d0700c0d000304988540e0450718040801e5540c440300e0a8040c1511540792040803180c4a554034841d15920110301600e00304201a5400e0500c40780d41d080444a041e40705044498450b1032050000d405006010002180403e90007844103581c0042164441e0000d46803003c1e4810001020a00402d42a00007035004a41c4102e1001c4040f40c4800400070316101004035038070408072070343c02c80858001042540c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 999888893 1250 999887643 999887653
    0x5130e061f030f0218123c0f1e011a061b100b010e040c090b0a0c060c0e0102010e012714060408090a12020109091109120f24010306050c0f0a1d01020c03 67
    0x42006c1c606400385810542403803c400d2251f1034a0076192412404850011a55101035100243c065064488400d0702c2d07243d0000b03000c0710242c480881c0101c0c5803c14028041c40300801c0b50b0301a01400c40c10b45031100003c81c25680009240e18014000e00a10060309000c100c121240404d50f04040c420b501b42640180e460009607410701d152401c0d180c2c46184144100548a03001e6400314003c2d20034034000c4d44068851203140200d107400a421b5030284910000c242e40f6024608501001d4915103044114401c49501ca1500040c03805000b20703ca0840705894a01c1a002008104803060005000324101110300c0d091450f03039074151000c18404040d009001031404002000740110079041036500031410220541008506004075007000900620111740d54440c03142e010010000b403201b5003001e2400c814041107441c1403501690001c1341031200500c8103548000140144001e081a0b445403041021015076804150070002d102d440c40c00544039146c2195004551190700005203064083c1002c1c010b44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 999890143 1250 999888893 999888943
    0x1140405060306102a0b010e0907050114120f010302011103040b07020108060414040c0603060b040609030206090103021e120f07120e07120305130e061f030f021812 72
    0x1240040b1950014414842c0380d5040300640000c99003a40014020000481244017050602e69000401030380803905440700c00c000d00002d00408988e00040d10002c3c201b03080001d0514a0340c0744980701320303d559100940c0d2842172010301a50300c40c1c0603040b41e000340e1720700310080714031500c40d61648a14407441c140300c14200310007401540203000050348210010000181c100c0c591001031403c0c5012141255084081c0c40d0521910703030180b00c1c040260103211040d0381028103000c40038040c6401404081d21801022801070207680c4039030120f91148100300d8403e400e80924060580301138122503424618541c00e140021003400c0003a010a1294005941d001c0c1492411009030005040c40c031000f1219014580010030b600c0011002e10f1512403007580c4a039512002e0720900541e4500c107421100d0380705441002c4c085980d07155a0f4031102c407825101002070009000c1000d4000b054400070700840075002060b00c50500d00da440c000c0d80d0032081901c0340d04501c0343e00c49006440b00c10440d006542703042c40d04920 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 999891393 1250 999890143 999890149
    0x406120906110304060c030e01020c0d05030c1b1c0203130303030905120c0d030b1f0810050a06090311150415020c090405011512020d03030507020115030b010501140405060306 77
    0xc9a20320740a4038000071804034440c007940690f4000c84050341d006484206540000da8148604403201000d50000c5040c0a111444036444403001c0850008002c00400402c001001031b004035554000c00e050f03040503012072140003641320606514101801c1803135091055801d40084221413404451191201c040390035075034240c004141c0000c0c1611f89218044003a062085040000c028405401000b446c0c0c0c2e860b9244010140c13160200c12900903001101d1f40f40160540c0c1196180382e4540742071000855807850001702407808240c4c03120707501148041c2c0010764107400941074021b5a0007004038482e9080d2480074010340186c511a031200f0f03050108001c03c1140740400d0400c60110491040d1481c0039454130014850000c142e4007554140d560710600c0301403000800c0d4041c01841061390380c82e407074007041d000110002580e8101400741a100c13400031340340354401e600c02031300c402200c414400541d0701e900702904941402d024203030108800502900034903400700705032821188024030709842c681d944014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 999892643 1250 999891393 999891401
    0x2160b0a060b0a11190506061e090705030403170f04140c031f1e0b210d050a0c120c060513020d020d110a0b07150507122406021e03040612 61
    0xc000440d0141040d40391720809030340c0c214180d4a00510042003030b03040c0b42042000103090101c0d60300d0700050031542a1400c2d00d983c0280355103c802d900b013481d201d0b07445040c240e4018205480800340100351034104404000101d103614060ba001e02da116141c000c0104c40386690b100c00c0c00c98581d0580c00300803801d40c401031616603120400084800410322a058400403200418035050240da4a600d0380400311060400c00120041c0907580f144d14207a02a00f8804941c81e40c0e681a040401c2290004922591314080d240344522598401ea00d08000b040c58040140410341a6100b00c0b005400c10340400e00c004040126550095002416078412040981c02c003c03011034030f020300301c48003002040304441c01e90b40c00e040b0303000411240c00c41642d1034000707141210840780e010302a80790807480d0106200301143c0c003912034006580000390001702400242c21000ea030200301500705083d8075501c100445c8480e8040360950180c51002030120348103e2a013012030700e9028a00818001486428240d4a1181039801c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 999893893 1250 999892643 999892667
    0x61302010216080124120609020f06070813050109080705210a0309031205120c0d0603021512130f1205070c0b04080d0314070e0f0402160b0a060b0a 65
    0x48541a000c21002c1031034202c940c0d03114074070503596070001c85512012140001003a0911540740e80f840d6040c1502c4801a21500d40c001e030005580354202011502e410311001e40c0f400008040503200c20003403030054860362000c400b40c5070000128400082550046000005480b90100680080c600f000c0600001c4200c41028009686181441c00f2040d03c0c14011003c48500030394a4000c0241941001040d075000700d210310040100070020b8010080003c030545030070401040c102caa0b1409402d4a05025084e02c0e08081c0d8403080309100300035441000340040102c188005420302e01503880742c010f0010900d02040281080003050700e40342c000f0740840182001e011060900c6403c0008c50745458010700010381012041d40300004061142c0c0c03404101d10745002d41c0510302800081c4404201c403130b1645019208800f400021403001c03000341d030703101ca0340003159401410231522504000d0080c2032503054030708107031a030030701c0940401c2c04000c8a004000581d1411b40040340f411004a0302129948a070782 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 999895143 1250 999893893 999893897
    0x5040501051602121c02070f060e010507150203090d080118091b08010f0e010507021506060f220501110a170904150608220f02180903040618050306130201 68
    0x200c10710040e500d18410703060201c1310744020302800a41880c1ca48400d003079290250300350742c0041c004010100d49680c000c000e446a07494211602500c0c180181c450307004542c0028003036056601911104400303036010754403620302101160307014103078070130309480c082e03020301402c41468078820380c08a00200c0d581280014502ca04524909074a07100320078085458240c12400450351111071081030440c85d8041c1400c48800c08008000b513041210010f940d810310650f412850900c0c61300010400c0c0c0e0381e0401d44085142c504521540e514141c1001008242e44014100d080141004045019403244111f100141843c00003000c080700380f5242c0084006a42c59403001000c010403040312680c495008107087c9413040c0300720790038031030900318041c001003002010031004500080c1c3c10107098406039000c1100c281c204007642c091190500110b81210307002c00a10501c408180305102c0308250000c010000c0324003e94981400c0445068845007180152080640c19448400490500840081400c80ca64414 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 999896393 1250 999895143 999895177
    0x40b1503070308070b160e0d170408070509010902071a06040f0906021e03062202070813030309140a090e010b031b120d0813140a12030f0506010504050105 68
    0x440000d01d07014039504200c610076000f041d01402c010340380c2101d40e040740c00d00d4699441c907641100000c10f030b4800481d03118820107110030140700b0b001d00e40101810400051061035a01d64658205654a022600c00d95000b404007100002c0c0020f2940f00b80e506199001d601c065001940503021090f99030081c1005a1141e1b46103090307a030a0550b40b068920951240d0f90141c0c84100410900c80c8800012000200354035040040288940d240c0700c64008000540581c05a035145a80c0e81900134000d0303210017008004006a0860504121141c880072644680e4407403002c0da48031450f800110605440d000c1c0c1000000e003040c0007074006034004c11507021040000141d1460314100280c6000100c496821146000d460350702c0703d83c10070361200314451034041d00400594400320300c02040c0d0301d001400407180b8146140d10308200001e9001c1101c40c0f00940d4101c604420407800d202803000c640c1402800441d2500b424506092998000d25204000503140c0c1402c003031901c1d00640d1030b84d1028440030021141 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 999897643 1250 999896393 999896431
    0xa170712060b032b0f080c1e0c0f161a03060301022703010c08101e0905010b18010f1d0a090218041116080a09172b08040b 54
    0x10400419141c560003680c456040328121381c0e046402e2080c00c0b002400c020004848500082c1c100030301075000003140d8030484c2e95140e082209070031002805103440c3c00c1000060265000c0d100041c01c450411062800e480380508880041c9440104600c5064100081220980086400d54024561005010300054035200c0100322880014034200303007a503600d9501003000000342c2824800d400c1120068200362800b400c000240402d0760405228120070b1a101054135200641103080840c0100541a800c5c007155031180004c0703516401500591101d95401d000d140350640c81400800c0500d12141c503007003000038060056843d60303101c030140307035800c41001c0b900010b1110061000780002040724110910b800114400c00080d40e5450601040c3c42200b4041001e41540b050030120003d5400080b80b0b644200100301503518014a510048101d00502e502c010704c1000410311841c480c1280309aa04811038440444680381101141034000402d00720000300041c04041119421aa0030360000a141075 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 999898893 1250 999897643 999897649
    0x40203180f0d0905010c0321060513021908070519020304120308010e060402070218192a081006080604110c0a03140f07020d150c050403020a170712060b 67
    0x71160303512500341d02554a00b03540ca42e1040c20b4401800d401d107400e0300c2c0d1030841e440052102255040526401015259001c909403aa6104400828001e095102c02c543c0c0561810001d42102080245500c802c03404006200d21515030144229956280e4a003032490190920103400300307407252281580700400000c1900d0b450b60800c0c0d0100f034401d5454816940c140480c040c050400030304194040c80c0148140320040e642e01415a0701081c01d501c140e002907a0b4a0624900e0300842685813801d140b41484880024a030142040c0d0b041100b40303605503015101c41c9048034503131012900095261060441840038074414140290880b00007080803c915000c0c0322901203c2d0310044600407103602c23690303c0104040e0441c4880700301d54040c20707071340e800c0070b0048028001610494400a20a00d0070710090010000c081201c1c851100694404200d1a03410340f9024041f0361203400141e2086000603000a856140701d406010304203000b0001c0c3c2609854502101260112080101c07240317522a5950041e640f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 999900143 1250 999898893 999898903
    0xf080a14030a0c0e0a060f0f1b0b0a0507080f010501030905100203090c0a0602030901140d09050f1e070f210b070e0f010206060a1715010b0c010501120b0604020318 72
    0xc0010b40050400e10000001d403401c0c9040f03482d070740600c280080402016030007604064400c0942c1c1000040c2c030f04501d100300d8460400c0c45400061051021032582402100b2092611400b040d503070030050350710341c04825198080c0440d40f1151120341d91006004651180e08241c1d0114440c03000ca0315444150303d001c0040c1d8000301c1d5a00384035801030948050a1a141c00d00e2030050015001441c90300d5001d100080100c4000004841c00036400200d81c201034699a0050b103480340c0081c1501c690b0700200d0341203074580806071449041d803c0041003c43c07a40c200400c80030b0488100e5107000110a1518254040480211384200d00c8419807040c086e020464100d08944100c150340d032401540d444120800088415464500f41158410740402085407500c80c1e03510203849201d6146e10f01c40608075515850403200a94010402c4013441c000a88491100301501c8021040e030001e100581e240d8820306c81c0112400e001501d0001e03e20003140f007506060b402160009030100b14156080c0202900714a40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 999901393 1250 999900143 999900151
    0xd0603081c0507080c0f0a141804060b04140d02030a08030f0f13151a03030a0201060905130503040621060b09010201051f06030f0213030b0103060507020a0f080a1403 73
    0xd04078852281c03019420901c01c8550002c107604003000030381440690b80e21240541102e90890000000b07140380c080b03004140040d4000d070b4211040f07690b4140c4505148402e0400a841405036041840c04107008589506807002e50b0b601e00d003194402c94501d000c00000c11104841a80c041c000d107448000407500c080d006600c10112400340c0c010070b040800602220f414010080d20054000005040c0010305010707500300364071080c10021a604000c2c4071008091110b450344c0030ba0510000503c1010036806412079002c580b0011420085655102e55081c1e0086403a04018400d4004110501c9054060404541c120201d42d40030201000451100801c841d030b643c210301c500083c04507000c59250b03424040d85901c401d128941542e00c5154120410f51400d00340510410315131a0703a00004404130550580f01160169070400503010b58a061030360300000280001c4e1a02401c01001503021800011604a0641d2240fa2807213010542d864019442e00840891010000500440c60b9180285806107000f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 999902643 1250 999901393 999901417
    0x90405223518010e04150e161e03150e0f0916140d0b07032025020607151e05090a080c0f0a0f06141b0d060308 49
    0x5400224045008401035200c0c002500c000503816818000741030070142c550100030800308141e00326048005032403448001070820b0b042460124481c04422440e81a08103d034842003100c001c7e62905400d0b00c4415003940c07010004159050300d00706801b1a04c18440780701c501e1a14002892402d50b2000d00161585da501c0205a0020300080c01165002c10075415040002c46004080743d2807004040542ea542a202c0c50929038400c20388441c1d035894100d10794203441e134064203402c128584550041c000746040c140042110240e80c10b4403031011007030804c40d00c048101c070405030002a6a507030450451540c4040c120780144080c007242c00042c00110110003030808584010441d2601003850380c03030444443c50700d0481036082c80305111304a82c02140c044039564022140ca82e64922000c0b1207482e20081c0107812240d480f03a014140e09126009a095001501c0742c2018070028105046011480b9829140325065040e40e0101fa01d40821110003000da2000742400424003550329282c01845070400c072a1008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 999903893 1250 999902643 999902663
    0x121c110304270513020a0b09011107090507090608010609091a120106032906090601020a050601060206060411192304030605060a060908060c03040f0b0112050705100509040522 77
    0x45407002d004465000c0d4410114a1038032401760001207040d1068400d012801000040c000002e920440e0442441c5401700c00b100c1c41240e994000000801301121a000000c0104c100440d82c1803103451818100c0742d450759407141c0c280c00c2c080030000070040f002c44240c0005689810b04020780380d00400113a000d08034000001c000385141424240000034110744d01901c2003400101940400c1a0031a13600301605072501e148664981005071300e01540c83c0d05c080c1191190100004000d0780c00a400c620480c0252000e100500c68076a9070312a600a00c40d0400906015120106100c1d216030002c0210b04c200c185503901c20a007410750720303a69a00c0340c0c0064a00d19160410800d0a08010007d900182000d19081100c949000c0340c41d40c550740c1c0580000b0705040004041000d000d0248840680e81e03400524960081d69102c0000c03606c0400d03100c048845014555001031640b40c03e0a18001d80445074607510303e450240303c1080000e0100414840c0c145070b40405081070030304114103440c52107225403030f481 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 999905143 1250 999903893 999903959
    0x15070e0d120f02010e190212030708031f030c030308060307090501090b0f120c240406080a0e0105060a15050408010c030608102018120c121c110304 65
    0x4010b250848450800d40e0306000f170700701d00c01000240017480240a82e44403941c0340c81c0c601c0021050147c59140d0301c020320001c52003400744450100158022180880691058001d011f039650900100d8840a03000e1030110104001090113800d9950341b101000301a50300c1142c5601440e01212003c0e00420800303990b5a030200f01c641044440caa01003034080300c207030f0f41441c058007540d0342c0c441a0882c1d00e8010341e0b0801d25804882d02c01000701d0042410381d40d60b242c4450b141d4200130621701c3c048415600290410095405981040c401e65008500c081c010307084035400c01303904a02052409001c1e0040000404c000500c45400f8403c2491040155070041009403425514a103440d400040001c006403a044400680418400b0031002204619036083c4c0c07180308a10320a01401d9500c460540c0082404001e00a203010100f003110071043c0c1150441c07070310080300a002e6620b840c06c90010004001a0315150035550181d00c031409802903a60441b4035040d12412135a00e80100302500111001c44e104070340d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 999906393 1250 999905143 999905147
    0x6140613060305030406031d010c020a11180403050a1205011d01060228020402040e0a090606080304121b030f05100506010c08070212011d16060302030915070e0d12 72
    0x3540034041620003030001a0442d100d6584900c2903105031400e140d950380100100b031b001008110030200e100802044100501500603440e07100ea0351301164443d89501c10428903241c01503001d81000000040004039a845640a0310306500c17841001c0c050114004061446075680d0195a018110420052409a40c54800b5a241c40410303044103040d5006010310000010104d41c0d241203c031041c1c0034425220100f030010030f0007403146401406504400d030003000500c11143d0002d000080c881c6404204941e55402c1d800d072207024034050f0301100540b03d6003050109003452115401a19805071202e801039495480c400003a01280040301c55402c0f022409001008034420340d41e0140c020f0a01071031142e411340c0c45404921400c4070091151102015410b419038003507100603083c0d1040b40c00e65004aa40c06006603403421282030143c4041812600440d40d940b09000ba80d026174110802442d2907130b00f0041d14000c560009000100f000519441da0071665242080100d03610300600d142d0f5540d0140c5880 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 999907643 1250 999906393 999906409
    0x8040f09140c04150507080403140a02030d030e0706032007051606140a05070c1e080705041401050904060b0301020a09060219081912091b06090f0b03060409061406 72
    0xc00c85818100f80001c204d2142d20384000c48000303044d0324000b5614402c074500b41c1c0840c002e40e08081c00041400880010802000528080050084040324581c5940340700403015a000d000c519900d035044440304100c1240250080d40c3d0025203003095440320300e030124844e610354000680c190780c3c944c0684220740303c0303058580b8036801903d102d00c0d100c1042a00d4840112451050501c800104000003c82c20244990b0410301c00c041d1905140c3c407841241822103040e0100c2c081d0081c48071501402c540044c1526241c415469200e4848500c400c8580c41c01c410410100c00040c0b050709c0d0725480d085244065a42072004044031803064482400b1a4200100240f8144c04045021120b02118481001150305181940e01456001c0d0700c880f10f046144104440c07002a46511400682c02c0011840402100071030030030b48040240b8180514558031041111040b8030392007031607445040c40c001031003104090801903900210107000881d2a50880c6d0b02e40c01281d500340b40300103882400e0400d2101a00e082a5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 999908893 1250 999907643 999907651
    0xa050405011e0c030e01110f070614031014120d0504030b06011b021e030f0109060e030310030b06040b0618010e061201120302240603061e04030c08040f0914 69
    0x1c00036a0004080400fa00d010499500035081c40099010050980c0c403460074171546840d242d003601c00c1c2e030880080c144c1c2c0d126130900500000c01d00c04526020031414400540e803190a200d281400000d00d000310103a00c0800c400e0280742c008800540c80e03c1c401d001040b040d0709255040d82c03400c1c3c1d40c503d141802e0b81e50b86070182089040000360b807481d1000151103000c130007036aa011030740721445e08100408482c2200307040c00fa2175054040d10b041d009c0c01840641c803512860b40944802d0003183c0390700200c40d07100d110072990701c517429000410a10220704e0361801a54000005040083c82c1d40344180000c0c0c1c5d0380c220407402c050844443e5039000070355a01003281e0361019020b039071041c00c0c4644030018403084081405603072004012a41f8010925108220758040d0700ca21042680c8140d0500c2e20314a0510000c4401a00a00c00d403404201d140d04a40c4141c03890032000848600581c9850b501101d120354000d03003e8484250501002c01c2016441d94100001c180401002800e0b4074500f201c4211844010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 999910143 1250 999908893 999908927
    0x4020403020607110402040f09021815030c030406020906030c07110108061309020a120c0f060801030c14010c0c080708060a020c03070f290f0906090d0309020310020a05040501 77
    0x8002000161103140a462600d60b00465410304403801c04040f400074003590703020305048840d0440001e942c3c40240d009103031800b0b039152494100c0e1024814852212510225544908410000652081144070265400620414000d807801c080340e000910590002e40d10003442500c002100070800ca1482c0103c681d0000030308101a247c640400056004022101c880e48203a803184201310440d61a011482c01510f40450100700790321042c00d0a420b00300701400380c81c6807481d60300c030040b8a4901600e001d0341226440302015014a003480740c50800600512081c505000541681a00069441000a025201d200700902040e45000b8010340f8040015140340c040c0b520400c10b00100720004002c0794901c0b504020080441c0c0d9042c540301e9400720a075120741c10071142400c095803c48480c0200355014503003640300d41015440e4441000d07152042518924035a9000740090498140a50086000c2c0c5000500351422a03112175050300c2641c0c0b1452142001440008060250b5a004201c00c0740b281d000d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 999911393 1250 999910143 999910147
    0x1512060e0601260f0117190312090209010b0c0111090607080a09030b0c1209010c0806010e010210020d020903070b07050a1b0306020d050f0703020c07142e0e0402 71
    0x4040410050007520560402041911070750303045a802103907801000c0906480b80451030150000d4180940070700a404003244121380300409580e001944450310107102d020b1300496405550141c0d130b2804000b8820410f02c4e29510340c1c0000d81d4400c5003460007054032404107542c8180b1075035000c1c00c441c00e4020181680005028040c03031f40e11540144d51030a81d0011001e0307030f1140c40074016111060766500c0109400010010400e003220b41c2c401800081d002200c005400340c50b035114030741c240c9911345500f000042c5a00300241044d8800c170110749c40000180142c1d851005c40041c28000e90348402c0c0300e50600d41d00007500d000741d03041c200060030017049820300e07003070408110303503602134031408000809007454003041d0b00001c943d002c10610030000e6612080c00c55859440e50140d4014100803505c0c0f4009000000002c1c05e03c41c003074000c40ba800002c40b0041c0c01464140701183c019a024a07130200d4200d0300c3c0b0f0b81c0b80c006035a0103103043e40f0f40110b00c0d90318458004c6900001445500d0114040c5c0c002c13401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 999912643 1250 999911393 999911399
    0x71718070b1b0f0703021318111203070b0907120b04030f1209060f20120a0f1d0c1e0409060b0306070e010e03160b07050c0a151206 58
    0x800314408003560008022507507a000041e050001c1140c1c001640300081c0a01d40c4511958000015400101c074400c6d25295155020a4030210031155198011031410606103120000500300040c1486605c0c1d00422040b40141000c4d400c51550704001c00842d10303681448103004c8018010001000101035184854400d034a507a50b03504100140503000800b0b104404040c0070f1928042e03e070b80d460601d40f0709810440c0c140a401d010001d04100303070307013001210300e011001601999102d07681102ca051155040d454000800150008580e0040c05200e055940e1240ca0f27070b03030b2503d50182202846406050003d11324000701c00600345081c405007940b080b0340f0641040c0e0500f01e0310031221042d00f0b0480e40095810f0480c1010301c0a05104180729034103000e00c0c401c10028940145150f4120f10080c0e8405039400d880304103240d0f40e0403210388500100080c4070300420050704903100a00f09140b1410070b0303c50840040011a22046003074000f003890801c80665044840d9000c0401c5c8103174094280140b0001d86 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 999913893 1250 999912643 999912691
    0x30d061d01050f06071712150a060504121e05070302010f212301080f0f0a02030a02061b0304030825030e0f030304031e06060605030915060f090717 65
    0x1d29607070200c3c0564804502c00c1706100c01420940b025000442030386581d40c0d040e00951803400c1046803120080400d000601c610783c200503c0100a40340c554480600d001d0401c50045000c11f0307445c60890311300000042e040f040b402080e21440c1c0c030b644640020500c541c2184000f40062031200341c0c1d0020000c3c1c0005c080002c80030001402590b080c03d15000801c5220311001c2d2208101400020030309200300030001404860014030a0081c10780302c41560400034100e0300c200c1e00d8a12809011f0761507031143d0f0300d42015152450040c4401e06200c8003d000d148040350b54642150000d51007510301503404690909166080340c500b1142d080f4112680d0300c00540342d6405030045040700c10702070140302c5888520182d504e04200300c4000c1c64001a515a102248510200482c3c05a4004071425400c1c20720018880c1c1c011402c2e00c2c010703186c420160140c082c400d25525401c400003810151b00c0107032040d81032826100d04c030010f40a070007107544000300d01014a0041c0200d64002d4050b200c03ca034101c83c10070f0301b81 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 999915143 1250 999913893 999913909
    0x1020906130e0f0415091e0c0302010801120512180a060c03020c092413150510050a02150a02160302010221060a0e09070302090112051b0607120c05030d061d0105 71
    0x2581e21710014207078445042010041c00d41380c041c2050b00c070b40b010b130039001c1c0100c481c0030340300700c80c0700341d031924026a01c6103029084842048030003413851384810418155086064080d080070300712802c283c0f0105507514002600e001050340305001280e003150030354090650500c011440000c0035500302e5000d08000f620151441410205820a940c2c108510509075803030407a411160020b421040c485510036114240721451b441c46a03520414800e40c1100409000e0701c25640010110340240681490b08161485503400003001d50503c42d0742042150240782c070f0714440a41c200e0081c0d000580f1484601540c5d901c01030f9a034946000100c0c140b04000f03a90355040341e14403e542c032950101040b512040d085925201740c42d00003e43c80384047c1c0010605041c00e1460b038444500600850b03484141c038044010388038003141d01c0036800100400102010544200e03982c200c500d51f901d802480704509444642c2903401c04860804441c1d1900d4003007110b101511210701c1c2020900080086551608002880343e07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 999916393 1250 999915143 999915173
    0x303072d050a0e040603080c03040602010e1204120804122004140a0c0c0b0f0609070e090103170d0f1a0103051504050c1204030e0a0e0601080a0e01020906130e0f04 72
    0x407411070410f521544035a04010011170b403004005441d40804511151240c01502030000190300c0d0600c08800d5050005140c0d041c0341e548409546400e003803004100190103088003e0b10141010040040e010342c05121251001d0701030303072010700c81c4c1202d08030345100f8948542d0564852410301d11900f0702c01104034102c5801c900c2101c00011010101c0c8404ea601c05103200000c2c00ca00e19480400c0580c080c0402014450001140d02d441c05556054042e500c5019181d040e9030840e40c03080c0180b00103240f0f03540c180103861030010018280103418441d901030707074042800740008940300e01040c101e00301c8201d50008020390900f01480a0316240342801144507801c650203114a466102158044030958100c6070380044011032402c0c980742c9400c01500d041c5194601e603001e098240303000110310403e00c03034190089070305030341e0005192210110781d0050902c041d180240b5540c200046005a03407480c0c002d04003180840448240d4030f1070408a414400e9004159900c410840d0003007100090a626a800b10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 999917643 1250 999916393 999916397
    0x8071118070801170c06130911070c03150905010903170c0c031603091a0a0e061804051915080601060305011a0c10050a020913060602031803010e0303072d050a 70
    0x340f0506a0784c3e24a8150400b601c65045407000515060000c00ea2400d00306031664100284460901409400014840c0d00d20280c092030039254284002182c0d200c3d8600c2d0344050001c0403400d5101511440d0866821140031400302e0703900240030031140020152650301410f44101141803240d540c1115840b441101d10001e0101c02c0343c0c0d0303032408141c00780211501604074200211881e00326079030200000d0f07000c0b500140206410a144081d503140840031211184a960392070090659501305001c0580805002c0d0401c25080075205c11803141c480c41030341c0040340d81059012007146002403140c1441010380080041500340f80040c4108003030080b600100300c0d0100d55890740d427122001d0540c10051010184c62203a070a180500c00003030310760f802818521000700e410b0800c18a51941000486203240b00e848096002440400048550f192407100b0080d00500040f49442c84c1c501c0c2c25003903600856107240441c407610940f620200100241b44805540300c09402444035030040060003031700510007000c0c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 999918893 1250 999917643 999917669
    0x3070608060d080309030a0806040c0e192c0901090f0b04210c11030601083d0e0607030606050712032004080c1c0605040f08071118070801 61
    0x100364450302c440300e9845030003001141e01c0e82010340410b92030344d02141142c00001c3d40c1102180040c07401b03224401d801d0502d5140c10004800c0d11381404486001c50705118001105048002019440340030310000e150140001e405100914903031101c2c41110251909015a2600e0030000c0020b000d000d00201c12a002050202c1c01d42d074501e08180d0b044410302106a2018012889510080d04402183d0209225404800b55078241c0c1080c540d690101b403040e8080da5100702c407540140014580c05981c4405880f1282c040142c4601980c850a40300c5044403030340507a1100c80c100034080503c07445070030105a207414004540b0748000100706001c4c6010107040d0958481c840310070316000c0c0d40b2004c10580040901410741d60f50b840244401e0300140304950082c02044144461880d10b6242c2b002c52800031400000c00820036211200108001801101c084500112190225290b58007401e1068032840c1d1502c58585031b0380030710169050300070707070680c640f0385a8061111164001202906462044182d40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 999920143 1250 999918893 999918901
    0x1508030319060b030a020f1c050f130b15030708011b08090604200f03012406090602071211130e0c010c03120e1c050304060c09030c06030c022a030d02030903070608 72
    0x200c030780f02300802449642e210140b50406021241c02c214402c0514003505640da6079410a01844403814000040c510a42080081c2039184403c5501e00c680c507001d002c48106a03100d0f20101c2c2141e10a010f030b11070f84c11a004008413a181c0c0440c005a00626806c06016a41803585c1c0e44c034000d01c051980350040005a40c3e421a164450120284812000074000c0c4100c03036044a18500082c01200c0007881d0003141c25010618602031042c5208031032442c5c1c0104260340c9042d03400700111104c3c1e02c08071800e01c40c1c510b240c6000d40d0744042c61449013500b0f800000d204503002e41c0940c500402c449865061211045942000c20781120751150008003800340030074110108401c06041404014100d1500b072007413100c4001c19948280034504c40c0d84101000c2090300c0d050441a03400e481c26210052100c03800e8038003400441c1c80390300004521010703801203030880100790a0510207040c0100c9581440b28000c600c00d001d5160400070402180c8075800034600e80704e20500826180c80d078902504c828405e2a0b8041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 999921393 1250 999920143 999920167
    0x90b0c090d08030f150f0d02190807060909180314030402040b0307060512091219050903010f09030e0d0b0a090c05090403110607021c030f1508030319060b030a02 71
    0xa103140952001c03007640e80380313041c56800e0701129098512414180c0801c91900181c00c3c124240550094000c080101120083d030803c101c040e2003a90002811000582c0060034140c01c10060300030b01101d460f00402a400e05d00e40c58211401e20381a110042881c010420210340c020400f41d00c070756880101160f580e40c03503001103406408005100c0707400d03114110001818561005c0604a0580314000030822510b900858a07030b0b903045103440d4aa60001001004058010348911854014030750900c00e040c00e4240c0c2c00a42102c80b801026440c01e61521500c000b0140d0000380b01d007402d170044420940700326880d01d84840c1114002c08280c21655500c2801d000e0119044291005060042101003141f03441d150080580c2c0300401e61b440942f08a0010805860000c0b440105181903444400e0101180100440180c0000c1000384042d42d0b0724103024865144150541c00501180801180e4034100546408072424802c54036580c00352501e07205000d009481403c90350041440384015807140c0c40301c485 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 999922643 1250 999921393 999921409
    0x20a1104051e04060605040e06100510120603054b0a02030106031a0f011409130f030f080c0702180603072303120a1e0908010f140109090b0c09 63
    0x1400d10b084450504002c10086140c00c62401d803041910b050000401c3d160055940b000150f036440408070034400c0c14802130a11822200c40c00109141411941d503448181c0c0b07080f11020341058030075070060b400a038072101031000701d65616884600d219a4920325503481c1d813126a8465410424864080c40d5aa40030f00f04200c103001441d00107008000c0242d80c1e1911144500b0131030b15860170403000300c000845c1e44003014403640c101e130644400c0038201d201e05020001540b400a00e41074001018034072400214004442c040046482502c6014500750243c2000d00f0b039170f500401751102c1d801d04020003001038032120409001000c1101c40e000d4241c807101d0010307040103041c1d082800c096071501100d6540f294596003182000c3d1065003640c4050380d44140170a424401c003a101c0001c10070302100390b07969840e0a2040507080030145841417900c2d44900d411429a10507601603070401e520740d00d214541d90f01c03046000e4010700718502c0030406801155940999588000c114510400020038500125152900703 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 999923893 1250 999922643 999922681
    0x6111911010f0e10060801110403030c05010212070503090f0715030f110c10110301030812150306070c140f1f020c0d1707030b030c100c0204051501020d020a110405 72
    0xb001d0000506505095944801d0b01840c20b0303440b4100080010000341c1032140c0140080c526000f9441e06042da00d007610904031042e02206c1e65903003000300c441442c100c8580c032401608a6659903642e42010342010345407066105126440b900800c00030440d210140d405001c01400c0c9041c0890015405c000d5a002071050b00c1605800c1c201c0000d1640b4001c0000c25201c2060414210400120079100000b03a1980800d001c010880c0c1e400b00700d00800c041031900c550b540100c81d2070000c0e8500010001103070800c0c00507258840401c3c20007030385504000c0c80c0701111003030f00b041c2c0c001049404800c402c21582d4540d4520701038081210001d4000c01310820b5011582c1c1e450010007100c2126203042c1d801001185100c034581164507008001c40c01061103402010303d0503000600501400b0843c104001584900c44501410f122024bc0800016100d900a1074032070381c1041310000c0d0f5805240006030810038001d0900c011034110784491000036044015283d008481610000313000c4c3c0e2800c10b4042030000c42c1d8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 999925143 1250 999923893 999923921
    0x3091c080411040c200319090e010f18020705010e10061a0c0604030809160605120c030601020c0f040b040e010207020307080d170c04050904050c10050708030f10050904050303040611191101 83
    0x2041c1101f403582000d0701a00300c1c0d20400000b50f00340e03030741ca003800f120b100e0f01e001d0200c15402540c0b601ca0100300d640c02500d00d030307801034000041d010380c4126040e24003100d240c81054181e4071a4000c200102d6487ca5450300403001650191070040348481e11030f11403074020001024810808046a074403001003003801c0100500c902040641501c604029003d0b03040003452241c00c094510024009a98150070307a0300440e01a0014001c884400c0c0c10417048500001613203070401d55400043c0c3d1181c0c0d65004264500310884001603444c0c400e070041c5400e201050304070340d003980e0005180c0c041260303014814089070201c000f14181c094072142d50090030342c070440e8402e41c0e0110f5404203100c280640400e1203c0194400c8400b0a2800141e80c03003030b1000d0142130f20180c2640300038000039540712007000c0300c0c5600c28601c1c056a24465242c0001030000c14050301c00b51816880401008200f1407a44540b50904150506150404d03260003006112416004080070410807114040e220015003500b06081000c903103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 999926393 1250 999925143 999925177
    0x12080c0d03020c0601050a0b0d05070201020c01021606050f06010909090206210f06100c06020904090203010c050a020c010815011b12030b090c03011a03091c080411040c2003 76
    0x2200010301940240c41c0f64105801580f00002d100e107410480b00040710103c050060505051a0001c0003c05004049609654080112002846007840249030845600784864200c05903820000c00302d41c40107020100741d820000a2041c2681c0203c144000c60310100030200c0e00c00184e20114100d8054021058422080700c140c0e2040542c0d54003071584202101d9001340c00355610300e010009a070000300030358004104204810300100d40140c00900120b1009040402d00340c16030383c0030032b0840340c1c50160b010008501141c00340046905110750b6112110902e0200c01604200d5000200584400c0c4161f0501c030000340d1040d0080340860306004925080314581c924134441c40400707405031031b220203003502c0307240018009003d40c40313401c003900d06803503c001080120f08104007100c0c2c01603002611880352807180c10f0301c2701d80e035005981c01c111080d08031b03580d512480e042c20f2030f018810000308003020340316a040c41d600243d281e5100e00c0900d401140c81c8071403088420035005c001d082d44182a01481540f108e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 999927643 1250 999926393 999926413
    0x9030602071a061e0d1103060a02040f1203020705100215010b19030e060412090305031c0506040207020f040f060302040f022a12030726101502030412080c 68
    0xe12032032550485501004490103035901c2080200e031a510064401c0c02600450413808076080100c00311071450f00c22805c041c210a11003000900c0c10b6001c849071601c480d00028140f202d000c01c04034950007801e880d4011621100da5a401035180d880e00d006103030142c2917140709554402d100300108941c10540c1c0241d2074180d40c40ea6240c803045d0703003e03032240c0b0103903d0451105034900303110348035411601a194016201c9620f03140c0c2e031062140c0480c0310702400c0041030140400890400c1c00180901540125000d1122000480001c00c1c0d403801000c0e640b01c2c61060002501603200c00b0310102d175400049400203443c41c2d408032a8401010b650300043d400c030785410400208110994010107401f500a079840d4100300700d4030a101d05981030500c040c03410381c21000340030f00e240d03000d4005160410224206403010282401851540042c504035000a00111a0510112528011004001e05002c03d03460640c05485880650350380300c1c40c401c48264485610401c814004c0341c90a8030100e07008501a5a09026 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 999928893 1250 999927643 999927653
    0x71715151504050904030f0905010e01080a110c1005100e160e03030c01020a03270f0605150603091606030c0207140f0a0b13050a1a030a0f0606110111030c09100903060207 75
    0x8115a0707211f0100e1a80c52000c07480d9030250408102c40c900594403000c0660b203548c500c0d400340c5403000060817003000611884c004840203208032000b2448140c0c0001c2d440c0f40195214080101d01e9201c03400d142014001d1004a50080740c40380eaa0a10b203050500000c0060380210345588623a040070a031652012a10200d501e03416000008441d02d05003804d2000c240c402080c0220700b5a045e0002e10480320103c02200203144e542010f64030200c4500311510301800600401c0107039000301c0d07001580790482d0104001c240f00341c00100300030b810a072500700454212004003030343e240b01d540651604410116540362035030340c40c00d0ba407003406040039146135020b980c1d6102190968005a18a801420040074007003003c0c1002c04000f402c60f144108004202100d0007646482640040d2103184500d0300e48080c1440115a40110b6000f0721031542c6140e03419603d6001b0b142115043d18840039000c030204140480004282c095030340754401100c007802170380c07840c0c3c006613145600c0c2d500c024001400400c210040c44 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 999930143 1250 999928893 999928907
    0xa12020307110f100f11040608041104050a05091c23160501020307112e09050d050d0b040b10050a020709140a1805070e060307030507171515150405090403 68
    0x1301400c60180144405000070b5002c0c4c4031001c4040003088000d0004014071813280e21815046400b41061105884c86030010400799402242d900117a980c5903c1446444141000001c8a002e0106843c0c101078040b014010b04011b2916003440100151060703140040340424101e1703101d01409501240704100360700e4014080d4200b101d03020046130b160281c3c103220050128041d5010100c0115410f152094a80c40790f0790765800720010848555214058030004600700290101840345481c2c0380d031180b0715044068240c88501324403500450900f06400381646840d00210f01041250511300e8580a032108100d181003032a50111484a0a025092580319640c2c0d40040c0a041350100620100040b050303240300034101d0000061460307201902c104205040481c140c1e410110007000da030320240d0742c2d840381898a98035401862014540040c441c441c0e08040161160300082c0d03803004c006515144081458170901d800780c0c1401140b40d00710042503018030104841c00782000400108032814a420010002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 999931393 1250 999930143 999930163
    0x92c040f020301060501050c15071e08010e1014041107050a240204141002102306040b0603070c03030b09090f0105090313180e060c0d0c050a12020307110f 68
    0x2d510b00366010840c6e510030001c0742d01c038485a200800c28405041c0d08106038400003002401000b0401030b034903c203d40400c03007100c0101c1b40d82e540c2e04640e504127982e4065854001d40440044500400200585000704c0c0c034003544401d0440300004c2281085190f03c42c18411908000c00c1390181341904820054401e120002059403081c3c00c0041181038620003089106c4c90245041003183c00d05400c009252041c443e40c0b8103581e0703106503407030008188010810b4031000e1500c0c10516003039150440b5003401e95490765030300120485083c007010465101040403444090101c500b00036000c40d06000b0301d40070745c021101641e801341540e101031611a07c540d8580e05554504449942440c000c241c10b69800400c1c0d40e0165556030710b00000c01c1c9000003025010b6035000350003180b030b03071941910740c040c002c28825a44244855840c4d50b07034070008503030104c0460789800310341d50030b01406010074076030396901c2184400e41110740e00740181d880c1c8824400b03035480a00f800c2c51102d02d1140107a24540c003003004ca944020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 999932643 1250 999931393 999931399
    0xb040302010b0607110f0a0e01090c1d0a05101b0803040203060703062d0801021204150c08010b070809030a050c10030908030402010827010b10020607092c040f02 71
    0x405201e600f00215485101d50143c5003035680040e40341c842c50800c21603181410300030304000142c0d9448a400030034003800d80c004c1e40c4240d903802d40c400c0702c030341c00c500100e1411803032a80c071503075030422540010000b00c00380c0500c4d4042d006c07101c9000d41d0709000d0a01007000c0001039002c0141e0158603d000717100384c0c3c0211004ca00a01030400071442050090050b401070790101421403006405203c1c02074031200402d10b44203ea000c6007640020014001e1004103240e42584c102c2c004140340900704807040240002c58440ca01e071900d00f06140580e4050740c0e40341515124501650340c2c10300d5040c025114002d07240da1030350501860760749004020700010035411402c02681e41484802900e00c2c198200d441c910005442c0c44001c20000b40190f214840181c5d00c00b507103895040b40d03039207560542c042c1c0800c1c8800701d0b42c541c1e40d0303000a168a407074141640d00c04480b43e0702c0202000c4c500000001c02000051054a000500d06014034007102814610078034101c0201680340d940d4503203418161384140c0f20000c1030780 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 999933893 1250 999932643 999932651
    0x90b030a05073c06030f020f0301030b100501050a0212090103380a0501090b030403091a0301030507150c3008010f080c01140d090206190e01020f0d080405070e040b04030201 76
    0x3070401240b10f444000406000c164941c010301e0f000050f00613081c0302d034400c91038039403c004044030710422070080c50295001c0c00c0c2d00142e42c40d1252030860b201c04907803c0141800402e001d800c00d2154006a501141511141c400340c5640c11480140c0c083e2512040e005500084001b002100010141600d0b041200c6040c81f00b04000681c4180700020405000b043e0004241180a11940da280401950014401e2410003c036a0351595500d10503406104c403500d0400d000001001406010041003000d0003200d502c1c011941c2e40b0b00c0c0003600d03890312542d0042c0180d01c5d030321f00360310100b610201c600840012050000d490130350f46040104605024000d05c50307008540c140102d892400012040c141a2042c0c42d903200e06c3c009a0703a0782e8035a410020350204580d440d01c11110060710346c0d00c040e182404807181d140003050030783c00002d000b0342ca005000130f04550000d64031144401c00041c070140707150300504014103070b6242d9007005800d04041303401c0841700085520074001041800f81c0107034807070f500a0340204 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 999935143 1250 999933893 999933959
    0x3210c050a03060614040b1605031b0f240a0e010e0a060e0705030a1e171c0e190804050a12051b2407200118030804090b030a0507 57
    0x17642e141c01c014407031001e20500740418401036260100501c0b180b02c1c5014104610401d0390307116440c44c0e000311150b00000d800a0320380003e007841080054140030180001c0c00c031020304191030f0f0903c8907010078503212100c0131301c01040c2d4842144d409500742002c54002480200e8101103515501d0125080446000c0c1c80c1419039a10324401080c20380560b81c008000d406100c5041d21422001031646c1240c401c0d000440d49140b00148001d040040d41050100c80181c0394400d1a82c1000f00004440102c1981d90404d80d1002c040880031076550300c94904000c800e40078010780d0a10f0740c0c15014603000260080a80310340481c2c540701c01c075000340c94584030300200ca040c541d2441600a03481000411107030003165038000180c0f402405242810703600b44c0d200c04542403c0e403648500f070044011205842c1d044864512030300d40d03540c0c095000c0030b035008035140411605203903591b814001d100b6445405881a56011242782507503013801442c10103034020007100c604542f68600441300d1092991404510583c261b203403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 999936393 1250 999935143 999935147
    0x9050603040b06010507030912051e01090c090203090726070b0a080705090d201c0f0b1308031e0609010308070f08090409081c090f03210c050a030606 66
    0xe03441558881540b0721a81c4a0000558040c3c02841c03045090065841c000b241c20300306000030941290092000700050680f00c0c03000074101c5281d04a1102c280d040c105684003280000d010a41107480551006a4035520540010306000650704a801c03051500400c83c030212154146800b140c1004000740e424040d5030380000b003030030b00c503c003110004504400c000442050288002d480030f00c0014003844406000c2c0d50340d4002240e52072400302c50480c440b100300040f5080001d00b1900c001c01c0f1403c000d0b040c1b001510752480d006000c4800070400c10b0f0a1001803801020b0382c420102403940b00c0145501d90901c80c1444912800e0780800e0686801003a00040351361800752000c0b41229084108145089800c1d102c0500c2c0411210003955009401c0000005a03116842205800c1d0b00444443c4d4403078151440510308010140034185a00e41002c8004000c650080b030030030b1841c1c0c0e2500301480100400f400c42c5c11074800040c181c1c060540b0f040603850300c0139001801800132004a5a007042015101c11007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 999937643 1250 999936393 999936397
    0x80d0207050a0b07170c030c011d03040308070c0f15110604020109090207030221180a2103021513061d120906090a06020a0b0f1603020919031101090506 67
    0x81d003a840300d4840820001000404000e19000b030040040d1440b00d0072003020940d0561180118042030340c00050340400d4480c00b03100d402c0c034420303525540503624900005441c2d6240141d01000d051103c00190b03440400c007030143c6500040080c2c000880c4100d83e56181c0c03221110207608401c0c04100004041c0311100c01c0846d045110303e034161030720206282070500301070094018034001c405501c10301c000600c800c14030700850700b00041c40b10381036070740c1d01d24076402d038401101c2e1141114002d1107031a40522011400c0003003a82c074034034500d200100701000b03808d0407450000340882a1802002e04010f00481287d01050410b00901504040c0120300300000040c004004225440702c1541055010079440b1225000900ca070400040c40341e03040891520001d9003c0c0201d901800241c2e209840781e2003003210345844503a010824503030341c0c01e440c03900000281d00000e900b01150201540001c5080c1d4968591942201103507031400d5507020107440e0b00d030100c02a1003082110340031420b24140000e0503d08842 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 999938893 1250 999937643 999937649
    0x604081308150c0a02010e1209010f360b0a0503040c05010203121f0b0c0f0105010b07080a0327060b13090201200705030f010203250203070f1106070c080d0207 70
    0x36409065640d0001c00d060f990300001c1d010f400315522a901c0c48034850301080003c00d02520310a98a954040440014102c84104001c4105000014035080b14205603184450500d84548403134442c400c281c3d0041072100f000c940c2040c21400400300d100003415602802661180744628100d00260351108016079480c0154010720000d00190b070001050520700d240c404403094541b502e2072a03110b80302d074407901646c0c0202200030416885008162640c8000340142801040803a4805180c80142d80740c10f8820700c41c1400c20303002c0c1500d50044020390b03940043d9514580100c044003000254140c5403c401403c00d000409100340b200050380c4800c04214400d0300c2002e03905844142d240c904c503005049902c5070705050981c45018090001403186c070148054141002041d00050360b900e8214501e100380071031202c8544000e00b07201408000d0355000011208c4407900a540001d903041140f078a02404c10300c0ca10907503001030021130300720204840c210110054401c0282501e00107400726070100c1c0e03107a2080c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 999940143 1250 999938893 999938923
    0x160302011b02060a1206080f03070b060d030f0810180b010806060a0912110d1406010f030c141f0203120f0f040b1f0321080f010b0a02010605030604081308 68
    0x2114045450140d410041c0010001c40e001c500d0582d87e007140c4e0700340550f0040c12040c3e5000055500c1c10881403121aa5109804941a48501c0c04603100102401100c00c2c0590a002444000c16818111251070130020302d480601c94030380c3e001201040c0003030700e0320070441c07408201c2030004101e4500d0310307000f911601c04840c1c1d994502c0c00e00d0070b99802c000c984509420340e10b5072040c0d18541e80503282c0916403290140140010204c41c0d17980d40000d450550140e02144546e44000810300c00030704603142c00300c2146d003c1641080404603c030001a400030a00149000e0411030051480400d80c000c0050700760051a03007414062a03035011880ba4082c10304461089800760000009000a0808500c00e0b401403502d8060710b200e43d40a80c505030101c038107a00300341c855540c2041c41c1803c410216071400d54488640c40c09044504029580510360001070161702c1e80d100010070380803d4103100350320403001000010100c034410304060612200b01d42c007038410142c14580706440450300300000100d03120340f11952 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 999941393 1250 999940143 999940147
    0x14160f031a010e011106070903021c05060609071107090f11130b130e01030605060a05030102130e0c0f0d0f0510121212020d060603050601020a05060f0711160302011b0206 75
    0x8000440f0803801054030a41400001210008140307020010684a112607071200c10310a401e500400401c2010f500e042000c681d154030070480059404504035421400a95400031252241a0143d500000128a88c1c10a00c1200310010301c0007199004100560442102013220410415819003140300c0d41410002c00140064100b00d068100c400178481510301140400030503854802e0090072003c00e0b030042d50120b4803203060001d1751500a010200402d4102d0085107800610341c484000d510343c1d0703c51000ca4040300c10000306400c2c0344004641810384045d0701c2aa50b0f6210044800051a0a98005008602c2c0000065044880800500c155041464034002d031501a580f8420014480e05408042000d04240032002c140180003610b1554417800000c158241800401001c07614000e0800d0704660056045002240c03001c1041b5402a9070815041100c0c1c0d178080c8280c403451030052000075144140b001e0036400c00504840740040ea4800d0b0b980844907024034503c64a02da081c0704000c1c0d030000c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 999942643 1250 999941393 999941441
    0xe1908120307091a0a02190b1302010905031002031b04050a03110103020d020a080411190b031302090717010f030b070c0606180b041407020a02011214160f03 69
    0x1400d4061a4840464903200300241d883d10320000d510010030555a00c041c00200386080c03019014000c640c0c52108811102540c1451601c4140c80781202410a0031420f132002160000e691046811602804019040341d80301512120803c00a5000316802c108010f40c0002d03140300d0700500c000300c40031aa00140307146140c905503140ca00e00c3c8103003410454103040c2e0030003942c8030000d5680040d0030703441c0e040d480d408154030b8141454a18840c003904118407441d1150030701c082c9408580300e980240c410f10017045441c2e9444019001d0501c58800c00030703500205c00810820b01d02e51045101e20041c24600c0407203100d982c0c4c0d00305d8099000483c00010000c03500100050f0b0a54414002c5854140c0180c0c808580c0941d1182c48200b80301159000c1e1850b245c480c0c03800b060906040c020441e074880c148543c00ca5030310b0700c500c00944890107404024100081032504080c8c00320650000c3c201d003000150700a0f03490510340316183c008201003907500d022030f00030408034401f1802885509111a001031522003407440c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 999943893 1250 999942643 999942673
    0x6020606090a1803032a090603150504020706020c100e030a14070b07020f0d0c0c2c0a020a0e100905211c02160308040311060903010c0e1908 62
    0x50000e1201c1c0c0c0043d40c5103481c80799002102c864025143c080d481c005003640102d018119101c5001798207540e0117000070200071240c1d81c010b032000100d401c50700d400910362145140610107000c1c2544104da1290000c240c060074455180e009050032015003088441ca40d410240b00c07410348100180985442e001403002c1c03c0748078081e6044000385c51500e48182d2a007580c95944141c082029900000168405400351380320101c02c0240c8040031449040900b541080340d80d071103039424201d00031260100b0000403405018030b42e811548181c034145d604805d08078503001c40c455000750840800c0d5000140c050310701c11503a060451407602811102d556a4003030908000070b01c103000d001743c6580507880c0149212403540e010180b280d1001150005c940c0ba18107c0c262200a240015040380e51110114041d81000092034990403101103a9105403542542c1c14513800141450203600c151a4065003000c0304408156800310000104800480d0003600c1c0040034048a100c00120b401400b059030700540340c14020f01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 999945143 1250 999943893 999943909
    0x12031219050708040f170712091403030405032a060703030209010e013b04020417060109050f01060e0f0607060902011e0e0108041401060b040f08010506130e0f19060b030706020606 79
    0xb40415032098030b03100c46980c440f0f0200c162301520000107026003206100c861801c052480c05000220019401c00d801c10b0300007911104408036905070050703800c5500c6c0707207003001240e40d20f9903400007802c01d41c0b22103190501901035400b84070818001012030101c0400c0d907000e1032215078866020b4002010920a41d0041c6001d02c5203070b10961500000c0003519800c0341e80d98001800586030001c00703164254002d240c0113142c40d40681000711b01d141000c0070070055400390001c2c9070444e00302c2d12300200c0122a004c0400c1d8034520547d4031541200c0c001030107100b40903254100225242c0b00380c1c1c60200f07100103401c42d0101c0200d10021200025401034410102d5803007007003c190810700400400c01c1c5040070071806400c4541c40d81c4191264040403800f001b80e0340c0e4058101004007140d0000340518600200003031401a445007407122203a41d1841c0e9200c42540810480c41d28070600c00485000210f00360405422100b00d07203003210341d00e007400440d1a0500300490110125145074000f028503840384020440c0c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 999946393 1250 999945143 999945173
    0xf09060e010804051e0a021e0d03180306051006021b030601330c0b0705030f010b0703230d060506090f0d050a050a030c12081512031219050708040f 65
    0xd4071170641401144940f0a03801000c1204803402003203010700030b00c1030009203c1e109003030b2071b14154011840072090311107144c0b4024499041c60000d401070b031940a20107038120203070409040c003881c00042080194020640c0c4041d0f6565808954600c02c407000704190601e0070301074094043e00000c0040001c018032102464a00640a00c551200c00c024580c01c01c85040d0805018000f40489101d2000d2010703a050306500402e01d4030b8410b2940c0b61460141d4101841841010302c17950000860009041c842e803001400b034003c075149810101001c0b4003182c51600401d04c2c88480618160000446107040c0381181c03060700025020b201e603c4201800c22480002a840c241d135103005420483c0000381c014420005094403a03210590801d8080c04e0044800e000000da080a0140c0c130b00070300400d00e03031690502ca00c5090031266400728040b080c518600314014103100c000c44000f044c3c00e01056140c801c1011420485000c03040001e5690180f04850707569050340c001c0c000e880c211000d40e0215900e500700c40e41c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 999947643 1250 999946393 999946403
    0x60212040509071218060513201c110a06390807050a0b31050c03070306060620030d050705190215090606090403031a090a0b1e1305060a030c060507030f09060e010804 73
    0x4160541003100d604170010401200c0c3d1042808be4081207107040030321300e07014100524003480340c24501c400302c00c2d0400d16108862851401080301c4000c0c0e01e41c040411b1421a40000e020b03032241e09a103042681c0e014a200119800410003002515001400d41030f005500d182c01012400d0410321513a1181800c0b0041d82a17603140100512101252810003108005502c40c0000040d4685460001400c1ea5545180c64201c904618008007600000005075240c030800c1030000a0180c031005402d59683c4141502c4031103403524450031103401600410b08440c41651200060182c0d0741e96800541c50340e50840b901c41e0b01c003920501050201e84680d00510b440710703400e0b0185054440078400a00381403170480b15842d989840b00c90182c510f0404e14504043c6409201c1c148142402ca5000546003862122107000c0c0e20756120001019940c0700c3c02408000c6400c800181d103010780b100701c01000741e40181c0040e40460004075844510a11800549040300d201c0c1d605d02101e01010300044034003171030140042d51 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 999948893 1250 999947643 999947659
    0x3011e180f0b0f0108030702010f0e0a1505040812030f1314161503050f06010e0a0302040e0a0b0115090b0c0c130c0906021204050907121806051320 65
    0xc00e001c0340c40d1055806021089054648944000c0391000c1c160000d003a80e42051002c0d000503600b0403000900c6001c1c1e8104030040d44c0c4d1400c0415880a0b031a808444211fa44000e882c00142d00b00c1c00038020380e03590340b056030b1038210142d8418406102c01c1c0c6001c01c0c08081e0390005207242002da92030b42d8001f4400ca00804868052200091030f00c0466001111448070101c0b00b041140c5000714600da1440d01820103105601c6d000210144403170b401170402d8148030301d0a4460006030f0b00c580030f44000d5075000b001041082540d805c1256034044406c0c04550f0803442e0800405d06d12803412040803c082d5a949803034030503003803200c442403a0704240e00c1140c5d0340c4114504070005a0301d0b0700e8403103440400d0b03100000c2c1880010000508484503580503005542003021305842d28030405080701c040c0c50b01621184029101c0040488032039449681e452072079851700111100040d40e041a0080b514000c420078000c40e154400403c907102c40d1064000d0141e14050861801340c07500b69142800c04d600109914 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 999950143 1250 999948893 999948941
    0xc010213290c031213060609141312120b09042904050613030302211f0803071b0503061f060e01082e03030903051608100203151f030b03011e 62
    0x71058907440e8200030f4681d41c2792001051128038247c1d005600c000000754450303504001e500c42055240340541408100514032003000d822080303540060244400140c83c0382c1c0d040c501410300040c3c00e10701503031a0b0760940140d6824480400c0d40d008440c003d6400c0700207030a03541c444070f6a007003028140702c0b400c405040d000c1c04000742c21601c240b00c0e049503602e540b41e030443d03600c1c2656034030210b810703540004928242000d03414406108000181d41c181584254408044000c1e0103064240302e4160f0301c11380e4940b049004000b1041100c0320001c048510420503101090b0b00c8090a6401000000c2054001481e9800040308000c0081c86004500c0048031905031011442d00443c0340c15017260815001300342001c0040040000c2000f02c1c6c02400851080c441c0540d08088a107910b525905020000d055000b0001c540110040f454408010800500c4c0c02100c0c075148111901801780c0000d040c02003440c1040c601c1983c101030044850001c2d601a003e81c0c0704100d24029802012103c0c140c0d800f8154000c150 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 999951393 1250 999950143 999950153
    0x30d110601181506110d02010515090c120702030d0b0f181305030406110f0105010302101215060905120607050d0c120914240c0c010213290c031213 65
    0x190b01800c44c5030307030304010009070a030014a0581a25840d0b011a8545010442070f205400c0c40c443c0700d188101d5003101c03941c4540020740b10600655040c0c400e014034180500440940000050001c61034111050210791441400c005a04401c1c010942e0040400c01000f062410a0030003030764064109480b400340602d9030348485155130002e41080002c07a24810350301ca200c04080000000004c07a401c001e0100b03604550124045102c0001c070142030000703a00c2d106404a400340c200350150316580c90b01c0c00c0019581c200c0203110b00c1281c812103009887d003010400040b0303000304400e8403c218a0316483c0c40d140404000c14018a00d00e4084000c2000803812101e9402d128050030001d980202440000c1c006c80c246560308140903c40c80300c240503503580b0f91081d048070740c42100b544a0040c030760158840307040c000e80901a101c0c003007049a1610400101041d1004580c001019148410700e10755200b2002521546003441071a4218100d50f2042c0a00805440c0807000d01d6404003070010030204401e555654 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 999952643 1250 999951393 999951431
    0xd1e020f06090304062c0609062107080901181104020702091306050c07032c03060420040911040207030314010803070512120f0c2205030d11060118 65
    0x700e80c50b150000030742046070707641c801d08040385010098a04141083c3c40c03007035409419003c14006014640205203440540d940d1000d44085800f0746030701000e4100c15814984080340102c2e03e21012445560100303002010510a21700c1040c41e10302a86907045003521002892080420b000343d1054003000400010f80301d02942c1c9000300503490460f80f090b07050380ba002013500d1004100b601000c2b000d20800b004298420040d941018040326090b02d070042e404204076400c15181c0642e41c25215800c00d020422031034804482515110032034407100e651804040200b51202c5a10203001441e40481004407031505500902da041e20034200020031500c000314413015102c6c241e0003d003c1e0342002c1840b07028000d040c05140314005145809520b81403510240f8405c4600280c01c2b95001010b81c0e0004008060f09030440e44079036a41c0c0314000b640602e95044005010040c040c1c5d9020340a013108c1442e2803070180300c44850840e420406807007181c0c04c000e83c040c24000c1950492810944480f44021100c9081c20 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 999953893 1250 999952643 999952651
    0xe0f04021c080409061e05060703020718090c0e1f08031b011805031c05060a150c050330010302010503180109082107080108060c09150406200d1e020f06 67
    0x500640000f521140e1b0384800c0c0132507405030340508020428040001e0b030206a0106642800e01445030b4052a09200c00003416641c0e402003541135000d0000c118071442d404000c1c42442c1c0517540c00e0750030300e22440320000b0031401c0c480c0e2007496000303010342011604507401c2091220b003500c1c0001203000c042c00c40c000396540140d500b514103400c00130b5143d40009001480c122070400071141408581012400700701c00f40f01c0c0d48207000daa81242c1c0484841140f00c0c201d1b44c01602e400404484d01c45402003841c00600014028413003071245401c99105101da0844043d50403290140c442504554030040080d2190301d20b2916078403913541e5401d000740001d086c4000f40030031014a84111180d640904003400140c1405096081486140401040140f800154241d4480c50009649489014040200daa0b240f00c042c001d54401c4004240410712607403002c3c141d840c2800f00810801140c040c0d0600c10340301c04c000080e80f00001c4080340200d4050700308000b07040d0385141501c11120304140764240b1382e0400d2800d031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 999955143 1250 999953893 999953909
    0x1c0614040308040212010e191103120301050a0905190509120c0106060801060804021509060f0d0c0228021507021002010501170d230405100201060e0f04021c08040906 73
    0x290600056003000745030250071450240c02084084a0340521556800340d082d454010754107524844d10403c0000c3d20b96284001022b0200d988c0010705e80c0b08803506420034003a1a000e4000803000180d400158025a4012035030f042c68848036000b846242c501130035000b4100612407180c86003c0d101031034013900500303807405440000100705040c60320082a216040e0710000810140506200150b1b83c0d01c801d000905036070048440ea61495480400c1d400e0080e80a405141d0f40003040720740842c003e680180720180c03051750984030914050451070320003030700c203c0110104002e4032821a00501f420b00d8505582c5016111042c14440ba690008500e01c400080c40d40c010303512903004001c1c5081804c0d540010420309000340c02e000308144402000e10035440f0886940d549410380500c201580c6200b1030b0050711000d440c0204407415410068042c040900c550300710340010b00300042c2e2250084440c3c074080ca500401000c151b4004025250060003512000e8403040d008000009044645205130ba00402c091 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 999956393 1250 999955143 999955157
    0x40602090103061a0a0305040314181005040b120613020705100501050a0605180a051002330a0f0b090702010b150c07060c080c010f090605060f1c06140403 68
    0x100d00060545100fa0300c040440b00d00b05002c0d89200c6102810b0b00d80700c9420380f4002405694a00b402c40d44d191182200e06408200040d04040912120784041a0601c056030140003019080390204c17000d00c00c91003a952002404d0242042c0075030a9860140c010200030002c886452119000c1400c0b85c3c00b0741002c4503070390320107606500f104100d405000e00400c1c003213138420090361a0a1000e4114407a8071311800c000c10b4040703144102ea5075034221490150401800150f02da83c0800d00203581e5407001c4030005808105140c48400e130045004c11001d4807410f8503a081507a44071041244060440b80d141035408645480c107801d0750781c44101f1050f00c0740d0311550001c0f6600109100340b1a40c02c10b00005403c6c40e01b0100803c09000100248010840b105443c110044039118140400240103e050a810035401c148907001c1080c0c041d0041500f1900800e4200310341e032141e20801036030a403503000e100c3c2c01501c40f1440d141c0410508010040050080001003210803000981c0c1c1032440c41210704030082000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 999957643 1250 999956393 999956407
    0x105070504031505150f0a030b130c170a02010503071205090309180c190c05030409020310120c0303030b01121103090f0303070c1b08030d0b03240103060b060909040602 74
    0x3c0e4184941c0341c0094290100a1410500b100d0079803402e615801d0383c02a91640300081c029198499800000e640180751b023000d5040030018080030410354103050300c0c0150640c0c80401c404054400140a050f0000020034103025980d00540300c5401c0203004a09112180e11000c3e03144d10540640348c4201881809565100200f40812010a00d01c0c0704051501280204010100305403400b1640102584100207002c0002003404442d061a80d80000340240008030300003a13101c041e900a0b50107082c200128608950701e42c0300c4601c540340030000c05010040008010000312340250700c10481c030fa41c10324009009811001c0c442042d1000c000000d0038000e000002c006041c170081c40700c2d03071524581c0f402840c51810f01d910002c001c10b04d4035170040c0c9029290500384101707407100e0100c000101442401e998440302e69500c100010b00c3c0c1020000e010380a21181c00d201c450441e415040b1300c0d8480e2a51640903425a25044000c3c00d01c03008458002a042207928410303542c081015201d50301c620700240e40c1d405d0b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 999958893 1250 999957643 999957653
    0x10905010e161406040b0d1b140307030c05131202040b1c0311010b09040b1602030a02070905150a29090d24060b0703081f03030f050705010507050403 66
    0x225900e045495a04030744407114500ca07480907074804555000030743c08981d0000a002510314400d550000100070b500141d4850610000d4201c0032081c103415500f040143c441c52400e6a00007114281c0221328001040094400c0303001e42c0c8441c1d00c0d1740880c0b070709a0400b100081145986002608242980302c4485020001c41c5003038000c0c172040c00b8007901c0400c030103800d241e21102c02141190b001800e1002c1e4001c0115912425401003000c018000c0640b903260900c3c3c2020100101c0c20349544940308000000c44000c076000000300d0325030040301c0d40184940c0d0f240040041c02044080c0500c030301c036a00b84114610b160781f0203d205028200ca4541d4550ba59403180c01c44000e0020703c2c401c65900c4405102401c030982c0ca0210078000a42c00c59510b40e0800384e495180c0c0d8181d0381c6814280a00380c42e005010403907103400ca0103030255910949840010703480300014084208a0b004800c82c4a40840000b400041d209840e2212019154200b00d030821400781d4130300f0700f529011aa0800020404101001840703 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 999960143 1250 999958893 999958901
    0x709030221060a0204080309060f0d09060218030a03090501201c2a110d0b01080102191701050d020604030501050c131203080604230a020306040605010206010e0a151701090501 77
    0x224200c0f104528091070604a030761240222280280303d03401c04901040998400401c407441c00e07178130b603000300320040c05440e0460094104042030380f611031200140c8002410b000500002041e0961100320b40b90f03141c88011203041c420f801c002a105402d00402c8004910200002640040d1550400b03401d00c240a00042035144212079601070a4141001e000040c0c008402d05503000703800001e8298490340301c00200b4048030348040010240c0b0340700c20000540702d0341075018042000281c1f141c5200c0041c08401261000350349500910003c030a000100300c549001c00000d1801071014045905003075480c4ca40c41c0c01c5039000c40d0f40c030f14a0200050305084010000184a02809100c12914103840c8140c400408203000184001c2c021035842820700b105003220294034001246540c48441030385010864031000e500180e0700e0500640c2001d0000c5410340c000329581b4180e13450403020082590743c5101c0c00014000c5000300100d038031079450010400030b9101a440d800283d104c000403c0d13032507403460324500312 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 999961393 1250 999960143 999960151
    0x302100504060522080a150b0d0804051309080c060f01090603120806191d160503040807081b060613020c1b061615050702010b0117070903022106 64
    0x481003105010242e00f01e01950980141030301164030f003c14040780d030b00d0540c4450300f04540c580310f6070440c44100140440295100420b0520a004003805081481001d0f0301c100001004100280030621040c1403d81e00c3d90b41c2e40304100c001240002c0c1945414816030701c88045a5615000003040004540800704000d0041051404c10002d140c40c0d601e4003541d54469552150030002807102198051355203d500c24144031498414410030781c1c0e0390f02d206581c0ca10100040562070921b00c0003501003d01481003008801141c1c03200c500c0c40d6074039902d00d100c0343c2c0006000c40c1d80306402e0007955900190000701201c0d04071901c0040450303043c0310b401c204507440110300400d0042c3c0100301d40d252095001c510082d0321450058a4001c201c421000a0100e0040401c1c644d444170700049442c2c10300102006098691340e0214003004542c40e0303100100c0c261010100c119021490070011030f4000881c405125500150038a068102c0381e07280c0d800148802030300000a040c26a818a40c2a8924406c0c4696500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 999962643 1250 999961393 999961397
    0xc04080d08040803040f0510020a0509010206060a2d08070e0103150b010e060d090503031627120204140702010e0c0d0506040f031403010f03061a0112020d11070507030210 75
    0x70614240c1d88240c41848000d03c0180200c034503d04110421204000d2801c0082d0602415500c45600000060590700803030300c00b90040c41500041030540c14400d0410050301c103441c0c0102000d4180340c00c1d009000056000d5038401d4203903054001401a41401660b0140c4107500d00e01c7d03804d514500306004192524a800101c107440c2020411191303810184049402400344d44094441c861404000014480000058458000082000341e2401280030411303c00019443d201d54120030b001e07007072803051220703008070241c44148041400100310941c0b003180190710060012500314498414080210000d40311800503030f45440719035192040502c1601c0c0c1041b41961000070f086c01c0342d102c0c00e542e0b03240500040d00ba08194070480050601c140321030f0100303c0340104410359a503900d43d0b10402e406101d10042d202e452521085c24101c2d46c0340c24810b18030820580d1068806004071150300d0096001c0d25861070702a60340c414038016200b038030021302001401400076082c06071450040c42030074a4036065101c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 999963893 1250 999962643 999962657
    0xf050d030c2f010e01061203080c1201050f04060b0a0206011a09010503061201060314030a02070906080a020f010e04090605040b0c0901200703020913410c090c04080d 73
    0x38542e5034420080c042600580e01c110300d03507200c41042e005209481d030b007403840d500340300c030109070130320555003440b1030383c2c40380c2d403040c44955440c5100007640c0507050811f10b402148c0f90040000d880c080c80100c2031108010000102140e03540042445036001188103030150b0010301c010800d004082456040744016501002e15240c44072340020818400105018440e880b03a98441c60004001d503c020040c6502c0300c0750035104034504e100540e81c0d0300b054160b000144550000456244000d02804040700c403000000d110b100a154200035054105445160402c68500928070507941c45028810071503000d004005810b0a050520a4031004010401d0811080c2040700e0310090340d01001908032041c000e0302e650b540305c280b111028148a0f5a61020b940400b00d0000d201c8103100c40d2440042940c8105081d41142d411100c10302ca01c40100d0001c507050b0522480150400008202824040c1d2202e1040c0c80003514036000042c04004299a800900000032400b8040c503641080000d20f48807031410240 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 999965143 1250 999963893 999963917
    0x1170f10050f010e04090c0f03150e0d0906050c0f010f020c0c030f03040e09071a090f030703020901290304030504030b130209060409031e0e03070e092104030f050d030c 74
    0xc0c0200110030225406586e40d400054103000c0036070034020140c002a41c070f0b821303980d5903418416004141010240d07d054504040e004d00f14100049480c4404090b071150711203280342c540203075510307000b0a40c0d4249a018402042d0010705081c42401078262910400603202ca401100b4107203400c41560a050181d0720004401031495000820796040741c215648061107682d9502010781040c8403a40b22800307204203a00500c0700c07509410b000c4c181c0707008241da200b1041c4207002c0400d40e45100310711000c0c0d0800d80e034000500044043c0f9081020355510100c00040340c4185c015266155803040b1000c3d0b000540c0402c090040080100743c040e00140c000f0000c155100340c540004118030303806400d00c0e225a940c0da904000305405001800501600e2210304800958618009003640c041700005031b01c2400382010110301010a00d200c0341c019841c1d1801071040c4c0d50f00b405450405c00900b90321135240d000910000001803d814201168184190060180406c403401d016069516801501040c80032200d404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 999966393 1250 999965143 999965147
    0xf1a010f050603042d06090602030105040f09021536010f2d090b0714010e0327121e0c04020301080d0f27080705061204060b01170f10050f01 62
    0x40e0b5441726030501442c60444400c40742200f464100d5002040070b81442210310038011075a02441c103d5a0603101404090406581c2d074045400001c1c0017035003c03220102001701040c142004d0070344010705400d9120801f01c1e610640b103401c00140d41502c0b8009082ca8500741959100c1e0082c0c00c0301c2d102e8140318116682005070b50710344a44205035040c501d801c400c1107844640c07150361001c00038000003454030742e0343c0380c141840000f80c00078044d0382d0300a41c248181c113074135400004201ca0b040c1d0070744047c850700441c101c0241c10074100184c00182d030205448803c0175a43c40c0501801c1003080e07003000c10009032000b140e034071030500c07551003850762003540705000400c0b00403400305540710344210a1a110300074102c0c0c49800e40784040c05890318411120782c4400d1481c034020128880050343c020702c045451141d914401c00c0114410715429021034864940131900140d00c40d00300e420701400c14140005800d90010845030440c9044a4098106018406000f050140103070300c500070f41000e4882da80221488000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 999967643 1250 999966393 999966413
    0x70e151c080904140a0b0a32040b040e100e0c0a18140705070201031109011407080405030a2d02030d050a0e03010e330705070f1a010f05060304 63
    0x1001d8602500000c820b04640d03502e900010000302901c84003076081c14000080c81c020580f605c4500c2c0100b80004020400c007240315000381490141c00707550100052020b080300304e00c0d040b001609400503225000c1620580d40c0e07000380311002801c08001c004013240c452400081e24500e80840060740c001100890560f01d855400c40d050b980314805003d0103106986c200001801e01c1a03450010303410140900a0300c40c2c1c010024413900b4000d80e41070100c07d11026440040f0b100d461070b0940810180c04007012050000d801400340c660040c0485810304d40e407000803900b40360984201311200b420b0150080c19040c0104038900702c40b00ac01d0202100030009901103a0783c0d1141001c8681440350106e80c681c0128840d5400b44084d81015000340160404005941c1c1d844c040f59040d115000c020029103011220a803482482000310b820700d241345a01c401d501a03566910104098070900040c50515002c1a804090503010440e05412110658544110900b03000d440342c100c0c501c140c0d0b04100384000b00d036646036 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 999968893 1250 999967643 999967699
    0xf080f01031e05030c0a080c070806010b03010306110d0603030507061812030b0a0f1d0610090501030519090507030203061602031909030c081501050a0806070c060608070e15 76
    0x24825001440710704006165000d20402c02c001c505c13071b01d20103c0801680d54058551500e0303110450f070302151285200e680b60b400900031813001600a00040010038907a412280e034207508000b41034901040034110000382c890b10f070000d40200b5400612881049500d11401115880c1114480d41c420410303507650b0301d80c1c0109042c0e001050745031080744d007042e40c40d211340d640201100b2690b00c0ca16030b500c4a51424201c0007461501c00030044500180ea5810110004085a1181e96400c600e160900c1c0c0198020322000c0c0c1104440600c09001e50b070319000c113220301e0200310b000f0b04c000d1114925500c101032400700000c00282e05c0c071640d5141000915000020341e41e200700001d400d950040501c410450745591140d2019100306400900000d01c1c2c44041601c540c2049000300e0143d207a0b807031b04103014480c605440b41c1c4015900a500040305103220303002c0039070841d100f19070204003181d0796080b10345840e0303903600402540100c04050014076800c8520075021402c0c20307030300c0002c03919a8504141c11101920 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 999970143 1250 999968893 999968933
    0x306030a020f030115060c1103060f010603050408040b0a02030c0d09050a0302060c210d0c0504050a060302090a1e0f0e0c030403050715180209070810121407060f080f0103 75
    0x6a001140703550f00303400c0b03400c0500c161040310080c6a0344034801801c054883c041910095603810703091100742400304403103109040c02024032149074600742007140208001002a50603000a2001090a280410050400303052541c000d54a45204500c15400d102000b40100d05001c035140e0100096100d02c0345000403079030100e40c45621082828481d0303050041c81d43c041824562a51019610703945044080d000c81d02c003624081048058600c0240c4092060b030295680c010012081041403a100c0e400405522401400e000000d66555104c0107901104400481e9082040c100900514064880000c024a81040d1240c1d440c1000c01c00350049101c00382001c0c04101d0001019028082e01c5c5111100c113455040040112090040941d1501c00d085a4100e03c0b4404c03a00c0444c2d1054440c0034100e00a01c54880c03404400c81ca0f06900113090998000c003151060b031089424003524030180a10701c001d1181c1e846003259140d071194010f0028000a10b51038015104500510104038007030340e5007210034061 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 999971393 1250 999970143 999970159
    0x110601180603080f120106030203010605180d0b010806160801032d0b0a0c0306060309020a150c02030708010501050103060f0e2d093f0703211e020306030a02 69
    0xc20221000d4956508041d00301e0f040010581c1540000c03a00070f01905010301d405038980d0362a04011030586c4002c2c812140050814045d107002e0b000b52201c6642400e80080c034000790300a6a0361402d070188002d0344541c0b640c2c0c0000b400c11042c029009540000d0a00d82d02d4210310540c155599800003511002900c0c1d44005545000c40c0d44098051001c5060398002e02c09d07520500d0901209000707442040342c4680068142040002c01038003078040c082d00d69500034001802281884816580c0c00588900d03002044a074a4803c400342c0c4082c0700001c050001000041110740c10440058148e48440e0703c07441641864131000c010102d41c02101a800143d0051180301d00381ea409103803861549690b59815003403c00005200100a001508c0b0410b226046d4600a01c030742c84003071050a15001007501140c80d400d031a0869000c241d020010072a0ba48a030404161440d0b68295030715824800008100326035541d103015031010404085075408007404004207600d180780c000042600c8481c0008000c0c016809 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 999972643 1250 999971393 999971429
    0x717100507050c0a0c060207050906091303050910050315030c0604060819020a1e08010b041a070b01231909050a0f0c030222031101140c0a21110601 65
    0xb1810880712614090001c545003046942403e030b12003140e40c45400d016100344640012541000c8103001e10400000300380c01c1e201c3c0d884103443c44072104441422400c100c8108004c2e4619035070741d00107101c10b0a0583d9400d4403880e02c06411440004c0701c580e100c1c801c1c1d204610480303050f903071003007154282c607101d03d841266500c0e480038150042032401c000d44c00d42030000caa11038406501803541100ca14008052407031104034082c00381c46004082c001c8071080700080005000d000c5414099190000141c01b03180e1504d0440d4403000300d00310007a0042803100c140300c1d15080818015403281600040300b1182c50804039a540c0081c8480000d5100d4101140d46660000340403460660000642003101801030000ea0300b6200014005d40c40f04c040705600700401c0514102101c1050101001c1da50702ca5003e06820003a0401903d807200c808035550700e02c0404208a0548280c203102004040e0302c42c00801c1d102010350f00d2441c8082c1c10240d102410400d950721191200040020a1411a84041040c44500325 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 999973893 1250 999972643 999972647
    0xa080c100c290f1909020d14070f060203120402010309050f010e0106051507080306010e0d0c03032003030609040809121b15030f0c030c2104050717100507 68
    0x54444054103865075106401850b0340c00d81d04620841c20208400001940e0b070403294484800103407000b6000d012424550404480150702c42d0704458001041480804002c8e80c0308484849400080d520350f41103010200040c1d221501c2c13201c0500b00e03d0024600b8901c0440d80c0d40301111008001a0405454103074240c184807007488596102803c220080c4071302040a40703154040d003903d12950740298050510400d2244a900666003c140c0c807020840c83c2da100e04004482880d240902241d0020f20040b10380c0001d1a080164402503200361102c1000085110100080080001d03465a03070340c108008000066449103203003984146e10541e69911101c51101081c203143e4124241e00251054820720307140310303410614255002d0400c4074490262140913054003100d0106807040d0004000b030380003154400712080301955008070390030201420202c25441c00e801512488800c040101d1241c0180070a0242c10b0000c0c50150850790010040c1c41c1c8807441050b9145508a000c40f8995900d00120307034918 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 999975143 1250 999973893 999973907
    0x6081504020c0d020106060915170705040506160b070918090312150e1003121d0a060c03030b0405010803040e04020f1513060206011a0c01090c060e030c0a080c10 71
    0x800700ca401c80c0c40c49420084064001c1c546e500a00c000300305517400000e40c8186001021180c401a55501c51180040001c201c500001c058001c9042c80028040458151682006131009001d03175801c94605001500f40002c050001034040004c0006405040c40303480c884000181e0300110810001464440780d04049803040c07210a00401041c1c2043c1d112124540345417881d6090301c649090820310b0f034a514411b045103d10510004144070640e80d01440f0a500405c1c0040e90b042d03a00400c9002d42c0c070540c000618025060304810f000c00c400303010000904d540740c03152b07041a041c1614204525414445000d64900a500c41c144116801b070300002c01315240d22160055140d0301a100a00f41a440b008809450300850107550954120140000e440da01c0080e45074100c812040e41c0e4003242201d8680b5400c0d9500078100f868040d0340701c1c02d080d030006000f00b2003040207003429a20f4180c60040901054205890f600d0058491203118405010801300401c06141c12201129610740400040c10140d90078 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 999976393 1250 999975143 999975157
    0x100c1103064f05150114011710150e04020403141608190807061d2401181d011b02061b09030a05010e0c130c080612070905010f0608060a0608150402 65
    0x2074507004c00010000e8185004c0d04030141d0988403e5000325030344000c803403407520440c0c0c1c101240a520344100a0541903440e003456004140c600940040214400310f8180da0081d801207456414000000104940074030180b181d055018040290081c501140c00d9a07030040303800614068a0b180400c4400c00249004440406601c50000e02511002410020000400d0301c500e0b52240199102540b90313007901224030301030682080400e02541d00b03044011402041e44c240c01112565901d00d100750f003c08480102100550100002c9040c4611101466503017000c5050801950b102d41c0034001c040701c80040c2043c501c208441c005032501d0300746001a141500d1040060007035480e04d07404605e40580450b10000c01c401c10350303480780d01c114025030401c00c446c00c02400e1b02c00601c001010811624140c00c140503022101c90460360a00e4440d00c20004442080e0b21506291811910820031141c005241c1c66020400f1141c00c07004528084001e0701d105801030640c0e080c07020144402c4c00710380da15030603a064 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 999977643 1250 999976393 999976423
    0x312010603021b15041a010b03190f0906060f05011419051201120308150d0204110d1508010c0201270c0b041d0f06100c1103064f05 58
    0x3249070109001840e08000342c0f4180e90403040e0341074032041e62850ba00e030b80307040b1200b01306543d25541c1c824120b01d081940d0500c030000b00584520404bc400751301400340c501d04a0007440c000414602d05100301c000304080d40c3c0f03c41e040c48010750340001042c0e0b07000261100e038518030169070202e000e041d000300c540c0c1c81078a07018500c00104000120361040400b005a042c0381c4281c840110b00d803102000642d0782c010000c1c4060340420422100d02c01402d103900035204000c0818801810046a110443c080d1039101c006040946a44503041206890901900047c0d80d00b600003040250f900006240006c0c040b10580f205c60141c0c10390100c10002d0901480000340524058103449540b1001e4580c840c40381001c170940d0505e00ca0012842134850551a81c0c05080e00030300300b0002c4580010292564a000b071800c0e115070000c0c42c0c00c04529141071002d288582868400c2c075500181c000c001399050307454944480b175440314050940c0494000e1188000301408203201c0745101e2429441c059180828050b24005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 999978893 1250 999977643 999977653
    0x80a1b11070e070203030106020c061303030e0d0506010603091b031101050a050403060c031b140430031106010e04110111100e0f010b040911060307110f1e0312010603021b 75
    0xf241c0741d020000d14181ea42030380c00c2e02c02e0021007408100c400c0c0661a022850040011010000640201000308030325201800905a031030543c0c80c8c850401109034040408641c617850840200024502ca0b00202141a2072241d422400c1da1285160103810061843c14000002142c19030140500309840041d680a5418045002450320050181c94510703009000e94076500110300701a800340c010f0400d66600b00000c03078101071600c0118043c3c2d803040070380000c20b20b85211030b2019aa68007441d8000182c060745980d80c0703504480744498070f0004168003094260100b2003c1c0400185040c400700c203014000d2074602301d40700e00074030814142a000e110a041c018a020044c5501c04804280c03100003011990080040c035030390310280803e4908d098001403940c1d42c0f548a1076001e10300003005c0d5801401034544002c1e1241442c046518120116402c800240c0c40211a0011900640c0c03a42003105030800c061403c041f42410010010035060003040145500441c80c3c2484800d01e48202a2016041c81102c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 999980143 1250 999978893 999978901
    0x190902180a091208070e0405190203100f050a031101031d0d0e150901080105060d09051002130f03080703030f0e0307080c1227010e130c080a1b11070e 66
    0x30020400050200ea0f210320000c421045180100025071180da00c40e100c04001052201c1040010b18005242d46007913000030b8030013111000c04e48095449020100c0d200280c150521048032460030b0b040d0703c6903200c0e014407041800003c4070742482c020780110038280400c2e880f03004680f07210a003072032900c00c910303038070464002c4240c0c103511550402403004156100314907040999101c580b40d2045842c0240410030920042050b802c020004003d6030040381070018090076256143c030b00300024610600100c0e500032a41d4080c003820380404e00010b02100c405011420310b5541da5210030f000c2c40c1c5010701415914012201406016000210072400380c0060326519661484d0901c0660420030715811144903141c1200c403102145002c0303605046221500400746011509920440074400202c03504001c1034042e524150346072040e02a4040030070540104aa00b07011030010b0542c040280301c07545040c100540d01e8a0b078002031002c00100281c0345041c400c00c961a00d0f40c41d1a00a80343d21960508034250200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 999981393 1250 999980143 999980161
    0xd02070c120503210108070e1807060504080f0d1706132c0c0109180b060a050d0f0506060d09020303070f050c03070e0105031b010318030905010f0819090218 69
    0x203020491202c1136000c0e0380e50808180c00f452000c240035030310b101c6e80441424003200b41039060700741d8442880031018040039000d5207030030308280e0140e10100108801084c180045041881a24002840000249514025860003c02c0d0722280c01030b9465080d902c002203555030b15889000c2010362801300c000d00520010100036852000b5903100401c150903607012404000308080350800d00f03001d059641004550074802016404628001130001099031180001c0c2070b507d40c0d101419200c125a00c07003d465101c1c12403079074240c415a00f52046542e00e4602000a159662002c0e0380d01900781c1a00001e0400741803010901d107100b20b40c4042c01200c5820150420000300081e684618403094043d01d811550342c8446a000314003e0040d554190400343c2d0300e82c4650032011040309007100514001c00c0e000c294025090302c0e000c407440c0a600150405400703208658100190011031000351070100c45502d0070b030401038170b03a120034049400c107241c0300c03a010420b6640e13980c0900906d00003951141200d041160310 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 999982643 1250 999981393 999981397
    0x20c011b0b060105090307030b07090e0901290a0801090b01080c1c031d060c0a110d02150f070819030513020d1b0b0c031c020a02030d02070c120503 65
    0x10580054103030301041032100311590451026507840380700d2801a444100c01034030190400005590148103019000020540803003980f0300544da0b40d1606019942440c1c5d080138000c600400d030404980c1030404150481d5130100c4c91030895000c080d150703d12580494002011181258007030015507080bc4244014000381110f0380d41256641c1c800c50312441d00c003205014070a1200074060145c01c0031501d001011038082d0150f0744a88203103404406600d0034400015210360000402c070b00260740040008003c00c4000140d0801c90102120644803440c41503000074440f5a002c49280b1240c070012861022010009065a4806074040111500e4101d107c41803848428040ca0f00c8000a08003000300307604007141000200c80c01d030090b001d4058400c1c030752100300740000d5900d8010181d446400000941701c80100c0500203012170600510341d0b82c0c42c8403546031034800d11240900780b81071040103002c0805400200722500b0803059580542c8800c050304050540b002c00303900400e004404d8410030380c00c06c840880 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 999983893 1250 999982643 999982663
    0xc010e0c0f0901121e0f050607030b0d061e051602070b040b0d0b0a050907020312100503210d0f090605100311360601260a050414010c02 60
    0x490340c0a404010401c850889030110311030300b1146460062040390788810681509a011341040e042c0d02250713001c41c40800c51138041c1034031051114007411301000010f1081c581c03c04024a801d20110000c8800a03450203440040107040300d5442e80c541101e0030b10b4001c08217404003011010016031030462a0490210740444826005010310310000c1071018400c13080d83d00340c50b4003006245c2443c603a010b40400034509200701e642e00c07c10040d0001410f6031411541440703890150702864030317030710032080342100303054040c00341804018441801d1055860010f42d0300403080601441580e01000011221034500ca0b400c021905207083c1390400200c200c481e000844120f12414040216070745080d01151a0031740c5010003083d41250780307000c59031481c21034500c0b94046014a1020036818082004401c00c0202e003214604001d815400c01901e0342e0005a080d0085011100b184c400701072500e0a250402001041c14004954030340100b03041c4110011845000d0b055100200030042c101d0350080e6540c0b002003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 999985143 1250 999983893 999983921
    0x102100c050a0807020d0e130b040f0e1002030108120a090b040617060105030402031b0102150f01090b12031e09030102270301020a05030103110f1f0305070908060f0402150c01 77
    0x20f0200b910700e0320001c0c1c0300070f0300211aa941200ca070117103001c1100c00864007187d400d130103469180700301c059500d600c03548031000420b1000082c60f00300302c04424104011084451001c1c0d10600040100c0c040200b000c07410303584862040b540d9640c0040c0161600d8030b01c0c1e000415245008140800c0d069000019a10b40e0013988400f12016956200116410310040310025095000300c0112503150b4564141c1d014660130500583d540000041040ca080c03c108131202c015003020385004009885051107813052400d0252000c920f403009a811103a034904c030340140c200301d0780c0d107540000344680900001d5030400301000b0001c1d50340e24400c036035104559560079070aa050081c0014140d10034501482100c104440c03075140c4504584c40e58035200300701c9042e2503ca075000040800306005035603e940c807180848042d041171031039070340050340000c007140c1d402071030841070010b01c00c4244000040058642c0d88099008000440303030b6264408900c4141c0348400300d00c03400c83c011076010f03840801900040301c0d4800716 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 999986393 1250 999985143 999985157
    0x905101b02041e0b030106210b04030908010f061401020102040b04030803060a05040524010504122630041e0201030b0a0603061404020a080f0a0e0a0602040e13021e0102100c050a 78
    0x2038009084d910a2003107902d85e112300d00807507000058030150b1010381c003c1c0a03040000301e8542d182c40040c2522101030344a42500d5407804240030b521546a01004040000c4c40214103080c10400c10a41c0d80c0310f01d0102401018000c000526603640f110517000c090304001c4c00c203200606044090b034040302c000f50802d8030f00503810108408654031510640c0c040364407a003100d64900446031505804c003450f285801310041c0d5907103140d0380b18140e070200800169140350130507501e196114800001000800d40c01e200910000380a21011070282c07040e80b20406003002c0c15500c00003442c4016002804088151600f02e45411800a81c0c59010380c4120f0440e248100d030030b0961824a003c00003248600c1c0311540c00b062140d00130605404400c08640e80c4500d408500142407442c1103855440c181000c8403c83e040d80d00094180b040b18001c41a264014108040c40b03440c003005980012048000f0340010710210b03811010022044c0c3c03080100e1585440c4c44001044001141d0360010541d501a01048003c00e1007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 999987643 1250 999986393 999986399
    0xc0921010917210c033103050a09080303060a06030b06070b01091b081e0403110102120a29010f03021b0102040519031a06060d0f0501060905101b02041e0b030106 71
    0x10320403e62054540c455030130b1666a42041c18010b01c0d051458050b41c034054800c208102ca05400c1c5080351050003034451980780c0800e4403000f01200600d07009603202d50030520030300c4101c0e01d980034101c0c2503a1107400c010036404c03040740106006025005010344600e11017400058030518681c8240140aa090b10400d10314043c40010f071403c00c1c081d24114880810708984400d503c40c10020300b0f400c940b0078900066002e4507512000d003039822039111803604141c540240422100c03680700d0300028100c0e524014102c090f085400300700314111000300c1414401c0c40010801498440c0c1d044405440d00c191549490903901045035000750402e002d02409a031000c0f2441d8030300311604041100720303a881140300321308d4110300b108807001ca50301410040d00107605001d2040c0e00c4240c3e000340c00d1142400f040004281d0700d085402842c005545d0700031030207101500c032600b144607071040c03400c0380443d441c0790b20041841061021038020a15442100c007140784003070290341d108640c1e811903040e40404800a120082d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 999988893 1250 999987643 999987697
    0x60f08010903080f040519030522230a090c0201090203070b0903030a23070b04110108090c0108130f08130e13030c14070810050c0921010917 62
    0x5840014000c90358810004000c81003501c0f095174081c2c451310640784405a080150744107030391008000c03000f041001c1038101c11040301e00b080320f040203950f640d034500061520032090010003000c48030028100e0038040f02c18551312000d0340b240040142c0700f410881b01e00b41c00c0000f402030402c81310880c42401414800507000e40302c401a10074104005001e14604901034100785c0d15041c1c402c0b101c5d01c0c000f6200c0061401000000060012075000b14410040c81c503091a01c000000300c00040c05051020038010310444180000d001000c09000303080c0a01c1035258003030900055844450010b108031004c1d82400700704240e41c00503044070714082040040c01511807400303a1301200c040b51188059520b102040d40840d100d0070850994034003d111f250710503141e0112450510915030000d08140e80310962050b001c84151080300d5000c1c4c901140f43d42416808000922105520300d000391080710ba0209005101c0b100391300543c0260750201c400900c5402032642801e1542250440f10040164100d071185112 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 999990143 1250 999988893 999988901
    0x30e0904020f0a062a1106030a15090f0c1d12031c020a140a0806041128180518070909140610030b01020d050d060801050f0603011b020712080f0d060f0801 68
    0x980c00184200307520845028000c41d2340001700440b90880c1ca51264943d03509040c5001000b5001d0100045080202403103142c040d145810b80c1d80c0b040003d01082c90b4012001070101e1b100e50380c41285c194046400d80d1080314074500401c44074507040d01c030b0048060854a0694010440754206488089002070861001e000d5030107201b800c0e00209210301e00203241441d0580c8450f0003003100301c941704c2c2006000f03100c4900700703d1700c1440211850401102800c46a401103d00040040c05060811560b410103020030b1001552500100c0140f0054000c60002405010f5200c003030701d003a00e81080103942e4160307070080846050318024003950746405075001071f6209003c0d2040500042c1c0081018507590740e0300320741c107500c807545100015554030b0012808100a000c5c80740980a0b52080300120b0902208150840306000364103115509005c10fa4008150085802c0e000c42e007020124181c54126801d207001184100d140e6070007000c400240c0038030405d6559101a0588020b107111200d0300303844401e420708031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 999991393 1250 999990143 999990227
    0x30506091903080604020d09031205010b1606050405150702010c0e060307020d08040501110406020105040c0b0c1b2710080105011a13091401170703030e0904020f0a06 73
    0x30791001000701c040390140c01001c2d0030400c060310051034001d003504084100c51912078128002800301d4150341c42c00c0502d025184c054108071b8012842c14800e040008141c00241368004e00d07442e20b031300000c0c06004040c06480414040c03541c0c000030901c0c020b140240201000300c680800b15081d0030311260281000342c182c83c825076854008040010001c00300b03852a030350040c0111030942d222a00850480017030405400100465000401ca904003850030b241c00851a4106d406400300c140f000b151004c2d0001100c000644044101940c060034401c00f04450350407038050400c00481440481205401f0050003d03c500c91401c5241c42c40c0da1101c030142e0a030b950a1180318844030200c100c40741740302c0d583c030000d20a1180604444030300d10307991040390b01a01c0201e111136901100d40e00040001114038054481c01ca15198060210b89046540182080104c0380c44140038602034070000b002c5440d1000c3c40d410f0030000030140d601700c558403000104200c1d9166941001c02c1d801c045698140407a4510040e16 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 999992643 1250 999991393 999991423
    0x3080304170f03011e031205091f0c080a0e0604170607021506100c0b0109020301060f090503191a01170d0207054b0411120a0c141303050609 62
    0x182d6443c2200e1013200034031058021950b01744280d40000020584081800d05810984415454000c6002004607014089640107400040c20512007080d40e40400344809a0f90300200d6580c40321000b150444100c1c0104508070341100c1c0000c0c0204403c1c030030f5800d83e01050888421190b4596614008a0325444412803203104d07901038030041002c61810822020b00c500f0641b8000d002050700f41c4500b19100401c2c0c0c000034406c0d80c00001401203651040c0d8001c0c050308107083c281c44242c0b500d00403c1d0344000d03003103080c0c0d2208004070300c04040240c041e0301e900a14039207246042c802c5d6101c2030000325080440c2c3c0b424450380302e40741c400d1400600100344081200e2004080c00f5011200d038036000118044210405650f01100356089400c8a80c8100311403019101880715401c0b98180080c0011100040305004102c00103200c107079400c014070b500140d031000d4010300120301d00c886800180c0b00010303080d120301205100441d01c0560200134141c0c6c2402c5a009100721000703501d5041e071a513101c1400c0394220a03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 999993893 1250 999992643 999992647
    0xc110601061209050102030a0e0c03060106050d090602071401052d06040b1f051c0b1e0415120c1208030a05100b190e040c0f1b0c03080304170f 63
    0x1080324003a4440d203042c00c0246401140d030b00742c0e40d5102403c90f030040b1211002965903116015419000300414604588260000c02c40381d4105040902a4000c6a5452078690b486002620421580703170150381003150310036014038028150f1400c0c203010703060450300900d604402c101c209031a054550000f01b02910900080142c50b1641410320014103503d414054104840740004a03008a02d04444031540c40150358086d1116004209100c06035600c806860015003480610040766070b0b20710706554820004010a41103032600130200c0c01a103070346107044100c140340b0440010a2a03048101e07034041c9100300070030b41c5465120344008903e80c4c6220006083d494040c00000d041c900a640b10b107030030004c0302d4041003003950f44280010b0164007803490079000200c4104141c10180e0050b001000e60307070382158103010440042c28001c01522900003440304011440b440300c84030454100c0c81800c11030f00450503503000c649a00306102203034420360b000c03500d500d00285066804400f01040d903050030070111030705e8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 999995143 1250 999993893 999993899
    0x1909060209310f02073504030b13050a08030903070510050405030313050114011202031b06030c0a180303020d08010b0703080402060a02030d14060f010e030d03052502100c110601 78
    0x1100421a07005540c00142c0d013007113940c01065a00308801c145c021090b50046c034107078071a03000c04030400c2c00e40d490b031082c280180018000078004010895100a1010018410461a003021840c21403464000f07800b000c1d0000c24008107110202c001c103c00b50003501103900c80031400f0365075412a601128081e00c41c1e0010300c0070031203490440038252540c0f4090380020544202151035400c3c25802a408a105407445491407011070605100008656420034000001181240b0110310740740b00c01807000d208110001041403600d4014540c800092280740c000e0029a600e03440c01035500d0007081155004500284000580c4a06520031245c07069407507940c144030b80c0c456500f4400140c1080100b982580400d02110840c0c1899116001c100c000d001c00c4070b9400d040c00402c0c80003010000103143d0400c4009000d85050303880010f1208604207952900050b0707680e8441c0001c81c1c0304440c5540075580d00c80c0c0c402d103241042e8000b82d6404030b1a0302c00c00800c0816080c000c241c403030700c0c40c2e4a59440140c2206c0010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 999996393 1250 999995143 999995239
    0xb03100c17180c1f0c0c0906060302031005060a020c091009090b09010e0303010b07111305042a0302031b040e060a0207060b0103050610030f3206030a08121909060209 73
    0x16905d9a80300301d040c0a50103488118120546400d40c00800000303901004010801d101090108d00801c41610303d41d2410003208070003900c40801400a500400100700071490401056032110020503410500308601c25651410f03c0d00e1440503608401c0039030030710307410481c0c0290102c2120704071180c0c841800d02d000031980e18500104d01c2c0c1e4031000d0b803007030300d80340c03011248055401504e110344e1203561001500140035240b9400000584000180600180c3c410b01c01610b00007072810003030304042e211600c1400c0c103000041c05010781303040e00320072030007048180701c1c0070119a000741a01034853785080c84805174500046088503421a2100e5000280d1100b0b807419600039488048085003203007000ca40b80c03021fa00314504900c075146404019440d100b00700c0820402d00d00613141c01c000b040780030704401c02c030586582600703004102101c200542d8440101c1c0c0d05000a80d00103035201c81e482000e002003031650800b440250841c1d107200b4050b580000c0d81007100c0450510601058a0044d0391401540c0705441d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 999997643 1250 999996393 999996407
    0x8011a0a09030f02061306030203091b101b170d0b040b060904021c18110907090e100320030625180f0b09010906030b03100c17180c1f 59
    0xf042e600440100480314104c841103082e080544800d07240541d40e030810500d110320340035141c022051750001080210f102c3e5038610008825142540c64041400a6480100810340c00c050031f00822a100d21222100709a02003006001c0401900c603003001041c05100520040e10080c840700f80d4403041c2006110b4442c6000d03030250162030305c0044402413040841e413003030b0200c41460301940c0001d04084461010400c4040c0401004501079801c170900c4d0900c250058030100705801803003046542000043c1082e02c5a8541c0720045030494000310043c0041c0c511b0000c84208140054043d0081c0c1000820f02881e48600140b1241c640d5106048003240f170f2009c40343d400385400103000c0f002d9054070004102441c41c2001c80540390400705150f880306003400250148600b90702820516042941d004215540070521408000c6030b1240854131401444003114500450202c1000140644c0300780070007541e010f655922440d00700402c9614905c032000c2003000120b14806040460741c154446040700a1203495 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 999998893 1250 999997643 999997673
    0x10e04020711030a1506062a0201020a05060106030204170d020c010315121b0f0f140409140a050d02010209060d0b12030712260a1e090308011a0a0903 66
    0x142a1286008403030029003441151813094880c41c104003d410701215041c404c802c0200007506011801c44441c03406000b00e09909640c0034074100e0910594403d6900038801302c0d2645a09c2400e9414540c0c54140c040c000750420b008105001180210b03040110000044209059045030010074180064000440203000c9500c0c1d0101010704040740010314545812041100c00c0c407814140f07800c1d05184c48945010b4038280c1c0320800d10b1001420401c05400c4140e01042640c401c4c4d40324010811044c03010801804004070001c2030000c0740d501000d0418004624120600d100708140c860010000a04078280d0140304045980001c0402080810b080c007030b40070349503040001c1d00d040c1d6a403006d0400581542c201d25400c0d5000070f104014070320b1859000d0b1808607454800c4850341d120101c08174084400101c002c02e00550a940c407800c2c2020307182790001d590030b40792200d0070611001a051070010301d4403034203106410b4540000d00702d604801d0020403d0700d1152083c0d5480110561840d1252403454217814 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 1000000000 1107 999998893 999998903
    0x1d0a0302031b060601230412052b12020306031c051b03040617070c06021b151308072f030d020105090607030903021204080706080a0506010e040207 65
    0x29400b65103003140011403161441b1184488400780c0b146030041e040303500b850135241c0e082100c0021031041c5820300398819a480c002000308900703c50b84070100e407408104201501c105400c1c01394051607222500600b143d16510031211000c1420071090300364400030390005000c82e5907140301c2a841c041d040c070100065240c949071031401400045109201c50b6007441300b0300030807092846223280b490720700d412401c11540c034038203c518140008031150303075000b15000c1c0b42c04045c90041080045845213560764440b00341c07401e66994550300d6500c000000c0716040e0410801a080012050600340510544803800400564100405162903d03001c1d010341160306085c204100342c04003140d2550000c60900740410400390604d01a4186800341c0f1401480030340104d00003889020000e800b0302140d11071b8840555540b507410441c410340d80104c3d410360100300200b490014500302030f80101202c038060 = true := by decide +kernel

theorem cover : BRFrame.Cov 999820143 1000000000 := by
  have h0 := BRFrame.cov_init 999820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 999820143 ≤ n) (h2 : n < 1000000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
