-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3798
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:42:29.077546+00:00
-- url     : https://prove2.me/submissions/b9b277e2-d5c1-4b2e-b123-e32a29db5456

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 682913669 ≤ n < 683093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 682914919 1250 682913669 682913687
    0xb040e0d0203040b0f04091e2a120b0303131503020913092102100f02041a0c190b011809050a060e0f01020d020405030708121c0f0e1507 60
    0x140041e0418042403140244402c0104201c1d41711024860809490301060000c4501400250f010188010503071800b10055000d03440c1c2d020145c1c2012206002604498941001001c221400b00f16074540d10020103001130f80001017203400503003102e441c0d40b08801e003031041c80564001c20050382c40c400350b0001e01500c60700803a600b00718090101d13031111030301c0700d800c43c007420384c2120840d4581d0380581c042c0344c808540850802c1c41581507000703041e450700c2102e07024225407050218000711401000140300c0c90ba40b20034030302a4201405400c0e541c80700004251420803113601c40202241d03000e04441c600703016800c920207050b90701900d403a501e0f9002680c10502100c900c00c8004200e80c12110311000440c036158801c0d0300c501072141c240c1d101041d0300d00703445e13003240d001d41c5030003110301d50105081c002800c00300403100241101d400203107804011015126001d014010019444500c0c1c03e01809480307080d6040180481e101c20340512000c40c00c483c0e040d444510061040000000080020b607580d4400e07203480c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 682916169 1250 682914919 682914943
    0x71d07020c0607060b1c02090612061603020c061008190b061318050f0f0a051c0302092e080105150304140604121106010b09060c010b130b040e 63
    0x18006640001c060007100d401240042da4610395541c80b206054032265004081005402d4125002d040da0b0b10401c0076075100609501e005800340070b5035012040b000915581c10046200c0e465050382c00c0b4040882c007a200300b001d00c9060340141c80c14040107820b555040803d40b803103c0300b990a00c0c1d1904078070450a825110003d400d00301c0d40d20109480303061200c1030381c902d1541854042800c0b20301035000e0440e00b94011045982c0c0c3e03c0409081400c5a0501c41c0051086084002c0c00d6040e206886150391559140c000ca680c21400c0300070b88131010300a80c1154240c020140407140c20480d4005400c16074060f10343c000f0f04d0015191610401240300f00406070603554010b0154005000400c82000541c1000f40b04680445d004034010300020303420442684141e204442151100349a14001020007048600c0e82403180c0c0103500502100d80800151208150165241074030740d80c00c030a01e41c0c050142c1d0b0710040c0d0043c0ca0740d80c0e04640e00341207800120b26075800382c40900c00c5e98102d49100d56129501e40203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 682917419 1250 682916169 682916173
    0x60302030c04291303020315041a0a0b0d03030903030506030a0804061b060f150e09100b01120c080924070507020a03170d0b0d110111030c030c071d0702 67
    0x818000440c50340d81d043c9080304054090000101d00c100c3c062415440703410081400c5588410400c110314003040b41c04000c2c201d40c0c501d80349605180d910f14207143c2c40010b180f9200803000f000a0f20510060707001c60340140005015002020141c00c000d8000e0500c44030640c0040e06040000310981030001e84c50314071690111800c0e01d051b01e040821070308420200c14242200320148007030000b00d07002e40104c2e2807100445500051f034421007a010002c203102507100c0714000081e03a0420001360000f05426400038031421021500302c00c0381004035020390907074a010640d60b03d0b181c04170301403585c0201c140d1b10030000d406c21600c541d030b03001210f00c007544090150b54146070400390029030440d104102500c1a1880600002e10321912669149200024090075031103203400802c02484100050140442041d41560250045402c0b40c6981b25919243c00c6c030207050206540e54514008030030021506560125425291034101c1005981d4413403c440c0715070001001103e040320310110004003120b001d5106600 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 682918669 1250 682917419 682917427
    0xc02090a0b030c01032d0b010905031b0d0f12080a0506011704110a03050d03051f08031219020a0e0901050907171e013c09050406020c0d0f09060302030c 67
    0xc01140a02001c3c41541128502040b03070404e003501407012416441e46d000000706102c265080010b02c08102540040c0c07082d4010f00b04982804003210054480300c0003074542480b003600b54205004806c1d500c1d100100010f010070072948031584d005443c2405040104024003141e140c000044511617682d40241d60f141303101c0c002040c001000004c650916000c0a003502031801e6694495a0401c0307104000a008282c4070420804d6900ccd00095070241c0a0800300020b80190801e034039140d490140b206900c2004400b01c0220b03074910074000318042010401002503558500d100c9009250b00b69a4850502600b41076001081e030b0f01c0e00d0307102244144010b40d85c81c0b11680100e00c00480c024005058885032000031609602c1050381440154083d1403000c0c3c030b68400c0d400c8001e9a8205004513104081102c0310003000d414056003110b0b501c4c088411014000c6800d48641c18202c00038400e40803840f006100d03d402d440720403500401c1055800707055407200c8545640e17640d401d50036413008035075050b20300000300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 682919919 1250 682918669 682918693
    0x1a0f0a060815100f03050a1109010b09041509020f0d0b0603060f0d080415110d0f090b0703140301060206040215031012060f0e0304051c0c2601020304030c02090a0b03 73
    0x1540d82c43c3d01655000400c00800c1ea20200380860000e01c0d00103440982022400b4402d100740c08042c503020110546440d01c40f51f142492000c582d01910003403520403925075021b900b0000744d4142c1c1002400d030b4044219900e5500c140340701040e80c4102a00000d841c20f00010200300d00d4040b050300e00c0f0356006004244050507290400c05019503900b800c898000d81480b004c107154600c8900c0b01c24120960f16450951101d81148901d821007041c0c60408200890109464103039101c1680421600f01d902100d072600106d1a06035128203000700c520740b180e5004000055500e5002590310b00460081e220904000600f030a6542c0f24442201e0700e003c00b003a402c0d4200409414404400780703140c050100082c1217103c6176141c0081d2101c0c00e00848a6034030104041c4034070303d4120300d15a02c142a003110242200d4841d511608004c00c1d07841107c9180b11180c91083c00b8900741d12001800b500103078000c46da40d240c07a18010b4048030300080c0030b9000395403150000b44211103a04c0360900e09407005008002c400409 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 682921169 1250 682919919 682919953
    0x15040504020102030f0316030615090b0319020d0501030b01050109141e0607050601050910030c09020d020c0f2506020606040908091503090d05030c030a090f1a0f0a0608 74
    0xa4800c0381140300420940e0101721450010f54001e0000c005078240303600c0c00380001026a0215000010040c0c45000c0f021043c40e0404c00401c100c0b00c03001101030b12551192040c141c0f40c04c46d0780180d05441c1c0001210707a180d00541c0d011a041e6486801003800c00e90300c481c011104000e13180111100c66515080c401010b00d07103402074441c01500c00000390b00d05100399020032803680104c2822687c40d8004070041c4070b14a0486034566204032011481c801c418903603200c1d05d0b00345801d84030b184900f43d0b0025504240c401150101c0d807040e913000c0d040340c10402e54091441e070740700381701c000c1001c5142080c4e489801403402e450424040b10401e40c010455510f4020801c401400403070070880304c0c000304020200241d292030740d102601221800101d0380300d142088009050a500000c40700c01c0020400c20403000032447d0054a80151b092080000e0300380352443c052001d9002c0d9080588640312180c1a041c4940c000081e140c461951010035903d00d0f155050800c05559040c05000d260307400c210702c00e034405001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 682922419 1250 682921169 682921171
    0x7091104090e03070203070605090d1e0c1e0b18010302090a090f1a0a030f030c14030f030618060604091104050901090c11060f040303020c0c12010b0117150405 70
    0x10040116152959900540c0101c0d42a15058080c5403c003003103110a5203070038418003000b004207007081450060382c1000102a444503810050911f15007106403100e81c0c000200d10758003e64084002408142c5071581e0b50050031240c00e200c01241044240801e0001d12501a141c0740c0325030440080480c1c4030340f40150702070f4103d10b07100d130f0700888a8440007586e040240594034503403550760030001e4065207a14050f102c614000005030700442d000041000014150808440c400e071301481c10201818031b51510300a50b6100c00844a80d5100210b503154032880e4007801140144400c481c85612140c401c03010801910085540340e501c00c1c02400100860b00e4103802c1500c0c80386080740c00902d055200e8001a01c120000e03006407520305d580c4c0707800d01121b5401540f8402c0d902c000e076000b031001e4508908429549500200020704058003c10001c404600810a000480f10010000e91030a04144081402482c1500e482ca000540c820307100c42c0c0190401180c14000c203030b010001d94003036482400744005040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 682923669 1250 682922419 682922441
    0x31c02070e0c0d06060504060906050403020f0f060f0d06181e1d010905010b09061e0f0604150e0a1508130f020604031505010e070203031501030b0d0b090d0906020709 73
    0xb000c20440300020840d2160002800144c1c691075169818108010200e041641200301072200421050016030788410302070440603000c0b5454480603000740040348031801480024240c2c004041415049821581c2001050f41e000c903085683c0d41c100069580c3c141d40c1403044d0308894101c00400400c0e00f40c0540c01944865040c1000b04001500000c1d030942107500d16038058907070341d41d1007400c40c01034940685100c1d04018210741c0c41500300c0154440e20449914446481e00c03a4501d81c03a1820507480d11000d440c0200403806404442850030070b0094511642c00a0040c8103081851001c038440c401d10101b8240c0b0a20b55481c00c280e6aa0804000245507408109480580301e2450729401039507a140200702030351090341e000790303001d0000040348141e40040c1c000501e074003085c004004420740d000003681d41c0550006c2c03951140c0c0c6010b6005074003c01000c01c201d5001a444028841030089a4840e1030190042c84100ca65180b020710342180c02100c1d0b80110001a0018101000810600d400900c1512 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 682924919 1250 682923669 682923691
    0x909030e062d040b070c091107050319030908030a0b03060f090d080c0d021303060b0d32030301120c050406050109062307060c030f140c0c0a0b0705030402031c02070e 73
    0x341d111343c2d4241090700086070407550350401d40801e100a62982c003400c01103c0211404604183c000e5489984078050802c0312098064102c05209056201350881030925030007482056590900c600040c0c00717400c9140d1f45900900c0340e1408100c4c0c000740001550f10414400300584652501500110b07004c1034040d045401d100014400c50442980920042044079080c840b0440820310303600d4000252016114010300c202c00011080e004a100d98580c3c0c605040c4500c0c05602e29500003441c0c010380c9007030041c0c900e00c40c4000b0001003500d00c4041400a82ca601410700c94074503c0d40c480c00c03c010380c0e42c2030040c1e134005098060200312490040381510301c04040040904100b1050002401c0d15422404085d9025038071394003410301d096010701c10081041e41e2482e041c05074202c101003450541901603c0110003500000d2420038444003480b1880d409070b0701145448242c100a840100035400581d400c1e4424080c0e1411494880541b120600d0481b0b0f01380c01400c09285003a040c0e502020005050342035034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 682926169 1250 682924919 682924927
    0x61602011101182f0d0f060e0c010e220507021e061819021c1707060c09030f0b1003051c03050a0e03091203090a0909030e062d 56
    0x481001e002d001600605100103040310020b07810803010480189400030600400700706911a040c0c030481c5426420740c802e8412156005171464080040c28490318040d00c403e14001200c1807000b0b02140c00c000c0d140d000d81e46c480e42e210150081180548202014080c0c0d50150ba240200c82c28a03900101d500c0301320390054072058000046401d80420181068002c1500840304016581c07a1070140f01da41100208010001341804c0309400b202d218000c0c0c8041d00c66003244c0340c0c001c100c078003c245003a5907070340c000c4180345030024400b05848241c02c580c80440754a4101a1540307101e034400c054010440c0d03040103202c02481ca00c0c1e102e03003103040d2000d4038031001e42030940e0000c404070f0410003d409001c42120440138850708084e00c01070840d00068080c1407900e003031250750480c1c0c580010030340d1032080040355241d00309942c002c0c2d41071030351082c8001d00780c009803103440c000340d40300b169403219a0803030190311400940d460050812800344070300380025146a0306ca4840e49003225440480c85032013800c200030540b030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 682927419 1250 682926169 682926197
    0x81608103321031206050108130c150e040e0c091b0d0203041b0905150105030a06050d0302031e09090f0402040b03010e010c1d010f35070f0c0206160201 67
    0x28098104140801c0b40c100d4001001056800000301411030080c11040000c00d09020000303140d104050640c0042c0c4450744121800e00c08a8170540004155000c5112100c1c6041d08001d000301e024409814401c82c60003617060b0403468049216991980300810900c59984e88000da4500b049407040733141c2811800340460041004e15200550240b4007602140e420403205400c060713960305d035a4000c003030403900b848103000284801200328001e040d82400c24070749075a00c0321000e500514150780481d5200c4d00d0350081d481415004001841041700e00301050800203a0483c2070301d240d100c0c40320444d030406400c1c8002440881701c9041141c1180c070090020424080c4400040e095400d45040001140d654418242e0225003025006014452443c6000e02421100300081d0064148a84400a00450781c031344e44500e00b040000c080c0300c4812040780a02d4681c3c4c00312000304c1100b003240c4810104d100083c1001200b8010801d0302110f07680200580c0c03034072948403174510800c09426030480c14401d860f882e00030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 682928669 1250 682927419 682927439
    0xd171b0703150f150b0a020109050d2012070807020301140403120b030f0d030506180705070c0509090718090c0b0901090b0304030c0f0201090816081033 67
    0x80d4060a0041e440021440a41c0c08840e60b08122290052520b00d11851306105900441c040355415003080361112a503c50a0303025000302c3c10000c220f406040400100320b5000f40c8070380701d0048200900e00e0890040095642d0350140b104902620350020702c1000c0010304840c0081040520140003c1010207401c11104548413060310201d0101d010105c4c07004414504e407041301005081280200540c07411102d00c1a01d038581c0c00900320425460714000f80e556100c0904a034800c8455060a81252429100040c01030304598421122061a9070740018a89008500d86008440210280007051310704031200307100c01c00401c01c18652035282d45c0180c004c20b141c1e0307081d680144000031105580c1c0c7c08650004040c400c0a4002c03400c0e201c07080c401e0001103644403040800c0a50311416882602c00c0700d00060b101c10903150b000403120b119111140da40c0004010b1001c00312104c9201f11403954681006140590b64004103a5510421009207001c0e00e40501d100f84480700c0c13018091f0618136031503001d02d00c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 682929919 1250 682928669 682928683
    0x1706010e041b0e15011d130b1f0e0117010b0306130e0708030c060c1204171e0a08100501050d0f0207140d0801050d0c03020d141902030c0d171b 63
    0x15101d070680360a044c82c2c07544c0088024480c00301d600b002da00b00c04010b00005041c503151244203006941c1e01c1c0750210040c1c54141140c07649503c41c103980710084d452242d00504000344e0045050000d03003040c0f410721101241c428401e040c1c038013107070301241150740b404240201110302140300c448881d00c654020401c48414420500a042d51502541e60340000c42c0c0c181c1d00c0c10002410581450741c0c02c01907901c84200800003a5000341c0e2017014004c0c0c0310144481058203024410300c2c100c00b4840d018040c0c0f81e91001e00004d190894064444180903a1002241d082030f00140c46142e000c202d003005034400c00c20b401d500c04035600300c0400005007000031a807100d02082114240b64440355201e58034131010b590300700a04030b006000c11508690600c034140d440040007a00d03844024090b1007403030001070402548080160b4901d802204a4040c41045251444005c0100e48140e00038080c02c2c0d00450b050501c81143e40c803440d0810009401d0040b180000042a0700001046808020424000382c1d140b806001c14 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 682931169 1250 682929919 682929931
    0x5070f210903020315090c1e040606120c0c033504030305040c090903020706050f070b150f0d0c0e090a060c08160c15020f040504020409061706010e041b0e 68
    0x521007490035441418504203580f1407089020040c1000c101e10b072080007407a415424400d4813100d01c010143d00b45420f070400602c0c111988103042ca0b00c0801c0250b4403256818082c3c01d1003500340702040240c0c10a60f00f20344401405000039070102500c0442c00503144043c101c00007404c155018543c909008034035194420748046000075100c209000a010306000c030348000d8a080e41c400c000d01075207980c01a40e02d8003c0d120742024403101150100050042c03200b40c0e0315071a0002c515801600c2e00381e800300e5000c00001c080c684241040000100300e4203040607a83c0c102d60303000c4444540d180c202403d802101000801c40b00c500d2254202c0540050110b014482100c0c0c4c0580b0351848074204200381c1c2c0c1504540c0c5040c202000300b0303035044a02040a4101224042400c40710042ea034664469aa443da0310030750b04010340050000500260702e0b60b0540c000030454003414203459010003030b00500768071444284600d00c4040c00d550041804541400100414050b80c440002440707035862406601050088900d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 682932419 1250 682931169 682931177
    0x203100207050708060f010302101101050a0e010c03021e0c1903080405070b03060306070e0103020f07030908010b0d0507030b0c19030b03151b090d0803010b07061b05070f21 76
    0x5801e0030070504025850243c00c50501408241c40d0200f02011614814880640b02d0414004c0c05101c00b07018022406900e10050000d00180c50440382c04005030172a405401425803030004180d460302c0c40391003561641e44900c00a40924403011301c2184c4284c00000400505000b4032a90761008000c010070f421250344207848140300c61829044c0942400100d92100300340700001c004200055401240007540501c0d5402d150300e0b1007140c500120028083c6101d08003405c81d0000320a4141034001480c6001c46024000030300000c0340b25001d100c600340d040200104664000c0c41d080c0005030340d8850695100811040c4a82040d2216080d44550103044100101003543c681855040c0c0c1000c0c00715040b40d100b40080d1543c00d0034042746000c0350849201043e040d81c1004121102c4c195a0150340352502038200d602280c59507140c00d1411041c1e80541011140306e454248891400c070024141002d94144a407103903410a200d0781c48180e0613044101d41110301101080104c01c00380d00351000c4044079201561 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 682933669 1250 682932419 682932427
    0x1309020a1b172206020606012001060513091104060305120a031410151119051603080c060a1103160c0c03050601050f010c020307171203010e073b0d02031002 69
    0xf090808903141d002201103401400c100000307660001c103101020104083d204c140e44e100001024010001034200341e9209611101c0b40c44039401b40e4100703900103030040199a03084003459040004565107132000074180c2c0c0001d500040f400d20078001400c07405003181400f1804846210701000d161004842402c10702c4802d07003040c0b011600c030960804228070203041c600e401c5c1e001c00a10036500c0300362040e5400343c0d0384200400001c2080611210b01881e8003001880ea6064036440c007207010340c10285441c2401c0c40f4010004500c0c0b01c684c015580700c0141401e40341d245444024600c00000034460300c40b000c7c459400021030004900400500085020b1009003100354100350820a40788801d525007410891000170a10141c0e40c04140705080b200c0070840c05104c04101d40034a4100868207e040f02c0023000440005440da485413549e620802d2103640e18032000b40d0300746046100e0b9030075403204504900d2090b408d55100504c00c0e00300803030a1004000348064101503000030702e80105111081c2c40c1075000700e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 682934919 1250 682933669 682933717
    0x10f09030e06130e181506031203100918140a0201030b01140d230405010e0c060a3c05121e040f060f09081309020a1b17 53
    0x815501e800c810115030706031911a040410b10010503143c000c0c581319a40382c101184810043c0d001054851341000103a40041c02100d00320f50813005c0c2201c542d4040d004011051584801090407a48034a03000b01040340010f040c090524010000c00c1c07044144000800e07038003c041245074004561070f0f9840d40c018202c60303846100040595185800c5141800465410390400100c190241ca0101840307507400601118800e406144074280d0459034407103401d04d131082c4000e206041d04601c200d0261007040720281f0f076400040c80010303c1900b8040c00080c068056104030300c12026548038242d1020701092510341107219074260400b0b00040706001103500007812803188034050300b0066004118a00b1103100d0a01044038080070440100300600724114501ea000401445074000410700e0064030702044114441c0ca088011540036250f4030303010810312000050700c900c16008440d1000d1007641c6050003e00c07080103400070384540c5417045522144081014041c180d0080c0500f0240c480c500192628851503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 682936169 1250 682934919 682934927
    0x150d0c02010e0c0d110310090813060c0b0609070908030f1309140c030c0c0a0b060102060f1b0c0f0d080403110a0201020304060e1c060f0e150c0a11010f0903 69
    0x1400c011801d500b040190f10055999015094102500144250400c1d1030301000070341803402c02403e2103401e915184c004c0d014065501e0151240c11103409200f06070303607102d403000d44918510900040c900d101000c006051818030b03c5070203402050074140000401d8440825070f00390f421605120000c1203003c500448003080b03c100720f200502003040100050b0300c81801c504014000102062841d0b203000020800700880682252880c072080f01c242c8119030b01610b0a6014648e00f5070f606401807140802194078105408031003409400401e10908021300314032400fa070755400c03180081d1018000d00c01440c541200610030f110341c11080c5e0345e400195150525000d0009540301c44000780c3c1e50700c13100112005036000412102031340d0141c18031540d42c3e884000010040320042040302c023544030b1049000104585034000b040c0030342050700148a140d80d41d010f10384d41c400454084885007180c1c100410b02e00403500009151030082c038541900b803a079801c50f0f5682561241000d02c40c0b5195070f010300345e080c50741c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 682937419 1250 682936169 682936181
    0x506091b010c08030f060d06060603050f0a230a0f0204030f0b0c0a0503010b0d0e030d090c09092a030209100905071b060b0604050a2c090318150d0c0201 67
    0x1090800b00c4541c405601d500c1000e0000074070301c240c44100e501c04502070383d80388180c0c010400d52000046c060319840b010006c1c0030380000d80d4a08040c040c1c5070040742d41003666010b04e0035400c69181040d4407111081028811118024100c04000b990b40c1500c42c400080d0360000f440074500070084200c4c40e02031841e1409075558010501c28070301c8001d02110005583c08021070341101c0c20742078060f40780c2c0d507103008590007001c0850a07120707144400100c1001c000004d411110000340102c1d001e810031552075800100752181c9090042101c0c07007480d00b105480004910415284100951900f0700584030740c0406d18050060301c00e00b401e8028840104840d810501036203511003218a030540a414982c80041140c0038500b5009003420784520740b04210b9241c600c150303401010001c00b44007000c6d998542c43c0706030100440f0108032201a4a4007102c02242c1c4910984c01040f00d0745c0251315000c0d0038002027815814410300113600448040e002c81d600240e0300060518100c081d01c1c00504541d05e004043d0840714 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 682938669 1250 682937419 682937473
    0x80912030c060f0405030d0207050c01080109150b031819060b03150103020603072c0111010203070801050d05070308270103060f15110a0f12090b190c050609 69
    0x100810400c03080703034004140190031262440741c80a55403102d160441c1580a0051034055451001c01c0c2071041c024001107482e4407040a03282c81e200c60b43c0300c6403910240e56001021f484111071440c1c00300016a50800110781c055140650035452180303402c5582c4c10b000ca000e0141e240c040303e030302c49a4180002441100c007001802c600511710a00c0c5041c0080161405100c0a07100f0000480020381c3e00c3e015003602d00100c000c42d0400b0105491303008003039101c1081801c1e220f00040d811020b0340710801051003207034025030b040c1e1240700c0280e18242c100000510b03030203030844a90061080000010b001e82c2c014001144050700301c61144001e08090032592555102464101800d22504012000b48810b28500381c1c1d155900311402150000010764405c10701c800003c40d58420f0070301c3ca8050240c0c01c80588520b5200e01034410340c2641507041101d103c2b055009680e00e20000b0080181468041d11310440780c1c05c0581080ba020101c2d5494141c2001c0342112002d200e90809640740324215905100662100c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 682939919 1250 682938669 682938673
    0x11030d05011d0105100f0203070b010e011403062703040b1207030e0c100f02030720030d050a091e0b0a030902091e060d060b09040c060201050105061602010309030516080912 76
    0x50b150200041d005d100040702d11051280e007461034038003240700303001301d5002c00d0f0440c048a400d540d4990a00480c40002d20400120030114550021989400b05001d4020004400c7c41038001c00000e6041c1d010000e40f9800e1901803104010010b0600c02a80140640943c008280400c41c5040b1f01c0250540b550314552800c1c68100d1000d03a03e50b030703449050045000c0d40c180b40000c0c0303000800205920350301c5034184c01b0701008020150101c80c6d80d014101c041c0900c0301134060b00c10040403208242c0b2540a010303c0e280100390000307002c2c070142001c25601d500400390014034412240d41c1c0c2c0e60726000c42c1c0c003002d160320000c2d0700c4104560071350420768402c6070131031980b40340007810b02d40000c003400d010503003c6c05540c810f01c44c54038030701d082c802c1a8000a05600c00140b1445032828a1f140c1040e0094991248101550030f2100018251a2240031769110384880f080b4030991340507540c0110020070481c1011428081c2c20311203016903800c0107d60710b44091040c001281c1c0c4613244020010f00708040e40e0b031014a9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 682941169 1250 682939919 682939921
    0x1060c02060711130e061e010f0608091e010b0301060b0406020a032001140a0b10050d09061b0c03020708030a05040519090c0903030e0306010b1911030d05011d 70
    0x507155070046558098000346000c103a03c080c180080e40300e525009120081a003450404105c41c0008981c46020700f46c40351000ca001c07290184640a101c03c00d124000c1c04511400e008c011645c02555281e03444107d690a0702d49014001e48410210000c400205001c3c0c0c1d561201c5081900302403049001404401314694100740c0ba188000b03554808200d0001c0400549441400c408210b1140e0243d060840710000e00c01e00c000c0040740c0d03402d81e03403c8600f00816414440344800905246003203180c0b420582e65100e282032405110030700038000114045a41690f03420503c1d00c094140b212814082540e84e070340f542c441c5041e040091034941280c0290066400411000c01d40c241c01c442100c3c00c4500c10360f0703075003410485804030301c00f1281d40c4e81c07107801c1c031a060a903c0030309541d220f100d01056920075151111070b04161070500d99950401d005441800104004014100b0401302c0b0a00030100c0d42e1420106051451075424296000444d90030b00c042c1e103500051150004001413900c180c0e107034612308005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 682942419 1250 682941169 682941173
    0x40905091009080904020c010e0106080a021806010c06091a09071716061107031b03140102180405090a0c0e0a110304050309091b070b101e090c05070c0e0f01060c 71
    0x44c440d620b14544100d03400100c14003000d200790030a01900a0340c030020050b0700c1d42c41000c1501c9400da401c00300d2140c1010000300403620034200601e8001d030010380d5151a1003034140d55245c000d0420b4181640e05078800310303040b8449043d5209161107070080b4009000c2c0c00c1c0c60202144113131906d0903123032651a0030007410103d010904104c1d0104541403840c1082c60942400742c590706140c000d4102400d15030b420307180380c2010b41d00112140c048a1280d40280c1e00340d00e044414900300e0290b410f007060549c0710140e0040803850315801954000c0010300503299410400e81e41c041450039990b02645680a0b58010041c0d25401c85c0314140640340442032140c61403801d55100c0c2d8880c46800c09062040c8840b00c00300b0900c0000d001ea51041d010f0b8208059070351314060810040034101100c004054141c006404521808507182c40e61000450000c62685281490b04402c00303020f407042400300300101400f51601081490b1210700007001c040802c4000c41c01d050381411030104050b0000404c0c80707401000000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 682943669 1250 682942419 682942433
    0x7020109112115070e010503070c02040e10180606080607170903040902070503090405090c06040302060f0c0a030f170f0115090b1c180c0623040905091009 68
    0x81944030407035031004020400c40c0388080800c2050044200792080c1d50803e0320440c09940b5540c06040c00381c4030003c0d0130080703000440f55480700705c90742c800181c0000081c10060034160083e0384024503810a98402500480d20b03070301142e91154460080a070f08403100d80c2402528440c03403014000640c0580b030700d80780c9484086c14140070346008035a20410040000c00464087c4256070141c504072106540d695010306001c0e6594202500c0c1d18070552806000c5681d40030005902030301500e0151117a0b00305442d41d0204000c0341c01042095030440c10411800145040c180141b100680c86030b1036410340e220084000400704842c150b00c003031510003103c003406100020030100d5411166101502e503110b031400da81c12914500d09601916840c0f00204504200783c05030682c55071586d0000c01d007002001010f104030300c402c903c00c0101412000e4020f0080c40120b1281c00255800d400300032501d00b10250744090348403503034426407100004036516000c1c420761000500c554103c1c018040000d00c281200c50300c80c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 682944919 1250 682943669 682943693
    0x130204260c010f12060b09090a15060e03010902030102130e1b090405060d02030d03020d11071703091203010810140609060f0a0305060f16050408150a06030f11010807020109 76
    0x503060002000f00950300d64483ca40107000310314049418460699a2184980e054101e00c0540d480b44030648002411100d06200d02440801c800c4090b100700c9203005401c1d90515900c028554041d521240844050b8400b4002800c134095000c030410281d51034800d80507451200a03010102c94401101c140000341003203000d4982c00001120006829181e00001030402e0313006d108025058010751030078041c2107409d07a01812211030070b0b84081c00b0302a02104010300030320413280000e21081d4698201c031040030901c000355500c08134074412a40c5040b1121080022038209a024201683c0100212650b00010340074850b90001e002d0f0300300205081400c000b400b5900011311950055426035407050880d83d60b400a80025a041403e40c0c040e410710f900b0040c82e0510841e000e4940e01c08001c50070032410312403030482d4201c0d1081d001820b0385412511903c08403603405000d40a20301e0f2103000100c0801c0800130900c01952251820000555510001402d404c0e0028600c00542e4540700366030010801e503c1c541 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 682946169 1250 682944919 682944943
    0x1006050907081b1204231f092a060215071d041e090606050a0b070312020f0d1b080c0702092502070e0f012601090213020426 55
    0x480001411015001c0a500903884d588003411500f4050105010304109110100c55000340544885002c07920602d03034801c4000f0345440c62000b104e004821513010b5900c0f1060042c03040e0b01141c5d804049002020384048511080c03442014801d0b000c00c5620b0301044844020709021100403464640010040d1a15680700e548100300180700079450703040c2d61980c0c01080e44440321a60398030020f4041e11210010a4000000c681d21031414802207031925201c140442104c0d500900e540c03506000e80d90494140030100701103516541c003840120302c1c0040b003001811082c03140100024010500e91400e0850944d40c060080610500000b40255042d66504417020b441e0150ba0349215030301c1d081068441c4096141c152050312489800c1c0340d0040c1c0d804520343e011500b000d8814152510f41d15806c0305113200078420f142030b000302142030a00000d9607103440c040b2940c40c1800001c2844054003c22015a40014030001156002034180f20900c1c8501c0754004041200181151b000c00c085c07001d59807544403803d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 682947419 1250 682946169 682946191
    0xc080606070302070f1409010f0302060a1b050601091a0a031e05070b04090915110304020906060c15010504062106110d0f0902130e1c1709100605090708 67
    0x14881454000c0013004000d00c1260402c0b1030595a072004403641109008034070388524107000c000208651458000c00c2920380041c40c00d071902e83c80010689908003d0340304540c2c002204400c20000c680140034042c0285550800499008420403007560001c13003030310f0200d1260140110510115041300c00141c540c0c050781188116201050400910b05030b00e0fa80000c0c214200002c01213803481c05a007100003218411411802d0854800080398280e805104038009030105c1480000c1c00340c6050341078240c1021000e0455407800400e04003040c140108458090380d06185040104120f090038807400008100a02010102000720342c0148031031b12410602030034071a00ea040ca0980c88000710100c411000d82c0715020881d0010002400c0080e08015600340d105400c20840c0c40d5a420050260007030508201000d00341c820038041c807103c00d0400e2240b4540420418542c20b83c19000e500c280c640c02502c00800401c2c000ca4000d00000549a00350446c5010b0304081082c000c0154021019503044030140311 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 682948669 1250 682947419 682947427
    0x70309030c08181903050111040e0f130b090f0606030c090c0901020f070905010f1d07080405101d0d03060e010611150103080307090b0408030405060d02160c06020d030c080606 77
    0x14410780f08601c070710303561540444900380090840f40c183d4601c100300ca125000a121711101d40c420707824140030f41d215010004080b000020b548d44c1c6820b0310294800703544d058030000350302035031101d828014040b036005445501100140000180410038039611200440050039143d801c04081007242201404511a03040081101141ea84c024000d151108040404403850075030303600840009800280f09810280d072403000045041304200282107003a00064190740c2c00c40d101c0358401c407100b0800800c252104e001da00e130621010700c414001c52021102940039180c0f25999154940d08042c03000d030760103041c107240480400c0080c1e0f82a0031941198001d09100c126100d9800c80941443d0380b072000c032905441020f001004000807580558040c0050340d44a62031a600d03800341d5411481203010f40103d580c014801085103203010300080400c45401c100150410101745140b00d001070301050121540d0002c10030610030190b04000c0c850780d4076214982803000c0000280e0140084402500560040100107 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 682949919 1250 682948669 682948687
    0x14101d06040b06070c06030e1b090a2a09090b030a03180e0106090e0711480913200105071505010503070506040312081008071805070309030c08 63
    0x103072104003074101c041e1600e6540c100c40e1a022030f0179621402880d0110303107044440706031030b00002028440604c3c0c0e480c0c0c02c009409120200441d10300c0003005511f1007621390380b1030340901c4440c0c90303103034002d4645440c1b68000c1c4031301d6000038201104a0300800011481d10006801d00d0307400080742c0d02c8494150134030808c01c40d410560038003503400c07039080340e40e40000b01000003860603480000001100d201e03c1115401392501482105c5601903c4003490b46603000341c6106c1b2600c440d450946980c800c00d28581114102d205820a00e050307201c10f1000c0c01040d8010202d007080c14144001c0e03a1040c50104401d80c3d2440a17690050400741a0240e4480110142901155039000300105e520b5603400444034015100301c10000c0010b4142401214020f006580e80050b81e418804c0c02d4609499010b02d810444110300c6200712030b012001003640d018005119800a91140140f000001074080c2c408148500010340f10070000b558401341511003050318200e06140800d50000618044072303070103c100ca17a254a05 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 682951169 1250 682949919 682949921
    0x304060c050c16061b03140c030c01090f060506012c0105071401060315020408060a02070c0b210606040315050403260a06062d05130914101d0604 64
    0x1640c1904000e03c20081000c001c604215207500c100e5241e540d03040700c9000601000c221001a0360300c010003003a2080d2820a2031030405000d810752a0b880c4080301d06000710080383c5425a41d40040954900904441c3d003030520500c1d02405900100a0900911035101d8560b200340c108840ca100039640910151041280d81c45801184c911540021001c2d44d401c540b100381600034906403104a401780d00680d41600f07500c0d8540240c9044404800103000c4d59030302c01c140f0300e01039404450125030000d20b03118042190500da00152001c07941c0305074074002d0100c2840306140c2011014101c1c501c80c00003030000f000011500001030701002180400404c103071715240740640c0c1111240c09025190b110a00540310054106c0c502c040c4648c0c0c104005002d404d649140c2691900840d84211045244002100e094814141c3e01441c00c40c10520b0481d140500c482c82d44840d408154102c3d04920362201c09015030081004e4400b03420001c0500b001e098503107446505c0b541c0e0200b40c035600c0c40c008100c400081071980c41e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 682952419 1250 682951169 682951177
    0x30a080907090e060f1b12040c0302060a020607030e010612060c12050a0c080a180f1712010302030c12030d150506040e1e06091321031b02030304080304060c05 70
    0x4180b4180241101110400d45810048840e0740304c540c03903200041d842060039141104682141c08205103012614004c416240500800a0380e01c140102c20000060311501d008103080c0140d0380c040c01150a211000605844100f16000030381da040c45014841c8c5040e444041d21180d0380310200041540b01d15805442c00c05510f94400d0b401707880c2c9000c00c105002e003074201c0711030600a50baa508684d500d5a1f128000c490182c58491202c040f00f00c0f8400010342d5610090401c140030b04030645911284412844c4a580040c081e80066440f0500400450a04120b911f282601c119104801c1d085844507090750780c01400300141480d62500c00f60240a0041a610800b420300a4030140d0703038a0f101c188900a0340401d036201c0721006072990300c0d203004880c0c00030304a0140703800800e8128035071102080350000d10020b100035a14034900300800c0041d0003401591480132421918049a00809003280d8000200075100180139500308208020016100e0300850760700075070008000500e05c191600031100750203 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 682953669 1250 682952419 682952429
    0x30b0f030111040510080c0403030c0813030501060314030711010516050303011d0609010b0a03020a091e051005040602280203030406170c0a0c1101031503030c0512040305030a080907 80
    0x4a81800302c210503581d1002001074440aa49207111080c44480460f00301e00115600302d03101d04140010b00000e403141180d00007032402031071400e04000704d000c01c48020309050342c07040311180e545620800820050b061440001c21500010b5810721381c25844100e880860803542c039040010000c1d141c1d60071300322050580e0116800400302e035165a150000c4428821041d03180c080342418410000782203243c00e5002c1c60590ba5084881400d01d0510482138003c1e4008010342c9041c032002031004258240324040751010f125000055444542c034007010b00c00406944030070700d820403c0820040c04450380000341c0c040744800008807805a6082034080b114001941e000081d40350000081c00a05254010444180d04444894403565074484c1c4169038003a02c06c40c0c0b00b107008214402501000704c3d4a0700462059000e040c10041040d4120351000e8028203056002100407410103455041449000c00907220030321030040d4014541819602c0d226a00d0058141d04400c000440002604400c1c0902c00702c40100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 682954919 1250 682953669 682953671
    0x30c021203120a05060d03090902090109090905010912020d0f14040801060b03070306050d11120705040f09030e030d0e1509031c0e010e01120f0908160209010b03040b07030b0f0301 79
    0x392504248a4a16043c2c805043e074a0804011400a10b00540340c0019181e05d606c41c0c2c020240b502c09040065003247c4002c60602182480005400c0200d0280034103480c03055000190508040c50440c0f980700481400004640c042d03600d0b02d04054204c0c8138a10390780400c0c2400c4490510107010001180701c1d80d0885840f550030b01400040014101004d14020111074809020168540d0103203c0d1a550f0720702c01900115410003d80942d080041c0d180c0c0f4001c0c00348081c0c0d07a00707546460109060300c0700b88010f540410b580704214014954000002246041c04070007a050103030420f44020054070030100c0b118031412030140c0c0241290800d20855a00504c040d0640c0c910030700030006080c018100f0040781011070150340b50b405e003561017580f003901c0010701611038003840c042c8040f4207001010a0401108416512103505001c40d41100151603d00c00507a40500c0006561051048a044c183c0c408083d103031046c02401700288009882691284280c900040d5400c00b82c4001600e02a0150044e5015 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 682956169 1250 682954919 682954927
    0x50a02030d0e0117070e060a0c021e0103240303030e190507060f05090307031103010204090212010f0501090608070815090f1b07080412020a0e0907051509010c030c021203 75
    0x10780042c000c010b62a4240c8a01c1800700710b031888500d65000c1210700c40000384840550101900d00b51024000c0d034041d41c41c200f40b007040344d54082200180d0082c900c1c011200084030224075580c1c54000e41c5424105c441c6140c130004144080700d883d001607400018117044c1c403407401d1701a00e102000121211081e24104003c40b0303030030b800e05c0307925040300f4081d600004501200b11680b55006001712100e0480140007048005e03d1500c80080f524070021035030f58103540070003001032040441d0000e002c640c0502c0341d0310102035142620381c41c0300ca0100c0e0f11070f07030610507090340030001513401400090f8040740ca802c210300c950395864454070307004003205c1c203482e0700c407007400d041c07007a100e42402080344aa80d1944900d010f0440761038928009010f00360000b880c60404200610603d03140d40700c07505400744060031007007400e40c950509810380c24003102c00302165400b50504010a14100c1980d0210902c5454180d1802010740700003002d00c5c1040c03402600340014100034504545405251048103c228400e89440d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 682957419 1250 682956169 682956193
    0x6140f0108100902030a2301060605090307061e0305130804060e0307080f0703021909061206061203090506092209060e03040509010e090f12030a050f061507050a0203 73
    0x121001c0c040c48115206071411607800000512075014543d4008008010b40d2000b5600c06500c07007404917486041514841c0b608903035040900860000d00495245c258841204106061910b401c0303500040801610060859600f82200c02800800f8858900410190303100040b06014030701c00e0100811f00d040000b800150264002071410b4034410803030035224000e07954072080342c1d5986501040c240d01e03048050100700521b050b44145114200c0303124560708003980c03541c1030400c464895100c084100c6141e08032400b00041882040b01802546940c40080c03019910001e041c8446402058020f420024002c2c0305540c440280407441c0404242164961640c5d0039480e011300446001102c29500700700007140e194401006a506450002d4201f9000d0703840c002c00c2c1411604c014000c0000b90013190380c0c48484000620000a5200c070003548103a490070200400411240020081240c07a01d002040c415655200d83c02150b2101c501c0b800340d9214107550424a0130300540f100c00039407510802c03507003c407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 682958669 1250 682957419 682957441
    0x10b180a0f05011b020a060509030106080a0803190c02121810110f0105010b03071b0807030503070909090201020a0215090910030201030b030a0302030a1b050f0106091b0207120614 79
    0x40e14801c2ea90f0001c0311804c000e10030341d440c400100c02503011801440c14410103100300094000440c1c0140049501707982c0e020024180300983c01d003030391a0b5038000304000e03c7c001c40100061107011400001c000840386440025242e808003c94202c441c1d2001503000c4002c6100d403000c0441540040590041c0d01c51108090921ba22640c01c0010354050964481034400b0306100f1503040b101d400c5085407441d81c5490040b160700480030030308501507000d40f80380000f084e00716019101c1544291540d0351b8a00302104041d1081c96654052044281400d28940050344e01007200d2a07041e41c107070783c070780c940d02c1c0710742d419408900070501c442d074005000c1010010b0740004c0078504400c0780d0003a00d0400001c80b11406254413403200e141301501603802081320503041407090050341c020700500c0c3d1016420001d1a070b603190030403000042030a020380d100c9070240442c090764800c0d000c220b24401d058600c481309215001c0e4980d4140d22514408485900ca600305000883e00f00d1503480d16142c420680f14942402000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 682959919 1250 682958669 682958699
    0x21060e0706030f0b06040302040504020307171006091e0507090503010929061e0d020d03050304030306151d03030f0406051c05040b0c0903010f0501081f02030f010b180a 74
    0x8070020342402580d28601e102c500c2451918480904598585421902800080d1101400403030b007600c40d054000420700c0c00503006910010803d0003914805002e881a1015942c4c40d401c00c4046034030b823b8000130450708a040c664808080494089650703075500c032040c1d8100040d80d10003505942040e54007010484d1282406030069520304280c2e1913990f0340f503048940810122841504060940801c0352000c815910101c40d440380180465404481da50210726424199042100070800110a0200b003641600481c0e02070007513500c0c050440c00d002d84006101c24600510480030010020403504561418001c1780c0040c03150181d00c503a242ea03210700c0207105034405440f0513856049001c224a41c2a1a07018041c05203400c10a0041540c440f0400310110790300413021a0307407540d0380d00e1803480d0056444c095240203020600241410075150007074920702690000d0050b4000e8810400c0212010080c242c2c54151102c4050f055140e512881c1d003001010703c1e04100590020101c8000161011511070392 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 682961169 1250 682959919 682959929
    0x3020a08030a08090727021905180d20010207030c1706090613030e0402120f16030e060f040305040905040b150102031305100909060f0503160e0121060e07 68
    0x3290159640c1c420103611815240102e45400001040d82030724040b0002d00e504000c06c402030f0041c17609030a0f40310300030701c21549000b030404070b000402d00810080130340340000c00720182036030b0b500b42e01031503541c3d0443c105080d51882c08403075806800344100c41e40b0800440018540c081038800c0c09a403505188146841c1e14550b140c090b119007000241001c101042c8035000b940600c0751034954070015074080d220345809203070054003d5400e0000c3c084080c40c11505038040c003100c04601410742000ca9529041411196502050509000e80401d011000003141d40c0d00c4005203a0041413074403985800c64240c449d1380d021000307050500091009001c01015550300800300c1d00030080030b401004005a80f24040d01c11400c0c01c3c01000c030300030405401e1180091040d42000d00e0700d00c010984800298007259100d0300450800340700002c0c1409907050400800414903d1030301c28003d000d20700074540c00d4040050140301141c2c02280d001d0030040031404408a05281e110f40c1c2070046005440105903194541e1080b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 682962419 1250 682961169 682961177
    0x7050609011508103b0115060509100c020d0305090a060813060f110f2205061b0109021c0b10140d050304030209090a0c050f130905010603020a08030a 66
    0x100410350410807894004503074250024006020003802088014084040c44241c5c4150b5114a0000e043c0540070180b82201590110088442401d648608442001106c01754002240302c0500c400c0b604102581c3e500b039030403201d101c4080100d039003c803201105842e00a401c4410000c0c0442011f82200c06401405403d40c0d0389491f02d99a0750044403540c0c019a010300904010601c00c10209250350040b202c44045040e001c5689904024520300d82d50259005d00c0383d4000209402d0000a10f00c0b0441200000d40320004140504107400035000d44144110b08124403e10708901030900345c2908008440ca03002040340034034001040e036041400081c07a1046030807980040000d480c05090203650300a844041d54080c10000c1d2003c00d002c040440c00340d0584161109000c0080169030b2480014410740700040a44100d541a141000e1011a0703030704450302c2804c0c542c039402ca5544448140d0450f8000b41d44010848144c40d0925030300410190304040d4100380c90140200315800000010304103034100e135403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 682963669 1250 682962419 682962431
    0x140d0c1106090108040f020409080c150a05042a0f0f03030e040e030d09020607051c1805010f2714010f0c02030703080307090f0905070906080f040204050a110705060901 74
    0x4108881e41c0300c0d0610300c40c00320b00b84601280110300340304200c1e0583c0d88040c00c00903554111f9141d0b110141c01c0f800360b418913070307000c64041f1005980f88201d440c0c00c100b46174424092401c10b40c0e00c0164200551a41d11000c000c5440b003240d0300c802c8a20010700a040b100d0103096401e4540c20840c2d84040180420380100e1201c2e0079640c0c0505280c4600e002ca141d01c235000c3d50030f203001011a4005803c400d1030a80e4881810f0042c1e4000c51002e21903070351481c00c080c54014401d01c5000000e0680c004122011241442c180030402a0fa600700106078030906144c5480e2440070a1480344d0045c19905424860307080c0312a0f0404151800801d4098003000001d8982d1030303c000c1402011103032551484130003034064114040800c00261150055500300301c4508101800940f2100c00010109180e4050307091280c856003440b0405401520440c050600e0346030401d103d01d044030301d41110780d0010b08020300a42e0384e10000f035202c001c540d00061445000841c001da843c541c0342003042c3d640740151030196180d441c00f8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 682964919 1250 682963669 682963703
    0x501060503040c03021509220b0a03081222150b04150b0304020411191e0807080408130602100e0303060907030c02070e0f07030c050412020d140d0c 65
    0x4015039100743d601c6508035125130300703507401c0c0000c1e00400c203220b034070100c401e001c983e01559a441e80184000b455402200344099044a01c2c0240d4030350701100c078000c6281320307001d00220302c501c0100e480322602e040030316205448000344002a0500d40759010510b03400d50f060fa030100302d10002d60362210801c0040900c4840c8140c0100310452b060102c184824203e60b99040103969001000344d80d00c0b40c001800041e030305a042040e03030310b01c1e4816050f00b00010440708001c60050b0f0000f48a1615651021500102280c0000702605103040038080d10103000e8001c0000c2c1c108800e003402c0703402803401b6030442c0c907a00340d0368200a0754803803500d25010086030400a110204450010550f4415400101010210380313071301c0070a40003003200340000400c5006111000c04c0d0701c440700f9102ca002d00c100d8001c40d0314a14140800a040780c590150350420444108400c11003d000d94001d94140e603011921911074400c00d01c0d08039801c1c0e035002d400c8040d41c043c820b04901c0300c9810030980c0496902400c0e001c00c0c010703420 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 682966169 1250 682964919 682964927
    0x142d13030206060a1809020a0f0e010320090402010804020f2106152d03030f0a030509060601020718060f060509150f0a110f010e031b0a08030601050c2e050106 70
    0x14010324a10800a48045145040e01d406c0840064009001017a00d991601d100d41c07007600341500105158041d9800410400c01c4e040d46001d240415030444c451118503240004c1c41e240000303000641001404404075040d5aa03002299041010003070458401040003c020b039803440b000c580c00c0315980620300004130000c8504045c0b0410003402001e8a0074102041f40c0080072011304a40400720309141202010584c504000500b100d10503004001c1c3c0301c050b01007004054500c010002c4000341c11000a001d103598000841c070081e500d8130142c480b103d1502e000c039040100350f41c0d400307400c1840e00c00301c2c00290035420034014900b59805a504070b120b00d081c801c100801d845100380350601c080c004c00c03601c110329104245048140356904103690714004460180390a68010041c9400c3d6074000242c007580301004013120300341c00301559001e0300f140da2450b15100f41ca404004c1550f070500c40001001969840284059022205c80c00c40350100d80702d48004400c1c0c01c40080e41558106460407001044031805 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 682967419 1250 682966169 682966189
    0x120201020f160f080613121404060302030402040506060909070e030a0f0b101a1903020d0f2f0706051003050f060106021204080d0c0203010605130915142d1303020606 73
    0xb2000814010341529038483c002c80084c10344142c1002200d1414602311109503000700003c01d031540c1d001d80c80341030074010802215030141c5441e104135010031200101c1e0326042d00d56503110a027802c011800d44000004207082c201e060400070603403900d0107201c2c8100300c0707002c1a803805400c04c02d0340c48900075200c0100703aa1490000380f4460340c010080c800288809030000c902c1e0030b91045842d01600785510701c144803090751803018076190415140c1041c084180504154040c4800ca01412500c501c401807a034401e040c4203c101c00343c005604c500000d0aa00b0840d140c0c1c0e0001e5a101c5c00320340c6000c502011b080d84908003070090074018010b103101482150b01031419103003a15000005003000c18a80b070b000f61042d080130441280c0554841c400000c084d81c40000c0510120317100c100100e4000698a40100d141c9900c0700120365452401f4044554001d220a48a40c40b441c0703000c008a13424600c42c2d02e8000c650340c4004401050451604200107601c00e01d01c0002110310039003c03203445032500400c10a18402c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 682968669 1250 682967419 682967431
    0x403150b061c0b0a0f032006040f05041113080601030b131a07091a09180f0103020603090f0d0c03030f0e0d141303050a030215060901120201020f160f0806 68
    0x248051684500032a6408543d402d6402061043c0303051352240030b003008402c59071003540c0306880f40725401c0010320300c020302080b0024102c603468a41401d121007a00000005d021b001d00680da240820108540d03c48205c031142c00b003483d0100c4d9000d41d103031440340d40e80009020454405000f407010600070221000901d10441c0c3c0060340c84c200c03a01100406610342c10007041d031f1003000f03118040010b07800891020464220094a5100d655a035044284600c0400b5078050060344107074001044402c020070000d49040d01d60480d80030390b8a494407d105840c0c20089e002010b05800340d200c1c0340004940051000311024480e850500079510b007441c583c412a110911143d42a4000490b16440c5600c11805044400c2c8609034003418800c500703400342501491178000b11140c4e032100400806068040040c003c842c221401d480c5503601d42013010410038801031250200e040346400c00e040c01c681c000d01c20f8401030180e40b411a11000200c007070040c9241500c0c407602040321103940c8003052294000c50850304c01c02c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 682969919 1250 682968669 682968697
    0x510060806040201030e011e061d160804021305100e0a02130e100305071409090303090c1c021e040c030b06031909021207030632041104020403150b06 66
    0x82d4841d00194090100c1d0398034403d00b03550390050008117010032001e80140e410851000140c484c14040180c035403150790010045002c60910400006051144068007510585d00c0c140016880d01d2010400381d900320415802e019051900b04000ca5420305100710442d000304003607007407070348070300c0d0b505402c074410030981a81c8540340810901002403400c08490301701a00c000d0440c0c5240c0e4a8036610b08000958010314540c8210010311a0b081c50844d10042d081602e140c061881c5007000311505584900d0306003003900814418414001c001b54106400401540250030100101c0c5000c402503100c540895a0f10320840c681700703034400c210f4482e200720b4004a0001c2e00c00d07869600c50a0070079054281c0c410007030760240d45507000301c00142ca4405559409044441c0103112650031803400c082034401c1c402040c03041139560902081a0708403604442201f19426020032880c1d12181001c005000741040e24581003400020000100003080010144040004800300000c0a003401046003600c640c0461030006 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 682971169 1250 682969919 682969921
    0x6180c060f1e0919140415180f0f0209040c020606010906050906390c2d04060b0a02070510090b0307111225020112020d020d090b040510060806 63
    0x1aa84106510305006500070195081c90400d200041c000070f4188068000f00c402414100000d015514204078081011078091180d0f000d4084000b0004419100c8d441c107610405c17610050298040e40000401d4004000c140045d10000030703407801035401141d0880c0224905032206a61500c0414182c0c003c034016500d4001c49464000112425000943c2e40d0360301c5003040141d41ca542145400c00c0219070f1056640b05462000c10180c81110007480c550000280c00c00c43d82c030001507554000380307103280c185640d40b01001610101f5103041c40c0c02014186030094178040c0003203480144e10b8068064400c3c3c640c00c4480b10381e01c903011300a9070194000d41c4c1010411849090000700400c5002d1a8040d0040ca4030b2070034108045e81941c0750400d5004d0076054020006208130004000e60803020b9041c0248680301c00400f916400207020b281510350f030300136650340400d130456001c0140c0c040301d60201c03070481e06110540b032508001d0390701201558100d4081c400d080030f445c03106905000d014100c1308124007030021 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 682972419 1250 682971169 682971187
    0x1002030901030e1507080f0912031b1605031b070e01060c03120c03140a141501110a051c080c071b0504021c0b060c071401050c06180c060f 61
    0x5052101c81c078407218010100c41940384c0c1d603140855442a41c4641c0c80c000c0b2030402210680c40342401805800e919048280307451203140442017141c0d0815030410742c04903c0720200d034164070b460060b50424040341490304499018044000081c200d403000e2182280c1d5080b0142055503561041d0740314031210401080010002036010302c007250011800f9041518883c0c0000020328101e4148001200c00b003aa945a500c3c0c010044203c05e5034020200c07030040000c2d01c0412010985420000c1842e07001c40346e80b1030104c0c8241d07c1036908440d500300d41011210403007814901552500c842030080b0100031011400c10103024071030680c0d00d0080c50261501c500e8088207456000d030000025929040c1000360000001c0c00d511240f005041ca1513008848880402442c521300041d10358214881c1c1c401c002c10310064881001c042120000c45600b0183e00301114003160050380c85000700701c0141c1060080c03e04126862403880180c440e40d02c210800e4416110518040107894084c2507039107101c2800601c50014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 682973669 1250 682972419 682972421
    0x509010512011b020a0c06050702130e031e030f06180106030e010b060a1e08060121090602031009060e270c121b04061a0d0f02041202010e100203090103 67
    0x1008507440d40c00460f154110100550800e1203aa01810040e40802c2c0010140030341c4080e841e0243c111403614620b004a1030300000c0050b04204000e500032076a603070f999003104804000f2180d6000c00810103170000241c2c01901a0f843d001280c0002d40100801c4c00600b491802c0e418150b50b0000e0392401c0d0359603900b841030443c010500990070380302030b6503070300d1411007280d40b0328000c0c0140c00610f5a440c98510482590700c001100c4c031200503028025203005014403680c00c826542113031186004d000100d0490754445c0340161019050140031548000144143c403a00c61009800380c445500e01401030766951000e140800d1402c459540340302906140022160281c100c10040318006101100c101100040001d05514100c2540c40801e600131603603040d18101070130350307821000c6d0221010045c06140525400e0b2200e07090b0100712945900203403400d408a4180e121f940c044c0941d800841d1141c2d22408107030310309030a03208203038007080b0032000b100d240e49001039041284819aa005e1401c000e41840190 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 682974919 1250 682973669 682973689
    0x5090c03010b071b0e13060f0c05183015010513050703240812130501050705100509030904061e0e07140c0105010f1211011b15091202030405090105 65
    0x203881e107880130f0b070010305051401040360086840182072810001107150510840320541510340030a4144851400710035001020344418460074544d068000012400054050003c001303155081b03082c1c0c0c03844010300c940c1c222100c01020703da90111081e002c4005075080c0750034801d03c030f56540150060303100c1010304a941c11442e0080c0250a003c03034480c6000c50b8040d030320b2414200c24402d848030024100227240c81044044088a81d128003107190108814607009100c1880c0915418001c1c00501d1794200841000380480c1c840300c40c0b03410069410314000a98030b079417142522034800c9081080114980315007000400e0300706182942c1310000b91030a1b1007c0c100080040512003031104203100181c0b1501c80000510648510341c1c000101c660500000c0c54100160b074211400c1300e20704c1d64ad6500003c00d01c0103021580d400034200801069002a042051402d452400824103c04103800c074260300c0c01504074460321881100560300c421080319040342c0da806140f1a60ba801558040100f0041c1498150307c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 682976169 1250 682974919 682974953
    0xb07021e0301020a0f1d18090721030210230c1b03041a070c03170405040c0f08061e011b0614160212040b16120905090c03010b07 57
    0x4031000100c0041e089820400c00b4501040c1c104a80c0780b0702e80d0348080041168600d10110844032400d44e40820341540f19456044030361013180300400c1c00444c04102c00300040c100030032202220900a4200e070141e040b442c100301c0251213a4012010142c50601511580d0350711055030280344455601d408062400207080342500c0310040046410b00c001d00b00610300c1c218a5600295520391400c0d113041018101e428450080f50410300c50a0001500071206800b125000003c03030a950002504086252296030b10440c1d0091508400c241c0241d003010103080701d0740b6513403074814450341d07154203015040c01440056641c029403030b40c10340300d030350700421150301c81030000002e0080881c15903544108031201ca0300c4428094400d1000c12030710030364640800c200e0140c544082c00101001031081810f41c0106d01620301e00400200d2070011403c280901d82d01c8a0f0780103c1e0062900c890414094030a188500805000e0aa94000121004040c404990495a880011074a009200d44505901409007922 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 682977419 1250 682976169 682976209
    0x1e042103090806010609170a050a1428060507020a2d060f060f060c081e1e030603010b01030e0c0415030b01060801090f0506011e03230a0b06040b0702 66
    0x1195112007001200d010f44804d031035000d40341e41042c1400c0d049011080d0300c00100d231701140d0987c00041c00420034042c00c82d40400301c607000d204a04811070608196024444d100d901070251191224481100700490b80e002d04070821041d1207029080744c942260700000b420980304a0600d42d0800020410100c200700101c82d5043d5082c510ba858400707442042160300c014544a90040c088454445500c0000300428285140b05d02020398032040700c1c0c000c0c9550605403079440049907000100c0c0e8000c40b02491546613081c00c858001321000031064009039603a03400b86d0700c0c10f401e0707c1300c07540a44240c0002916040080c4289000c0400308000350175201d03002204040903000002c0000c94422440e4003800301901e50b10325039070400b54080308507083d040c0c0e600c0300b00b410302043c803030240d800c50122401a4a090410045c449154406034060041121150809046025895102903070549942e02500d204e030790501119150ba03082208a0185004120103034108004d42c07001403810040b562034003800442 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 682978669 1250 682977419 682977437
    0x723180301021308060c03101202010e0607060504051903082202130b18010506090f1507200102030a023412060e0105010b0a0e04090f081e042103 64
    0x82400da800c441d0142c036443e6055a014450b4a0382070100d141e02074880c400c020f0031850f0049a11400d100e062040d24003803817180c410745056901c140100c3d0f14a0380081c1c42a9238440280c60400001d00003102e06480500502040c030800c4000d0141004100d41c256642100548030743c04d10f00303a0207410000c04110141d202c8030110041e290075515183d00f101b0103600040a40c0781e10103000c5029031a072801d40c2c02d0700140005000c4c80c2e40d5074041d62a01d25080e0741d10b205080400d40401c0011b0f04118000e2402e10000c5401c1c0c1c1084261015201c0641c84092005440880b48005a07942e02aa1f80c0c40c10143e04800510b182614680b23444a50130500030000084110440e4004148804d0710f8100300305084503010302c88180055401441c08601c3c8400c020095585003181145090148000603400c010880c4540c0b065aa00ca0308101c4a954101e103071640c3d0905a4a07005078613500103550081450340318188031a08404000a503400c0b0349003100340d42101c1c01c0e00704403282d11040d506000c609000c4072803 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 682979919 1250 682978669 682978717
    0x3181401020c0f120a120f030606140304031808070801060815011203021006030308090607021507030c090b0414010f170112031106070203130807080309040e030c011103040b0723 78
    0x340e07101c054000c4900006c8aa81401300810480000d8aa0030a1604200c2d0800804ea40030389400042035800e001e441d00c94403186030844d400103a036010903100c000c082c0c10118042e28003140e80021100341c0c038002c0000d66641c1e040f4680701c80d5450fa080c41c0051003280100718540105c80c491500500ca8410b0b42e102c0c0b2913501c41c1c0e0341107c0c0c06800690019000d0400c01c103540308200300d45038219a0b980000c1c1000c0030340e0103c1c40914000240140105a2500641c0101c9801080303004003512640c04540c0d1900c0e180d00700340c0c01c41c200314051140000c3c600340001c000700e0700035091302103c0103c036880e18415a00b4400b01040c0a1040d010407020084001c0840c0e0600030240017403402181e0a078061170b07496810711092a4180c1c5c59800500c03894004040130000a80008200e407489241a140402c0344d01c0f500e25685d0030340c020b0302103800700e65081a04083c0c104c038007140210720841c8500403044090301c800008450441d0b6108410713146014090643c0009040b0901804041c42d100d4000071307480d5000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 682981169 1250 682979919 682979923
    0xb03070b0d020a110f0604030f12090b070818211c1e02040f09180f030c1a01034b1a0708070f020106030c0303181401020c0f12 56
    0x490581e408103a01080003410719500c48498001040e60500030804600300300c0c6034949660001d0001024007200b0b8001c044558003071485422000710070002049946068104141c40080441d44c1400107141c040005254242e25400100c0403800800100f40700705418800d00e5510401d82450b5031030803018040c18500700035030814500b0842c0f5030900403072078000024001044100000e580c1d060280180828424591300f84100d4003143c0b8490400b0030308140c2450010703040400c5400182510018400d41000c0c540c2124070350b00c00d184143d122840c580790400582410980c203010090400307802a6800c01c140070500700d22451030034910052102d000840039004c4900c94038419072088400300c8002c0d0000d0001c0b0100183d0b144a881d41c0004a504c0c100c880104807070750080500051041e41d884071302e0114400d42c001c202440d44050880070039501c030f007806046400040c5050342014001e91010031550382c4003610034000501a0014400d6100c020204600038800400d03103a04451801e522001414003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 682982419 1250 682981169 682981177
    0x1005060d08071b0602030f180d0f0320030a0804063602120a0f080f0403170d0f1b030e030d0507081f0e0f04061415040b0406180b03070b 60
    0x7190320902220b44584200243c16a0664002c409541043c8624000c0200d0402100c008066042d11052602d003080c00040124004c1c03031020b841c14814044e01e03002c068100c0d8656103e00b4803011000211170301818000d580c3e110f0901101c00048260011800282054000c0b50914800300b02144d038001401005c85907400185035411601c4482c10240030940c14180902a800c9540d20003600840c0244e85420028040d820301c0100200800192200010b10b90020b076000703142d1081b0144411a107100384180c041d08014800c0c251f1500e042d41000001015101e8410a40c02182c2040c010f0003a80c4000d0f00140818001442c050104200c2c1d407040d0801b07440340d5407280581d520b4200d82810700b10059641c804c0c120840e020703580000881480883e070751056255102c2d0384507a8842c11555a85004400b40800500e1f00c60030072078020030310030005c03c2160340c1940b800090701c0c01c00c9019916420401544c00c02c1c4100300603003154481d0f200e4503454603005046c0010028080391022f940d44c0c1d14600103984 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 682983669 1250 682982419 682982423
    0x120403020310021c15091107050c09070c080703080612061005150c071814071209110d12140f0304060902030c0306040605060a0b090102030d09030e060a02010203040c080106081005060d0807 83
    0x8012201400242c03003d1041c41f0074183c1c003221321810040c0c50707540c07241d942d140041da241c45404001e0000300b101d441050305546440c0c2c4108050303113480117882d001d03044942c00c0d50818032581500b18001c0e501200051b6240c441d02e89810550002031800c02480300450741d450b1000303607501007081550709125003040088002c000c07a0b0070701c0a002624402410881300b0f452400d07025800c0324018441030303603400741501000324448600058a10070500d40ba14006c0300000071560441c01c000304030070a20410380726401d160300d1030351079400d040c004044c4204030328803070b200d2500351546017400410003144880e442110138a201504603a030030919080080c0c80c0400440f82110841d450381d0401096007004071540c801801080119810207626000103900c87c000c241c1c178118030aa03a04030090a0500ca680c100c1544400501156502d044180c002400703540100d6090352000c245607000030741c4060501c0b9850031a4003e0000e07100c850700340f08039080640b0740903048903408103a00c0b0080010a12082c010301000e8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 682984919 1250 682983669 682983701
    0x403141306080f1b0703050a0c02040e03030603010516022e0e0703050c09040305030703051504360f020108100b0f0406020d03060e0105060c07030503070b0603120403020310021c 78
    0x40340c40e070021003c503003004184050300e01002030400c5020041006640d6555031500b4680d46a03103401200319010380411401a6103c1e04102e08960386e114040010b40c000c10007a0001d0003a83d40700300c41400104452224080103074007190124100203400a08440c0904c1c0b6021007030070301c07050400c071401611050726a443c10742e0848902041045820404100000e8040e81e420107149000d4030003408600000f403c010034540ca03030300050010380e90082c500c0300c0c0356070052041107066803504004036402d05080c0c4900c03605030080d900050301c000c0d00000a4032a6405604810312401c0d40d801100c501d0b20182c2011411510210302190401d1034201a0101058207016507413214034024009113490941e0012005051038000e040c00b40590340213041e81950030542d00180e031a0200a0f201d41340c0701981e80090214000810003e042080300d14038607003c3c40d03040f01200d00603a0654047c4105114612000b54164419440d02c0b18050994014102010032280240740b40e0301401144402d48071401d0042e1890 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 682986169 1250 682984919 682984921
    0x3030912011e0603240b0d05070501090902040b09040207050708070305030a030617100b1909050406060b0a080406270f05070b04120f060221040302010b090906040314130608 76
    0x4805a02103542c000229101c00e000706460350f125903810060f160319010009224a01080385150107801c1144001c0780a0141004050713a8140303162201828000e050000e0f8800b100003a074603034180244c5003a03e03400c2a46514215410080100035409618201c8003801a0a800194004c060001d00002d50050780555910200c0c1c00c8002d00325080c0742c0014a5094450023642016000000d0482d00a1050700000840040000000e030100010307074810304041084503400708001410740c000a0099101c0e03441801603a459003101d480c60301031000c5d61030000f03007500e00007404101a47c1000e243c0e8001481d4482105400f0441c000d81036501c100c0c00d84041d0000b400d050204501000184000c0407241800740c01c00d4101034001280155805010f449500c5064072981408400e5046800140c42216031000618145041c0d00710541c044509802552802c416203a140c01d107668441e01c00d2100302c010b0170a03030343c50f554151400f0588140c2e1a15a801c24410f5075801c07003c107101079020307001c3c2d51109007035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 682987419 1250 682986169 682986191
    0x9060907030e0d1e050726040b0d020d061d0c18060d0504050f0f0705060f0c06180c030309061213050115170f0d081305011107031d06090f0303091201 66
    0x40006442d04c1141045410010702001c58441c000b40030f01c03280c8034039405081d01c201264054250107603400c6528100c400051030003402e403061780248a8800700c41da0510140e56038500110480c030351003030328880001000001a2130500c1400042006440d490080c0e1010504600814800c0c1c210030f10f11140c1c0e5547e0004e110510030100640240543c01d08010401000402c5801c1d071201407500c2114000c0b0408104500c0884c0b000b400c0d21440240d6000711234141c07510910050894502030400c050038003c2107100c00e0181004030485040b00400f41c283c1c0e10b0013904030030034500b0820081c144181c155030801c8000001e802030007001c405c1405254001d1117182016500c2a841c441e51612200a5110124803284000b011802c1a120032250424031880e560315181d03110408480c000060055280440201c55022128007601c5103501950b608403030205011404032a541c050b884941c0e01020a02c00901c15140c0200380700d42680c0c02800f500d08004c11800401c2c007080c071000070350245075119201c00d50 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 682988669 1250 682987419 682987457
    0x408122a0d1505130b040f0c02072d15120c120b06070f02040213080d0f0f02060601170a090204020f0903012403120c08030403080105030c0406030209060907030e0d 72
    0x40c0d4541c149000c915542c50800011048941c0c03011007036a458070745c01c0c41000b50355941d0100443c0e0a240c8018440000740300002512400d96000d00c01c10f0140201182c0680c5080d50601014155070300c0a1850180c1422621019070074104141c004004000c030300981051258050144180380035203034202c400d69108900400e4581080795140509414885500440c4400c00c0307094400c0c0d010307200144d0f0354075600385a0000107500d03000310496104140c401008141d2001914030802c030f0680d20718000000c0c041040b82c6480e42651158005100ba01d054082d403a000001103030004d612280c00100380541e40d02080c00da0f002078102d038070702d07001c00f14840040e03040070b0050040e05260307a813042e40c2c0b00c0c00c3c2d03440482c082c070080d0002800c5150440c0013107914901680850100d00e42080d4041d4036864030f8900101038040900526009000710310a0240c141410b0082038243ca9006102208903038a2005020042d2002007403841010380701e03031102050035070030311043d200250543d807078600600412aa80c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 682989919 1250 682988669 682988681
    0xe0f0a0212030f04030602090a0305030c160f06021515040e1b0319061518020a0906021903030f02071211150411040f0b1c0512030408122a0d 62
    0x112054004000f120100c0350010122000d41740e2000006032650302050200c2c26490854000401c40c1c400060310140d8000d0000b80080382510ba06d200748007850700c2c0c0e0740d511000040c80c4102030240c0d1101c411880c5400c0800b500960050000b01d401c04400d02203000213055030b800081c2c2c0c0010350011400040d284202500c3c5201001c000c1e8000c0c082484902503024140c2440d50340a45050b0307880070a2111b00100180c06001400841c1040100781c07005203408001f503002042c00f20100309410400030b01c0a00104038584078118500c2c1c04907150703003651015000741c040314001c4990643c2c02c100c2c810008140c0640d08035280240c4c1e440e080801604010b00345000c603000803d48229030840c040000042c000007522142d01400c0e540030540c0c62000c0b84c224041c0c1140780c0601d50207624110303c0050b14400301a050b01c101d0198044642c00305500504022a101c03d0300c01818203d01000304200355014074444c40d4015070900c0c601e03900e100d480740415240c901141c03c455044080040c50940303c0c0b007903000d40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 682991169 1250 682989919 682989949
    0x30206090106050607120203070602070c050420031609080f0106081e0a0f0f1406060102070605131406070b0a0c1e081b0c061302010f020607140304060e0f0a02 70
    0x8102c4a4106000a5042d001d40b10780140a5620100a103140314400d0042d10b1245500c0700f0203545880551074152045100741c0600c0c0d009514000146d11701941800e909240a8040000280703075403140011801100004030b806024005020b0002541140801c044072000d40c41c00000242241480d42490400300c1107103901d00e90f06002c18603400b1805d404a5050704017540141100c816120514020420300248503000d445c0108400d0100d007103040100d0082d100c1c4500b40d00b0b440301c8584070b00d400d0b03846009101c400c0c002070401582c20b1110b511808100c10341c4c041c0c01402c05091213400d60340c0160303103441103840d00b0940e40c58180c8628290f1300007152803079604001c03901c0c5403001104800102500742c0240b9101001c05000e4280f00300c904000b0803200381400c990162200d500e09040030700020850600100d0000e810780c40c001030803d07c0419028010395040d40d40015000010200c00e180d500050426104165280c5c054042103501b0051140e03130034500d0001d4040040f4134010014070807518010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 682992419 1250 682991169 682991171
    0xd05090f06100909030924030e0d0806121c0306050301110406270902070803010e010512120f13030f020f04020319094202070b0106030c1e0504030302060901 69
    0x24042d00c8000703498201c098810400340000d10415a0404540c1540942d01480031030401c1103403240110300c80070443c8665000d9032014088071004035151551042c02400140c009170303109011454034a0449010342201d64000d040310000b40b800441c00000606643d91500071941d10081001142400c1c052040c81c2000207403c10304091610070098000c031341c240c025440c0800e21404207000b0684400c0a10064081810215264015860a45900d030300a0081e050042121000021207141c8104110340740c5901c00080c00c0c60000c00d2680c0c0000d50400310380e2140c180c01c1800044480d0f8001444000150b0065031100c040764014014413021195a84005010b140100100410007c0c940d0455401c07900309500010140801d00f070018100e5001001852001c045651845030307103220703649203111011100c14518100c1d0b6130b80182c1007284660800113041101900042001038000e91040c01c810203030f8203001505a180107048500c1d419803a0076600810404582030062603410004a6030202e50840 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 682993669 1250 682992419 682992421
    0x40e0601090620010e030c01021b0a020a03080d091703070e0d0c05010c0f05060c03060109080a0b1501030f0903020d0e04020c071a070803091c020a02151e0d05090f06 73
    0xa002e404030400a000c810400b0f01c01400aa03025408880461000c40580b51107004070f0385614043d40c02040240a0051213040c0f08118840104517602c103d540100345090061444d40c0b181c415422040040318059502d0b000d4030701042c1c2e0421080c04405805030038603540c0c54a0040903084003051b4102500440100c1110740008503202c2c03076281554001d00300b00c880f001c05880d00c00d1000085846c003c1450042c2410301140400401c05140220003d07210203c80d103842c0d4007880c1d5650300c0e0340406001e51b5400c3e804170380c4515801d0510050a4018507010428024402cac1e0041940c803040400c07401603000c061208a1b1f59401f00381d5064605003100d0961508603440840e580d40c807080d00845c5400720f141c1810400300c003100d0701111199035201121a48910b8802d4480b9220b504507107002002c0b54072002504c070742e10b2002c0f65407907480340d0007440101040b02980e000181a04184039401c00054034005c10300e0b90848101c09004400d56084000ca41440d14410761820300c10b194200a0b55980154 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 682994919 1250 682993669 682993679
    0x418141023011508010513110d0902010806180a020a03060504021b0d0504050a0504050c09090a050702160806070e03010b12010b1302120f0a140f0601110708120c150c040e060109 78
    0xd145135044801c2154001c84481e00030804034010b01c28042480c0b06c0b44800200c468007103c01c2c0e00005030887c002d0b210b81d9010ba94100500c0030218a80341600c180b440d15000160346203a0039405000c110703180d4500019419101c0380410102d9101805980c50304a410703440c0e00412408002c440d15141e4945402230174149404041104400240103092090352a8030001d11540f000d01c0c250348a110004002c00e10b00e0030102030440c010a0142c07500c00060003031002030a8100503000030030080752440c0c0010440ba95400008482c00a603401c0f101d0b034107549031244031146079107040c0c800d9101c0d00800000262100242c0800946514040401290034010f2016110440308208030300d034440d000c0302c80300204e0303900c60849034020b0800d446040902101241842840300102c40003c6c441e00007a00d40d41e0440014180c0559121110300c00e40c10395511000041c02100010000b61040b50b82d08004c9914180c034080119604c00c400300c0e100c01000e000840c1c100206241c1030182500040d003800c00c441018101 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 682996169 1250 682994919 682994927
    0xa020a0605010b2704020d18061a0f010e0a05060d0b0f0a0302010e010f1103180405090714190f0602030a0f0302031003060203040812190b04181410230115 68
    0xc54111072403041104c0c4906a2070f140c040b1950311a841404000c204124041443c08143d8440b0a440f220b00d0038400004100540f1030002d01003000901c2d40b8900d416010044440c2c55404107140c1c0c1080003000001a903032190781c06040550380140c030100c1c9403a004014440c1d4940f101d83e61501c01c5000c0c0b0340410144c3d030070050040c5000002e01e484162201d40c1e10f000ea50384001c0840c0100750b03100010b00c030480340c0a10940c11001e000101c40601c036a40f9403d81c010340e0f8003031900031820440719201d2074100c20702c0c0a8002c000720500c14075200300b00075590f22603100c1d04411035105030096040002d04402056001c07404404031059801c045045060071066280301c400035000080c5003540c000003241c10b01c1701c00401c0c0c50100c1d0404c1152100d516001118207c5070140d038241c0c4900e1402c20402c4111860503006913104d01049200c420220f18541e103610b880000600da001d05a03003d01c0088513200070541c01640c40010825222400d41c04201c0b881a4041c08143d03c288130071011074850f40381050384 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 682997419 1250 682996169 682996207
    0xa030b0c0a02030c07031a131a130803090a020906010c20012d09080102040308090d02010314070905032107060b01050c0a0f1203050c03070c0302120a020a0605010b 72
    0x151695040c0c075900503010503483c5100b400c0d448441c07480341110020810459030300194441c1c40604500104e9120b1103491a03130704402400003084003c2c071804000a070220105407580c001c015003443c0f40ca107070305501c3e1800ea0303500941d40d6018a41011407400d0560501000d1290007540070304c3c00c0c2c0d40a03d220385030ba034400c010044885a04604440f24074505a00c101e41d01d49101c01c10fa01c1051408021a070302c6100e00c00784029110104582c648001040601803003030740d0890f908510481e140c500d004080040c03c1040c000101d040c5a83c8040490b074111050b44064440c0960707840322a5211f0410301010b10f4400001a40347c842c0c81d007002406803920a80054400320740e400342020544d00030b5803005917800d01a5040c0c0719850b00c50322000702c050003280580ca270841c3e4021039807404400c81026040b001e8500444042c21408000c1001c141e0341032098141e00800c0f0300a10541d007039071142c85514010782d8011aa45401a4440d207264030500c07850344910b0740106161a4454a0060801c10042d10150 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 682998669 1250 682997419 682997431
    0x31c090203061b0a0305061f020c04151203051e040b07031805010f2f03090f09010621020706020403110325050d060b03070b07031404060c0f0f02090f070e0a030b 71
    0x6192000308000c0e403100e6a100b1500ca04540d01d0074440300c8c0040d8000d581d01c421550740b502c994180700c800d101240f039140c01c80c02998400c281caa00c041500e5201510140d00142008014404503500c0143c0a03018802034005040c0006003c3e6640d20103080040080c483c80200000107a1100b00c10030450307800030f0314885ca80a0078100b96083c0c01e01074020881249080405011001c000d03000b9104d0518084000d0a500200301d414040c0c80c1d10304400d00c10803032001d0194102141e04030900828410007084080b0503851074034005403811009070303104410380e00198002c41e007180044509002911b03003402403d000f42954040c20072a1100200c1042c02d280081c46000c0c01000d503a075461003030001d540c1012420300c00146c1118071850740e4041c0b0b449254001f510680c0050006015850408024421503089814035501d040b00007a0a445043d00b07116085422501000c0300c5540b000162540020544603480d01d415a801c84d21b8441b0014206460680310284204003145041c0300107065042030711340000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 682999919 1250 682998669 682998671
    0x40503100509150711071a0d0e100c05270f060309190b0709060503090a03030c050d0507030e0f0307020d060203060307030807080309070902040b0a11031c090203061b0a03 75
    0x14881c100040e040046581500a5504000b000c11100c29017150000442075030740b00c101d800c290b5a03844042d00c1600d0359210482c907078000300050b4004500a800040b03682d41201c043d9405d29200108201c100c0300050600c00200700086000300541d455000d0701c44000c50035210710046842c840c030000f540034411200306449001d01001007400c0302c01c10003c60402010035030034602041560300700701d01302e400126040c000154010401003001c51142060724010204500108540705841e07806401a0813404800410020140110420780c41c050140303074002c0c80356031070009141031909a0981480f908150500903584208044001600c0300b501e901441d0790010341c016100c0d240d040010b030a10006a10241030402d010800d0802c1c050424001d40c000c0c240c403000c960050741d4074491102a4042d0740f00e0201c0382c01c010305c0741c925411b00034820703d800110f00d001964600304600d140041c2c102d2094480d8092282e90706c410800f14102040515007045d2802e031100c540030294840d1200c03610a510110b8109 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 683001169 1250 682999919 682999921
    0x1a041404020409061e020c010b0d031704083f1b09060f030103150c030504031e02010e03030a1a04090b0105130f09120305070905061803100e0102130b0405031005 71
    0x4040d1540c009040c89049100e01c050394a03c45c020403001e500242100e100552034094200c07402c0c0b070140c2400c10000e40c90386800003002210390b15041c0f0058028029201d1803010403080041449141da40181442d8642074900903e0201da10040e92980c450b0340400200c56420510080105101540801d885e64100700b0790382e121484040364450060700c1c03030100401c5004c0000700411811001c0034a0401c50081d0401c40300e41a403a044081e0740c01610003034081248a402104d00c440705d041c80803132270a950b000114120200c500328078610741c0104d581c03040441c0d9406c8075049841d409401c9440c3d4003012141031000901c01d840b280c1d0302110620520b4440d1215081e8403a0b0f4501503040001284e21100e401c205048136410f00044a007004070300240001d280130f00050f60b61303000b01d8000c4151a000b904031410142c49140d11040e03015031540855151080103441c21055085010341002c11002c0000980c5800c0c0d03907100f0344040744480e0400031540703c0900c02401b00383c170009000496506101408152 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 683002419 1250 683001169 683001173
    0xc120308090d0206011a04050a081f02040b0f070204150e0a0e010b090a02090a091821021b0d0203030705101b0c0b06010507021816111515131a041404020409 69
    0x10520542e03001981081c583c80c0c00144002020030980380c080240038400084031701c0003284030300702d11071030040c008403c0381400074fc05507110000242c02494400740000548200182452070481202d500044103c0743c500c04021071303480c0c203002d010a15044000284107015580d0006101600002c155001c61980855800483d1399071001c04002444000400c01000028030754020b2281d029400981c0c82e045900c02d0040c03124075092010580c1103681e4003820184580242d0205c00301952080654401d085814420144e03806000601039588103000421500300c10300c4004007528240c0c880441041400000000d030329401040004100750300c11078006681d502c000060300c3c18059440060b40045a140340d0141e000c07940c00549009406c01c034071606040041c0c400c100c521444003040040c040e002003500118000070500304035002001000d46048401140000c078181c9400307001412402911203079002540440b080840071034050948080c03003124110082d6510084010b000240125030300c4001c141 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 683003669 1250 683002419 683002469
    0x10f2a021f02030c010c0806090f0c0906040608090105060306060315100e01030f140d1209020f030105090a0c0e0403200f120c060c1905160c120308090d020601 70
    0x40c0c085219407016032801c0c0c90000039500e411022802105601e084002c03880c842c094000e15100d00750003000041141c0d5110060550000003800c0c820319440280111962561030401500142509603900311840c900003042d035003036920250400380660131100500809407400710300f081122100f464404040e464012038650004003079030098494400c3d001c000300402c200000500c91260190140c041a100640142da4450504082480101d07030313121850701c0c001005400c01301c50b060000f031122101c10b0035007010170300352002210081901d402840d124020042c04803c0e64019080c5815501d20342d1526079000360852030518860700c0403614a0f184900c83c88402c0104140820131b600658030132401d0080450403035040740251002c0d1780500070028401c11000000e81c4c0001031110242c0c003070607241c91400e950030350000d01711010041a000d184e90102d440c0c02c4030000100b00c50750b641071007800c003800c0080c069200649160720700d800801461043c143c1c00207030203041d503804401c03260740740c00f0741641c0310 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 683004919 1250 683003669 683003689
    0x3200f03090a020406060e040f0c0e0d1509080702120c3d230f0d05100b0c070906060e0f0f130f020307030b150703031e0905060402010f2a02 62
    0x358014200240412041da000011900081068906010302d1549c2c1711580e095401398603464001a4141800d6201ea00e0200107001c403d50203600703036001000c109026001a211000803e0300d043c0c40004012046080211a030510085400060f1004a1050f800030b10710141984401140b544080c1c03503901140d0740c4d20a8048903652046419400c0001c400c4007408180100f251034820f41d112a1001808aa090044444001c210720010385007895900281004000140c0000c45203145102d002c14a0f00c195801021003540000003400303940d20b0318640c001902c55a40cc40c85c20032444041c80542a1034156400005800841300d0310706052400021035924810000c0c08010385041800040242032182e006501a80c0d565505002c5082d04c80184500c1050000c031130000b001c004c00640010905ca540982c03840c014030481e000d018100440a0f00603038542c801c00780e9a035044032050200715a00032484180d00304043c102a09001d001c000c0c074410040341b0031000f41940d40e0f154180d20071503451020034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 683006169 1250 683004919 683004923
    0xa0503041e050a030e0d0c0302120c0a1d0606160b040501020f0d0b031903021b061314012a03031a090f040b0106090b030c090103200a03200f03090a 65
    0x41c1d5103141140c1090380e9540e41d104020b8000c0707964001280700071b08005442c0303070030640c01801c0f010f145881c5071309020303005103d2031168405019a80d0a8095980d8103c5004010036a110240da0f160307544200c00902e030b84019007071a01c01c0d00100074450011081c000c0d00c45410342c120405400f2075a0354145240a4464401d18a603219000030314584c02e10b980c0d9025694800b015001c680c80c11107200c0603e11140c0c81480c024000d80d020148811201542c0f13220840c144401a10090600c41941c0f00c2d07869603102c0d41c200e40f85031260351400344142e59100c8501400060f00b0b50324080c200000c5101007131050803a20000d82003585604244418407988450400454000740c608007081c0382c058155404040140c40890340081408000940d04e441071082c0700a507150b00e29810f10b551500780039562587d200802140c10706446083d6813005189160440e00d00000107110705c0e659401e0048028121092008600441041d601e0b4040401c0284425100c3c0102600f010980d26114003640525142d109900 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 683007419 1250 683006169 683006213
    0x4050a1203030902061b0106090501140d11031e0f0c0a0911041701090201020f0d0503010909140109060633140d0f0903033213150c090f0b0a050304 65
    0x400d20100c84041b62492500c48032000810a1075214030100066810a2050125400e48c1802000383c07481c03d021010700b89403107a0b00391044032003a03401003824034130b040400001e0814107011040d407000040c025648103004c00c03806058035441040000c3c20013003881c000d901101d6928215946401b00140445003d801c02020001816070160682e50180c41022400c80c018011980500041180055100040d40c46511528107603030030310481c01c1c01485040400c0c0e03210280f011585449000030b02c1061022070141740701007a801d0400c06030004140020300d15091000f4000240e4004220308980207107000031a00c0e20300c40c10485030401d220180603581540c1d40b228904800d660010b20203610002100b84291400d00286040d03081d0915520306d612400c048a00b068012000088580c00f802036001400040000c208100e98482c0700010113004003004403139030740351402001a6081110b140046c2848071021088905094081226004103d101002c0c01400300215080010354401a4400810605 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 683008669 1250 683007419 683007427
    0x5041a071701030503040f0608011d150405090a0615030203030301030b1003140a06110723010e0d080108070e1b131a090405060405090304060c150e0304080d020304050a120303090206 80
    0x4c207a0b40b280e12904c645401c8001c0d503880021b406002d21401c40c102c84584900d403800003030380d010303d0b003d004c0300a02440c1c4961518051200c199a503102d084d000d0b0031a8002002e801d4194074000c000c8800000900722001e058440c1000160b030004104c0781901d51150400b4019100d070ba241c01d09841098000801c420001d840030310282070006602c50006009240c1840700c03500c40103003904140b00e002c2001d01000d00100d64039001c1e0f070440300c0401d00d013200308000040101010082c07500b17090b00700d0019400680241c004100c055001c011050107069031221480d030783d05200607101a10f4030b021480c0c100c06140400c424881809448004000707040407682000316007020417402a140c1d00c1010706511543c030341008228241050b228541c4074061500065142c40e040800070350300401421002ca03182eaa1b000308034500d2214030302a00101007100c4000b5501e40703040220040c1400202400d280031540700340010407860b520110482c00301c032030240808a18038000d00b022009000d4001d0060341041c400a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 683009919 1250 683008669 683008673
    0xa0f0305030403080f0601090b130302060c0312010b0309030a0807110a06050106081503071806030c060203030603120c060627010f0501021b0904022e030b0901060305041a07170103 79
    0x200045100b2440303a80d0b5280c0039a50900c1e040c0d4061810340d0813070b00203604000140954034504d03004080324146524990426a5658005007055001205040ca1600041260506494000d207890b026281050449055141c11800103075280120b096003010001c580c00400c034030038000d18070001c4a0324401d0540c1c0700e2200d58101340010340300030b02c0b407400095a00301c0090160300c10302442d05262400107000d400454500404906008080d00003408410b17074074000080040e614684480081240c1d0700596280d2801208241c1003c00c0c140c469102a00100700b10201c0c1d4001244c0307180d021a048861498940899000040601800500c40b5011500e640003180034903240791000308662090342200c2141c0c0c3c2d030314001105d60a4154441d80c210400c64082001403400020105400700984a004404000c0c0e2a404010300b0101c00c82c18080b940d2150a21001d08003000040c1c090f00040c2814486402c00e43d07582d200ba2200210070204000f500008505007a10545604182c0d0400c03045503012540c6078 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 683011169 1250 683009919 683009927
    0xa05360a09141609050603030d020c010b031204080c060a1106040302010902030706031e0b01030905060f0703050f0601020a17040f0b0405101103041403070f0311090124110a0f03 78
    0x55400741e03042c0c0700c0724100c107090301000500d48402d50301c4440c000316081d1400e40f960010701000382940c0d41c940014003402806c10300d944007070328001c0d404100101e51205038005040c00d00f030340c00391346031010382c070401c010700040400242e05809003600303603501943d402c04500110703442884020182168001e502c1480140766054002c0c04265000301d0603900d44540e13508099003100d40c2c0c074a8080617030750300b005102d40d154172031b61003101220340604010656040b251f40e0300c1d0600404890101452080c0307000e022450b5072520906501524400381c13005641400341c0080e6503079495035001000c00c0d8880101c00b11046000b030541c1c1c000c0c2009449103040c50303203030030000206400c280116402500d880401210251050010380e600f541004e0146141030f0510307500c0c68407480d180600b140c16100b40c07040001d4440c40800d00c1001980128004d101140c180e50401c0503e000603800311080241501c14244240100c1000d00002c0109041420003515111012800c00041e410040e02060085420b0030501d40c03c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 683012419 1250 683011169 683011181
    0x2061e1e130b0a2a020a110d170a0f050405150a1107090b0103150e061011030307030c020d030b10031509060b0c070e010303020c0915030a150b0a05360a 67
    0x81814032001c0301ca042039800c0385804da034400c180c00591001c0c20795008500f2030500c2c91707100c0402408441200742c0a490b4881c088400240030f02d0789107000903a01030110b40c000c002d00481c1d0503034541107203428503100010361882c05103140c0107940c0000292403400c050003400080769040c201026204a258cd070805c010045c858000e40034082030410031400d1490041c3d554070001e03602e404280c4a86916190103105022003041d100100b84584400752080d4000100069071141d44d035507030003040900c0c240303600038144040101c0c09814113007002a1001c0c0d982c1d0300348501c02c000029260008600c15442c003540bc1e000f9882d406071243e030386043c00203d615000940144900c0c04954210368815a50b0030040341e8202d42480060016000101c840010b03190888025410800b0b41c400350700c4421140c1300090070301464030021150444206103a200301401e90141300c450711001c503820a155450040443c030080c0c0310be402640b1188031b45c1c00920207625244084210162000c03000104d5180c070601803001801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 683013669 1250 683012419 683012441
    0x21020c070f09060518070c1b030c03020a051e090709050a09020a081815040809120a03081810020c01110d0605030105011203053702061e1e130b0a 64
    0x1043c104089650b0810495840300c8031039203081441d00340c1d54a00200e0301e0358000c5108a4980c244000000200c0740c0ca100c9040107140122002d02c880c0d407031032040142203e2160702c4607000b012400407080300400308910080e040a416142c000490b91745580c00c03070f01c10110383c00085c2d07c001c461401141000c03065000c4e19403144541c941100c2604c0345840b021200411a45001455002025091a01500d00301c0650850300c5070700d200e0300f880440c00000310101d0681c0e03625030869020a030144203060348140001d4214142c1c1030b40c901078650040b0f0340ca0300c136010000c070740481b1500014003001d000001d61020b2074808000c1400fa80b210640c1030600090b00403072044e24401d40c00d200c000324141241303403c0e46071007aa06403a480c0c940365103131a29401b0641c2400d18a02086e03810b10b00040c0726030f00003c4001400f41164040d141f1071904440413901c1c0c220100051111542080402481c2c0f058100310506020742e9075100362455446040705c2988221031500144820803110034001070540360703040300c0b00807a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 683014919 1250 683013669 683013671
    0x60109080a052112190b09340903020f0a090c020703141902010e030708030414030f2d01151523040b0a0201020f030f0906010806040321020c070f09 65
    0x43d210103040e083c1d00841c0040c0307800400c4040070035146105100065517502e00c50f000401c032440e000e00043c074500c500302c41410703000100b98420025185202160b02015050350442c2031254040c41c030081c4040484e00009029502000070301070241c3d00c0100c944001c08032214180000840700d007009444140f06d03c004c5030706080f416105012640f02182100b00300080304100d0710684215001103461a21010b01c054142c01501740c00b01d9204130600081c005041405181d4036058401014582b6119504981d40c03442e811002e401000e10342c81011004213490620016124111001400c900410440001c0c141007243d4060028000b80c0d10f49410b00b46d6407498a4000d0b40301c0d6241d400408040b922640d82a040208100c18800c50001030050500f03200d4501c001410046d200310b40c02c00ea41d00c103403100381401d0001c0040101c004020042c084c050085580900703480c0c1090f40d03003d400b42c40262508040d4584048500405103620b80c1940c035000b00040454145555801c02d50f8140044c0e40100d205003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 683016169 1250 683014919 683014963
    0x2060702060906070c1109091f020408060c0901120507090f06050c0d0513030503070b090d0f02031c091208010609080102070213020315060301030b090607170f060109080a05 76
    0x24900100e1298850340c2c080b03025040d2665207000484001e510300b0030071110074215a850010740c0e141c441d402031085042d1001015940382c00317080b04012801510040100701d00402040c002e400012600035085111940e29540b18803c0302ccc016a4603e10566001060b24a000100301c00342d0b90000040c011182c01c0b801d4280101e49030b40d8102d4480c4112502c0710702c01c1d4001da040c4030b2801e01c104c0c000c04107100d40652240c845604c0355102401d43e44002c1d01a2400c080d0702c01403000701d850512240210640b50308003085101903805000e500e900494040550f101504001e0182054064201655450340510810320002031400c016241000c00c0c0034410004144050105c0d1400c030501c02c481d881900186110789402415000030041d5000411619000900c5680c00150351110f00c0614065407040203820010301c1d000d4603040c540900108400100110106061000040c1340c02c59500030755000f040c52415a205401038820b01d191380e2160003144102c1d4614000c0c490b0100f000c03c5180040c0e2901603034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 683017419 1250 683016169 683016181
    0x192103200f0909130f0b0f0a06212901090b0f0a030809031e1506040b0607080309011508030c060601030c0503010509060d0b0705090f0a1d091606080712060e06010e04021201030606060206 82
    0x21181da070700601d0245150401290071400400b01ea4018581c4154555000d80545810015082500f0078003541000000e0bc014010301781a400f5030000704500b0303100548095500400030310703001c90303a11010304150b20004007a8003540303040c02170300c5040040d482440800700006a4441d6640c03090520104500024004203825180c1800348003140702005000c241000c0b025100d80010b58070281100201e0741d81d90121980b8409120071800c01401d946c4051616607440c94507050030040020030b120304040c644101c5444843d00710b019039049d01c00c00e50309840369503581e5000c245c50780e24854001d084280000204101194054001d000740038080e1110144d002c800c07020701c0340c101d03150f0240e18001d0070540f020b0013680980c00c1c481c591000388401154600803030368400e03100e90000b6410400015900034100b00003107420001e0411044031035001042000e00e4006003406502c0d01800c1d050411010400c03504c0d80e980c4540507142c41506400a1400550f52850400010301e440c6c031030748002d80544000100b07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 683018669 1250 683017419 683017421
    0xa080402010e09060102100b040e01090f0c09050f04030c03230301080115180c0c0b0403030906060e150f0609040e01020a0818192103200f0909130f0b0f0a 68
    0x4007901c4d040e001007180d01040c07121704025042000704035401c01c2e41c0310611100400c00f4011801a10b000b458250204086810441d8211040c2e4203c0a0414100320074004402c1600b01c10561003505864102d0140e4950f00d001c88030221940070711140300304200500005181200300450496100900030008002d03452082c2c0b984202911680e0290b40e04020301c3d110510341c540000d20304407098a400c02a8801c1965400b100c0f403420b4a058000941d5200b80a0400070b0b40c0c0305a07009040b1000e0b5018040c6007000c0310030405070000304014001d242060b400840c03a1175100a4a03004040100b00740b01000520350780b43e000790003d040d9180000c0f0b4000102d0860003501104252055109024007100d0707402c500301002c01e8002c103400b01d401314040442c40c42076921f264400001007040360780202d03448840c0c1c2d0040031188444921920165410000c45c040d0480c130b04110783e640e4409071500c0c5a280e454085025480c07407501400340815100b0103070002004800d0214912843c0f400001c0f5410303458100080c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 683019919 1250 683018669 683018671
    0x90115090c0203040b0c0f0f010b010207050a03051c1e0c0c0501030506060d0c09092309030408070e0a0603060c050319050606070b1902041e080303070504050d0501110a080402010e09 80
    0x1c00503800411052111a10440080214aa040d401c0303440b07040d0001001444d01840e00f032150080d964403c0a02195070381400400021700c0100d55880c061030a6446603a240d01d840e050412407540701c441040042401a0880710349521504203210700d80c5e49228010307000303002c020421a815140c0240c0071a59601a00c01c040c0201405000039003000807081490340103001c503036100018040e003030000003207212803401105200d00907009900301681125024164100014107592002e820500c010b0025040021f0200d04030740800007000750740c0d1202d240000042a29400c0035020504001e4003041c41d9070804021405030030764010120303260801d80c1100d001ca40301502ca040e40301508000c40000301d054a80c1c0340d03802c080108c450402c02500c410a0704200e81c0a0351050842c3d500c40f81050305105884125100200242006180345207841d0b140106240300d0703802040d11038410074510b0400e05c07000b5480300e807840d118000116659400351902406840088808900142c0d09016501036414116541 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 683021169 1250 683019919 683019941
    0x103140c0316050405130b090a06050f040c0e0d080301081e150c0909191a06090418060e010b040f0216060b0d020d080301090507080108071a1209011509 67
    0xd5056407542c00402c81901a14003a150400000f0f1001003001c0c2e8a00c02c0f40c0048940346140069400c0000c01800241400208281111464400100300c652070342e6619032807041044a0000c1c48200c1a40700342ca40b41441c1ea12075421103040343c07401040024150056050321031020454510304104092007500030140e606404068001004042d400619080b04981010740c1501c001d0510015070045082c83e0340031203043c00b2520341040d84070903458441c450b030301c0d9400d00c00300709039108240703080854100e1080d208c4d80d0717015907a1b8804459100700001c015410555004000f480341031030300c82c0340350301030031000c10301ca8031661900c6c4114680b00054801c4500200340d40000d8100c20070f00703859460003030009000041e08103600c41c0d000d200590b9514105c0c820b1a104400f843c3e141d5040103050f408941c00145074030244601c2d8001032100c2c201c00a80c1e0012100c10340d2500781e8103501c1000c80c0000313010700c4401280110002c000c1c0080028190000c140390010aa20021469680d500d4081920030203105 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 683022419 1250 683021169 683021191
    0x17070212030c0f0c100b0d08090f0f0306040524160f03021918050906030325080d0c0e0102030315150910170c04180e0109020a080a02010314 62
    0x1008a659180203550b010b00105205030070407510041507025540103555024031a0024410400c068101d44219103070071034251500002198640d4500040d031260681492040d1070265180300d80b03950b521551071303c101024042d1121820709103410fa5503048510103106082034040690300100c6070028000e4030908000081c1d2010850404007650714080c10020001099020002e91107030038018903040c0d00e0324110703640d00401e810310200d40350300b15500c41d0420f80c85600b02e9020300c00c0990700002941c0511100b074240050554a03021f0001400e0b02001c0002c004610208144850054540c40584409201d1b01e403492a40320400c01240c0700d20007240c0040c4082c1d520701404d040340c20805181110480100080d510304030159000641c030f01041140200081c1d24a020310754101c199040300e5400400d0603001c182418144061403642c200d0000481441c01c6e500c800415000c40d09400ca07440064000d0480185107449410407502c130803070600260702190a20100c540d006103202c080b14850110840 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 683023669 1250 683022419 683022433
    0x1050604093f0f03050603010b03121c09233012010902041a0408030f030403120501080304051801030c0b09180903130e09070504050c040e090d170702 66
    0x1400d8012a2441d01c0982aa0302c028590503122000c5500d080040c0055480f450440d241003180141551001481c40e40281d06008400c03002e9200020151001b81c1005401910750f0000140c5078100154948110812414080d90000b44a15846200d196034001c1520304070010300e9070341c3c00e03a80e03400c8586007461004440d05040300000088891403102c0700490701e2580341c40a141056142c5250030b0b08503003070f5294002801c020451494154800d2840c1c40030019082a180501140d100d00642030001c61a100c0000040c041500c1611407407140010740713008004958490140560b241c01034004d007801000b66101c0d001c102400241454100d80d480002c0400660505c0c00c01d5890703410410032603401040b0004040d1200b212101a01d220300b103807500554a0b01030b00e0000d041140340710317401480f1100c0f4020500c640c4680100b079030b0041d01c20565001c21145c0741e40941d01c1c00d03481103500c01d4103541620000e0000e80b0002048004080382c0e00e0f40c0c0c0301e010500c2c06000c864008010340d128230140e032202c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 683024919 1250 683023669 683023703
    0x103050f0c0a09030b0a0e0c0108041a070309020315100b07080915090a14030d090e162105041103070501120509070504060e04020a06020f0a0f14120c0105060409 71
    0x101c010b007204031451400c0d12501d0b6aa9551009400017500d0380c410043c0c517003003050810802005001201e450901e4055000d0800b51101c01000c848940501102d480c1800040c450700d009420260031a40e02404a07080302228080c0301c41c1c000f0090b41c1c08080e580704280f00240200329882501c0280390811072203803501c2c26140400120f45090595804401c1c0140301400660755481d0000004009551010511501031030070507080903001aa5071b01404000f000610458140d01c141940c0171031040b46001044030300707090a40c0c19008408030104802c00c4000002411001500014012481441c1001d071000c550410180c41d08418041d80d4002032002c107422035040703810f400607034100882505540460340c13144042810381d100d90300501d00701071036042408214100f4242242c020007051016001c4201c01c1000c01d925142c41b01400340c0800c0000d41e500c801d100804043c40c60b984005405c0300c9220040301c0300308041d1703040b540e0082ca540d4038003800202141418003a5665099000400c03c603244e41603 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 683026169 1250 683024919 683024941
    0xa0e03030a020705090a0902090408130b0708090d1103070f080f0c01020d1d03061312090540091a0601050904051332070315051f060e0a050103050f 65
    0x6c042d603030f40310340361192040583c88240107603000d2805005001d41d1a28031a81e4190b001003181d000c4911198104410004034030601d003134491401c812654a9140d2245007810b8103080141070040340c1c54040d5000000c0d251446200103c00c40c0e449400395800c0c8003400c8550b60700c90700c009038850301503084890038404141c41600c11000e08030043d101c01e03184583e80004a440d0001c21100fa40200036412840720034407519001a06a056640c501603000da410103000c42c0040d000c1041d030190222034004580b10000c14003605541d2500c03051b400000c41000c2c451084080c250a0f40180c400c02d46002d2550b54209481518602c80c3e04182c650914004e1024280310060500810320865205180b071800000344030500c10301010306a241d405182000704117414100300040c10410613550744003036001c1000504400c400d4060344800c2c080014203a880c072183c11240c141c1540c0250ba1000030840104070213070000f451006001e07043e60a40406c5072a080150100c840a9411418804000c8001420f03580c0e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 683027419 1250 683026169 683026171
    0x1806052701260a050a021305010311070812060f0312031609090f1d010e1c03061203021f0b0d060906060801020708030610020d0512060301090b04080a0e03030a02070509 74
    0x185850518041d50050b5039080d40700090b149090714151030700f4000010307041c0c01156003240d5284070441c98642020003003401105a440303000e060603181d01c05404498001c1d0142e07500ba64201425a55810041d10314104501c0b080fa002d13031190220100d500102c0c02c0001d0311091244425850514603103401c4544c0c04000d40501000040000401c800720701e650150048080c10b40b14294003198103405a105074403a0170f014890780c50203a1601d56400e00d4141c000814812001180c407140200b882031000440c06040290460849010640300d07000c105a40090010900d00a00c54a01d0150030b078060910280c40190f4800340c0d000090100031000700d102c0c0c2d03000c0e1030004e115040009207c3d5030340310f00c5400c1e40c100403811740c0c02e5080441000560300740401001c0101704140302808000050920182403402148410322a050090001a480c0d45096011614058108e40000d420f843d06140096a43c0e0001d11490001100644003010a04000056694081954000d40a014140710900440100c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 683028669 1250 683027419 683027497
    0xc05070f2618030706030c17150d050d03050606070f02060a2d09080303062103090402030412030c081506180d030203072001080c0901030f0c180605 65
    0x40050840700c014030880103080e55001c803204010715020340c004042c109511540100c05140c2050f429200e00c0d54060100ca82c440e500003500c5100b5200d40410403141016490000d4021121035a200c0c2805030006802d1029101070341c00744401e0b640c0c8410300a16024440e8020140d46450f001c8000600d8405d01030400d007402490202c1201e070100c00c080da59016400200112094500110b0b034056501000c140050050803008520b5030400078082080c3c04400c10601003150010305900c01e24103c00e200b100c1c84085c0051080d516805d20b820703c1c40c900082400d07210007203441c003042c011800e80601d40d414402c01c405079400d04070207114030074040700d0740c40349500e00b00001c04484105d5007941d80038001d13071b4440d001e0380c011625507805207000782ca890b021071002c030003d040c00d14803a40300c0d0ba230058200707500c280041e0b09551151030340320068000d0809000c0b04a41d050900000700b030503660004061442c1015400002849a0f54000c1980c41e40b140d40700718401c10424480c043c0603d42e4800c0c24040e008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 683029919 1250 683028669 683028713
    0x1e07050c100504200105040f0b0318030a0306061d0f0909031303081207020303010e0703090809061602040c05281404060201020406020c0f060714031c020304060c05070f 74
    0x10703241400d64040b01c2089038116055283d0b840352500c80c4182d00c014030500102801c0441c900790800004507400c15941c440c8008a40e00000050b11050814200901c0e031048101180c0d1200500040036015007418062000010f5004030a40001040f0031200c9414460145c0b40103810207060051000100008150500603c010000c2001410716124280c00940c006c200c0242c5440700748080303828000e0040d000804560080c0011300c0308412041100b5041b500c00e0a0000b01c229a9140c0204c20380244441c580d0b0155000c0340c2031920900d11060340d40040e2080704c080000c03c103041e205440e07174011f401400c060b040c204400c0100000701515078294030106401e0415a49126a1441c0815030064002030010303500820100300d9660101300000d100c80040b10740c40114207020020800794020f25402810a03204c1d000c1c00c0d500b60000b44101c812640c031102c0d100c0c1c8064404109240a94400d50741207894a203003401d940e030035a204500395146682e014691085a4142c1e448410940301008492000c803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 683031169 1250 683029919 683029933
    0x2010302040b04090509010b0301050115081e0a0e010b15040302010509030c040203090f0606040c05030712060f06020d090801050402060301030b1009050415230711030910020609061e07050c 83
    0x929060700c080c3c402440300020116051801329103650942d8440c40000d80a40e0400700140038004607a40e0340e0120185c9031520013100c5e900c4c0150481b6046101800c48141052081445060380030b030f411901203d28480002e100c0700c075050341408a10406d41250300c020043c184028001588214020414a500101100c041c4000000003408907401920980919406599031124081062182940c0180201c80400a00b801d15074054a00e20008050104001c40c07901c07815000310039580044041e024610341180005d4807194042d54071107240072106c001c200004000a0950b030140078103440740e5400f038805400c6918581d08d40030300180144c680d0609510105c400b140311582ca00c41c151043d0b0150149640301150f48540d1011160003c522000010103c01240c085035854101c1c0c030340010040c030700780344445078509582d4114061a402e0035488076540014040c0150300059460040650700300781c0303800762105542644140c024010b000340030010031001840d85402000540803140c0050142c40304 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 683032419 1250 683031169 683031179
    0x18040e010f05010303081e0f2e090617030f0c1c030b04060504050603120a11031308120c0a060213120b01030c06020c1c1103030708040602010f060e040f0201030204 72
    0x35100710041e4003032103a0380c0348010020b0607801224240c00481190100d83d41d0a50090305c1016000018a0300c0c2090340340e03902148032607104610400a01441c41a81e501c000711800000000c0d00b042d00c5000c2c0c002d400c03c0400f2072400c11001c44100d840180340e009601e8509441c211b1007454014817000030090041c0c2040a642080819038481e0785034071983d001900ca5011403c1104440c03107900407600aa14003003c00a46072070001c1e074042c107400e40200c1a5164400000200c1c2c0028445100c070600340400700d080100032080740650010f545121f42903c6010b404400380c4d2800380110b000200155019100040201d48254001c0503540d0940402844141d2202c06494101030942000c94081c0075010041003401110724144000d03000504c0031b0602007003042c0000d02c40c0506841d64030403440001020504010410340074881d1100040e09030303519039615080c1810182c0003841140059400c10040303401c811010320801e010780700407510b131030390703640300d40e1103a4880b074008001c2241030550802c40400c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 683033669 1250 683032419 683032421
    0x1e150a020d0c05090f12190615060c05061306060e18070501090f05060f1b0715020705061903061a0a0e1206161206060c0506061518040e01 61
    0x882400102805079881c445045080111121005040204103003480082c015540b00c0d9072404c01140b0403a600480704c14094442e0f414414443c0700401e0400d0004a8141085000e81258512030410007041115035030703803c426940b860a1800c0104140c0010000541c840340c101e040d449024000c0000007200c1e912200c01031030715841078a502c0c0030300c40700072240c01d11081c04001d03903005010217182443c400c03880c10181410448090044603c14080450601da40c03400c4241074a010f00722401046202040d0007035126203509690040041030784001c400104003900000703c00044481c0a04500d180c1000e03c04410410b0008a078540c00f0541c682300c0004d040466003281e00a41b5642807109030303a940340004044c10000265081900940041014642500b03002c2103207075020040b01d64141916001d0341003264126000b100d110202460b2100203d0044d034051004181c044c071030b00848025844100400280c8416040401c0c8410400c102010120350b9801c101880700030060030210f02c8084405601d8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 683034919 1250 683033669 683033671
    0x506070818120409050a0c05041202040209060a1107080d020c09130213021b1f090c0306060803040603050105060c06161b050c0306070c0f0305030403090518010e070906021e15 77
    0x1620102d00440c00f88950611403003466049410301008110502480e0409000c5001c1c030712900c1f4100161010182c250b440e2032701160810781d001402035a0321b2128210281c03402e0754440c0401190710842c400480c0d080d40001d460a0042520340003400e01a5904003004a01900200f4104401520761a240c0051300c42041c0c4049602c4d201a004d41c640d80b0740c08200391010040700f651010b070b81c0b01030100b101e00e01c034541c0700b449581003004000c00c800d01c4034103081c00c030b000a542c40100010f152440004608401001a1003030350041d5030140300740d980c0e92040110f2402448240d1035103070811408280e055020350004110002141480d403a54440740c61a203c2c1b0000801c4241e90507000b03c4041c203400c0c070b03007407110f01c1d44800242017130907031100c6a8541c10100907135400024140701001020070306242c06616440d00401c0001e2040024004889141806420038810076a03035601c6c50010405c1c160045000c203040c3e03001c079401000ba04040b00c1d003140204003504000b40090042c11880202c08001203031803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 683036169 1250 683034919 683034943
    0x90803041e030506070f021b06071202030903120a0306050a320616050c0907090e10030f030f0e0402250807081218030304031b020f09011409060d0506070818 69
    0x503441d203d6402c070190070001d090302c8c01e46408039108030300c81c0e46a450700b041e120380a41001d5091004107503074005034554411070010319418418145800c40040300351006000703121590750103005036aa600c040c032070754281c54003c1c0b220f801c0182401001c100c11000c60000500320750302d012101048503070045109907101481e045040202c0c010240d050160410207800300980a9615a100c0c0c58410802012803075240078001c4680c040c0d5011031900410028001e010315000321000e000b0708401e1401a00e0040384034031140c0461400c00c0d041e9014a814400c1c4c80004400c9500c140707501d17110b400b044030f680b0107400044444c07803414403950703010030000b130b0183c219101d0760801401a401d000d911a85907a1070444d103c0c020346d008208102c00a94080040c0c080b60007941c0b445101030181c0d1002440704084034081c1c1e03800c460036100001d0115000d044007811007009036100b400755140d4009109480400c0c600c0a0076030342c80700000c0340400b84118982c540c04030060706048001481c950505051040803a00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 683037419 1250 683036169 683036177
    0x3070c030c120909050609010e070c03020703170c15040503091201061a030712180605060f040e060106110a08160807080309100507110c100201061d070f090803041e03050607 76
    0x6001d081c106105d680d4001c1421160381c8510361600f00c0601c0d0000000301000d040050705c1c1c1d8040200340c001c109500c0a0b650060010b030582030f08100d0070800f50440c50103072003a80f040118001d26034610f403a006005680101c0a1450108018180010081003001c00051503585020004a95a56617404500d46851488030b555a06203044000d040c4030300840c1c13101c0c0709494003400c900010a0325001400880e8003d0022803117644090004000c200c0d0f0002d1145c0081c00c0c1000c07134560503404034280d4140d9565443d485900106000c506039111300092005002000c1000804541031700050001c0c00741b0b1103100141d1030400701d55151388486c6c20603503520065512405186240c3e440601a2691000203450710310a0384030400540c3c6d9442040d41c1c58680112004012010300900c00e400100103031000d003491401c111a03480c0b40d036003400320846035000020200e1400000f002e00c01d42c00711044131401d0008504241c00c2c02150741d207140040609100c4500995000070000d4414070400c0c0c4501e000d619 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 683038669 1250 683037419 683037437
    0x615080717060705031302090414060f091c090314030913050411041103070e0303090a170c0108010e0a050603030702040c050a082a0f070b0c041d060603070c030c12 72
    0x7489031910001030000c0051080a00411860202e0030310040b400c940c044408218540382c6081c94208050f100d401c0f01c0081c0681c0c8100b002d40c900c2c00c10424050a182421100c0d035000c031124600d403a8000e519110001091440b003040810309482c0c03800c5110798080241e078500100000002d0309402c1c0a014a83e106403075204100510030000400c1038241c409560600640010103031054107480014542002c1c0301000708844040d407000c0050380d6203081c010703040c090840d4445408003011150001c0d241824401c10599840d1035201340a032034101c034009910085180c031a40180b401070080203041541502c424071540d070150b41e60340030301c100c16102c40e1203481c1d5034520602d001f410303510000c1c01039107e0024200320100a01c1601000c01804403c81d50030740c0c1301e50402ca0020401c1c841c0180181c9001c00342c006004d101024000107008032140c0100c90f455420032040d080b40307013080855032a03a0200e001e1000410040c010319159101c5442480e0a64041e441681c449014800c20b160060008107101 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 683039919 1250 683038669 683038709
    0x40c03060b0a060c0303020a0201060e0c0d0501090905060711030d020304080d050a0b030c190302060c070e0a0c0807080406092a0602010b030604030c14030d05040201031404050a06150807 82
    0xc03044051103070095035400000c41c1003e2001e41096500d03a001020168001030141c01c0c2407003984444040c0203034100c800c5450514500000d12500003801e43d034501c40c030b00400022100d040f441902d0741c05621401503c50b660311000150b4403411150010b01c1d5034001040304032010200d038801075100f1031041e1046070b20b5a20505011003110030084c41000d01a140840c894071540d8001084010391900f1030fa09044418250003c442441807580000e40018000c03c1d44003210f00040f44400c291420541c802034555141514101902e05c40b45001e004034507400d001c0340c8468810950316500c00c0c010f00c00401c00d10340c159a901e490b48a41c00200a5641146071200320440365500d9030300003804684000e01690801c0800240c4a80700508018107004960b0807601c108203c140705040034100c80401c1d01d484001b04000c410161104590490010740b03000e28903004000b0f01d44101c1d0203181c0020042418103070545d5400010955245080240400d003030300010391090070844403018200c1c00c036181646c00042 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 683041169 1250 683039919 683039921
    0xa0503071211060603070317130806041a010b03061c02120114070309080f090103060e070206041109091b0103020c010e0703021302091c1b061106160f0302130806040c0306 75
    0x142c1d801c29641c0080d01849a982e400064800a80f5048117200c07594200e031100b02c5290740700c0c4c6103003049040443c1200049802c00890396502c21401004d0b0f4040411043c203803a1200e43c000d0003401c1d004007080c000b2503820300380344803815680030800200d070b21014040e800040e90307204440e0540b40c050303440c0d0741007a501e044141141030300880141001d009145107552030031403501400050f1a084200842c0a45c15a8401d40080008040c01a010072140c1068540203403210000c80782a1142c0d681074082c0c64550030840030941c8210a000098940100e40107841501c00703803074030f00680c10581c0902806564203400c6c4110424005014000c1c9401c51940c030520105140c1441e61410191040c4584000340d1200c42d001c040b5034505080d0500d580740b191600000f64880e051800f84030025041e40400c000d900103080020032510001207074619030703840b40790503000d16074140440005420302d52081207240c0690081c002400c41e100c0c000c007000d6100e0500f40e00d850000c88095403144400c04c401c009115031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 683042419 1250 683041169 683041187
    0xf0c020f0d0c17160516080309090a092f0f0607030807080702030c19020f04060303092c2502070501020c01080a140a060501030c031e0203090a05030712 67
    0x455010303105100003024090b2500e1001c20028108452040000b480340075141d0448004c00c1414000c92510080340c00c0581c0d4030784060800c0c8980d11440c0c80e010800080010542c3c011800062040c11250b036080700c03e201901142608940a815504200003040c40341d020b5030755100c420540c0040c01c0d0000c075040040d506e48140140303008100800101021a0b401039000ea4440c100c2e0402c9211034581e008101c0c41d5100707041e05500c1600401c40010b144203140b4901c05402802100d0750b040000c3d00d1f0040004450390307488000e0229280c00002c004400b03220065244400710f10149840c0d080c007074440c0a12440080711110080c2d1314050f03505a040c04000e070311101c1404144000d207003450400c00082c0da144043d41c03100b4140408580029031805490300108030311540c00c040b041140c104104d0600107403805018141c042810310b4107841009200b403140c01c0c83d592866011203056803d010046000b984043e118841a000b24283e0b1000300f4820401407100e00d1042c054100e8a100c5180010944d0301c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 683043669 1250 683042419 683042443
    0x31806070f06020702061209060105090105300a170a0306080304030c091107050109030e120f0703062301060c0c0b0a051b0c101d010309022b02040f0c02 67
    0x20901060010605841400345520b9001c00010390b9030b1090300018260340200c4800705086200b002c1044524000422514100c0b4010783d0307070303084036600ea20400011381581940040048503820701030040c0a0035002072196861524140e80c0001600c1c0c45110b6180b048480c07065120b503000564141c1e156041c82820002c1202002850500d41555643c482e840f6080c410151041d465024424000b07040c00700710b902456200000300084141d174030b405040c00c000c80030668440c0f0f42452034030b011000e010071150207001744c200240a9050441c0d440c50300800303d01c0c000c812000318414400e04c0d06881ca1002134080c01c640d4840b0301960841c0e10b05442ca5100742e03040102900c03003e000c48801543c0010561b001d43e00e002c0d0132810b0304900061080c0c03034030416000d19a44250182c1a254855401c411b451803110031207090b010f00c81e840c18005400340c40000e0703002901308424625092a450095001d0140b0f120f000c482048c119034a6000502a20030403204c40b03804599450424002940400240500348 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 683044919 1250 683043669 683043679
    0x2090306130206030f06060f0a020105060907090602121c020c030d0b0d03050f1c020d0e060a06080a0f0c0504050703020a020d080103030e0f0d0605070c0201180503100c020f0a03020318 81
    0x1910742d40030402c203000c05000205906101800314055a0300d000607a0400740b64462519110990303104001d002e040141d0b40c543c041c07000b10001c00c00b480d20560714201030390b1494000384243c200e08500700c5090b81c0306000845860f4007103a014460440f46000500d90034076424001c507100c9030240010802c41d1078a0301124403036401e070214030000035001010b6594600d0035016454888a001182c80f00d02c60140715003c5040b4030000300da8008003402d62114441044e001d00700e1b56541d0b20f000c0800c00301c507554000c1031081d60068140fa400106401d00c5031030040d100750300080ea0079a60b04042000d5030801c0d2095000301e40c0214050506690402811a00c00294903200040354596107014110381e8490300300b1400340d18480311034071168507614808200254401410801464216001881c80c1d031049001c034005081880140810f445000a0500b900c02c02806060394201500c0c2c002c0040241c85480020341c06080c2801c951240184245442180a40c0156546400d800400406500c0c400c1e4501c0c816 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 683046169 1250 683044919 683044951
    0x3020a080106030e0c0a0603020310050d0c0e0c122505090112020c0102070c090e15041e030e0627010f0c12200c0310110d05060a0504060902090306 65
    0x100354884503440c111a1141000604101000744490400030842540e5801c007020540c0000c0d1039078941d00861140703686014038072149469108000c1a06043c02c00581319141d401c1c001e0201028000c00f054019800c4401c4500e02100c602e560047c046049500031100340854942d4810004034290304002d40c3c0b000c0c40c190b85030106640021742807000c10402c02501301e60100d08804924425411035914541040c001041e480d0740300842400303001d80c6404003400303001d80001200089045000240070f1036114180f8250040501942ca04105100009070100f21030201c1040154a8807802410703249014140a03001c0e00c2000c02d8034a2416507007005504010b055a0408a1035911034803c0078102e501c82001d9420400c1703018201e401241301080880521360101558034820800554601039810035400d480b0800040c6d030555003190b0000807404224541007015201d003244076404030354002d8009101451054840000ca070440d041d54206c4008181d001503508007502d410011290311001d203210031808 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 683047419 1250 683046169 683046187
    0xb04061d160305041e0602130e10060309120309020a180b0406080c01090902130819030201050f04021f0215090102040905090309060415090302062107030b0a14010c08040f060207060302 81
    0x40d1501c205148005c5030031480074101008801d404a464002100451107003840c0c48520800840c02c0a80754a071803143c0c030710000104039000340074003030580350003c00c080d81080103514158050000c180040f0390000d003a02020945144d0414244031852100304001200fa1001c82444221201c6800000d850b6120b044411801e030b82c04800341c0c041d100c803100056140d00b880902e4402c03006440d004805035000d2900d58502d05c108404078540c60900980c02403160351210040c002c00d01000f0745029410001ca02648400361080d0000c0340700e808141c1c812aa100107810500c08103103403066910103c00d03500001c0422600e603c1c0e000c0c0c190052411000b440c6064894000100a8840d0740306944603907200440543c02140034440600c0296006801c240d82c40003001c103410340c940c0b000c2d04090415080ca4000c40c01c075a100c1e108840320b14a002d8504090341b803c024425408210300032100e0b0400600c01c034030b0740015610b100640001c0c4402801c94000d01d00781000a0f0400c0034030340001d8100361051060b128 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 683048669 1250 683047419 683047433
    0x609061d062a160b060901230f0d05010c0305091e0a030c02150f030109060608060f04051b040905061002030a05040e13080a0e01080c0408030306040b04061d16030504 73
    0x51842c00060600800c1c0c00102c1c41e00b5541c060355040e4400040006a094284118064554429441111103907a40c0ea00c58050500712540c240b2047d100c0901c0c401002440d0410000000c0740c5080105140c038510140e86d94142900c00031011540000d860b4401d10028903002c1008500c5640c900c408007034400480c101c8203075034403000c860283c20840205400021354075849520040d80d401c9440c920740d03900c50070036000315980c000c3c42480c085516024000501c68443c0350628081c3c0001014105a100e60100304000380401401010884000e00000031004200c50300030b00c002c0251b070342c01250a1610700200003131282011040170541d00100301040b1100e40c4001250191000401d1030b0806480700009103d210505007001003c0304000106130200c6c98005603d104403100036a02c80700030303a8999260a0707070340c0a03a00c50030740e4a604c140081a080d18054025907003013040508001000f95440169a01c0880300b140c0d5003002c0d0350803409120706505194500c13001801c3d242001e00c810300707180d52616 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 683049919 1250 683048669 683048701
    0x80c090c0702120601171c0210090c080a0320010b01050412030e0907021509071d0a200d06090207080306130b03010f060608010e0108060c070f0609061d06 68
    0xc248410002a65000c641d14908003161202c07011007241d81030b42c1c44604174101d804c1d5050306045944203c8195841c0604407900710000e10405501401403201c00000c860042c7c25422012240840018408200913100b00310744000d983c002da0b2180600a140101846100140d281c1c2e101e5030390409403440c9661340c0000485044a215010401150020341011500910003114265201c00d1490034414280c0e4000340c501800c080300c05c10b10314207481c0c6c6008250341c1e1040c0d200d0407144140500c042106000082e542c90b42c0301084a002241c550700007032803806100f0105c1c041c04007902c00031580e0080405940704000181c8500e140440c60b0400075151201240001080d00f442002c4250182200300c501e5004041a014050024480b00c05e40820320f602414181c025900042e102d40000120804002c0d0014101c5030780601130035490b00c41103240f555540c0441c400342c0d92000c00c48822400039040d44140300401d80101c400051008001c6008200d4456840c548503e9500a100340410203d08030500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 683051169 1250 683049919 683049931
    0xe1501092f04080303040807300c0c030c081e060c09040e1509071703090d030c08040f0602060a0e011a091b0f0c0f03190503040206072a080c09 63
    0x1103200c140401c0511255109607008101d19002c00700612040004500c054140948142c0b41a81604070030150642441d200050f4000c64014103c048207029001c5c0c00076511840c040d0074010806c40d201d80b6200010039483d070001c0403952042c0d40074003207105001d038215000c00061015202c1401c20002c109840c0c015150703034a20469484494100c00c80341084000c1c2035070619940c408007498850340e1141c45100341e20642070a404510800e00010b0700c08000ca401c14100240155091091034034115102402c082c0122070090b400c2002054454030030344590000c00140e8000c20581c41e1166184003611070500d04048283e0420040a4400c6c8801d0f905420201040c1c8003c201660b42520350041000b8500d040c030170484000880000c81a0b00c98001d00c00313492094100c1d40c00c1480c0690065580c03007410030810910105841f0020141c1c4101e00440d000f500050005052204070b4a90109001d00e4400c40c40545101e64106014880c00060b0b036002406000c0140c0322070900c81000c0b801c5c40c0c00040503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 683052419 1250 683051169 683051231
    0x90d0c02010810120c060e0f060f09060403150e0712020310050916060503160e1f0e04050a090507060f090608040503040b0a0203120a0b0105090603040212010e150109 73
    0xa0301c5032030360502200107040300f07110b0300d44c11a1a410840f507a09841d00418000601614554241d82081c005c098040030016007243d191003c00c08010010f50040d030001580182d0820002010440e00b41008038a03d40b034030300010351050b840d40340b40c1c0f41a5980d0320440c12212030600043c0981d80114104800400d90180422541d840041e183e08082803500450191401ea02c00810f80755445006544280c03004651000b0a00900c04182c40d00012042d900c1e0340402100342e100c95012083c40c2800c0c0c105080e08201c0c0545038800c0010b03003911030031100c0e0f605a581e07c1c130310300c1d0a03c00c0c2082940c1c01001c0d9030501c0b0b00d000c01100002460100d00340140c4080c805404082030030010104125001402041100c0e6220111441e000751668025099403075580080c070007041010b1818403600c148064142c580b10724200c0c0c2c2d10240102904010400e0342d0042c2c20500c424001c110a0061040c0d00007054003a020f5500c550310344d00c0c221241030b000100c07941d1800c40c500c0c0072545200030070503c0300740200c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 683053669 1250 683052419 683052421
    0x70c1404061206230a240b0403150b1e04050a1103060118050a0e011502070506040303123908060306070509190602071706070e13020d1112090d0c020108 67
    0x41c4403808a00601d01e5140b8420825041055241580d80300c00c1405100c0c159502c1050301d1a69260700e613410038055150b000303404100800c0002e0ac03d01c420801c031601c0100110b560940da000040340000640703072054150950013400c00349841c0503c10b0552040042c1020000301001c038440c01c04d1400700410290500440c1d191800c00c2140604d0048010600101848903503911503036040404142840b4003e40484542c00c003421050010822400341c60000d844141850700e10b80f4101d844500c0880d10b10952941c5407070441861440d000b580c0aa900e024419034501d9102040d110b4042e0113800c42c92042060340000d1214a51b40840c580b0b810260900d00740d51111848000905840c000703951400300d00908820000fa6140c010600c04216613000200c8801445c00102042c0c5401c800c5850780c000401400700302103645000a01d40c0e4045640c28001400c2c84004103c4004499081a4013481000c011074005548078810b46000c2e8000600401340441030800e0002a0020b80f0103103009043c080440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 683054919 1250 683053669 683053691
    0x30e0d0801140a170a050f120331030c031d030c040f2c100e0c0907050f390d030216060501170105010f0506090d060e03070c1404061206 60
    0x50f030540c000c2c101c1d5005200309010140b00362a652512008129000e001d100c40d05042c0c1c01c000302d112080c0304403c10415240d0b50340d601001010b03070081e031105100700d0180302d8120410700c5a41c2016804038030030388406041000c2e6060140205880208102c1200490403143d40d964030045640d1005020589010030f00b20003515911000d880c011a0301d854804694540705aa2441c80f55954810104141555500c0d24001d0f441001d4a4030b4551400450380541086036990504525045e448138241c5003140c1042c0c040c00f0448000c0d40400425030b03451100110080301c04000a115a000e281e0754994120001048100d954a42d6490380050080c164040b80511981c3d0b00c13504102c69056102000304440c2da1141d4098444244c00071141c08651300c1e01c1e001050b8801c00b89110340036070708001d21542c140078001c0c0c10010f07180e06105080395015241c0b000c80001030000c2010b00042d5104090003c100d509001c6844841458032840c01d214074201181001160300c17407911001801e81080000c1400d80082d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 683056169 1250 683054919 683054929
    0x90c080c03010f0909050c30030a0504030f11030d0509040f020a08060607060603021003020a020c0409020901210b15031005040b0411031e0f1506031c090b0703030b01030e0d080114 79
    0x465031f2550803903071025106c8030000358070250003c3d146001c4110320420b8028038019603a8002d1030b0000c000302e10200000d1010a03140c29403220602e00c01d81d400c10050b91031001090500301d1040007440450b034045a4139401c1e290038000c41e0700800d03014030b00b181041e02840b8028624400030704500d020761400901c07003060040365080b07400a160045d01b00314a5003c240401002903001c804405c1c01801121359007921441c190080628243c1c001701105440e03420074402c07a14080181c00c048441034680341242c0d000030b01407003146200d41244072a5440140d540014141080150005040310a00d03240800001a002c1b18603a50450341000f103d200f440e1750540801d103451101c4044800201115036025450000050101c41042e10002650a0004005001880f901c0c0503034409505070010034050201d580d00c004400c0090401d480c08804241d0365081505069000840903030004c2d45401b00e503152540c07d40038000c41825204001d00743c01505840060840d030060007410115141080c10302c40c51b0352a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 683057419 1250 683056169 683056183
    0xc0e0c0d090b04020901060c022115090a02030d2a0206070203031303061b12090501140114010221070f030e04020f0304050606010203190f18090c080c03010f090905 72
    0x8114800c2103822894100b450141c03000300c0b000c0b441050b0940000c1070b20342c46030210032402d0f07a0145c043d1b02401c007064801a480741d410b4141d05040d120355400d18030150440321440d4000c20b903e201801c08800300c1d0041c036040c40002400074013400180c141000005643c0480c040c0c24210001c030404860200307100103050b5108503840654584000704034009000050181c20301128441d4000704401149508641c0028680e00032400c0819200740301e081008102d80c11130500680300ba1b000281a8010344505050201e003030f0404d041107003984c0701440c003e50701081001109001d47d180210301200031703600d1215610804a00410403181c0000003800c02d8010f001c07104250000820a54980b010b031460b150a40d041118180d603284202c101190749940080b0880301c0e4503641404640c00f60612202c15611320b9110f02c19003081001ca01005041e8005004501c8050450704501242607440f040d4010301066001c0e14031003030444200300401030719486090804c12204144c00100d508201420000d042402d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 683058669 1250 683057419 683057437
    0xf02030403120c02120c0616030b0a060c06060506040605070b1005090c0a170127020a0806010810091b08061509010c03180f0e0106020102030103032a1209060e06070c0e0c 75
    0x5800301c6c8003d5407010210340c8078030881c01d03c00c91002d010f184003c101d09030760100301019000742280c84207007c048d02ca5000415441d008403000b15805640d100490001e44c059440b81001800220364101001100b0b80002e0300103140c0c1c241d81c803420741000001205070201810950039940001042e1000c1070140c8048041d400781d400600005603235035040b2043d2070740311100944d1400250445030140311000c2c42a100075035407907643c0180d40c0d61404010345082001804000001c40d0780000001c4118850003903600719046020401b40210350010007604903e07010705150310030414180010000200c400503128051030034a0314080d0803640341030030340301c0c103820320481c840300d6101c0f413030116600c41d04d411444101c883d41c0c4a4070800341e0b642c0320201d00301d00003030000400140d40900486041440600154618200703900451640c24107940c40c01c141c98cd0303015104011400c608810024213801c640440900101541c12130724220b1039a44200144a050003100300c610320700d0020884d040070760025034815038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 683059919 1250 683058669 683058703
    0x6011401120905011d0715050703020f0f070e2d100914010501080906010f091a060a080105040b0406052b08040e01080d03111204031206030f060f02030403120c02 71
    0x140b91030400c0380c060f04140402003142425184030202ca51070000d04a022a00802002d00010040071803c442992046034250b0840c401c0011607003c0300400e000410b01c548100000381809440c00044081144005181c01e4130341c0b0f45408400e40740e00d10300c1c800200075081b108400809540c2d0841401008686411128190745400c0181ca0300780b0300d10540d68140e030401d8035034070f120796202d041440d0b450600340604a111130b40c801c800c01003240c2d40e41000f44c8001e96440c00207020000038012951641025075060b0000d0f640030010049820144902400001c080d68140811401d2102198864640040d4191002c50083d11400740c00d520415881d1f49980c0142d0456803a81c1d140401e104484080c01601594002d01044240700c0d4082e22580b4094040707503c0d8541812200320560160350802070040e4140091034540764001221440360b840654411001c0b10320480c0103045c00e104403442181d012040f1072040040c00017080e000713503a041c008040d80d0030109035481c005400701d05113015580003856507 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 683061169 1250 683059919 683059931
    0xe1302132c01050a030b060303071a1005030606060a05070614070f0207060306060906050a030b030729070f0b070c020603040b011409240102030c100603031409030601140112 76
    0x8100e07072609645003a20001e1415500103034264181ca20007a00388111940a40001c000300000b84c080700d20305a1041c001000da03030034404151182a15920404e0120000161180c200300d80307440c141c00c0c010062702c8240c1c000c100c28a8a00f001c0340c109e00c15003521100b405400b18604040280ce034100c0b400302e000ea0007007003c2500f0003000140c00c60620b104070300d002d40034006010401c10f10920401084078055941d815000d450450103580c01ea00c02d5114204064481502c0c0e034071601c00700098401084409607034030030030111803900030f104615510030010240081100f4030101d600c00846140c429004100250a5101c0800544e80c21a0422000f500254048100411301c004036a01a04a031005d0202070b07200603140b010802c0e101411181807807000c213403a039003416a00340d5200560141c00c040c01100d1400c0382103c0a9880c201d10b078ac00462556844003000d1080541c03142046451000c01c00880742130045440c002500d480d41400f5034080c181d52032100c204203038840c2c02091203012803a2010480 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 683062419 1250 683061169 683061179
    0x70c03152d0e0330130305090f031b0102070b0c070618080a0b04021503060904080313020310020a092705100302061b0606030d0c120215090102030a0b010f0e130213 72
    0x8981807007801c12030504e03011a00b001c0341800d10005108241c81220f0000010060f5001d83d695004241900d8020307d48045414003501d0401c80d0505018940003c5000070407080c000900d014440d4001000080c0c003444003641d096000201c507029034200d0300b80328070503540d501c1030710086900d00d03402070340d00c0d105006104c828032404514081c0950b00940e1f01411350850200c1540551005443e034640014110001402050410014680050701e041d101d00340110345070000b07031410750340c103001700400c0c1e84c0050014200c5802c46070f05801407040040f0b000d020301521000d05801468159100700d100e8440340000c52602c009150304002c0d550080c450b649178950916a0800b140703002c00c01420b14400c00e408500180390000700c071420700d0f0040e65000b8030f4903032940e80d40449500d60041807040d40300f0051100c900028441074035100d14a1030000580720701e030000c120000d07140c00d42415818840424044030409600101c0b1402ca410160740b28044040074030030354402442130004205041441510104c0c0b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 683063669 1250 683062419 683062447
    0x31e0f100917030f04020405061314091b0108040f05030d02041d101217070f081e0304030c06021309020a0512010b093003070c03152d0e03 61
    0x2036080c2c0a80a840100050040c0010b1a480280c3d0030610076026500000d00515040d000030b50300079070281c00690b010801000540c141c07500380390321603007000d40348080241c01d080401c003c014120042c058400c1c064640f00020300451009403000c0c0841e00081e07541c5003400130400403180c103100015011981c0390740c0da00c00320040b504c0036008405040c907018045001041d0b03140411081e1019000f010060305910f54410700c80c803d0454045a0b15201800680c2c0030401202078581d4080c042d400035595514a1b160350300030044004030b01c100202c014418030010030381c4484e80007207456108030016902d118a101502c481e0030030740c0c4400281030000a01c1c90f0440d5111002c1d006c580c0c249032010790380d0f03601c51030340c840b4500507001295040f0001c10b2041003107481c0e41041c69100c0042051080c0b4401c00c020506d4215805a43c05503074120f4100810810054401841c2060b1054102d0070046150194490301500350401160000362400d134141c0009060030b80e020b841c00d01040011a0396132211007601c0d01c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 683064919 1250 683063669 683063681
    0xc010905160303032a030e070f0b0301030b24011b02030a0311010606050405030a0b0c0d0615110105160e01111006060f05180d030e04050a0501150e031e0f10 69
    0x180003a00708164500e00c0100a4901e5440340343d00c1017108011a0116800c50041c5a201c60402440c803d00c00000f40001544030b16001409020481e0744c0d4960450402e24011230014010032040d1140703058103a01d08500300c680c00b480300424070703208400c3c2a0040b2613010010078001e02a6140c099000441b08240c0c10070484108079000c5070003408426035442081c2c1e4103010354070a103901900f09a0352003002500681250350f201c540c1f80d41b401c1c10000318044038021100c2541011640c428240e21041507240c025208100c01b0b06d621000f4007141c07509502e48140c180d81c001d542000c0c81007011511500360301074810a425201300104880102074082c5010000d00b020b80b1841c0d01007a2048050841e140c0705400302e628104a004c52020880f84a070140408818585c1040d420003502606100160b520303405134500402e10808080780320b5050042840ca803400145c00d0304144240b8804c00b80780c2d40c42c0816015806506200c0f038016a026202070682084207808060406005620b80306908103c07652201c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 683066169 1250 683064919 683064923
    0x90c1c14010504090201090512030412140c0405060d35030f3319080a020405010f12021302120126030f090904050a020a060c031209170c0109051603 65
    0x2100c0c403079030780e0000e100840e94004400303800030b4503500c024017042c2011095020001e0640c02140e20302903a90154000003c0c007040c08603414444402c2c0285080780402c001e00000c20f003200c003000b107424128005410032082900c001e0149079030040b0100d52a0309100014a60030203d10701c0510648580b40c218000d500884601015088a201107204014840c003001c800d2065a0000d0407241811003000301104168103180b40d019a91030f21840300e61020022040c01070803a180288038400e00d038410070060700c1c0140c001c03003080540e426003000f0300071080c0110300000d80c0548825090039511451400a407240c0350b9403000d10305103000002080c582410400700f41c004421030b841c000c1c07034441c00015128403550250300c0506806100141c0b0b00d00d814a030f6030b0b41003803103402203800d82161a804604065072507407000c004111a0f40c9083c0034076400c80300420f2245020203081000f00c07020390341c0b540d00c030542c40210240d030a0f000c114041140b109501140407150050100e032411001d948107028002c521b400300b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 683067419 1250 683066169 683066201
    0x9011d040e12092b0b090f07090e010b010807021e190c06080903070b16050705070b0301090b0d0507062a150b030a0209070531030201111902090c1c 65
    0xc0002290768100c4441411300d0900681c3c0b000b406515442078618018100d04070364083c101c10106007003020401f43c4024100c01c0000710300101e0404402c0e00311100700031070605100f0400c0030090a0360f804101405840300d69881070b0110803590380c007903150445841c000040701105d0000340742480502e1190b20100c5840b80c1c0c40f4002d5a55034810340340c4902480000801039030060000c140b80408000b00004031820618245080c01070316111945460a151310515519a0010051012902a000f1090055001c0d1416881c0c03140c65a12a6540c481c2c0b13214070010041da42c0d801040380b9004000c0141c44400741c48400300b034018141010348010f440c0c070564001d22450901c078450a414045400300c40c583d0010902080c80e42ca48070291802d9224101d402200003440b0800a0000442402003c1c04541c05607184202421403001410b02c039640d14000c00d00d54055250341e039003907008460284103c2d6054660803443c3c0c8605444e02400d003c0d800c6031650500c84034664400c0c03100264042071812010001c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 683068669 1250 683067419 683067439
    0x6120203071d15040209060d0b2803060b0102010b0a064d0c03010f0614030303010305030a0f0c06050c0711040204050105070b132109090209011d040e1209 68
    0x1c0c620150701a040741d88020250424005014500c014900c03da10b0a80504094035050f07900000601710750102c91420b10780ca696000102c003c1c18607401c00300400850200c6904403a500b481c58401c00909444010300d11a00c503c1420040c0c2d100390051441b54030003401c14103080341c80d8000585001910aa001558204503100f0b6184181e455040428400091042000e09812005c0b4410003a031404c1a981c25101d0340440c05840d880901c102c02401d844c007400010020304100c031507031055001c1c0001c00d10a500070310052001c039401100301d42e04031301d59082042d5101d05015040d11094880000508006e151134200000007081c800248401071048410011656140381003000303e005038024079000407001d04c0f41c074000031080b4425a41025042e1a0700e0714460a40c1e86140b40701c1e2060854451145141d100f02c0b42c40d81c1c100c0150406446010380540c141012000001d080c400c82000304170344121a0a0a1011620b0701e60104821031440c0f016500380000300300c103182881d88a03003006c03402003803168 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 683069919 1250 683068669 683068679
    0x308180307060c0b1017070e0105090c121e04060b100c08090d0212060a060e0c0309060c0a032c240105061b0f0a1109040506190605040612020307 64
    0x104950041e5165501c5200c3c0980c080d45540c25440e000501140c1c221003004000306040782c82d050381c107000f038480000800059040c480484903402042e802203029040e40310a12020500ca5000c0d03520450080e001510710b5a2410a184180c108107000082c6c100c51141c00e10003404843e41041c814140b05450707805204001040031152200c00c0980a890304e4270900c441e641900d4000c3d85003130802d00041286001002083d01c5604101d07095500c001216035901c001c00c0f0303c141c8440c441754042c6202d071b1070904601c4e0521441d92100c500501c4a0f0310800d0004076031911038025403042e040b0000c03105120704c080441c0c250401800c1007000e2140140d00ca40c410014080300c05015020a010180c07420311103903440e06080c0403060300100030500e03400d46105450441030104000083d005014500140740314205810300400090503110801e000710000c05c100720100c0c07030001e40c1c2034002c0300100268070364401c94443d03040144250b8200a5015090400000300b41c0d000c21a036802c128003c405030388410b0b66803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 683071169 1250 683069919 683069923
    0x90d0609210234060e0406180c0f0816030b011403130507050a03031d010525030909020906070215040510021606020f101806090f1103120f09030106050a03081803 71
    0x203c24000d8035410507505005192060448081c007207006003020511540b5901440c0d6894103400c84901055520b19100d80c031250300c4412121800e060b8201115141041c0c0d485000b020510039103801451b03128607100703500740d100e0300d10702034070a10a5401170307100c2c20041c8030403040700d04488054889225052007c61989800964102140e80c10f0311120103061080d44040000c0360013850050510909220b00800ca200001c022800f2904002c40d4411036005890041c1c0303211500d8121703612452040c44441c0d495290f0404542e032003901100c2c0402170011812004035684103541009820803401d400c1104000d400060315214000b40700e801c60300c01e94442000326030f0b030740030710809400d90b9001085500213542668440c03501160920710290b078405054a802c800e0303c0d0050021140b5143c2d4100c800305200c2d60818043e51500300f10003814001304c01182c50f2005000e5072030022180072000411041e503513025030090004010150030075040c50b9880c02c0140359a08040702600c0400708121940300c040c900 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 683072419 1250 683071169 683071243
    0x10b1b0d0504060320032e12020405060d061e0b061201060530270d0e040b1002010c2607080702010212041b0b090d06092102 55
    0x1140d031864203252a141003103010f00217902e00c6200e9121003001450307441c1c207032100851143c441c0500180c1c040c0b101030a10303441141e0381c010308251881528002e20220198007407011a0b40d804403408500f0391201c00009051308440070000301010303e00980701c0183c501004074001c20300c98143c4100841c0844405000b024429100a008171642510041c44020b0141001c0d1080a04c00542120b00c3c040307401d180102d510600080381c2142d074040e002c010702d00100340200c244444141e079104a019414050055803400840c1c000e00c1801006a031014860300c13103501c00c2a84000090105c0d02070648000c0190081c0744c10000000090710700c2c11172852808810851066a0303034650000c80d00340c2e840703010850341c651001d0710010455408011f055025804148418000c038010842440000301803181a605082c4591000900a206000c04c4040e80c0da0803003510a5107070010404204513084d0701d0b2003d1a4503c4110300361008100c14142c0b10000c0d40055450701d41d030b5115034094820303084214100c4d10144 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 683073669 1250 683072419 683072443
    0x9080d11030a03021e0a0e1c030801050f060d090f020916090506030403051b0709060618090c0c020a06050c011512020d1e05010515010507210e09010b1b 67
    0x200c02c0240d0400548254010300700c504505810001c41358281c1d1a20b016036101a10020000b44030055091300d038981504140305414000e00d04690800056401404150051180d9445100d500ca0242c0854a039002100c0001c0070706071080042101c00c2c03900c161041609001a0700510300c80d000a16100f100d04042c602c914101c1c2c0301c0100c2c07103107440200000c0c2c1c0c0c0000c0040b402c0040a00500c58284035100e86421041c0242028103440e504068081c2c007141c10541c45501007018001c80e0250321408114201c090b600c0316100400e440394002d10540310a1410380300250130519621000034201c3e03001d0098008800100000d1003104508400480c0d21049400b442203414911110440103180c81850441180c0c400c403500851200313213000241030f00214090694003a5103c0f0104241c04400030050380b00d017042402e0481c2005000d8a4064004500c2a144944d65030b05e12751007642c003402a0424180c0a00c000c2a00a00390307140c0003030f1092a00000e074142d800b26503540c219500d500000c01c080048107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 683074919 1250 683073669 683073673
    0xa0507060506060f0313140d231201120501060905060109050402091504120b2514090d0c050301290d030c05011d060c0304150e0f0a0309080d11 63
    0x21515000300521016003003a41c008000c02415014a444401444c80b440310241c80652a4400d0b0921007901000e22414101c1e94100020124005421042a881100541011900e0441400044d10b2580300300d41131100414504400050007082d00d0b4981c4200305c1c45100280410303030b80c80c045d900944109030342990224061580c284011b0805601070600d001c1c000300701c081620140c481c0c21309142c1c842d4000d03902c052000c42e0084180100604005d030040f4a404461802581100e011005881224049d004100060040200c1c0e00543c005541c03030b40c88014042c004010051500d1210104140b00356802942451900c50900c4081c80700c2c003585c03c80044048451401c80c0302000502c91012400b102030100c0e81c290180490403d102c4d2050690602c002e00c401511584186454024020b08543c6402010400c200001740e007000410802a6244008101c0302c0250007400d00f890f9420191030020b110f604881340500d5442410341044403035000584455030102c400c01c440303056803120307152510303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 683076169 1250 683074919 683074927
    0x1021050414100e03161e0b0117060f062101060b09011d090a020a030906020d2406020307060c11031201090e0708031c1805010605090105042c0c0a06030e0105010602030a05 75
    0x3820305100c000100c24131409503100c00d14030310351b140580e00e1070b003240a03120300c0b44990040c080819413001c0c030551001c40400071325a910744605000304080000b00b4042c010003500c818031078203030301c00f101c174915448644000f408840d46442c42c0c1c20709a040103100a0004180c80800003001c80c103c058460a0b00002c2d00b551030701c5c0c0c1d441110201a600c01c060360010550303185000d0300403075110300c080c03d00060813810100786141c3d02c0440d2181c20300b80c2c0c015400b241440c20410800035400004888115901c410042510030741058140c8941e0122104502d4901001400f0180403c030244400d060301c1003000c1c00c1240003c3d10306003940e00d48182c001c1d08140d510400c01d804461040703001481b4411310020f030104500c40d001000e0840d0042c800d400316030300e0b03441e44414011440c16003066405444261010014104540210000380c0d583d0508040c2c49031010002d412209d8051091010a49001e000404041e03540c400060041150010105c1f040d440d1900201e149031011080743d0043c0c095503211428 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 683077419 1250 683076169 683076187
    0x10050406020a030e2206051509060a12021209160816290c0307210e091003083009120c0715080108010f0b1021050414100e03 55
    0x142805022684441c1c910303030324030b002e0b50800010f040e02d41700c201e0082803807840e280a010840b09040200345403084180b104a203141c6aa00c00c1d10741c00074041c0360080c2040ba507904d03007000a201d85192841d41a4110040161441001501d0751051010300c4c0801c1140e6940c000c2e03661182140341800c15903505602c0c040194010b00e1803a1000c001250320313854a03c01407204c40c07040e150700046a4448607000412644240082c5021440040740c0040301c9840d40c7c2016800240509840da0141e031003a0204004101074100380306089000d164407030f59941d59909a09140c82003127030724102461544035080b40450003032000c03003e0039004881c410010020319100d0121603203141c200da0051849885040780c000303100c0841e049070000700d041c103440f46510f650610b1062402d41e26003551344081d40b8100510b28009440e10000380252508500c0e14229503144100e03c6465443c174030224030541030030507041c002072100c03000001ca0044035040881e0028103000a03110141c8003072003088030a5070014010001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 683078669 1250 683077419 683077427
    0xf060105010c1406100e18071a16110a090b06160212031315030e0c040e01140f092e1a09100e06040603080324060408010b10050406020a03 61
    0x102041c807542c40125062480c026076407400700115148003004490703440410003402c161030641d4211481207c0401200c1c029450b007640c90b6401d100c0d0b40c11213050003003030040d90850002942c3c4040722018010400c052a4140121000144501d00d8494640031000003081c00b0584030300300c01d050b0044d004074108542140900b0342c47c0d00c0c2c6c50040e40c1180c1003c0101500c1c40c3c0034401014504050180c10701420308041d284201e190140040d00c00b850714000840c5400800040e000350040c100303c5020a8000d0b400128901401580323401d0381c490640c00303040c05055000c00c44803d2107040c1c1201240c0300f9201c008ca01144020100c003424102000b084a039102403107a60300030004040c0d07154040356011002801051402c041183c04608414500c1410311111240d0341c0701035002102224188607550560f110314245101c042d0800702c2080c01c450844898002280842c180c0003802042240c55940d50f01d400ca0107000701c01c595511803580e00001d50b58940c020020b031030980d100c0c3c3d40207103210160707650199 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 683079919 1250 683078669 683078687
    0x2705030615030a020901150e01091202041a0607060608010f02030f0f070203070f050604020123180307090905030d0b040203011a0d090c15081008151e070302030f06030f06010501 78
    0x19402d801a100000050b072140110705000b401e4502c03491160000e441d50052580048d808924104802188100082e2205a4000c48a0fa4044400042810880a0b904440600240b2858010501085540c18025154825001ca6111100a00c912040204035400700d00c0210791860840081c14040340041c5111b003040345e0301000b2030040300e00e400d01035140c509600340e1914084031903a020008003c11564095080c1202440e201d29020491032220440c541c54000c2980020008000200012032940c3c100007000042044a008015400d46420056120b034005214020518207110410b01c1e24109442202d049070600080011809185449881c66a2009142003103107511980114041981d4070340b948000c026011092004500740d0744083e2065100411012001816800c10840341c4004540c0c0e001e800d00301d1660300d103070340d940d031110b00f02000000c4c01e80c2001d1410b4400b0448144e8040d4011401100301012030046c0d80d81d55410955a6500c0e0307001c0600b82e40000300104065400790350f02c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 683081169 1250 683079919 683079961
    0x9030f0303060305031602030f0708030a0302070218010801141006020309090415060e0106030e010905060f0c0d020a0315080f12090f04050f040b0f090a08090406090c27050306 77
    0x40382c120340e2600c549107950800345102c109502801c901900718602080401c1c000c660820150660318034011000e5100d0046100842c141500050141c0455a418030b180c20940200140080d035561110007490003011251030803280c000010300410014108584007101b2078009900543c0780c510614280485400003400031a0b005602d600c02108251341801210090044410032a5003036141000003001d80f5074421528a00d80d14011400001c01e0000c1b40c9540c1c8a1603015181301c007520b800c00c2803580f83c410901461409440403484001e55030b071642201449200f104000b2030200d803120070341c4d42c641302c0c0003100f0452a40041c03120040504108040c0c1080c6900a00310381c606032281c0089016545c0403124503800300c86940802c01041404140c1c071b5080390303240d030480c181072601000c0259144510351002d0480742d00407034854200d0b540c0d504020040e0051200a2000300b00748080544500700d078070703c1d00c40c0448686981c070044a00c9216080101c400080090149458444050404601680c0c60b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 683082419 1250 683081169 683081171
    0x3060f01090f1e0e01150311120309060c030d050106210f0b1806030706031415030c06040e06090a050c040e0901021b210405090103020907030e010606021e01020a09030f0303 76
    0x45442c80829815a40c05102c3c3c6801c80414a06246039105084607540c002855005290301c0f4144046940d202030614034401c00d40c1c05584000402c140141781d0b004100000360300c4540012036840140c404005002e082d0010401032180c1d03602e6a0b0152506001d0042c0303062029107400c0c6482d6203081c0ea070800f001c45042c0a10005100d07402c000400ca042d4010f0066600400c1104244901c40c01c2c1002090010f081c3e038901040441100074a803e0000000740c49030221402d150140000703a50144003146061304010305841d519541e6404410110b001154603610800802c1c00148110065001e024800c004030600342d49043e0801e451b69200410190410b4003c0d0750038041d02400210000d09042c01003050f500914641c2094001512485001128600c1507441804108842c0d22000c04040c1560340c101e42200d19603544180840043c544837030541ca0a40c2007000009240e80c000c54071000395031a03801a0354505454107103581c00d07480344082c56800202002d1080000c20703881c0c0d003222425482850 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 683083669 1250 683082419 683082431
    0xc05070e0c030c132d12030e1215160e030c030304050d0c05040204090b0a14030d0f0e040603080414091b0a050f040e1509090706231209060603060f01090f 68
    0x1001d9945e02c803c004a8100040c410113070009140d40b603a000000034043d0380c42d4000d1545180e98000d200204059015018a01340039028180c804180a0380d5241c5503003410403401854102a10351407100c4406102010952040701514103040c0883c01c162484005402107182c14600f8090080c0c0e082c1403c4199000720761003070003052980c0d0714001080140030920f80820450445c0c41002208413880d03010400758002000d9075095034801103800e21a8101c64241030800501c40b407020740342c00044804d560b80c4a45059404001c12401c08007420664015400d0040e80c000c00c0d40500200c0e59050301d140b0071811a028640a18580c1e0500820030349006160140c20240035052a90190708590821000b000141d0f0070044800b200c94010b80302d4202c1201d4004107424940c547e80c4c0c64024a000d1101013024807500c59444c0803404c82c184c0101920000a150343c1d102641c2c0c40307140b00c00241c454254901407a00031902520380050058011910103440140e10f0b4030b050442e0700100203000454444e83d850368 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 683084919 1250 683083669 683083679
    0x307020405130209010f1508061c0332030f09160f050f0904260415080f090c0a0b0901120507020d021c140f0403020a060c05070e0c030c13 61
    0x1009840c0a0780c00d41c0910b460150075807040040c1000160041d4901003940d00c2c08200c4480c422021f00b40460b800e081c514041d866060204000740c60450303068810114055058080551100f04110450400040d1030203140c01190b0840310b080300280f454602440901c04142803221400026400110010403102800d0f215074528003051440d03440301020f42e484103403c000a081403100d042c5c40e41e4007151803645524165403000754814442200c1c0c0091100000b8440c1d0703808283c01250b0107004a030840c125881c903000401000e43c0f00454080c0e26800c140760215044441c0014150403101000740100c181500300100300c040c903084403002034100401030036081003102c0d66229144c0900401e6014002c40e103110400a0301d04501c42c03400f01900400350300d10403031665114400b80700c000c0020001a50303e900460300500d80d07000710742010390300c00004038001030060341100989a1862150050b210304a58420038803e002c54202c500380c035041c2c0104002003000c1048030042140401e1103000c890750070344030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 683086169 1250 683084919 683084921
    0x509070b2a0a03120c05030a05100302120c04180c0e0c070602030a02090f0f0102121e0d06150e030c010c0501090b1612060f030201030207170d020d0b06070b0103120203070204 77
    0x2028007642c001c41c0c0d8082c2030540c0700c500341441600318801444132100d0364200070700a2000600107410281e48001007601e01441e560360740011b6800804003204c0d1600402103944845031661400d00c61480d2000150a0400e6070302210306490b0022458081146401c0301000e150750010440707440c2d41c01c1002241e001614034801346004070703082c507401600d03200d107a002d02070591002d04007a88183c4401c640200580e0b800503000e4007181c40d0311001600c0342c408402d44c0650610180c444158100c01081003074000d0761961040382102c012680c1c0b42d400c400b0010b4141d9025920301040307034041d0801e004484465004130702c3e014a403441070000003074040e807039101c820b8050010340700d0b00c51010540d0000076409078460401c01000d0300c0445c08000840c608442644a003940b440700906058021949806201c09440c034401c0c2040301c41c0304143c4e10310071851401c009600075840055020f240c20581402d40c1041e2007500d4000340d001c812004181d003561101140e45d80303c1c101f11011840104072000060300c403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 683087419 1250 683086169 683086237
    0x80702070b0a080402100e03101d010204080c1504060215151003050a0b0a0b070f0201110d020f010f0209131d0d052107080f15090f040b0a0509070b 65
    0x1c15922031405013424410070503403c1d45294401c0410000c9021401d10b6500030601031a001020580000c8014000e1901c80e0703003100c51084581c0c1c0c0e500c00714001422160206012403004011903501600c0e1080003200e40e1070b1700490042e0302c01640001603c4070f030301810031000ea4101c40440341020401805900260010000c15005400a038a40040c48408080ca004120902c0ca044804105260030010601058050200041d00c1d031200c0040b041e041d0390003050890a180c5114043d1107403001c200c200a0b41e2036615204010440d864588141c0c0810801c0c400e031011814003c00c500658002240540c000d01082c002d21800c48200440380c2c440b007074082000c44c91200f0a901c455858010308000812807401d50140e0724a58100e440c2000205c030350200000e540140300d0340011030395403580c88200c512640070040d403070303080b103a25802d0000144100f01381620403881040c61412541d1441220340940e14240e90900065000328801d00281c100c1d42e001d8481d0001e03d814001507244211612600c9820b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 683088669 1250 683087419 683087437
    0x2010203120a0e010e07140603150301060609030b09031602060c0106320a080606150c01050408030412020a0c0614090603042411040e180f0105150f060a080702070b 72
    0x2554003e2050300c0c9000703008030140c4407440300141504030f02d402c0c0e140c3c82d4105505080c40c420140000040c00c0c07060110000f454940c400f40080103001d88890000d40400d045000035582d40300c0031400140c41150001c122641c100306900c0042440c101c503404c1c404d09800c01901c08060b9503d41d00d0100303099104062050324404440b404130982c0401e621a200301d45070080380c00d8003980e408034040c04500030025003150800c000f074501c003c031b520b4076190f404041d001da02503191503035084c08244000d11510300d000d0b500585c001c1081d24000d40d02c0803805d07681c92100e80c000820034660550208039a6006030301e854910100c69100d185402c1c0800d0001c0e0140c0c0c812074bc00ca4041d401c841c170018401205404038101c4000044041040411700823803d541d178090741c4100388001c1c1c20326000881c050020400c442010220300b0441c0d80320a8800304c80c40c040c010031a000c2e24081e50105119015291800303080092560107051a0700e042c26011084500005c010041c80c15031188000c0058001180801008142 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 683089919 1250 683088669 683088671
    0x10050f06010f080f011403070b04060f110102090d030806040204091b0201140f01140d060920031203042d0f0308060105031501030b01121406040f0912030902010203120a 74
    0x8030300000090b0000440789521002c0241d20000c005081070010780a5042d215581c110404542d113090000e4a00400c64106a10250001c02e0020f040d982000c5221019120380e10b8460a0340954000c9608038001ca00407a40c2c420340b01c202d90000b29020b080b000e60816005400945000c1d121a41c58081d11403030540e070281c40e62291100b40c501d940c20b105544801030041600e00041c2000042101d00c0081030254020850784820440400c0d55000100061076038451000d1085205074140755030307510400d02040781c0c50803600781000401c4c9008103c002c4d00301151418241141c5660701c07841460480c404054192460358840c1007001c512281784d01080c0c500c5800704059004841c40c0c010300d01c850240956041c01403c0c0107120900c00008440416194207203000103850300640012540c0d00c0408103019582481c0c004410050500c0c00d58152044038140e0341405103602c14260702c0d0031201400ca01a0140100d41c41c5514a02e20940014450500500c1107909140e176a0341c1600c20401c1c243da5041c81030b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 683091169 1250 683089919 683089921
    0xf0e061c0f1119020109170c010915051f0f060c050a140f0f0703081b07090c0c05060f0403050906070c1a07060c0206010506030c1c0908090102162102010210050f 71
    0x202400c031600c0c0f58102d9588000d010b8044159180010504144440300110001103003400300003d0940c403146d502c80c0c12040b40c45900e00000e0b60b9000402055880904001c20104552401d040130400002110b0314488140c01c000e143c00400c44542c000000100c0303190150301e003017502080f00034540c0d0f5404d41d009005443e00c0d00c0c01070109031410441c80c2c4c003220540c12031801000445d10506c00e465055101a961548856035460054104121600190905c40c6894000b41d001c41d400780008900b00d00c91022665280c0b82c016210306401000c1710010000b07081040381d03910710705165001c5d01d0524420603c01148a0b12240b116000050480711210080e10100c1c00710107118541c024aa1401e0060028151a504210201e44607120046c0b010a0202000410384100c044044a040c81002c0a54041048641c54503240da0a0340c080c02c1c0d45401071244221410301d19146200b024103c4240140150711480b0900c0d44481030844c002d001d0341540180c0740c07010740c0c0c981c19000d624420f0045c9002410a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 683092419 1250 683091169 683091187
    0x120201030902040f021215030c010e01030209030d200f10020c0a050601032607030e10020a020d0b010303030b03030a1e0903023d08062b030905010f0e061c0f11 70
    0x180b01b4018083e43e01701283c043d00e200b81d41c401040303100c0100020b1030702c400d525118000584c06417181d16051601485242d01034504d165010b03001615200c24041d4560550b03940c8401195507280c2100d841000750061035442d41c5000165008111505580058510085194907440d0074290240c1c0241c4100322003480b00f201e003070750945030b500303c0042080b07100b81000900d4038010b050501d101c561600803c0c0780500c0744900d1b4020030841000d1913005140389880102807524a0f9101c0080c0710480210303060506080483c600423040d13030103089065440c480060325940d14800c42c600c103940d09138244107017520b0200140c6c079602c0546000450105940d9600c2110300c0030b00c0308071300480b140e108c426010703920013240059005034010341041040f5400902d101d40e2580f0790b41c242c3d03018480b141428594060040401d84c02600c1d080490382c00340c9800140080150b000e17a164000340010590145003084800518280e106a01d2207a00d144080013802104140a40080f1450f90003154a02030300402c50b80d0f0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 683093525 1106 683092419 683092447
    0x50607030f06210c060801080a260d0903110615090c09060309160b040315020a0e060d0204180b0607080a0e060d060302091e01120201030902040f02 65
    0x7490b6110440b0010f014a030f5040c0481c0d551200510001e00f050007461050b04a5009038003406010b40b4580d2217103440705066910380c40388520040181c00c0c0115036400340407091240100000d0b001120305024011f4004c0d0070100405a003c0d8042010300400700c040b8846000e17098901c08030301e1b01d4000d803c0415000d80d040a039040035000c41000b140560000e08041102e4541405449050311039031201c0c550710036400b014050f4101903c03500181c80c0507500918040e0020300e0300040c240300000016246d0380c0300400c903003021a00402c044c03003105142c00003440c0111803420200040c0010ae00410098041c400010f003a42602292155015000b5200000303214001812580d403052070704031410050045000a80c00740003100001b0300c44035603810030603003404800070340d06019030301c0d06104081400d001d0301d007241015111022a80140c490340610444144895409602d0781e20034007a003a = true := by decide +kernel

theorem cover : BRFrame.Cov 682913669 683093525 := by
  have h0 := BRFrame.cov_init 682913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 682913669 ≤ n) (h2 : n < 683093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
