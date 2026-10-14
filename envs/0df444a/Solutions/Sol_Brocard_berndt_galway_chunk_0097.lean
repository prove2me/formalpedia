-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0097
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:49:49.316518+00:00
-- url     : https://prove2.me/submissions/e95166f2-a279-4151-b884-fec3ddf1176c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 17266193 ≤ n < 17446049 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 17267443 1250 17266193 17266201
    0x402010e090411010f1701060e09010801050403020a0201031109040e030a120501080d0c020d0506010902181f0e0102150901140105030712030f0302070f0c030203240f040f0203070807050405 83
    0x10940c511402150082c400f42c0302411041d004440d194a440c940400708403021400851030a0f11101c1d20b8040c104ca601c07006821403100c014400115816032140a55a0500040c000800c3d00407840501180e02880c001c079078085060321704c00b0039229130103400d5000340c60100700310b050f0500417004d801ea0598a580c1d00c00c025030301c440700c8800c0d51020f0240c14170f00c0d00605410340106010b102002e0b125031004d42442404c03010340d1191810300400b688a0700030b094000501820541044107030080b079001c116050103000c8040503246170564031204030b01c418400300c008402001da00030012414030348001c41140c1c0041c40c001050601030040000c0030310146107640000310351840d02003004010340300b6850700c9800c2c1440d06e8604680b01004040c8a10505a0811a0300041101041480245805150038002c0c091441c410b2602c0c2402142c402d050307001c10002e030600750842124485400c511980c0100ca2141c4444c10320780c56034400f106000f903140c440e00034005141c01d808076010007107400443d41000f095035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 17268693 1250 17267443 17267449
    0x30f0a12020307110603090a0c06020706030606050c0d121803020307050706030615080a021204052a0f0603100b0c0601080d170408180a090b04060b0c121803060703050402010e 77
    0x144450040000303003000400c09003402c048000e5603105187c80708498010080d9218420208440d401401c0160401d071070901c015038050151800800036442c00e0b61402280360041e43d180c545114040007001100452102807015030703000f92003900803e1140110040c11450081e50383d41c84181c1c00c6a00b401034a600140c030a0203846044200c4814000b18044040390103012501c00d5401407000316241c3d03081c000301d6070945003008814031980c8200003d11102c103101c028103403003400c02a46001418204a8420001d40f01e000302c2c0d8440c42001d88105403280c840230303c6001c2041e181d030482d07120544040b4004109810004a844c100d50080082d2000f081c1601d00840c0e400007060750800d01e416520001c9800101c0141c002c114080b03000340040e0061503150f0000d400f400c1c80da407112030350a49031a8465114070f410311881d0010488004120b28205a6100040d2140480752020484105c01328201c0c42401c50b030b88882102100003002e441e0b407490802405401000d040e40c00741d0010300c5800f50040c1031300b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 17269943 1250 17268693 17268697
    0x20c040e03030c03041506120c03060f1512080f03070503060a090c0e0d02030c0901030b0702161505070302030706060b030a0b09131704090207150506061602040507050405030f0a120203 81
    0x241495482861695907440743c40e801c02102e0740d2100b0706a0348840001c0c000100c20740d01e090b0144274008255403245035082c80c0050741c0e00c034400d00741110300c0c2a40c895612680c1030210000c5480181c0d6081c4170303414908104d0158050380c101d5406403100041000072040e8044000c1d444cd0504440f04e681a9407103500c10bc0c11244802c01c080c0c0444d41c00b03404c0400d14584201030352100c03480101280c1da01c14844010828428083e0700071074203410780d80280183c2a8040c0504610465001c581020403807414120309561101c5d0ba400405101001607450103062003401100c080d543c00c0304080c804190340391342c0030505034400c51f05418400d103004d03106861071034039100703160003000e04407003410961081d42c41e180542c00c0241000041030724200030000d14a2054000b43c800d060041c4080c0078810440a2024141c98001300000e100b0102004124184900e411540c00140d4056900142541c2e0341c40055609110302d0308200c1d410703c5120390845d00c1403000520200005d102e15021034a801c0c480b074040c0e82e030b4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 17271193 1250 17269943 17269951
    0x309080a0b0a021e0a0f0f020c01090512030f070c060201060504020405130e01022b0e0705010804110103020403080429090609041e020307020d0206060901150804030c0b0106020c040e0303 82
    0x40e071099070105410048540280400c801005040c00d01000b00c040b000d50681d10031000311020035a0149a0854280c01000a000345c1080f80040c045000202d80020880ca03450b0047e0f5110300c0c84200e0040036443e0400c00e550700754088a41c01036903131042e414002d604442d0307403003239070015800c02c2e0340880c03941010300968088480207420000c20141190010b0090b161000c81e0702140e650030300081c81180900c00c900c2400c455007082060040356803440031000d40e103102c030140700a0340c0310310030420981c3d070320619641e4802d03042035a00c1d016200c140b004030040e100b150b0000d801040007140c0451020504040b0784c80028458400d4006112280c0c01c482070382c06180c5a06500c1181840f03001d0407414241c02001400700300e0201c0c1d0031a04240c0d1107a008a0f00142c5402005a01c00030b12040304680401075960840740031110080698174210a120703d200c4c1c016000c40402c100200410201402096001d0000390b00112050482da11110029a80e2920a20b0144100d0030300e001c0b40c007003200c040700712401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 17272443 1250 17271193 17271203
    0x1080f1203040f050a060507031e02040305030f03090106120c08010b040603020303090f010306031a0108100b0a060e060915130609080a1704080102070302010209090a020307020604021009080708010203040309080a 93
    0x442e0b441c3e803a00703a00e0310a990002d41d82030140e25000000143c1a02c917461107441d00c2d490018508102130045038030070460b15240c1580034410003041c004280000181e5003441d100c00185030343e95031400350b05405031103140e100c88504075a108206c0700300021007108001b038407003041c000c0214145401c00c000517548a0b100181d00f64104100704079007801c2c80200e0380c490301d0042c1400710b070f41c903580d503140d22040c16441e0b101602d1800300401804465014403440c0001c1206035000d102c6c511900000640ca0781891062800384820f00d408124951242415034209501c010824420b510840e0200b511a83c03040505c0c10300306c482e010f00812000e02980180c02600d5402e8010070115009035a2a0344a070028025103c402200f07100001c0c00007401d00041030a0791081c1d0025031245500d07020703c0103400e0080e0a5298a40c018000c0048550380021801d504c590104c56020a6108180d425070303203000c55801007900c50080b0b582c0400c29100540055029030b1090350341c2d4514613512101c403625140d0035000148 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 17273693 1250 17272443 17272447
    0x601080f0601030c0207081006080c01020d080f06040b060c07080c06070804140102120d0204030209010f0503030702130e0304030303060510080f0f0606120703090606240309060207020a080601080f12 87
    0x1c46035200343e00941143c2c07150b004440c500707500d442c03800e45403a06401d00a522151550303014004520b00f07020f800350490302800100b4451094400103008070000078a101c0002140200080040e17440380c100c9001e200010b0642644c0c0c82145c1e48541e01c40d01907014240e144d103e404000c0b041c0f820000b084620458005084c02d00745400d262500c1c0201c20300300c085904510850381183c440140080090844240054005996518501c107000781114140e104400a450405040129072000320407103c485070304440f41c2030300009000b5058002d1450210150082c80302190120402d5016800903050b907800302c0e036509060341c0906045070580c0c001c88a04c0c0e2b55245030f00114903050402040c007500040e00501c3c3da81410200380400b18440000c44240c000039840348484001c0c0079881c811280a007100b03038981030b5140a0556102c01c4c0b100005015000c05541d503903250180b24482d81a10351141e0b004111034074031507540b690566590400c1c010030700f0314080c802c042e812900e800250aa8110700303000717203030b4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 17274943 1250 17273693 17273701
    0x20d020d0503090f03040b03040c0504110d02071b0801020a0e040c05040608070e0402030708010e060f100507020d150b1f0e100216090501090b0414010e1b0d0c080601080f 75
    0x207460b6000a800354050388644c03600c1d14480d56052001e00050300380c0701c0d20540c880c941828100a1b200d05580a87d0040b07181c00750105035030207441e00712049582c1001c40565102d40718a441300307807503c08010b004112064603001103940b410640013021200d216039200500c1c444180200011141c0e091002c0000c68000c000030844940100c8a56601c0402c4d4104032070100001000708050307a00807a200b2001807071800050188880507181250081c5040d40c101203200c0d481c1000c50803564030300c0018020b1010101d0faa000311740e100310740c0b15205644690360088a0000400300d002070034142805c2031044000b0756038204282618180c10001490f166200d05000c014502030068512420141d503003180200c180007a10340650b6030460009004c124400200c03589003040e100c2c00c40d5108401c407845107040c01d501140725160403d902d4190f0b1284004298540c03503042c0e48d00040540d011410746d030024082031401c05800c10364040b40417840e85403100041603803840011511198100c0c5c40300c0d82d0b14942c001003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 17276193 1250 17274943 17274947
    0x121103010510050c0d080f0115200c0d0506010602060708041a250903030806150409020c15010b120a0c020a060e0f120903010c0305070503040305070f020612090d020d020d 75
    0x40b1140c0111400c1a07884e100202c2c00180c00c0441e407202850100e4046010b000d50103611540d854010860341844020204000c0401050801011110300000c44409100007141c84140241c0030305c182d000b00f17036407495003141c42c22035142d000174801c0c0800f50140302c0000d541280500a45442160300141d048070b000e606c2280c400303041c0ca01611314084015038a440748003005d9140300703901d42200306803921032a0501c1d5180080040b0340c002c0c020b900541c015041080b1410502c4155810780b5804080980c0711a84900fa0601e071042c41c04c42c090701052107000026449001d00c001b040700141c0c100043d0580d036030f41d13045201640e801c00c1c03600700103a01c10140000854590341c000c1d511414480e040da0105401d09c8001494036013024109040c05400180d115a5490300b48075600504a40d03043c140801d1619040141036808000c2c006014030200181120401c03859141541095900800403511440e0711614650000350460b0f01006c42e20440440c1b1080e140005129490a21142c0c02010046240c81c82 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 17277443 1250 17276193 17276209
    0x3130306050a09080a120207060e03130b2106060c0105040c0e0603010b010c030509010905061803010b031b0d050102040801050a02030109140c090f060c0106060302070201021509070303050a0219050d1211030105 92
    0xd0071140687c28445031000542c10b00409910f920075500440d200c0807038102c0700c4c1e141c3d01c0301e034090882000308001942c4d810780c40d00c40c50030580028044030380340c42d0f0350320340446c1141c42141035403070480d40b83c48200002c1003185040b410541d801031180030602d940e90400e050803607420b0303010301d808209031249400000c1d120b2402002012018504a102c1554800109003290010303507007803104e0000684001000c1c1400d214510007942c08400412103010504c0e40c4002030040e41000c1c0d800794441c8060102400f100750100c2c0c0040200e800208801d1070414181002900280240126581804080703400b028418040d0382c09512901c1465260904280400001100c0455600d410003c01c2c46040078000c001c0c42040002c01d115100981e071942d551000a04200c070f40391020101160354002d0050f01c400010b0920103403941414056610392036905c050b45003002d45c10720200061013801c2288104100491300d076103241044c1d00e40800d501032004080e0241c035082886c90a40110500040201d8904251 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 17278693 1250 17277443 17277467
    0x606081b01050423030d0206072307030c050a05030a020105060f04020a0e040f060503100204090e060403080105130207050105100504050c120c07030c0c030605041104060503030901030c02010e03130306050a09080a 93
    0x28130070100414000801d0a1003202495800541c200300c00300309280b90001c2d0b02c16100c5050708415800014040d00369a4180210f0340051b08212124424070f08200c4100607002142c1c2c1c206046276100c50401d64000d010306403c48504d8050390322281000d41070b0070305000744e411040c20758861000c211070100a00c402407010700183c20039203841d4440090315071014440752109101c40000580c1d41c5051009001c192a0300c96640d0900c0c2e4008801c01022035400041941500c00c1100c0421481ca800b00f1458060f0142c8003015003194a000144801050b030b590107882200c4050b6014006a1b54105031066103004100110542c0d440e0200003611131004a070052489a01c80c4c1400c0984280c82d444004000c80302e900102c6185541c1c10510043c0007040c41c0c00c2101a03821181480f80c0360401020a40304d0141e211514107040c0c2361461412018004c0d0000f19403024075404503925101d000003895400800d0b403000b500c0451404010501d42c410f240140004d0b150440d010034a0642c02010807111609803030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 17279943 1250 17278693 17278739
    0xe07020a060e120c030c0f030702010c060510030204020d0b0405250503061f020a060f050c09011d0405070c11030c09061513031a09060613020702010203070209040606081b010504 78
    0x140100d110b00c0310140190412500c5a801140c6481204106c54501074540142c100141d10074400100183c1e4802c0411040070740c0300c0000f240c180c407400402a0b0351300e0690402544a0700204042880a00551000d0f2812004840c14007881e140d4507003440c010102410340d10305460081c0248030480780200c0003141c00820141030159104140e046040760410b60780d00c0080182c000c04021401d21031180910114250805020000d504020b04074075180d100d007021a40c14854541c42c102008000a150b0a00b4000050320a0280380381c0b8030b02c001e103600201c04040301d124171002c49400c030300e040001d0442c070803802c040d01c42405911984100042c01c00601400d07000150200200424014007588482c01581300710043c41000340200382c1c2c1c1c60741c030b00003c0046400d944044d04004a80d5203203129001d80d0100c00d080165103001d1400100c1c00c5129590380650084614024001003244540c0004200d5031030f5401c1da0262091a55041e003008031100c4543d00081d801e000a0245044004030550444521 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 17281193 1250 17279943 17279953
    0x40e0304060c080f0a0201060305120301080c0f0303070501090506071202091008060319030c0b0702031c0b010e1e0a0501020d080708070306030f0b07020601060906090308030603070b03090706090e07020a060e 91
    0xa0349000940c0d0b4000140b21700180d455110400c20450100105e0061103104802c040c119810001c1c5240e81d02e801e51581e034841c450034400000e0a8800707004680c1d040f03402500a000700c40c90b40c10210358500b0241c0d60400080c8022107a4540240d49200f6600c98031001014400c0380712a10400311032841000d4003540e45809403c07030740c00b210725072080511402403007500d4021004119050080a10200410709001d40d00100650040c1180001642001e8103003603034000346a940150048030804940b0600c0340d0040444000d000c3c0312000012500d08211f004ca0b04800c000da1520700481c0c80b03c200035100c202283d020008182d48a0050740815030040407450000b62141d030360b40361608000580075056803440616414040c0260b81404214090001070a1011b002440c0481c001e080c0b81d068480030300844004004580b00d660240140c200a1080040c0302d0346a007047c1c80708540b101e07a64480c40010a054180008038614103c080c94403134040d0350084d0010b83d00039141c503005000842c25002c032030700a03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 17282443 1250 17281193 17281207
    0xf01020a02010c0602360f100804020904060204080d090510020102040620012003060f010206060102210c0a080414030105040b1303020c060a05120105090103170a050409060b1206040e0304060c08 85
    0x45141b015507070503140d10b000e42c082995000e00451806156005020f21041708280c00c40710f070030082c000e401503030644000010382d551303040030f400078002d40c1c001051502840b8482d4818961000d05507003907403404c403500d1012816804003a03080784290b200e07045c0480c1c4184c444901c00340c016500210b50048120010409002081100346c1301e403403030042d9094180021081c00020b00f005400900c405e4801c0c00100750505090002035510b20681424801c030700c007540301340c0f10104c44000c2900c10740303480308080b103d908802c1d152038030203508103002d940d03088907824202c24541c0c5014000d141c0103c0d0000040303051a22108070314aa10b4601900039015403017501081c3c1d8040c1c80d50801000405181ea40f043d0b00c59440e08028151140c069200034030822001c0300600210780c0801c08007080d5016100d4050b0740702891319090310140143d9120b40c0d44c80b0320f02803000541400c100d0080094000108180380749940d10402c20088443c10b201804981d401404184280343c000c03109400e140d4051100c4030306246d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 17283693 1250 17282443 17282497
    0x10f0302160803040b06030c01091a09030105010b070201080c1201120219060306050f03030c0c0f0d0506010b070b09031608030603070f09090501050702030c060604051e0702010b0f01020a02010c0602 87
    0x200c60700c1250a1080001040180403c180c0d02d1707600440c04901901c144481c0c200020050390040c0100b24036a40b181c00340700c0b441c0581004441910310060003c1c000d569580308804103d0b004074500b03030b0100e030303884c000210700c101c8070700072250344c0203102d2480384480c0d00b00410f008145003001006c0f84c10a60202e10411848501100d0800a1086030b43c0403d6080c107103403d02000303440790340c9d10307034001d81c000e00548200c0c00700864403c0041c82e00350307800705a4451000c009100380c0c1035248080d0880c0501400480c2c40a2114000c100b0b4902802c0c00c54a10f0f1101c200704c07943c80c0b0603502034816a0864a54100c0041d080750015500701c04d004040310411030715513075480e45001003680031040d0035030b95500c10010080c0030f00490f03078844d00310300195041110348000c450701c0d00c0c40100414821543c07440042e561100921900840c0142e000d44490946050791020703000340040c44200703228075440410507c0710340c80001c3c50800540e0680d00d140c0d03001d10507594000690020000807192021280c00390304411 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 17284943 1250 17283693 17283727
    0x403060509010606030c0306030201080103081815070507050a03030824061c0f05240406030b04060c0e120a0303020c030c0a0c030b01050d0812040201022a0306010f0f05010f0302 78
    0x7661000000b65007072611034040d00f118081e604031030606080190810150380c10410180c1101e4200e20b82c00d60310381c58048950480110401020f0b0700c4004c5c02d40c08a44007aa420240102034440e0080f2030400341c0391010000c45258903c0010001070350a800900003801d49001c40158070000b00798904200b201100040c4590007d0f81c2081e103191000781641c41081d00c5006050150940307900410850030f0103d4006091002d1100085103660305041010490b01c46501ca6001103820030f244000e00d0519190900180c0400e401c04000140e880810303034803a180c84c4504d081c0500d103400003400700c2c0d00195401d801a4210722060901400103005100c5216810b0100140c5584a5081514124154506100c01c148103070883c50151140c107402e000003030490001c881807002e18950384c40c03003580c4500c0102e11f011100032a810389801c01c6a15001c0c400c0340480884400c2c1001c07819140d0607a02c900020700d1842c1070380304030303401590b5110040049500605101810700d09a140261038070b0a0000c0001141c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 17286193 1250 17284943 17284951
    0x1050705070302100c020601120f020406090504060b01030608060601030c030605030a05070f06110316020d021302031801140f060d171e0a090506030703140c18010c0f080d0204030605 80
    0x4918000769020426a050010400d2071200380401c010780740002030000d56441050180c8014020a0318069041c84100101248030590041081c402c044c0c0318804a00500f40555085840c181080d85400e02580680288403d0f00c08817002410590744150044025065802c0c40c10185542e4020100d4641c40a200b4603150034000c400800c025450a81454008007240d4811020440b40c806030000c00000030080744c940d003d02d0b88031880d00000c20300002e0503418410328000c2d401030101d8040c00301042b06030041c62090103083d040c010041d124030020303402e807400b210800800700d44070000124004100c40308103420880180c444000140a039441c6c541264118040e14004000803401450903c40c0742e440c1d00d60519038100e4541003219500001e480c2d004580a198499030300030001070380f580c0c0700c1c2d840084c1c50a00d85450350b10394140609418040e600000060000c01a1410540e0f42c550041003c860358941c0005002c1c8000c0c4540c072101c910342c00501240c0002502084004040740e000d00807207000b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 17287443 1250 17286193 17286197
    0x406030914030909150a2606100308070f03050906130e070c02090a0c0302090904050f0111040b071101140706050405010b0402120f090309040c030b10090605040b03100509040503030403080112080703110f010507 92
    0x361f40b852100503d0300f98018141344100d44165810f00c0040d10306001d81c5d0345507a016501e400349400516081d68a809074150f103a80240d00440c05a440106803c413540c1260500780100d081c036204c02c08119800d0880c2d00020350002801c03004907009103c00e0707008442056642c0740050410b030014000541e1a03000f40d406681a9010f01c02a00d40a80b081c407501c5801c40601908030700e0b1502d08144101103000790314000c0d0007000c9001e4075150503401200d01140000c49a0802942c41410b447d0500003001d044d00c0590700b42d0320b0300c1026503090401e0f10860710002405c4000302066038400c645103c03000d80c001d040f04858003040c0017940381c13619903000d001c0d022001924081040300304442440221048201e41c002048004042086070741c0d0000100d50554160903511984d0382e03500c11350340c650340480f0350109030000700150070041441008000765015601c696520a41a40c0c4e480b00354100c0c001a103c0980f041008001d10000039000f8000c0c2c8284813200740680d15000e0300c580c2410b007120022154600 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 17288693 1250 17287443 17287499
    0x406060801031a0103031b05010b03070801020406090e06010903140a02060d0903080a0c050301090b03030c0f0c03070f080705090a090213061401020f060c070c0305030406030914030909150a 83
    0x82001020500500072281c0003010070310315171558500410081030010401c0d00110340ea10140144903080d0030000d04048d029046410176903030b406219000758824800c04c80000c43c0c41d440415500d6a00c1412805840c0503500e030001c550075515007a4401d5200500040e55128070076880005848580181001c03048008001501c45a1401c02620a490052285001c13501d8590401d01d4a0b4011054034151003e42800040c40d201c004c010901d03620070354843d410148590105440c9a020002e0707088804902503056a0526a460022040c8540c0502804c40190424142800241404804103034000b800700008160072032182c002c500300c2d9a40405102c03485490310310502c840c51810203100e002e20020310081541c0d280039070401c0d0315804080c1941c05082d03000504c05091010070030040d009150004140d90f51507680e00070250060404043c2107800049050007007071001c030084255202d140020700340031070540e200840084d11111a840840c0d1044c40c00d00e001c90301c01500300c1d10b83d02044044035089 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 17289943 1250 17288693 17288699
    0x303080c16080a3f09080d0209030717031c0b100804050115030209040b060301110301060306080d05040e1f0803070803100b030603030f0d0609050412120203010605040b180406060801 80
    0x42113020060044003d071181c0301c5201c40a00e9110030840103007980c04400d00b107004603070707145031000e131510b400040e0290002068141e01203c03103074004c1c0b40c0c0c010114210b491103607580702079810700012001b0107580e80e041401011303111104d00c1000c40108003a0036002807030404440010340f10800c00c4503e0300019000b007040200700300702440341140508011861004031840c43d40010200300c0700400c010032201c1036001050540e10250000b0100e43c1d034070744a80d80c503503859020050080a452040e0a142d200d02424000041c1c01035044506943e00c101081030b2655078002c00c84081090a218030181c0a0358550000b5041c00500181003d40c1c0f05400455072801c00c41000700602e40c4079089012050030070000c2c04403c1c1e4000040f03410078030450703480d25151040141c100d001040c06a00840000307003000e00308020084400b421021071589900e4100783c0d0404400c2c80f00c00c03808240208804140104406c1c04200d480c10080d110840c02c0124044001031070f040804c00341c8030a94442c1010401d200014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 17291193 1250 17289943 17289947
    0xf1701120b06060c030405060906040e040b09060109020702011b150204080705040e030421110405070e040e16061808010e01050105010f020102130303030506120601031118040506010303080c16080a 86
    0x51a0401403c039070031401c001c5003e10031501d0340f0031403180511540000580c440c00380c42e00070a4800410f68014590310519090404551030b0300c0c11100b489441c0220030012440503500c3c800d079616503406960b100301400240180954510040c6000e40b918911b070092400b02c0602400201b01a00005000d40905032500e0244001c1d241c0a030405041d80c2c000380000d0040b80d00e10004190001c0041260510741c91940c04d200c684455200503680d082800c0c8401c00000d140c020814240601c000d41c0c080280c568000c540c00d49501d040300ca011011944400108003251007800c00c2c940424007501071500c0240d8900450f42101c58948030559076035107600040003e0b40e004907030f076000c52480703000941c604450030b120b0010646103030100078181903965000ca807140d120b09003540e204011003000c4440a503101c1c20607500c04c1c0c002c0c00c0c1003403050354041d42410070381381400181c07405a58401c4c010040c503400d59400b5a0303609802414001c46c00e80621100004110042c2002510360003010013a43e614041e0b140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 17292443 1250 17291193 17291213
    0xc03060b090303030a0c14070b01050f0915040b280608090601030c0902070303110c06010f120302060105100c05060403050c060705030903030a0c05040504020a200705030d0f170112 79
    0x42985005001d0125808944011048030340c040960140061146c5102a05603400300e910166265800e83c0070800808000c010a1424140c40d0111002c5140848180820100083c103c402180c030400c0540049110304158124101d9071800400c2500100380300440c20b000000030727403036403101c07243d0000c403c00c422a00040065001161100a00301030341c1141c41d0384900480502c142a071059000032124181440f83c1e00a021b421511000c907640c40140d455600c2e5103040130701a070300304c0306411003000543e824030341c04481c042903054000c1d103040e80c40e00c0108000e40701e100c80403800b80145042c200340099018450340d8131551180d00e549454890201035139140c00002429102030080800503c141c000c1c0c00801e032075010045020106181200000c1200d440c095640903503000b50000c036004102c59081841405140040c00c02c0031031900103107407482d603114014801e458064020004140550344901039012800c8a18282601c000d0850008500c0c81c601c04d0b441220101c407007602503000c1200b0424 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 17293693 1250 17292443 17292449
    0x4051c06050903120f060a050a06020606010905010e010c020919020c030a080a0c0804080307020a0605010602010e010b04020301060f120e100b0108090706050301061107050301060305031209060403090306020703120f0c0306 97
    0x1103040010a80c113802e1180e03000b81205158200c240f0000780140d032030040d20000703050082c002032009a80d507207000c1d59811065501a000c41d00760310010819510603c1c076404815030507960340c40c14100c07075006e026042c3c0d0043d02c030140b03100304c0781900101c01441e40028400760240d040110707910180001d004200c00030141600c55a9400e088111440d1640309041c290020f411070007165407038440036401ea1034400d0302c002c020802c40c2004000174003240c042d80704907220000300e4000e0100d5010b00c01080101c0c03100b40204d0703021500c0c96858001d628464501072641004074100001c514006402c2c4600e400c680721a80c0b00c0e00d40c1c88800e000010350340846219003110b9011b00505c3d100e403d00030301030003a0005024070010006000081000180100500300040c00007030020000c290f02ca05102e03440394004140c903140f02c80384501080c070030080010290301c2503402d03030703500182c5600b50f41d03c803c040e41c0005004e500b0442060700007894120f040c801c010702c802c0c0c44040014610803d0b040642528a594 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 17294943 1250 17293693 17293711
    0xb040e0a06050a0605030703020702121b1207090504030507050709020304030306090507140a0302250209010605180f1201020a0908060604060308030a0b01020a15020304060b040203040f021504051c0605 88
    0x301c020062902c0e00343c105410795105040c416141e5860510480081c01a0034020f58045803900c0c2c0301c44100004604003112240d4040880b4184d40741c002885440000392619080a500c102020004140644c0c00550803600c02d161a525140807521494030300b000980229000c50741c004280010517405114260080a1140091103503140010019140c0810100f00400c441c00c0040d4940001d4801c0d0b04586980c0b0401d00c3d00c0058182004014003800c034030240c2213006180030300000c10007d0044043d1682c2003041c060302c0d403e0341050380070f12400c2c4041c955100d03042040c40c050043d402d002070005e025003189a6841d07500c02460488294a41040a020305000301d00d080ea0034400302d29500c0c220303648900211400728503401d8401c0102d00d005010314002c0c20b10380900314001801c07100c42d0000d40c0507602450060201c1c2082e41c0c1003208034482690010140c0c01a046c2500c01401d04011640003141007004943c1040e54400211b29404481e0418040b0360460841c40420031000b0311442d07400031104 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 17296193 1250 17294943 17294951
    0x105070c02030a1101140c060402190e010b0c01020f04060806040c050306030c040b030c09010312180b07200301060f0305011505011b111005040509071106160c06060b040e0a 76
    0x1500426110184500d01603c90f00b01c007143c0652031703401450b00000d052500e44d01613507104d0b1080292a02e8110a4030101c5c460340d104c41320751503140c0d030100211080d9140c0c0c5403034076116481d02d1403840341540120b0315104695000e101a02d00c03880e50030050002408141c441076060301c4d00c8030400084450084040c030030300a0078814450251800140b40c41202801e035030004160204900080c41c0405100c2c0f001e502c0195031002204000034655800c0122480c2e8071401c0e540c2c913000b0000b41c00c910b154060140e40080a205203404a9984588503540c1925942042d450203d10030200c1d017034400a03006051044600c103400c1080000903c110701c07221000300c4841880b0750900c00006c1c031842d10710008074030306501e0162030002d116200040420440c4002c0a20030318105c20003010344260010720a03e442100490b000480880c01032140c0c142e8954010080c1c0159903894100902c000450012034003086207045400000451910880c0007500b642d100da80c1d107036031504800c80e40e800001040308480c40c0c10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 17297443 1250 17296193 17296217
    0x3050103030509060c030d0504060c1103030705160609020409050f0f0c0a0302010f110102040303031a030c01080c03070201180b150607030903020105030c160c050406150905100903020d05010b03010507 88
    0x1101083e1007004a0890b8015a2074040c0142d6916502501c0c03420050507191105000c20041c485c0d10002e81407249403a000750019401000d280ca80c0021a984008a0410804003585452208410002a11603d0000b41d899030680110b42110800401160551f001e59850303009058100b010700c0000b20040d00421201c80900081000c0e09801d2100078140030602245140c0d4138011009003042d80184030003192107507075a0500a01a150780b021014806007503106000d0103050100300c4842c00441a1a480903544400c0c0708050385900c003c20b040e0465590b40c000e6050341e0502c400c0300c80801d006a2001a503030802035090548110340d2001580300301800c02c42e060019400c444400c0c200c0c0d0702407e0158032079481004480740e1f0b2041b0b98201c98103103480b035102c4081045020240041d1102510100a0643c0720a2404594164404403402280e00c02c101081607240c81c15844810743d40e03a142c0f0140c00c9030759602242004110360800c40301070b5102c4c030110303a40e401c0911030b581e800b46603490400c0480c08 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 17298693 1250 17297443 17297447
    0x3090105182406030f061501090b0406050a270303110d020d021005090118060c080a18060b030f030304150c0206010501090b0a0e060a030213050405010b030105121623010305010303 79
    0x1200d20100407244112000141050790144100c5d02a070307200c44261030342441d000190b8048004a00826400300e0486100814034100300000c0d241034a2151302e60a18001c03881205482c445c49020710b03402c0c40300740000c25000c40104e820b410001140310b40c84044142002d042d5540c200003410480b5000c6600c9040041c000980c0081c0d11200d110550b100001e45840f207034000e502409a070803c0264180303411b5881400c01c0280d50200001600342e544204c2603448400e41107081e00c05102107081040510264040410525880304440c11300040486a404a22245c05030540e08110b50994007010b1a031100400102c442c0100302c070054103440609599810800007230a00f02160107844101038000c0b4209041501401f401c045411f401400e880e141c140008006002c2e60001c8444031034640708240000d2142001e0080328180d600f007100380340c1561b080c0420300c421100103c45010543c400c81d011000784c0311011071004050300080d442c55640390b030703688510010407051401541c1050324001c01040480d07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 17299943 1250 17298693 17298733
    0x70203030c07030c0204110913050108061504021908090d0e0102060a050403020a050a050f0709020403020609060a02030d02030103080a030c020606030604021c050f0f0106120503030a09060e030309010518 89
    0x35007a5208540718486030030220b400c2148031400a400901e00140c5070602d100c00405010000300c11600101c2158031100d42e402512400c0c41002d810750302250208a03000080141842c1d000c07006800181802d50b844564407900020202410200d8249020f00c5280242800034015180c45030809140c10707800f0f840000d5a51000400800002d45e40d40c0c080382c2054030910040c3c00680e0072004603802044282060354507178604600080042c0b04042c000951121a4029101165001031841d81403240e8242440707004d41c484080c080c11404100030800ea404102c0c8080c0d4040c601a0710314540b201802100501200e011040c00ea080d980044e0070461650381c0082d540360300c9641501d466000c2003000214030540081020b0045c0745000e40c1444024034500021030030480d002c000020f101c0c03e5503030880304000b202c40702e0000d0181d409c10400620030190070340004c0041e0748180300000d42c4946004002c4d04542054a9002c040d0b51210305204d00c0180100ca107886140040014100768001c0c55441a0b802c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 17301193 1250 17299943 17299951
    0x807060c0b06120a031701050102011802040e07080d0306030b0a02040b09130f02070308160e06030c0a020319020105040c060306080c090402030a08030708040c270b0d050d1206080607020303 83
    0x1c1104980010a2a1150034004510780c001208440d03107045a4a000b41c03803003140100c3c41168a11b0140001076941c41401400b4048a5190f0261440c0005400b844081c0c111102c0c0340f07000c1d106014000a210304100419900458030b581d0015800e400e6103002840c0480103000500030a00520050121280000842d036000700c04a549800141300132034104050710f00c2c01e010451117407020607480c051540002c007a41c4140304a0165520800c2c181c2419520b030309140340d010750000f10601c005502180324400074070b9100600d00480e4146400e900310403c07044801007006005035180c005020410003003840e00c8001d06101e0805100413070404a8503030340c070f409050314244101204401301d42991002e02c0340312401604170003503c0e40c2e4940400c01800c542170035101241c4034400746500041e50206201501c3c0c60000b01001c0c04450040e2404003405040c00c040010b138010306000030300e0002a02081a048048481c0c0c0307959150740010031007101240c6070380e44406d800d90440002c01c0b40480c0d0100c00c89600c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 17302443 1250 17301193 17301203
    0x3071d090610020a060c030b090a050c030c03131506030303050f0610120207080d090c060e03060103170c0703030e01020d020109050705010f090902030703021b0c0d08031905010b04030204060807060c 87
    0x300c200b88034400ca1130007115071000341040e482c1840400d07810703625401400070310a09440e109550785407401e402e4102c0f4400c48d14400450014004500c0c0341803088015600701006c00c2054180c00f1107034442ca09041e0000c1100104140d8a850030420103816015140d07210114940466180c6070201c08180081c040c05e10110070000d25400c600c0181509606481307800b0f0304103d50790388802d00c092000d4010100c48000f502e004002031400602039201c0c1040400043c4007070098020b82c2d181d07a9401c0705401d0605225030858000f803244850901040140d5030041d4004e507030300745102206174000f9091030304280c05001103904141d1000c0c00320b00c000900404603542072800d00c00d2003500b24030466440326a900100c01117400042440300c110b03416000ba20010b00d030a2882c9440d14843c07000344c0d07550145008069081092a00204003044408010f142d110742d0402c1000619000c44841404452090708050a06100032806001f581000d1003a000904051801000031074203203807003c0c00c800744210000385 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 17303693 1250 17302443 17302459
    0x90e0604170d1104081c0c0803040f0b07020c04110705061603020c0a03020109020301060504050402130914010608070314060c031302010201060302090109020909060f0f0f040b030d020303071d0906 86
    0x4004100d81c2290303800c1507001020407085440e40400c0821354002d02c5482c07203d224008212003041840c400840521788a031312102000305040d61420b42d0f542004105545032a00031240c04086a01c1506040c41047c180c5d02400344112880c08000468070315228070b0004083c2070096000140002402c01d80250640c56000303448103034140d04401a2054002482c224000c00c0d0400c0200342d0150082d0050910031002072024685480901080b40e1040364040d50000c0144030030034202440ea0b00005619004107002074075070603004192030039182c1a501c0130790180d224290030001c3c0310380001d4015451007280080d081905005c2d82c24911400040c01e1503c0c0c4011900e049011607000358000300c011603018103412125a5105900e00094004140c80703030007051140700140052030403180441201c10014400d04440b0040c50030320010489842e0450f420641d508001c52007503808102007a1801119401036589280030000140001115500760b0002004d96400240941d0307003203407541c0d0105054034100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 17304943 1250 17303693 17303723
    0x4060c02040e0a0c151409060405010509030709060b0c0601380d110306030d0201060b0a120605120102030405160f06050d09060507020610050a0506030f090a080a0315090e0604 77
    0x341054040f080060010204d5a00021001c40226200c010344481c2d840e01043c2c10355410b1841007502c56020b007140e104004000c00d2191b98010f00150862040103012190601d4407280d004044403003d400a0001001c01f05030305017400000c0007482d0240903a10902d141903030501c2076004541400040289405158000031414a5800b2040d1b80d182e540130942846100e1200300f0b48146544240c0e0500d000e03005604050000394014012181260456031225180130300d92841150440c4003ea180d041d07041d19034000080079a55003a034560201ea0304000141c5c3d90800b0300d08180350019007006000b02c899400c0c001c000200100710140121002b0341406640d840110710350000800e05100004c001c1c0385040140005940d00040451040d0640e6145500141c4ca8800300304100c40b03984034041c1c3c407160400005a08070581303c3c5881c3c008031000c080b6070000c10140d540d50b90070f40101d0304880000e55140200701d400c00a04280d01c0003040c92020400030307014034415130f44e25181c0080018000038010f684c05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 17306193 1250 17304943 17304971
    0x409080c01050712050105010816030c02010e0f0303010609050d0b0106030504030c080307020c03070611060c090301060305030c01050a0f0e0606040b01050d090b061201112209020301060e030105090304060c0204 92
    0x4603a440000c100030081c0b07141024018160b001041d5052040034600303000800c0d194020b68045004e02a07034180581c200d4000c810403030140403996884011075482e9100c10880c80d100f006a0100800c1410142d6200d6041c07040041c101d150a5015031b11500300200b000c0c020962111f54141034420034500401d20380c4d190300b011389141d43c0040008140714000010800015400301d112a00f0807412030654a100795914411074111a460340840b909400c4400480c03090380e80c80005203166080913001141140d5a0340380c043c203541041b1181e01d9281d46800422121b0400e502c14400d801a04d805d04100200041c15001d5540070004d191500a554502d80c000c2c460303004909031443d031010041d040c45071a40c5032602d811148000d503662806003024889180e110b120600441c100070152090290510043c8550400c140c44c4500c071081a00020180100e500000c40c0000c40c007a103c0d58903074001b581001418582180e200500302041900700b80700605c049980404c089490640403100481e82581091175 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 17307443 1250 17306193 17306197
    0x1110f0711191712070f0b0105040e07121401050c0c0706050a08010b03040f02040e0f10060302030c0d0c030b01090504050c010f0e010311160f021903020d030c080903010905011506031a040908 84
    0x8a80d15001d0f012802c50100160714540c6d00c03c0758891078414507266070700c00c1444291070041c484250030f41c10001084c020f01207000d1001c02c01e0ba0141a0801d81620f0078840d15003101c00c00e80341042c0064000645120b541d0003002940024074203442d00c02e15181c03c4841c01810401c060142e2104050300101107000e004124032070403500c07900203104021200e0001e4120303594040e0114022054054204404074650951007900c040b2030f006805860b4421002c01000911070303110404071445500c0210200219003012009406010f007414002101d04281c1031440c940030030074140c14100b2204151346010142d01602d030b90714802c000e0a02050072041000c03009594061a0390710b4405000c5030400d107040c00710454801c0050307402611360b4400070f0700038511441c60300c0b40d90001035001861903202d000041d00c81e0105100f0140558602c43c01c003400310002170709403802c000b8140c660741e4460080c050035100d0302214600800c0c0604041282c0015605040c01c860b051040d5203214a5446500d070003880f0314801 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 17308693 1250 17307443 17307463
    0x70905071e081501090e010608130c030308010f05060a0e01050a0207051f03140c040302010c2109080d090608011806121b0504020703080a0b0301110f07111917 70
    0x2000181c000c01600c0103090035011511803160ba2202d0780032901d00e5000e54590410345405408080d03e40e0b08140d4150384907100a4114040440c60308060000b0945841e24000070318800d640c1c0081745d5252401d201c084030210380000b8400c0c40100511410160007488a0801d40000e09019484040c2c008042e42412840c5e44400d8102c40b001e00309001c3c0003d0785500b40905802070310308001841c9544802403030800c088900d041801c208102c20301c0903600540c02500d005100300e0040d15440003000c4486000c00481510a021542518043c446809c080c007101034504544c3c9080501e8510f001d0000306000d4040c41004800102443e21300790300b030202d404c0503028001d1022441000c101d1441c1101e5a05141c055550b458010f485011805290500807140c682d5010359901c00242c0750000d8640090200b21119035041d96112201058401000080c24014141d605803a4a491050511620201d10703c141c0038441e0b85038900c48824102075426800940300f10091040160044406c2c0c5031401c60070903 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 17309943 1250 17308693 17308727
    0x2090702191b06020703150908040b0f030a0b010e0a0311060c1f0c020c0d020103050a0b0405090102070303050603060903041203031103011403010b030a021e0103090206032d06010207090507 83
    0x1c502001e000340c8020045555561030700c92012140d85200490b100c18842c04024280341ca0646081105501c0b50021780207213020300100d61900e039503140350284a034041d030051100c100000c403c0160011651084180303942c2c3c01c0c01c1903401e01d00d4520001f19101c120b40401444481504c1182c03034140c039180240c44084980340c045850350700c400da1020801030200e41d6884075060905401800c0ea03032010480000221025110160b010190750065029202c0180040f0300c040e80c030a490786142d40c440c001c1c540104000750006990343d01c10f050040c251400205400c0c00f076400746007031051001e40002250115083d44c0c400040d2511540b4084018150418061594182c04800480c08840b400005001018114002c2220941c01d500341334480e1905500a5806602400c080300140c8100c0350320022110b051400040424141e80051019003055030302d44c81c1004e4007402035001c0c04469080d0031211442002c40801c901c1c00a0000b136542c00e45004020b03241b070b1030750041010f09004d00c0603511481d91074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 17311193 1250 17309943 17309983
    0xa0b06090120011404020901060314070c0201031e050624030103020402030402030316080909071106070509030106180207020906010903080f09010905060a020105100603110d02031005060304050304050405060f0d02090702 96
    0x8401e0000c0076510507139051741f041003420000620140288108001182072540c2004035990342c1105891410b400740e4180d043c5a2a440007000d11481400c0000c00c4005400c800a000d042c003106214072881e10704d90380b4030202d0040b1030410060075004160780c110303030781194050380d030382e4070380c40440d00310701800f240c04030b80b003803800b1920041014030005054800ea0598601500382c3c2c4804045a16850000c407440d0300381c0114010030b01c202c0c8a5002400e074120701030f0000c00c0c056581c1448400101903540d0700300900e42d000c504902103150910056400031000d00e818141d003800c41e21241c503d071150a94804103080d000446000c2640982d105400a0800070a6242c4481c00d0060180c003900084900c0b2011620304c0c0c0700424401c0c00791045001a018100d080c9041003000700e11500203502c00b80c6500f03140700d00d0701400074a40d95090000c603c254414806103817143e20f0b100502050300e00c0504003611401c6607007032218881e04d808880459541e01140c0d510066101e400040e810314080c60040d034442104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 17312443 1250 17311193 17311211
    0x30307030c0210030203071b2103050103051c080a0b0301150e0a0b041806020d0b0406060f020c060a080f040c0305060a060e0f07021e0c0607030305010e0a0b0609012001 74
    0x700d6080054001e9810103496000f02c1011412440100c9001c00880e03010213400710b520b0100043e500c4c01c24421941c480300d01101c4141d400409516103d11400241c4aa005000b003140511035411619511301072000100780400001c0d085000c020030420070243e46071051145c03958250088003c001038a1000445107032107041d0f03481000000c03103401202c5814282c80200500302442074100b0509480e01882d4910151380e80c80019612024001d805991602c0a00110f07996610404004000603111650074a0b2001406428403440106c264841d004c144403008455412403036141d80031101e40c425800c0c0e82c0e154500142100c64540001e82584120010003440c04101e501010507a80004134850f090364401c00e5089014001b11404001a005070f4956072002c0d64034040140c1d040014005d481c0301d40441e202040c1c6640060b14207500103038840c00100140101c0603103458215000c240244010121940400c0c03139481842521410003800103441410345040740315200d14145518028052846 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 17313693 1250 17312443 17312447
    0xc04150903020111060603030a0e010504030512030106090f121e0b07051809010b090d0f17190309050d080c040906080f0d0810210203030309060703050c0c06040803130203030703 78
    0xda14041203001c5140450740b9280840e000500c90700c1a20014000c41ca80001460200c60a400c1203458130705014061002100042c8140f0031800200805000103860713614028005103130000030b03442003680c56043d41c0c0c00d000004a610b11305014a401003403400e518440c1c03843c1150791040c540400b90490f00c020082c81303011a80b1000034022618412140c0031446400020482015030a02c14450261f00800690700301c0d0421003a03640756035000b0340355000c20321410348901d0400c841d030000740d414001000640722428045000c0104400c0b4261030100100040c0ba520300d40e90340d010160150a00080780d0002d50301d01003410071200a40850752060214554400d001a50b640d400d00c1c035805c150041c29591000c0328481d025083c8582040d0402045442c81c1c441031020102d00c0305002602101814403840140e10100019030107000e020009142c3d900d09540c000b001c031040a0030344540c65404000600c500d180c00940c641e08640c2042c05c540e525101c80000c1c11028407041c000a40500000c110300040c03507 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 17314943 1250 17313693 17313707
    0xc020609010f060803040e06060708070b16030603080901080405070807080c04050106050a05030c0d06030807050c010f140406080a060503190303241215060801090c050301060609050105030c0415 85
    0x4200300080c80040384003074000095450ba0702070031070240e00a000c1000740714181e2869640010b00a00703428900f68154461403520b5106a209031907003080304060104541c40340b500745000f20210b2504010036800c2d0785d104031443c42001e1026042040100100e024080180b000c50014a01c1608031000d20f90f403107000c2c944034548003164920540c0390000000340140510210345403031403940d0b40c81d441d41d900c1030030b5505280c1148003c101d41c9560742002000180e0000300820b04075000e1402803194507040f4000400350b16044040078104402074041e82248503910341641e058401c18102020190364452920004002d2075003c56403502c19440c049a070b1003404209103032018082e540500c4041801c021100c96041040728118103d100c0c2003040005010301221800041e1041c9480004050414081c5041c0c990703d8001c00031607503444441c1c1701001000205c1100070002500240900b41c030345040034000700214890706050110000020301800c2e01481240d02401207011080408440d0f027000a0500c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 17316193 1250 17314943 17314951
    0x7170c090c09030309190305060106090302030c01020706120e120d02030709060c0309050d06090b0a06050307050301090f1202030412030e0418110613080a0501020a0e0904030207030b06060d0c0206 86
    0x3a48500045562078890341c0480380d02000c080d00a45c40d000d101000e01c2503076a0b40ca00b5092240810341d401000299041c880c040c020002035a650482030305500401d41003102c13403200c2c141954031281042141c95040038049074442c2d402140020800610520f5a041c0f41c040c600d0130f048224000307007071054000e0540c05103024900583c0c9150a041d1039180c00e9440c5010000007401041c402c490420441c80d02445210a0324421240464010200d0b5240d07442c1003400d866040280d07889034030034400307402c0401c60b600040004400a000c0c061190300c4000072400961406405c0780d241c0c10340e40440300d00070000c940041100702840050700c000c40c00c00406c02c40f28111068400d41c01e100c0494401074200d40384052440c1c010000800e035102840420a4641c4112000b216044220b240000c0c0050140b03c80c1201034060000036a0b0754010000090000410304816445042c2950038080402c0c0d00207004420703030f94803007103240d66900d0341000116280101c80644100c64140a1600a01940840c2c1a401b03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 17317443 1250 17316193 17316199
    0x1703040501060608010e0a02070606091802010807020a0f02120c030f0703020a060f051813020c070305060c040b0a120f020703020a0b010501080c0a030203060a050406081f021207030203060307170c 86
    0x1002e601c82c0b9040303403107501c203101c3c850760582d02401044036680d00b50300030007484d441030780f000a07075660340c4c100c20341130340c1c80c800700100c3d444102c01850081d940c00641e5554090554400f0704541079a0f42c0e2589840c082c4107030041c1c0a03141403000140032250410041c646c84030000d080724180541c880d0807035070710541808101d005a190020024103180141ca60351410007807a2105401c0a18080740003840e5a190001542d200d91190395000c424101d62000700501070054000d0000c036411400c256160010240940150000400c020481d08100e0001d840d500c3c0300615015040e0f440e440426400b030700710181247d04040c03000404404054000800384100d6111328100c2c4110303039031034005540142d01210501e80c84001040803803032140c4245d00455200340020030f01d1030ac180d12080400d00b154402c0c3c0001c0216400444406202d00f8016181061465490b6066280000303284004800c154042d028405040c2c001c808070300b659405000c88005401409411240d038540b440d86281c0c0c0c0d20309044a280 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 17318693 1250 17317443 17317451
    0x40b0a0b040902090f1005100f020f0a080a050c030f0d090308060f0109050415030b04320c0103050402010c02040504050c011205130b07020f06090a060b0103021806090406031703040501 81
    0x902801c10740502e41425400501040042d81c820940000215004148517168900201c0100b1b81c1e03030340c001e03a42c4c1220304140e41d60f6608011641020b85000220a40108140e01c07402950002401e000200d0300004050f10701581c03540e056080d4685540156280310b210000042280c446900444e4041d240c05d500a80d581503543e26548103104885401c800c0d01400121081000c0c405400e00d6003203c41140100d98444100a44e02e4a4604101d0070554003107a51494440075440c0d25038204801d011143d400f2100b0000e0388040da204160b64102d114004c0d0b06058650380040c080da8010320800310030540140052045140c2031a06640b03d10102e41c40501103a0b040c1e0780320703110a10611070b040c8688002406040901030315100d140b030609005001700c1c00c51240b06504a80b24a0501449005040c02c2008014a40061410b20140c1d0741e21050304d4101031051100e087c01c0e04082988200e0f041050319965681e02011000c9409003405400280402034881540006c01c03106000851113a070241000700 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 17319943 1250 17318693 17318711
    0x3070f08061c0803070207030f0b010609050306091c05090d030804020103050a0e0703060207020613080a0b010e090606010f030b0301020a080a0b030a0f030e040204030f030203030703050108010501060c03110a0209040b0a 96
    0x404403119001c0c00140b5403422101c4000900403400854100e6110700444102980d21354854003000641401144c0c4a130402c801000111f4008000f44043c2030118050409440c0000281d07946000110070305220f141410303080c5401c18003600c200d0b060201c2c083d02a500a80b05410007070b00045007a0b42c01c90000e8034110000300705401e21301c0382d03c3c2da003c00c100150004030f141d604e4010180d0003448003640d0049041007441154182001580014404000036200c01c1210382098544032030142d000400e1204044104056854081403443d40700e000ad003440180d01140308401c800a1401200c01a01507100113007a4441d86d07001000d0b1403151165020030302080d00d20700c050640301c2e030880c440100f0310302400b15400002070080e00390b003500c200c01600040c242982e9442d81c1460622851040d0050780000042c05442d81c1c0c940281809014014003c0c06103514126000300902410003001c3c2c00c00c040c480701d801702d00c0e1b0141b005400c4140c004185406a06060418195050090b6294201e46107410112 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 17321193 1250 17319943 17319949
    0x2101051e010602120706060b03040c080d020109020a05041802060318011109060702010c0303020906040306060303031404020108060105070203070306020301092405030606010804050a0203100b0a0905010503030a050a09090203070f0806 102
    0xc50584105501a20340b006007101800c8603a000b201045580303d4403082c01060f4402c25002840c070880c006d00700d003141c251a15019908011b80841c1040131a41004041e502580f50061054121141541c0c0050f00709a1041c12086002600c0d40095000c0c0300002807210075030420098484011018000b04003219201c43c046e2800e101d112800c0380c00290603c0340101640c011728845650500074117025140c080340f03400161041d0f0154004940e200d0362003900340700f0f06130b040c40340048000300300189152504040d000038000c0680100a5410000002400f100310349081c0102070086510003000e41d101d584031100c0c04050640c03244010000c0b000704119000c0541c0000d03824088680240203803006445103401110301250040090b2034a220340d02c100c10060710108520102401c040c440090f0b001180740030060f1360201035012045581c2004018006690003004442010410741030042c1d070f44582350300c00c0c2c0304491981d10444e103042c8003108200310a0b07003001d801c100880103a55030207244c0da00d130420 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 17322443 1250 17321193 17321251
    0x50307030e030301030f0b06030f0a06020a08060108040c03060506040b060301090605030607090e1b071e141f090f020306010326030114010e0303090406180c02010e060411210105 78
    0xc0d1124900c10b06c498046501c0799144c9030011000390a4070202403081c444640b80c441403000842d102c81d0300080c0c0e104456800810940c2089007442d02c50321500b856140d21404030902d02014141c0756503200410429652644030304110400940b0041c4c0300d603540d403c0e41d401403055100311070090140c000014440e41c483d40c201d1050360540b40e50030400352108071000211a500140311744a03548100300f008042442c1e5a040707002002c1d000401c0744a4103491800000c0164401c00020595120380c40c4000060103108480200d40b494041c00569500f850411144010640d103005e034041c0590740010051281c8d400c5002c1084601d560700c810f01e409a112450900c1c0f10912402000102e490a000c0c80da40c0300703480c500b41c282c4005080300d00b8400d003100090101e80d66a48032840c40300644002102d0200140070307010024215000030841e007a1409211b5072034000080c001404a842424a80c0f040d94503100c920501f045a5000c4081101040c6a514003c000644044058868104020704a03801101d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 17323693 1250 17322443 17322449
    0x14070203120703051005090c0c010606050c0a030507020f06070b0103051203040309030213110307050405030f03030402060a300e010515010e0409060e01020d0b13020703050909060d050d050307030e030301 89
    0x40c11441c0c55403000c20850062102070080c1841d401178101c0050301c0e94908190394020303032119045030741c0c2e42d800720800c90849490341d00c01d6080c010244400b440b11500420341802060305070400c07540d5040144009178802c4003900c6066441040856a14203000040c480e40d0f05a80c4120115209501e44101a8603103010480e0002d0000e10821000c3c00103040c031601e00c0e44c42d600900300100c1c3ca985000507402c0d881d0000c41e03180c40000c0c07002c60108043d01c0c0411002015452070344c051440c5040c50380200b0102d01c90904d500301485001d980c0350100d5080c4200200001c826080108a45540318a07242c1c0503006154420340f803503003400042068403074a03002850000e1016107988154010b1807042c40054001030f030301a12840c0d071300c400740480b0510a00080146444440d07000070b40c810b0000c1040440c003200310304208564414014007002a800c03004492002c001140c42010540d81c8030005040428188001803060003075507a0404002d41000180d802849940c50900601101407449681c5e0b0000748 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 17324943 1250 17323693 17323717
    0x5030d0804050307022701140117100b090d0b0c0304031103030603100f02040302040504140f0f0a15090515010504050c12041b0305150108010606050703021c050409090614070203 78
    0x8044401032a1007880110700760840c1c061b0f80b219508040d102101c2e42400d03408040d0b8170f010b040311f9800320f6a0101c0f07591400340c40c0703800e00300050030141e00d9019480c0315401110951000000d40c00c1059650025200509602282c495201e103495211107085400554045012500e5191403a00400c03010003902c4c40380b0750180061054035580b04102d0080d1220000c12805c0c598204008405601e45008240c42503010340c90b402000d42e0500381c154580002c4005005440d00540140c450845000c519180c003103402110300e50802e0313074011441006010b80b40b002046c0b07128915421a05021340140349040310403ca804000c15510b2105c8040300e403284900107030421200c0000640010f03000c2114a240070b2030000c041210640f00d039141443d1022101110141182440c01084610024094000503100c14a00305040040980c2d01a40e524604002121026180c0703240d100074501c0b032001d5070014940310701c060000d46c082c0d0070300b14001e0024603400c41342001c00000244050340000304030ba0000c8040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 17326193 1250 17324943 17324947
    0x20616050a0c0606050d0303020c060703060f0e060303120906070e030303010501020a03051602060307110c030106180e01110f0a120b0d0b0403020703020607030801090c091a090301020405040905010605030d08040503 94
    0x510071505a002200103d03a80c41d99000c0125003601c03440c907050035052103074400590f20001c54500c145801e60041c00c0404041c00c00300c0920000546c0b08150301101c00041d00d410660b01c501c400603055001c0c003200c42c3c0c0b1030f505101c1001405000040d0075030040c01a6150180e00c00986400c1c140c50f44001d0040381c1c0544c0c000400d110000748568000c040b010301030f41c1214a0110540d0000da402d0b03009a03003010004403455480005a08140200f4000704403c074020000030380752141d00b001845220b1001c41040f81d940b51101100c441c00c0d00030740341d0340c0408509a031f6100c044840801c56600007140c41800120a00096180b20401e4440d0788001c6800601c02d82000846039136800b15854020b004804500900c0d10020041e00c4541c0608411072003a00e0780107096050450220403254500b25007000c02c03d5044040140c00c2c034110041e04146048030405603038608010100b8064071596209035049491b20604a040c0101035000c1c0d41540c104505807031240d6869401100c0441c07050310060265001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 17327443 1250 17326193 17326207
    0x50d03060e060901031e0c03050604060c090801050105030a060905010e0703030f11031201030807080c060a09061b0f030b0f06040e0106090609031e03030f0905100b0607110904081c060602061605 85
    0x41c0d046d00d80051251103541c400989986d695810500142c2c1c08990031520780d04405921600400360001a10080000304030759890140001d94600c2c0702c0d8009440c082da00d0351082c042c044203402c0544050525003c0340e640580d02c1c54024007003040c0d02d00d044005520050074450001d004003c40e2807101202140d91016405c50319220301d2a0701450080703956010070401d01e8000e00003803000a1045404420002d52003010b410042c080d2054122441c2d0f1420341d411410301c8054001c034981c65070b02030f645400514640c0309004203070750031000060254480c001040c0005c00414004ca01c1e81601c0b2950b5507242c2665440c542a1200241804010300d070070141c1102c2ca08082e4556045801c01d03010f840d0219001504006000c211002e070791050746c09410442a5600042c0c0d03a0040c1701170f002050350603a00d0000c0580344c0c101c4000c11824128468010f0401080130b000480c82540d1141410015642e0000304020f038180080c40d4509c80c0301e01601a80c0009503104100701248081910035480d000d00e0310070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 17328693 1250 17327443 17327483
    0x203010c030903020c100216090f06060503040503030403081005030709050610020c0a030b04060615020c04060b03070905040e0307052a0105030402130509010920011701030c0308070f050d03060e06090103 89
    0x10310b10a1a42c1144200321023880c0c0c194207044104003e00c42418000740403070300c060180007942c690b03070016030511004006000009a00000300c83d0704c0383d0186814581ea8542902d00810004540c2c032655140c85120804034551045600c4680200e8045400f040c4044410400384e0700d8860900c80c40e540700f51044400c2011a040c200307000e0f44180b2030310000a405d078448500703502001d030415000300182d0048000d10040d007001d110f010701a01c4542d0b003050540c5000344000700b000801d07001d281e01882c1c543d0f22104d1011b2040080e10800c1d6801030a4900519890341d103001c10302000614056200440706001d002c170350140301140d01850f006414242c03176442d106020800b8100240c9200c03203a40d600c0360202c001c507124002201454003014006085c400c0000c00040c080180c0c81020314240e00e02c02c3c0100002000564030f00202c0c0d61101c1060380710015810000800502e0b07140140c064000d1040312107405906502240c280c8000001c10a056224001030100c050000d0000034442155600d02c1c1c080be103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 17329943 1250 17328693 17328709
    0x20d03020a06050115080a060506040b1308030a030905070e090c06071109011511060105030a0201140d050109090b070c03080106080606040b0c0309030f1b01080a060905130203010c030903020c 84
    0x160190045429802442d0382d4002102d0302680180c03501c0d68072002104400b0381c0550503582003d441d5509010756810800090480e214510035600458070005400e50100c081180000003041000c0540c0c0e12104010000b03000750440040407a95401400000b040d010740200303d084c01180b01070014030710b00c21141d0912140d6844500203507030103c1e10900c0101c6669849402c103001c0c058001101ea11640040c102410228001c000d100a5402c10001480035460001e002d0000ca50246170800c5040c01100c00032825108040b10035a455007000000708800046400c102101031140540203020383d2462012240b1480384c10000700094040c0740100149407040c0185034108d10f000f040e145ca41941d4100414050384450261110b503003010070728202e00d01e424494910b511034008040c0100b00f00c4640e800000b60a61041a41400302c00808220552800d80c01a0003503c40d840040000b0700f441a0958080f0110110891081d0b091280e0956501d1290042601d034a915400525083c050441003107681 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 17331193 1250 17329943 17329969
    0x90108030a050f0408010f0905010b0f03060604091e030504030c0909020d021e060c0a0b0108030a02030301060f0306030f0302010b030706050f040501050903010b100f0806030102040320041409100b0a1202 89
    0x10340f428800814152402c3c4251100a0400c0c140090584000c1c9406402d503030b0f400c241540b141d03034018166180d43e18041000c0f54800002c4800145200240c0382461802080805c807000050b5441010020507411100138001d803801074201e6402280e444a49805482c0c070340000035004650740503460014100301459803600500320250503100c4041c2030108005d070b0403131040c1c3c0380207a201030040c00c140301440301501d0240866401031840d04201c5000655a40300610805080004a00c0324030315a500c254132140145a20824021020b066400d00a0103400741c3c4e800740e482401046800030300c0314081c9080358101220f1888240c07e0a1501d00103417055000740103c0c035010754803150240a01e41d15003405940160a81d103c058005100b4000203140440062002d03000381e00c10042400426652420807440c208181781c07001d000008400410b0140c4100ca40381d075803112505007030001280012400504202c080e030800c11000e940b8804001042e0114810002c01000c0d81c200000982801c2282141c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 17332443 1250 17331193 17331217
    0x703030e070905150f090f07081305030a051c0903020d0e010306090603050f07060507030e040504140109080a110a020f04022d0901030c0503070225030503120402040b090108030a05 79
    0xc2591070b40b42100f5240c080350a500c0c5148210301c0c0001500e49031602d10720345941600c0003201d40c94a07070141e840451011341140103004c20500000c0c00d0755101e411050805503c5030983e43c0321160740f6405042508111003003260b0040b0380c551840c034a80b043c4110050725130103900174907080c4040030003500c2480d207108600d4105071310b600011071b028404e40070720302c000c40c40b98005080d85100d8094282c1800003a0304003904004081002c1401f1903480071160f100c014044130000b58680b210300d000e4030320303031501041054036500b0003c17882e043c8088040135121408158843d80c0c0030b41080840303581c0b500c100140c02584400042079410341801c09601038205480c1d001502c04180541c090400c41c0d01c2d00385480307400b402000290b112270030759250251100c020b0750f60420340e0071410600300c0a5201c03401281c08a01008103028403c020f0045580179500654000c000e0740d40d01c4003826005044440101c80581c0101c3c10860750284608040403400d041f20b919038040d40c100900903c1c121780a601044400788 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 17333693 1250 17332443 17332453
    0xa0512030909090a02030c0316030605060d050618010501080a081803010213080304050a05060c0d140d0e0f0c09010b0406050d0605090a1406030705010c1103030d05090304030302070f0b0703030e 85
    0x55440d14000140528643d43c000c01c3c964030300d44100340c50a8240e03114180203408c40c0a0902c2980752101c2401c0a4980c030001c04904c036079403080481c0c4541009036010305544251011301103100902d40d0790441000030039009100e541e807640150742d41d511801c0801080000700300004a881e4443c6101c00e61040ba004001603d401d003c010040301700035258018940c5078000203020485441c02c981ca200040c2001c2e42c00710300b850100304065407a004512822418801007c00760500e81d4000011100a0b01e20310f03008000038090b210f0160380e50705080c00400210720a2041e56005444d051801c03a049038900c01003c0d1406003414022202c0e500b111401d0140e25072648400b140710343e01d80c81250b20810390f20709d0020300c051302c8009290701c040c4045c1c401030182d04025030031701030360368001c8412441076007100280c1429100340000c40d01e10710075200c5d0b1946040c44c1c5402e02a00000210060046900030b0b800c07039281e0f98a4050346c1010001034492010354100c04c205600000b4040d80102041c1134000080d50 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 17334943 1250 17333693 17333707
    0x114090406050901180c02010c0507060b0d02120106030b01120809100c050a03030b09060a0302090c0708090a091d0102210901150801060503010c0503040206030403030504080d090f020a140a051203 86
    0x14406000c01e81044d11108100c0600800170f091610a80c0002c599070700c000d0200803400d54000c1c040e03100d8407038041d14503a218a0743d40c2440d11000c102020655000d420000c0e4941003070f50742c60080110340002c55203085424000180140c003402c0395248180c01c02c018625055240f020010708095050f03108013400b85508146010a109000c0015071300d0003510003040c0d045505042011000c402000984541c03e08001800540c4075954481c1d4060752240e05540d841d500e5061488480c0190149964172088002c1c0200c0d505200e03400000c482c5844410301c0b4100000300200c54241d00840b02402908007202c0720046242e41d020b4800c44d0004c0c2c0d1a0000a0003076025207101c00303c908581c03c00320745a9180d207010489030a00348035601c5400c90500c0c0c0982103040544c0001da062001900150170113456401250900003024201d0b84484103001c8104102c003a1403500c0c0302820b4001000b40e20a424008000070450f5847c605c40b640c1901c01416804400c1c00c0208000250a40001c06da14030320080c0020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 17336193 1250 17334943 17334949
    0x1a0907020a050d0513050904050a0605070c050f07080c06070503030f1b0a0215070309030e100306120b0f0f07051204031107030804080f010204060912060b090117100506011409040605 80
    0x1000d14a0604d0383e03a03603a242c0110703015001c9000182d20050041500320304010201d0404a80d400f061039001801003038640303038900212a4002c0c0c1c400302420502800d15031610a5030001884d1041b9107482042d11003c0c0c0e1060104403040c00354000180c0f03a07800810001d030017044010701c80703540b040e8664650460303032200c05041105608025500340140c0e103da1008a565403071441131719849001e81c9428400c44003070350340060410701750088041c01003d01010002d141030280c0c003c43c015050ba1081000c080d61541400019510b007900c03070b83d07041030000000c44c00c00030a2500fa03a114098a44400d03180415044000c3d003d040d008009030108801c0c030b1100b02d42504103210041c000d50241ea2a07544481c00e1010036404c05203500d02c500c000340c1c41080200002a0001c182030b00301c0703070304041140c180f04190400c00082e0818405442c3d200050740b00108944a018015403030800429080720541d1041c03011107000c03101c0c103a46540c04107481d82c6805003055191001071004450291000c20007a03911408 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 17337443 1250 17336193 17336203
    0x20306030a0b0f0f16200c0d030512070207030f02060d0e0d02030d05060402031005091f0906080f06070503010b07050304030f08031e0609010302010c05210406030c02011a0907020a05 80
    0x21011802c038401061100c4c4d06102c402d8650051449803001510460f0360401078030145204480f8403211003546454014020140f06a280b160300180441580181c1841d008207558801c0d4211002e00740e0703000c00315592a20004184c4241c070b40c00603a00d17081840d1902040381a404c4031001d04a01c64480b140c41c103003c481803080081428460300103584404a01801c0707400e60360020000380c06a441402003020313440d10104150221941aa4036414503220540c008008804a003406c040d400c0b04400c001619011302d81c8500c040761a0341d420348015181500100d501c84005448000004401703000521a1000c01c00003040420312500840346015a25900c01b030100015000c29501020044100000100303180c42115001611030100885881c201c40050a015418000a41004560807030b050400c2404c2005070ac440d01410145501882d01e020100c50a6100d8061500000d0038070390104040d80c0140500310701031100384102d07111400301000340002c036800103140100b1486038040e039002107081400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 17338693 1250 17337443 17337451
    0x1c021308030406020d03020f030a020a0c0506040524040c17070e0c0a0816050409180212100c0207050f1e13140714120414100905010b120709020306030a0b 68
    0x18545841c9030100190500185c0c503a00c005150040290405c1c0728400000c40394041c401800050b120644440116080026a40c00400d540308074411f1000f884800500e101c8103000c801d01d4041303021242ca244029841d0141d030028400c0c00100c3d424010382c0303004850b00012403207240440700c48070b6903203998641200081c1c602c1c01c0140f9000620580b125441441c0c6940710b4501a20225007114006000300a4405d40c841d4062542e52414200300715803000380300100d5950002d0003825420700c402503c1c0e4490300e110320380841e0310746042d1b400901c860001c0b072024212400200380700c150811590074401c100401c41c0803000800d032501c54518948e590f0b402c41c16508200d488000a11f8000c103221070308602c0025000c03006101c488a100307800440000210b0b01e0058940500010030b0b02c4615000084010b41030110616000e00040d00141403020350040310359900030307402401150b0b200f03c1070141c1c001c241d405402ea02c3e04100000e205001080d00115040700f80178049070400003481d2107407440404255 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 17339943 1250 17338693 17338709
    0xc09040215180906010201090203030d02030613060303080609090c01021b0607050d090305070509010e0403030b030c15090315060306010501050a02070503010c030207020102010c0f0801090b010c12030902030f0f031c0213 96
    0xc0b4050741a040c40351140d64000000e0008214045007074002030360728002c07001e28803600d0341c00000041c201c1c1c81c1c01c49a503248100122040c0142170310391902a060080480c2d03082d0003030700e00c0b00005911100028403501a00410f030040c2011101152a0000f6014030800c20340d00100204000e0307000400070080302c07a650010340c0c0d44c1b4401038190301d8170390b08104045e401248160401001403100c1d01408903000d802550608000842494540100341001d5501c0040c07a484a080510b981c80b8075501e600030b003100241241550b040300300d841894662131809440303c0d038040c2e000000512255014000414401000e80112903030159902c1c0060b003500c04100280c0c0000341c01244c00011944c0900442500c1046410407640b071000c1450020215407051150803140343d282c40008140d070340101c01d00e101440e001001d40c80d54529412001d03010348420a402c901a02ca41c40d85000c0c000401b06006070100142c5000c0c61a03c44401100e102141240000c0f43c1c0300d907803c2040414508104d135000005002003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 17341193 1250 17339943 17339977
    0x1206010303080a0903140903010b09040c0f05060403050c010305060a0f0303170c030f04030e150f0309060105030a0f02040c111005041106040f09051017030304020405070e030c09040215 81
    0x9441c00030007038807025000c200300fa810603401400180d0040c441c03800c0c400208020640354120180040c2c050543c481c0c41c507401c042c5030700500041c0b044418141066039030048403d01c016940300103106040c4607603c8042d2170f54105840800140d8440c3d0855600008014004420a603d0746188980f504e5191320071004a100c502c04c001140b00700007071a41d88450f40b20005815403411651450501c07000034130090030010140f022045650342d10310243c0d600322150034016140c079050401920070b640151000d0710703184907140000895150010303058002503030040c1070348480c51441e4207020143c814040100284402c00104944e054002c2002403801803141e44c001c2040d00300750038100b0001041c01d0700e0034001c40b010002032151007004110f4038203c8500c1000012030707984e0141d10031002c9095400101b0305840401222658403000805540224000c4608005540711100e0940b040304902c020907405410481a030704891400201d056801f500140c926480540a102c5e164003541c01344841d80c400140d2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 17342443 1250 17341193 17341199
    0xd0203060a0507030c0c1a040c090608030301030c0b03010501050d020d090618060b0307050f131401060513060207031a040f02060309010c08060a03020a0312030b04110705060708010b030a0209010509120601 90
    0x4540240001c05d0414100011025190b40324110592006072141150320500070219041042e03400c012801451a210208001c80e16001803c0d1603a00a01c02612802c0140301c02140c0103e854040742d0403200d05031034141c90018241e005001a401002007440c42d150341e0740c510b801140c2e090103545d081c15502408005224141d10b046070480342061b49443c040e03401a0000e0016403205441001400c6088800c4070311041d41f00c0290001e0030040407100350b0300b6091400000d1064001010b0b181c2e1102c01125580100d071034480882e6608500c0c8805050340e800640e5051b00603400fa034030590014000c404511401100340c0101c2c90030740c002c2c1c540192907951018030481c80c40c0e000507480d4014034101c902c01ca025140d03400040c0121150b00025200b04084010041e0441c020b500540710390002420078091240c0c1000b2040c06504180d4003545e41c1d002e00c00006806912402c04541079034000c862a03411511040c140c1c000940043c015070341406402c000c0740c8090781d1480351f185160405a00144810340c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 17343693 1250 17342443 17342447
    0x10021f0501060809010510060e0d060c0e0312090102100c051204080c0c0414060103270501020310120210050f040506030903040602010e06040804060815090a0e071403030d09020d0203060a0507 84
    0x801804c41c0c400d6490402440390116065044008075030a43c81c02e4540360402500286e901083c050008000342e1a0601100000c1e070040081031344d20a040701960142c0c01140c038610054481d0400040c0180c00203a9491a41030555001c506680c807e40340041c101540c00c250110035400c2510150744c4110082040b0700300c0d03041000303481101442510b0500140c100741c00c15031800b41c030240c1042c1c145911030000c8060300111103c00c80c204585441a150701c60b41d9030501314001d60041e645a1190304c003030389000c185241d41c0070303801000350f5014120340140a140301044900d0380101c40c45000d041010000058a0307a1181c01850007056908051680c80d0710303041010b800c66690426200702c0c0c0e04800c00300701c08515503506840444503079060081c81a03583c03c1c84000d4214200e2105540301503001c080c00810001c9030b20102031344070304400306c910864230f814203000031421000e103203940350340704003c07012003207070a070304059460f51000e009180ca0700d145038002030402c02d003110940c031555612405c100e0125 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 17344943 1250 17343693 17343707
    0x30a020c100f0c0207060c111915030b09041109070201020408030706020d150302060f0304080d0203040615290d09170304050106050604030803130f08041203080105040204060206010510021f050106 86
    0x5083c0b40020200c2c40c0c0341030340140102804003030141140c1e00342d084d09801c070f4561891540ca0721001c050703070300e614603202c440d070941510a040340540000d20345102502c4a00300480200d0050f0780010182c2003030800007042180801c1d0040450702155028040020b48050800c00781060b9442400050307140e940307419011040380e41d60101d600e1548001c0c40f080000d43c603440d0844100c07185610280350f582d965030600d40028480c040411005030301c0002004240f2050f035200c1c204006d17031180e0810009a5a00c9018902c000580c03180116000c458032001c510f21007140240010707101084080343c0b05541d0385035000e583c1182d201900c08038100004020030000280310300c202519046503c03d081500f180c6900703800380002054030b001072a40b03505c0d540c107011480b0040300c0c2c9260700004182d40e85840b03030002010f504074104110003180c1c0307410002c00c045c5064000c2d90190340e5981e004000301e0303107041c042000403940e5042150a60064005143c1030301100720075180200142c9c00d01095075490144014940 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 17346193 1250 17344943 17344961
    0x3050105010b1b071415090d081801020708031c090b070503011a0403050307032a05100b040504080a18170325150b040f020d0504020f0603010e010308030a020c100f 72
    0x113078105000603c01c00259002448000b02e06580310790b411680c000c280c0c0c2d0b841c4141c44403a03a1210484807400200b10076040204140c070030301701503180d0100c2410016a59051180182d0308130303800500c5104120707140c40003c10045081c005002c20300745d000344c540081d40300b020360f40349000900c0000140b04124410f1008041a003080b0369071403400346940c0398991603008600e002401c00458800c020714003510706040c1007000802c9080c1c9826200d091038000c1d600c3c5894017030450041e0400705031001d641360511450340300c1c2340c01040f40c0e4a05050b4880c21909030b00e40790030040605000000203d129550700001e4400d6501da1780003103684802442d00c550040320080e4112a1220910403400e00082c1e040800e10340306140b0242c0420303c40400300c0040d000d07000c42c0300c440c2181880406e400301041111703048180110b0003560386001d01818101406110320003401510409a07180004000142440c0001c513405485110010301349232106c009a414000360a8400801c16100e402401320380c2207a1084a0708 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 17347443 1250 17346193 17346247
    0x91b0409090b0f0c030103030305190e010905060c0f030109020903030417010c09050f010c060f02040801140103200303030c1806040306050925050904050a02030105072304030b0f0603010603050105010b 88
    0x45261442d0840340174401404000d04061701c460104203a0400c54882c02d1400709405000d01410414010303170350081a0071442070312030b48030305800304103038201203011221080c100d4802a03287d0b03807c04a80e040a03602006d145d5405101c1000009000000c00080b400031840e4080045403110700d01ea0020708072140e641096219007480c40d00200d807a82c00c05903000384680e1103440416202d11400c0040024001d42d80000c010f0350821080b880040c04011a450503248180c000100a001c050130200c40d0800080609070940e10400126408041d004080c040d40454016030341a96880f000100310107400560003106c4094660090000d5420f0903c105203042c400032010442488919140348215861031040340c1c003400324a400302d0309110013440b40c040c2c0290080c000340b150342061440103000300d0b80d104031016841d00c10b102848d08001c1d120700300c50482e60000051117464544400c946030140019141d1603042d0360742d62002000500238080c3d1030081569102241e26280010340801245a5010320901 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 17348693 1250 17347443 17347471
    0x312030b0d0f0201090b0a050c01060e0723090a0e04120822050c060f03010612020a020307030e01171504150302030604080f0705010609020901110d0806091b0409090b 73
    0x4948844085880080e0420b440020309502d500050700c0340030040d0403004040b40d0000d04107240071f8105004000140c4003000030002a81e07030760540c156940041e80c1305000900c0d4040300014a12064420304802c01d4101c500b1403910300c0707907000203516141310b900140c42000e0b104208801d01c80050003d01d2401454284034001e4544486505070581840782c000c00b14000440c15202800000c001e0000d8090010b0421591794000d107641c0150ba8000342b040318005101451100030284042c02500c05c03002d420740045050007034035902520004108800b250400c1008994815212050031009001c0c00741c860385141001410010321080ea04404a4032512410000d01000141c800058555006400020103511144c0204810354580f04810000e40a58203000c00460b4126056006203c03521007600c980001451054105031680b0b521111380e8042003003140000d41c20f00741410055480003600d40754610102c4104803d0b101d039001900301000135aa61a2603404000401a80b03541025001071800 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 17349943 1250 17348693 17348711
    0x106020303060d02101b050610060f020a06020d020903100b01030f0209030c060706090507080f07150e01080601091a0702040e01051303180e09030d05070e1e12060f01031203 76
    0x1201d600204000038041c3c124461781d40306032071044078651854000301d50b410041c0b28031410000d40c0c403d4140c1e2500005070400c14001200c60050034034149044183d005011404215100e035002500445200150140c0801003402e1964040c0504000200080c00016403070640b4000103007141d2114144208441c41000200e50582d07000610001508048903c503030780340d1031850402c000e0002803000410601c990400800d1400c408504c0c45039910f001000c80302d0003640d0b07003004601480c21414440100782d50f42144503155104800300ca90040060400d0a4010fa491803c1110980d001044d4000c0400100303031102140b0741030050000304040341c0001d10036410300b040c4000e03406500100c01403c0c0400540c0502c0401f841011013001000032040341d460030b10384848060749035800113480070740322840c00d03000940d0785004082c0c1300018000a00070304210b0320901e11540340c40480521040d0303c60000700010307920500402c0054800d0401c2c0c0e01750902c80d49180340001c1a4903110209100f4141400c1c0c2030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 17351193 1250 17349943 17349949
    0x901060c06090203010204090e0f0c04020315090721200c030306010c0606030804150206060d030207050f0a03060501170708010c05030703050a0f061410080402060406140c011e05010602030306 84
    0x5501200d4001d18002540070b090b200280c0244550b601103598142040300315000494049804800c0011000580303580201c5842080120700c41220f4034060341c40303003410040050030b00d03101a42d40300c50a030401500e0a005a5544240b96680c8440d0440c81c5482c1c0510304010000d88850340707030701034401d4401414402c2c4181c07840e440b0300005008334104821180884140300d003079000b036002075811500903a9a04d4072176810015100b400c0f50340368094415030780480d41c04d0a28200c5212801d070164043c01e0807500f044d0400c92414140a000b96228031035a80c08000321740c142c42203034000d00604001400c600c2d200440c6c039050a01d01d90280740f041c0d02d404e030000c10054004e41200e9000003589000030311075841812080081c01c0303042254022919101010414000c2d021071003241c10310840b020548040d06030703400c80b0118401c94000750804410700041012a00549010001183c138074030090a0000f003500b803608403901003505007443c00c15046c0c00b900030601c0f445140c0c05085203101961071494240d002c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 17352443 1250 17351193 17351207
    0x140307080303010314121603030c0513060503061201050a0b0a0506040f090c030603050f0c0a120305070209040602091f031413030c0c080709050610080403081305150406050411090106 80
    0x4c0030708000c6251140090403a41405200a10801d1500b015203031107984061182080c542402207000c030b444d043c05c1d500a140140c0545010b000c240040c00903032818000225070640010303003001c0d0404120303402c40812010078000c0030700c074413490f0360b0008640d40d042c003c105845031150f0080780250000c020a02051213805400c07000c5e22489030020440780c4e014070049005007210303400603042e8001c2d240842005200462402c030014011920390030041d0702c42e00c04000070400c840d001030208604109000050508000c0564440e0141c1c1c00141400b6403500072a1650131211080c001901c3d10014111599816114200c0989100d40c0ca403100c41c50305103ca48081092204060244410b0300401000c100e100c103403000c0074080c06415200c050317540d00302d0180600000c0c0c818a200d0b210034070300501030340e104071b410780d200d5509681da5060300c3c0c85040e01c03100d825104200c1070b540313030180302c42c1018201c050483c0c1c0d5004500c18000040d00f0b20381030510410321100070b0850791042c181c2a004000d8958003200c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 17353693 1250 17352443 17352449
    0x4050709060c0309030b04060209010207060e061c090204061701050a05070c02131d070501030b0402071e0804090606080609090d020c01050a0314040c03030807050702090c07111914030708030301 85
    0xe2031908401c06043c00c1c1c4040004e50300041c0b0f1884128200000c001d101c0d005880301c4082078080341e290b0740c0c940105540c40d1000c0c149154012509028002c5a50070a240241041c0c0074040c001500828503000b00d002e8580a0f0055035201191419504000c01e0901ca0381d548400d68200411080c24469001030495141c0d10019204400031040440181d0702603002c42d03240030f5844a10000040003810080c1c50701d5080c840e490211346420382005490500d0f00031148125130125030509403800031001449404c00202d030130b51b42e0386000d100105505a6510415020342144d8446114514200301008060f020040180311250003403082c60b0100360300000da50340d21120034285542c40e820096400c03401003021040110f003011045091009005d420540402642d02903520524503640c0ca240c242d8803881001e8009401082c03103000640c075500400081d0422921590004180b010780700005128007003090040741c0000703401c4604110201c0da914014408000035805080400d15109403c1c2c1c43e800144 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 17354943 1250 17353693 17353697
    0x5060109050406020910030506121606110307060908040905090f06011a0d140f0f0f01030f080904020a03060e010906030506060603060409050327010309050a0201030902060d0905060f060405070906 86
    0x81c000c1000c110b5650195071040d08068419400c4280c810320003400b030070b01034521a00422807a028080611004a14102466848000e0303007210740c604a421501d40f12a083c466540d400107000343d50000d095401071848840c096a080c50b04c0d41d003461100401c83d0000740000c0d0007540008102c040c0301e01c001c6082c034111004502006400460041c00303030f140f84074503000090094030b4456028038000030f10211602444400b0090280381d0ba5060b450900c18005403507007035a0000410040000440b10001310750094401c40c280c0e070030020900701080c280d0300443c6030080805d40300ca1050080c80ca200b281c90340140f17040030080c8003a0f0b185032a01a220300015010350b018480010000c0c64a0b15607401610803142d01c40c00701d950f920460b00031251142c9015a1003c0c0b140074201d0501c0c9550300c03034094546081d4021002d005621142e90045d00181412417040340c00c594244841c528003c454421007603841d0140303010704003070324100032042d14841d030007800740340300c1c0c1e1421051294040d880a80c10043e180c5078 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 17356193 1250 17354943 17354951
    0xa06051603210f05040b0a020a0219051c020303040201020c04050c07020402070204020408030f0c0d030b0a0b0d0b0303030106030902091317070302070806070302180d02030d030f0e1606090b030405060109 89
    0x2400310b11682c0d2000c503001c2e14215040400c2040604020751140313200d180a400720044580341c0e140d14400341c0c420710341c103000164800010105140004105000024841c4040300c1d0700703810707462090020416008820700580c201100b00019035805005901c5a40c0c0102c50400c86442c000301d45a045002d0400083c0c01030350301283c0b441c110b403600e41c1202c01400d4480c0441e0780315400344100384201d0b4407803181c40d00389000306071a0004041c001d00880101da50001c190301c0b461820107000300314541201c905001c0590b203800e0880510344040c00114041c0071582d5012606039141d0040c004010702c0540000c66041001c08018041141d5284030998004180314696940c030f41c50034128540b8244e0f800c4040c00d40107407000e001070310741c265000348810022b0700e0000100a400808102e9a002140c0c1c0280d0141c1111802810861180e13014900c1480b81410000c2c28040c94407001d031500c085004d001742c8000c01540140301a50700050200018a000c80d400d5255150550311b264549506100f414070300f54403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 17357443 1250 17356193 17356217
    0x9030f07050c03010e06060a09050702060a020c01090b0108060603010e1209240a0309020a0509150616080403060501080f061639120c0f200901030507050a06051603 72
    0x40c4000d18802d40000c00a001c82003004051030b495400c02d6031218480d00c044480050250007600a0910950301a000b40029a03211420f2a010350b00c54510300f40f90303559440c60200051120083c4038040c2c10241d00a01641c545a01854210f0300b04e5225091154041c860031b107150710742d1600300d0b952400107036040040080301e01041d64003041c0c1405120514500070601d92100c5a05a005496140c002c441d4410542d54030014030105120698200f0f20403003589050002c1c034284a0020500840b940c82110000e07040c0c1e4640050b160056001203440684890041085841c1086103000d0307820b2a03009890703141407040c141108440035000203002c0c00200350300c06040c0000852031f242e5040c48074900c40142001e003540600d80440c031800071104840c42c15884807149210b411400300956121003040c0c01c14001740c9400300301111459190b40070545046010b0640c0e21750404041c001c41c400c800800304141010100901014250030110400101307200320401c0207003080c0444015501820300c4030031241 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 17358693 1250 17357443 17357453
    0x4080c10050c07080109020a050a03050d08090c100e0a080606100f05090a080a051006060504090b030304050d032006070504061d0a060e010305060a08060412020a210e0102010509030f07 81
    0x30b052062407103805100b000040c201c0041d0841501a407080311315452090321903042080e5030383c0600003d4455404040388200b15030080b030f0b90070307005a41c0344100e07526402d000c80010743c000c1002c00c11000045110600414074241203a102c00605001d1010341708516040300401c100b030031400c0900c000c00c4001c00051007ca40904210303014010098421071000342c5840a05d540e03000c0c8030303808a03101d114002000b8040c52007445a501074425036510719103400d01e018607d00252a8558155070305003c10003001131580d40712420300c8107491003038035044504014060101808030500c0c040b0005508040d08102800d41d2180464068850340d040209a00d0081c4019001c1004420003194102c0c0440d000850225040041941150400d03641030103950703948414802411f0107449080c50960000300406c00160a0101c030020307001403841202c03440301145d16503a0100c0d40c1c48180f4942d8422010104071803a60000c100020850280028410b5040004101e55a07100782e02241000c00c8010803d1b00c01c002c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 17359943 1250 17358693 17358697
    0x6070c03061104030b0709050306060d0203010b190e0106030207030c0b0a180c08010c02070f03081c0504080a0e03010b1e010207050a08010515010c05060112021302030f040506090304080c1005 84
    0x56008907041040031940c9400d02d00c1da50290000751403195105c0b0002c0c0802c0d21400d00e800503901d0240180242d0b403282781c1448200080d81c42c04a9141d506d41c60041d03800c1c5c0f1160940c0f04812000c081c420f0380030b45810b51005100c2c41c10303041001054010800e4102107500402c00c8040c140c3e00410740030a0742d07903022905d8024008030a1303188120030500801c0c3c082c0100d44282c9400d130350101008004411a007030041c2c0e5243c00c580314111071200e608c0001c002150500000e0080ca0044040195418803221207070000c03514100e4048400103000b00d22001a1a40402d039540452400da00030807400c5403800000d003c42076498502c0a00800380940e10040b030340f090221800401000d80306d50b40d165143d480c0319019000844020000ca481c9c040c01001e150320444030703407a241d90440090096030f4242419106c524a2200050b40c01c02981d060513501600140300461084002c0315010040d03040c585085e03414244054007180950344140000d005505010440c10000e4108503020384030b0b1850982c09603181c2c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 17361193 1250 17359943 17359949
    0x60d090605040303050712150510020c03070605040e010603090f170904020a0305010905100609140301060506041806050604051302030411030a050d0f02030a050306011b05030f0406080c030601020c06070c 89
    0x680c202402d0200305501504243e0054038203403100044c503411490000100c4401c0b2900e06200e580340030042115082c29012500e040c1c09500c1a115486074040110b45440c000790700503400140300003000c10109a5521180b4007407c030600d010700c9101004d44911035040b186183c080e100c1f120301c84003031400740f203420120390080c2000380c002c2d0745944010401400500e408d200324405a8145000140404013083d00c000645040352616080d00d81026072045038a8804030700203400d0b40d61000b000c2802e41d00ca4000d00002e0661014044441d11828404019141154409401840c0900041c4600d548082400490035004900161256224203001e2880708203e01d00342d07014001d10070801c0074054041041146219651140704410b1013000c001ca0380e07407080d0440e46001407000d0022480e150320850710716440c04010b005001c3c80c146240c0701c039801c40e440308018455400000400304449034005c2c0701d060f8000800041c1a003145002e0f80040c0d00c514908410034450300c0000703255010090207000c40707006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 17362443 1250 17361193 17361203
    0xb0a050901111501140a141011070810020403031b0c050f041104031208010b090607020f220203011703040b07060504030c0b0702060118090507060e04110c03030601030c020d0e060d09 80
    0xc3d50392844410001d82240920306d0146050140108048400020700c500300c00c07010305000c0d848070b80c0303000c2200c10141c078025002c1d090040510000303a80c1c03801c014140111040380001643d541c0345107001b40038004030041003820101c821601c080480c4c054500030080303030000d071490f0745802d02d10740c0018001c1005055580c000840860080180038205d8180f55941c40c2c1503d440b00941d895003600c44042c010100c285500000810140c001401d0a1404403d441300141138000409071940c0b40640009800004803000c66010004109420701040d101070305000c82c0001d10314090400700f0100c00e43c81080005010b10f9101c03030100b4205845881000340b02600010308408074240090004c0d2034003402c0c03082d0184802d40b0056003401d40c409228030706103240c0c4100107111b0030385444015107c0419201d0840e60282d600c24204c8500c1032000000c6c030513030038a10055075492828000260490300001454002c55001c03090b94001150003144281d4442d000301d4869890b070b1002e101e040003405c4c6005004007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 17363693 1250 17362443 17362483
    0xa031d100507020c0316091401030f0807060902040212041106090108042003100f05010504060e040311100e07030213020304081608190f120509070b030a060f0e090105010b0a05090111 80
    0xe0306c0d0303141d1004090300c040880601102d45107040014111f4803e00000e88046520a9200c002611600c001d04400d84170b00c030301003500745035600083c04a80105500924218415003000b081002e05003c209a0755000c03102c0c5400c05806500007800140002c000502d200141170701901c04100e090701c1c000410900404451380c684445c142d8001921842c80c44040d00381c1000000700c2c1c2803a040c0a400c0070369054540c064410741d0b664a00300d880c00d86203070030800c0034060040d1016100f030341030060001c2110100c0003440348510b144184289038091443c1c6a40092060090000041c54402103a4001c1d50440c80807140c0100b070700308200c2d14854410b29028080110b00d101c0c0c0c05641289c286119a1225104d00a00d11070310021002600c008507001185504103101c103108100d01c40c1d0145030840c00803600002e000b07440e80c0d107001401401b50001d0580e5100d000821501d0b0200b4050302e40945941c5c00c9250601d07005136005800390081030301440c140000d0008100000004001141280c40d019503888 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 17364943 1250 17363693 17363713
    0x5090403051b0a0314030721090b09150f04080d0606090e060f06030a020a050c0d0203092803080903010e0d0305061306030f0602030c0708070302030a031d100507020c03 74
    0x16106912928440721007250091001d00041e1010401c0b43e0001d0b05500c950b0256032401e4102829503000402c8401403040620307024000701c100b0800c0c40303d100001100011070ba00075042100740d208008109040d1940810000751250003030003035980c0c00036004800110a0f403070b14174109481c1d0050078018503002d4944500081c1066029001104848c05440740034001d4555205003c5024212041143c100004102066180f80d140c0d0040260a003e03281c0b46003030a03a00c6040740c2c04c0000000401c030040e84040340c1d0044518090307840c22030880c05411b415005000d142a1029210072030f10000e01403c001045090554400303410482c80281c20000380c401c400c40d0601c02070f00806040d160705018074100142c00d80c0c01c00c0c151145409490700280c16001c00b00150359207030082d52008101c40a00f14050040c000000c02d6840a840302138801c0d00036585500040d10700400300c80d02e5001401c0a10916505011208004501c01d00200012613010a44c0d0b0390301070b0164031b000300412580f501840703203220171 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 17366193 1250 17364943 17364947
    0x20f06040b071403090604030806030106090603060c09051e01030507120207050127110402070501110705010c1803020d030e06090a06051308070b0f07020a1d0901050702030a1b050705090403 83
    0x3a200c0c110303c0c2c90701942201c0070b1000c5800b0f0300084038100c90726449680400c01203400b03901050340c0900020008507075981c03255210402e50300c0d240d2040702c0084d00d1740c0b03581c0c41058004904401408040e00c1c804a08001000c00c0346002803000405410b01d561400465403140c41108115001000004103660720741d21868042d000700410307910703a81c171020044501540441c0d02000003040c1c0c0d030031040e9801031312140c00802000794070001c000c880a41d82c0303840d01c1c0c0e02250068090030071140507100005200a803814058a0324092150780310200c0e0f0b0039107040c001a0703201c0d1065044d290b054904103800d044840d000c246a48a0b0102003030b80201001c00004003268008000e0400ca10b00080c5c8040090b07440d6000f56a40c2c3d141d000c0c1e000c018005000d00081121b0402c00780031010300003000d20802541e1030743c0302d40070396010844544400200c0410000341c20340034011160814580c0c03005502c1e06680000050400a41d00c2c2500c4a0f4860449990305000042000710040c0c24018144445410310f4a00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 17367443 1250 17366193 17366213
    0x103140c030709080102030603070e0c070c06080a15061b0201120f06090e010b01020715030204031b210209070c020409060e030a08070c0519140109050f0111030c0d0b01020f0604 78
    0x41c140051070180c1d001c40c00203018007c4e680550006001402d007503040081e00028042c0c0109218400c0c88184045000704000358000030007800d5503110241142820103511042d164080103658035002c1c410401c000142d440001580e0112402e8002c58080c482c620040700c601160b600503d10981c24541003d40740190765100c84200c42d280403041060350503480030035080c1c651090b1a14090f03004100204034460f001c1540d40043c55903854018901500da54030800b60381004507040386000d410100a00400c40744061142524200c0c0c21041091003050380001d0f00f10800421600821013100c500000315103c03030b0045161158094010f120607480c805160740d032500194040740c0014041130105140c3e50140340905441600034000e000b0423180500c0080141c401458103c070566401c200803644d0a000384a80e0351101e02c55005088036103c407901e410f00350303000586100d10310300b020010301c01403080c494102c841041c4202c50101d145c822020050303040c40c82c000b000b00f40034006c0900b0070007000340100d9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 17368693 1250 17367443 17367451
    0x30b01030b12060105040e0a06050a1b020f06010512070e040b04020f1801030f0221060118020405030604021203040b04030b1f050303070b061f031a03010513110103140c03 75
    0x190800c55203103018200060320442c42c540b5900c641103a40103000900b0903800c241d8400c00e0b600208e50b41a1500d42d01c44040740d100f21843c083e003039640d0000c10a00000d224200b14a01202c0c030080601005410101d0b440d400180314051141c840c2140000205070140035450003071548510080c0c030380c5018100548881c0d002c0b90100d1249000c00c0200c07456180020000c1010200d8209420840c0e003140d46030020340030002d6090f6845420741010350744440451003000200400729000d000c041d450200459000354182c4180813842d4014041403210b9100007411690050301140c50702804080310148a095115642100385c213131400023000b00034042040d2031107002c0d0541c0409036078040317810b81e40d2070313050b000a003c5c0304d0341600200160000f2411410416420020040144040380358444018008400b10286540422f0300c6022009070f20300d020340c608001d1001074000b40594681909440c100c1075094000034004950f00e0300d21019640309a011070790800a0000007505410704015403880b41d00111 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 17369943 1250 17368693 17368697
    0x30309050a050315040303050a1107060b011103190c060917070507050a03020604050f030106080d03240608070819090602040e060409081e0904140603070b0403051011070210030b01 79
    0x180d80055141000907090304c0480da204040441610b4036035048019041c0600013290b203d440e0414062a441182d004020030f602c0b401000503500200c40003d4810800803200c0c4401d0f400506c87d075008509404103242010724640b80c0024220340b649040d00080403c924040c0c51840603d8408205124400081c81c041d40128202c0388055a602c1c10045400c42d1400020b400203020700080005041c41d01442c0c0700c0c2000140003180542e10f4100c1940780c1440d080814001a0303c420380d01000e6a0810740211001d1421089040c00c44e00b85030b0007900d8aa00903000c00308008800c80040d840d2846a84000d9544100b20000c1c000542541086000303508070740101030300c0d2050031004c101c062034a841a940340790741c0325000b1410244807119017500666102c0c0390f001c0e203e604200d0104180d445203e42d40e808104012401190b04010301454945062360b04528034900e030070081440460300c0010501c18038800184089070100d4443e40c896618010803038000d41003030f41c448290402c2034041d000101d40c1c82003a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 17371193 1250 17369943 17369959
    0xa020109090203010317090f030d0206060a0e040206040605031905040305030f0106030c020a02120106030b01090515030706020309040f0b10020d110106050f0d0f0f08040305070b0c0303070e0a09020403030905 91
    0x601d001c04100d02c020720008049885110700b0030810000c900191042d91801050700c0c000348205d40210342092042404c0c000103802c00e4007084442e01c1c224030320b0400b500d50604660107516056000c1000e038842d5004000c04d000b4084005000c0c82800c80700700061655501c010702c000d047c503140191454005450f2110802c0e003000011880c90303c01d2003000130580080e8000c102104464090015201c00400e8414055403150b4020010891003900d4500030041c010000034945031000703071203082d401c414042612036008200100301096000043d01c00c404803c0f50300144c0c1d0720032018000002e000c42010642c000201c03410030b004242c0c000c24044812182c540700e0706004c440910f151800c1f6800c034090190b10101003100c2814604102e42140829441402943d002c00314a80f18500036a07425030341103c4200c030014060081080501c01070001381030102040303003071402d041040380c0c0340e0100070045c0d8104112900e02c0b0384250703907040140300207260845046559a80701d00b00201000d076603000d00350160b00c00c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 17372443 1250 17371193 17371199
    0xa030e010507030e090c040f060e0f040203010b030a1a10050a02070609120b0c040b040b0a020c0a0302150a0917070504050c04030f0b09010b0a0b0c01050a06050307120213020c0a020109 81
    0x40080b140c5580d4941c0d03402c0000743e2050200700d40c03124054801840c5da10f0a10000c10381407400c072249000b408030f40e00c2d0020321100d4017003000440306901c40035500650046c40104a0001860103aa401003203019004c101452120504200042000d10103903008036228030b1514034035000001456600069426101c1c2c031503c800081e1024206407151090300d030322154601c00410803c0ea451600444000b40e0f1a01c0d196407003100301001d41084c2c04c800160040050b4001246404211600418506486000c559031450f000070300e8140c1d40c108021110b090005800700c2d80e41c401e0004074003804544076005034103040c80100d5585c80d25940a018051464280490805111041035908507580300042c45804009aa80d0840202c0b003e00105403035903c0d090f01c044107540b10544c0002401990710b916445812810055094034070107840e5500003840c0450900a5440214100c82503801620a4810520062000c100407266180000021510210310035101c0760b004607001146c64002d80e2250840360f1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 17373693 1250 17372443 17372447
    0x605040b0a0b0306061905030a030f09090605090a020c03070c091a0102060937150b01030e0c060f1606050a050108031305040506060702030307030905031006030209060402031b0403050a030e01 84
    0x100030300e001035040e4408000902e203480e207141b00b4500c045908403540c00640c0e60303002103480c20f00604411804220141030b54180d90340d0001e0100000d10102009004142c9803802041c0c2211002e80241d280580004400c0303104282041100e245a5208500c054004d64400e0791000078021040b01c882006602e0541003441d43c400200d20b0300030040440030b082c0b0004d9910f400c0ca858125445041031102d000450100040c2c640c4002200c514001c54482030404407441c040c4d421180c5060255040c035190904449100c41c1c0003414407200d00c0705461082e03503241c51003032240160048a000e00269180c51400d101000381e075801c5103004900c00c80060006903202d00b8129100c4c0210040400b8291801004200302d2a09411207034100001524441ca49940d03a0042801c560001c402580481c8042104100c0303414100414100021440802c00c10141968005407810340e01604182c401c50b00400461503400041d0240d00d0792074006c0d400c503581e0311341d607140454590b80202c8041c1d002c50f0365070340c0c5140030f54 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 17374943 1250 17373693 17373701
    0x1701020c060c030604061503050901051b190908030f04050a060e011b0f06090305030601020607080c1b01020f040e01030c0b04050a05120109050304060c1e0302070e040302010e0a0605040b0a 83
    0x2448040074004540e140d001c642c44a41008100540c0152140c60000310f00c100714003050360703403590f036900480c45180c0f0700c8055080d184003502100d4644118044500d8001c6100143c0d1201c4d0417030052840500c0c02c201045405000d140c110310403d0200054640c0c9800205008000300d9100790385075030140c2d589060580c7d02040906035940072546030102464041ba1280180314100e02c41c143c0b04103405c00340d44690003101e030140c00803004103500000b403000d1980c0422005600001500c2e048406107805896084a800342c070b03004202211080b82e05410000080d01138840c550701c04803141e40c440b035464081d00b440c085c00388402e88440c1c00500001c6004001c4104560135144041c00c6480414a00802c0c05015001d001801d185035590f403a510300081c02c1403000300000c00403a81c4040b0b0a10090425240144050700c0340c03042028a101e2100000340c005ca1120100e94824500940d255181d050903805850140300d44151402071214440c100140d41c0d00032801a070207030700103801d2070703032008403076802c039 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 17376193 1250 17374943 17374957
    0x50a0803190c030903151a040903120b1c03021c020a0302030702310213051207060807090801090c0e150102060c16020607050307021c0f02060708040b030709170102 72
    0x1440190700c800441070040030b003400b180c1c2c40b034a003410b0380c15566110803110082e00203042e42e61680740c28402140c4184c48400041e0040c01300c1d000c1208640c01c2e64058510005000d01400e11074130b86203140100d81d180040c528040c41035a008501000e03031481c1c000d4842226000c002c0554035420181655180300040f45007500740e0580007949030403003680800518410000410142d0080b4905500b0700306007010001e03203140780101003d0f0325121850017540d900502d940100f0300980ca44a095581c80c200054140202da0312410040300c9916260012290201c69801c43c603950760802096400308808800c00d5070413a10580f120712200d441300080010749440d02c05049005903c8800810382da55008802803c1c0704406006580344808a03601142d1650000c2c2c200361a00d41022a0300400c0d420080b41180f0104070341c8039038a4030300c412540c0700402d0420642e4007030300525022941c10100f041901c11a80540451051182c0764a4110001450010b0501540400844c10803403501c3c0c51005009982c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 17377443 1250 17376193 17376217
    0x7090e04020103050408090415030501050603010b060702090402040b0607030c020103060611061603230405150c04030803060102152802040602070603090501021315080907030c0603020714060907050a0803 89
    0x12600c464004401030803000e802074854560030001501c10707641c0c501c01c4141072400035a108049510f907040043c2100e20040440e4081e906200c031580b1103582e003c04a520b40c5034111100c0503661202d0001c80d00921000c40e0698010038002030150515800903c910301c0b55100740e800f0300c102a10780d00708072012101089201c0144e80154081020a40740009155100b0100d01d000604017079584485001e5004080001c074140d1581414001803160500c901e00068a41500410142c1480c2c220501644100d1001410800d0040086004ca070300c20301072902d4600c014032141c0f182e030600c40320071819483c1c03c0b01c00b98440c9465120102583d6118001e40d412103600782c0240a2051400740700341e01404003940304a400d035508001c0003460052022101010300000c1c1002030906a00c03c001030440d400181051596a005510400c0040c00c2200c20740140c03005464056203a017514904074540814216580b0494020501008a1050006058011520200c490840c1c01da52481d07116181e100b03071818008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 17378693 1250 17377443 17377469
    0x302090703020c1518010e010603110105031905010b0a17040b0a090201050702040606111603020603060d080702030615030c060909070c02060c0102130513020a02060106030e0102090307090905060709 87
    0x600301d000e40e002d010403001480940d02d4000c406850b100e80c0181c21907241980c0b2000015000e04820248588034113244000020030205045840780420740412581c82810032100000046030001035101d03da085a001c0c1c3c4040c000ca50311aa0a49050b030009411180042e4070304a44800c400340007800d5a0081d50004407401080e00c0f0908194064440302a0580c14081c1c200081c3d00140c8540c81544000d00e0716070b8070b0f00d40c610160069241000315440b240e203141e42a49400b4005a07550344212600468111069140703110f0524181d06c150003200c8020f5414024a070070080704030010f049000802104805444140000d502005014050040760507040101ea10000d5807031805100ba120503240000c1c60641810001910542617900c110301740f040340b0315020010801410080b000b40d40c181c1211009504060858800039622041442a00101922107401c18021178081d4116089080064203481400d40c0300c240c1d0401034000280120b0301c0344252400100c50310300c1581a5800e490080b05405 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 17379943 1250 17378693 17378701
    0x8070503040c03170c120403030e0a031703060f060c0106060e120601090207050a0510060311040509030a0315181e020a020a06020903100603050a05061609030f0804030f1406010f030209 81
    0xd1140203420360f50300d080c80c50400841c0e0401104010075150030350000c40440d41c80d420361500418001c1000034507408bc1c88071100600004031032843c00020780170a000e003283c0f42c0e80c4050008117885030b14200547c201c0e0000074045803095042d006101a2501070f101c05181e65040c1e003d00c07000c410200c21103400c540080c001070000429a400a12246000d00c045a40c005030301c0d01c0d2103040c84207859803220406c0c1d0720481041000030800c070803101804200d80c200058070f451284c440e101e00c0340703224200402d6078030032052520213001141d00011b0302c02c103d01840556407c03540b0000801d20400002550105031859002ca00e501c2d0003129892006540541070805140e40d50b20040d400902c8941e90500410341102001e03011841070100550184008000e01c00481c05d09a04040000c2d040031000ca01106050b04402c2c0c101c0c1c1501c00700c075444203001d0890305440c02c04007080e0040b42c0005025101600b00c11050001008513100031400c9031301910f840d642c1c0c6004c51204005248802500441395034002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 17381193 1250 17379943 17379953
    0x601110a02040221010b040e0a11070b0702150727050a0e0705190309030807030b0102070b1b0303010603060602070e060906060c0307121e03060815040507080102030703060608070503040c03 83
    0x14043e0784002810311a0361408090710815240707400d13000311b0044400482d0820110304a2134500b504140407001c20000a0f8a90103914418410b034000a0014039055010444c0320b4403c20540801d51030001c01d0002504010400901c100003c400a100410300540405a4031011880023022107a0040040350b041e4900500454481c0e401051042030000030700c002485090007a1180c40c1c2c150309270303030006018520b0b03140c090300340c12025010f034080514012040d013140e60006840810745564508054036078840e50071141100515685502090002100005009800d50000000c0e14126000d40d00540d4455001e5403540b0021103190741c1c05a046000f007003090030040b0040c40d0b031a1106060f43d1030120f05890305488035a0040584000520303400c045009003440c196a0203284050380340900000c3d00c0c06451540e5403409065800108500d2000b00c2c0400a00304101c2c801801004002e40d124680204060020215403081c1004507581c1d000041140d84900c045920995200c0e100074030342420f40d1a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 17382443 1250 17381193 17381197
    0x30301090b0105250b01090203040c030803060f0a0920070c0605070f0204020c0c0405060604060203040509130215090103060b0309060a0e0106050a120c090524030106030c080303040b0601110a020402 87
    0x3428107105040004609007442c004c040710149013255040080d00100f480c0c50f08507202c059200308600ca00c180b003400002201e1303d091504690b00520701c141c0740d4603140d0004441079550f1400340d6010100000c00180034056810005400500e807820030038588544014807094440c4c68001081800700711407c2c02ba0b00d01500141c54031a0080070b588500c0c801c40d034042001caa1045142114581c04003000c07490030315040c044d0f50743c80401a142c10b41441d2426201a5890081703014103403003115a40d0004400c03026291f00c443c4455002010030324480740e44c50304490640d010012080c0040e003040030110340c24032000d00b1a80180c1e1060010103880da03911405500501d40d03469111500d549801d800201651000384040c068910b1146030500c10b0301d07500c0d1105d0188842e0303002001c1c180c107020400017a11841c0f004010241d0098880010520ba6640081e0040a05030801030824059950110302d0140005c051449640704402d851342549074100107440d075140d81400800d0a621040400c401402e140e00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 17383693 1250 17382443 17382461
    0x13060c020304050a0308090a060f020d0c020d020612040506060303040617040309030813050a12050307080c1005180d020f03030a0f0605040219020706051611180c0912070803030109 79
    0x20541c0e04280d21000040e100000950044c0c40484012a0a000f0b928100c0802c900a0505061066070b42101c050040d40b41c40d0030041c8001840f0020b403075a0259140c3d03959250129600402c200d40c0c60050071652100b00302c05031800e655910a860014126040000c01c91f0706842181e2101c000528055aa8030b0b0b252000810817420008103030800400624008051301c49680c05101031400c40b42440d007400803c0702c0d280d102805000700c4590500124001004031100f0039000902e00f580c0e80c0c00c00250030b01d0590541c814015031458030b000c003c010041c0003005043d051890040d0340d04442420300c22a62044100c01c0b1a0340c2e038100304041469070125500001c0031206010700460b28035500e0780010200e030003d20040504090502c40018159414000d0101400d2a130030b0150510143c1d030f8075240b000240013001051011001414842c1d56079650350407000f004403400b00309440c601200005015044043d449004224840138a03541000104020080d1240d1400031402d50f86445084000340403014 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 17384943 1250 17383693 17383697
    0x20102070209012c040c140111070e01090509160e070e0904120906081510030207021905040b04060506070b0604140403030c0206060405040809040903090b1309060e13060c 75
    0x45080161120b000c0c560080c00404c101c0c0044540c4a10034070100c10809443d1144044004100300008443c0c1480708107881340c10b604441001c1d0ba940040e240000f009852090301d10078002c0000d003004174000d419060302d9042d6000d100503100c10015aa880701c40700d802030800200c00e002807160044074801c103540702c8102e00d041c808100c00c01020a1000005903030503175200044184070018260480c1c4a98010b06441c6010320942c03400080f03544201c03903040c1420b0710810001c04a11950b51080e01a5107901c2e8000302060419000004d080305900d041e442900c0c0110308043d03460503145410f104590848402501c0c0c40d2501007595512052407000400641d4050b07683c0d1108600d1030340d481c228074441c503c87c2e01c0002e000c414045000c0e01e0800010a064486d07401c00080100140e000001d6a401d1174082d240401c40c480a403400f034601d40000d8001410303001000c5201152107a6402200f8101d820b20716003004001e0703c0e80d25142c082c000c1144c6110301844d0007035028001174200c0d40821154082c0f8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 17386193 1250 17384943 17384947
    0x3080705040f08010b03060708040c030f06020d0f020712030506010504050f0409080a050d0501080606010e1201060506030a09030306120b16030204080102030703020408010c080402030d030c03060f170709050f1303020102 96
    0x34028501c0c0c0c00459045462981c5d504c0c10f00307480b6400c0802032290131254605150355686015905c0e5461506940001041050b024071084e082143d1901034542c9404141c800b8441c07249052400e80080d000380c0f100361040d4691080104145000388501d500400c0103079281840e00b414081400107442080c1200745d00a5a5502000040344848c0c0107031004000f2651150398603a00340243c8015500103800007855500100281301c0e030b584e04400c4c0d00f0320030002079440010b2a207018030703150f00401c400d5100303d4204500001f0450001d070103134000384d08140302e40c03810400ca41c4c03151780b4008000c1140a00070100c001072030200c3c2c0d030031000d58261450b81403685005844d007600c1d890382c1400c0e0b0308251480800310f40c020405201c270b24030a0150440410040c940010585400d4000981e501101c000c1202819928142e0307203901442500a04003a150812a1051440e92030b121101000e400070301c1d1194500981901140001c000d0041a0144001c6280050395450340541030203034108009084081d5035003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 17387443 1250 17386193 17386199
    0x40504060b03010501090e0c04060804150c120e03122a0a05030406060b09010c08090f0a0806040c0803030705090f010903061a040c0201020702010503011422020903160e040308070504 80
    0x8602400024140300400a078580d4074000000d41141300726002035104c0741c002810001404541c105070340c03c6844030715010a20703441318200340c44410151000c00c80900d040540500c64960055a00f0543d042d808070708100c11981a54855101e005504503040043c403001d02217003080c501c0e800f01268100041d80c030354101c030044003d00c080303a0b0300c0340c0d1940011503800700401007889100c1c45944000d005000307442c2e103014101e40000340f030b03514080001418001e01140c42e41c17031602c401069602d061405403914a8003034a07644620364814049034105d508030144200420f98150100a481c00381c00b094482d00e0902d0040c03000c00030055603144079036040161030640000031441d03900440e1126000e1507014821001c0c824140010380f860b001c80542968010041100142d030300c4411281121354200d0303070382e11203043d4000250007408a6051f0110150760311a1034145c69855074014804458110115442c0102d481c29032102c01c4998843c41c100c40314440300240c0443d000c1e64140e17070310403c5483c0082c50503413 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 17388693 1250 17387443 17387449
    0xc121b031306020c010503040b06130e0109080d060f05030303010303050d0b09010b1c0b130b0d020d030503010608070903080304060209010221090f04110f0714031206010806041b0c080405 82
    0x45080281662112075080011640502070a10710741000c2c6010b07841e625042d16001199200580b2850003000b20a20f0500f020383e61f41c0c444c03410388a00e5402030068440c1401c01d000c0c5a00702c0320500d2182450014000784051100c50014210342c006000395086030b00e1528141c4a503003000140e00801d6848220310f02c2e030b07a5280425540a012291061612041c0251910342132107000c002d140161440d24201f02c2441c1c1c3d81d1940107250107808180402c0400240d0007060000d620342c08029040101e10a0420416400034040d6050361101e41d99032440d9601d407182100d0000d180d21000e001628201b012501261160300103004440341801283c6110b007581c0001002070103140c141c00100ca40c0881e02078030600c0d0002d10203000e080d00f29030900c441942d1400c00140c0d8821440f4036000028006030758002c015200c510a2001c041c0502640d40303030204010442d005030402c90703220303000428900001e05940740601c248003d044800c0b96000701e240070160280c4051420b00f5003a078001030203200014440da = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 17389943 1250 17388693 17388697
    0x4050a0c0b040303020105150901092406030501030b09010c050909040f0c0303020102040f090204051c03140c060708220201110712060e010507090e16050c0303101404020c121b03 78
    0x1403540719055441e481c5041c02401c40e4000750101e4160100d04413250031994404080300d041d240d180000280307480c55020311100810304a44908171800c496800001d080e80c0640c02241202e0042004072175960703440c0c000a08940c2c0080014000c1001400013001904080c69160360141c4120382c16018900d05071510102c44a05038030840043c0c0d0001010700200b0196944503005200b040ca0540c2441d040c500000d00054044225154020007054524240351003000002460280d441030070703903a810b40c420501e8a33980d00301e0743d50b404500004081412401d0a8040200701011944058414851680111090010003500c510984654a008205510380c9101da4000c14130540001a142d400c5124041c207440c8010104402c0c4110500c3c20006041c0d2036004540c4901c0d400b44500c0002c0f21390a084d5000d0188011a510174400070003084075007403030a4a0407042c3c1c3c400200320f828503c885404c01042c0c0c81040e0b0000706903003050200b1000c1044a03006081c00c002883d2540080c0e07003034500032074034607 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 17391193 1250 17389943 17389949
    0x70914061b0606030712030e060c01110f0d06120f06090c08030c0703210f050307050d110901030b0618040513050a050d080702010c08160c0b010602030403140105010e0f04050a0c 78
    0xd80002c01803060501e0100030590040c080801c940c00390b002161400b410300000841c4690180c440010050b014100a41c40040414489410316403a16180d0302c200b00c264101a4684840e07518210000c2002803c40c0c0c0341c42d901c075500c440c1e81d014040c4c0f1a42c0754030140408090490308001181008100c0791010710142c0a000310000042900e10b10358204180c1c6100303007840c107040d081d04103104220b4440c0d10904440c245243d0341810342d84c80c0c4400b0000c5400d88501114a40701929081812421046100041810f50b0003607030140240b4a140e02080490711400180d0454070081034201000c0b170070160042039026544080044100c0c505450351070070002001801c072441c0c1c00c002083c600c81500010002e400019030f1008106585101c4405000c0d0000505030f0350154850011021030140701c1c0c01114242d5074015000c0901e940e40e140044e41c6c0780c00900049400c60306058000811010510032103040301e40d1065452015101d4200d10100620040c000341c43c14024504184046091000c6030001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 17392443 1250 17391193 17391247
    0x1150b13081e0c060903030a05070309050303030c0408100507020c01030e01090b0903090907030b0d02040b03030c07150e0117010909021201090309060f020a020306010605030601090f0b04060207060807091406 91
    0x400072005a29500300f840c0c1100d0203100d00e81c1480000c4040c0c40020a5901c070b810a818096915041400c09031703201c025035400a0342c944000004c02c800b0320100800351080359058022590304810760070050f81a60700440704940103a116904640741903129030001925160048000204c0c40e80c80c0e1107a42c0d030480c040301c0501196200087c0c8e01d1581c1400030310558003003010315040040c05c44000000d18095072020001e072050303440301a2041c2c141d070140100d841010748a03044548096039203040000141d229560000030864103c0321160f43d50050030044e058a56100f54201c0c103030308100d4440020700844901340d800141d01031480050342024420a0309e101e01a481e0170aa0514241c401800c0101e01c0c15008210b420419800005880001e1003e0548585040070307030720b959552004a40d008142e5100c195030030441031001441c000c44c6801081694015070036903449a4803404150303507204003661502c000641d0b0400070031401c03520300c00952500c04010801c6260044002c2c041147c5001c0c0c04400c80 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 17393693 1250 17392443 17392483
    0x7022d010f0b09060a03030804080d110d06030b011202030304031b08100204051c210e0a03060b0f060c0613020120060a0509010506030a03110703020d03120c0201150b1308 75
    0x103450f000e20341c03951010080341c0b2200740301c2c11960300600c000400762000303004a00c0810a030345005825013040c443c40086c20203051706c034101945c80e5009005035103c2924440740da0030010980d218042151810650040c00440c036152460340c51840b6a608041240f41541c1080404180c2580602a03819180c011400c05600c40782030000300a003034a001d02210264280035007800c00003a8007000040d0194400829a103400008140140c400d15402c4880c1036220800101c04010030400342e0103400c02e01c20641d070021261074540c0501803d8840d440303030019142d201100050440395141d074403055852041c1741c0451190980080403903c01007480709141c06800030301c2000142070f81d6108055100006000911013400e207100801c1d110315505002404010342200c000310042001c114030802140d0143c0030380c80003032550400402c541c24400c030210310541040041241a4070500074248078aa494500c4048545040310907802d960001e03c407220201c6040200144080c0f05115200d40c41803040c020324 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 17394943 1250 17393693 17393711
    0x40807031208060a06030b010c0c0906080609030903031b0a020307030c090b03010c0906030c0302041205030714060103021e010309050f0f0c031b0f0a080a050115090507022d010f 78
    0x44070103003a464944003000100c0c410006983c1d641502a02200d06500700000e001c0708480049030489071192000c0c3c00c400c2d800c84002504070240d80040111004c003402d840b03060f00e4204a2580b248545100158144d006002c0c1074140300d510700e0743c524295108822144c4500395503012a0904005610541d41510040002c00282c141801b50348840a001c40080180c00480790000c0c100462601480c020183d662030408681342c001d5040f54090411880d0301d0881f02090701e0201ea40c2d84c00340c58222058401401c00010514000401c1c906032917004120900c1071418100189090742c500c91400d04050300c2c0d414840c04100180481c2d0403044a0310085d040069241c0d039210318000d40c040b92503009134081002c00303544640945000d01c40001c01c54504580c242e04c0f10005414884541100321140180e421400c200441540312454250392841ca804500751386e1049901100c0d8111a0384004da000042c20707095840000041d40000b140300c5240300310450040300b0031801c6685228480301003503034030711101c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 17396193 1250 17394943 17394953
    0xf06040c08060601080a020a090b070501020702030d0903050606010302030a0f05040309030201090503030708221a0405180105010e04090203010f060b031f061b151406040f0e030711030f0304080703 86
    0x300600301c80380062405060040000304a250010b01c81010942c1c00b040129a440c400c5014400034860311070603640b940010b00b002c030f0007903006520407031203807003a0040348401c1030161003c1c801f202c2d04040602101d170350b4540150040e46c0010000350745960f07a42c04110b016020751044901860080c0d07141c075240750a40c4005002c0103299040340384242c1c801e220510010b01c19200320364140b8040c0c011034a0410760320914000a421a41020030078841075180c903082c04a0381d0018008079181101c0d10035520100100e4107a0041c001e00499000509190200c1e007181820b40104014074406400040c588900d201d031202100c002d0f810200708550004207000d1411004039407032450070725003840d500b0141e240c20b40150420b02c6003845503210340c401501880078000704000015801e100c040050061500b200390158071107208940d05403040340380503030707401d00c20246121325158484240011494800551546506144601c40e00c0b43e15103d00404810601030070b2001d03000600d40c000080030200e04510706 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 17397443 1250 17396193 17396213
    0x30601020709021903090c05031c020127081303020a06110105100608010302010f0c080a05031608010303050405010509030f0318130506010e010302030403020313060f0f0801050a0e0709080f0604 85
    0x4103a150b94014041014240403a0b40c07108501d40f524100000c102c003013403504480b64051588030592500032050001d030300740200d0700141080c00323032a4000c2008505111840420103000510084c4421101c0844400103806a000703151000c01c501801450759500d600140e8044c500750001400500748001d0005800402d000d15500054402d4a0359040e5080002c0107145d4a01484082c0c10410752805129900b409101000e081d2900245401d40d11580c0c2e00006e482a8001d890036201c1c3e00d160710070200b600e8816000a41600d915580c1c1e0384c0703420314181c01110250407a11095506000c0d480f40c49401c0e010070001026035040f00d800c1694000c00580800074059141030714151854240003c020b01a030f84804400681d003c00d00b00140c0302d8440d07050480c03650184404040c0030594414000c40c42c103030401010302131403500d50f558014805138140c0403600c0c0103017071040941040380e03040284444030384216142e611480f6441d1182d00d180d51420000d142c20001401c21080d1707004071003840140a50540 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 17398693 1250 17397443 17397449
    0x1603060c210606031505130902060d060f050108010611070e0705040e0a050f06090709050603100806040c0e010906080a0609060b0603040305130b0306010c0f05010b0a06020102180d080d020a030b0a0306020306010207 94
    0x3280c170a01d18604408240a603e418070b50303141103641d034043c400c110b54490040d681982c0e1048401c00199442d004c500514008a000c0e06001c01c084c44000240309110307504403c42c3c10400d00c040c006061515500b49641c0300060410018058203100125a00702803010041c4101245100880c050a116241620605020702101e01610b03c1c14200700d607130b0360809620340c110b800988001e96241d0b0f546045009d041d4242d04541d180d07015100c2071005015880717107240c003518500c28107100140d0340e07021500308603551485030f40308540109136200003044031540108a02c500038100403640042100004a0139070007114100d020030800f0801982d02440d5100c0c10005e4526020a40d285041403000078146050a4400520104d5040b240700100003003904151100040a00204541c81d00d0710000b83c0030b03400150346804000ca15081030b0003140307800d4031001c840c00e40100302e052401e0b1080094101075400b0340c881c442819220331a003151900e070400004001e40c0289401622070410000080c10401c0e554 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 17399943 1250 17398693 17398721
    0x91e030f0303061903020108040f020a0306020a021c02030901021b040603080a021c020114010512010b03030414041401031703040809030a060b04050603010603020f0409140f031b1603060c21060603 86
    0x13507030510040c0d0300100c04540150700b0150060409000f40f0000b601074203181c100801881c00886c428000d180c0000c0d400e00d41010b8120f024549014403101203a683c0a000501030042c0c2c4003030310301c48a5480f5142c0003a1415400b070004130f8080d489403541c4115030302c1821a000180d01a4100100108480020340c0420642e403000340018808110014042c48045c020240701d103079001e04104030079009610100c2448000303002c0d01d07141e940e501c440d5081b41c402c0002a5014030b0829140c80801746070701a005041c3c0b40e1105282e01070404000d080c01a94200500403618201c00300440301d0349030f0b420803070811214030030200428881e084005003c2564000b8144d94060380c1020000e0005a6a48510041520003500e002654494030300380392030b06100001c5004468014011a80324120b800700080c0300c14035031550002d1811000d41519560ba0429280d0050800030b40d150500c0025075a8010b80300094092800c07408018070403415000ca061b0104038408060351321030302004916010300515090349021 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 17401193 1250 17399943 17399989
    0x20a06020c070302031c080a050c0706060902030106090e0c07030f12050c07021216030303020f090418050105130503030402040c11060a050702070503160b09010201090c0b0408010b0411091e030f030306 88
    0x721801501626008e0a103001003902c1d60b0014900d05089016a51445e40184052140a580700c07015070095200b8026000001c55000c1d010070203442e400515402484440302852500003c0d1310100d5003201c51012100800c00e2541c41001d52009a000d09170280a03e40e507141d5444c0c0070ba20421110a030039081c051269000018580d0200310303010700b80c60407240c140c00d0242c1d95008281c1c0d10305282c0700d080511980985480e410342090300e2042d04042859100e07100030401c80d112140d1906c0583c809600040496108200042c0141400d0704012251042070409089103094901c96500700001201c1c0082e1651741c42d010000d0b100d904001d4680106801e0b07014158007400c004903c040034174580640b09031802c0c000754140c02c81e40300b54840390181d500265142e81160300d60308000c0071688144140844c82d0700f04401c9814070310301031180c1c0500034111606030785003c0500083c41507070810000c0404244003a0741c444141c0e42c9080c4000c0000c107030f16001640e52880c0040411214881080b1007415910403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 17402443 1250 17401193 17401243
    0xd0306030203060610030e1902030c0402090901060c080f03040807020109090c0912050708030a121407080402040504020409060f091a01030305071b0812030106030b010c020307090b01020a06020c07030203 89
    0x8070f0125007000040e82c1d01c202c920310040080e0003405550140d81090b1281c3c126803c10403400e41c5690003180d10171410340b1010604601040164014400c0c900d40c8001480700411149002d242204001ca101d401083c3c103003001091480c445400803242a621b40c4000a5044210340e448840b01d80545544041003040c00b0080360f0040ca60a028056072070100c50125000e018040104000001000310000f182da480c1004040200200092264480a00e08045400a8060482c04c000703224040c5580d4218003544c6640070040540000b0340b050707800940d82c2d013150b40441c07980e00a59103e501400e9020032110b800c1d2800d0f40400e0400100da80c1c42c41e032180700500c0002c3e4004e00316003c080d002418910700e01c1c20000045045280e590010805111369000303a40c03d403d044020794100c4240c0d8038100304a0170540011354a00700d0410000b54543c011341d805114450065010003620a410f00c11980c280069503215000c03a4060107440003d40d0240d0b104004528042240c000c680c402c4c0340401c801208 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 17403693 1250 17402443 17402449
    0x30f0a09080d020d02040f0b0c0601060503130305090d0b0a020c07050a0e161103030106020615040207030210020c01110c0615120a03080c0906030a050601080a020c060415060b0d05090d03060302 85
    0x1012085910183c0004440d1a0110703540c040e203000d1b00e8101076200505e5607170f10341110240e0180c041d10b10980581e00000500300d0085058900c11401e614082c641e24000340e400719050b500036a1a1070748500f400b00424041400030200c28403034501c0c01401a618080604d09a1410f4100c0e4800b900c21188803409100000320002002c0e040013803484200303903001c200c0cac4003600c1c0f400c4410480c614031f10020000103801d50340010981d001e07541c0d10006c407030745444020520041c4d01ca11071018001d6804201c41c0d100500031a801044c01d1300311b206c00080d02e4541140d115202c1e501c0f040715120950b00860601501c12020341c441c0c0c070005411940000100c8100140d25241c0310b240c000a41440b2606002803111103601d012117107962001009190350f07142500303450006100075560365001031504030000d24817451078030848144c20308540c010000b9a0300c603521541d03100d8aa40480c084540c41310000105503030114007819141c00d81004c049041c1c0b4103440303400d29003401032052900b010304049081015032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 17404943 1250 17403693 17403697
    0xb10020703021203070b04030e0901050a050609130f06030c090c0302040e0c030601020a060c0c060c020c0303070b0907120b090d030b0609040f090519021309030e01121103010605030f0a0908 83
    0x41e40c140d0310790301602c2a03243d00320f0650055401c0039000d40c00c002d04103c10142c2c80810320400715421596510144d03210402e06c1840301d200c4c0191500f140003040207000d1481c09815049030880006408107051445030031030402c0d510158400c60301c5212919080c030038122180111101c4411516045041c1403510881a0380d0402c040d06e4103a1410000000c1174417640700b40101d1b00c4e440d401070300a00c8611454503000300301c1000d030380d021f64030245000c801c40310861000c41c508840c031200400070344c204411620b41d1903105d48040c11111203031103018030004904080c440f041d100c2c41d0003140d1400d440d1500c0c1c4039550415418002c07c5041502d0403030300300015a50300d0300340c40500400340c3e00010710a420456003002030064003c05400c40c4595054459403003c003003045031351240b003a500c130201c2000b6800c1c1d4405590038403200030007099801001072601d510540d0700c0600e480c402d01c070100d04143c004070307132031010340c000c2c0c00520000d1000402c0200c41c00706004540d400c000c90305801c0195240c540c40d03180c054 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 17406193 1250 17404943 17404949
    0x4030201120207080a0c1407051e03010b12011b03050618040201030f061401110114040308040503070c03060b0f0607050a060203060411120403020105091b09040303060905070e03010b100207 83
    0x1c80451840e07280c152009a0580b4021503000718050360b04c074200710002c0d1840c50a4402180c01c4030020344605103940002c54508111a40036014120650350f0032030329400741e4080028190950359817000d04410340e56250b002045087c240c0300006100c0415050801107500c1c4040c020300b40360401c400d00034252a01043c01c88100c00e0114104d040d81c940e8401240948100c0380d01506030340c24680003060b00c2800b80d40c0d285482c013003600c440300c0328070f00035024a09071070710f4000c0410070004910000c5c02007405071000c240d1062041c0e085d203107001400e0355286c4456400390010f65009690380304d00c90403030810429070201c030b110444016080003070aa841a42e140720344100106555008804145142c0b80d903007000c1120301d0ac5107040c41e241c0301d0104442901020403201600190f0078600410038400001c5030401c0f1030510118071440a0141d4801d010b0f1620340034000318105550343d040040c201049100c2c90f4045c54440da1031092071003c2c2c0d03003094251410005190300c00d4450824003401b0a400103040300807 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 17407443 1250 17406193 17406197
    0x10906020a020918010c09080729031003140f06100e04141009080c0606040203090304090513020a030f05070905070504090f0603020603090a0c08030406080a020d0b1f090803090604030201 82
    0x125130742c003400c5650048040e0901c122960815100c180919007000a0009440c40841110f0140e699503404200000e00c400000d00900d950f880203019a8044400544d8012508886603202503529924040114403082c04100d00d43c001c040c01a21950701030001940001c000301e43d020f6180e062040400d100320018200800340040c070701c5406480c04e4207104a44010181d0742c01004001824145140b0719804004000c00034020f800001d81945420700c00e90b80124403000040d414241844440002000043c0801e401d2a440d0102d900060783e0300c1c1c05207006103101c0c803242c01900002c1d29189152216641008451a007010104140180e00078141c030304440e1200780216281001c0140c44000b8041608040d40100000082044234000056800001c501c0b9000485486507200003864a0380118001e04c0001036021000c5120504d02d034018000003075a182000038420483d20000e91000c600446a844030703403d80c442c1e0840c1c03582000da0080100a490041d500c1c001200000401501c62800002c4c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 17408693 1250 17407443 17407459
    0xc0913020c0f030a090303030b0a080a020d0809060301031208090a1e0807020a030605070906110601050108060f03060f01050102011a0a030201050c03040312020705040c0c05060a050603100219020c010906020a02 92
    0x1034000c002c001c14102d02e942503081d00c2c4e4803801d020004040e000980401d50100381018040011405c080f00d020040790801c201401c02e42031603500300300404202c0c0000f03480e4590248988000f03680d80d440210300031b43c030950103412031042200026000500c0100300350b41c0da421103045000414003800005a051444060300810b201c0c20786440c0f00580145480650441160500803040100c554000e038010b08090301c0310781000d0380c0c40344201c51151461240510301c3d0031000040025502468007640c004400400000003503040318007183c5018000c44a5004440c0d40c0001000103580a114015564000d0582010289280303000710b080e008962200038100040002c1d54080b0000500039100030390390103030f10b5200d0000310242c000c2d650012405024422460181075007800d41c040c0c41c82c10b1055a0010181c1502e17a11408020f0041400034003054243c01442480c5000e07400f20b1000340100702c10003010001406101030000d24000c1c0040b0041c2c144194948148162900028483c41c0340764111342c582 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 17409943 1250 17408693 17408707
    0x2010804020402030c040902030411190305100b040b030d090f120807020d060908070b0402090105010306140915030f03040f05040b060d020c03041212171003030e040605030703030504030b0c091302 86
    0x5d40c0611655200c240e030244040140300c100006144880d006080c120795191820108400c1d0768201040c03444001c02990243c2680c94001031907030006042c0c1000100009400240c6034046403c2603000005103001640030b68060100002c0c501a0f00d015043c0600c4c104800c00c4555a2185240700d2544040c0c419503110300d069007044842e4200744400740d8015001c03911242140303084034203000e09980403840b8403003000003c07903294481c6c8128006c540e1b20700d801d511402d001c4418010740b002c0c0546040710115401104200f1602c04010464101d020b5000039079649150201c810b6600c9003682042e4410703070605103040c01541e02c000945841841d00707030006035264042c100709842e512079980101d1140b055a5903a10030300640360301c85000703c556074540340009484032003040c00c000c000303c1381c401d0001502078043c408a88985142018402c0c041c0c40080c940352118006454007500e503004a0000e07400060500410030302c210f146801440c5070204906240100001403240280748203016062503000c5a54 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 17411193 1250 17409943 17409961
    0xf0a0302031b120121020d020f010e030102031503120705030702060a03020403060603080901020d08010501080106050901110304080307050d020705130504150507050c01060e010b0a0302030702160803070308060603040201080402040203 102
    0x2000c0e0504001281540c0750070319412081c0d00f1a0910500b803403400f5940064940d44192148856410740c010310341d0401c040c103642040003103c0241c01160401035184040b00e03543d20700b403000710300640c01422400c110b50311301010546013004244801c404240240800000580d0000a840c58142e04444258641d4042c00c0201c0084c002c503400030301814100600081400403c500a0005003400ea09441c4d010038006000d0312030240a01ca100d000030b5003440100f05891080028003c84030301427515026080640025a1458126401400c90742c0c10009012040010801c41c00100d41360f14000741070410314180c0010389c0d10007402c0100704280d485000141c2001080c1d129125142805002000b032803e112000a0850b0032414105072107628100e004035121000c541c0e590b0407505c4184c900c0e8500010110201d0203034002400c44000d44c1720390911b00c21700c10888280d80c001b07803d83c07800450301c51856050003050710201800780c81c041d0a0400511025076408290309900a03015240560f41b91100180 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 17412443 1250 17411193 17411221
    0x101712121305031c05070e10030f0f090501390503041505090105040606050a050d0212071203020a02010206010e01080604060c0207090f0f0f06060807030f060b03160908030f0a030203 80
    0x92643c0030006544010030840003c0d41600300c0c4112080005030340d1b0b04400e0f66030a0340c242c007855014001e6020341354001c2c0b00f50003070a9110091140440d0710001c0303210316010b44041c1d00e41240c4994407140d064501540c500d540741c06002408030040302907101d07254040b071309103002c040240c10048000001014010301808031405c040d9a803030204082d241c01d080301402000e082c1d404480c01e07418903000213424542440200c042d98401480008040000c0e400c10a1580e42ea0a24103181d00451400041c03007800a60401d80440c000e40251010580c41e200080c10184140c010041c900c69030030042c4007480d40041c4050340541d00250015284480c1c0030203a2420f00198800312400d030a0010115a0b02b0494104c070602c422803220030b0144110701c1001c2e02c140c60701806014009000c2d4000201a42e1080d04004000c000c107280000741217490303407006155688100c0c0c030100b140d03590350720001e1080e0f03015440b0001030410001841c00e0402000c5400b50b03d200780c0c4d41881c10140c009c40800d8096042da14 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 17413693 1250 17412443 17412481
    0xb0f0d0803070305070c0c15030c0504061b170403080301030b0901020301030c060507030212030a090302010b0d0201020303042d030c031206030809060a0201060801090c030b07090501090e0a0b030610171212 90
    0x2070000c51541c0d230300b01e41c50007080107440d2000185c288945016604d0086041c1e405584040d00ca2020007a1040903c03201440445c4080d9030903102070304400194114178000304043e40c0602040780d904e6046042c0380c40d00b0398025289000c0d07a8410001000800c852102001c191103892900035541e031000d050481c80e0028404094000f00030010501807980034903032113000c0044c880d40083c851145d0410410101c1246194041d025030000c100050009051642000390820754801d401c0001c8081418005503845070300c01100800c009031500c60500d81c000301c019128444122041c400c503811542c404070f941c000d10445900030b14002c222014620f000390006005014050020400c0110741e040481d040c3c0c80b248000e03920a042d100200c1c0c0094460b107001010b582042e158558007510304164082c1e9071100030010f4421a0b616881e80c1180c0ea02440f00b54041c0e1811254003440e1810803082e03821681018070030508a0303202044002c1810040c00c25a03018000c0040505440d5031400501c0d04452800a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 17414943 1250 17413693 17413703
    0x1030b030c090901060f0611100209060f04120c090b030714030309030a050303010e010f0b030105010e040204030203010504150c021b0f041805010c12060308070b0408040b0c010b0f0d0803070305070c 87
    0x3000c200c00c0c540151700030001c582d0801000a07985651790800c0d1845100101c680304030350000480c00381450410f400402003e44080d15042c6462801d519105550304182c12003c0b900c61954400b1040c400600c00e028007030b00300d81c0020802c170f0700300a00099640310700b44144010100e034107050f00d1080e541401610040b10303000d4159020462540b0705942c6913030090142d000700b00c000100200b203110110301c00700156a840c103156440d603400d0030019109404d001c048140c0c03243d002c00c4040b0042c1c071f0a005281c05a40300b6614000407810108861081d51403044a02086522842400104545801480b104644140d42243d26500910042406041103031840c24031078540d020f6207410030a056200b800e03481e281e985c40c0e0301022000c0c0180340c10f1ba03503284409016280c0c184a08004207081d82c880300d801038840d03500d40d45001da64040b01d583c00e0f00f080000040c00d03555804140114100942c195800c258120740c1007080103110785d1414003e01024003580c007019614000620f10f40e000364500c0c0744044d044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 17416193 1250 17414943 17414959
    0x150402090a032603090604030e04110a030209040c05030c040b070c120503030f220212100c0201020a090902030105091306060503011109040b010c0b071407060f05040302190b040201030b030c 83
    0x1d0500c144001d412001e5030100f4084141000441030b0078205403400340030020094181070722951000c8407525411006c0541c80350361604003d84201e5100f004102d4094582c03400340e120b1941408101c201e9021344022030070b02c0010810801e524440d20101c9040d15070b0000d185403100e00e58107160501a401c2e4204a1141341d00c2920380050110010195102c0c101c41300600b1a00c1d075800e04145031b105910b104d1068400742c054a0440146482204160324940d444110b034400544050303001c0545824258410260b5030001e0200b4141d54005222400761580100a5182d94500404121034081c028668001010301a2101080000c0c43c0c008900914008001303004074032048441195030b80c819103506109502d050038034105540100c1d2015525500311103000002c0d03884407029100240039202c80380600200300b080f21700099140c07041140c81c120301000001d840c0380c2850007a240288100c4148080461744510700006240f40026580c440d1b42031801007582040100407920341540034039115404589 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 17417443 1250 17416193 17416199
    0xf0d0605091f0803040302090601030906090501060b0a02070602120313020d170306090f070806060c01090b1e01080f0703061107080304060f1a0607110109030b01030302010f1a0306150402090a 84
    0x501e1101c8206840044025034207550300c403502584c91041d4170009401c90a1b1000080f02980268044603583d8010345011038991400e607165421110079400882003c2004140080540d41c10881040034010600041894030703440b000d44051030000403c01a400e4110240103011512000000101c7c55071210004050b451320f0541c54440342c100f2039003030380201721400004408410040c4030754052a080d4441c0421511074406002d003c3e4003041b5031009a40d25201140c1c00500301d030303500ca4440c0c1c800414000300300102c8009540301340b006900c02c4144e580403a890000305800814000c04980e442040001c00540c000d80344041802100009000140084100014800c07607400078009044858020000714140140c8019021040300402da0001e0b010700800b0700058980031228051030050426041c03980e43c0e80d454201d03100b001d810880050b511440c20b000300c0d0b1110301901a00c41c40140001c5124143d41020941c2e070703407000700b41c0880303000040701d010440e807580d904544030550043c1c400450162 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 17418693 1250 17417443 17417461
    0xc0b010803030921220b040801021201050a0302010215101203020102130905150409050a021017130305122a0a02070b070203070e0403030b040903030c1b05030f0d060509 74
    0x1203407500c84601500c00c00003844142072500c0002884c3d8100750301d0506010402c007280c00b000c0e800301d0300303050707a40710b040821070002a001900003442c0394000981d4488114110341c40055041c0d00540c001c0c09110700910040c1e8000c11420084d01010303d02491940d99002420f4030140194030058074000800f4281d4141030303041d00184024003a0700109280c0c1d640c0c6030160805c4501c101d80e03400e43c1c1c03104800c2c031010914058010100041c0201c0407641c2503102d6400180040000090610100340b0861030790101c060380c42400c0ea801120410840349101a40d103002c1c08a00c40d0980401101c4100400640e003240314950f60180c00d040c600c0c0c407034040703144c80d009030415034401009030000d44103803403001801030403000850701c41942c042c025020681c580001c408200344050000c40a16440e422800581c0e203980c46444080c3e40280d50101e0503c415000c0904588030320601c0349141c1c162080e0500100342c0020445204802d42041c1c1a0f071a50007280c44002040950829a48001c40c00d041c4034002c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 17419943 1250 17418693 17418697
    0x61209021c1a07021b011812050d020a03020a0204020a0c0c03061d01180803040804231206040201020706110c030102071515030b0103030509060412030c0302010b011b0b04030c0b010803 81
    0x1d105904440c1880c200080b58582c0c11011103c3e10300592161000596040407806103541d0f440043c1000c0c225100ca04d4144040b092484d0003080e50b082c1c07200b2103c0203005040080100c506528006002145020f4a0082d01da0038465400390107182c00050b050389052003044901328441c1c110304500c048540741d103446409020000d040f208000700301d9940c80c60784201882465000c014090019134200032566030904190401401500c180f07100f480f00084113400c1010800e8030708181a0024055a90315041004102201205c144a64001001c120050b40c00251200c1942c04600f081c01c8070075200707640645001203036184550136500110703403a410070900312003594130903410b40380c1807120242c1d00d101007400a50900c0b000c0d000303125410040021034000c00c0146100080641018a89034407148542d262150081d403c800156242c2e1680c400d150382032090344100c0c2003d04e085208090f9421002288035110b4030007074172400301c50010508060150300d10301d07609907102c65042155a91100d03002c0d165 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 17421193 1250 17419943 17419999
    0xc03090b0105120a021003060b03010801020403030f0c080318070801020c031213050d030e12041202010e0a0b07080c0a0b1305060903030709060c1a0c040501030e0102040803030106120902 82
    0x16003044800440c8503d40301c445180000364400040414614030b4080020b42c00320350100e10b05255451101240035400500190f020381208000540c0e02d6145250082c80c840000c014003082100c0340322260000f130a50300851b900125113aa035040032410940b25241003c025a000c0421503100041c2e014840c81c0100181c0038500b0b1900f604071142ea01d45001c00c081442d03030b210050864002c0140c401c2e60381d029a110900b600d409400f12284a0303410340604c8000c0d401600900400040902d03680c0841d0780c008400c4a5000341640c0c03590b0041d1800e900d2400c50b000342c40004150580110f42a100c21000f00100500c00f0f130442c511100500f090300f084002e00710280c005031614050000011880c2ca00081281e00842480d40d40d500c8c00c0e4680007088034000114401241d68800740807129a8010341407580c0c500500c01c134070000f540c441c602000901150940c40c1c50300820390043c0b10800207601c0200c2501d04540042c20a06140c41100b44201c3c02001d000360000d501c07840c070800c040305811140800ca401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 17422443 1250 17421193 17421203
    0x201050c07090216021f05030c03090c090403080f060a05060904020f0702090c0405010815060a2001050103060c0e150403030c03120c09090b040504050c060a180e1b040308090616060c0309 82
    0x62100b0085100b940086d00f00702c2e03080072400801c04100070828050055a1190301002610881041d2000003070381380ca415a8285c0000d50b020741030082e010302007486140c20810407146000c915103428040b925601424604500c03d603804920310381148807034000c44070f0440c1c3c0101004050b00d00a01d105100d13410074012280003444103000945210080480c41034003100003001c041c02c08184180c00c9803100c40c000f012015000e000e130502140300d202401002e010390701c103203004240400c81c1400207110441001170980b14081c04e4040c0081e2466100840d000c0c0d0f909460540b02c1e8411500301030b03c144401c501c0d803d130400d00d40b102100c2c0c0c0a81c40b11700c1d81c050b0741f80c03003c041c0010981300301004142d40c803d0341c0140682d0064044a103c1e4602107000301000342107810301100a440e00c0c51055840c855650011400350744d14810040300316410102c01820714041c90a66040a045403101b42d501d0003a900044c3c01140300080301c0041c1c03541010301c240382640c004018094100e44810090240582a0040316 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 17423693 1250 17422443 17422459
    0x31404050a030305060603040b0105040b0607060f0e010b010905010903080a030905150a0501060c0206030a050403020f01020703080907050406030314070203030f0403060f0615020a030302070f0506012603160201050c0709021602 99
    0x101701d184c0701007228002c6802000c84d16460f4201030400008003c4035000c40e500000820611002885078000c8074111168424001008108609000e007500c8028040d03070b041200a88040c00942e80080d03890381600e40007120203888054160058000b4580034002a1884c8038100d00d052000b044070007020700c5111070a6092250b03036a40c0c1c8040c0c50700702681d10300a601c04801d0001a41c00440b80d400540d01c103000c0d204076200c10b001d803c043d508a07440103a06a0009503600108600c00d001002804028001540c04011540ca0341d00c004040030b15a41c540310141100003199030666030204180c031203c1c2038045020303a80f180e4901d0200014005082044400c0741088800582c0e05845c0004642141080e00504002202c81d50701b20025031102404403061231460721001c011910401c030781f80c060300c04500f11420a200c1c0302000311029014804d0076081d035104020251404100c0c124034011180d0a08102c1c0c3c03102d40c1c1c410058203100458000c948142c0c0b0200d100606151599004075a40e07000b80c030224 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 17424943 1250 17423693 17423701
    0x51204052b02010f060303050901080619171506010c0b0c0d0501060807021b03060c0a11060408040611030306030d05161407060e03071202010c1a0705180d0507060f031404050a030305 80
    0x44c151011480040c0100d58140880074441d4000d120041e0b02440041107440c0c0046202c0c0c4080310b0075100d400155140291082801c484007041004d13903036001d003441c00410140303000000203050100c1060002d15540000d008540342c0c0c0104425241000ca81800a2010750707140e02000300104000c4604500511850207604290f0031070808201d91a40c010300a41003a60304c150502c18251700403038002c8100820031000d90080e2a0500240f0700441c071800d0382035595490088010000308800001004907042081070020f603580000c0c0c1c00032500558281103803030f520460b030203140d002c1803000050300303031805050f00e11070a880c00308561003030f500c0544800e4450080e41045c10b5545189014580601c0c0780403d00d6000356010b5691503601a01c0750b1152000d050400c1d0303c4e0100c400c0c040e190b4001141001c6500c000d19039444074a40d261410541380500a0f040c4e42c4c81c2d03a59174510500c01c4c04280850025400c0103184030fa0071110800036481d40300310386814146000c50343d801c02c141066002926060200d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 17426193 1250 17424943 17424971
    0x5011407020a12050f0613020f06070213051305030f040e0f0f0f060d060c0c0b1305190501110a020a17070305030402100302130806160306080307030e1f11150601051204052b0201 78
    0x20354140f503000380c0500e200d01100de61000050601070012840035029068000014104000900303652500752600341e191454888076000c06c9a01601082c070007c0f1500400120003e00308007254070420b0740740c01e42c0880d110740000c543d040c2004803001c0c02003410180c1c64498641c02c800020f414178420a207a8106590350140026508580b5000400a4102050030b1859030012040016860300034000010294041c401204031503102c0780007100942c00850030113003400440c46012a1000504d50082c1c900784032542c000f0031074440200700a10038034864070810700702c03403195042c0c5400e01000403100c0000f0341ca03505010fa85002c2203801202000e81c0c440c0d42d040709482402420308035a2948015800d01209e5038058030700e905421480b60b08200e4804a00f003a81300450194812408651221054400401c80560401610820300724203600c1d801c05004069034442d08646240c0c60400e0700400d07a454030300e0041d00741005174007200503801c1000700a64640070580102051034001d0b8000300100d007512059 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 17427443 1250 17426193 17426197
    0x417100506130504020f09070906020721060c0903020303030703020c0c03010b031c0203130e090d020105090601120f0204060308091315091a03010905010605011407020a12050f0613020f06 82
    0x595500440780b007007800030580340c40d0032180d04a88000c0600d0396011780a4040b4111002c1103c1000c0000c1040340100031b003603014000100544900d14811307541a1204454880c40d4000c0c40009180c20765942c41222003030b1261100001542c0d005003a03aa50b4100700c0740040203508001d4415589029200b401d0743e09141c14030136440c003210040d001e04240412a600701603100750503158641540030070012040030118060b00c0c0c0001e40a950000b8101c0c0c01c080c1a03983c90050108a0001560300d00310501c400008000381c80e9044a036444e2080c140440940f80940c0f01140480e4000e42050a00101008020761600504a03501058507100881200700d02da405c01d44415a1041001d00e0708220188203110168000741c00081c0e0800c01303d0590b010520100703086038a90034095401ea5580d86080c0020740c2d001c220454011301d552234150600005800060101d41030744600d01c020301880071140300304139090024102c40340300c0c207060700e80d00d140a9004a0b0408070b4964100d2040c03000c1034808585181c0201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 17428693 1250 17427443 17427451
    0x102130806060328030f0507060c08180105070206011404060b0c03030a0e0313030f14060f0103060c14030109020a020c180402030d030915090606080304080304180204030f1b0302040204171005 84
    0x4043c04c1030400360388040e9064141c0320301c1c1c0b4081100400890021540e00c0c0150b0000e010706030340e0b1f019039180c9002030030b6081070010405c0ba101d034180340c2404100ca900281043c151520755540007020103000d40040c00611080d4040c80c0010030200d21006c28450201c060f6218090140e4103012240c0911040c6480348698111000d80d80000b00c410b00201315001c4030212114860786440c288182503107082d602e00030003164031603490300e0001d0041c000c10056001d200851445810903070000c0e500c83c2010034650005010746510b290b40131410441d0644200b060360340d00400a4120710781c0d04040628103644a90840b82a402403090118a00c440c0d4400c0c482c0599550f006900350102020110305100900200f441c255144c80c0c59800c08a0601020300041c001404d81030000e540d6280303414100c0008030109481e11030301600c140010404140c0000340102d810340c2c898a50101c402d0181000344803a1010b41000c0e40040c800f0402282c1c8440c2c101220343c10000f81c4040b83c068403034840e07114060740e070225 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 17429943 1250 17428693 17428753
    0x10c05060103031d060f0a1206060c0311030d0227030a0b010501030e0f0f010902030105061905011116060f02160b0904021c0e0d080709080a030e010201021308060603 73
    0x40e004202203486607024a04a200b0074203c180c01c03406200c0051156000180002c096090000d2428402c503004403412440b000c10400c10701c41940f400e00068000d0b581001c000d030510807502100c1c44140410300841e419100403042c21522400c3c80b425001700b80703002800004072800c208018541c145070001301c0001155011024204d140e01700b10044020348100c50104003184998076901500343c85c24040f084c6420080c07000055000201e004040c00c1d25005030002d401000b95404424609500c1c0c0b15031000e9440a0030640c1c00c40e40c500b00414504032184415031003248030110017251550340110840307000003940e401c4030341c01141641700080c00304a0784110f0316540b804108922207030038150040c00d480030b00c0d0014104003a841030708a0040d510364011083c540c1e000992205581600006415001230280c42c01504171401c0c11030b40c0d955201140806030038003050701d0103800e89a01c00d4040f00e600c50b490241d40d00e603460b681c403030040e51100203444480c40780c0640006149006120412003000702221 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 17431193 1250 17429943 17429953
    0x602030c061303120509060a1a03070501030b010909090309050a09021903110c030706020408150108031606090503070b0406060b13090209030312040b060307050105030717060303040f030311060105010c05 89
    0x106040300b01246885030071024841e5880e070b081400603c520a6a1103505c1c024007a003080d25103865000200c0b541d0307101c6450981ca85507407100c1580c80004601003074130b82c00c1c01c00190800d8010010b840d4113902e5406103030002e040c2400b10b4200b650066851044a00694159154030740701e0545000768020548404000511003440c0d01605219402200803001c050354007500e4800c1503007040f8219072045405544180c1c0006042014001c2000001d40d00200e00002011039410b1404460b140d11664000e03e9800340e0003000f070400e0003002d07800400d8a590045c21030f9590041494100d900400484068544d03a2400314005800c0341c280c800c58626552039140301030114104101d10000f90022070503d80c0600c0144420b61421920240941c019401960088080c1c03505a04040c42d1010741d0704094104a014800d20017101d0308034a4815501d101e19465034030bd60b4810011074990302441c2c0c40803010706a00c0d080001455003102c0041d8a030074458054502c2030703072280015900e00c5a0394000800d541d201d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 17432443 1250 17431193 17431201
    0x9070801060e0d020406080708011a060301050102070905040503041d07030e0d0522051005070605130b01090f090b0c0c0705030601030b01180b06040b0d0513120302090102030909011508010602030c06 87
    0x10098545000c80d04c02800020096228a0494605401900300440580d910b80080150040342d585140d231440c01101d4032851581042c00003900e5812520035040c44a4a0780c001c1003c0120600c161006020345041032030b40920042104000d005080d030704400420710b0070039282c0800c507001c1030000030341599465003450a0a04400340b40c0840e02600c44601600400c40b010909940ba24502c013002d03000c55031003589405060030300400315000134010300c0c03010b0100030380c4400107100d048a0904440e244d010000b03042c2c885a1460020304207419004002d5850b1004101d40b218400024000b40c1c8529012140d10684840506035616000c0c0000b825840141c40100403a40401c1c0c50810307485481440800c4c55a058801701d000c1e50403030703003015813044408144840210f00e544130303180d406090102c01488441403070b15181d044407103d98001c0109a00000c3d05403c51f40204111102d00c60060400720f00d5682d03035400f0700454413a10340c1c8000015100000050114400802c0d1034425001e10046c18030b58903 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 17433693 1250 17432443 17432449
    0x403140a030e12030c07080705090c040503060402040908070506010303050301180204051806010c0c0617071d090907030b010305060115050c030405220504051501080714041815090209070801060e 85
    0x1070341100c0d01d09100410445d891aa014482c58000f804c1c003c0003000502e080004010001c5401080403d500c0000d00c404c20543e50001080c030b4010381c040d103000400f000581440c0e401c074401c0c85001b030260311596000104140c1d000c0003e6040307030b8072041e01c40300b290031704061031050344600d201c2c16510140d0301005071500040400520307008481410b020700c920900780d0ba040c0060000381d024a0105400c4001c51100000e000708143d0b0140c150320301a4540384003056488007000701c0b440014044c001c40300000e814580d08200c0080503541021310245d066940f45405030b9203e409004091030310705601d081c41183c41c0241c0503500c4034511000a075061130301301410300400381020500000e604003900c040010080c03c03446102e001d01e0040b405050704540b801d106807000032042c2d010400540c0262000c110030f40d01608015020031084130301040d803d107601518541c000707084801070300703ca00c8601c1d401c00d8000c8a900c404041482600e40481e0f66903101d1054900702c00c2446000c0114003900c0d0203000ea0f01d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 17434943 1250 17433693 17433709
    0x20a080a0b04140109090201030b01080601021c270f060309020112110417010b012d03020d090210050a020105010506040f0608060103110307020703020a090207031b0609020303030c0403140a030e 85
    0x8076028000180c04441d40c402d108400c030085e0b100600f416a42c2c1c00c0c000a550f4540524400d00da028245a000b0703041c030b940001d40d101000d1200d02c0c2150a0554103070590340c440c03400b00c000810180032161000711143c10546420300a032050441d0b0904a1400140b04d1703000e8041c03101c0140d016103407418040c00500401002c2c01c680384c20205c15810420010606400081c4881ca0009203080000360052a000000d062814580040c244c034803c220034482400035200a02131161030f00340b80243c0c0b6211a026060046e00c801d1030001d5005903000281090f80f42c3c041e029114400151f8000d020302d9076a0020301c400c0b4480c0340a03000c204151090140103c40c0140c56942e000703030045c500010340c0007080b040c500c1c26400a50344a00141c2045404200b540360445a4402820b0980411485d10425540181c95001c490001c0c040c40c10b00c0d03402c2c0c1814001e85606c08203176590040e054135900e01c0e0140c070103165640207010032a0807410000c0390800641e000101c803862a940341d11400c000c00d0744441080030308 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 17436193 1250 17434943 17434961
    0x309030609020d0c06020f0f0c03060412030f0207060e0f010b0916020a050d020a1a06010203090402030601121e060605180d03140403030806090a02090f0405060d050a08030105030c033409020c0d12020a080a 90
    0x41030b03c0308400c201d3f940356032001b072504500038000003501c1c1c8200342c00c550400c440c0d10f00c40400c07a0f0404015112075600c0000c02a00800381a0050641500240059080071f44c190780180150051030000d0346c101d5004124001001e2003807020b003844002200c800c41d10f001c810341d113842c0160300600049405090681c0250b422541c1410122161041c1030100015202d07021580c504045007100c400d100142d0502850000e0100e50a006080002e0303074a8207a061141c20386154403860030211284185401800200652541300d81440c3d0350384d0301c03800c014011410540c2c150380242452400100d95080d24403d40342102c10040c280401000001c0401001d400098403061344009410450400108100a41c9001c1d510030705141e41c41c2c0d0300d060101400e0141203003103a03000780c02c440d5030400c2e0424601da650424030302d03000c0603015a2562b11a031090384450b51300701411440c40000c05200d0342c4000078111560590702da4548000ca151034845100f44d000d0500e01e540810300400204804400c660041301c0c01c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 17437443 1250 17436193 17436197
    0x405072d050f16050c04200307030204080d02010501060207050f0907080a0b04091b0f0b030103030507050a0c0305010506090606040f05011d09040b1b070309030609020d0c06020f0f0c03060412 84
    0x1482c0b032404440c65654032801c58002c24642209124040040612650f094040112020411164109800d05800120070821090607a000000604280c003a606840c05010f00004071010200b90000c042d000f080d080c01b8a1001d03111704000013032030345000000d14620001c09083c0d01c0761030f21410419203031000c000c0c0c000e140141d12422101804e403518801c1e1749007c1d0280030400789041c2c070000002c0444107150001104048100814402e260752002164111390381442d00f0b942d81c100b01c0c10600d040c400c039600c0040c0707001000c9100000f48801500424061a0111a00c007601d45801c0d0422a041c4501e2050050350410714404200c69030080c0b2200880e07490081c1200d26013800700c00054048401203904031041141e182c14412600c0c0301040c0d1410254401e406e0b14682403168030050901d0186200041685485a00310380440d200d50740d11808182e444003111a6603070b122a0040d40320341100000315128860025003040318613000610018801015020b440103440d10740f504201d569544c0c1c1c2c0442 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 17438693 1250 17437443 17437447
    0x120503040c080321010b0a0507150b04020f040303030c1106011202010207090c02010c0206090703021804110904140f030301030209060d14030a050702040b030616032c010b0405072d05 80
    0x15042c20240024001d101c101c10714a000f00702080b0500540590607048242100360601100003034513004021280d0f01c90f004500711861b000b001e00c3d800050241509a5034100e030000c58040784e845d6200c0f003d482940c1c0700351402d0200020b4244200d4942607101f40000041c0e20910040000300d202200001d00c1e10300610590382825100c501c5c500c15030f20900610001130307548400c902c43c2c00f42c0c103209898200303813a03038040c0c16020710710740028483c1126906000c80104000300400c0070054030045402c252903000d841c1d00d4042c5014100301440c1000811121114003440692100c031607400300c01c0700e060741e6004002c1d0031a500e42e002803211034420b01c1000c4030022145440e0080c110f50030005030001014690390a5030320011441408152022600307441d01036030155060240410740f802104244585034030380051296003040340780507014118801c43c3c0001e0368020750604000c2064100c06d90000381900c042c0700e503466204044400d0a00400e100c4ca21040d82060303000740103900c0280b00082c01e400c1c83c0ca0b074 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 17439943 1250 17438693 17438699
    0x206130b030408030f0c0712080a090f030c030e040902060412020105090a0807080c010915030b0301020904060308030a140403050a0810090e0604020a090b0105041404020d02040b18060304120503040c 87
    0x30103103034001c0d01d080d80c00010110801090076030300094158041c000c400242e00306412641c40280000d1034501c80414044040c0004015818541c03100072020380051a00d4601c0c5058280076004d60710050080e400169449102d0b1120304040c00f03540a203541c045c042c140b40078a4260b1250320401510012410800c007000320154558450b83e000e006040620040c182c036034940464949800f08030b401840c18802101410000c09100c4503121480300880d007004201c1000c5100081c0c0240300c0c1c54052544075103010b0010051000031400b440c442c2e108410100000c82a1034103000450908031001030001d02e007085444841885075002da0b402200d03d56089412a032900441002e8868010780340d00c0c1540901c0801c400e501d04484040001d0803411405c10158400c240000d00501c11400f40910018860a07001c0d100d485903030494213448004d0b00110340352612104608a29403125110000c1e090540003a00101c4c907050045034059079000074411208400d10a0654580d00020805c0d00c0c3c90142d10400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 17441193 1250 17439943 17439959
    0x6011a0f07080c060106020105010504110a030504020109090c0e030f07030c05010c0c0506040e040b0610020c1c0506090d110303150409020303070f0501150e040b06090c1b0a02010f0e0d020613 84
    0x1909950f402040070300465814240003c0c01c480d4140d004a200b1410700d50902c3d00442000f0480350072009500e000300e12940c850005a6500e24170380d211150241c0f0b062582c2e200241d00007850508124200c0a488101e003807540c505a680100d400003034441c1c000d001c410806036000d80041c41245103d0074862104541d141e0000e000b5030803d600100400c0440f104000c02c1040b02c0e0003460307102d44c1c2180d12585039040c00303400035034881441c0160b5018603000090360201002c140170460788554084201d4100d40b401101b640c0d00ca102404040010921500307010440040c04010749100e5110001100c0c080d54190f070800001c0c14841c101a03030540410402400410b42c00d0100405050192300089216181d40140c41454402030b803014602001860601000032920716a29400001c22111440da41d183c2008002c0c50340b090003420032090752401c451060f0384401217644152a4000d032a1600400580c00c4145e400402d81903656a03c144c8641c4004014075000006c1c0075107000f1081000c041640351402d0b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 17442443 1250 17441193 17441197
    0x902040801060609061e08070c020d1101020c010207030803070305070509040504050607090b0a1202070507081e06010f05061c0b1504050a05030705060703080702120d0c0306050306011a0f0708 84
    0xc5180e5101c02c001d200c0503422100c0703d40248240d282103004a18055012034210600780c080b10100040306021a4002d8400c000000c241500181112203002e85441c0081c0400b64801c001805800b912250110547c0042002d40880350010221842e554800300100d00408005008000380f02d424804210035403518401c55104a1294009090340d0600709005014038031154001401d06a080040301c542c90f034001d0303604080d95403542c400b50311036440340b80c60340c142229500540883e2080c6451104000d1094007601400c502c05020342d8080e0b6219000201c080300503000c2c680d0001d00400030b111055440186181d41058101c0000030f095100d040000d5034100d0031883c05007000c401050920091030119900d400420003100100038491502012541c02d0107003c07c09818400d83c2400904180e001340403021140c03122918265940c107020030003400800200b0307a8100042d29102000c40c00341400603030241030340d40102048200c002c407003403001141d5218012200400100b888444006020380b80 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 17443693 1250 17442443 17442449
    0x30d2301080d02010b040e100504020409060234020d03050d0608011104030c090b180c04030501020d1a09100909170301140108070c0209010e060f030f0606040c08010e0f0709090204 79
    0x1d44004442c007440203080d5413042c8005c611892524207078a031040400104513102000482020882d95224000600109096078000d0b01c800d00002c0d4030550071490321400034003008030f800b401c807080c02c007070003481c01d00221650001d420100c000d48a001080c0644007034000035a5503000402d1841d202c640d043c0c00e540710008003094400010406104105105001e075000c1c2c1901c040c104100302100c2c001400394896050800500910507000c24944025001210043e541000081d59039901025060b0000e00c0170544040404606501e16250b074a0595030050144071814003071409107003409a1400146105102242c00441c043d401185040034a0050742c028201c050303001101c608d44400140000500401b07020400a080b4594401a940c01000314113440c0750154400d140e6a403900840d803102111111b0076407510a03910303904455800042c402d440f514080d5400d0003c0440c0d52000d948110307003800343c00c032041c11400002c1c41d80a100e040c0154042027511707100361a6542e4554660483c0d0042e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 17444943 1250 17443693 17443709
    0x2040e07050f04050f1611030403051014070c080f090301060e010303080f0108030d27140f03090d021002011107080304060b0f060d050601020106090e0a0606050d0302030d2301 77
    0x4004010350b14000d12012084241610248628908299070710031130721004000ca042e604110360120000ca20a038000700fa640701c05002c036540e40f600d07410900d81e1510051700800031141086108020302861007200d40c001d21041d12540891a03884d039501115800c9000503046500c000c2c8543d200c00d941c24040c01c4000c00c20100a41200d50650400400c80c4800800e21064114400e0040020307c40c004112034290040e000d00140d8442501c8a03040340c042c224501082070051007a83d0001d120194502200c81e8132400c0803145080308010109442c1d004e036441160380444001d11a1000d42041b0b8900703400e40001d8400001c02428810001c012a040b011003903801d42030100c2000304001e814440c0352070204c000c0316411100086800060341a101d2040800d0310561207101040e101c0c1d000350400c20250254040500c500015050301c00d81e9014120001e0b07884500348200012581005500c1d40d04950301036003c1d45c54100542c151718054800e40b56620301e000705a4003008100b0390005116030103820b0742 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 17446049 1106 17444943 17444953
    0x70210050a0c0f0312020307030b03100e0709050c0c01050103050d1b02060d0e010b06040b071707031e020f03030f01060807090509180102040801020c0601080601060801080d0305090a02040e 83
    0xe00e40200030107001205015145415811072b0603100c0301070302295040c0f441e4070407060642d4801c00c0e02d685143c00c46281408148034503041107a02c2a003510003186466400c165250131135800340e00607241a0000f411aa641d43e4ec08606101003c10100c15a2142e031130700c0e0002100741c814603000d80754583c1d580c2d01c522107241c020340000d107400900400e015120755554501501c5603001c60760480b901d0781c0708440c19030024010019208220341543e200071046030740c00003104800c0340c1100848158402d0341c4c1d11083c2c40008000441c42044da109200f0b401d5454860081d26003580600000c0a203c214a02480540c03581805958044a1095103084200406c410140284196040480c0b2940000342804010200003080360490320010100c507103a0b031380d480c400c580c415028001d1482e42d400c13030282084031510903002260002d19410980d118540c5c00c0c1d0004040315020003a4074195049 = true := by decide +kernel

theorem cover : BRFrame.Cov 17266193 17446049 := by
  have h0 := BRFrame.cov_init 17266193
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17266193 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 17266193 ≤ n) (h2 : n < 17446049) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
