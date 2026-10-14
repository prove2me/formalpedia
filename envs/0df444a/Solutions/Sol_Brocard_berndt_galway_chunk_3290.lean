-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3290
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:13:34.707777+00:00
-- url     : https://prove2.me/submissions/02fbc538-815e-4b58-8870-efd626abe3bf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 591546762 ≤ n < 591726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 591548012 1250 591546762 591546797
    0x306060303031b0a052503030b010219061e0618060e01030c0e070e1c0b011211060d1b030c08060f100c02040e071401080f0912070503090915040e01020c0d0f 69
    0xc00240880c3c031b0100440c90b20041c164035019030031b5490800e0004100c0d41000b240c1361410280b90303883c003808051796210b0100f640b698139200c03d0310b8000c2a103810702005850300b81441d20701004000040a1303c1c500000010120a88680d0364100d9800000404105160240080034600d009100e0f204000340c0c40c5426a0580e04e040c10008003441300306d80ea10280e8124a440e04818a045e0001000c000d41e03203070b00c000000c4040804500003441a0b4200751a1102106c032000501350b04205d03a80c20214041e9000c0000da85980f0a040749042179035403590f15141c3da020b01c03003460700d0000307410f4201e000c43c40c089488601800360064094405040000c414000c41d80c5c80341015410740000b0300e00e0b0b0005005113a00c4da171000e8110f0300201c5081062501d82002d6144564400c050b88100310301040c0455040d0900409005070707415030002400c0043c1c1803034102090390184500c41005032081e454407044c0c00107514140b0944050044090081c00324042000f41507071b400b050400071404020310b03e541c107028440d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 591549262 1250 591548012 591548047
    0x3070f05030316080c07030c0c031415010605130905061c0b0a050c04060207030f060f1a030d0e0d02040f0e070e0a1a10180515090306060303031b0a05 66
    0x40c011406140c9904010060f0100e41c09024894810802c00c5010f0144000010044500341580f42c102040c6100d40c6140182d14000c4503800580203005c203000c03000034150082400d80701c2500580039045542c2e01c881d41500e46002d070403064982114100e80c1805078003a02e43c080d40e000389000300094410624901c5c201e02c0d11086080131114846d2107002d0280c151000d0007420b8010160611403810b042c10140029680c00282c44041c14045002d2801e1003032250351ba118859170051000c09001040c0e21160484246642400550013403140f03941c40740101d07114020711450300200038420a2920a11340802003d00302001030b0f0340c07045a540d60760040c81c1c24200f0004c07009040e64002090380f490704510300d03c1202c2d41001004422880b0703504014003a0b0b00c2c210079500500b0741341070401b80740415034285000040d07641c000940002d800d501d200c0641004401030004c1c40c00403070444005945a005064a0340020340e00000d81900e8040000c20040d0104003401c00c054440c540241424007025183e03c402 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 591550512 1250 591549262 591549293
    0x90b070804081930050106030216080706110a0c0b24010507080d090c0303090e0c0307080709080d0c05011b02030403022707031a030109050c01180f0915061d0f030307 73
    0x640d40030304c90f0700d0100442c0281d41c0100344504085080800320195030500c0703440078000500d02100000c8c10020071a16074000405541d41880054403a450703100c01400b25402c0d00300c02c0c0c42a207000da0008a6070540c96202545280000000204041e9600b00544058001c01c2d811907140600740b12a0040c9002c0f40b1034568081e00070380c0d207001d080f865800c0181c00404903410803a103042441d020041d54001020440e50000c03001d15042c03000b5070b5003401c201c40c001c3c0d05030464031440c040d05440d010b150740d100e0300e40c22401d0f01034002003101c0c02e4542c1c1c0010310800620741d0750b00583c0081c00108003520327045c0303619408425107000706c07030400280138041c18521008851282c0400d80d94440448100c902203400c0002c04820360080180f0240c2ea2150341d55440481c1c1034904000e420781444100c091807000080062081d00100000f0646685902001d030440c000800303d404000304000401a205090284103001081e020000c000014824440445079400406030188070406c4800b0001d516401c00c4d4451 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 591551762 1250 591550512 591550577
    0x60c150908190903020f0f061605010f0c0921050f1207030f03050423010e030f0705060601090317070602040816170c13050a090213090b0708040819 65
    0x21080002029200e22400c1d9802030208040f00101307100585a4070b0085000e604116020107002100c500001d040c1d2140360510011031591070b0040341000380541103150060310030b80051000060400381190604058411036a12546240c000fa40030f003075202400c0b034420f0096007a1126000400c031040d10303041d820f100c07080c0b00d00c81c002079039028158071514140c40c011040ca0180541c0c10603460b00d000c0e0445200c074090010318507400007024403009510005214dd5240140c1c1e407103000913582030005401c2241c0541309401820300040c49588120382440a0340e034050806500807030025006503140d0400802190415820072020407071781800c0154140040c9a400400d4600d0300b048481100d4004155601220382e103c460a4005580d404180003550781001500007195518140d07841e015100d5024040d4100203011030700d85220449070002e02246028140c80c001544030000100c541210454010380b203900184801d80311180f05184013084844907141446d8070784000e8004407a4481c0140c0500d45 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 591553012 1250 591551762 591551767
    0xa05060d120216060306061d0102281a04030207030f0203010b0d29090d031503080a0816021524151201090c051e1215010e0f010504060c150908 63
    0x2a590a480e0f000e014080703600c4c0c140007052510402410500b02e006540c9151545440c11075803d034030800c40c2190310f982c0000018403645220724511024894610103540c0e600c1080b101180d00d109520384180a141e241d4001e180c03003459074481c06202c184030401240c4c0755489140040709559280d604504041c003541481c0150302070074014a0922280c01c0e0002d820741404c008102c1003010104580213499800c0c10081080340d1001703946402c58296403c0203204107408038802c070416601589092085c1980c1c03441003c03612022109a990701e4542015803890201031002945e080510591481c001c00100080000c045a142c0056440b03075070f0040e01008680041000410740082c40000c50050404500c1005a0781000c00014010321850031501c6030b5120443c21004080800421034000500403c61000e407400c03c010380c40d11800d08202c051340003848048401c900c41c505080b5034410814142c41c1c0d01d107498036251040d21f02e000b031840140c46000900346400c0810540f4000d10200740e00c1107c9c1c003503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 591554262 1250 591553012 591553033
    0x1140a1a300603010e1905030403060606092d03020609030c130b03250b030711071404050c0a0c20030a26120a111c050603010b0103020c060a05060d1202 67
    0x20600380c00420b800e1107a81040ca00015142c0d012038903682c0791122224030002c80d90f542c20001d26610a42d40010701c518a40100014103d030311444d01c50940720810700d203402d192804840340c1030041c2030303610303010821107000340400043c0707040b900030039240e203005d403d5500420940c0001118208005c020b00c07500d54403400482450301d02406200400a0780c45400c501c05502480c8180065078240207448100c0f00000106400700d02078a511200403044a0881e03030076540300c280070040c11007454900d502850070b10001c074510000038001d9401c0e10b862550f80d041c01c0502500c450b041c90100090b2000545403249980d41c1e191000d1003a0701c81c1900482842501030f013400d40325400210a0402c600c81024240b04440b640003034150070070740100140c20007207401a0000204503a40c400c112008806221803402180e214500b5081a4410310b0200c008102140c0c4c1d610040d001d0b80300fa440d44612680010300000c03010791441e48195005540905031030701200e00c664a01c0c0815030782c0040c030809039100a2819 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 591555512 1250 591554262 591554347
    0x60309070f0b070c05040c020106150c120912061d030d0510090209060f0c0c060417010b030c0f01030e010207020d0507030c081504020d050a020603100501030501140a1a 74
    0x420041c00341c00e0701c2d0362404001d03441d50541036100c4c0c01010322968441003401e07511031003500244003070720b80220315201918100c1d20203059400c10724800c803042015494201c2c4428000e64044c801c40300c0030300c6480e603001c00b1f070350310704d801451900186080c0e2104590b02200d51003082010302108070440e00d0000e0207080c840000c1704401103d90001d00c07054010050100e180c0c651105075a001d0303610700300140d10b500400d0b4550f814036000c8681c882e001440450001562220140d1500600c4150030080241032201e030f0a040d19130b0b0180b01c0f0641c0100091000d0391742540702c1d034420107181d0f09007800142000250342c00659801001a001e46155001078028020701c21340801600040c0b2503040105146014483c280014040050003e40b0511141400409200051281242c0182c0c0140322950300c1c680807101c10f514199600a060009240c00d0002c40c440e66485410003050070000c0007042d0721450905120f02d40c4445482e0300040d00401d00007800703c01a00c000c1c11201c0302900ca203420103800404444e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 591556762 1250 591555512 591555539
    0x203040302040f0e03040509040c0b071a1f05100203040b0a0905011701030f060504110904051b0a080303012d06020d120203040c14040e030301140909030c1903030b06030907 76
    0x31643c06403610906400300c1070004111401c4540607141800207558900f8035030701c1c6086035480300c042080006000320800c1442a08400b50600f1001001e16a032500700030301c0440284594110610340c0d000c03500723200700c1c40c000c0034203080c10255104983c070301602c4007580005600032080c031801042407000280090340e0420400d20901982e80d810210039031443d215414401c5160700040c0041c0c3d541c50206041c000c1c80840e1501c8101f010303102605c681031519050759200000c082c110010140400d40d200f82d454540ba142c0c0840724114021030840c0d00340320488000c0520300702100f204c14005500c04074481c4405000d20014031031038000d400c900c511084041d1000340070140c002142e601c10000c02000510f081100c034140c42d24003550f02010301c500d2020800625120010050380c1c4000300000801c001d4a51140ca05120280c44009998440140c8140e607401240071828841d0007041d1284610b401d8045400501402403902044018440c000300d1074a90017640c0d021300d542c00c0190305206a0110140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 591558012 1250 591556762 591556781
    0xa1b03200a061106160e030d0804060e01091a0a0603120801030303051501020d08040606050a03060203011a0702030a11010507020603010b090424090209042307121a010e1f020304030204 81
    0x100040d00c00c40807840c0f20f0b10340500402000201d0301402c800c40384c031482091400d040c1c0d01c020f030440b140c801c1c1102c400780c1048002c035801c0f100785042030150840c608060040505003075001d1002403200803824181000c1c1000104550400c030b548110001c0420000900038919110070b4542814950440c18018151a0001c01c40003c0c6414900c03491516640010903da40d903840d403501c21900d07100d518220000e0582c039400725511155456010050084960045048070003151070000030392818018030029010740c500180d0701d500510512008280c070140d0031b00700d1002c1450b045241c800c030782d030005503d500281c0124032a802c0115000e080d905061055141003134988210402c41c0080e4440300740b202185001726100700340c01140d098841e450341d40000003140302003205204407240354001400740c10002c03240c0754005180346810b00306240140c42110104c0b014800e180030325680020040d2143ca411003491600014003288046581c0d0424862060071240c0c0e5003e540c0c0c52f0f00e980100415074000d903c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 591559262 1250 591558012 591558017
    0x4021201050c0a091d160908120406020c030d05250204022107020f030a0e1504031208010906082109090a05090f120d05130602030f040c12050a1b03200a06 68
    0x17040ca041c4580f030b202c038540d0f00581e100e80d584a01c0603a584200c1c0d00f034040e0b074885951072045542e038005420340c00d000361090318010307401c80310140713881130405582d03400030b500307407400b148081000642d520203451090481088114240c00c2d880410783c040b404a03402a034501c007644405542c10420445c801280b1900207103540300500b01001c1c00e540c502d4603403154020900034440d1030888014162985860000c4140145106549407542c03410041e03030200d02805d02d440000c002c031001290034403552140d1003d46400e807006100e580300e02c144802c1d031121480400b01c4806002d00c8858220395484003424071941903201c010415041c2011800c0c40c15025800f080e007942c024000d4a1840404030064030720701d948284001c5501c2c2c82c0e011a04c031410070210300c040d01040c000406c1003009a0800070b068011440341d54060280b564075020001d9070500550018a0b94024080107404a41d107400717041414610a04200442c2d640c0340d40b405000d00c0d03000045806802c1d840c0c01d000452515407002001481d450 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 591560512 1250 591559262 591559289
    0x7080313091107110613120609140a0512030402060d0516030605040c12110c0604061a12030a0804111002010f11071a040f080c011d0304060f0804021201050c0a09 71
    0x16584d000c3c030300700c0b40c0820602440d40410010428031040c0c83c403200070210402e10207840c40c15400c6c00400340081d003400340c403250320030b400e10580354034002203030f00ba0b154201c4060000a00412450843d640c8060010b81e400001808003503041c086611030705004201044568512856415009d030640c1d030b450344030a128a241c01c8841a580d81c001841490440b1503400000c1c07003103410f05982049005401c00700c80d01d4400c41701000100000386d4820000040785c807640b01503400d948410082e03030240c00d40700540380d03400c24000e07108114000e50b00141c2041c89090340d01c012600103030125030126102008440145e4641200c0b00822005108042c441c002c02c0d20414036080d0305840e603241d22010300b2014040786801c031001400f400703079074042d030002d55500a041e65a50309440d4411030181a40c00300d404130700c500085441700c1c070100000448045404540321408002000c076000e81d0608001002640c2010510011092002080c80b03103a12a402c0c1e80c00d074035111034560500402c0d001940d0042102e11610 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 591561762 1250 591560512 591560527
    0x120c0f010b09060d020603090a140d0806030d0917010e240c030402090103080a0e09040b070f0908070504020d0b0301050a0c090b1305040209061b060601230d020705070803130911 78
    0x4056128076011740503105c869581e1100107010745052032042d009001e1580d1407610320b44480f40810807000c285c0060781d528085494010401d41c03115000d00034100892403c1c0000c00c018503d400c18130051a40810000800c4081c2d100d8150510300181d904041d0201c094510020410008411940282c4e03103411860035032030070380e0115220540602014180140100f0380d008400d10810b024095644040c0c900452801c0902c1c0c01c0c544102c09490303040119500e400381c20120b6105048034000c450440c0f008002040c81c01c000c0c08000e41c00200d0741080c0503105e82d020016500c0034041c80e4000c0401c140001020035051200800803040383e0410242c2c200100006907500d036004884e60140e480480f00181e540110000240d800d108691480d80e80710420038001c40c0b0101d010600b42d1142000703880300b8004107120b110403c0301d01000320300100c014600703100003c0c004a440c0d0190501c580f0943c21030380200c1c1c40e0300c02c441c515005000941100600301d44c0500440d10395026034185443c024044d503090448 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 591563012 1250 591561762 591561769
    0x6010506090d050a1709090c0309070504110d0501080309011e0e100512040c05030f0102040302030a110a08031c0b0a0303020606120705060a0314160203040e0702120c0f010b0906 78
    0x11003094a11450301a51900203121040c0003a1044c6640180c1a948481c1c5584101400d90400a03041d03100346204400500e801141e001100d10a2640501501515080c102080000e00c0c0200c00c00321101414402000800100d02c2041d0103080c03942c0003175440b041e504c0d0006207401180ca8104541c0e088090b5035882540c4c2264407003144c200100c8240000c03440302601101c050203814071410600d20003000b4007041c0000510f94005944065003542d41c51003e151080b03081c0d121328403000390103078400c094203c0400d94bd084660502c0c0b000070058512941d80f030401c58559009000d9943c0510820900200b000002d842500810003042d07460000b401d256881c00b0b5121040141054098148a0341c00a02074809001c00005040010009500c50170070000c000c00402d00403001007544443c060119900040701c00e40d078440c0294543c000e51900f418400052440000600014107600c07401000141d0200c654000d405000190300040200181d1040200d0a42e021300403024040e0300c4010600c6107548 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 591564262 1250 591563012 591563017
    0x1903120b0307030b041416030b0a140c1e0c01090b090d0c0c050405042103020703121103060111010f2a0e03070b070213230a050601080402011d03151806010506 70
    0x160000848020324201b45402800c20040f42c000d081400b02c581004030800041c940c07528003503000c0e0203042245400a002c0004885026100c0250b0b65109018143e00703103002e80386800c8d020941c1b041e12070810b0341c803040c0c031404d40e01d030240201d43c454001020015018010000074001c8226454080c0c0410410b0700c5d840341000f19805400c1c000e0780c69000240522194036803400d40800c0100c5841094481400014000c0d004103908600246986609000291007070003542e490380c00720038a503851504c0703800041d504c0422801c40b5010a54a1340105510a007003807003400d0600c1085450880303d81c8107090110000d0700821250814402e9915080c469518005410020b5030404075401da95105240001044580d451841d51106070900031414500003410b016800c0d4032405100b0074055442d0740c5803501c10b550044a0b0b441c00500c00030001005584200d10b4440c0c1c6141c00c5018040340d1070003c01180c10603010401080c003d440c60400d01404070800209030f4807595a00c40030b4800c950401d00064490b1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 591565512 1250 591564262 591564271
    0xe04140307020616030c0213020309070b180f13020a0906171e060a0b0c0136030c2d0b070e030709020a09050d050d020606010503010e06040903021903120b0307030b 72
    0x24a10140404e04043c0105401511b06400400c082440c1500400150203503104031800035060082c00340001e0b0011080341a1b48820b400031280c827101c08031080c1440000078142d0b00003175002c120310081d288440901d10041822036904e40d00e80420904100001e0b144c0c0022004040d4010459810007003103010101c0700101c4e101c488040004280c0311540005e0160826820009445400161062645005510802283e01400e590820814070038134174050400711909108560344500f0140c03000244940310300d20204c0e00c10b0204084178104011044503900c0c12816140600e0315180500081c02550400795030301041c145444850405410082034a8901c144504440f41d50040381c60b001050060101c800070344405400400c3c10171141c24101e58819404207010054020031002c110554483e20859060b1101c0032000102521190b05200041c040904164218051000030541c036559a8803a6100c060181d5034907007151580841c0c103400c540c0d203c1c01d568882d6008100400001d0035454605a10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 591566762 1250 591565512 591565537
    0x60315040b03010f060602012003040804060c0c0b040b03040204060f0f03020d080c01050718150503070f020c1504090608010204260a150218030703020105090f01090504060e041403070206 82
    0xd00754010200b0701500e130081c2154821800e0000101e14143e05500c04010340107180150f1141d00c900000d4828203200644002d41142001c002c1444800c3c010fa102c41402442000ba000001d43e54069008d00f5400c160020740c62031600006110642c9000d004640103052400782c084103062400903042d6007881e2500c4000d00540c880316404060011840503642d034814507100900489c68040c2c401810600c151124440001000c4030105e003050049008030110540e9440da5841d5450b4000140c514129060000f421803169030303142481c2d40ca44c568601e141c6c1d40742b00b000b42d45550500c01c2910540f820307600145680c0c0e01c1400204940001c110700c1c048200201c80005000c0e140c041102400d26005000160520703503614000b0a0442082c0c1c004c1109010303e000400c003140c090820907880c5c68180c4400303800035000b841409101d01d028001c1030440101414241c240c281e840010406071121a407201c440c68500c101000b007130002c0700a030343d481c144481c000ba500c0c00a1a0340041c1c101c0c0284a6140c50 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 591568012 1250 591566762 591566771
    0xb0d051e06040c0e0319030813020904110d0c080d02010c1b061d01050405060f09010902090612010216110103050730020408030c1c02070302090408030c13180b06031504 74
    0xb800d80200d848880302040942650100442104100c3e10b0781c1c00c1c0755044001a08000029002700d10a0a10715407182c0d00030900c80c801d45498848034845c1281318030b4140d1080c05e403041c0e500020040c40340c0337400a0800c1d001a285c0800218400380c2120f41105004050140c01d4000c1c8030841240150b0f0092254015400260005000d40c0d1581305e0003600d03e480090340c0382c2401d00c01800340c001000d0f8402e901200401200b1740e203510819080c0c5c1c00c2242c0094100c0c0600300894a5481e000c404103915000b000d00041c03c2540381501d400865803244d009540c1d040421001c10003e5906001741c0b98442100d0501144851100b4070103030050003160084001400c0000c02d400140c603c0d034040b2401013241c2d8080f607448480e50202d2603180c0c103c00188040c14040c03003504010b0303140003080e40e0081303903001004800c1c00d5885490701a0940d10041440b2441c40741040b1481341c0c2a0484070501c0039003600303070250308104403000c42001210300d101c807120b2040303c0078000c11904500100141041386400e440104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 591569262 1250 591568012 591568031
    0x40c0309021002100b04060803030f150301151505040b16030201090605011d0708060114070f0c080607090522150b1c1b1b03090503070b0d051e0604 65
    0x4005000c80e100081d4840d0b41002000840765000070714044031030f559981003100c03200ba60200030440340703280b14150103a0400d000082102d00782450341a40207944000c400c42503026003000a084444001d02113210250040c0700f4050f44034403041490300840c5500b0085c3c9040d0515400c2c001e2030240c402c81962103a80c1070301e02400c1500c00e41000c03d40c01d500407018811940c440c20b0880000c02003400c60f900f02c01c0c0c1040000c4000384102241c600940043e1240348003101c020294002950221300c0c00c3e101c06140110200009003583c2c480402170407560094041e0b4203080354002e0004100e0740c012442640c80c000200d0610002d0345500c051030b410b184000074034142c040e04092204003540c0c40000d901501041403400c4101c014240710f50241c50300010054104c2408a00e00c01c8004817074100c0c0000e50800350582d0721005c0c480c26540d014001e0810030043c55542e80002e10b88540c42d0041d55103070002140024108009008068121762000341c0b81047d5184034039040f280c0000100400d106036185c10308074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 591570512 1250 591569262 591569267
    0x2010c0f03111b1914060721030c0801060e060f0304111315060311090d0c030615050a05032e0213030c0303080f16030c0e1c0c150e040c 60
    0xd4107030b500601d055032406007200e00e05140c1000001c0d1994040d1108103061051080d00d46040015103082514040280c802142400a41d4007c030400b2101d510184c07a2818400e0b019450001d00c420b003a03034010950211811005000308410786c0000103008805140c0101a03940d5800e580c0c1003507043c180e4a0b1241d80d00d0410072140c070031260b000b82e0440340c10503900101c0c3d4121b1b0082803011480030030750396a10781e84140c114111036110300d1208100a05000700112440c044002d030f1044c41c0100d00084100b074494452900721074924084421024104208104a0a10b2000c2030000c02085001d06901c0c2509203082110311090225a05249280170002035258115410f6611071243c550360302c41c10544030b14003010006081d00040d401308840d603001a40080507003441c24410585480e01c1d4a60304500320f03086d0007604400d2a820103000610840ca00340380c03141c03d050168418544550781758180982816407024400790060282c0301c58840f41c40d41500e8100180c00c24590703066400152101c002e400c00c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 591571762 1250 591570512 591570527
    0x603090a150b0d03090503010e0c090a180c171c0f0e03190803040c080a030915020304180c0f020303060a140307170706030b04180222020310031a010302010c0f03 71
    0x1e00f40c0c4014032220180c14140c0c0042000151003080d0700030000b050704181d01998810340210204d0340006501700080c050852a000088011040c182c5130540340015a16000700070000c1d04110300c5500c080452a05414040001c0c260321210317005d4a05541820060041a4040001c0c3c040180050000b5100b400d031010030078841c5010103d004a1a425003910741541140c0c03041e6030a545007035081c1c00201b40003d01241da0140b035a890785420a0302c83c0307041daa0308074004407003042c1d80030b41c0010b110015250501c0d441d0000041070f207a00009000c0620107020b440300243c44400000c541c0144100001c60b00d402180509075003001f0341041840c0201c200081c40d00d2019007140d00c0e0350565111030342071150f00051210a80f0201e40b400d20904490909100407203a140000c040c060941240c0a005410b0280d240045100c40020009034900840581c8081c3d910079110441d441c002d40030104180140e50420983d07501c051280c4066030751543c0c000800c02004440b01402100c1010344003800c26008410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 591573012 1250 591571762 591571781
    0x140a08070e0a082509051302010c06142e0b0d090c12050f07120c06030b01050d0c0513050906030d051612030605010e2409010306180213050603090a15 66
    0x444510100c0b05261080c162801d0207132440c6408031210205100e2000d005003441040c0e030507030b004c012a00503001190000d01c202803d4038016601c0c00c0540d112804045000c0c45103001d100c031400c110b8074000c050846802c2c550640920707940240001e000d600c2c40711013151182c40040401054441c614180100c4d81d81d0207a10081070b4281c0c0446190400101107082c2071001d00c1c400a07035640130f5503154000305140308180010101021603405128880c040d078081890000103150803030500101c2014942251034100928000c04ca01041116650007807800032409004241d81d92489400d208020a41da0010554800244100421642c24820f11000300c51205c0c0d03004146030610442040003e4000c006502400b8000b50081500d651141040018012a10a8407407262031103030085441d850540c100092041c10140c8845001035805e0b0615503405200c0e00c8044010380e15500301d44514080225540709900829007401002010300010400c824400e0700940840900c0a034440d00070004e161005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 591574262 1250 591573012 591573029
    0x3020a14040e0103050d0801030506040209100e04030216050418150213090209102c0a0801020d05090c0414010b07081c0504030f090819210f140a08070e0a 68
    0x5400107a200302058214103c0340108246e5040100d074840440e4503143c01d0101800e954001c0000c03030010300b010207055500600518040c0c0350b0179260305036511100d0041c1d03806c0d40140d10005c40f00b0186614410420010002101d082041c451418855084541c030503101402000901105100e1650140c0403148002100c03e0799100c841d4881414000940020b041c990049121400c00c0d84c0b041d00865054070078100056142c01000160904880c0f0f0207600c24606070800040140050780100900190203008150140802e80e40b4010038000d1500010303050403841141803068480c6007400010310181541d841c000c5c180d54030521420a50101d104100c0044048a8403a0748480c0015082c3e10650043d0311035603c000c1c203660015401c80d8401024043c0c141641c00106103004401100130000310400d124000300c1e19113006020040c820041c0b80ca80343e4001c50b0030f803030150200d21b87c0120059000c80c04480c040d8182201d03c40018100036005104009020302a00c18520b1580c0c0c001c2c01c80c00400449 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 591575512 1250 591574262 591574267
    0x90a020903031b060a09021807020c09070e0f09040309061211040e1f050616050109050f1f0e03030a09030c0b27030429070b0903030f15090703020a14 66
    0x2280c0480200403d003000707510b038010748000ca030074000e03640655135009400500448407001c3e1072204094054000d4004019031007071881344c0c01039850300e80c1403902c95122501c52081881c408401c0c00000b025048100d4401d0b0300b94401c0000190b005002d880a071121841d10412204101c07180b08020506e19809040f03c40d00030070000fa40c91200d42b80d4510450b650f411a9580d080408200000b0181c035000341c0754494810b100e1420305001303200208210501850011984041c80d07140c00b0b041c40c0c0342850800094000d007192054007031886603404d0210705448401c00001224003102510f90202070b001c004007039101c210700010705109040d100c2e0080d800447d91266410b00d000210810001c41289010105203000641514a40030041d20100c0d001e41c0301080ea06059100c0000310944140000c030081e0006201c0e110102c1c112624180c45410400011a52810500c2c403829100c00d00400385a41c9800c460456001901c07401c54a90700301601c1c1c123001d0307250354084400340c6d081c0301c00010020030410003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 591576762 1250 591575512 591575527
    0x80f131406010807090e03090f040c021f0b01030c0519210c0306091a010c11011e080405010b0901080a020d2d0c0905070207030305210103030e030f0d090302090a02090303 75
    0x460140100c4101c0002040651b40e480e92a80c2c5034040d20a00c00c1c0d004114840d03410050406400c40001000c2910541c1c506200c12961885d1302c103640c0c81c2c1d402d491b0795034009612442d40c01d8490440700da00a0306090f400e000702c2c840144000201e5082e41001c10440e01310005865030441413500c4040c034407240a02180f04003100082c01030900c0c0c0f06a20226041508000301c07008240244650520180d41d84415862030780c460a0592000508580c10043c0e00d0500c5000c0c1d110b155038060700b6075403559070a13003107062a0401310300352188080440d01c11a030410042090000009414030540d034152034a0400800904045a901c00003d43c0480151040c082681c02c09030301403818003003540703c1d1001086141d00c0c2d40c1c81e0b10072217604940d0080581e101c0ca1051000c01d0042001c0d0103040c0c004a90202e4405415560382d480000030b920440c085280d09801c01028a8140101800f401e4848020030141c94078900042020000344406070080e100d00b00400e0360b0211301d8040301c29810340981240d5a4031745 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 591578012 1250 591576762 591576779
    0x9040c0503060f010f1d0a03052a0f060a030c1707350f0405070b070c1d042406030f0b04230615040b13020d0c080f13140601 55
    0x412030b02a88200640b1540b8000303903019106281d02400c46649141804600040d0595040c001305c0440740d1110f0404000400038508118085600000c805800391790300c180c0395603403040c0c00483c084a00c00c2c0742c010101c40782600c403001550042e0f00b0902e0003080005080700d0070b4814040078500c0030080404002000340d1103410000000f01ca9a0a03003011100c0c02c0c903850040b04201405606450074242500400c240444074500a1b81240c05401075503030107035603500192140e90011030101d641282250041103114040040341d550341e000042c00468a240903a101110b070914480400c0c003042500c0480c0f14854040e51291019561008440782c2c00960740c1031200300100226801c41c0e1601d0460131481c0100e81041d12041c400543c0d0006003603030b8603408020400b0001c007034041500300b03940c1e030005806d903274583c0001091801c02840060342c841145a020003511585000e00302481321980a01080720b031840900c86d40888015180e10310f001451078194135254884492292071301c1a200082803611 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 591579262 1250 591578012 591578017
    0xb180d0e01051c290a0902070b16050c100b010806060a14130e01230a0303020703030f1e1206090c08061309021e01020106060813030c050f1f0b030703081b010209040c05 74
    0x6008031741c10840e1940d5840d815081c0c1c4103009000300051209404030700510038800702c01800c4441401c02908190845d61103d2074030303080d096600d9040e600c0d40900d03060b6582080401b40c00000681e801454030540100281c000d91044480300d06203d0002451820042600440c2d80038080302c5000c0740c1c3c1c55030340f40e07500403185403103100062606036442403a507510300d450901d001c00c0f04c0d4141c01408429166840594081e00440d252400f8803032101c41e1032142c0d1a150741c40c102c00c0d0780c482c2c91300190040700c07400070b10450301d8580118602518100050602030f40016020781d010000b142c1460b6241d2030550301001901100c0002900410024203c50319000340f1310100c08801020380c02000f00c0303541c0b10022260083c003500d4107520710952401e514003082c0718404c0706143c00e005404440b81e80002c005124a80010180b120726412130089003280c541c50540545108800210000c00d00d250442e210034a5910a400b140a0f0400d0300d600c54507011842074050b9850800018020481e203509800301804c2035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 591580512 1250 591579262 591579341
    0x2d0111010e070f0f15051e070308090606010201052a0c010207050709110711040207062c06010b0c190f2003160e0a020a03090b180d0e01051c 62
    0x1c100102c070205002c40301c0d841c03c0313007203400610000500078003000c02641c181e488417010091984518401c2030150036594010f006540c0b0aa691882d40e01d40070000700e0610340064103050441e4104400d100e051a10001c90100d82c16134400341d02006001c04400c80c482e031184450100c00d07540041503c000b8400d010514070304407000f41c18140b00c4068007036100e01c1d983c81003900c0140b0b000d5040d9045c20150810358042d015040c45400e00050700c955400007584800d82c0d0701c241135480e150104048040c03500602040d401004056129800c0001c088002ea07100c00e040d1403184214807280c150007042c06007074441035020b503030010b241110b0303640104204100d01e0b4070a140c07640240b00e90310000214003000d081c0e940c1140c1c56100000c8031501e8240140c0040c2d84812700c0b8100b015121051034000c43c3c0600d4005000d07000b401003001c442c3c0380301d0014505002c4c2800380e400c140500b101203004a66045400c0f180200078103c02c0000486c008802c1c0c00c001e00f01001d665418056036500946280e02652012018 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 591581762 1250 591580512 591580529
    0x816060c021b100513080c090705090109030602030a0209130b10030608070e0714040806041a06100e040b0306150a170304050d060f0f060f0b071709030109050a0803060f2d0111010e07 80
    0x556509e01044e00c00f0311030229400d0000302114000c0022400a502450300300c0c00b00c080141c600348a290024801280e03a0181002141d07070f178a04c524088c0f41c8842189115071140c04c0502015242c2414991a030045116031103940c105000080c07001d5104101025141603d0f03603501d91199224480a0340e83d000c2241d084802c0d042601d50f15031820343d850768051081c03100a01a40c492405124225143c02800e00103641281e250018260241c1e401c0c030825100700c9002c8036105c0c40e180d0050400510324496404107285100c4005040d401680c00b000302c4094850903034030389684007030a00d0094000c00c0c4a6010f05451850140011444035103500005d080300c09000007010003d85800440700b540c840e114005008003521341503410070407040c1c000792010036001000060f0718025600c0702801e100325001c0403107000e5400030800a945c9000d0300b544c106044c058910901d042740340004440382d280b11260042121041003580d094a038801d0f4410b0341150811002480580d50144840741d1b01e001354018401d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 591583012 1250 591581762 591581779
    0x60609050402040e18030f0c0c04050f041e110a14010305103b040b0406141e06030a020a0603020d0b240c0a0816060c021b100513080c 59
    0x1030030700e054001d0f034041d281d90180da900d0302e4035105016030803200341c0c1d401041c0702d0005005190708241c0d00c402a0801c450b625016040e0423480340c0030042283c500605520035400804e0502c00480c107910490010212070241c80c5a0720791190410710142c0002d0040240d200c1c1e00e01c440805d0340d080e0f8030356180d00e03805c0c00c0e2170500564903480100e0340d00c040ad5006804240100c0d00e1050400c600708641400c1d03030030166805505803c48203d07284103045003120182e4206101400748801c00c4424815540c5811602d0941d08d8181040c1c415034007a0494020f0f02c4800c1d0b00c0352004644142e406106840861f5401407114a02aa40742005800380d0000003e04240500e8180e40c80c0090038003007018807008800c0d1682e0074810030b1941c0840180d8001413180e066a1003002c5540d40041c00d0940246002c810010b00c060710500310f072a080b02521811070340d00c404c540110048100c0c9003110313840b0205075041100c0b00300d8103070850385e0200c466010741484052107820b03188002a2507000031910000b40c020a071440003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 591584262 1250 591583012 591583019
    0x11070203060907060212210901050105130c0206070518120c031020030c0f040315050a0902091b07060f050405010c0906080f07031b110607030b09040b06030a0c030303060609 76
    0x1d44603d031520070000941c10000c01140f4101500d001440000328000d200c882070181032461043c084000c0b981c00200e03a5513880188894035290400034456888010288210300002800a48403200131f8081c81c02d000c00425001c4181c2c403003900c2a9002d0101a080d8540d00c41120810b95a46001010190082c0210603d40c0e204440c0d81c0181c40b00700542440c028081c003c0d4402d000060343c0000c1500400e5030046c480380550303000b500020030046001f0000700c4040d00501c132000048031030240411076414544500c240042e11070020f203d0380411040c558049440c1c04240c0307100d15104048000381303210b00d00f1606a43c1141c00364049400745004400802104a000405540803125401084d0100b84840001134a40300703030b81803030b6a0008491801203030b07050901005818112141101802107541034050480411007000700c02d52003c242d280030720030061810b0100744503c00140000c0c0c0110301080014159480810074085503960001002d03604c0d03030781c03414010b0050051303029210004113905da000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 591585512 1250 591584262 591584281
    0xf08180a1a0a060b030105060306061209070602390319030929031609150507111009060305040501060b07080c0c06030c0d0c020709021912020406020606060d0b03011107020306 77
    0x100d0644000100ca43d00c1d46c1d0a0901300a50b0780c000030040759000c50100000e03007201c00d078101c0280c020b0300801c00912059050090280c144080c0c91a51840100550901d192205034045001c42407000c0d4819030341002b030030001082c2468818881000c000c0e40b00c612040c20513900141e134404640d9039003150004030610700ca0054540d201006040c50400041c00890143c07a400e404040760805c3c141418101c4580c0c4841c2c0c1e1482505222030b00002c60000f20f502024015030034280400020300f240e018408031b4600c0d4019200c1902406584109643c800c000b908000d004d501040140c40310812041c1c540a017840c001d50b06510602005403240a410400401c41c02e020082d240541d560345001c5d400d1074540c6900000908042c0c004008502c01e05000080d40300c5544004e041400c4045150f10034020003020140a042c455240c1c0c412207403040004111256011490700d8001d00112841644c1d000d9004041010309400072800d43e0651030181095000d01081e401001d1007442907003590301540e41c00b1586d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 591586762 1250 591585512 591585521
    0x2001021b0c0d0c0e1905070c15060f0b07060b0a030c0326040506090609040f06080d08091c02031c0218090f0720010f06081203070f08180a1a0a 63
    0xb00b81d003003102d80500030019100c903240e0f8445d4000c00a905604e000103030f180c1c02ea410594281c03010030340c50380f51403042c441030b0319a41c07210900481c018080140b03080a2080d094440b0b105090742100301040c5032042107480d0f0004d6039510b0005050941441d1681402c82c0c00c130f20944002c0300c91795481a0401420560803503100030284a140c03c0e1400d1910b041e0a0102a620400315568440402c108410003551140304604144ca58000b0002c2d0b079604128001c0e1401902c6018102400855000c0220402e400620310840e00800c0c88903d170320318004502640303180500c070b94905103040b1143c69134090b0000382e4040e120f41c5400000980e070600003c802e000c62100c05803200c0d045808420005a00e0601030b0900ac80007000106800ea40606190703685421200c803e54142d000c6500c0f20710400200320704200b041049031807003100307600c1c5040401c00035007003403081c000d004103100d84a00083c0e5042d81820540005808440541e12000554a001030000c4c19140302c808100080b20003107442c44255205 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 591588012 1250 591586762 591586789
    0x6013b01050105130801020a03050402040f0218060d0b03152401050a0809070f120c090c05030f06030c120606100f120b060c01150303020f1c2001021b0c 67
    0x20400156401e09004440c41e6002407892003000200036000126140300344000c0c03011250303599000074182400d104000654201204402070f160061000350f83c10000011580b400903c1100c40315a02e01d104410076004e0312000707030803a901d8058a5075403140b24440104452142c3d8819584450681a510350f500d103030981031220600060b4180021a020350003900c0664010008a085606030340e030741e4810016090494001805240954240204005025035200040d015400c400c0c401202c80450080050000410300c400d002c2010010400640341030014000e015005440d1140c2801484811075881006440303c501500300142210702c902d100f80c0c4000c80740c000e161f44481d5501d18249018004d0b1504079802e55020701c0812040501110920403860342c1d10090a09215052031414003a0905d40c0032140c84d002604280c0c0c00540b00070300d10190700030002c42e60809900c0035522610240c0406102c80c1000000d40c400182070704801910741c003a0341034030300d0b0720100c4a603d07230004140320a0101000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 591589262 1250 591588012 591588119
    0x1c021b0f07060503010501180f0f0311040204121b090c270b04141504030308060108010b040311090901091506180905060606030402030f070b04030c0b03040506040b0c0403050601 78
    0x41c0a1988569540f860135023072039411030300c0281c5030160b03000544031951000000301903910b420020800a83d95400040c0c40440d01103013024a490100c1004444d1303150010407040b0700c0000b9051444450600402603e0484000c00c41440900c3d00a4030000c404248000407032400b04000c1c09c5115000b0284040d50f6241c8901c504051805004a840190804210b03620001000c0328505003840e14014100031070195a44070064207080340058030541301070f08051a20041048240b010a8007124221008078082e19100102d640c0d0b20381003401065a604010a4054207016168110400350414801d4510700b00c20b01e1040007140003030b0b008540743d45030300400e5504850b00085c0b440c43e1440244d680a800581034070215800039079801d003002815003000006030310100d014410f0240e5040844041c28410351080c1c95801e003510352070380d51a00244000e00c01c82e08100040c5e0b17031424260030745c2d00440c7c3c01411281e265841d1985481842030b8410000da40c003400703901c1000d001c0c901c0800070060a1041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 591590512 1250 591589262 591589267
    0x2010c021003180609061103090307033b130b030a0b2d0f0a0207052a04090809040c02031611150c0c01030e030301050a05061c021b0f070605 62
    0x10390a2209016800e0740480615907115151001c01079420207041c01544112400101041d0701d181c000e04840c484401ca41c068003007801000400b1000008a41c2415014142818104460303c0d224041d1514044552104829010341c0141e000d0b85400c080507101040ba04000d4400c0c003c007410044407082c0702c0080e8107074850401040400c00701803d4036040515154a03200e10301050000e0726220190a9249a07606070351020044040c0001c69125040000e00f1015403801c411a00d503242d44e44820320004501301c086558001101ca031010003101e4501020f0014000600e09080c001d050750803a1b10351502460a1009141c1c0e060f101108403902c2c00200c56005035a08983d071620000a00d1080016800c0b40d00d2801300041e260710b59000c1c1c680604244020b00c083c203004c1000400742ca01107003140d1403503802030005000301c2e40c451002106aa0003034907101c0c0c03682072400e585c034000129042c0903034140d84000307002142d25011801314144242880704480100308501c10059803840d05200e55030004505 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 591591762 1250 591590512 591590537
    0x1809070f0516020406080a050d090e040812090708071202041508280c170f01050c030601030c031410030c0b07020315060d021509040c05030c0405040c020a060203190b06070201 77
    0x4540b1805540d074005040003460507110744035a80b4100c08460b05540c1da500110741c102015610020b85800f5001e0012107130b0543c00e1130740d0b80c9541405141000003468050a0019000c00030030840700c00200807401c02c03140720555a0380050501044690280e000d54144a0000c424260751440c2d50122014040240720101820030210709c42d04a407554550110001c00729017010581c000b00e40c501074031141c560080ea118030041098607080c540010346109904080c2000440706000303042d41d030301640a0034003291408800070210b00078a03c074034034281d070000b5070800d112141121044d41e10589104076041c911054032960800308900401000951691020300d00280004c1c0030b841c85500400003600031858603820354001a00703d004189000c10380722001c1583c510750314141c0101c0e4001d81071404c041b49503080c10880c880035031056015031400360b07880e4488406040e1003001190015604000111349a086c02c4404020200c0440400520941803081041071840c0c1942180d4030300380e0503160502001d11 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 591593012 1250 591591762 591591787
    0x711061003060b010210050a05010e1608010e06010c06060e060a1a091c02101d0f0312130b0d090203100606050d0e0f070b030f10030f06150b1809070f05 67
    0x244403c040c11801400312111200140c0c0c0038841c05007918400104256060440419900300000d0411016803407294003258107a0304001d056055810028401c02666901c40c0140c4044204c250700415252821030f001902c21540300010f0301801c012503580720b0107640d44c0b03006400b04001d032800200103041008072407200c0c60300c6090036400075000150f0030000300c0d03680c000031052540c1c04001004110b103008140300a03058081d4464049004881d443c10314080c0c100420341d10b98490440aa41000003d54198501c41c03100e4204d00507d030f500c0d03980e030f55480c5c101c2c1c8001c080c0892a10480c001d11452410440710340c0140150f1080d1811543c401d41003a425010003c0604007076a10928180140d0b18545440003051045502400d00c150751296681040100d850a03000003c268020703101c00380006000180c2c4d1852002c4050307030058804156148243c02c81d04200f08594810328250800103004400d441d41c0380c4240c016044116148d11459846c103506603005091403003004001001080301403c501d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 591594262 1250 591593012 591593021
    0x9070206042004150602010203070801060336021c050d230a0e030709090c080f07060503220317090c0f010c06090501020d020c0d0504030809060304020f03060708071106100306 77
    0x580043c000f050000e0590f2100300f2840058100c200103035000003c0094407a088030050b80105106d240c100321754200305243d5046540c0a0106c9609961416481802c01000400080c9401c0d00200303a036503d401415020349441c0112041200c890254952407102c0502a07412841402c4044030341f900c800e14002e2404001d54400d00e00c50301030141c440207481d0700b03403410000b4001820340b000f8005201c1c4454189283c0401455104c100b0661005414001340b020104002007118110300f0003589036160250380c034030b80b0a0486410404440100d4691003419840408949194100004607495031591a085a00c400584980c2034009a0f911082e850715482421001d00b0940241400101e41e902c84d45d4403401c3ea400019190a0a43c011400e5902e002090102401000982c2482032030f00f46541c0e0307562014050059454400c620202c00541035480d03603a9002c800c9040103069444501e00490080d003003507010344204001848801c0d034110120350000b11103004254480b4001c5503540785564140207403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 591595512 1250 591594262 591594323
    0x11030106020f0a02130e0a0c03050105270c09060d1406062d131103010905070f020708070504051005030d0f180e06090a020c060108070e0f0105010804171e0304020907020604 76
    0x6104214440c40403861102100010327600c1030001146900f4001180d07106461035640345011030304c03081602481104009a0004007010940d682e4805a80b804002494407000c040050a030b515003c4402e00100c0300461014840d100440340c201030800080b41150302d4401e04102d2515400c882a603d00d031619000406920b403a241107030208102180941d13503003c64100703900c0a20a9030f10355040c04a141d0b0020a00042c2281c14801401014601039507950341d001d1900c2014011952400482c25200002e440d076409007a002e81155202c40306100024420f86c1d00414080025101000c18040b00780c01d40000003c17942c8810a00070300c1d4582c0f404010a00070080d007883c444903400c124240c2210020700c4641d00030004c2d40c029050322442c1c500c05081c3c5a03002044c40591454090040c0040d0fa0045070154000360005c0490400354802c0003038801e05d00c0744550f808a120390342ca25514404000200540c400c6100756120481074480c3c0c9400c1c0e94505041e00c004111980c46684140380138200010380450 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 591596762 1250 591595512 591595541
    0xe090c01080c0d061415071703061c08091207060e04020d021303030c05070b030c040603150e1302040e0c151e040b04080c030d02030f160611030106020f0a0213 70
    0xc001c03d1100103000c8445071751000701d01600168025000345030507200d08418408000b001c80c078003407007a82c0e00d40350041803400c002000600800803e54903110401c161b030403441403101002d281c50603410640d030160448802030b4424001074010700c0000364088cc03034600302c41d03064558003120a840c404000c0070f9040100d0510109909000800c040c0400125040045010340c688007508691400c0c942d05040745038029640901e420800e101c0518496400c440854026160025609020340327240203a072403c035030082420f90505010303c441c880194a03449040f03442204c0c10440300804218650310381d0480070081d03500942c0428164442c1103160010404848500300404030041a11401c644640298000f180008808202071003d02020443c410103014114000d04d000c95403404025034070f2040844460201d00040380180404241c90040446954010782c00c1c0903c521132218850590024424100148501408440304c9400803d00c0c01c0c0068024000c4c18a000001d0f010710080c08222045020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 591598012 1250 591596762 591596767
    0xc0a05091b0702150405181012060e160914060a03110a241704020f01030c090504090501241802180d0302060a061401021b04240503070e090c01080c 65
    0x5940300e002c0d045140b160b1184c26500e403814101403010b5500024041d10514100070140800c9404e80d40111007100c100c00805d0907840c0c0640307800005024041d05001891080c200494680030250085600b03481043c07408001d01c0e00b05441820b01020700b91031807900300101000600101e403c484699001b944c024217942c00035941d91500e03102d403447c0d0440001c0d8564080420242d40e030b078801c00d10308403021400a00715140c20f154000821a02d89800200e040c103a9072803901000394000d02e58a00106001402001404d07601d0410502a0000c400500d40b2103041c041d007072190300d100221510a440301c1c105040440040034010100943c000d42040308640303d0181a0500c07a5a40d0b60180d06d1030344070fa4050000c6040c0181c44030142c42da280c00c821021490542c501000f0399001482605030100d81c01d03603100d0542c010f008240280013030006401072040b00c1c01f0129004e0303030400b5001304031030080c0c04849130269102240104060151445180e9400c404400041c5622903245280c208001c241c0d0f461 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 591599262 1250 591598012 591598027
    0x80f06120a06050f0a050c1603020705030a030e0907080f0106030f020724060609150c170406021605060403080403080a2708010b03120a140d02030c0c0c0a05091b 71
    0xa107030103204041212559111001c0040c03c4201c01c02c4241c10400c3c1e181d080c032060905498540c035074004c0c41101e8a5685008210030b041c0b6100300001001864050141e40403068141001400102526a0340b0301506c1c00001141e45a485500d070b2070701c0f49030140340b10641a400c01404401030314211081d1801c0680a108450204813490001c3e030040240300595001c041c036152181d4165107141e8010310510001c61030802180ea4628801241b003551403400215003000d80c80c0c450610f0402000c0040025800309001c68110b4002030001c112290112100d640d0350b03510030030003426114901000341f60503410b10003040000c1c0100060000c04541341000840404d180401d04000380d20b05048401e01400c0c1201049908020b2140081b044003d9014040b810f0b00c1e034440e0b92281c403c07080108204003800c0440c101c80020070007074602c641103034130042d580c0b41000c3c00410f029800c0b9900d05c2c8030b80d020700c4e260f601845c90650a001c0c2120703c0908160180e640c0d0540d121400e24160304551320720752040040a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 591600512 1250 591599262 591599299
    0x7020a03080318030f1b011509110f030c0c1501060f051c090507060336050f0312010f2705070903020d050312070503090a02040207020402070f060b01020f0a03080f06 73
    0x91082058400c15182c45506c3d122031410621040800d80420340d250642c130103030700e0344019056425100550b0000c21100031a858880c2a4400c52002481c1c0c000e01000b84201c40c02c410005000c24103e100c1103800f0104803120044844400784105030100f40080b01503141035002d003014100148400103500040401c0c0188a4152980a6000c039070b55041101c080c80f0300e030703014460174540151410000c0342888200a510324080000050404043d00c080408030811000f0801000c250f654201500d45940d0481c0000700180c0083c010040000e006a102040c101c3c444603a010808412601c400c0240301c280600500030300d0080c11302010400340800100261b10303004460384403148240c0013596229680c01e00302660220182c100030030440100240001140e00007060729451340c0480b00107907140700710700c0018000c4c0b1079510018480c20403020004103020560340b100c403550900380c080d11034489210111a488010b1000300030301041444c008a0040c0910056203544004041e06202d105448070104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 591601762 1250 591600512 591600517
    0x11070609180b1c230c060f070203070e04060c0503060105090d05010b0a0608100e0405032205130506040f0e07120f0501380117040c15091a07020a0308031803 69
    0x800c41c241e0050406010040b0070003c81a80e0840700b04c0f010307080302200366440c1d00d0364180d00c41103200e418081303540752154449000f00c6084560041c103c46565685034800300c0c911001f114161404d615082e00001c0c070360f02810859104400c16521641340c0120002040500000a6001e5a1641d0307540703040b5a05843c1d1404803800750103540c984141510301045203004c00c1c2c000340c10820301f180d260010301000810000540348803004c06003d041c90b61750741275140c28642a40c2ea108585c00940441e20159910807a845107005100030354045c0b04055045642006803005015582d005500400b0104500c019030045003103138602c1182d0b002032000340d685800342504d00791799680ca0100045124071100b6200c080c1000c1440000e05412182840d0320030010742401c2c0e0341c03400c15810140b4400050208030b280c00200c0040c044000210700c80400641d8001d00181c4c86c1d000f0300e900003441c1070380b40a810310a8003c2d035400c43c4c2d000340628151800c640d101041900090403481d003901d04a1184400003406002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 591603012 1250 591601762 591601789
    0x518190203011e0f0308040b0309030c0706090302010807030902010914061b010b1008010b0a1103070507240801030b01060522060c020901090c0206152e11070609180b 73
    0x1484500703d002d20350442180302c20b0380c840842c0034040c240c1000081c0d00c1e40d040d14102d65019010648030f03955039407030320704520843c000d402c0c240c040e04001107095a0401300da4000d80e130013079a40d2081a6a415003d13030440b40328503c0030340031400711a030411a1581c50181d0b0191084090078003428441030111804c00c0c0200c880d01d0100694641c03042c5241c504005618240c1c1001130310b802c3c5d44551610403102018494941400100f100d030100254000504004407000f045c0e0000448041c25507946961040311410540041c0da01034140e0541d208a1242a056069a401544800c400d034a01401601c0d96440201f001660700041c40c000c416501c200d0b02000010300c480e0305e45500b1241c251042055103101600850074140c500b050385000c0030b50004a85902a526075106403007903500500045480c0404152140c68894407545075100f000c07595440c4141c02465190325491201751030000361945401d025450009a0036042000840320355003915188100d810f000003071059101010562400780d070354 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 591604262 1250 591603012 591603029
    0x30503040311040e0d1b031710180b0a090207111201060e010e0f0402150c160911190f0513090203070f02011506081024031401051819020301 62
    0x4001c040d0300c1c1004c0c0945408004a00003a00d91001000303c0074001e5010340406001007402ca0080104041c0204460480b010164009814915100808104a80075800343c0066140446a04508072079540644044414014000d049050505044900a41110200351103566115000750b00311740321090a182c0401002c400410b2050030140883d4a01c041a8851200700d1489001c00c0b64008034902480e03040340e41100c0f0680c0c0920754091245141c00b41e260000c80038040ca190b5010300d807000120010865058850a101d08101903c905440307000382890b108142c296810700c261064031825030a10070107454140641040002c81038508010343d103412846c00e640d4000144040b06400010007014485244000d006101c1182d0034500052818031800062119813408074002031009401c0c10054004d0307144801e1007507948440401000f000c00d0750301c00402d19191a42c0000f000142145050b110b000d00003901b0080419000001c1c40c40060104049060b554510482c105250008600034910381 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 591605512 1250 591604262 591604283
    0x10062f060618011d4302120d05040f050102160303050105060c06071209060f020d2a0f0e0402160b07090608070c050f12040611070e062b0821090a17040305030403 71
    0x9803480521880000305c00065602262a405104001c841220310301014078401140586580c548102031080c01c80c80209a5400852054150080b981081d0b034207600075541800181d81e50818850a0b124061080702c094001d440042c007014000c0520200441e00310800158102c01500d440b01150031414a0388103498002a00a444040501802110000400c0c02003010b003c00880c41c490300840039811000e0000c0e54116680035030181c6407402c103c1d0009407003035549911203055404d492480020448274501c407840404c420724401c0c9004000e03034500392101c0d81d0584400d04240e648541c0c0c500100da0b5441420310607000424280002c0e4180e90032500c149032600e00349030380500700e00003505404170558040001009280810564540c10441c241d40280c44e0030300c0404003a8a07015089810f40400d24241428402c10000d0001403503082c400d10101c0c0404a59444188403041055802c103031103520075080140480c0d0b264042d034080c07041e1074030900c0c501552603594604640041d402540c401589 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 591606762 1250 591605512 591605611
    0x3030204090b01021b01080603030702061207030501081501050910030812012c010e0a020712091409060d11032104150810062f060618011d 61
    0x102d0050b407091a800340042e00aa0422002e103e80080c44150040c0c10007802c5808151544c074103108a80c202c0750054080760b56003081c008401441042540c80c680000d01d440000140b6110204140ea417141450029a0141c0d00e840e00700000000c3c084c000075140360000c00c1c0000080e606200500c0203103200b804104456140680524803510b100c2a00142a12165411802640c2e02040329041d00c490320000042500c460300c0c030360024000e1880003480b94a01800400c00385800c000120100e4506240d224109944081444050700c0d00703032a41c070341201c0354003500800203a040d801c9849880f4050100c5060144944680440e844600b07041243d8803000103003445100309401c2d071018109541e0a019015082100702c3c0c071318400041c4168400c00c01000c0c051300302e00fa810341320003901284540030b00d0b01409481c0401525024183d071094400c0c903030760024806a00d01c40c103546040701e84105401803507071091030421516050082c0400c15819000c0c2c50700c1099201030f80010700030f22010061202041c1c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 591608012 1250 591606762 591606779
    0x6061204060c020f0c060d111b100c031104030b130204051005030613030e090403050f0403150510030506070f050d05070f020f070b04030210050915030610050712030209190303030204 80
    0x703182003042c2c5a8001d0292105d81da180c1d8022168100d80344040004c000721034266880c101c0c0224a10b00c07031400305541c8030b1402c619001602e009c400c007c1400400c0482100f140130b40440340d202c042030411500c00c0c0301c00c00c08a09242c115a5200c1e00c01a00703801d8900c0c05500007801c40c0e0045507804000900014140602d0504004281c0e21180800d10b0b016417415a85003c0c1c05804503c000c01c5c454005640050200b51003501561001260490015140c030f440740340c01842400305920398000e1510b4403001429890b030b0113030010201d98104000e001c05845140048880c010307112448414007900708102c808a204a200f410701c29901540d50700014640d450000707017051050000248141d204800034800c07402000111401c0340e604a0745540c00700c00828082e9120300404814a40c41201420781d080e0011425000f54800e040884200c01b2441ca001d038162500d0151f200080c1c848044c100051040ca03010303a004104011005003841810200b11000000140c01500110000381c0c020400300500d50 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 591609262 1250 591608012 591608023
    0x40912031103040b0a0507210204051002030a080a05072c09060604060806010f110105160e0103020a050301050f06070c0801020c0d0813022e0522120b06061204060c02 73
    0x388850070a91850815441c0d003030102c44040d055002103566400480c4040b4099403100900110303150030703005c0388000708540c000290400c0c8101d500920a09103500c0e002407012049031703800c1c003480e00c4c1c02280303442d10003c8500420008083d241803000303442507410140d0390344991040340c80e40d82c0003007401070031410140001d05501526160007100240418000f154002d2082036101d80c0a1a151108402304501180d007050110052740303055281206000c0c0c00600003403c0a0b0681050320b80b255020110070044089219050005000400a01c01400b0601d841c0019140000c0c00030010350030074803242c403048081001e5502200c582c1e03500181c40303d00c9c02e4003880041203030396a90400151030314150203540c0c201c4441d070342c4c028801d8040030781c10001c2d80514a40c0400c03295a089072600721fa4210b003005001ca86c842003440c00305240c8200400704050380d01c04041d05594910148404803034580c0d481d5881190084d1446034031040c01c0c051075144040004085105500480011919101600c0042c0c00c6c01c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 591610512 1250 591609262 591609281
    0x3010f09020403080a0503090c0a060c230c040b030c04050f040b101d1e0c040302010206180304060c060605030a0c050f0111030a0f021f0c0f020705100e040b04091203 73
    0x40e801400104042910407081e251a441035040040e0380399158000076003845a81040c465000c40c9040c00416107552202d0b620070010f10501d0720a500e00140ca1240c80d014020042c5c4a50f80c6d448280316610701c0c28a500321000b040380140032503400e0400b20002500b0b81e0411260000704060007070800042c4094621142d07006400000c20340a40741c20301c00703401300010b0440e50301407400d81e881c000f00320450b503009031800242002a14030b0055003400c000c5c01801d580144400d070300522901e80810490315664164400386003825008611309441d10720b09a4104c4100070081d120150703114800100381d2402d00c02c840d03006101c0c8155440540c203000c1009210080d03c12064104003100c4e6016440c18000800c90300c41d40c025052510344030134502000c902c0d04842034007490481c40010ba943d6030419041d00410360900c00e0791500504018103140490f0f44080d1031041a42c409882c0100d4140103020746c2e214005403030050804035050000c407000c03501b80e90003000100e40c0e034030004120881566041c42b401416 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 591611762 1250 591610512 591610529
    0x1090209030303132604170303060a1401020708070806270606060904061805060109060206150d11030d020d1404051809011e061a030c0304062403060203010f 69
    0x10311050001080d6207000042c84000c0912800701c40405025800c801c81d18102c040c0c03120301041d0100d0300416a101c0c0c1103845082500d82a042e4000704480c00801601c1c80345030040c000311201d500d441c8184010016124409041d402070400201d101d0005001101c05001d21200034282402c0c41403680000d0588005082c0600400104034618404089501a00700350100c500549520040000400402d900d13031280342004061450990000f202e504001e1013400240c880707000956a4503410790302c45070221000300724944c0181000b01c00345800554003100038001c0038411155a004c00101e8075111181c201500075078804401090400d0340405400c1020001844c2d0030700f09840d1a001ca002c0c00c03000044a84020010700c00940200002d5010305c010507110391803d00015070568001d00141002c0c0180403990100e1150000d0112022048034041c40c41504d8092840d03a4039201c0300010194034000c0d180790192110039042100d600c0e54603a0185000380303c010303540d500d008007103408204c85074088001c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 591613012 1250 591611762 591611767
    0x6030d09081b01030615270305030d02210705031902090303091c06020f13082103060102070f23041515050f0d020c011a06030a0c0e031c08010902 64
    0x9180300841d480c80e9901d45482c000700309022100042c1d002d0409600014101c0c0b90078a1244082a41b000b81c03001484251080c00010070031a0006801b0075009000c003400310b41c000c108103111380031640c0c003c00715115081e42c400340c0c44060b50000c06146c4000d459900000702c0110900c1510f04030b80103815000080c050086180041d4280400c0d124042e810134203119026842003238541c42c0e024601d050049522040c119070328059000303a810a80c00c0062843c1e489828006c0c04280703113000054200d1143c0380c0c2007482070a041e450b0800304c038980c0000c0019046014100c0e000038650f400100007000350010314408001e210902801f200702c43ea1640101e8425814a950801e46a4101d410102518070341e030a480c000201c0e50405498078400c240c80b0f5901303010001480381946013141e025148504140c0004e0018030664440c25107801c603070701401076000100700007040411540c2e61200e04400c5030340c00c019000454400009007041d1314100001400b0000b103d0b09a400c0d07a00880c0c0328090a0501700450 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 591614262 1250 591613012 591613019
    0x50906040b070f02030d15380702031e0f0d0903122706033e0a1403090106031407030b010306051503030d060f0512060408070206071a06030d09 63
    0x1d030410809040d107403e002840c028045154070074000c41c1c1940704011424003201c644030580704144d90840c40380c0040d48000042d0ba40d120740b800c411012500d5054007160356031410008900742d140d070206101b240e1501c5403403c800080d0442040860b880072490020703208180c0c500035001e01b0121a03040036020843c50076001d1000841001403070003005468030b44600b5900380d10003500d0501650702d030f110b00105801e050024000703905412688820080004031002088802c0c080540d01c080c4440d00c02c2154040464803096100e04000b42c10030340c411f8900141300c2400c582d0307143d4859200790340f41006039440d107105005200220400e81c0c000103000b0020240c403851500c0d882c0c3c1542041c00020441038484d8040b68070704614807003000154000409032590dc040d0f0300000001084a4840e000e0350301282040001c662805c84103e00015041001410041d45d0740c0d51808d50310f0b4800c6404903800401400807001042e0a101c90014158600b401da100c281031100c101403503c001111500108a100300e02070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 591615512 1250 591614262 591614273
    0xe0a030801090b0d0f030219080712050c0c0d06021e07060b011e030504030207030c062001150e0402241b0a12030c0e300c0102151302031b0405090604 66
    0x580410b811849a1210415510b1b0483c00c041151101c0205003620034080001c0c02000c1000300586c034451074a07016280503407142540d1a0060487e075941310b40180c0c124214034100740410501c5103108140c014038055800d41888404c94003a100d80d051400b010903d501004801c1c40380b8100c41409003004941200324469400c0d698803407820b010700f0961558081000c050081000402035a840390050203007585810740140002490410b80d403140500500c0c08000359030611440c2031001c80980744001c104c1c18281d194894003000303007007260400411110300034842e410036900b558500d0904d0085030b0300e002010709107506c629441c10681c0960040c403c0751000504c0c20005940899460a010401d03141300901136414092070301a041c0c002c017495041c648800001c6002d469004405045403d80551441d0740381e9964a4540245016a000d01341e00c0c10b80c00784c1400310603031126070345e11510180d540030f0b030121303090914074030715002d54040d0242010558a0240a4241e0140031217000705050b10301034852 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 591616762 1250 591615512 591615529
    0x30516081b012301030219080d050904050717060d150c0315080105011206180b1005180c030c0c031b03070303060b0315150c01020c07030309080d05040b0d020d0e0a030801090b 77
    0x38850081c1f08114001103407400030780c800038600d5030150f420706205000060034561005403400d1140d860b10300007903200c90003852860880c1002da4501d032081e588040501403900d414203c180e40a4260000036238142c1300a000d65000138410303035000704021610094007003400707849402084403070741042e00502c0f410313803155050069160442d00114400c1480e0303001c80110840007002034920002c12080004007060310910004a440075039174020074031403080c000f8a2044d401d0341d550030024010004036000204100141c903400000c54180c0b45001c1c8008440c1400301c40c0c00402c0d484a800c0400d20400b40741c1c140c4030720ba00500304180c50602e140350900341900d400541d146001e112f82000c4800e0214202c0420555080001c840000c558868000c28003a941c0d0405200c01c400180a401020030011740215003a1502605902c50034100760906070b4080749600484907001e403455003409010001a1a030050f05103180c0140050004840b26040092503107205811180d103450400c00d407640a0b0b240d0310703803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 591618012 1250 591616762 591616769
    0x32404030302070f150b0a150804020d050106082506030c0e0405090c0a08010b09061801030f15110a18050d02041104030c0305060123010c030516081b012301 69
    0x1030040e40c3e046075240c1150440070381d62000e840100020b4142841c100b003640100d410389011103a9040c115698002c086141c64003582c050001000b12012034014148041c3e01e110b0a84603078000304802c1d0b21401160314040301181c04401c40e0a89800099140440702500c1028140526040c0452907440c20094100760542c0c68080c020b0303948074002008280c0034007002401c80300c024850b104055072004ca041c00f0300301c10a55113100d10764a2020490701d00c1d01401c101e1694a00502181075686181c50389108004000d81c00d0300c014180070900c1c81d4036000762060400150850110a0300c0d070004000042151074035000c805451030581c4810303c156a11400800030003541110701045a2070352040b030708254015640000c0c188442040003104000c00840e20b64140ca413502c502001400b9080440b00e03211b601070801c036010501480031400840c1c896401080d18000d221552030a8034903580e581c80103070703100c50944a41c82c0034031301543c034040c0000e010714141c482c01e20900403c3c46d0915881c19110749812321 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 591619262 1250 591618012 591618017
    0x1906080c100518130e0c040204050a0e070e030114160903080f090f10030204030201140f1204050f06070806010f032003090708030301090603030e121f0608010e070503240403 76
    0x5901d0050300070a00b040f070150716018001c00390000e07200c26080050091018445118080d009500000d41440e10a6608640740100250300b00340c5800c0c26031481070320140406040281401d401304445e1000d00503042c51081c27002d40320080d45494541441251901d02420041148070001040452403100076100d40740d9250402e43d99404040d4009041d2a4030040034540203014000c648543c40c0e01035004c0c10840e4000c1c0c0706d4140c00003c1c1080048035200300c1000c0700d02c00409100c244031440e103050303255034800d208404403100b018401c0c444503d080c00c221141e00008a22504001d000d59101544400c0c207500c5040c00c0c0142011820b40861404040e1251082d802021002450005080203028018030394602030700d0307595860300100d4001d00050300041c3c02282100d1101d0003c0c0c06d1160314949100d00310006800500600e0f004803002035074000f5038108403602e038030000c58811002e00c0390f00410358041c4002c2c2460f44c9010141414048500445d500ea07844c44941051025010130010782c0c81989803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 591620512 1250 591619262 591619267
    0x9060906010e0a030c1a0a0c060b062101080f01271109090c01020106050d03050d1515031d0a1703100905070c0303060812071401141906080c1005 64
    0x1440121001c000350041e040d0b00010700360b400410b001d2050b03005c2c000d0302c50300e694400c800c0318618000304c06846192541c000045180c10844003144595101803d11035004184a2601d0228407850305d00b4442c2c4000240126007410040269050800c5215a4961010001d00c440884811120150f100207019409022601c500450400580c5035200f03c1d1000d004120410301d08180310159074800c00d0100c0280503600e48800440c0c075140c0040e4030210140e25980e242e1604105601e03500c06814100c2e0f10b80303010315403100003003060308040703115000390f08043e500004c010340b501040d001810b0844590405a4100e0350f001e10100d0b00003521080c6091881c03050319620b0701c424100d480340170303a0383d448000078a2400c424041d05a81c02150840ca4030301a41d070034031145840d090146d448003900603600360112800c000a400160003020b090070481500400010600f034040c00c1200802c104503401d1030889048425414860900d12030790024005000040200444400105d482c11505201e1a018800c01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 591621762 1250 591620512 591620521
    0x403171b0a0e0a1505160620071403091e030a060204170c0f1f02100c030e0f0f030405041a0a06021e070501080103020603090a0f120f141e040f0e060f030606090609 72
    0x6541082300d2181501c000d130400e40c404542c1c88903180d042004100c600342d980324110103041d00000150b803c40d180041070344240b284003e09180400d8004502641c150041c80701c01e00100e840340c40580010201007040c040494000c29106050000c07055072140324010309200010541c071350750f080030380b19410f11001c1010882160010303407800007184903a501c81030401e91204603959050b04821901a001d0007115520044101059100c451a00141c0010751040c00208520b1030190092a031387c1180308411000800d0940c08510301038040d410202c096489100003111034054640c03484004041280a06070aa040c240000e008400622010788200000300204214a800b4881501c905034003a1160200300700c186040649007401440d84804201e00d10110304c0481e0042c080900c00f40015a07000f0710b40304c0710540908c1040140e51007107640040520002c140a10040040400350030b500d402034095140210410001000c80301e07840b03019800c030300d0911002d82c4071a11225004141240c040b401030340ca = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 591623012 1250 591621762 591621773
    0x1e031202070c060905040c020c040b150c030c19030503040b0a1103090109021002280303090c1e061b0b150a14090f0403171b0a0e0a150516 61
    0x1000900401910310004a180070004081008801c5400301d85039140d03081d54a41c00c00046400f1003110f0b00140c0c1082c45005150314065110300f10300c08000301101004420358000080320340044d6a0703031096070b0000609000c03c070000c0280000311070704000e1048031074001e0350b40102140005840108000c01c0440800c4812038140c000107880b030450801d03d6220320708000030301d0203030640c550140d010340f60f003a582032701140c400b080c1d8161118802c0d41641860403907040b180d02036030a80d0030903030406658551180004004001000041c4040ca400210f0310f003414104040b0f000241c1e000406000c44500060712030019010303089051174106401c0440b6030b40d441c4a80c120300030490040d56210000280202e01c90800d0030911414802c00da8603c042550740c0c61480254580c140c4000d804644900305400794003e02c1540d2581c01140b20a808482c980a095565030540206c001e903400305405810f05050f9052540e846070040210306021100d129081d5005850b510602211081d0780e44c1445020f0309114 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 591624262 1250 591623012 591623027
    0x1409010201020d0c03020a0905040e0a3002071e0f0b13051002010c17071b0f0209040f120f080118140a05041b05030c0d050109050a0302030307020c0901031e03 70
    0x810300c641444a0104c51070003c00a6021300c00f45404140103120108160500f403054980c80640a0010441c141040e1501c22079481c01c10100003500d280b43d544024800710042201c028144240c00501c1d0807414145a003003c079441c00c04121041c015042c0401120740e40c0f00c4c1d154103c840c1282c0696940005605010f0807002c141c1015800038508807491040650541c17004a81e00c1784c0703035111060110840c01d0341401e02c205032807410001e24007001c2e044003100b240800400072442034000140c8000d80d54007040d00010b003190180c400380b00300c812400a00140da94602c6c903045c4140380c584a00b0601e0303000a04055018042c18159940c40903003000103410340d41c052250f48001e91081000c5107402da00000280c01c1c201e50417240c65110456490170480e180030040306640c00200a4108a81390758203210506000c2d2006407010b40d294400381000c0394060150804141c0a1750103555a40340c100d00103803901b50041d050501800020700100003103506402049400040c226045261012904040341e03001e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 591625512 1250 591624262 591624277
    0xe091c0203190e10020304031a07170705120c07020a0312020307050f1b1509190b0d0b0a0f291b0c18060108040209040c23031b01140901020102 63
    0x144510142224166080000f400d5211400c130752401c188808801c040740c40e40110700c4010b1404110700c200a908003910300d000d69000e4420301d00b140c805003c000386154000016141040400c00c0014070b0786981c010448681c1e0312403a8440802d14112050380421500c5501d0b110240100102c0e03c40311010520a0040300c0d48150000e08403081e61602c1c0f15181d07285d009041d10064420f202c607400100324102140c0440074258600c3d00507003046118070510000d0744002000c00082a444d51780400c13036103503000c05401c14010780e03040020f241c0008001d0003010303002c070340000541d00280c600802a03580c005100800006824107202101ca80006101a01740195078141000c2c0440c200102a03080f00040c1280c400042140c80c20030801c942d03000d070902c500090303c1e181e0010310141c0006002d41808860b140e042441440700020b56a603c039241e4240200030300249011014420260382285010004800202640700198820140000000c0c01100382007800c00c3c05282d01003040c80a584c000c0d0b0548406 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 591626762 1250 591625512 591625537
    0x150307142b0203040809012007140315040b0a0f0b040906020a030e030c03070f0c081c090b0412020f0a030206030c07020a05030111030712090803070c050f01450c030b010e091c0203 79
    0x450345070340005071625018ad0615000c3d200d10041040c12504401c0d841f4000c0350440ba035842e0320f8603583c408601400c140071042410310b03201e4174291241c0d1034030700c00d11801600440b00141c544a54900c0101903440d90524203800382e1060043d0481c3d84c80210446010951001c1d44c03117010000740c580243e079000c899006800b940075062400c00031449074030009800c0c400559a00460a48500502c080780c000c070b0040008020396030320120010f00b0080100001c42e01d000f00401d41c0c3c076a880c6e000405070b9104071828000740c0d902040320070031800c2582c03420000d032600b10024004000407030100711035400700500e480208001031011140d040115844a00b24a40040500c0d650303107030080000e0a0f1800411040710103200e03041000d90789040c180308210303000c40f958081003845024200d01590403002c0c200100c051119800a0000d1100c8440b22400101e01c9080241c546514508210590000590100d021600715108000e038040021841007418801800e140085014526080b4614041d11a14250 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 591628012 1250 591626762 591626773
    0x1f061d0a0b0d0e1c021b0102010f0608010b030d030b0f011b080313020a1d0604020a0e04050a15061403010b031008011802030106080c150307142b02030408090120 71
    0xc901c5480d04403920242d4400c003100d0020004104e002800a41500014010b821207807000003109910312401c0d40101051002188600d0841860011280d04d940451034036959141c0743c0341141005e000c2d02902030315078202040002131a5002c14100806151041e0410007440c4070031a20750700c0d034121244160341041c00703a5201c2c5040c5816030b40d404510a82a4400c20440070001107200c0c2c0c0c9110b03010030725521003031030300c140e1a0481400044e4000d01409170900880308a081403a440c2e0b0710034148658003041d00400c88184442d01d020302c070100340e0440d1080005074440c0360850a2071100300c2c3d0441700519051380d5299541e0180741004107440c0c1100c0c00550900d1120a0f4452440c0b080c40d401302e000314020451166213081e515520010f07030080c550851140001d000b0880181e0003d990f200c01141000d2100d03211084840d0880e52100e02076946401307841d1448804181002c0c1116103c0042450031499400c10303407030781c29046c0207142609042141942201c44040603020b000008200c00c10201c82 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 591629262 1250 591628012 591628027
    0x61806120f02120403020a060b060a0f12020d11040f080102042706050907180b09030a1112060403020a1e0305160f1403120603060f1b041a031f061d0a0b 67
    0x1f034964681d101d00b96110b508080301c02d40d55151509c22607611001944401c0c40001402c0c200f07487c80310304024003411896007803015a404a84a001c0d19408070411581e942da250f0600c40320100b8180c05800c14070540e031050000b40003805440480307600c50b02000700c683e40e003c506072100c40080c214076000b554000254005000e2120b401c00085400780c00c41851110300c40d6150080c00695002d511102e5616500c040880000304a100b062400d5280020741b21400303144c0b405400515107a0b003507904400507031022910400b4042211407041018403580014086201c0b1070700c005115014606445038604003030420007040001503504916980c0d0701c059500640d00c002119141c490b00300c0640c00d00e04003555000141146000301e80c2078032400b01070a0158907034a074600d2420400d41008258000003008201c041100791070949140200090510281d549251010b24234541c500800005500c0d0003014000780095508540c145004510008203140518281c0c00000d00d4101c2c558026000c200e400501c00c0d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 591630512 1250 591629262 591629267
    0x5120301090b030c13110403021011060f09060f0a0b0a08010614010905090a0e0a1b0603060b0c0d0f05041d0906130c0302130f05090106061806120f02120403 69
    0x114129001403400b00404100380b41455110300700f00c1e848641c80f0070300004641328a02c4c035501441c2401e00040d0594142a103e40c01b1424656900428002040034048400100d2104011003540710a41c8800c2c061242400003085980d4503000c1c0c0700110b044d904000280c540166907016245001c002043d10b400c09585000090082c9554000c0741588031314040d21410950042028008582c1c0141007941c4640d1600d1400000741144400700c00103000b502c120002044000b45150880d402041d1142c09241c40c10780701408885c8280c0c0031450a0a0071b011111030302e103000c81c2d03440c0128507904200114584210044640344215000313112081c0000e0106165082002031861003441c17003070104d807140c1d207543d51010312014141400074030f4961240010310040c20107514880c810004894003107440c0c1212075843c0c00703a038812900e2103030a0395108420011aa030220003c0140ca0348030350900c8200b0308102c0700802202440007464006c640741e682510300e08000f035044502c2e40e510102c0c81007842c106443d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 591631762 1250 591630512 591630517
    0x6060a050d1a041a0303090d110a0902030603010f06050f01030b030f07080303040506010519060c030c1e0b150d0b13050a0b010e0901060b03131505070e13020901080609130512 77
    0x6500881c07410340083c81c0c41e03528000040c05113000400642c102200b5008100601d020058100d44030541b510b45200309031592803506000c1c003044000907840c0d2400e5400e150858a4000401d1451381c00e000c0700b0012616100c14022b4945002e00c1c000c241881048007103440d04088a640c0007407845601400102d50300e01201031030169100e00261086640c3c1c83d010812443e07842a0b024000482c80d4804125003030003070401c1d1505500c2411f0941d5232640b0758444000d4840200078109900c15601d500104104041c0c40c40d6521004100c62030914480000114401104100c00103144040307a40c04a142e01817803641c4650010b50140441e20600343c20325149804c50828402c200111750a18041850020180604004c2e07544080207142035a81e10408164080c600783c8003502d100b08a00c445050340302c1c40303006651080d2641e4440e1390b074104080003132107a003070700c0328071041c0f1028814003180549aa02c01d440c180c101c030044030140915280d112050741e41e4203a0f030400420034440c1c0340303041c0e0085075100301 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 591633012 1250 591631762 591631811
    0x81f08030c070f06050f0a0201180f0203010c0c2001030f05151f022d01090308070f080402030d031e0c091d04120813060f0501170706020606060a050d 66
    0x260307aa0b45a81e003034400c60402ca5400703950040f40042c00450714a884100190000c654644004078144441e100c6e5101258035a01056680007540c640c003400f1360500b40a0341495131070514041010710110344603599142d0801030446180c0ea0700350000b54850b8400d40221684550400781001141003a440340f40b00e04160000d0103005060181216020040034800c40748500c00c9500500003020704050048103880ca080420014041040031403030b0040000d11032890391074840e4850680b00c0c1411030707001d070818000d850704004004201e0704101c01a1004100070064110a050210f030900610100c1c80d0114400062003d1092910300807501c0964405010b1086483e400002461102410201524a0022100504140c62072040320060501c505031981d400650442c140c000901c09980380015213896a043e00c080305c0e21354005010305480c800714020008100c00081c080685030410181d00c1d03010051844d031160310045041081140540e08a400320396030110308000d40304030015542c100014008 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 591634262 1250 591633012 591633037
    0xe0c03060f1c080d0e070b160b100b0c0d03060f0501120203040c120b04060c05190c150f150f0f0b090103090804061d010f0c0209040503040806090303150102061501081f0803 76
    0x47d945101c00d04840559020440c40c003c0803003151260301c1c60300c6000e40081c1c10040580400148500850042c008684072840036020411000000405442c42e98115a1200140500802241c0c0c2c1054490f001227410020250b00caa403135040520291800d45e22040580783d104850800300b00440d2800d6100d01d20800e02080481c900c20300807551406171007072480f04824000321422032a03005110142c801845241850a01c4540c145803c043d14008601c18921545865580c41d1502c480030145001e001003a0000900c3c40c1b800840c8101c00304544903e0925200c0041d25001a902c40c0e004200e100703800c4211150b8855440300024003030540d07400112040c44025040103000c3d8860707641c21048542030755811b40410340340d800304030521030041c0045886102c10440001c02c00c02c1800107a00c1808588003543c0c80386440101d0f50611320030000c0c00303030454000f0010002100d00040031528651003c0c0780080480e520800498035403140042070b8002512884030015103140000300512800c036400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 591635512 1250 591634262 591634273
    0x11e03021927050109060e272a060a020304170307060903170a140c1b0d18061425050109081c0501050603040b0403020313060503010e0c03060f1c080d0e 67
    0x9038031171000c465160107000402515080400c058051030100f080d100343c41404032204000200c00044c0c03500e0180c02c82c1100c1c1103613a1748c0c608010221000304111300d01d800d03160b9a1820400c008000d49a01c43c80c0140e000da00c0d83e122030700816560800646000b55480a8100b162881c0303424080c1c100d031903c40011411070306200c0002c41c030380d01e680100c0b042036100000103c0340c1d84948039a03603210f410224003c83e20059131120250042010400881c071034029840b0000700142d030015618501200d40c0100080c41485089021005841000c940c0341580354004800c84801c0601080c00e20240d400003e80150700b442414414403070034400504400200044412160a5506c9500141c94091007000d5102c00d0910000700454003044025922501c40d00c182c0303141c48070620280000350300070f030054400108084014842e204c250705410b6000a280c030b011a0440c50000c0006a152030481ca810b0b008090f02a001e035104d086403101d640c03655038403401752500d0b200c40160030402460110396050461082 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 591636762 1250 591635512 591635519
    0x30b0105041e0c020a0611070209060303030915070e03030a08160201141504060e0c090103050c2d040810090215030106091a1201030b0609011e030219270501 69
    0x10344201c0c81101003400002e015090b064914100a0103140f84010940c01040b042c400060028400c40d1044c45030142100c1c0c07203040341d00505c0b040c148010b000502951040040c06806017001801d03807450030f540320030389008ae0744000c021141c580c03424119903054800031615101e0a500000045d105d24030003404800f0000d201c3c0012800c0c0d40000702d90381344410841c030200f600b590845a490311001e50103840803c10360b82d182191040c11904072840b820040b0040780c01d103120b6a150103029003001c1e50380d900302d040c0714119002c103550f00d9000c405001440e02c1c0800c0d1501c14542c080a07200101070700e0094070440401c2c1410313503000d03001c61002244100c0e900314107000544040020f890581c1c11540e03031400f03818140b07092001c0c4000000380c44407040c481440103007203420007401c0b40c0740a544a4060000d4909000043c40004103040e0802144200e500d03128802c0d00c49082041822a60120350700303442d42c031074424a40c40c1c0b4041038000e9110902444002d00713100d00c0d0039072840c551086c28081089940c0e41c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 591638012 1250 591636762 591636769
    0x5041a1e0607080c0c0619180f0e130510060302030c040923030403020603130b161b0f0605010807061e020d031109092505030f18210301030b0105 64
    0xa418403032a40c032820512005020074810741c06030000c4c0300c0800440380e001c03100c07000090261b003001b05810381c00d0151182c580d1004d40d001c0401c0104001d0043c45c1c0404500b04036000340180c00d00d000320400e0980e0300d400240c11005000550b210b040d00002619040000945038001400c00d5001c141d009101c1ca06503040a401c1600c1011005900071064403203400110707000c0356080b40ea81c5ea580d41c0610051002201580e01e0400450058801801d0f4480200b40c6180101d1900001440d8900c001c600c4008403140a030000c0b03228501003441c000403041c90f0480c0c07901e20101851064003500700380c544400400c409100003409015160152038201261602e81880c03049800c1040740c0c00b0050704203d09150352503009801c4000070060350300c1c0d5281030000d844045034007440210384203074220030046108050300e0452682c0100f80c1925180142c0340d450012100340200d50054282048188030154916001c04184540c000301207804d800611a1048000c1c030042c01d4100b800182ca0382d5414100001e820b28 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 591639262 1250 591638012 591638059
    0x6010e03150601030504080d0f0219021b01050f1b01060503250e0c0f03070207031407030506040b090102070c140a0e01080d0c03031b030906140c03040f02060405041a 73
    0x10301d85000004955a140c0110003514001d40100c03118002404151203503030711405029540741001c0c0e40140c540400100e504200d40c400d42440055400100b410351a0450020310701428030300070300705030345d0301c04c00013a080c00313940301310442800c4115110701c40064044c010740080341150400c0f812988001d81d01c41c5413408001c4c0b001040784030009000e004101c444401c10300c0e03c2c0c0c00095030039100d05050580247c03001c542c1c011207800e030060300107980034820000d11084032210881403000402c14075095a58081d0741c0c80e0042d1024100a00711400a84050402d40488400d01e6000c3e600d1068140e41d10300c2c000b006031701030030383d64494100300402085540d803004c1214101d80d5204000e10709081c0e1040300365041480d280d4280e007050340300c98850034030f00b20201c10300c0c44250907698005010141d03402e101080710403021000031617a42d800c040c460140e00601c140c0e030700550230101c07a20385100382d440015058841c46c1e00c140d41140c201440460a5076026000301c103044000e031145207441508201c0e80c0046c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 591640512 1250 591639262 591639283
    0xf15010e071716020a02060c0c01140c0705150f0403030f1d010903030503090f07081f0b010509060a020106090510082b030c1412160903050c09060d140606010e03 71
    0x32001e10006420360f10003403400a039460450050f1840150b154000c1801d0742d0295203048041c0e072143d0761154855030310420150781075040000781400c0c2001c1a090302e88440039445010f202c2c40c03102c00511342d080c80c060102c411140b604030b41035603126503925010f8051071150000c140410b00b1140b0b00020040341c80050959048140e40703c240550860341e00781c1300c0390009011400399200b03541041082c40f404020300c2002d411482c0044c0110807136051000c44a201400c10900d450f81405101038041c0d80100954459000440f0b02940707a48107014101d00500b0346500184031141804184000003449600e080d080e290710005445595480d08010826200050b80f4220204100310360717034061b14800d6000b00707945001346c40c203100711200c4810f250f82d440c0c000c84806e85007160307420148000c03140030001030040801581001f0751418510748440d0303200d80080c2d52503809003110700300096180d61001030040210b940f0240c07100041d1056042581e46440c2140c0341404900a0b80303100d0010704c2c000407102a207 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 591641762 1250 591640512 591640547
    0x204031109220807060b040606080118020702030c1210020a080a0b09090615040209040504050d03060518190608061f0503030414040b030a0b0a0207030e1804030e01020f15010e07 78
    0x51010581c0c0c3c003070f110350200f00c050398025500c10382250f099845005100051000340c0e0f410700341c1c0d41840b0030000809400c034078101401e40b0401c41c1d400140c0340421501520b11044070840601040e05c0710841c18038610900c20010a8030005061007202d8111050300d005030540d200c1081040191014840000300555404000b41d1150000448003000030003e4102c004000c1d0001d401c0ca001c500108081c0ca200b0790781101c0d41d13040130005040d07069040c8900710003800f08442c01c4016115a4038040300741c40d40030703001d02c01d1138544140700901107002d90401001440c9039800c94420b403030203250f401000212091400ca088000060004951600100740d40c02c0c0c0d118462568072550700300b4100001019901281034040c059000701d5408600c0d2040002d10030f1225040260ba00c404070302d401048140030070100f83c03080d03030743c01c1e4101c0504520003603207688681e01d400d001d4003650720040180c0c640641000801c8642c440d406045c240f802180b00d1840c101c4030f400018030b1117600c4080b01030302d0742d40e02c8034140c450 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 591643012 1250 591641762 591641821
    0xc010804030e0904150c05040509060303090d0f02041d0c010f0212180310140f070801060f0507170c010213050a140132030402030c10020d0e010207090204031109 71
    0x3507031426030f01a80e00188210040030056103200d8030901640c40c1043c0d00004654049820842c0e0b040c503080c1241d0014040b005149031081300c00000d081c1030800b10b0090042c140c1090780004540715a40614010400c01040501440251400d143d0f00ea13034944616000507080384206042500009001a4030450020310f241401000628481c800e12080ca240e9450300c282c4d005280141e102d8428070100e62414502c02c100ca1501c0c0c4100008081d01038000c004104000004201050340308940c414205050701c0e101c1da480181c1d04180c1c000b0034071400d107841801d50004807940404015030080aa0880e8050005055a925010401c103e9098031810405100d0140d0900c00d940c4601100761492407181440884460100e0903010104808000c1c068440000010302003586420008c96a0085007114030410384854108007d4507150010104400e05c0b840f6042023025a00038060880a05000ca404545039640c908040325620f6031307407040e45e010307415060202e80100309070a042d44014424000d4440d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 591644262 1250 591643012 591643037
    0x8011202040f0507080106090602070e0f25020303070207090501030203071715010308040f052403100305150a0c020d050406050a030b1e04060506090a09050402061201030609050c01080403 82
    0x1940218456089038465a07802c9401031280e103c1c41a18090340c01943d48081c1c03581070100192003010290050b100355804040100300d40090081c42d941c0c0847d010715031100039218101603104215004407007201a807004500c80001d964008040c501c03403074060303003100c00384c2e940c413aa0788084850030700000c1d415402106080c40030010b040c07107403841308200104442c1d0640c0340c40b06808800e5030a03001210725590000d02002900080d101400103050100c03140d00b11800380c14082000100c801c50b051f002103c010002840090107240180019a000720568807a00c0c2c0e41c03100116800300c201c83e40d002d00d5103001c0f00b400901e88000f440f0491600070703840300e03441c0509028041d10540c00c10480c0c04201611a01c1e031801503103551903492001a2a02c0d00d80c0c080c090303818200701c250ba0341d580185005001c18000214969100540002250042000002d5a403541c2c00443e82a2092804100140c45000000402c02c01c4036881004a180184140e41545c0c4417540110790704401900c010b0f000400c3c180710341 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 591645512 1250 591644262 591644279
    0xe0a0f0c09110909130219090c03020306010f0e060c0102040609090e030405100c1e0615080316020402031911131203050406030e1c050c010609090503070f060906020d0c0e010806010801 81
    0x15500942d00d400504000b4400da400500c10664401f401d50070300c5c000c40b004010002490203030328180681801d00b9421850134400007464544c455403200201b10400c290f181441e19240b0445150541000c005e5503035a803500c2001c0e080d80030318442c89404a1a001002510354004800d46041c0c0d0b00090240e5001100924111101c0c1051101501c5101c001903034400c003c3e01251301c691486200b0040483d00e080481403191000742d0591203101d294204000d400c03240e07107410722803004081d411200140c49484076441c150004c9100913440409616014240514142c9000034240d001c0c920240d0380c4c961600d9842d00c5003e4410b000004020520a002c280000b5000381c10017024400d0300c50485d2402226408003040b02001c1a0441c0c4c041030300080d2881c03102d042809030340b000c3c0c1000d050500c11005140d60300356891080303200c00390400c1c0005400d042046440c0d0411021540c200400395114008820b80c400100380f8204140c02041550700181802d5000c0c0000038070500d416119004543c1c030f040004d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 591646762 1250 591645512 591645529
    0x60106200f0307061d0c010807120209040204080307023105280209040e030316030e07090e03031512060a020c0c130603120215070e040e0a0f0c091109 66
    0x1940c0340070702114404590001c202415125008003000300d030400d001952840c044800c08003141c225000200c1c011203a90300851115000303042d030305d421100c2410344038101000b8081c141c038181e030045c00004d00042c011400005411414000ca481c01134514280c078043c0700c01c0146a0390f5444120b140c0020703a810080c5a4049036000318107031441000047c105880c0350b046000b15004074040345d800b20f00d820242c207241c461500c040d0418401140b9605106000342a00981c00c0c01e808105600c1710700c0d01441040c103010780001031088038828030020128001d00c07900c07034004455610204410740950b205920b0000e4401c48080e10701d001600580d1a01e52840012358008a105002881400d80689642e01c8040c4030340c0c00c60122600001c0c0c55400d40c0362240c030305035800c0c044100b10f61114021400c981c0504240301c3d00000d00742005d17206440f417140410041c1c1742d0b6000480700c13800380d071203608107001e02d81c01e001071200d00c203a0f6905401364880e81840308035506000005848041404588000d0608040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 591648012 1250 591646762 591646817
    0xe010510022116050102030f0a0e0a051b010e0909031206010302090d0224070804030b1815040201020c040516030c0906050a030213260f0a0b0c03100b0307091403060106 74
    0x109502c03c00c4880e21640d0036030f8400d170307008a03c7e121203404004454603944180c100044c2c1400181000c40d001c0c1e11000da440004c071203c100702c5504d0001c000c0381680212241c680c02200640b080380031b46015400c6c0c540307a42081c4140c1b00300c500c0f581c0c00520103610be482241c1d1303450002405150400015028440700b014040c1483da014602c0c0020900c41d004040090207940b4460b000643d5224250b2505591202d03010700001c00c503242c2d00d0600e00300c602010600d00b101d4000c00309203051564030303400101d113040c0045126030b801514100502c403000001c86440c400d020030580f81400500710042c0100c13408190344c452040019014007070b0b0a034092094008000010300c0071101c505440c5c81c0c400c0c07415124403409004104400c0700404904451040c000b841c08104c542001d88a010000d88613881007400003011a005224004001083c1e0348910450f00007600c05c03010280d0b26454003402c007078003c0040b4001c0607503803000d004006840d07150019905060300c40f1030781c550076590b102e2520b810042d86c44a2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 591649262 1250 591648012 591648037
    0xd03050c070e18240f1e070339120b10030501060212040b070209060d0b0f150901140d03050403140d03060b093001060e0105100221 58
    0x110700048044440c5200d80c020050b509000f2440286926801d01d4541e0b0b02101c011400305044e1030454018071901600e60010300c415038200156542c980c4005c68410005480044480000170b000c1107546c0b50b0302188081404040025546007054000240c1d100f8130045034062041c1c1140701400c3e42d100e10784c100c28400741d200f800300b41e81412000051505001c100c90348002a5074000400405504101c404030000c403104c2c6080c23801e41001d611200a1155081c068020f845500215009844036900c1401d40d982080780005a400c03c070700840c20402090b1010038503080544485021031901d21f20b0f03035048030b030402c59944104d410101071021410740c00c082034080c07000a00c000400702d00c00f6581c0507a00e6440798090a00400400d601804491084d0040c0405503403d02003800c09032150a610b010410f5400e400c020142d44174074040c903101e190b501240980b075003032060002d289521270303501038180d6408403403074498030a801c101203a075a5032220b8840365070b1200502604103140c4d040005c1c030300905280e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 591650512 1250 591649262 591649273
    0xd12020f0303040807110109030507050405041e0506010807170a02120c090705120109110307031e020c100506040903020a030c0c0e010e06130b03070303030218120607030c020c0d03050c 81
    0xa0101030708580080b101507401603800140e51040100c000d100858002d800d08040b40e0403410f5844036999010380b4026280580c0d0340b1804102402130288401c01114541c0e0f0740c205550010b441e006c1d8031900d0030312420069104981c00490048a40740308101c80052031801800703508190307002c106540d02503900c1000c0c00e00885100c100e45072120524680f0403880c1d511041d0f030300d00d0950a04640068164814032904d86894680701c5410104402c0f2078200d9140d16003c5001f0000b0156031100044144103e04400d100282e0002c2000380491a10402c4030300c6c0c0070030004e55480030180300641e40c45540090043e040310210400080c000c0b4000d102c81070041507401c2c0700a489800402c03080400fa00300b603034010780c4001040340600c0c061400900803800a1821300686900402003541d8000c103000090034944c0100c3c0340c52061524000400380520000c20640040c80300300c02241c0c45400c02d07075080700081c1c00d0003c50100140000365003241c8440107032440030b400005813001c58070750700009801c0b451400780 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 591651762 1250 591650512 591650533
    0x9040914030a1d1c030e0406050303040909171206060a0203130f030b09010e1b01030906050a02070c29030c09120f250909021903110901090504020d1202 67
    0xc01c05482142d0258450082941000681c0c54000700098003061003124010300104089502e01c0366407001a505052040c1340c401808005005040d4030707080300350140701c0803030700081c00d1140d50000e05c00c0c1c074090f051039201140b03070084041452045020810035000c48a01090341c80c10030340b00504901c0481d1040c1c034204821700341c008004814661107001c030107814040a01c14010007100c1640c1104001000b00a12044070b50b6003038860310801014221850781a0752141664003a81048803507030f41c0418100064540030042c030000350000721003507500619805000c10305104407110300a81c1d000d1540c0740d0411100b018a0000300380c2c001401d159000c2c0c42440301c0000c0c0c3d00c2e10f07250440180000e01c090b02134003455107582c1e41341801c5c07181c0f125151700c5100e103203407007000d500e842c06010b481c00c0c0032012401040c540045204503603030403c0341381c051500480c0013091182c1d802011180e003004542125890741c1c1c1c3d003050000c0d40c1003a20040d43c0b0801000c1010005407040f6038803080c04c042130060342c0420700c9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 591653012 1250 591651762 591651803
    0x70602040801020415052a25061814132c191a04080c0f010b1005071e05010e10020306030d0c0804030f0c0b070f020411090105090409 59
    0x1903401070400380c3d000300303091040002c4042c2d0500e64082924041d401c0c0b07070341075102540454044610701198402c50001c05401e02d001d1142e041c515101c3c80c44002240c0010312202c540503035a00c140000581c600029850b00030848101104455a1441c00d50341a05404100900340c00c2c8850b41c00c3c1c9480c0e854455080054142540c0d043e41c407059119201288207070b0b0750807400c10f00501500c90002c100c40c05400005a10740c011904441140c4000038025681c0d45850486403060401e032003000d11030990400310301881500b11001c0c1e80b0b000e4071101e1f00d6101115055505005e0b9010043c000c10320016005180d2905642050307a140c00f0b40000300d0405001040c40d41840000b03042481d415070000304124160404008501030b103107503441d12031b520481a4850360414002c0c4c3c080207299071a520022030034402e294128401815151a905a48440d180340603403007401c0c00b01c000ca0050b800c007400c134085c0c0c058090640e001e002060f100c051402c5141c0b410400140062081154164403801c0c00740300045 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 591654262 1250 591653012 591653017
    0x70311071a060307270509030903070e04030f0201051504200f09011116031e120909050a05011a0a020106030c1d09010c020307060203090a12080106030c020a080f03060303070602 78
    0x688110900c051410084185804e00e8080d811020541c616180303210424882c91800c0d00c3c02d800382040000b900e4070f44866517825441006444c6900d8869480c000c43c2428140c425107004130700c41e8541c800b0403d5820400da0984004844120100328559044038490500f60421240c0244d002d04002e5090f0f2070b0300c80c900703160300246451000042e010440d106d10307513040003803404c0000000c40202103501d44000c9420300310f10716000040480c4001006400070040f440303206a0484d0340280c00d500c44443c050030050903208c1c40c0c89000b4505050401040c0080040e100302e606030f40301c8403603403040e08000751107107081ca501003508242159680c840000c0821081a42c0c0380241070310828a40000e04803c03e02c4580a1020b4030108940e40b614000004854000045607000380d03000e00c016071255289001d140c2040d9103601d019040d64001e60001d050168004802810b039000364400b00585600d1580c203e0b42c42c04210300040032960704000c000801e0090308085c50344440020126032803c10f6a9480105a8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 591655512 1250 591654262 591654293
    0x1206060801180e030901030914010603110108070f02060c090117090309100801060503010618050402212413110d0b01020c04050606030a0507020f031303260307031107 73
    0x80c0e02480140218814400c1100e1808800c40342803120001108045450748038095060381815560f0300380031304010030700780d0740d89401000000801c90f00707075681003640c441e0784030300440b60008000100103503e07240100c80c26000040b540d0f0081c81e403590743c0c02c0003201d5684040101d605102920014a1030075130152a50740c0710f0201c1030041c6880380c030098140b00d07070800030000a20500601c000148001503016050307a044543d1850880d0340d002c05400304200160b080d40040b60094000035200c507402d0070491218070b4404444a401602d5951002000d460602d9030b0b0a0030706010403652a04c140d40344c041520911107030070230400114111300c0384a00071603074003400ca05101d05440c1c803500070083d80c0500140402110668044c0894078101c000606a1312000b000b103810184d4450110f014903100f0805c12600d04684011a42e8a186440035004812110710040344c001d6904100321480c0c00b18010840040d503901342949042d03845111050303001e07002080d00c041d4010400d000304c401051181c145400c40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 591656762 1250 591655512 591655517
    0x1206070c02010e0415080d03020c0d052107200d050d0e07080f070608010807052b0b072307080f07030e09010b030916030309180605130506010f0c03020a020907120606 73
    0x1058030b40031b2410b0800c1102015081410300c1404000314501d00840c800c010320b030043c50044e69801c04c00030000c07150306250554010f091034802c10041850380121500303010581813000b2200700241020035550392200f00140400003601030004da020f41000b0f800003d5440208002d540c160313038880000380d2910343d40010782d80e0075500040c2c0800945801003409405000074001402d40305040001040d03149072661144840506178044503000d201c5012500d00c0b00f581c1c00558108030b030030290313030042601590405100c40d04500352001c20750340c3c48582c2102e440e254441c10f8142451180c1400d00c000781c2064100394140000002c040d48240e03524420b07980030f8051118483e840c0c0c00d2070b40b001e52a00310b00c240d841d90888144041403000c26001034415088909061480d4008803e02c80090042c0c1a154841038000b06004a24a403014613034010521584080e030795078880c1a00d00c00201ea40a0002d9400741c0903810890184001d810921945544640b06081000f094800300c200b00d0116007040c2e004e00c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 591658012 1250 591656762 591656801
    0x20306130311060f04030c03020a12120606110d08090f060f0a0501060305042105250302010b0604030b240904050a05120a2a0c03080a09051206070c02010e04 69
    0x4040d0080c0c405074242a115008203c9440c103034400c2d480c0719801070009030074004540060400c05200b001100d00040d440340412030400804403018018011821600050070700f00400030030310741c1c0b14bd08900e800d0302044e802480240310486090712110409001d86071180202044210040c2d010400c09025049034401480c0601e0030b010310b50100e8006811040c2010b0070170043c8800300c1d8051404000c06850061000b00786405090700b52503902ca0030060504668090749100c00103a030b4421710301c0341107010350001d0040b4000e20741000034501c50740c00010040c607003030400300303003003d2811200f400d00c0c0700c1489200541d0002c032000240b4002040320b0850b0980d015805000c201300f07007800004481c00300302400358104540c035000034021200c14500c0c40492412000035401c6c100284481c0382c40310381c001031004103d50b01c2c0d08019165911090f12a030200c0c411032000a90b03804e248503803800c802e059070068a21500c49000031244036039207803001d9041007600400c041140da22031044118a005103042106d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 591659262 1250 591658012 591658051
    0x20909060f010f030305120703021605060a0c1e260f060a05010504060c0201030e12030412031104150c02010311040b0d06050301050708061507050a03030614030109020604060509040603020306 84
    0x1d540c41c40581095620500307403401000003035045410759000c982c0e000d00440880c1d4900d04214020f011301e071203186010102d200c4900a011022038564051015641c0501020200d0101903e4050018409281d02e500780c4072240b5604d80b107458010503a01145034411804d24112100c0c05451b8001c0da80f02841c40800307014441d15107080b0345440300a10080c03c0c554106442e280000c3c1420803010406414140c4884000e0340c00c00043c085583c8000c252840b254990505080c10b40690643d0020344000c2403030801241c0800c0e410f00103030f90440781081001e00009a042608581007402104c0881c145a15112040700c2c404040014101800342880102e440300000c0c1d414a05441490744003a000703901d040c041c0002580e100110b254003820940e50941100070340c6603520f034540b245c80000344ca40e00902c0c4082040642c142c20140c1200c40c481c0000305100c41c40400c150803200090700c000c0d80214100410406140503038040d10641900410008a9075a00c5d0082030400c4000c59a0640722942c140c4c8e2003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 591660512 1250 591659262 591659281
    0x1804050f010e162718050420030a050d11061005090106120b130e010f110414011101020307030506011115041511120402030706111b0f03010e060906071103220302090906 74
    0x30080303160b91418801807c2540b1010b00340c4031030301007401d4902404030030010a92001c00c1006c611720380c0041150b884e50303184170005140f16810031122049000d0070000c40d516181c0c460901003034540082801000340d03e40042503405242d00c5003401e01c5107807105070320491641c84150040195055010108007400c07144142402c4a15200c404400207240000e04c0e0466580d00e8143d4090703070091b150106c44c00c80e031540142c80010381c580507004598000010080300c1d41d410342181380510340a0700c5840201490201c0c0380d0715980e500300106d0401c2c00c0c42001901094180170340c90710804841c003001440d0074903a07242e81c400d64080c26201c002180030700b081c00210b040400820005028500e0003505041c80444290784800c5001c3c0c00da01c1d180c01440c079000d507a50302c00b00b00307031070404d0010000c0000400c9508519180c001c02c540340c508a00425002544040c0150407066181d8982d5014510340704003034480900501c81d1a000fa034080b280c001c004401078640e085210f0113006118003c2507546490082c9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 591661762 1250 591660512 591660539
    0xc0405010f1214070803030703020702044205060a031e05060a1a0418050a1b020a0311071203020303011406180409030c02061804050f010e1627 63
    0x10084001020008016916100c8010a5103d5000c44001195964071564900d0200b941c1c22800319400008103122100e5015402490501c0c801c5d00c06125420300d4180c06081c03101c00b5a03092200607200394000a040e4034072010018070003070b205800007455071142c0201d0a40e40100640030003195032494000c2e0454075004119198031035440b418440c504c1d241000c2041588948240915082d90120070444801203600741c401a014401540542c0c10402c3c0385da4001e018255000350318545403c00d040c008142507a0011000c0c5400d4000742a00300b200d40e82265456002140c002060160781004900304075018160343c0329a00071f40c011034607541440000300c030038841190660711800d030810003902e05100c7d2480401c0612022038000503c840f19060035101c200316071a00035030040700082e08a43e02c1e2100c801041c0c048100b81c4040000d581c502c91030605909007030281c09403d06004000a41820104620b00000809468401d1110181404d00614602200085050b07580048402e014200b850140e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 591663012 1250 591661762 591661769
    0x5120315100f05070f150b0108100b0403200603070509190308091302160507030c0b0307210e0d1206050603010b030408071a0a0506090903120a0c03020c0f2b02030307031505090403020c040501 84
    0x401601c08bc600420950340d4031461100506009500042d018040001c1508410034a005002d0994031310700200c0041c82c5600000383c01e48a00c0002000701c51032110300d040e01096940c09258540351480d0759042081e22051080341c002034540130000e1904062106511a41d400d100300001d0840c41c1c1107160000b03200c01c40c4c1e00400c554070f9081c4100681a41d00c550a805a07220107201020004a142002c0c005440f1200f5142d00c03500c10f5842e07000301d051b40803e004040d060000c0c0c08001e01074441e0100040741c4400e101d009092070090001c03134046420080100700b580c0c400d64502080f0b9200385000701c2e518a088034204038460303440f4100807043c20005210341d8050301c0c0703e002d18541034281c00c0c2d204104002a06103a2080c2c7c0d61800800040d00039411a14020002d40444940c0400300c04403999070640400644011030380001c03019038003d411146404410302d030760080c500f035940d1b02c10101c0040020048140140905810004a0780c0f10149042c0c0280c0c0258040d20700d440c00303035040c0800d44806a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 591664262 1250 591663012 591663031
    0x6030601050603040f060b010905210d050403080f0c0a2013090b0a150515030105040b03010b060409050c0f030109020c0d08011d0604060305120315100f05070f150b0108 74
    0x10400001882d14040080c4503540301400087c0b90021038012601c00c0001d4200a4201504442810400c1c0d50041d078014050203c0c0100d840303c8400c0142280c040c0035501c002026006d0138040545886094800703400c101c211801110301d40c00050f19101c070051044450300a440710080201b50380ca00384540100700b140c203810f2042c00388107669641c01c2c00317651008000628441d0b41e404143d415001c04000400140b800a1050f15a892400070341d0006a0080c4030f028891232800c40307006468201030080b007001c00c0f001009503082c14940400c080242000520040040c1e404120313040d00141c0000156000c2e00034104016210400301102074544500001800188590f1600400c4800d00354128035420080600360500541c0350640450041c081c25000200540140c86403000790a45407005140710b076200034840d412140080043c00388440d0494024000603500d40c0d034448440740554010804c0e684600321407800c118464907220f9100c0000c4490072045900c41d22400340d1076910500e056040910070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 591665512 1250 591664262 591664267
    0x301020403080d15320a1203050c0f010213140109051e04090c08061b18040902030f151009020c030a0807021011090108011d0103140c0a0e060306010506 67
    0x180c807400c10a00450000c00076098580c413004400001e00d10f0a2001003440c04005202d45c1c0302c903d81d40f00040d801c80301ca48401000350a900b00c0350724000d0900b900701e81d00990700c42c40081c2240ca013240d8036445800d43c0180d51242d0325864081400920050060003184103c6001517810185003d1075100c24901d140d0401c08000400e03c40340c1e0b0b55094003000360441d000c19196980c20038002c0303409410010400707455001042c1001548201c0410024880c41e80c4e810700c0f4000c4600b442c0c8212060281190b10800705800055410841c14141e00004180303000900b11803899501c44986031800170910100c0501071613503001c1c8603107031a0310307624903014281142081d41082c0c03000302c0031580c9000e0800c402e403c010004000c83c0d10340b40280b20004110b0303d02207003844142c15440b00300718103502100d4500e0016600700000108014400c0d1519481c45090012800f164a16110b04075007000303800807213900703004507500c0f110242e4403a502e860040200e03001d42482032030440c08041c10848140c2c8058005d0508 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 591666762 1250 591665512 591665519
    0x301031203051509100e0a0c031803020304051c05011b0834090305150610030218010f120c0905040f0506030a03030510090231060504030201110f0105131103010204 72
    0x200152403e014059518000783c0c1d0740c040c050309402c0455444039028120450501201c0011504840310102c00343d00d0901c040000340e181c12030ba40d49003400240c0180c0003840213020905c0c000c0c400c40c00303c1d50310b02074240160700c9030b86400b421a42c01011109200c40c000c0360b01415141c1100500d80c0c030000e00b10040f0020003110710144154895420003030034988181620a507807c0c060a464005941c1100840383c0354000f180da1040040001d071649131245200260421100340329008442c3c02842401d10090780c64140f50040d540110246111804d2221101404030050b013035100d00c8400304e25584e1b460714011314060074001180c44031055103000606110810085440010700805010f502d0300d00019581d0b510101070050300015040155841d0001480b451709400520031103100b4010303607180083c0e1084580383e07505582c0039442520042241030104102641c064440600d804800d401541d14450240803040d0855108580141c4400303c002c411800b40400d0000c00c5403040e00960086203030906 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 591668012 1250 591666762 591666781
    0x8041e24150e0610110a05010e0307151505130b04020a020d0801121109070c0512071e0c0911040314151506092b060b030d03051302011b1403030103120305 68
    0x740c49124060205e020703151280c0b0704040104490480d088002041b034070500141c203907143e500155007500c4114101c0d61004e2384a40034803e407000700c060620b19040d0f541c5403d0600405281603070050139400d03030b6480c030414640c503140002c3c0104484d0b40e016006524010401030103402c0182c10071104070304180580000030720010440b1a508900725124602c5517140301080392141169000200540100c000000c03d2624090160100f82e100da2282400e901e5402d01d001d4020f845007101402088407081c08000810a076031002d920728103a4440300789800d440341c8600b10580603103010002141e01440c0c49520042c060a4801e0304000c0b0741e110a82d000803248005500e901030b4020240c440c0081003100c5540b00b03000d09810b03100401404190008000e0740c100040105101700c92103001340030350320780565070b14420304c01c01d48110070445040e0071004180d0011113104400007034008541d402d50079524049040394000200b00700b007080085560f903055180040c9040c0c0f00015010905040406201540b034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 591669262 1250 591668012 591668029
    0xa030c0e090907540606090f1203080f130605040b0a0b090f010303122a09150c0602070203030c0708100f09030c0f062d0c08041e24150e06 61
    0x5420101c40810442c1131400125400c0104c00000d894030702540002d0413600b003091142143c22900001c081d490342d40c00070080c4c00c0c90802e4000c000850743c00001c2d019540d48212950045038101030005030149039a104002c0714019901501d03100c405104002020900b17010315842c02000b940c09031340d07500307100400b004203071410700005081c403805141501081123240d00414202c0001c0d0191842a030066101e5008240b081c40c0d1403002841409010409900003042e414030f02c0e0080d40c0b404070079580d80d00d400c402504080e8080780d2500003002072a014130401c20030a0098100c040c098448901281128022a403000907210846c0e8144030411011903005118a0503154110800206020291500c0704c0203140d030500fa42020f1a000e40180d080c045645e148440c45080c02000700001301c0d0840c4142c9030a13004550080541e031616880e810344003024440402e249206a20400c01000380d030044403c810010017031241c001e540c0300d29040018007164180340003401a115101041d06101c8042900348 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 591670512 1250 591669262 591669359
    0x20a0507230a060902030c063c0a0302030a06051f230403030509032d10050108031c0b13051504050108121608030405070e070302040602030a030c0e090907 68
    0x216130b2020120f040d500c0511914980000007008030b030761454580b554100c0280c039140c4d00101303a00310011161180300c818250145206070031120a042034000041180030303501c02072000c2599070301d030746000031030791a690402d13490302400741c4104103020b4000308014403c1c0d030014000622064144104020a40040102d07016203406107070003035035544000042807400000f00a20403d65445c02c262008512035490f00d01d00ca16020f4055414030030303004070482c00780c0f0340a01542c1d040360010002c7d10398080030000e09142c41d40d8a600081038130480c500002da041c0c0c50a00130b5500043c0c03141c041141860600c0201c4503120030441b0100160750401d0b1006a40d4003104c205410507803800a1a210400501a0000d00d05a0b200c43c0b1aa5240fa20345842d0b629030940e48641540084010003040c2d08138080e00a440c184c03451a0700541c1055071b815412000f40400c00c12540a201300d80418011940301c0c40c45c540d1084e202e41008111592401c0b40c550316038403041e40c10002d4081c10418000b0744080034100749815 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 591671762 1250 591670512 591670523
    0x9020d030c0201030209030a080a140702030c01052d040603111806030901020d06080f06060d0819112a0607030507110402040519050a1203021005090709020a0507230a 73
    0x1180782880140c00034402d2080c3c803503040c442c00000c8020000140000c2c00004640e0b9510440000c1070854501c041c0a030080081d8103030070070088440300d944100040c0c8280c0100360300d0243d0485000e2840304a1072030701c0811071400b8000040511a1035014001e5180075100c0100035403a14044001c1c1030f806401e4060141c1c8141000000314600440c01d40507200e65000040041101079034810103181c1d614801c125010b0329010f020002800361415591040b07034550072945151034101040842e4135485d01c0c3d10081d2040c0301c4c0142281429443c00c018542006400260300919031042c00250b070301d40b0400c900c0c0c40d48111004c12458000039404800d80b030615500c00510001d4800840c0001c0180c010364105a40094600c1c0b010300340715070240000000ca41c0140c491200040e00c84038999005d1070b903090042e000d6400078010b0300c034220155201541c080f9400c01500c0ca469107c00500d000c7c0d0744205a0040000c0300428841c090052011903880b00c411140214020309102200aa0712640086406400c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 591673012 1250 591671762 591671777
    0x10305060c211902120103020a05040c081518130b01090605060a0e0303041509150302030f0f10080709020a090503011829040b09010e0a0309090e0f070b09031009020d03 74
    0x20301101c9150b09298681803d64155101c4040d030408204190b02480241e00c500080780c2d000130700d400c0034411000840c1c6a03070744410041d03403001341644001c6d20300d446544c2c20400342c5d18111444100d452440b40151b00441c03050480d5003e5090070340b09540180c0120001601d8880c2c108900d980700320450354103554505042a41c40c0c40c120009003036002d1544501052210038201c164001d50008091040d01c0020341480c4558403140070480c124002203610001481d90000402c8691201810040d40b210900194101c2070380c81c3d11708642002c100340c1c030901006801080d201c3d01150086416400340030305074000c100c80c0408c0d4907903810030410100c002c0c00e00e00102440c01001001202c08107032072500031048620174100303440d201010361400c0300d000d8041d52070482c00e0740f064a404a0094006a007650381e6103a064204a202001001802450600d034402d2104a00e03100307409001010080c00825034141d220000c50b0705160401244c40c07056400b00d460114907200503070b11941c444c61039a07018900b059 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 591674262 1250 591673012 591673021
    0x100e0f1203040e0901050403180f05010804061b030203060301230705070813030804051305041109060102211210030c030605060d0501020d0506040b12030f0309150906010305060c21 79
    0x707003544115040043c001c071509080051207a0150441c60260b886a0781d242c505014151b60813107508070754041c03030015505180c1c04118940c8201a5541c000340282000103030381c12402d503158001118042000d0102c1e80102c1007181601d421310031490902e400d10000d2240c403001451040321450010051401d001c40810700d1024091908180c0c0c1101142a445140f15a264100609550018400c81c1c0c8100340c1c101240b880a50140102401036902410505020048108001d80ea0700020503941c110310484a60200714820824499880c10243d2000c6503a0261300c07501c0034441d0340c002c01d002d1180401c0e031010000100c00e030380c20b50200ca0b0413a00018164680500154501c80c0e60880a00303198000b14082c51030f0380480e8001030103440c00316400c1103582408c0003031107081c440c120200022038200b400401000d28100f002560701606100940d030014002d15044454000142c034419000d502000050040020800400341c108081c4440c03141490740034120f650130400075540c0c078281e844000000c035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 591675512 1250 591674262 591674299
    0x20f160f0c060804060518100f0b0303070803010915150509010e090a0218030607050403080304080d09140d0305130f150c030e01110a0c03080c09090103060b100e0f 72
    0xc00c100c60340200106803140d030341d40c001050088244e0742640d4240c40d08002c1884620441c0c0040480070080015191852180320b42c0c90050511b6100446240d888829034a91541c0a1004003030071881a699a81c0342e50602c0403200448428204025000c0c1d10307030b0410702a5000e106d000c800c121590346403030f0b40e03150520300048606036002440650460075202c10f008407007030346030060903101c0001c5180c01000c40c0e05d0810103079111000d551000121b04204000e2001c100740800659001c2c1c010a4071918015440d0340707400803289288010344022082806000d0b454205000a1030144c000385402d0141d8100141004885209040300402a03007500007220108038401c00c520340d444c03100410400c0f035007a80407000740c040d080e0600c0000140d481c1052460550140700c0c240d0341544940d80d20b05680e036030b103907500340e42849016062900c0395105200400f41940c2d0307002468080c6108020102d800d200d40707428000d050201410b602c00b032185501c240c2c281034071201c43e03913001d0000464805180e1101608036 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 591676762 1250 591675512 591675533
    0x1060f0f17100c11060601080402060d021b0307110123040b16020301140912070b28180b07031803030b010c02030f0f070e0f07051e0712080109020f16 66
    0x2c0d039195508024812120a8002e2040c010500078101550360554404004544510040754001c2d8085c0b018003000761030084660151003400a08230260050f800c1c00900b181c40c6400810044420b086003104079840340d40e018101c2000c2c500e941221420085520b1403401084c0036078011403482c640d010450711102211399101c80e00003034003c1c0007042034041940320404070705802c0702e035010144901c000781b0412580d000d007280c01ea5604107544500b103032141010038112070380e9064000351504803650462a410400d1240e01c5040308088940884c0700524640848250740c010500c00900d807034007015401c2c20380c0d03507184040400d503d40b500180c6190034400681d001a04464040d400d4070038028904103d40c400140900030b0b41e6030b40101d80b03d0594820b08401a04811510204240c3c009004212120f0085000e1300303203103244082c001224119864410180c0d00504425614400fa5084400c0502c1e04000c00a0140030803c800703600d456600140c200d00c40c411000c1405500b076802e1407032010b00003941c51 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 591678012 1250 591676762 591676783
    0x1713120218180105010609030b060906010c0c0608040c0911070b0c041a030603210a08070e09040302060601180b180d05120a020d08012312190501060f0f17 68
    0x44075030780e0341444500082e515103a400400100d6190100200d01940a21001c00c1180d078071000c0c408403569114144108a60003510350f50602a480c0004400285155447e0300502420b03900d00349186024242890444032907172010040d10301d815022030360a00c00004417140b41e40c006004440304d1f02c581045051034801e6501421011042d91254201c181d90b80c0c0045014201c1201114000100c1000d41d0140100e04113003608210f8007042002171300c43c09411415070040040c02d1081c00b10401101003030100d0401c4804070b00603002136003088059131300303c46a01072002d95602c40814150400f546042d441c404c2404048002d000c06586041030b6a0f003240d40600305500405507403100c1c0d481040445070790070518032000503010341040140700300c1c428018035040b5200c1b1801d02e0000c41c03005000c2080070800c1c0c510702d40c02c9408614501d0700c1c0307070040085154510320f0240c0054001e9807800c12030f003120301603000036261105107042003001c1000c1c40c0c224010b50b90b00b10242038042c040d042060b0702e090045c08 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 591679262 1250 591678012 591678049
    0x90b03010b0c0705120708101116050a0609080c010e2a03011d01050f070c02030d030e01090506090d020c0604030809090606070c0807030b090f0723120303010317131202 74
    0x91120000060210b1b2210890b211002100c044d084000c0a4409a0b84081c00c1c01481a2090150b0689542c440ca4811201d6000300240c42006103941c85040995800840c184c94401000408550703008007480740d40c2c110355410026000108140320b03120400103400c44140301e8282d400c1d008151941c0d00b0b40c416143d86005400c43d045901011148034080d01003221409d030882c4040001847c4580643c0c0080b802c51340c0100580200d01025500350020041002400115944d5855080001e201001282c0c00703003030004014048140103001c0249440c421401c2d0900504042c0420800201081c0a03900c1000e402c440109070340d034401c1d012401c5801110030180c44080f1030400011291400718003001a00e0080381d2007005a81c407003101c0380d81c5005d44c201c90546584a810100103580f0000310b205403440303003c0800d8516440c08000aa00400301c0444d00c2140d800000c01002044921f035000410904055030381c0d410912081c85402981c08984107480079504200d004004660764480c0c002c02140103007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 591680512 1250 591679262 591679279
    0x506030c0f150424050c070902030c160c0806060111210c15150402160f020118080321071d06120c1b010209061c060b03190606090b03010b0c0705 64
    0x361950031004d8161080c19004030511050380000d00e104c2e01c100e03510f8843c803d00400c50545001c00d6140290300c000c0c202c0001520500c2440c1e81d48056012140c001070103a8a00d4500750704000c1c0450074030401812680c148030301c1d54610704e58903001140302c842003d004040740d100b00e08425900c514500c42d00e118003095000b081c5c101624a0101c1480c02d001e65a40c518081e44c80c6203450520040707102d500c200822802e0180303035210015600b00a0f1401d0244180b40803040c0b12601254040481d2a9400003a079503040820052000211140c40041821082040401d903050000c00900014035101745560a80084070044042e03031540c0c0100e52440f0178a070025101c9103018080c48420b90010803954000c8090303140b140030146c0c0c05003b030318a0100002d00e100c0c94000d15403036040b441d07005001d5820174079840308030014004203040050762103203200d1b04c3c1000e408000c48146004071003003a0031800900c02034000038000c0c10b9004c02920305552070a9112955501603283c0c003440c002c100da0002d54001c0e44c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 591681762 1250 591680512 591680519
    0x30c040504032006040c030b10050406061706061e311d090712050708070e010e180613060b04050c0a110102092b0f0f1101030506030c0f1504 62
    0x100d01c18109961030702107001e000680b00300440d0b0302c410b41510060041b0500000c144007045070036596a03003080d011070540b50b803281d03103401007410f403040e03540304d81d02140b801d640360840101c0c14058940e10001c01c458180c506502c0340c550414048071180d2081c1c80e030742c0c0800c8545e080a50301d60100110f00304034444002401001070050091551400b9102c20901d614030201ca00c0404002d14901034606440507024160800500e0b02c0c901040c0c000c01e0700e0511901d81e0000702e1100a106e03a40c06003481d00b5880d60250305151045d50b40800141c0811003944050024040d01c903400f2400d40e80020110039510380c4200311b0f007020805170041e410140e61103403038203007402800f2030340c8801841c0c100c5080e142d0394424101d10031014200e004d0303580c105800214075494500f41304882c0b911021500080c010308000b50041d40c4030415408010311084442a410b81403000c01d20189410111007004240703418081890000301003900c4400000c01d690060340344510200d25a5038030340c1e0900006460782e111548443d83c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 591683012 1250 591681762 591681767
    0x30b0103080703120516031116060e0f0307080f0904060801020a090302130b0f0d03260a150501170408301b041e0b0c0a023a02030c04050403 62
    0x1080d0b10440201d00c2c100c2e000740d005206030240500ca0300f0304c51038140304284945816005000f120050922241040000c44004100144903035402402a40001403019031700803400e2520032450014a01a40244011000145800c08031003008145841182e00d8a0109000c100503000c26040f5460715400810943c16203030b07001c0d00c80310849000f01e0703904a400c0c40300142c4004542c442c20074941c009030700c2070440319103040401c46124601e120f4035091a100102400d502001c04034040440e16181e1800305108102c507180c0540712220811564000d1802d00e45030000c2c007610501070114011900c000300180c02d111303841007515008108940305050081d81020344050385240c0d00c0400500e030680720080f078020301c40c141440810b1203201300710a15003802d004e03941e07030504c894068010762400400400b04450307803124040c180201418004124804d00d84c8104140100311001c81503103a03002c440d202c1151030f014034002c4410b05002042020f2864680086406e00f500169015005800d000500c0200f60307 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 591684262 1250 591683012 591683017
    0x1c0204030812010501180b07021305010303180b03192a090e090303010501020a02011805041a040c0206070503070e0105090312120f061e010201090203060c0a0207080304030c090b0109030b010308 85
    0x511269070082144e80307510066400d031309201c0c0c000c200001303910f400b40f00c6404420300070000c142c001400c544440c198400d000781600c3c0700b600f04600044020b0441c41e08100c00b002450301402c5056445421450030421455417415960350f03050049490f84e02054011000855009072000f40b1442172140420002002c1c2005030a441100e030102d01440015884d65030101c2500c0c1038520580c0980155061500110b0344080134003112001000b10f20000103141ea11407068079034501c40401786c1d000204101081204a44840795294103540009041108055015048039440030303e6042c0805000703300401281e0500070352108903007500c543c0c00349a401c00c00c0301c805000c034107405e82c180074190741d80c0e10300c200d0180c2e0041e18840d402c4030b41c04410000414003d2088400316006100004a000068000900d081805d940b9101d8040f400280482042e03810300c0400013800700072004518003443c5684199a014031445098005991030600503540e07807240d101c0c640215000950b4000035616814681d4241e0b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 591685512 1250 591684262 591684277
    0x30e2b110f011407030e0a0e010305060a0b01030b01021203091509280f03030203061c060c120b13020c01140702030d05010f06050912030c0102070b060306150303040b1c02040308 78
    0x1401c1c0d500c0e070054690702c01d2842407200c902d165249810444980e5099034001d100400144e80844004070105400c2c0300b00ca01c441c001d50140005010318200941c2d908112010b00281c10b04043c2005101c20b01a6000186020151080c90085c1d80d02d81e1600e0380c41d400c0041000e032051607030384142c060080d00e550001d0b02c40301908105220f46600048d40841e410300d0361900d04001c2032880d41c2441807010900075030145034414000360420f2204141410b120304510b803140400c032465603648611a50007a4840040100ba00a000c01002000b140c6000201140481d800c0c86120a0300040c0e00900c04400b03400c0a5186041404080700a050681e0041d440303400c2040c4480310145440300000d03100301c0412100c01160740a84500d4a00901c030410700540b5026070019410510040000e015070b150240300030102d880c0122045201130406804150800c81c0c0907040c1400621007584d10f01142d50048115022100c2503218540d980790301041801544503080c1050170403520100380082800134080048c03402 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 591686762 1250 591685512 591685519
    0x150d0b01080d020319110c090106051308160e0c120108071d25020106180e01050c07081603020c06040b0403140d1b030c020a090b031009030e2b11 64
    0xc0c0600382c2c41240e4034040c40d030f4041c0848002c0c2c00c1010582d402001500c0340c0480311019211030420840210318030800aa0114000400c00142401d001e1144a144c4018101c2d000141c20201031101500420250038011400350080210100f9142e411550031200034902044040f1000d6070349810090310349041d48034504042d084001c00d040f480041d6080c040c41200012002442d14001e50940a188822554080e0640d9038850740441c00005000b078921810056400101d8003021020400c0c1c2910000b0302010200c0d00148451800640e80c01e040e194190345082d4212800c40f51401c0c12444c5c40031806030681c00800002c0c0c04119884100000c01c1600d0064045003007450064055580d1503000b151100c00140b2125143c020101034208079104550081c50501c06d00c4649030001440000182d0242c10400d55138600500282028410b03146c500100c003004101ca01003544000d03003940340301e12045124552070310f46890703440c4034003101d4080303a6580703c62440c00e80303064034103058003ea290710401e01c03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 591688012 1250 591686762 591686773
    0x206010b210f06090f01060f0507141f14130f0c090c0c0210020a050607080a06081605031507050322051b1906051b0f250509060612150d0b0108 63
    0x14019140745c0c40e24101e90705592801c00011861200b00e03007030b802046d01100d0100084031500b1118208015103c150300c4180d040c00c09840407555080d00b1034018010340a049210351081020b50182081019551500b1001c000703800017007071404007040c0d801d42d08020300440ca40381210404a85c00026407400d103100f581c0401d500b88031850103990b05c1d800746000a0031303548100c00042096204a481d690000303100b19021034150380304d102c1d2074185240b11445c0105510724510801207440c0c01c20402c1c48824109194411904103590020158803005010095003440c00b044003d1008021100400e01c0d900513081d1041e60603242c481230840d4a100204906c01d50f0000c031000c42c14504801500c00712a40d035154107140c0900120011207240c02040d004503e0300908680f14015007080c0304c0010710410f0907181e0403610800c800040740c5403145070011402140d0f05c400b0020203494840c1180e0203407046a000e0001680d03a423a04031940030a205441d600035444030310800402c174882c494030781601c0c0800140c40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 591689262 1250 591688012 591688021
    0xb071214010f060c0507170309121b0a050607140309030703050307210207032a260105070512041e03021c0905011d040603140307022107031b0302030d0e030c040c0206010b210f0609 79
    0x1c0413309400f500e50701140410441c800a406000d94580b40c090160542c3e0401c40128002810103030303654803d9409130400642070f4100311040408030606201001c0407407004080340002036a501440c04010014424207514141a90641c0208800d21182c01c80400005407584000c1c03102000c00404a0f5020840041030310800c6018083c4074030a403015954142050740d4903248130326580001e0310540781043e02144c03044020208020505405009800030105100c2e452294004441041300400070015499014801030781c0c803010720000c9403444000390a1040c0c50b840060004d01161340014002d108032003085010400200c06400d03118022240e12424142188804101e400f41d83d102c1c494070341080e4004d01c0041e440c078486c120030503441080069116200d0340401d01d0f19060b07000d9034000c20380d0314000d004985001c00c080558090143c031300780600480f46070041d5564074103001e000039000300454a030303400c0c0c00c0e152541015440311214144460424448585000078140c504074028024480000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 591690512 1250 591689262 591689269
    0x603030408062e0b2104150b180405010506120a0b04080304030201021207110d0315030b040f14060a0b010f021005070210060905010807050a120b071214010f060c0507170309121b 78
    0x240c40303683c002e00d003406d0380100c6030152002884a031002c8c43d030080f604002c850307a07500c1e50800e01d0310480c46007000103803c0c10700004100c1c5804050100c21915400f503210740340001c5154038182d4029a00104a81c0c8944035841c0c2170b806030250080c0303031540d006c00c9000c001c1c1541d0b01029030000300c564402500ca01c900d900d50107c1c1030b5000c0c0a08030030840b1285100b040000c9000382d01035881070058000b400c0c4d5010300d545100074240b001c0850009548000e0a00075920041d05c91201c2c00e18007401c00401910348980040e45407400304440c5a6501e55600009260300c0c000e200401d104031803c00100400c58030307070a1400c0185000e015040d40d92045000201d001d04240401c10244c5280329194540890156121400428020420b81c2040a680e4203000e44c10314501506803550328014001c9801d6041c0040c416404060f9844a000c010060054401240c0042044420b4801d1082c401810844200c030840c5140300d41c2c0380d080e400c0b0504040c0340410f00300210b20203014250949000040302d00c00c03000c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 591691762 1250 591690512 591690577
    0x90109060e16020102121005130b01020d081807030b04050615010215040c0315050402030124061d092401050901050909060a050402041d0603030408062e0b 68
    0x401e828001e805001c10b800901203045081412440d10000d8070f000c803e0071012260f0f00f415a001c80c4008586070040c032261526881f002c1010780e005a00b008941140c900003552180085400b0091049560201c0e4801e52100c0d490021000807208903110f1907928a070011129104840c01c2c1c0b082c2c082c0728003240b903040c44d148805065200580c0207044000110881290702a0054001c4400362448e20002001518415585858000113007000510745400c0c0181402d4135032101450080b40e1850009011000c0c00751402000e603a081d241003c00104040141c199200e03654803031030740c8202e0750f0081112813424504c80c2c01e5083c060711b020205041446005444a0040c0c58105000c02c5040c8108d03400e506104000c02e40c481c0740240040403080d5a2004107040764420780001c80c901d8000004070040c0600021600e80000055000b185001e207042201038480130f010303200b036895090a00b4055400181c0003c100301605800e507441030442e0b61012007000941c0090707442407851170405850103104485500313 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 591693012 1250 591691762 591691769
    0x918060e13110d021807030e060a0c030b0a0b030c090d0f05030705070b0c030d0507051303050c18040818062110060c050c0613090908091801030327050d0b010509010906 74
    0x401908182c0c01544410305c644020040020140c0c1c03034a00b2314000c03c007007140600401c1c40c01c0d00055014002c4400405462100c1215405814162810061000d4010449030300c02c9006610544441000d400280d04000012024200040303115440003840300110060044600c500d0455101e95504d030300c0c0002c00e000b40d00c0c10404036003003400ac0c2d41c0e480720b0640010f5480641483d0585c54500409030034001c200d9542c00030380d1140e01c106024900b0f424610840c89405001c1510000d140c9042d603505940c030311455503004102400d00c14040310944030a001c0e91915002c040c40c542d40850f09090710f8040807403c0b141d900407417007201e4002030091302890040303840a4108015244045041d028012241e0058002c00b150440b902400034111a8038440e002681d44902c880d0f030344e10440d001c20030041d0055000840d034410b940100400c0000c2d000800003901280f0118841c004554640207410007500d1070348041e42001c1210b40700d03800c02620566a90503507000312400925a40c2310030141003261075600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 591694262 1250 591693012 591693019
    0xa0b1501090b07080d061508040b06060412020d020f1309030201050f040803040201140405040e0304051924180303020109140c01170c0c01020a08011a0a0918060e13110d02 75
    0x41c3c000701c2c10880040255004407940401c403a43d0f20080c0c0c413411001d156181c40091741900c10b03c030800120681ca240c21131021079002e807c2c1814078050b13036581910800005e01c61070b11320a81c40c00f1034913203064410108500a11040842c00d03007480c544054881500e0031130040d403074100014071014000e01d1050290f130b003026480741180e5840d1700540e080254242e8201190009200c0051581e880c0e0203000c551000240145454524000c140400c9560450942c00d52011495041c0501d4070000c40c0900c1c0000d0046500c03030101d8407620142c98898600303115030038280b041e08001c03007030540540001c14a05e01c034a40050a5044a4007c1d580f100b464080c1540000e07050360040700400000380d41e01d50081c0c41414400e190980c2c07410310908a9000000c580e000c646441c00401c031101007442c04034150070215519071302d020390400c00104450017500401c500e0110b00c00302c820740c0c00d01c41d61000c0064a42015072005500308002c540f151002101e80844005210034807800080c2401c1103007030301c1280e015 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 591695512 1250 591694262 591694267
    0xd030e011503050f07060f1d0f09070e0a1409190b13020415030905070b18100e010210061a0703230418060f05041e110405014802030a0b1501090b 64
    0x1200c90301c0e49850580c0c042070b8080800c27903040701c9a41d9404030741e41c0580b2041e00d5481c040c0800f003040c8445200307694020860f00762030040c0c5103e203440d4041660b5010840b44600c8174060100e54054008018002c2916040342c049446c180e60a0003130380c01082540d00c03040b80c2e0b04003040305800480075681c01000c010029013084900700002c0306010044c0030100021074040180382149000701d00d40069082c26040020761103900d80c40e1950f0103110b1100c0c00350062906202050610398031030300340850040741821411001400f40b0905101b2004410402480b0f6032400e6100d00b1404500019041401041c60303610f23072400e090706440041d2040c0d000310f8403003000d10f0303041500e000c0070400100303094800081043c0348a20300420400c41e03442204090740c1c640f1003854849040c44001003550790030000c1c181c0d0f080f9110913a80060200d078002402c00140101d00d00c0f20403030b400326950311303980c501c65002909449600c410b00108210040380c588211080c0072a03c3d240b04188004650301d00043c4144949681708 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 591696762 1250 591695512 591695537
    0x100504050709050402030f070f080f060d03140a0e01030e03042102040204080d02030406031b080f07020304090c031a0103290d140a03020c0406080d030e011503050f07060f 75
    0x98110035400403040c00c1552480f603442002c101642d10882e540c00511507400100a10150030203204442c1d0300340362401c140d10b80b410340920380d005000a0003d0340300d562410800702c101f6100325400c01c001401d030101661101c090400142c0071003244043e1307a01090a2080303c407040030000007690100c0c1d0130182c100e007505a11110140b41d0705803500d13069030002d808200c0854103035800c004802261542ea4000c503a2a460054024101c0395803401a08004040805055031540d201c4412500302440403448050354a4a00d4180e145205507845116218200700008458641551111840c101c180d455400d02a8804004404848400124140040c43e00c2c0c00c4400c0d1409000b0003080194010b071030202e50b864151034845000d0b440f1011a90f00768003e40c41001016418000032800520584060000d2800c002d02240c84000e0307403051404241d501c85840303455484c00d400080280512041590125480c3e0a0141d10380d0826102d02c6e01600c241c1000040b014403e041207420b03216607a54411102c0507 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 591698012 1250 591696762 591696769
    0x30a030806151918030b1801091415010515160f08300405071509030b04031715031b042d060509090d200a030f171005 52
    0x1006454503420003040d400d02500728081d0b80c000e01580300401c40e00055201c03000300082c01410380701840100c850791040108000740b01d044240d078104215003005115a40d268400314014200d410024000f03a100000603000b0030004140708844a00481070080140c0e211010b2280d840560802d60001410401942807103402500303900ea00240b190300501c00e0481103482707165003a013005007140140e2000c4442c41ca1080c101400c040c5680f4207028a80d01985069202c4a845540c0c03449908881e11012440f1044030788500e09a01c05954080c00d10b40050516040007010105001010070a00e000c03900881c1e9200c442038841d5060040090050040243d00030030600454881300d0084d82043c0c4402c2400310044122a0001000c0700006540c0c1d0912001002e50003540c03100d074007060141036440c0a00a0038000801c591030f240c02907042007600409089928841052041010100d50040d440c40b4807c15600c1480c40d44102000c0d5203989481040c0340081002e207a003510b01111300422a00304100c0c0d400c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 591699262 1250 591698012 591698027
    0xf0406090f0c030b0307061112340c0e07050c0a1a06010513030f0c03060e0c0109090b0d0206070f2103050f070203070b04060b03031c0e03040303050301172e0605030c030a03 76
    0x30000c00a4a1f07211209101c0b450705a00140c9011041882c41c11040f50042b10325441c02e130701c6600b82034804c6404074490304d440304034004501425007040a490000b4a05500407000c44454032016011180a40901e0401d122020018541214803030000404034085620076016200201c500d0000e071148a413556603010710a2000300e408132001e60341040008040760191185140b6015020003038100e6060340800180b00d2072040d08600b080710315040740421240c41c2c0a4555090036415501c2c4e030740d13038802ca05207029030360142200200855441d040706090b9107440318030001d558a030390f10144025129a2540c0d1308069044914070010f0348188180c5010580744107501b40c009001d20000503040e004540401d05682c00220452034081020030450f0440b42c95100e4580410076503000f0358241403c42c0d500500c2c0c2c0c80180314004180f1030110990b042e07000c052000343d0b0060050309a02690900002208111072010941c550781180391110010742c500b4042000c2c2290100200581a43c400c959011388005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 591700512 1250 591699262 591699287
    0x121503100f0c0e15070516060c020a0503060903040b0d0b0402220b040302100c2105042408070534050606030601030b070f18030605092112060f0406090f0c030b030706 73
    0x240b01b10a1f820304c1c060181629440038021540c1c9410001c0c3d840c1c01031000003021540300c14041c0e80014204011000044161010758201c240859502d581012851018000c51248550310520004885100c02100d400e0303104041003070302c500f0b014a5500c1060290b42e00840c4000303500483c1d208840d94031284a0380d1200441c038072840701000f4a039164100d20f820144c0700d00b60f00c008540005028803482801483c410600c0c09444484140f000300d9400041000d00c000c0c0c001c07402e00602150002003d1410317030446c0c2c041c50081c2d0010074400116141401000a014820f030380303a00400b8080341c00c0b8100894841c0c1aa6000400b00c00c2c15110f20600322040700c15044180100100d00e00f1020704c0c40c1c00c42000800460040f0400314460615407440c6e410124a600340d0702c0584106961012035003807180507114040c01c069030509041c1c0d50000440c514001134010303030b13901601c0e00801064600442c0e0100340507040b400c0c804c10035040031a03000e41c01c640c58030620703e0f89940070b01000c0040b288103091080d000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 591701762 1250 591700512 591700523
    0x206060d23030306011106090d0e03071a031905071d0a080303090d08090f0c09190504030f14040e0f060f130221010b121503100f0c0e1507 61
    0x203040e101c120462421a0030303003801e07801c00001d11010b981d01c400070b00f004078003c001a160508055101903641c0343c0c0c0030140c40c1030121440d9031000f04d50301800000001c0c42d0304d810211540c01d1400d8500300c01e50044480e0f03600100c41100300025110103201d007038442c20103500c440c0c192078100d4100d043c01c0340030b11b0b03031465008025102c0030860301c1c0d0610281d40110064170040889400c00640030384010f000a006001581c0018102c010784c9000040e00b02604074181d50304c10a41e2030306240e4491a080e07005200f07094034100710600082584c441419018090b80740e80743c980b10000700d08100042e10844c8525949034485502160341003421410311074000c00010710304e00d800b046001c080760154040120b54044160b0104800414008045000c11000d900c00c8041a0a604113410b0030101d002e0032410000c500d8075100000c0e92450030035403410820740002c0c211030b9015054a50880500346d80740d0107000301801c0032110b84103a8021151009550002000903074030200364a5010810740258a0a0b84c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 591703012 1250 591701762 591701783
    0x8161715100206040204050903091f02010906050906090f010b010e041d06100305010506010e090a0903180f180207120507030e0a090f0b0f031c05070203030409020c1c0206060d 77
    0xd60340d030300320968480c40550050f0850340303400e004110031500001c202c1d0406810800962410750703076042c01074140c00800102040c06030030b00c400803801420b40850060100f480d0074144001c1e4800000c9483c8208110411185c407500c00e042400d09032071240c1401804291b1090450300f040c501600140e0460f083c1c20b000ca0b201d1301c0040c10b91440c010040c0c4005101310f80e1010b0a2013400000e0007080d5100d0420301300001e8400c1312034040380c000301006100598440e41c0390703c00c0c1c04140c411049010f20420100c1512601c640f10038050400f980603104d025400320303802c028180641444d000741d80b8080d03005030401c4141c860080090f01c880c0d00404045040004154010f451550360043c5500509522180010200c81c507901701812030752000b9041d403049028600c06040340d43d0020b841c0010740190404002c0d00c42d442130040c0ca0034011070078000d40c07501020901189c0c4490b41d501400e50004400e048903940c85a4640340040c0d402d14401c4140182c001c900042c1c0681400c042d030400f581e225206429 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 591704262 1250 591703012 591703051
    0x90102030f0406180605090f01050306031009061a12030f0a021204030303020406080c090a030212030906070b04060b06070c09111c050702011d15060303090a0e0601081617 75
    0x8880e50b0190f00314001040700c2c814072030070f1301c442c90300080064406410f20b9850b280d0759000040301c03102d690342a9410008000700180d802c3e10705000400c00240c14102c1808034140038030b0844060201d0381d0b24030309825210b00d11400c8604d05a5111901c007041d0001443c80c3c0b00d031074840d1983d44d038070000c0e1220070343c420002d6254002e07004e030b00104001c0d030007960016143c504210f0b005100d400301900304c2650340000c0c4000c0150351344c2e0303080400c1101d504580400403003c2500c2c1481c11401282081903000c00045002420300a41704561841a40704610800a0b00003c0c020080c8a014078070000d04051b100d0031040c441c04206500c8511880c4078000307a035007460b841c00e214035031528500a0101d02903443c1d90034407802035024010100c42000b1080380c074450070104005035a5520480010210210b901c0012900585052040310507007000a000303d1001c98039840500100c402c1542d025001910090018840703038500385082030fa10421380d481c1ca041d2a02485001c50000016203100b03070001e41d103030344031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 591705512 1250 591704262 591704287
    0x3080a09030506101a1903270c03060c051c05340f1409010c0809150a110102180d03020f010e010f060b1e1b12070506090f060c09010203 60
    0x101d105099043c20b403441e1a0074160742c408240c060180b125602c003800d10030121080000340c01104400c58a180000355102d0100307540d00d60708d00c452010201004800300003424020211403200603a40540002d21410f030740203104840c20300c911003400d003a01c0913905440340c4520711a0089038001a41402d00891440085c6219101000c40c1310601081503400c6144d0300c1e115000200c44003407008500300003121507040c00703030302140f40305000c650f90402480400c80410000c1da04180e0703202500c00341c412060650012418102540b19006000c0810b1810007803101e071000500840c2d4681146000954070031080e5420300c1100924004124154090410301c011000002d100d50361071400e0303000c004107201d000707180d0740c5048a4403900450010103080140240c207130344c80c440041014100c0c0714510740d10881c0c24140301800f00d002c00343c00030900841141481e1a80101d000c1e00455000300107542c03013612400511503075401c1c0740c0b400c420305801000010f480c1c2085100508280035041c0141c81c0751809000d000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 591706762 1250 591705512 591705523
    0x3060c070b091c0509031603021c06020d020301080f06091b0f010507060c0801050a060905030303010e130804030302010f0b09041718040f0501151d091e04050a17070b0103080a090305 80
    0x180340013650100d60616280340c01c10006103058410614140c034a41141c021074030b00240e80741e4000c545161020480104001541110b00d608141034085440c0d503151010b054071031030b600503c07801da0b21901c404a40780503404a52020b06401c85001c03124030b007564006010740c2c00b201c8140c031410b104080c007418000c00e50600415801c40c9541d51350074071560404041007080d040b2a08150104622144d0900c00f50301c1c00270441e41516050000aa849c0d03075082201d00e024500004024145800072800004064054001ca681054a02024040141040700b0700046131000c680103000c58800315240c041440c1150700421420b000f00540c009648501804603041c2d0740c280c02d0180c00340c4c0c3e440d0010084040440d266124400d46441d00350951341e5141d85076101134002d90140c40c401c007290000304524403c0003017140c01101421401c01020714044c1445910781d5600f0318140c4217009044480d80e04124541c08485950340d205681990690a54075810307546d8100108000030b00c800c001010000c24003c000c07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 591708012 1250 591706762 591706813
    0x1090c0e03010c030608060c0913200705070e010e070f18050a0b041a0f041e050a0b0909100f0e04110a03050708010b0604030c0510020115120302010b03060c070b09 72
    0xf00412070030700e48076100345041f00c01048d94264000602603810550b4038a902000344000100340030400d00d01d2907204030a0440c85001c2402e0f05400002c45034104080800c00400b120303c134026584150f0b07a80c010302180103c0444200d0001100402c403e251240a401450040f1402d940c6000d0895210000303d40182c40503001200d1003000030408010520301e951003441941c00080c076060514411101545060145008a00404400403492941c0c22100000b480090000820300d00103c0d03682c01c1c20002d180c0c401500780d8068180340e0700041c04844806447d008a4004004050742c5510b03210340c41c100351101a104a130300050790180380440c0e50328030010b0b030080c600640150032100d00c2d0518090841d08a144941d0045400303100c10800b00d81405803035811140140c03000303000011090070807070040038442040c18002e000040e02003010004180c858030750394400d030003c2000390f00003c100355480b5400c5507104500c440400c6560700203580c60502a40101010003154160320001008029402c1104d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 591709262 1250 591708012 591708017
    0x60a0e15060a030b0906030c1c080f0d06080c0d120f020a050102131d060f01030c02150f010f0617010b070503070b070807090504232e0807060504080601090c0e03010c 73
    0x71130311001031a14018241d003068040700180601c039084008104411030826480c2920010381b11a5010b00022200302d03062800c95030a002d03a584080d046a0000300700c00d000da04554410150100b00609100f10286285508504100170908480800b01c800391180b001c440110f00800003403c000402c240003800c05d9081c41543c000406003800c0d04042000d89002559841c03900380e02c203200c080d45501085900c004420b1074003042c84503808506074504076801c6075202202550742c04002070004030009840c1640c0d1003c0b580d43c541da41c0d45504403070009600700b0540514074070400410000c41000010a80d091146082c4c90400706203807544210b801044a03c1004517841400b0819101d81c4240000301501e0704070340810003011710060036110b20001c6070407440380700700d07100124041c2d482281d03024441d5085032981d01da075212a1940c00a2044280c8241080703841030321000310341c5501075020755094882c0300c0f00903c0180e20340000031001d861000114401e102e00704e21802c22a44080c090940c50807842d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 591710512 1250 591709262 591709271
    0x19020a140904390207030309060c081b0d0e030a0b01051c0b07030605010306050604080303270709060816060c0b0a1d03180a0f0e19020a02150708060a0e15060a03 71
    0x1207400d07000c40c0d143d02e003c4403c541100d10107000090b04403c100301a62424509074890122500e0304500c54480c04d00c01c01a00a0360701c0c08825040000240b6007600380b056503603152082550b00a0659405201d1801410101200010f000300d00744001c01041d520505086c440302103107d034a81c1140480107451910010751101428401365805014410050000750f59440c9010703d0540d0355070303c0340005049103030030b80340c803012aa9088405005400002d44648241c1c1e00056441d0342038002010288036488050080d140070745130000305c0b5035080c021075005454500348540190350301c075003400307004000d280703016980c500c86424070460050300c40b0003140d42d400850755035811442c1d51200c44008011184945031040052001104190010007281d84a0720300703048a07120000b5000c064499030f071030740c0d007840d01c08991406200d41c0010170111138038080ea805642901d41030011500308800b2190190031241110040103502c0707400511650107445d070b07400050494a80300c00a10b00794014a100750003c0c0d203c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 591711762 1250 591710512 591710591
    0x903080906010e010f090e010e12120a14130618032a051e0a02031c080114031507020102090907020d02070e0f04030f020a1a19020a140904 61
    0x4000c2503025115281ca10300d1190b25184c40d07110500c0d206d01603852220744a481201c44000250481040800f401c4199a50300a594400c50100d401a680d0300003c80144404201c02e081903101d10300301810000440f106940c0c0301c06030901c024002d2441210150f50b1043c0c00c40380c40040d101c120300c2c00b40c806c0d521300c0108101e103080c0900b60005078040340780812000d401800000c40024086441041881c1c0003400e07404e140800500b071540c00c0101a405026060407070240f88900e01c1c009140124a8880c46243c0c2d032140081d03001c50110071003080e0540d0011070a00030301e503207031440e4590003121440090302d402c0300c3c4000320350880400e603040320259101640100003160184210005442c070018000d00c0d82c0391960242d42c9414014102030188541501180100c0d0304c00e1103a0f0300c820740c000450052500c0312072940c2c00640000c0320300401541100c1c103411544680c41c000c491102040d9601c228650411031000d00043d07100d400380e41c0d441680c1d004000d000d081c1c01c0b1811100e042107029040100d080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 591713012 1250 591711762 591711781
    0x90a12240228090e0714040e160f02060103020f0406090f06050f04020c07050607030512070807120b0102061504020c1f050f060901090f0b130f0c0e18060a0504090308 73
    0x90018a0398002400204081c40c01e60344000d00c41c044916840c131911140c1c40c0c0c0031003901c882c0e1012201c00415107000901007090007544c020b850043d00908040c00900419580489840040b1b411000058102800400142c60f08010302d1080d580000c00c0012440c1c0d4540c801401c651105103220000342d2580070401075403410200080400009072000c1d0b26004e03130042c501d03881e01070a00480348980307030100d90b00b402c1c98464003d0702c4811510301e400003000c2c2082c2801600d13500c0112100c6000400880c0b40c103550701207901500b408040187c0081182d03466070608152402d117407609441d0015030038850300b0350800040040030120142546401030008030000b01e4400c2d140b00425600d110502c0006002803038a50705046411a1715900740002d5034201042e026002d803c21032000380d486881103d0b5501d02c0511a8480010a011841c08105400c11020290340b4002c171540c0043c0e0020b418203110f0303d9281050344095000030020a03110704c00d91100b00080c111803410009400081d80001004440c05 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 591714262 1250 591713012 591713047
    0x51c051902031515090a03030207030506010603020f030a0216050d0f08060405010303230409140906071403060111031c090b0906040203030a050a0e120f0c0402090a122402 75
    0x400104254078600d440342810001d64140e0f207019020301080c044840030000305000381c0c3d4607190010004048255a81002540e8a83d02e000590344c0c2d004070000050420300920031102010400c103c554256554031040c00021741106202e20700c43c001e412900d000140041c862a0590300d190b48454080104a5400401503034004000e240100c0c600390041c000300750007244c012015802c0729182c103c0401c0340003480159005030340c080c1c561182401030034a40900e102116601c500c200f1001c0741ea480d600c8803000ca84510394454041e42000c3c0c1000404c445500c038410310800c1c110340208492803d141d41514131440c0704280054510301d50b03074007420303020041c41c003011701d0b0840344000080405080c6070f00041c3e102d00c00d400d041000c0c003000182201d08907025181480280c0d03001008281005144004540c40b482c44800c01000c0c1d0141d81c0c82d0507520302d040e2098500703c540c0900725100660401c0201c6514994128058591002c95190b5131145251200e401031408070307900c40580c88508501d8141c8804 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 591715512 1250 591714262 591714301
    0x2010c02060d2c0109110f01140307020c040f0b09040809030f060115230a030911090a15051009030f110604091b1b11150c03090a050a05030d030c051c05 67
    0x240d040a0700080425a090700300d06000f0407c4901c1e0751900b0710780e40141c4000070b04440200740040084100101c2130340100c0c0c01c032a1083c06503428050041518040310403038a10f100d03900ea1181b591000300300894007460181042c500064100c0c0e4225031f841103110f01d40f210986c0030050710604801600c02c000c1e1f112068000326000e40c01d58548031000c40e540b40d22180514044481010b64408851060003200a83e14088440140c0010403030705009070020060400002111784900c958a00080d0604190342e14a600c10041d6540940550450b500c1c42e903906601e440a841c814407842e20804540c0d60740c0d0050008110b200000101c01d5020300000c10104511603c11040c01031000203002698060300f541800c00340d00c0003a501a818881e00028074400c59000720014102000c0360400705c4810020042002c228212000403409a543c0100001070080d40955601500500030182a0b5400790b005511030318440c1c20f00c41d051000f000300c48500301000c8108030302c8068a030030034440b00e0f03c20051280e461 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 591716762 1250 591715512 591715601
    0x8061501080c040b03060f060d14010f060207031b0801050c030f1f0306090213020406050918040201021507020f1501061101062402030738040f02010c02060d 69
    0x2a14002445100b18012403255070041540080003c3daa6540d40f00400410f09009084903107800c00704440c840140301c100c5101c15000400c100203d0001c410b100346604540c1154020100582140e07100414040320800b88a41c1d076401100104130304c0070031f00032940f155101d43ca01e0303500c0386030918008810b00d00c0034020009031403000400009240d5000445825079401913804a801c2c4030b54030100d55a080c41e040810246880807901040d40c951190041481035021142105a0126031000e04124030003030b0385c02400760b0b101a07800f40f020141004082e83c0f003901e500550b42e041d441184000e0824005581c030103000d090a800501089401500320400800f2660080002504008400000200c01d04840e000045003d401040c200c0c030820440d007205502101296422070200b280c44404117001d40c1441100041e048583e90030b1070a01d440707510a035040090036503001e4880e001501d0700c84565400340d80000040194180d8461180103200440440314514130004440c4101c01480c3e10f208103402030b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 591718012 1250 591716762 591716777
    0x20306070e0a12030c0501110301080f1c2106031101030e06090703021203090d0609050c01050310031104060e150102060603070303020312090102041a0a02060f0108030a031d010608061501 82
    0x5441c2c41d030341e0551060b11810b2080000c40702c05800c040d9801ea802c0701c4028070a41c02c003510320090b12104030185040722005812a510800c0d410045510f6110700800c44911920b003540c4018060f01c80c58070858003120041b442502d200d00079010130151940e40e0015610307417a200303070003a0455a1503c1b0380118148448047c1281d4146040c0c2036445404510010b485011202c8105980101c01d0046904031500100022503600491820340c01800410307c0c01d407800d000748032101c030300e03075005104883c450111004088203c50860395100703401690601c5172a00241e89000103d400c0002c003600e43d00a02500c042c060340c030540040024501840101014000d8011080400000360004140c580c80d8100241c0d924a603035480a44500902aa90200340e4007800d00c0865150716101d0002000900096401c2d00c429a88280d501c4100302803e10400c0d178264402c003c2500c007544071761300400b0f02099240c0b00400d80641c807403c1500b510703200d4101202d00e4100358240302003000941402098803c017805c0c00c51 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 591719262 1250 591718012 591718037
    0xa20010219050c04060e1b040807120f060504030c060b010203041202041d0a3c08070c050a14011b020901060c0f080a09060e03070503210c0a06020702030607 69
    0xe40301c00360501d40a4070020109080820031600f400510103545002e130041050350b65a0206916241c415a03440080d4100906082c00c4080e40d042102d0588070108010002c8918000c60303400c0c6000701c164144d8400012300550320020b4210300900b13001d02c3c003030398456000d4540c07414031600300c0302d81120450540d07000b00700820282904d40107040b00d07a501160009070161013440042101c207004100b480b031a00500c080b220400a1001d00d002410b14102d0584000c0304400d034801e030714403a1900c4050000d490003480f220002e80d11400503e07403503100d920301c1c40c4c1c256611004581d81c41110380156400701c481d00f00142045d40e110f508804c209078450602002504d0395008100410300c103001d22001c0084040005082c802500850004254803949050382e41ca41c902006100f444035014800c0051001018564a498002840415510010f0150079000320340035020810b814142c0000c050540c0030f02c03004080002c180100d5100500070800542c1d502000d1041504002c0010240002e0240b0f508410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 591720512 1250 591719262 591719267
    0x50405060a090c03050102040305300304080a0e031c030c050928030b040602070c080c010801150e0a0b0a090e1006140d021809130506060f0604170a2001 67
    0x2590000301412000840c2c5403075041489030141503800141040d03000003000020410002520b5000044130410003e04920342122030700c1110510b0f80b02c41c488803090010402050300c110042c0380c3c0000e503003411805024600c010a007024801c0071542180000001200c90310b9405000b0503020095030301d44180f80407062000101110362061480484044c1c10282300000c1c081c0d05444405143c110044000502d071501e0450b000c1d51203200100c4284200b01000201c2006c0002d41d030644203416141d11915070700b01750500d060040c58180340c10400900030111a9545c607003d0003400030f88074010005d561034040351006030604000c1e034082460304102d2000c1001c01015030110b08141c5009185c21034848000c50301100c094000c40c3e007072544580c400640140405003152802c0348060054407085503030b035a9444c064180203101c81c40034082c0d4000e940000c84514150440c1604054020310182c103003a00c49010311812003190424044591203409820f0a2040c0300b0450040c0d41104100301d12183d4004000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 591721762 1250 591720512 591720523
    0x10f020c1509011b08090f09150907020c06070305041d040c06030e100623060f0d050402030f06090f1902060f1c05070507110a24030e1203070210050405 67
    0x10442450124a0301401da00c20780341c400707100c44000c0003100c1c44544d600f00000507070b1281509a00c00d01a042c0d4051050500c0c240041c890003003844140707404100c0006102d07050134010303c1c00701103000f44403070303080d007a501e24014288043c060795032182c07110f0401403640c2000710b84041c92000c1050b40c2c81000001128440e880055401918010444500442e007561038141c4202c4075248242c24408045580440642040d50322808550103803003800810040c4961803150f0089080038680030003119151035030907005280c0251000d400c8402c43c0d41e0000b440c0d8245a401d882c00b030303a25080000d0141810500308807442d8029123000006602402a50014006102e04c0c0c0c070400101c080440e280a0f400d02c0c6018400c410342500c0014803080c03904040050669000050440700400150014000da0414000c800107031614070341105000801c80304510b003510b6044e840c0c2c1d01010b84441b0714084402c3d080c49000340507880a5403c58685c10002400781c242079a81d06460115441d2408200108100149 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 591723012 1250 591721762 591721789
    0xb160219080f07050708100f050f0106080a1112070203070c140604031103030d110d1503051011190915020303070816180f030b0612070501030b01050702031b010f020c 73
    0x4140c2c0e500c041c10304d08581451101d40c04400c1c1401a0f800390012100290040e06a848221000704004d983d080140c8514800030700568000500344000100c0420140c1d12601e111414945a02c1c240190906075040c0031808803004401031300085260010401003a0075003000d45451801079106d088210007296007405240f2010313202c2c0c5501d4800c091079460600c00c81e100f84030442801c1c0481610704401a40301c0d4018400103c03c1464002c80039411207800a05500740c0754800e01400446084a03e6440903005c114610000d01800700644041c41d820286212141a019107030b0f041101d24000341c03180d001d00581155015500200704106e41d00381e0048003944e0005500180920102a00d40c00700c0304118880300052030780d50031060218841030500e144400702d80c4074031100401d640d5141c0a105560340c034507010f80d0319944981000d004035802504000350407801890200e0a208013500068039280e002c40650300494500c090a08143d640510003420004c02c2c0e000401e40e40e4060350104511004061 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 591724262 1250 591723012 591723037
    0x806070f0c021c050a0c170106030f020d0314030a23060916020f030d150807050306010b07030318030c02030d0203030622060b040f0602011503020a05010810030b16021908 75
    0x20072803e2508190303411896825004030448040c401c29203040588118a070162000041040c50265087e000c1409140c00b503e51202007138200301e00030b030f00b40030321692041c0007102840610b61040c01407c4006000d035104070b41e1740d000440c09141059102c000ba0649503020038000b2140401c02c081511240d40e00750304403190f0098500d20140e140e404070b0a000c0b0f01c04041110b400006540f50840d02a03420081700420100d00307801c0d101d07507a629402d507030302d00340d220b12600758000900400984014401420380305000307003400b00da500040c105600341102940400c901151340d1103501025810100902005507026000540c03550400400142100b08008807841044400d03800c044603041c0c0d02e0708004003d00a07255003d850b1901c40003241a14022401508015883d25810303801d400c545d12142c81c01c481d0060308801c01a810701004480d220b000a00e045407a022440d800800500b03080c800c184101401f0400c0d030702824055800034100550814004001c3c0501c04404006c280110100d50aa40422 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 591725512 1250 591724262 591724279
    0x602060c07080a030b030102270307050d140309031c020613050c1c0807261309020304060207050718060f0b030c03090f0f0d030c18090209030a1b0806070f0c02 70
    0x50210045c2c216900b0294040d40082180e2481c001002001d800d14003a0180903808450b00809059480d0b0883c8901c640c861035141d1518080b44131701200c070b41007007000400c0c1e910300b032580b5020915002d2102d072041c2c010040542d04400d02070f41400711a404c100810300401c2400c1c55030315819641da4926102c0d5220b5004480c091840c41c0d80700340180ba50b117600415441e168000c1d03041009801907070400c0d42148654041d02200542d034031f90b0448802220302d4000403011401c1c0070220000b900018001c490241e401c210030408614100031002c001d00316402843d80c0050380100480aa401c982e001104801c0c8400060021125130402da0b5404440c1099640d100e40d00e00e124603183c8034800c2c200442502402441c40709801010901d524407202c141c609100f506c52508089581000390303401c5030381d070340f030200f20034001070710302e80c0040c024120000c00700d4030880c4803611070b40c40c03e040020096103100c0d03548508019908080c44500c0c1d0114181c1059038414860300d002620011324200c00070701c9003006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 591726618 1106 591725512 591725527
    0xb01050d03080a05060609030f1e0c0102071a0702061c1104030b1801060b0a02010b0a080609060403120231090507050d0e280b010602060c0708 63
    0x542d03625050b07944040c1400018200946a036a1001d41080301710502e030303001c01000c1e10803009400035165819006481f048801d09040d030410040d007007240180c826a8010555104030340d01f0f07544801e246541800040c1c107510401500030b50114010421107020744e003130442c600301c0c038007480170400082600069041c160300036480020200c18940001440c03404481780039512200523a000460b003130352034855445c07558121035101c00050b0356489058032149013200a02c0e0041400341c000e0165030030034206054490000030f2000d000d0060501541890554903411a100030500c42544c84800841015000d0011088491643c0c0c24031880c0b40811441c8641c880c81d80218003a40320b8a20308503900b078140c8060b040385e0170b608090340206080780c041c0c4c0d19000224400c901c0034000e0580085201e1425003003112040e0800000c41d44100708010305041c1c0001200d507095000450940c94840b03 = true := by decide +kernel

theorem cover : BRFrame.Cov 591546762 591726618 := by
  have h0 := BRFrame.cov_init 591546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 591546762 ≤ n) (h2 : n < 591726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
