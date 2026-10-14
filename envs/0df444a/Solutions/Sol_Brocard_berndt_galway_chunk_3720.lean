-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3720
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:28:52.44298+00:00
-- url     : https://prove2.me/submissions/f84f1f9d-7519-40b0-b7a4-262a92c4ed74

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 668884892 ≤ n < 669064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 668886142 1250 668884892 668884897
    0xd090803090607020d050d1107060e070e010b03040b07030506010e040504110a0f0b22030c0b0a08060904150203060a082d1b040213150c021f02030d0903030b120102 72
    0x1480303001128080e58803c01d080b615809026244004140e052000d608070042030340144650941c0042d00b1420071090361200781c140d860700c2810885036008428288031600558061138050301070070700c00f40d16500f1f09030f0f40c02048040007010101015a5500840e249030711401128950005c010320510460034a414107501110190f0b038501d100d44075075800040e8000071240880211112202c4c0c490a00c226440b5801c82c0d49510740030401f00500611011000400000195014018480b1000c0d29100d182c2c0c000303400388802901462082d140f00741080002061034031960f0380720748060800343e120385643c00400d03c1c0e8106500111054000c039450b0000c0f240301c0010b070b030b07400341042c54030074520900100e112034880c4808400385e04e01c2801c407050000c49041036002007108400c070b901109c0340d05030754400790740c03407800598884c0340080d0503000080207501d81070a000c02119120203500c0151184800f001e541da104500390381003c292291360500c00e26000394004002c1e0400507140804040114007503038005d5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 668887392 1250 668886142 668886151
    0xe0a06091a010f030b03030415091701020301141c11061603021f09021e01090b0a18060504150e030c031c08100612051b0c0304060e06121b0d090803 65
    0x3011012040d03d164404d008000758001d015028510345800c022580c10020a030003200014070203c140002071500c2c06264002110301c65030700042c0c481d41000740c2c10500510200341a0320601850030704810038001d104248244a0380110309110350038542000c030300c050248809403000884c1028100c03040c542c0100340c10343d2202040c9a40240381a00400f40003c07510100d0000c1e40003149900211490b54481140c0f942c0d030401410b0154040d691010703c40e015911040390680010506001440c0342200443c589000d04003a0a01038105810507191400210400a80c101080401c0c003900040b42c8040c0700985200c40041c0580e64010600024500c81200c103103003070b034006210780300069000d4282c807414005a500c65601d958061075190088d9010b42005000c00304010002d004882c0c04280c6a03008103a48411f01000e1601c951074840f0103084018284990760140078200150410780442c0c400459101640b07116903404011000e2200e4141c1c014100000e8000746080e6001c018001023034040c40c400c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 668888642 1250 668887392 668887397
    0xb040e06040504081e1216110607080c0a050f03011d090303010b1c020c1609060801150303050a020a0b011d06030c1318081b0114100e0a06091a01 64
    0x9626418140021503508403000ba0a100c018004540c0000004407604c001c03100342c0d05568100721151212445ea9402a01c808942611f60344107402d10a412407441c5c80c1d0b1040801c080d10441c500644081c02148008101c0c800988001840c101024010320640d002c0c980f1318000182c403580c445001416400300407001c98841044500052031349000001141d05998071419541d0600b07820864a91368031030031b24030817070080d87c0a00c40d1203020703c82003260b5007000180c00b000b840001d14060003041110880d0b0000200d50341494500b0556050020b0880212076040c50456035070825981c04038200f4004000c01802412504000291081307000d0702c40510440000c081c00c00c6448600401d503460304000409904200404018580f1440781d5224000b03549074040c2000d24050f040d0b03100003645d0712019202138818510a409044800c092091103001e041d500044407107410018039250301d4040c5480340540c2e403501800050205015608614002e065144062100080f0714400d02030600000414500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 668889892 1250 668888642 668888669
    0xe061c0204062307021c05100501050f100905060d02071e020307050d020f0909010e100e0607030b1503040516260c2b020607080703030e16090e160b04 66
    0x302a0401240030840f2000081c08918080b4540d00307000d441c101501c00a68060883e0111601140080c0b0400c0a4284041000900c541c1031004000d0281d8280c6080c500400500c011820350b00e0b00080000c0943e50101c80f0359882c0d0803010000030192244440041800303544048220318a84030030300c079028041c030803419902450f0700e0380244801d60b000928040c0d40000382442043c060304001c404c142d00070042c02c001181a21102c0d40382440d108482142c41d000ca9514100149814000d0100a0308900d5500d0240514200c0c40d00240c11a0788040382142600b10000110703042000802c14004c03000641162105540d648110042882108c40d500e40d000700200032141c522401e0100398981b0200d001000d000d010108802034440c3c2c421300007480144145100d010320701680d00d078409822a648140d074445c3d5030f01428503004094902e46880d01c1038642c007030078900d40344c0081ca01c24001920380f001000240e4406081d519880d0220011210300c1d17860308003001240304e04c000030040c402c0d038075081c01588 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 668891142 1250 668889892 668889917
    0x21020d060b044a0d3609090303090501050c0a1407030e1e0a17060906091e010e0a06020c070e060d2d03020615030a170f0417030a111603030e061c020406 67
    0xc94404900030340074080e402c614080c008400c00d0792000c43d41c02e00900d00050100512f54403103085601c1540c104142d1b11007c142021026403102102d240703902c2031119607042192560700941030360100500d25100d1006506155a21602c107115142000380051405040c5550ba0007030085500102402901ea0b006241c00030b1080200020040d004505a00080c0120480c0d00e041e03240020405014208a54844a800075403480070015154400d0091400603614415491030b10b00c9c1c040d203075225513883c2d58030104010855440c0104d1215540d0080304440d000c0c0301492410003510726200c0340c034100700c400c24424824540d000901f00d22400301042000320007800138041540d60340d540c0000411011400240080a61100d4040c0c5001808440602d04103078854100528a510400310b042030791f0300c081148680140d00c455480040001c11002c1d01105800d006000a0754007540801342c1403210000080a080d110384080302c007101d900d109990035614008240c04007030f5006100c1c20b00002c42801198 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 668892392 1250 668891142 668891207
    0x20a0603020c0c0315130201111527060f0703091709120d0c08130302060d0f0509010603051c0201060503030301150201110f07020405090f010e060103061505090121020d060b044a0d 79
    0x4c0710482e051b10014102680c0300004056180c7e0700400460400d511200480d00081d2030640e000c102110400c1851b88840c0e40d03400f44153c1020209400170107030701c015001080290014555a0495002004950b0b034400303403241d010004a09905c02900580c0c001260300711480b095003c2e030401542000c051010347c80c0c18805d2800c4c1e90341e501001d082c40d004a104600d40310160200500c041c200d40c00040340c80381d42c03000005c0c2590001d070b211011640c0721500080c01c040d030a00c20386100c0c244448046082c050201083e80e00c0307000d03a4100901a40e510310101c0c86e584070070090341315400b01410080c400e01c81007030780741030308c9003400e200840d049424120146850403002c24550300f901c0001c1c01d00d01d1980e1900c07844071030b0220114012055074490300318640258864809003c01c06000f1100800e80060301d03801d020813a010905042d0041b0340388203046c903034074000b15006541e1980c1068000164002da41c04010704010b074011000aa03c02c4403803541d5000d40000300b40201411540362240c01070b036400c820 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 668893642 1250 668892392 668892451
    0x1112030d0e070f120203070e0c030a0606050a080403030b2412010909020d03120e0601060c050d0c0c060f1b050715020f28020a0603020c0c03151302011115 68
    0x100d450300601e10409024203c13103215006402c0e0700044c12502e00c1555510320300f40c40d00c02035804880024001003000003181d46402000d004100900d001440c00703981150080401c500500010201900c580da21141662511021220003107109070008501d254201021016440b2140305800c0808140002428080900c41c03495040d4001c0d020041c4c41d00181d9044a2072054100022086641c8400800482c0d104008290280006403a26081c0c0e58550400a1412140582c00c4d400c00090084040002d0b0300c058405044505500b004000402410340075102240b0f90001440c2c1c1c010010829000e0000c0020448100c4104205200c0f1659084000726151140c41a01005076802224120418421444007100e2145400c4900229003800c0c0c2c0000c8008825500c2000001c0c2c011848043e03514041c40a400ca0b04401c800034800c8140c90000034101c4800102200d0f40004081072140a5900800b404481d4418840507070300f1503040344502040c03007601600c0c5900801c402d1a14402002d002c00b00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 668894892 1250 668893642 668893649
    0x1050108030301090216050714010914180c28090501080106170c09030d0309031e022a0d081c09081204020619021509070608131112030d0e07 62
    0x34500c0c513828007221070003075401005855020000121070b440407490502404000d480012400c0980c0c003204000106041216046121070003c9601020295981c1e007187c09000345490f1120300c4166100e8410725218010107000f0b58420b4040341c00e03445107209940f24591000ba454031000c1c0840c0e201c0e00111001c0c3e00074000c0304e01081100c1803406141426211507a8000b600e03007002d914003000140840c0c2020004180040800e46075050602015004501001120300848040f4501c48000900940d100f41c0594038004a0079000c0421f022003802d29100314050b200a8800b5071414180d1a000406500c000300d0500841034403a0098000c0c00940074000e0441c1d044a9142e003042840d00241d00000e00c0948102d07800b4008200b88504840c0b84202a00007503e96005003801c0c140509141009900042c116200c41d04040001e011a54003d65210780003404440c16004004e02342c41d046040c1076035951640e07805401240e81341c243c540000020411128414410700c1141c0344145001c2d6520b04602 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 668896142 1250 668894892 668894909
    0x120e0a06170c131e050d030c021002122508070c060f02010504020609011209240b06070b0403201204060e040e030405040915020c0309010f1b02010e13061e08010501 72
    0x1101000380100d200c520b44c01c0855007440c0b0458041d580d4000540030802c114049011840000c60403082d0304d864010308000b06c1550010b800705011800301003800f849103016402503078100b80f410201424006a1109695600942c000e40d944800d040c803010340899031080c0c00009048042c1102c41c3c40c03041c0100c1d8090340e4050b0002c3d0405103024010f403a04450f040da6081c0f819900c8900c9404030381022482e40340200c00600e14405400c0d540c0f10102615402c48a141c0129020422003000525000303901d0b9000f501840c10ba0499400201700c01e880400400c4900800d01c5082034202404001000400c111851515006125440e402c14481981d25034401d281481e04244000c00050034250441f22070144501840d980000707501c4402d04c12a0817031a00b21002c0da1003c9149004d958120760304040304402d50401400c00403070440a0049030303012207002810000c54040f00300082d2a811b4a865071300020890922140d0785410b51b26088424016421084c20740840340091402c0c0e042c42441d050340e1440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 668897392 1250 668896142 668896177
    0x512070f0b031f0f060c1e140d05070b040803100306111306020c09041205070602160b0f01080d1419020604170408030301051507021503060a090606020a120e0a06170c 73
    0xc5e804d59400744c080900b92507a030015201c2c4003640304c4003608981d440d40300780a42c000440901310f006103491054141141485420000e050204018420b803d40c400c0d4041105940c81ea90130320007146a0b1941c1d07000401c140d0515980903c3c10b18070001405483d401601407141c0c06a4a45080340e4508030345204075004900580031074041031554990042454075400c285140113200e40d240c00483e070101c45400340d8012603103218000c101c0082242900704005050a00e49941464001502c3d29500351500e02440542103060f0140545082500c1c0c59040c0030300850706c1c28040200280d110742c01120100c8111200405001045490030261410356403510f005504503801c000c14401d8903510b000c000400d059090214400580d1341620040c11400c01710041c6d0746906160307003800403114858100c1175200e810410140503007640003c0c07000030030350440c1c52700c480c00c404600c060303801c84016911241c10400c0f0b61001302d00369400c0122540307030602640207210b50f9940d884986909008650b041000003075407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 668898642 1250 668897392 668897399
    0x3120315040b101107050a060c0506010e010807060305040c030209041b0b03070f1103090411120702011109010507031404140114090d0803091f0501050118050a0512070f0b031f0f 78
    0x745014a5a04044d0300495000d15100c074000b4000440582c132900c0014164a0740908010080c42240c2c010b002c0c4000748110395050840c601d80f40c1005000e00f2040541ea5000a414000102900002140c000e07002c00410b01302401d10001b50b0360801021001d000d100c1d100094210501002c40f40b040322280e890b4020448040380031245039554000380203481c030040c0400c500694491007120041030b1040001941c46c0c08003245003020401c001c1a58003136914044280ba40390b00708004139000f50b0807d10f07100765030703250310f1405070b6124843c10740f0103075541400314020804240c494144054a10300341ca62041044203210528250710810030900d81040f5180640000202480081d54004004030240e1b80c107203e90f440000d1a06107556980f1090381d07211001040b103941c0180802c200c3c003040342d0310280c0860801020030051000e5200d203034003681c1e145142c0082d002040c00304802030040803112400c100d90714050349203260020b944540c1d0380100c00710000e50100b520342d0140c00b15020600c2e110007441c40c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 668899892 1250 668898642 668898647
    0xc0c03091e09020c0f0d21020a1206060201060f23060a020f0a051c05030f07050307020a051c0801050604030c050105070204020421050706030b0a05040b0303070203120315040b10 78
    0x1a010700003480c040111004100d00b0180e00180c401001d41400401400032158105403030714400d01000028400c9281c9255a5650040c030542c40d0f40d400d081016a5440c52484112214024111816907a0b8a01359001c030300d16906400ca6800c0710000b11310000f4290700da1403442d8007405806128485003010300320300c04003030501101410101a560060742c501450b010362060610024910841e815005544c07140400450307507008107408106881d1560a500d0203080d0071040c040b01601071002c0c0300000c400252521f100f00078008000b0344c804240e0760101080d4002182c914252a90100410050b40021603142003c0f821703503041700d4102910758100381c9040010b4030780703602039501aa00150200008229445884001e10000150401c07500300d04005082007820505590040700c2003600703005010a082da2104054000d603034044a000603907009040002c0e240d4402c16500035003500523404001c9070000007001a522a40d1030011001148242108010840d00341a01480e40050440350b070812461 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 668901142 1250 668899892 668899919
    0x80304050a180b1309030311031303080c13091a040b060304060f021312060b06041202011202040306060f06111c0302030901110414041b020703121403070e040c0c0309 73
    0x906a000010701c84841800b1400403008912880c2c2c000ea00d0722800700406d98544a103103503144224190703d0550070040c2c4010003411b4840405003c20610401051000d40c1e90300841b0001e400001d0f000e1083c90b9280300c2c1034094403828041540d5001c0120115440c0d007841d0181d04500c440060440d1f18580d90303a900d06d801041681d01003980311313a003807011002d031007120350b451000303003900000030210348003a4540f90303043c0d42d01078082e17a0151200f480100409000408104030081c1d090130280300f80c8450000b020300034080ca60010b4062410200001440c1c51183d9108003900c0140d541e581401c1907060020b070340c548200141600c050030030f40080c00010f10a9000d0b40d0070054400c0082a10003600102d05d02c207070050f401c00c046940100c1940300c074914140c0301e9400c1052140c40101d04421800b0000b940340ca10512014003a6030544280d699900d12404000c100012481c400e26241c0c1040c1300d00a0620000c444201e0203940340041d98149640180c054910f03c42d410350b00c00c00c41c641050069a00700 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 668902392 1250 668901142 668901179
    0x1c0504061404150504050f0d200102011407030b0a06081b031f060e01091706010e040309030c0e041401020c1c02010209040f0b0306100612052d0f01080304050a 70
    0x1e41c0610001c0740300d140d00310541c400b4003800d82d103060f159030a042c20030850007580c4101520503483c0c08900d000095002a178403909049520034030800300c45450051740501a9880c50000404107401000b21068140e4054105200e0980303505840c946c0301d140960b84404142c1d92980c82c1d164081050704041c41c484001d5070b0000c01c411043d08200d0441201800b0302d0070681005021511246a03044156402500c100040c021000c1c82d000140520b5501501d40c541802014801951030700043c0070f25010300d400700001c6130701c0128804a940d54103180904510150303002c480ca0810800050f138250814000d03502c49011104c0903045c2d03034182c0d032810700622003583d0f4a03100b075540034810702c41c03140d45a00c40c250070003840d2400891400400c400301401e080000705003900c1c502d19038dc828003415a000708490701200c6840300014194944844010040e0022410304203560b1040a0920307404c1c401d148914010a0304290040107039881e1400c0d40d440340114000c1980242145508100c1c0d062400c0303603044d80c0e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 668903642 1250 668902392 668902427
    0x20601031115070b010e070e060f0a1b05031801090e060906150a0309020a09050103030210050a020d0c021518030906030a0f09051c020a03090302040b151b1c050406 72
    0xd02c0d40100b0100c80c3c111041c25242c1d18071182c0108503c0801440c01580b00d0030500e000d00c0034540d0134000400740e0042221600f0400c80100700c0d009954044c01d8140f0060b12800c050703807840c003170614140344c1d41da2154042c10030300440c562401190394010508c4c00142c0f81256610b42d116542d00d8240001c074040100340a40c01100501c1244100d6504401081c409920b5603005c640300c3e80038014051500401d0780807100c040e1401c0700402c0800c2c3e010a20104420f05c141012510ba1241e10800010780205c60000d28540d1401c030000500540003d1041c0400300d040c021503085585550325407030145003508450000d07402c20854503070ba07450240000c60b84886003110014409036029035160817145140c0049409501c2074404074001c0400c01b501e0480400148010718403101240d0b8000c28003006131100038041c6803a0f41c2c0e0143d01da6038516214110380602000b00d81c4a20719002d512981e0120ba4a01040c103014540d894030404912444c1998504d005480d11840d0915040044401c0381812020051 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 668904892 1250 668903642 668903659
    0x9150302090406200d0606080c071a040f0c060306170105010b0a0c02060d06120201020f0118030c15090b1801020c03030705090109120c0f050d030c110d1407080c0108070206010311 79
    0x11400c1990242c244180c4030f10300000c04909152002e42003088c0941040c1520206000c4600000e1000e121040c1c03200b00d41100c040741d034850b440d241e6072072954040014440d42480c4c80100d01c0a61550009040311680f941801030000c110350100d00301e507020b000c1d0456041e000c0084104080c01505032010440c03001c3c100c94a40704090427501d0444035550000741100345016440001d43d0303810807000b110b41c00058000c000701c00c1c071004184400c2030108401414003012601c42002e01084001da03403005805800d0500101c140c5180031003103180c2c1280c85840c42c001e2410581c003103400500c291825030180000070341c5540c85043c020750345500803065031030410100501c0814180e0240c8a444074992203002409003150405000d0800c1c1001c9810050250a0109000d400310b42d00c0000b0840c0142c0242440041c1c106107800b05000c82808a40503021085020401110020011301e80080725104c00940701c0c84480d03500110358a020a4035a0401680b0800040c008243d81e0845040c2c005001030807202d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 668906142 1250 668904892 668904941
    0x30a3c0b01051e071a0709060e0a1502010914030405030714031f0e010617190302030c0f0c030735330c0903070303030213050a0f09150302090406 64
    0x3610b03009208031110b00020041500420001303005c0e51a0f60071072042040c0100b0385402e520081c02045503210304c10822808490418994683c01c4401020f0301006120a20641d003481d400ba018000e075a1003115900e03291885140441e501005407001d41b44004d018100c541e00d0910780c0c07620a000d05441d182d06000718170030b0722a0f0030318190142d8a4a803440310301003180c00c008040d6030701b19a52580490240a101450302002e10000310314100301d0080921500c0620000b81070880c0385014405072500c0520401000ca090000c0c0040c17800380c0754000701d04545206440386004e09041100001c10022200c103401c40e461001001251407046068903422510480c800211003556060201030f043d18880c0710301e145200c00015031052030390005108100754a080704c40e00c04250b46d0300f46480b0203410554081904942000c0c0a803502008100c002e000c0803010740c171001c0100b1038150602c00c54a410785000040d0302c2c00b41803c2441d03412250000c0103e500d039030b03071030f00d03103e0251034501004c1008444001c08030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 668907392 1250 668906142 668906167
    0x405070e0403080a0b0f1f0c05011a1f050306060a120519050a050108190c03080f0c070e0108100c0201200d0b010c02030d11030f030a3c0b0105 63
    0x1103100310b020307585156040c2070580048044500c481c6545c1d000300040f904100003922410364505c005585000d0601e42054004e00840d03115070044801071165007094a404800380034000114582c4404454070070100e840b00805000024101c882c901c041642400020003519025014060040407818040012184030184a0886100b212032010554400c1101110400d05215080d40140c19800c104495410302c840a075035800c04000c4503280e421400c106c80100704003401400001c55100344d0329900d4160008444d46150050607402c1d00034030442c3c070300080760003110402604903061708000c1d100040132111401c000e81100c03c100801e41d0f480380e0903e1042036403039000c1c445108166203015101c41206800e0b500361030001d4111810030654054000240c0d5001c100200c413844942010701d0003140409426085000d905040c42c108500841000309800303164101801007503030017103e059108403175810080c030f114021030040300201641201c05d80f2508070703034080001004141030407400c1400216a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 668908642 1250 668907392 668907419
    0xf0f04090213050603090a1106070507171c050a18170c0a06052a0f06040609120c051f02371704080d0908030109090317100905040507 59
    0xc80c060340011410703a10080d070780341100a0700c1c1c100c4803285035040814002c0c1d642e09000794040c1020058942c0d9543e035580e200103c03400d440d80501500c03002962012143e0a04401c90790400d001d0150507243d4141640951900c566070140d17031212414804100412103102c3d01403450848002e51005000c14110f54001c1c0040341c82503144000c01707061139000184040c1e40055071243d028000c082c01100b0142d03911401d44480346000c0400d20582e078000d1842c2d1850b1042ca801050240d01540c5e0600c014000035401c9440c82034011000009400d01509003102e5502407070340060300940000c1c49400c0803204201101588a90860025003812814a00c1800412030791032480f21402d035a94070350f80225010b42c1180c59401351414940c141d44069224003003100801403000703119240010301d45440c00c0c00c59000c46a2a5004180140c496071581a00001850821802c0c1d0114900481d00b8603d07a1000c02e03994414580f18505030700e8203182402d441c002c0d08014000301c485004110380802e01240c101c04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 668909892 1250 668908642 668908649
    0xd090503031801050601050a1101141305010e0a1e020a05030d050c15010b04060f0306090203010b0408060609270a0506071806170103030c030512040803060f0a0305070b0f0f04 77
    0x295a803402c0c60a900350010840d151444120303414602005020380c1c009050716440c042d030381003002a04420122003401000b00120001440c17850405100e000507005001040803880b0324001c000072138090880950b40d61805000070034401c0c2c8040c0305550000c940c04040715082c4041c082442c000e031aa00020304201c1000d000000080000c50410403015041010015220340d910f1380a4540d414080652010311580c0124018400007880200d1103070310a0388101c0c02000d0080f011502c0f561a1055a0768950040c440c590f0140b056801080c1d41c0d03c1d2040340d4a0250611040e01c41c3d80781c8144d10134550111010f421811140104014400481c03028460701d481401c040ea07622f003000b1500100d002a100e03081d000701c000c001c48041840d006401c038200c0a41503980600307003059841c0c1603181c100c45500c00c10440c128852510414041005902070195001d42c004881010320720a2090a10501c0c9459120207013213680450010062464507200030041c010f04000f220b45000d040d82c0d00b01d24141d00590 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 668911142 1250 668909892 668909903
    0x2304030201051012080304032006010b0702100503150f01140706023f100914060a1a042102090907031b03030503180721060b06190e04020d09 62
    0x2400c000e00c403242400500d0144c071030301e035080340d091406803280703221030000410080511112032022a0000c922031140c2c41008c0d022411201c0c06d68651007240c285800030007007280101c00c044001c1d001280110b060300d205004012541004005510070007000003540401c1c01d050103189181200e405240300d0050540714024034000d65a40b820035500484000108055042101c480d0180c0001818100c0a62411041d507880134003a600e0307400c1138010a82c2550300080a451030600e4803030300b03c54074096162140348111703004808682e07241d02c1e090fa0301d02c02d80305c60515890108818005100916010610b5000320003951003840c580794080307014039034242c0b4a0781c0c0c50341c010b410030410002c5043e1092620080c0442410040b491640c0140c114007010b005140c15400030507680405210800000000f840118004151502000b45854016240945c1510424203060012005040c81021100468154044c1c080104c020b858116079070b49605216a600c0784d020481c4801c040c00034010003801d02c0c02407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 668912392 1250 668911142 668911151
    0xc1302030c091908120316020c060f09031501060815060c0a0803150a0315050901020a0e0108070e04061502010f0c0206040807111f030e07051011070306051315110403062304030201 79
    0x247c0541504141c85107020215401001c038540d8079181c0a054900601302c441e021a110168440068101042c00c80c1d08108102840b00002d0003d0b0301100280c050540d494807200400c05000c2441071600c0b40e0b10503003110364002c40c0010005440340c0020344c3e21181c400000c00f40c0300811400240d17490060350003601c031301d8180c10604100b10760b24850b298010f01928005c601e8503044c92809443c6480c0014458140890040040d6240307010b954081c280701e20061040282c99150041d1a55204200d11084010b40c42c00d8501e80302c46481d07218080702d105568000384800e079160359a1224a520010040340c01641e11903640556844d20650680307000c0903415000c04800c2102402000c60f40c3d003541c03403882c0d580540020040303501d4100d2928034003145840c110140207048403003680b03486c6180d80006c00340c51401040003400541140314560480c030503070500c080c4011058000c000e8800b16501600e50030000c010400c005000b036801800d030344444290002e5039103c244075440ca40d0b4802c560540c0586d458 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 668913642 1250 668912392 668912401
    0x6131104110705161823160912320123060108160e0f1903030912050c041e05070c0624090207060b0d050c1302030c0919081203 56
    0x5002100b85484c41c054407801840c90034044043d078201031066502116501c4081c1e10440100600040c4c9100618001d540103040078001130b426030508804c078100050100c000410b807540516148440345401c4074144c1c1d28545d038080c110f841d8a0030405c81e040c000b8038400b51000d490f1000c2c05032070140080c03004410b00500c50401d4013101c0d071348003c0019040002e260308021840c243d4034014801c80c0715600d4440c200c6491040850f001c045200e0119030f1003149541600750a010307590100c0150f911035556502202d40d10019084d0684a22a008000341c00080b242041030815034800c01350a0007018120001c200a854441e04981c403e4403040e001030924a028000d05c200c80c05a2103410800382086018503200303a8a03a004802c1c54016244815000255441070206e01d410030150b40070001d001d5070303200c0070525040741d9070946040d00d0360051445540e18041c641c89482a648100820f1201500e4035460104101210601c1c91171034001098411020601c0e0302d041050540e2030942c0316490350b0ba403d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 668914892 1250 668913642 668913653
    0x20f0105010f0303120c09180506120d0c0f0510050a0b03070611030d05130218070210090b0c0702040e0d0c0204061205120d06091a040f0e061311041107 67
    0x405802009014400210401c006035004584850f006070600b0001003c040c0078508807081f144551140301701c140a521a101800410fa1016010341c00856174030103a40001416113482c1c0700304103141000b06110000050107d04000c030200b5030315108809481c483e0b403c0c601780c0000c0b42c40940c0e205d840c0540c2c0c0c0c01c01c000b0302d0508000d41805401d150502d80f00070740201c41e440399244101d00c003181070f082c0c071040850b0f03407481481e1047d11066401890344205000800480c00001d00440d002c800600c5420b4001005c40300901c6402d080681000c4030620917034440d400c08506a1041104031b80040d175500040644203030900c483d4103040f0b05a0380d110740007280341c0100402d0750600d800601c03001103000204e00004e80d000941c0f05080c520081c20035250180741c040301c8000d040940c0000b946900346900b0204841141c1d80d1140c186004407010410081c0000c081011900c040c03a03405c085a01060203c0c80240c0c0011807004680d1140621489801000b00410700361550320510307629014002c140202000f4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 668916142 1250 668914892 668914901
    0x30b0102060c0f090a030f0f0512030103021e01020f01050a0c14030114010c050f03030103060204030b011d06060c0307051237050901120c0908010b0609010e190312020f01 75
    0x5400d10040c00345041002c8507000500c603100e01520008400a000c242d00d4507074004400046421106c0c2c00d09082d0941071003000515904000c543e03d003d220124001c100d01403003540e050720b0b00600714540341c840c4008007081e1000031141c0e16040d0312403501c20640382042400395621460305070f840419000000365010b021051030445400840c48140010702240b0002200000c4030142464103610243d25410004d0520400c400300d0000b81c00300000100500c0aa034004000b20703071142c000040181c3e6075010720502001d4508802403802c2842e0041201c0340381c042d01509010105400b600d281801da030351903502e084400441c510800d030000c030f200c2006024001450b110302000b11404140e40000040d80b81450100355001028000080380100030750f4841c0b852424100750484081008a0700d10102407c2d1000d83e00c1000070542c00c0011003001810008151084000c0603150b400c145010b035410001400c0130200d00f81c2e20840c3c00c01c0008049a02aa000c00302e00d43c0c150040c041d4806404001420b58 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 668917392 1250 668916142 668916161
    0xc040b0604030f1101120b06031303090e0f31030311090a120b0c0408061305010219021c110304030201030504110d081b07030f0206070c050405090102040f080c0114070618030e0103 79
    0x546030111082d41a12001c0c1200c0d800381c0c02c08410b00ae2020249008d403402a003a400c02c240c13044030581000002d66100d09218060050f1108091044804070030f1081c1c4444090a0402d948108010b8840064002c1d00b080401c4602d0003041d83c102100031000c5035040c100c66100c51000f400000084d402d101e03050b01c8064000509440d10303850f150078140600c0c4da40501919180c0d82036060243c80d01440f0003941501c080c40e044583c1104644170844000399620062110b4800c0c111007158070240240c0581700c07034481100c061014500301490b5800550080c00002c0082c0c40800540410384c0c1c09582d601d0803120368031300ca1000c0980320000d400310031034131469a24031220341d903108003c20b10114440d0718500c0440c650441c0c40e6507481c06545410400c8407502d81c06280c010b401d1000f800f079241c0c01034000c3c00c1035440d00054141c001e0758800340030b503880c0d044803060740c003290414103040c103040143e0000300780c054014134001c500d01034161200c0712800c8060b14241d002910310415042c117983d0501444809 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 668918642 1250 668917392 668917427
    0xe040b090103020f0d060b0901120b07020109030909110c0d0201050f0f06030307060e0319021c030516050a090f06031b02030711010e15070506270c040b0604030f1101 73
    0x31581540e010802e0704030000445403203090007038109010014143c1110490030005003100d0f21a507511000c802c0d1681140108644034800c030b90002d06114414421824000e80680e10541681e00d800060001880d0070003010340c004504000c0d03120001c42c00c0040c0b12080c0800d44c00021180f5241a881c90500000717000100000c031702005104007980c001056494a0350481c6000078200c1134003075068038500c521003002e04807150000202da4104c3e00803424040000991094400440d4055421004c40c1d1044450080d03204503e0940f10031355120f280503000400035070600955090711030640d00d015151950080000903200c0381d007034203c0351a00f044200b01c01c007240020360800c410b17a070b29107040368a644583c5042040e1409401c4403540c4441515018280c40c258190760390700c131414416108c28040b1105010124081420207410b0130700540d880e03c140350342000e8650300105204001c090000c480304654082024080400403036600289200349d5403003080c00c03d481c012104000360000610307a802c201d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 668919892 1250 668918642 668918659
    0x150b01020316120c02030a12080c0901080f310c0f1203030506040b04140402031606020703030804050c090a020903010f0c050904020c071208182403090f0d0e040b 71
    0xb4010080c55540115407001c040380e4611802c110450700c00c000500040e62600c10700341804113000c01d40004601041e0940e80742e5260340c0d19072490501511520745481e00149035003001450510519045503080050110003400880800041030425440c010b5244e51a0100c2d075000300800948012031402842c0840c1c100418902d408082840703e0400c000c05014551914002035607aa102e82c4110b02000c8001c20401c140042030b621800c4901003154102e0207440342c800a9174140480b000341c802200e10950092481c103085aa0458000c2c1c03002d001124944501d04022030aa900e010500d84102d0250ac0010b80320821281014252042581001d02c031515180000022661142c21141c0c441d409440242c3d072545035402342031038410700e6480b2a00307910300e0300c036a4020424050028441a040c403541e42d14a052842d04000d0782120001070200c60392809007104200c0b0a4201c06035a2000b82032041d03402d8260340001945c1040c400c41130080005404841c05102e620b441d00c01c07400c040314151845d05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 668921142 1250 668919892 668919907
    0x1081b2704050106090e270c0f0a080c010f03090203070b21010b030a0c05070803040602120106050906030a09021f020601080f01050103110121090b0411010203070f0219030f150b010203 81
    0x50070f01d178482c014659400c8440740010f56180003441840400d0595600c240c0b04e4060030015036848000b07022550303220f98001860083c2c141303040400281a0390f24400a010407400070001034030484103080c0640249515560544051f90703051110704020303c400340c0030b165100d00081c9441c10000d0540c1d4481c0c4001d51241c01841407040610030360703134010891600040c1c032001d050300603503d6000c1d001d80104417100020401003009800d8020f48130000d007042c20a01545d032606020f4a1034010744110702c0d0408400e00c00522065015005041c40e14000740c0040340d40d107404c050f00c0314144080b206c1440544e010b1001000340e00d00030420503109000003002044194119551740c3c20f1011200c15150400103140c02d15400024a0716403c80109000e00081202038103501e041d90a40f00300321402d4404a1448582c81340f65400032080711107040c0c1c40091503090720b032241c0c00c00c02046103895040302070101c8e074040400001c40c4d1348541c00041d4040c040c0c01c802c1c2c3d000c40e42003501b44d4180001c6141190010300040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 668922392 1250 668921142 668921147
    0x102130918081c05070f1707050c120c24070c1110020d0e0f130f1b0c02030613080702040e010609110903060105061215010e100f020d081501081b2704050106 69
    0x11f280c03414109074010ba8988030b4000803a880d0103a09442079040c041c0c48a202132000240008001e41c00943d0255030303000d00d00c04d0071828040c8a180480710355005003000541120321808110120520038811080c0c061074440200b8006032000c40d9007000759112215004107141c11a211a4444804540c1000b140388410046424410001c205520841c1c6038336140d09060700d5038015522540400440b1130040d400b64000074884420710b02c059000b4003d04000c11245501410201c00f42500030344090710346001542808010b160442d000d060399562840c01080f18100c502440c0310002c081c64100751140910020107041010681c8143d10800c1d003000500405001416401c4c0c0c00b0609400c04841481c02d1001030f52002801c4071a01c0c1c0c002d4000d02c142a00c181c01031100d5000c9981035084880303502c60400c068840c1c103415684000311070a6034401c1c01c8650b10900810b80c0c4060b0001da544000030002010490b25002030440c22020480300203a8204030001c0319495890000488080c000c551601102 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 668923642 1250 668922392 668922407
    0x1050a050f19021606151d060a030f030207210c0902090114130e1311090402060f0706140f070f0e0d0609020316090606020f0102130918081c05070f 65
    0x144070b00d43d40204081003c04c1200ba4140080d41c2c00400501c040c402c40c444410202955028020818507810142c1220044c0903611030312034000036001d5400c240c21602e0701c201c41403c8510843c21482100c001260001004404060340311005000c0a4000c0051800c80f12660a50f00200d07400c51050001409607070740144590840e01d420300707102d41d403048600c1a048066105410028030310030b400b410f000100d01c241243c50b19040c0915004240c0b4050b0074101724250340180c0d00a58440002d00000c421040b082c4001d201b0103106000c00584442000c0710000040801c40f0744200003142c04040107046904a40f02c8040c0501914200300080300c00c1000a1001c80482e50240c00c0b0b9640740315080440d14200107444c03000b10a0717a102c800456480405c24007501c0b15000d040c0040c0640c80718011078403414003e640203200da80240001441c14882900700414415441ea13034004107402c0e2000c0840c031080020241c01d194506a008030098542c2003d041e11030150400c0c3c2007090034802d40d440a40c0c0203d0303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 668924892 1250 668923642 668923681
    0xe03090307120f140303040b0603160b0a0e0a0f0801060602070b0415090e1609050307120b1003080c03120708010e270d020703050708010524010201140901050a050f 72
    0xca48034000160b0600041c1c20290781d000034040c100340102e090804c2c10010156210301d1103050b9891155032040e040c16247c0b1141d0a403d4030340d41d090f030002d214040290002d002d41c0e103e20720b4820070f00910740c00054403401b52503102480316501a5001e01c1088820f000d807401402e840d0001308401d61a000d0907908911840c030840d20300c216403403107500c05a0f1107100030300001d000115806005040203a110b2582c070b038030810b000001c680036000002d468140811600d0423104414803440c560199130700d88030400c010080104200a11403400400000c0030b64010f040382d4452800216142d000e034160f42c1099500140502044c008400b004116202d0301c03a1a15070301c007001c006850517207039823002950303034590100001c114540281a0b1280201ea40090700000303ca004404072040140c6d18040c407400c803401900e01100402804440700040340c13030100095540507041c4000108803a4440003015011803c0d5030180f500d9441d40305100c0f071003110b40034041d08000d131100c003021142044210200c00e0b05081c40f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 668926142 1250 668924892 668924909
    0xa032a1b152f1306050c03090604061205010537240311090a03030e0a03060f090506060f010f0f0c060c050c061b191403040303051f1a030603100f0209040e03090307 72
    0x5400403440b91b00b4020755030303118070280850f0344480d01d512000d4064a0f145031115080c0d86070000000e0f003843d0003802000d0041415807907000c40c600140b06000a426a050300c5140c03c0080032001842c070b180c055802d032401503101d02c41c00313200382c1c04140102642c15080036001c0c0c001c81030045d0a495034888149504a0b039260070701c864000c623076030003141c9840c2c415403024003510b00d4656552400100d60b0081050f0b103225009503071709992191f0801020700106d0207a18001004012000042c80c004d0b805070400d0146420540c03800101540d0f100144d541c9103c0500c0020008654071941c2c04003001260381204000041c0f5034a00f4208454900038007643e607002c405412005410050603000e1215019006401200e0966070b10305414090050081602c40d040f80420703480502228240010090080c0c41d00042c030101c24481d80500644a60400b401c080d80c58000d031800350111032218131900100c48603030000581ca44856004000c119291000c03901e0309500100401007041d5800f00d20b840684040300e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 668927392 1250 668926142 668926147
    0x60907080c0901181824060b090607020d050f07150e01140306011103070f0c0e0f0a0903030f4d070501060b0a032a1b152f130605 57
    0x1507001c0038040c4210ba9540004020321104140200c0381801c21303a0b020001000d200f90404040604110ba201d03108c2d40b00b5204080c0010030341d030300d41100109002c0340010042c10b1000d042e074540078100780500f54005495403102500300910650140c607071400701344504003910f1385280030001030004129428004080e40c800000506568000c860300103c43c60851b007100c0e280c640519010000c0b424822041e60400d55100340040c0308018100fa440c400c8940420045150300d812003490007604118200710f040c1900d85030002c41c0904280f081007440c1a00c12036001003401c4007452086003d0340011803948404c1d6200300b03d4072140c418003480f003102c0080d504407592a1881c0c01d00600508203a080b0540600c800601c070740109905421104c40c0030030407405041a8480017022805284415900c0f1001c19a18080e446600601626010042d805042c91150054132240d20004490035115545844102140e44c9a4042c08904032595099042e1008502e1310000a401d808441d400703105440411100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 668928642 1250 668927392 668927429
    0x60301032316170f0a0203070e091005090d0909050601020c09042a240801052806270501200307081c0c08070914030109080a02060907080c0901 63
    0x4110400400d03082c0100d00380e102ea103402c56484030603086210b800c1c040c800c0342c5498030750700c0c0017050340062103500400401a862500441c901c01000c01403064866008242c18650021003a01400d4400e0603120043c2100c0008a000581071401542106001740d03c3d2008210050340c002076184800a4101e41e4407246a50318604240c8078101d500554007510001c4009018044030101c00000380e40c4508440c4001d0007000c01000204150f900154000884e1100108003031300b040c00071031080e0b002041c044020901e14001c4400c000290368400f20000300e10b204e940c1000c40c880203168020140e4914680800752510000034030100361059070002c5500e40b880c184c04400b130104125507119500803081c9448400304001c0a4100c03112401880c0315a0030400300480d050b01c2190440c2c451080c0d07461729061a8180b00c030304090404800c140c01c1e05903503284528404074402c3d402800c440360042e8001e04151411001180c00c1a1440e171200b1150b9202d03407a801c0d80c5540707240314030b4150f414440007213112108 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 668929892 1250 668928642 668928713
    0xe060913090f170909010e13050a11040b060f0405221b0e191a04050a0e071b05030d02090409122d021b030a0213091106030103 56
    0x1080c02280e60514000710402005091140400d00d50300030210031000000b04544001244a045425580104a10010700000e0b004105640e0445500d4850746d8800c22155682441d0880e616015907103070343c540090059a20f0302e4094006222000d4a266003800d030707882030130401c500450042522a0825174103035080020340c1290801001950034041c80030307001c1403100b0000650250310780e00019004030545101814036903ca04011b0a0803003600515600c1c1c45080b041c442401740c0c0014141104200001d42d0780c1d1003c00c02c070090b241c4444480c20a00f4007a9010b0009039640145c00201503460041d40c001c15404800e45000116900000da80c81000000050080010880c01411138040c081898281a03100100040f01e103090710500750300041414140420f05007200d00e01006030b01c44140c0050629802c88201c601d0440a07003116a10103030ba0340054403a821240800358020743c1c0d4040c81c420300446005628190800361040ca285505680315904490100b00c4041000701d1440340120b00c401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 668931142 1250 668929892 668929909
    0x1b15150a051e041e020703030b040b01080406091502070507050333040206040b0403060c0215280e0d120b060307120b0a030804060e0307080d21020405030601030f02011e0e0609 77
    0x40560200c60344c0e0b03407900003001c001e401824003600000c1c0b03005c0c10407549051030b1041c00009030058441201aa550740d035000c01800100d40116080e040e50450744924401c4e500103800c0c050b12030000b0b44601820302c2d081c10304d0f240180544415202c80004130340080c06c0c0900700325015405504002503030f603480340007080c03903849140e12400c000c440008001003800303056803090000d00c0e01c59081d141c282c1440103440c107030b100068560164036642404074032000089429006122000c0700070108041c566186114103008000300a40c012881c003011001c6005030030712030030280c46000c0303408a045003000000101180340d039032a044402960b950400d040344d5140c0301c0c02c070300556121803050303681d60311640700600041302c00c101a40603200d01c150200d1342e95408100d9205a65031942c804000044000e005c1000c40c900b1035221050507070821002c11151018014180614061000c105c04020244001400d03401c0d0180504c0c2d03003100c003540800e4200d07404000e15406c1c0c2c60032031f04a6200c010100000d1581c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 668932392 1250 668931142 668931161
    0x7050a02030f130503101116060b040203040303050f1b16051005270327010c120c03141306140919030b0711121b15150a051e04 56
    0xc00000c00c90303540c0c00e9902d0032610f0070fa550641c180c90b5050040020711055841c1061074001f06d58087c00041c01d001c0184960030310080c042c0402291052040011400700e030300903101607000980b2039080081403400078280035040000d030210300c05102a058268001d5020b0f90180d948030f110340741e03003080610504000c0d034220614002030410450624401920315806002d0303181e1110030350491204281107012003507420345a441404041c1c1032600a400d45e00c07603d000b2144070305000c5e0100d10a000f20703071110f48505100050b502c42e501c09030040c0c1800b405203000c860814000072010010a4016407001001004880c0343d41000c210207455032010130518003c2c1400300d0b400205508003400e180d0380e025903800490740600503d0b505501d513040d0845401d0442d812100c44c1d40d102116416810344024000c00310f06403030f01011900c103185541c0007810a01410b00380d1a00e0f890343e00601440300c501440c4d20018810403a07034043c800b8030701408a21202203030302003486814841584460107440341c0d001038098 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 668933642 1250 668932392 668932417
    0x9020309010c0306050105040302090109090206070b010626010320030f1603021206010821040306050a020909090105010f090905011d10060602010603030816031407030b0f0a030b07050a0203 83
    0x128a04182081d000b010500088400242018400036481d400740040310203481d0003030700400e2943e0905550601801d0480b4041760000c6080003181c021034107203070940b03018200b41e83c1c07503258003018160085022000c80d040a407006100000400000c0c0280d080d1003c60800b68941d580c10048000000342045070400c100c0d40640074208400c034002c40011140c5003668422210408500d010310082c6541c0c0d60240145003582e401480000d84841240005910b0303110140e14641c505038484d60781d14243d03081030320310079100740e000b0039080528500394032550b03880341404000700107640c0b4001c0046001f49a621518015039503506044003804001e4101da95413004142400101c0c07910145803544c0d41e5215030214076041e1901d04003140d00c52041c0240300850750107503039001d800e80320001000207802c0d1200c50003051642c0c50003c0a08520403070311843c03007503a503524002759204030070050107840c96011b101180b061a00303801c2400010b03800c05030303260005100c1c0b030f1454503401300d40020307403443c4510f155440d0b5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 668934892 1250 668933642 668933647
    0x1c0f0e070e09070b1b01090611040e09010c021f06090504030c0311010509030711060702030d03020c070f180b01020f03070507030611030702150a111b251a040902 71
    0x8205100050850469082011003050703039030750700010740e200e102901404809030700412031407520b41e41c8032070000004007080c400090b08510980c1c4a07000c4030000d070001e44040a01103010411080ca80d034019a000107a10003d2201e0109020003d44602e10101020307205107408038039102181440d03120001030218205d00300642d041504001e019070040c03c80840025500c020202c03c1403d040c01004d0081d0071501c011800c01c1d0b41ca944034401c86010800003908403105211000c0542d03410000307801440020303200140c1d901e0010300b1207030074644182c100500390715400404200c0707083c0156490211103082c00d00042c5c0b01c0c101c9030040b820280c01c84446030300c41c8004101d0906004000c1159000ca0f40b1a0390104050f020131000201c0314001100c00101580017400d030300c1c80c03541c0d0001d0116072056860341c0c0000d604020480c4000241c11400c1c1c1d001005807202040c06038081c080200301900c1580c0741c41505503c041072812840b019050003a04581c40354019840002181e040c1550058188c40c10150b4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 668936142 1250 668934892 668934911
    0xa11011b080d050402030f0a0309060507060e0318030c0607020d060f1b020619050903070201081f09090512040b041a1c0902030106050a181a0d08070605060f061c0f 72
    0x40e2509540aa220307000340e501041507c1c000080e00c1c94400d0b41134403038a150318134003001038a05822141c0182c50640e292150301001c000c06100800b10444004400c11444039036405042c41e00d6100c00b841d07409050100802800b60f510072450841180d4420800308031001425035240c09020803101c498008107032401c4000c2600d40110b6030b00c1c420202e0044544a441843c4400c0080d07800a9814005a404c10010500035522662400b40e0080c0000d441d02058019402d0201c04c5200300c0d03000100340d6544424031010098140240c80405500f28061410242040e0300455584a50711518240c64204000702c03108803500300c156000390b2202c8000d240314851000b5110040c01342910100d1103035103804400318803841c102080d402070303400c00f4410880c22a00041004000c1411010300118984090300c0900c081d41c4102c205010184220381007601c81860b0301d0a80d064440192200340704404100401e8210344400e415207a01c3d000308084801d86034841035540004214003480400030b981030000d0203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 668937392 1250 668936142 668936167
    0x17040510090f031205010f05100207230a0f050907110c0301050a06030516061d0f030f0a030807020609030901080408070b040501051b030f070e0303040b27030a11011b08 74
    0x44002d03001e03803a071001c15200400c2c1e940850703101340a0300c410309482c00030903c0300c0d091521907154070300c040f40105c54070107880b00405c800d8400d05050340da15040c0602c0079022070742030000852006002c6841981301c80350400b40080c040010003402d070310400c0390900c030b200341000041144180d5a107003d002048203052440040d03015000c90300007640d091141d0000070481d0399003020355000b29010f580c0c4241040c402c03000b00708003481c0e510107020f41c001c4006445510302da80c24881010300040c0c40004240903c2e907403401800c001d900904a4003503410003404c00110030300101c110389803001d0900c0c01800310340d240d01d4442010700980a001e400103101004001c10080154802ca00883e0144004043c000d038100c4254074904c0f04031031000112101902091005000b003418490440008050b80d0074035850706004000c5803c5014140da042c4500520400300d9010030a03010751004040d4050413480722691100d034188610350a50a04204001a20001d40d0b1000c407050242d4942c00340f0070503661a81c44008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 668938642 1250 668937392 668937413
    0x1506150d020c330c0d0e071212170c0703121803030b0d020f1005040806040305070209060904081e0c010e10050c04150804020f090f090c010201020a1704051009 70
    0x51040003101100401c0038060403040ca840034a83d4807a09a50f5550b100c031103080e613400500d070707002c5410b4071450b40d180300640511110000d0203401c0b521010039682e509021030302d154030713621074024003c088003400001d41001d101158071201c0694545c2e50386041d840c00310b44442090001011242ca008180300f01c064203000f00300d01d154003a80d01401076007001020403621800d40d0000952025407588090f00c80d04042d85011480c0302c580c00d00b5800c050313645010320b0402008440813000941c00007842011840e01c2d074a0290071410568424406140595581003644544140c4034450061100d03142d1216111908951044401c01d0013888200111018240c1d100040171014580700c3c2084002841007800303d0544007203440c106003203000c0d034050000c15184180c0c043d0041e6001660706841541e103071681034405000300090704c01c100c1140b4000c0800e60411440017050390444e4010003a0088480d0310000c102000d680000034a10746456524150b490001d40c140e02d01d01e51401e080d42242802001200c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 668939892 1250 668938642 668938663
    0xb1504050c0a050405130608011805060702070e070c0f05030c010e0105010b0f0403031d090f01530d0237110112060b0406030e1506150d020c 62
    0x1024480c58554058611550090200501c00504140003c2001d45042108424107081c0c0010018440352074100090170350304200359000c21140c0c404480800c20808100b00740d0312100354409068a02e08200102e0b081d0130025200c28100b01c181c2c0a44000d101c18000f118814540c030800b204d98903181303182d4050180400c0b0503807031400d518000002072451882c0044541c0c1d503e544d10210b143c1400e6a500f0758101c914403403e5507000340c0c544612402e50b201c603444180142c02040c000081d540c13420100a800c446031140c1c0404900d4025050482000040303000010440c15440b800440442c40d0081d031205000405420850712030b221449588940120340da403030042c0c8541c100800416a07103009500c1400203441d00307118080442100c1b011402e00801c00039000c00500d00608219a014041c1c4140c0b4544e411206800600003000c00805405100b90201c2c4644c0d50040d052400803280740700b044510050a16028280d11070300000c80400c410124cc80354200301030304540341c45011804940c0c8070b88001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 668941142 1250 668939892 668939899
    0x717120702010506120a021c1a040c050a060c0f02100509060f07061d151506070507060815460602100608060a0b0307051c1b06050301030308130b15 65
    0x5c42da0151200880c840e4125a00a0a00d8442c0400070800720b005102d510000d845000341810102d500e0030801d4200e40c0039038009d10124030594184810131101030701c15842001030000380003012000507000c03480c4c640042d4044441c510355500c1004180c038140b080d031406070360007540083e0b25a480d4584101400025000701010803425402051080350102400e901e8551648514020105403010a240551010310150701501440c10b64001c605c858220a5040f2615001800b05008055100b980c242c0d01018090301c1c1d1041d44505404076440307400d42e181817030486840107049010340384800d00d100540d50500c18a850400503054440c5400341e03c0303004480c0180a03c400c030030384c40343c4240250400e48480c0406484141c07282c00000c00107201c01003180780c140c09602000110740d512440d4854902800c0314440b00029160b00c0c00407881d8101109400007594203220a00400c0e038880d0503241500d5040c20070100c1381d21020132001242e8000c1400074500607030038003006000c0e00d0700c6111112680d03094 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 668942392 1250 668941142 668941159
    0x9060703050d0b06040305120a020c1005070312051306020f2101140d020f0f0d0210020d031b020a02090a021210060f0c050c01050d060918030f090501050717120702010506 75
    0xa0b04000040c890346c0b201609562242c41619405010782c8000c0400600900459110200c1d140100b0400703075040360003401054010036a0070603d6004003030400c00c20141130007008240780c0625410481800700a0141440380e0100d49000c01c0c510a40480303c252000041c000e426403004140b944260809000d819105110802c003031500742444400340d00c007254007d001d40c8036440c0308000e000c070307110040e01030b50341c13208101e1003001c003684800840343c009042eaa8090040c2c0c10052101a042e1041001c61500c00c04000380102891030b40070507030362103840d412038407142140c44d0740c50004040d01440094a00030601c500910400c8000d00844104a9201d9103c41070030480c5003c0a40e01c1081c0708030003030507580103030004e007602c0d610603802850000c001000001e860f0391076650890031104204010200c4068000f000400c2c15000720780505842014900406043c0c00c240000b40580110349000b06048090310403030844506d86003c0d00d1000074000440040c901d08500028080c0c04103441003801042c80 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 668943642 1250 668942392 668942411
    0x40507051f0509090c070209160f11060c22140f12070314120705151f09020a123b1b0118061215080a0f0809060703050d 53
    0xc1c06040c0c0c00403a86480b000c2c01c040f02c0e03c0c10f000d80c2941c010404540100200a548010384e919960f66000d641031015800010740f1a00c40900403259941d212414042e0a9402e2500b8400000d110382c2d01c01ca001c21360945403020825030300c0027120b4000c0d042025002ca000c0224a8030014810340c40e0004084a0350800d2481d0303074041c0300501420301404136140e0032211003400403d8040c5504500e88046008540c6800020600704040b5006100708448542022000b100310550540b4115042658001043e1300046a00c54130190001907101d41c5007070780d4010400b0716400b03000342c400e5411080843c40a019200c40503100d82111031131461004854803100028070380000c1c01d1042100c240c0540c800a143d031880480201010741d0003100614100a00c12840758424152071072020000d148688607a104d00544c00b20f81425500d8103410070016640d600010000510700140c00c181a503040107800031030180500305140c540c460703514003507000180040c02104150b802001415404603c20f81040300201 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 668944892 1250 668943642 668943679
    0x6021507030b131a0d11040b01021203010e1312120606030204080d0503040c1511190b0408071b12021203130611030415030b040507020706050f0a1704050705 69
    0xb032800b6503040b00310005002101c030b005070712850131070901c18001030080c042c0310700081112031604000c56401d81c8455200040d030415014258103c142400502089500c1c00c2480030b5034013052040c0f605481c00000825442e10801034040c61031900518200c004004100e8041c180004001002101c6442d054000880c1446442554191400b100107041a01011801142c03503410140095401800764180081d2004951442064840300b50310b40c2058141c81450041c18034003003607600c2e408146040c20400002c0c08011280b90710690089a60341c442406050540b505004600d207107000340c0a100c400b0030301c40d04541780484401e01c21210401d000c10600c0030325481e4010b4618100044102c00e409000f020b00a504003001541000e0860b41030a5481d0804c0a1703a1094500800100780d581c40e281c1d80300e00b02801056408001d5000401c101868110000c00c00d00c64415146040d82000c610421002d00c61540101f4508161101c1d41d0b40d41820b061058441c001442028442d480d1345141c48030740c3c1c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 668946142 1250 668944892 668944901
    0x2060d021209070302010816120c0905130e060601030f0207050601140a0602030c030a0813081603030609090302060601050d020c07150305010807060c02040906020d0903080609090f060a020702040b0306010602150703 94
    0x26810b1f960b11107540c81d240c00e140140b0507120380100600008004c0e44038003078224490048815850361715103401300c0c134000138000700040e0044943c3c515414812840880c10002035520b07040138003845c0005046202034a550028004c0080003002405400000542d00b4540000c00d00041e0080303480401c066a2040143e81d03030320038645244025001404140b00b05130103a0f04051f4042c03a002c0001502d50201e684018547e0b01130500c5041c5007012250390001d0581c14426007000d000300d050208041202500c0c0690781d6000285124100403001411031090030350340d0182c030042c0c21100111404ca640317841202d1045540000020000ba1509000040001c80022440c0c11038900f0340342c41c1030109058003400007410034083d084e0f9503281c08001c40341000003079114035207507c1d010b960303070003110f04140d0b08105102c80050210140da60208078284c100c1c1d42c01080c0e554018145580c0182c0e5601140b01080203801c3d904816603140c0074103000000c4083d0045500035540506403110b0100b6960f10b441942240d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 668947392 1250 668946142 668946149
    0x506030a050a060b0d0f0b160509030a0204050a1811030c0a120b060d0b090303100e060102100203040204060b210717130c05040f0b03010e0109020d0f0c0302060d02120907 75
    0x140d00001c40031020030f46a81c4800ea9084e405170a01d114000b07543c84428a461040004552082ca000100241c8000e10040031405103290310b4968a858800d00011341d4844260001070300c40c941d02d030046517504400d54003900d490004000700e040c20b64114203080c1148401d1522081c001e000c0d5a003515154034008424000703907003c00b44164869015910340c00003203140105003a40010b00040031502081d4491110382c42020800001e40d0f0ba45400c642107a400d50056005da01d03010507440620940ea07030007040306881a00101c10040c1c82c0c2d5030b1400040d000c0d000719400307000420000180c3d00c0003465202114211503044d0680302c12940c0710103601320b40301c1071801c1c0b500c503005807041d01051184001001d260a214020002007442c42e07281c0c400030341201c00d800d1320301c180c8030342e81c1c21400803500702809a0940401e005008221460307041c0c003c6a07071b08914560052500000012880410440302e004502468018168645603800c0e0301c400002940900b15584c00803040c0d0000a841c000001440c0058 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 668948642 1250 668947392 668947403
    0x40b1003020915030408300a06060f080c0a1b0c06080103230a03030b03010906051008010f1a150d0504030c1a0402030d080a090b042a0b090603060f12070305010506030a 74
    0x70200e20204404a4136059079070321f1009402e4481801e5601e4a035034109000b03d8002a0018045142c02c001410040940001c44c050146000400c40542070010668a61400c0780c02c2c0f802d1002d46a83c40301c00740e029000340042040700c40100100e5131640c8039220034140c1c0d01c90703080c2030300000780b0040030a8008000520317846190700c00c1e8185000640300c2e80014403501009800810400441d91b41c044c10745400b1601b010072204454010009020b0902541070401c44d1144200003050700c0082c407120300307054460264010a007074803102c04203c956400720358481450b07040400190030540740007800c80e07802e0041602e494903040034a004000b03520304c9090142d40c0c02801040500c015800c190341d00f0301d00034585c01206507180e0760b03400840c203961005c61085114505d0f2074002c07905c1160345001d8a17980008070a0781d0303d501c00144034080008084070041b100c1124029129682ca01c0042c06240c00c080c0d10a400c103000c07800d002c0d00d4240000d401c0d429284508000c0c0711a40d224001e0558070f0f074021801602 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 668949892 1250 668948642 668948647
    0x30a141204030c0f020904151505031c2304050316180f02041211030709050f0c0c0106090e01090b0c030705180a0b0c030a09050d0305030411040b1003020915030408 72
    0x180c0a60607020400e4804e000300c5200128039000100c82c800211010f6602440a820904640609101d00e58051036201d210000320b030304000c0484d1f03641c2d040f01000c03a810005485c010000364041c88003242c1100446007000103a050700904284190000c1c070a2500901c00c03a91070750310b101241b26005041e00c40041560750404040c01c50752000d8a40b084403414015070030031000c01c05401382200084018082c9040c1c4400e000300e101490300c0c110507a070016150524003414060200014039181d0341100880e01c2c640e0302c80000317403807890052001da405040c80030329001d82c01c1c1d0740b5001900301d00d072554000d81000403a59640c0042811500c000c50388200010f90401141c961480603a0904144010241c5218942500c559a188040c0c1c000303041011280d00105500c001d40c2e80c05024000501010b442c0c100c0b01e812244e4002c0c001d40000350000348000c0e00c80c4587c4207641c44541c4103125486000f00301da0202e041440300500290300051580e80079242440100012900c800101c0c3e004640c00b40e121031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 668951142 1250 668949892 668949901
    0x503130c05040f140c07050a0803040c210201031a030601090e1204060306081e0604030503280e0f120a050a020a0c08010609050a050709140109090e030a1412 69
    0x5a4102019004859418584101240e503407154030590842d21070360f01001921000100c1c07044009000249030500d807420410a50f80094400b0900c80c1d02d9550150751076450fa11245800c904500707080d0049800c003801c07410414014040000407030b103801c0c002e80b03040140480a000951440c0120038010340c02da03000c1c00c0104001c0b407150388101400e0982009803645541b94a101803000d42c410341c05000001c1c1c9a00050021420a0212850043c404030503c0105031407030b051300307885010041025043c02004000607880e408101110206500300c440e000a4880c0b8110200004140a07541c9002e5807081848405c65103000280d04440607400350081820440c409074212440da1125890b102140902109400011048403520001c0c00403240041510b505118600c003c50b54020581d040c01c03428241403000c1e964011900303200b41e4480c107032000c4c1001e481d04c0044c0c80c101820303401a00c0c624548800c2c070400c0c120202c00782ca25045d26954900441410b5501715140303002d25428986548680700114 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 668952392 1250 668951142 668951161
    0x3120601031a100c140601080c0d110910050d14071e12080405190302090604020a0507120509032409120a0302180a030303020a09050105031306021e220509070503 71
    0x240c100401860540300050700303a560a43c0810080c451601c1781e9010400600007054144001100c01106031102402d200190726184850303d104011140110705238004545107250300202d010180002a103613203900f500c0c51074545981d1003942ca184803a4000c81402080214075506801c40da9150300c00c5a028660410200c5a00c1e00904401100d1088017000300092945a03160140564045182620806c503d1801403062a1500429103403107244100500c0768031541002c261280340341c01101e0701850011079001135030309200c0d40709001d505119603080c410b6280720032002d014160008440e03444c41510b0301c03480e4668962004050b414010814041c20a1b02442680506440403040051040140c1d144000c1a107401d003c0c1c1007a40020380001d441c0c15101e8001140c040240f400786060f1b480c518040c4000f400e10100c1040c001c1c011600000d16036628010240c9212a10340c456011076925031030b18510340b10b0110440c1a210301c42c0b040e03641c0015a80391224941c2d106407043c0e11514910380c1d0f0358182 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 668953642 1250 668952392 668952409
    0x509010e0418050f010c0509061804140a090c090203011410030b060f0403032d1206090e16060c080901080603031b0606011101090f12050f0c03120601031a 68
    0x941140d540e0b5040081034020120140d040b600460140c00a10600900c0c0e50070b440203400c17510148a001c0019070740d40d49804003101ca105001000d2204402031030f03000100649400c03002c02c402c2007480c806014103000c4071f0f8441000203104840380c0c03d0090b030303a42842d001d0b80403d100e410005101c100c03001c919400c026090032080c1425140016881c07614500244490300094a8400d03e424046014420141c01c54001e00300c028110075013104d01e8111040d920700c030701c074111044000c10108404441807146240c1001d00035107664503051003400440000c0380e9443c0c00100900680504000700003d00c036020303610030b02045400c0a0024030380700c140d2005640c900d5024000130740600c000c0108410150056055558172084180a0421410440001800100300012480c000c3e4902150000081d180ca070444d84101d91181d411a0b2003020607405071b4490041e0b880c1c0c100417220008050554141c00310060003042c50900400500e40c0380e00703004404903058221014140c01101d205c860b10b51606544 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 668954892 1250 668953642 668953667
    0x916030203060103020f06071202160e15060d0209030a15061211091008011b030b01050c030403060b0a0f060e03070b070f06110c03070f05070614041206020409050708190c050901 78
    0x103003860715001d0b60302c0015510107889c5100c01600300d03140c801d0360020204151801409169070103c2e841c06e00d40301c05101d047d98510401c0c0300c1c400000c0c00925140050b01a100c224600074180c83d0314a80e03900346040352030230350442c40d02c820b46025000b1512083c800940a1a950021003030144410400144904180c01424040010802140004141c00240188844039015070b0316002e5000b88a00c000c0e040e10042d0414605211003400100c1350941d00005880c11250031007008039000391240d002c20300b40c6600e908106180b41c43c0d41008213038140c02440701440308209404803040039650740806011400ba08900070b01000f001d40b0418049255500a1032003a12520525494040424101c9255601034041111002c980000c0d0320300b03215040c06405c00030101410401004c2c0110700e40c0140b0f611513401518846900103a2040502040c4c1d4140c0e405440210000c020030f090251020744001d40c1160300c4d081d020f6080ca0004c202c104c05018264840505031281418111102e005480c8021042c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 668956142 1250 668954892 668954899
    0xe060a0905031201061106100602030a08040c051908160f050907121505030c2b03110a0b240102120d0209090414100c201e060916030203060103020f 65
    0x110b483c0c014805051034001d00407500d039440002e80307000c881420300c2002460b0100e800060001002030702d8012007100c400a9061a0014595503949072120f1307028155007200d50400040920844100c1640e580d6100b83c400700b07404c81e40344180413180101d8880c00c501500d0105401c040080100e0b0070b21170182034100d401404c201d00c0c92070141007010122112802d42c000c0c80c803206c03d03040000d400d052003500d940410a540942e00c1c2604030000300036480c901ca20a113090040c01c030040c4c05042c440d10f03035062403554250030b071241202d850030050302c0454140ca40d0a0415500882142207046000c1c80058130081a005480c402904040c041d02a402402c5194181502080a00003c0d940c0c044140e1040788128068001c6d8440014a941303400015420061424075200c401c03078045400c152179600c119020403411301c144130301a4110381400140402e0030111205407498090012020800700c0c4075002c3c0380200c0307074201c80074006840b902140b4072010b50960424001031000d400c0502c0310084824014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 668957392 1250 668956142 668956147
    0x14160801060f051e0d06021c0902061902120d05010501320c0703050f0a2a090506011215030210030c170703110301060509150c0309090a0f11070b0702010e060a090503 73
    0x1030081641c4504441003180c017294001110702342034050203c46074400801c04010400d441680d404140c030f912848145040140d0702080b405060b40c400c0025201c4280407070303440303611035001c0d241c20400740c8001e02a15000c1903280c0000e000010100403c41c42104020b45080444142c0c03405009290f44084580880d0780107141e804000b1440400900640030326401c0102100307003a40c10550070b483c240c010701070100c02600d08031000f0640c1c1e00305a0802d489418074000b071951140001a5400c0e2582d01c00c0d4004103080c01c0340b602c8031121007919401149d0080d9500c20500d402000100c045403080d102003404a02a440d01002d100710304070701158402500c0c1000607401c0390703450b40c0322910b400980c42500080e000043c504000e080550804c0c001e1b03100600a142090095080c50351030b80904d40400b80a01300041c0000c004c2d9540703402640e0b482c0c00c182030402040d18400020b1081f40d0140741c096030a01d144001040500b0302c14805d0804852030800a44082c1d1903000a03440900341c042016501d51105 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 668958642 1250 668957392 668957449
    0x30203070b0603071a0d050105092430071a07030305090307050f0f010e01021c021c0e031215100804150f0605041508060a0e0102040314160801060f05 66
    0x920380c0c01c4222810b42d05c004d41c65601410f0700d801600c00503080302d4001c564800511051602e8a10180b1541c402ca100001e5244640404601c803002e81c0700450f100490760392180c5442c1c4c100c404451400841030410b82f40c03040c0e01c440f10102400301c0c002c2c0c4a4102c4c0b200300028000f10303100303600c210781009490058034034107006622254508015500c080400c0c2d0440710000c3c40c050780c244644010107074803c00130f504040080c0320007210010f034502d810b061141c00090311503084c044450420b01c9820040d9003001031941080c803032640c035000030010762801d05401e00410800c060141d01c101550800501e46025611140412103d10300c029100b150002030300d99401d18540014000c98501041da150005840d85c649401c00c000d4851130b2003601411034803280d0034484c0031004900160311408405000c502e0f0041c4030360141c028460f60b40f01529030010520030720f403071881c0422500d2048600c070702a6002103071a0b0016a00300c1e5828411040d280a060404004030b040000e1031309020b0031042203ca00c00b50700c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 668959892 1250 668958642 668958659
    0x11060c010b1201061d0c0d0f02130e1608040b040201200a03080f07081005040b0d080c03090117100311041d0708071e0302132309010b0d030203070b060307 68
    0x1000001185540d440da182841000329900800c0c1c5c240041d02c448003450304040035440301c14401c0c4018003041c1525005149240c0c040c03134045401c204140503045842c1c030796030600c24003003503418cc403030340780d6007020b015007410842c0700341250f6003e550000c081c1945900c55030300544004101c90040060f060000e5282410244180007000000d4000d443d503030064a801c0081001c0000300408000511640d0800d105441d400d251441007658402e55000403071600c800c1c0000c0341c150a10800a1070140002a2605c000c0c0d808000b44c00c0d994400c2e25210b00c52030038078110845842c011503d2000301000b400042011401c0c1004d404104135010f00300140c070b1940c891260314018641c140c0071200303a1089004002c1c001040000c0c034000c122a034001c0d04010205005a80b402100b03100c0a031058102030411040f40795150f21000d428240440c0c00d403010b0071100c980320300400e8100d40603c2294038007203081805090411005c044258168055490107455035981500c002c0060086074062084550218407001c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 668961142 1250 668959892 668959909
    0x215030916080c0906101d0a1806090b060415121407030212071119210f14090a050d1a011206060f080c0607260a1b11060c010b 56
    0x40b0700b0302a2402c580504148495020042d1060340078038050704415000941c04000100d141000b07507131003283e192001c1d000850885903900181d0803000d0400d541205000b9990040e02242c1c8140c005010f18030048003000b4a5002d2440781031003159640b407d0b62803c1d17102c0d01c000c50380b2025a40c1c0000361004561031135140c040c801c039100d00100340d00007404444090318800c9594089242d28004254042d08540c00351501c4c104241011020301c40a2018100302182103013403040e10208190500c172400b0098014503070740b03a0310b0018000c1002040c401d4000c42c1034404039240c0308409021804040e14100c2400a040c4454105807075480f11110316501840500d00064000c2011032843c820100c0307541410412a00140d0240103ca10340440800c0b4061000c10043c5400c2001c840c6e44da100c010074107065000103510035480041200c08413066015104040c0609405c4000da07407243d40e941210049581072903000c0707102420811001003081140d18010008141201c80c450001c2600d2390300d10003040720b80e03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 668962392 1250 668961142 668961149
    0x203070c03060e1608120730140c0601050d02030c100e0112020711040203040201050d09030503010306060b030f0109020f0408060a09050c01091401050d2c060a090215030916 76
    0xc607281c1224500c185001c00070003207061441d54105101c60302c4c018107640e64a02e03122017840450300100f9804140207112a04040f070310307051207080b0825a18230b5070092000d102003810a0100b010f218009500008038010b442c3d001042100074110399090070204a0700d8845039008036030522a0841d43c0401d521040e0821040070640d07112251403000c50300001d061003210b00b408031625032040c080b01d40456a03825407020307200c80c1070b1070040c0e0780d80b96400101c809100380c0703181d2066203041101020805900000442c100d901800b4100b1881e030300d0351440301c0c03584801c4e110003848954010050040158a070700500f40300803003160340c44c9400c3e5610780b1300e03040010441d2050340c100c4c0e40c2c0c00c240d0705010050045c10000982480c22009240c203110b03a260000074540c920b1410010040b88441000c203041d44a44061444030110080900e020560b01e1140d01440c004200349000703000c00b0070801c003514000d00d010035500800c61131312100841610207198100800210292140510082071682466920381c0507 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 668963642 1250 668962392 668962403
    0xa031104090c0908010c0314040b0c0f0708041a0928090c020f0106050909030409050a2705010b040b0303070611120702150f0f15210706020c030f0a0803070203070c03 73
    0x700c03440c1c40b8001742110581010841810f00b0724821034403030301d22000400e520552151a40480d501d82d50703000210381c0165001d4002c581c10004495051192040107030044a107c09219003072025140c0414207940282e00c0141d1700a00080c091080301d804002400c0340318400c680b22550b1250380c0700d2500081d00c5a411341f0300d0150b00560542d2003007600a0041e00b0107040145c601904500b04190000e980307204511451071415564000315102000642141090164840c00c04041111042c1d5035488103c00444c21aa150710b404240c0341e541c05c0c50700034903d00780070003800b840c140901611400301409045052040f5a40c0c104025000103d043d80b8250107003d6030740c01058802103144295000b52800b500c140780481d490310411030700541043c4059070003142c00401e28a240b41d604045002106100802c143c0e01085403c07801400c10001a4003086a446a08649a00101c10181611070b070b004a25a0055040345040c64040750041e0019031b0800241c2c030441e440c084540c1c80d80e05000056030001c641 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 668964892 1250 668963642 668963657
    0x8060417042714011d1f0611012022050a05010302180a0602150c040e040201030218040f0b03070611030a0c0c170a03030f05070c1509080d09050d0807050a031104090c 73
    0xc100b80c3c0c91281c1d0040d10b80d806c1280f0304203040c00c240c00054041c0708480030050030b40ca160750454400e4000c00d00c0c070701e030b410000492580c020703c030207031250400c500004044080303109070f10b8442d07a9403600804681c0d018000740d492900703090044020358046042000c40e100c0d0300001784510b8840d400524001c040c540c2c090580b01e04c55004109a40c0d501074000b80394404280001c3c0130345550908480d8000c4da0900740166038464034481e0a08148000300c01d40d9000780b4001003848000340d103030410055081d040b4180c850071038071407005943c07100503e116030806600030b100304503243d030142d001104130a01545140c880b056481c442e59520466080c03c45020303030000408082099018010181c040c44881001e00c103614004e100200348424004000d00300904a070140080c59803254044090300380c00001191395003000e021804050014102c2c110382e90320032031480b403100c00e2240406601980c402c5da40c8900c3c0c21400c0004030041d241200c407071407200d58100000520040b980c420f1590701e00c05511a2407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 668966142 1250 668964892 668964929
    0x1201151b0f02040b090f010524030a0e0c0103020a140d0e100b01170103210509062106030a02091305030d090f05070503070f0e1003020a0806041704271401 68
    0x81a10b03113803074405004078545403d201d9006448020541541d900f80d9125041491019503598051043c0400c80c4550100000b440341c100202e4120f1000c2d90900e804a60300b03d040c030300044040f032151505110010742070b04016081d803014100145102c001c40140424004401c09a06044c000400f4086a120f5901c41c0424180d58018404d00c40940802d03651940540c55070310f44400107101455141b0000003603204840300c0078040e4060f9a64803002401c1143c548030511703206e602079100e200300d0290202c0084001007040c42c0004402c1c5519a0160140941d51a042102e94034070314a650129078601050046044640700c82c8220407009004012100d480b5006041c034900306a06504881e0080d003181400384140746014034030900700c500c14044040c081e9070742c162901000005810081d48080b0034400043c0584001509c0e500650069880c20004170811900c0e885500c41d0384a00100000282e55000d02c840e14038035644c000c0c0e521000003044030103459180b00400308098000008101c140c00303091 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 668967392 1250 668966142 668966149
    0x6060f121406010605300709030204060e061c060e0318090a0e030a0c020301090c0605031801060302010219050307021206010914040b041e05121e1201151b0f02 70
    0x440d22030510054042c950401e0380041c4039108155004a0000c141001174104107018103203a07200c2c001b032024400381c074244140c000307091b0009480144e01c110700700305000c11040c40081d0401d015204c000c0080030000620300c089000b158a25005031000d60307803994406501d030300070700c01000f20302c294a040d1001040310400b044400320000c1c2601d40e4291070045925000c8000004950f011489400e041d210f2000a04c0000e0144c07542601c000c200081c02c0d00000b84031a0010099400344842c000d2140250301d10313040745402c03144c05101c0039005a10401c0c0600a1301c2c8242180300c1c0e114003440a9918014007a0086002c040c0348103c40810f81d4400310040040e07080500c81c904044c4030080b680740150906454510a20744c1c05040901000da03004400c03904d0078003c0c90020071055205003910305500b880c9484038102d4014070078441031402070321342d0723014982e138440d08a4481c9110f10708182d410341d00b40f0441031086243ca0b00f003039083c044954100c016000001d046040c543d8800c082d1021181002d01c1231 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 668968642 1250 668967392 668967413
    0xf0106081306050a1e090f20060c0607030c0c0506010603231e01080d0e1302040e04050708010c0f0f0e010e0d0b090111030618190513020916091206060f12 68
    0x340c2c117a403610046100262000031613906141c0c0040100c803021848603440342030350f554601e400c1d82c0320f0030010f800902240301245062140710580c070104806e42400390143d1b10001c05900080c00d075000500144100c90007079011100701c50320320400c1042d0b80011481082d80e82c6003900d100c0100d00002c81500035810410b0b408601408125002d088400d110f2070b0302a040b054201409031140d10750541407458003c159058900074140001c182d6041d05280c1421900e418050090441c95400e001d07500180c0c0307008848002e070101696403825030070015064204c0d22154000d0085041051501200c1c003070384d45890a0200c1c4500840d080c9429050410b101345c2142d40c60251840f189905204000d40340c2d03038130500303002001c00c07020000c0c401d50b890581040c04132020b000c2010310913213000e05000009100803070ba80201442074a0050081c1c4400e44208108108803e07000b000540013030f81070043d41100e2820003003852041074003142ca01d03140d00220075030314071503000000845840c0598405122503400f1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 668969892 1250 668968642 668968691
    0x1e030105072a020607050d090e01060c080a0804020d0215043b100e0f0a0b032a01140a03020c1002070309050904082703150f0106081306050a 62
    0x8050502600502540c0032890002502080d41d800580c825001c3d07440311401c0b0350030340e0341c02001d980c2d0100d00b104000e852501d05014101d0207116550011401c14003407207003180d800c0d030090801410710446040c212441e281c010030480e080003444401e00010303143da800010000500d0b419182c2c443e0f040004030100100818480046560091410304050000482807000c0c4840705414401c2a9120918180d94031781c076a000c095045e0308403080280c514200b100403406204080d100b030007a52201e02c02c0642e140e0703100408030500401804000e02c017803000785085c0000d81042c145000710305d9a80d0852509904000d4440c00030980014500080ca0018007041d00c2c0d94500e401c3c01c50034200395440047c50381840d8040c140c00f4104010101d0b040c09009800da617024401040c07036801d1110f842d5010000c4106891072180070f031080d8042e03030201310000f01f2141d00c075400107007100015a2030b2074000c849424000c1d0500005803010544a00802c1e19400745130f108119191340841c0c4416441c01403601c1c5c0c1000c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 668971142 1250 668969892 668969897
    0x8030919180c090b07030c03120504230723041d1005060a030f060b01080c0705060c180319050606090106171005120105010e010b0301030c03080f091e03010507 70
    0x2505200a10820706525203030000c1c0074000420300300048055844031990b41144500c4030001c00c0300380815920020458403103104e59280074000b548038680c44107441c03060310001c000310700007e100030b17003001d001400d0700400800904031044255551400b0040b58a60600e806413025640c41c032090a01f8140100c81007003039900071154208041500b82e0303031250340c2244181c4280c0d490700041640e03940d46485510143d50424405a000c040c90b04d4040c0007802240c2c03186004c103020400041100c0c0c0b40d54144e982040c1c000000d4100307540c41550150300c42d80101e8407602c26001c0300d45002680c0d18201f002201c58100703401d0b840d100c00c000381403852512000a000313610507903103080144192030f4811000184218503602401103500d5081500950080b90340025400c420488802e50301103505410480c12508003146400c000c5e606c40301e020007144024000a072000004000400024000c030700209400500307856503d040a40c000000f4010081d2140d07a020550100840d0300c145107000e2181036080700560 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 668972392 1250 668971142 668971189
    0xa0b03090d03090c170307060b0a05060a03091502030405030309010e010911011107090e01060f050f0612070309020307030f05010f0504020a050d060e0f030c0d0212030103020d0212010501080309 85
    0x4600d540d80d1640c0710208020140c680c11007408110100302100e01401c00b0743d200d05040260050119580d8000b6003081d80c00c0c1d03040c4001c403030300c5081144844041d51307405420a03160407020301041d800780501000480b095000007401a400030014030155000ba840b600256540381800d00701c1500b501c440c00305083c0aa45481d000b1000907802c40c0c0c2a440344503080c01c1100344201412032143c10700b040c5500848125040401e81110f00b10103511003000d842e200641c0c07c03219030b1604140810b98180c0140980c00890400c41d1284940f0354404582e4010780e1032502154045103540400d00701041035004980300c0031070050841c1081001c0c02282c2840031140c200700114945500003038003a2619104141c05440c0300b50b091400c1c08200d400841200209808440b9520382401c002542d99000190005641c050902200d00c150301c0802c0c400c5418100c0000344e4116400c50b020850848003a52049034003c5600114507090b00080c01498004c1074600302968444500c0b2050041c241060000d507240e401c142c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 668973642 1250 668972392 668972401
    0x15061b02040906020c060c0904110c0d080603240f060103090f020f0102030f030129040b180604050405090d111515010302070f0809041b050306120102090d0605060a0b03 74
    0x1800541810540465000c5007a428a042800c020302c5640c14500a6000780420010851030010050111080588042110840e00d9448001d40e00500c28400a40d80100c03038881003851142c04216040f1800a041d611000244100c144507910f51845070780c0b5248580c010000c200c4e00e00b402003036202e282030800340b09042e0580e60b0802c002c94203400082c401d0380c04540402050344204160b1350796014807006942d0760350f1241c4602e222000400b80099014150b61b100004070700220b41a102100c107058402400c00400e60581000b10085046c6a44c0140f001d1200040075604d0b4068140038000c680058414001d01c9680146400340510302607829a22007102407040d86030329500340d42c3c440d1200c4c039a0580c82c1880750049010b03224868019110b2050b425040b800d1142d0100104000101241c042000d00c48000854400109940c00074020034424000243c1ca41015800350031244074604c001031524440300001303410a0051803054840e03680d104204181800c0040c440300c00b1b01100034031207095180 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 668974892 1250 668973642 668973677
    0x60f1505010e010c150908120604090c030f1b03060e10020c0d05070809060a050a11010605091305070306111806070b04170c03040b0309010c1103032a0705011506 71
    0x44010981d410090002000418416422041c0e452040c0317809062021b0081c03410b000710543c003e844244000a80c03800868103526081c0300b6081c0341c940c070070581c1102c47c0c07070741c0c507502c0792411059002e0303820b41d940c480140054113040105070080c3d03109401c0001d10101c801ea50f20b242c51020013500900510410003014085000124498090b0b403514101d682e0342010b18080540e030050340c0c0102e8101a0110310b070801a6002400350031280e515a840941840400d010103007070711041e2040d184c208501c8004a00c0300c6000a0000300601c1c029422903414554035074070103080715002012401481c4c404660390510140407584210b0102044491a00f0080e041d29420800800908018040340050304800d03110349003031041c0e40100d039100c002d49450f0341e600e540800703146c0e00c1166800e0042d481c0c000034000385402415046010b0001c1c0000b103046540300114003c60548440a040b65106841800007030b501c2c205d4000c10f1402c0c031802c004618640022420840b0390b10b0340e00000203006880c02591070300740 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 668976142 1250 668974892 668974907
    0x90706082809111903201c0b06121b091b070b0601030e0a030c0305130909141606020a0303020a0309050124090c1413080604060f150501 60
    0x80d00c1901500c1003480e008141c0c0da0021074920090594100245901485055031030001d030030100f80c40302e0303018000c54040400201c40340d0000800345a00c00e0410307000b04c622a0041900ca60000d0090345148510200644a002c0c01c0002100d01000d03001c10002241400c0403c1c0500740f10040090011003400d0710304060030038030001c1c040c0c02843d0800002e02c00784072440d091065070b405448407079503a08050401d000120b8044407024040b1741005645051520001903200e03940d9016500d58200761a9130b80e08039030326880f040950703000548886001ca2045418843c41c0750a40c03281d02c41420211101c1c520714105284102c9161007403110010401c51a1740208050101c1a45842c00594906100c3c10a600600d01d1030750180003503180440301503180941c000a0388001036031284182d1501d40d0b80481100b0f40b500030f466100000c0204c51f074684003034021805071100503c007c500e16903c43d1225a1540b03490ba0840b002e230303250742c2c0700c490419060301d0b40d11503003010b041d9800020a80724101b500180030803 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 668977392 1250 668976142 668976151
    0x1e180c060e090a05040c050d1b1d041106090a060c0b060a051c02031c031d0309100c0609051c0912020105070f03110601060309110d0b04020904050c03031605010509070608 75
    0x142d1100b0004040140060350003011781001004c1e1940301c40281003410b107102022809c2340da040c1c2050008941c0c01e81050344804880713411071710032046030b446544040c00404841030b0160481814014001107035502c44a11010384120381c1c6880f40390443d4100404126800351082d8000c00c4800424021512190004111354101045141c420006440800e1030052001941002403507900300d5026141d506403c43c016a100c0c03881014281c00021314034a0716845900d6183d980f1190302c0b0fa5203c102d03805009403910450090000052070040361b10b42c2c504141300c1d180800728a60072032189000c1c0e2500103000d000505900704d01c0c0503c8145c0d950001e455442101c0c0041c01368a03101e01e42c81c041507c14030b402180600c090007036804950f0f444101801a110390181140d400144404000c502c1c01c048018158180e0040c1d0a45041d403140e800f030140b0824050011354490240700c8152181d500c00b04000c0000c5821041590f8006440b07060003401c6420140c1068002d40111004008440c1d104072455000f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 668978642 1250 668977392 668977411
    0x18041a150703020a05070303080105030d0315151412100e04031715030a03080108150907090e07080d050904050601020d0c080a18030b071403040302101e180c060e09 72
    0xe62000c2e0805074038082410310001c051744076132a004010181d2081d00309049440507030840d0442c0c2c101030826410f950fa00e1201440c1030350b0652040103800340304c0e240c81e220036090b420140c18148550070441403983c4994001c480803042c0340d040c44043c010784102800180491444101d940c18540d8000740a4a0402c042c02d421052820101d80300c940040c8103003508120040488010600c24a070280c4955006d01ca050002d02441c480c2150101c0d80c1c00213242708036104009000072600b4800c40c10001d140301504c804586c418294080b03030121003000500608140c0d5140c10740c94000d44001c00c426608001e000c40d04541005124078030180c1c0180603800c1075580b040c081e6403654491030048900180b01307180d100b040640b83c0400001e02501450306406840161b40d800d000790f60b8602d604002e84402d03500140140d020510703160000d00f00b80d1040441b4901d0200000703e45d00441c10a5003038940e118a080d12042418040c1d0b03040240344003406c40200032074105094690080300002c2c0d102500140003102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 668979892 1250 668978642 668978647
    0x8010609061e120203070207080c0303040f030b091f1b0f0507060e030c010c05070b16090306090c1703090a06022a0d1406040b0f0f15040e0318041a15 66
    0x500500407942060980c03080783c011512440c01400007507648d0110300c12141e05015000d025040c1e82004000c071001e40b03503004410600340b4916600c5004186c0700804040581c0610003010580c00304503140c40ca42100c0005002c00d1100c001d400b43c0c1c0c954410f515520083c4442c1152442c21680c00100b50344529401c00380000b208030b5202c1120b030542c480d0081c001b03c2c0f5460600c0d10790003a60000301804116008000905c2c503a5075207100a81561200c1180c4804242c1174102080052120741041d010684035030500e20703615964102c804031500300c40001d84000d401c0425081071030b00b005014800200f041c0d1000b460035107413a030300000040008404d032f00204611015200400e880b55103181001039404401c01108090400140b6200d21081d00c08a42102001021490301161040598050403d10072090456215071a04d2002d240c500a81d03e908103865001803010300e0428000350440580e0310880714014400c1c10b0400c81154044070301000480503041c0b01c504261150f4410860b0b0082150400780d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 668981142 1250 668979892 668979947
    0x6030b0a0b0409020402031e0c030408070f110904030c050f010b09061309150603020a080102030c0313030c30020a0f060c090e0a0906050a1802010e060409020403120801060906 77
    0x5002e02070f8401d000e0341150001040c010319403130000602004103082c2100c00d201b62588101c0c08000d110684014100030b40034405000407030355000500c03401d24810386940a01c0182e032004107641c0101100c1c10b0300481d480b69041c800b801030a0211007450309504008010889960b000900c0700038018020034000c80740c400004d02041e51542c400780c0d0300c0750010071002084020b01c09000103000c81e400100c0c01034602d4640050b03051414002d8074000c03031001030550300350740e03800b0141e8030244140070040d0b013040180007074a008200308045401c03451956201d03003c022001e0646840d10103d20320743c45402c40d404614001c001c105098501070340c981c3e10643c0450203911a0b08200d42040e020b401c900d41c1c0125010910a881c0d1450b0b000070754292151000380b21a40da102d848004841d001030540c0c8110540030b00000c0150700c115100d44521074001c000d00d0416890700c2089040341c005810032120f004000c90a12201074111520600502c6075240c003c00c52410420010b1103915510030092a0304106111403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 668982392 1250 668981142 668981149
    0xc080f0603070803040e040c0f0b040b031302060711010318020102030301120302010b120c1305040f1101140d06050a0f0810020f090402072a0803090108040618230106030b0a0b 77
    0x30010700e4444200c0e174685491310b010b4a440507003a90129420141a007000900f9481411510111608440282e04051921900c4100da030701c02810b4410101c4c0c0e1001540040e03031143d018001440c019045c07444980c0700c0100240c102c40d84441046011001c040003000140e0380002240d0640d5500300c14007004010340c0c9000e901400451400365448480004170b56400540050b40c03003066a03040713403940d445080394000401111410340e0302800040071040d80101085083c0c40110105c05d040c504020310245000c81d42c600340e0415018203800319100c032401c00030ba207070204c401009000600c08a0240506d0800742595510000e0720b10b50280b60049400d00000502d00103a402c0c9510150003507507550551700d04004900320020303403103208902c40c441c81d4103403058800000084d1940d0f84011341c5403821080042d6280200103004541c880e03128510b21307100c1d00072541000310140c4140000a0b113140c200c1800a00c0c030305081d00b40d840310ba140c2136042003c100744d401c0249e00140e500000181e20380341c41021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 668983642 1250 668982392 668982403
    0x5010311091c1205040608160c0506131a010e16020f100f1515050c0c1801080d030b090601080421020d09050a0f14010c0c03031e030c080f0603 63
    0x85940801c2110900c410b20000d0740840c50b403907100346118038a001c10030b20255040c3c0030f1400741000185402000138000c0082c3e04600318100d00e1428001140b00c020f5850510b088801c0701c81005074080702020310b081112440300301c0141500c20034815007960401c000c041500c0320040501c2c503c1e00f51b04a50408082c0207000c034044080c4c03c001501e10300c07141910303070700c01925000244030100303171034201c003651045005820102501c1074128203000c40e0210140840e2103400c40c03050000b1501600c42042c0703060356000d4901139603c041d0a804105580362900c4c10b800c0a0f0340e601014103250500324840050b0381d41c2800d50381c1c4113600b400c2c07034003060b01c5a0505c0540000c2d0070b400605410000328403428030b6500000c102003c15455507644012035122070500000544501c5400c0a803c03005005029141c50030f050025072500c10b142c214130001117901c400304c070b1810383d0b030040d400b262029000c028403400f00c084100340914182010303c040d032160300d0010003004004122150304007007440443d8887e0b506021 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 668984892 1250 668983642 668983657
    0xc0602010b1002300d5c13030602070b060f0901170c030613120512240d030e0f0109050310020a030b10050a0f09150e0303090d05010e070503121803070506070305030a11040f05010311 80
    0x1d07442061f90312841e281000358032421050340c040f038003100040c190b460005981d40f5555006010b585071640391007010302d0788201c0c2000460603400352180d40b4100d524104101442079000031702d4103c503240e076400c0c10544001005185002c01c20104449001c3e17120a1359501e400120f804c810841e5178400040d000c180160361440c103036200503906150828154451080c00d00400704840044810801800640b03640480744036060701900103040012006489601904901050382400f01e040c1c64082c0004072031190404501012810226600781c01644c0b01252194403007060511525542c1000c0000e800b1102500201d000c005d0580b01500942e00c2c03c1c001c1d600c910070003901020402007107107000d030b0103040a2110902c292203035280c00944c03880c000506040300300c01c81d81c0491500c12444000380090744401e014542510a0700c800084584828000380002e038065034807a92a824200d04401c280c50842d2901880d007501440180304020550440301e0880e1001d003400a4200d4001018481c42d0180c0030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 668986142 1250 668984892 668984917
    0x41712040e0609090601060c020f18010b0408060106210c030f1505090f0c0a180308070b06031b0a0519030c0602010b1002300d5c 57
    0x140000340c0050210072503001e01801c0790022003540e141d481c4c107513642ca030900c2040000b91105030755401504129403442420380024180070b10703481d550031201c03010807000e0748000300740c1000080411010784144580ba003d01828600f40e02515240d100305c2d054500341e082c110405503601c0000e444034a0199210b4a070002030480180001c41e081c114104000c0b050344949070260b510719002030318800503a814a449180244040b03070a000d1203001c2201e080140c07000011f840c481c2e40c1e5020011541d02030280c00018446e00650107985044402c2c5030510f02e10144040106000c0d243d0a101641c400051000f41c1b4410740300c080030302404000642c0148001c1d030003c0e0600f602001c020865035410340000341150415512080f411884c1d1a0480e5140c4000c0c0301c001c2a4041510541e001e604d8003100c02c0201e021001c540340c2001242c03001d05048a66107a0a03141d000c0680c00609842d42e101d0261a035002d024545070300c3c50358140303480041c00f5200d0303d00440c42048407154101a800413041964454a40c05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 668987392 1250 668986142 668986147
    0x2090310020d0b010e0616240b1216170c060c0a030e0607080901050d0912081915050f0a120308070e120a061e0c080f07020102040b041712 61
    0x19040c0000398040d41111140300d09024111009502030340030351045000190129280c0240c50ba00c84101c0c43d444101125070311404d56004c03804010100003119400c001c100000303090140309041119840d40b020700d454540d08024003441c0c0c04491034000d0f00884003001c00c0d020031041c0c04104a801c1150a840442d803015001ca003d41c0030440000380301140c944a922039401c1d00c11080300f080481d010b2100700401d0040d0030446441d1552042c0094000b0f0310b821000400d070700d0600c1d6140300d0055101d00007000024100f6040000640c1d4041c0d030380d0040341103818100190010300b041c0c40070600d0103000d00380c004c4080d030411340d03200d40340d411800c07004182183c00503d1450491034020b0100b50250351100000e100660131b06d6103890402e1003c590310400000409028507966a0400a40381c20000b24080d42d25490008549c01c0540c00f80543d02c95140c0d071510310703528091030706c2605504090102d1046a00c140014040d05015804071002d40d14007281d1014184042c88016240280c1c42c2d6103003000750b001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 668988642 1250 668987392 668987413
    0x503070606090204180c090b030f04030f1404030f11030d093012031d0a0b0c07050d05131a18030607091809020607210c0206070312020903 61
    0x44050004144140c409200c03255a0b1290035042c1e0040f400f4502c5981c802030620b032140c1a20351310510040b1a41d05041341e0156031526003600541044a6030245584500200400c00d40d1021003000305884906210789240151525244280500d0100070305480840581b041480304100304020306040c002c080310350305025060001c1244c1c0281c0f143c01e448190008110020801507414081d0f028065040e01038181c1c9540c8a0380c41c01c3c00106004420b042c1c3c0c0b5212800072920f071304800c030070b1000d90b01d006103110019840c090880e140000d0408e5036040051000100080d40407544105110300307803600ca5128002c854141d120a422603000f505542e880704030891040c180e0030080d1060030894440d86103042a46000d05450b550112844000074810b81c1050003a00c1c86d5000c07520320400d54500018100790154082500c5a114400c00d4030025401003181540e581600211a11001c080c40c0c41d1800e40f00580c0811418003c809000f01840680c12090b15424403a5059500b40080241210611840e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 668989892 1250 668988642 668988653
    0x2061204060209030d020a050319050d0608030c0714060711030f100921080604050711060901050a061505090f010e03011802030706050405013c0905041d030d0903140403 74
    0xc114022070080c024200e1070f0403102c1c00070521801c070b548c00c44051442c004207825000d40c14542c102100742800000d010b041d03c00d65840c8111806030889038011643c0e428004805403070310185602c0307041606076a00c0c1d240c805446d0103098940942d40402d10400700140100020f04045c605a82a040e0780b0885001b1030014000d034201140c5c2038042c0c10006444901803200300190200c0341e5203000071801d12000314203141001e51003607900c40454513003000360700e442d138519a0410000303035454840b0307039110014410300e0000742c40b9100c0108200c8205800018001ca40500f440c040c0c0010035100740ca20064008199020356004180488000c3c003c1000b072904009180c0321700d40d691002c0c1c0c024895082c002c078046001e007007100d007a034605860b403a80700c00c2c200861014030b68000d140d203140c4616042070310600c1c8e00c800b803411070340c1246910791000e541e0502c8148000c8075200804220104031540440744141404001c0f111038480c030079004148514030341009d450840aa0f01c54100d038903000a0008107200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 668991142 1250 668989892 668989897
    0x40207150504152c070503010f05100b0913090611120a0c080702150c0d060608010918120c060603081c0b03120f180a0b04031401060605090d020612040602 68
    0x5208035250f50211242c244a08200e89001e086542544d520305400200701e001030380390000240502c002c03104031a0311540840d003916640c010040e000ca803110203000900052410071006002d00318400ca00b040c000d00c0018020b40d0313801e0301051055507500b04c0c080a1080d55001014400c810300300f1295a442030b040d048036003200442c3c4400185107084032207107e591260011a010f100903500038400e03001e85415804042c4000b0f800004d2500c4200041d0404141d6401404010121500e42c202290700d030030354900c1075410090800e039103907088000c01c40c00160100c000015054003480c0c01c1c100d0040b18a800e00c010081c60b00060030f00000499100c2108502c90b085074903614240b901070000c0c0070454181540c410308441d860414200900880300701116510182010f400390745d20a8084502c800f020490801a9820001440070300040900038401c00f0180c000c90702c10044004c011540c9050b00050960040003182ca21511090001d081555505030540f00c03030038000040801941440e142c844000d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 668992392 1250 668991142 668991151
    0x412030c0501140402091b0910090e0709031a04032001052707060509130606050714030a0903020f010201090615080606030a1a1e1f05060906070b04020402071505 71
    0x543c2080140c1d0111120307564800d0203150b01809140d203549a0406180c6060200d04040c0c0b01c24078188036000e102e42d0307250301035a00820580c4840c01d0440c1003400100071031400425810900018820400005400d80c09045091000026209440d1101e03c0d048805444c201d8052030000070828909021401c10341c0a2400f40c8011611400030b00001c0c0394101e115180c0b0700083c0c41c26000b1007810055030307008200400b000350000b8102d88100c28204461400c5900d42d820480020300c02068010410001e9124580c3e00046800198240400749400402d2202d00b808001c1c0616024451500c250f4001d41141032615400340051040d10200c409100484400e0302c01d140d03451040e403011074203900300480c00d001540d07001560905000e001c0c0c0408840c04101030082c2c1803d0320000c803d80900e12042c000720703015905007407604510341c400c0d9144401003205500024450300081081c0c0b02c40d41d40b00c40440e41d0f05a0b0080744c45001da5650300024000f0700464101504113a00500c03031505040069000d00d119 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 668993642 1250 668992392 668992403
    0x3091707151803020f180c0903241501020f100e0714060a08040c0b03150a090b0d02011409030d0908010f0605220b040c0509120c240412030c 62
    0x50052503142211015015042d0010000003420240090308200c0c00e80c00e12070708050841683d031b03421301102d0080b041c0200c0d015600000003054841540c13a050100100c14281c0783c40e10074500080040303c4075500c6002c1c20808000d040314880c409540d00034040507540d40318a0007992817840c01c040601c005007a10200c006080c0c0501c41d07012a80712041c3c422000c00401c0600054103001d01c4820548580401400584948180301e10001c2c450481c44002d51060b407904403481c030082e400764103002c0c1008464000b0941907041042501041d214100f00041694091a11205c0b030030741010b859550344601c0d0b0000750140140c0221586131600b1100f0f203800c4402c0340c0000c2010700c040600c00012101c1714003c0e158402c07010b211801403a00b940f200d00030741a6000740c0c00515081402e000508640100c101100424404a41d902540c41c0080d0306039084000f00000c0c200078404080050140d040424480080d6210480900c05100c0c0341420303640500360707907404446000110308000e40701c02c2515408484 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 668994892 1250 668993642 668993669
    0x110c07080c060c061801141311240a1112030106080903090d02130b030714030d08040b040602031e070201050a05060d0c05061e041508010806070207030f03091707 71
    0xa091103811564800c0008026010640301c55840f04100f81510402d041559221144603c4001040e01041c1c0213013440c2c12302c002c03111302518003a0018032400300b01500c0b5150314107508032002059004100d0003819400c0e460380d59100340600707403200d40c06d40040c0c580782c2c8038100ea100000c151032001181691415242c10505546048030259244a0b82e080c158101140400450050501025101d032080d008807012991222141c080783c80d2000503840b40c2d01190781d20400c028142810310440c1c01241041c07500c851a4506601c1e0031649840240c4001d20796680040090810003090b20151b08a103509403850032541002c00009018200540f0300c130000f20300e00004110306282c034448210703241c0e5219181420840ca41030401180b03400030120040d40d52003450181c03046d00d210800803c0504802003490001001030f880c010310318041600160300b242c0c000e0b02030101040d0000f9184c82125030044410405190030700d01221003c803035a001d08800041070401009400c40814060151142d103807031440c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 668996142 1250 668994892 668994913
    0x50709050717094206040b0d2303090a0803090a060306050f091f12060f05010b031501030f021c0c0503131104180c06090b040b03011701110c0708 64
    0x390744206a42c007001660107201903800c407031940301480704d500580032a8202d0040980400740a400b00b4400203810703220741c20f41040035520b014400c6040c140d0301a2411401c0c96440e540746903c04503d101e1009500c020a40801540710701001100c81018000c1c2450f111155507840310b503500d4010a5299204000c0044003003421807191183e1030440d40004d20114510311044180700008101a0104d030311004814415420000c0008640c0700401440d0072805141c1031b54108403007101d801d1120001c01c44c1c14100104107414814041d25003001c0a0b134030281580141e400107030028000380c07080140c61800800d00301c05c8600d01540310140e400c100e00050010b100803d0088a5a02c01103640d007003d40401108580440c0005140c0c2501c1007001d4400a1402640003201c20002209402103070f903d071505006000301580806081300605610854a00b01820040c0c00f90140c003050290f10807110141d01e1841d11440c0c01d4104400d00134803860f00350381e1202000c10041d00c4883d40e00446416128202842 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 668997392 1250 668996142 668996177
    0xb0303070c0e16050906090a030b18010e070f06050c030d05010f031101140f130b1b07080703020d030305060607021509150f07030315150807032909130507090507 71
    0x49040d10300315610f0074a8207035005c040124940250264540040b2124000310008100e40d09480c0120740c0e910003044880d0940d03460b1802e484400f1821407180d0000c0b40d04211a1003440c5c005015507100d03051164403188655030103403450181c035081d0701000e42032000005009918010540540340140e800c10601d40c80d01d0015640c03010a504003009610081003050316104c0440090601030411000035809182d44402080564104164004101d4000300010340480c0041040d2001400b044010b400314910316000607290103000100901031589840009425940e12411600e0442c0e00074403025007031085560803041d40e00000d600b107001e89898000c9106100043c0305071b6140c2ca03c0307009110302c1c185856804070301034510709104900031103002d03002203885480342000f140ba801030340eaa1440c0d185002107008040c1c903e40549a4200790742c2e0071091884440070002e80030031100c152696402070b21004c03091104403914000c050194001c554010071500a560004e03802034500f641d03414001c00200454 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 668998642 1250 668997392 668997421
    0x1b09050609030a080c03040302030f010e071d0a020f0f070c080c0103020702090406200304080901021e1c1202040806430e09040f0b0f07120b040b0303070c0e 69
    0x242c1d070507408010360400003203c503001040c030340c0c00c01300136642020355a070b011a142040b0400c40c0d012a9443e0b40c40380343c0d0240100500b100a104803442045101d0045200b400300d660050640c0240c1500011690088240c000441d40704441d03003210155108452b003449200b0081900442c0c050b801b40e03c90f620744541c400d0007900c44254005181c11510384a035030341c08000340000881203070140d012000585955400d400514440d82c0208425036485000c100020f0070801d9010015203240c144c0e407a0401440c0000490b6940c0c05005040840c12071200e54050380d807041c0c81c8210455160000501044a840c0411460300608082404203501c44440c2a2080c151581c036034034030000c021280c3c000101d55140c00294804254030304201000c510000d01051100504841c2034400c1e081c04082141084000440d455000b4560600601103042491000700509a0b080310b00c050a1344800112640350381c0c590054803c2003004003103d580f80c0c0580381c451101078840c42407500c81801c135000150041406480d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 668999892 1250 668998642 668998657
    0x10e090106210c0230040b0c010c050703050d150323010b0607080a18030812090606030a051b22061e0506030103021c05060a1b030e06011502030d1b090506 68
    0x45c1c444060610001824107010824501d066a02c00c001c410007015800002d102800c0e01c240b2041c2d41c0c0c03c00141e505e080d2010203500c00100071042094002095000b0300f9100251007039080403410503d1840c80c20750300c01c15a00080c051a22100c0742d8160a000d29146c0321000501000a01c41d0210075002c001c554010740030094940142001058941440365021b6003400b802c030140702001503183d44880013180c00042c1900c3c40307040000103200035603404101c50341c2d004034128001d02d1001d20543e600c40d110150103034080c07a100140c2c180160141e480c103d109a19082c80c9100824184480c8003c00180c4541c0c440d00d400081d00c1001507051070b10000c9040250750003c0d000c030f85581d117598207005600d448041d81c0c2c8088a0010710310302c0000c0040c012540541c0e6a20008203802000f000000245129039002c4801e0524000e40c00208410103d00c6d82e044802d51002c8800ea0940b00200f40d00750300c42e03070314458031943c5010181c04c00300202161552807540255a54000e00d6111000c0c05418414080d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 669001142 1250 668999892 668999897
    0x28120b03190f170f1b0307031706030c0306190506031621080a1206050105090a0512010e062d01030809040c120e1b040c0807050306010e090106210c 65
    0x10010720101d962a41c0e040c0510b446081c3d0052601c28403021805140c010b00041c1e03002a400040302c1c0d1000601d103501d50404007103600550b107460320541c3d014051010244c038420442c1a6240000c0e020781d42400980340c5030740d0241c2900c00d1803414a0701c3c041d07c060042c00d041c0320f851905001c00e4030342c2400104602141c1c42841a064100d0500601030b04070b20444480403c0340c9000051003001034072140140c040d45080f038840200c0f404800101c0010740d00140c00c2181046010720044d0300365620107a1140450f1402e5552010303126098110601404100c010340301030740f083c01c041c40020388102e500380d034039001c400c4003102001d00c00d122a80c0c550789003071001a050040a00060441e887c00798800011b140490404030b0144608a640b40155040720605102c5504100368908400302c4810440740092002c40f400c201076041c502d4040c28a10014010b03404000001c000600c099000d80c001802d404402410701840b981d482d44024840d00c1c2d10410300c004241d24000b040140300d03c80c01200100b05954 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 669002392 1250 669001142 669001183
    0x70f0c060b03070b1204030f1e0c080706050c070606090506100f0e030d02010b0f1005041206090503030a05190608120d1e020702010908070807050628120b03 69
    0x240c903600058264200c0e15907050060703200028400d0038400c01813102601c40340901c1214503280c00e014003240326030482c100601040382d60083c52442c00c00000c0c81071244509203a03942100b1801d01c041d40c0d004500006003080d2030035003441036a4005c1d50142103182c0c40342000340002502ca0b110300c415640c2c141c0c2c800f82c02071050850035401900500c40c082d8540f000e031500300650242400081d00d4400c0c1701031843d000d42d648014480c0303c3d043c0701c48240c40300142501c0e5980074529102004200703100d44c0c07241d40b424645849404c800c000c0c4a400013840365810400300c0340c0300e09241a40c41c004110544903215450001a40440b810005004a00c22600400c0261000030030f00b10304100ea40c2e0281b520400c50680c0c800d4010700d00010003c044603101c2d40a5001038440c0400c0c8005041c08801d60002407044d400340000b04801c0e10b0006100081d94403c0d61030645035440e5402603d061140840700c02d10440d40a030400c07040603813181e054044840841c5c2c0620014000e007040c1030b140c09045000141c04500d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 669003642 1250 669002392 669002417
    0x10603150b030702010e060a061a030f040b0907120623040c09050c070506040501090c0501140d0218040e1f0207170304020604080f0303070801060801051f030b0301061706070f 77
    0x510340a10b81c00f400d90b00000c54122101da0040e400c0c01000c50b0340200d200d80c0d560003401451115010f251700c0141c03010717141c0c1c0b82d400c003c1c0c006440c190b00200000d04600401c8001104c400040c400d05c4d00030228061000d0b0b02e1106c2c5d140c407402514218a91044010b031403400c1e10207141c20034000b41c0c011608003403000d007c1810b00c581c60740a41001803054036003070010880d81002403c100140c40c840d034015400024280e1507441c10028442e1144d20907810001c59540906100729400c04071400c0481890006a4424201c0c1c6035000c00c0c2200c03048242e005c7c1c0341081700465243c000c50071900542000360564a50038281e070784a0124058894090a0102d0003003492210000f02001550000c0c00140014105981c4403812854841141d4400d415034002109000c0c02e107030041e0070340340940003e050020a40d810000803444403404403500c1020050118520b4200c140031740c0c09003985802c00f400a04c070a0307450301c04002c13030321450803801c88451041c3c0c0000344140d442510320040340d022640e9090381f03031201d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 669004892 1250 669003642 669003659
    0xa06060e06040510122c010506030309130b030a0c0b090907050a02190f020d0c0306050a02090d080d09080310050a050406050d022701032102070b1905090a080705030601060315 77
    0x3020030801845a81d07601206d00107100c2c0c211010590302c0114404000310b00603200303d0030340b80d016290f580030b5401403211109598a81c000545031850101001440c41c545000181c904912428003030a2044200404507030251580014603007290b042d25000b000303454501c0d08483d28841c418009005800c015030f000d00000b001da030389918490103280b00c03c2c241016038000400b0048040b40840700000c201c0303410800c100590240c0c640c00780402800718200007254010403014507040d00000c00000001851103000b0100344d100c4c1e0640354029000701d44a107856061041011958000c40e482250131140c00075061805000300d4041d150003510943c02a006ca90a210030044c2040f08114844261030701c118101d48004021030095010f500b00d503488a01190b0380b802c410300f9044044086400c003400a000081b070b40012142481c2100d40580b0341a03d500c801180d4a020710444943d0000d0011400100940009401000d44600300d0070b48032903981c0c480e804e40c01c03100303d084030740e40311003525908201103403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 669006142 1250 669004892 669004907
    0xf01080106051803030a05040305070918141f0b130908041a0d150f1d070e0a1d06030f1605060901091d0a0f1808210a06060e06040510 59
    0x1200f14915161100564001a0440c2c012840210000d2400328041060142c208484001446038034400c12405516245800038120720b03110107029421076902d2181c40328400c00c1100600080050000110340c1110150009007550f070241e03901c5071036484c2405240c92681c1c0326002e8280d9121000f0703450107142c15130a000d41c0c0e40c84030f5518242d107402c3c0300000300c00340107014440406090988100c4028202480c13a0001001608280a01088220341d001070703050110b903590700302c001400e082004522010001d190170700726811906001410500e0041c100c40c041c000c45000301d9045060b900e100c0c0c0a02c4000f641c030007240481d082d0f00c0120300da042100d82081d0b801000400342c10b1400400c415210400603500415820400400f80c408000f00720003c09213114044012450500c1400501c150400d44026004088405085214001181d04148030b0114075a0403008074160050703914034020240c0e6005100e00d1081402042550300303280c0861030b104e802c032029280f000f00001065100c1c00011140d05 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 669007392 1250 669006142 669006157
    0x61602060402151b060108070b1603210e06010510080906040308040203010f1a240706020d060e0c0a0f030b1507151d01060e0106082d1003020f0f0108010605 69
    0x1200070041d140c0304000c1d410240380504040c00017010b05514280e8110320701603040c1e10a65061000f403000c005880281c2e56002c162036054600070000b64144d112b69898644040d0a00300ea19141c10342d045400752000c81c869040b654203c2d0221000044020161801582280c94031582d40145c3c0000c0d0000340038941342900140081c0c00091941c2100e2a034400700c8507113a000400c10941c001001846144c4560441904540420a03807011207084802c85198028408000c0c603c0c4d40126510480c0081a030100340142083c4c6a8105141021004080b0b1070740b204880c030780000d85008a0752642d902034040c2c04103c0102910584415020403032488447c0c103ca1001c8404403404074050180b0042c5000e0300d003072104181009040301c995030040030300f12840d42c0e100c540c1409100c00100515a04001e03002c0d13000405000c0c903c0c000c0c0c502e12074554a442000c0d5884003840080c0103000352451078464000580e4400e0300d44402200c150302c200140714050b80b4119002170503050050040c0d0f8820707030140861 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 669008642 1250 669007392 669007429
    0x15171506160c12111e101d0a080c040c0c082208030301050d030e01030e010c02161a0a14121302091e060112090209010b03040501061e030314120f060102061602060402 73
    0x200001c5c0005400010101e40140041c00c01001620107000c0048210f4a0708011264495883e1070301c0c4081b9103075090b442d07200744280e94a841c4120007601400c4011302c107950140d0525620040501d03407000000c41324120340d0301c1d10030004011030703403600c00002c581c180c2e2002891090308644543c0c0440f2003c060410090426850302007550003100240100400c10040da00504640b00c0409404000d054050780000c41c0c548406000c5903403440c1400c11101001c1c00380c91320514103440600000300303904c2821803048401c040c0d442005807100c0ba020309000d04501c2111a0106611450510b01c1e07082e21a4400507107038003403400440e01d5580101604218170920580108081480d030700041d0310010f00741d2001603840307000010001004402e208071000380c070508010000b6245d44007140a0609110f0000a06102250b8841c4440315401c0c3c095460317541c444864070110380340c910703103030140706400f0b440c010302601c15980031442c0300c40b4064004031203d01d00c1d80100001d41e140c0e020000d65500c03807000c1884 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 669009892 1250 669008642 669008689
    0x513110d0602040803071104051302010e0607020402190507060609090b0a090c170102070606050109080d050d0204092904050c0706150e040b07080115171506160c1211 73
    0x1070384d04007403002d800c031640104500d406081c1444180f1080d44c1c8001c000091905c5100083d10050380c01044102d21400195801078450001d0b101041c020300c80e0880000c1226250700e5681a17240c1c0c4400103100e01c510134441400003aa503042d0050603191140300062174044080001030a101c441d0307001c540d500b4041d4907005030300d81c0c0d1454241503106070080020100e07500082c018050082078010340d80141001c0ca00300005a161001c0180c403480e0200188040100c0010000421002601a370703000d8130301d48038100308400c2100c6182400340c0d00441021060502c001c00c0c0000762a0912940b4883c0c0c0406500c0d0785001061b6032144000e0030a00391720030250314078001c0440d080b04d030100302e10300c201d100c3d0503004440d040104000c0c2c40e00e00305070b110229107505011036201d51a8003003400400c03242d81070603e031807603151018010480c0050308c10460304110081911984d0a00924155540600071083d0300070035600d0305c1035007a440510400180c02c3c0403441d0a109600d080c0f8076000b0404c41c140440754071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 669011142 1250 669009892 669009899
    0x40335071e03021b06070c080a0c0b13060515130c0306120308060306180a0f0f0210180506070507031707060f091202030307081f0305010516030513110d060204 70
    0x401ca10404450000a41c00309588a41103070a601800c400d0f00000000d10303d901c0c0034400100110a0403800414080d00454000141c40c02044002686030344400c48600c02d103000c500724058201541004d445481c2000c001c03e5402c42c80c0a250000c14402030801214200380d1000031000d045072440b01000c15503200d5000400c18400e500580781c0034400d640720703080c504041007014640070020f800d142c2d40d200408900e40322098001007008015902c0001014920f005043c41e4800d40d09165001e500800c1180c000d02c0070583c03099251400182100110307402c10f480e54240000c0d4003a019008041f40e1000400b4808541700e004400c26409800a5413032600310b0550f03d000c203590f00006115a505d451754124410080121800d00c91509188000c5055203042c50000780801c03000340415100011075050850b460062040d04806150420001d000074100b80414003041181b2a882d800060316050214100f250302505143c2681d07005044c503000700c00d03880108400940911f0080751302a030f0800000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 669012392 1250 669011142 669011177
    0xa05120f060a0209010f080c09150d36050624060a020708070b0f03060f270103260a0503071b1101081015050d020d0e0604033507 57
    0x11441403000550144e00c50302aa400989890342c0303242c08100b0b210189040001070b24040081d43d20860341202c80301280355402441d40840d1280c14006405903003040b158480403401040c802c030b403403406010101c803e201c00030903c0da43e206040348000e040d80c0040001c14410a0000c0c070302ca074002406501c14184410440025810754020700c04280940c010103000c1042d620700340003c0c0c00038859601d86500d40035541803841c01610000300304512880300c00001c0440c40d11015a0440540400705030340304a540951032550082100744011126034050054020300c1d204520f8041e186600ca0410007428507541510a45146e080140300e481001a0211502c69800a1003030141003a8082c0c081d181609114000040038100003c10080e5402c1401400300000f800c8405511400030880c54450340f20100e040403000641300c0c01020b03100325420300203866000100440c100e4090b0340b090300c80b12590000d4094000c3c0c08032412180000d11980c000700c945100c40d038480c100ba0300c01e04c03e25003080801c401c1d0800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 669013642 1250 669012392 669012403
    0xd0c05040c1701060e011b032102120901020a0e06210109020a021c120e010b06130509092d0f1b03071a070f02060c030403051b0f0a05120f 61
    0x6520018a0303070b0300c400b080380d070780d24412502414403440d000d100306186000207060405a000000c0001040144010074075108080805800040704500782000d019902610702940001e001804090355407004590810720520855580c4613494448107071301c80060040180700e030094129480388815101d83c262591a03441c00c001c0c00b0b0024214016280c0f42d030f030b0350020f1806da00304590400040e840344842082e1500060f10301226841d00802041c0c141416280e11b000d882ca0796031858102402140000d84404590305600c141d91080c1c4000d6180d9451080050f525051050300c0030740d1f555a94008141c40c2d03604030f0f54550300700b88001114608403800030a546012802c580802c0340108601c1850340919003404110002c00601c1c40521803501ca40c0458101442180401043c8100407038160b0219141c40c0b05542249021105a81c1c65a40c0e0317040c6107031550410001002009900c0151240b40d14001100703400d8680064040b2108034140000e21140405030100310078140300f010b8944134010030400a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 669014892 1250 669013642 669013661
    0x4050a06110307031b0c1401020c0a0c0819172a01060503060601050a140306030c0607110307060302040e0412140d09150908030a0908040b0304080a1e09050d0c0504 72
    0x961980d64640f4403001000c4030914a11403901005c020803420a031944480b100c04480d8210079122801c41803024418024415219032201038014000801c052080b2040c0301c10403202d481c819120343c0c00c01122400f04078000300d04010441f4800c98031030110140180c0107001c82c1141030301030312035602015074280d105015030555000c603a0344900050055040c144401c68000c2d40070708050741426060a00608400400000084684408000200259010010030700701103c00b4007240d41d40c000c0f905020f104406400c03074103406445041c40000e401c91182c401c40342150034414000d0300e103885683e5200389845aa10b02e12003000070780d044441a0341e4040b00181403295003c900040d07290810710301255041e076200007100010307140507060001301c0c92510072654440034451000400c05c2180c645401c95015540029104600110400003007241160082074541002e44800071780c003144860001d024001c034403840000500040003041a42001225110303c14440c0107110340254a800c041012201c640d030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 669016142 1250 669014892 669014921
    0x1060e1305011a01050f1e1603180312050c01151217160b19020304060c02061b220317070308160801030807021f050405030c0301060e040b04050a06 65
    0x110402000f44140d03003014150043c4107124030400e4001070100e01500c00d140b10316602c0025140d039a101c0ca83e140c10040f480c1d4003192a15214840c035007210744d05941e4011404250b42034900e0303039400200303508041103075444030f551074076035441503400c0700c42c2c0d0003800c0211006c1d900d0b244800740d52851016a54080c003c83c052100f540c05040c00e01c4004480402c2024184450410000b480001020121408213400007255201c9481c0e04c01315101c50344114040c900214804801e010030080d007500b0400020f0010b60844810b62918030050a00315007001c8411031903c02000802c60202d805000e03030000420440c07101105623075a0725261030944400005002c030303040010300c000401d40c10004240e0040e0041c01e08103580c00c14400081d03d80c80060001a200800200f4100210741e662120350407039021200b9080c401042072900a00181c0090041c1031090046031000380c66800e05200d0801102d1a5500c4401641c0b908d80300d8818041c8043d100360344601445018102180c00b90141c2a862540c04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 669017392 1250 669016142 669016171
    0x908090a0b041406073905060a12050603030c07080102090a1e060c021f020d0e0d0506181c050301090b0d150c0513060c0614131401060e 60
    0xa04118466000d50001c0c0c00c034601c10320080c042465818034841d0800b03000e070303600c0f035960510341401008400740c52103007092441030650716041c01c2e41403a01a5500c18180c41c1e41000e03240c5400030022580509244400043c225107a074240320710340c5030000da410a2024056900d4516403811150500c9151f41105240d40e400048640450038007101d410700900d40002a20580100d0128459950440f0f1285804104640f0720400035540c0b0355002800c008403016a100f29004040e0b000307500d4545009010012510340010080981010700d24010000e901c030000c2c141654500e0070850301080d800800810742e00c10501000b08624030111602e84042c4c198aa06450303624001c400415500084540c2c6d020308080c5440c0340001e0281841040d402c3c0400e4000324008010510840e00e0340114803403070a400c07100e0200021500c1d0044e8044a00174096542442107440700d102c030b40101c034816112100c2860004556001182000c04509540c41c031000010480c0b5944903120007001c2c1040d140c044400d60f01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 669018642 1250 669017392 669017407
    0x60f09010e1c140613020607060209040b0406030605060a140d0b1801050c03010e0a0c080403030b0d06020301170c0f0306060d060f0c09080f0a0206040b13080601090c08070804050a02060703030f0908 87
    0x100100c0c1c1d84003170140c0d418100d241c10b0340e003c00c90b18024000024500340d0081100025603459802c80c1440003405842003110030f503603050010180c40c0648809004206a61012400c020b00a401044805000d40341408400b51903980380c0c01d98138020b1003184840c40d801d03c54281c5441c2030003128080d481c0140c3c40da480794104480360007040c1e0060310308030680386080c800346a11500880c0340c6a015415081c00120340860402164007000c42140c0180460710000020840b2000e6504c6e08101c000c12008503106440328509002c503145d040c081d455407650107a0000380300f5207840c01c029250703a80308a5000c900031150984e250140c44440249902081d82c0b0101442540810403c038443c41034140001c05c1d00800c070381c01240032480b0301d0280c0c4c1c0000c1c20000b642c2c0d04204080041c0001814060100d42c1c2d1343d1303901d100740c0e0000c10060f40c081e0002201c2c1e0020807c00e030303c5a0001382c002d030b8004010b00548140c81c2e0804c802c5500c01700d0100d042c1616500841c105900510403103091074000d13214165a540c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 669019892 1250 669018642 669018683
    0x20904050d090b12040b060103180c090f05090309040b0607080d050f0c03150108270a0b093d0c0c06060906060e0d020a03150605040605060f09010e1c 66
    0x101d403c0740c0c942c904140301000d0307624012000030b50003d41000b011040e40d1641d0b0012000b800c08034045140010a01000104200d401480d00d400c44001c08001c0144041484060701582c00035202004190b00c140048821403a03d40d103c007480f000d000301260318118807943d900505801420b140b112456903082002084500d9809030703540200c1c4444410701d51301d401170359000221b07020b909071070400c481c0c003001a10b404c18100c8166010b4071000d18043c06001e80c1140390750b41d01304210007114200a5030003c582d07098000201a15568803206689103e5151109469010407207100909540c44002007100440c100c1440b8034803680100f0b41d114480c50030b603400c0c00d03000e44926502c0348600515202d01007007040d83c0440320300e015000459401d5080c0455000140c1802c00c5504058491803102d01070f280900202c1d07108004441e001d442c103101503507032941004061b000ea00998071014004101082da2580300d08460b41b11014000c2180f48840c03500b82a01e038001d041940d084455122840c44050b1001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 669021142 1250 669019892 669019907
    0x181e12030a120c0c110a05061206100504150c0f02041122270e060c13050102030906070609050f03030106020a0506061e22051501170402060f16020904050d 68
    0x1000050151001c03004000304441443c13603019102d500d0112000e601e6a0b40c0f100b02c0070040070b00805103515004c9603e900c2c07407462001e030348440c810040303e55131014103401101502c0c1141c28101d808080c0210f00b5100740c49040600307038100c4415041e031074a400181e45a01c603900e4541107003807600d9125082e05140c1d40d140c030034548203e003041c418040b080141c01c804101c200a100502c1170f509802d0300c1d003004230300054100c02d04070602c103002c6e4a042008a054030006031903248000320b00b80b6440c0f0b40c2c4400583e1a8443d40090540019003000414082000c0384c200d1203686100d401102d6540b80385101303031803c50300281c112078010703009161140306000040003890f41044c0115041c401010021441494450b540303482d880c0a0034021406140103101c1e4801048055115081402240750480c0300e8522140e030b0b204010301240c0f01210075000c022404501c00c3c8125405000d0510b443e02502c2050940d0700030220320a840e020003402100103854469015000b64403c0300200350f10420301c1000390a15 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 669022392 1250 669021142 669021167
    0x18150603020a200601090e0f100504020315090709020f07060905072909040b0303120103050307031106070819020f07060902040c14030705090d05160603050c181e12030a 74
    0xf8001108150032a450208442c0d0441d008031400060805004c0429401c14500a0041c02d03640940e140c03501c0c5101b400c0e041a44100e10890540301060341c082c0010318102c2058400f514660301000003030144403055401041c2030f80c0159000da0a080241d81c8030b1080d141010401c5a10342c101d2401000303400d4550160810403000a0001801a90107440c081e1042c0640c0c12031a102d6911405d910f4035940b13040c0229540b4075110054078103190303101c0c1000c550341d9006020407000204008001028113501041142c0104080e0307a0b010a09d8a4070035500c203481c800403144186280c0d080140507094103101000384060340c4650404150b1500500400003101c80c0b600402c814002840300001c3d9103001901144c0e0700c020a070422075228a03520010540c40300010400400358802d02e4004075080c600b04480b50b0840d00c140d503050002b075075001c038031100074020042d810113030402102c42400303140313000016045285802d410b08400c1e10f0b00e110000740007001075507004090780c0001800ba44140c0d8442101ca00e0f5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 669023642 1250 669022392 669022427
    0x1109010503010603200a0f0305010c0e01030212180708030a180b0c150c040b03130507170a0605040501140403051201120312050402030f010c12050f04030918150603020a 74
    0x3d091840d101c2078103250310103e490590841e03145500d55190341c2d0010940151810b84a1180703a1030703c03440c05074000d29007064660041540c02640d030384650301c81d0080780d01e6001c00003000c8100b40c68110814103200000a6030891b14000c83c8800f080c01d010410141942000655914100017040070141120100b2500100340d2207404000c01e007000c450001e01980c400200510065255031200340e4103003280203d030843d1074006000411707c000e0790920000c1020f0b00d0b0090b0281c4011a83c1c9541c00c0c000c85442e01140034040d088090240c01250050b841940d03c240030f0380000ca01d020040c4480780262104840840c08120302069200e09050030841d02805041c18050031a0300c1411030b103024150007170156152110395100c0000600f10741f0248820805100c12100078868054000005007186203020340c0c441e03002e480c10002a040d01c019210613070080303401d0f40350780c0341c500e007003004400c503124102142c0c114036910f816a0003007010b15100d47c18010019607800607180c848012009003021411403030b1340d00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 669024892 1250 669023642 669023651
    0xf0f0c09091103060607060902030d030f0506030c0306130204020d090302071e05030309060a0c170408010b03031c0207050a0503130e07230a090314300a1b0807110901050301 76
    0x82c5682d11400c598110b00211070340341d1203e08914040e005407540300c000079014011681041d40340e5401da04035840354620118180b2190f502d040a1541c0e41c98030135030040c3d15238080000705040281d09981c0540060010b44054075101c0355040010649040d4501140168801c4004004007668454400304005980c80e60841042c90840042d030f4a014400c8000e00c55940002c86c11011402241c0c200d207910390205d1400d1070507100d014410f501350414171803480c0359401c1c0a95032005107400310072240d0304c00d810000c5103040d00451940000a4106400c102c0d01d44c8034803000940071800401c040d10b42c10341c95009055029003450644110808050020030a11000710041200300001c8240e12000310760744900c1985681d45d12070111070794030700c1d680041c202240160108909001c0031907591440030071031001a059480101140a000e0290b9404c5411400180424070010303203c2e0517140107006901c002618004c2c0c843d100d280140d030203001e00701c440a103500035491090820000407401400110001c01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 669026142 1250 669024892 669024911
    0x804170d09060f120e0706020f0111030a0e0f060a0207050d03180201081009020f0c120a09030b0a060b030a051501020c03030409020c0307060e03030f0105060f0708090102010f0f0c0909 81
    0x14054000c0c1e000e00410311050388040c904a5228454041568084810501c41c0c2810f1701314290f19403801d40174444c010301480e052651a4101406180d100b0302d10b00311030610315070f5403202101c01000710038540f03100ca001d42d41d0441c0380ba0104010342405150040e80c016500c0703031503203401490138160004120626040004e054520381e444c1c00300c004101d40a09001c100da94a140343e4030b03200300b41c68000340c485030310110f580d0b14110741080107020710705400801c540d0040741c80d415a820764000c030800e000000300411004d1001800745c241e010782061807000c0114030740340c84041e2320203e070704100c940d00361542d03543c0e00308804640e248a1032894044203001800668454602090310392066021303280e075040e00003611001c11501001250303c0f140e0480400c009920f00e082c80f064072548290768180c825603042c0004281ca00d41102210100113116492500d0304400c0da0f9644e1f53754005103001410365507901c2a00c0c61602981c000c04044250301940011040c44114025003114030036000700a000d8900f1003002e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 669027392 1250 669026142 669026147
    0x9120d0e040902220e01050c040914092d013813021b0307050a0b01090c0c020405090a0f0c0513052a0d060303030f0b010e01020c010e0f0d0804170d 65
    0x200701c8924280c0c0404d5104001c0800002c1c100a80c82488190701e80703810000c5840c0c485018100b9140399581c1800b07043c2a40050285805050300c1e80182504801c1c200d0500b2181500004e40c0005242c0c1503810b03d20f130041e80c980c06c486484241d015910084a038107030b906441c101000c2c44001441514007010740e0080042401583c000150100f440d0780007940400303c002c2c82e03410214032003031b030700071660b64100034904140c480c21003010481700007100d28004100712096000e40455440b0641c5da0150391700342602080094034001d0484000d03401307100b48003004500102c40507d0b000780518100e0070054500350511417021000405051900c1c45c090500c6549000160050401c0d4081e80c1c900348508180c0c4c04d540d40c1403040240310b0311142d141010000030140c054000c0003480c008000200964886a0010754181e0000e180c0140160010800f46c0641c2d8040c1350354601c0600c0290030348620050710404940000d481801c160744604010604110756120241000061113154005d84056076105902 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 669028642 1250 669027392 669027409
    0x10f1d040c09051305011a0910060f0815101d01140412061112040317010b0316031506050d0c23030606072009060301020c0c060f09120d0e040902 64
    0x14802e040d901e540100382201080028000030743c3c0c101d0020488001d8400904407541079800a090050081000081072070b01e240c155a000c89a01c0d07294624000315000044400d280300900d91041d00514041c4412540c4031300e100c2c1804c071704203078a5a02145100424018845900c0c80e202e904100c6104000f40c084099001900c04940c10504401b034107208038640a00074009699581104400c0401c49a06d0201030880303950040d80242c480305503c0e1001c1810b10251142401001d060f0f6904002240007561503607608425a42140340000c0c840300c80e40c1048550b80c0d02c0fa03100c04005500410a10040c1c5078038801c00b480c4850500705100708100e5008000c00c070003c0101090452107000c40020000e40b00c090850340d032107511030040c0b94620500c0a0004122180080f01401580750800064140c101403007210705810740040206030000071711040140ca94021000408084001c0c006403121b030b243c80010b50118041c0300d01420180c000c403071000b4102e078541c035583c520940c00d081d00103015031102d0030b1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 669029892 1250 669028642 669028649
    0x31812020103090212010207030804200907122a0207231905040513060506010e0102072304060602011d010c08010303050a0c0c0b0c250608130803010f1d040c 69
    0x80100341c900c4a400019005e6a4801d5140f0035035000080480c109036001356560301ca54441e40e040484540040401d4180046003844140c201c014400415006030103840030074032074031001002040b2400a071030006c2c540c451000c508150408484442d10301103406101742c4001c0c2c0800a4410b440d01040c50398048404031000d4030f00e003e00d9540420a0f404a4101580c2000c0c0c6000352060089040c5000290350406984506440051514000c030304c643d03210b00b48142062005034000c0071024100b003442c01076500e400a0901d40000c10400610158660b40540e0000b04469000000e80050740c1004580d20b440380c40600d0940d9140c43d4041091a0f0000d002e1815a03405103806501c40c220602c00303881c44035003404007920b43c0b40700980014071040d03000d006080c1a4249015581c81c5100c48403030740c28100304540c10100c1040f00002c103001c0319204480d403543c00400c1c2c100240682c9502c1d21040c800303910a0f00400da4045500c041840740092091600800441c0d842c50100549050b03103819551140601 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 669031142 1250 669029892 669029897
    0x6050a2403020607080c0304080a120f1d010c050a0c0501080718091d0a14010b010323041112070509010e07021f0e0312060411030702120304020307150206040318120201 74
    0x2801100f404a4503040d0341c1b20565042c1106d0b517840c1c03a000072030744d078040303455080750501405d0000002c064403c1e07010352a00c044a0311801d29103030760b0740311103544110000401030421000c1040d810200d00100f19040106004940f03401080d4104400105801002010a014007030782c0d505445800c900e001e40c1500700c8480b51000111080441c80301004420000744401852090224401c24043c078600034524501c002402000048540d40c01902542c0703045160b16401c240302e400145000442c442410b80c814411911900070030780f0840007803c0ba111000300040e80760700181040c0594208a0790240c00b40240c030741c09400918100704000e503950030105110103108401d041601880409804c5004070300b946c44144c0c0d8966002d00c84540c0002e1003280d109228034180250500c04081c80821a8001e49842e805000b076102c4c0e45102e201c0a502c0980700302e8152048910001e0501c1c080c008503448000307641c1c007900660510781801019216000d030303810302d50140d000b420420302d41d12000403a805682070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 669032392 1250 669031142 669031147
    0x2d03030b0a05041e050a230907210b0c12011509081b120709021b071703040e070c050a030503010305010e010c09150c050601080604020118081207020303070f06050a24030206 76
    0x250b06d2030090f0200c948611003802400e00a880e8006a82062511541d9010f045038040741d174901360607219034800604580c0024011030300e0b5001c690100000c43d0b2240742c40e04068600040c048010140d008241e00c0304c0310407044003411541c416400520380c0018801c850040c040100000c029100c5000352200052144606441d108005101030103d10000c101d858411515200f1014503661205400301d503210803170082010100c0c074074200344030754020b14070960021400c3c00d007880c0b0010351603e00a4440fa0a0000386040d0b000003a00070010259018820f646698595265103041820340c4e0825525102c070b64140700300c1d0505540e0210345e00c0e046071110003481c12046029541954110b414450290550244200105036164002116400b0300c1c402e03603078013110901980c0200032109d024012000181c0280708010030314041100a03106090004095a162541e55900d45c802403001c003900700c03600360300c5008220802480788101c8803c170741a0b118451340c440c0100c01d07100100d075160000031b104d881c02 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 669033642 1250 669032392 669032401
    0x307151b1112030408010c02060412050901110f070905010533090a140a060504030c060c410102040506070b1e070903170f03042d03030b0a05041e05 65
    0xd80221007901c0c058a07004040c1030340c50049403030f9400303401403551960034110824002d51001404a1040740c0002406010a813000d108985c1640007100d11030400c4081a0704220014090240c10446802800280426841d01400c1c40a846059100310b00c241d5280081c0420135441034507018040092091207140c54075985507a000b20300450406d2078010240c1040424098041012107080c010110707260920280e4415085807648140c1c0001042030181c000104211401181500ea1003032052094060f0034003d03100501a0101c09035856400c00101c44001c1c1c21500824510030740c9240301e00c002d5140a0901010800e1481050310040250302140e0005060211100340440b210460300118241030408140007064807042c6d0009440c1c8207040c241c0480304481c00002c507500c400100000d0760443d525911410410000608403116955001c205043d4400c0344420b841e40c03503031203501d0000300200a40d041c050034a00603003180f03001703503c1d29203600c245040351440c541113074154401c082010b80da03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 669034892 1250 669033642 669033653
    0xa0e0102071d040606050405100317070803070807030605030706170411040212010806090115030206070201020a05071e09050121240b09090607050d020c0f06010f03020307151b 77
    0x192035000b0401c0d516038000c4205160a500140341c0101e001c2c00c41807010f1515102040200e0368140d03048580410100342c02c00008001c0034101c401c944010702c080b8101500c2e070321045860783c000c40301c0400083c0502d0402142c0c60f0984200405442d00354001c107005070030080007601daa0041d1688038003402e02c1c280010204030aa03c00411070520191040d510b40c0101012481030400070b0041d0b40e030502078500080d1205205215480b01594a4001c40c984245540c0074004154070481003641180500071204012400802142e0700510180000e0506509812180f80105003103400070f00340395013800c004000c1052507900b049a220390740922199000028038140d0044e46407442600200301c202e0340f45500c0088a135229150850081d50700b945a41c0d5036405064469208451faa400b007072301441413400a8520f46d028198803080d140c1200e5035047d5411165290140c26030019402d2041d0003400d10450030184080c034000c14a01c3d241e6816080c00050103040701c0101c180f107054500d048403007a4140035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 669036142 1250 669034892 669034903
    0x7032f0c0a060e0105040c09051306020901020a060c180f0f0e060303070b090102030f01090504020a170a05061302041104060e0d1a19060602070819052404050d050f0a0e0102 76
    0x5038001810020601e00b040c0f541e0180c00c00b12002e07a24403290040003d04a012400740f82e108014640d842e400c5105a070b60740c60000e400000c0050704612549603d0f10004103180304030a00000c41d42c580440b200b41c1036940c04405950354001010146200701d0401200050213a242d003500d0414441d442c045e40c5040200b480d6014242e80500f0a00d07500007400b501e400306500950141004101808450b078a804142d01504c40540e002908400304410800c011040072000d00e020807011000e80b400c1c40e415885881c0340031026604014140d025444440461409101e6481803500d443d00c020706045c600203006d4410f4200c84810346c015859680c80f0300030000d02005001001c2e990b104004818144001c2500400525000c5088140c2c503001e8082149400000c00c18100c0340650010075000c0401d10420500180c096011038991042601c00c90301c03448046882c0c00443d16244202c444e500d0031f800c01c5840d08820380b281006008081094001d40d025400803a5000350031418801e14007000d03040100e103403d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 669037392 1250 669036142 669036163
    0x509040e03090a030b0f060a150c030504080706080906070e091303021516121a0f0303190c1a100621060f061101020f030f0a0603120807032f0c 63
    0x3410683c0080300f040b5104912a01501c0c0300c03075661400c1d6584201f80205840e080c01541103441304a680034001c83e204180d01141c0343d1080c9071042c00c1c5503582441c00c1c60168a9000f403004540b00108220880750b0421503a6441b841a10b4628104800710000c50a2724501400810409011101c4403040c10f0080204400c2402040156240352400041d00142862042450b100092540b540300070f90780e515000d294000d61182002e22400c030188010001c100c80042100350700f48c0002c0c00300e03840006014031222001c0d4490349038502051030519114030070f07060494148400b80300041c00e019500108854140c180c6a10741001c9040c1600f4101d040d47e001e017618406030881d42090000305c1e141c1c1401c054007040303e8298890024000310200c40d5400d030700907400d040700800300c28000038074241080034400703801000e0144c0c0028000e803a52110104e1481152b141d8021441280600050030382c1032140c03072040f944002680c050500c4840152400c043c0d915026040540b0100c0d419400b404c2c1440020202c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 669038642 1250 669037392 669037399
    0x13060308030c3906100e06120a02040f060e0a0612020d0203030c06010f150302040e070e12010f02070b15130b03011d070905060603130602130302090f040507080d0509040e0309 77
    0x10301d01801040110000300b20044000e4000d150229120309140700e2000282c84282d04081d209907108001c0c02000840b480c48e01c015445440c0c866405603d45100b000c1c541440d030000030845c41d00b8965101c503020700c05015044014581141005100c00d207048224040c3d42c110b5481d030406c0554000240366001d00358885040e4002c0d01c00000340844803803080400c5440e044000d6405a0725030009808a004a03c502908100e8032320004824911404151421090081000c031046041e40c04036401c44040c4a020f0740c0c1240d0000d03c0c1c1c0217112032001d80350361141520a45240783c008071800315a011803140c03006108a519040d21121a03502034106204001d900100d100821941605550356a500c0f44640d890451502c004550181802d030104d0f44101c0031841c279094441400d0341e40310029409020312160040b07004c0030100041e0b960300b090343c0c010500e031912803502d8101403c04c0c6003000403e900c0509103500586800341503d82040c103507903040b942101c00003425403a90092900b50310036280344aa1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 669039892 1250 669038642 669038707
    0x804060b0603190c03090c0e0a0204031407031a0603030720040c0210150815041b1d01060503100b030a090206070302030a1403071e030905030c030913060308030c 71
    0x20244441c0b2420f000420400005100c0f480c094602903040b24841c0001421101520b0428809414145480740c0c0040e1003010040c0740a0b640c0c1c840b828030040940604607660082c05040041c0403c40400c00305010511480380c210b814080002a62446410b000810228040c1c5610920004d45c100c2c80748030501c060024402500c5004000b9110744034001812001854905040c0305c928003032801100b5212001700400741013005000c2c0200b58035004100703c03440c106081502d00c860009011480c01800420248590382d501103c05003034080c1c05807c0301040240500030800f0001c1c40d04003400454803104005582d07600e03400c403400050461040003070b40140340010b1281c201a4004001e00d034441503582e441100e40d0301041c03010114030054469900149400c3c07040c0d0800c4603a50152038804002e4100040d003d0795544c1c5003820758002044954554101044641c07513801e20302e00d0003440c840301c00000c0003901c0c2140c0d101403040c0005805100e1800006c21001c000d0441c43d4042c4c1080402e1141d00314 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 669041142 1250 669039892 669039901
    0x70e0f092a1203030c0f07110307061e03110904090606080d1715090703051e04051f2a200c0a090905060a2f0901030e1b010804060b0603 60
    0x440c2106021000e0241d8a40c10042e1500c02000c010760340a40581411240b4088001c0c80007407103900507100603149040f610106a03010b94082115200600e0152100c00c2d401200d0312020300e00300e41c004ca402d4181030400507a55240000801295401c0400726400105125a8140400141020b4114000620070281c100542d5600600f0241040340000812034040e612100e04500c941c51918040760010803100c0440c1da0b03a030094019541c400c00101851040c40c01504044034001c0090340c0139181d07a0412284070030f242d803220106e1480c07100c1e00d00c0c0500070a01c0c96013a200c1281e0800c6040b0150070500641270410620648a0710a402c072005114003204c0601d440c0582c50340041007000b4441e046080b4000b4106145e805840341c0d00340c0000107407110f5914081248007402d002042d51030316400001d00815a0107050395001440801c070300d803240c2c0f90b840300000541103c0d00d62101070105c0e48801d407140e401074401984101c1a4000b03180400c4691102e103884005800000d0050343d12150200801 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 669042392 1250 669041142 669041203
    0xf18070b090f0102070303020d0c0f02090f090d0c03050d090503090a03060c0306050406060e10030f020a030e07080a120f09030807060510091503170702060318060603070e0f09 77
    0x9160301c1da0200d820440b0501d840005a95403240380c40024003680280e200c9100c82c5005001142a070703405507208000b5805513600140b00d10300111503900041010b8014002090400c000c0c50040c022282814644911980c4015201e0f0081001f0906c802c2c1e112080c5034100325051003698010368014090701c1480380c5914000d8050081081e201c0b0000f40f61000000713a89c80d160080f0303001c50314991104980301813500c00340200f0109400c818014561240c01d51000001d043c401005441060358000521549042c1018103080f26a8131041c0c1662002d511800883c1201c0c02d4040a404582084100320860200946612907980e102411041000ca80401440740325001a8030900c40e07000c00c003040f83e44840a0000f1101c2c074a00411032800201c40030f00024220400004105c004440190300340203440c0e0008006a00480712900d0a030b9500c02074101c400020028590410001c4001d05012414414070307520a08c4d00a00200307a0700070361008550f4040040c0a105946080204100c810320001c0601 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 669043642 1250 669042392 669042397
    0x2d01090c090e03030106090302041a0901091d152707060c0b070f0f0c05010f02030108030408100e0a0b04022413060504030b1303120606020615030a0b0f18070b 70
    0x180c504150506020106030b10b0040101ea060754120f40300c0340c0039103040d5000c1c08010240307812882407030000c1400b420700b10364480701c03454000c100303694004c24000c4d9091040e84440e01f01550f6001113070700807030480b0310046016905a900c0200641561040c41d071000c011b44515010082180150040c0f000208800d94041e04100220340a40610f50b10781e142d03070a045030650444009440050504080080c0d600c0c03190388188c44242c000e400102d6000d0f0402d07000b10890b4800e9016181130392001408001c0c5800501c0303442c400600c048010088846144440ea0316508031810085c155100b0200007401c551792413041140f180d003c00070041e28200065480c04c04c5d50301100c11601c0ea12550031001500760300c602e0484054940c000010505c3e27496156810340700c14241d0300100c1c1032007080d8030003c0950f041442114014070065005041c14100140b451402e07012051409000f60011702c0c0d104081070340e001c40c1d00d41044110704040d01a90303034414002c0411910360b41844141c00b43c000d0000300341003000d01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 669044892 1250 669043642 669043649
    0xc26070b04120f110a230609010b04200717070803150a1e030b15130b1801051e040b1002010e0c030d080a05061f020607080c0307022d01090c 62
    0x110390300c1240f1403000035165100300740845225030f0f000c032a03510001011082881204400340311410040038402d0081c41c1401130850706642d07070f41c0d9210b4800c0042d103414000c01c1000b80d09150400c000080c010300043c2d4610800b0005460004441d40c9000c4696a103000ca8040c5600000380c0c0340c03241041248514a4080c1419030fa04c52020700401140061120b164054511207558003902400c0c03650340d8000a80000400d14610804581b0702c003030180e1100003800d1301648078984002024603a504c10814004500c101c002c810004010050103e600c8468000c481c124241200040c0708143c0c000060150590f880b0036504010201c08108000c0d805402824203045154203a48801c2460720903d41e890040d01035590008030b4a402040c50000326901c0260816000f4040e201044100c0d00e0060b100b440c080310850041e0310001c20484455445407401ea00308088860051a40c14560700096a0301c0103142c40004102259055103124440c0301020a09407034603100a224415031070814214203c010711 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 669046142 1250 669044892 669044897
    0x71e030b0c120f310203060103080334051c1109010809030909071805190618080c040f02040306050903270915121c020c010c26070b0412 60
    0x5021425410686040f01d1040754407201041d000d400d004600d02501240c2c42e2100c1100094003a1071001d0380701840694040c600400316103a07241450301071401c05051528540203400f010122148007040428550f60000d500d6140c41d503160340007003051031000280e282c003800310249094500314082074030f81c0c0a411010002d032500e41e041c0d540c601c40d150701c030310034417079020b500450394400076590711300848664000d4592240e00901a40d00c4401050243c00039404854400c0600501003000300c0d4400c0c025941c0728106101035604902d807a070000d565580e00d182e280d10403501c83d0320070306005184e503055900860308003109110034201005556240da103e140c1c950f070700c8150150f441c1001c041a084008034840302a081e40c5850f9550880c3c1c0440fa0178212207641d0100502e11010028003003008900f0042c820b04d00c80c541025156080a46403851000c10a07052000c034202d442c01080f02602e401c0d40081c1d01615800019000c50314005a070f07c24070a00034610305a01003404180403041c1c103c0040c500103034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 669047392 1250 669046142 669046177
    0x90b01030c0201110f03070c0b09100e032d070c030803010311180f07030908030403090623190201090503030f04020414090a11060c0a0506100f08071e030b0c 69
    0x11078102c2c02e030344641c0c40111010104000d02c03542d221150700115030040e800d14140c0c1c081d10380d568800d2064202543c011603654840c60a00c44070946900c10860902c5008000394a0f00380c441403076000d40314041d08042110786500d00f843e181e5002d80740c111942181e020130b228540e075480f4905000300781c0081c04280c91903000c03a0b00c0780c030140c00c0100d5800d4451404600b4801d070796851020702c0260000042018040545508182c4005062900614000c40c1709480314280c3c01d080c04002404100218060305641d10024010b440341c0c0c00240854034401e101c00c0c00d003400c0e00d0707180c4420ba01501c0d440b2002085071000200300900c4045080416008a00c216828842c030714000d002d4014580c400d54441c9443c0d00f04040490001d600c045040f680394802402050800701138604c03650802600c2c0030281e5064102c541000480c54103561042d02a0450109000140b802d181d4255900c0030a80503545880c580d803c644000052103103005002503900c0340c03600c03405107000e169482c141d8028020004008500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 669048642 1250 669047392 669047411
    0x9061d0a1406010b041502160305031206010e0604030f05070b0316030605040b100302130503010609060905060405070e010f300b030703111c050307060207200f01050a020313090b0103 80
    0x10a400d4102e4048003044e5080c40d0804140c80c24011004a946055118207484401c00c2c04aa942200065025070b01564680c4204520b14403480c400400d11070400001030040311195031400c05880aa9800c00603400b00300760585400713498448681c2019038400c8012041014100c1403160188144601e540c01741b000c640d4035000d20065440326a0f203260700183d01250100c1581c402d030b002d410360050059450100300d03564004642100c145802283e000c64840d58180703d500b005000d01074206106640c204424545114000d0080b1003c94015040100030fa400045183c03190304074141400160804a0809a241402004050310b007030641c1c80c211700f031168440903840d02084a0301201c0e00141030700d02d10403440041102003140030542a00c1400291b210b070000c64002c2004e801c1481c8240c1006903103550900b4140c002c60800f81d02e03d03c0c41c0c403407590b45100b503445142036600c42e02c00a08040351a0047d941d42030382980688005981d422049907400030300e1004030b82182c4410002a00d0822201c241c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 669049892 1250 669048642 669048683
    0x6180111030a0503070e0f0d05010f0605190909030c05030a030501031e15020c16080307020901170c01030506040207140a1205040506090d0606050a0b0403051203060d0609061d0a 78
    0x1440740801d020403c140002a0880d000303510480d904030380100040340c0c1d68140800110b110743c20700f0068600742e56890318008001d89500c2044082c0504a4100111440200d03c55410401c5801080c1d25640c40d40c40400c10103000305d0000b65040d501009503602c51084007001030080400344000c2d9440c100f100e4182d8045182e440e403c0b00c1c1e50350051710b081c4081c81002c02c1c8030081d60000070b81403968815000040d465810b03102014010b0401d10000d150744602e1401008000f81c01030b000f004c8114120b400038010b640b800110030440c000c0c01e0038041600e50364500001c00901400c1780192010f040382007207180501e0007252540c5076501c00e8443c070000c1d04180c04203c46900660060940142040000c11100d180c0b407401030340a10700c034410100f125a250804a45c140d581c540c0f0030700c6240c001090610070490305005d182c55021240c81c504d400d500d00b45000856100342c510015000d190b03580c00703c006100c403a41207800c00c00c00d264107038503418580c55000c40d42ca030070f1082c0540d03a10503c919515000007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 669051142 1250 669049892 669049897
    0xa03060b04140f24060306011110020d0f0c11030304110a030f0f0219050307050904020411040f030309080102090a050f042901180302100f05090312090f0d0b0a09050307020618011103 80
    0x45c0c521402c50303807901e00641d04c040a100c1390710301502c2000c041c12404410b03400104014800703003901181c80511514a401941c6000ca8920107206003ca07020391484800020f480d0b019400080b25645951034501140d07021440340c2000d018500c1e0121390070f00348482c000440361264420b0b01c00a800c0c810000512001c06c0080c017820750f2640008004000d0340c640502e07200c0c5c01900050000880a8070160807a6080c0d01c50750041d407200c0202d035400c1040c150449282c000400c1030310700175440c0a02003400100090030340d004191041100380c00b41d1415440c0c540c4428594041c500d00304080c4044580ca081e81d0988604103a400104070408181c14401071840b41e0044036070141c6060407014100c6c6090712034400e1103c1c0c03103040080c28011441183d0341009400551007401c0205550384840d03000b44102c41004003a100d024280400c10100011401d000851341f2082070a4000307220009440c1003410b40c880c00002960254000c1650007181e04421204901c10750b00744c071000242d043c032700296034490 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 669052392 1250 669051142 669051211
    0x603050f1302030c01030e030c06090a0c060519080a090606060e130b030d082d041502030f04030e0105070227071d010305060f0603040308040b150a03060b04140f 71
    0x40c0c00000182c4c0055002e40c010040c1c01e4201d80c107607030800200300440b525040c0220f0f00a030840e40030503d04014082203c8881020301084d1801c00c2c54080c59020540000c0042c007100b40401c054540001c00500d5254411924150f008500780100c03503031820001c00206810311560300c10202032f208401000111300c117004140c940039000d4070701006200d6080d02d401000900380569201c0728001a030200d200031481500c468400040700543d17041c5802d0010040e000c4c107000c0c1c64120700c100240058201c1e840d03c000e5000c1c0e450311340751805000b240300403942e600070006c0c02900141250592400c41413070b10700c000c4880f400082d8489569507800000ca44402c501c441c0401403102c403480d00c03000c5d54407a030400c5a00813000343c203d040f14020b08010a210780d108640c2039000401103000d120801008072812a0000b00300101080e030410941c001400d2903000f0300c8020302255440c4045910380e126a0440210701c01203002d010081d00c1c01401151800104954809040c0d990741c842106444c203085060200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 669053642 1250 669052392 669052399
    0xc380d020a03060542041a19050a020a0b04031103040e061003021312210807030608010b0622080102040f0f06091a0c01090204020c07030b0c0703050a120e01060603050f1302 76
    0x400c9400d140490b4117042440142e49002003c100120b1514180f941844030001200c1166136a0890030801ca903408580601e00c030b0400204100340003107150f00140302003449030030646e100345649540c41c0030b96402d071100d404620b9a0001185c0003c1407554112641d1003a08107448201104040420443c1248110380d07090031102c8141da0300b403221311940780f07104480380d1162013040420350788024220780509041e11a1b0313000038404810088143d070706014241c000c1c800503001307000c00300a04002481038060060600400c0552080340b840c2d40c00040c0e84000180400c000840d038854464004070300c05c3c549402a482c40715414107000445900c507500030400c81c0d42c1191304501f00e00509500b50740f20351002406203e550340725400707000941c0c0caa1004200c000100d1000b00400b510350b280c08410060000c0c0102c00c50340f4140541c50200390002c00701c6c0c402120034980b03d00000590304240c00100a990040c0e1859840c10740045041901540039a010361407400c01e54040d80d54030000e030510300c81780d100000d40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 669054892 1250 669053642 669053719
    0x1707080f19030c02060d02031509010e01120503160506071707050306101e05091305040f060203040c0b031003060b030109020d11031f0204030c380d020a030605 70
    0x6014411101d400354400c0c40c1141140c1943d4000540a8110390310200400d98004103201c1c40010341103180301903480585080200e50b04d014400c903101101445103901800511a901007045030500c115000c0b0741420250541102441c1410350740e883d01200c8180103c0c0d041224088001c100781d6030700d807080f039039582da140c950f076a0042401010708001e1240001d0180030701c40f84500c0c03088110005210f02c510b0f69010703200d00e404805c06c401815607225000049142c107003400013150307d17152650790440d040f003000350740c82c4c40c1c40c58455421001c80e0b02c0070790003000120a000020920301803a40807a40101000c0c001441503808160880d001610002c0d0700c0100840b0f9580000c1140c44174040c09040242583c005500a01c105842900352900641c591580082c1c20b00c02c2005690895001d0400c1c00711850404054100341c880c40341a41c60107048010300b0060020320400118100c2d41f4141c08000c080d91501607919000d805404a40180b5111b524088240401203000c4501401c0e10070740c0c0340c050b10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 669056142 1250 669054892 669054913
    0xb01080f0121050d0309030306140d200d0303020a0206010e220602041502034803190c0302010e0f030a0302160c060507110904020a090b0414011707080f 67
    0x10348240106092528460181c103010701260040c04680c1204d101502c021803928100d160040c04c54a10740c10800840c00954402203650315a8a1130081c0658001045c00081089038445071200d401000b2240d4030042c5032245008166050300500500085034003103940700e03600c403203144034100003c9030441300e055880c0c4c010540842c5000003044c40c503070044a0040ca0107880b0b10101c400b45680d401800c015074000034000c400d10030045204090440d00d14800072001c00829041c1c0c3c5107844481c1001c441c104e44003220f18240b401170007215849040040c40d207030381403503a180140100190200a0f0055441c000a80902a10105081d0000300b0014091440d01c081028144c1c0250842903d1845403180c000b046800108150f00030350180007941c59a81e03c50f41c280c0340c0414180c40030340710355001c0c0946006000050306d0358100d400c285e0310200300218540c04e404001c100100b100b40d00d4480c0c0c040380900001030703030032454500c2c076240205041650401c981f10041681c0d20f20000d442c40300c090340440307400f0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 669057392 1250 669056142 669056159
    0x60c0605060f0301050c041e082508060126060402100c030201060b0a08090609010c12390210090c0905070513080313081915020f0304050a060b01080f01 67
    0x168404030003031242c41d0b2400034401090840700201e4006441034000181885440c40d4201005c02c03910000041203490b5090880c0d1589807030101c0d21610b2040c0b4441c1c900b03110051a890038101401044e41220090340e59081c040f4040032003d00795004180300070401030300c030340320208950344240d401520350540c80946010480307000c8500c0c80141c00b15580e9110209015180000520b205406503451842c1c42c140050424109072014100c0402d0303030b00d001c075a080b6143d00502e01d041c4a40342e1110005510784148800c86001c640400541000d0b6500d60004030194648200d00104007610340c2143c0d81c2084242141c0205d48420402512003910000e0402c4400015000103501450754078080d81000107910003c1d036a43e40e41d800074003c2e0303000031600002190580104100030309408000f040980302071f000740210f08410b480082d103038044401c1c00c449110803d8044410080402244075034a24182c14125180e039000b50701107520321708024084080703611601c0c070756024800c024280340450340707012581c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 669058642 1250 669057392 669057401
    0x309050d0e03030c070e060109050307120807030531080d0801030f02120a080415141e04080a03080615030c18031509010c08060103020a2f03040f06080f01060c06 71
    0x141e40d06100422602d14600e0042c440300004250030403416809080900024000e4011034004a00980c02940200f200c068600620742e02280c110144075139401d007500307046032184a0b4194489400c564071040800c540351400c00312201c10549803a401c426511100c007c0e80300c180d00903800780003410070b03030042c804a1202006a020207200410f0480404003040707041c0c0c2481040c0100703507091040810200f107010380145070000100118a40b0034a00e64800c1d50050031800f40c020000000c0354404035007001c1c0d148070000c54016051210884041841602d0018080001100c0140c000d4690021003000b80e12070f241900c5c081c800380d003803441c104000310f49410841038003500225494411503180301c10000e074040407240220340010012a5140c1c01140247c1103a03009008281058410410f406d20250700400380f93f0200b4285521080d2401b550041c05403071440061000454000080e0015501c5003035042030044a800b5120014583e480514210140d90240f2880c0c000c0f0301c10052180024030b05a00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 669059892 1250 669058642 669058667
    0xb010e091e010b040501030f0605070804081611060c21162006180906011701050d020f1306060810060c0803041b08010c0201110310060e0a0b0f040311010309050d 71
    0x24040303c10000007130640d07100307a10541d074103020041400c0500c0158045d141d030044881c2172401c1c0a080c04e5558056900c00c0300c0e01c05101e16202c05400d001c22002d101c2402d12290f0050020352079212601080e40c4074100002c40049680d8440d11402040c9029410344102d80e00d2040c2d45d4030390740100d442c0d42c3c4141c251002058520784071a035158050f0f540b13540c086d0443c41542c204840c0d540700804180000701030b01800440c1805024514501506c000c1c0c030009054030811b88180c4403a164070b1000c511440c4410300349960000d10032107480d280808643c40748003148c550303590300da03029140c0c1c0301c039514000340034050b1f5030001e0505400d180214032820000c64100c0c0c03103403800e0120414410041c10840c002500b044085035103c4404080302942401542001030342c96401c00d1442c00c10500411012050f48200c00902080e285004401d540300594940100f41e94a10329a540c050740c00c0c81512035000f0b0004413051a000c8250345002c2d4404c1c8902d280103940300d030040242000c0090f040e1020b0281e80d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 669061142 1250 669059892 669059953
    0x1e030a030605032b021c0c110414060f010504120f050c100507110d021f120b030a0b090a120c0c0e220606051210180b010b030705070b0c03040b010e09 66
    0xe410002c000c00c1b0406904a035025aa4014070181540740c14100749220750b0b2018421803d0040783e83c4010b2200700e440386c101800300c0303074086200c5892005803013038021036214403541e62600d0002000c0c403102a440b494202c4c130401c150385014284004200040a6901c03501c80095030030300c4074000251103180d441500c0b0500a11802e035150003607000869100b28000c000594a00070032000001035000382c07400e01000d1001c20140304c540c1070310002c01c0c2e03682d07900803001d0029002c0c00e0128850303100c1409400c400d10b070014003040301ea180707210000d4907000c140c0c42304960004643d5000240301d001c0516403405031180c90510005401496001105002d8204081d50869600d000c00511035841d0303414100c1c41d0400001421001c0b250032007030303070071240301c00c620f504500d80503184c160001d000068414155403902c90030b00e07100d17114000d0446490180300350080600c0c403d1800e114040c0a0380c005144124440e0030004800d0fa240c9035002c240c2d00040d00d22507401e600c82c0c00d601c00f030145d8201c15500e13120380d201d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 669062392 1250 669061142 669061153
    0x312070e06040618080f0d1809061203080f130b0403110106140a05060f090105130503160819050c0d02060c0d0e03100b0f060c1e030a030605032b02 65
    0x21000141c0c42e038080d030f100b0004900c0c4154421140081c00c600d0fa0000d040c2c0f5400b5290241d44105821384039001e1034004410043e03142d44040180e201e4403030b440060b0059090420145890380d40903600c510345000c1c140c000c5500c9100040100d50f6002c01d43e8401c2c1005070224095031420790307450650190240003141840207802c1d80c218820001d2090b030b0001c14050020b0085160072a051048000c2150007990080008101040090700010101d0380400c40a01e04941e0300d901c0141031704980480743d00310b151302d8004c40c6140c681c112034006100c03040d590140c0594011030041c1a40100842c84582e005100790803850340d40d851840e000407815143d90000d0005171403c4014100103042414022030200850382988103900141000c001501e040308048004011076400ea5002071201c03960f0380350b480c1c41201c00080c000d0f415a0306100508803d4200e8010705050500d088650740c59400c0300400d280041c1ca0584c1c0040d50303143c00a180350032400035803140c0805241c50341406004140d030502400551180c0d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 669063642 1250 669062392 669062417
    0x70503070b091612050a03140f120a0b0603280209040f0c080f090319030b0d11040f140402040c020c0904030906140a120c1413050901090905031207 65
    0x1409501c0384100005400b82010f1801010300881e1082241c000c3d44d0104c0000308403000003000014041c815542505007034000080280b041d40b020312410405c10484500810052200410001054001c8840c490280081e002d54014822180400c603105d0b0f000031084000c0d03a030b030855003481c018941900e444016152078800400304040e11030040d01202107a9031000858844c0d54050b000130b8000303004000188541c103008000e16564040c01030340500302480449000000c1e8040d0340840c500010240c60007040100905200d84050080004640510b08091884a40204a204111a010301d800101c42c1316100c036001d00c0010900501e000741035104180e940507040d9201044c1910a9211345e450740c901c01d04040004001244400b69a0401403081c0410b104154201c20f0042c003003850100006014001d9440c100c4600611004aa13542040061124168007101130381c0c0c81612010b031f40300380c1b142c0d83c4c07010300204541481001804a40042c04540300500c401858140c020a01e89080c06d01202c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 669064748 1106 669063642 669063653
    0xb070b0c071a061908030910020c100c0204020705070f031208010f061209080309030c0f0609062a0409050906090c0906040f061a07170a1407050307 65
    0x71040064500e41301c1030140380c55000051100c1c0803080e41e03801041d481e40d2080108078000d2600d590303200b003160b000090f03594800c000602444c80e03d480c0c26504603402c2c0c038900000c0b640103408008400105004000c8040503181406005182500d10b140c240160441600c5500a10100d4401002917580118114044074060b0410340c06140500700420000d060003500100850130200134070500342c03c00006003504a8101040b604400e180b271703542c02e548040440c5c090f8119441080021088452054010111212440d181103424505605000c880d0040d07049080003a650b4410480c0760982001181c0e00700c070260001c0d240c1e60030342001044040070014000b40c06161144140380c54143c060f4450300051800070002442940e031146508180d61096a003601c00000c071086041c1481e074001c040b14103000e0300d611000510400d49003403282a410a9030141d900303000c1440984007090 = true := by decide +kernel

theorem cover : BRFrame.Cov 668884892 669064748 := by
  have h0 := BRFrame.cov_init 668884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 668884892 ≤ n) (h2 : n < 669064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
