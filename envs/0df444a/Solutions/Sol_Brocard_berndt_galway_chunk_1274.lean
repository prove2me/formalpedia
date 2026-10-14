-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1274
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:06:48.368242+00:00
-- url     : https://prove2.me/submissions/21c9258a-e6c3-48e2-9019-97e3ea578751

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 228956834 ≤ n < 229136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 228958084 1250 228956834 228956839
    0x1050c1b0a03141e0307050a020d020c01142104030207050a0603090b220f03090e06010f020a121211041406070c051e0603100807090908120915040605040c0f14 70
    0x3210290000700d1881404d1030604c130b1142c60004010014070b190700c10300034401c094240c0e00740c503500307030480000f030b40c0d6144c501c1101c0d408991890510500003604402400301022144940d8088003800704c0320b00c2d507204090f030b82540160031103d0f061001c0d06100788104000e2909107000c0004242c1030b1145101c080e8090411031140c520130a04444101030700d6990700304203400a04601001009180c0900b0000c000c0c07080702044442d03100000c1041d8043c80340340310042d183d50058809910650741d5004007441420b05102400304002c0b0025690165200309446c07145052a02981c40307041819001d8100940c100035441890704000c032400264a890b80300007201c0341070360007012050300e0003480b02100c45181d40058000c540401086040403a42d0140c10031640c204040d1105140c950790120207442e41d02da00a0601801084a02144404451845d80c8401c8000c29280207492a05029201e024183c07025114582c450b030a00042c451071040c100c00425412031445030540c0b411048501416003030040743d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 228959334 1250 228958084 228958087
    0xc080703020a0804090204080606010305090604060902120d0305010e10060c06021c0f09031e0504052403040b010f060f0c0b0601031d0a0b060f09040f0f0501050c1b0a0314 75
    0xc15000704030080700998800006500d8a4440b0103950080d0490300c100030440c46103c01055040d4080d1103441c0c022244180031b84000d9880c1c4d00c80b60301905201e04103d07000116290104103803102440403410840841c1e030040740765498507081501300803014264000e8070f07048804c108080b6802aa104c50200e522500c0580c43e4000d07a01a0340d142c040740c00320948090306105048050101d20f608c111b204910039101d1349060034940c0b04030700c4d4014090000e5008100200000c0c0036038a01030f41040d00c243c10b0001d002c02c1c020b444825110a41e04107a8040b81d503101e0240040c090542c20302c60340300203000c26180515a070740c00410700170314010007407034003912084038100400c507241d10942200c069010a0314142e1010a50040e0030381d581c8282c0082521302cbc20540022840b00c5c0390411000d01d10900040c6101d403180c07256120015038280754101180e002004241c0340001600038040e19108442d00c802240d240d62811500d440790300c0545840031501d4010481c0000040d4100c1001d0240518030b16005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 228960584 1250 228959334 228959347
    0x109030f060615030905010c020111091507020d110109080309090114031e210f030703020a1205010603060335090a0504092d0309090504081612090b0a0c08 68
    0x750007458903410850083d00d804054100d040d425400c0b0002d41403040b002041a0b100f030712000c07400c031292603d0048052004005121103490495100e00cc0c0c01d1a1840c02443c00c6400c4e80010b0301580c450100300c4cad000c0308201201c1103d6822441d085c0041248902031850501d03031000050450105014030707e8400301d1002055031688040051070078840341241d544007403540c805041640e90713150700442000307017070001c2808a01e002090140d4191042d41540607085d13458481e0240d02030f4220700c11000410010003150b00c14110342d4000c1074001d0100303860004085007103041821907031480308100882101d0b28000f00540d0000c0d94414846ca01200041d1a222440200000d8a1001581c40940d005050043d410103200d41010381c1101e141141c0b00d00c070b140b4803040c1354039540d8048a01018010924007042005900031030741107039500502c0796070b0851506032401c00941900580540070340344e40801d561240c1e003103600180d500010389610f0f500c0c40d041a8080034020400c43c04000700800c101c0380030424 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 228961834 1250 228960584 228960593
    0xc0c090a0e0a0501140a02040602070b0c15150109050103052a090a1403010e0705030706050706020702040603030f0e03030301360203160914010f030207020a08030408030c0f010b0109030f 82
    0x441d0050001025105016420709145028000007034401900400d007001040301001148200c800301d03000d0b81c01815607149014007214542c0c01c0034010740d10310300800e07924045030f440301c2021911a8042c12804a55040b03248001031021010344c01c1b0a050603e40410700203a035842382100749515058029900e03042e1b0003007008504500504e05038580125190380045000b0141098000012105800070812540070380b407001d0f03440c2d28510440b03030941c0003d103080c41044d205038000c081e070a0040101600d004159408641140c0c1c06500c00d80c00124240c41c0c18461a910001201124a0803030085085504200c2218007a50040c0003507050304502c200079a0000300e00b48502d00d11b00703101107800c54034bc1c0346c1103180e01303500303040801c24400060315804082000603180305560041c0c181a17580d03980d0342210a1090303000750301142059a102c40d0080340090142070800080010b0f014100146880c0c8461400700c074542443d00712001b9403230341481542681a43d100780040300300e035004218481500d5103402e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 228963084 1250 228961834 228961841
    0x1e01020109140304140d1a0a060308040b070b0f04112107030c051c03020304090f0b04050103050106090e030c1507050c010e070329060f03070506030109060302030d050c0c090a 77
    0x40040440c890b5400340062000e010010b08121030030000e00500302c03d55a4100702e20124898001400c01b220110040448490280c00e1a0705c0b02d1908000245a5140c0d190502940c00984c4040d8180703000045c200d0030031408210494004c44014020041030510350b81c0c128a03001014810f034004c410540700100082c2c8d81c0c903012901009070340283d903865926800c00c00305084440c01041d000e02095034241c241920a42c0b680380065415074051410241407452203009407118603201b51030b682e00d07030101d074400b682c441c4034540c0210300ca5400080c4035860540c0317404c20b46025040d012126007052000c040e65807004100300b101c4524401410740b441e640d0307641c02c2d5124020801c0d4000c0c06c0d0301c2d00c4440d5180030310029400f4203030b9004090000340d515617103c40700070300786419100410510540000c02ca40e070416209100303100070010140c41e40c0c1503c81000c6011134009034803030243d203500ca40c000c0003941070a00c28041c00d06820f10b4042d00d007402c19000c0a40d140000c034400c500903950079002a201204962 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 228964334 1250 228963084 228963101
    0xa0305090a0302090903070b090307110d031106090c04050702012f13140f040204081b04020c19120f020a0f060b0901030803040b070306060c080c0f0d02070e010806061e010201 77
    0x4260280701d081c1003413600e91b82e80118a08441000c481404a4500c12000040d103010540c400c940100001c039280500100d00300e108030403024003131414035884c5201e4060005501c50185280200245041d2004100c10f586000d4003580542e45482d88142d111400c508603615000400c1c149124401022404072903288910118052001410700003c18968907003051080304980454030400140c90700c1040000300c2c07190307110b2044164028080b114456240d44400d00d5101c20050005041c0850702017054181901c43c0d036040750300c1c0d042c24442010048003e024082490b094500b594011520b1100650740301d14086002e0203990105101404001444e0031010411901501074000c0396582c3c601010300750025141103031404265000034840c0d41c842d114860449100f0780d51901d501d400c0d920341c415980c5c440c4650300220701400c04405000041007010307036541280d030741c002c2c0443c1d0724000141c401d00c0c106810440b090707041401403009954840d80041c0c0f0f4010400c55801c1884a00c00c0189e00503d401c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 228965584 1250 228964334 228964339
    0x60d0c060909060608060607200406140306011d180111040b070320030d09480b0d1a0306010608011d0c07030c020120030310080303090a0305090a0302 66
    0x1000003088156010502004880802a00380441900e81405940c0380340c0860352103070016000d011940c0800c05843e201d5000b8013003082c0c1806046072640201d404e44090340c008503480d80f403601c5e110100e410304000c0c860041010140340c0d43c0d414807404161826030030140a8481c00c0c4840d50300c110780c804003984602051380c0c06424007690b465613200140b603181c100c0d24090f00451056520100054000a0300c42d900361003403009140790006444000008001001003a00c000b40b06041ca9011a1030241118149a8130031000e11880000042e0f0140106141c40010a00b15410741c0100010320940303060301c10f0001c5402011400d20040d51103c007a4405284001d0362509c984c400000701203400580c02c5040e15480840c03100c0d0280641a0580301c09400c1d41e1036002e4920810074000824810718554155910503d0400290b028070540c401205880c02103104603034000005200040e03440c201000c00070515040a0350852410802c11034551030304190240600c50300094403a032030b991b1545a0005144d00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 228966834 1250 228965584 228965603
    0x3030e071e06030605060a0801060f0c050102070b09010b1f080c1c060303030e07080c06090d02091603050f0103080a0809071208070615050d080901020a08031302010e1c0803060d 78
    0x4001e8038441501d5114010110707103042004501c0f4203068044942070349071a110b41a50b40d20b0034008852088450f0542c6d01041404800350b00020402c0c0014412140503144004031070910024490031a070840a840f0b1040010303100308007103101c11520032903880d440c505000d80c00e0390b11605070020900c0f50396003281c800d564201c0c0ca1200d25240368019404e40c2d001350380421149100c1e20040c2d5030f40107036000d08840c81e8401000501d01b840e0580c020480c0c0d2001902c5a90800019804204a00c800765454a400310313481c00741503d91a0300d0b10502e03911200294201e0740f654550f0700c0c2c01c07090740b04183c1c0c1c031001c2100a000040d25001c040000b007004114500441c0b08145640c00c1058194000100480d55903003011101c181810059000030141ca07001400078007003004682d20140198802094281580150595600400c035060042c1d031040015404c1800f580da060301c001041c01807444285841250249034445254040c1c01421950f6070381300b000141c0c2c0340c0359840003c003c8440d40e040104071341300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 228968084 1250 228966834 228966869
    0x10b0904120f0203040b09040e031b0618010203070818010b0306090708060f1012050c031209040b03070e07050d1d0f0712050c060a03140a0203060f030a0f03030e07 72
    0x60503581d61140c1d4070240e44403901c032420000304030380300e01c101d2258040707100040c40b643d4002d1400d0341c0014600c2421004032490024400140707210356006c3d0401d0702540e001041001190312102198140d610924002140f542c90104030180c9409c1d005082d5505074040d44600b051440303402d40c031030303612004d0045c08c41d406450401c4c8410355401e400d004800040c05442c002c50403440d20310f49228092981d0840c1050454281418510b05807204a4280d07014401c4a52040003a2070501512504c0208401855038803401c01040c84140d6140b03000ca24001c0e80640800c010300c03ca460041c80c3c002d0058917042d030348c1d196041d001c880030302608007450407251b520344601c07403441c4000240344103071200480c00e0f03d068039038400403442e0000d0228406456904100100c000c01d24001009001d402d49605000504c503078004c0c0030004400c01100e41c401070035070010500031180b42c45000441d4000045000307150021282c1d03139508190390402c000409050311400c490103404424080d1030098004e11003140d04d80213 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 228969334 1250 228968084 228968093
    0x5030c030a0f0f0506190503060402010e060f030c04030c05061c0b030c15090306012102060a120f0902010207080102070213051b0c0303040204060605071a07020102040807080307020405130b070c05010b0904 90
    0x201034450300c0c42264560519911b45282c2c0a503c0300b01d035001406000150f42c1d079001034030120000e50710306070300007030420252482002c010040c6005400071090a40c8440c02d610381042c10005a8021602c00c1400b40030011900d00d501c40100030102e0b01107400304800304480042840c0604011110340e211071a0b5850280348040500030b001c03c0038044045900e20b9a80b460f009299031501c0769141c00a00c0c11850140140c201407005008410051400721310789848034981004540c041c03624158115154000c0206640e8100b0090015000480003145019070384e030b001512044161110040040d00d0303a001441c00c698006504040310703454414150784046c0a0416a120307807003128101d2103245011004139005100d6010361b50714613800000b0b04d9814600d05610203440f20010540380c2150b40812022500d40381c2408030000408400b0300031916456144108825520014030080301c0c04543c1c521800400d00104240d60004000d040c001081e5056060103405402000d1002d90009040b0040c0000c10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 228970584 1250 228969334 228969341
    0x60c050613170a0503060906090903040e090304090603030804020907110c1309120909180b040305130302130e0c09160c1e0f062a1116031b06020d05030c030a0f0f 71
    0x31b00e021030b2007c1d1155584d804100320000c041d90b080a07964810300c0141308041c0d1100407981c01c203140703008607801d0030743d0f88250b48140c4080740c00071000a40b1000511086040040ba00d41e0800030f03c3c01c114503c4001c8440c1c880c0e46000800400d4400c440600c84010401c1c2141c1c422280d2076000080794407403440e0000098454815845054041c03480c0c04001c5905d1801c0044c0f8210860b40584050b4440c1c540c0e41b002c54441e003103681c2c038400745000721400000503550783c0d085040c0a03030041c2c00403d0041321040f0b03590425800490540c0a80004010803103601801c040c24074168040c0e00b400c000481482c1880c80c402c9100219800c08402001001014481c13410365904010b407040c032007805692024031004144c180071609280c100350003c007102246500a100c5052261440c1080300d010b03c484110550b1510a035600507074618622511032a406030107207003c40c0142c0140c0c0000c09020584000080451000a100404000e03010010851a110071b81000d0f221112007442400112059120354009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 228971834 1250 228970584 228970591
    0x40806070c120207080c04020304061401080d18080c0409080c010609020d060801021218120d0905010605090c04061803060c020718180602030a090f120801060c050613170a0503 77
    0x60100820b2112400e83c800580842500c0921025284d600861401c0c44065000684122019a00e90240103944d111f41c51125009041c100020040342007081c10180c0301e08016005400003088102060003085000507201d001d1000c240d600140b04800ca040469441c02442030780c50740c55007094000601c031007007600a0061810000c0c0e0400c20117076543d007014200d10803a81954060100349001401641c8006144605080b0034020764642186640c0c881c110740d4441076060641d941c1d1500200f00303004092180b040505001e4440d0b82c1035050050b1010401e00840c0329046c10804030100460048000782544801581d11007818012040109406903c503003060084070183c50001c0e22a8a0000c1e890280740c02c00c541480741c0f0001c00c0500e841c0c91019500c014541c41100e9218042d06c0300081c20224030625003809076000c0d05070056011002010700348107030f105100700162203d0a0b8003007180440c00903000160269110b41100c094608600d003500c44804540207014041111440c65030400000c520 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 228973084 1250 228971834 228971843
    0x90c01020c0f0d0f0b101d07030c0212040902040806060307060c080c0c15190e06041809080304051c03020906090909121b10060e0112080705060403030207060f14070f05040806070c 79
    0xe5150300c41046c0c0e001c11f480594030700796180c070340f0021419444c020361080030345811a10540d20030210410013800c00b0f80c45a446501403650000d030410844200340101a08004100d01400c0340394a4900c005000d0414484003504000f0001100000c014080100ea203070f8020250035001c45204241c007618041c1c010080240f281080d4a0b00464110b200302180488008024034090074142080ea50b450010642142c004600d43d650f1a800003003070146004d1841a44030394010100c04101c0d002000048a00c640480c09041c014849944195240c5081e580711402c2607600c0c490075038425000c00d1400605000032203012000003007400754400445400300085401c003041b1a50184a05031001c102e074024400c40c841401c41034011f1001d9140c1d48407010015000c1c0c0341032800c25038240c913030f80d0420034241c6040380400e6000070810100030140c0600d400e04c81c6980750420150507803400c00900c01b04000d0000c81007202188000a000d400b500541c0c011301510000c0762014070300241c011344101b0304030304180d5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 228974334 1250 228973084 228973111
    0x1608250e01030f1512050f03190207080601050a090f0b0d050105100b030906070f111015050904021e040f0e0d090503030406021504210f0305090c01020c0f0d0f0b 71
    0x64140385030003001c0301c0c031130000d0280c520549450401d0300000511074045409025041c1c480c0c000c4038003040548483c0000751021065810541d80c040d207015050360004017113420210040055641c1c90325194201c0d52100030105852240840b920004e2041584180d40403501d0610320060020540c0074034490044444802030b041c1c1c54007006e54a074042101d212100e070f4030400004020a105034a581d940980342d007400179418035411109424440c400c0000c1c0d08031503949008690f00d41000040900502c03043d00c002519040c83c0c0c021640000031072004c3d900810641007184220b41390340c0e000100c5c0c00c100203400c022060301c15003102d4a44080107560b01c0002c11045010407640b50200c1100c0407a40c0d40c3d0024a242a4030755079000c0c00d0240140251a006228075441c201d0001c0c443d2071070300755441e13940e400c0ea03070343c003881c6c0041d04542c4040e02001c025072009284400d141d80000f1800e600c40c00441c0c41125403d82c0000041c0c40700d03204c107002094038040c0808542044480d82106015604c0524280c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 228975584 1250 228974334 228974351
    0x613020409091b0b120a0f0b0603010303020607090b04030201120c180810060501030b0918070512010e0f0d2102040317040317030411060901032702030708061608250e0103 75
    0x60700c0501900185c86911525a0f01064400d046544194411100c620001c540382003d04001882c5030026401640960422820001030ba0340c0016400080c2618a007050b08040c1540c0000b8046030000148290850b41c0e554090461405600000d04c000700041d0b14a00c40e980380ca014030340f507840c0c44000a0342141001004580c0b5800313802807840f144c001403c10032260355001d1031826110b507641111410380c060600e010500340c4032400c0240381c1d4081100040762903251000d00030b1408480c26400601e580004207800c244551204a00403681d000740c86412540402c42c0c43d10000344600d03800108a00139210280206203650000750044a01070500c0505000f2110702c40b01d1144400c681c0205144842049031999140140103000504018540010001030407076011445000e02c11a00018903d140d95090440c0303030070005200501840b20103860039003400e071040d00c400b56503040d8541c2444450710014520141d1545243c40342407901d00340d041b000c0c014204c081d100310040e030211400a41401c240307 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 228976834 1250 228975584 228975599
    0x309180603031803350304030903030e150a12021c0506271303050909010807080d0c110d02120a03030b01030608030a140c010f091109070f080613020409091b 69
    0x10208032504005c0c0d031074114061203040000f104600700e059100345a4403510011000300d00000d10b1140b4400d40710000c10605504004d40111240341c0114841e4000b4103000c602d600ea480103541030000316081a040a80c10305103044080e000d0500340b068986c0e003220300e0000800c50341c1c0180c0d0248106407020522440d4034000400c084802d11000a1000441000301306202420180e400711140645001d41c00c10342d051000480480307003030b4800c1c00e09a20040c2c1c24000303050188078070603a0302c0c5c26080c0a0f00802c0d56035140101030000301180c0740705440518541c1d0070b548500c0e0f6100c2e00005101b0503a91540c80602d0050b0080102e0415240040c0c0b42540c0402d40722400011a01e400c5260303211915000c1803651021010742c003550300c08d401c075500c660f170300ba403a0002801104940383c42240c4440801d810381081c0050040300030180c008000202442c0000c0c00d4101000d940c00040c196030741c10480c00d401c003d05010348240c0e40080d075140e1501071518140400c000142c160b2108005a50440603a02c0e0403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 228978084 1250 228976834 228976877
    0xa060204030309051f0509060f0c010b0f03030c07050d0c051302030f06040c020a0b06150f0403050c03060708010e0403210b01031a0a050d020a0801181a04030507060207030918060303 80
    0x2004000c5205a445245c889000d6009800d25040c01401e07980761218048000700690450040e1095982d1941c0500c10705150010806800e490280c00071401c0144001e00990307580e60a02c10079000d02c2180500398180642c5402c2c0c8000f5200140160700030b503040c8030f0710000035441141c2c2159a0020344020500c00d1070070740a000108bc0d4268002e0030f040c8256140ca21080b000035040c070360322041c04000004942105000f80c04224200b0403c240c689146003400360400448a450900c6030f0030041c1000b44485e008205a030540d82d501e4001016680caa140035030704068201d1190880540c80f0204102c0310340e054004618921003a602440001d81f080d85644520402894455000035061340500c00d600f4001c0c26001d656000070000c80610307a840c1001421034540f1410f4201900d800d800407024011780d046421130000b01400c02c48001d24164500404a007c2d04000030300071500061005d00745441030035000042c0110f1814800d9400c0c14a042c400140010301c030807800f00c0c0041038422004524201d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 228979334 1250 228978084 228978109
    0x12050a03050c0306150307031515021203010b0a05030901093002060f1302010302041e03030908070b0f0a030f05010e09070803042303030d090b0402090609060f0103020a020a02030a06020403030905 86
    0x706100301140c039081c420002c0783c00c000c1007d02055070f01c8207040000c2c0d0081480300b0051080341024001400c103450000d04100e03018100c0000c10000300010425038512808403800c91300d00f442c101d030b102d03120380341c00901400801ea0081c0152401d144d501c562181860100341c164100c4088244030412a02000e03a203440c02254400c4030010f403000000c4003010740d4940180c50302e1051500600c3c058076900790418403040c400003500c0503210705c00c05104068002a05e4409807900170020280030749000c00790380061181307240510040c0f00220702001030a010350031020000d0840c0034248250342c0c480d04c000c90b10030000c0f5100d8000e031081f0351002682c82d90200c11201074a61454029041c28541d0f07103240307403400d0445074a43d0141302c20040c2ca862010548100e00c0400d100e0300c55401241410300421450f008060600b42c403c0360f25205000e41681c607402640c01212003802c0140c1c40381d10604003a800e00a46410103505801002d410008029550740100b0a407407190701c03064026074030354041c4400ca03203004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 228980584 1250 228979334 228979339
    0xe01020a0b01090c050d1506030e030f030a18140604110105041d06030a0c0602031c0c080f0a1b080f01090504050706030905210a0807050f040311030a12050a03050c0306 74
    0x6030010b201081c8113400c041c4070703184142400c61810041c00302c450111201c140d89044c0340b05140100303018003903250050f5031040e46d56100070b608000d00300002c40118070028003415911943d80440790809200350f1640b1610070b420400854000c0c041d40070151703d64408803404c40f140140280300c4109980a10155420360380070756880a079002c1c00d80340c0d00e10b46a50260182d41d052040102c2d01c0c0006911006910141066601540c3c075400080d03101e01c0e00700a1200d5880e41c0500700400154060b62181810749d00040f0245055101d0321184070030001010f10808000c0c1c404451442d5018070740d000b10100b03004900c1491200309607a83c03003800b68100c0360300b600c0040180d0030041082200c64804c2d00114030850096042d103d41420007485000c000040c8401c407648181e0220303c2d0b08046e5000003040b6440013190800c0361804d0604908541c0a2007180001400301605010000c0a500c0801500c80031035071009261074081540700021b440c0350011214000000e00701800100381c005400156401510701 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 228981834 1250 228980584 228980603
    0x301140402090f03030c0a0506010b0301061202160506090a02090c09010c02060a0329041505030c04090501140103030e030601060e01080f1f0b0406122f040f03050601060e01020a 78
    0x120003080060361180d010b0961000c500b2110040c581d03400e000030004141d901c0e0003854480200d2a0144c01c280381644035840d14403082c00104500d50b04000803810b03070501c068005a0b10400980c80407500e8610450140c500d10400303040146090f030003d840000b407402269a1002a5a42e4a50710068462442c0040c00034181541c200d00508049014000800c1541000300388950401c80640a0b807a044410456502e0343c4003501075503050500c1401641100d00c08645a810308000202e070f91448941007441c080d0b1b980e0380e031200034803c00303600c040400002007007401c526580d0390800400103002108028480d0182c03500000d40d071801641d80b06c81119060710b5405040d500e008800b100007100505e0185207240710840d0107800003603e500030010b41030a420b02070701c4505200d0010002d60b0040c201c1c4070728603d00800f503400304031111200000c0c030426202040c2500801003002d0074074007541e44606071a0368a8800401042000708515041e9001a52444d141c480141d004a9440402d02406840b8901 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 228983084 1250 228981834 228981869
    0x70201150f0b0a091a0a08070305070c15060e0c0a0e090405060106180302040c02060a0b0103110f030711100b13050402011b020f18010306060f0e0a050a06090218030709020301 77
    0x50039005480d010019060103c0c006541d030008109030017001a81c00254070002a0304034040b0380142d4025004243c1e441d00300000e01d000b00e00034164125490000c0c040c11071514281c4d05156942e04084050004015000f41a080026010b0903a800c241c80c94804a00082200e007918142810010302c283d8000c00103080c1646016016039089180c3d86500346042d500a801201580f9640074540300320002e03a00401252400da840b0004556201d00018105414030303915071403103104130050314200030110311215941d0316029403d44811141c1804003505004d0012a404443d035190712504841009441c0b04440104a2064508a80c4200e03002030115200350a500c048054144038031901c5840544605a00c4442e500020a80d9420000780b02940f0500b000600421941c0e00a410042600d05540b5964909000107402c400e400180100d0303001c1d0b50b03440041c2424886030445001000d411200319601c0319101e030345030b0f0100c4090300304c2c40c0684603220000500054500c200e90481d0032400c0c00c0a5a9003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 228984334 1250 228983084 228983099
    0xe010b0319020f0f070b062809020f040504050108060f090316110409020604090624020303060613030b0705190206010807051203131d07030e0604031b1a070201150f 72
    0x1004104034145400042c828030756108130768002814014000d441d8614a881c01000b0002d00505403072030600310f64644071041c200d10200b0708580d0145d80702c41c0c401680b2004608100e500314044ca5002da035000781090700000c0c00c7c1c080843c0043c000d81c075040400d00b0f656101c0c9031560740c80c424180b0441c0c1c2040e5200c114800328000340c113000c40408004001042e15551034000801940090700304d200361940e5800c04004c0d80500c1400e1034840e54403136050000d108990790f0042e44902008040c940035490020f240303011011700300744580155078006c0c0d252400341400000101140c2041c5503050419041e035203c4050b403070000036224100d41c0c0303110003015800d041c0801d0000c1d4984a051901003032106000510303045000c00c06032009050600141c0d0513885032602880c0a00c0d4000d0144401d1500d40700c8130688000780491100d5105d501400c18104a01c2c56012401c1d055481260251204104003030360115485c90a44403805000168000d03c50103405401c90000c601c0b052141c21000c0303c0310f9a0030000315 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 228985584 1250 228984334 228984337
    0xa05090c07060e060a0b0a0308030109090c0b0d0b090a0b0a06030f021201170607051303080a0903050d03050402040b100903120306170106032f010e0f04150e010b031902 74
    0x100d20140d100c1c0c20306105a8410301940e009202400f01a0410000c000304050719114071010f202d000c80766032002900d59160784000d80b0060080c0b001c101c0d2188515018810903a02940c010464400b426590f0031603142e6420080c01800c2030203120700c1042c004540322140307500a89803000700003040e050720685029003c0c4e00401c6001c0e40048065028040c1c0484500e4904009008241035400004c07003003004c0040900b490b40003803584042c09402e114400b145020402c1d04001d07a40e10002a6580d603015034001e0303c042e000c5520040041c4508294020040c4e45504401d0040380b0907070303040c1310440000042106903183d540442c00061100101000811010381d100303e1070240c80d041c006010f68650b402d0340e414550480521460340e440311820010800c12403050104060500601911012503521401c2c0c0c0740170001c00281084007102030b0340d0042d41c0b401621010594000e00400c05540c1c0c250b00200005480d1040300c03080300720341c1c2c00028602e032002c0841c0e10494212480d806107081488051009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 228986834 1250 228985584 228985591
    0x50f15130c0e0a0303050306150301060801060e0d06060909050c010e130b0406030506040c0816050117090c04020417010e0a0b040209090307020303131511120a030f0c05071704050a0509 81
    0x2042a100310b400b0707198403490202805140a641d8482d81e0385420414403010f801c01807020340f1700340010001000307070035406911136054441c1c1d86000c1101c242d040c0002403006080301009094a450708900284948003035200482080c070601c02c0c0c0d052958048019107200c0d40159109801010030904030658210b290f22401080300010400140107031a070710394510b010401c030f5003103442030345202d0144a0190704002c1da0b05c1c00d17080481040402c40c2403400007071603200e1000044d05d205c4809404103a44960612401065810144c82151101e9503107101c0308031050004e500f84e050b075290202c48139000c000440d524194540144111650392156800d0005165000b03013200e41500081c03011400685d01480103100d03400c8440c504640582c107107121031a801d140001c014060081d9104806020b4030041220300c0700e00141000d558a0340f14803081a400f40000c0000f0013041c2d85440b90a6011603046005044000d000c3c3e00c0d89000d80c14030318000c1c0344500c40d82c05a50f03801011044100b00c185810404035070f1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 228988084 1250 228986834 228986837
    0xb04020706140603100b010905120c030f1f0203010e150a0312120e06040203060712020702180a151206230702150601020109110603040305040503030d050f15130c 71
    0x548403a54031450219041c0002103100c8003849810b01c04a45000c008410320b00c1e08102c0100700680c01c1c2c1001070b208110780d02c5014001c0e04081801d45102c40140004c0c0c50942018080e1805005407034032564480c1840071030445900c4030741409481c10b02151081c1c90503254850121074043d102d42a20341030300c00000e00090b82c0701c410b0440100c00550703400000d0901c070310152a4091410079542240090364044041040b940c0c0c081c07400c000150b41c0000c0c0f02600070040b810440d0204900300780c1078001c0d2180482c007030b410109105010100e25001c10036140700c0d240c0e502081001012185908030048201d01c40c08103a0101c00300b110000c9400c550000d03012054112a0f2400760b24403048081c01e981e0700312202c10260304803100a180c416152060650300132002d200030030030b644607503035903054014115007641e0040d0000310008003010301601c22a030280100408130303a2121180101d90025060440c2c0310010a46104003241200d07482e103940c82e840c08002096100100c14041b108001000c80d03151120 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 228989334 1250 228988084 228988087
    0xa09050703021009090b0916030902120307080403120905030a0602090a030b040501141b04030f11090115020d021f0b13020a0c170c0a02010f02120d020a0201150e0601030b0402 77
    0x140e90344040342143c001142c03140c41015141056510803265207002ca180148144010026004c10b00e0141f4298881c05041c0003e00c5003e5001064540026103811803891000150301424007042c100680202c91003580d4810580d0445201114014003a01c506a016804200c030300c0001100340d0003500380940c01501d484041d40d030303c1e10b07601f5002400b034a0580d05030b55540c03820350308600f0484c0450790111507901100c00003075001d13442d200148034504c4050809207912030501c04000710914456041540180100400e503128410704900611000040002d2b20552070071700312160000c5149100300594845c030f40d8000b004801410f0241c41c00c0790102d94440450307c0907006a1541e0710260580c52119500c0e20109040c43c5802c0c43c10b1800440450410354080c4180390414500082c4dc50500b40e081c601018aa615201705a241c0003806840040d03402c0080b410038600ea116502030b003011101a030017400180042282038180d88140d0051000415448001a0041d406a0041c0408500140005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 228990584 1250 228989334 228989339
    0x3030f15060406031a01030501260a080a09060f020c0102060c0a0201090203010e0d09050a05090105042004080604170c06061207030b0f060906120309091801090f030305010b09090a090507 82
    0x448aa0142d0030070004260f44000440c0e03006907004511140701c5c802e08081001d54103090f00140c0749064101c886c02107070650515018024410301211009550141441d91107401c494800303420034019000e41d90000b2403201e01c42411910000780002c00385010b0b0003400307043d03e45041c07528aa03071241d043e210940d900c039019080142c03024810f522041d0354a5014203810181366900a04d141030b5648114415015440d050025030b403604000c90440304d086800040c80080d401d8002c01d00900700c04080301c90304000c100021075400c0403456605c1240f00703901d890000030340c00c3e0325000315008603246100d0580c84400000c12504040341c0210480640d48102c8401d07175501d0ba9440f5101c0c0044610b80c801910070014003440e41800c1c1d0219422140032281030620f04e4030520541d54034040c0001092190b02400003064021240250302103620328400000d10100708c01d410003004141111108a0000f8035200c00001c0f00d2890000740c6a0f0504020b081c0d000030380340d10883d103000d41200d031801d403464003500c00300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 228991834 1250 228990584 228990589
    0x1202010818061f06020f1203040f020d080a0806090403050723030d1a03070303023c030316030b030a08032d01080706020d080f132a080106060203030f15 67
    0xc07244124802c042d4518020008501c1c140101020740c00301d800e5512840c80d203440c0b84000f14803061f041003481c1e202c0c0c1c0c81c1e0b074603410328016207106010302a41084a690f2448144444040100309255130790715048042d0f2148c0c42030000304002250b018000500070b0150070002004603629a0b0400c00c0d040ea804502c030956a406420755000c002ca050340301d80e851146407840410000f0300050150100c004e00713079617807444d14040e4a4000720100c80c0c0c1001c0109801d16400c03055a4031030b020803803600550441c000c1d031000317049a030f0354829079140030034410310720780ba0442e00c0c840e0142506d05100500034041c030110340e13980c0d0001904041c00351200c03940e0a80c1103200200c400c0c0d03d803100040c5490202101da5140000c03035070400e0341c1030f048403086412031042c0803502070300940c1c656004109a140d1908a40d61031122904918559a000b0690b08100390282810440b10300d45500c03940320000880c8055544116140c22240300d8400c000c00f58205000083c00350003082c0c5d25947c800500060004e500044100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 228993084 1250 228991834 228991843
    0xe060d140c0703091202010915021002040603051e041e0302010b0409120909051005090402130f0c031a10080907030507350705060a0203091c0203060906011202010818 73
    0x1000c1e0505940840c06105055100da8520020120355840788201100758000130001030040c0240081c04890b07900c0301c4400d901c200600d00104641c2c1c0b074111b494a4072080010041d005c203940b07200c0b600c81c600d14403402462400c3d1107580510341c401c888800303620314504401600300c51184242c06655807000705040c55101c1e80240d18030075200b1840c0550004914078081c12180380d82c0c004c407607801e19140410401d504c0c40d13600007046d03c108558048055072a031000032102d0320b600034400002e500b8400c0d584624101601f000b50394001c582ca0600c40c3d080081240e00c00c400c0000e010f540d000040360310b0307c2209805210265088440c5d902912074060700c9886440ca040c0b03096100012000c001d10807403844100514068881d030100315010006440071a0031159158807500415204007030018040c6515402001200c984020141034089000c20044214034100c840000c203900a014540001c1c000b80c00110740c041c141e03840302403211283d5120760011584550300409204104201c08002e6060030001c01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 228994334 1250 228993084 228993091
    0x1e0b0108060105120d09060c113a0206070204050711031207140909060f0109230a0504020c030706021e07050d032009131107140c01020303070e060d14 66
    0x1d00c81545001c0500140c0301140600b03000c180c108a040a54950707003e0002c60845002d032600d00951140f07400d20038842c0b0386040d01c2552000314a00050340350700b000014601c42ca1300a409103044101c6414190113091851840213500040400042c3c005182c940e00058005c489031900e400349400041c40d09146501c84002d140f920102c21041088140d0302c00903114441e0300c00a8036500b032401c0e1901050010101030300d0140f045d8000400b540c11030b4414030107440100f26114040314140c402c0040e0342c0e401030a403030405002e201d8600011895060a00882e0b81d2440e480000b0b61600c407564071407c00035080845240542c1e6800c0f442082000e00c0f49020340b41103405540a400c10910710307240501100d1306919188400b22422750880e0319980a90181c4520190540703444852131045000c940023021140d4035100c08101c04901c0b1001e11120502c480484030318a0110340c0b2a00c101c5005907030ba8042100c00d100014031010f034084e924101800a81803000c9039910104246280780b81c89518200c04a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 228995584 1250 228994334 228994349
    0x1080705030c0706150911120a0b060a0c0201030e240603060907260714010e030105013033050c0d0b060d06090203150114090108130c0e010e01080309010c1e0b01 71
    0x12503007101c050301c1040384c2500410901b0782007114a040c40f001c588240101402417040c00000f013701025a40170742c2280800600c1002030700c1000d0512410001130a1082e201c031001082c1c0c000000d00c00742030000e08140070b11010002403850034500004202c0b64034620341000c0d0a00001a501419a4010886000540380c444401da101003403141c0010b1110800709e03a2540300b60306000040103014040403403001e929840b0a04c01c41030b031900300c0d01c006482e0402c02008083c80315102901c400000548081640d10311012101d400081224400c581505e405842d41c00368403004001806039000558841c112990019002c903082031400c100d6101212540da0096034410340010400103241c1c0c2d9941e060564007824281341c0420407448020100358082e13481406d0603c02c60102246104091100c2c245003594804507202c182d40d01c0700440e01c0919070030701c00c1e9046092580c0020a656601009452a098060b501d1840720010340d26020114600d0139005401111800140d030041000130021502a1410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 228996834 1250 228995584 228995587
    0x5060103050c120109020d17040b0f0306010311070b070c03030608060711070807030c0302130b0d05010c120b061905040504090f0b100b04120206190e01080705030c0706150911 77
    0x81d424840d034543c4a950600490b45018224001a80d840500b41645034000e441144000c094041e00b401d90f00c0b6a4106650001c1e0126049403140480c00c010752180304281e1301400b0501000d00f1013080b030301030448028545071120700042c0302d491180d2540308885000e1320700800d80c2c69071068228100303d02a6682c000162201100581c80403040000360010142d0000030840146075807141c50b101c80700c1d4003000344600211074100001c4105500070704c02d017540040c0001c1d52038409181c081e0080c4182408000450110120005248a64803441d40c0820380a0400c625104810b01501c4c804110156078905101c2c013408007040f15201c034072400c10140d104003640017031400c450402204800006180c0b024500e00c1180900003299148140c03000c1300ca180c2e0070309602622510010300540507503e80604850b000e104917000c442e611140403440c400b0280c1301e040c940d0700e03162030803100ba100449480c03c03521410401030300025865840400300c0e0355140d28100f8015118030a4005541150b828008002d00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 228998084 1250 228996834 228996853
    0x301120213020301091a0a0f1403120a05041409060d030c03020f06181006062a0501092405010b031305071206051801050907030b0c070f0b1905040209220506010305 72
    0x5821b1401c1c41c0c00c0d2801c41d100b40c416440e00d000340000c0304060103101c0805800c90094441618104441c0202401c2201c0254880b844084001d00e00d030464410301051074480c5240d010a82080c14440d400303844007401240f60082c0175141038501c101030182c218110300c02c001c0c90f030306055014081d4a0090400380d480b402c2d40740310030f00440d1400f8403510442d00f4407468800100509500411100f00310700010482070080511445082c8048000b481d02400741d5082001c2401007014810104079140044807881000160711083e5800700c40e024016102e0304901000850125071113840414040c40c401d0048849941d15004911001c003040b0000b00c5040341c98400344101d01010030034205070120071000030001842e016000c40d0780c4104c2444081d00d003403c160301040d01400d0882c111262542c00101071000048a40341ca040c0308003003180c500f2100841030100c01c00f46026401280c0c0a60b40013000b0741856115450303a5048030356800401c450790507074000c506001410521140307000b14001c1d4040e100c07240 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 228999334 1250 228998084 228998111
    0x507020d0506074808131d0907090b030102040b1c0c08070e060a0525020909030a0903021207030215090906060c030703080601090801060e0415020f030112021302030109 74
    0x11843d4000d440104400400c0c5042c441084901490708004c840300301d540035503181381c00c1001000c440302402e201c0c0b0000306150b140c820441550110344880c01c0e03029404c01e40b4460181042c41c16594a5000d1b08500c004000c0405aa0010008810014001031411750303208003884690307100d44480b42101c0050200c0303124554862040141481107410001c80925000d00c001f8080120750032143d00c0360318040b4400d5003c0e4444c20582d407008801c414410151084640b401000d22803201d41244510090300000785c000d02c011096600d0000311381ca480b60483d085030708100004064401551981c4070388100040541e50b051045909408425036096507000401c3c14440302010040450b40955401c12080750b50300c4000013142c100c0b0703403d403400a026403540b200490720b0045940c0704100320740c00e00001040c2100940001ca000b203100324003410f400210003006c0c2c1c080c0d01800102090804045c00101b1078801d00c0300c65851040d02c010509150901144200b82c1280c0080c4c21860400d6500e101048403036 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 229000584 1250 228999334 228999347
    0x30306220c0c1707080418060302040c020f2808210f1504020703051606060f150206011e030b07031116030f020109050d0c210512180601090c0507020d050607 69
    0x84100008051403d51181c488500c00d206e244140d005518074111842d0806c0165400880034560081042c00018a80c02c002542d07541400c483d18214020360550100d0000450000038180712004801c00170346841e81c5a286007134103c0313801b2040071a00010442d802009403d0024400d0071000600364803400c000c55202031080c0004e42540c040c510400500000ca43c22038140c1d203510030520510310b0041880e140c4500906070710f6000e641b200c40d001c00b0205400a0031070300940b2221469088800aa0b030340d540180c0c1d0040c00409100d10301e040c90400f840480c00c00807005a00c1030b12420086901c0840e002004401d6214030380306c0b0b00200e03040020204241c0d000d4a8007a20100300e1000b44007031040703500c40d1510fa0a111080d01300f80200100c804040050016102d0319000540c295581d00c06010a400780c5141d00064180c58043c00d401d000495000d519640400080c010700000c000d40c0c0c2c2425503440c0142860201e440902c58244041c9005135103d014002c41203100d1130241a95051403500903118 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 229001834 1250 229000584 229000613
    0x120f050103170a08040f0204090f0b060f150702040e070b04060e0f0102011e020a030f112119110403020303070606151106040f020d020a030b27030306220c0c 69
    0x1050b2040012414003903015004c142c11641002581069521038030000d801445030b900002c20656102c0f00328814405481d079040d1103800259001c41e000d851410030008021515100c0414641007480b46901600702a13101c0e0400c5c0e40084220307075040703031503200c080200d800c15844080024081d801114650500d0800c0550048080c0000c0c00081e500e10012b0340101031000c00703040700a9000c0f907004492480b031b4105242d0078441c40810070403440040c0c4c40c91032036440b4074056085110700382d0f002030380344601f044105d120f10700080d03030072080455800454001e0b288a51212211050611021000d40d40a02c01000070354030440000503407516099085d26050005c503c281c050007840c441020080d0070114400d90b103d40d20080119492080b480040c01c00c15504002075009607000201004001950345443e00803441c1d007244003041c4444e603007150306544001e403030700401c0e4200b44041031940c01c0900d0104001104030000e03000c0e4a20101c0018121003405010100240100b41c2c00e600380300301369010010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 229003084 1250 229001834 229001873
    0x15040f06050c0d11010605180103060e0604030c0308090c060a08040302060c0309030a120f060b0c0c060702010e040b1809010f1107030c0f0303110a0305071709070501050a120f050103 80
    0x1030020b105011520b0f00c00c40c094010501c09141d070b003100a5071080d8818006060003e04040011000380d02d00c00080000340001c4450a140c00300182400d0310010341c0394800c90313050381d0300d0b041c40c07246940c03c4401e10b074040c0214807588905101160b1550301e00002d4040203e099803100028501418001c0c40d0460141104d615006c0030030038003203034100100880b144102c560034030108613115008000e00518407511040303e01e510f054400708034400a44001c24040c8040d10485524031011801c04c1842e00c6011002800303d102c0c20203140c0642080d41101707181d5440205845030600c0d0340c20b020105910111408085a50750781411403181056100e8181c09a0b01303010300c2030911485580150203034108070300c060a400c803c50280310030148240c01140e00010a4078813039031540518503014003d000140c1d910800b04424143c00c59001c0811403e040c0305400d03050042c0005450000191915440b05401d0010000c402c0001910302c00395009401500c0079107000020f031503145041000c0814107400b600b10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 229004334 1250 229003084 229003087
    0xc0115030809190801020d06050a090b13110d0504380a0b060c0a0501020301050a12110f040b040203180606060703050a030f0902030a0c1707052103040515040f0605 72
    0x10106049100b07a030200b40c0203072031041002c0040250300881c0b00f036a500c142415030000402c6040c3c0395142c1c000c5402c841c009e84400700346640303a084050070382c0c85603d46203411140313450300c4001d403075110b400003102c0d08070071100306150049641e4000280d501c1100c5c140c5950075450400d10b903e908411812070300700c6050711829250066441e860400e800007804a0008548407010141c1c9640d400c41200d40d560b1850040328410281171500c1400303900240316591240c805680006246001c2c0300d900c0494035801440c03142581d2a41c030811406296020440c1c0c0c10542e500d2901c0c84a445034030040d4000d50058480382c0c82c41d202c80070010326007070000380400d00506c1c081c080309000a03003140595260100506000c500540c000700300e030004250006000e9810310401d160311003809101c410103000c2e13502c0c0100801c410304456a141b40d8a0703080c0e115468101c7c0d6240004051626105c500b4414411070b0810340e85025916400200b001c0c207daa18a0745c0d150300058201b2485100d000c01c800101301c02d080c01d5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 229005584 1250 229004334 229004339
    0x906010b070f0f0507211a0c0d0504050106050406080f0f03090a1401120903050a020d02010c0c03080c040b04080709050f2214011104050414040b01030f170d020c0115 73
    0x701000304200700000e10402405411404104091000c207002d05010b1408401400419020b50000199010280e0f045800f900748107011f80550700206104121000740c062411324141c1c0381500400d0010000d4030507540e10368001c43c15980700d0152400500001005100090340b030300036207060006c4801c1e28030f1513a008000c003010079192440c010049880c0c19002c100a03952000c0103980d00500200d0380d10a180c07600c0889402c2603000400361109008690071100008206d00c0280d080b590150307548404101410707460780c0041c2c41030102540c0440e01d4201103041996a600785080c540194100d0203054020340d505001d030240620407598001800300011410741088000c0c22650500c00c500e00310b1348406442c0b1f200c1406414040d184502c40c204000700301d5099890000d08203900240245445203003450b00005c41c001140300e00703e000715080201074810340d2a6139125004c81103040421502001d010600d013501c2d03007540000e04031907240c02401595500400d0002821a0100b14013880313a60900300d0103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 229006834 1250 229005584 229005593
    0x151e0608010e15132a0608061207150203090618030d030510030201030b0111060103030f141c02031801020703020a210c0204020d0b09090a0302011b0e060d0603060c080906010b07 78
    0x302d90040c2e51003080c07034003e80050401019404051215181c160710303070184045c940f42186464000c483c0b44d40d50300c8555450b40c104020380704030045d4000510364003886042c8684050070710704030280305150044906d0480708601188154001384500759882500c800780600030b041c240062500e20200c0c3ca0100800d1900d2210840401e0381800064101540c41074002240d900440d8103004149130b0744115242c0790381d07030701c0c0080400c5411001c01001680c813440303803041c032400d10056680003c603c0c800041c020234090b2900d002034000511030360b42e084590154800c800310a00c018940b06010394040c0800c00f10b203080180081c003126000ca61115514280c5801c00e681c00010b841813030390b0444d000341e9150b994594110103001b0000f0f2007035005581c7d1007444409100000c984128030b120f50001d000c803000704000000a860071031182c2010030915000d075861480c02d0340040443e2080a40c0c0050850b44a0312100c003101c160316280c0c408518040e00348820b10404120071801003211461592906502c1d03520f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 229008084 1250 229006834 229006873
    0x6030606090f0e0402010c21020106050f061e0714010501050a050a2904170708010c020a02032e0203010b130918080d09020612040b060a030c03151e0608010e 69
    0x40c1c600c0c070b00f481c08049002c6a20803030703450005075080001a041040c03e081d40c607600c80122030310640907601c2c0c044009010b04100d42c450303107545401841c1a08101c8114407903100350040545040c804a0700b0000103000618983d1791a04869116000140560402c01800140e10054000d54450202c05908021034401c50203140400d8030b10f035100038000160211031482c4c6014907000b801040c50b10b040c5405800c0d82c006521400c80308514001d02900c0b410100990b21109051000f0350103810100440c01c820950301402e000b42d280b0b01c08650b00c039240490740082260001c2e00f00c161101e40004a50701032940300e1f172103000508900750741004403660380e01d04803d6011030004000c015510100381c48614200d250720070700c0b0007900a044295031b4486142021011030007240c0440d841c4420b00c010404034108600080180c0350b0203002050030754116110980a001c14940207450070341c5a09068035a504484e50034041c44c1800e250124000f400d017001503080d2130081e407035580e0940c800040c00c50034012180 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 229009334 1250 229008084 229008089
    0x203041706040b014103150f01030b130c030309060e0a150e030c060406051201090e03030606220b1b010e0304050f0118030b040b01170d0f030b030f060106030606090f 73
    0x1124a0340395102642540304e80b408108800c1d400240721a6a22007284480c00c1703620342140c0031000d650030740c568040e82120012040c1c4200703501380a07440c01840001e00d01a007040d00702031880c608160b502c980756a680b038890142e40044001680340d4400b042410b420680450b00a0402c071407125025007401c103162201c21044c1c0c804410000760010060312500c09000ca2080640c0c0508002d0743c0b03588407034000c0c0c000c1d4403c400d10a1040c048200026036140d0600c01d88502d01501030195155403545010003102c2cbe00003406440e11250000044890b04500180c01c80c020212907610a4464042d40f208051440380545c114801c0e0f41040d403882d5121030007004403010740b43c00b250090100c0d00398600403504a07441441c1007401c48400c03407001c01489603440350940b0581c450081c2c040140e803a4560f0502c42c01003064015240e44c03010f0a400003c0c0c0c0103510a10148014ac070b80001c0d00341c80c00700000d292140e4210745441c00d40055006015550b4580100c40107001c0300c2c02c00032102890104c2c0d450003042c1c0761 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 229010584 1250 229009334 229009349
    0x1c0c0c0b04030f11030309030c0f0f030706020a03020409020309010b01020f010204050a12030c0b010909050c100c03080405010f0603150e0115090f14040311070e060d0809031005070203041706040b01 87
    0x1800080f034890007040a8952031480d0401c49440745041c107082030f960707446040c9140041c461b841c1000141032001400803010400e01300a5403d00c43d16a9070314005e0f40108419109150b000e0001007080318192024520842e261400810100d01200c00641070034010b00c84008140d004001c02d010b1034590501000031a030101401c038580c20750a040072241c080036010b00412140d000400051445180d8202c0c043c030324000e00c165a029a101c03420805050505214407010036808442e0402280c09141000da11074020f20000c112040d442c0341c10021218250070407110f503000c03011003002c0e11281c1e116035860810404002c100240b07142211180c8509144038420a460326602c0c04900c40b4000d411a10210403e10780b40040e83c2042e2074041c2510307904070041c0000e84101080011070000300b160b07560003460b0103850f00349420010748800701e540d4010560540c151040e505900e580710303000c1c03150520485032503000d50b031100c0c01c212040c04402c0c070081c20400b01d588501306000c0840d141b0700b405811103c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 229011834 1250 229010584 229010597
    0x60109052103092107080102180f031c0201090b0903030105010503040f1118041a0c04060507030e06040311090108060f0a020a020a2a0501020a050a0f0510021c0c0c0b0403 75
    0x22251076034a54803520400d1500708200241501d40001071200482c0502e1100068607940d80e00d50080c5401c23805940403c0c40800503016192115060075040b140724081301500743c0d00780d0801010380418205000c014140181c2d0341c4d546038002c0c0241c0302c40040d00440d182c00078601c1e5500d13010009000d0300024101506210100003c00c040080400b03c0107030292000c1d101000319448510142c4203030100f120152440001c0103540106100d003004014880d8060701d0a003818a41008011189a0004c0608806005080c520281599104c001420041d486030440800d001807c406001e107556041c3d1120000354040c0c4148140001c120f50001e521520031000107860f5070400508030300c0c10040d001c01a01200f80011403280d042c40c0c2c441d44024540081c0704e0040701560301c00c01203a81d04000c1c0c0303028003640c101220610000360030682166895009030704580150940741035060403a400b080d20151000d101102c8008030000e00c1c0248040288603082590030803100f904d810a040c60001e1008041085 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 229013084 1250 229011834 229011889
    0xc0204272118030204050c0d05010f090e2d031b0604020102070b070c050d080405041a010e1002100207061d03190509010806090612010f05040b090f0d0806030102090d060207060506010905 82
    0x80010680d523651000c00000e11013540e4a01450301107150a000d4980702d90f0504010810340500007449c491507800368550140c07040b081c40c0c10101410080310003454140007c00041422324109450720079200d001202500060816100291522185900c02c19003607000340503c0010980d100e5001c402c0702c1066401103200300442c13030b0040c843d20031074201603405032901c0d44511041400002c2d01c044010300380ca582c3c69030080e10f810010101c8500c1c602c400141c1c03240d81c450121314100c0c0c014000b102d2003144041010f014001e50020400ca01c55201155a400410295440d1080c01c800355001d0390a81080c2e454140780400003020a20020501405541227402003110741c1c850100c610450f0031081c00030400c0071881200c042c050501603d003619a0444079001c10401507010038130200c118140360051170450407084040e85d1942d002495107505560901c0340302c6550329459503407a09a4422200140d58161900c0d01c0005c50320050701e81410002001414046038541c0d211001c07180d081030004403030030503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 229014334 1250 229013084 229013101
    0x10207080d210204150315050f0f0a0806041506060e09060d030207150513050405010806040311150a0e010f0903090b0c0102041d010608160c020427211803020405 71
    0x220200784505910005000560556002401d01c01c800c490754148102d900007c480c401600e22400f4281d4030050004034a00c4502d003024026583c1e240c050040b0300c0d2135580d0a0940d04000d0b0482d410740d04491090001002901079100f4400034042c98100b8481403518813001c00c07561040100054011003050070400f09041c000c11a82c0020302c0c0e000c81c0c800c0c010034503400c000d095810010143d1070f203c0c0159404103441c85c06025150684048000814080d615070720110b940f1480c87c0010400c074003903031f1051007003489500c4055114041c0c1160211744a4500d646139800c45e20710a249000720303490000b103e00081c0e0f0001052040300c940605007030b1242c0300121194024071940e40042d04950300300c212641c240104880450403145d440e12a00d81e25643d5048507900750b40300e41960400514020b92903001841e1503803141c104407021100311201c0c0340031403c490391400030700303401518100c5020541e41e0000d001038005400c0e1401d540f900040b524607141040949070014007000740f00e01e417180001610b45 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 229015584 1250 229014334 229014377
    0xe150d05060907050310050f04061d0f010209010f020c0906090711030301080c010809030717030403091e09060501090e0a050c0702100507060f0e0c010c060b03010e0615010207080d 79
    0x59410600780c9945050810005655811070320441e0301034081c40e80041e03001c1007144640c6105505010310103c0a0ba920741c0da140040c88241c501c03c0846011543c25200e020080184400755074225000680e50000c500c00034249200010810045500240307117803900c2e40301e45081c550004d00a440c0a5a00d490720395003507604200d80c0480c200144404000002e0b0010006030102d00c80000b0380743c5035159120080031070f40b00c2c4a44072018150150011415000000150085034000d002c0d00d00004002c0c1c0b200140c00000e100840c40c0009050aa40d00740840ba000e803003807100a00003400c01c00012440c040d18003845202c000e1490701c00c10340d5900081c0300e9a90030001c0301c4c542030380245207011aa442c1d5034083c005e0b402c6141d065440078640021100d0021040c8204071291070140700038203414502d94011505141000303401c6881c02e03150507104459846c2401401000c98078007001d0b140625003107101081340710348400c41c5811075100d1001005850401300340001113480754544844110300340e6042d003680 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 229016834 1250 229015584 229015609
    0xe07080d020709110408191104020403030c1401020a0e0d0c0302060f040905070824180a06050114070201050412081c0b040c030603120513090f05040302060a060e15 72
    0x2402040c210390051a400308440e800d40700d00200c104540c03200e00180f070318107002c0c2d4041e544059110070145070b00d001e026031383c00042600ca14000207044a024012034166001948214040355004190100b00300000003c090406040c20085041000c1c0c03040c000c0c0030b8409032001b240900040c00e07110741400b0f103040640f0003658011b421182d407020300e8003132031003181d10612544403503d20f0320011880c45807283d40c01743e020381d2040d50040078440c110a145500f0030007110310b4940c03004003001d07014051900f2a00852050401c0c40c0700140c82d80c072f007500141004a80c980007107080c4804224807001030781c0141c2030340d0aa425120188000308104c1c039140040344101c0e50203501414026100c0304902c0c00c1074111001010080d2000d1180c80b401000c00e0b410740c1c20902005100c0b2181c02080600180318002401f5159011100300f00c0d401d1b0b0b980f0342601150506140044816100e00800c824940c041028542101d160381d02080002d00d0603c03406203a00e0090401e1854110598400c1c7c09680e0f6422a40a0f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 229018084 1250 229016834 229016849
    0xf06050d080310060206011433040906050f0a09090201110a05030301060f05070b01090b010507170a020d140d0f020903030c0c1203071109040302030408030a05090a050f01050a030e07 80
    0x1152200e40c10000d11540048500030243d8404070700100d8624070128951b8101c13060b40103c5c001c03c0ca0482c0400c854400314604040c1407400302c6405071355201581d200010144011514a5541e80c10052400162005904000d000f46020800061140c60701e45c1c41c20112164410002400803052004a85100000881c4481c0740700d00c10504061007004070007541264045e855080486280c2481914035008843c000382c011030604c0b00420030301c1d01c250404200400145855842e0020075910881e440c1910041d80300182c00100340420781079010003001c0141c103020308050010040c040c0c003003101440b0300120502c00c29251000f0500d01e4106405132456608014160703519a2540151035954400703500b989441480007040040c0c2c010f5001c02222121a0042c00714241c25442c0810300103046070140c411821844100f1002680181c18070203800c0f4550103584560380c501d152010400c6907242600700740d106411075418140c0d641e0f0000215990f81c000c5080102d485403000c6209420480c03298030140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 229019334 1250 229018084 229018099
    0x1005030a120c20090a060e0402090a0e07060201020c01060504090c140102010b1509030601060e101110020703050a181d0a140106051e09010e011404030516080c10050306040f0605 78
    0x2076030600b50340f012405681c180c80d01e010030781d0f840035184280c9000d4800c42001501207004503015092080c485035001c000b5910206110591150152410707405034030000050358089a81400310f5400c0c05494000c090443d010702515042d52260a9494a0752150010450b0001c1910b46664000e40000c01e52001c000c2562201ca0505400c904a40d032003c11098407900644002054480c06a031504402260240a0f12030309600642e0698280c08803040c4403111b0701c40c0d032102c45070942560005200141c403941c0d6558a4041d1088054800da25400c04001d200c054000280320a0207541000503160b8045002441c03039845101c00e00005100e00d80d40b5032803c040c1e40c0008900250450000d048006200c2550408130503040c04519150181c281c0c1240003c00b600842c440d198814902108000d490301c041d245415941d595107440c08540103440d05400080e07001c100020351061007040071890342074030140c02945070007500a05070701c002840e01d841680d0303500000303c10100c1c907482000680b00141454 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 229020584 1250 229019334 229019363
    0x9030306101707030c030f090804120309090e0109020a08030a12020f160c14060f030115020f0d03050402010f210203180106090b090603070311150d05130204051005030a120c 76
    0xc0240240c1c120760400700b41400300b1401008003d01c00c641c02140c09c84c81a0b8103041c184a20060a064440c00c10b5080211100f03000c2011655841042068001c004c00018030b15854810307c40704840ca075201205a410038801018080c1e003100400409440840d0010794480144019900c20f0194070380001c910b11303441400303000700b06241a02900341c07440300082140441e00a010807682c3d105071272404003441010320041014243c40f003500003102c035150041e500e01a00c44541030345010b21804100c0f000a8a542c240415035030400e9401007000348500d0020141c00d02004281141210400101c000b542e00000046000c11800c401207102d41002e002400400d6990b000e900103020703025000381c4100e0460700482e06925002420304200c03580400d41c000b00c4142d04c0c00300544c00c40414138082c140203041080645c0e0104610603140700d402d42503060143d041250040c0011908000c00410010141c4c2c04d0622090383c0000301a2410340c1e0007804600403c040c04011030b4000c40c007090003081810343d035410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 229021834 1250 229020584 229020587
    0x50a03110708011116020a031505010e010b0a0e01181703030a0b100c0f02010c021807020c060c0a0f0804030b010b1908060604061128020406090509030306101707 71
    0x2030060040c80c000448410759111041142298200c103c2041e40384002c02212075440e01152407444990b00050104e01c095035130343c50314003034003601040c148882c41e550001031007402c0381400b4241c058040307080b9440c00c000071200081d0407059840d410301c1c1800601130049000400000655014103040714600180c014941003840d40c9400540b0002c0d141c2d070508038848143d0412162080144103242d81d03880c2d0f005456100c0019611004a090307040143c408050805070310f4091090382c1440c552880c144040c94071f401c000317007800d00d41d842581c8030703407800c1100380c071101000641c283c140d54000c03200030300c83c00082c6002e05c900d2085a0009150304106400044d04c0c0c44840080c01c1c8a0160351800e03035480e02039580489112004850b030380ea000809000902c00c00f80b061240003034448142e000c950244410324000c24482d10640315010115030031704407842c00c42c1004d001d44e10090185280c2403159007080c50b0255100e0100505441c094610203c00c2103005100e0b070754201c0e00029407503e190181c1000b100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 229023084 1250 229021834 229021847
    0xf04170304050a02101d030c090f0702070f0b0301060e0f0f040b042c0706030203040b0106051b060901051e090a080c0a0c14090c0a02060c0d02070512030417031e070c050a03 76
    0x342e0421401d0743d00c1406c14542000b082c5800036150041032400c0540e0b56001c0f880004c04003405403400c6102d114004110f500081c0c00c003401601300c00100701d0b125031500b44000c0281c1407480360b540c01a81140c408240c561244803080f662078004440104101c452440410010308850714000036110590185591002c00806108080c04401c2d007a00c2d2025214502501684800c0c0c40041c01034056500422206102d1006042e410803010780d800b56005602c0c8005e4a003440548240c42c0b036954601c18081111001d80300180c8070026622081c96a00e81f400940ba240c410b103407805400d4a074001850415040706010904005501a62559030181c60301c0c0240200400d42240e40e010b030b40080c000c10b044640b14010f449020400341d00800003540d03441c41100321908403107464000c268090060400040c014410754088620480c40d07140c591402d410656000e080c00c803610400e280c02001800926101d00e800014000c0d51205002410b80340c500b42115072110210340a002401290100410540e0158 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 229024334 1250 229023084 229023107
    0x818060313030318150507090306091203050603070b0904020304020f030a0506090114010e16050f04060e0a051005030f060616060207060501060f0906030504050c10170f04170304050a0210 82
    0xc0c1c013040300c440c80c50480e044620a40d0805080c0321189104021040202e070400c5074811080d140000071180c0d0f1303581d000140c2d034143c94119642003201d000460031a52511416034800c60440003452074034604008883c842c490001001d000ba41c0000026040d500c8568281c50811005801c64610700c400d41031490f200c8005584404d115401c1a1891140011010055041e501c0d1344c03d40389002e890349000c1c0000c5022000c1c28005000090140103038051515000d0b00041500c1c0d19010380c440826010020380c02090b0300680d10030a1aa5240c0c9011584107054a90110f4001241002c0b500d8600c0022884c1c024002c0303109403650362000407400c1103100e40141080300e12495051244d41d8079440151381200400801e40c00044050104124103403080d04220380050084040e83c10103c04034004c41c502000a840da240896100b01990401c08142640c6951200500780301d4000d07410070ba5148081d220040c144001c407079902102107024000144518540c803640103110301c056141280000e44250b443c2c0d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 229025584 1250 229024334 229024337
    0x110c0c0f090105181b0a1206061d010c1406090a0b0c0a08063d080603010501080c010c0c0306050c070c1d0103032a060b18040f0201030207031103030103031227081806031303 76
    0x1000027610900940c008a185000080c0082101c1c41d0f0000441d409043c4400555a50051043d081031044041c03040c41c3c041d00c0d01c000509480c04660800030003140e00070b04820080c00d020808407602d00d130f02c00b05c00c03600204111071000700565441c041a06041c1e050401d07420035500e00d00804401080000e1511190b41e85480c0d640c2207070380e644101400c9a009200f00401600440003941c9a03600c00c0f40e502d841d0364840d8495003802c540b01d0b2109000c8890440d00d0024110300001d270b00c1e040c0060344071110014441e50034050300d00105107103529040390f8107200040c10f10802e03207000c06ea10310000c0c00c05c0344203452100303e25091503d18140003000d485d01c1411240546000300e040302c080c02002158a2049802c40c01d442103049896004400943c00b060702903041296100034180030340030500095000b075010760303611004846030f10314010448000380d10a1a469004001d0130607100c015046804445170092201c0741c85101d89004046002c09d42c07030b034256005400004102108c1c010b5400090b001d40039 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 229026834 1250 229025584 229025591
    0x4080c1506101b06150f0905060f10170709090c030914010e03070212030f0d051509090606100504090e073015110c0c0f090105181b0a12 60
    0xd110640c2c501e070140072141c194580300402c00d00070600a800c03a10300680303003150700e42c2e90039030b200388246c03081e0003a4200c064000e07200c00c1402560f107059642e80c200c1600845542d4210701c050000074000c407100d00448055006200001001580a15000d00003001000414403019a040c0c10050050100c800101c4018203145019055404148074503181207050200031450036607290200b0251100e581000c035110700c001c10241d8403801c084406065143c0c046840401c0505214216908618001e61102c3c020806402001000d540020380d00741c2225059483c0079904084980c221070300c1c8140d8000c860440d08001e0f105000706e500041c9402180c81d5500c005860070303c1199080f00e00c1101d0588084e10540d00d0a084e8085010350b03560580f00d54840400007003031061740d42500c40300d80141e0007015054100207118829401c000300004540d000807034403648d0642c14038002030006e01940703044010101b003102c00100c02102d02c10704582052440400192590492080185000720031110307855503504 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 229028084 1250 229026834 229026859
    0x91407050a02100203040c030507180b04050f040b1e0114130c020703170c060a0e1c020d030b1c05070314070f171608070602071a070b04080c1506 64
    0x420380075a11420107a5001d03210302c01c0805141070203900081c000307032a03041904030000300107041000b40900500da101c00030100f011615444000300c1c3d0017900c0a5010b0340c1480b0402140010180d4a190300641c083c800c203031540c407401c0d42450340e12a010184001e440c8444004606400c0220400b101c1070805c89141c8020b00c8880794003000e64111030003d4006d613000002c14400610305403c00ca44441d80c0c502c01905003007103294014900542501c01d2150f41e80d0381c240c2d001c1011340c00e0250402d509210340d41803042c03040b420802550b8410b11404d0b00d0405545034480314031742c0e840c41c0c00c0741b1782c408400040c07805c1669103040180d1210400d00c81180c1c480240044903541c908003180d000c088403841015081d1031468080c0c01c40c001c07411030a00c8886c034002c00b0101000101e4042c881000b9140c030000800080b401e100000e440c1101d580c10260807200600350300010800014121607115902454550680c3c6603850014501e0250100c130500038000c0301c41c03111301c0800301c00d03015100b1103085441248509 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 229029334 1250 229028084 229028087
    0x32a03081609030b0c0901121a0f12070603020d150e0f090d05030703020f0c190b0615040b07020109081c0207060503191a040c030b030d08060306071407060501091407 73
    0x8010f11009000b4401c2c00c000862808220001d000000c0060409035101880302d4502030031100a862084041c1c1440b0509205604000300c11100350301c01a01c0c162039060030a056165644001e1041008258002400002d415003e8010503680303c800340f6200e00180d02c868554030400004c0b1004842100002c000074040003000404940e5074800345c8900c0d1035a1a800d40c224041c2d40070300003000301c1031400c03c2801c820603070030414007070030000002810210682900c1c00c4802c40e0406803446125455403128584811009422075045540c410341b00c40d91010302c2d20040c0c80c0c04049030721240460003603070740c0300c0000210b4260600c83c0207219401d5a281548412040e02c10740806d5a0f01c5410680800e1b480c1300d02c003083e510139805070035190301040c000c0d641303900000c050f203c00000c843c1c0040d440b1030403070045041c1000310304800c101032300780407030545010741c0440d0342c0d41c500400310170411100c02841c140410042c0e0845d0b00068216909110941e116001c02c40501404490283c20624200000f165075 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 229030584 1250 229029334 229029347
    0x90a020f0f03071709030d050f060109050111011407080901200702040f110409020a0206011403031c0b15030415050c09040b01090e04140d0302070c03032a030816 71
    0x103a444202281c10200010050a1960001031200040c000d6081141d104a084402c1c02c5104504480c0203580e0380c05100c3d040d000341c50028103003000741c0f07034540c052001503030304030400300281c40d42881d0000c00c8161000c2c0d079901401c5801090a0f4044e20001480f02c0c86500a02e141c0c4920075220003484080b020780040822840d0502c0b02420b111000d01800b001442d05410040541e01d41d42c0011480d8030030040c59031070503441603010180d015800650000295010f010703650040c021250b00b006007030000d10100fa102e01c5448040540628010800001d041c019805400451005409480d040c1501080d1850541c4151010f0b1003410381040c440750417205500405108600340826a42409410300610000e41100c65819041c42424071001c14091240c151281c1700764000c061100001400006460a14485010250805004220b080d0100d0880100d50341200d82c9443c2207119070840501404004c000c0113120515a24090244030034964852010b0780070b040321031103050008075403910640d40e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 229031834 1250 229030584 229030597
    0x9050c0a0f0806060a030209030f060916050301050115080c0c0a0c05010e0603070905040b041e1401050102070b04230d050d021e0a080a0c0804080a0b010e0106120b1507030806090a02 80
    0x120101700130300015244240c0103030010000203000c482e44011904034941c18840102c1d0358040580c0a01c12040c40702685100500041400303034020001d55041c9800d0040b85082183c002c4107001081c0041100041070800702ca60b40110182600c0116040d072500d11802c10092041c5400103071036401c031006074900070301168002d407060785905800313600e002e050102400002050a510598031119218840e402d00750440140b5021000011514400088450000300c1a0841411075110a0060088012881c22a0280d80c0f89003061514140c8429900294100960701c194000d10048801d000304900003400c01031030182c031b030207880c252400c0c0008800360708070f034010104080e8012072420011405a100800c2c14508920741001e10101c143c448141aa005900502d8142d010040308818400c0040f101400b4201c00c219142c09540350040c01010094498060031f8030382e0b603c00080c001c0d95114041221845804600c00c1d8603180c450801824001080b00c03450b005078080720019032004198421910b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 229033084 1250 229031834 229031839
    0x30706030204050f0d1110030b09130201020a110a034404060c1e080a090b0a0c120903020a180608010b03061314010216061a0307060c0c09050c0a0f0806 67
    0x261a60713a5042011200741040145c5400d10031510031929525100340046101c0021b44001c2000c141c1001404400740000f0210a5141c031811003120060f82e02042402c102c540008078810400c1708400050f030038034556840106084030b400d42107101d900341c036004030b0142c0e60a00307419880c07114002c0c900a000003110400c00b8484004100600132140118a0702007824040e0041c2440d08040f41003203100d116842030151028240803a070b4880480d07010450001401c4014000e60900617941e2020f4444d0205850042c610403034100c50b402c00e10320a402d500011030b001000440e6203a5603100d0004011303664034032030007102e04109012038007550501941501401c050020081a51762503100526500100c604840d40d0031001380032005201d0034005070504031031104401c40c02d0480c518003142144c1509600580c6004051440c40c6035550200b2040d045038940c0c14640c41c03251451401c010501400d0b000380000700d00d001d040c8048030412601500c0080110b454600800031401d9040c0d0799282c00b25503441d03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 229034334 1250 229033084 229033099
    0x212032a1c050a1808160503060c070804030609030c0215030a0b0904080f031b0a050301050f0418030302091c060e0d08010b0301090209180f2a040b0a021e060603070603020405 77
    0x1003124450303904c81c8070340c8001d0b510142d034031130319004503d00b00b25001c0c2c0f408010300380071070040c00f035483e062003010303000681d800d500d03460704486a4503c2418095444060a0340c3e949019400615000d8001170345407a03801803250018400c048804c030f00680017520b030540004c3c60f009168803107041440304280100d8004810038180389c6940e0043c00240e000401c008400c03086400200d29000f65000507014403111900c4891702c03981810240300700c2401505030284070301d09040d00c40c0b05115030307001c1c4040740f6600342c500542d8030326014001c180c11410324494008078055035102d46052207215444140e400f0f104a09440c0d500e005614110b034420028025000b410504000400103030000e0350040c11041405082c10403901200c030280000007100300d44079070b1522a61020840d800c0031a103a40702030322454a402c0c8000c080361800c40801e9015500032061a5131000403906c0340b02c0d000300b14010201d40f17003102040803542c504c1415500c405058030814042d22858001040d654000d0017500c1c1510009030812 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 229035584 1250 229034334 229034347
    0x3080402130617010606030f111209031b010b041a01053712110f07080310080d0504030605160e01050a1206060c02031c0207030212032a1c05 62
    0x700003106003901080100755034280000e564070b074030084500c81e241c90400015005107002c4000c0d0030b94031200a0298130500d420700c0da00502421009807100328500074000810380e07131051021303403940c8614118008100c141c0103051b00241c80540110780c1256003034400384515020022101e20408554400340d011410a1100d400016280c1440c81011018a04040745d51030309a0251440c00d0058480240090a06504e01030101028001d428039500c108405619280300092480042d005080d401818004000b0111741445c2d0004240c03c050800e000c107035180300303000c0d4070301500c540e016200480f485030403c400140c1518240303801408000b101e17224100c01c0703110180112141d5024410007001c0c8804a01c9510b400d0040d0322504018040e2a1100c840c07a07070450040501e07000b425100200815150400c0302c00550307012407582c04495050741d080c000030103803400302420350003080c4d0051090061048074112850650034680d41805100b401e80302030070131408035034101d43c0001e245100481c0040102 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 229036834 1250 229035584 229035589
    0x14100b03130206070b071d0303180f03070806090615030615041503050d121e0207030c0818010801080a020f0f01021e06160f080a0b060904150f0b0703080402 69
    0x30350307014400c0c840100c1249416400500d580e04900802c3da5040b103040204007605400008080c60414482c800c8182c10040d840000e82d688545a0700320764140c58032202400b5611014404869054000c060b104016110710b03146642e000d0032134540d80c441c4140008078402951501600b010ba14010b000b400090761044401d05441524030320f2150440e40e29400b144202c40700c84034440103144600c0c0034203080c1524490040c810b05000d00d0680b00d040c40c04009404a6140302d60360000ea50101501689421803400c050f5030507904050040c0c2074040000c0d940300c1c4015481003205440e442602e480c41d10b0390329515000ea442d040326a00039000000c0002c08200c900d06011019100307281441183d0100b0203840e200303a80b10303070005125400e681c010018000d1903120142e603c541d5203050300d8002c0ca0144459001044094040c00c28501d290307032507100701041d4407440c003100c0c442000940140300c0391034070005200c0d02d6065803055002e03040451001061404c1e81c0d0089452203074040e40c0b64042d680301e5408 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 229038084 1250 229036834 229036837
    0x90c09040201050706050f180c0609040b1c05030c100c020c010c21020c100c02030d080405070b03010803090a0503010605011d130617060106020d08010b0703120614030114100b 77
    0x1a8180202440000d0005c0d40038014148160a214400005400c00e060186071440c403010043d40b0641010b0140c4010340c864009650030030200b01e80105140720351380c01050b040300c0030000c4a451900c0041000042c010000014134126000800b201c3e540e1905201800c101c400c02e105903801a00040c0c2c0d040320b69071054141404045c02449007070070300312002c0c40d000c80c010501034280700541c10040049205280506d840c940208080c2040301d00368049a0000e80c40301c1514001d40207020441d80420180101002030001400b007400f0482e41e6540c4800a00b680c0e0340042d0040d922070a40c84c900071030b40d41010b001d442d003107803010307110f003503100403001042c15102c3c0703050105942061800000002c44102c0703000780ea008008070700e2a218a092481e80450a00c00143c029800b59800411405505030340002c0d110f045580d02d014203030704c500080c9002c03174604402c0e00e40070301201d04228010505207400800d5400c0c200007100200410640380701203800d00341c800c8032100c4a076150084100040740f5a0070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 229039334 1250 229038084 229038091
    0x180606070204090f120e091816080709050a020906160503091306030b07090305030a0c06020705060106050a09081c0509012c03010f0e0a0807020111060c0d0c03020702280b0409090515090c09 83
    0x405a681d20441d003270701407030480410b40c4a5680780d80300050800c50441107104168020820074403e5140041a902043c0e423803091004a42c40d09440c0c6904500340801801a503005110081007103010707685114a20000d007000d40010358442c0d91450105050b64000c040c0c072400c0b00d6000010b9810000c10610a03641c1e112902c8059410a03000c001083c0010030a001090192070300c1d8549c0c0744c0303030008200010031495040e042005e1540c000f90001201c4504030301c0d01e1042c20841e00d442ca55400500740102c0300345205000d0b4100f1010345c2040041e440721052030b80010316000360000c106c40300c9030011003030603a000c1249504481d006110144041003038100100100c2e80181070100c1e40c9610b501c036144c5400300842d101c084120000c2080c061101d591301407c10104100c0c034043d82000b080390000707801820480640100c00b054503210f5000703295040924002402d1210341551640c1d03441c0d20381006484680001c484500440721490306c042c5443c10018003512034000148041103144050005041029 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 229040584 1250 229039334 229039381
    0x2060a0b0303090402031014060f04090b0f040c0807031a090103020f0a2102011202070206032806030302240c04270903020f0705030309180606070204090f120e09 71
    0xc11040301113403604e000070b50051b01c2e00010041c480d458090000c0010b101681454450390003000400400800141514199000c401001809505c60000070b540f41b901444020f8204c2c0c10016104074054210040c980700d900c4585061010100403515505660801440300ba440920080144090704001c1d180d0400c072a0060300c20340c050741d00e0310001c4040e8111042030308441e01d1240450700855a00c40031208807990a40c0055041000c070390f00141443c040144505040d049a02d54410762003403441000e032624945450130002c0769124140292075a000000c1e4101010086a003504524000326406104640840074130341030900b00700100d2000707190703480c4440740000d0350400100c0d101028800d48000c54442d40091030300c201402c07c01414403140d03a00c4240f0a80041c400019241c6800c40c02c1e0403c4490b9030700d0900e07180e42d1100010340314042c00d034001c0d4019241c203000804005114040380307120f46c0240210b4909500d803150480f0100d882566042c0c124400c01c01060380805000101100300540 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 229041834 1250 229040584 229040587
    0x1006080a0b1c0c0f06080105060c1005090d140304030e0112090501110c061806010902091309082203020d021c17031f0f0303080601050403060e0a200102060a0b0303 72
    0x541c000034000304408101c07280200e40c03080d08031080101443e0450010440c15400410312484c1c0800640b00001c14400c0900800002a00002500041c014400c44a050501c10019801c003c6c401c266290034680011010802400381105a8a40c07801520b21407541603883c03107140c0400c2d1004640c0303110a882c000901d1307070300c0e078044a00141083c000ca03040d07a000400c06981f101140b0201901c0d08101920155080718500115000300c034000c201c0c2030541c0e0a121015985401200200f680840c0c284480702d22685403418070340c2001400c1000304900c018060050364074110841c0c038140d01e00071504c0001d6221b66001640317401402d051901500082d00c42582000c444103d80380e4000c410b03050f64044490a50000030085000e91001c80e1003510645241d194500310305084451000701010b00015062042403000100300303a125800321303406150710400903c14140b041d04403039901d00c0020f508076180c0f400003401c0f50103800d041c00c81c64054101640141216160781210000a00058a50a805020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 229043084 1250 229041834 229041851
    0x105070804081902100806030c060a140c031315020606300d080a1a061b0d0507110402161502040503150108010c020303070801090e01020412080705060705031006080a 73
    0x2c0600c0814100a000b12255900d005248108070045400c0c0d281c80050110791070034030140b61030020b04036003d480c0590b421035550390311501c1510540c0442d40303641850100003504043c10000440a007101c0030007420000311080c0c40d0600c002d8410b2000d05040c0050b07010b030000600c1b514190071458000c0244c0000c02034015034585004206002d503c0c8000300300d50083e42c07540609684010051707402003181030100301c10a10b4104102c5400820410a8800d0101150741d141c01d024443c0500c00202d00c05045400440c400701c00a0500c1c1c0210100f81c0701c840400b414604181880c2c001c50b02c60310340088102c4941d40b0581d0320300c010603800e01c81c0d06001d50703030a001c085040e072001c0042411000b108071400391103624001105003500c94142d400380840d0000d0062040064100820341d042d166281c601140c4000300c0511240240150307404203074507203050030302c4006003c8007400504240d0f00603c252042da548151050351984401e4403002c01c000c0151804008281c4199008d030340001a180010a0322103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 229044334 1250 229043084 229043099
    0x1b1a0f211e010f081b04060504050f09010c091503090303060305100222051809010b030a08071103011e020f0d0905030a12090201050306040504050c0a0b091003020f03060105070804 79
    0x10126007546501007004a41c181151803003410a0062040d01d09041c0300c0c0c0d00707004400b070316281705518000020000e00c810961a070f41d640c1102c1c000e0030015104000c180f60800402d1040c0c0b0701613031041869481c000d50303111410311601c0c00500f5520003030070f069149003840000b10004d000500c400d80c01c0507902e80700400000d42c14401d0101c080b81e81c0707501607250308034034031414150038a00b00c00c140da0064911040210b6100c11403140000d2030b03100260034140e07071155040c5001d0010703449460b90501802c218401000440c01c060701c40e00d40580c01c01061030401c081454222503030044115152003401213080705100e280c1c1c00a14100c042e403c0c40c503050098215041e0143c0304070010841e050f400c0270030364000480e84081075000440702030000340620181a00007901a02c009040203001d0741e01c4900041c00d1100c104540c024895001d4007286900303540d48151040d5801c5481500c2c81460b0000444071503a21174001e0360f8070300d028003400030728580341c0c4c00065504d40d1101d03070202d6240740281300000d88003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 229045584 1250 229044334 229044397
    0x190512030c1e240603010c05131208040b03010815090c0306190b0406080c091e060d0c1503090c08030a050f03060f0a030605010914370204031b1a0f 65
    0x20740d00d0907803d49480c20203500301801d40c2d80c02142c90702040b0051250b0902c030b0b84516180c1044a01000c2c0c452000030082c100001144201d800c24041c6d01d4001000007111a00080e551212404006440c4155107403410390603211343e40401181d9159015401040c040c46c0080000d8440842103d000610710b4800d102180c169842036222208a420540003400581480d01807545c2c8815049512003010820200b207440f500e03030141030303203000e07451518080c400c000700300c956400500044e150056030048109802005000c0415046854502c5e403580011203100001c15038500120300d0301c520342003501c6040b484d41160002466164441d2181c542008962158038510018602400c5d01003111342c1030481d0310082d64103150f008288003490000b080080a2031100721000202249a0031002e180c40c1d9241c40c84240c0324009508400b88002000020450b600c0500c100b41c1c061421551101a03492481d4489034180320343d001c1d103807a400c1045000c0b0031030400007810403850540200326111921440060781 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 229046834 1250 229045584 229045633
    0xf01060e06190503030d11070f060207020a1505070f05010b1507060c0503060f1924030b03030705030313080c03040906090b120d030209060702190512030c1e 69
    0x40803180c014800300703042c6010035070701142c00d00100b00019850800400d44d00e1280c10a1104e1190b6200da90000c4584100c04a0b106070b6084114030360f0142407420480005e5100040484c0b050f124017000080500c0204030081c40e4000355190309081091a03101d400c502d41c8864030031680b9540c1d4540f40340782c50b034400341d03440059021005600e446001524248084038582240c05007804402d0013044140c0e0385110314200c8050040d07901400c07003589904000001085500450585048d10305510700403980d45101540710080b940d07050110000300f40505869104040f006071058004200040e41d4082040503440307000d10500c0c40300d1800100704181402c0d41c12503046900001c1d19201e0802000250340101702d000002100c191502d100c0c9480c3c2140e4030425040f04c2001d0580100740555682c1c0d071681a5008590081e020001301200861180c8003141c030390041a105401c09110044d00c0b000010a036018081e000004042030307124425055000482a10088624410290202c2e490303424214503619 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 229048084 1250 229046834 229046849
    0x11030109090308070c120f121a010f0c080f070804080a0605010e1608010311030f16151103040e06150a0804020906030307051906020705030a0203090a0504020f0a0305090f0106 77
    0x1c20800c2840e0080100c2c0018040f502000200c202e50004540e8140168542e45c0c141e007091440007000f62010748510f41c8000304080038901e8026401d0300e0540161036001090741c02d994000c56403c090405075080c1890380e0002d0000642030000410201044d0020441d040c007550415050a0b5203078400341c50304500341012036034191141c00400c8245c6c2403840507500300f841c4040010a4a4400c2002045040148005004070040b9000746102d89c60510803c549000c000044d20310461113803a10700312040580c8a280704281c900c0c4030405400e0700c07482d80341c5040c983e4403002d18501460032114144048029010703540c02880003201c0300421500700010405050642c42c1d041c91072034280100311103070b01e00610040c083e4108128013400030f41c0100c0c003644407000000c0c00f469208120b084c43c2009000740c043c000c15600c80040d40c9001c5503000000340003d0304c000c40709a40c3c0d0686440910003039004441500000804c14450b60034050301942146900c1a079a0040b1002d6101b406c0295095601c50b901c00754 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 229049334 1250 229048084 229048091
    0xa02070317011d01050904050303060d02040b060403030302030f010608010303090e0a060f03150501050603060102070306200c0609060903040311100e0a0f030209061f081e0f090d0f09050d050111030109 88
    0xd91120003d025503004043c1180c41192034034007910340f251640720082c1850702c0340d11070904207411581c17283c1c000c4c0807180c00600007030f80701d640303900d40500294000d40705001406c881d00000200244100082030580ba030640d02c17010310a103424140c150020780a404050300e20784983e00400e101469001c102c004502405050440010341da5010301243c00680145001d8076080007004a142d800041050840794496000103082c0a1840e244420741c0b6004081c500e0b400d000502401318980024981b80681584010340d01242c461000d056541d105a100040034110a1002010f580c0342c420811031001c182414078603403001e0030200080c034294607604150250380b202d90707007841507041070555180d0004046d1015181c0e000c2140e8811a012402d4007800100a05000005c00018100f201c50011121400b040501c82c10459028111400c003121030400d00d1240c080384040852141c10a40c400d40019141c80010a00381410720525030402001a21250340355a4903d03100000400194002c205501001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 229050584 1250 229049334 229049369
    0x10e1e090403030b19030809150d0e030c0706020705130e100e0d0e01030b0a05240a1d030d090603050a02210105270a05040c0915030b0a020a02060a0207031701 70
    0xb40c042020b14044039120101d0170240000303138840044540c01401100c50140081000c40546064402d107020410410b08007110f4108460000024100102055054840d420b48518089a450219206080d400018102c684000700d00c1d0750700091000d00303c08140c896101c11031400074140d41c0e100c10041240c1d404080101c00e42e03940200000300080d400d20302841f503c2c244600003401040d40e40900d51041c10a8003265040d0411580307000c50240d581140326032a1004001c000c0c02905880b11083e0100c0150503104103039190214800c40c1030900e54441201241c01c10808400070200140441c41d4680c0c00c0103909014084090220307120212161001800d605240070701500002003c030041d000c250841d0b069401030350b14031402d540314032010b0000030190344906040c2d401c2c00160740500325040c60800010040611402030740700352401440300408945903181010128816550040300681294011915841c0d1940051031118001d19141051507051a000002c4071002ea119241384104000b20 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 229051834 1250 229050584 229050589
    0xa030203150d050f0d02070f03020f0315010f030b1e1f0b04090b0a06030905031207030906111909050a12050a051e07080a020a030206070f120f02070503060402010e1e090403030b 78
    0x5d20b1034800440c030280004034540300d043d482c10662800028400e10130b110f060449a107013000710b0881400d842d20040ca40796540e0b11504030f40241c2c1c0c0001c2d143c24020200007040880655800d2a80c0070b401400e220131940d070030781080903d80c41030110001400d0311500001e0140107070409003020705070349980046c2c40000b01c420004600a203034400c0041c03504140f004004a9000310035071f4003410001161208030742c0e81c502c0490003000c4d4402c0c010441e61800141e081346c003001002400c0031394101e001ca0030351030042c118151005c0c1c00612a030f40c0d000400b500d082c012100c252902e40a00e40c4240b045410390402c1c0d54825040044036054222805101c9485140c2d005040001ca00200004c030050002445c0c0c0d078000c11701030301e518000680501d030000b0b01f400070040091080b0002c560025507820f42c410010000034087e1010207039060051041017400b1881d4607000c1019406158161a2403145000c20010711070200452100d4059001049100170000e407590846144954403e0341c00180d08080c1750304 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 229053084 1250 229051834 229051843
    0xc02040e1e060708180a08041503180b0703020901140307030c090b0301080319021c091406090a090527030409050109021303170c010207080408061b0a030203150d050f 73
    0x2061482644460b081c400c8080d00b00c403501d03400242030550f040c84000d500704942c0c58102241402005040e00040000350001070110410500307207169018884810000340c04210040384a4000d44885c400c4004104018001d0340101284407040c1480001a1a0381d40c14655a800c2101d000d40801d0311400509039295000e4940406844c14804040c255410440b0f09580c1e40960590030310b9100c00c00081102d594002c104a1840e0900d840c6041c1c0040c02021004006440a2080d801901c00e5220ba0001e6480c0800555003035000250a06008520345506032018100103080c03655402010480303080c10000e5a440c290104010000661741c1e1031a01e20408201c9405a0000103003a105200c8032041c41490354044084a400848040000c4c80c8141071421512624040c00c50540c40059a4004c000b4110043d0048400c4a401d50314075640d45035004a034503a07001d00c107000c000c1040101c4440b141c0a5030141d6000403600100c2c034410a0710101086000480c440d050300c00b603201054140c11080f0420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 229054334 1250 229053084 229053133
    0xa030f060b0907020f0319090302040509070501020d050703080a090303060b0c03120709060e0f0a0b131a120414011d01050a0b040612060e25030309060203040b030a0c0c02040e 77
    0x40242503009a2900246c1c890007616020301d880715403c2240c000e0035118128010180d50020800c010303c2c2403401025998005c3d038482d4034098000c0707d00c5802002e0190050300c0301150540c40d941003642c0c400c0c44020061811031811805c0c1640e40101083d5209548090822505000001c0d95129804c5043c2d01240800902860400c2440311007030201a50017030310550b0090b420703603845040251420001d410740205400c2143d0700c0340003090702c540c000032003c50881154081c0c814812650a810310416141c403a030801c0d16076100d42100400c0024480c1418907541519000000034680001c10300d442801c8680c124066240e9122410310125200b107201c2e08210150843d82082114600034502d1040122800051f000b02d0351810096070850b410701c180b20480304c031022900001125200ca1000c000f581c0c0c08150002498400b020410741d00001c1110180da00c2d5240142c110368420f1100b0000d07154083d089010080d420ae20100162600d0040e0208405400083e00f0b03c00154141512021402d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 229055584 1250 229054334 229054337
    0x703080621300f032503091718120c06030406060302040b04090308011502010e0a0b01030308070305010f030f05100f0e010b0103060b09090601020a1202070f09020c0c010e0a030f060b0907 82
    0x34011250a848000100d07010000c821240c3d42d12941d803000d5420684000f4500c1110341030303841080d5460680e056105c04045441680e42d400005800080b91003140980342c00c42e007130505201d046038420324100c2c200c20841841002125200e41078030020409582060340d0440340d0329104c6805108500d040d0080c00e07204034054604006070401a03c001780390a10600c140b0f83d0a421003451418540d100390421207c1e01001030454600c001c840c070f030081c1130700000d1000ba000a88054041982d15101e401032904990052401d80c2d01c041c2991501c1420703100126040380c40f8810b00201407245a220301404c000004013040c0000c5a040b544200e509540e1903841c050304140c5080c0f010304c00903480c882559401034056661050640e2000d00503498448112000340910030106098034120380d0004103213040d20a04040301100c9950341201d00305078042e0162550391170b0001843c40c0101d51180f11a0508686d0040460721910ba8a4562580d00501004169891516415280343c2428045a103e8001145 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 229056834 1250 229055584 229055653
    0x16060c021f030c1b05071a0c1218061303120504080d030504060605150304060203040602091503040201021504020d0303050408090409051b0a1a0724020703080115050703080621 77
    0x1390b9a180c1c0c0321781ca2801140e4184070303003040c02c100544026003902c06640e000400c5070b800c50130703840b02078410350819420161003028464041c64241002016034a81040f161100409681141d54003202554201b010700304002c82031100240d1600c042107829030048441c0c50024150405090210a948580d041540201c40503410511004d901c0022203900c0740d0041c900580f262a5032411101900c5080004c0b5400583d1005c0c03910404910001940078501c00d0302195204940905422205001241c001c1e40c0f01821088401c0801d000340c010a500600c10700c0007929110100c00010200e0b08840380549681d8001425107500c030480b901031030b4401c001142d1076400c1d14645040c5010481c1e0100000b015544085155000c101340d0000c094080341c0c5501d0f1118074845039803900b00c025000048241d00084180300000355030101c00903603100f040e965941d140d103060f90380d46040e14140009800160081101e884902807104594403a0707240e82001409442e400080080c2034141d9000da10b01000e03000b4030b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 229058084 1250 229056834 229056887
    0x100203040b040b031902070803180c01210e0607020a170306101d040c050d0b0906030d030c020a0b160f050f0403060b03010213080d020d0216060c021f030c 68
    0x20210559044071043c1d950070380d9980d11044903018078486141c3e4010602e00203c0d418080002d90b101451160520b03428074104040c4e848030300ea96a80c2c00c1001740d408142d50702c00c00b40b05880d4418508000c1030b40308a01103206d0804000c13880c070b000070449620005801c080d0340501005205020f03800650004e07204903040d800c2110010300320309a41c14801d0b040c07045160700400c03035000c0e98009081000c001030003000341c46a0603e002d0099488094014880c914110040c3c0c041c0c81c040c07802c0c0e405600040c0040015452242007a001403040c008844190701c03900c1050340014088c00c80e00da204071000c80c0245218407554101900594010b007581040c400e040c0081400501700c0f134251812a5044900406c400b212a804a80244561050050b54400b000408541d6400014800c0c0086074207038200d5914500c2004101d07144c508032140c6d044442801c103c00c000782e40c0700c0d580c800304007070004020342d0f101c429003000840d4040701c0c82c444001007034803042c5000e800c9401c000b65003410950030300040820301 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 229059334 1250 229058084 229058099
    0x60304020a060c02030a1e021c0f061107020a0b0a030b010206190515040e011e0b06030f270705090709270e0d030f05060d050a06110d02031510020304 66
    0x426010302c404100310561190b081d5601041501803c0d134200c03075a1104043c450441c03400e24405001c0983c080c12151003107823602e40342d014007003a00d25000300400c1305202060340c901000e442c002c01030159042050000701c0140e6681c0c40c2c098024134646d04000ea88010340070003d8140c03414086400d066401880c1048030f03040c0811103501c0d61100321a00010380ba0340c2d0b00d21100305001c60250154100380f03800b85220003840c055110308281c140d020603940c400440001c01c0e00030745811241554001d8000e1000c0794580b0780b074101454000d481d40c06030b2001140d0b030201003079800d00300d9200310200d5486090208103a0801904498000c18145006070103603091182d50f601000c152640000744a00e004403104401d04103910501c0c51f203541900342c4450074051140100a40104140004081d2402011403070350320f40004460503050b4448050f02c041c80080c0c43e144001c102c11100220890400c000031048028140b000f94800c2d28103a0790040010206400d2001e000c0d103c40244041d540104428011032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 229060584 1250 229059334 229059349
    0x40f1508041205190e0a0b0315011419051c02030105090708150616030207080a330f05180a08041e0f062c0109090504060b0a0303030c030b06030402 65
    0x35410000201e004040458101c0b03c0b8840d901c3c0444400242c3d030403080205038408206140e0b05003c44070f41c0c500c10b8441030300f42124170003a19000c0b20103807641c602120650061018441c0b0040e40308400e4146681c0c070030404c4211080002c102d00185c000210494080850304d9002003481207000d04506543c1401c0115411105c050030800c03c0c005000c000414505a5080c202d151038009069070b92139410040740811040d0b100d40003200540160701c4003059084000541c614059084078190152a9040324001201e80400d0200d181c0c1d00c00d051090403100b0b415006140c00b507002c09600003280e1400100c0d4045440c03005001c1c3e0059002040f41102103220074058030203545551841d242c1220190001100c445029404088020124070001801d00e400c69039080b040c1c00e003020a4a174107802d462018844410000c0c0d05030214444160074401c90405d540b05aa02501c00c650019680c90300d200001c801c189181c2c000c400298032400c900200c1ea81c18010b02582140503900c80c0d08504081c2d000440c503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 229061834 1250 229060584 229060591
    0x115140a06121d0102091018060818030c0a0c0501080411040f020d05040503030114010903170f09190602012304150908070c060807050f0d0c0e04020c03040f1508 71
    0x42003a159400c800c110b41c2584505590900c869403040d080c10742c41c41d114086d4000442c080e100d2441c5610300b1005c140140000301020004824100000381813100541d0300900c050440c40083c09904038400c4044400c00081c40039448190007031461002a14002007056050b400c25030402000328203000000d0854280081d121000702c4020030100d0b020b005d104001d00414103441c881c2d41c101401c0c00b060010100013141070700d104005081c0d001d03c80e0310056450740d1442c44010903c0e00000420104492148017400400e00e81d41c136060314002d1240c00003403a03c1e85443c45c41052099104041000d10f070240f05428a942c03c08816011b00c010b00a401c42030000014030140039043c0f205450000745910798005100c4590020745c5544070480341c00c0461046070640259400300e4081c10102d1000c13400b07034064480b520312020405140240550040c070141c209004144e00b48100c174040d80c0b0b5507a4990010b0841240c1c0d04c0b00651305c6500c0e15289001d80700c1980d00c28a0309a01c00c08000920680c0301d00700f41c4d807 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 229063084 1250 229061834 229061837
    0x130b361513030804080601080705060a08071404230a0602210d0e0303010303030f05241801290703090e1f030b010302031c0e010e0406080304080115140a06 68
    0x1140104003526480780715008184200c03107071000001c030802c00c501010308240d40000045864036a287c00c00c2d1030b0b840c8014011203500c4041404400c41480c403e0314525806466031410003101c032409610080305801c02d4000c6030320070140d0400c164160b510302610602045080325103101030b03441c0690107502c5142c40242022054000111814152400d40441d6007100310f040003045440e0400c041039840307030000e002c101c0002c1c2c10312200c0d503036551403409028054854500c00405822400148200a05504482c26000050b450a203015044c40c103003000c0c000c20f07c003000c0704050006020024207a0040071b660350052002489a0000700b50300c480700100796100242c42c80c01507110792002c5803a0950102c04103007605010326020003000003406006040385c1c0700360100d941441d0011203081c1714000e041245400200c002180500a6105c9c581d041100c0c10080d1002030469220b81480d41594000d4000c2d1800d69180c200074000800c03040081d100070b003c205881018200e080d400103000c00094490b440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 229064334 1250 229063084 229063099
    0x60906091b0a09080304170d080402060301090b01020f010f20040b180307080d03090204050c032503090b040b07020c010215060d0c150905010e0d051c05130b36 70
    0x142c90314080c68500d0041d003c10300803262a00c0d03444680e582150080c40761603c0c0c5008100b007a4507180d00420b419030141d94004c12803811a802d0034032207801000001d4180341148210000f01450b500d0070700c40d8a081492002011594407040c5180401c0c00403410054152140704120801c00a40d5402c2541d19807440b10039a13480480f0400d000903d0800e1a812036001400f03072a4441241640551041c10414804d0394280b2040ea140d82070300c0c40ca070000303c6100c1c400d010a0035041070f0309242001c02003d400c1e038500700044c0400064440303061100342101d0858580c0004801d0058060301001144c07500703030091005200040c8001d0850031807020117400385008808044c03000b0204030070901c1e04809403e14002045401d400850002d100012a101d4240424050741107604c0b0b90038650766107001290030000034961011a06d0501c148074074049100400c000040c4081242c0150800744480105010720940f0b441e82d5201c42558990041e4072151611480d41c02052401c078103c124991000031800c49092 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 229065584 1250 229064334 229064347
    0x414070513090201031b09030b060a03030f08060a1a030609090102160b0405070b0d05060108090f150a09021914040902100c0f050105090d110c060f070c0801020d05060906091b 77
    0x1031340a4021007046c0c0c0c0300340d180e1003000840309601c8000f40c8200c1e40681e0304030a06889820038451641c4407400003800240c8840155100340340200002c1d42c20000240c0a02820360341c84031310006040103040303d10f82503c0d0010910104d46801b506154002c10401e00842c5000d80c6901c1303424214808000c010000e161040008003402018495600280501001d0f02d60312511903c811008200131500071740810321400204d03451800c0020800c0040424100802c004008204886d0684e140241001d110741d40b0f4580120060700c607041d98803d40d0b54441c0d001e2015a0811025110810014100b80e028510b001040320244e40d510b0380c602c510b080c40d420500c168480504003840a4040e600000d00103600f401d00744003980b4000507606003081065034032014000d41d1140c0c0d440c0c480002008250740010309000080700e004000c0010a01c241c0316564a24100386d82c0d81c01c45080e0713000100e0000000d640c4404021881c2060316540c0d0b03000f9411168078466185c019401046074100030341c0c00d0041040803505 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 229066834 1250 229065584 229065587
    0x60605040b06190e03010513032030160b1312080601050c0f0c1008100905060a0f0e040b0a0c02070e1509010b0d1104061d1302120414070513090201 65
    0x8004c2041005002803003545080303216426a0f44402d28110001080f50304840d40000c3c13031860300240308030341101034111000d08018400c14040c201003603640f1a10010b4640311800400e000504040044803060050481c450800c24a9034500070035809000720000c100e0f100007400c1c0003510180c0b42407814403800948070710004a401c0e0140e108003004500c1907502c14041400001070604082a04a51054030702d44c800c081112050415160881e80b20881c240030b00080416410056003e4005040000d0450740c40d451018000d80540c40300c11b5180703003002480107004c40310f90800c1e03010002260502003034000c0c120007907840090744500b0200c80700326400b00340030a5800c0112580b090008041074400d507111140d20080f584401c841200d2189001d000509000c030326002c0d80d085809079101c88503214001242054000d24424100d42d101c0d16443c080005602c2e1071025203102080788a0321452481c03e0304d00b031621201e032684545001d44c016642000503644403904000910380821010807081c006100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 229068084 1250 229066834 229066847
    0x1050304081b0a0b07050c0316080c1e06010909030f201204140306040b130203070b04060309060e01020313141207120f0807080406021308070b07060605040b0619 71
    0x118090030b2110011490300b911000039031001c880d02034a0013000c01d8441c43c00603561803203140080900b40d0002c2c0000a1509244840b1030540b5000f812034903c1c080e5552a12410080c20024030304c15203031752007011510010208103243c0134001d4510104105611038070040c14040e64903200b28104002c03041704903e0140703019950300a02100e882101c0000c244a440401190418020490b07144445807512410b441c0c006003050040d038000003c0000341d20f510031584103083c03200c0426038151142501c0080c15034900760003807005000940d0001450000c918100c03081d074100320070506241e801841403065210075484102442503100018600001c5007402c29030034414688949945540080b5000c1e06214055080145808041d51011170310000c043d42510456000c1e900e900004e12800001800524194010291242c0c40c0d010fa4848940d134406191400120390405d4800110216800d41044268042c4001908044a0a0105045590100340f003070140400c0004002c2010161001003405000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 229069334 1250 229068084 229068097
    0x1812030a18050a0e07180602250308190203160c080607090602060105010e0d060603080913050736170f0f10150803070606170604150c09080312010e0907060e0105030408 74
    0x71203440041e582d80d0f0000c3d4a40703080d00c030050000270010070011045a80c81907844103480d07101200c0c0d4140b5501564500380c4600c201100030540c881085289030781e401e50041c15480702c0c400c01c41000d50344d091010050510001070f2188051244414060107803d0b0041038507030554000b80381000583d0148400198062002c80e40500100d29101c0003205010907500140446042541d070401d4103516a00f0980c21600111141e90000c0d04490045407a41d80e495081c02152007804041d0810ba80e100000008050265000b0480032092000081c2550003c2c041092130000c24406420328400c070103507083c0c03909224132400050755680c40841d600070010202d10406041c0a4080302d03140c00341854494001c0145004403d201c107412803005049079000902684140d0344410b41c0c050141c04030484501804861100105102da00c00c00400c12480800140c114460302103000d21865140c9514104040c402515201258200b0384c07060148a8000b062105000030a1800d59030320ba030703581044440741c0900e4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 229070584 1250 229069334 229069367
    0x90a11040e0c01031112040602030703060b130b0306060c15060f010509150901020a12030f0b0d110d020406090e060412020a170703180311010e040501050f04021812030a18050a0e07 79
    0x6da0034082070003808e50242d031081c00142c070200003c1d80c41d0341c4014040d001d1034206100d200e07201c3c5401c1c4024192480a90f41103003029040d0303030808003039041007402e00d46000a00c514114801040010501d00040c0d9140725680a083c1039152032080790200c1c10907010701005080310500092095400d0b442000112100c5820940207803598942060040240c200142c0c1c40c24418144240000d4528200000200d80303035000030403680134242d460034030042407400d04040e40d100d65200701c0002c05800768041d403002404003402030156494280381006814041c4a005011544031002d1080000c40c1d08035040d402c66441d4ada080c0e198440c1d071608880300c9510f8055207039801c0c0d801800004100000150300751000090702ea03400004440c0042c401100d42c00d100740e42c0c0c44840040414210b04003903006046030400c3d01001c880510440020485000c444207545040da800005c102d03401c03d503c05802c0c032450644048005400d807a2400292900b405406042000a14400490a030301c5c00768070a0a801c0242 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 229071834 1250 229070584 229070617
    0xc090d0302150901270c05060c030405011404151101090c0b04031401140a0e0a0b0705070c12050a080a0c1b090606080c040e060117090a11040e0c010311 67
    0x924000b5296005000101c00c40e41c50a0301040e48a8010b026440c140700c1c1c0c0100c41d51441070b8814410100c0c201c4a9403c0c0c500084402020529840c0d860091540c101640021036aa5252500042403108859256189a00180801d00183c1c0d150110380000c6030852034075103901c1400380501401008891801400011219000529036025102610489020f803140c042ea020f00c400c65103007a9500d841550004040702d500141c259102c503030003540b80e01400011291402d010b42c0c0c1d1844c038040242d0350f0300003052000c00c8400400c6032194018000d440d01700d000b102c1800ca182e59003a61540c1441008140050100e8400ea0180c400d014100c0e080b9003106000108107032581c91000038083c68024448100d040103030109030325003d1141c180c05059000c812500d4a480d00b212410502c101500c000d04110300e1400080b0040b04080304a03014601d40d802070446140c40c0d1920340904050641064003e50401040b404a500302089a41080c002824049078500c099141d14295109008140c0c040201d03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 229073084 1250 229071834 229071859
    0xe0619030303050f0903211b0d0203010f05010c032a06020a0e0a0f050a090903030605060301060f08160e13112a03030103150209062106010e12070902030c09 69
    0x1032582155000303011036200e1302090b841d813070441d580300d02c00c03500f4a140c13480c1113650b10980000101e8105e41d014103e0784c4005540c11103a40c0002d8558007000301004851b40110041c03100951180500b00103200c2400e22900b904101c0da0042c05031410860f00301580c00683c1c002d0300100070828403105200e580400115a83c51071903802070050707082d12481c0c0b405030085100c089030100660f01224143c6e84010003000d440307480d0801580180100c5481203080684030880040e158854501860292a49440d088103054003e4401440190f0050034001d450181121010304a5003080c1014190481070f1541c40780c94034441640f401520301c992b00121040d20020300c2a00304e03c0403040541040b016101241c0103170300303003000301c580d00d000c280006041003000300e140c1050701005900400d240b13070024100f02c0c140507040380103000342d10051a1040c2c4210704103042114969100402c0e4041c60000c41c2c0c0704000401d040307022603a0b42401e0146180059001000c22003401404085d10030240005104803a00030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 229074334 1250 229073084 229073087
    0x20a03020d0f06270b06040603121e09060507030e030f120c071d0c07030c0b0c030106030e0105220213020c03120f090c011b05070b0a0f03020c070e06190303 69
    0x540060040d20004c0c60101c02c40d1420041004070a10282072088a46682c600c58503001030740d4101604046d4002e03900c010000004181c40c1d42c06c0110042c0782c0b141881e01250241407110010b83c00d841c0b03002c206000c6812300c05e1540140a44a4150701860050401c40c641d0002c245030150703c035240741c41e521441c1628420204030400420414056034180e50105580d20700e0354205007030300c4020180380c070900790008a101003a5400340500c00d00070b240502c082d00542d00c0d0f040d100082520080c0d5582000001407085036018043c545803d06001c00070407044c0341c0002550b01c200c016141c000001006550094159036030701e039003621046000e400c119924114490820740ea68803070101d14409048081c0080d105901c460303c91481581e0200181143c4040c2c0c0c401101c0c8210540702c0741c8292407464401300041101080407002412148694070741c1c03201d5008016040750015aa01c10825004102110303202901142035012104120702c42101503d49500203404211210a17503010085d900c0400018107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 229075584 1250 229074334 229074353
    0xc070305070512090f060c031605100e15150d06110927010605041a070c1e030b0c13031101050c1c03060609080d0e0402090d030e12030a0219020a03020d 67
    0x90408a41c0d07841000410300c1404468041c0c0d19a0782e0094000b80142030500d41c0240340e0b607140ba0700c03413010703503111041e94a043e200b207401c4582c001c03120b80c0c0990806400310302c134000d940c0d40ec000b01004500b4401d144034002440c070141c18100070040d071744402040d0881c00016095504002e8000e0402000e07208000b108194032a8141d84415603103c19400064014060000c89060310031000200c01003001c100031020359030b442403208460445407150b000405400b440c241503280c03029210b00b10310061071030508000f0600060001d100b0040100041241d454602c2d40d81400c40e9807120b60b14008880a02c0142d803280904400900a8050300ca5652180b2100b007040303412008107030b2000c1250584400c81240c040d0014011190554050300000c001d85006895020700c0036001013001d03160814a0020500503200701c00c0450115001c00320003042842c0910b50300c00304044900c01142010440e4100a6880076500c5020040102c201c0203074095482d036101c00c03070140d074002d019074848040900e00750425 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 229076834 1250 229075584 229075597
    0x190905030d0908070213020c03070305130905040f0b090c01050d1d0f1606080402100305100314031323090c090307140102060a0605061909030b011413050f0c070305070512 75
    0x2d0102c035078004a01345c6d0b07a0300c00c0e2403e20805030029030600c3d80559003501d031540103100210508032030304000034141a59001e03140c03255204031454400884079240c0001c207c0005408041c45401000c50f240507640c0c01000d03110940800c0c1808929407100c14611880264071003810130309405030b03056500c060302d0006507030440184c004d100503c0c0c840d541e000031654000c09941c000c0d0301816415001c842c00e4400d400c083d4012000800480300c05175247d039460707002d100e03100b911f011796000420482104210240001c0c002c15100f030805105a050090301d2949652004080e071041c0d0949000c01c0b4401400d80a89902c843c001c4c0c21100800d48a08511003c101d82c20070441c010700ca0200000c0149000c2c0c010a41191405006582440c2042146003110b03510040c820b4100a44890000041004101528000c10400c140d004c1c0c0c41c0444002c0c803540440100c00102c0041c1414140048030060604441d407000303020320510b0b107461803440c00701c45500c200038018180e44501c02070741c01110080801010f5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 229078084 1250 229076834 229076839
    0x3060905150108100509031303030f030c0e09010902070c03052505060c0d08060102100f0501090518060601030c03140906070801120b0109020d1509020d05010509190905030d09080702 80
    0x4405640103440c1c5207020074016040d00740c1000500280300b10301038002c903070041000021340f8186800400c2e41404042564010341c00103040703441444084c2d8040c0f142103441841740c0b41c00c108142c00603010032100381c410700c10280d60301d9000502c20180025101c1001c06503a100302550a5031024038040c040010114408089a065003c000106450013104881000c038000c0050130b20503039002003ea0341e0a20080401c0d065000702001c80d4041e003400d220b1454904c800c603c000946d035040010030002c0b20001801302c90304004600002d141303000b0004000364805824600865004904401100508000e10702100349000317580a0040c0000701151151240c0303c01c1d6030303040507a82d8440081c40d409412010180c15000b18a00600c00c8018913001042c606030300950100d043c100e80d108800900707403a0390010112542c0499540c0aa05107402807d00400c403c8802c9081405d040c040344025010340d01030315220b43c2d500c05009081000500580d40780200c28201003001681c03606101c490340d8004201280f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 229079334 1250 229078084 229078093
    0xa032607210807020a0b070e1507060606081b030702012007021203190e03240f1510030f09020402040b04080f010903080615040e0a020408010e0606062a01020403060905 74
    0x200d040c49048074500c41c0f5001e81c01401c0144594841e1007802a0141c95001007101c1c50076080055103c00b42d0b240011610511500d980d080c4900700b9104039400348d0400c50170410071805215001d2007450554404039890b210742790340c984443d1016401410901007200c22882c0b00003a00c201041404080e0503401c4c000c0c1c074012003961b120141d1544070f00c1810140b03040589614400d156140c41065083e40d00840035045580349480315080340840d0018100d048032002c45c203020001d188542e00721a035088100055030b08030100c03040c80040d240401107060030b4100f5075620005d0b81d840400c3d812000e030068000d40119512504c464511403030703600a001c0c04540b481044810309484405200d200521a05075440c5240c94940d9810040f0640b070842300d161000174140710100e0f5149501c400c0317500500840a00580d95031130141280e0940d40880c00e1600d15800c90700802c9101e4a902c000c6409900010005807400300c046610260f07024100008071105600c085800300c200301150340414100c40c080c50484 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 229080584 1250 229079334 229079393
    0x903020405090706050d1d010905071706040201050d0f0213030302030307030c05040b0405060c1f140a150605090604030b04081e0f04060c03030e0d09060f0e0a032607 73
    0x2e568a030414030800000840410a0342d0140c000c075403040c0360900b8800c502d5034060000340541307400e40d11190001e80b11900800810080700514804550b125181c40307019180382d141c650006003840c05240e0517070308102c2c1c41d1480003001c8012a07040b01e45024104211101460710390030000d5803600300320b524102082c5005000c0c10715601a600f55800c4441006a4602e4141004140440c0790000e18215080d8441d04562149480010301440450f40395858001620814001000d90f044009001e541e4072504e040410078040000c922241c0c20b40f0741d5410040d40e5003000d89c0206989102e0f6908c0505a0000c4000340810448482c3c0107007c40c00742111210448081d1040c204001d109942289204040811080104501030124005154001e00b0300081542a040300242000b81150013400040d8211000b8080d02c3e0300300030b00380c6008001d0303e4200c18220484002c110360740c004c0e000141c80e48106641000105082620021036481e86008151300c0304240e181800c8044455880c0d81030461581405 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 229081834 1250 229080584 229080601
    0x20d02180709080a020307051e060d0e1002030601021b12031b070b0f040909060f2a0813020d0510020a050307030b06130306021c0203070e090a0b0108040b090f010c0903020405 77
    0x1e004c1416002030241030700324606410400c2800300c078000100da101d8114961146517a400c00640060b0540c520301048240604203000d041c43c030b90140c02c82920788103000744902070f6030014091611080195080700348684c10b200148081182c10401c00051100084540c2d408620945001f042c05200084070001500c4800c2c0c07900f00d0081040240903a20180702c00c015640f000d41080310b03128004c030340014960b4011141c1c030303094800315200090305d0610001954400c05034003100f14440e0650b40381140540c209004620002a441c03240a03118149020341841804001e02407800b50403403108045544200806001e005a00700f01c508402080c6080d0020445041502c00c6500c0c070107000444402c0e45095580f9a8002e4209030f858154001202c000b805211005200039801401251500f4504441000400001e80c200074034031600344d42805050852640c00c1000140c10580c01954180e01741d40380d040c0f40745404070000c0303903101030f60170620400c44668004940c1402e0740d00a8409000035501c43c0f94 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 229083084 1250 229081834 229081843
    0x4030203033a05070f1713081b01060501111c0c03051207210603080306090717040f021201020a0e040f020903060a0f0507170f04020d0218070908 64
    0xa90107400400c00003401c00310004001e145072051020108286820148030303440c100900d12a01c10b059550802d001106030410f0030041c44819614040341044c9842207444142840500071203009402492646d08100c254408d440c50b441e40300ca8840c11204a400d20f41c0c0c060002c600c2076502242c4442e000701c40c60030003c1102090349440110390748501e20360400844204469900507002c1000038000c01c104003007108081400344006569410094002c462480e008030100c829802020303240a1041002602100c12350764009001c442000081d43e50308425200e03001018502e0751a007020b1020042000f4649440c00d032218000c0d61101c182a100520b824200d101d5181000041610803841c0744252034150001c00c00d0b2040141c0140c2003441d0840840c0ca05042922915201a2102c40c00803244240d0700c2259841141890441c000290b4450b5140b000302000c1c00c40305815541900280c1952108105503010580c0904011604003280c407c0314034111003590020005000c503d80040c0c0074a0004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 229084334 1250 229083084 229083089
    0x4170d0f0f0e040c03060f08011a09060a050307031515032a090c0c11030a15020f120c03090c01180603020304110a060c110904030923040507020d1404 66
    0x440d900103048000c0029a410084034000500304045103520000c1a141c44c081c160800c0b1545e200428500e00700030b128041c00c0d0194005082d16032404500d04072003420070b00102c080e224151060641d54132000e0200720445a80c0c0c102a80500c12a2030001c200540c40c00614840c0005942c202f0410341090302066007091940b0003d409006408011100524040a509240030ba40100501116902c40c28801501ea42d04040c0002c100e50601050610410300070074170780103c1c21009852001056543c1c0d00000e902d000325158856400b013030440341c9107140d81c00c80c0d1605188241010282c9412a1504d10650040310104894024207003001c100d075000e03050103081010000a2205004e0404008600942009005544a115039411082e0b992a01041d09010745a80d030b0321303404501d446081c80c0030034001030082e95024003028010840402c4c2d22040c80800e0707076289290b411203c49850491044000082c44081e8050b2404061045c29500068180f94041450300c50312042c00d0003a001600318000c61 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 229085584 1250 229084334 229084337
    0x21009060201110909060f030f010c180e0405070608090106030506010f06110c01020601140406150207051503090a03030e1c0806030f06040f030810080303040507170c0d15140c04170d 80
    0x102e001c00d81501d0131f035451100c007510281c101d0780c442607584020b80c25140000e00c0b2501050280512141440504051034094040e101803008036040542d201e80e41c90740b4600c036440c1000701040c080349410200790011720042d0b0300441100c1c0d603942c4078030242c0440c004602c00c020100710340b8040c01d03401140106501c5050b07070058004d0300b026032a20038011010f0042c2e0001c107910982d81c4101050460000036501d4030004298010550a0b01300310910003580e5a0700c00034a00b03080c1c107108001c40d0100005c7d00e1400c55a2600e0701086080300038072100d14121000609003c5400801d95810007241d222402c01d1003040c0480496070065071011000f6210001624003070700943c0080c0030103000c01c0c000c4941e40d030000d07940b800c0c008546030365104150842d0000d03607040b2015004094100034800158140981030ba07000c0016000c0400c5a00015505007402d0b01c0060000351008950b50070001c1c25403060750311640e1011520309500d030021005031154080d0242a200c0b003428081032031805030008880300308400c40e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 229086834 1250 229085584 229085599
    0x17060103030e0a0906080102041502061b09040603061d0c04140c0f1b06060a1502151008030a020a120804170f07060f0504030e010509100509030106030210090602011109 74
    0x20340d00c04032816050544800e030040d4480707400041322a0300d842444002c04251000584440c00c000380b070040300906407032010443d03001c5420b004001c8000c00c111140050810030706a9100031041c0820003030905541b007c0c140903d00000d0840d1240001c0c002c450700c41035407041d1480086448100000c4400c1540346503501001d0200045000a00d40000d00d01e8030203c00c40d1303e0620b0702c1c01008001145240102d0181078110b0310910003642404101c03840581001c005682e0341c5c91500800030359660401128000f420b03030241c00b2903040d00c1880507586c0a82824429a0750343d440e541c04c041c0d42c3c2c2070007050031110458460354011195100306081030150f0f51004c1001003a45085c41401407a401240d024031501d042041000002051845503c000c008180c41c0840e01e890103040207412640c204a4540c140101000341846c0c540c0c2d00b15410b44110203500b86103898482e41e4011900504040d00000c0d0014041401d54030102e400c8903d510403141241d002340000d10001807c80f609001d05160f140d0406d88 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 229088084 1250 229086834 229086839
    0x12042114090f060408030a090504020913020a03200c0601080303010e010b0f120403080621030a030e0115060203130b0702060a0e0d0b10060e01080402030316031b061401170601 77
    0x4040040c010514002c00d85842c01507840005499503205900000250f40300040700540250404204001442c0843d021400c1c446041d020801c22070800d800c40700c449034000390b0f007a581f5009501c210005480743c106211701d1200101c19840c960b00c0042d034003066218030000002c2d0044008103d134141d40c2c440e004502070703034a08605810540c012000c1812001020f11600c003860140341d4900b03100c0c6002c1da5a07516035060010601c4070700f00c211014490001450030b071460406500108895102882d40741c0000c103251010940c43c0103001c2c022482c2200805040006500da600201030090003160048441c0e000d0f9546507020308a10542c0c00080d0032a00605c910f288460203030a01012000303016050004070340081c1d580000c02c800032503806442e915100410f0282c2c590242d103011085100f800c05015a0901c4d4001942c0d038040c482d003640e90400f20090342e41c1090300c1a000c0c0199542c164a003240c4450071454442d01810f2082100040b0005850001406024182c0842d216010f08000340c4110390 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 229089334 1250 229088084 229088117
    0xf010513090c14030f0f16091401170a150515010206010305070501080a0b030d030e010b1008040609030c050a12140910030e010b060f031012020a060503041106120421 73
    0x8103002025500d40900c2404144840c1c00780300300c1c41110286d0005d00340c1400112488094450260050750480d0b1602c005c011403c0d050368080750550b80c0310800d00194680d02c8416900e45020074900404000c40420b0f100110011900024050140c12140d100740e9640d5000483c3d036802d007440041e10301d074000c0300c1c10820303940903101103a001030001c100820307110005400310b8035065041d0480c4000030303502c60801c02c10407000e101c1d01101400445111140d0220980f0060009c900500701a1100f40d035002c0101c01c1500a4280c203091550120a41d00c4201007800e1001c4900c0c509520140400e410b0b000340c1c2c1c0172a085204841c1d81078001014146c88010902e011401420720b4142408550340c0c1d1480782080d5901c420191420b41400950255a403400485003000e0800f1a0700041400c80003005110040c0e91b01c0760803405039805440c2098a90b5039505080c103150403000c1500c1e0704883c2c00540c01c016000e01588441c801e034040e03030005500a001c03404141d11080302d1684070b000500c41c06004d01080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 229090584 1250 229089334 229089359
    0x1060b2b0b1c03090f080606190b040605252d120e0a050303041203021606022e1401090e0c0a090c02070306020a05030910060806070509180f010513090c 67
    0x9806031414601241d221a00306401d000543c110101b10b03401101005950b14103203d0a002c1481440c2c030300d21030140307401418022030040d07010751810702c4800b2480165580c5813900d080310f81000b1441520580115042c14165071401800201440d84c10401240400207085100820554043e200d10f6042c400c050303045804120302810203501a1460703100140d00d5500704003400c00341000e080d81d41c0040049250107850309071140181c0c04c101035060404c05c24207030041001d440c01d5404000c800c1c00c1e0455001586101c0349801312074000e00307260004504000c0b101c00d8031036050350b02d8540304021425110719110b035900c81d0a0744095010f10030160030300014035290401480c80205004440c0303002c0c0c4a6941405907040b1001010000d54080100b000385402004403083c15503031150200318180c00d02518a4031200001e04103418000d00040007210b03902d880f01c2c480f0b00002d11102c0c0840c641802c011900c4d40040030f00c2136504c54818001c042c0f07002e0280344a4180c2c0c0c941c1c0400759180c494584902c00381c44 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 229091834 1250 229090584 229090639
    0xc1e03020d2a031e0207023706170a0207051e03070b150f04020c030d020f0a020d050a0507031d04090609060b040b2202090603070305010612020c100e01060b2b0b 71
    0x508d185d40c0d030212a102c0b0410840340108507003a10a00c0803074507642561312076180d2000c020814407040d4828030030900c11540d600901c0307410b009a0f0326405070900d030340350081072419128119540e0300032070385104020001d0280ba034440e03400c013802d41c0c444000c0801c01d00c080c0b84d6001d40c00044501c00d01658a82076008003550560340d016603050801100d110000c030b0f0000b1401101c2c0c0741d40000c6147c84e050341400f005a00c8403003400c0c201d00346038900c86c0c000c040d030103682001410301490280384c0030903c032a1000ca52085e00700038001d0060401174680303080a010f500108446103800c25111000314075041c010150b008002409480b018000140d40000001e0201c0c5040d14941d0b01300701224854032110004c0d132080820b504c02244551408200400d80d2245041c200009071052000074104403000ca244a004040d061000c00c0d40081d52045e1401404240e1210b030000e071002034101c00c554a0b001510b4154a55070175054401100c003229001a616514201c650100f0f0010103d0600c8822000f84400c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 229093084 1250 229091834 229091839
    0x7051605010e01060b0405090906011809170301060f0320160809150711040b0a0504091a090706030b030d2a0c090f0f0c1e03020d2a031e020702 63
    0x802c00d0380c0414003401c41d50903820411420100180c10700050030300c5203500350032020450040051358035001d880d41d20121344007046000a91244128018041c4500c0713465044503038518803907901d5a44403030161400c6800f00104d0003290400703942900c02e2580c440d201700036500c0000300500c0d10b00066a0510080840341c4202c900031402d11486009880d198207a4a51501d50080d0b03554410440c100801c0e4031403036014203881181018039210203501e8000400701280e1058a020032000300c1d905c3c0011380a01c40c00449000301c0189001c000d503142c40059400e085650f01d03201008418502c00c14152030703001c040800000f10b440b9903030800c0080c0c00b0440c4c4401480700f401c46003050207090740d0303030f000c030350300e596000b10075040d00d0b61020480c000e114402d0003410b054001c000c00280c61116400b0b42210440500500032000100f488800c9a010b03804464044c4100141003080071440115060034901d415074041c11010552a11450035000344a4600c0701422588082040c190464035034010398007079031080780c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 229094334 1250 229093084 229093091
    0x30718080d02010905100603080909060103020d0e01050604110415140715020a0305010605030f01230a03050f070605040e06040c1e030f0f0c120221040c0302030d080705160501 77
    0x36010805200c00c0712074211550010072552080d0600525160141d802800c06a182c0742042000620190854903a0381c0143c5d000c40f4556140300044e0000e008101c42403030020b0520300030000c0c12030194459840307540d0840e020842807001c007454940b907014900401c003050103402d04111829029103042c080400070310015500e08603c507580c0f82c043c403450882c0941101e4000c151022110707090702032240034044e1880c3c014118a080401d407d8480018810b00000e031345480d420354038a03401100100c900706005081583d5140d502d1518680e100c030201250400ba010f515070105100d4880d104880c103c41e506002e41c0c9494550008000042c0246088a000d20180380c92440c107164116003417602c000c240792030003d02000c18081c4542501c44034800211034600d01002c0750142500304124211807001c8030710050f19848807102038110320800c0ea080b80350111940d0108001c1080b0030740c3e01002d170391003070b0103407800015400025600c0031015990030000c50001d200100c0c0400407005810600c0307010f82c0012 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 229095584 1250 229094334 229094339
    0xd0e120a0210171602030d0509011811030d020a0b0a0509100507020303070305010503010b060a0507060e07030803090c030601030b010e190c0e120c01020a020d0f0204050a09020f1203030718 83
    0x46030000242d12500104071000c01020b0001d018a26095010510103140011482c0d8010025120b215003500051021782d01c0c004551019025801980c00b000b0384198590791003018148101e1100c244680350313110b072003040040d04500d40f0204484035901d512020808150712003104aa014000c0200120440d220b07002d02c0801c10042405924014030081d00916503d090210009091711416000b00e80603030306040c603100160b1100000ca031030009507858100c0d103039112464047e000d0800e00740180c1841c41448400301c18810484001c6000d80e400d00c0c1104e100203240700600d82c803000c0910000d40b80e6010000108203499001c68030640c0099400350f0340420740815400d2804aa00e030800034800a258805103d801c0d08040040101c0561410024504d007011940001d50340c0d103250310300034024004150450704111a841c001014154010014040c42c542603110340e00601c85590203038481e900e4281d039541142002183c1e2810b1804100207149595a110b20540f81301d816a01c49014400d14103100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 229096834 1250 229095584 229095589
    0x409030818010e010c0f0e091915050402071b0f0506041202011101240816060c080714031312050a1e020a120201020d09080d0c020d0209040b0402040c020d0e120a02 72
    0x41007154009515102c6d81d001c2e10b1400140000601c12040340140340700c00c24881d92220804410440d0f00c034841c4042070b428116543d4695001280e84801d03045400420208100301464980881c19480421040b16080c0d4030040b2101150407480f489030054030800050140d0b00c2c01400740d4404d1f90041c1041450f20b0480c040e12400c40c0c0340000c10241b00c0c41c0200c0c40c0790f100b803a45000503004281aa005080102240c00d540040440034131404050103d1010300a04200c200d0080c5c5851031307005070026403005d16265100740c40f580903004a00003901d80040101340c09081e9950000041d80000040c580c50250b65100880400c80d1460001c0d00c560510f0050016952065050064070002020315503001480c400a40781804d441a40740522148080034054400002141500e40c0d403e4500440b00849900224100e40e410600107504420524100000d0000394405a401113200707031410029080d070003101302c0c0c941c1c1441c01e00340000b800302c0c0441c283c1403414096000c0c050402806032901402036600 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 229098084 1250 229096834 229096841
    0xc0d11010e1c050d0e030d051801180801060f170a02041a0d0f120807020a0305030604110343180b0a080405010b03010b0105090d170a0207140409030818010e01 70
    0x6088035994000b01809070f58130340c001000000301c0300982c010807c3c0407004002420360b01551780c503031000501104030b580c000d83c86048482e031003900410240c04410b840e03010090191509000e808800443c1c2003001803440b1000c030a40100b5841d51000d00113443c519803c100c0504040070070503010481d40b031030300c1c10640c2d41d207030b40450002e01c00c40c4075403000503a524000b01d200360018042014400d0390703400c10040c29004164105403d80c94648155070f9034480340007900a220015001300030b07000100401c10ba80700841c0405d0f9484000025030000c02c0b0404039015a0780c1d0305400da03840c15081130403400d9042400360402c0c013240c000c1c00d1444036485895101e0081c0c0b640104408000107022a000c0c0024410207115940c1c0c0e00c50242c000384040c00202d40064080d1085400c5503001e10690b1004100b17000205240441c40d0040c0c415aa94032561004025038503400c0b40141c5179810200221030b9514036041c801c0290959140e2101c2070550703101500940f10207081d240d950311554a5004c0082d05080c00c0c072 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 229099334 1250 229098084 229098139
    0x80705130816060e0f030a15020f120105011205011a1b030a05030f09071a0a02030705060108060907080625020a0f0c031203050702060609060d020316080c0d11010e 72
    0x140120b0054600b90000300003034050f89485000d0294000c070900241c801240031803000e6000014a2440302c00c400c4084001d228583c8000e60180d4041004030b0b442d80304c00a028100c6009a0340e418440201d980c50b041107400070f11a91403102110700e2804040c810140c041c0a07a01c00101c0260301d1010350074410b0b400d5500021140c000680000108080000700c8055281c220070460010801c650030004104030313401616240e210b40d0b002c0460032841c0103201700221480968020241c031400e581d40d1800c5561088261840130311070044100c049020840043c3c070504c46d0111903403041d01205021a810704000030700c1c884104601076110404003103054070300d113851003910451012508900e103040a1030350000701204041007504060502140b07907400202c03560440d604a40000590715000002401c0d80140c16009406003c4e0b040300104005401d0030340d104441150040d41d20384035200040101182d110b01c801082003c0c01305080005500c904803505410704003400d40c400c0313143c5d0503e00601d88407025 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 229100584 1250 229099334 229099363
    0x703110604090f02030901060b0418020d020c030a0f08150306040f0215030c091903050a02121006091517070608190f0b0f010207050a0509090a080c2b0807051308 71
    0x92105000307003403288c003000707100000c019402c041c1400c003411424598010703034114003a00451500141101c40e030484201c9403401c822682c1d24481210054480c554445030003000c1000c04001803041d110302c2044060900f03004000d0400707651141d4030b1b81031f0b210b0040c1c030685c2c019810044000400b140c10f402503001d0400039108544074203000c41000780a4441c1d400700b18080d0300c00703c000c0000802c0050f46030f1210350304031002d005050b10310740740ca0b243c0150f0a00340d080c0346041c0040080e50344560b500001c21061031300c030107a001c240ca030b68228014084118a80286a01c2040100716580c4240350180d000150307010b6640340131508445c0f040603110122a040040c0344d80d11400700149c5000907200e400d1242c2070029040340d0b403070f00000401a141610600340905a40350000701447c2c0207020f02e604007039001c1c00c0c4945170b1041a241c156604509108180e412800b14076580f645002e00d608123501c5c1a1580c0d5060150f91180011149904a4248141c4000c8040804603000070140003124807440c54 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 229101834 1250 229100584 229100587
    0xa03021b06091b010c11040905100c090303110712020112180804081005190e0a06090f1e05101a0d06050709090e07120c09020f0a0e0108090703110604090f02 69
    0x40d03481e000d1100b00500819041c0704004540f800001c1e02e0098089031a46c044800003100074880c240241094100d02c40c01e00710781d01d07000c9100700c5140c12a008400341c1340640c0d620000b0400754202d081c0d80710320320b01a031289011240c5042c401907105400100b000c100241000c120800184c0c02c2410460b0081012070b8800c102003070500811404102c120140340000b40148000e0426038000e500180e924880003d000381c986400582d0310720301704a4a0041907110200f008446201d0034410794404142c402260740082c1c102e40a40c14022504501e40541e4004014240782d400000580006103000182c4000300c4b0300c280c004004560b14001c0d0600814021440170400c0d01e41110010103600054001d41c050a00e0316070903040501000600c00265503c02070598031445103807c06180c1c0c0801640180310450001403082085100500500303840041616800c2c2a10121001035920103c02c4826903072a503c401d50030004134034012040400002c01520007850503072030311140820f07039600460341c00c04942c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 229103084 1250 229101834 229101853
    0x30f0d0b1201050a23060a15031d0d02120708040b1615090204150308070206030c0f040b0702040b0d21030b0d030201060509010803190509130c08040506100b0a03021b0609 75
    0x1710807032034050410316441d0b05080c0386400000a0810700c1c05007d02d92540102c05140c00e8668000d45c0507503503000c1c1752000034000480c014001903540440360a5903006016850003030301c0300c102007010741c1e071b1855010f845107081a0520840720103540241c400b0308804424105110b01081c882050160501000c10000c1034001d0a801404199680100f01400da280e641c501007000c20411000d4030030b003c3d4110313241c4d507481c5c50f848042d944a0040100300040c01c80b0004000030000c0b40c41c802080d0052090b6001d100362903c0404000c1c110056603009413894440348103400c44100800c030940c00c101d0050070000380c0b200082c4046820851040c0c0c1c200c025039501c480c184441d28060362524010038103600290b00d00024401c030f00300284240703c402c5092040208220078950313203020340140c01002040c410007403003078442001002c0c140241c8094455009020100e0555030183e42003200395604980c03401d00c0d1042d010022170083d4040074043e0041da04019043c1d54900081c06543d0103400060010007140a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 229104334 1250 229103084 229103111
    0x3060518030a021005040804050306090604140615010f2c0301050907030519030309051c080604110412020a0308032a071a090a0b1008010c02030f0d0b1201050a 70
    0x10265120345034680e10902240000b1a0300140c130400c06451128003041c9500c3d20b10b452041c50185400455240c00b03204100301d050440003409a21a80c01418801611081d00252980701d51050f90140040c4e030340085c03c3c1c1c0c0323194001c0c69025038010061504940d84004e90304220700d8800110200c2d1008141c00001918170b1600f400703140e401c000c200c0c003c1c1005a145503a195603c52160745000d5019007440d00c10400d150180e84a01c64a40d04003003924001c0015500b1101c4030b1620500c07844c04603080c00046030060500388035154420484d04400c51500b03081c0300307050103e940a00c0301280c2c0100c03071000100000e140b01c0c02850080c0100e21408641c1314402d03030010f101459100d560808a04144040c00120380c0021040500515003251030381c0030f4950340c2c03000e820310301489005071040c03d5072014080c3d48145d0f804210111012440200814220310740202d807a8400c20031a08074002c011700c142d1141d00601ea00640400c1001000b00c40c101401c010a682501c8084840f030f1011544ca07003076002e690 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 229105584 1250 229104334 229104361
    0x81620160b04080d0207260f0a060c08150906040f06091505030f120d1508030c060f06010903031403090718050405061302060a031a03030d0617060709060c02130501030605 75
    0x64814006486911f090401408096001b00c103841002d5071012102c1c203440e142448180000c01c0c00e88240c3e014010b6508150014004048203840003c0c6540002500a420075801c440c846100520804003621003c042002070103a03420300e0503a540e991000040c000c140d6201322585542c80e0034042d05510328050405041c0705c0d03089100121900a440c08510840185040b11044c0005010010b6501c607019100003c1c08400e401c80310140c44001036100103503200140d10740c031420344130025200b150745079401182e481019100040108644625101e071402600f009164001403140c1240c42550344c40410058500d00d1507600c41c82c050381d030f00038030051000c140070456000b140c488001d07482200982c04501c0f64803589140d0820150b03124489036020548483c805402d100040480352506080c402e080300400c42e51180998294403ea2042c00300740c40440c619204c0c40140d103e4100091400d42c055481d51a0141e080307901a03203003010307003501414621403640694001d00c800140c6242690603a00e04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 229106834 1250 229105584 229105603
    0x2090d11240304080a020c13020702030709110711030a08031003030306050d1101051e03100801050a050903040618090501030605060940051507081620160b0408 70
    0x31210720300c154440506004044035001984400060341e40c1040102c202c2c1000b1100d400729074080ea10400720041d030301c015006040c09038003c4060350340711555a44903908640702150700f0408030500384103210118aa4000c1d90a280350050242c60035103540750346420060f88210b900c6214034554500a10501d58107210304400781006441c40501c120f410b840d14682000350200311410030100107100b2041315114113541940030700c0c00ca0203603101c3c24401c00b4045408800e00840314103621b442d0008803880120700406028020320809180390505143c82180c0c2c00c076059412000309500c000f80050809040d00c0751900850085100054604283c4204070301400c020f0001034140e21600960100b04000ea40003401412070400404903080400f22400700c403500c4004042e105004003404c0310100c0b105910f13494455603059842c00440e6481d042500010300300b0a20035070009404140400c491004106141150325050080307425002c1940c2c8058200710054100c0141200003090402441108100c200341 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 229108084 1250 229106834 229106869
    0xa0503070b0310140102030304020904051504080d0e07140d081b010209010f02030a0f03050a0b030304080a03080f090c010c020f0306042003031c09080f16030e040204030305030403030e0102090d11 86
    0x32070303120380c1300001c0d41e0340005840a44550f070b51001040420104104514406240c10107a840d24a418181505150080503890305054140304090b107210101090030b40555080c5915455030000b20024042c0480310305a04568841c410000443c40c5c020f4113140200c0c0c80821800503035101503d000040c00c0714030102150055500034000c01c6070841d0130000031003194110f071900080c0c503510050f910014003a04084250180000030700480d1400c3c0105160800f940a07840d103022945a8801640f4242001c980480031758000d075000c800a03600c643e070303500c1d90140020150500b442e100400641441c1e4140c1d17003165080c800314401646081001d02c0004110b60880c0034500b4209600300742031423041121100c1c0807090b55019210104400c42e4280e070883c581910081780c0b40c08104696000704074002900f640840d00c15180c003603061405008a900b50396155840c241140c850b40e5064002e17029507640c14600c2c0d5002d2042400c00e495002400001d58001ca22042035015000240958915210b51441 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 229109334 1250 229108084 229108109
    0x90601051603091d160c0f0b04080405040608010e0d020118060905210a031512062324030c01020a0201050703021c030509010c0c0b060f0a0503070b0310 67
    0x1145a8101050700e510000034500404012228501214000080e0300700401614079140504120100243d07418420801e1040e03040503e0003511058070404001d00000300510140554034002842052856411074031a044c594246525080001e0a980e030b0303500700d5101c503951071a009069001c10854584241d080340020041d6440462100300c6041000901034016a102d20385070080001c200908200c001e410140502e4900001c0e030003e00d0385c0c0c0711340e41ca44002070400340100c02201101c840d14007165882c1741607101050190344c80304003501010903103103140c010381d01310107080b8084008640d114410503844440c405119155092014500c903050034081d91107510750a02c41e0f600011030040e4182c09007405501d0302907501d0101c0c90546e502e0384000d250484c865501d8042d54241e000b4601074601000280b0a015015004450022100740d01400c1041510b020800504003079002082001c4064509011581c41c0c03000b181c900700c2c241e44070950061000080085d6026081c0c1608050042c592404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 229110584 1250 229109334 229109341
    0x3060a140609010308090d05030f0c0c1801080d0f020102070c030c090c1b06021e0406030b010f022406030304050402040b070c0b041206021b06070807020115050901141c0c08070509 79
    0x80b61741c2e0140c035104a004050503281e00050140410684080d81d850808095591581d503010984031140c0c1e88056000302d0100f108401d60182042910303060352801e20050110b041e45c070b0800c4822480d8844039005555080050002043c14035031440040e500580ea881e0b0454644a160011216590703044c0003001400c2c068145900001c2100e03129140e00301310f01585800800c055941d94121866048445410008001840b20f4168000700300b409026240d09640d041503000aa8a90f1030b4800401540954030b40485a120020b900700c0d40c000e803001d0112400c00c0d44440c041800c90b4056080019000d001045460810090340f02d0303000904014003d503802c051620407140140540c040e40140034a8001c16000840e0b144403940024900c10301e01180d29500305806d01602450040c4c80040040d420154407400b040308078000708007100d02c06090820583c2c60550640a00c40e4001b0410f5480051002d004065801d00c01c0012006401104601c521a1421035040d10f0084079902540c011745100080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 229111834 1250 229110584 229110593
    0x5040e0309041a120f1b06160312141503030a1b0204090606060c120305070e0d0501110408030301090b030127050f030414240403020d050c03060a1406090103 69
    0x340d035000c0d04107440120720f846064a0342018854904030150b0001c008402c0002400f000140340003116031a20103448080c40c03484202c800c0c805c1d07042d1025820003010401c00c6050300c003a40841594034000e141201d001c5c0c004200302000d803040700901c0e984000f140000c0c003000003020b8480550040b0104e005502c3c0020039580a0400c3d418070305030800c0801410f00f1001035446e0758100c0d40b50300d43e200f8420000c0503101c0002402c081e2000c001600c0781c28801c816982c00c58003d00c0b484e40111816280c400818032040104001200205c8040341d49540720000960251261305c058406844001e0145403250b044c080c20340100da1074040e941d071190f070400a4030300f82003030700c90909454039038480c01c840d08100c110b0900c81d02d8050b14954100c058400000d00081e1034003003207001a0721203001c50f444200640304041d11501e04e135211001c01c00380c1808010420042c50715022a0002501c00e40540340344103400c10000c3c0c18410112045030601e903e42544a00c5860304440700c41e8014404c6404200340d5040d42c0743c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 229113084 1250 229111834 229111837
    0x6120506010e1305120a0e0d020f0f030f010c0305010510030c050f090d050708100b0303030c0a0e13060305030304060c02011505010311040308031003020a1212030203060f120609060105040e03 84
    0xa456901111403000c9000d00e00b00c26007403006035800c02c0c11a07800b401142c01100172071b400890f2040000300826040442031408a00000c0703119001004000b01501900030803940b940c0f0020030703a03070622810389240801030007802080400211a01d0001d0190703d4001030181c00b0b11101203100805141c5204180e4240c0c101c0c1c1628141050503032020f80314450000403030010300003014080d1240c81a80e100244090000940000102c020700044c001e180c1010240740d039038003081c1c3e0b0505101c1d03018402200980c2c803c2c072108a900c6001820001e507404613600540c00c03070301e19400070356158100100300000c0c05054000c0340d54000081c0300801080006a2090590090500945041544400c800c0c2000c3d6680d00517500030310b412018007540c83c10044503103015107080d403100301d001e101c0c1c42d80d000504501c1c40103954412500014501a00c400d0150128021341c401003111f40d20201c016102e01150303c400c40d41002c04103800005040341e08080d20494038001050344454800c80c200404001107110110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 229114334 1250 229113084 229113089
    0x90e070c030c020a0e1f05030a0f020922050a0203010b0109150c06020408010e03130503030a020304060804061d01091112030a03050411030118150b010915120c0e040612050601 77
    0x9010302d1003080e107200007080a01994481d665084041d828045000521804c0a500c007130007a41482c01c0c140c1c1c03281403544031143c2841c068400340c2d07071280c808050305080a2441c0e000d8298551600284680501d404400084010594581e0b20540d5070100f103003000d20503c0d075050824203144840074074184494402241d126000410002c40c1c41c1d0681c10800907406540282400c40001d002452448540558a0304104221102c00c9500c040014680c2408011184441c060790b02a626080c240a0241c82844020f00122030055880420040a10800d00300300d008885610010500c54004d0400601618042424511402d1641e03821615a84000b0441d840c40225003400b00b415a110b0030305580c0b688050495035095400c0081071407034515400300441c860b510507103401000200d03104c40c401c21206050301c810b010071000101030083c0d034039054584d20040320f1032800342c550a43c07007100c503000d403000110101c0100b03030041018401c516042c080c07036001d040e12161010780740d11340b9110346540f2801032 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 229115584 1250 229114334 229114337
    0x509040c0504021803030409140c03010308030c03090a050a0c05091021030e1512160801230307140a14090a0e1c020601061706010f050a020a17070201090e070c03 71
    0x1008003040e0100042c0c2680d01c1402002d82c7d88407969000d0250240000509034a80070140000003083c4103801820759060701d801c65502030540e520f501104000b40d10251050189119030440d15002888c10001e43c85c94602c152542c3e211a45020b05100e1081006050b061201035220b00038000c00740d000e080155078180c09601c003c1811403500b4242d6110220041442c3c10075054415001c0100120009001800c451920120b035503880c2000485408070b9021903800280280d00100102c401031a40d40f64240e807601243d15a0500882c0041d00e403c0d0154030141050304406000109480c0480424000b0080d161415a003419000c0010340788220003800210401c2d666a106075140800b000b1081e01d004140c0d035180501c000800c1c4c080d41c1d8460074818440040c40d0302d6041540c842101d10424001c0350306031070740c0d02c00341403403d001e0b189508050040c03405c40c8101c401c900086503400c44000080c0703602c8400d140d5500d0f62400010540700403904125209490340b0140010b50b640031350702d4004030740c05 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 229116834 1250 229115584 229115587
    0x1140306180a060302010f0203070506011a0f030a051f03030801090f02040b0c030d0f1a0d15060306090204050c04030c0b09030304030b0c0903160f0b280206040b010509040c050402 79
    0x14000094040c8500c001e1a8035820030070410469410160303401034096a000740ca6000e4920705101c000ca070341e171180c00001020f5400c0200100300e00700c540903255010b59080101e040c101061900004174030740048558000113510384040c0300100d40700352030115100d224408803520b00350a544000e030a440c018401c41c0b42603030340c811074a208241264162006000900c40859590000340c2c030340c0f5565040007608000e41450030071244001c80d86441040c090701e904d9010b44200081c04003c019400c0d420280c2a50703985d44405c08491140c030603206190186205000004019281e030040c84216000104600510b2408003c1840402e510602001c11512610b40c02590360b045000460b041d4021948020000f8445c0b1061044652442018100e003540540440303c0d103000303506020269125603c40c2d041507515200d010f02c8101c00031001071481d410b4481800250401c07000c1d0148903c1c1c020410007006812a206020420071111500c500500046415948034106230300c0314600046c051280d244036990 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 229118084 1250 229116834 229116841
    0x2090423070821040506041d060d0b060103020d0605300c031c021c030e010b04050105221d01020a09060801051008090a0c03050601060e0d080403140313060306090b040b011403 77
    0x140807013140d000c2d00c0b01801658071540c0d100303a18034000803103c078589100941100052694200043c1c4840c8903a0010480280c07625404c0041d8005e40c0700003030300d00042e62911804203d68a03601c000070214000000c0488082d200d214500303858007020080701d0101e812501200c41c5a84e000070761114034110850440303110103225042a4505a5507841c4414060161161860210f42690000c002c1149000023808001c210204200445030240034240d07004000301c0610240301b680c00d400c04081c1030200303000150f0f102c401310042030082a200032510b040e9000a00e20701c41d15031100c00030009001604180e44154106070001e20140c800500080c1000740850018034a60380401117040c0c1981c001c01040240c035142d04285071980e60034004c032004200c00c02d030f009220381040da209407001c80d00840e07058103140c195551030101040c282490011440305024030070050752021810700c002c190b15100017614500c0d0200060594110f5050310388190f180c8002108140d0f00a1484900303503035007a0b083d542d20398 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 229119334 1250 229118084 229118143
    0x2c060906070b010602070612140406050c0c01020301030803161706190b071103070b040f0e07020109380106020307122102030402031005090319020a020904230708 71
    0x8464000c2c00c91954400000756854000c6100425141d9035501c203065400382402980039147c2484125002144103800a0003180c0301d54422500154248815071410050051080c2039030004c2e0800c1d20345500001c01c1c444c0d1050317458001081001d00d42000c407850f01c00308490600c4910003c1249010740544800d07180b500743c504074180b001d0020307161815100e4906040c458040014401c03010702074440c0001c041802d0b40c0c47d0f030a8400f00c50519600c411031608100da00a2860380251031802551748402e00d000000e240c5400072010001c2c08044004d400303040c0c3c2c2c0c1c003600100307100b6201c118001069005105482d80841154005600311045000a00b01390b0340840d08558030f015088010b030405250b000401810f0f40044d401907000310212491018aa101c2c0012a00d0903680c000c2254001c01503000ca80180d901900074400603070042d00e40d00649a00404c3c4164012281115401044810803c8041a95004005550b1508000c000f8141010300c02903484c54101401e00c0360304203060b50b410411 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 229120584 1250 229119334 229119337
    0x902090f0a030b04140303100b090307080102070803040b0f130b0417030a090501050a02030705041707050402040b04030201020105070f021e0c12010e060703020a0c06091a01060509012c060906 84
    0x100001c1c2000e80030740e40e80e08040000c030f001a0707000c80709819420008040000c0010542e401012a41e00350509103141c41074044a542c40303d50842e401d805120b100061142c0c0a1020b0280c42d0f02030321415640e0720f85031034004000310004000c03050048103401807080c1c0b1794410340c590030a00d901003400740361500c80d41000c1004491101ca19800080004104888030b8000d03001401150320540082c003158031580f6941099010469100c40042c0050200708488600d0f0301034514802c400d1420b680c841a03c03103010509a9003e500030f0000c03038200280410440d60309100d180d42c0001a40380095503042d20200080d102e03500b40c2007240c0781024940700d010311140c00340045051040000c003000c00e003034603081d01740c0d010f05104080c0d080140195030000d001c06000b8000c03a000c186055503001500c0c030f1655108001016408415030302002c2d5080405161000d80d54494080d18890b21a03030344610150380010040f00603011400d240c0804505c200d4804d0b01c0c00354005c03e00b800216091511510700034080b807103d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 229121834 1250 229120584 229120609
    0xb010b1c0501170d08010e16090f0f150219020f031e060412050301060c061e020714120f0405090903070c030c0e0a0606021f02130608060a170304090209 67
    0xc107072505000207949103c1400c580c03440400807041d1203a44030343d600306a82c1c0620034840c031414821070ba1700143c580c03c980d2150004504040c10039441464a640a000d0070000c2078229554070b801c084020300a24154950300d00900b06107100614901da215860b2410f114000c0340c3c0240210a040c58441c3d00340e40600510902c1544408070305000e41416140765982c040c180c600b0780703001e4400c19290401d5880303101160f05030360460301c4100500d121585e9810003000c0000148030342e04806007840e001c10400340020005c2038002c4249440e05150b1203141e505003c4502c1da10b503034501003003284c040002c0222069404480e02150440a82e9680075030740c038151f1060300c10040c04540b90301d83c007000704517005c03c2c400240c6551600f1455a40d490610100403242607001c0c146c05a0305c070010038032203005005640f0600b9082500d015061402c000040750408400f5089040818800420010141007450b01d1800804401c080d208404284c800c3e80390b228802d5010f00005941c000803101042c1d00c40012400c0d2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 229123084 1250 229121834 229121887
    0xf07030f2f150f2710140c071503050f2401080402030c04060f080601060e01080a0509070e010803040501020f0a030806010507060605131a0a051e0a03080301150215040b010b 76
    0x94070600052030201c44d01044840c044000d03c031180400c45401c000804403001c0c6120348590500c00f00d60a1150115040f403180509180716050021030866682041900741100360703100403503503080c0903007907840391080144403054030262050120f8401c16058010000c160b820b003880b5120342c403603002007420310070650700ba00e411600300440021940c400000700c20413210b00384e0544017640d8982d48100e8004031070321741c024000341c446008580ca2031415400f541e04166a201164002a500c69500d40340720703003da00003a41604049000c10941d41c040c407036044a051440090030f50b1110507134028060503070240002d81004404035000c0d080061903840640582001000e122200c072200c5543d0025040b00360340e100106244511905d003a09000a204041c1d820041060030502001509110301d4044202180c0c1c0c040c21110340000810422001180a01a9a641781c80c1044091001900d060040d800e0250060812801c020100314540c99141c159110405225604d41451990010401581e441440c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 229124334 1250 229123084 229123087
    0x82a070804150e0a08121206011b0b09190c060e2101050720070509070c0b0a050601020c03030703080a0906021b010506090c18040e0f07030f2f150f 65
    0x169040d03008802d0000e405000c40d038902213039840780788042e1112040c07400d400710903074180412044030081d9007046600071010301d040200400003189410310030711070860a803410078802d424000342d041305006c0e40d0003070182c058540c103035107810740d50389074481015124420030409106440302156031000d80c0051b40810442d1003460542903c00e00c0341c000c003c155a1f078004103441010561454243c107800030300184005000e0201c161920303061050082e802480401005003141410f00000c655200d5980250464030740065140b406400191600003000c0d0318512070380c028048803002a81c4039180a500074032100c2c010039248100e283c400064002e0440c40b0355002001080240000d20560200380701d490104c6030f6550548401c49003585510980750a482c0f201c4420351319000b2410140c2269079910021b00403524006c4051121908229068001b1140c06020b920440c05012440c403040c00c182d030b0340300c1c0c00c0c110140ca194801070903101c00000303a5000b4a40c1440e100032603400701056404880403080c0c8039 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 229125584 1250 229124334 229124369
    0x20913140708010606090503150a0b060c0604060f0e030a0c020102120315010f030b0609040b0d12090801151d071106181e03030c030c0409110901082a070804 69
    0xc41d254405800b071032089601e48100080e103a403052446100312103024014100b03038650443d1001c07242d27200400c1848807584840d09040d16854400c01801c4040c130040190006040914201007038520308040489100d0600d80c80501507500030007107445202e03031804e0a81c168070b01440180c1c03c000e075030500711446001c04004c1180ba10b42020b00400d0741d1030260703070711044400d2403d826011075400801054004c002031006110070306259210b54030b2801e0040c0044015880c83c0d507181c2100d00900b50b0704c4009094104c0401841809024640c409007901180c2900325043c617540c1080348d40380e196440b510880c180c000c942040d0044080c201b41d210074400351031451620002c0074200b00700b0541030910a00ca51080d2241100d0503211401c0c5854504003d0f500d1615208840708060700060581040581c0070000010420041d03c40d41447d503110781105910b424046d400075008a900030800b80200080300c3c0e1650316000c1e01d405859600440c4800a6101c1da028140303146140a6a00003400890383c5140c035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 229126834 1250 229125584 229125623
    0x15110604080a030b0102071a090a0b130305060106030e0307020103020327012c060f0603070906080c040f020331020405010f090c112d060403031413020607020913 71
    0x14400c1550980f0107110019582e80120b0750b0302520b101d44114541c01c1e180c012000d0984000030480004020034250480b5154680001e540e44281e046101e0003a24403020020010103028060062049083c00c01c2144500e800f807076101d10072400d00034101a40040000c00e02c840803440000b80384510442d00c2e00c142445100740b802041071842291109454940780282e0b1400e02c1c0f5184003401001000e40f209454460392101c581a01030718007070f41400382200100304841107214604c000c000c200010864803004a003440225004007181d204180c4c010402c00204500010407010340c1808080400780310801c1181d40e400000100b1002944941007200025003a0250641001602c1e0500001c026812000c2415a601a4101c0c1e0307080054000c009001127502500c41291054a20b49110504a180d07150342e10b810801d04841c1100865580c040c4890b4440b0001e80803680a005d1420440640900750000359090040c03c038028854a0040300040001100c20001a507560f403041146100e801e05041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 229128084 1250 229126834 229126837
    0x304050a05010f0b1c1e0b100504090218180712020906030c0d0f02010333050a05011704080904060b0c1015170c060c0a03091d011511060408 62
    0x150360560030000c9000000030780b4410000080d0001781004035500c02503119240b401d001c5407054a43c1d03203440a03400420407a00c00c000c80341c50b02c5022441064a04101c0c140021112074010034000c62801030100c0058540066031600d1000c041404000b60b81c8040c00804141c10013520916180540c1d280020841640015404001e02c2215039020950700c41041c1655400350001203071340035850a8234880421b94207100700814500615010600f5815020311181c100895001555400000b0403200740f4462064400400380c14203e6801d40020318084c002070000d02152031461660780840e000c03504000e0754508941842c0300240c414000640e4411541d012030300a281c0d03904950040140601410b540351060b8200d2904131003000c04410706161403205806002c10042d0038a1040701e0001c1aaa42c1744000347c1904c1a0300ac0c0100f841c040c20f860010060919984008044001008100038150242e0f4a45046d680800601c1c030b55805051002c450555481d02c1001da24068602070000f440103070710 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 229129334 1250 229128084 229128103
    0x1201140a030203120a14031515070609030c0317070e040c0207170706140903100905100527010203160e061c02030a050906060120010605090907060311071203090314030405 75
    0x8070340c22410441c0301c505140511085410503507010742a14900340c08d21b030040210a90340404271a180c2400001d5550704c08942441005a000c511804035a80c00c040d1700c10000c41001c6044092010a401c00600140401c03c4096185102d00e8a9206101d00203108100c81c00050204c40c845c1e0890100440440340ca5100f640501400a140e80301e00301044c4d1203180443d803000d100500206540c00d85c100c02c02c801170804120441d15402040c12641000005000b00c50180c0c0071000080440d190451445046225881c062107060740140104102c07554000f208240d40c22140c00c20310b107040c2d03c40c4001a00c41c45290b141c2e5489088900000c1340c80411a07000d1845050140c5040002c0d4a401c64241c0e41c95400300e5036a0f00150a0501440316412216040f5607021344520001c50900d440b6800552064821039510700c00b988205020421150300d80204007003104001503403440d00103591101036120703a080680405140c2c40315808002c252050b20040e04180d020171403240c41c0d08146c030b401625403070180c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 229130584 1250 229129334 229129337
    0x1e10111002040f0e1b0a050a0504050d0309060f03090525030b0117100e0307020f190303170f100902030c0f0a030207060c0f0903020405090a0b04261201140a030203120a 74
    0x400015108503404130f02c5a403009003081700d90b0600300d82c1d20044886500100300601040002c6c0070001c0c0036140c210405480702c1c46512001256401d11360006c0c0040c000808810030141002002008030308049a040010103481111800015074407201070202d0070150303c010b00d080074110000850380d0001a140d008461500140e40c8000c2030b408907207060321031075001211560000c1180d28018070702400740e96150540a0080e4070184058001400340c24590350044e40400d00c0c8403503400c2c170b00b18a601526481103040b00200030034208460109207025841c01880000d5030b0000124901000b41002d54041c2c440c080001c5907900f10a141c0240a5000a00700326066070a01010084140c0560190800c0d140b40d41c1c0c0e920020f601d59003c120107000050800071240c024103201d43c02203204540e17194813035402003c2403000c0c0c20f80880e2800a501008030703840c500703040500c40d44084c520908045411140d00c0c0d110002004a914006011401c003644004c0d8544244505294850600400b0380b400d007540303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 229131834 1250 229130584 229130609
    0x616020c06041401030c021612030314071e0e09070c0312111e0c011a10020f19052b110c030a0803041707060b1e10111002040f 56
    0x1a801c0c085240583d0041a000d02d903c8180c400440d48a0b51040400500a20459035074000c4044811906030543c1c200880500c3e000211806041d05400743d458441c012205080c21440d0525008104072980c40d0140100e031000ea001d801c03200e2044c0070800404500902d505001d090445026240610803003084020a0680d0703580b0004c07001c284a01b070502c0f0b07c030704801c40c54034090f980e008042010580042070321174414051000c4140c024031584d006044070203c9681208404010032150600c401050b0085501528a8001580d03002c40d8001c410402c0303900b05841c440032441d2203030a140b054414070000300290204000d90f0107a4140e5847d00d020300e034680c0e444603520307441101d0303c0e50700282540d0740613881170200c10002501c000041d544503015010f2080c091a0a2842c0341e50f40d40b1070f1606580030b40d21a000303001c07145001f4000050000b44449003c424540300300200c0c4001182940034000d100320081e200c0c05929040c07180c92030048903004215511515020341c00c41e54660341c012600c0c449034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 229133084 1250 229131834 229131853
    0x10e180124080f0411030708070b03060a0e012102060d02070b1005030c0319170c03090301050f0708040213020d0f02030a060510090324020f072604060309080903061602 74
    0x18905440c0501c000c43c00610f640da840d0348030000c0402010b402540c15102d034920000d02c200062002c2009003144c0000300b50740342080001c000c501c0c005034101400b4990041d00401070b10842940082045400350702c0b40c0c101042c60700004005018071540c0428840c00054180100000240c45502c61881d46110b040417503200c60616a6070880040c48a0f010340c401ca188c034910446402c551100d0700d21915642d02c2141c02e85402001d60342080041c035200740d0011440e40307103502e02030080e2a402041804032019610b400e0100414080c0301a001038060300f0020720404002c03c0580403a10049908c40003071005064000b0100000c0d48105c0f0400d940c14941500400d444c584aa80c0c0c10030a1001d41d10f24401c141140c480c500021004006a64036550a40654061001c240054031840c208040b01c03a41750f2015041011000b1202460302110f0400c0295485408a8440554040e9030f81c43c0340009070007005207420812841122402d030b90500c205003c000c040d104091140f03c050803190f0a4920640 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 229134334 1250 229133084 229133087
    0x7020a080304120305030c070606030302060103060f110712020708010519050903040b0906030907030b0708090c150a12060e0c0a020f0c030a020d020f10020c03240105010e180124 78
    0x1503000307415a083c880300758003000c6071140020b10381013481d0180c802c0c681800d96440e842211101c0e44100c01503000507004109001e00d6204555403661600418030802c00c900c41d5502440c45203601c01020340f10410007070041241708000240103040c807400204101e04020742c0072a81c4808200d801c0f9020b03420840058240c102c0070068a045403100b48185003448115010001690001400c0e540544141c440000c045885540c0035400342d0440d0321407000a040a40c180c90034504400f0b4214000c608100c80600c99024410444209080c10300c0c1075040743c5003180500020700001e5001c004050425402c1c4000c2124000c01000415515000c5851280350704101700d807120500c20030306900da04800300180160a001d1101c502d0b40f440186070612100c0d2080001e200b00712007500315070050744940c144046a0070308001d021034550040880302c8014901040c4880000f0050084604020011598540755100c076440340d6610380c0505500110b941c6c50b001c11008031169000d83d03c14000d9155140902e55 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 229135584 1250 229134334 229134337
    0x51c030315061806020c060d11070f081c0506031f1503060b0420031504020702060a02060a0c0e0a0306021810120501060507111e030d02151e1305100203040807020a0803 74
    0x3480098161f906024401d40391100420b14410032020b40d260800c00c2200061000556151151050a059480301804c1c0e1040c112070014803e0742c03008a03d450148440c0d5176000886402c00340d40c0385100340300d948034058020f000d00b0000900001c5a80441008001c1000c1900b1400030200f003a0703030400800500052803801c40600c08664500c071501000030072851911450141d064520203032001d403070451aa40407035410340c0b101d801500140c01000502c841c0c444030340500c0001040e2894015084449480061200c448502c0000c00340c0746d001130b40c0c80c64290f8003001c488180788014440c0078210014040548105803121340212002d00d400d0012078018003860548140c3c9400080705034030001884140510b0203c030108900c0d00b01090314042c80b40e03603010850f01d807594015602404040103800d62401c43d200000e0204111a1800c01240203c0e1801d60511540701524080204244115041c802e0410312a210b000d1f403650300010400c17080c04504001401d040748261620703c51540d9400c10203869 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 229136690 1106 229135584 229135603
    0x20a0e09010e010b061605070506040305030304031215090b040b1c03021b0609010f09150503060306070f05030a090206040503070905070f09051c03031506180602 71
    0xa1140c02c0c003541c030b4030901d0359009114034158940003030000d005401c00b07043c01c0041d032034500e014000c04220480050001405940c4c2c1c03161241001912548110b034140c000c52000c0c044084400c00911401c20000c19820085807024240f00d0038001600c08000c000e540561034030300e2171505645409920310b81a9031000d00e0355001140c2d00d000303410b00d07040c0c403003002054540035000401500d40800301c582c1c00209107041c00c100c1000080544020340c050b0059402000d105140c00b141d250003c0003180100310803402c480c010b54900300c0440d0f0715480000c20000203a4140049200105580c10000d5510320051241e41026100c1012900d01000d580c0040f0110f03807118103205040750030040702ca2030559035180400b0b10a04100229113038002d20000c40b0260140d00c50502d050510a50040101410100c1e20b60401555401300921a01c00904202d0300e018a00d00300240b00350000500301e50 = true := by decide +kernel

theorem cover : BRFrame.Cov 228956834 229136690 := by
  have h0 := BRFrame.cov_init 228956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 228956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 228956834 ≤ n) (h2 : n < 229136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
