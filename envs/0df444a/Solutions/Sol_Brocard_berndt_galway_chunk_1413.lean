-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1413
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:51:47.279768+00:00
-- url     : https://prove2.me/submissions/590fa0d4-cfca-4602-8b9a-a73cf4d49932

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 253956834 ≤ n < 254136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 253958084 1250 253956834 253956851
    0xf011b0503030403031b0e041a27010e01031211010921020706030615030b0409060608031206030d051b070e0916050d050a0b0408070606030c0819020f0d03030f 70
    0x1001004510452081e035040c0540c5041003200712078140c40d0100000411341103401642941095404030700041c0d40b003120540109d1907000400d02c11074000b0802a201600c3c0650100c21404003150076006001584861840350716648840458002c0c00396030400b0001c8075107000e01010025003100007031a400c2250516021815200c9052901e04a43c1c41c1000d4000d042c40000e9503400380c4115002c48804030003508203820300c05000c400070b000c3c800004d40d00980e2400b0213800b080c10391199402418400c0001c5545042c841d00c000c0c0c580c440200060f100358080890030819551000581e03c843e007401460304d008140389881c550500080d42c00c1080c407070150500300003421b0b40000f1138030b000981074900c2000780b81e1a841803280600c0f0680014000e54072071980d00c400100500303c7c180d44039005425060500c2002d0740c82c101512210707401a034801c0084001441542002d00c4001c0142c040811101030f20360700c9034080b03480242e10072602d51080f0303100e482c14414980203030040d030340c90218203800304540c95 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 253959334 1250 253958084 253958093
    0x80a110f070201120506030712030201140a02120c0406141b0d0203091c020915010912060507080601030e0606041d0601090603120918200a09030b060607020f0f011b 72
    0x801c0454240d00140603201503c0e180b00b014400c0ba401a40058040d0000505192000040c2100340604404542d40c6440c00700034251850402409603584042c056640c0404c8000303641c40f001c000d080000920700800080161a4101500003520f940c038054164030b5082a0450400c0c1549a29443c5c02a00a00000541d00c65012004241c031140495040e00c4030107010909510042c040078000750000425008a01d0742451019440746003d014581003000603101d41581840c08400c1ea41140c120b922001400002500700c1d64180c1c1c052404e01c1d041200300541181d0b6566800058151030042d41e950031140c0022004c400600d040d8969801114880c1d40e489540320001c2815200c16100342c00c1001c880c88100d032103210980202c504c1c50310420303000c1240e1050710005107084061001c1d4110341500c880400400701c806408461643d8a40802403851420007207900301004000c24030581040000c40f0045e615141500b0302d14070305440700c85805400c4001620fa2100d880442070704041882e05040400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 253960584 1250 253959334 253959337
    0x203150402040e0a0f060b0a0f0807030606170a0b07032003010906090507050a0f021e1e030f0409321f031212060308030711071706010303080a110f 65
    0x160701c00c0c1c50420491241190007a201d8005900c01008020000711081c04510290852655601c000300f403592420b56403036580c1e56484030380c0d000000340c8d01300001c1002404070521070340b40104105281c0d8016180d030141096103070450040020110940c410104800521a900841180c03c00940038079010b0b103021f407000e0150300244100d0300c815041000c01701da40b00c418010240915119250303181000c22074801501d004c40c1d413010034004c51040e00c1100d50f0500345120540e0003114003801600103c02540e18003111000c801c203c0c0002984100010441e074201482260215520704800240c1c04e01b0140d8020400d400041c440d8094101c02c00034110b910b00714120b06802040d9865540700c60580d480492144058281f10241404865241092620b8003c041c07151102c0c0c1044000200c0795103079a40d030a40c9070010703a880780020300349400540326903030b0801290000c0d2002e40c1c072200c0114018070090355030b01c0050100504004d02c0401044403407080360003180100c401046402d4480036276500b150300700e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 253961834 1250 253960584 253960591
    0x10203010b1b01020909040f03020c03100b1c0302060c0904150b0c06010e0609040201030f02070b040303060f06180504241206050a0c080a0b0d02030601181b0203071e020315 76
    0x1092581e20b2000d81c0b100051003142d1580c180a850f03200350b81d803136803100c50091031880019004d41c02200301c0c0c0040b0340c0d414805a06c1505501030700117043d840600c1030041280341c40c00301d034621030314440428001c41d800258569000382c3c0106195a12301d2024040744c00b410b14a03400d2003041d8509117011480c40754404c0507280303124000080310034983e80e646404408400c10350f10345030482c0724000402c1c0994480d800c03402014080000162401d0090703075800c1141d00d001c0f9404e50019035074000c14881c0c4c4100c1451400203021038505003d10112000703407e03030004424452184200d50306c120782010040d1003030b081c0c12105900d076411502140e03030b40002080c02c035850004075072551030900001e5124100740b007000141e260715550442503584468151000340744048510b81c0c0200d0f5507003000f0069a003045000d028202010f0403642d40c00200c0780040c142d9034954414065006030f8002451610b03400403d5500d4aa000316001151000000048070307461005900a9090300454114926201444100303900 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 253963084 1250 253961834 253961857
    0x901091406071e0f03020d1107050d020f0c0f0f0a03020a030b06150c0a0f060b0d031106090105010e070e150406020a110a120609060204270612080f03040c08010203010b 74
    0x30903000d0b4007030100024415203d85010035809098514050310a501525405d10404000174050761071107a003100c9070b00909000c40309580044810b21496605024500e07600060340c0c02040c4c281c0d5080c001400700f401407015207016100d510545403240d660f00c4050401103070090401002c60b62203041c8900314510440e602801900d505030b0b10001180c5610132107a4040b84900030f008a405ca43d500d00310307811080142070360016142c0b00032200e40d6940030307212080719200352654900603220b580c00a08044000b0140305050b40740c90300412507014048141e40c2d01110602d4071074583c0d41c6003c00a445107c2c08800042c003504040b80c00710b40c15800049407035820f8052140ca9011030031030780c00c0216801c0c040c06010341810340b00035007000060301a08440b800a103d06e1025003019240d14011103241d03004042c1441b003044d9a00211074400c030b944202400350065003e9012040c100341c0f80d8401c90f2091104001c000c040010000302809040d102800c05032030b03980300a65aa50b9211000d06164102c040c1050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 253964334 1250 253963084 253963097
    0xc07030b07020d0206131208060d0624050405010f0605070615030b1510090603022512110a020609060c0f160923060d031803061d010506010c0209090109140607 70
    0xd1360f2255186c482c3c5441540702c01d1005181c003040038100c0c0d81180180c0103c1d04400c00c01d801030000b0f40c040c020036a4169000203803d4254611054454910400d58001341c000c1c0c1c54100148900d0034003410301030a442240c201580c0e5110540340c044020301040044c8804070b1005c100c04400c105294203030380d0050984d0041d41c021112040c08202c1c0c00d407680c01c0200c01007070829808004582c040d8025285043c102c840c040000859007080b00450b80d80582c0480d0104d0f44404201c0b02c1c41c0d005000c980e98074248100500610b190742e0302140881c802e0304d841c0345c86240f012034902500c1008101001c6012440e405070780c1441041050002c8241050180315409810224138074149103552260701c42102c0c0340000411207481c0c0c0d50034490200c0b8601000d40030000c021075180709881000030510000d6220307080014030f0130300050b18408100d1110380c502900744d042505002c030744e80c0e100b0b0b41d0016140e0122070000280d21030340d4540340104504000240008100041155081804941c6904c0b031301c41354450700c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 253965584 1250 253964334 253964341
    0x3070201090501110c01270e070329010302030402040204240e010f0914030708030f04031104060b03040605090c03010c030b040c090305100e160803090a09051b0c07030b07020d0206 79
    0x545141c102c8101200ca2035008680b02c000310343c426a40d03d844580356042c10080e0008807100300d10747c00070300d8001401512000e002c0c440950b5261042c04840e11540a01807000280038200400c06c0780321103220740c10103130040049010b5507120342c126001014900c1c0d90168203103109100f03e507620055026071005c40c0d100580c10100d540181c00d8101d031090076540b210034039410700103902d6048034080c1c00e07280c05120f62000450b15480c100003c022583c500030f00c058543d885c0d4a8801d0207950b09050481c011030804031300704090b5070340d40266500958000d5002c070f45995003c0040345000d404c00354142d4190300700740c850b11426070140e022b145080d0741960103010211681c80191500a02440001c181c0d0340580c10700c00208043d94003241413004000141c40310001e42c078085003403a4881d030308042e4558100142c002564540840800001c00c1c045505000c103241c88411131511512203800940750f4400081d07a0004144203012079800385174425840c0d0901d04007072100958440842040102602c61280070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 253966834 1250 253965584 253965587
    0x20907030e070b3f060d0b010504020a030f020307030603230d08073515090705070c121407061b03050a1709060712020301030503090f01180803070201090501 69
    0x18036015203100d0303000300344162401e0344140c4958804000381c1000c100181c00684000d0000440708001d002c1c070013000302e00d40709034a010392440f50b020340418800c82c0c561595100141d684481c00741122401c607401600c1d8802c00c00203138058101d060b02800b1052000080004554165010200380c900480e150721801c2ca102c00b1a01d06410300d0400b480c01544040400d0301c001c0e1181d40b440f40d00100c28540540c0c075a44110b02085401500c108011a241501e41d0000e085220b01c41e0103603005407011200d6510458100c04505a204007a01800c104000050300d0810b00108000c80c1006208900e0100d18020300c40c10000b0014400007807860050240c01c0000804034442c3c019001e224415840c1400701c0c14031f55800750342c507178488030b59401400180c0b00184240501c00320894460040403014082c249002c64004180d10401410380c80c65501c10700051011440000c181c40f01e000b41a901c110b01002c02100684024840f0302c211300101c1c0309543c000c54000800300107040c42c903200b83c0300c402c0d04070340740d900 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 253968084 1250 253966834 253966841
    0x22b0c0f1505130317120a050f0906101e0305070e06032a01050d06050306090a060c11150a0b06070309050307050603011d0a0f020a0306050a0b031e191802090703 71
    0x282c02c20443da0107682400403840c00c00782d1040c030781d1220190500c3c05502000000c2580811201c0500140d5641e041000f561031482a00e0752010121025200761302c0c2400702c01716200814051041d24014a10750114000c10031000700c1c005e590040c0459000d5580c0f1802441522021035145000b030260707082d020005e0021000c03c6070740740d000d03440c1c0f10840600390004585a801812882e0031076500d81c0300004031902d06106d4035008030794210142145d51414141401900d610098440401040b81488402440c0100300001e2208080d410900551030350202c0e440600000300c0b1050384000d0024520301096008401d030360440780706405840d4070b41c1e541c408110881c0402d1180e2541c003c88241881c08065044440030f5001501c40d00c006200341e07140c107081007240c1101841c240820b0750394106000f546000362041c0700600300176030980d24500e001255100b40c04207441414201e48102d8000c50711034450307400300c0d121040075482c0811421206080840728000c414005034020410a8045a0824420300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 253969334 1250 253968084 253968097
    0x51f020310120609020405090a0317090d1b06050702030703020f0102030606031501170a0603060e01020304080f1810030f05060904050304050112060314030301180504022b0c0f1505 79
    0x9015565072440e00e40408409020068111212075840498800683d2540300705400380c042840107000e400c1061401600e40c00c2c0d107127004001c0c02410010405010400601d042c8000c0303a5280c960310040341c80d20402c1751445000d000030509801c05040014555000002d0040b06004c1d9085030820007020035214200c1c401038421a4015a0400015005440001e144000413006141c100511500c0720340d01400c201d02600d0422007162100800c0061140078001d800e80742d10310030021441c45c00c044c0e580d00624444e15601102c1c0d4403010030b02440520404c58075009280c40030340040c540c5660804010b0043c12451007414449243c600030950a042ca071000314800d40e4030800451429040c43c0040d940d110150075008045612140b0100015040d042152060355030b807002162a0350504001d210300c0310a480850b40034602d0b00c4108005030b500c0c50714085015141e2030040c2484021450482640800e03804040e00c034040b08580047c801e0ba04450850458201d183c8000604a0005044649100d5031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 253970584 1250 253969334 253969351
    0x61f02060711030c0607050307020c0102070b07031103040306090b07030608010c0e0103110f0711011b170310090509070e070f12050c0c07080106091a0603150102100603051f0203 78
    0x82000422060151010002d0a800c980c1200d040900d001422490310b00100c0d0715100154000c000c0c454419010040c07282c42c00802d00103003000604041c08104a4042c110000e42000090142c0382c140720018000c89001d036400c554140503880981c204001072004c284e070700d100028038003100016150304c18418194544056a1b0b00c5a400b180c5000460240002003920011428201700a01d01040800004c16a10707100b00043e0f104a54160000b4000b5040e01c525003002c1c1003558030010000e0114900142e0300c440ea1100c035501e80d10ba070285959400c006401111600d460070b000c0c03200e90000000c0103001c8072211481c0080c290b4a00d0400c80c2c1d05001c04a541d8081040e0540d8407030076100e2504441d42c00603040480c60b040400c1c5241700740c0340c44441d52010382d1596441805000c0344900d03010701070151005d4030214060040000100301e080c40300400403008405d81501d1592568400c3c0320075240b07a004d41005000a544034241303580c40d0004c40c080c8072201083c040300142e0030710a5000766072051100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 253971834 1250 253970584 253970593
    0x180204050f010e060d0608070305010e0303010b16030c0803040311070602120d02071728051c020a120e150f0609040b040312090803070e0a0b030c1b010f0203061f02 72
    0x9400152001d03c1e4000e1920390149050180300a110010320420005101600c024818180780d400c00600f186c00826551055420400c01030240341036520071a0140b204d0b000c0707900f03600d00082c20f04440d49000c404006003405000010f12040c9580a048285045134803015103004558030f52003030380d0b680d82c2d0541114401c60103008000c07800081d54050804035003c0c02c0b07922071480c01c941c054441540503060041c2078070f00d00c680801d0000f1810140089003c1d49040103881d0000c618081303d00c03020b28035100c03080c582e000107901841d80e1050300e810b241412020310610111860301001a200c5585000c042e4201e1602000101d440310040d0615000d802c01420545454890707403103080405070006c100b54140002d12240d11600c2c1007900c17891003114003e0b40350644905007508010100f001c00c40003284074401a0720244002141c0c01c00301e0383c01480c05c40c0b0740756690360b0600f0303070b5840d08929290744d807025440c01001c140c44c80c015400840c031400003241d0071030b0452410f20100c0c00d142c0c1c1d14201000142e10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 253973084 1250 253971834 253971859
    0x90b0c1c0504050d11100615020d02010606020c04050a180309150302041d1008060408030a0b0904050d0f11031207170c03060d0303020f03070315050d05060f1005100918020405 77
    0x491120075404014810381d4401407005a0709020341e403d95000e1066101d802235641c44c403d0303040c041c0d030203040700e1480280200c501c2c010009503102184d00d081c87c440c07651407022440e1881240d00000c44ca0440c0b85e0142d103000f10600b17014000052900c150502013200d0301c40d141c0503910900c00c170303400c1c1e47e0030100101600c1c0030007080070a5140000c00d144201a401840410050000c001680c46070348140c101507078030700e407403c243c000380c0304001c002a008403021130074000050000710700b40410032440e02d0446292500f882084418601c54520310b03100c0d002c0000c40c1a000c0c05088201842411251150006075103c82d1f41944a02d04c1115014015081800842c110740f8051081c14004ca000f4500541040e03414000b41800741d00544900303000c02e40e104040d201c1400700b1810407004100c00c44110354608a42d803205510780c5002003c1940803141940007660502580c00244c015002c040c0c190301c118101ea1101038980050750080142c00403141c05110701c0700e40e8074001c4a0a89602400c02d00042d00d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 253974334 1250 253973084 253973087
    0x405090a020901050c12040807170303040f331107020a12020a21030807030b10200105090f070f030305040905060d0204050a0b1c03090302090a090b0c1c0504050d 71
    0x1005a4400c0341082030400c071030050b11000f000b003d00ca080341001421f40c0c55140c2220701c1c0c0ba00704103522401658500c011242c403a1035001c01030743e48c000e40040006109404034034000e40d07402c149043c615825009001849800c4003122140045a489448200102e100e5021810824016941c2c004e500040c0840244401101102c0700c0403030910103002c0148580c1c5540c0c000112003d0032140800c001151159001070640c000580f9401203014103041082d00303441c1d404207444491501c0320106202012003801440c94034540c004c881d01410790000c000d82d04000c08100c0e00c400452804401c80d2081a10105800f4000400d1000722503258031080e103014507258038030001d4040103107480e600a546c14032042c0542c0b0b036401900d101c0c04070410000342c4450154200304403401060710300b041c070000800c10000002d40000c20343d02502d40403180b071900c40d681c048407500500b044010003011144103405014094402d03c0c0074012515003e203000d44402c02c0309000d1001c641302210301411139400b00b500000342c607 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 253975584 1250 253974334 253974337
    0xe0a110d0302010b2d01090e31050f0d091805060d0219080118080301170f01140411060717030a0605150a08160804021c0b1008120405090a02 62
    0x580709000205005240b08001101c0f41c140c01c4103040c0403034a019031880800642c26800e0b000907401d0030500c10007424403c1d0780c400070314000e06200000c105c500804504a1991840a03901783ea016200e1200c1c2040b40341c0070b6200c507212200000684141400c0750209c1c2c1c007072690003041d0b0346881840281e10100c150524040c1101608450308080c6541208000da101d400341030b81ea14401c0300003014001c1c5401c509d41d084401c00b003040c80300c00003070347d121a000075926070841e0f0444a032101d141c0f0349400002c00c110b0906480d4070483d8002d600c3c10b190407441c0340c060000148603a0143c00d07101c03030038000f041c10311404e4811420300808001030380008115a080c403801968000c054118005081c58032900480c600620309001c0711120200071440e010455480b81c041a400b07040226a51447e42e0039200c003074108070000d40001e10424640541c07071607260391158030700c3c4101d8018043c6140d40c148005086441c1800e8020b883c00e6005180c079486110489800316000c50314041d20b0a4447d5817195101d8009 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 253976834 1250 253975584 253975609
    0x10e040b041115070b07080106020d02030412031704060504021003020708092e0302030108070824130b04080307080f010617041505100f060311090f0a030503031303030e0a11 76
    0x151000e1940d1078002c1c03102c0c00340481500c180c0a13100740f4100a20301610641051f171027241107502020301420220b90100595040f02c900e50071178084c4207210728050383c2011441f102051109200b000b00801d00c202a04424011802541c200c00c1210301010210203911414201600d090000c014100aa050481000044030820300944c0e17906c10400d001001244011010400000c0e0007200500160005000d00c00c000c201c5900188602d02408207210034500d04050601000d0038020300103501800010381c409521503000910b62124031f8185400c5005401c01d490a1001403c1e000008800d2014030201e20306a80b266140c501c1d21801e921256001c4440050040300c04071030310039003c004403c6900649001e001c80b07030a444ca4003400c0a21400c10700300c05a00c050101810031350140e0201d00034408507920308000fa1608228112910049080c070003c84d4002132041c800042000a074130b5000d5884240305120307035001c1c48068000400d040d038078001d502c0080e140b804110b80e800603074503008204110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 253978084 1250 253976834 253976839
    0x403030905031b120c0301020a02010606020105091507050310050409080403060c0809030f071b1412070e07030b031f0533190e0c03060a0e100603020c031c06080105010e040b0411 78
    0x42c48000b4006c40d09982010102c3e90151391920b00c1445841d40a000b016804025000146403104a0000c0d500c099500540f01c0400e000002021400d490010a080f42c003801c00907006000b0000c00d86400c0101d03a1140c841640c500f407510076401d0360745110724180c5000f40d5000c001507040c07100712407140c5d240d42d01203007040740c010a03000e0b042480300d031141c51603100a011402204404e01400010320801c2d00f00e1811158440c0c0003640c0600c1105480d51109070000b00925002400310100004240760034505031100d60304c1c24404040d40001c03000341e0003207032140301c04100d0314a110080020014001e10303201c1c08032480f00c48a18030580b8501f42400781c110100321300505107100340e6868414040280e0155036280c031404000007000041d04004040d140140303400805140c0516058000080762403450280d03000305500001c048110090400a556010325030381c080545020280c540d682c000c080c24400c86019509003000040c03104021050300c0c2c811900106e200300c0c141d440d07075180100031300d00c401c580c1d5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 253979334 1250 253978084 253978093
    0x312010f06051905161a04060b0105030c0d050714070606050f06040b0409111b030403020f10021f1d0c12060402010807030902030a0c060f0816051e0c0607050403030905031b12 77
    0x30215186d03079644400e650882a01382014205420070030169003551000a061010400a0241c80c0119000720350300d21014900000e12034585100488250188043d650302a01b0082102d45c24050a5403044044440465404500412002c04d000d440d02841c8174202c03008000f804100b03e100c3c03154100141018100c0c0c030041c6007a01030388000506401b41400d81d0300560012030b040c011401d08001c0782400c000f048801c682242d4070014000d50b15090b200c044000c0c11010704814580b0708842d00030081600c1c0f64243c21041d106007a008555803c000c0304014401c0454040342508580d011445501a0341c0694860089680300075068000d04812003007280c0501c1140c0307080c07011034424803810f0007410150b45d0741a80f56900510083c0003035030240050780c0841d02c0083ca0503506410008030b4542c5040203000100074803655038821a64010318004101c1402808200400d55500c207000b40b0682c0d100b510303821025601d442c01d06a84c1e400509009140346103105a042a030700d4208000382c80c103c40c110440c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 253980584 1250 253979334 253979377
    0x50a08101203020609060109050115030917030a0b090112030212030714070602180414160504120308011502010608070b0c010b040903260906060f120312010f06051905 73
    0x1e081500c000d1000b5001a00a07006005244c0c1d41031041d14010815484180321075410042c001445a25181d0005c082c07541e83c6608070104080c003840511850001c000e040d440341381024407031001d41aa0841c0034805c00114001042c0d00301d1207407060719210340603070050010601c47e00300c0118680c409010306081c040d5003460700c400300d90680001e0820034862f881c0503031943d103090068901c00704000c2500703219074180000d071240c0d0421599295445940704c2e8a00395207041181059686106d260010404808030380b5003d010306820214490407100c410140702c060b9896408201d017200c1d0309000d6401160040641002410841000307070002c0405940002000c00501c000038040b9000402d007107011030440c2d40c441400b0040c0710400000c110b0b10240701691854803030b800c1915000c0c02800b0f548111420100f03414940c690100700d0920084a50440c1d60b6502d10000c80e031006002440341ca603409143c60300108009104005172001c04150103d42d45031010060340c140d5080d0458044554150580c9014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 253981834 1250 253980584 253980599
    0xe060f07030504061103070506060f04110f18100906051326010b06040308030c0c0a050601060309051905060601080a020d060609031e03050706050703020714031801090501050a0810 79
    0x1080325510a44072169518a0f08a0243c41c61000380e21788070940d0010f10004020400c01f14440c1d910002c119601c1c804031404e003000070010143d0b482e041d20106008101046418828001070042c1440300601040c516140e0003008000380e5203580b4007002841d01401006000d01030b4010744600c04c0c100d00b500e030000d9201c10300b0800d807022034101040c40c4d03251031400c4400d4541c03e100d0b5814044080d43c2c4180b0301411501c8555040c40702400e940c809050009803060845424421030b481c0c103500ca41aa40c05507980c1800034007038043c1050648480c02100181c010107483d010b5900c1c1c820781d00c0009400c0c035568600054500031401812440615000c00c04100b1030300c00c0e1300c6110003404454540c00034290550507c580d1101e08404d680c52408038061440d03002c81c1e000816625525030103580442c0ba40c1d0741000440c0079000d216030080188141d0400958510030120152480e50f0300c030700001c0d8501b0b903c540115144d040c0c0e441120301152040041c28000c0b4810300c11603a1101102c0364000e03089544181 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 253983084 1250 253981834 253981837
    0x12030f2d0e01090b090d0804030501150f0905151221120a18080c07030c141002060609150315040506070801080606060f0d180b01090b030a050d0e060f 66
    0x1120341080038481008020940100700321034074420a1805a400300d0a06004c040e2610903501a14854140111018200720194040710055503000e80240064a01318110340383d104028080c404c05800d02c2e0307002140b1204503205103485403a015013095641c0c19040c05001990780d00c40c80165040c002c059400340d900c000700c032003d19480a410311b195a0361340c0206101c5528a03020302516883d6007000580c0300d03a0f021403c0b05017012508a480c0c50b650301c030040503903071030078036540d00041100702d58030700c006a1420001112505280142c881107000e14118008980360501240d50b141d000546030b012884602d0070b51204d01a01a01034100c500314248004034030110101280d0482c1d05a200c0c20820034010b51080015005080303200c002d088500303001c00040d003e8001c049888101400110307060358050380c5608404001d40ea402000411510070707040c86026000c090080a10150806405840b18280000c107c403980350800060920002d103100d048a00c208000351030355000005111a4146850381d10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 253984334 1250 253983084 253983137
    0xe0f090c0c12040602150112020603060315072303040302070e1005040207080c011404050a0b100e07030e190b010306090602190201050703060b0405130e070b040303051804050112030f 80
    0x28407686540c90700300006c1ca000708034011209411030080041004055070b408081d041d40e41242c4054a03a034690001c68503055803080141d822000d00421301101d00d4101d49246034105840d001252013100b032881c602007900c0152001401640b10780410010350304c4800006402001c0400310704452aa60300014040c0d03000004160303410100001c214a0818003403103031003082d42c0c0c41c402c00f800c0d526007622816241d00a405002c0e00170014800010440032109000c240900414410b0444905060500400500c205c182d40383d6240300701b480c50890210700c011808003642d8400790300c075001e0307085980e00005003005c0c040485056409121050840104264907080140c05600006091a000400500b51404c4e540300d20400e2104000070f11058803110340c49807480c02015804107020401003080307840c0074599846820a684c0c0810007004161b070100c002c29402542d03050419006201a041200301c0728203124603903808070021080d4000078054503d44a600d1a2030504e224a82800e8004614407820769 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 253985584 1250 253984334 253984363
    0x70e03010212251209080409110901080705030114010302091203030c070c090203060f09040c150c1b060c0f150501090c030f09030906030e0c10020d0f0e0f090c0c 71
    0x400030080d02c0d021140d02d0450100c03540c20103000c4203502010162000040c014032444203920350482e4424031243c0350441f402441400d60400c03c140b06000d600d640d030f40110080c1d50000340800045a03d0300e20ad8004e480c103840c40c0049000d406050100190000c1d402041d110b40c0040100c0c0103040381c4001840510b120308552460709035203c00d5482c0080e555501c5400480a541c414030900010761603007905402d80d19020303900072281c3d49640c18482c10f2413031140d200d0716024980c586000d40d51584060309644403031141d04040d00c4042c0341c00c540b24200788103010705030020f000c00e640032000c1400e2108009405000308405071828100c2c203141000d499090b0041c19009490b41c43d040c1c0b420f68144541c1100d01d400c0c007420086551196001071400c002e91260404142e183d600c80b2440040901c0300ca4070424009006c01894100729030069100c4440d081e0200c081070120401c10804c601402c0c14080f1043c00030540f01d0581c000343c041150700d01c000343c980e241c440410302409040c1c05042100340c030840e008 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 253986834 1250 253985584 253985617
    0x33518070905070e010f0306140d05031c1a04060509161202162d060e0f0a0b0403030608061306020d0b03030d06050406170304180b0616030f0f0806010305070e030102 73
    0x54005040301c14407010200801d494403208020101107040f078001089c10484000c4d00c01350450906a02d540100d110070301e806842d031032001c0f5011003950310003c1700b448a2425040844040c40400c41220941d20415420003014000101844240e400c00100f1911905140d2510322040780305e801260801000f003107402c1e4030100908180580d00a02d0905405030400b500003450704108090011380c00800000c1280317407203e0070380222517010702c15503064401200803123050071040d040ca40c0c0c04200507242500070030b2403c100804c2c00ba4010404034030541a0244c03080324044a40d41d544003e43c0b1041e031040341d250707450110380010381e818801000d031071034411000300e9000c2c10f06d02008203ca0107640001c5946d20100c00560407618040141c40848107992a002030f00e0003080640006805540000c5610210000c0c626100c1c80c841030440b50014025515411401042a029503c400081c12200c0204007428009036140d1301c80c3c4c01643e8848914540360070300e6501040441d0a80c0c010414450350b1900 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 253988084 1250 253986834 253986857
    0x7051e0307051606020d0f12020d1d0a170c070302100c1101081003080c0304090912090b07030c110a0b1b0c0604060806060310050d03351807090507 65
    0x404012051850705443d8071666950302d42100a17603903004212890303040c40040410070380c0d201e01800f00701d014061010406e660b14500c2c010314000518041ca0080750300400b0103101581c0040010322480f029600c0403c201c0c0b2120b41045500c41508040b00310942c2e4442c1410100041c1c41e840703c070701c2440c0615150074000862034640054510150400d15040010b41800c0001040c01070341d0301004c903500100c040d0b03643c1082012007070541c8030302d0700705410460804c4c1c0d60310100590703066140a114510703680c81c6441c80d142c0118620750b218120000d13001030b00030103a19000c1758011203a4940420001d020910b00ca40e036003941038044d00030180621280c3c00203140c3c005401c500b070111231540403013190990b01c0d007420300d40c01511040340984982c0c0074110200c006103c80610101d03140241078000c1c101c10842c1d809280040c00c0000507007250341d042108501003210b01c5001040c0440c00c0000204601c00e9035585800351002880202d140c030464410340c80c000496040c0d030310500e03004100a0ba2202c0804c80b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 253989334 1250 253988084 253988093
    0x60b0a14210f09010b100c031101090f02032a1210091209060509090106111207080a1715040c02120c0105090705030a0c051509031005060f0a0e060607051e0307 70
    0x402c001e2800003da414070707000d50165680d4070745054003d0b00c1307402c1202506001d41002c584503441d03038090700a80d40c0307860030810a10107000c05000c81c683c400c0b0100c03200d02d140d0300d00c440005c521184503d086024081881241485c001c400160b1a6103c00300b02e40e00441c25808407410380e182410142d54980d100498460300942c880e0103100640080c1c03c3c5580340107980c1000c505d10f60780500c01c80c0104106402d626602c5c060a00220101c002c2441c0ca60342c4500c00d500700700f00141d00a1140d0004201901c0c2403014181b15018800c6c072a1032501e071103c018801100920000e4000714500008600070020164298140080035003c00c808100c000181407900c261214a07180b00742d0055841703548000b40c01070001d030000108a060b43e405658030400d0070a1401503110764010b03500794030b41c54003035041490f103c40d42c83e034005880340c1b0003100c024442801d01014070440320140c2c06001c0d0002c0c14940012540c0c14140000c1045520545c12601501c0300800399801441c0c126100300d03442d800c00142d000a00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 253990584 1250 253989334 253989361
    0x1a010f09090201021009171225020a060903090513050103020405010b09060307230f0c01051506072006030f070206150d02010c030c0512091201060b0a1421 68
    0x40c082403a04008000c902d0300040d5440c44034440404542e9101c111110400021601c40962003910055458031100e14200500740c070301c02155112400507484c01e440ba074400001042c50315001440d0043d140034404d42e2524006032020900a405000c0c041780002565100c0d0004518050250300c000122541184100420740d8010b03032022142c071a09108940ca03035507e41040705d42050b51401c2c440309207e00200f01c04460ba2070721060221079103012440d10402400400240304010800e40204015a1030000b0401010f42001d1459000007040c800200060040080c411034800305000030401001c08000140003a4021203a0340709002c403000510581580400c11190088000215003000d90031000c003203080403041d0302019041000e403512650074180900964000640c001096404032000c0041b484801e9201203c1e4a00030040e00d0301052440c0c0040c4140300c00e4955a050092034032584603021601310a02006102c4480002c101c2d03141d03502c4287d1041e05c00c40e007044500c07072603503d4013a400d040710 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 253991834 1250 253990584 253990589
    0x70e13021209030301030206040b0c0c0d11091305071404022203031d03150402130f060f0501030509072714070801090902031507090317030907080d02030715091a010f 73
    0x740e6005000500050360342c2410345041e0b984000c91030380c2f0ad800d681c08040c9006501020907030404c1c42e49240000344918452a84d078a031800303598103c9613460710700503003038000c2002801800c290040c3c1002e001e50f141030350740b04c66403002c0140003604000f00c883c84252401004541811329503481d0004200301500019580d18142c40300005400700304641011a440381c0c09980720b41903e4080000103400c664500029030f21004407008200200d450f4941e120004042134041c10407124114038000480303600c00c7c017541d44503140000181c075100d460f15086031079820707081c441104900d5400d48903658060079072040460100f00851041898140450301810022040e00702c1ea42041c1000307180310143c3c5001542c040d18881c040c0d10102c0c030ba81e4083c401c07030b40b103082900010040e000c010908203001a80c0405940104201c8040e04d54507603450866580e100e001c43e10741d42c00b58105008000c00f25061a1000021108511000c50390000540c1e8040c003a102480104850300841c100500034681144800400b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 253993084 1250 253991834 253991851
    0xc0501020304081b04020f0d0b041b0c0f0203120706060f09020f1e0c030408010906050f010e0c0306130e030a021006120602090a1505030a05060414040803070e130212 73
    0x546400c21640f01e85540e10841c0c2441c40c691582241c0510b42c54642c11074002e034001005d00e83e154242c8135151406043d120340c880380302d503041c0000040c1c080d005c05251400d07000301d510303000c10f4602c0c01d58034800c051080d030720145d0389405010318031141c0c1d0562600602c1c0381445a0000601d581c204158000600d00036040100c1c2e462041c0043d40341840c03c002100c1510040640d8440442e074408403220580c82010b180204a01004c0b60004100e50150040304546120304414000d658400c80c120301162000d110391881d009083c0003040101c240d020017543c100d80081c1601118108058441c000d07031b0801480300481d60720000740d0f581d95990620181c40d024035241800d0000a29121110b0480c10340082e01901155000950405a50b01c0c10314601c0144400b481948503809a1900988903400c02c0b51034003070107400c00c0c000404034a014414400c048550801a6215032220f40302c0141581000307000304207020030204004d21950322003100390001c241006002d40d95a0f0302c0c101c41908440098509075 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 253994334 1250 253993084 253993087
    0x50712050909150f100c1e0804061110090c0305060f04081c02071a060901091407050a030f1e0f02090603010512030d0c08041a150f12070803070c05010203 68
    0x1c559a42c010b9000e0700311005591500c0000c26420008014805028429920050b0320052482d01d580210000d00c11501408401ca0a5042e124003110301c0e80c02c0450042c9098410441481020701401d098454900600c04031042810020030080c101c0d40901d00a54450820301010001c02c241000300340d510031003150b00d03130455003890b035617001050050040e06c000c882c001c0002049962102e5065447c080d40140c4001c80307001c00c91081c0c02541d0001c0d9001c0d030258003000b002040b407e00c5406810005481d001d029030a550700d203c1c0440320303604207480e11001c040e20340301081540100c130f000307500544030b13201141040c0c0c9610030152000c0780e60030b941046510340180040c5105640341400d40341140c006070384045070040304459290440c400c0740d400c0c4500516140c06880300980c08580c55109502c9190910150b15000071428442003003201c112030400707404075081900342404090303c0021900944609414150328041606025054026850540c00130511174107003c020b032900d000800c020b00166 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 253995584 1250 253994334 253994347
    0x6110c10050c09090109020a08071701060e0f0904120f020c030c13140c0301060e0a1202011206090905060a0b010c0c12051006140405010e1e0901091205071205 70
    0x25200c41000040d921515940c0002a580c00c208a0403500c109800400c00502c541e141e0031401c0c02074102c80c1c10040016011000245680d01542904410b100d1111380c40340b1a0b8a00102214140344030031840e81c1151030200f071541d0380c0c0c550611041c0034500c81c1c1c10300e800441c0000e00080981c050715040d58119131000d8540b81c21601c0201d004d417144001505c81e2205030800c0e208907030140180d540304075104035208040001001c04003018505a411580c0d640c40504140003c00030a1000b0340604006a00315014180056000380e0782e08602019402010900d00d80e648906022107403884025141c23500288104010610644210005031409003003242c030180f000c1c1c61701c4503480006c1c003030755410748403180c40d00040c840100316404401415403800d101440e290203c2403c42080b40500d0760199080000110390078a400303c000c1d2191441c0c2c864400d40c040c62006c244d4010802903e044169503807903200c47c1c04546044034000b550110361300d4082d074401191800703c0c003030091a21018104002405030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 253996834 1250 253995584 253995607
    0x20102010b0a0b0d1a0303270109060516050c1216051503040f030207050306100e090f1f020f040e01051512040b0a1404063e030702280611 61
    0x2c4e01c958081c020300c009000e6400d10301c03404041c1c0d00c418409606100c04075178010014451203100000251900600c2c400c120400015205c4411600034000800c07000d01404284c01c4042d0081c2c0000c1d03014104541900900d030340480c182e40302c0c1c040c2840c41d940020b88150300608540d110b401c024601031b10280400300b4401c418400d107000260000705445921034040003072610070042c80c405804010180c41d20b50912080c41c006060452181ea1580000c0d0000100301102c00706031120fa40c24040040c0040e01804456914204e0881c03104880c03503070b03084c030048440181080c0a000513040032100c94155505260800442035443c84212228860402003445424030346541c2640007544900072400700e4580c800c1500203005090f03032a91110345910100400d010300360300490305c9000b028140300129141c3c00000e51590310143c1e2102001140c8403600b41e01c0500d40c2c002103901a5152042c0c2e9040d400c480075100265144070344010528a001700070300f083c4201480381088202e00d0050052030000050807 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 253998084 1250 253996834 253996837
    0x703180209130201090e010608060405090c0904080307030e01060f0302041d0c010302030a060e0f0a061a1605191511030411040c20030408060c040b04090b040207020d030c020102010b0a0b 82
    0x100b00070b00380e803800b03103482164042c84458000d0400810300709400d68450310001d04400045445038450f500b003178040b680c2010082034a003044c030070180803110541e803203444201580e80302900d08000c05988400034a1002800e1040c10060250540c0040f0054510300400c029076032071050f6811140c038550701848402d1000a10504800400c3c01c01507103a03901d1420341002010980d00c00c0305111400c0e01000742901c141740c8010f108003c0f001d0100320041c0c42e464072544840191020001c6039504108a1b050b50110128104103d8810f10840d040c2c1c0a542504c070180c507100034001c03a011107801130700300f216804a000703503e01c0d034640b004e440c0e0071403526488900014140007011405159190b491149481c4a11079221030100501c240c132800340111001c80c1d60b01e0740144100105400f81e2404156080c2e9260111001c645038010b0305410142480001002010070365003a40d40a81c2c200800e800607210085810f81c110300076224609250500d0002a0a481074507018509c01c00c0c03c4c2005110319580c400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 253999334 1250 253998084 253998091
    0xf09070f090b0a0302040c0807110303011401110703021c051203070f030b0301091e02090c041d132102100b03100906020909040b0402030706030506060a080405031e030703180209 78
    0x22000315095401c84080f8101ca9295000a9040385c10154800e801d80e0704075070b44070f0181c50150b8030020a0480c45ca420340e143c0c0400c1c0600110500551110740c0958820006020302d14410403c0c1c03181e40b50740c1e0b8009949032500000480c1c40c000181c00503024080c0038840301d00740b5401102c0407842c44c80c1203100202101611180d50003895644c5101c010319072000d5128200030755101110040a90ba850341c40c90407482c00e880c00700c0c807940d0080c000800c000b10755015075044484164031541a0300010311f41000340d08004001c00a483c402c034906002203103000000280c82d981c60740100310030410120700203040000d07149942481d1070604c0c98588050300c000440350394800a444c4000380c80105032030b00c1d2000c0d10503942040d80c010b100205100c140f14170b00849500540c0301310210b94046075113010030360590f141256000e03800310090102c8100ba40c01890340c141d04c1403280060b84e20701242c1c01208c51508a81801035040030700c000c4104070129030103108524003003e80c040340040001266000500140005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 254000584 1250 253999334 253999349
    0x30c020c09070c05060c030105040e0a020f0f0310020307120605030c13020a0e06030103050c040c0215011e050d0b0609010609030c03110103020f0408061b07051005070210140f09070f 80
    0x81c0005040c50322455450115542c000c050300c9490400b25001c81d410f410a028071440b07285004203c41c10038000150141c0f282c1c2e4050100800e210440c1c0411841c025905112034150192419044140c0d20030300c02180310380003d846440411440e003400c20111041600618001e0780844a0156140c0da0390028036082c0345000c60240e070720090404210340c23407014040b0551b0012070200c004810003202140450351200305032010403c1d0384410000700d81da140c0181010207010384032230041c070825011007064910828803801d00160155201c2c0444c0d10140306030340581c2c91400080520085181001406006001901d050540c950071900e4105004c04c40d071000030003080740f000300004940d001c1e40548507050400100540c0700c03687d131a00302da2144002c484c0d4902c03a00081c2c2901908002e0721058456071500320004000c01080340e030b4a1002004050041c00a6200302000c00c01d4013442c600910002c403c2d0407450036204d047c810a090100d28002e0300a14081d0054030b4140951212641c3c02c0301212001c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 254001834 1250 254000584 254000599
    0xa0203040f020915030a050f060a18031101090f06020c2109060304020a081906060b040b121306020f040f090b18041703010b0405011d01050901030902120601060309030f030c020c 78
    0x44d15440e81d4603070b84540c0d620b500750160300080e41c103002000c56540e84402d001e0003035480b150340325070000084403460403002e0036409424100e80d01291107100740042284408000003200e00080d02d48550288840310700325440342e000140c3c6090401c0a02555056180c3e00361581c143c1810407001c0c1c20381d0301800078194001c0300040001000d542e44c081000000340b6210f01034034803400310558041c070b845d241d19400307448080c104180020600c0c046022101120181c40c0036505181401c0d10f4510010707409000c00e44002c00581d03c071408940d841c8001c082603030a0412084c2d4483ca00b01305e10100c884140c1c8000c10107440d0039900c0d8410f4031110540800c2d44c1c0500c2c0000410b82c1d681c1b501d412144e803207800009101c08040004982d180740e50000b082695404d80b1880e1103a00b046007030508403d281000b0a0011350144900c00d601d500942103500024401031254988075201901d0b14031307104090740954000380c0c4541c8081c040c0340c1c005640e03840046aa250a0084110300c017006991443c5440011b4040c0030b1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 254003084 1250 254001834 254001841
    0xd0e040b04050c03060a0e010b1605031b07080c01020105010b0706050c0409090c1a09103605010917060106050306180a14091501120303020906120f0a0203040f0209 72
    0x2555802850061401042048581400e200d401100e803c1202d02e40e0180401c8140820020000d000e6141200d2420071038501c0c00c1d03010b02052103403002000c0115154401130141518142036405060f000e5000307203004051080c544150140340842c070b49101c07415645081c005100f98180c4104840400e034104402280d2a10703481c10301190740c4625440080440d1405090f1010001f0014545045035132035050b030030707001c04034403100b90841c0320300070405031312041008196852600901c14040e41144e071a40c45a92403038808050800c105010080c40d02c0d41c7c0c2c4000e0248059078111081c10041c2c0901c003040c01210b007032a411540e5400060041070280800880050711550b54800911000d040b400c1003041e8070b0411544001c0a4481c0d60703480402d004110000641c820750020344c04502d00c01012521541d03074a440c0f503070040e6440c030070815010541c080007840da80c0e40307860004044989444411076468036000d0054580a41c01901c00c1d40540c0c0104148000b15143c1c00001c1441901100c0a002548 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 254004334 1250 254003084 254003089
    0x1206050f0d0c080d050c0606150a0f2001021306051306080604090804030813050102030a0906031a0a060918140604020d0b0916031b0903080307170c04030210020f0d0e 73
    0x2455200340e085220ba81844e6070200d62110150003c0e4001100301d030080d03110003080204592201804a0096105100b52221503100f981e1700c112204103428241488164641c1e05444410310383c003070b40304903900054041082c0850521117001002c03140ba126040c000d20f04602c5c042880c0c58416a0208182c0d080820100c1e0f580d6849080703115030204003203a5855403443c11304203982180c01d0004440d41e451800180c81e500100850709010183c4e51000441410040b0503001440c08080342a4454000301001c44140c440000040141c6156219411800c0ca07000c0b86410610705c0c03010454081c0c0c02e1026090302c1d029800314243d040001101c1c0540c03a480001705d418010320710064107940c0a0112424071a1104206024a0407072407940c0c0c01340078006040590100769084c181000300000c003640c40800100d00080040c64000840745001420300d03800c1750100700a402c0c05d9802c0c01400304001820011032410842d4803110882c14009000d0302c00051140584410051a060f81070003c014491880365 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 254005584 1250 254004334 254004353
    0x50901110c0402041805060f0a0b0c070810020316020a080315040f06230109050d0224030a1a0d1a09120c0705090c0304110607060204050d050d1206050f0d 68
    0x1c07a00500110740301c3c3c0e56034000650b5902c66401c5094114907220104146050003000381d082a82c0140904110781e1038240c03105060303440082900b9050003440000310340b41c00140510a60312b400c4420141c0c0303e06000c0c0031080c0c001031000350042598081e8200c1c80010700008292a40442c81103616115980c480d130215014145100201c1c807213501d4490045101c83c40d000f8100d444042c44040a10451402c0005442114030350240c2030344a840000d200005180090001c48078199246850155419004020109410a85a402d9440d8440d01e580e0110000c0e22095a42c107501242c1d841000e04042e00c030701000540c1007055001c01203001c00040d028050070000001100715003a1a2a40c0d03500c6e0f01c4c51591a0051801264410760080c004101c0e41d20542064a0085411524a05805c000401041000d42c404a0105c4035290284400030b00f56495440c44400d0b07a0003a03000d480d000000803801802c00d02c28252408200707280c600280001e89030a102d03210b1004054600303102c01007107400e013000c55 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 254006834 1250 254005584 254005603
    0xc0b04021810030b01080a050a0b041b08071406070209061e030703060f0605010302040f12022202030402041113050112020d052701020702010c060f0603060e0d08010909020105090111 80
    0x500300079106004042c11045454000c0700c1c054100507105076200c01d40030f6298244084042c0c083d074400606900490280580180c20902c64600b60010b240c8080310003911190590080c991604100010088210b01464044c0c076120b0450390103250038041d41c00120104000392059010b01c01c44034000302c0040d00d5082a80c0305010003005c44042d2540c92602d50040c00c101d44a80480a09050340094254020700982e8140c0b040c0d044941841c504003481e03102c140643d800240c0e1b1010001c140d212180d40c0074400c040d040c0d5100b0401503541d240038014003069817090742c00905508010002070b1664051860244207664003480c141455548181d0b241002e1700a0352000301c6198500700500450b00003026640c942c2d402e41d0310301d1007000582045003a08038001c0500c042d010071101c09034071002407540e40c400110540d65010009480d03880e40c036620304032a042c0e18550310b1503009081800200f078221001078010140c9200a2010b507000f40c0c0020118003840032264148994000d981c18140024000c0204 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 254008084 1250 254006834 254006869
    0x624120509010921020616030209060f2a0309040b060912070503100203040c0e1e0a061d0108030409090201020a05160303120b0108010323030304080301090b010f0c0b0402 75
    0x903050081019008040100f021100050300703040c820740c1d100f500b2802101c1c604c001d0b006048541c1c2d404400f906420f0445040e881059800c0100300c4059569a019064903080d90520715200c4c01a41140250b240100700c40360803caa100c0540c180e543c4c0000304852800009a40c0802d90500c0e100c08034419009032403111360300420482080e0f000c04000540c02003141c1c4101c08407403100d6a204c1c204000c901c400d0388c000e030524101d01c809209a0001810b2141c20500024030120118803e08580c0a5100103a0b5800300d0344d03485035070400c80e21907414001034009826903d41c50f29545401821590b0707108912411520716140c00d404802e580c0203119003045145c020701907444465031404a654816840e00003240401e11035000c204a109207031103811701c15203060310788424a9095894980c0d42c101043c1c440b82e03501d82c5111081d20071560034000303180104c0c82100390546950404161109844803400804c2c1005908144680d02c19445075041d009503802c5008512140c0304d5001041d090a0220700f280c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 254009334 1250 254008084 254008091
    0x290c0a0c080102130e070806010e060c0d030605030c10020a060b06040e0702010b040c030e0c090910021611120a08070c0f03030e10030b150c0705040e0d0801060201062412 75
    0x1c0010701074005000d080000a802d07040640c882c01c0e0078082c0c41050b40e12000180c207000001d40c1c10b5024050000c00c803200100b0035400c3c8bc8003041050b280c44441a0448002a220b5400f0046400d007000424464038040f110300003885074007240255181000c030000b0701050340703440b01d4884e01c1c0c0f2400c003114007804030100d4004c0140340080010780039101c1064021301807441e01e4106a82e9510030301ca080003a40a990241c68803040020800104410142002811b4000c4190300b00803860f41d44000c1070051903408138000d03048403a050000c90003602580550281d88030303000b4002c41d1200450240041d030f0f0310074034041e11035032507044c01c004040b4550858000c030340e66004048285074100016a626010444d0f01c10800c1646000842c261410080c0c1d142c0c00c6400d08140b80d8034058610041c00c100c1c01041c0031102d82642c0e440004c1d066038505101080305400001070761801c254410141c90141841d80000e0000c6454500e0709103034050400d050284c03010311558500f2100f4491202d14404041d41c500030b0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 254010584 1250 254009334 254009339
    0x140f090301060b03070e040b0a0510030b130e0f15010e1e1509060315010b0901050c0d08040b0a020c0d1b12111b03100b2206060306290c0a0c 62
    0x8104130340c02a6110301c007051280000120301c0c585402021035005025141c070348c0540c5004180040d42006544403014547c03207045100305600d0320010700d00c504c19290004181e450130701034250305010401821100b130b030300100c6c5251000311a0f000d4040c111240c81c480d007009913890100e04480003140945034900340d03074990705000340e0580c0583c3c10314541d142190301c07840740d40740c0d41c01b05603445007410840c50754211003500411020344a000500303d1a070b418100507240c01c11028006040c41034990203030340450065806e00c818000b405801c0c1790300c0348107040210708c3c111540c285541d5955040841c0410400015009840c00144000c606282e03648142c0400000071003200c060f0406120900100c6244034440040065407140c9040010000000d005400c4500150400001400000484940000703001098501201c80f00c0358040b034809034220005003c604001e8001d060321003d44c40340c2c00c0b10704403180f0241a0304441c0324040d00310858014855440c84401c980d6030404001810207031801c00900d400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 254011834 1250 254010584 254010599
    0x308040321050703020a02090a0e03031e2a0f041e081209010804020409020f030d08060102010b010e0f010f0e15121b03011205070b031302010816140f09030106 70
    0x40d441d2440e4903011146508001004461900070410080e005a200040f044090304021048940207030021030003140b4004000c508524690054843c04036140d03030840311080704464035058541115410300e9007034001c00101d4600c400b849201c0144023000200240da65100d07000c1d801104c000b418014014010f031035560040350030315400e9108800c45070241c6800c210402d0164011078104510507140d203103158903141c0a00c0014104c1e90800c0ba0000014001c6050540d000c0003800791610955840d0310162503d04002402d4801d1a40fa00b418810b101000721450b9070f521040c4498480b0030310300050408803003441141c0207180420301c01c2e00668602d94603400020301c0b4004154603d4890106040340e02e403a0702500800c0c205c0210558202c0050005006410039880442d40003030003201103400c02c54850007400200d07403003500c8200f040c0c0e682c21221011540c2040d8071076402880305c002504001c020920140483c4507119030845a0305000070a44040d0070b00c0000d0301c1e0004005070007040100c0d00c6120 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 254013084 1250 254011834 254011853
    0x60a0815090f071e050a03110c01090516050906060702090702010b12210a0905060d1401090e01150506030c0a11071e09111603121505042a110703080403 67
    0x1211000200d9641100c1071091420f0051204c103042903580d503141c03210403041200100072401e40006e81c22410001d6018a03802402145540c1c0d008170080c00c001d00f50118600e5219145a000340d001d00245020880c0c0e50740e07000e0035100d103980c040c0c544003400e50324001e04030300500007441e00e161f201e04409500da991140018441c4d10411080c0703850142c071202da8160040a000384125200082c400c09020300243c100400904030328004514045038211105480400c0390500740c001801003503580810601c94802400740340511003d0420307844180c2c0c10000400c28070721005010044000c4009452041203118040c541003449149090719461511042c0303140b4101e803580c604100c0d4802100000c905a0050303c206040b005c003184410b458243c0800500141243c001e000350309228072114010000e180318042c17465814901803180c401d503810001004202c82c0c0e030200f01030302c0d05002d46c1e1880100034588064031086885050074103014202c59080c7d80342058540000b0428400801e002041001c03180 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 254014334 1250 254013084 254013091
    0x512010f060318171303050318011d0a0302060903070503060109020702030f190b0a020c010f15090902060301030b04052104030309051002100c110f031e09060a0815090f 74
    0x25800d0203202c209200070a4543c01d894000350030540e203000358504191108006141c55907041c02404a42556500c8040c259000036000f101ca144501080600540c2d021908400e44420440202207604030800825192010780c01300900503440000c9602880d90104000002000d000742100c0380b40d80c55802040281d040180c00724002c0c400c00d60b0b402031180004c02d010041e2a19040d084604d01c107035840f40c4611460260803400c10a50811101c8000e0100b8025a1415070701d4400108841e861003141242221042d44072090007454040480d0050f03551800701d9044a41040700c4885a85440c20039900705115480c0303c181c038a00c8030082039071455014002d03200b140c0c0a500c0300c904182d614030a1200782c010311008400141c00141c1c03880342c80002ca500c5458400c0c50751410344085083c910149141002001d0304882c1c9500c08070706041c1c407810842e180004c01025140c40d609040780302000c01c805000703e0485600784a100303000622071504c106903900c1072040003031407040641003c0c00d050300c041d002034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 254015584 1250 254014334 254014337
    0x11090a060903260307031109100f020706020705060a0509040f1418071503020a090e09031314010f1b0f0c030204180203060109090f02030115050102100e0604030e010512010f06 77
    0x20f1001034402d0212000000100440181e2246103a480b400110010448146801500305040c42000388a80715201325503000b26143d15040c0803081c0300d80c00070f03162007072a620800455002c12000d01003a00c40000381c5054419504026440e4050140000c01804480500a00d4589810b0001080d8a801e040050040c0030120203031050f000360700099511181c0701d0140003102411141e80c0090980301e9401800d03e082940b519001072034881d2122541c8007000d6a16030304030380c03000c40e80c1c0d4081c182e0071068100412000000140406811002178440790100c0000c00a120390300c03503402110f03a04444844055688001e00c0b0b100c10046182808160586001c164003551a03c419001000302101c240c8030b8040e001002030440303030b02e418819405056400380845020488468841c0162002d001c0e907503a80c4000201000b110707040c800024901142910001c40a90a0500a01c0c24140100d40c441e0415094640068402d84481c016110340c0b2465284100201443e000080c4e00e440801541e015a50305 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 254016834 1250 254015584 254015603
    0x2151014061210150906050a080603031204060f0c020703020306010302040c231809060d020f01030f0e01050103050c0d030804080d0b06070b090105010f03170306010c0c0909020a1a0d11090a060903 86
    0x185102105c002c0460b02492000c43e00070400c028140d0300a0f04150740c0000000c0c201c030f1500801800340c0e111407500343d50482d00691500d001d61a0120b21303010340455510700d807008181c40c600c2c680020365541d5040c80068090341d83e038044001140e00c42c0d416400601c0310a4984c0c08981001200f118040d84408040b18454030211a0340d000352900080031401800000c240300f00c02e02280d001c1240d0f01800c4046581459a0350040c4825030950b40607403c0b111101c0000050a5032460800c40e081004003441d00c0e01c40c030420b0600d0000603800254854100f604152195141d500459500c801083c02244059120b400401c05004010400240501c01d0b00c03013034000e0156913a00d031400c103015035841c0001808400500d801c2100f8050110283d070b0300090516254120441d10348540c0705000d000e4202502075921101081e096082039440c0030000c0c4a084662885003564100701d84042c01a20604800d446c0c940000d041da240c04a81038030300b940c100400c08039095075034801c00b51200300a480102c1d101d030740c07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 254018084 1250 254016834 254016869
    0x30712020706031b021c09081506090a0e100209040b130c020f010b010c0201030b03012a02060603280f20010207050f09010510210c02151014061210 65
    0x407909040c0007030071640080c4400009001400c141d183c4440e0811b04100c81c814000070015020071032301d89003400345200702840b81013150512044010007050b4506090929030b13008820400000c2103041c4210000c00161901c1c802400a0003401d80c55a640344d1096908000804c9451158801c0000031055002c032044038040e504114241c07440c1080041c003240c882074804016500070303040503900f62002000050a04010001c111761010766070410a04e503880c1c07c50710850207404100780f070f03040b43c400c42c018011540c0715102a1420344502c494010307131043c11741d406002c2024044510704665400001800c040c0c14031000880c0c4412003450250043c030940c80c1c0014030f400c00c1c0313240e007003000c0c00946880d4181e806d04c0c0c1031050075500d41c007550302000040c1200048920035460400c2545804c1c1c000841c444400d50f4000345005a00d50b060341c8400e8540c0c050045c0c4120210000d01118070701d903a0f88121710140c030006a070500030134100c8815000c908081007010003c00b454002540d0151081840c04039 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 254019334 1250 254018084 254018111
    0x91c170301091b140405060706020904020301060903120905131a0d080a1d030a0b09160803191724040f050702070e010e060411040803122208190203071202070603 71
    0x4282c513110f011a002c020070b105e00d00300300000340603040c0280005031400302e02201143c01c83e40240e00c00c038009404400d0a004216003038a98080c242080d107000c158007030414001441b5800c3c14076140c0740c0780d56103140000030b0089507600900d10385c1c0010205044c8000d10700703060300194404000200003502080b200c100312009003648140c2940094000c10f0099510f40c0d03106410880508030720301500c00c06d004003062148408000001e840c01d04080d684403080884100240303800100002d042c0203240d09084407202081d602550301c8001e0b003407054080d0340305042280392038a400074045c0c0c2260034007414103000d01e4a81c100034061840781d4211151255640c002200c05c41c030a0241c1204000d501c03000c0b42c40c506c0c1c03d030000d09081d8086d0503000d2601d41e8a0401c00d02d1030748045150100e50010000b000003910810002840c42104911814002c0e01d00380d94400325441249006400003480b0f00d242080305208000350345110358001c00d51801c6000c16100030396209480e01c15140000e0809040c0360820 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 254020584 1250 254019334 254019347
    0x605040b070f23010c02060f060f1e12030c0f0109150e101406030607030614010c0c09090309080c040b010e0108130503191103091c170301091b 63
    0xc4410301621428550300e40d8401100300c6042c4800d84100d152422000915034500980e0481001081c00000781c94140344400390400c000202000740b070300322a80070001c0c0e0351240031110041541c201c50317400c0f014024030b401d2110900341d800c056400451040d5241c1c40944000000c03d607030111030003125044000702420b10700742c9055800c0180050300b18080d404000d826a0007140d10302b010801a900000c1c002c2044004481440410782004404c03042805114242408010f0f001350b00d03403509020080c02c20500e1042115110482c504000851400d00c4c2403090003c0c01d10f0180c2605c01090100001504000740079421900441c2c045010b218580c590b58913151040b81c0d66000e06031541801c1142401c01911214801040c080100980c945c001000500c180014185501401700f01500c0001c8000002c0c0700c5081d5607070380700d0540c1c02001540d40c02e0b0744120b081c0502010401d490703100d800c0c2c203260000340c054105408148050010001107a4036a160f0882e402442c2e0140800c0c2d42c0101c05641241c21 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 254021834 1250 254020584 254020589
    0x60405060d020918060a0902091b180a030c0807030203100e0d0503060d151d06040c090b0117070503071d0a0303080603190c050a1d1302040b04090f060501060504 71
    0x41d84089500d801030511140c0070f5030066926440c0040b103030201e030340141402800c80c1c2a20845a540c2c1d0001c04601c0c2c2201c400ea0801222102010480c40b103501c40304a62184208144000c40424815210b50340c4035081b0101840e440841c0c0d00400e9600c440580c0d96060b6030100702d10900030941484480140c80c4240f0003220190360040001000c01001580d09074409131510750070003180305d6030b880807880902703040701d030542207000c0000d5103034600032109640310034501000d0150b00b1540900c8045442160960181d40c25000006000303500840166802d4041c3d10554035030340105020411965000005035200d128240c07180401200820560b03030008075000756035688648446014404644100a030f6548004058100c0728040e10320400f0300c0408201040072101580b00410621941c20801d0540d001081e2003070950440054000300205d214100500783c50540c100d143c00b010944d59190011410346c5c00c050030030002c0c41214108007420045e420300580d0341e40c0c2072100028107688a14121801c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 254023084 1250 254021834 254021839
    0x15090f1b0904020427050118020d1119060e01030b01030c1205100f030b011401030b18090a1a0604140720070b040b0c0708060408030403030c142106040506 68
    0x4900d0448200a07101d203018005a802aa488503d0b42012410003407100d20592003904143d0011000e28103542982c04003207901a580021441000040e01d40303c2c080e468041e403200d24000b145802c0c0001c02c0740740886241f80014400804400a121030700454075000b000343c00c1c0d0301408001d414600650940e80e40040c031400007080c2c1a070b14003e8880960145d0380103000011300c0c0701000d94824228150074a203420036110641002d004002c11844999080c007448420709051000d00201c00000c1c86021810850b03441a000d402d000840000c1c05210741650a5801070a11a86210540b050803211504803041c178002d6151000e03100d1100100c207252842060036640d540051007241102c9400304d049101c0840c600d02c50042e0124122200030050f102600414142d01c1e111414615241d00d40ba040e68824003940c0c00c450706201c00304a099044941c019054200420600c81581c42151018041d42c481c1c0c417805800f1841c940161007000000115214114090580391150030030081110029554280d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 254024334 1250 254023084 254023123
    0x6030406020c161e050405150105030c071208010810060311060715050a02070b010f0605040b0f070b0702071706010e0a1806020a080f130b07031d15090f 67
    0x80000300190002c2c0400518241070b201040e1840744014910402500f1140002440401001000c552084d03143c0c01010210f1702441203080051049100744000e805450400c4000000140780c03285000840e0b9016901840c980c21070300c0d45202c001c00d084028007802c070040c09800360758104044180110ba094035004954401c820862904101c95a48091030440c0c24204850380d20260b00014443d6038800c0b0794030003015a2701c4480345001110980e05030494a00344001036001d018441c2d000050b05c041d6411141503d5481d42d26240c5d5071218082c5c1d010080c03410b014a800c0218a40d80070440c403084804007e010326018110302001510b40000740103214042c101500000d038100004e81004903c15508405840207031f0550b102c400c00d03030344440c520101042500082c4500c511301c00e51203690189614071f0030304c03d84a031580c0700700314018060b040703008054a0341000f030300c0c103001c0ca04280c0d24031000a045030708400300081720fa85659401c0340d40181034000d00340203034914500402c08210701404080b580 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 254025584 1250 254024334 254024341
    0xe0708010905060a0e0903120705280c02040507030b010806010e1c08190305010609090c020a020904060b0604060e0f100c0b1504060303031d0c1c050307081b0601140603 74
    0x100140302c0280015800320b031008002555034005004507004e501c50304c029540e0762682c80700b039800910001d804c203001c0100c100081510f02d0064050000b000f20307031287c01d00e85590300803421511540b1220001e50b01c18a000c2c24410515015805680007070821388131113000d07a80d20380040d43c02c00007088656030403500850030b6010040c1010908590984200c00d0035051007045107042900d01e2a4a020380e0129940b000148266034018101c05c008140d100024841d04a04030320007900e4031110a0000d0141d0200700c080380401c2440d03048400c850402800c0551a550799480050910700c0344900d8502a000300c0c148000d00d420003600030300c138048841e140c84000641e140d6605405407402030880c0810030003002c101001da0b80706c1c017540b0000c4d4081c0d075011079200c400c2d2003030700b042c03ca0003648541c5590140a0141c0e103030711444510300c00d580040c1020400618181040d604502c0b841400070003018000410700c020220211900180c181e00780110350040c0c0c3c84070110b0b400440300406840d1301c8001232001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 254026834 1250 254025584 254025599
    0x1e03100902070212010203041b0b0f16050703150c030b030c0a0e0a06080105040b0103060e010605010f050a12091a0a06030f2306040803180604020607020f18011503060e070801 77
    0x14001c451010f0b2841c03000a84a004d81c03030072a00182c0d02262548070b000001802c0c6442c0300303001809025190342c140e02e4043c02d8500f11030240b05006501e005144018410401d11005000e00d40085da040b00d68141165060072044008143d80e405403c0824601504041d442c10002500c2b0041000075203541105410400d003610800002000a482e941d1200d501080c00750080c0103c900442c032030200440f441d411460034800750344003142406184d83c5445410405030703038002801c020310699400d056599841e0003000f1280600c401105a141d1404c2c00e04032400c10a01c5c0e0044002d03d8416032034811a512400d9502094072010f110141007000d40103001d002040c100310403001007000c00aa0301c1052308001d0314450619008a806403002c030303004810484100c69521210540c0500701014000c9407030168000380043c028100060f0160882220480017901c440703100010030303410303458101c005682d40d00601583d2145030900d02c0010303003030281c0000c44400038840c3c1400740181d52590141c40c0e0034909d2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 254028084 1250 254026834 254026837
    0x1f030b221a070806030a0b012601060b07021206040507051e030d020a1214040b03100506030109020414060a120b030106120302030309070617010b03070c080d021e03100902 75
    0x410300c109215001000001035005485100040164141c800d003880c00075400380005000a103441d00a810404010340001c128040c0241910008160240040707080b415540f0701c41800c0c0d0a02c41d07a0361030004c011841203c12405059220310031546158a208000f080d951a41c809940c0108658070600050000d46401450460310ac1120100000c01c068000002031500301c19400a5000d40c00c409100401e101a1041160500b0030302c2c2803640e81e00303407150101d22081c80f89201b142c00c8084080f0114058003d10b0ba5000e005080041880d501c950710740642e40020341c01482541c0d2181c12102c2d07007400c2800c4c034600380c3ea2454400c1c0c4440c1101504100c10707601401031a2006a0306560716480441d0300300381000c401c2c1c01c90f4040d500644d100d01e4071215aa18220b40c0d90010303414000ca01c0b20070705101c1c940031905419100008591070300c07900cbc3c0c040140e841025443d0300600b00000070400101d6114a81d0107020301d950701028218540032f21140141951100340c0b550314800c00025000d100d400c06580 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 254029334 1250 254028084 254028121
    0x6080a110402132c070807180b040303032c1f11160507090507090e01050f0616030219061b110d030e070506040f03050d0513030308090c03151f030b 65
    0x42c01d0410041c0b0300b01c01281030100884901e000710306c00c8004d21050b942d00901050041544c05000c0c04110308104184d0348070700680c4002010541c6980c0301980c0c1c4080215002851807074502c0d024002c0c0001c8154030748070045010304a074240395003030388080903d4190180c04000e5170740d8034802d0b2a1910886801d01e041d03062403030035229881504000291540340707100b11489550241d03150521541895503660040c034041c0c0c0036521034664800b001015503a800308481c0c0210f00d43c950504039844524083c4d040018920110303e00040800c85003041c400590818003100b981c0c0764601520218442080c0c0e82c03154418a41504e40c1d10021044842d80d020754010850110904100d603c21075031000011401c0d40507070041c119102c0200300030010850100034280c1c2280e01400d0217404e01e0280c024203061144648800760400c81a100811005502400240c0d8105002780540315010309074181002c0001c4199040b141c1c00c0d0f1003200c480d001101d07d40b04001036070340c028011000b54407083c5041105a10b03c9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 254030584 1250 254029334 254029379
    0x3020a0b030402060c0718060b130b07150603060522030f1116170105010e01121506090227030a170f160f0303050703020403050c010f020f0106080a11040213 69
    0x4c10036044d0241d0200b006400800111a04107c000300342030250064558941c02480304140c1403001c80c40040309108500e00351850716046603140c41c1075043c501910391140d004154072a14048000c403d000d0103030041c0707114102d2104003000c000304044040b1140c445c8000042c00260f40e502c031190301c145c4542001d10100312031300e003212804011100c000e1507080050b0b018145000c42c0d0150580912000c2c00740c1c600414102c0c54912142d0303d00400c80f00c9421903007a00900035550100c4842281c081580002c0c00b0f071084050443d19048500c2110000904031b102c50b09002d0092074090b5824a030010703a1210003a0700c001038040329076110450b03000d03035040119424640310042c0f1810790b296008140c01e2811500510f01104403550506004d400ca030405010031082500400050022803c0054401c4043e1001c2c80c03e22030080c4400e5049042c00e9040034054407550a1120000e8007200000c7c20500e62801030551500c1086d4010800080303202d0300d120000e42040c0b4010070040b4004020f03800810b2400c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 254031834 1250 254030584 254030587
    0x140412020d0521090a06021906113009030a0c020103050405010b1906032f03090709110a0215060306070813021816030b0901140d08030408210103020a0b03040206 71
    0x150a1400c8100050f00f030f8010380704010581c042c45180c890381c81e100400b010300103041c8060301400400218014040081c060644a401030b100503e1000102c07140184500034840961142042681d01c1c41c00042007a0400c0400c5030104000c464080300300c8800b48000d8072161000e5801e54015006050024010b071065561403203807803420303250b07201c5480d405005141c803046a80d04100c00a0116041c50f012000600c1101900b0f100c0282c038000e050442450f2004101e440740d80305464680b41040c60381202603e030341030410700004401003a0103066030306601e80070b9484070a40c540555480d001c0844003e0392540c04407000c070300c1460007580702540042d4003501074802c0c59007a80204030103164901c0f049440131030b000300701308211034a4501210700c007266103010320121600000252144c841800340340520140310140051540c2c8c0d20841d02d1100b580b0840741512403406040020150300030311100442c503402c51038503a684c00e0302c207001c01d41640c0d03001b00340c40326244c1000260080c40e0002041240c100300d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 254033084 1250 254031834 254031853
    0xa0210050601080615070f210206090a30030e01061406040317070b1003030314060a06031104080708070503120f07060506060f0c06090705010201110f03091f020703140412020d05 78
    0x55081d15140724015a10880707911608c58078401001c00d58034801086400450500a0001000c10701000071500304503042c410040030000e41c0c505101720b5410f1150251040e040151450300b44e04240140301ca07540080204503aa40f040c410000103800205a20580401c030a10000740c840300c828a410301d0449086041c091140e5038059502e034144c0300a079940307818060410406a240c00b814028440c460f0901d10305061400204114202a020300424952221400c000020209042d540107211900444107080d0362030065580328885030103200d010740038910729a0102d2241d50121055100750181c12072502d05a80c5904008082c0a0403259000e51f040105007a441d80c4c02016282880d0305001821050411004280c50444590720150569041503041c00c03002148000b5200c2c044d03004503881b44c0c0d80d07072640301c0d05050009103001c0044403500c184c1c821400342420345c003901990340b00752aa0300b1990514804a00325006510824040910500c0d0348030050170720810f210b14440c45203080b200c4298 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 254034334 1250 254033084 254033093
    0xa06111c17010e01030b0105040c0c030f1115150f100f120e0f0105010e070905010804210203030a0501060c02060403080d06030c080d0e04022503051e0a021005060108061507 76
    0x41c0d0a030b02c074042c0c401c050401482403200822049005001c1141d0401ca002e404e00d0014180d1176040001805100742e400b0310700c000398001c04900300d89203078110680380c2c0d900d81c4a032407002c000301c04d543c14aa46402c400d080c8060341055a561020701000034074055143c40091000c851038101d1018a00030060b04404041514049005040e86105a42d02911044003517240c1642101c0051b4805100e01c0080014840d28580000c4500c0c1a16000c1c6488680c55855052802c26406c040070540b0640701000304102171103501002450003120003400502459a03500411240300861a0010703500c42000c000410028100c500100190700e4207420120300c0e1640e036103d0840c45061944101400d41190701507000041c2d1140307410250020845046040080d20030408100c0f000d482004006070140c0c81100b02418055400e54110300c600c0700340103141e0200368810349071680205464030050711030106140d410003104d01443d849a00188d4501398590384900030020b6007140b41403865072000c420001d050220307 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 254035584 1250 254034334 254034377
    0x405030304090e010f0501050105180f060318070f0f060e04091401020d11040e040201030203062206062c010f050c070b0702180103050709050a0f0e0c0a06111c 70
    0x62412810008618070f0700c145103400e65104a0807030308001c0c90040103020680c0c0003015140d0a4101300c1420030101c1d030720008520f03140e40f90b40e0720552220011040081442002d107904a01940d25810350701d20a6a540142c4206204c03405000109882c08801340403003440750005091401d0001c2004c14000c03203d849807500b80f068503103404d1080e500056008a42250b0340110441d680e0301009140c81c092030902c03090f0410340c2c0600020f04140d0004080b07600c90f600d140c0760001c180c1e0f480140715446100c1c00003031001440f90f4403038500452094000401d68004c905801800040304070004450103040b80011201030300308052040c2845028811601e40c00e0080160741c018190942d01207131784083d24010048032082e620040c3c0500f070340900040c000680c002c104d00c0c007100c250b800040b500d51a207c1c1d00002902020302c84a89031858141e03841a811070000710b10950100039101c050354140c507440200d0b003407080e1280c400d20b01d034809951240da18590312038038445c0c0003851501680e070710300d61703c00340804 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 254036834 1250 254035584 254035589
    0x70305060a050a14160f0c02060d0903030207020a0b030f0c12130c0b0d02040806090f150c040302090903180a050d0308040c090c0c062f0306030703050316060608060720030405030304 80
    0x9517140460612507071600043c040c110304045041804154001d07900080c842c0c0b01d2207400d24101c40e00c843c001000c0602075019a2038869000b02005100d507103401054401e600111020443c0c00100c0010800d01181a82100d4008034550000c0300740d0303035821080e03d41003204c0a60440e00d0740481400004c5149000c0054a00e00f4110140541d803280303411126840c000024195040981100100c2007c0010010307495018242c280403450345070761004c030320720a24040da6001941024400c02000207d1001100800d100261001100951250002885681c0081d4001c0681101d406000710020034018a0240c0c2d220b8070940840000c551100400c000355408101b1120124911042c05420001240103420700d8640400f115803d0803a0b00d54030f9a000b0110144020396107030004042100c075101409408090341d040403c503540c03101510f8407400615586401640e07050300d811408a4060000714080e0301034001680d80004050f41d0000390108003000305010f0483e4481004001007940341030019000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 254038084 1250 254036834 254036851
    0x9020307090905010503070602073305040312110709020f070501090b090616020601050108150901080309010324050120070e04022809020f0c0703110f0102070305060a050a14 76
    0x181d040c50510b03840c0c162803040c0c01c05807081d00150703002d120060340001c1030740403104a003d08400e8507000f402c0e03200b4402034036580044190342094203000c41c82c5d00203000b00100d80c458206801c102410b100126811201400741c000320343c102070300c10400d0b0b54081e0007506102400082c01e918021040d51020b003124404007003120a0302c0a43c0400c502c80070140a0581c1c400e507084810868400910b0f002921003105020303035070602c480c03180442c039440c500c480400721a42002c0d00c035403801d58541d44910754039000204028006401c207050f00e60900d40a4041070000055107105c101c049080500541342ca21030700102000200c0c12148002c41c81100704000c800038a10030001c3c1c129400c1600601c00798000e002e003140306c060f13800c1c100d110b1170483c2184a80d0445008000041c1c4852000c1841c1c0705900c58075044210b01d00c41e422000c401d01c5045001c40103082030496040c104003d441303005980b6164148000340a0b90021070000d0b100340001d4108552010708120006030b43c200c0c2454000485100740c404e0413 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 254039334 1250 254038084 254038097
    0x31303050106080d050a02191a040c05030708010605010c060f141006020c06030402030c1002030d1e0605042c010908040816061d041d0a120e04021c0207020a09020307 73
    0x2181d000c0c14020a000c1c5103051410902d480c03503101d4040c0da940204422305040e070386508554024842400c01002c50740601451400d030394241418099502c20080c020540329000c2e819000600c1a0148100811154107171502e81c1030003569204c0340010414504800748081d2180351080c0911007110718036101b05030015481c000c9604042c002803030030042100541c0222030400a12001d03950000e2504000d6000f10f8a01c28402e04a4408900314014003480c89003150600503000e40c4d03034558408402c000f96002c0700c1041075545e6441080161103d840c500321848640c04019606820081101c110028506002143c04500303940c0744d40c0c1c0c583c40f0381d0240e40c013508003105a000c142c0c21014144020443d900d440d140e206640280805008101c010aa100302d0351910892896509184038901c2840d10f00c2c1035a0307022302c080c101107248030500d00600002542c0340000781e035240740c94400d0342c00b5103400490603c1020552581030000703601589080e89d002c4062100050f40808600043d0710410b4942d8522 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 254040584 1250 254039334 254039339
    0x303071203060b03040215030a140106020a1a0103080f03040614010e0a1a01080c07020d0c1502060108060907060e04020909040602091806280b07060606111603080903031303050106 79
    0xd0442c1c07159003206040760307010018800541c2c1d52021b980500140e00303400d1503913501e610070104000c00c0041d03507201148002c07400000d0442d4012800069030f5018a40c0f42c00c0341d420800f4203180d41c050901005100716418489802811005009190b0151081600003504403005d0f40030904044c0c241e1081a40002050820015040c680110030b20341e800e0b00c452010f02c4406c0b10010b40140130040407a440600e02251810540d564800ca0f5100c0c66002f06507500c03015240c41c1d01c80681e070b0414503044054443c40d80002009040003a0003031240c98031001501620b410003000b150081400904aa880343e001e100b840020b94400601e140224441c0e800107a4a10045080c440c0b8040d05007130316100d04105200300302c4144ca824001400c20005d500000002c10700f000704015400010383c100541d100008550481001038942c82442550a146c4a1001542d004100c080c3d03200050941c610795001c6c0800c00300001a1100060049030030000c040ea0b0801000e40045440915180e00a40c2c16030b440d001d08 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 254041834 1250 254040584 254040587
    0x1090905091b01030b09070302130b0c03091002030a32030f240f090a140103080c072106050403020309041a0901080102070804030809030a02060d021b03040602100f0b03030712 77
    0x1e081c160310080c04d0a206843c100c0d0002070502c0001000282819000158403910600800c5110081d0911030925900d4441c01036010b5608e4010a144070b0040d61034142e513664460002090311240c00c250303610240701a00c1044110103041c000b10190784104800d00700c00742c0400211000d10b201d01e21200c0c0c91117861800340034000d001420641401c596010361006103480707448a07660f11259500036141810079032a400c402c10003c00407c000e60780c035082c10900200c1000001c80007090504048001c0f0f0f03c80c1a2948803c000c1d0700c402d070380000c00b100c01000740c81c000070707105801481d4410b0103070040d203091201c42d0000c24161106124910740c1c0606205806090303152880390710740900a010000c504143c403075590548603110358000507148030000b2501c00c1003964104a031f56251035026120a407114a0114403401035080040d506482c540f9039103040030195400015034045844a03402000340d045a680001c009000ea40000c18070300d9161014240241c4003000109201b510902c011041441c172000d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 254043084 1250 254041834 254041873
    0xf0507020d051606051908090c06030f0a050105100801090b04240302040e03030c07080f1603030b09090604031b03020111030f1e04021008060f150406020c06030c180109090509 77
    0x1003401804030900a103100d80c0090321601d81c6c0c0c00307081d04220354035480d040c500510340388001c0c14065220400008002c0c11450320500c503070281c03441d8a17040c01140d881d203041003038020b4818508800201d22100400c40381c0c2468009800c10034002e04000365031103c0e5003613044030780c0701c4014000000e0040ac10800031418a03200740307200c4082040107103003182050394045400e0f10590b40701030301050300403c0300090303100454211044404003610068040d642031801030017406905080034402c144503000070f0040c200c00308a5900c03481d45560f440202448440111040c4c540003c0191304542d69070f0b58601040a45100660268501341207504081ca40081e04400c04440d0003455a001041c850501c0b00585a243c0072010040150410303500503558140440c03116805003c24a500242131300e601d04808503505e0081c41035400590135036200402c3e07a0f00f80a010300c0f09842100d0b50000c100130805000101c40005003000e04149004001283d07286040302c1650410341d81c0d04a607410250340d0844400d07602c403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 254044334 1250 254043084 254043089
    0xa1e08070f0c1e080f0316030f0c02060f0903040e040f060501051e060d3201060906120f2c010513050d0e030f010e0f010605010c050d0f0507020d0516 66
    0x54030100e10001a941c8108201510542c40f041c82155000c04007000064816208041d000450b6140c8a20b40040c07100e07004442e000381200860b142441e102c118040c00c0c0149406000f40e60000d001944883c04000240c841c0100042524001400041102152900414095805111120642641d43c02d12204540c4180e101c540714415070b02540f100021840030308410144110f60194650745900c1075200a0b00604040b81e00221407900070990b0610440b210406034005082103812a0383c882c5410744e040c81a6000302c2000c00c01c0d00740b402e1001d003807542050500d107884000c08102031440c005c5c0c0344a84c0380b154010780902041d2120408210609104140e403002d01c8030303608a0351001e540c03502074654030174018640800401c03c02c8030380f90b614200044503850341142c0c02040300c4284008115120143c01c81881c400c0d5003480800074096210313107030394442c1c0c54006e00941a4130f101c2c01415100c1204201d65a010b00c00c05000790b10242c0d4550b0241d400e418042c40181c40c514860b0080c2912062194 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 254045584 1250 254044334 254044337
    0x8040b0f0103030804060b01050424030f060503030f09130c050c0c0105070f12090308030703140907081f09061109040b180703091109042d030509060a1e08070f 70
    0x32030040022a074450740040d002a04440300180014000c4012600780c4074941042030312051100b85500c2a217814040c20200141c4c0e035408014011161008a00b0303540e051003550ba06500901404042645400c0144400c21004001c0840c841c442c0100006403403180c0a680c0104002041a00780040244804074800310240b03415440c080550b56506140303514200041c0100c49949990b260312405180701102940c0c200c0300f5107440e4545000001c019103180d0301c1014445284002040754254002000360a450010016000c001022288d0101030019104041002900d41c8001c902055003031017211140200780820130398030619503081c00151a0b400484c0d41c01800c840a03044000c0c28001c4405800803034510700481c242a4604000c69007440c0381d80c0c0681c0c40b220500074841001494a080f40c0c0f005001154060000f40d50072041c807000c80c904601501140080140740018600300c00240402d51540c01c0285461902c0541c0c00b411544010382e10300461280000d00c47c110f038001041c01c03c1c10086 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 254046834 1250 254045584 254045611
    0x90f030803010902210c0a03061a030408071e150e0a200105070501050c070311060c04030303200a0e011b05120705010e0d03140c03160c02041b08040b 66
    0x440e92800310a100511545421607070111316894a21042c4c180000c0030003140c0d602c0080e074140441180c501e0390214298134042440c200b40003c00140c5101400d010140a860280c20f50742d6175121000c1c15170082c0b00c11101d400101d400881030b40082080b50400d2070042d282c603ca14070130070100d441122004c2c507140200f54044c2c9507040010b0700e003080c0e6446400ba6403009100403142c41005031800d010314400101554244420040e141c0b81502c09881da00d0301070703620413010711410170400c5d403034840599604030890010082840800c0c000d400c000f201c0b4241090108940c4800c00d021085070700100703900c400260300f48854102c03669101c0c0106900d4103d11214101c0070b9110396030595140f1840140e0322403001d020038403800f0b0060030350048120804c03240036140c101c903000d14002c008100880d101400907070704001107540c10396010250b03841011081c501d000d10340e040c20015500d0641d05c49007203900c103840314621080e20310340c46012002c941c65500c510300786051620b401c0100500003001100e46e541c9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 254048084 1250 254046834 254046839
    0x6010b0a0f0e0306041518030804021503250c0c090207140c130f02070803040b040b0a050402061639080a0503190908010510150f0206010611100c030903090f 69
    0x43c0801c01540040c2c4c00b90055803464030b4590715001a007103028410240c030040c90400b0060540201c40f40c1d00c43c038400c4a0f102007855039851841351500060f00d291004400c410b01c201c80030601c0c080b101c582410f9a00340740815102d5503965451006558010168464002c102c82c004c000c65441182040c65524020302050400200814500c40700d00720b184c80e180d510f0b2440504401d001c2e13070440755440d8100100580c4ca00c1d1600380500f0705181903034115603403070450700000c1c50280d01d4422680126030091034285040347e5a000342c50394011300c0c001941e0512078004540102c0300342074062601c10205480e030380314400340080c0c4651118101c1d8028510f58200f26a10000244040201c03428000501c2200c5500103903840c08440c1800319400205142d03180100f405070f102c0203803101c030084509001c01400d051400380d00854121019840e240096803000005001c001c1c00f07420304800c60f4020b80101c40b905485001c0040a9840c3c2401d4030010076500d10710398061560000171540500509440c1d107403032a2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 254049334 1250 254048084 254048089
    0x703020906060706020c1c09060512010e0414010e010e0f06011a0319111309151404020d0911010f09060f031a0303070c0504061202031e010204030506010b0a0f0e 71
    0xe00082181d44246400a240810404941d040c0d410304c404a1085640c1c0e0710302010181c0024000045102c081000448005101840354003100c101030240040001c1591030140c0d2020350017006082140c1e05505100080900082445800e142c030700b508002080300c0711000b00403810001c1600400940340c10003c0140701c41368251025101d500d0b590310510359203030f48200d40c452142c6d0510070030024041c05e124a82e0059070511002d407084030031410401d000241d407071441e503084518403413603103005413240702c42081130000c10114401c01e10310180000d0300d801400d213003d40c1141c00c4884112400406401c49030002c0d42d2040c00c1e26000111410410002414220050310400018424104154a500f4000003489100740c4282c501040902101d845107098070740011201e205000d0305028500d041800500c04500440003601160043c020301812104000c0800c5a000d146040c80b03e199002c100c00000160700b085024000d181f4640d41c40c1e10358921075002000008598002c00030000c102080d0038a40d03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 254050584 1250 254049334 254049349
    0xa080f07061e0b060a02061f18020c0c06040810050a150b0c010501050f03061501021606030e010b0f0a1a130e01060f030c1b15050a060911130302060c0a050a0f020909070302 76
    0x1ca08c0c40300440300e801002c6080e440003040c1d07402c504108040d0020b15120f030074503900a0504440d1080c1643e00c00344a8106000c8107014601c00c942e41c139440003103504c201d440d0783e52209030030655400001c00c10341c01d00180c401d0b1100c00e960000c07100148c006000c6182003000c0c4107031030141074125500d0548410700d00000e981c4180c0500700324014504041520322503030007000f4059070f41c0e00703c0c446141000d1b56020090300601c01981510459401c1008020300c1d4609905a213800920042000300c43d0341c14294540f602c0080004c103850000710412003851000d90703882491005064404c120b103155818013600400c8080790180403400c0c5400c20300c00702905070f0412460201c0c03008003110054003800703d0900310440d4ad0b134600082d07003a03441c2c1024011401c081c0c0d00320724180d4446141c1480400002840d030300780d510400650202c03d8104400a000603d880401010302d070b0300203c1154644031143c0c66080c184131019004545a0501107101d004608000410b07541c4100564050001186103401041c070a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 254051834 1250 254050584 254050591
    0x1503100e0a022217060115051305030307050d0f0507020a12031b1b120b06090c0409020c0a0201170609060f0406030609080306041d0a080f07061e0b060a0206 69
    0x340044400092200c26565040e40c0c1c0380c074401581c00268080b90f0f00b120752402d40318000c100d009214540c60800c000c20000700d1504a501048108030880c032039174801ca80e41d030480b2201944161100c0c0001415580400c054103000703001d403025020f1480081e10281291a01a4189007484014800e10002da55411603802c21202d2000e1541e0411040b40340454180d0030701d08050460890448000d82404008441c1170301c0c00c81400d140790407071500e4031400d03401d009482d400200721a6003080003030418241380781c1150300800c4507202e141c1081d44036200542607812181c5004015409480d40000750b41c1c2c007a9071211906241204030155090000201d00d402a004103224040c0f41c0c41c2080c858240c845500100095400420401c80c0aa1a107480c1c038140e8002d40b000341c4510308140200e0741d0200540f010f00c0040b40c095000f0041107040c0e44d01d04401c2d400800c4205c0500e0070032302c070343c1700460740724000c0703610446000c01e903040d2094405500908481c603100d50240107440612500c500660005802e541 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 254053084 1250 254051834 254051849
    0xc0d090f030213020d0218011d0d060b0d08040b1207050a120902011b0303060914070206130501020421060c03020c0c060f0c12130e06100c0c0509010b09150310 70
    0x14601001c800c0340c80680318179501a0011403000a80c070140c04165010191101002d903074005861960780e035034071a94082415682e03400300040c00e002d000502c45521011030b06001038260710b0303101025242d4130801e4100303522000c00c0c1c0000040c00c174035503051a0600c44e481022800c00c2c40c00c3c82500c00004043700030304400844020395801081040da030241f030049900e900c5d85240440c1d2820f05181c0200501002d01c44c00040c103003044000c0c001443d222007820f204111940c0103080d181d545c011141c84032210000280c5065608100100703a41140004680d9841160419a2008240b42c80c0007811510b10710400d00c00c16105208030619100003150030300203035030100ca14503201d6580e602c07804100c0c8a80400202d480c030819500f240b480c0722030320140075008ca02d1018000903075992101c0131500ba6044521030751000c4c0d080c500400040c007800d5460007183c0240080c924540e10381c808558a5002a00540030150f00804d80f0800c500e00341d036610011810288907176080d4106003185c0c440c01e1030540074840 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 254054334 1250 254053084 254053099
    0xa020315100b0418020c070504060609060201060b040b0717070807030e130615030903030b19050a08010507080103030c03050910091802160210020f010612060e01020c0d030203180604080c0d090f0302 87
    0x1b030041c020040b81c40504001442040080c0d91100007600d03074404c5100750f00155003030500025414240c3e8007620111810b40c00300c0c903c2c200240d6035886000031081030600348180144100004508410098820948243ca40340280c0c0c07402020409100300b00d1846003040740c1010030902201a544070040c03007840f401d040124080c54135240a5001e00743c0c140070903821202d5071078003a01c24212019030800f100d500341d4018042e10788803412542a1102140c0d50340c0400c921100400000f442a612620340a0080c0f0300141401c4500001402d42c00d00e8540c030600003121404180200b0400c58070300d1901041c03229085180090b80b100980d2035440c00304002c1c3c45004100319005641b402403002141406c00e141c020800c1944654200181215900301900d04601c0d2401c4401d00580520072940c1c4907103114000c100040c00d21f1f41c1100a9440285614211000d80f403c034415100c080082d1030056218500e0203071a4a41110b0326403030131100640c103004016441004004c011307004120401035030380694001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 254055584 1250 254054334 254054347
    0x1302040c090302090a1a011b0308060f120d1407170304020409082205010306050913140a0609120f080106033602041407140306030a020315100b041802 66
    0xd890310201c0354400b94000c50914108248030701d0300da000c0300007a18102801440e075194840115948440041141d4981c0e0740f5042c0c0b040840e000b4007015030b0065000f01901690306408002c03585161806240c1d2040b0343c0304403180c02025400c074002d07a001c3c6140700c607094240301054903085100101c0f480f048111440c000080340035512207801001e05a6000030307005583d440d40c0403402c50b800d042d003403005468803071004010642d503109000b000f0445100900109140d03c440030701501c1604030840403500c40020f42010921150144000380850703010740b0340020703241344900f442044166046840c504000f8480290541c035a0011100e0741541d810b4900011902d0480b079079034038131010ba00b1f07860031a260b001e460701101c8000e24001e4900d881c4240c43c107000729a0301c2ca01e10300846600395400310200341c401603d81200103034000550392140d0000c04030742d1070900c2500428184084000d51307071000c000340c80030410f01c9400c01c0c2a00e4014410b101100703141504d040c8801c3c00c001801041c03c0c00039038000510 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 254056834 1250 254055584 254055587
    0x19020c011112031b04080d020c0108010e0f070215011e1a0301060503090106030c0f05030f160b0a1e091d0103050c1c151506020708030f0901021006120b0f1302040c 72
    0xc0513001d8407003941242d6140e85031420f0301d5507030401c8811032006208120004005505c5403038283d04036840d401d64007070182c407a12400c2909903c028541c1741140306840400c0500208110114001d1464509284403000a11503001d810031007600b01c0342d000da20003c10b04050404001c01c990448a86150031038903922000a0103014001641c009003040c2c11a11010445020741e51954040b01c6007102140d000100b008000345d140d070303820340c600304404c1a1008204521070342c8000a0142d040700340340017504c0e03400c290030040404101c442084d0000d208403200303201c144010384031300c0e520340c48890000c0b1040d0f1441d990f007640d03000700e007003011701489404c50032086d001284010200d074154495071240a00200b44c1d4504002e200c40c41d0380f1881980e1075180000e03014000b043c000e00740c5852001a40c0b4003466040c440f1070580c41100090b0440c4a1441260000d04080c4100300c003801040c5038202105840d800e00c4550329202900c0b904c0c3d200300c014180820398207615071621034682e05030350114202554100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 254058084 1250 254056834 254056861
    0x51905070f030e010204081b0a12060b040f0c0815040f05010806010306060e040b01120606080a030807031a03070e0c090d0f060b010509010503180316050f0d1e080a060b19020c01111203 81
    0xd442a10b4ae007194800c2008040c0e00a0000c0c12001d50f400c000717002c0f40d104890185d82051040300007003140354011445542c00481e02c400450001341c80440c0c40c0d82c2048024084807007d0b8402085504420300610400c955401410018610611146081c0c01c1c151150121640e06215120282d031010100300100a0190003481c0241283c0054480044c8142405030a810702142c0000c000f0b450200b005400300c00000000b8203c1314058000c002d00350900c1b010400d190400b81135602c48400602825129903107010b00001d00a1281c038051600716083d14002e015541300e10146414010103200300c072416680601038941c45284200404a40d105c1aa0074904503c22284980f0300303210506410428003200003220040d01500100300c2d008170000f00380448a03240c08811010305600b2041026540910441c48180c0203000c0b080f0006107503940382c1301c01903183d00c40790203a41c4100b82007031056200c81e0180800f460b22042801c04601e2a40c0007087c00c1c0c5c403803020130802c00b5191001710104007141031000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 254059334 1250 254058084 254058089
    0xc0306120305131a0702010c020a05280603060b030606070201030e060a2a020613060e0d0c050c10120c140f03010807080a020f0103051905070f030e010204081b0a 71
    0x401520200e00c9801d00400a80c800d8100c0c804007000d50600044058001d030041c0c900561108820341001040e0f40111010941c81c20140d910440966010441d552504c01044031800c103000c15500b048401d1009002008440d400207091510b0700c00104010510101265807040d42141e1a0f80d5404603440140c00400c1d2842c2030b000d2078801c03001002220070942d4000e00418034a11b9050100c00b510103111021490702800c2c4600581291010503a801c9003a6401d0070b007940720303810100345051100ca01d145090398116200c80001c2c42a091f5909001003070145140074401a41d090200014548000e0600d1840401000c11319607104c1c40496043d115901211480c8200054180c0d01c003200c09903080150000c1c0a0741c102406407150009040c000040c00b03030f1403254040c00003619100610010b500400b0b0041041482542d06078006880001d03a21880307200d21800c1d12000710a802c101c40c0241281c2d114540140c1581c8104010f001c901000510b00080079104014800c0034070800f4007060400d4101c2d03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 254060584 1250 254059334 254059349
    0x20d0e01020102190e0a05040203090a06020c070b0a021005010e0610050c030c19030e030a15020706060512061005010207030309031106091302120f06061b1624030e030d0c0306 77
    0x4104a14516174090441c0c040381d04112a04840e490b2504100000c0707200c1505c0c2040107902c2000c103080041c80c81d40150500b0b04011064401035079413142d580401d0740c00fa480207001070304140080ba000d08031602c02c940c0904408070f000c0d199480c016011800911195920805028000c00c01c0f0541c108100101d42c00900340109a40ea00e102400340c8a0b60308064030400c07808101400c010308050700303000803052610354000707040000e00d80d144100b100007980096000d0b41c8041d2115030104254580403005da810122020043c04a0701c0c28402850204015801c05030440d0040340b42000400d500840301000d480c0c0cc1210484440401d40014681303200d044140d507000715040410400c501c803a940904480810082240c95696911580c0512940e0465545034012028000860b0804590242403040c09680c4101d40e40c24050040043c010070503984180c5152030840d0f003e69002c0c007c0d02001c505903d02d030a05204c0c062820b030710503840c1e000305001d44404550b030761502400c00c2e10030b400003402010311 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 254061834 1250 254060584 254060617
    0x7050d0e01200904050a0b010203161a0f040605150d03030213031a070807020d050a0c020f04050a090309141809030403020d03110c180c13050a0603140a050601020d0e01020102 77
    0xb2100d0020290400d00020380f04903d401d0000352515140e0003920000c5905138040c1d46003080004030400b0701054100c1c2514001c07035140403d4490348400030454010144204181c825180c685480000d40300004c08154420422200c03604060715420301c1c1c1c5001e1903150a0141c0c07251108043c0094162140c3e20207040007103550a0195210b030868070190240005941e02002c550340e010041e039403102500000c00015000704040c00c90a8461802c50171018401002e07041810490800a0103417041540e001c1308140e916540a01016048004d22004000c000301c92044090b4071000596401103404590f405a001d14000680c820000c0c42141d000c0e6500910b5440c03c680c2c58100140b003d0104100070701144034900d400c00e540d25004048e0004180443c1d44411a6a0f0314507681126400550b0450741c0c0c4401c000c00403c5c180c1c5e45e400e104024041c540e41c0080d000040860090a540020b0011600a868182440156640411800031288480c01d21107448050400100d0092080b42a02d00c0006030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 254063084 1250 254061834 254061881
    0xa030206220804092414091801050405070807050a03021804170309060a18050601150302161203060f030c0b03060d210f210c0c05070602030307140307050d0e01 70
    0x10300c1e40c032200d80e80841c009044040440d240c40760704000c415000d490302e0200c1d00001340c800e03441c7c003060103030f80b19404484900c070b02c2040da0221400d452080d00c0480ba1500f14283c20301c500041001550b0040104070b0703040d41540e10f19000b003030208003041d40380c0c1481c00d5144005001d011002d08002504209d400d0255601c0c42c01c105030f151a540f003920003e042605003003c11281c0001d4001064180760800003a21240c0d1030b205041032a075a410f0a000e0925800b0301220366900c541c1c00e83c00c40076070b0007250211403080c1050703001070031201e02c1e402005288246050500c0400c21944603402690b4051681c0d50380c80d1141310000d080030415050040400d0070107c0c1119008080c1d003200041107400e0746a006c0810860300b41030310300b0f0a00c120810301480c1c402c610f120b012912500000740710556070070b0440c46001e0940303e060401c0c800784c020703030302603070001050140031684403010b41e01c840490400a420b5050642c0010024800c844052040586a0000a1900b40207500504000d000301c0910160203a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 254064334 1250 254063084 254063099
    0x21609020d0e030313020907080402090708100f1d07090614090103020405220b0603091b06070203010509060f01080a1104020a030b0619020f010c080c0307170f15030a030206220804 79
    0x702c3c6120204c0c0a07c540c000460442da02440c070321030042c0c2d4020006161a664002c080302d07508401403001c010b00c0c180e0500010030b8182031075000003400c484450444c0f46031108040c43d0041c10068440300420420010411046030706c103040e55000103800c00240c0d82d42400b900120043c0c000c50b0007951340302107415203e04d00c406205c002c00000501d81401400440b03250000c110031400100c6690946801070702c02034140050003860300c64030040040556047c4910b82d00402c0c210f80b4100c4109080358041d0b0284040759a03c440060b00401000005190000f55a9944401200c0170b03e5003c1c007841e00030480f103544c0b90003071300446000c41019020350b0711142109031480f240c0d1251694131003d800740c40300c0144034540600502095440c65201c40707c0d56103810f08401c8559000611003c00c22042403000c1e0901c6c40c064801c1405980b04546003050381c1801d13549204241d078409001440b0b98032048145c4002500070130401da000c4c03502c401c00c14507805d440f100380300481503821004100d080001000704000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 254065584 1250 254064334 254064361
    0xe07030204051e0117060a1703160c0f0b04180c0c020414061903020a210b01090c0809030309150a0b0909010204091103010803091e030d1e021609020d0e0303 69
    0x148801d0ba0b860070101c0c1515000005d0b603405541c09508206c0609050040080c2080340e180010380d2803080f01e140c010b100007110a515040102101e4081140e801081008200510500030705144110213242c0fa00d030071124182031402c502c0d10010b4a4851040d428031501810717460b041180c000d0800c0c0012110700864004183d0b084603494454904028107101000d81490f11505480d40a00b6041002c0d00b4a500400388100e0f1185012140004404680020b500300305694002d2240748008982e03a072210902814403007004210007225882401041250400040d1104600c200300102e10056101e58491001400000c150642c01420210034809600300541c003c0c0121029a0000c200b041d0b0184041d803814030081c41101c410358428010500c20340f03003d003050300c802000e4035214950308150001103810f144000c140e540c04104c46c1c807081550600d6440d881818401c00c0d101800507200b0210070142420914010103143c29404604a81090810381c0502e003120540401c03070b9201c0c542400c950011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 254066834 1250 254065584 254065639
    0x305010303080a0213090b151201050f1c020909160605040807060f080714041a0909061002151306140702010609021206122b020c030d090e0703020405 66
    0x3408800000708101a10310940da20110b94a0f181d024171031404403140702518400c030079036170b001001141020064880e4801003913000c40307801000a1561410041151802c3c4e0381c86100e0062450720003250540c0502c0f101c10782c41d41d50440c1c030902c040d00e0300560b19107001100f2440c1c0c034030041c5000700891007a0b008400b9104482c04041100c81d1140c50b9501180d0b011081c142d0309000c200c0d5000490810b500980035125980e41d90581345003400d139903014030100d03c460784646240b41c1100041c182c41c2070030410851a400358007601d8038403100c245044000d54a40a89100d0400d540c607140200d090940810400e400c0b90b41c0002090150309201041961041070030350700480590328080300081c4410203802501d2003203d860040314100c0d40c0d1901030149a80b01825640c600303010341090100841d18070f0000c01c480d000481c48060f865400d83c540a03150400d40340b0308511aa03c500c4001c200258080d0040087d511840e0b10012240c5032020f09074068090754001907400030800c48098140a0350882e06802c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 254068084 1250 254066834 254066837
    0x8030307120b33090d03030504020301141005060c03090604090b032a01030b03030c0a1101140c07060c140a15050f060a05010e010e0604090501141008040303090c150305010303 77
    0x108401c00041103034903254100c00f44449042c100d1000b046010451128030000030f0300001c0381c5082d03008800114210608a41200440c3e502c02c103000540c102403040400380360485041c4110350418084a00101e07181d03101d01441070000040b501c81d07000f018000d40d0880300b00034060035103c0780c455613180060582240118000c0c0b10b04643d0f52611250340b5441405201d000300c01340000068000110301401e02080201e4041c0720800941c40b180c5000c100c8030200d540580c2201a0442410000500c1c0080c50580c10312020014440c0d10503120011400e40207d86060501c000f0134041c9203051140b10301c1603903210b900c6009100048060180d280010b801c075809144042201d50b03101041c2885840c0192000740d00400d07951000e000740c0d4000c0928030758020f01410240a4030742501d0005849521a40082204540311001001200b8498110401c4800e086403401d6400c0c641c000010f00a800080011701090b03110144d460038001c0310343d071800203070000307112050024465400240181c04280320840 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 254069334 1250 254068084 254068091
    0x2070605043c020a12030305070e03010605060d0906090206040f060206071b0b0405101a0a14030d1409040f020307091a040923130b060901030f15060803030712 70
    0x88280000c80c0d0b25000d4024000c031005031020768003000c0000b0407a03105040360840c419160105d5607118030381450411501c03da4002c1102d240090b4010440501151028021ba06190080c4078039681d200c1510f07000803540d840040d8110302c60407d070025004064000c1d40040000074041450034085046004cd1802070702112495228030f5421900320000100f140c0400c1031080f21100010104144180c200d409482140c1c902d061b40c80b122070403518012121503a103507a400d2020030600780b50348260010601000304000e1000103001203a01d903034840740c1b03207002c0001c40850713100c2c035101e041d007500c00103d00a8000c105032503102c62100000d600a54002c40810048040040c0201c044030b403500000b00c8642099091602e81a21030001d054200001c2040b032a806c0b048600c604601000613100300d1000c40400122003041c18007254140c40901003a024020346401440400c002c2c50b104e006450303110303010441354101c81207004000c280340c0d00009a680000814480800e41c4148a0030994243c00000c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 254070584 1250 254069334 254069363
    0x60f0f0e010e0103020d031116170a24090606060f1e02280605040b0106080a0c0c030c1110030f1a1509150307030203100b0c0a0b0702100207060504 65
    0x31022500740702d240810401c000c014401428105000e030a00391007401c12140392002d01c105035040c40c0300e0005040740a002100c08100d90848440392802d0041c01d200684203031101a1501007a80c61800c81001d1040d040891401601c500741d0300010340c1a4001c88200302480c1c90f05001014509864078040024216803e06240c2141e01c1c0c02011585c200f68005203040c01d80524821008101606901d41c15200b01d040300c00801c1e828001d05204612031980040990306111014184040160030034010342d10b85032a8052051700406462242500740c01c0c0005e031000c59141c00c07602540c0d82000c40b608180044c850300e100b00d4250304001141d1000d074070140091218484151625001580010751000c4000c140e651584003c100802060401400321448540041a580a1603000b6a0074100080d400000c0002252520300c042e005006607000b4039103044882d01b20301e036481c03401030303030180c48503180001151038140200300154041900034410340d22800181070100c01007408640a0303c2c65243c42252 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 254071834 1250 254070584 254070599
    0xc030118022d0706060f0302420418050115020c0f0603091c1106010e070c02040e07050d03020313080c0a0b090411070602030618010b07030819060f0f 66
    0x25100d610612001c280d020030324902110210364103030035040420100403c110b402142d4030f8012540980b00084a91801c10300c0c40c410f006c0103003848502180350b494198410b2012900483c01c1c15008654000300700d2138a511140016140d208985c00118500d8035810400002c695a4004904a410b500844280713a04508001c0c1c0c1c403002207030003640e40050700c2080c0409506d0320b0400b440e04980c84004540e00945a0400390b141080855140b1001c9804003060011400041000d1409048940300440090410a802130059503403110300130b00c681e45481002101d00c404100100c018000101140a804158200079441f81c1c400100031229104d2142c0120b40d07d980090101142d2030f01601c06428186070400c03034078031600106502da45c4540c640780c420001c1b50a210241403030034010480140d8a0400d102003004880f4221031600c0e40103c07100c0100004a2108150b0342c071550141022081e82d980c4035481e40c904400c0440d1008010301d009070105d0340e40e40d03c0038040181c441841115480381d850300300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 254073084 1250 254071834 254071837
    0x5210907090218130e0a08070c15080429010f030302070f061b15050f011410080601030c140d061802070203030a14130905100e0618070c08030c03011802 67
    0x61455840f0184150502d18101020483c500200d2250300041c26000040d65038185601e0060a950940000c25168180144146220010000614140740d20394200401811903103000700302401801040d000912500b0355a0340701180c00c080284071601541c1c441202d14006404d82c00b0581c014840c00c0c20101d81c200d01d444c03400003525143e4541220f0307880f01c1d00702500d0034442c120044071340d1025a0100314402c459030207102c0c02900c82c0c0c200c2c0305c486e6041805078602c1001c141005807060350072040c00540c00f60042815600810286804210030722222026120680c00e01402c04071000e00265407150390f002903112030191098800f4485803d0a401301c07100030390207006c2c0e0103945504100031030b2115500840940001d0699650103904120350101c2082071420035501a00510b0749031410006404a0081058003400c100180c1c2c5441d4105100803594001000b0402c2540203003140200d03441c42d002c1c0317000c0100c41c0d0b844810103a40745007504100881c2e80003803054101c02108440b111004081a00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 254074334 1250 254073084 254073097
    0x2010e0105040b0c030c04150509010e06120705210103050606030c10090504150504090507050324010e060a031721070827070306020403020310020915070201052109070902 75
    0x440c02c9419110b14031130028603800540090b00340101040006032542d01c1c10080c11809500d5100c081e1100f03942000500443c0310346400c144a64000c0100500c010b8448070a07035000003445c508603440d02410b0041a50360440d280150303555405500000007041400101d0910500055003038a0700f00b049441840080c52825a0050108080003c00d0142d82800d5005042021205043d100700640d1540454202d80c48202c0c141e81a8102c5101400384e41410444039440140f526206001c0351700241c0c0100b184807060060002061600021540316514103840310080c50700402803041c446041d00401c2c603158001d840b9120800c2180d05001c400c01a09035080c0c2c4141070075140c00415954a40a201a601c400e1060996400fa80c02d40410440c20420a003006140300300790060340c0301c6c01e44c01010310f00254980031290381c500404c1000110780792041c110244c00641e618460b1030744d8071031005031020f0041c803100303d62804590201c01da20040644c400c40c001c9950405071040592640c421070241d00c68403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 254075584 1250 254074334 254074343
    0x405030703030e0607120806011107050607030e24040806010605120c130b1606110f09011b080d0218040b01020d0f0207091a0a0b21040f0204060608010602010e010504 73
    0x300020000310b030088001101041e40240f05914100b03545e516401107000004d007240004080303508116507960459460100c005184004114981c42e201c002407040c4031380d140c01000c10035061000c181640302c021041010b22501400c04143c3e02c03080e82c0114194000e4407500106110300e200000340a40a0400c8801007002c50382801d80075501d0f1940390303445510861700480310300340807800010301c3c40007080031b06221240d02c44981110003060418405444255820030b68070306040000300c0c00420b06500f12001d88800b0f082c010002c41c00001c8681d40c880580d900a402880001445510062a0f43c001c8c22035103000400700030f14000880520040f101900c50b598096440894807140a03805000e00d007100e4030144c07044807040740d03c520f1800192045283c0701c0300111083c00f2109800d24000966402034080032210b01c2c03c00401401c001606021041e8104403615a40e01080a0101900c5060304190300075105001e101c0d9558001400803500b44211001540381482d11700c07202e5010b000351801f0740e801 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 254076834 1250 254075584 254075593
    0xc080109090510050a0c021005060f0111280201030e030a080a050a182105030f0a0513060e06100f030213020a0507150b09010e0702061602010e010f02040906050303040503 75
    0xc01640a000303096140040d02c5610071080c100c1c1851649000f840d2050a1a60b00851660fa003a10042d29014007802d49401c2d00d03044c2410070203e03454510b03074407003058030034a480c6c105411000ca51a0030810050400e4690410641c19529100801400800c071940f003a0303401c00403850301c00c039010303202e01038000404001801070300840e42c494480c0d0001c0f90807800c0303c0c5000481c010110b09081070381d02d240400b12100c00a801203182480c82c11125122003114034200a451440c040845500c0c002d001014610069995404100c14040d113280780a25035600041c20050542504600d6076101e1003112060340e030021a150120305070310149000803c80364090505034880036001c466001a401c02c0d80c1c842d04220742800983e010590a031385d0140000c01024001030004210000c2c0101508142c1000101042910a1090859000850a0380000708040c001c4045020b840101e0144c5400c140880b00c075821b0001044d0000c025034020002c69001740d80c10001103030345109044d12400f4a00ca4190b06400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 254078084 1250 254076834 254076839
    0x403081e15030313090605030606040504030507030f0e0a080105270703112407051207080304021e1504090501051e131e0b120604120c0f14011e0c0801 66
    0x503075030058100072100500360303400c202100c003c08610f02c07000e502030400075031a200108550b0500f40285504200160340600940c0b9054030301400c984a1410f004081150080b41c08004520840e81c1c101e02d01c03002441c0e05942d5907214259806400261825807a05090085070f15160081450780c0480c00ea615003c3c1c00701d585503441d000c1c23030141d501442d80c0d000007510031900c90b08500c45201e548030400340b9040036101c101500300540340a90411035006182010400400414404404d9070740c460350481c0d904401404076446000d0180c0c20851054200d404248081c00300b2151402800c10343e1000c0004201581e81e940c10001e01e100c100f031514040c004000700004103400c2c2502040d6040610a84c0815045110040801840090340040400d941e40f265050314074580016881080305100b0010803d600309500c8600300184007000c03240900145040c2d40081110341c40f5050085a00003412103001104820003501801d00002041f4000c2c5402405100f4004c1e903201c0d044d600881c603a1400426170 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 254079334 1250 254078084 254078101
    0x216020913050c040e030d0e07030b07050a050301030f110d0302010f0b03211b030703020304091416051b03040e07080705030910020310030807030e1309020d060c180b030403081e 78
    0x85c0085903800c0301c0c0000c108440b203006160142c0380700d80c00380d20002e0081502d1030809410340000030b0302182c100081003007040151039001003501d040d070340c10200102008000d0710700420404911151a50465a461f421070103140d019840f07440d003480e83c980c09203c1c02d0468010192100c042c1c40f03041100030100c0540c01811071005014001c001800071000b022076000040c0c0b145903030007244003240182c0c1300240038024004580101100500940c00303100131400c0644401d42a0240b1017040010464082800c001111000b200c034030947e072014058076920713a1150540c50100304102c940c40049505000850702492140003240e1013083c1400240c80002c0142c90014044d600141420b1801b4207440d4011010450090042034418031075200c000c2c41c10010b0044c03000700304065503070413001031405040c41c000d6215a0010165103512010010ba812400e80c4103841c505d122000500d120380a42d103001c10f114070924010741c004c5001e40c07500340c000c2d550308184100038048503000300e46120b41e03100400e2885 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 254080584 1250 254079334 254079341
    0x203190b1302013c08070e1002070b04080c04230403081504050702032802100b0d0c15021005041106211302040b03030306060901210216020913050c04 66
    0x8a105261010360300d8001d8003a041180c01d0180c0244000000d152002e01284e0f18801c0c0701c02c900ca160501c045d440c50030050180251880100041c01381e40f50550490b02e051003400644042c01c0248612510760b0785070050382e41d9402085403a240168581101011082040072440b4540c040403114407025554a0f58101c0c0e50000c040d0103404c202e82c040c040f41d0040c0d40c5602a4603c01e00d0300354001c40e02d1b141101610303082d955208002486842042804410455010840e4580704010420100e003c0004c840480c800030301d00f44c006800b0b03032040c1c0000714017000c45003110504140558202d8030880840000c610441c0d106840080c41c1d2803500e807008a1904140002d0514845204d81307407207440c90b00740281100c0326400c5403049208114688000d0440c0390500c600c2d11210300c07d8004504500c1d0482c00b080703140c1710b1b03400481d0500001c100d0b09402c8034100c80b143c0080c941404c40c20342d211000e40740c0d80c0c0846030410074124864616040018021000340032030b5002590000000c0c41100280c00600c03004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 254081834 1250 254080584 254080621
    0x6050a0b09100215040305180d03090918020604060c15050f0708131506050307080a15090819050304020405060607030806061305120f0616020a02150418090203190b 72
    0x1580110086000b80132100310282c0d2189001c1d456a658596504500302614816402c050784100c0607110f0311f4020a520000324815104800c00010b0740d0000025603031180510504004e52040300040c02080c0c4540c000c40d91000d40b40300d002c020f00340d030400380c000d1070a5440440d98000c4d0030b158580040c2d0054810107003aa0403e000d40b07000100720300d26840303c0e1030040c00000c0f00d00005880380b04c2001142410803404005000310400b4080c880c42d11b40d00c0011007c3d8403c0c207080c4081e02d44510505000001003151101c1c0580440c0043c4d0416400029040e5081101c0992007a0f2500c0c00250035814400126031000d98507545083d00c136034420301044226001100705441e103540c10280030138142c0b039946071002145061300c01808665039450b141890800004d100400700d81c0e032216260410394000403500d088982c101d4503403040c00300a0408100502440d4800410900350756820405440c2991150000c64020b5080c1c400c0c00d041d0288844060005201c01085403403d0800940b00b1000c00710351564 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 254083084 1250 254081834 254081837
    0x20a06050a06030213050411040c05040510090506031614040e040303050c0c01090f1205070c0b030601050d110c0c010203030610080c0c071e05150403032012090406050a0b0910 77
    0x50090b22130f00415a42400c0b4007090792a503a40d8000d010a10002c442c032060452001c0341c081c40f813901c0c0d004c4010003038001e51080c907001d0165803d4103200b2500401e00341d0302410010f0812038403460f000c4007500014401c4643c1c4c0d4042101c11803078060004030f44c42282d09039002c50304004241d440f035580440007400c0090125185240c244000c4007158000c1c020000450700038081c0d204c42d28020f003055141c505004544100b0301504000001c002104004c4020407100740900b002e4481d650403005035424400c00f40d0600d215850514002c0850741100f002c1c040c41c0c132140d01217441c861054001641d9912054a20541c80304406d180c00d10b0251040503156402005044400d0414043d444018070340501900111102e0201e0704450110a122400110040c00c088030035000d80281e0084020072807286000140411102c03e10300b980351504007103400d800101d842e08a1396480d0301e07100f4502054110309052440b4904080c400104c51802c409024113450045885501d0080403104101094425840620 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 254084334 1250 254083084 254083091
    0xb0702011104080a05060112050c01140d020307080f160e0d020a0e0a140c13030308040618050c030d1422031509060c020a111c0807080d0506060a020a06050a 69
    0x30454a901d0141c03004040c1e020060401c0c001c00e04d0718a007801816003140304070b0408210240d011a0b000149000040e00a08008500801303d04186915102d00f0ba0500c40b00c5000000740503c6644c0030000e14400e12007000b000c18691502c60882454000000d04200020703110540001145000da10140000788001c281d4061a5600c03038000f4140d06080384d03182c1d5400d5848400050042d10651050782c000307100030283c2d142910fa00c103800e61142150101404109400000a080165039489500030501d150702440c034051203840c042d81d680c05504c40450013400792180a22460740150711000d14201007039000c82c08c01ca070055800200080c9101c00c0c407401d0140c03000000200b8603000840c20380d6010340e07001103082e00311401e00030b060b5400400424110751200001e0008100741c40c0c0021442035048071410700c1d48221614030184e10190800c09440c851000400b002040030036001410109813010b001c0c42503698503010480940124007844001d41c11429181d8002079070f0b68400c56022180c84c4002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 254085584 1250 254084334 254084351
    0x1061106220209041101030501060c0c06081e090129011b240906110304020d03110f0f0a021c08030a11040e010b0a0e0405060105040918080a0f110a08070b070201 71
    0x83c1c0c3d5090300350b4050f58450903c5240b000300b540d240c02120b000d80b0260805081c40c100c941c1c0d507458901d620b40b1170841040042400300c2c2c910610408603101040303580c04c10300d0303143c240f41170030a0082101002d08548a8080c0d51407a0203520303012100e03211082c05031104441c01c2000c9146408250030301200b120700d030a2201d00f040c0b030f80e21109058218404c01c2c140000d501c00045ca0314200b1035110303020751860780b03406004020040c1d0340c095126440c107900d0306c3c2c2580403607040d00c10701c0e1404c0c0b0030100001150103030603240306c49488006020490980203d0f08520702128004850396419140d000240c824182040000c1c64283c180c1c002c40f0380c0004541c0203178a000e5403200d05176094502038104c84800388000407818034007940005808000b0a044608020900b44030b000644540700324850758003000e454905107104880840040d8100ca6041000c0e541c2c2c580c4258001000c01003a2080d540204000d0003c0758140359000550106003540045118680105503c454000d110010720020440d929156030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 254086834 1250 254085584 254085589
    0x240b041b1d10020d08011d0705090a0e0c0a080c0307020304170a240c031a1002070803130314010501080312090c0d120201062103050c160f030209010611062202 70
    0x81192140640c3d028000105040310014102201070348046040d07002d4407281c0f1044040000f0040e00021175041132592501000046001041c083d404400080b10540c200441c194000d0000c04400c1456a24001590384021446d0a0750000b50744000c011ba00604c001e00c952556205004009521042201c2c2120b8503581c41d2500446800d941200b030f4180c41080000d1080e5501400303130007588605082c8441801d40c00c819008046039007240d445020b40300c8941c101e0700c0c000d00018001e801000c0c1900d0b901c201041000b800720f669840102c1c1d61074030204c00c29020903411321956046c3d6039500091407400034100d4485005480241c402c4a85000700c50040030305542e070010880f4010710803421040001c02460000e402c403921075200e442c2403030b25490f04c015440c2500340ca200304c076645420425100d0700038480e80e91030110041001c111411610305c010410035012240b034421a80701b02c811007020303a281c1d0030850340903a06811004940d8000b1001c00c80c5081c5611030300310031600c0143c00d800080c0c900e400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 254088084 1250 254086834 254086849
    0x11208070b01060203191704030806012304060207080f0304060c06180506040507050a031106130b0d060e0a0621030e0315040c08120f030601050403240b041b1d 70
    0xc00503a10005142c1c0c519001404080009106c5080c148000d111902c82c0c0080c040b80204010200941500003802e10303800380d000041136100b0090341c07480c2c000210904803042d40c018003c0b503015101e4007400180d00000002c12112007064480511700f081d15010040d10144142c80d0122002d54503600e0344008180b00301c00003a170940c007810040046007018280396040020316000540191287d040a001095400802540340e860030f50744e00da0b6800c042d648000c160b0045030001261400001074101400c07a0541100044d1060780c10b60712925201d2605240c1114101d1282000a000000822140e0503001b04050204c41c02810f000200e049800000783c101512610b804014140314001c1c0400d0001c5c20402e0b038040d0010000800b0060303e0601a00d401740951800d82e6025200040015840c0e44202c060782c0040d80d121200d074030b1107400c480902606120807100611014a00001ca0880c0d2030280034030845003880200d115a54080203c0031038075045400e00e840c00e6400b09075041e801c80d03202c020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 254089334 1250 254088084 254088089
    0xf0d0908070f0b0108031e09030f011103042f0103150f06090806090309030606130b0d030909050a051006030902040b130204030308010e161d03120a0e0301060e011208070b01 76
    0x94202c180b00d4a2803410b80d85108043c0c1002140b5441400010b5518210741304c06240c0300c00d040c101548403a40c1c400000e1403c05001a60b0002d5402d0210f0403a2880034400958000c510582682001001b071159030746004801d0f28828405c140040c2c4003100075402503000688004884042504050321040c0440b45000590710410015003c40b000b040490424440103805c40c0d41c1782e02461400f0700a03400659152405030425200d0518440c20305810641d40d80a41c02d280005001807240712103a050141c100012840350001090600713000071103980c0d05107d0365100d8001c0906110040d0b050030702c202c0040c180c9030012a0440e0fa01e01030a5083e83d038030510745079000501040942e8403421894001d00304030b0103a11100040c4a10300c14005107082d04014810314219900d010344100c042d00c0c2d400d40c1003c0c1c9264081350507000d186a100100c0c9a002e0040404460036201c3d546407141040616080306d07428403410307041102403001809201e0000c0c90a8058601034000d51f401c103d020389800086400030f9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 254090584 1250 254089334 254089343
    0x703021308100c0e15130306090803070806030a0b040b07090e0103060614090106050f0a1412070206100602030711010522050102010b0402121b16050c03060a110f0d090807 75
    0x2d0401c501102818010107640388500e20344203038801c1c2054082555a400508460450343c0c0105d90f03507540c1400000440d008541001d401d00440e0030070708103005c4036801039462800241e08c842c0001c03864100060502043c83e40190005225601d6440d80621500054455030410002c49400269044100c0f422030180d0300400c8001441d40c0340a20b100d035018514005035001c2d680c032000412415410000343d40d4036a48064a096a038002d6250489003000b41d020090a510804a41448006c400940051083c11241c007118019207500076407941a048500c02d081c0168410854040069034508001c1c000c0300041c104982491000e40b03c0480d460f40082d400c100b102c0c1415410480f80d03a09000360340c0780c01402c4d0340852503c0d00181508070603500c002c00d400054101d03101c014000740701400c02c0716108840a59110321a0010f468465202c044c01a50140720b489880302180700d861541c851b43c402c1e801d06042c8546098100d05c0700c516640c2090411001903a07441e41c030b00001c24820341c0240300c03443c0704 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 254091834 1250 254090584 254090593
    0x60f0c13030317070f0f05070804120b090d030605100302130f272a0c06050c0705062508150a1725060518040906051b0304050a0206030703021308 64
    0x542d03c1040381c09801000a020402802d000b4040503801010030140800d40c0c3c5011580d888032800c02c0040c501c510f0340082c051100c1e087d440c0090100042545c2e026400c00e00540d038502d41d40308011010784d8506e00925900113030801c504c02d5040d02903401012455140082e10710710035980d99801b070000110f6032101c5640e10a41001a91034031400e0b08601d1861042ca504000501c2d000d0703c001c01c800c01d40310350a41000591185c5607900e500a907411000d0302d070301110034401881e0042d0040c20710b400c1164212680e21840c008110043e000c070740e071981302c0311180f0740500181d01010003c40b103d80c40580481c106410329140c64a4030703102e22003444007508a104202410080d40b04915181c07820905002c5030408911024800c07114075004d0b10005c031251880c1c80c980300e11285428440f030860f16400c0e20b520511b4101c0400802c000e541002e0311541e511003201c2c65410707070000b0462a910013190001e1064000891590040c5484805190441043c1c070b40103080c00602003032011240b0041d084804958403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 254093084 1250 254091834 254091857
    0x240b0c070315020c0d03110712030b030601060201060f06031a150708031e01171b03030c0304080c0a1e050d06020702100206010302091f0b0a0c02030d0810090905060f0c130303 77
    0x208030445942c1c500b8030381003003c250441180c0042340038840c0020311903505040041010380c0300b80c11451048100409403141941d5403d0040c0c001c00c5035105280780391010040c0010164000c1c1b05110740000e4901e005040e1054a00c20008501d042c0014200381c150280942004128a64040c6110b1080d0004504024200100d20070040303805034400c4528281c6000041c8040300080b800c0c10800d11000003c0300d404410000003820b40c0603100d00c90900c1e2001290000b1003480015011064100c10b0724030808068542101e802c603220042380b04044060902010071680c100181c1c82c2188074024200182044510350001d0540301c828820400103074015001401940703456070609070000521111074850000c5c048902e26011241d10a112008401080c44a411806043c203100300545c02019903891440150b00540007036015950a210415500c2c4042440c2c0c445101c0da0038956049030080843e49d460b51041041c941000385400c550703080c144042080c03030640300e01c041c02a5200382c54140c4c1600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 254094334 1250 254093084 254093107
    0x308041d010b040501020a060b0103110a05180a21051912091512090203070b03091e03070201050f1c0e0307140c090103020112021e030901240b0c07031502 68
    0x3401a0824001d51004000800482ea0002440c0811503444400401c40404920068000305080506c075094110002004c10b600c0d607000006018249844403445420220340c024044c3c8a600e034050400307400c144010400c0e050200e082d4140d40305105008544420341c0d1034190520364040c50504440c2e1306440f0320200d40003034001c1034005c0540300300c1c1c00300c0b60315698100000301450244030745c00c129280da4907400401d54030180440c601500004950b555682041c03145c02d550303040142c00c07125100351500000b0890700700c003108850403243c05039519401c00c07200c50a419659800f80b405264450b440f41e0400301000064002c001015030444c003c3d40e00c94050341080074400392210000c2810ba0020190941d8950701d45403a5810b4030740a19003014228001d0050000074460302c40c003000345c03904400d8100c1e000501030317008505c14031034440203201107503a2070346e901d02002010035003001503550081e044c4109000e481c09000c85500c140120f4500c0c40c2d594648040e80c101000d00c00903520340020700360a084 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 254095584 1250 254094334 254094389
    0x50c0c010f0509060a0c0b0f04020907090621090f150b1507030509120115030c05030f070b0a12050405070905060603040b06090408040806090c0a0609050a03020d0606030804 76
    0x100782403408003194030100c0109188a10b02119105181c007003948100544078000940070f10744e03c038800500d9814280c41c42d18002c0d5007103808a00c1010301e4000130300b00074464402d2134110340b011344030305208003034454054038007905804004030a00c0d991030f96400824040c00d4401c8406000300e401000204803460040141e550030130045001d4075846041e00b44a000c03d80031264103e80500d40517444441c1c82000441050041a044442d9030a0841c1c103140e0b903090b0031450045038400c41c844503000d6030340d00c1415142c0c0d81105100506804c0352408100b2429400010096000c0078500f00404141c01809603040b11002d49099480754848034041c80340c600b65104558001508640712421880d003551403148140004100501502d014400701e0200319070002520007600d05072058900c00e10340050425a620f0006120344c0c4100c5c1e00100c00510a070141c0302030f1064480141104003a070f410b6400b4401d01c02c040304412500e2940d55580040407030350f000c0c003074005001c5000c221000c01d814001d000819 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 254096834 1250 254095584 254095603
    0xf0316030c090213140307050904052a09040f080906040807090b031609090303020f0a031a06032e080303010b0301060207080c0d0609050c0a080a0606090c080103081e0406050c 77
    0x1840c4100310381644e10045441c00d07411940003040c08a60f009641010a040156a9001540042c074001c140030810501060130060284140c5040c0c000900c04c8100c881c610905584607900482e008000c540800c4102c07505444aa0003500402d240c4400c0e03402080c100e92040d0b01c2034000d41c012250620952400d80a034001c0300ca821401040c038a0105004070b0032400c41d5101e1084d2240d80d4461120806010b034043e00c014181841d031300740e01c3c0c0d240720001401422901b14061000c805409100c00c1502d0184140e0307025800c19122445000003010210600c00c486001c0840180015000015403140070030085000e809803145041c4c60317524180c000ba1070500e098000880c00c1c1c01c403004d529400d0320b90f00d03d221845608908040b0304001d80e4103159080021410b0b105800820704000802c80c890300080d40d02896100e00c804110301c1d41c0d240492800c4440000e110800a05403200400220318044080e01c810b6200c0d85002c2d00703800d03440013031240960241e400203011580100384140101c0f01800315030310 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 254098084 1250 254096834 254096849
    0x310051905030d03060e0f0630070e04021c150b120615030706050f1e0c01060609051c020d111c05060a050a0b010f14130b03040b280504020f0316030c 66
    0x413418002c00040507010f0310045454072215070021000c408270040b02c0708010030449420759016a4590301e181c461543d04440503801055290440c0c13000d16468903213600116008541c1c018140701105200024040d02040d85038008850f00282304040418060940503040120071410341503148814141071034529070028042c0302e028460398101511100469006c00044044000076480181100c0054040c0c9500440b1030b600c3c165010490342e40001c8a1070548400b158080700070401420a1700d2000340e480030081d084040e007411b03000003804100c81d61000c1c160040000d2091402410401c40c62203c120703059542780d200c0010700200b04854400d894014148070380902c006152640082c009100c403010200810110340d448200820000042d103109c8501c404419882c0c07940c4440c0c000303c07504282c070265210140403020513240101503e24208030155031b018418a20b0356108108003e0000806c180e800c41c450403940d04c5e440e42c0610420719100d140080145030181141002070000c42c841e0060304 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 254099334 1250 254098084 254098111
    0xc13050402040b1806010f120219090510050d0207080912030304060c360b0a05040503011104061709030d092001021207020409050709061701050c0310051905030d03060e 74
    0x40e644c000758644654000828244040300074a00a422108030740303c0c5032000b140a10105401c2840c3c6440c0d000307449c0b40039860b91500d00064031401001840540301d440c1901040d0200004240166250040c20415004da001300d82090010400b040410300c1e03a41d1300d2007254200004000c10014503108000541c0c0451620305440910240c41e0304120120158241404242c00240004441c42034940c40291081c000001d032104c5440901500c0c5030404d000f0035110b9401c1c41c0c4071100103910a81034a0803a0501d5943c5010355210003448100c0d088091304021150108112201d40c1c0702c080c1c040c034140107105594001e030424403c5101f1400c0340c1c51581c1e00d811900700c0f00190003a5444c10b020b0381c401c00c0e0120b60000741d8220910b0702e51f1401208bd44214411800c0641c00076000403c1c03850780d200016032034000c0c07040e1f5a88170a0390f0000d00c411100a10407801040c0305000600703020030354200814201100645568441c0002407829038685400000240c49240070f120611610b040d180d0883c0302000302a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 254100584 1250 254099334 254099359
    0xf06080a060c0c022b02040e0703031101091a0a06030f030906030b0909100c09170607090e07140c0307021e04060503030301080a0b07090b0408011b020f0706110c13050402040b 77
    0xf5907549804001d40c081c042849602654500700c0c04200305c002d503004104204141010082c1500d415551005502164840105c414143e206003d1007107440d621007440000300c520006601801e48001d41240310055031100080000341ca0000d8852003d030280d100d00c1c0304c2c1c0f843c0c03d40040560b01001c1e80b080c02a40e080f4140b01100c0030004031035070740c00c01c2e18102003584146030104071403845887c0d0158a4801d40540e079404140000300b8140d0292940766124212140c842e01c0c1100607560548200c000112500c10301001c20b080080a840d21000601c1034a14280154001501d070004d9040e00200c00c0c600c1c11101d5082d450a440380d500207103010ba001d1403c5602d0181d0f580d4407103d00740400350810b62484c00003020240301c0d001d80380140c101904800c0e1135a8403403d06d5402004020b030065190042c0b0090f9180041c00000e0000795490b1500061246034100202111180c0c143e1701ca540451260b0f1649003842d030f0354414410100010700d480051305140034010001a00e00441c13000340503180c81c0241 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 254101834 1250 254100584 254100589
    0x40b030106093221120307030c050705190f0b0a0b040c0f0212031003021c2306070f11011d0d09060c1101051209010219020303100303120f06080a060c0c02 68
    0xf000320120121410b02e4811000b60041065043d110030095080c0a04544048800040b001860041006903420056107a4605c1c2c240e80901c22814060043c3d8001c5182c2280c1010801d000300c40c40f445400003070240c40041e91045003602c0c044d0f4600351004d0b20f48000c0350050515100b00040c0b40c4861918081d40101000040d44840600c41c2040c5030000000000e840011031003000303c011640645007032494000d440c0500b0880e415800c04451801610315503400280c40200b00d0240b9a8241020b40710b540c54000041e50241c1c03601d0f0601040c480020380b20400c002c020300c40d990030b40b10840d01c05002000c000501c242061030000600c002d004603030b40700303100d0664040e00034034045030f0ac41815144840c0740c500580b400d00409802e6840c43d00101c0400c21100010f4010304020a003000250201c09540002070f41c4a00046802c4044006000d80800101c0d21070090310007100c4040d44001074500d00030060700103449042c0c0103115907500158401003040f009118154081030545403009880d80c40d03600 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 254103084 1250 254101834 254101919
    0xd0b070e36220f08070521040506190c02031b0118060203030c0a0c0c17212d1902060a02131517010f05011d03030412030203040b03010609 61
    0x4114501550310035500204400b00f2400c44032150800c01030340c0c130799002d85045651100032030201046c0030105600d64442c04800f00554099840c0104040c0c01e1091084800c1080810510b40604104000840c2005a14144228006440b64424034400c500900002404c07a0544011356015031001e24000c00c1100d40c00b00c240c80d0040c0e0010b80155840049100c00c68100d20310010140900504903c0002e101000c00780c161040c510900645900a00c1400c0581c0030955000320282c401004001610304004c07480c0070800080c80142d8002070040406c541c100440d000304540c0821002c4500780e0082d100e07010080b00fa40070115003002d5142145482484038400302e030784144c0044400601c10440c440e80260803081e400d5804c618242c03080e40c0d6982854500c0f8038680b1509d070210f01c10301d0f0325041107400030000d00e008000142c011441d0501d040170044005182142c1502180000d00010a0850700800114002c11080d81c5006076a414404200c0f09031000221411008070b4204030920400301040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 254104334 1250 254103084 254103121
    0x6180c04091d0d0f05043605041101080606040308180103180f06020f0f03090703060c050427060302030303040308100e06281509140d020d0b070e36 65
    0x2828200040801384103035020f00481d00005800381c05000f02c820000140c10004000303c00d013150b040c103049200310000045810584025010f50548032180d5417030750141c014950440800303800503141c580c0e03944a454031504021544000e4100240201c485503a00d03000d809030800b96035801660252550761855041e028074500209210b40109000003903580d03030b00c140d5080c41400d03524241e481c41c0c502d017003540321b400e02c1c007003100c10700e20f440c010100c518414030a44003950702c1c400140310360356540400150f1843d03004102a4005485420110044c0c40a101550080303200783c841204900380080942d0400d030b410303006000031800b4030040000f03d9441d424a414142c2898013604a03207030007014941c021800070340080300043c0000c0144211164051450300445140c801200c0e0031103060810444032184458019600030954080800803c210101080d04552142018096035141e6030100e803041808a45136100001d102952000340700b0071500c1005041c20080c0210000e10300800d40101510014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 254105584 1250 254104334 254104337
    0x120114010e0403030605040608030d050f0c07140102070203070b03090105160e0f01021c271a03100302040906060302120a030206130f0602041401120c020a0201030506180c04091d0d 79
    0x5070045010300d4065405403000d00005881403007519162034201d0b42e6640140480704d04c41c7e1500000400b0303c444001001e0150300c5246200b0f14003152611a0349682200a059410329503082000c00c0040e601000031000900700c01d10215100d00c0c11904407800c480004040d905018001001011002e5102d0407802c0c0000703085444d00c100202c0d050040703141002e48a003402007010380c10a030219042c4c0240200d0689043e00740c0b000c0c4840414545190f00e04414480c40b80e81814601d405070302264160003a5510403001c078180c9629a41d29000507040c1c418920055800d1544c0d20000d10650034070011640c10f4002c0340004102601c01c03664020740d40d10004180743e00100b1204a03a80400c07500240d10200146c2051040d51030702c1c0c848000c1e1584074200810180850942c0041d00d5005040b03000f0707065945100e40282c109007110350015409043c00600f141c0d072085202c5241d10354560710840302c82c00355100d0b145175030310745080c02408011110806074420311010011400d4071540300001d922807222509 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 254106834 1250 254105584 254105609
    0xa0e0a0816090203180a080c0706090e070f17041104051501090e070201060909080903010b0d170a0507060c09030512041206020702190303110601170d0e1507030302070212011401 78
    0x960b12a18021024084a43c500e8046c1c00540f60902c210840901a58511001170350f079000e50b500001c1c2c4416080b88580c800300d906810004504502580b50160034076200d0600c0032118a00d0764004003d06004c56048900d10891181408182018410319070700c03044402c46031185503030a400107800101e26200b4204004c95000014074040e20030340180b0700400002d041840488006c0c40c010700e00c1d4204080141c060761a000e990115441c0c00d040440078181c000450b0b000c0e00401002c83e980560015259000707004e810400031001540c1e40c4140101c07040749560b000200c900310314240b81002e56150006240d541e06001c14403135013103102c4404c0040d6902a800607070303894841c800318600c01103218a40082d1842904000241900810400c000c01811707021703616160789640803c030008031040820601d50380001030404905021b4008400c100100a1140b00c003541400d50f28101ca500c46602180020340100300740046042400c1c1c84100713840d450000f803021200c0e485510074056414484d04045020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 254108084 1250 254106834 254106841
    0xd090509040f060e0102131409040201050315040b0a2c090d0c020315090f0f06040c06081008060712110c06160306030804060c050f0a0309120312020a0e0a0816090203 73
    0x81da0b40a9007208540600a40d00c61020031a03100c031f000c02610810b8901c4040e46c544c4000d17440d000d45014442c84d8161512070840d00c0d0802d01c5c24040d00f000d9046900b080d03641c11102030320b070b8070351614200428050304100d0b0a947c0040c9020b46240c241500054040c080314103000c00d525002c9400c07a5444a2403421480d504510b0000900d8128001082110205550280403680c4000715150307008950301800c8460190740c198003190303580300484000d400e0319411241401039500c070300707d807640100b07103d5080001c036a01d41c0c0000d0b0900724140c4421003c982c0d00c1c06850460496030085c01c0c00c40e0840e500c114140450012641e0300c0c0c0d0001015542c10066414172220b2190081d4490000381d03821201c2c091300c0c0d50303c0c1e180c0548102da43d24402e44080c072038200c004005200c0090115290341e490b903100da80c110310b04802074181811481c0c04400340a02000102c3c1954102d00c041c000c520354940e43c40343c41140700014480c0c501c0076070f004910990020030701e030350b20850b54440302400c0720071091700140c0da5075 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 254109334 1250 254108084 254108093
    0xa0201230d061502061006080109020c03072a051c080f2101231008061302070501090c05010203070b160c02040207111c0201140307022b020d090509040f 67
    0x480e00310300c01e04040c038041011074003a402d80310303800007400513400302ca80b43d40750304244076071b45100d83c8124000145500c0052103000302580180084403200c00450341403090340da5603564200c94210410203005030f01c80c122034814400340d031000000d210a440205601e8410300c0b20580d0702c61800c001074034011740062220300e9401728a049807a2080c101c1d00241c0043c2c000090001440c5080c440c440c0365008c1604183e1401c44010010088071800030440b01c803c0e5800001941c48401c01411035602c80e9408078442d02d4140240004c0510303d1044000040701c01c5146024140f07189643c124a04550041c840000020511041180c024032440c280700d1190340c11510888542c403060b280290450b001248107001c00070700560a0381e50314030440c0d502e10060b50701c09800c03144070a01c0b007000c0d000400d10014044110700d040c0045030004418415280d20081c0300c6411042108c0a0950031640c8141403c01001d41e03070f0601401461102c1407034070311442450440015489640980094912048200c00c0405c10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 254110584 1250 254109334 254109337
    0x6040e0703050a03260601021b04020d0f02040906120c060e150403060c320f040504020a050d0b03010c0e01210510090b040504020123070c03060516020a020123 70
    0x45038000100c6411486904d0010070100050034510500100c1d080c0304409a131424002030300c0740b58180c0c01001d07800002e000003c4d04901c20001e03580c02a908011a50200c0158007030710050080c0108050f91701e80c5041035000444a82d07600c01040c007801c480c050b07000100f480c0804000c461152030802ea6219443e0000340000071300080007000c05c000050004100000750308680130003a0b0640390040a10000c040107452088400c80d00550106c01550034840000f1142c090041055107000150409444038040740c100c1e4403150280380494004a4145180d00c0780f8040c1c0500c148054000303101045040740054205c1520070315090501402d48400352910580072440d00808903a608180400c0c2041d4003003c60b005c0040c0240d1061030b013032000700d003c107040500030a03004a506a4070005140c034100c006038503402c005c070100424807504200c0c0c1400714111544c80800395000380000078090034a1070f204844400049000e03025500510b8203000940c2c2c00c80744400c4440940108002c2d41c20110244080c0d0f07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 254111834 1250 254110584 254110589
    0x507200102160c14010c080f0c0c03030c03031f0302060403060c0c050607200a051b0307170d030501080c2b0b040809190810150b03070e0306070e030606040e07 70
    0x810034900d000700140810b02c1583ca007240c1440c0b600c1d03d030007540040110b40b406401c100240c40c1c01020080000c8180228004104810101d41590102040c510000307007954000c1c080100c1c950700c0031080c440c40300b06103861705690403da544461070161860f40851050700841c400501401d82c3c0310401c010407803703068030b5172600b9030000039500e8920b0010700142c034501c8141c103401002014a00c024400d03040025104100700d4214008103040f00d10501814000c2080c80c8034250036004480c1c001072402d083d40242c010841510000e0034015007100d90050840e001680284c40961041141c401c01e6200d905054440004940c1405003c11003441c5100250292602c0140a00803da00b00004d001c4260094444da4104440150740111404030410b203c20716801403864640010b420354049480c107500082025550f030350081051559100c00d40010741080f504580402c44141194429160512a0650088484c10034134038841c00c61002c25030f950380040c84103018642d43c01c1c02400c80d030f1003003041000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 254113084 1250 254111834 254111857
    0x6030e1b1c02041b02060604360f0803010e060f0f09040804170a0215191b06050a050a1103070e011101110c1b030a020d0f0606050a060e0109090507200102 68
    0x1192000f4604501040400404c90060140784003050241c649801203103a2121412088407110410b8008403050440b100d8007100c491081c0201440051820425000050b0141a020b41c8070b6140c003026600550008260601c203e803001204050b91b46c81d9003c0440c680ca0603613080c80c140d034403494180c0061050b60020032024808240901004200055070300203a8400d44e03040042c1c01005049410364011045108215160071001c1902c0903c2a815140b0034078924101d0b143d00f61141d1240c4040390401d03524030f03800513103850402c1580d0801e03006101e240881b1071011440c518250f4002407888840c0001e450402903a804401d120280940061080c1c5601c051101c0d55034081413042540d030302045545d070904010940c0741d002c5a18020500100054001d00401c2d80060380e5511144007856441c4215000d5079540c4020030551221022440504000e49030300c01704035a00343c00504260075941c4602c1d1418284410011b14590003a604498000e0b075106420480100048081c00380c012070311084c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 254114334 1250 254113084 254113091
    0x5060f0a090e011103090a260403031706030a03050a0c11060d02040617010f060e03010e06010608010914100302040216080d0605040507030c021213030209010e0106030e1b1c0204 78
    0x380720780d05502842038250b0840081007030701120030312094180011502d8080c26040381e00c034080401e804409281540030109242d060384c9070740d070b80c2010043e0002d030800d4000841c4041090f50a0740d0ba4040d06401080c02c9004140d02281a5001440c80c8140d0700100200300e560341030041080014514240c1c5904014400ca450b40030700c039031400094101c0e20606000440b03e41c00c5c3c80d1100384540303049043e0f80c9494082008641801b20544400d60001c10241d010741d0784545030f0a21010038013040e40070382229030f00d100c03c0354503101c5441705640e45040100d5030103c600080c04224442c0c960344401301c0e6415030307015032034544840500324440012040502440c5000480101720140c542c400340c199101243d0800c403a0302e43d00d608800300c901d520408405684518030030110031701400050240c007140d02a8180e05561240e02160303055400b0307030200030b0307880c1c1120040c0f01791a094055101d000300785000500560411a0400f0283d00d0700607142409821580240d56422041d0041348400326000f50092 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 254115584 1250 254114334 254114339
    0x1120525080105091c050a0e01050f0f030f01050102160501021906143c04150e010c021606030b06031f0b07050307050c06160b100e0c0406020c09010608010905060f0a 73
    0x1394071200044c1c44841c0b00103a600d00504ea0500800507034040c3c020b5981e4003401d02140720700640d0705600010051802d0074050000051000c40d040040d0311608540c401c010704da5142100291401d5821040c600c4490070142c07003804266400146070041c00d600394403800388604581048002880306980720704044603182c00300410704114900c48080b0801c0408000d0400d071407405c0300f07000e45400c20069002c1c100c0b40342c042000b0840e5907001154403800b80302d00040d00d40200d6245400c42d44030342091409604a11b1400c05001e044050000003802d03a0b0501380b08260350a000900310b03200040c101c228415201c140d00c001803190b507030b01038090034101c1d00c00342daa40343e1410030070307038980004000321070620410040c6030450502c80300f030b10410b9840d001051300402090780c030b003020500024a8615202c41151000810340c503182c50140c09020040541a555400c1600017400d2002800045002d03000a100401c10590712841389811507030b0b8890f001031240c8624000401100122000300d0740300301c018002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 254116834 1250 254115584 254115601
    0x130513021c06090c1503050c120604060b03070306030605150303040e0c07050d0e1306050f1216031110030207110609030a140102041509051516080304081201120525080105 75
    0x130100341c0301c000000c45000308010074101d0540b84100d450782120b4a0600c40788030740308103c81040360003440c0100007050702601e0f401c42c0e02c46908201c0703003540069100c1000304140001407007255088a502144480f0040551001c07940c0d138070551060202d04450400080c5002d4071803003e40e103800350304c0381c00d48810410b1100018a19440031881e54455054105400f80b140c0d07241c86201d041715000341003d28000085401c002c00b410616220b401f0743d000340c401c16150b1380d040d645148080e40c411004407480d84054410301031415441020300080c54410422178000c41c2c0c0052503800c0d240e900f1208143d0300c904250201c0e0070038220860080c6101d460300f00309203103440107402800a4484204000c0c40002140e83e04542c1d05841d813044036005054040545036031184d110080c00555031504c4e44540240407561001c62503802210306440803140440c80c511405030b4103107841d005201c0d156074001c11440f6510b41c6500d0303142c103a640b02c4030011504218603180103000d02c1c00c401044600000c00461034803401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 254118084 1250 254116834 254116853
    0x1060509010528031a090c0c03070b09070611030c0a0f080f07060c110a030e060307050417010f06121e02040b0301090503030103050712150e0703020a0b09130513021c0609 75
    0x404400f03e4145a040005d01020420310203100744000c1181341281c813040540e0166911800c5001d04902041000401060402d0815400794138100000c1c0b01c558a810001440100442a804400e0300200141c10680a00264611410341c209600d5080045249041c1000c0c1c0318607070b460710030700c0d0010402c40180b0626a002081c01e030400e8843c1002c1e186e00000c6c9a80340c42251100802065000492448500b0028003466010100341040c1c0d01c2c1031388800c04400c20b9070a0070700d0341c909691648034500b0303204071500910006018020034000d0038561030781c40c003150b107184444c1c81c44c903440214131030410355856421100300c01d90064000c1040400e82e00b00350b84ca81d80700740816034603807162280c0040c0c000004040c20682e69085102400500d0101c00008081c0c102416109a0ba00c10a40e01002699a4000b214014100c1a0103a07903166105401d10200002c240c61700b100c190f150100300440c001c0441c1800d0314660741218010001580d040c64882c40c07114503031002d003140740b13440300030f6003088035540 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 254119334 1250 254118084 254118157
    0x80318030c12011e0c0203161e0f0c06020304051003090f170d0605120307080d0b13050103110f060d11040e0f0906090d0905090603030c010c020102090415030b010605090105 76
    0x130450040004a0905100b17458a680d40340f40103030b0040064071440c0c1c0207082880705241c451451201016a9624682ea120080b00710a0f540130700c00d44561010000510218001440103002540c2003601c3c2c03000090115030003080c44001d140e15003015800b0002c075480307412100da0380146103400400303d411900210b500420b0b070400030709240c40004503141c94110a54401520600011890303d140e0303070b80310350854003c15120041241c0314080000c1d80d0340c401c82e0448070241f507181d0002e010361460034188003032400744923060302441c208211031a01d03845680440385030307086040c004070b80c1c2400030076100c03281d2003503521401103c40340c041440882c0410011690289102104840942d100d4041240e03c40000700810b030041380310140c003007281d030401108003580104020166428003491241c11070170360340c012142c3c00c0182d60004180f81a49858032403021480700b1201251a001d00310f80d110705982e0018012182840004121510241c0c0b007501125440385110400308000c2c001c01c8641900040c003103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 254120584 1250 254119334 254119361
    0x71805041a0c0d0606020c010e03070b0702010c02030a05070b0307030f0e0a0305210a0603030905060424090b0a0314010f050108040813031209050a170c090604020c030c15090601080318030c1201 85
    0x1000c40703012b4500020b081c0180d0384c20068a600c0c003452a401034070122a0341200702d800d030007648114408980140f2a48005207000860250780e03182022009040b28207210605003482c0c6008089110564000707114011961305044c41ca5691003c0c100c2034561360420003d4040c0aa004400c0260500c0150060700c1128032a48507014825254001c01c1641e00032070144000b80540001c0030901c6001c01418904080e09034181418500c0c0c407002c032194264010071348140800d44580d4000540c00740315030840d004101c1035089403411820701000810300c0b0fa003e0000b5040ea50301084152207409041d2000f4000e55121072561402a00800007800941c401c0c45283c0c0310b69194000090070035906010303113442400b076102a00c88008004200012007401810103a04a82d09103c1c190340700c0e80400090800111010007070041091449032800c844100504822040c3c10100c0100000707180041991007a0040c80c0c4001c00158120000c00d1514601c00c4030a03611000502140034005010b42c030446071903124 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 254121834 1250 254120584 254120597
    0x309030506010819030c0c0e0a0e0d0e13150803030924070906050705011e020c0111130e0c090d030e040507090e1308071202071805041a0c0d0606020c01 67
    0x383e100c21600d402c0844c4003000c4c0448803214410010744204403207a207481c0f240c64090315640d2500203850040304d0844820a410f507403140040100b100800041d142d8026501e413103085400301d040800d9040b1111b051050549031140c0300e061040c02004109009007c2c9841201e40700d1404151255541c486000301c00c0714034a400078401180c03070600404072f1140c541c81c0c0700c12002c14900b0760101e0b5a41d10000b0181c1d180d560304c0550f030441410186074030315109598000540c07240c803820b0b102c44c210380d20800a4140c1c2d0104010400116a14074903440444410441c20009a43c1c4d00c0010ba45034812a400a64405002c0141d1020550000d5002d98070744001d881c2080350740c0d41d4084c141c55504041c0205001d51101034000340b80303030105d804604440b43c804e10070b40f420b04041c0c0d0340b0f080c494401c43e5040d1026810012040c490074074101e00c045a4020303a03201c244070034141070302d03046401007424a84015840000c00007034803034410303541280e0741a8000d44007005055a00c060094031805c40c000c019000481 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 254123084 1250 254121834 254121839
    0x3071805010207030f1a0103111002010204050a0306090c0b0309011b0509180c07050304081506011719090f0b0f1f091a06040f0303080f0108150709050d030903050601 73
    0x1050048001950010707001000300a040d92180360741301704444003c9445003a10750300d1001801c2c900c0b0581d03008500c501d160740b08948058080080c3d141900320030501f1684103100400c003030343d5a0780b845011203412050016400605040c244004201c5c0d403c00400020300005201c42c3c00030552003501005801800d050506c440030f03c00b143c4c244116114181c2c032104081240341e10102800c00341d034225400d000c00c14070300b800a035101811500320f0f500425058201000443e602241c6e40c0c80164003074024a04100c240304034952140444034003400c0c40c8404e20031230503403e4402c003440c2d01058042d034004c0c200c8100148140b03001c10050707200b103408400080044022a0503003100b00c4c20786902402036803289110500300010100140110103240301c2d20504448600641d8468200401c041d114014a0000090a40c00c004e44a10350161008210f41c40c0b28004100000c00881c1e080b010702e192940b0f0300d0310313601c0c0d51004036a03400150304070681c03110039100c4003401c01d5000000301045034420350544605a9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 254124334 1250 254123084 254123117
    0x906040e0f0604080421020603061e0307080703060b030a08040303080613110702040c1b02010c0f1407090605010c03050a2106060c0209060a03050c0907030e011e0f0605030d230f0307 80
    0x110001b00080d004802030000c07a109140c00581c1c00004880c23030020910a03074841001900d84506684942c034142c05c40c40f800e001740f140714020481c0200003500108602101c942d641d0145104070701c40036081081e0300b4042082c3c0e685000911044807024181030008400700a800040f650006a089115519000300e84141a024010301154120b85200700d42c2d090400750015902d0758405a4111140c0203984403540c00100d80031080f1080002e5040100f1416040c907050600703c80c0103070007141c103200d42c606a8034002075000c400c40700150307070300e00e41303151002811480002101c50b810100e40f101414698085a8140c1c00b403d48a24540200c0d601613243d11a142840058582800040c003d6002403102c5074150410085942d0414030503d80094104c040e160748030300310358010b0203a414507208410128507004084c02407100d644d0f4818030030014149800d0000341c0d6103500d02c050605018244540521800c00f0807203004602030000c107402e0ba60407441001d0801c41d170080319400046007980d1031540050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 254125584 1250 254124334 254124389
    0x301240f09120609020907020a032003030c1c0e0c0103060f180522050c010e060a170a060305010f05040b1006050f18030d0e030d020c0906040e0f06040804 68
    0x103003030a440740c0781082e0401c0b00c469450305000038140d4a05841e80c60002c0181c4804036003e1041803503a000d480c0c6480700c3c1c58020800070f541e00d0241826204c139000498180e00220451b5041400381740600d5030b0301503845540e5400348a55416500c0e09207080084881c25002081150303801d0301c00d80c1e08010640d206c1041803500c030501c1c020054521b1200b405c045244c006907100c1904503550a03015000d03402c283c59604080c920700b000407641c07600700030341680c0c031035810010890a00004848090a00048070703001444040c0c00c103190091210000085203501500d07070b1140001d181c10070002e1100c0e0410302e18200c080c26064400f00d0320304d00b11100240407003c4140c80c110a03207072540da4080c40d04c040d800e851409a0000c155040d02d4031030ba880580c41f10b940400566620701003a803036680301900c01008050604800307044500a40d08020241241c6960301e6040700c0e40240b00301c07000110b003202c2d2107050345421801504401c6920131a81804117028a10016000b251221103850305420103544ca0704810 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 254126834 1250 254125584 254125607
    0xd170d0b090708090706050421030306030803040507240e01200304170601080c1804030311070302060601030e06010501020c0d080c030412050f12070803150405010902220614070302070b030124 84
    0x20701d502a0001c09c401800c09100d03101c00c3d006c0e01d0041080e9032030f602c42c04074960003a50101c88592081200300b003101c3ca1100704001c40034079405405550960400091b2440003501c2a040c1000841208040003040301c00c4112070201c1401c04694480340c850342250004c00c02560545191b00c40c403000040c11040004071300ca42d800028140304020080000c00205000c07010b0800c4050545407071400d003007070041a01810041d8001da009020600342074001508961004100c030300c440d0880801400700f40d03000034030502c1c0c0000a0301c0b00c030002100e43c2406034a9008880d00351010b8000064000703a0900342e40c0783d02e001c203805203041e90342c0c2c0310800361166a0782551110140f000740040c0040300100c5e80b0407000d5513024240900e0400040080c10000d4101d070390176080010910344c04900c0f5040c0d007500d120f54040a202c070f400d044e050b2900b4801d0191881007003800d80d010f061400108001014400d20485000740354031040f0f0b0761296100d03035031311811889170a01c2410071040f103412509924480c1c00c10600 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 254128084 1250 254126834 254126849
    0x9030c0d080901021e03010509330112020408010509070602240402060909010608150a030807060b1309030f0305160c02060903030705030d090b060d170d0b0907080907060504 76
    0xd154a4800548000d074000701900e5140d5805d0240b54600980b90714000c08a80c40031103401d50f80d42c18031080001c0c002002c0c00c01d0805013044580855014002883c1e140300c10495808040300e02480d030012100e6140741442214558004600020304281c1500720314050b14108082e1099152100c1040741c1d940301140071080300038140080d030f0802c0100d5190a940250028007081d203807100400216108034801e0b804880090030701000c01c40400d41a201406580808995100500340365440303031401400388502c00b6010365135555040c40f00fa03031303010a00701b04080c00d84000d02201003103003170103030401003124916000b090170f08000401200303150420100d480c0c1c19845840c0007140580a100c030a812035070b103442d014407081000c000032030400c202601054400070b41c0851490103501e403840c4000d8010740110300600c050403201000a40c1401c81c01c0354401d006003a00e0301e03443c1074130160020342050482540c000395054140000154050a480d01c255110412035070440e076186011901807156115882 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 254129334 1250 254128084 254128093
    0x9110a17030d1d031201090c030c0206191b020f060a060e131410021908060303040e0a021c0b0a1406070b04052b03060503030a09171c0207060809030c 66
    0x120715120540c80083c0f001242d09014114034000c1119919681c040e0601d0078400b05200c0040181c41e40301e00540c020302031203240601140d0152100a07527511800740c02901e03001818091150a811603600143c000c44d14100d80c1c10021541c08006034541003100009059030090f2800940300c09480d0051404840407400d200c0b21640d16030500280303403508440100d81e05d00420402c0d80e9988010800100031313451034100140e49001c04c03000010400c10403140a02409810b000304001580e0100545007100d54035032a01304155038000100d0300074460800081d88124030f21410401810080e4807002d04e44100f07481c03c80c80c280c0c0310003140b141e46400d08a0594013020401001d00003d01c8841202d8001d4840e00844041c007400160741650103204081400340c4400307040102c0030240e0b05004020080c203065010798644090070f2401462401c1c10f00442215000c251004184800100001504001c4001c0256143c2c800440000d480300c1680c81903000190001c0f0108042000100407202104900802130 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 254130584 1250 254129334 254129347
    0xb090c0a0b09040504050a140f0709050f060d0f21200d0c03020703020d03050307170105130c05090d080c070506030610110f0303040b04120e030a1704050409110a1703 73
    0xf1000e840020400c507013074001c1d401034600040742c028020344c100d07140c01c018056071292007034040c0c0f03004a15072010700090708010a00c524010083c0741a41c028409032481d100c2c25542c0e00702070216160001c0b004007840d92107406400e1500170410b000e5600704080d035800d4401c1e2078038541e0390b5441c40101c45405a54016101010003a80039194062406110303005407194030350349400081100700ba03d40c0c29400302d0b00000c10007081c01c0d4032a04071280d204100407106403079410000801c140070742c80000e8806082da10a03107058001d0181e01035903c5203400034854080f1543d0761030810a1a00a0580315401d803040c184041380034035010098a21a0501500c0c00c1c0007421011000c0b20b2008401d44540d03824081d884440010140034001140300e2401034910004605041c904511540c030f01090300e200704440e410314818541c1d40480c0c115065134012028420140082030380e40c102d0311407070b485182c0c024944203400f0208000f0242c0540d20100454001c02c00c55541c081e42038024045881890340ca80040080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 254131834 1250 254130584 254130589
    0x12030f030b150309010b031203090a02060304140d030f0f020a141602132304120f02070f060c1a1009050406020405100518030d02070306020915070b090c0a0b09 70
    0x86000e80000348095120000c214000c0219031084d614801c50b80d445110a51841c202084000c2c604400750806a1551504059003511904180c000a20428000000c10203100d042d242d0956114030500c240d8a84c3c0c00901009002096508100311145080803541307403500109200742c404182264556070b0f07200e00c40b1584200143c4c0908803044090600c02e1128001d625801e07a00c0c50700b100544000140951403041014040992005c040d150348000c40400002680c0000000b80700a0710703044c0100517800003102a824620640c000201d907a600c104009441948400041d0859005103044610300d850800d8480c10940104c030a4030a1440c010b10810182c3c07034030351007183d000f409501c0c0181002d07150700c0010955000010a41c000500106542d011086124404000500c04400030b01c9540c9440001030340f41d00c05803101501641d404201410152142440840c40901c2e9280302a0358a145140641c8a58010345d10012540700c0e200010105041042c1c0c54400c3e01c1c02842041c1c100203201e001c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 254133084 1250 254131834 254131841
    0x3180105030603030c0109050a030e09011203030911030610060909060e130f080d060e180c010f030b0a06030606081b0f0307020a0c23040b060412031e081012030f03 72
    0x407950103100410640c180e80c017082c80349026141c400c4000c0e10000310344d400d0003403071000707140c601900c01c45100700100480c1030f003601c052011b168542800725002400c0c0c00c0005203402100082600742c01010100420f0481c480307050020745406444004109846502d82c9044408600540d500c0981c2d0b1008104000340d5140c20188076407203140d4045849055943e6244070303820840c000301d00701d620f9400c288103604071403c44030fa1104546c92250240540203180d19aa40e902c1ca0000341400500060741d0b0302c091094114102000d009868141001d80d1548020010000e52003280000b5802d0401301301400910307004924801103034001c260070151680205d60141c0d02c050654000e52081300c4064000403602c60288004209844080012005e04001c401c0540c6141010030b11a40c079040c40e8144540c1c07450107a0b002d60384403480700100800e072860155041d143e02d040894442c0a190250b409240d40209180e114441414203d4142c030b54a003031107490249602c03001004a90040d0751942880d2180e030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 254134334 1250 254133084 254133091
    0x52e090e0f070e10030c08060709050906030c01050904060306050f091c02030406030c091205010b03070902090a18060815070e06030405060a0b061b0a060617030a0f0c081803070501020318010503 85
    0x6044c10590b02d07901c41041112a610816003900114108031800c1d4000441200600040d00e07000390502c2d040c0002034072200101d40560502034085200e2045803101c0d40160003460740900d0800c9682060540f07501c42400448074110f207417203a0229480b220222400341d0a45030034a8000f141801c1c18030300107a010303003030781200c80040000368203000407600eaa043c030342c20b0313028050400050306009240516007407080b0303034011503050742c01040a030b40103807a034188070383c01ca4611585d00c0c0300d2a22031420354005000554804000780c03117001030440c032004645d0340c0d45010305601d8441c6032580440d18280311150008840140c200d810100000350a003e0325000140340342402424140703445074940b0311003090324102c041c00c00315a005c01681002c100d0130b4424840a0018a0800d04600541003031042d03880c17061654010400004000d082c00030381c040c40d10a01c600d40c1c000314960700d8901130170400e120b18403072540ca50302ca0705c1881c0c00000c042d4004011121042141e01c86000420103420056a4650014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 254135584 1250 254134334 254134351
    0x151202040b0a0b0c01052511070f06080f07020c010c1401140a02040801061a0901050f0405060403060207020103140709060c03021c020d020d0e010203090103052e090e0f070e 76
    0x580c500c801c0e0396100140700000e40040100c50fa00c86034042811801c64070001c042041003901200600c1030319200002050320082589450740901d21060700890800d515540100d00e038092154002c03981c07640020141d803003441c00d1405911a42e4a002e03040781c0e00c0080c8511140403c4034201040c000c980c500141030240340d4913000124038544400748146500c4000c0750340da01d04950100d401d1102c05030a000e034100411504070310180c0c0f800e1038440c02481c0c1c8074010505051001c0015400300c02d01c8141c080d00c00800c0010070a83c3c65aa503400c1500207036210110890009242400d80701500f4003a18100e401140c2590310241c1320340c01d140e001d03078044565000541c15885442aa500144140d0751200c07081070940e40078202a540441c0068a4110705036032800502c2120b501500ca40c0e40c0c00025180460024600498240c036004103800f803010f442c5a041400942508001c8441b01c03080d0381440842d92807000030842011800d51090300c40c2147c070302c200016000301d0010044000001c45281e0000001c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 254136690 1106 254135584 254135591
    0x7150e0306010806060120010e010605040b0102030a09150c0b1003030f301b0e011b020303030406020c1e25150c051612140115120204 59
    0x108042d04000c8030809800c54004001c0d01c441042c01c4000007004031301a689c21039400307440d032401418015400c1002e01300f0154800000c81d0000c1c426691405109401c11003c206c8000c03000c10070b00b04001c1300c1d41018010561418100e80a44c01465170504414a035250160409428408500501010320b0002c8400b0380703412913540a1410040050141c003050788107480041449400900d1481d180b115440e034020303000142201c000e00700f41c84203240c0840025a94000c0b200c0c040c0000e406400a20200b00054081d8003e000c0c1c2c110785d00199201151044ca41c2121a1280c0407481c489902107403880079400d03000e01c2c51040f00444812010031f0780b420080c40300c2d10480124581410444050b0a41d0144501030081d501484000200e40e01c1081c3d5840e914010381e243c1420aa07881503c5030004143e0ba1014841d0040b0000e40c62201071b19030303280101540d910740f1008020380c3c00644 = true := by decide +kernel

theorem cover : BRFrame.Cov 253956834 254136690 := by
  have h0 := BRFrame.cov_init 253956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 253956834 ≤ n) (h2 : n < 254136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
