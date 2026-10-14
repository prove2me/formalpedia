-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3274
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:10:42.550005+00:00
-- url     : https://prove2.me/submissions/a98e62d7-ba61-4350-bbd3-396c595bf947

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 588669064 ≤ n < 588848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 588670314 1250 588669064 588669089
    0x31501142b1101090b090f0d0f050706180806060d02030c0a1d0114010c0f0602090a031505090c0a090b0d05060c070c060c021503100e0a0c0305060d03090b0f090402070c 74
    0x410300150b600e8407090107440c80300c1740280300d040701074205020087c03444080100182d06030203990b520045891032440f805c0710a0303007080b0010802c05401550300c1443d4450550445d4a13281041c05a52f40d8440081600e4410715100e100a419910f06100c001041c170000b5040094040d02d0300c18409a440841040410680c07402c8000522460440f03001600500c0c16501c0d40c0c1e410b03055449a240d020030119003074500690800084515070b480e8401c00c3c0c0113610903404d810f0340c0e0070070080c11000c07210004c10b000745a8012900c5144141d9940c014034050715800d810000d40c0307613071440101c0d003040d400b424020502e00c202c4017071000010b04680a04a444d01c1001c02055080c0c880350111165401c0d0500203400035401e0100010000e64207010f15804880a82110b10003562164460b150010550b800c1202035552a00aa50f195150040c158046015101c02c9070101040e900107010b81640e00c42e4408021317011030891000d0448104031000c0e07490042007075440e0300f1703603040c4230301181414841d8030a07081a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 588671564 1250 588670314 588670343
    0x1140312090a0e100f060f180807151101020d050919050c15070510020a030c1806030e0f0f070612201308010905010209090105031501142b 61
    0x10340d0800c4901c80c600140c841c11045161101101c1c0140d0b02500008a1218141d0040790a2840c00c01141c000d200740c6d41d03489280324425002034414180382000c00b01d038400d142c00c00c0c04042000142e003030031540f600160b080120690642203600810a075001d130580d500000b10303421200203640229004a01c02c400380c8999181404140e0410664254020690303000825000810302e42800260450038661038024078045940d81d0342e90a0154100504248950125088950603814807800c1405001400c080102c00814182007a10011030f01c262800c041d11020410a01002032010f04860103c8a003100c0d003001a04030403a0311040c1d140141d00028608010000c1081d0303180c0501110259031012600401d451050300b501158001c0600380e078090001000060b582c08244200305103e4007403000181c8412001042181c1003030181e2015200b41c0c0444400710300c1c0f0300c00c100002c2c115040306100380000030800b004121207900042c07505090107841d0444102d5010300f0b041038000103208290703101c2d0003003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 588672814 1250 588671564 588671593
    0x30609060708070302030a1d21090a03060f390815013902030c010302030403052d030103050a0302010609020c030904020c0a06020c0714090609060405180303011403 72
    0x40031141c010004180d500419002c0b03000e0303801181c100b60a10404074001d0100214813559120b40c0c1c00116490707120034091240400c2c5044610500d44003640d10b0b074500140b00c40061072905560101410007a901c902400136101154031404c0f0074840005030300810b005c45025010800000c0030784c00d41e8800c02088440302e0300e01c0340c441c1e02d00c241d8803012040f0030030003042c004640c45002c1d40950110030340403070541080640501c0901081501056022421503080e02c14036060030751002c1c1d00c9050500600600000035001802c1d86c84804c44904c01007090420401c081011545842922204c900000004001e008000c0380d92840c0301d029800a00186640300108000c030b03c141c01c80494140c0050008030201d1520390010a02a0240011914030310f142e40c40e01c000f26405800d45050340d40c8902e60030072440c0740d18003451410150442e0400418544400461110040105100d10855540002456000f40300000e2307404c2d410f050f801c0380e07125a12010826401c84c40b801d9864030030700c5400c04030103591 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 588674064 1250 588672814 588672823
    0xd050703020406210e121308060c07150902060703050c010b0109030c15030b0a080102040303080108070501050304060b04090f0501060821040608090a051005010e010b130612020d02030411030609 85
    0x54405544d6009008203401e1180720034038101c0a101c010940300d02c0f54040340c1c0c42c208802c41c04c045c0128040355950310380109081c0b484d140383e0310144003604820108520541c000b01500c000fa608458654124004031081000429104800a50008003c542c403030905074010082d01c10003051800802141c00c01400560b00c00c10140300090042c200b405e414844c8112046a00c02444001d08022800e0800f40002075203e040540012219039070100e030401c2803503402043d2500508026001c1c18a03c1e08000008000b40300c0100b010303282c80d88402420030a074640350b01c1035030722542252903255030400c41e240c6039020300403a1040d1185803080d41d250098001e0306c00d03110184000034501c418a0706180510641c3c94036801001400c2c18000c00321300c803021031014850450092240c1c8000561907042130740d045500c80068104900c03541e0180710400c0a091700c0d21040c1c0658040341030400d01d0002c10000c0304080d10400d07001c00204e90010092204200a190010766004811410b42d40e450340c441c00c1c8107a0f20f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 588675314 1250 588674064 588674069
    0x406090504090b1605090301061e0b0a08040221060a050a0e150f060d0c030f171c0f06050a17070602010203060612071403010303020d02070602031c1104030f080d0507030204 76
    0xe040480046041031300401440e042605003801e08600b0301544400103401c48000e0780c0180e043c0c544030480c0d00c24044030110008040e01c07100c84c0c4582484001c850080a05100800013401460b000c2d0449480d00001d050b0030403034990b00c0007110042d1a003004000701811098031807150700b600742410110041408960b4482c2c03403410420300c1409075185509440c404402405158006101400003c0403584d40c4203410055030144204034000c1e011864201441074410f0403040382031005009082d00079402d11044c602c80300c00300c0c0c008900d80710f541d005c801c024241607228a520011421001660f80c10036048002c81058060070788841d150b81d40410303800e03807008503440c648c461000c00488400c41c1071129100c1d04204545449107401020500d280c0b4564020b0304185c02690007450010b81082e4100708007409405c951006d5814011a0002d0800c0050740780e9800e510a5181e8100c0d004130045441500c00443d00a9020704400ba007504041c24640e01c58000095024140380000b5943e60103802280c04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 588676564 1250 588675314 588675323
    0x503131701141303030504020f0925021504020d051509010905010f0b0105040506030702010609090305090418030503150f032410030b04060902030313170d0306030b0a0b1f05040609050409 82
    0x440fa1002c2d50101c00a0000a008036070280c010801c4983d652191801240310f0803001240000020410070700035088103d40c041c15085600c803c4001000b20356600c035164205506866100700f0446918103281042e0110003518201c010410230003003001d60541103110024040c0000304190f50a140000303058a08103643c142c00b01c2d00c10042003205091060003542d00001b148000951a074441c8000c90949a81c1001900003580c00f18820303501c3d00d05031050b00610f04140404117001400341e034003d00700c0d010080406e0600404895500c40589511610600c40100201562090100484505030001752000c4182102c54100009201111840342000035260805289885036450341d6480d0301a201c0401c04a80600040c414485001980c8241e41c0c05000d141c2035440140208070b00113407800e800c42060008050074080208082442485100d401030300b01030011a0008140e40402e01401d0b4040d400c0903000052454881c82e160300a000c1c0081d40c403d03a0f0b1b00f841c1103540f0403c000941d00f20701d20241 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 588677814 1250 588676564 588676591
    0xa0b0612061506130f0905100b16080c0f060a09050601060207032109261002121302060705030406020f01050105010e01051206040e03040e090c031c0c050313170114 72
    0x1d02c90714080c005410201c156841180450303440742c0c24614480c07a00e51001201c1500c49040c0900b03ca00c400d00080a071554000300740c205120103da003158002500009006c041c0d001400303882c4844144080354040007a1400c0350035905048007000014900e60b0819550b6010318400071441c0c62000c580c0e24222034002da5206131004c0d440a110703c5401301c2040c0c25092081c1c0300000228403110b00c143c3d9081d1414510912403881d0b294412a003041520088c0c6047d86204002030801400103c22a58110351400a0907210b55403030310100f01240328124000d480c82c8000700700015030650019010345121040d100900c5181d87c2c800042d50032010b06251180420340a010503044170302143c020341d82c00400200045000680c200030365066501c16040003103d0080f2004000f1042c80401010030b100005130300400c1c10000302200501c40c04c50b451840020040c5000c0e101c070a1150800c251502c500c05010840360803a95030711045801d4003c0d409491155090040d11594104046005e81c400d4010a4100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 588679064 1250 588677814 588677851
    0x2010912031e06090213082a15030f090c0a18020c0109061a0301060f14102a0201081609050d060f050406060f12080d050901020c0a0b061206 62
    0x35000782828a20750082c240c0b038002c00c000d215020b40a40c0b0000c0403070500040c0c0d00d84104075001103000702a0070882c1039a01c000c3c03503131103502034400c070152050b40e0460a044019800c4400036040d2013080501010f19040481400a62203003105042d0095907800c0c100c0c0c400140710018001503039030707074031505015003c61400244150102c0d0020200712a580000140e2600b045c1d580d803084889059030718421f40d40744298040582400d00c5654040e00d9114100c001c40c1d0314142c405074100f5000d0142500a002d60080584551700403880400e111140d030f42200480e40c0c040034040c0d40034001c3e440582c0000c111102184401101c1201559070031030a940c1c401106050106005c984011450210b5402d0b540d0401540001880d110311801107118400218115140062520300c1c144c06421144040340c02103954000600000b044036100211418040b686544607000d02d802030140402401840c020074407640c0401c200007007014810300040300c0c280f1414040c0c1240e981d03625421240b06c8003869604007078 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 588680314 1250 588679064 588679067
    0x80a09020d0213050109140108071e090204030803060405011e030b13020618030f0d0903021009091d0f01140103080c0a12050c2a130f0c050c060702010912 68
    0x4945540040c0c15116001c1e801d602240300210311000790300340b56a980005100c003241c0c5000c3e070040003050004084681d41400303c40c41d1510418864580c03000d00c666a07a02c000c50102c0350030030082c844124119110f613600c0c14529280c0d40f0858285105034581000802c0c2c1003101040041814460706000c0c0745103045036070f6140710039409440c94050282c3c000c02c41c401030f640ca100801e14581e6442d8400740038140b05092514004194451454941182c00340e403c1503603100d03040e40200c0341c0450302d0904514802c0ca09460f0a080f0780c010124803130908542c0c0110303031806c800c00e40c44041880212908402d5a0355154200e070b042c649450b4180301140700400200f00480302404d12240c07d0002c3e10201c0314641e9a416120100080102c0172031000304e007400201e00140b208a000300c10350132a80704542c00da05200001d2145100380148288007602c403e91803003605074410394141c5007124040018080300b0002429a0300004c0d002c1c05e84d07209041c000b90b0075500c180a146c0c0c0350381d844000f00c915079850360300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 588681564 1250 588680314 588680321
    0x61503113f070504021303050105070f05070818060f09090a1109120309061b06060604152006090109021302070c1814040807051605010f0c03140301171507080a 70
    0x1000307501071180340e030082401d66a501c01890b940e44403002c17900e003041c03075440d1040c02d40d01d00602840c14012240040060f0540000c1101d00080c1d0003151656603942d50780c054a900b140b4025030f180c2062010450140d0f020080008200e108411114508075a4400700304006860004541014007001806000000c0c10111031804049840c0010b50341822184004a07109400444880c0c9000441c013110b9a00000b0500c0455000702080c0c980c940f4081c2009014410021100c0400c6c1c10402011214034899a00c11500f654620281094945900b441101d50307000e00209030041e803190442c02050443c2010901c01c41d1403040c0d01c000e010494a01d8804040d03103d4154071f204080698449450014402001144c14410392007140030540fa0a918103200b441c144035482411500703106110180141d0f83c104900c80440c2440c1d02e0400000420b43c6411203d0701c0e0f0002590125081c080004600000354420b8904001c0b41c000803560019403054007952981000d61300900454080800715040038203680 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 588682814 1250 588681564 588681679
    0x91501030c090f020702040905010516020c01050306010e1f0302131413021b010501090212070804172a0106090c020a1e020d050307050a021002070e01090906150311 72
    0x100e00604203503c0346c020800f9620b0410080394665512010045100a07003032010503840058030080450806d0840007030042d2102500d401d06000c2c103541404141c2da03800e144a5850130484482c0485103000d040068040d41101000c20110b51049801260200d200c10612010400040081d86240c4c04c00c548200207600040a0302e0702c05000a8001044481c00d002d001d00819088100503030311498001040041d00b001781c0004204002c440500021608030487c42c0700c4031520651060340c51001d8640d001200b12203030030601c420840d40e40d00e40125401940401c0854040c184180010000d00c4022a2282c4083c40000c1ca6204c07100d43c0800080e4424841d45d842d1803020301509400c0c0c4a03602d5851464208041c12601544001d40341011400c10b1000394001c0441d43c0000d00f54141440e41c0c0c3c1095040500400c01c0f02035440011805220494011149240f803a0f80e00008507074981c144070b1b01165105c41d01d83e014070395500c0300c1c4c101c01454150428840405e502128403042000c0480c030351980441 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 588684064 1250 588682814 588682841
    0x31202070f080a0506070806371409090102070510091b0e060130020c030d050117010608060f06040f110a090305010605041802270f091501030c09 64
    0x10801003549868150307140050b0110200a01c0e00c680c15182085c07924200030b10744400c100c62181070048949903105858140300441030350303044c0c07a600012941c8081104525a0f5801c038146803000910103404140c202e090141a00d0000c22581c4d40030342d2a0a0b81700e140300080085c5e2008035110403010305035100507000740c0320303051140c23814040310002e020031605178010401d034012120502c02e2542c1c2101142030211500407440c81c0c2c640340b2010741d0004407441d030385856002d500094440220002031040b02d1000401c041e04000e0b550310ba00d03280100346c00000c0303104020742ca0b02d0000304100d880012204d11451010648007890381c2c4040500c0094846c11000800332501c440d49480c00c406214007a0025246071790300c00000c280396042060a540107a0b105501942c5810b030710708100d4041400e031441c140e80550700f000700d6094031140402c262442d043d003c8210481c900511007040b030441d2401d4001c0564904072900c10b01481a0b4075008242071000500098108104110310354040c1c0200040c908074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 588685314 1250 588684064 588684073
    0x15060102190f0c30240902040908030415051b0f0c100506040c08010b0a140d020a03050a0e0c0f01032c07150228020a3311030301031202 60
    0x355a282d50343c807a8140c02c082e80070704000d000401140450340b0580000300888400c3c100d10480c1e6102c0052241084100115554000c40d14102c001030580080e101113034050b00030410210141840001d0b07401c192411140c4071450700c0c08007108040740c042d05010f5020507900909518642c808400c00e9440b92256040380c0d4002d03c501c0300709080a0180c0c1d18481612007010a01d4a003c40030001106d25150030542440304480050101840b074000381c40720200542032000503002d0a80700c000107409803560550f412070002580440080d07141d01b10034061001001c0030700c030448031700741103d4940074032442c0242c0002e1100464000b5601c0303500058200003256990b03900003002c1a4440c080d00c1d4100c0da030404103a101000030020010304413000441c1c1e040c14070152840744c08402c80040410000b080781c80c21036040c000703014255a0381e071a00d1001080b18142010b200100080881c2da0b4a00c4001c0b0507a40c4140a031556049038010311100340d900729084d02452660b801c1d955052090201504103c0c00c6108 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 588686564 1250 588685314 588685343
    0x200a080711010e010c08090d0e04091e1a1608040b0a4d0711031f0b090c04080a02060d090c180e01020708160203010f06120201021506010219 62
    0x400b0300c1810f01e0700d80c60740b0010030b0b55240f2200191410802800240d0306074801c1c88240d18040e4040c1c44022000070491b004258220310f4103020051510610000b1018207401d145003080000b80041000d062981409100d500d917142d401881c19070042d0a000b81c003003402c0f400003d0002d2040c903452540040d440c01c0000d50b4041006a1740403540c0d40325100e1b85030588200321546c199003184004a10000202071b096030448140428501034018102c000f0070a107100b07501c0451aa83c00d000320710b40c0950011003c00381e440c90440c550003808540303807260b0040d0901c0c4081424a40d100c0112402d891401e0700408a03008103500b480b0490744a03c0f00040081d5461b02e1000c00100c50302081d0b4002e040080140c0990082d0007040011244400c0004126038810414000002c0082d02a66140c2c0074500b06103010014500100b070141c24038101c0c9801003032400c00d0103e95007011144030070955000303070b0890380a071403919813050031810251070143c05030b4090b15172407010031450400720004911034040c0554242 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 588687814 1250 588686564 588686597
    0x6010512061c08040f0503060604022506060b031014090708011707050904080a080f0103050a120302120702010c092102040b180f07080903031b0903010b0a0b030a200a0807 75
    0x8009400001c821044c40601b004245402c00c8450f800074021101146410a56400703040903c2c00000c1c1081c510700c0e82d011034020b002250f4000d4009000f072082690f40ea14082c820348203068110b0140403004a9100700b02d01650400c2d00c0c2071486101240c030740243c20303402d02030303000e840315500030383c0000e54861300f00c0c0842d02c3e40300d54452600440c400d5a0003034407031f200c0082c00740401c0801400d4141207005100100301155001903480c00e45604101d03d00f00360f4850300400c80c0070344075503040203001d40c0b54032040c00f006650550007803200c0c1707070340d40e4808000d90740301c054000c00400340034443e400182c091441400589010340c4003002048005084203181c060071007540a407200c0441d50303c00d924800000300810344e1f0700400081d03407007080c0e00b000c3c41c9549042d4109090070750500e1f4135030542800204081469480c00d41c4030300d8000e00020010800d46941e2089040f00d40d0084400d41c81c010704040380d0941d00040e514054140c1c42c111024203041c00c1d01000111a0024010704010802c13842d80c2c180541103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 588689064 1250 588687814 588687817
    0x20606090912070605221109060609030d0c0201030f0c05031902090d08030a0513030f11071d01031a010b04120c051f0215060609040902060f0a0503070806010512061c08 74
    0x114070034030001c906443c003520454559080c0c81c42e188003030300341022a04c0010f680c2c025984440c201c2108c0748502500e4034008200f036070040f5004581c151042c0084078442c0c41d0088885108540f00741d8052103c010b001c0c1258040d211031141c010082481800800c0c401c07222002d00b0846042904001810030760903400045c1013030f41c2d00c00305075100c01001080c0f00c104109401110303409003048075400c10310105950000e0501c80d050181c50200301e1801020032002d0000c3c0100301c001d010240031581150f45000521000322428801121080e00341e010005030841c1c0c0d600c4103030413101005452400c0503d400c4035645401000501143c40c0004910301103515510080c0a42d9042c601c00c2411605591000b03010b46050401c0ca6040e00c45158901041055030b15042103540f005003c3c2c501081e69400752002c99058000c1400c050381c507040104000000660003406544105000c1c0d45510003510f9400c015540f6108050081340b00c405807600150403030906103196040785143c0020026910010344800303020f03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 588690314 1250 588689064 588689077
    0x60c0414010509041512031205130f0507090507030209090603010621050316080711010903081909080a03020102071b0e01061b12120b0a05030a0b0712050106020105010501090e07020606090912 84
    0x8011b440c6203c03e050b40120310824881040390200420300303004507207601c2c408a4590050070222118481c0d01005010b0100900401c141d10f0240010300382004060040d41000d0b04480c090007200001426a1405000c1c000464248200005098140c540d2001002e107034a8801e171080d20003008200480c4441308041545e65000e803c299864100741d150015810342005c03040c0307040120011003440450198400c079404001c02018030350303043c1d006240558226091342d00170340ca903000742e41450042c5034064008001c0e040c03103407910b20030a020920607403540c42418080c0e00484a45c1c00010f0020900910660344102c04000030040c0e4030000d139446031048500130440b640040c0400c03d040100c220ba0340203040e14031600312805201d21b07003040d0201750f0343d200c0d401001c0c142040c0000031071030240c06191100b080600381d640c2440f40f9078452034043e0213004c003807141a000800a510000b50303220710001c036a0003000310340d002e0216a00c2c0c0c0404c000c1500c001500502c00b038010540031900000456004108 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 588691564 1250 588690314 588690329
    0x1030f060e21041502150c090109210c080d050f090111240603010c1205060406030c0b04060206070806100c051e0705040e0a03020d120b120a05060c04140105090415 72
    0xd8450070501c0b269800500d114051082d03510500c8002413241080b1b0401da40807006440d042d44130300e041401265000850341c404800105076030b8802400e5548001c4108a950140401c1c000d00c07951400310035a20944451001d001880a011051450817103070010043c4040514004c441c01c028150b026007440780c221002d284284150715402178169900d50060750101c42103008101d44410001701821841c107040043c80400e82d244002905680d89038050400b40d134005413080b0f1807903119904003903a0b40c400c0c0078801c0035101da0303000107201074890282c6610880c009407080203480e00c040d80a0b22601600c860032500d41c000e5040e0100328503880e0f80040c0e103c00c0c0407002401001d02d004203200803960218003d04094100c150324101007600001d2544502d513003850018034001ca84004440109118030050ba400405e11000ba0610030b000101120014090000d5600c030b0b40700c1c0365941c8941c0c803442c800d188030035151411000c0c40d136018030082d00580070060808514205000d40e07500200d10903070840075 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 588692814 1250 588691564 588691567
    0x70509060114091528020c100809070909030215060904030e092502010204031a010510050315100e0103050f090d140c010e150705030c090409050a02030d230301030f060e21 75
    0x40c8240e948044816120105d800503144280004010540300e40071511440144418440031031000281044003100a040483c3e00304407080151034020349445030031313030041e0040c0031640129481c3e20b001c400150155505858807185000e00307805005004d0380051030b00c0e2035042e11804e1081c6035402da401482c006076141d4001a5502d00310b240c010101800411b16a90f6901d19000510040e160307480d81d010420040c0c185030303032690349144150182010751000c0ca9007140950b2031040f102c07500000c0c01c202e42c0000340c0b4140300950781d11504a03804a4111048134665020401f0460740b180908a04452042181c10a91502da1011190743c251111031802c20f01c240d20000054800074030a120716a046441e41c9802031850a01c403214003d5070003003000c50761280d9501c00c03007401042410010882c40c80c1d07000e0b0030b5540c1000318a6006e0503600382020510102110104c004241072000f01c22281a207a0000c1c2d0550480c01d152540740c0100100c2032540d2041c03060b00499081d00b001e1406050030040000c0256 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 588694064 1250 588692814 588692857
    0x90f06150f2408090a0c06020304031104020712111e0604031704152a0e100c08030f10170105011d0103031b151103090705090601140915 60
    0x600011140d644410b019101031203001140482c852031440060010b0300d0007034070689906807502d08180d618a0018000104203074000b13543e940100280c42124050b41d0f0b00140b18114030180020780c40341d11801000d5000404508540c03c0c0030741001910203082c2400c8900320715070329810200709140350403110441e43c040c03402c000070140d00c403010b88d0701c056400d6054a42801d10355114000741440640c240744141d102c1c0c0320b943c4000c04aa03182c10b0364080c5042c456014010661024001282c4011203038003c02c2800816440c2e41d014113850001c4560190801d40382d030303490240030b24506d50040c00c855000e8485900001e208400158045a0011000d0002400b545070682c0340d0042c50107440b407005015410001040466080421060601c8044591020450070303441e1011070002200803c0413110f1400c80021074004828024510a0b039044048070409a1118100a442c01088490600040b40c8103202c082e6000c02c04040c005030100034101a00d0f13840b1240604109070001c2d410000900a8225503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 588695314 1250 588694064 588694079
    0x80408010e03271e03100207030806030c010503060607030503060d060603030504060909060e0106120b0a151b080306060d0f060608040b06190b0a0e09040308011a031504090f0615 78
    0x10f425040d42503160b90081e07103a080c00814054401c802600d0388031100d070855541e10ba14180002000800d45240455540301c191402605a400558049009100d44194034665500070350489000707d41c010202410980140d40480e42540b0003003106811942e1442c22030300089242c060360011714840d4032002d03140c604001d4002c000301c1141e44841c1c84542409000c100c030080b05442c10307040d58070503d02450300301d50600c003c0b0040c2004030113058004804c2c0c6400158045516079801210015a50300c00390344803200c07540506400000005410404104042617503071030000001c1540d42180600418139503001e060314011242d142d40050042004041048104004440c0030340c0d00200c21035003120903070708103030204401003400c0c058646a01030011303074141c0d945c1c00750345100b00140004280442e0741c6024500108138240a01c1025904ea040c000f600c0c0320b00c002e40c000c0c0c0703200b20b2500d0344600c8042c0e0280100400340c581050180c601e00035014a04011035504c0c05100410500480b601e50620320b4401c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 588696564 1250 588695314 588695347
    0x40e0a0f120c0f020105031314010b180618041509050d08070c0f080322110301230610030f2a051e210a1505040509030313080408010e03 60
    0x300d02004250900e040003d2a014807807080d41e078080c6000c0c2c0d200d139100b0281c02c6030950300b4103024050a0580117607201f14481504070081c4e0010035100d2507000139045a251810000c00c0d03908661040f8548041d88040f840b142509078418061145240c160085004036001c0311000d00382660650400380724241d00c0b1f9002140d803038000301c5620308090842c41c00d0315807064054500c40010300011001020804001c0d45e05816100590802940904829185080102801d0840005000c2d501301142e625421100c5078040c10f18903440001848255111000c000722440070030312400c185650b40025000c0d20200e0720580c10f40b4401001400d0706d400d00d81138400d02a02300c15a0580c20000c0c10021004620407600c0707441c803004540e0300312503215241014241d085c03072620085210300035501410061182c03030700c1d084845070724440b00118030001c0c0c903041400107680048681003aa54020000304405000b20740baa4012103000e03048150500f600c03a80b910b401e4403135000b0030483c03591003c240182c1c80c805030302 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 588697814 1250 588696564 588696593
    0x90603070210060617070809160626040209070302070623040b0f01210f06050405330708091005010b0d06092d0603050316140c030c0609040e0a0f 64
    0x40860380703400441c3e03103100c0c0c0700802441d1b503041000540100e48405000c0004940000307401c4604165140ca6a40c010215485078042c03102509020344940d03540c0c1c00703258800d405541c004c1d14955036692200003e40184d4410382046444c0c9640700080d00b000303008460700300030b07100303800352403641e5400d043c18901d200308000303000144140098001001407440040440c401c010486102d60080e145904185945070070080e00601923a00300020001005000701c6c1c2c002a40a0418000607500da540c0b125176010300129010502d60415640401d003041c2c0a40e40c0e19512031400800c4906844907290340c030040e14001e27403103900c44001c01b1400c682d0340c090314054080580403400c0b0030081c108200038020312040b45554040095469080030308130050954000d5030196801c542202c1e907071028151490ba203403001c080141d0b080c450045400c9075403900030445045000e00200100b000745520000c1003081d80c0458112644560350308681c410400c000d10034910300c00d01400c24440340c0007075410003040010303548 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 588699064 1250 588697814 588697817
    0xf0c0513050f06040b0109090b0105040b030a05010807060f0e0121110a020d0507020a17030403050f0307121803030818060103060c0905120327040203130203010c0c030c0b0a020906030702100606 85
    0x144031744140d640c0c41000b08044034024400842e0388840c0300c00580d80c80c03103250003c0382d0f90180081042456491504021b040b998000202c0d1000383e500c0804503602000350346841e0000703400307801c0548507610178807034172010104a802c0b0010180d10320144204403140f001149000c00c1010640443c4c06030103100148140341c6074201246055100e9000544c11140d50151103060803408400c040d20700c00800a80e009141c5c400203c41c60352030314401c91580c9410815085401000c80041082650302c00d41c401080802112686080e10b4107555095404100040c03413004040541c2030b0b140100d2904022542c000d5004041c0002e6004207030100a29408254000d180189241002c00c2d01040d0b00100320b8414805294403039290800944003401c0a80b0b02d0000c082d07000d8000704c14002e281400032907501089108500800c07034080741d55015504503440410260109841d054070001007542040e0f4280d110305110001441d04400b01c001070b989400c10b851100050f4460412600941c0d1140b10b00700150030103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 588700314 1250 588699064 588699071
    0x9170d0927020705010b031911010504081f0e0d08390d0f0c210510050f0f0a0f0f06080103080a110c030304080a05060c07030c0f0c0513050f0604 64
    0x44079888912440390a502904950001d251000d025003075010311000c1030000e040d90000340c01110009036403070040000fa1000c1000030240e031a030b0b40c0600101e800f200c0b24040504490400f032040320401c10141c00d48a0b0b082c1d0348417030440100040906c003074802c400380b50300d0705680c0c1d040107002d02e0f08104200d0203a488600394441c1a50b2101c020023441240d01300ca20407416a6400950446400350201703001c000f041a00b00b5098009450b006440d43c2d40440308080e09100c0800310045c00e805850065847c04408004020140141c0c01c020307100c7c3c0003003400036190311510b21000021882409450f0b004480c04404010184485850000e901c001054546071044180d410358031400d09a00c200c03810a000c0c4994400c0505420714103000f400c0228030014107480d11075517074524090302d403050030304100d44030f02032000001c420000307800c140c03625941c041e0740318004448203a41711202c80e54482d40940c1c240148040000741c0da81ca0200321034001e011007201003010304000303890002c18540900500d10036400c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 588701564 1250 588700314 588700349
    0x1050406050f211203010e090d1407020612070e1c0305121f060809100e0c010f02032701031b08060603060a0909050106030b060d1703060109170d09 65
    0x1d4584261031201c0c000c64140c8002c1c1c186450512018014000c111450b0050360610713030340d01d030b038900c041d5040f18907540e007050075031b52454a01615000d4a002c1840890a0741a036440400213000140c07100360310141c01c0e245401c061041c202480034044440c0300010344040d00e0b481e104d0500c00400004040344e54250b282d842d150f5900070b80300d40510b02c64041c3c0400000c00064050416100541e02202020051140c0e076841d0b00c4000e01d613807001c491007507443c03244c524000400d01c400e124028850b950640500002544840115002c6041c40030b40e00451000740844480390520400b808640b0043d407000212800c400780025042d03600b03d0354042032340101c0c0700450006641100700241e0107401120403507070341e0355440000703800e1460940000503002d290112540c00c200055000105072402109100720503503501e007c101d009822450000c003290701101941340540300d0040035541101050601364403d507150b400c0c4110360054060220344079489262a41084c40d00120f560025242c0102030000886 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 588702814 1250 588701564 588701569
    0x507030203030604050408040902031e011d160c0b070c05060f010b0a112a03060105030708030703030207021c0f0c080d0c1118010e40030e06040b0c060105040605 71
    0x8000c0c070f12800b80d9141c0000a0402002c0011a806401041802c5449051000416410998514010810510f11000803d00305d01c007040c0d00c101c07055485640d141980da11140307450041340c905402001d1040002d80900001c0c60124944d100d0541541e07081d44800072402c102c2d02c1e00700c0140050001079052001842611616004c80b40401010b060071400361f00408080c80c0b600c504035021210300020708003a0320801c0603074241100c0301c5108504588059881d00205500d0b50300e47c0c031415201d50310800680c0d000034001e4001d084054001800b4040505403c20b0504013049501011188422100f070b9100070071407a910940302404000004054031000c0101c040d01e1540303075980250145090a00d65290382e0340d511440da6038002134440507151969130780c1da80e00c0c1c0380108cd0fa42c01401c9241014100540c03000e84030b0500c14840c2d984802c9d1060001040f121007c00042100b83c04200700258190405e44407540100002c02d280c0d1010f43da10500740a4660034140706802c00e80c400c90801c501080160b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 588704064 1250 588702814 588702817
    0x60f0618010303080711010e0a2303030f0414030d1b0801031104110405150c0d0203030615070f02030a2003070e01152c0a1d010902180306040c0f060507030203 70
    0x1290f040c200b20405441314501540e003949110300c1d8a04640c2003408a015a4002003050b030b910038400c10614002c07280c115004c030400444000014043c0d4001d000085e00408400c0401d90800d006091301c0740075102da0a411402c2d03a2005200c07c68240d1659100c01c1c1016115480c004400c0081c47c1c500300a50451340d41956803c603070100355200320349408480f007c418003041102e0051038010180c00500400021060041c0c1180070603140c54098505403800050020046074410040140503c2e50510103e09042c0c01307411a034019035079805280320990068904101000141c2d0041c041c0d814030349602c4d10030f904000ca601c0c4070380d40a90080307441040001000107180c0c0c1515a05800200900d0003c0000c0341c00c1840da2070118240c10f038680705801c1c03010342c6080700c420082060310521245c070744848403001d00c4030302080d41c0c51a00212000400c88081c2030383c060103409109030305c1c8000b4031600000091418030103407002d80d104000510108100300c003035590400141940d040440c00c0c40542e88002e0749a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 588705314 1250 588704064 588704069
    0xf0415090b04030807030212010e0f01060206013b0a090c12030e09090f031201090f061404050c04182a1b020d0b0403020319050c07060302070f021002060f061801 71
    0x3403084c0c88005c91002406a0151801220007000d40300c602d40c2d68501b00030b00b420054a500c0f50f410095000481c0070313440840c55038140c4802800320300074510b44074280b008210710062020480c05080c0c110030b01c0e1186c82540103000f515800340102d40d0066a041004818060364010801245d244001800080d0003000c402c081c02c404548420150740c504511a013070030010801c107910790100080d91100c0c03030700348480c55060f5220085c0420031841c0d460328007022120b190056480c140e062114003023580c0742030380010307a00184144e038090900d070356280a4082503844c1e40040c0c11298403003145600b0502015030110040c8005482940810301840000e0311214494100b503030000e045000750019529001d10040036550302198241845c5040e0030000d4036904010503018440010303207100300785207100b80151101d25030110090115517103080b13010382c000e611a1800f00c03085128410440c000d0390b280da645a030102c1150f009007629251009540485000007020588200c1d580e0501048111a08604606 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 588706564 1250 588705314 588705317
    0x1c0f150510120914060708090705090c2205191a040609050d05030909100e130201050d0e10020f12070507050709050a02070b1005030c2d0d0503030f0415090b0403 71
    0x220f00c0402e044c030006906013020203006a01c145c009004516074070043c03030b0f0f04c11f00f1018141e804403500c03a002c01c02109000d0f030300f1414060302402019110350018040155212801e07009aa800c0d030341d000451515052010481d200c021455010444c140780000845480b17082c3c0c01e0b01901d040e09008002c1c0c00c4403e070f80270345400748014468000801004101302c0e64910001000030080c0d03e0240341602100d42c250007000744003203000d000310f0b0b004035200c0b40200d65070342e050711803178200012140308100038071000b0b4901c074040c41244520019401c7c0d0307200030482603040318885961341c07480c542203103642c0d1300242c100c000b088000c1003a1004540007060b0349058aa819001080f0340d02d07403440f041e02a004410014150942d5031044c00a070410a500701000c03900181c06a65800c0c041c4000c0044042056246080b2080c205003405070000d001c040000000794020000c80c241c440e030b070300c0b2140f03590000c5401c90704c02c0540c0000d00c010b1000d196101d40720002034220900c0700d1800c0303507980454210007820040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 588707814 1250 588706564 588706571
    0xd080912070203190b0612011e0b041104090c0206010e090d0e060d150302130c091202060f04030804180920040b060a0c0b0c0c060c1c0f15051012 64
    0x3103583c1405401d002c2140114001c0c0c5a860500341012015800c1e41e903c2d200b004001a05c241d1030006018400103c05241c0851401c1440d107078500c0060001c1d0300100d0f40c041c0d03484c82d51100050141d0094805414140400103030700c80580c00181c030f00001030700040c0c09444642e04000729000c00103012000f0a4071450150f80b210a01408140c0e540111600307034614604108114006080084c18582103078003c50341d010055034069020400c07241000280700008600c283c0522a00300100d440240e5075201800c8035240030151040e2184503006600115106400024104000c003400c0d42c580700900c2050303c0070400ba03130480c0d441520300c0801342d070811004e00262880d42031507a5503500c40c440078400076000b2582c0c3c180d04e0000130070040d800ba02c101c1e40d0302412004200384005584c261010504410000c0c002d07612003d0000d1026000038180c1c4080e51480c007004410987d05008400741e080c407640c404078503801c0400c6c01241c000025080b07540150428050100000e138404c5624421020a00000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 588709064 1250 588707814 588707827
    0x4020403292a0423030706050f0f0306030f010c0809010e06100608070e040204120b250503090c0414010302010e040c05030703020c070803070305070314070c05060a050d0903020706020d080912 84
    0xc10703800340d03134003e00c40c00045184038621524070010024458508a00b6101c5158680005546034050b0b5242020180300502005414504da4402160800d00045c12107082c4962445003509580fa0000080002a182014400810424003403207070807131002005840d0f18503000d0140c03042c80740306200d074200b00914036010a281d24040c0c004400701080207441075594607114405104000203807501100e04660f44000109040f042100000c010541e0a40403105000d12687c100c410f50000b910f00c00302030082160040041d91184071306441102283e030701c00e00540c51400007401c0300192840d4140503605001401e11150707841400c80ea400f001600340103848a44c404004c0e0b241c100c0e82e40101d4000d22002a940701810307009005403089521a55030a004a54941540c20701d42c000c440c0c0040071041c89481c00d003c240744c000041d00a40d50240fa02604002d120142c0c2015038100716015000350300501c605101503541442605100041404d10380242c5c1402c00155540e040c41c40c0008a4182c80030580 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 588710314 1250 588709064 588709141
    0x201080f040303090212060916150309080d060815011202010f0f4506020d0507030c02031c120b030a110105040e07020105010603060f320402040329 65
    0xb43e104d0341c01802c504e20342c00c0208806580d480341921250100d21176003075000040d50042401c2810381b0100d0903449004c170b14410007903000d020900740850b43c440b0207008134140c0c003d96200f02401481400e006040c920f03003004847c581000c06800a1501c00401101c200140c1d03003041c10510920a50318102030729162121040711400001c5c1901200f000980c90b103006c41c02d4010040e90382d014201015608042102e05098a040303545100352030168100714107070070750a030081c806429918061b0800c0409400c00313178006400e00101202c00d541044600c0039546015a010700c400c0c060041c00d0500300160001d410000b40d5816901d01c00521000010801039101d0744070754240c0b07008180440190f001ca0501c0103019010f40000d001e140c4c006482c0010000d4044041503c2e403040350050340b4449500c0611001402c01d14103030000c0c400030b003d08040c64010a4071948000d0008602400c44001b5107840140d542042c196800289115401c0700c009000c03480f0f00360b83c01ba40711806100070311540d100340c0000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 588711564 1250 588710314 588710321
    0x10c0b0f0702030412060204150207030c06110c06120411060f0403140f07080607110105150907030b0603100317070c060809010e071503050702011103061002010f1d0f03070201080f040303 82
    0x104050101c1085e852800708121500030348140c3e4220801601c06036115070f4200d039030b00600d01c40a008455018010840c041c054800501003c450078141c1c1e92034100f500110300c041d403140c900314040b4504c1d10100014840c01401401c00ea8000300d5805142c259080d42c40ca0250099000c0030305140060184000c41c00700c03c12000f10084074113804d44d04401d644070211916110300f100c40030007051011503240001401840b64510910511415004500d803031814443c90b014001c08441c103150740c83c003101a190b075418000d07500c1408d46000c42c032076043c210714080e408011030181d19000101c007480944001132902e85518283c4d01c851030405100c0e41d034446650702508006007200a24080c1c0c03000071502c3c1c1c1000b500140c07450040c0c1c074144055281c00c5400c030700700c5800700001e000520b400c3c4042150781c07801004518805c02d60b07100206050882c2520302c412611142e13102c1c94080b080318410004840300384040440c0b42601c00c051403e2282c2c0d500080d2050344001c203c15240122030b00040c0c10107010b0352 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 588712814 1250 588711564 588711569
    0x80c0f031516120e0d0c0311060103061a0d020d1b120c03030e1e06390c10020c0609040e0d0c0c050406050f04024005010c0b0f07020304 60
    0x50340c642860a00c0070340d82070301e0500150310000040c403a100c03d10384140107000d08044c0e000d04200401e8a0741d0403003011a8240503c03042201041900d080404010804000f824080c0d07002d02c000143ca10074402d02c0c0c104221244116901409542940d10056a250241100425081003000800300661142c00c92612056080707400100c0c4074104040a0201e0a604502940d00c00e850752100142c400040040b14841c400384148074070100f1084130070b9410008060034400c4541a44143e00c030b1340c82c107a141501203100309580e034441398114a100320341c40104480b100c0180244ca440d5074040e42d41c00e0003500c0b04040040075002e0800020700502c030749c5070380e0300121407049120203450400400030001440c5108001058800008900b00411140341c20711948040302c03401021038070500742ca9814080603400c010703a014050781c007035005000c41d82a48441c0b60800d501c882c080803285920070382c18444c8248150070003030420012000c04000610b0403040290064028200b44c50503603142d100c00c901c2e51150345c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 588714064 1250 588712814 588712843
    0x100e031f0e0a05010902010201050106080108060402040c1218020f1005160c0b0703050a11010b0f09060f030f0312091902060d0b1504080105060d0b0612070e040b01090b0a080c0f03 79
    0x1480c681d003d01106500603658580300340c0c000c0c0481e07660b65604071380018003805112400d8000c1400319006140c554040750001c2000d00b400414141d4800011040f80c91184251a414031030b861140114604514403c031008001c0b20021036840741140c0003005400344c4240701c007000107600508000d1000541b0254020b040880c111030f9581c05524004010341c000d5400307100403442c0e01d46a906002018094151255406010f80118203858800c0081120000e000c0503040003884800303010300c0d01c040c040e4502c54103a41000b5a41e5042c8148942460030000340380d1041d5070400310b401e58642504200700ca018540440f00d07251580943c68951000740369604405030711003003e00002c5041c003502c10180007111003a6001f080a075031440c09226482004a01c010031555000d0001200380c648540d00d036604118080403202c100d6241c01d011501d03035a0503101940c2d40091100100522070f064080c1811107401030741c00441c200d16002c0440d6403030000c2c1c4038085c4900741400749982c0ba81c03000c1041840d00c0f80711 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 588715314 1250 588714064 588714073
    0x1503040b1f03120201181511040503060906070f0c0b15130c020d0f020309090408031003080403050309100c150203090c1507060b090411060a03020d0e010b100e031f0e 73
    0xb40e03e0542003514a40072601c015509252022401d010101460103400e40c104141841408803541c1c040003c01050701040c0c0541c1052201040341e440421886200d404954010141030408030340260012400003017850401c00c0c020881c400180f403421080360480300381d04001c40b04041620014804442c2080c610890714500070a10355125030009604142c205a92a81d0020b101c880804076244e11503144420f41040e0685c001c40c001454200c021903001d40d000288810702516070b601c3e5107880e03010b540180c03003e0b07101140e085180d20740600080d80001c1c4a0400c00c0540c02140d98180994000194100c1d8a550100001d488188140918400c60000401d02194004030801c49806034202e2602628494030300b101c11441410071642c9140a141c100300d20503440d088500c10880309030300a04c00030b01099001d1000209025a50140c1c0035145003103000401da8840a00a1241d104140e400440c00c010b600800e90311a0344021a00c9660403226200d09003442008410b940040e0504544481c0749106 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 588716564 1250 588715314 588715319
    0x30f0e1e03210406090b07030204031b060807032a0804050d031116020d0b010b07050d03060515090f0d05030309120304020a05090403030b041a030601051503040b1f 72
    0x20104115240540035001040c00d00d0082038400e549005400e00400400c039040711101d450b5074400c0c0d0080d031051055001280410441d500c0d4403111070191241c00120f60049018010442150920451282c1c8200180d04003881c10030010140c10300500844280350703640c261410284a100d4071040501c2c403840d4070b42c029603080c80c402001400708a034151f803036004038030103511100d2190042000d0031180d00394540c10035413404040428101400310480e8405080350290340010186501e030750007071030303070412007601c405250802701c0c20007680b07095441c105072500d041844140e55140c03142c00120b01c52820306407500d03413500214615198185003240d2000d503640380401080400002540306038a110141c4614500400d40c40003140404d40d8020f501186004003030000b410b00844480c0d015010f0301c0e022070f810710802d01107411a901d4406186e500c0c003888100c803406040402101e4010441a03c118000448407203600c8000e00003c0d20041c280b042c02c00225030500504040401c0150319164100302955 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 588717814 1250 588716564 588716591
    0xd1418040e07062304060e01050c0708120c160e0109090606050303161506152105100f060503040f02060702060d0e03070b090a0201140c01060305010608010c020c0901180507030f 78
    0x21108040c44240c41413104940d203200c00c000050b641282d600da03d480640110542c01551103821810710407145109120300080c140d24100710410035080070340d403c1c0b40c0e02d5801441007810400c00100c0000c07002e00d00380080101407004103040c2c0c1140d049040019080c452440c000c0040c3c40c5580c84254940f10214601c42c00101d40d52020710703014407880c030004020000201000646150f8401c0300746040010010702e84181c0940c80110807441d1180900c0d03410380306412844110f039416900424405200c0300c00f4803040001010f40c0c00940301d1400e01c00d0640c0741c40c1d5503860024001480c024051540880c00c201103440310415a0307408100d03144140b0181d41d440d00001d0b5241c0116a081e80c44290280200b4149036020510901564040c1d403052101d0000c0c3c0750320031242c1d12824040078903668624000003c164284990030207040100c00200304408450002450500d00080c035500c0754940f0030041246512005030160780d070848370300218480e6035400094000307240b4814070b00103d17814416a80c1e41071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 588719064 1250 588717814 588717827
    0xc0d110d021b060c040302011b1410050c0c03310902031614220f080102030f010602070510030c032910080603030a03090519140d1418040e0706 63
    0x1c0501e1180740400041e01c07202c0300d9851000380c400128081c01000244050f52040d18021009410f01c1c4c655020035140b59913410401e44c4101402105810121418045d4441409040c1d0030a08032041c80b81480c0301c0300f081a81342d125000d080032101c0c2c440001c420704111214403a51ba012400044e0510484d84d0758181e8000c1d6104445001c004102c0288610040d030081d040003000452070f0f40540d003801c140d00010028003207030070720030305194014810000300001c00c0480e0401030200000090703200d050403e1407980c0000c041c3c10080c2507401c01802440161031702504550403180f02c1c074020645a280311030a03001459066410398007265100d001241d210360808034403890f1103058944046000704100200c440c1e940c15102c6690640007001150a90303846500046d6044c2d000341c082c0c400b042c0038200903000200041000f10b55019000c942c40c8503544040c4030401080e070084c20030380c200c148580110703032183c82280044a40f044200d9003052003a00c5562014444071400750844108503180c0d82d015041 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 588720314 1250 588719064 588719077
    0xd060203010e151504050f0301061703120a0902030c01180b04030c030203160b0409020c2a12030c0706030e03090409030306080c04021c0e12070b04020906180c0d110d02 74
    0x80e00c000407283d00e090410110968402d000c81a01e203040078101001c000800c056a84405d07403642d20f400002c03c94403c040300702a004051940195910721140000e1099108010903054000c0e2038552844056100450140d140802c00d19105104404000001c000700142da00140341440000c034000c400c0207004034000081d02d008504651441c1e404001c040b014004a000314586110240002c00c00e5450580240c44030404220680310030b1803202450000d4190012100c07480d180d80d0f9004110700d810312241401c200780c0080c018616008011000590301c9185200d03900406076250000458003070b0a00c240c5241040c02001805030038421304000780648514000c03001c0f54000c1141700146071801e07100301c43d103c00700c0d003180400030a074503c076440082c4401c41d043d4036140508a200b4050404144c01401d80c640700b480c5441d0582424014404a008000c20060141c2120703007058441e91988401c0d540c0c40714020b01800e5680305070f1b00310400504000c90007142c581c080400c8a0030510b80c2034001e80034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 588721564 1250 588720314 588720331
    0x303010b36041a0d060c030e1501052112180616053304170301080601030606060f17070504050a03140d030603020612041e05061b04081b0d060203010e 66
    0x8400541503c210300c1003000d0f8003e0855008000143c05c4d0b82014100440c2c03810005402c9035032000301b0b420508000b450b40f100712003510061000c1d24241100741591948190b050300e0548286118551300d860800d0800044000842d06034509181203540100951016003800e40390102507240352903102035600101c42130b001e01d44284001110440800b80c180f5a880300310060200c03461412040700c0e0010b001aa25150540180c4620b03865080065008024442c001d2515626500b400021102d6680100003000b4a8540507096298048042043c00d072148010705099120ba40c1d0550790b0348595440780e40c001c40769a80000c01e00182408202c40d6048440a41e0b14294000c0c0040707046690310702009521034801e02145000d4000d80c1c0c080c41c0d000e88030358904883c05841c5480c0e0015032180702c400f104d0350f0380300d102040b041340b184108164001d0301d0120f60302d09280c10520101e44401c02c90700240041106110084066a0b645001914094000204541d256102c2064001401c4110f42000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 588722814 1250 588721564 588721571
    0x2802130603020a030e061909060f0509030d060815061905040c180503030708040e091f0501140d12050708070609030306050114070308151201141e04050303010b3604 72
    0x101642401b05800c2e00c10f1501c1c9030321413240300440c460f0900420000405a84085d40d40c0030401000c0c05038441c042c0501c00e104000c40d1103026840800b41524450340004190340c020362030754040c1c184140c0500307800c81411500d01040000c01200c40e01001c5045d840b40d6849401c1c40c403940f000941002c00e407465000601a030a01198032441455941d205140b4000d00c0d508003004104105180c01e860380f1740002c81d500c1924244251403010444021000d001c080c0402e964000402c00d440180c1c0b0351800702c0350282c2e141d41200395107440e03000312034800c07080810512100040b194100712040f003c039500141d00c080100324582d550f050040003444140100d0303000c41c00f10441d0450540104098544007981566140201ea841143c04100d00c1403400c002d9410038800d10218424400038010b0320001022601d036124035240001e09018500445044845668840340a00c00451000301c00c403410b40c1e042035070f069078a109240c4a481c6880c1e05004242c09005ca807002e5101c3c03074442c4082c0120b01c01c000c84051 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 588724064 1250 588722814 588722831
    0xb0408130911091903140d0e030f0a02100c14011a06070b01060f0509060714060c04060909020708040b0c010c0210020306031c140d0b03070801052802130603020a03 72
    0x140c101d600c05411141d40b00c2082c01401414039181c154941d42005561002c0e00c01ca40d01d541e140401d00c1001c008444680140c0605540c15500c95441c20414004600425001885007443ca0b125061032001074010b05206c42e10380b030558086d0a000d048554031242c54102440090161402450260300c49100011881c0c0210000d00d44902500c01c400d800229480040e46480025100712440f50401414041300340032507100d503554030000d046d0781802500984a00b100c2c100714542015030040a40c0341810b03080c08203204060b440200d81090b900320400042c0d5407480b604000c0981d016551080402c3c20000882d401c18200c1034024034085c0015800f16550144072403030340c13000c2e4003007114400d0f056070100d011146407030310f4000e0600341100b4604014800102040c8003880603401542d280540a403942401081030400308070440007002420001c00060900d014426500c501103105007503012081000b000c2d41009990480c0c0200e205980d1701c002d07007035032070002601940207a084a00400d140c4500d1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 588725314 1250 588724064 588724079
    0x90b0c03090a090c12020c010b06160b071e080c0c0f10060605031b09040b030601080a1e030e130b0316451407020a1b05010e01030b0d0b040813 63
    0x100103030131355039440d000210140d20071981d000b5000031144039403e42d00ca010401060b146c3d1801400c4070785500040000020300c41c28400507190003e0300d40310030060201c20081d00d007400b182510901c02120300d40400e040d2034203c0c40c48500c0c020f00101024038098541d410903030310400070b0144180007480e40300340021079480d6400c5e50b02d400101ca4000700403110000c0720001138110700042100000003031001400c0f103a91004246003203405d0b08000000d5000036841e909005c3e03180b001c5a80e402d0548840e005c1418555001890610803040490083d03000d11a0004030682d142c1081c0b19814018080310030005504641ca01511102d10585608410501c0c4801c1510b00d00a800018031038002ca001990280b40e8190200751045c46440f20103281c1c1d01c03070b0035010b031003403082c0c0150282685600070a112092800c0030b002c1c180e07100201e0350700c81104070401c0002da60030000c0100c900b8424200003c0c40c290060100e00940010b03a0000c103500110001c000821551002030708580b801d8110f0402c0b400d813500d41 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 588726564 1250 588725314 588725321
    0x908010606090501111504060234021c06020310140409020f0f0a1208040e090706020a0f0f1a2e17010207150e010f180210090b0c03090a09 61
    0xc1c640010711a03602881103500aa40050031a0401070482d12880c80074404148504e4096808803140c68000441c04140101090b00074a4510707007140c2032b000c0c0c1211074140c0c5084542400c0090040f00559101901400b50140d05001d00da04000c0540d42ca15180e040b003c5d01c40d0380f600070405a1000d00c25000b600741011b2250514055014014003079084044041203080003461806985c42803200c03a001c07551381c5440001e814900c0c803136620b0584032402c0c5118101000da009000c80743d1070380884810010194001040104523403c5074000c1c40031840b90800840c0d0045031140940903680303101d81160b01141502455103d01030300c6510440c9090b80685a030048665540e8510703030340403030080c00d00000c2800b2040f40d04514000000618003155a542d40c0c0d4856000500842d0895807400d02580460b002e001d46043c20008890400480c3d800e42030301c2c08010a5010080c0c010780100340110388280c0030303900500151807200d040513203443d030849603d5540d91000a80c54010750b210180050007a210b0300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 588727814 1250 588726564 588726569
    0x90106060e032a040e010501090609050f0406020c0c06031e010618090e03090312130b03010e07120b1906020f0d08041704030803070e210303060103090f1b030309080106 74
    0xa0241030351010030032141043c4030340c1403c1d0302041005403050b40d01030740d00d0f031203504040c80c01c007000469150702d01249501100d0203640106030103414041006000301c14010f00d41e03030155100c10300584aa040700b171f029107801e4240c0780c2140c0054001090003610f4000408042c0a002c00c0d905142d1607a898040403280c00040034007042c0031701c183c08001c1c02100e04640003060a12511070440c0d09098059000920f485066981c00da4000800520700d4214103506c40500d02802610b2052807031545001001d0301c81441c020a0601000aa888681080710b5075070003407040540c0051000e2217051029a0311500a4454418500944154600e0b1010740001003100240d295040c0c0ba05241c0b542c0b40d4032141481c500c5190400b5100307608110200c000707500c50700a0750007049550349a5207800058802d0180004868040580002c1052a0040c861000100f04c0780d00c5402071074003180010407490010f4110074031407070040082800700d064a0b805642d80100604482c002d64881e0725040e62100e50701d08031007450 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 588729064 1250 588727814 588727819
    0xc1008010501140706020a031407030b031005071803030224010e04080a050d02220803310e01150f17131a07030b100e0109170703050f06090106060e 65
    0x82004114541c0035400350003d841c07983c0c640900c2c0109a40c0c4050480c0e0107140848042a03940c0704002d0b030310401041c2e80741e101a8600b41004400d600d400000d54510f1141a100b065586035000503814a04c50403651030040403c1602441c00c90702d910b0003940351001050b4407040c600c40e80d014044142da032401118100c802140900fa00341d12a5101c19206070300c0000d600081c45010040640c00c80c5051000b0300c0605143e0850b0700881100541001c0403101036845466298001d03c031814a980010b5210503080f400c500365448184001c074030850701842c0319880003200c00010b078000200101e148660030140006903440081c1c8541508094640303880b02da200c1d00b02080d407100054040c110701c882c40c504050041c2e080c01199035241c0c04001d821070003103404900113a00c91034001802c5c2400f107440035004460381000c41c00c03043c442c0c0009140303110134495480400554030004040020074883c10700515008010b0741e004103044004542da580d403d4076034071203944c0b8280e00064014868a140748108000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 588730314 1250 588729064 588729077
    0xc150403030b1e060906090931050c0108180304060201140f011211190617220f080c0a081305010c150b01171905090d1b080f04090204080c10 62
    0xa540920003250040c0340c0c26600000200f00c47c66056590507142440354104d040c80001080c034941da80030016411990b100c0303a42d12020071100002d070340480c400c00142c0c4207107441643c81d510b044c000100b583c00181074041070700001401080c030310f40c103420085c0003592003000300b0400d88604190418000c000d02c5013060010178200e60000282c80c2c00e5007640c40070b100524000003440480002e06000304035600210200341d45242d0109004103d0007031591154060b600100a180003920b400350340c641801c401422400c407407421500b04030341034054915240349081241e40450562034200200e038030a00300f18034040c418040006642d8450110304540984c0306240009225112480001030507180d51024140422a4042c801e28917070104007070f00c0b40d030240503e070348182101c541c214201d0b4005065134149400601e2490621504001c43c4075825143e00a21602800d0608202840d4060b030188408020000100007807a00380c65009001901c0d12002595034504441041195102031070081e500400c11 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 588731564 1250 588730314 588730369
    0x201020c0904080706020a05040e1e0c0a170c0306150711040905010b1807090501030e0712080c0d03060302040f1401090c020c120102070309060f1d060c150403030b 72
    0x60550381c66411a03c198070490520707010703030344003000e0303800c10940c50001503404101081048582040030703403c980900074001890102c8810003002820050891b02d41950000d8a4160244140c9000c030486030b07030082c50780c494140083d00a840d54400e488a500c2042c05a6100100c04411001c8030030295000c079501c209141000140700103841c11060948455584004d10700c06522030303242d050090001c0c640019134500d0b181c48042e004e0f050b2908080c2c1094901426000d8006000400380161408101840407103041450144000d04c10035203120782e507004445d07441d102c1c281c040e00200700303482c402c0b81c0500c00c00e0a40007510044800b0020081c90010580d00104150001580001c115040901c15614a00e00389008102d1542840d2008600f682d4002001740c18980d100c0e40e04405410a807800b211208480a00180036158103508111442c111031406525507880e1011500ca00e0340441c00d40343c0481801080032030342e58040b41c0960110b800c2401c030095902c0e00300820940404824500c01d00d107003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 588732814 1250 588731564 588731569
    0x1050f03030c0d030f0221010504150503060105060904020c0d1e1704020f06040803073206150d0b1806010603020a0507082203050d02010b010318060527010b1504030201020c 76
    0x5490b50b00449170ba4204102c80000403c1c2c400300181c9058819545080c4d403420040c00104c40380801c19408865100c03005011581d4042105030445404840854440f00203000240c024460302c15204424880c0300294500540c001480c144910781400c182441550200803e91320640051241e0041c0000003001030010700d0254a000000400900710740c0c20151211215883c69124040035940000c034008001c80100b00300540803a245003c224612640d5000000f2a507a4580505a104184840d0170705ca10070b134842d03204040050b900507060686509003802010030120101d840e40b1094041d11002140f228001d000f11466011107540b904e1500d0703110348882c15540c02600d180800126060409510301c40d001280d02c004e14050405804800000d1602074215402e441c0304d030b41414103045000055032240345120710101e412000c0421175960301042204c03400c02d000b41c00600c51040c40446042c6a20542c060000410203035005040012540813000103401030780710090040e4040d00555a01c0d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 588734064 1250 588732814 588732821
    0x50708040b041a10050f03010908091e04110721050a0311040f09020417070f030b07020a2102070806011a13090207061e1514031f0501050f03030c0d03 66
    0x70340038451800e0f262222510b40f00441006440d4114100c50300d41c0140040e160220303900070b12800403802003185414503542d0345170034010010304034450400c454642c3c4008850140e0300000c2400180100108010341407081600c2c0c0180200f1380e40c41003440a00c02d00c4141070f0b81503002c445c0583e1a03182c10404c29001c01c40103445404420719403000240720011b005840c607007903e03028041003400036071518105400c850708060382900f54412544840300400140c454111400183e90b00030003082c4043d0b4401d41c003640341c560592001000410f0000340b811152a400041660b0245103900f0746a10742c2d60748250300c1e0385030030038006c82035120841442952800107050050042a22215051607443d40d143d16200c02c03038225100503503141345c0355242c0016102032000039181e211000300f402c00c094000d022603181011075074081c090100703c0781c1600516603038040284402903107550030f082d00b4910103d02c020000d413400388501801980d061f035621302c03280380c007000380c42e02c501d0308100030045d5036100d09044025 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 588735314 1250 588734064 588734071
    0x2030403080a1e1b020114100603021b0d09090e03181306030f1a0c07030f0309060209150c121c0c0507150c0f090f06051b0106031a0a050708040b 64
    0x90380d003030503556051249500441d160400003004031051300001d042d0182c00e441d403004015101d0400c040410408920081d10142a1109840c0050311031103400d50000e40c48413038005284451003410110507445030301528180a50b0387c280801e000c1b4801006015a8034002c03240c21681c8410542d00d159071900307048002080d2042d541c0307030101b1300665903240c00005070312488040d114080c1c2d042108903441101a904c80c0c104001090f45458000241c500070801c0e400e01c5102002c05031515501820712010360150341065200414a4410181c031040d8140076522010940c50b0324001c51002282d01142c860035039003001d450003d100350041c8004202001440c044c048142130003001d020801c04943d20700350244048181d030400181041c00c03940041d120340b664800e52020098900790610030640398540000480301c66003041a00c8001c0c12042205000d82400240300300d40c6130480000600c564030400c10150382c01c00e42c0f0003201d501c9451030350040c2c50045994101151450b80882d00103032801c002180e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 588736564 1250 588735314 588735341
    0x203040203100c08160f090b1809010b130b040b04170109050102070b0906060d0201210608030705071a041214100e160603091101180e0c030a05010902030403080a 71
    0x1112410341141800f00c40c4080100c0c80054400400c018449000d80c84005500506051142e946d4041c10300003003441c4564003411001d03580c042155610f480700203030585080100140004002d68548100741c00030340202401d481d40280c822400070765801d9040848042c2c0341d640070090300d001e0400030305200340a60184074444a6580301a80c2c00850030030b1019125180c8681d00206c140d0900c444140d190450282c07c8034401c02c9000c06010041c0c0e0400e44c400c1c200c40b55444a95034404903008810000c1055620154041c080081c4000402c0000300c2ea04081e103000368003259011240400441c058025406195420600f4849034404500c00925481900805600712404c81058594550541e28075500f41580f5034022510510302002d00a0007201600c1c0c2071504100888603a00c581100780102c05440f0305020b160000785428058002e2914040d0000a410803201e0030081c1121010343c0c8110f0714040f46600e041d0010400c0c86e224021280196059964459191903007101c40c0000e1620480420 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 588737814 1250 588736564 588736573
    0x120030601211802090903030702280503040801060f061e03020d02071b0e130302030702270103030906030516210f09030503010504050901051303111e0109151505040203040203 77
    0x1802e01500464405100c42801080c0c2c01d807992050000582e800780c2002a150410320800015a60002c0c04002c84481c200d1407618584441c02c0d840e906102e0700e0f00203003142c0000103011984503c150000300031030301d210040700313510380e902c6c0380890f50300007039001c21015000305060841015200b50060200041d0345a80103103803060943d11501181c2e10000a4096080e0a400800401208102c12a40701d110310078440d00104050f82c0c0251a4407948600a114103101e051088900000300c52100b01c148003110704915a50712810041c011445520413800001d00b080000303000007810608005528419072240311556a411100e424016102d030f000c851410382d00c1403055281c00b00c1e0701030f103d4218001e80310150f895040c0b00500c402c1e603030000d0501d20140c1c140400d01c084051420000c47e0340642500e40034103140d00d0f0314103150070080d01810488924801200d1041140e4065114020300c601c40e030740841000d080d90320400e0564201c071011181c500407007141002203041640003550b000e803000b000c5c0d5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 588739064 1250 588737814 588737867
    0x1205010b0904030c0c09201326160308040608070c0501180215070203031204050a0204061d09010504030f0509060c0d08100f0f12080c0105180120030601 67
    0x250490400c4500f6800a0081191a0300b40000c1d035100d000a05001c0c2428442c040c0e9030018206a14444030075100302c240005000d03e036400c4e040a881d4060440c8210741d110400403007240441a030b4109507000000d010710343c0d5014012074110300320012250301001060515141050a0f2020800100848284410400b1080001c1c00a2140c0400a007050084c2a0044054014000700d078030040100c80002e442089210056170b000410340d001e102011f1a076440d03940d00d924003241400c1c88200001c0d0410705046000c50104c03645000e01c216a001e4103c036101c680d84e5002181c4c244e440645002d004940f4020b03181a4180c81f64004141c00e48028000c40d191045050080303182005080c449000681914240f242840c0d885060400502d5006400903000b070510f03d1111409155100300f8034000403540408040246c445e0a50303040d681050020851803418042004541c840c40c000c402c9503502e0301114060b00c560755198849044648100c590540d660074005541c40380c001d4890640c0940c4e010140c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 588740314 1250 588739064 588739069
    0x6090e160e01030b010309170a0f02010e0c040c1b050102030a0b0103020a1d0604030803040c09060f030839060601180f170106030b0c0d060506030c0d0b060d020a0e1f091205010b 78
    0x240400b0782c2008c001c0030358541629034001d0104007403c59000459050a0058207843c0c00010710864200045070005400350107000d054440d1034104420001c01d04a1a110805000040d405103101c0c1002800500402d08444011006c901c82c10a415001c0b40041c041411b84007440762000401c1c800140200340f801e900d98039911110341049038111032441a00d00e0078001419140148401000c0c00c0310103610150841d07541600314001d9865803402c003100ca0648003950341e80c0134140c00105818134a070b582031060f40710840761542e2080304c0e9580400c1c648a001c0c10030501440b07444045907540801918490f003045031000d40c0728400039454080399240c403030100200300304400c07080c09220990142a901e1240c1801001550400e9005c20b101d080f01344200201d545060741100c074460360b4050002006070229000034880d001c0e03202e0503202584041441850b0580102c07503c0e2507040125207080080c03590000c0b00900c0f51218901030009481c80b8020400e100c04a0010b00c0914461000411101c441c04003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 588741564 1250 588740314 588740333
    0xa0e0415022203051b0a090506061c1b090b0f030a09020a06080405060c0325030e030409020904150308040b0a020c040510090c0216150c020a06090e160e01030b010309 73
    0x4800828180300c0c1c0082003003002c104800702000260204030001c4088010001b001c41e40340d40700d40c19295403280002040c5961b0042150981e02200c440300f12210203500381e0000401c088100d0050381e01d0140d0100125501450405044510f14840f0b40c0c5803445c00e4903104120b4002502050070142c690441d0303401130342e42107a00405440342d03a8510005d49010308069103052005404000702c40020802e000040c1e000c03014240350482080d41c1a51a08280d28049000342501c40b00c8039110300004c0307004224000c65070002e103880541107070b00344018800340c4418135a0030320620004091480030002084481c070900054186881d480c016180d400305e500012030251101250010b003d042c2c0c0030000d001c0d40351030348510780310304806200900c0760588001003c22000e41c0c9002d120490055640d1140620341300f01c40c0180d000d03078040c01ea59842d0b80e4a800140041c01e10703000d1a500d900c10240042c001502c40c81402883c690a652904804245030b4010f4000702841c027031441c1010789400843e8003050300c1a1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 588742814 1250 588741564 588741607
    0x3020d020412050309011b0b06101b140106050a0503100b0a15080a1103040b0c0c03040306110405120f12030423100606030605060306041d1c08060a0e041502 69
    0x8018590b1658844001401c0318000c440f90503030711f0103191040001c5040380c42541e038800740544481d80d81c3c210000c42950300c03011101142e16240103042c0403c040001403201800d609401900900846440e0420041041c256005454140d40281e03c40560301c041c0d6041106c458102034080d80c0c6c00d03a01c642100060070881032464000c20017203c24850100d0f80ca00c24003181103400140c40e42035051680e50603940356009449481e001e0008181006c00802c00d00850b4000d692009040001c480c86145010058025108541c86440e91410950181d84081044103040203880040c021002c0440306588060300060800d0356100c440c1d880310080007070641202da03940d604034030084c000705c2e6207560307844240d03546034101008150a04100700159140c82082c0d94009208640c007207000c4050300100c100040c554a000c172603030320a030120090307004507640c4020902c14580c0d0f20051550b9441003845403920b03551080c40c4c9284186000a404103e00c02c24072001d904e92688050314016015110f80855440345 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 588744064 1250 588742814 588742823
    0x411070b0106122a030e0d02150606280c240f060f030b0606070b0408040f0b040b070809030a20030601080615100207050d06050f1302030c0103020d020412 68
    0xc4005020b01c42d003000c5182c01c8600c0c00d22007406401390807120516140c0d803110100e0400050208140301c464042d400c51795040940034102c406c085d451040017940d6406079180791a14401c0c51000c40c6160900c0b80c100c0d5004122940c1c1554203c80612081c40c80d032026002d2482001601c0200c1c400052803000903400300d025200500c0ea8045900b54030f9811240038582400700c1038500481044500c00b0100d43e0300460f600074524844603940c4001048c40b6100f4424020000700444003044208070b00036020f80140c8224070f030301981035501c414490341507200324010714019030800d1202e03000060315440103000580000e4145c80c0030345000c0d034402c43e013204a860325046503103008841c082141130400001f4018101039006003101c2c10941c1ca41c81c00b8102c501da80c00d00841003403c0418085008000420040102a00000c0f40400900f0018010075064602d0308203000d424020401d981d00b6902c14401c00d81d0014058218209080015002544000c41c02e80c0d000380c00f4080051038510108040c00418002d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 588745314 1250 588744064 588744083
    0x3140d0b180f2a12092b0e0103020424020d17010b0d0e060106050d0b0316090b0a0b0301140103051503100e0111040b04080601120c0909021c0f0c080c130b041107 71
    0x9004609280007040380d0701b4040d5080c90074582c5c90307042d4113a1000c8400d90b403c0c8940031360065030048000c4d101d2038000c0d407020250600c143c0d81d25103030b010f8003c810b07410543c241d8000f4046003030100c40142034091005020500c250041c1f2444e03000b017005202d1102202e03c00a641058042c2c058100082607001c3c60110340003040c21000000e890060b0444000101e003c0c100c0304840d405150302c40c241500422040503541c0d022024940c8941d21004054400e102e119600ca696400600c07880a221041240c0004c0c01c080204004143c5104040d00c9400014041c03d80150810200341c01404400c05180c0300350740300c03164026102007100045c001341480d2a06150307101d080004440c80c00d030041c2d202c0c0b0101201c11801002066039071044c5010b9894040000c96013040a00002e400310b2290074240c4603152003150601c0800211040b0640740600c16140d240701140d80d1801140c50350ac5101000d40c00c0000707000400b0f0003001c10b0780a9601204020030000d8504074403025004c0030f80201f44c0440d0350160 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 588746564 1250 588745314 588745321
    0x7111006050a17060a02091801090b0a0b0a08070c030e040c021c0504050102060406020702040603060c050702040605030303070f1b080304030f030e03030417030403140d0b180f2a12 79
    0xc0c2012844080c0401011034204101e10f200e84903079880008103e00400d907800701c2d12040f40d035030f0001c00341d01d0910707013402c10030880d61501d4001e4000c001914480b4480d0030340703000000701d1038001001c0e651000816240c5031302c1a541d00e50700340c801c41c03081d54085007008811850704d111595030344600c0ca203202c2d060380103100c50503d892040f50b448000407151420f1010511007040342c1da034001011380d03000d60320000158985102e840810054001500f000b0940c500b014485210540d10001504105001b01e03400e1050315034400c14541c6a203c103480396000075a8100f0308003050b0340101071500d000c05210301d401500030003c0c1c40d25000ca41099030b08a0000c2c02449650101700c1e80f60141d1003202101001451450410340d0302c4811001c0040c038a8640c40c200800000c1c24107018400202c0c5440d5a01c40c0c01d41d42c2c1204050100050079024441da00c500c01040ca154184000c03080100d00c80e507007003103400c0110b40f070b40e01c1046040322298401c05440703a403c20341072854054200182113141038012401c0010709 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 588747814 1250 588746564 588746569
    0x2010309031806020c3a03020a05011103061f0807050705030c030a030e06010f060215091912030e0c0906062b020403020a1212050f0d0908030402030d0801080309090711100605 77
    0x141c003180c1c20091009040710712010300e48450000b4400c90500b00031170703001c51b101e0310f010b070f050845554010b0825481c01100c56004503d05c0c000394480e000440d07051500040902c294092101001078500020f02c2080c002101c10b80160000d011141c080d0003280d04000260403410300c0d55004800b0600029242d4800740c085100410141c4c0c090200701180c0c0b0f14050605000a66500c401120040000304072004a840010f0510090802440c5141d0258040449040002d1241c0f80c0d90404400240f802c100d507000004040764602c000503000340300c4c070740c03548455080281540140590404155050000c0202c00c001017180c001280795500380940c45a1850041048141490b8454081c05100e4000a030026803800021100541c040c00e080d600d45203489448000307800b84084450307145161200c00400e108141c005140b003240708404954800e0381001c42120f100c0c100b0311901600f070744103110150750781c5408008903034865800d01c1c240d84049410b60146140003240e1101d06c0619075203440074849070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 588749064 1250 588747814 588747829
    0xd0305060612070f0e120619060f230603070908010b0d050316060b0a090f05070e212b0212030603030702011112030c030a0606091202010309031806020c 67
    0x1100716812400d000c0040007000a01000811071010406080c503141d520314010002446200c601030140e00c5150042200d480da143d0059800d80c0d40d811101c10004043e4181e0f028106c00c1e205070302c8a03600304034580007014098080d03040800c003103119120045070705622000080c5210301c445603105031219280503107131030031240d07010348142c0180201000344010404c00403c840a64010b010050242c503403606086c1c00419030303126090b07480050004001014200c9070404101c400d10f06c2d008001d207844c0c40909903244030f120f55459030450114101e0000c0010080ca4120000b442c010a4400d0500c15002c00c0c1107191824503078483d00038a6114040b5200ea0402c402e1110000001c40a440c0d414080c0002e0790300d0055480090401004c100c4d000480001840150140c48020080c0d548a00f05114050044d4100721241034000f45050070001e1200c0c0700d9500700040700c240c12455141480e0340c1d00114060304222034140d05212404111010400c0d04c1704407a4010403183e8007400c5191940800c01000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 588750314 1250 588749064 588749071
    0xc07050d0c1a0103020a03151e091a060306040212030405061c0e0c1f02100203090a030f0c0c0b2508041a04050306061210020a08010f05091501050a0318050d0305 71
    0x40480c0b1001800103865005800c02502e030420b80790210390860454400c00340c806010003695010221060f01600038150300810f03080d0f4440e01d2604440380c0d2010080030b01307201c11541298590b0200d400301d0094108044080340c140c0c0d0034815a4075054440b00407800c0d9034000030604041e01000d0a1052186500c0c4c4640d01d004c000000c090a60303080c4404c00244c11030300c1c3c0f0b130345200300b0301c00d02e011554424020440c9910341002407a00707544074582104c181d0b4449802c2e00040e03002c245204650100107204680d03a22074168404201c00801f410070a1030041600451031007000c0d0720710707280b014090070110420030519a20410310035949600b4440d035042c0040080c40044030303124044c0b00174030082e50302042d200c0c0c0c031042c1a11001c00c061075600b0001e292696107a016802c56200003601d002003a80300b110f0906940c0103120b400413141e40c8100380704154400b200e208542c01400b0703415000ca9132042c1d00030091014180750101d01020151205403d071440703908201ca40398001040c0d080e465805000d201d51 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 588751564 1250 588750314 588750353
    0x22081c0f020606100f0e0901090608010506010f020d0804020d0213051005030a080d0213120507030c050d0b0402041a041a0405160903111503010b03040b100501090e0c07050d0c 77
    0x500c1e0401802007581484960329090620000b484917903409031081104200c074920051940c481544c5d5403240034000e00c014003038880f00354203207400169154040c01084008000d11360061030302c0d000040040700c24a202801c00c030f0344034599240d000c0150b07603005603034000fa880807000061141412158940ca480d502c0e40030314001e40142e01d51074041000d2800340c5181016080c40942d071400440c0c1e40810400702504248054a01ea82d201d0302404000500c550980f881145030041c0b0790388500401c0128660b2000c0100010b040c20000350040c20150041c50f081c950818211841e100414005003d0703400007070348801048001d4000004601e0203000705a089036250103812102468014010701e45809408040c0031f03c07042000680b0b880d01d9555103131400491413201c00381c58ad6100d18050006a00c141da0650b01e0704c5080c03020a541c21f514032101d0080b160142c6590340303400d01e40344102c084001c00400304516110705004003804540140403400100f01e09584070046c21047e8a4401d1001038603407078000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 588752814 1250 588751564 588751573
    0x2090108030c0f010c0c08030c040512150606091f0c1e0512130314030d110c010c0e0604090f1b0f230a080603032110091122081c0f02 59
    0x110f002e1b0000d11460805400002d072640c3e80e511000759a040f0300caa54030490300000100c42400c03400101190101500318040003405090320703101c003002031500407040c0403940449030001d01900714107026126201c00106060030040c2d0165030319410b0601400c52982106204034000c138200308031045c81492810b0821101c1c241c102404100101c1c040006400000e01c1ca1802c200080b90386101001512040740500300e0511a403910030314034044ea604440c1200b030041d820310a4038004a401580340b604800b0000d40190305041c90505250080c00106c81450000e507903581c03002d070140700b030171900c0800201551a00740c0900c7c1a10301c018800300e84410080305d404001c004810842c5607040488039800002e2030014940e4540728002419407048025041c2c08600d605c00107158100e202085c41d1180d11400c04641c20195200f80c2281038508001400045070001c1041e01400800d15400144600031007400030540c68843d8120380c074013400d1010030806110502c600e140341c0c5d50701910b880b10007007040c400b41 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 588754064 1250 588752814 588752831
    0x606030b06361b0d02040e0732091c0b010605030705070f030912050d0207090b0f06070f15020c0118050606240d0504050c0909190f02090108030c0f01 66
    0x6010560301045042c030030400c002c0205180320038003902c0110100801c0082981e4803068081d280c001c0d032080c4502c4a0f40710316480041e0046000d0940d0403c0b01c04040050340c98a140e161580000d400c0032071100c0c060107400e1080359459101d01d60030200301c1d44622a114021556030500b8103d00c00141d00200030440204100204540d010042c0e8185552081198450b515940340903541c1c440c0c0e640022456078601d8a01d2018480006a6540350746d220b41c084e1a8625250340c2d0250541d500041c400d600044409003c119a09080006140c081d00451080c0200c4006d0f94600c40700106c04d181c100c41840d00030a02c1c2c40005001e100b502910a502000c2903203840481e92520b444040c0108003d2040e88084400e030101d1100a28817030112a414485607955000503c0300b1004103c1a0b6040da03181c82145086811070178000e40031802480074500500d400451101c48044e1102480f404132119500c271101e6a0041e1604c050301406020143d002c2d58032402c3d1070221902e07014103c2d4448009a0401e44007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 588755314 1250 588754064 588754129
    0xf0c0806060a0e04080403021314160207031103160b0c06010605030f0f060f030d021609021e0703020309030a0804090b031b10020a02090106020d08090d0f030e01090606030b06 77
    0x42c84215400102540503540d12802c0283d12030142e0f50019402001d1940e4560800d410b60344080441c82014400d11095203079030f080103805070888140040940d010782000e10100d18908599800620001e0803107000c4800104981500c455541c080d05500c18041400d11600d80c052007482d0145c012458800e041d89400600382c0010f42016080d0510003100304046205c2d40c0707802d44036545000e4080d044403a05070365500002d66850744a4000f0582004201c00800c0441c406d000b00e45410071000300400812107885107105a55111038001c4040d40300400c0301591903141403000052035401000d81d9904c036458582e0b18804c1d078072640c11042c400d8104200004000901c960280d20664040e201c485d0f0301e0800103005da01d88100040065440341240c4000500395500080e0a218041c0949e210800c40e281c0c015040d84d6104c02740b01e0800858012441404501d01c60703031213000b10700e40d02d00001c40d0305005500c884007140e00d180c2066605200d004100011400d003140c4e4041d655108400542c9030046c2d0040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 588756564 1250 588755314 588755329
    0x403120b1c030c02042a080906150607200109080d080103060b0a090f0c0216030c030227090d200a0b0901020906190e010f170907120f0c080606 63
    0x1e40c8960350703414503410010705114851440030140d02070030400550141010910070101c164448100340640c10001c285450704c15000280036404040040c101612602c4482a45031106e070107140d0080d10500c400030110306400e266055013070550700f0140744842c1401c00102500c586401c81d403001d41c001485001010790000003241125080200001c0380e02040d4006064841da40d032002014508110b028002900240e10080010855400319100f0243c0802c0c0e10380c2c51161444050206a03003200300304050b09150302c182520300952286001c040d200d00d140011800c2c07040c0d0b80401f00740d010080400896030444042a1030044400e102104070400314005542c035120050300070700e107a01840c0400c0500d1401d4064a140d220014201521140400b4041d040070742c842c0e0b01c8200052003582001490b50240032101007040391542d0b80741021011076401001441c0181c0464000e100302d0b84006280c89801c02c00c00d800a1117105454180781c11424410003146060700b0030301c8580c102d0000d0105654603401d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 588757814 1250 588756564 588756589
    0x1602030a11030d0f0203011401030b03030f0a02011e15090510050f0a0f0602060a05060d02090432071d1512010b13020c060a0e03180a08030705060403120b 68
    0x290040310440010951411805184020710f400ea080c1380503018546541e030040c5040e40d412100c1c003460182000011801e171848041100d405400400c0441031a02e6580024080b641c0e0500001c104044061800195151900303100c5090035940c078000421054042900070080c80c4000c414811400d0140782c942b01c0e056984900ca00c940d1010036500200d07250a0a890020310854000c0980da03a650f140c01380d01e88d4012102e4060261802000aa4a1074000b4000300070a07000341c901070103030f51180e848669200c1e108043c00c0030020960703d0b03880e010b250f85614815220759030018000e001d2800003041c22104002000b2058174060f04100440e00c00c494a45094200c002c8599440c0c0048003445140184441484948c020080840030921306038039070001c1c0400350106080701d009654801d0301000b1200c07244664451a00204508414070400b552507501c10350005103500d440d140c0d03650010380b8680c0b143d0b40484403a08618100002d0580000c2442d0f074241c0700b00004c0c0032200c0d0032000101d0070700204 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 588759064 1250 588757814 588757817
    0xa0f02160b04080615130b0a050a03060501050310150302010c0602220602190f1221020415050a08070305150301050915010515030412030b0613030b01080a0b0103140c030d0f03051602030a 82
    0x1e429113805e80e070b03070391021200030440901092b111546034100000601824000d00b400307031241c0e61903290800d005100b0402050301030b01c540400b640c110f900440f4910029042901c02640900580c055070700e003ca2010031004500e03001c5019079140000103414a108100800c42c6041c2c44842c1d03402180c0d28a842c1070485030f1002e01c000119a541c6020303a0300c1c00004036541d02c0300702e0101d801500d5070b20540c01042950701e090540481d0300c140340c804030380d1440391800007000140f840001c1207103140242c00164000011100070903081c1070003404642120003c5824038480e6100c2e40800111b00c20132044540580000c1d00e1460640e5490340302c481c031910003d0320091054249c40c09003001a40f02c1c0d031040c1d5000304010f00d150340c2c410350030b04441024801b42c002601c1c00340e001c100001c1d6445000400803003c0350302490540ca56032075501e40002d14040c0f0a1502501d0007802118144c0d65001c3c842e070408103140d0744070001c541f260401c0060850b0402040b00b246084d85420140211f9000400c0d21070540342c7d07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 588760314 1250 588759064 588759071
    0x150b0f0706020c060106030c0221091009050303070533040f020307030c08060403090b03071d04020906041d0609060906040b030a021f120605060a0f02160b0408061513 73
    0x107240ca40024070807280104064002c40c0000300c0d0550741a048041c440070710b5402c40b4108110305200040b4400112005100c00c60204445601d500300100c0030103800060303051000060343d81c0d03808030342158030000c011500e1340c000f00c4c001c96400d15241540c4150207203000d282c452200c0740c07036910140c80b48041c001a1245030500341c003c04650b02004540c0195a201c26130b4049641c0e901046661940d0a070b6080b80441e2051001182241c0300d0010b5910500d00da81d1800c064505030f4080000040d01a4407258025408011680302a01d55100810017424042484a20743d9103c240c84400881d019002611400c0303c0c0044c000a03550302c00c059600640d04603030001d03506040c00f0019150622070b0000a401c075078080032071110540801ea944044070031a482d801c01c070b002880310210813200c0d540074440d80700000744110800240b044d601c3e0041750003940101c4013003d8031420005c0008040d0b500000b907c81000406004102003440480d4002d00006a080b03c054034920004484a0140b400403502558 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 588761564 1250 588760314 588760327
    0x9060617040f201e0f0d0602070803010e040c080c0f040b0301020706050106082d0115020304080604050318040207020a03061512050f120c1f0605100f03150b0f 70
    0x2c0b00d0386841010340c070402c5626400041841191040b011042ca18401e00724121001c01010351029080352014000b08035001c3c8008010400906041910040d1200c503030903c4008001010074000303501a08603000240f11500d03192400000e61481500040455001113545020303d45407091600310710301084130701040303040d207020120380240220103002e4913140c10400001140e5400c82c420500034603503000034401c84506c140c10343c1402805160307640e102c103082800400c80800c5082c00c401403a201c51059030b262659490189103003030015901079415401c00100f0201c03000d2406003480312080e007590250b0401c280b540004158207101e01c009004651120181100141c0105d03819001c0c04269040708000b507820708143d41d41c1c000c0e80844000510400f090340580b10b1003c0b05890009508034010b0241e81d03005045400000300380742c0308415050316074402144c15640e0410029010300a5510981148500e510088c00c3c0da5800484d00e2540b0b6081d00d042c0960400541181e40e060504840a6034608 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 588762814 1250 588761564 588761573
    0x1f050a091212150609030b06010203282316060213030b090f0106050607080c01111b0c060316110a02090c1804140106030b12030f130906061704 63
    0x40d000001c082039124851082059049508011445521101000900305003000b400a005080c044d040c003050600d88200001800600305982c4038406105403801c01a400400480c0c50882c02d03842240ca04000c0103552506602c14180300c14040d5060700403540803014078a84a49102e40d003104901c0d41d0f01c8104503003c1c0b05242e0115003080e0b82141002a00503624244026918010398101480d8003d140b0138038403403e4140154010b59200404952808459035290506a88014100d60007552140c680800f201c55000240288044552400c1c464101460803141402030501e2424803070f5200744248190541000c00c07541c400d90440c142082c01c2c0c9091010f084c50568140d800a41c00402c800c100300c086034460b00649040200c4540c2606480c41c0e181c104003e980759044040d4150004138010030000303103e41c0001c0300e40540600405028089545207900f181d01030031541c03124080014000c8482220810080000d1054007010007169040610042200c268000c0c50048091900086010301 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 588764064 1250 588762814 588762821
    0x1e0812131205011b021609050c0412060e030a08180a03050301050d03050c071410091a0703030b090f07112d070f06080a061d0105210102030a050610021f050a 69
    0x350b5454140c144d00a412030300964802c091010102520100d00e000903010060b409002d00a401c0346403680d04141c1804081403d8041d404000d0f00e00381e49a00c58144140014401030103554105c2e82e5800441c07078803c42031003d80b0a044409189175100c1c10090001c243d0087c26241910b0085036143c5003940c840c1022546402122011046801352900006a190705003080e00064074043d00c4c4a031800c881c40d00d059460380318034030500030000300d403c12007505205d4403401040300d94424200050040c403000c010807003044040702d13800c500d080c590f000d0144117071b0403554040010550707800404100e5008400084035041c02d42e401008106000ca0080144101744003d40180c190910341c0e0316125a12800100f9003182590380e14526850700c20081171100b404503a595880504001102d2140d1a06041c042d0440301e022602c2070846100d13446002c840c0d028002140940800300c4d002c509403c0c107004201c141321640c40c048055501404071141c0c941c0c02c050303070035040c40c41c4008001130b80c0d030314100004080d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 588765314 1250 588764064 588764081
    0xe040f021e180406060602071203030b0a120b010513110f0705010615090f14010c0201110313170d020f0703030309113c0109090f061e081213120501 65
    0xc8030030104020740c0340140310b0711a8802c41c0914410700c0180d0783c469081ea220320140c00340c0580100d03030b000c040012134002e803c80d400302a4083d18900c2c040d651000d41501d0b045001078100c6644185034010041480c012040181d5100b01e03a0081040810089480d1550310039042c00520443c00031a0210a000c800e502060040000702411040e4100f0307024001c0064081d405149100c050010003c0398207511035080b00e00c3d140060f1600001c4050540055410380c1c81d020700007600e440200112522003c000d140135000f031200801c9400301941814446003099400c107156002c551040d4442452041c00060071001c40381c060a0000f1800010700b042c0b9a035140001c2026081007840780c22001199124150460700c048403441c51400018050f8000320307014243d10003a00064030260144110419903011250200401200292060344c3d8040103000c100b50350000519900040010440d0b50424080c0d08031040100080c580b900c05140c0300041d21755220b0044d04403502405441d94100b201c2580120407 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 588766564 1250 588765314 588765319
    0x18010315030803040f03030f060e0a05190c020a0303062c0a0605030d08251409030102040f090c08011e03030c020310050a050618011a0a200102030609010e040f021e 72
    0xc3d04d1409040a0f00007010300041100086c0c641944a040100301d4031450056030b01400514807107840360b42400018140c00713819111030395215404402c2c080b10b10301c10540700d070703401d40c01810a00340c40c4d05022301240d81d198001c0340900440d002901a0813041900c0c0741c00180781903000380032074448442e0782e8000c215580040e90544206d0f2080454542c22258a5210b242c200c80705035401c41001117103100c3d142d94452041d0104132942040c001d5808600040c03c0c40e441c0c007500045c2003030340c3c882c02e00220f622a5401000c07000e540d1049000000c0d031021003030380503250f030b15505000c6071400540f5101e4000d00b1310010f020805112100c80456805201e48a920300a1200c01d12450600104000040000b81d4030144a070b60780000746030108000d4030715a4120f40c081401c1c0c2190510340d1a01503266844000158108051440c01104ca4448414248005441d0400058882c640700d01480070203034060300410441c103101c60411000842c035165000150340c1c1038a1507880c18088040584c00301284040c81da9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 588767814 1250 588766564 588766567
    0x1107030c090c02030702090c0d110409140f100909060b19080f010b010818070e01031208181b010306080f0a110418081e04060203070c0b180103150308 66
    0x500851640031000c0d5000418200400401c410060b81d0700d00c45e440c402500407940d440000d05021780304018045440840102085c2280e42014511050b8040c3d00103840701030f922010186041c41c600e01040d4080070030000448a030070403028140e0380c8500c912a084001e510380d9070311001c008a03034104913030101c4054440c5400c200591a11354140c021070148116170b00c40c5c50342400701c021050003403104a01040e100c1942075216a4403070151304462411714212071007030b01800031f1a125480c0312540250301402d11102c1c1054041401442090042c0030b0015185524114691a2502080c480780140104201d00c03400d81c81140141d000d0702181e800203015008440c00d5000c400c42c003044086859100312100160131407500c0030441150b03c0074100360000a110155480000c1c504801001600c0c05941c6812005d5200d6002c8660359029401807030041e08007003044010811150f04040140c03411840480c00c0202641402c4501c02d1061079450415481d4880c1b041d1241f1014140381c00303190401001c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 588769064 1250 588767814 588767819
    0xc020a0203060c0f091507020102010b0301060f1403010204030f150501050102030717031008100b0108061e0603040f0b07030903020d1125030503070503280203120910050403081e100909031107 84
    0x61046d6040040241c0c090b50070444046c100b460180b00723040603540340c5481c11120b18140301042b40f41d060a00c000c2038266508010200100c1e000000002c0814814a105500041228418401d444040c0d200e030f810f552040c001d03e40042e482955100c3c468901050a680b242c0d907219400803001d41540c040c00107030250707040c004441d4215030800c0d40d2015003a25010016111303c41030100c0500f44141d4446e0440c0300e41980e48441c0b07400302c0295085402062810030000880c0c4130b8408414055440c000807981e20880e40e0704140d010b0218601c440b2041c109650303e1084d0001c0c0c0d68440000c003400407000021210b1b9030201354480508200659044404c481c1c8600503442e00700ea80b45d11240c4444e144140902186020050650600c0ca012050394041e508007034031502d861082d40800f0301400da481c006d1581e82000c070441072003001c1c0700300d00030b960707811560801c3c80c640102059189074012910803401c0412103440c2d010b050080c101d5050110006185285007001c0329601800a80e2125078060240300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 588770314 1250 588769064 588769099
    0x718211b060f050a0e10050c1204030c030b0601052205010e030604020d02010318050f010c0207050604080312180d0305160c0302151312030603030f090315110c01140405010c020a0203060c0f09 84
    0x40c014241702300e4200d600c00c100ea400e008a1601451200400d044074403141807000030840c8810640017403060405900384501d0500d8183e03060300c2d07000440c6a1000b160300030041982d220ba160b41ca4080c0c00d402801150900341c020031005440540c001e41416268503520840d2b042c0e061007100c1342604101590030488807564294081d184002c411070040c42042d001240a141c010b080702e04803040349004501d8503400b44000d40c3d00034001025142c2a40d50100c2c0580f00250510001000c21450760700001c451401c0101d8034004202d040c041410440d0000e044000641c000070310404424240401c44041d03074400d40200300d00765200324001d0102d185000b00503010340d010b4002c14141d91090b1201112160b44082c2100d4040d413922000d850701144502040c100e52031030b80018524641d101a0034034007040160a1401d60740ca204404402d81c1103c1c0030801032060130f1160015008051010f06042d080680000350b441c040038004a5121320001501a010030b440c1044414201000d40703000303e01180703400d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 588771564 1250 588770314 588770317
    0x1506041805011508091e01090c0308030a050c0306031b0d02040207051b030303040c151101020a0e0a080a0b0c030703020d0507120c030c02060718211b060f050a0e1005 73
    0x354040a00440c6070020f075043c01004000d00ca000880300a001c0c506507180c1d490318800751442207a000f55a500c84140c00308442000e0a8007440c0204409a96410301c2ca80c0f050403648000c01c4441040001d00c18004039507000b081d003100200c04410303d640400d000034005200c400c2030040081d070140c800618202000380c0420141c40c01040c0c50b8101d06040c0383d40c018180c980c4030448004050030604c3c3e03000d0158407503001c40c0a05a01d11071520501355860020300702d089030b114240039004a681105031211618101440d00c1c040c03c0c4c910040e00c5401c03940da0f41d17001c009101500084202c1b8020001030300851195040d2170101100e04001d00c13640c204004040c010100c2d5250040b80903041603107038580d22b4040c1c020301301c0022960b4000d00c07965492142c1100c4401003903011020303070450010b001030746006541031000841100100c8460fa00201d107000004010810920300f00b612440d0003c00c03065800501d4001450a6814116a42ca5204108507916414000b41540c0031210100c0204459072220 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 588772814 1250 588771564 588771569
    0xb070312050901060f0605030601170705070f050609160b0901050f1e0403061112010611030d1505012705010315030b191d030d0c1b1406010501090e150604180501 71
    0x1403481d180146c80311011550351004494140c04075511000880d441f18212034040c1d0f00100c1482c0c42418202c10f030b541c0301965204000b00b6038180d0700031000d10200180510024441510702c44a40151034581016900a400385a861078140100030521494100208048903803116507243d003003021840c001e51200c07154005010686900d0300c1c140075400203090300400c030703030000c1440c1090704841e07031a00300111001101b100284225000c10702602c07203070015501840400f414400b183e1442e9905020005058581d14550302d2140803001b6a030200700e0780402080400d4071002c1c0380102d8800400f10003082105204e46c001000751905804111001c59141346c240800c0894920a00c5010140848140240301450481c81300e41c1081240d20301481481d44140007588843c100001429011303100342d400d03689507190641d01c2c03007204000c5505d000e506002e9075002d4070090174020045814803c060540e02d500800007a00c0b03d00c5842080c20b10741c1c07510240c50003814400724440c0c12942e1020100d01801080c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 588774064 1250 588772814 588772829
    0x60d0f0f0b071b11030f07061706060f0a030f0902090702010b0a08010618020325020304030b011e063e06160f0c0309120803070206060a08070b07031205090106 70
    0x301c0455045481108108100b40f40d100c0e00a40600150710f804003000003102c00341e58544900c1c03e000202c4d08040c08050010f100545650f410030401011103401901d0013881c180c07290100700280e401844600c02502c103407801ca40390006405408203010300c020084514040c2d400030000c000c002003150b05400412a0040c2a1000c107105542e03030314020b0903a030b80ca004800e990615100c0110040019a0241d58800c001103c1c1d0781c204120800c190304031240401004005800010b070500510000c0801e460040c50700521100c0f500820700d44100c4880e02038051001000008000680c01c0c0c0503101c0c60300d0b01d518100e881c11300200c58540c00d0b890071407001c0c10700d10b2a5000e4000012801c000c030403060304151800c0e403a040b034800e0302100700700c4001c1102075045043c0502c240d40443e01d11411b481c1c2c16a060302c0381c6815590703410414406840c1410007000d40c0d101c1c8004000601041c030022501c0000c0b10701e07494010740c80d0f401514003600e0210684907a00c407032510b48405c01c000480150002c40444100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 588775314 1250 588774064 588774083
    0x1416020a15050114040e060705130509090307200907050702012d03180f0f0c12030c0209011514210a090c05240f16030f0206060303071a060d0f0f 64
    0x132800d0100307648100d4500d8003280c211600140c50f540c01100108189240300380444c1031903894400003025510700b51038400041d40003159403410003c240c4c40e4007402e444c01034004080e80c00d0f8403000400364032004040c03104002c80401c07500e085900685619080004a130420070a4407012a00108600c1c00412002c001a04081220f00c104009113550349040f81c002d1644850158291240e8489000e1440115000d010180000801c001d000100b200300c6c6200396070b004448606030041103020941078001802201c0c0c079440070b48407142c110141401039042d104940b03407103881c3c13549641c04503c0801c40c05001c0401e42801c00c0300e21401b591014031582d209090300c000c181d450f40184002c0748403040c04065800d29800c81b003d10008980003600d148080380700101c1c40e1070b00c40d480e071807010510500c0840100d031840c10000e4056806011007980204240e0013182040f1301e80d21a540020751074140c9401c02c000c010701240d010780356420030704800d640000c203610429003503141560102403a100b00341c500034078 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 588776564 1250 588775314 588775349
    0x5060a0e160b09040b060f07050604030825031a04090507050a08030a050708072105210c0706091407030b07030b37030611090f03011416020a150501 65
    0x8066600d18255442d081c161820490180c084c4401401601c00181d4020414403200c2002c6040388000c024640c1f080303000c2d0200d0f06091901804039500a42001c1c0f0080110b0074841c400150195004402c03601440c0c04034003807440701042c000b19030901e20900e80140c1440d8585082c400b0010f801001c94a00b0f032200d0703000d41c2c0e4a640b199101e014400910380010300070881407011540600c043e1010138081c098850f038961050b031102010f04400b501100c08101c0128903440c00c220042d80c200c0481d01d81880030780607480c2c645111855885095001404980d44440c45018400c1441d1820383c20180c00084840042e120304203d014402e084560704d00107400c203030001440342817014204103442e411114080d070503507012861460040040c0c4001061400a120000200743c3c5405010b4202d243d164049a6440c1d880c403d01903100c0315110700324001d0b810294440b041c0400303007440503800701d51f40010818a810403201241013650003600504041d49080110220440640c0024102c60031008040c51484 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 588777814 1250 588776564 588776593
    0xa0207081f020d150b04050f09090a020d03111605120a030801120c03022107120503120403021c0306080706170c09030a06020315090906071418030f0a0c05011d011b05060a0e 76
    0x6011239400078ac0d5084508c02c85c0050070903a15201800d0700c41d00341403100b400030030912032600c00d00c41d4101c103d420010400b001241000e040308030f00a03040002a24038142c0986000e00060380600c20b10001c00d0045002c0f0040c4aa42d5240d000510340c0104001c0054003042070100c2800c2420f000b188071805a21800500003848600e28032021781d00c18051400d1070036080ca07003524428010000d40560180484400e00160820307d40070340303ca80c0d508e00080560402c00010718082e91a088602400190188035035020b1850a20f954008280521a980d51043d0f0300807034240000e8100c014111070000c018011940641c0842c2c102d045010b030340e07400c1595034416000c0d540f0388095941d0b0000c01e0304807880c6000841d008004001800f518401020600440310109241050035403c19007142c008008840804c0503564481c0014042480d10705209008102e10b50000c5480c10595070510010140c487c20150b8020202c2910070b4001091390341510f0442c1c0804090600c81135140064011907420b9100344 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 588779064 1250 588777814 588777829
    0x171902212a0a030e06090604031d0a09020a0504030c03030504080616050702010e01030e070e010807090e25260f01020a0507110a05150a0207081f020d150b04050f 71
    0x8082103480e50810400c80485407440750301410a00c010503440b10452640e1080801c01540585001d04c010031903071805050062220010740720802552031002050f030070320794606000c0360565044680050792118210001e0b545485a584000e080300d0b0288000400c0c107402c1380162007110311410030348113165030792042d90a040051031414000301e00e00344002c0c005548109880c034806041030500003200f001c0c01d00c07694500025640300152617050340d0010b01c00450148003c1008146000083c80000b03040c001c015140c0c5c1f4035015860280441100929000c08108050002000d002d0b20010030407030050064403510440c022101002c2c49081c0d0040f4a10805100310390b000c2e100740e591103040100320f50380c800c0c18060103184141e1280ca003c4020074541e071450240c4290303044021880b035540c101210003904004681c6d2007101c2c190050003801d11905a428440e260b40303941074030016511490481200002c05d40011059000075820001141010b2010001c00947d0000c8a4040d01c4200134020082c10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 588780314 1250 588779064 588779101
    0xe16020c01050d1e111b0705030a02010c03030621110a0302090a18080309070806010806010605030a020a020a1202060a1d0c010e0117040f110105030717190221 70
    0x142003048000311490180d0b0142c0700100d003019414650030084140d9a040c0c0c0c5c00844480762040002440c41c04030070511103050310508440c400740c4803e40c43c090009450b00c0c2c3c0910003905002d017030104d40c020141708c0d510607005044204041c200c00040c6181c0b0304549420104200e130004036000e1000480d2801c0c0310701c4000c5950003401000e4503075810f41080c000e4840d0f0450000703c8080d00300746100040e9240041d601c6040e0140040800c0f03460030640500e0144180d0000046410460052002d09c0d07200044a601200701000560741d101c149400300d18103034500780d014044404000105140da940072a003140140c68802c8144000301c007420f5504801c0344181c41100380c0d9445159014001e50244c2d111034516001418501800b402d400b01c0982090400ca9080322101d540040400810840b8128100460001e02c4c00900703524140300c0c09090740080401c400f4900b4036110014a00402050300e0314808d20f1645c0c001c0d5101c101008503000c040b801c043e80d24080807a0100015042c01810b009241c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 588781564 1250 588780314 588780317
    0x5100528080606040f1e0e0c0901030b06041103040b0f060d05060f270307020d03050708030a0203010819030516110301020a05040e010501050906073f0f0504061409190e16020c01 78
    0x151ba2100c26810001d0071642c510201d00d0150344543e04040c6c1c1c0d8828080c1c0218011941c0603d10719080080200305c031001104051080800e205002c04185032075042540410b00010066130b40d06e6800001d21246074a81000b001d6202c0d010030841302038980310110b4020510481414000910165190180c803003802c01034015900034440d01002d8a00301e03503440c0c0d4060280c2069803802440c0e4603039520710750049441c03007020b0303030008010085602c081042c4c140c104180442c3e0013440307201d55002005803091000c1c04421007400c2c030041041c032500c0050110a450014000c5551f98020718007d005a0418400c1c5100d415655000113504c1d40520120f0b00c460100905e201c3c0f800c2103540d00c0c0c009801d6804190390042900341440420301c0011710150039444004400e1031792416607030b000104407100c0001528104002032000304251070300000b520701501240d20081d03482e01085008103128045464000141c6840003600040041040c80c88601800d02504510224080d00e942a6580d000c003014160 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 588782814 1250 588781564 588781601
    0x6011d01081f0609060f030204030b010510140d0c0815060a1b051516090e010902070215280c08030105010806030c041a01030e0105100528080606040f 66
    0x2206600c00c412180d40414401c0740310140342c03024060b00360110300c150071510115140c001d050003165007242d6041560101c0d45021341c9458115a100486281d040c0b0405021300c20740d0289081c11802101c0c0080000d80c0a844541c96102e40703244200608145c100e910041030400e00800d45190000c01d0569640f41c010303003045d24224203090100c90820500c0301d07400043c40000281c0c00003072001d1107000b22002880c01c0a00c8603007052440c004080988411380e1041c48000381c0100101103604640300d0440d20301d0800140c80e61001c2c00802c4060100300c2814040d00c1c0001601f05a030110702d0381101545081751840c00d06404d81020a6654048000016011210034001080f49600c1040b030554131130000303000d80d400f4400080104044d10500100500b00700351600e004022540d05114031003909411070000d01072070508a01000e26511503003d038074003031070f1907200784205928116442000c2208240c04082c060781d48400705a19500141e8040d84254180b002403100b81301c59008000e00a540d07107501a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 588784064 1250 588782814 588782867
    0x1504050d080a020712030c12031e0b060403170703020d0521060a08030d0f1a090c0d0b03031803060a09120806011e200303010807062615090601 63
    0x7002a6048003007900300710700c2054030200da1081441e40740c2e15580d02c240c96400f140c00051400b05501c00100001400301f51a001c00e208030381d08458aa06626959440006822805813022550700c0c841c03030300b000c1e024600340f551041641d00100f000340b4082e8001e0b401d40d140d0000d0b402c012121880b0748401d81c82080283c0440b000200c0d101240550061001800080340c00d44d6620002d0850308248a8400c600e80c0d14034030302e00341045a0082400c0e24030508440358807000c2001c0007480b0700e00050044101c1d59004180c131079065203258003015148000404407501c0346002d007100400b0754861075440d8041c1c00f4074808549149454003a40491a0b80300c918080c20311001c1100311490b4000510890411061000f81907450189905480741464140e035400030041d0042d0034059100014a021301c440c0d4020001003210001c0030400c481603841600e840c1040114183c40c90002c0700610041c00c00e0303103e6401c14800310101c0c0c940044034040c02511501d1040d0790b1503006480b51031800901021aa0009400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 588785314 1250 588784064 588784073
    0x5070b0f240a030204050c09031606020312090a020a15090608010e0612101a0a0b0304260415030504110d0803012106090308040b01140607020f120111091504050d 71
    0x10085100c01c054a400982c41d82d07600010151001134941e090004000a40302000d41000d0104500703244131203004036045441c0040c000c2d40c0380b050200d00b82c17903e10141d0104e00d20480900a0740d14043c0c0003000036550307503200e500d0038200c01c00001c800004282d000c10005200360150782c95034100d070f03a69090b81c2040d590b02000e00022080c486440f4440b40142e00d013076217015010b032040002032700c014a512a18030500405100c0d2962580e041041c10120900800000503410414115a4010341e040b1060700d100d54032005c2d040340255004518000301c110f1801c0340590b1326501040c4564025002d00d00b225810409110101c1e0400a000d00242030400060290544410003d600a1002251b03900c4400b0262110301c116080041e086001900c2c4909020034032032010086409000904a07c05009080c000050b10b01c2c4606000207014203140c01e00d808a503540e81d900304206c00084030083c0242001c44826052907032007441d007188a510780388480b00c06660f4120540301036810127041c001c1c144038251103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 588786564 1250 588785314 588785371
    0x915052817040201200d120e1b0604030b0f07090909120509061b01060302010e0a08190c0305060a0e1c050d0504020f030a0501020904060e162003070305070b0f 70
    0x1681070101080c02d215440903848400c540505d2044081d12070181388035002850604a41c06100070103040c12581c2c0c2a0b26004100303a03040b1102c21003d810001039840224980f070086a201804a610050400041d0301380d8500c0b00b0302c620200d03030354003042039103d4103031208842c048a000703003116444a1142c00403d001d0ba004008004008048a00744072400ca4500440c0b5281c19450308a03944540c1c00b0001c558000300c0b0796520000c11201c1611950621500568a003150403030518903030340001610301400702e02031550700a141c0040c165001c0d072802003c5640508185c040c40c0955201d032004020411070600c1102034419160741d03829141a00f0081e00030090700f800780060342d000001410401444d82c040103035114440c8140c00160300c4025280401c4200d454aa20240121021804020702c0e4401c0e46103c444004280c10425114610074904409881520110000500c400a6000c0600d50002d000d01581885580c0d003180e1503865071011aa902c405403107018680c0040d51490450919100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 588787814 1250 588786564 588786571
    0x50a0c0504081b031908041e05060d0207060209060d0509060901020a0912050f15070306080c13020304150510082802010c050c04061202040e010c0518010915052817 72
    0x60445000005c045048410710ba40024102c07440301e0002070412031280c8000034031018621070800092198942130201d0032900c07464240556280c1c1c00200013042000d9070f0b0542e5040c0401515407910b50044c10700d28402040e040d294186c1600c50400080d501c0750050080f580280010754403140e4952400350030769228640581e0449250046c0340280341c04074000c2114020101034402100c0302424400c0c00581210320a4020407074541085c81074486a446110150045040c5080c0060783c03036446003000d184401da58204424414208410300000305c8028283c5010342d0300c460709071030045412101c51101d02c094a200c143d02c1800c11100c107400b56002d01c0d4000c891a01541c10f0310795005643c000602111072030380082c008043d0000124056003018800c2d4030008201e00c000f0015481c007041c01402501078103180708521404070300b600080d43d12818140009003006583c03421881c11800010300750341c010800d509440e03580682c0c07407050a80c40341600355032041e154a44041c040801d0380c25401c00c81000b07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 588789064 1250 588787814 588787819
    0x8100b1f020a120e12011103060f0105090d0b090c0105130b1308030a121112150301090803010e1609060e04110405030f010c18050108010e060312030a050a0c0504081b 73
    0xc0404030200740c036407102014090442e0b13608103240c1ca824080100007011030051080d1a0300d0300810382402d24800e4220380c1c200008850f5625030220381c00040341c1503c5501605900306101c0e84141c0200841e00410328040c0b2003201c1600d000b40c510703a00445d1a8090300721140ad0034061004108882c0303000d0401049e21211120a800700c05482d48603c9142d540903a5154000460884886003000f50324403034019410159070030b50b0314100c620340340b0038101003016280c5100301040c81c070b00030404d940940c4860207640d1f00c66007054696a4480c0c00185601040382c95800201d040a845646c542c400c1d24100309482e0395840d83d0760002e03004814000108a11041c03040c0b0400c0410012903565410403131800b558009900219588010380360041200038000c090450380a043c1c1d40502841c4e0f000010f003419200e40007481c802c2c9683d0000041d20b40700241240411009002060001c41103847d00014401c3c402c0c0c200521100700d56005c00c45c3c140c49244a103500e140c000301c062000e04550506c000c050f10000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 588790314 1250 588789064 588789073
    0xe0c06070218150a0e0f13080d150f0906030b0a0603020604090f06030c12050f0319030e160b070c0e01180515090702010204030c0f080a02060f1e030108100b1f02 71
    0x50901168001c01e6580100c403172565220100041d811300e010440d9030003402a0048044c0e18099a2074840f507010300070203010300c2c58032001000c681c1c04910148200078054440002c00c159514000f5100910560005580c0320b45000b000031440301d0a4064001220740c0602143d10b0702e40341001c0b0070000e15034024520701c1c2d1601c0e143e000020646a400000140c10040c0c10250503440710301c0c05070700c1e0104980411686030030078040810074414031a48031382841c2150030041602007017000301500f05610100131096040394280d011606503035a4004d07114441c0f0074403042440c69124088005040024800e40c1d9403203150785012240300003680c00168000550b60103900803010700400049000d641210b00c0c4006079404107041003803003039040c2c10760300502000c12070996086c1080c01c0307070352601c12072480640600800184103082c020722804442c88024044c10a82e8820140ea2802d042d5900070f10600ca070300d200b402c41140005400303120350076020800402641d000c00710721a281c1901500c082c10081075000c4c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 588791564 1250 588790314 588790351
    0xa3c02030613030306080d030b1804050706050a2c180f150303191d120c04230a0903080c09010c170904090812010602150712020c0307060e0c06070218 66
    0x1b0100030180c00e5200c20303100070a8a140344402d104401300e000041194901c403a00500020440101e040790a883c1e60b07180081e552490110103540306150b1030b4007440c0701000c0320f2860310071410440b11144c0d900000c1300e11501e41d02c86000780e101d080750166000d444458120000c105160640c0c82c500307401140103419a420080f641e60780c40303210384003804903401154080903d000020341e0040c0c1140c1d4606c0c2100e0ba864041d0703a03c18159910100310010358021a07840c1c03c0205071480e00700740d1341e07036451256003070342541e10b05603983c00c0140c940340008401084803075004c071301c0f0302c0c43c01c4050358500b0b20103940313a019889198a03000e107501c0401c0c2900c05440c3c0f04110709003181e15240500d55000380110300b00750b03503070010841d0b0300c041000c140d2000046410410301e0ac07440ba28078018842d04030b40d051415080c8407282000b000c00038480c1c100c042c555841300040c81d0b020460b0079081414140c0b0b4080a440000800a00740f09071407180c118025070080024131348401c1d0340304161003160810b40c141c401d5940502c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 588792814 1250 588791564 588791579
    0x30c0506090601050a0b1e0306011106180607030608030d090309050307030605090c1002031b3f0301050d1e14060a05130b01120201020a3c02030613030306 68
    0x200180c4400100b900540014006800c0c111844401440361080003885d214100c0004070390609120302420080070000040b9510768802c5013400140e81c101010b464032400e0200e41d008a0b4030a2508401c114000d000000c0c1c44c1314000d10415040310f4821001c0c40c078245002c02e0500c003c14480e1030403020300114000200750780d2410400140950b2081c00c0c00a0749040501e01c41c0c0c03903c18406000ba200791030300ea03580d0b8551a404015500c401c19014810202105005c0c007890420b1840c4006c010300354580040d40e0040310440c80009800745030040952540783c004008107280748000d0107400d40200344000040b002503100c2d0051a0081e140800140c84088a655032007041c400384011000d607940100c040c0403a05880b4890290450320300d00c45180544125507074205c1c2c4410502c030340380384c4e1041c8485880640e4006e22181d801c0e81e500c00c00b40c280030101c0898010300b803031a00c01d94041c0c00c1079508213040c0a01050840e105030640050042c4107a076980e00310143c1c2c0c80c00009048042580b01c42c070014406 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 588794064 1250 588792814 588792823
    0x9090106210213031103010c0f05030c09041e14161413060c0209070206010f03080f19030c0e06130306050601090b04080102071109252f070512030313030c05 69
    0x96a182e00300300d240f901c1c60502078407140c002c0402602c2a490035002c0481f55400503d026a002d0490030724648944d54414003240301d0282d86001600581010395144420f00011000009441c400208000c040394084010324a02c408a500010003102840b80f245018000e00312204c1141e403841d210b615140c0602940005888203601543c0494842c2c0c030b82008603c2d103148401e13070046451000740f43c40d40c0f400c1e2040c504008984005040440000b42c40c2607901c031150221000c9102001c92410780c0fa802c2c0000070f0060220b00040000110030041d1801c2e20b242000403115041d02d003807408010141192103c07001000080c0170b00e818408044000504e038000d41c005030000b0000d0000042c1c6500490828445c07092044050500c00e500c55010000200d251080401c0540114540d0070b05c002c0000d40241c0d00f0180c241d15412014210848140202100d0560721648400300020f5800e0786541e80140090800040c07074560710b40d007060002400c1340904d40d040105c40350203881c000c0000c0700151600d5092 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 588795314 1250 588794064 588794077
    0x90703150e3a0203030103030318020301091a06040b030322050a0807080606150a03050705041d0a060801050402060304060b0105070804030602030603010c0e0a051306081207060c05090901062102 85
    0x440c550900b502d4810075064400003040d01e241074202c2506404000c0203407203102c140001070626617180c000b0600ca0784640450403107168007500800549905042104844810018400e404544031001498504060194071080c00c8090003e5080c428060050f0b002c6e8140740e50380c2c59880380c40b52400150b960300c024420700100700070070140c070190f81000c08540c20104014045405001050320001c3d00c0c1c1c110904498146806140c0041d00351108182201e40e071040754440d8103040f03150b1040c45a910344949c10f441c003942141c601004216507c42d286820f0f608110380c040d52292080c8006000704d012500701c81015803051600c185001142d030382e9800650080d8006a4040b0740c04410045141001d2041c2c0c0c88000b8a420f01d0f0740240b0b0100005400030700c490184034010300e5480080071205605030014005000d0101c1916034a840b124002c1c205900a640117031895400c081c80c0c00403d03030140f0201c681d0048040d000b640c4907820450306580202c205084800c452502154a0314000c10a2019058 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 588796564 1250 588795314 588795343
    0x4061223160c12050714060108071e06050909100e0403030c020f0609030d18080c0a0c0b0c0303010e13141c050325020a0f1514090703150e 61
    0x49401c00603188100e0100030072108040c0440c03810120041051240c608120419600c0c05a079101c4041c949003664000d4400e1180f92803007040300200c4c0d0414003003903641c19030b910440554003c1d04e40240b4034019180034402d02011403410842c3c1541e6085c16201298400c0040030042000303503689003600400c00b4100c60075030000350b0719507002a204d98180100d072041c005100c020401c504008071095101e10411103641d12030341d075a600d0a401840c1601441303d540760460b40701501c41035419042c54644404840807205100c9019000c81e207007071071409540403103075004015800c6a0900c900b5640700c103c041c203030005510756031013004000f85d0165034040e04920a41e01030803540f002b042c0740d0026041c59000b00e105110303041c4104000c5480c51304100c00d0404442111070440d10403001c0c140c2c2801107000c00a005019042e0041080c0080c03940e002d9401010400b041181d030a0104c1d01a0342c460003a601c10459070024003013000030610421151006424044001500e421340343c1d406454607102c0d82c22140d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 588797814 1250 588796564 588796631
    0xa0806070309120f0206060f0f060d050103060b1903020405041e1202060705120429070f02060604060501020606150415030b040b03030a081603061815050f0105040612 73
    0x4104005807295030f1092241002c001e00300c000d50340030351540307030003000c1c01e02800052342001195a142c680b04015030304084c181944d2a11440c190300302820007400306803225414400c48140500344815101c003a03c020701e02140740300d0b0a680c00c10000e014040c106844002e841c961408101100e0060914142d10547c2d15920209aa210281c1400d000030406820b0007001e10002e401c0202011a8a600903849060308550f1410250030200700704034800604404080309080040e51500144d5a08000301d0907002c80d14a6a10801088107440081c007401e4016000040402d12034180b51554803c070781c4c40c0c140a141055104c2942003a10319400b8074107000691503030500302103810917104007000402c00f54061841d100c0140b40240c8440005030a05440c80800813420803e68030035070142c00600040020704109603140b409c007002901d440c213010b0700d0406050034005101c0c500301000d6587c1d00c00c1030315081d003403e00d010410b0341d1512140f01b2003c2003d0710f40c158903503000f0704500c05403442c1130b401d140748 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 588799064 1250 588797814 588797831
    0xc03210203191a060f0903010e0102160c05030c060d0b04090203100c14031501080a0908070606171515010201061203081801050403050412020d173601030207020a08060703 75
    0x21410f48007421003040e1107183d101c3e41d00350192600000c90306004201a030312640e0b00c2500010034010400e03440c151206500c00b0400d022108002564450400d0290412a8a05484900700340e12048001c1480c1c2e44440200042c0303c0319805c43c0c000c0c6610365001800090307000c040d500401e0030300030704241d480c50701079862800d10b01a80d08070040140b10782150305068150f1030080c00c10341c21070488100355030522a12000048807482950418031005a100752040e40307800e22132410704042e00190185950b841c4030500310080c1c0240000d01050b0300e0740e0380704c40d0581036240d040600500701420240e060465403100300201c2c185014101822980f80710f80d40301200740c502001800900340403c0d220346401d90601c814070000c680d01030140e0f03040e2404105015001ca060b440011607210241c01e008105440ca0b108036a04094801e01030034040001024003e40f101549000180d40700c034141822807401c0d800c07412020554400d80c050103100348043e1400034003944401c00303a4541013085070300000298441048 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 588800314 1250 588799064 588799111
    0xe06040c06020708073008070b0406110c07050108091504080904060b0708042c07020c030c0103020403020d0b040807141b0402040302031e07150518030705010c03210203 74
    0xb90710041003102c01030f004176414604c121401c145103000302c40c2c244003005401d50100d91207959102096510054880d41c5001c1440d0500002004a9054800764034002030300e00700d40c24603812100d8207840103010b090454103210042d01d0016000d081446180b0078065924a05247c4410765070249014407072894642495404100660b40340d500302c003010f40b5040c011040094006000d0743c06489242d611014403a00320348242c4500c0c4a002244001568034100340216a600400c1d0111403c0c420781c1a5900090071070b00541c2640309600c0025000406040f941020500042402d90401d108488444c83e104003038a400500007103d1340c003200c851708240c50581c40401c82c8841506801015202036007424034640004e500d8100800f510152010b000c6201d1900000030700596000e8a0310306032801e02d01001840c0101079421241c24041d8899003a103961201d0b1900003803200403a0380c140c7d62810080e0503a071301251402c12402540846c010412003000b0400514000345d0f1080146440c00e18010419410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 588801564 1250 588800314 588800323
    0xe071b0b190c0503060f01050a0f050307210b090f011a030c090603011512050411060c0a1b030303060806010f120f020901120203011a0102100b15030a05160519030509010e06040c0602 80
    0x1106c505000c400c1092101003500010001005452030410580701d5441c408150b5811442d0260441e2940340e40602658a50f007903440401044410b45020750169284160000569802c0c054a0105880343e040b200d410b060000c0215840228405400c4c00c2c002c008001c80d003950001c2e04540c4e072aa00c120603032000c80342e02280620f00c0e10a414018440c0d4103280e160724000240c071000c000d024800c001100aa20201002618441340c0d0040d1b80128020f55000080e110341c10718001200041d0510000140c00c007000100c41e810b9586000509240030701d0301c10701c030714107060505044070458903a4808001503900c0482442c028554028446201c0070584109400c50703c40f0000021290a002401c403016640001e0390110b0030304a180c00685000c0301000514202404004404400d900100308514000180c01c158028240d2410070b001d4030000480650b545c1c0580c41181401c1201c0c4d203070350860107202c0d80100303030000c0c400d60000610369000301d4581d040c90341c11202916540541c0d4010010305d07a0400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 588802814 1250 588801564 588801589
    0x1e020a031d1c05030f0a111315090f0506090409021311120a1407080703020c060c07030f050313060906060b0a030c08011e170c10090e071b0b190c050306 67
    0x20f00302e461454040145241c1c86009003009400aa40c3c00c9410707141400707070f000c80302006400c82c41b1299480d510496030150000c0003481c1000901003010000302140c0740f5003404c0a5440040c070382401e0600403010300c40281102c500582e03101550f0780360420310300c14910444084201d0608040d40d42d040c2c0c003184119601015200701c0034a441e26400014664400440d1500090f9500d0040300e1925042c0084010f07000e1403602c59290b020369402e0000c200e401340010140a0712070344030080b0440c003410301030380c40340021584662003084e42040303040001c225038010100681710b9000010015201c1ca048a1a90001100100865905c2d0103003018160010301c180d005241400c12074030709008585d003801c0314940724420034030300c4030150722002080030080c4104140d404c0058941c12515511079802400c01c413680c1325005200c5043c40105140500c602007420000d028001001641241540c42c0321085030002e00c0e010440c905010b410701c00850b0380c0111440301c030441e074617280c482c20048200840b030010300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 588804064 1250 588802814 588802817
    0x102041e080c06041d0a0f1a09160918021b060f150112020702042a031407080c160606121103030301060c0803070c05060106051c1e020a031d1c 63
    0x344810400d141d410071204500007480308420174182c030340b0048040a440e503850b0140391242800304051105034208010b07094048100c3d202c034100e807901c00401c11035910b001d51504c000750180d14103005280841c00701c154100f00a034030040c41c100c0020419020310182c00c02210281e040a03041c0001740b190914031f0307500080c0138580d8030403110000c00084c0c1200e18256021400540101c0d5820555490390f1000351041e00001d060328243c0800d1230540d44108114a0040220349445860380d01d00402903440e070b00c1b5005a4907840c0d95a1030743c4078200d84070f030441440c03110040016107000f4005440c0d8090b102c010312040c01d00c02c1e0419410b142079046000b9543d43e1a020f507000303000400c00280c3c0034103400141c5412191650b903a841c2d005007100d40c42030301c80c001384c403d03c41d01c000001c940b03510078001e02980b200a1400c110348501700b007840c011f9840100079031804550703980442400c014150300401e0000d03010700b80080c00c000d00c42001e41d60946020409083c540041d40b01e0782c02180580350003241041d05 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 588805314 1250 588804064 588804067
    0x3050603010c171311040c0305010501021005070e151e0901091e030201050705150f040b090105040c1e17010605090603150c130e10090e0a0f140102041e080c06 70
    0x903807100c07071071100003c095290740d0100c2d0100c54184520900e045c400741d240a8028003d908036005c1c050058682842244d0040c40703024071802d502276440c49200d026102a554006d030480d0000104140041d048240280e01c00040100718440c54280000e09030100c20240581d483d0b10700d00700098002c0c4081d9006d4400d0b81c08002c41c0002005152540340c046d240e09091580e25074440c1d0800c0351610b00009c4850031004140380501400d05441410303284503e10518001800750354507000182a00c00941d03001b07003506100502440342c8107034604102407040845100c2c00d04c40f5a10307042700074004a10400c8401c265598082844a030419103e6558003000980042801c2c0301001314800000c180108200e40031103000c201101075441c500c1c020401050307084441002401e010081c150088480d2184038174041c6082c0700c00c0201540882c44100180e04000011803c03052529141208004804100b41d80d5608000100e00390011051b8018002101f09502c8805810b042440d031419000c400300754071440c070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 588806564 1250 588805314 588805337
    0xb190806011a0c060c0304061b0e010c080c070315050a020301050a0b0f0405060a1707020601051804051c17070801050604090b011205090a150e071205150703050603010c 74
    0x1000200281102d00384a800c41980000d0240d404241c05510101d421078000c41040c80b0a29101d000030314000c5000314010441e549840080c0f400302d1580c04506000708003100308020840d801030505ca8030150141111602d8010030003556400c040458000712000001100f41d1a07903840a8410a0341c081c0300c00b50b0444c6154104800508003003140d02c140c0d07480da240000e04403800500001681e00900d40604003c0d21030001460140c41031004880b5059400c0d03108000131401c030320014129049036406000d01580f900c083e81c500d0640200240103856902c10100061050561800416401a081d0351208414a071190043c02e038060f02501e001f0800860b480107102c583d45032400c0701d0490b030116800080c120311140069901882ca15080c1d4200e80c0b61a0801104200101e0007024040c81a030300700c0c0300a030312220101d0032160841c01c911503e511801c07042c044081403012980f039040c02131044a812039020304001254080c2107071100f0019444409000981c24240070f503018111090910509801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 588807814 1250 588806564 588806579
    0x151413020d02120114010b0c190309050f03030c0709270201090501030203040510110d1112160c0605041109090336030102120f060603100311060910030b19 68
    0x140725500283c81011141420b0580b10000d51080400744020440641a5a90751800024980201c1249242c60180305003c40603010103d0406804a516440d0f003e0100d0030321007480301d0910141c001940511041189040720070303003003000c4401440300450104080700c1c40101074481640051030b642c0000200881c40700140e030400001d0058800030700c0c00581f01c0e80c030350500c1d41c908050030041c1806c051402e010000b800001800500c040c00c4103010510a00d46111400001c1e8032400448890005900c070204603110710503030320030f00002c1e0b9a103090f40010b0100d07103841c4219034007601e08592580f4408640c01150401d090041c1d40200c03241c0c06541400c1d0880e400d0040c82c0b07140f0700317003903c81000449400031115068022030358020000d00215243c040e5a82800114081550740c07842c9079404100160309480c1c06012240304001a00340ea1501e00d2440d52180c440410308009164001414400c10841ea180c40100c0c210074085503038041400f01e00c40046c0725506281c42a00c48050680d07040510105 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 588809064 1250 588807814 588807829
    0x60b0307120609020f120a021014270612010f0b030606071218090f14060a06080402030309040203130303200405092205100e0d0903120c15141302 64
    0x2d402403000f10b8043c003e0300c001081400200601030740480c050000c898032440002d28070140303070f100b0b40e01c2c000c2e501d18070303001078420b90703249805003900d104104005450540c400c01c0450020110010700c1c0090200480000c90582025000da03413501603503c0100020440c4028140c01800c0e03080d40c2d246507080c150b0114800b4803d108001e4100c200c08880800d06910401958081c450411b01ca584210b46424442019005a0349422840c0b401d054850b01e41c8a10540c3d00c50203000300a0030b1103010380c0340c40d006540b00d2400800c10703a4140401d009442c0c00d81c071140006d601c501000c03114103074848200d144c090115110240440030115800e40010709034441e900417181603070421540396810b6500c184d2241c0c20700d41314a0041c0c51403221801e440040042c0000c1c40c0d0484090b07184248a84404000f070305646040206010000640442040011a030b0b20341408890498a180000c1a81050346406c90400d0786100079403442c60b80c40007482038100420401c0d98112140d51283c000c100100d40020b50031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 588810314 1250 588809064 588809099
    0x1205040609050d0f020301050a090303150b19030f0c0c031b111e12010b011403070f0f050c0d02070f06030b0d0320061e010501050c0d0e0f120a060b0307 67
    0x555210300301c00c410704c908040036450203075006009011600c1e01c1508000945520701003203000c6070812034401d1402c2e0038802080d060305c4c00700c801e2504055000d102c803018018480540014103648a410f00b4584507903000d4010070180c02d0704c2d0b880c1101c032a450014940d42200300351940400a40c500c900003d401c14820302c07440c0703800720754080342c0d6140b107442c0c0744000c0307015140191300c40080c140e911038050040d000305010031000d0b290078005008041c9000014841220100c0020b07c45425411006001d8015010490f10902e4050300340008601f100703261801c14515500036a0042c2404c110000e480d034107000250507140740500c480c25040012400290a50b6030040a011441c0c840001039040c00064035056482da1040300c8280c10704261903409012032050950000f00f00d500041042d50040045400a07412a401003414101c0b08800701c0c0c403102c1540042c0e50042c0f030a152200d69070b0740c80c001e06240e00105c10203801c10000b9860010121402c40442c140607400100d02000140a241240c10307a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 588811564 1250 588810314 588810319
    0xc0c0c0609031906061e0305060619030f210c0302030d0216080f0a090e0f060d050309030f01020306101b0605280507030c022a030a0b090a120504060905 67
    0x11110311080000e42010703d80140b54509500500d1100c0602a40750000b20856948140c4603070b15408450142d003091149005c041c0c001d41c05100803c0550401d00625001d20400848501c1071903140d0751421100003502c8030507500110000b800c2405500c00020349100c040385410007121402e401c1c0e82c0a9201c1c002c1080340c5007050b5000c110b00d0a0801d018604d940c100d03a20055559440f49524071101c05038220442d180c00080c283e03400840e0318405292258003c8180300e00095036940c868041101740410007004554900003808000711644003001120300b41e00f0201c0015850b45000400e0000c8000c1501d508001c204060840c1484a913544078921100703500014081090f60722000144901d07842c0804843d04c40f58030000e01d0403d00c5040d4001405180195000e01c0314403a00003007242d85100d108132a9071100c140e04500007204000b61007100051074003809079040f181c05e0303848040c030251007110002c06540151503904104410401903001c1ea01e05d60500c28103003414141b00410410841c0170742d50 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 588812814 1250 588811564 588811567
    0x5041b080408090409140c04020a0504030b0601140309010b040e030909010e070207031b0602210a0c02130e060402030d0801080c01030504060e010903021006050402030105090c092d090c0c0c06 84
    0xe0038030401d44200c0e0503a203c00751052000110794a440782c00000f840c413100d650360046250103a40361038140226100e1150b140d403407070f00b010304584625200c00c0c2c015103000d05006941401003803010b81140a035105030601d01c00080c8540f80d80d001d1106441ca0040075611542080000d408180e842d0b803020f034155400c0f0401ca2119540e000c005a1812110b0b820142a010303200c41007281261a003843e42003601c400d40e003500c401c1c03070701440c5241440c01e0b440c0410a0070b00081c051842c81034400c401150b40c0b40d000030b2080080c507800741c1305038084541100c4641d22603002a803c000030360030f04011103100300c00a8a0150b106600d0400c040c0d49078488041080d04140c0c903080494240300c3c0c150002070900d052403000304010009458060b580c0c5108083d1410050f0800000103281d14061007034a0480f0070141c81c520035941e5000b89110a50311480e405540103081d008403040894804665402e10022000c002030b00060036401c2050344c280041c405020001304001c4603100002c0403407002c00303000d4159800b6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 588814064 1250 588812814 588812821
    0x22104080f160c080109110f180c09040603081e13150e0618010f030902030c04020d140108030406080a063501110d15060215100e090a02030705041b08 66
    0x8501075005035002810604480101060548041d0f00c502c1d140d40c1324001f0000c80d64000310a2181000d142100380d076001500c1180e07500400c5203c2e07107103940000b03100750a41ca00f41c00741c00007804442c0310740c2040d9564030000c0303200800d48002192031040700c9004001c5030309004081c1d9600c2c1c08401d00e4005e48a03c00d8040203c000c0180c01008400040d0100030304064503042c028480c070045040c44015917001908600c20850b110b4040c1c401d0032000c54014001d010b44101c04c00078131000c3c6d800f54100c800709641e102204050407482d000707103078007900801d000385036910b1500303100a18041001d024107445510b014410005204100000400100360740190091603400d9056407242c030036000304400031542008504c60540100300000e110009152500708141400004d4200c5030700110300910015a120506100a140c000c031a03044d4441200e24940e801a502d401e0000342410b0103031509021640180812402c44c501440220003400068800f00241b88220300504440c0310310f254584103006803c03010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 588815314 1250 588814064 588814087
    0x6030106180c020a1208070f26060d0501060e240a05010c11040614030609030a050a1b0c1203170408090607030908070f050a09020f040501050d0902040f022104080f 72
    0x40428154008090913841000070102030300d240030480c0e07c400012502036031b00322854001d802d5150900b0388030b950006400000d90001c4284070014015640c095800440b401c0060024020600904110324040380070f81005010798031100440200c004080701100c0214400d9210703032491608840003403800140074000c2e41000d00003c0e201c040e416421905140d070218140810540c0002c900070240c08441d039994550194680341d0050881c0070300042c0d0104028030b4014403d000341c0c03c40d464642d24500100101c0d0350b03500d420180302d601c16041185010206070030f064000c481145021400602c04800e07180c540e807012658803070701144a22800c400300d452020300d4803403214031014050010850b01c10a84130b1442c00c06010191103400c0c4625220000895070784640c0c000d03909150418039920f400c0c0b50800d001540d80d500040c503103940e801e139200702c10005a501c90041c0e024000401c8001a903c65a8540390154500782c1d203901d048100104003070200003804202242c0d4600c1d0042002074690703000000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 588816564 1250 588815314 588815323
    0x8040515060414280902090f180102030907090501050f01020d1206030506010f170f06160c0501051003030f1814040e0f0c040c090302010c0b180106170606030106180c02 74
    0x800c2000302c031240003000b04500c084c1540120511040c11a80440c0c6030901c13105040e5800f40c003000390400c8440010844c0b0154040019801c0761014400c40c0e040d55264528500726001140c015041d540412010003c0d18954441c05000d88415901c0300304802580c00080d59a01d42e0400340810401c9155180c0314095403580018091607009055a2881d6905c00d0140248149401020700c28500c4a40c1c203c51581c0004a03904080c211601400d040d0b941d02c10307840d05242000b5101400d22041503600c0300050820310a881c416000900c00b00740c054190705000705045034010110381840654140d29810141e266480c40c1110103042c595800f051a080c042405001c124a08505070f20404079204460078020801c64194ac1d01602e007040b000d10b400c2e40490702c01710640701c040d002c2070651407000c0214510502066000721848070509006c04c0b00c1c02c07442d007152065804416491200015002c3e00b00b410f000c10703a00000300301c0013804090704002c1218040d0b440360070030003034151751000340300c3c070b43c174020321 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 588817814 1250 588816564 588816581
    0xe010e0103051b1f0e1c20030109020405010e0403090602121611150315030c0603061003060e010815091c050c07030818040c0305152103030703060f06080405150604 72
    0xc00c60005450b100250030810018403251088103001400110010729040391014187c110403a40f01c0c5050a941c0710021100070840030340c05540702c0c810100540c0341d41c01000e0091100e01c005815526003400c00034281d41454000748110b4000d4005451f0703480358030b801d0b11f0350102400c010741802c0d40240790001c60309010f001041c1d044021820300c2080c101280c0d024500c11810804000941e500c1e000416854508403030809620800500c00303d440c40c103044da80300850006500340020080c1d120b94090700180741c241d128441d90342c01011000002020b402c1c400341c2049681c0020f024426082c80c0f0700c4081251540c0703100820202154035540b040003080380d00015600705407402d07512000002c3d00d03081301c24421007090141e81081000c0e0030151181c8260740c482d5020f541c00d000d05009070820041282074002419003a000c0e54000d5000300c0c1c0e4180000c2d0301806154400041803450701682c841c00030401e600420501c40c0f6001000040f41c0e01085082546c482d0b03407110304140c2d4511001500800406 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 588819064 1250 588817814 588817849
    0xb0d06050109020901080c04050d112806030f02190503040f12030903030c020d020c04110409020309010b04060602460303141b0909070e060706060e010e0103051b 71
    0x800002400302c41039000784a410420780c0ea42410740e9420b6920401446540310740c1c4c1c0c100c0d81900480d8007088001e445071024400007080740107040501051306048422250301c0c07184403030960508000b141d805100d03441109040c0e0300f0650070019500550495042800300781c5040c4a00040050104003c043c40403500b260700c42052000082c2c040c400070300511022a01f240030038a0914000c580c580001110204152290f004000b1444440d0502001c0c0801c035800d5550413100f8040465100194005140b140d2641c60001610310044820030003940c489900050544d088003001c800500c003064600a281e00261003c085000d206ea0b000f8201a942ea90008034040c440c25082c401300f581c140c0006012001100300e000082d00c6420646031503408642248404030340402005880b07041010120b1b50050040c144000e03111115004070380d10381c1c843e0808031401540d840381071000400310400c60740501b03211602e0841960440c2e40d0740c1d94a2800c880300010100c0c54003c800703100d6075074910074246181d10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 588820314 1250 588819064 588819071
    0x60b1504061106071409040c09120308060a050f0306010b1614150f01080a0303150b12040507060c080f0903010902030706090e090d020a02090403050909181b130b0d06 73
    0x841000034070301420305145040341e005010220710302c40e209a05005c200d1a584290614014202040000400d1140c003902c05003d036821000a00b460103400d107940040c02074803071142e00c0c940141040414941500300d20300c5002000b00540b41c5440000f8020b040d18051484641c0d140780304580c01c0d03560464288014001c05030440c804000c20b070049144407810b028421240301c0c0351a01c05851840701d40134001e808480e803088420300e0119109801101ca02a49890b50440194590f6011110b591009810701c0f00310014006100411004010f030b00002d00051a0100d5000042c1c0e84120341c600c2428841c0c0c10203100480c04001c01c0c0c0d029802202d03601c1c0d00500322403541e551032034058055042440780c04260000d80000581e00701c0c0114403114100720b1039002e0000446243e0800848440140c800d0317042100501c0389132500d4456583d11400303540802d02454803110701071202031400307407064a101562500500f120856442d100c80c1e14881c001c201d100840c0304010f03a004224002114480948502d06 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 588821564 1250 588820314 588820319
    0x9020405010b070b06010816050f040e0108010c1403010305032b0c020d0e01020f101e050903090a0b2d0702041107021206040302120a03020913050604180f060b1504 72
    0x541c030007440d05a2007400301c101c1e545d40340c10041d42e2200c0100c480040d821003603001895124801c5000b410000d00c1c0310b08183c200f40d01d030007401c4282d01098128409681d503909070701100e6500150304a000d0281440a545158110380c0e490b0703104d0003811742400802402c0445180b4842c2d0407407800592102c440802c0000074500f24001303686074082d00c00c0101159178901c1e1b8601c594404102280b039040048008c002e1074002c860080000c10b0100e01204a45202e02d41d03108100c80305000d0035000e0f0100c00300654640ca2560100159140b190b4003002c001c40c3d08000101c1d4104c11111045001400d0046e070f46003102240c0080e41c00380c880e288000303501c141340511005403140460050000760f40255680a616205000b601d030b6590415240500540c1c400351608410610b00001004080460701e0054109000c00010031580440c8100281000c1d032034908120f4107003403d2280d0340c0c02803111118241c0c841c03000c3c0c480d43e04a180d9441d014240603100c4000040f141c8079100c003400d240c04a144102d0780c0d2607 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 588822814 1250 588821564 588821579
    0x90304090b0604181a030a030c0816050f0c180105100309080f07080415020a0317070e12010e060601140a030b03010b06040305060f01060e010801260106062a08040e04060902040501 79
    0x21340c0e01900005d041110050341e500c0c1000205c0390009a415244e070f40307072101503032901c7c6070a800c00600800c810710300c101c1c07040c001780301400b42a5805020400602e62000d0040810605940d9201140d00c0b0401031801081039a0300c41c5d50100ca404903904000480c0d110701d003442000c1d4130903000c00e10890701001410302c0411204100900c2211100309161200c0c62503050200d8a13a18856800740c0042c5500380c0307250510303285980c0c854115240782002c0380084d200c000400d40c2030415414541c140d9665402f45031640c0c0d001c0c0f24096004009290054502d202903000c43c05900035044c0f004101540d0301c452519a4401350701c40c1c82c101380c2c014420354031240d6078540160307101812a503540084810f40000120745000c0e0400c80102c007416185c035a1140e0a291121809190222807200742421708192050700e10400c1c8207100150105550756505546071010103900e082c41c848a50746801380c01d0f170b00f440101d42d0f85820380301603070044d0054426646480c1800d0010303119442d0060750161600c0700005401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 588824064 1250 588822814 588822821
    0x16110303010b1e1801122a02010513030801060f03061a04030c08011e1a10051321080c03070515010302090f09151f0f06080c03090304090b060418 64
    0x36070006560610f08030101250080600401080005004030404910716641c01055040b400308404000051201b64145120169200081c41300c0c070100128403840c0341d100e03428019a644042642800020304115640040c01610140b00f1074040100e0f008540715814402d4002800400c0d0b075101c40d19509003100f94480303445e80540300c2150000d015040c00103002c10103018a0130182c00100704104c840e1100c3c082400540003600041d0b0381041c1b250741c0a14195a05005194480b51a0307076103546a101c140450b00c000c4038250044000a02c0c88851200760080c058400a2140c2e80b1001c51034607502c807074501c075145014000380103006001d42115400703030040c0e4117007040c1240d00032103440e180d2b511031401920f00700c84180d40884041d0000407907440381d001d9088440360803c10200c803c0550b1106001c400c1e010361110382010b00c0d1076010140070003c3e10b40c010f82441e00076107218181440e6042071030f1160340e603226502c41c1112498444516107603558030902503a00800c2000f031141e42d180340e0385031204000c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 588825314 1250 588824064 588824077
    0x3070201140f0115090e04020402130503010507080619030b0c130b070303020309010f1a0d03090b160c151d060f04090c021006151407060e03121e16110303010b 70
    0x2088841030140060610600c10170040b11184160b001c540d490725024000a50b010103103000242c440d540f03001507a0f4400340701d44d511411840d0384201081c05c041081100d0100d00082d003034203512142c3c074103002044421038804d800890b4208602d9594440c00b00d4003110312210742c0901201d08010076030380f00b40b60309500210320420344400200070004c208080c081c1129000034540c04040c0c02659060711904048d001c02d04203901905244d400b0607038034820700a082c1c1c002c01c03030310b1019001d005501080105062641c0080d0103c0400e408044648250003481e0b002c4802d41141440103a00030152241c80701401c4600c0051140c0780c05603550b4030f46004c2005001d03042c60440041c491007004001d40d9041348282000d6600c1c0143c45403241207842c0c400c542c500304e4080c1c00d00700e8850400c2074000040e0b030751088200440300c60f00615141d131440c0c4038031007100c9402403410b85d01400340c0f08280e04001c01e0405056103e0441888840119034002003142c55002d05040959280300000000c550003a001001c1c001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 588826564 1250 588825314 588825329
    0xd0b0405061b1209070f170c030c180a09060504031d0906090106050a03060503071217040305100908070b071d04090b072102030114010908010b090c03070201140f01 72
    0x9511441840c0c00d54462074007240900300c0c4280550700034083e151000700c0e000603100049500c00c5443d400d040c094028990304c1141250411a044281c00740c00b40400e5203030101c01c40c003500b02c50142c040440c01070042413000d5001511030301c0c0000c4951650b40d118485e00b9420540410103481e0515000c2d002c1500c400349040980c5412541c012940b030b0855015101c0c89010307102d694a6480c1010564081d00411450b0381031503103131348003c02c00391420030080c40101448a03241b501c00d041400d20004440e40b540301d07030100050800060010507400107002d0b00744204c421002580c4401c5013003032041801403010003081800c2c500141301c2c503c1c1d400b54886000521840303030b4040a10a40040004a0300c0b801d50040c184110303e00010540d0380100c83c104407075040d441e14003c42c1350340c501c08001203a10903005140b408822005900344e41d640241e03640040c202d0b01008000001d510342c0022500000100f641d02c0d0385900200081c0040c1c401e411a2a445e049040e021440d030a2070900e1403c103600034050f00b071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 588827814 1250 588826564 588826573
    0x40c0905060405070f0e01030608160311030706090315020f121005010203090108060409260d060504021c240b090f0a12110a0b031810020a0905011d0d0b0405 69
    0x4859142901c10750340600315917203410142482c101400c0d54401340341151241455501c0348005441882409a02c1486400c5502c0f80c06203400c600d032108802d6250318105000354420403060140941003950441601d800ca00c1d20582c000841034541e000c0c0c42103013680e4ad0000c00202e03401c40030850700003085000310001044103c1071500c0b42c00481e62405110300d00360000b0240c0001c1611327410b050303004002c2140a48a5a42c441c0c1c17518059180d400025500031480d0400042d5260308004144280009000125029032420480d01000002921aa0b40c003441c220b40d034210420341c060701c4c08403942c026a111060255101d980d007020040303a0300a800d0060203060380b40b1a02d403491500c145200f06541961210100340104e589622800c40c100701e800c01c0e0003500c0c050011444080c44000303980300b6080344a58401c0802c504440e141482000d0310780c8401d5030b0040c0b0661a03216001461003050320020718004500142143c4800400c02190b030040790015205a403440a0041e000c031824402c074011720031034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 588829064 1250 588827814 588827821
    0x130603020c0c0f24040905070503040b0106020d052a1f06090207080a08090109050109060c120c090b091503010603021e030603101109101e02010b0a060315030b040c0905 74
    0x1428590b084186a44030b803510024a0180c141c25494100c0302e01c084d905241050b499018880458109550030004a000402040100040c05008501609251010700304416070554098881d0151491541c2140181e0740306028031841d501500d02c3c4010400201e0b01c03803884200503a48600c3c0006007241c0098101a030104001e04a4000c81c2c24940d48070340f9403171910143d842c044441607009031901056548880250012410900406108502540700010b40f00c031800b50140c204030302034445800c0705050080701202e4942100445080300c080c0c65a0035942c8107000001452110040c0003000031040c04000800c0540d456409000110000038048a54400d01d0300072003000e0100720b0b03403e0342c15807011a406483c1301e00c41d000700d0030420352010414105021280094102c541c50304203100010711101c0900516002600100c10341a0759000170800d81400b200451f16000c0d140c0240014151142e000d0229002c503410751600035030b00f007144401d0740d080524200114449600c5114400c90400c40130 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 588830314 1250 588829064 588829069
    0xd06061403120406210908090a050319021512011d071106010506091201020706090302060a022133150a05030a090519051e0f0303040314130603020c0c 66
    0x4002d4405148041c1d1810589052000c4900448900850710102405140c0e451040d03401d02034003d905202d0300001e41ca6103001c00a010101009500545c030a5028001e54241844814610400300703405070307850a0070b90300c900b01d0044d96100780d000749010a4420400081c9003c5000c0c2e0b88000000b00e0700e00c0006544030a101107030029540075030704150340c12a81c01040740345006e070f0041a652001418184461800488490072600a4141a1007968507208074100309581805001d03803189414000710706042030714011068a40313014192031000a5044003141080d481c0c6008140344443d84031980407062207611110030345008040c0102c1c010080d0100034400450300000384c4020005030341d1907500350760310143c070403001c0c0032000003d40d640e00400c80350803c101054002c026034203004000a00300d507082201e0103e1504410314a91000c0d4205101d146000f80b00401100c0d006905840e0600504401e80d81d100d04500c5942403403642c100c0d001000207901e68154014210b4165088151a80d900a1405 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 588831564 1250 588830314 588830323
    0x22090608070515030901150e160302160303020d0f0912090b0f0d0207030e0a060201060f050307060f0f032304150e060a0903110601030609051c1e0309020d06061403 72
    0x9200da01c5110100c0801c900f1124001a41e844001d01d40007103414007183e9002c5540c400d5135000f1500c03400d8502c013002030859204032000b443d40320600e0f08602c1d10000e9007000d00700c016018801820140c0004499030f9503c81034021005111036440104034180f03003440d0405882c0e0004803020701190b060200000c030381c02e51000740d40d024101c02280510340030901c1c03070a50003580003601c214240324581503e00d449440f0600034201500c040d03000001c00f60b06007000e140100510740d00c45407103580004800d001465116408170f0b41d000b203500382298407106c11030b420341c05400d010344400da551807040c5690301c03031595020200307000700d000c2c00d111022801d0482225064801000c1015107035404035000c5500401d840c1d0080b205140640350080d0408030344080706003400002e80c81a602540c0340d5418a00b4084180310f805142c44203002000301090b94000050400c88680030344001d18240d5000b0541102c1c060707000300b0102c0307a004015103030707901c140c2ca082c400911140c015010501010801070895017000074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 588832814 1250 588831564 588831569
    0xc06080f250c08390a0507050111030d0f24080d0e0111010c0207031101030b010903020f030a060203130c0f0819080c01020336070e07020c060a020c010305100303050d050403052209060807 82
    0x6e010308086030601c0c0066900d21010302404905100c108182c001c0310a9903c60300c040c4040c061300c041601d28405c50024041c0c4401d4100d102112800f00e02004840b9001400d403400d0803d6080c200b6204074054010380781c500800c030151125500740000180c0f00380c1e0100e00d400940b8812a0012882e01103000118110f80312508940d02180b2110030510241c50a102c0b1030100c810001e040300c2c01c9644507135030301c820382e0419903020680c84140012241000145111640030303081c22408009100e01d00f03a1346130b50717440445070781d4500c1d884400754103014412080d0403124200303903400003999070f0b06050450740e452502c40303480b05004585a8003590800e04806024402815400000306241420301030162102c1720040e20784002e601c07d0203405001a03c6900c0075065204458018110000c1c40500140aa80c002000c2e420305104c014010b1000a030003d0640316070002000700012256500d24060741c0a114003107074581d0724031031600c02d03919600101048000f0380c2c0c0610800c1c00150340c2c40a10650f078140c03d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 588834064 1250 588832814 588832823
    0x32304150e060f04031a010603020c03030a02030a020702040504230c18180d12050f06130e0124031e0b0f0a06030c06080f250c08390a 59
    0x4080c94410041012034000082c111880c002c54144400e00c0f65200c0e5004840c1d40d024807201e4112484010301660040807070341410362600444a42070707900e0b88801400302c0045540480400c1220441c1d9059903407680c1d01600070016400e02d41040d07800e000d80248440403022242c000c0e0080d00d00c0200e02d0140c80c00c00a002d03608a500040040b8625441c000c01c0181c60100d410004452400b08200051b01ca20700e90300c81074103101088506c4016184002e0807000210030762001c1c050682ca501000000d8000c004800041c81960002c03400c1c050b0428020514085050a420b28802c40d056a5100c04a0344109003142c0c004040d21310301041143d6510f0003411224205000507501141c00325419800b0b0350750701700096041d8803695030200c2c800722500070400140700442000741009400c000c4540161a82907510700354400c1c0190700c06951041a1410204080c0000010800459100b5603114840c0410000414040c61540070381d504000500103506005036074401a500f9030106a84c2c4c03560341c12 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 588835314 1250 588834064 588834089
    0x2b21020705011e052101081204060f0c03021606020c04140f0601030b032410122a0e1911070b1302060405040905060103030e1504150207050a03032304 66
    0x5140030882d240d02440d000418407200700f1202515060b000b6a107400d0b0540b04405c60b280b94104860380c2c0c5000010308088070010402c01c814031a4a070015082c40b030b00c10461070516003105d801e11b0101d040c5048100c400418108041020441e01c1d000b0401500d45042642d04100c2c41c0c2902600301c0110301e0641e0400d0007820048003280444d440ba400c000754260001d401c549519803040c0810748403190b550724140d0210040820700c20210440c4100702c000305000072801441440d551980e00a00303a0941e0941b54640c410070301280ca00914070090b030000e0070b07481e100c4801841c01d40508004c3c80035507074400c0207261a0049100c05c0d601000141c030f032102e030050182c200a954521000304549503010342664000700503c00040c180e44d42c0d002e10380d0002c0c030500240c4000d514518020302264030000c0c00d18840d041012070001000030f044142c0e42100c00e150944034038244641c00c00c5e070401401d5042203802003040030020044c9900306a40c441013070294110088400004101e1003000d000d030f800356900d107000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 588836564 1250 588835314 588835337
    0x504120207061713021201061e1518120506040611041526070302090a060201231e07020f070e0112060504170318011d0c2b2102070501 59
    0x50350200640c4500c40c0c000c6240c005805030001042401b0030480303550169183d84040c0460103198108a1640201d40c842c9101c050900c5111442050242c450800700507200c004042443c0700402e05030010024031042c3c003807003071550610b107131642002c40301521100d0a1054400e02c608404040b1021aa46500c0c00203010200c0381d411a1b2600e00203921000c0f40c0c01c1c0056001d5000610300d071550007101c0984005944240c001c0c18003150507510f0b0700c19401e592404803440f0304007481c071404400c9481c036080118415510000e49030b00c41c44070b08000a41130300846042101c1c154002603150071814068048a00c0260360706c46040c0007000901403441d95081d4100304000003242a0415504036121341c80c0d40004009170201c490144d00200c41c8041e10680c809529190340c42c081c4142c3c9000704154039140117103500005142c0d681d201c0b0025460084412050200e140c0710146c0300000507103e00302d0b4419060701c40e81080c03055252401c81160b40001c0701c03074200c0d610300e000003100e0044803010386420f4074415 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 588837814 1250 588836564 588836597
    0xc210e03150f1b030a0e0d0201050621010e0601060f1205070e01050304030e100302090f060702061207140d050708090a0203060414030d0905060108012913021c050412020706 76
    0x420260210041c500d542042e114422a0070002d1403140d1034040300080c40c100044050f030700d04003004091f641036915000034002da1b03884044028405554034140b02108045440c940d80c0100302c5007204402d607000344000468080d40c0000205d032410034668600c0c000f2111031407001e088600540d5410040b40610103410115402500a10f40c0503009003007400c0e040000038081040b80019801541c0043c0d03000454160303503d401c2c10860088001565000c2c1081055070110f0183d124501030450940202800980182c1c49a141100382d00b191451190301d0b06801559240540810303502c2101144008002594003c0d0000e103c182d41074008000781440e80fa69194502d4110014180c8116408100401e64402c9461b001c0e07824618401c0c4010002c0750314101c411401c45405580400c0b803100b15025007000d01005405558044008440c80031031105001a150300030700c22148198107525001c200403504c290b4541c0030303a1040b4002c02c5551040480c00d01c00301d8840303a0038024080499680c45c400030071072 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 588839064 1250 588837814 588837841
    0xd082110062f06040501110a08041104061a03060f010e011b0303060f06020a150b03120c0c0a030501020703110309210304050a0b0d1b0801050108070c210e0315 70
    0x846031042c890342202e458814403412035010540140198401c00030311042020900c03036601c1060800700d105042c041850001800200083c0024200c40b90a4003025015525a0701c404000d10241d4081e403240302c60101c13600d600390802c40700c4600c120703007021341c82d0055400740741c00030310301c290582d604402803802c178030205083c4a01c60b0b400da081659803040400c8904c1c5000d9100701410340d0342c004040002c1c26142410101e0b02c00903240201a05000b0414100d03100003071070318014441d40d10400d842e03000c001c00032031401d08002e02080d807000b4402d1002080c80019402484038038044d5aa411107091100c580644e40c0c425040c1e41a044003a10050748000d0f0396000001003c0d060020a07079103026580c400081142c2401e82040d01807041c0054881d90650544c0304200b12005202c4410445050480020340038000510586041c01441e4002a4801d845a441403900e1a40080c0c0030400c40d5509100760000348041111130086030418000307000c60701e0006076848841c02071410030380041d503c030354011005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 588840314 1250 588839064 588839087
    0x20c06010f230f01200106080114130f0b041a0c071208060f041806091b0609050a06030e1006060206100504050402031c11071d1e01230d08211006 64
    0x40f219803403c500400020f0044000601082c00040360a0240c00ac0d81000c1d072502802d520103c00c20090440c000a00100615010701e4014019441903038803410b096000c075111f02c00c0300c007902440200304001090f4182c09840c9903402841245002c400000c02a01e00d51000e44085a00804841c40900f4600d41504010700806074441200311220f80b50307032160305803000b00404030b81c200030300d25142462186207802d400003003410b460b1280ca0340e450b000204849050031f005040400da100c00c42e51050490810a02e1042e1a5046c1c00304170301503807480000d40302c8105803100141807d11410000303076032411b030045900075074000b070180907081b10f01d0580c540500064283d110038814000c4012003403c0052020500418030301603000c000300300e044010560362400520140300c294a910043c1e504c04013035140f003030544000c440140101105400c00a5200f42000803e5a00c00c005882e18010804903002800c070a284ca640c1da01420244014181d01030780f0f04445400d840f01100700104002403040e000c0c03229 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 588841564 1250 588840314 588840347
    0xb010905130e0129030304141e09070c060c0504051c050c0a180b01080403021c020705060414090c040803070809153702150a020c06010f230f01 63
    0x81101e0240c02990030340d0400310b42d0041492041000314404510301d06000744c1c19900300c3c0514505420700030400660300c062000c2c18025040e102d01b4180031403081c50020304080c401442e524040c9800c520040100002d213208540b01c41c20114994481806041075500380c2e03400070020302d401c02c542201c4400040340c151085e5064031030030606c603055490303045a038400350405000e070340e4804070301900b03a40a40f00d04028080c10010301c04100008282e021500d804120305585844080000e030040807450300c071f925040b5951102c0d0014000901e0400d080742300c81e112a043e84c0104095803102003a0320b16004903c1008001d8204002e01e100081c0100000d000c8118010040866048002c04001c0b003a004110884a00114003000c545441440703c4000840b0f0315850707035000b0310702040307000135103524007140342e05d201c40302180114086440c2c3d6010b5840d620290030840e10990fa5038000d04071001041e11607000034098400000e0808004406031043c2900080d090000d40e4100800444000202541502c07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 588842814 1250 588841564 588841571
    0x2a0105130b040f150c0309050904030903020405130b011a071203020d02070c0801150b1b0a0f11090901020f180d02040501030b06010e0603040c03060e0703050712060c02010b01090513 80
    0x9201c0409502802c05010030a60201c0914105440c501c4124010703450003042c016402851000643d010340942c0650704241d0720341500c0e80311454140c4e080810354000950090600d0100000c01c80c495184030001402010380300b1069903502c6120304c103580c88071802d600020080210304041a0302d283d0010601c0c01600c1c00500d0100075034490b00480e086204102c03074110001c10104100300c0240982509417025003400540e1611f403145e01c00d400d110345014910100e01c0d68021020380780050201100c240d8101c15801440c0c10b443c60181d180d8102c038900b080c03180169001107410507030140b086d140402cbc0004000c0e4501441900505007801f05003d00582c00070300d607104900181c40d84d014440c020b503c1132000401906100b0b0015101c0305803090310902480c014410880441c1d03074030301e145045039007110000400c820004815070074002a908050120320a5541c00504502c401400031300043c094041000001a9040220709a40b62070000b0303800200380a1042c00345240500501540841390903002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 588844064 1250 588842814 588842819
    0xa0e040b0718060201020a17100e09010f1503020901150903022e02210705060c090a05060a080601030b043b101a090c0a030207080906030a020304052a010513 69
    0x742d51940542000380145d4000c640c0c0305580e90410000c6055080000c4200013a10345a0310f035a03003a01c1c2c5403103038100445000001c100089002c0d407003404110030a03a030600009010090f40c18052413144130882c00741100c0c00000403e00107005440e1881703d401d60740c01480900e503408000c02c05d0b0101c661038130700104071000140045950300040825680507006002c41c0f904040c0b285094400c80e618000c58101c04121000c00a4070100c0c0c85540140c40f01c4060346c4402030000807403401007080e0080d607044070b000141e0400742c41d04008110310031142640c0c14400790011800340320507200115444140c0a40c1d00044602030010b4a01001c0140d20416040140c2c0c0901c408962808800c40a4003409030303514004500c0718540c00c180251411405c0e540d116950500303801d12405442511100c00405902150000c02c01045008071903100a0041c0001d840b804c149800d40000e40c07060341c0c200c54a1140003045502440908640c070f402d00340e102171b17880d140009940150740903840035008180303055005801 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 588845314 1250 588844064 588844097
    0x10603050f1303030b100201240b072303130e0106032304060b04050106091706010b0a0c051204030309091b120e0a02031e121606020c0f06010b0310050a0e040b07 71
    0x1124400055001241200a00359582e0527040c0c580c9889049140100c41030140351401d4040302d01959108040414076114070301440402c03024805035400b01e0000043c08521001100c003003600b0f4440d11056001107076070701d82c1e0940071540000c0072000d803900c0e80c4410400e900440004aa4018096a0041040700110000030304842c004d80000c2c012030943c9009100c08032100540f00c100302c03ca4401006103504045ca01000c50154010050800401000300000c000e0300b4819603118004080b80e1940769512407401400002c414094059038510704401c3d260860003030100b079100004940c40d050a140c403c1e450200144c4450282d14501e031080300e40317510058904100300030203d108169003c3c492641081d000d420048905116141802e00307101c1e0f0741c0706001c4a02d000007550760100c40140c0d030b000c0003c91181043c508050140c00c500600000061100e8080b0017075218050404001000c2500c407401c0050b1a642070007480c981000080c00640021207511001d900082c407420305e4074010294052 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 588846564 1250 588845314 588845329
    0x34050703051e0333040c0207030f0602030f07020a120807031508060402010201050705070c0e07030f050a0e0c030708060c0d090503071101020c0f030303040321110909010603050f1303030b 82
    0x40240380c0410001c108800319540503151480f00060b143e41c84e22256020a41e0a450440c44240c1403141d95501100e41e041030003001124000c2d644a05d1243d09040d15042400003500b0407605054202040000038400341e1012410320344455101101f0a6202c903404422995500020241d0041c142e0301c44841c2d014054115160380148030401c0202100d20309480020f01350744000e4503c0003031107801d211110010b0f642168110a1b038400a007140c5941c0e60b09074084010f03000d00c2036248072880c43c03d824400440300d20741002d100c0d01854001c603240b805e0480103041c0d0303500c0c0510032808650050000706280e02c140000a105024000310080303807880d100c1d02d80710b0555002c1c0c101143c003c4030741c01e0280610b50b01031010090380c3d28115184886042c10f5800f01e510391000520040030041d07a110b01e0204c200c581c0d550462410480324042100303080b05190001c16a004c1036085200c0c0c0c0e002000000c5040c0709028241c070891a10040450a444010409100101014080341819201e09404040751900c24 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 588847814 1250 588846564 588846607
    0x1050d0b0f0402131e081209041107030f172415130608130f0f02032a040e0c0607140c100909050603070509072609063405070305 57
    0x2900800707581ca0b140700c1e080100a030000e0110310040700d401c00c029034080440d02c420380c21824007c1e6684c3d00c442c0c9000400030000c8200180403850085040c405041c1d011400080302101615401982002042c0340314404100301c405113080c41e205200303120021185d01481100d00c1c40900416514183c0d0807132414560001880d16800443e40c5600700801c5a00c0110030b40c009041f940c0d01c541102e030300c0d1510180441c0840d4003800f520040c010400854401700002e40d409180c05c2c50302c0d04001600c064240500d40080c810754403560801203a10074100c4041804109840002e04c12443c1020568079110255030012065903280100c203420030f1030b0346920b6080e00b11a01c80313980d4010300504014a4404903500030b01401d01aa01009050280f034442c5451590030000f80d0501c00020340030310203070780300740101149226114081c61080c004101f00000b1000d000d44409501503044070a000a03006c403445001c080c0180c1d81d1900301c48a8040c5019000a1020b03a02902d8841e103001c02c50440e1001e15400039 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 588848920 1106 588847814 588847837
    0x140405060d0b1c110d0f060f0e0f071d0402010c060f050103060e0a0c03061509060312080601081023060307021e0a0c1403030c0a06020301050103060e0601050d0b0f0402 74
    0x902109550b45c802402e01c444230040e031108004d45840c0710896081e00c1080c1010440103408940e500c02d036a4104451652868160468090204060002d07410710002100a4000c0f860345d00a00748004055480455654914540903080b141220310b000c9442d0054a12000000c3c1060b0b010380880c0c0c1c021001080c0d0072400c00f4101e0554001d507018000182ca002000001c2001c10b07051000c8210075519022020759910006403220300086070b00da82c0c5256405002c2c0900040d2000c8540380007101040c0c6140c12010f01c1c0460140c2e8400d550b8a00580c1c0010080c207001c1c600b0500f40c03102c6425801c094000716090359034941142c021030060040c1404482d500107155142081554100229131046413011141414888002d500a0045a002034104403020950440c2804054040c10060356518503100c1c000008230001c1c0107000040b075001c6100980c400300d964450001c9c2600980d01c = true := by decide +kernel

theorem cover : BRFrame.Cov 588669064 588848920 := by
  have h0 := BRFrame.cov_init 588669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 588669064 ≤ n) (h2 : n < 588848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
