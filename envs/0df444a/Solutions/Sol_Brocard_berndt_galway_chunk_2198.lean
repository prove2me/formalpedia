-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2198
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:57:55.063869+00:00
-- url     : https://prove2.me/submissions/2f2f27f3-3ae1-48ae-aef6-0e0c4e5756ba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 395143884 ≤ n < 395323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 395145134 1250 395143884 395143921
    0x40b040b2508040501050a0504030c110105040308070b09010f020306100804050304050301111206010f0c030c0f0b09012007050d0c0303060b0d091103060903090d1104050702010b01080708040b 84
    0x1400389051001c840e400100c25185440c0c0d200008410300304010500c03209000311500321030b20320010002d81c00d068500134101c1c9030141024095952102d4041c030143d20130812540250780080407681c41303401c03500d000c0741c1001065500b6069982001844a5400460700c21280142d10040000050001503a000d0701c8185000b40269010b00050000080b02d4400780a032a501242c81260741d581c2d0040e5030059a203035440904502c1c104007182e8038102d45282c004104100c070301e401d4101300c4100c10003454a0001046d40131300050100349001c2c00c0c4620f10405401c50300e4002c880710002c6401c41d90251001025001d103110240041d84101c54001c0101d0044108502c401d00900e40030641c40c0d00c86400b412140d2252400e809810303034444940c0d0a0100d80e1001c0044904210064145402c0c9051003aa80c1d02036183c0303c510030360707104040104104041e541c0840661002d4020710040c07810100181c02403012090050116004000050700b0502c41c030305161040d98001c40d04003940d11010f81004a900d01c60 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 395146384 1250 395145134 395145151
    0x50a0b01271a0306090c0703080c0306030a0f03030b03011a0f0603091603120f0518010f1206080102370c020a0503060f0901061d0613090830040b040b 66
    0x26500071405078001c0e107011401c40b0181da4215540d040000600040040c020101280100103003c000b000070352018086410119007003400c0c4e22600d03184000303800d18070203030401400c0e04070f000349160406030190020303000c504040b0002c100c0d0300350880203444280780d8125010381c400c4880401c07190518241c805541c012610304226902c0b0710b078503031030400c1034400754000f0390f04170140d4090b90340070380d40c03060304011011001c0c40d220f41010008140000003215049045041c0014034020320112131041c0401500900b19100c00e02945070358450040c000d5106414007010b6580c1415120440035120030b10070509842024100c4640c1e2141e00d0455603140e60f0031040368041044000091f1a41e000c11083c1d00030512200507007a5800c102101608503840c2d5485000004141d144d220b02c0d6808441c85030f940b00b07401f03175883d05096078801346580080070f1840008000400101d190720010040000f07940034038261001c3e0910030f00f495038000347e0410007181d00a00c9140d0070b0002500080d4114107444d00084070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 395147634 1250 395146384 395146457
    0x2030c0d0305072406060e100c050f03040f08060c0f0409020d090818030c01020c030a020d0503070c0e1e10060315050a08010b030c0a1a180303180103050a0b01 70
    0x2960715809481451300a0300c01d210304e400c1c41c0504c0c02c5000c0c032940000307140710308040030208582c3c808550150b0320041504140b0003050700c2c0340b061107014000d907a04613189606407641c40352240c1c480b40c0d042085000300d02c4075200302d40024842d00b45107400c0302c00040368000200d04052030a00c400e0301940c05014002009616440b078600000c140788003070311105070039405804ca207040d40c0c0185494100c201c0082c0b81150300000044510351130102d002001d050b0103a40d40d411508182c1081459031040e00c0340201800c4100318001004909aa1214090590815400c01103003040c203000450f500c054481c1c3d09052401401000041d00030f0b40306d001d11081041c030f9a00401c1e80c031800100e5494055100e606035035110102000d081c58240800c6140580803107154520600307108000c000824404907046a08030000380764407550301e030400c0c4040c079588000e04584d51403080c1d508031024403e4400300b0340c0c00700e402c1402080b071404d89409039051812041c3d644010a42d0344803900d0b00800801d40300010b03210007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 395148884 1250 395147634 395147647
    0xf010e09030708121603150b0702121c020d0305010303080f0414060f060406080601030b06060714010501030c090f0c0e010f090e01120b090307051015180c02010c03020702030c0d0305 80
    0x760360303001e0304c0440b4003004a440c8501e09140c0344109113881034078501c01c051808511038078400c40c4c2110a42a587c00c20301042d1100c0342440420b0550fa151725030040c00d803044803580d1194216666802582c134440d03600703a503800c1c11b076648240d0a6410038040280171842140019040d5000d021500c4d41c064002c042c81400309035a4540345082c0303841566100720303400340d0504112281c141802400c3c01010b40c0401800f01c0d614507200c1c012000c5000d00042d11822000803900b06000c09803101e0080a06800001c1250b541d6916001c1c600c01802d220301c0d0079540c04d00740303800b00600ea64414143d0b220103544170700c0403000e070040045440c1c5452009400c00d200c000c0c00c010a0416914051358080c0c0400b44001030380c0c00323240c18040e507100d000034130020340346d401003110600140c07012074080c4540411903c0030501640d02044259490701d01c1c0c101e040000210510501c03404200d410842400f680c0d6002082452611a4201c0a07407141040183d0164000b08240641d0304000b000001170740d01138135040c1d08000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 395150134 1250 395148884 395148893
    0xa020d081902130509150f04050c09120a020f0a060c0b0907091409120f0409020304050102070215070c080f0309061309090f0302150601090b07140111210f010e090307 73
    0xf00b00001c2d0b5280d140c0c03012810b104500740f0310a2660002554002c0900c62685e00c40010542c105510805d4000c0352948c0c04200244400340649441c8103008080200b85120041d0660381c80302e1130340b016403240b07030b18008468007802c1c44001c403820303100280e5505074062591313161400740d00c43c0907003440710620590f200000d814a0704d120b15020004814510b401c5401c11070005450001e41001200b510072042003109020700c400780440e0111030480d400541c8a40d503e0030b04500a018880020390080e091002080c1c0f0320004100511883d88510445003030a5212031307905a84036001c080c48280c0e644204005215480c1c400040c05c100c0080c40305506185480b0381040c0d05940c00c24600300c030000b100c83c080c9420141c0510056444d2481080c1141c1941f4001d0002440004c0d18418a850703030100044150911000c1d19840c05942c0308030000340302010a008040c040c0d03500c0002d205c410100403034400f013801090180303101d00921144e054050580d0070700071240210136001e04003800c13502c0200300150016 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 395151384 1250 395150134 395150137
    0x20f010f060305070504050106230d090623010e1302120a050a0201091401090b0a020102130303080a06050f060909060315070309030909090215030907050910060f050a020d081902 78
    0x100000000440c080b4594502a8070345212504014403031810100180221a4848400c10001021811540741c101440300402c036a8818408402d0086080040410a01aa9801845501d81c000e0540ca580014a02c103a141c024028020020414a8440424011020103403034001490005040403401284086a50306e8200c040340200c43d40d1f08a401c58005540e044070340c0100034504500ca0f0510b1011030702c002002c400da64040d00315042c902140d5400914405d5050310040410308800b1600030383c50b402c0241240404460100515060910204042c14840700c02a44800050989030400c00488204000d200d402080280c040c07080d01399030217191410b1103040e4002e005e152000104501d49080003000040642c21400390241021800801a100d141211002c41c507480c21190300c0307459a61009060280c1507100c20380c0080d580302030012044134984c0d00b00444440c0d42f1503800d280c2c00c14600340c0d414000c01c20000b025800615803200481d000d5040154083d1805007130403000ca44002100f0101d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 395152634 1250 395151384 395151401
    0x10e0105040e0f390f0f130f09060302010c080702040e0a15060501030b18070905030f1e06100905090a080c03070b063c0a0b030a060e010321020f01 65
    0x10b00f1100001d0140d41e04240f4020000d10181d0080707682e80c01001e20460541001e616818061500700041c41002d0384040c2c0c09940c10f40c0e880c458aa40e5841009054101504460149140308051650001040d00c440e103e500116941a111010000c0c9252548001030304406000da030001e445d9820101700c2001400003509842c400c0c6418051020014003204c1240c10036040349042c50b00c1d02c840d0385481c0c2d0303900485465140349801502e400c0e80e00c13030300201d800310010b0303109603054420850f180e002c118003c10518841000c2d24468141402c48048480c2d032502d0a640003030800851600c1403080bc1080e8010070740c0000b2200464070b40c0c0501c1c1e03607400402d5100d850301c2a11604041422000c2040c1d8035082c98110f0310440710100b040f0312240c8180d441c80d08000061504100a038024100c80f014000c0301e400400004010154865a4000981d50b5600488030384502074540b06e80800d145e800703005600d0680e41c0015954030000c00921740080402000c0d030000d01548614442800094401d00403001c8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 395153884 1250 395152634 395152651
    0xe010f06030509030412020d0f0b0106050d051f03020d0503130303050c010c091526180d05030c0f03092b030609140f060d060c030203070f0c11010e0105040e 69
    0x10285020401000c40700064080030f86070300100030410000314000c07904012660101c901d24020f186900d000d08030880d448000401070446e902c00000c41c0b40d0032002411200c4040d4009100940d549945c1e01c1c074514608110103442c9003115400c3c00941007480d03845c182940720301c0031245003c09406861002102c103a0080f0000791000076405180b00003070040319110940c40c1000080b603030a00040d41507400f0307041c41860810125801c4090481c50005030701c402e004844409898504006041108150400000c3c0a00340b05010300381238807610070021280b107080129502c42c00c2003000700240c4032550002e0809071062040c00032035a42030841d46000802042d41d0320b98000b0280180c0800340030703144235500c50200b0740c2c54410064846d44802200c168094003c000e080364a9903607400052140c003620131702500c400d00c3d0138996080c058040c2d0066001e03c5103915030f0700c51842400070450701c40106a04c010282c60792107e095460703500440b2150b00203c0d0504050303040039140e428102c0d00ba4421201c088 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 395155134 1250 395153884 395153909
    0x10140f0913020a181a01020c01020604061109060c0321040507051003020c0f010c020105090a0803010e07020f060c040f350304120b010504050703090c060c0f0206070b1023040b06040e01 81
    0x24150451001c2200700380000e0001e448c0c01011080083c1d110304004002420f81c0303844468090036100c0c0942220728000d401040c0c1c68442c03803c103100c182d85c1d800c08206403041080820349128800034547c42a44070b154840c2c0101401c40c20007003488106a900307509482490380a104c0022500310500554200144280c00000c48145810001307003565805041001c4940200012501081c800011a81518420340c0c0c0d0140c0c0741c882c0d0f54200c1c034100d900c1100c2980b5009038002d200c240b008401c0200120f5490300c0c00016003170b8503402444d800c8802c0c0000c2200744966100034000b1100d20590026622a01d0810344c0d042031380d21403000040702082ca2048810080e0f000040c805864184101900480e00d1f1504215801c80743d91900040c0e626405101c081c0320f070300403003001001104d03000051001d5014181a4861005240c08003c0240999482e00f0100600c400850021702d104000401c102546e02d2842b43c4500c06800c1c4002440300c07a46054000100304000b050440030742010074000d110f05803009 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 395156384 1250 395155134 395155151
    0x40906031202061b090f0609090106120b1e09041b061101060806090c1201060308070b0f0a0902060d23070e0a06021212070c0b10140f0913020a18 64
    0x242800c9006020090012007004c1c0003011402d580203540603010151003242c0c4546500b0700094070b030301416030b6065002801c04004207045da030054000000305241e44003804104400420020524505004461561b50708101118940303808090150814001e84c144907013034010745000c01c2c0c0301496030402808070310141d15000c00c0f04e03000d110780f100030300c1a400500100e040484000e030f04c40e5906151148a00b103003011030210b035002984100002c652203843c1d00e507150501e180404040c102100e10070600040403001400710101c03030090f500e42e250b000706000e107021881030180000780b480004190041203015104008000b01004041c051501900c038000c0c0c0030300c3c0404100860506801500071908070346064041200c3d4141542c100f4410046000030399900d0203012035060342c4601d009004440c134001070040302d101401d0f03a1005c0d15054007440e003a10007a0130600400c02c5080e109160800002000200d50160310842c42004500c0100b107100080da80b8405004400003000207445403a540d500d02 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 395157634 1250 395156384 395156387
    0x307031d03120310050109030f080f0c0703060614010e0d0b0a09050109050a0b2a0f16030c0302060606130306020a0c020307091e06150c060f1406040f020702060a050a050409060312 79
    0x4c0e40005c03c02441c03c00c00045c02c40e500c1100304400840e00030f00d0808040b5500f01c600040d64240c4800391400411120101d40e00e0a00c0d00180803a031091101c080d00c0f500c0c405280d9403245060a000701c2c0301402080c12842c46a41d00884114000e04003501d00741d030395441a0001d6000c2c0500030b10240100c00408260049041080444074003500200400b00f0300b801c3c001180780600b1441c0180700902100540301c1d5150940e61003503101d0302c1001e4000041d0b02d1002d01c1019001103500400c64081e508a5036195100d0042c04000e210350054801d1340d4203800000c10014030242c006004426170b914040d43d40095690102b0324180c525001640e403143c49481403c501c00c0212003502c0d80440320841480943d00d040c814401800e0030703c80000820044042c01000d02646070040e050110500b0020001c40009101c0700c561810166a403d08c030714101b40710121402c06c41c2c02991a46500104100c1c0b40150320740b02a41c059110707048081c00d004003800005410011440341c03c5c02075008030748211089114100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 395158884 1250 395157634 395157661
    0x11113050a05030304062c090109021903180219091401031a0f06120705060a051b01060e0613110414120726010603050609011b030e0307031d031203 65
    0x4158003d071300c1407004010301c40d031114900f2041845404401b81480a1520703500700f4030f0354010510780000c030110000460101550042200304601a01c590003500194001c0b800e0710042009140c42c50b100c04c211a0140c600303a44105071100b060144540c0d0342c0d03622001c0b5010f42c1c6080d811401c42503030290040091101007400040321248140000b070851800e0080e001c01c1030406040d03140070f41c0e10104002c403114005c2110030003600e0000c000a496050482d00108141d010352601c0c1240040c9010640340c50344140564810388000078440a020764690041c0301e000140195543c05407a110342040b5900c41b41100204050000320306c18041c902c0117070083c03080034002894205c1c0c85a0100c3c10400142c540700a10306c10340038166810485980c081d41d1524003416031500b024003036004000900a404005510100340301c06c039000030340305ea02160101a001c50706010010f5803507420820200c40003c1c0300d1800d0394242448202d4101c600715414000c24a86031003040302600b401c00010511003107503003141 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 395160134 1250 395158884 395158889
    0x30e0102120406020c07320429010914030a0813030c0b03060a050117010608060102160801200703080106050a03090f06140a0209010c0602070f0f0c1d09031b011113050a 74
    0xa1001e4038928141454947d80f06203030441080600341414107503429691504842031072090311081c41c08001626141400e6000c1c158034a40c0410043c0c03000040b00324200c81c00b004102001001f50086203201c0c2c41e9804c280d800303179100072072408200c03101000042c0c4540481000d044032403000d030b0f11ba00d069000e1042c070080d1500854144950115101e14002c0015900741c1582c00e00d107450700050b141d200042c0c2c60401c1003480c10000d000010740c007182c0804150311030010b80d00310f11b08002c204001041d444119100e1036001600081401c0e00501c02240580020328107484945400603d40c1ca8a4803500700801c4103900864030a5100e5500740300c00d004400c00c848c0c00203440c0c0da0452a0001c03000000e00780d42e0807988010039140e000704c0c0903405d200c00c80d401c02c142c1c0c5403c400710248007101840c010000e03200e98003410390400f2445445c540602b2062028500c601d60307090007145841401100d801c1e104118500800880d0340310350741c0c222a03000d010043e0201208810f18110902e007032004202c030018154 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 395161384 1250 395160134 395160149
    0x4060501090f1e0905120d0509010f0b0a03030c051507120c0504050102070e04020607080705030309010e070f0308030a1b0306061209080f0c030c0a0b0403080f01030203060106030e0102120406020c07 87
    0x91140c041c0100c002d502403c54021588000780041e072910706a81090010182c11620200100d03540111401d0390308198460030005000300030603103c40c035580b400c4410740c229464102903c0b130000e00020b40103a1440080f41d005004607503400004500d802c0004004550120004008403c2d01c100a407040c0a411440e10050424034149401e190001356601c00301d22508480c5030300e20001c2415500d41c002210705040c2c1040006c1ea9071066410540d81d698800d0b5500e41c5258a0010302c10341210001c1b070714030140d51190f90100c0c903480c0744d525040159000502074071a241e42d10112400f8881319071040f110580c07841e88000c41c14610340080a04031001c0d20310050043c40c24907600c400010b90220807180c0c20802030420300d80344c1031a21040380c5180110752600f0a60322a0314070307200620003940c400d20f00c140c1c0302c0c1d558043c0640d50818558100314080c030000f90598004801030000c9030094020050185020000500b800c0c0c44000e1071000550940c0c00ba168030f603000494070b03480c2c00203011080151489 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 395162634 1250 395161384 395161391
    0x82703030316230a0f0c02030102040608040302060a0504050303040b0c13090b1305010806060607050304030812010918051c020c090f07200304090c050f0d1a030f1207020f0904060501090f 82
    0x26000e000a142c0700781c194000800c54502126181705001e8584090722a401600841d21640c59100c0907180c00300c02c0d00c0a80c058841c107400548050020300819105940c021b011b142561a01c0e6038444401d02e0191215007102000c0c0b040da035500507e951004010016100e0100344060f000c002c1c0b20751520b908006064107070a0000607c4640c0303002414541040090300d1407a0381d0507030744c101a411805203402c010619078000440c2842043d030800c0c0c83d030580f038003454200400741113405451404801c14a0040154005031452105040f5a41c00c03440e441c05c007801074810710a52080002d8052404440d00450074072810706102480341d1001c0246400241101100ca100d802d40d00829502c0c0110310a080c0d1581e110080104183c1c130038416191007800155042d40c5030a403025004000e0801002e110075401a0003400040c3e91030001191547d4000c0305001d071105403041c03440dd11144d44200c00582c2c105030351070b0409003e501c541407040c2c40b4602640000400703505100c3d850b02511441c01c1c020105905 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 395163884 1250 395162634 395162687
    0x50f06090c0f1e1308010b040510033c140c010e01090b0a03020714010221130206160803011815060912030e0423090a082703030316 58
    0x80d0303541110a10700c910100c507100e203c01082914607912401070550300003d0b035a080080d031040150410320810804031418030013a6209441c0100085c118070002d00442c03195450107041c1442c508191650820140d41182554100c2d40c50182c441c0741480100d0b10345031400c007110b010140a008400d078011003403800c01444000e0350002400642ca50052076450f000008400c00624060b5040750116540203030381500340d003403404416000b90482042071078941ca01d5014000315110b840b8100c0d12511036141c0d04030300e9892a40074000e41d6000710100d0722000126a000102003400701c0c026500038200c9048100c00035901c051108107441406080803400c0c104007600384034003070700810580c060300c43e4400c9140c00a091814101e6a01d400003c801d90030625120307040d814161841406884440c020001d0300c507545800402d40e5440844143c0035210000520130b408003881c0340014140ea0440704190002801c102c070000900313683c4192060142c290040c02c0200555800000d00f40428102191400350a072 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 395165134 1250 395163884 395163907
    0x1103010e0f070201090b01030c0e090604170a030b0a0b030601090f080a12020c0a0b03090106080312011527051518060912070308030403020712050d0c0f06050f06090c 73
    0x3029015a0901c004800021036091003503000d851000d4110f4048071503940c0d28148078001d00342034080c1c14410402000000c5503080006040340c041ea501000442d4003180c02008603e41d50814084c1c9010107441e0003100760190341340b05803080034000c01130040e503603414484009040540280c1c040c040381e09000d00c0402000c0c0300484c0d5a1286074000700817410035006050100d0400280d071109983c408095030020230300102610245100e41c52180080245984500a040d0f4038069105465418040100148521010100308100ca4103040c240a15602e4203004003a01c000f03140c0c000c1007500008900c04002a2030320806241d086148100c0c0189440c852a0702d02283d0480e81514500600300015600265241c1852942c0504189003d4680854072850702d01c150342d006440a40c01031040300400320790311b50800c00720780342d4580c00b03c0203050316800c0366800d48203445c2100040d10010580285d0384007041c075a001d00d070300c5910311000999980c904081080515180905010801709042c00301640341c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 395166384 1250 395165134 395165159
    0x80703030509040504020a17011b02030c0606060c030f03010821070515060a0f1418060105070f1b0902120f010501171503030a0c050d021504031d190302010201110301 73
    0x120b100b51000314099a4500110f1140740203548296400100c07803000218815040d070002c0141d05141194501409800d03408070390301e0062600340c0070190070100c0840e034039161584c01004d0204412056a08082106c040708215401c04d901401403a0000240c44c556818148901c6170441034149000b400e08100b40c50302942c036034040c03e01800c1000c108002c01c0c8241d030340d00d4030704000b0f200b801040300100c0e03194a40c8614514a4203009400340198500e03000780d160313980000e10310482060707403414207094a03a262009a04000c07413083d60342e203100702d08916104481d000ca03500038141103040569110f004031815242881d0061090036081c1d002030061165a0b80602e2059955429610581c510b0703d407401c0c0310300054043d500869042c440051181d10b247d4006181140352409141a20b00310800040242e0325810300800884d440d008480c0040c2c006401104501c820305100700405600c4103000e00410740b1400d0001f000520500041010011984e09004460240c0c012000f03c0c3d06552602c440003812 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 395167634 1250 395166384 395166397
    0x3191803150c0e030d051804022104060f090f05101109010513150903050f0d0509120109021002010f0b0406080d050f070b0f0609010b0c070608060a090e010c090807030305 75
    0x550b15482c0c6a04400e00c40e82620680c9400141911008040103802800540c0411040d40c000c1c014184001d586103800d2007684c228410003d444207814403c200303e00b0800b5001082114000d035541003a0505a246109081c0f000b441424500030341800390500d14a058800810345d015030f400d2070400300b071101082c401c0d50360002c0d0a0a2094480036446003c80101e015038120048480b00b1440700788000740e2010012007120302840927124004079005c503168450521071444000b0410801501c00d0500f0300001e40240c0482c2070000007030100c8d081c0d0008950f0184038080d0b10050303441d02030850204441e44581000c0c180112000c0100c60710b0030b5803003521880d0380c11040d4107008020a007c110b00c00000c0490b400c0c25480b030000c402519003c3c401107811602515481c1c0a045018000306000d0100c03400c17155040240302c010036002e8074100d8202d8191400401e400d412034402c0341c0000d650302790340c042e066044400c0e0001046165120b6401410100d00783d1109a096112200c00c10100f6040030485c2c08 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 395168884 1250 395167634 395167673
    0x30a090e060301091110050c011506140a0c1104020906070f021c1e1a0a0e0c0904020f130609020d0902040507170c030a0b1005030703150f061b020303191803 69
    0xb5000c0c111007a10340f800303001504074880d4244061030070340c032500c44000ac003a90200c5d120861031030f0424a803034500d0f004040701e040104114441ca6004141010018210300c04001c02c09443c04005501040190f00a013200300e075442c0d4284180c504618019035554442041407010488144a5031103e406e11404440c6903c03250700c1c000100814801c40812603c0300b848146000d00305414051105d00c01002c1c000c007000542e01400705071040314641030415502031a0020000d01e5005e81c80e0003088492440b001160008966900c000904010a0300240141d070a810100140021160041c00166030005001d0b400b0800c000e01b242c28030001101031207401c540c3c0140225220707034400d983d400052030482006075012000b500e070951001e5024009620421890390103028050156200100c1c0b070409000b100d400070a441d40900c2168030902c65140b036400c401c6c001140c6004141c010a0941d888603074a0b18108080e0b28040707084d550030142c401030045618a00c26100c1d440e64441ca440b10440340340900 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 395170134 1250 395168884 395168899
    0x418060c080115020d1110050103050f0d02030310090b010c120c060f0e1203090a080f0415080c16080d1401050a14030c04090213050c040f09091220030a090e0603010911 74
    0x18070201b010001302d09030b0000441c040120b940c403410b020b9640c151007000880c1c2c83c4103407a2803140b564401710590b401071415486190b0503d0038038a160000e4002616590704101546858601113121000c0d0b82d107400540341c54000000c003080c20118181c440322a1031064107410305800c039802c0900000c20300ca40100c1c000342c16840e9101c4031a1503040c00c031054005801d50301c000c00c500d210300c1100c000500860f50204001150355400000546542d42e0444080018807428440c0c0320140c00c0411040ca942071050595514001215241341d0813640821044420440c420700140002e0030005000c1000c0c4c4554000f101100c1101000240d035410b0486085004945911030b8104545a13240c1200182c00f503120144070601d405d61100620750450b214540054085000010701c81003a8481c0320088c1c0e030040440c07429180384100690f07110740d94480c28a810041f00a503801c40302c3d414006080340c0388059981d07480d8149000602018098040c0256212b81d00d01030108000a1185c0606980e4260548000d03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 395171384 1250 395170134 395170157
    0x30f0314270901050102060f07030e10060306090203060606070b2d15090114060f13150507030f031b0e030102091306031208240418060c080115020d 65
    0x45a90780034409100d588008011000c0d80114886541c20004820540e40d4074180e0baa54401240e40750000d90b5a04000c56101d00400c0c0094402d80011070580c01000032140c1d40820340c0019800c9401943c000e45099a0b02c10302601149400d011090308450203c91030303401c2039125111034003601406045100e400402c4515890221071000c0d5600c6503075a000030b070903403902e0918140455141d10381d15003440384c1680c4001180044081100c04d010030805800b00741403040a886805450b400500c01050100000d4030025580e1400c0c041020800219540c0c0d40d00d45101e0b00d00602486004000141458184103240750942c1d2150010170240c160b5245c26420240d584001c03900a21500c001150040303401416400284265000401281d20503003c1e0240e60340d010400310754800c1c1c240d0300340214401c0d519405081d0240044502200803004100184402c1c50b05a962090303a0040802c0314255120030f070082281c0d400410b420700401102c03200304c25044403104001d40b03c003107440d4001f082c0444441c28 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 395172634 1250 395171384 395171417
    0x516033608010c02071404060b0f070203010b0301050c0a0c0c0807061101050606031603091a090109140114040f0305040b030708090d0306030302100915060306050f092407110d030203180106030f03 86
    0x300014041c94207212b41d10303200310381e40ca01d1a50040d030040c1d00070740c01d0030300d50a80b6040c14406d00380b09440e008049800e06401810407a501560154190341c6448040004101c3c00380c00d001c4c034001071013a911400f80b40320030f601e2100c0c2902c5000303001d2845240c0520805c208001e01c10081c0700c03c0da60902d40000c0da4406850240c0080300140020f800c01c440480401c40000720544c000843e190090304542100c0a13a528130900342c0c1c50030390910351450358100104001981ca00d4449005c01e200341000ea092a07101e8180084d0741d08102c94150009415200f4080c45620074025551141380034030301405007078250b03200a0769030341500301d40411040d61805203a062100d20202102c41c00004842408910360300c0c201803024080c180c0d0120040d04100b030202d1044040020102020030078a8240d43c0b5811002c0810b2101c004020070315024415940684042c03490309102d2075101d002942c5006841e410500c2d2a011181c040002800442c2c3c03400e141440031540044d00d48110740d40c1803800ca550000f0b108078 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 395173884 1250 395172634 395172641
    0x2040e011b110f0109020a03020f0d080f070b09030901140d0608030c03040f060809100f0f0c0804053318070b040302010305060409030516033608010c02071404 70
    0x800d451080c0041016008041c2d2100c54261000020030854400c02d0811490380d01700d40040c44002e40c4482a44c00800050400e100c02000c800f03001080c461041c22151183e01c419130211212007070000c00004d00c01300300104081c602e50003000b540019400d040c98400082c0c081e0350310080400c8a100c01048082c04405181c100300003809000e01a40d8403000420f000325900d4010b03010359280c89140500100d600c40c40745c030000b403040c0301020042281250401044000340025030b81140e1940d150000c040344d2600e58043c80f0484030056444c3c0b912464542004d40c1001c000002c5000070145011204240400420542e01203001070821040315444551000e0302819034400041424000c01c00e0000c1c2003103009c00a041101d000380c80c107100130364851080004480c040400180030070f800740b04031751440c441d01043d441603d110341040042508042d416002004014142c02081483c44861031040d103000c131401002890200028405916100c1001e07441b058a402000e0721032190100900c0f0550341c0e41c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 395175134 1250 395173884 395173901
    0xa0902030118050106170a03090e04020411072003010c170c0403050703200105040b040b16060e0106083c0114010f030201180e070c14060c1201061b02040e01 69
    0x8070352242e0400c90318100f4080c00c460f108525520303640c0c012401c685940858041c1c48a64945e036400021800e09103c0d200d8031f0005001a41c0140c1d64100ca0110780700c0c88001004194066044031810b41501038502d0f0011540500301402a410100000190768014065410b501c2204d1070210040d41c031482c03014498003a9074009800703407042250000c03d00801d00d960f07044401000e0803400781d8185200c01075034284910300c2100d0f5942e01c04c0008000611010300030b0140f02d0300c0038040c5909102c2c981c07240001d44500813000c0310281d64030141004100410001400c584a4043e4070807640f0400f4149518260b1200e15107104d40715080441540007442035005e01d41400303440703448600b256100c5411a461032900c2c001203000c15140e40300210249065000c400c121202181034148c1c0d540da60030215404940d0003411250840c0c840c002c3c0c0724550081c0052803043d4440701e585a00c840048118a40d031001c1a4481030500080494007003001040d480003081903501034401082c40710703212a17580d00400041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 395176384 1250 395175134 395175161
    0x105040902090d12091d0606030403030b13110405030d1701060c020105120907050a0806190c050f071101031d03370809010e031305101707030e070b09090a09020301 72
    0x580300700105903008040f410655260880e030756074041d098501c0c0305940d071090b40c004d62303c1002803001900080c880e42003d10f0182029041020403440a03101e00259000c0701c15003e41040041000d01460404105000c120745c61850099000042064410443c00040c000c8404221ba03585500e815a4003d6040b5103070707801c0d81c400050482c50560401e68848086020341441058034000c009954500040c0c0b80707005210700000200c0101b1140ca2060003000d0b0b44480c0c13001d000c03040c0030030031950400c00003030442d183c0a115078010403203e0000040840b00e03188052449481040c2c01c246604600006031020715088030714840c18000508980d0078050050001d140001009901084400703902c00b0b04540102c40710002405181031369440c907500d078040c044082e050191042001c03c110f01e04404400001149420484e41084440d24544602141129201e0110340c0743c91000c00841410010304000f450304a18043c14421404001403181c00e000e040905003d0f1075600c8a41503590070b41c041c00c11200d45 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 395177634 1250 395176384 395176403
    0x7090e040602040311010e1c02030f0f0105060a06140403030c061805010905161d060d0614040512040323070933030f080309030c120403061a0105040902090d 69
    0x341c54884060343c00350008036840307000740303d032002154014005807040180c01064800c0d004d4404442a40c103c00201050740d1500c40d4aa440c24004018005d080e002c21f60b19001080c80e10b00081441194500b03a4041020041c00701415055441200260750980c0d506241111030710410b42407242c040d020001000d010008620826000c000b015404801414440d01c00e50317510900c03644075500c0b644c125105410031405c61004050b01c4410704c40d1456440721004061060204039900c80c0412580200c00c030100c0c43c0e160209000c00e2103002c102d03084215195100c0f2503e03007400e542c0d600c2c51110445d00c911480104000613119114410701c04803010303048110b010005403114680380501c442c0c0305c10f00c20405081d03080300c164140c40d07940400d03001d9941086240c542c540207039542884950000301150311902017840000f15118081c0800c00722420300034156502e403411801e0040440e00c20341b142109001c1c6c0e00c0100845640c000c800d0714100c5907800070058450401102052408c3c6407804010404103d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 395178884 1250 395177634 395177641
    0x4180e150406230705071a070f091e120305070512180d0b07050a18080706080f0f01050f0f0904080309061303350a0507080603070605090907090e 64
    0x11496006441240100014000ba01c501000114049945071281c0c2c2d03d802500002003159019034000d1104a2180c02c8200c1c035803a071000d1044240c207094880000180380b41c030400c0f9003240d01444400161094085030780310000b007c2c0d040e42180101e07111b074a51000d1800c2200c4241805642075079512600201640d441c100400034102c3c0136031104510407017a00003860340c11203a040c00a440da442d543d01080040c85c2d40c460304825181078101140d44000c11200540d46888454805010720082030113100401e020703820900098140c00d0001c3c040003c0c0c15132442000800495404014115102510075a8100704950f01140241051202e07117a004075000c000e01c0100400800194868840c81041c1c41d0039031180003e8002001c80d503c00a40081c1c00c0c011007000e540048081c41d461041c50407141c00001701034000e46d40c080702d42190500955940c8400f004200358000c0910b40d840501100034107059402c100b4040c1c560702a41e103002e40500a10f8000418460058120001400f1158031020315441c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 395180134 1250 395178884 395178913
    0x1f26070c0215120601080903270a08190512121302011101180507080c06030c031906080a020907020d14031005060324040c1202030406060312111902010504180e 70
    0x29050781c1351340c00144003d000950100011041da1019010344c88801d82900d442038225110036807500850354065501100022400820050510741202c1099040000c68090030050b0030841500351410398900d00b007010700c0075462248a101d03800051103801407980402400105c50030204031030103241c2503280c203007002c0c0402c1a0309101d0f44050300c1138040311206a160100151900111890a9000304050010a642511900182d98424804040c0c0c0c00440c254468402c103070390580d488850181c000501110540c2009280e0547c13001e803a00050507003861241006001820000c0d032008203d90203c0803030212000c040d0b04400504000340296241c0c1820302e507468ce041c01034505202d0000e44000303103062038103280c0180782e00780c002c548424491701c4445085074080e5000810032500c0a6880d5000b01c0010941840d0071401070765561915912015004968a03100c0c4401075524a40c5000c421a401070f80e20a00f11403c1e51401020400d5030355000c05442c015001c08029030b0980d001e01100d080040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 395181384 1250 395180134 395180167
    0x20a03140a06030510110a050c210301090515030c01030f0905120a1101060501020604020607140106090e0d030513300503100b13061b021f26070c0215 66
    0x690244044c0c44805d8524030a00c01100c681c1c000700c07400d2100602809803080d000307002810b42c040504090750200314104003540101d61401c104d00403044000b01c0103100314021841120f501c42c90000e0380046012801c2e002030f030390301ca40c0d00300e4074101a1202190b08541ca0240c00c240c003070365072200860f03180540f000601c22f42c942100d45503000280207401c540030403d1050185204862041e006056152515024040c180e408072005a036205401c0d2440b100000007481900010225420300242031043c011449040122562004041508002c00d1110404003d031412600c25444007118881d012209410745480140d000e0000400318080b00d24480703242c214008501c0307012400342441e44a522004002c0302801805c58020029402c1d800030301046028100c124040d400d80010149036041c95800643c0280b680380f1400c10030b454038450014080c0d0007420110004020355002402c1b0f107200c180d2880f40540060604c810004880e90074015134032520001080c0c107003409405980c488089408801e074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 395182634 1250 395181384 395181389
    0x2f0702040b060415200d0c050c030c01120b04090206162d02010c210207080705240f190e010f020304260102090a06021b0a05090406020a03140a06 64
    0x4509200c0840ea0300c2c0341010840b002d40392240450080e81c41081c3e802c40e540744509540d0400c1c2e20300d201c81d2140d0348104001455550495035500580607485103061400e14210560f901d0080d80900021401c5a0300310b281d542180700e000c00002102e000c540c2c005405070000f8400a5040080080e8140c0c24080d400c842e4080c0e18010008020300c0b4402c0b80e0510f801008000845120f02c1100c0d0030000158400e240c00180c3c0c5024881150001103d0790302070301c010324100508405644072060030092207201740020401003004440d455141010102c10844a0060801000e40ca400004041c0c504000300320644000e500310404040341403101c440041d04003124190018080380703100c800300384041d100001316019182d0441503000304082184503084044001e510f4209555002d1001402545031081004020b02e01540242184541600c001c015940c2c40c843d02801003240c00020700c0603481e05101507030401d0340800b00581c1ca40741030a0860081c04030150072070b00c3c10360607010b0014461403a0060810f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 395183884 1250 395182634 395182639
    0x2070807140a0311030306060d020a091e0302090901020a0509010c15050c0711040c0e0d06180c06090b0306060a080c090a030507080706032c120301060909050a090f062f0702 76
    0x43c07445403000d440d1740c07800304844c0c20f40d011804111307841e40811140c002e0541154903080200e2103d86036442c4400f0b40440d40c19284c96421026030400640c50519001c0c0d4000c20b01000852800300c4103a0000c141d403080d225064148180d032414207041210000c0501d481c04076560003000340d414803e1200049501c07050f02503440344038507010400c0314a028030072051003441907200c46146411076400d011440c80300444c10740d2502c2e61092142003900311095070701041807254010200d00303810030802921201c015000a1035080b000e0040091070f07101c81d03045415065080c14103400554070544c40c401e15200760b10038141c00030903010b400010001e000500c139007500c0d11030040e180c45607110781044040398040c98030b850b24008603200032a2021001100c4841d016801819110403403000d15443e026a88280e0011002424640f420461590580710742c581200141c0b00c01d000c04025a2101184202c00000180030380b540d0b14044030701c10702105500001624810302d0702da104c80344501260303d181c0201101341e0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 395185134 1250 395183884 395183897
    0x3110d1b0612150e09010e03070f0c080703080d110d0e010b0a0518060402210712050c0705060412120c0315050a0305060118180b0601020c0415050402070807140a03 72
    0x140d040c00c94040c0110829401401c0c203a00f520705a6003880104001d00201069581d0b40e03010b1482200900040c00241e000d1500c20402c9006440e04810214496100344440d402105090001946c4642103030f5050f10041004241100c0780305100c0007910502c459210300d14540b100030060f82006401c0700080880445115244594660506c82c5480c1074207120b032403069260307000848034a000d0b8041d0421002c0313444c444103890808404408907042c03c2e926100418011407924900c00c0d80d42c01110f41c0017541ea5801404e00b00305039a200d54514020300014007a805000e1001074030b034490b0342d5940c46011140414000da440443c0d0150040480c410340f12405801544d0220309030400080b0f080c1225403000007003100c0c1e840c1c0b0300c801600248103008221040d031608041d54448562940320210303c0e000302259260f03401e100b00068606401e40b80c4c181c3c0518145003044048900b00311048007241c0068174007603954011480d040c5ca444c0f007a00f5004000c00b040310b00d5420031307100014034036000512a80724503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 395186384 1250 395185134 395185157
    0xb0a061d1005092d090c190215090a06060e0606071506052713030f08040201031410080c09040203070303050c1002210a05040c050f0619020105070f0512010b070f060507050306010e0108060a03110d1b06 88
    0x1d00c5843b6007100c060380c001404002c3c90000407000104802c3d24464000005907654984000410112000402c0300f02c4c3c94002c0368412094040390038440d00500c16411303110605150ba500a8044c880f101d0000003444018000201564020f412548003001c0c40c00c1504041d107418101000100c41c180215240d501c01c0ca00c056500d13060200381ca900a5400800801445140d075a08a40355804011206480d00403090350050403100c0380054243e540d19240e084448030080070203801901c07001060701c1c40241c10401880007040e40b010100080c3c69066421492454a14011403214811400d00102e10002403204881003541980094000d141c4c0e41c0d1001d101c9004540121420b0183c0d5101100444201c40100641800b00c4020305005200f04241e02010540751240822034901301c8119020900c0002000460340c0d00c80d130304e0a6030820034201046c10f404c1880202c2d0715082e00f03020041080c01d4140000e40e00e0395907108072080c000c7e80010000750f46161400080803003401440b844c03001c1207008998 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 395187634 1250 395186384 395186399
    0xa031508030906030c0408070303021b03030a080a111204050303060f0a060f030f092a0501110705090402180702010b0a061d1005092d090c190215090a0606 68
    0x261003150450340046051801080412074158009048140303014010000051103500c14003040c8001c60081d0082c0c03001140d040d0008401c0b19120104501c40d400401c040603426070804189a080100302400043c1c1103d140b020301042d10aa480d11445000b400041000f004400030065101c0c001c01c0e01d01000c11007038181404880a014082e4038082211070000030221880399104949c0d98558203800700d40142c941c0c031f4005004030100d8040c40c4c0107011010050b0b0912003002c0200003803100f881c2c03c04007070340074032402519084280100b03031084242502080655507141f18516091001034101d032000c0c01d080d007000e8001d1807101c4400c0d015000d4102c002a0540c0204484c01501102080d0030300b013070800300b04200e00103002240307801c00c0c0142032100c0110b07600d6451310341005881d030072921a8030040c03103654500901501d441140c800c807109810884481c0f032407400e540d4018602c0e80c0304882089050402d034205142c0c800341d2724805c000082040a0102c000130a401041e016082c00c02c105600d8055 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 395188884 1250 395187634 395187671
    0xa080301140103181b1502150606091305131e0309210308070c12020f010617070302060d0e1c031a01082205030c010c1b1509080d060b0a03 61
    0x80a40c19145038469107003c541005c440488910210540391042911034070743c0c0219100c088072120050703200408a96000c0c03100f04101d50000c0d012110719091008100000700016040000256103541703a0f404120a5201c1700c480b0300d126580007480c0b110b03140010380d814460b118100000d800255520f50300250013091503004c00e86262844860480040c1140c4081e2940c0300302034540d004019802e40604046440c0300e41c1d00d00818015400b42466030704008009003511000d070803043d01c4181c24210b40005900000e05001181d50664119450710692610080204265001080140200128100103940c130940c0d90750303824125107007001440101d5a024040049510074075002c183c100e00400c00050100e52800e0003107510014002090069598050a6401403074600c01070343c0d140e500d5040050740203111500d01240c9070a8941003005076480d000440d102a1866007881640c440340542070101d204201c4200011440d01401601d650743e80c8101c041e880001d000e17000a00e8044116204000341c030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 395190134 1250 395188884 395188901
    0x3110102060109060e15060c060403020708011406031c0c050106030b0708072f0f030c0a0b010803120a110d0c0f090915090509011d0a0b0a0212070c02010504080a080301140103 77
    0x72201101e0b640c4004513070031a1b440407680f461744500280001b205840c0704200e414801c0d48207901a00c0703814074104446080d0381c044034030841c110900000b000700e20340b00010030510189641500e90018140103038140c4d49149040006452542070030000310500400719802400344c8195652451203580c2c1060458441481c00c4940034a0581411110800349075058503080f0038400609440c41208059021840d607407000d455400c1a80008800b071051040040b10b550061010601a5241078400d000215603148001c08480c40255102904036000c141c0c1d1042c1c4803886070303e86007084641c3c140300c0081c0c40705200e01219400150300b54070104510b4070364000c1a440c0d5070030180380c450550a2001a0f005042e0040007551a5981e4a00603903002c651032461456007124440907250703141607410118140318004100b001441d0041210003061580c440b04c440c0e10003024600030b00b4494491004a03410f204a130b01c0700d60305100d4101010244810400114101c03a64280d02100c0494620019025603090302d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 395191384 1250 395190134 395190149
    0x6021c050c16110607060510141008041109010305030d0608070501050703081b0708190f211103101706151302040801020f0703030b0306160f02030906040311010206010906 75
    0x601c04500703256001451500c80512583c03550302070071024400314000750001d0741c00f91240c5448200b80001c05c0502c20040c2d0140926914140c2030b120a1004681040d0601001c0410800044005420300c8982c040740c0c5400c9100904890086d45e5a003820355998110343c1507820400e103080b02c00283c0600003c2d9840c01c41d4410386840d81400318036101031303034901d1004044840040d0003000c21083d49568a0080c040180b2a6907041c2d00d60210a00f0f02c10001010b05514040c44450484180c03015040700c0d4001520500400203490f17601c6140c0c4000184c02040b4500c81c50070804424014406141011181a11510b9100c03040481810b0040d658882d004d0318103d0076042c50180d070106c20308000c0000c05130314604c1d42025103000da64110f5030b822030703012006281d0004000b040020070540d1500452841d40f9017280100494200141040c0651598607910020310500d211481e0341c590007841130310703000240140080d894075500c0c00d250300149051110b00740180900400414014440d104440998214 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 395192634 1250 395191384 395191387
    0x30f070f0b131d070f1704060b13090b07020f0313090e070b030702030a11010b130b0d02091f060503010f03170d0207110a080111030c0a03090f06021c050c 68
    0x144030380c0c0d8119a11207406688602d101080100f11111507401c180090500070b40201c50350b183c945401001d01402c11080320411541030161400341c0c4103a05a203401c84c2d000080091051703480d00004100e000d000341c888401a00b040391030780034041c402c121030f481140b01e9002c1c1d8080d50f0070011019141c2c400e0303401120358034405610500c1500e0071640007400390710000702100e20b41c9448004c40c0420740c10444010f40103a0000801c22521a48050680a8500380301d0091240c0144800050069200205806e0010303030340351442d02169036100389140c441a009040c040b02400d10200511a42070312901c044883c40300302200140c091f20130411a030485034a000780e48009406d40d0344046180d05202403092a030b040078414080c0d100780034401403400030f1142c11001840104101402464003281c0e1203805240d151410510301d103056141120703441400d4040702692820b1012007600200b008aa000d484440c690b030055040010a50040056042040c2c01410f00803800c94407005540c002ca0300c0c1c5450110 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 395193884 1250 395192634 395192639
    0x10c0203070f0b1012060e24040b0c09130f0e150f040503070b010605030703060f05030d0309050f010903110c0a1a0703140a0906080f0622061a09030f070f 68
    0x20700c1420a90000550242070090075620705c240982451810b0b03040c0d5805a80d2103441003a00420044032000d18024000d440b52365251b03e542d0003034250010005882ca100f500001034285802100321001e64000810709403002e42c80c184840020050f0030071340062a480c24803034071040340d4000782d400381a101074480c44000b90748a4105042d0b80c00043c1c021603041c030050004600060101e01340d14064082941c80645138038225000078180d90032544001705910107080144010b40300840c0082845a607400e010416003883d19003149030a0071030804588075480c0c507402d54200f50b0f000c000140419050030403104280c014900300400b401d940e200c2c4500202e01000f0814a00e09000701614005000b402d145c14100c0e00e01c40070744a281d020090703130000a1191101403113201d400408854100c01070740c600c0300043c907200010401c590541c00c0b041200e00304100802c4054403060b04030308094801e000003204400c4001e407203103c3e2508010611403080c061465115540c0d08002180e4003202c22264a0000407403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 395195134 1250 395193884 395193893
    0x2030a080d0f051311040e030414010c02120303061f08061c2415080316020d1e020f0405040b06040b03010603021c060b01050301061d011b14010c0203070f 68
    0x1d01801c410005103031070700c80b90030540c4640d101e2507200c0c1e108400c8040c00340313002e4681400442c0140020358822441c000340443d0b0040c1c0041603605440f90b860210504400881c016110903c10540082d4000d8684040e540c0658002c005580603600a03141d000020040d0030242c0780c510200032440300000c4030b90340012020314007c000c4103c0c04400f0500000b0540072500c61108c4200c89210541c42c590325000c0c070040410380c505c900c0f03420304040700d24a0b003407505100f040c0d40c5238802c4884c9407000549500402055540e00511004125031200c1504070103031001042030b945424010b401c0e88280f111180d160304505250203600e10032580417400e521140c0d1408104001040701d46046070b015982e4440100c0161124800040780c2008954840060082403510009540070080c03481d040120902c01008001e4101604a514054501013800d4900c004e500480d840c941c116500060841d4085040301030140a1410703012100401c1c0083c0b056294a90782603a882c81401001099000ca182416003c00d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 395196384 1250 395195134 395195137
    0xd170304080c0d0804030e04090c1202180711010f0504020d24180605010909020303030406020c030d1a10030614040513050f06150f01050301060e0301090215040e0a0902030a08 77
    0x944101c1c00c81e418010b105100e0340c0b902900c0407042010030909400c0c4001e0640100d565405080f0441d4240034075812662002c080c01c0761449441204000c141902d011035031110310f820b4002125041d8110035203001c100c010f10301c0b040340c0b01000da1540703070507c08414555140500c40c891070f00a4a1050401a00e03540c410500403004460140140340502840901d142c5002c0c044d690240003150b1100d142140c107050741105c0e41a40700541c03040ca0310001100584000c0180c95003e81c21000060b196000041114114814081c2d52403000c0c2c07902c100103011049500120100800640705541d54031010031042d01103407151302490300d524042580c585141c0ca06508410352101c81036104010f011341540c1c40c1898120801300c0040075400c01c504020b05d0004407541100242d03400c8650034034502403000080c1640c8010b0040e0700810242d10090802c0343c13000d402c030448988e4003512155014680f03107075501d10341d0441d0044120340c48034040826001c003100d00039803451540060140108070b04031b60b03680c0020f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 395197634 1250 395196384 395196391
    0x7030606081503100221060904020d0b070912120f3e060a2009060304060207050f0a1b0806060f0603040201021603050c010e010f0903060b030307020904080a0207050d1703 75
    0x41c0f003084c00000b000a81400500f18440d150a500c0903485000128800c0800d001490a07001e42d12080400001d40e42d0702d407400e1011034002540584589030f805040781c103444907400040203070202d681084d040142e2401840d20a05080d41e0b8000c6115501340c00300c9420740c00072002d11144204070b05204204010001d0f00400c0941126020728013007203000d80714100541203d0b040c00b055582d5003c00e10128801001142d46880d8025141c640301804000a884c2d000160000d0407003540400d070202003150412140300e281401008840001c42c541c03a199000d42054610303d11510081c140c005000b41c00000d0042c002c1c48002c00a0726a414004103010541c0c000400a0781144214202804500380c5d07054000081c50080028040840d1007500142c4a00c40303640086040228602040221a510404070005c1d25401103010841c100c55200080c554000c480e0040e501900810501c410408100c00801031100f07a60251529250f56000700502c2d404c000a000c2d00115808071032207100c00383c82009503031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 395198884 1250 395197634 395197639
    0x3051b1c05060f0a090c0b0d0c0c0c0605131d180c03060c03040c0506030c0c160b1210170304030605010e0708070e060403060f020306040b1c02120a05030c06010608070306060815 78
    0x155114140c1b540c40034140c0a600c00600d451000401501e2002940aa0680082035007001040d01c1d440c0d94600c0b01e5550588a01e404006010402d40462440c8062a00040071707003100305030320443d4a02000040590903180c3e010484110481b5180080d004294800416401006008145c1e101d440c0d810f06640000d0048903003818001021070f01e503440c1c03000385000f90a0010010344403001c1c11f44062400d50b0314461050380072300841080009000303110071100c41c05002e4000c416180c990800300e001c15145e9402c08010580558040c5202d4003000000c1c10880c0e0061506000a0341d94040b94010141d080d02c21400050b0103038002a05140251510305e045200074024919086c6d03680c5400c4115004601c1d8601c115800005111003441d10f4020507510040c125118968100c6c00d113503000e4203e2000310001c2c0129181e074032620101c1010b010454003d074104068030398a400071f10690b5100c10b001d0094001080c620f01c0410791f600d11a101c1c00c0155007464944ca8031986804503101070710b03040c1242c1540d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 395200134 1250 395198884 395198891
    0x309020303130f0303020f010506090403050d0b040c120f020a36030602030711010606050414041e02120703020f0702010e13090602040609210303021303051b1c05060f0a 74
    0x22921070884000018410a0f82c0010000c2c01c0d40f60003810410184000305a41e030408040c003c0c1130380ca01d2039482e0041d1b85802c2aa13034070501040740001410f03401803420303441464400ca0f4201280c003d50200c1c4c4101c45014100401c040304a1032004074002c400c0c12400040e1192104403101e04a440c8a605019821504401072030608004401940e95030301308441c0e0540100501c680c0a8104c1c0111619100c200e000784003860a09000170320901880c8609840c410442d00c1495540e00c85a200445402030000f1480703050703550312210006940b00440460030104400c00003407101d4480d20952300800480c4c0443c51170701c1d05640044611465a42c0855400300400c2c5a1503000d0343c0c98030980c038506105460250b129454007201406440d1190311064080c6a0308400400010031009010344443c5c2c50700380140c07900d540d0340890a2240040e04018002d1048000d03036603001100c1c0c180c000640f1411074040b030000701c00d902c0c864200c500c503001c02452070b4480d1001c194000310045110303500010414000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 395201384 1250 395200134 395200147
    0x105060c07080f011e14040b100504020705030a0f090f1511010c020705040506010207050105040e0711030c0f2b08060f1305100602070609231206100519060309020303 73
    0x1c1d800c040c0d00da001485075039914613072079511740c0c40070040504400f9503407000c002c1003403104120344200f00010001022a642c1100080303840c00e011624601825000e0411500c0b80111b2810a03503d501401c0488003040c9414202401c152141c080700c8195450400031084040c03a20241711001d5082c4c181c5101401180443c2e102d00400074407811000c2040b5a000303160082c0b0305070900040320401b40056045400008061180c4c2c0d801170120341c1202c0300745900c0d000507942c4041c225114032220850006a010014103004181c03000030b07031007040c445402d068645800711f0b0356480349452884c4c8842034503814021703181c3c030702140a10742c3c065000a000d000c2e1026000604006030700c11401c002c016503800d544000b4000c1e61070006481d14003500c81c2c2c1c0014440581025005010440588101011940c0e070350120b007070081c000440710310b0000000e44804100800e83c40ca541d25503004581e40c080122240d48000384d00d1500700c9441c00841c41c01c03445100f040e41045012009010000001c2e0703058442000103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 395202634 1250 395201384 395201399
    0xc04170106031e060506060910051e12100f03170a120f02130815010e1801060e090f0703020619030b06210c030402360a0c14040e0105060c07 62
    0x812910f80070310b14010964860346090f6080304c41c05800c15010300b1090103880b5040c2c0b200b5112a1540c012400e00a032102c6845403028032146c102e52142100c240301180040c114681203807007601854485034405005926004289280940d40c480a8030381000c0b03820118031102181c0080500400e540340042d02d008042031400d050700c843d225201e022941c00540301c1c2044440118190140480e039003d8240b80d1b601b4402020b15903418013032030142d08580d10100d02122400d04a0311010940100280b000703035074a00c030903615102c044581c0c3c4098001c00000c03400c0e288001c556081900e5000305600d0400c0740e8281c03c2883d030800300e140c00c42895900c16000c003d0783d52342405421090380900020801c0a00303480c495601c503001602ea1904840d042c0305000040e9104109200305070485204001c404a2105114102484000c952202c01c04d1240c140149544944c0007400b24402030348407442c840b00d600c0c40d0f12886125902c945c42040840e03400511052405000820851801da0708844070640c03541c96 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 395203884 1250 395202634 395202653
    0xc0a0312121b090f050f0609030a06050c0d1113090b01020f0a0602090307061806030902061902010501050f0a0303050d0b040908040f0302011211090906040f11071a0c0417010603 78
    0xb0030307440d016802d40c00060500da00c401c0d4500074002c4108281c00141c42c001c0865048040c107501030b445071001250300f040d151010049400500d41045043c0700360b06000d0142a802e9001e502010099404c00d402510054117100849070310380c0000a59106880c50300e40280c000f000102605d07070440c0185056072400e484100318014809010f920011382d510601c40c02c051502c1940d610100a001c070030101d280da0a50b50050310000c503a100d04000c07612a01c01e10000750b80d482178205100c500f00700c84007030102082d41544414141d400030b031a162a1542c0160401c02015000d10000380040c608000b811a0a19290030402880c80c1c081c0020812407401d0342d4041458110340c015003800c10003002d0401c2990391101424030502002c0a04110200110281d00c50600c00e411001d40541e003604c0100385161901d07484588040d90701401000b2218661203041030030b078884401521b58148c4104c410341e12907007070802c1900480850303c00d0740c617091901c80c0b0503410200705c41c0b10b6141035503190703000030100b04c9800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 395205134 1250 395203884 395203901
    0x1080c092d010906050a030f080901020102040b2206140706090c0801020705030a03050703090b010306020a090506030a0207231e0703051c02100506030615030c03100213080c0a031212 80
    0x5001a07415070402c10030f40115925540801c5c450602c5840130400704000990076400c46800a0301640d5540314000180c4c00b81c4141c3d44840444000007442011858102d4070810b03000030200000c1d4601c60352514200c07003c40c40b10104400186c030030840d00c00069416404201a90322455403201c466903a0908075089130071466003500c8a070030014401c15699131500c21554400c2003410100400140d03a01c03003200c0c1c094140801802c103070340000d0bd0a809400380341124010300c0c00800183d628900004000d007e5041303100c0c2203c0f008011030410380080011504125612086001001a902c072422099040d900866412006014540021011410600080341700c10003484810003291340489009142601d0000100c480320700c0d100a0040307581d4041145604001007240708e03025604440002070420071210460356242c459807040d00c085025640251400c103110340300c9903100035540c070074050301d46180c0d10041c0d85c40920341e1000d0000444410107280049003528001c24254222440942107880c1d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 395206384 1250 395205134 395205211
    0x90b12010e0115080406050c0904060f2c060d021c0501061d09072601020301150e060301080a15020405030607020717030a050405040e0c03030a05070606060801080c09 73
    0x220018001c01c500640300c0c034014070360041a01c50510440200600000018000500e0b0644950200e659551221305481c040c8070011710400c50345070341c0e6140005d00b00041c41800b107070340381c0200000b891407030001d50070940800d6480381503810307550f0f1020071000d1851500c0c200d070b01110404080440b0101c001120071924450400042c030b59080c18011030f4001a2143c010014840440821403500070110781501124141660180b000c404c84440c0f8411202c001c1f0b5a000642c4007000020f4080e06c80d1190704a180001c0d02e8149440d07000009111261200b40a0000c851703208dc8241c1d000241c100c070400032910f004210040c1010303200c1002070f0030120142c400b40d00690103c58113110f600e07100400c0c4103030f1074820700046250624068000e801809503204440c4103698038400c9010404042c007110f450003034001c003680e83e42c8208801c06440c54205007000e403040e924240001c070307031203000300d20a6059908120003000520241010041d8500c0b0081441852041241107820500c035028011811080b0300d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 395207634 1250 395206384 395206417
    0x15091d01030b01151205060105040522060f0608040f03030f0f0506030c0f0a03031116170c01080c03012d08010207020405060d0206030105010c0c050a03110325050f01090b 75
    0x40d0b003450075180320103810072081491a031056940d0941c0204e041000c02a8500000c40c241e980c40300182d400c0e025030b40c0543e802410040c00c25004a0126100080c003150700502000307041d40351900700860f00700354080c4001081550012a011034040712018082034440c1c41e001c0b800201845c0c8007010f0341c0004070040b004030b4440d0184130003803409100081c04034409580c0d04580094403400169289a13034440541403041d0f0241814040c50144140347c03801c052021100000d50f522150b03041030000d11108881c2600071181d460410b5840b81802d64081c000720300c0406d0969013407400e00220300c1c5400f01c415401508040c04600e68600f4212010002c050b054001a1038010354018001580c00042106109640c0c2440380c00044c1c0c0c0f940c0c00d5a056980130701c0e184640650b24036000416600c503812180d07210502e000c00000f000880c0d910075141003000e8050b03030011001c11882509007103444603503c040e1080e00e0320a022600701902858080281458000121561180d100c08a0303489100b0148000d0003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 395208884 1250 395207634 395207639
    0x901060b070b060913050318031905150c0a08011412010606050409060f030203030d09080d18032703080f09060304060207020301060e09030703030b0114030906091c020715091d01 78
    0x41c207076078481c3d000c06403440581d9908125590180c881c81000c600c45040b0351039003c4e4044548080142d000c581c4812b04140e0301c00c01141c1402540c5011140300c00310443c841000144400c41040142d440c003850989441d8026420520800711200300310030f9103600b041c0c2e50000c15020b400240580720040c0002d48540c0c1e92a42000c0300f400c04d036013194000a096003526802000180c4000003229038141c10b450001655410601c2d011800d841151480030310a404c0c40d00e49201440c246003c800401c0c0300e030301c40140c0700b003625038202d8100b2211603d0441604400d8000c001286402c40240303d8540c112840324a04a644000a03006400565081d1002a13000c41d0311811070400b442024043e000200d094000e510702960681c0c4c7d2441040001000c054a9007000300e0180d0003007860405c0d81244018041e100c3c50915a0b003a80d03010f08661580340b070303c0742001024007902c83c2c0c410310b408560594080e10005003015201c070b0341001d8400491040280c4140002440c8101c003140c64607544894511001d00d51 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 395210134 1250 395208884 395208889
    0x4020d06090c05040c0207060c02060d180c050f040501050d11041506080108120319020708040306020a08091c02030403030c0c08030c1c021207020409020a170307050114070212030901060b070b06 85
    0x40550001c1740c1554041a8180031b00ca4020380c0d0400c050340d0440d250b60392020310081e004094072201d000030038030803050f440c03003c1040b90342202c0350700b500c10551388034141c120064200001c1c0c85007840703941d80002c0320340400000701d11040500300504001a0020030424580c0030f05031000041503202000091411005000c2a001440004882c44448c82e60310300b1410b000440540485500d14444515907000a00e80c00f04032180c4185e42c01546c101600319240c0c0103494000d800b2000803504803a960082143c0c619548031410b01c12400c401040d4010340c141815942c090b00d1311191200c007510495800180016a40410001012400c1020b8081d2030f0300629401100b2608076003220040c190b4100010603520501800242d6140940444012641e0b0300c103400440e84401d029000001082004010901003103000001801071901c14002000444520710080d170010b41c2c10303624000107070011034240c40300d082c1d400051034205410742c3c00002d131582d4070103413003903e503000000c220741005202c400c024091 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 395211384 1250 395210134 395210141
    0x4230d0203062802030c0307051e0d0501050108130309140f0a0b0703180e040f06021e041a030c03070f180602010c030509010207050c060c0705121b030d0f0804020d06090c0504 77
    0x81420f4002903040d81000000c80e007460000825000130000c0124018000d603010340b03800321000a010207015500c501a40ca4400507100c03d00456020400e07603c00304041c120020030315401160180d6614444034100810310801e0780322100f41c1940102901c50081c071560312044000010980007014039903501d400d2030090010b440c2c2211061155010200c2006215501c6500c541e00607402074a20b030314052186041380003030145a000011039a0f15580041118230080010003c4d5000985103112606015540c2820391101f26001316a42d40180045000c00c0c0c0280c005640070030039810500b40600e8800e80070b50001010750f20550050791280c00e1400e04c80d03014030415030060741002c000c0d031501d1010303164a5501c45094846500800002075000b4990100b0f02001018083c0101484482c00401c15416540c4c511610010440f018902640d0f41c00e18000403280c140101c0e41d203c2c8040c0750f6000d5401d582000000b0426a0400b0720389501000184051050300b14062052489010617402c110510044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 395212634 1250 395211384 395211451
    0x1a01080c0d0b060d14010e010b012307080408190c0b0702060f0c0f1009031b210302190201150504050f040f0305040306020a030c0908060105151c15060e0604230d020306 74
    0x1031009114081c07031810105001990bd80404000c015916003092a181115100310307072121031103015006413024242400040050403d014501c551030080d103c592128042c030801130000e43c406010007050b0040785164015000d0780c0882c0d001c0d5200084540c0303a0608044d0884411022159144074031401c040e0495408540581c400000070707078901c820b94401c110702e0040c002904181d240d00c0210304080f4444d0b0101e60000c041c680441200d101c078044041c1c082d100d00401d030445803415100104160030948201c1e032142000d841641403903100c0783c554040840c1c1c1a0000c0c0d0402104010110114034030b0700040884040b40d84e00040c50b0f041091000f0b08901139504000d02e6a0003050042105689000d03004003c0305805c1840e039640c082c02500105841281380320036003a42d041200c044180c580d0000e00e03208440f2140c44115046428100f0002e15102e90b026080b1600bd00d883d420205030171f04840d0401c0004081c0c581c94051640c4d400103172420302c0c2180d02101e041130021500145e8004001d0998a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 395213884 1250 395212634 395212637
    0x7021b13090b1905060a0e130c060903210816020102040306050f220503091e09042103050601020a03050304050a0213060603060b03041e0c09020301031a01080c0d0b060d14010e010b01 80
    0x13080c10306070005040c02c03805100c0c05080709180c00110380d4200e5980300a50002d6845500004140d945060190000845210558540c030b078110714540d140c250442d8007c42c00141d0354821015603640a55444003101d8202020115075080c000400020f00a03ca090302940354862a84101d10317102c0c00031850805042e1404c201442030807480d42c0010800019689009022a91449042038024007000480f4500081070381c0325081c0020b002c2848200da0030841d103114010402911071605001c1601903507010313126180164400060b56001c17138401d40c041e507000792149040e111403589680001744048140b400742d9036210340c1d0303020801c0107580503c511001400c00ca00e6403400d501d072640740c03c41c5905800340c3e4440e089004180540400000400303000c09007410403000c64403542c490030203d62103007400b1900e016034440c001c00480c22160001e840403c0031001800b01002040a80e04c86c01d0700314000c3d0070560091034441c205070005000290309003590301d41d200009090ba598845960030b58004800150 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 395215134 1250 395213884 395213891
    0xb070807051b0f03240a090524091209130b270121020402030403030b120a020f060304020d11030f031c15050618060d180308010602030307021b13090b19 67
    0x4260860422403d10b01008030000c1454a58a051981c00640208840245640580074100020500c000a40592440f031058009000c1c1e56503075009942d4540ea140c40302c908041480301191074a44004c437004500c0b00240c0100e0380181d4040800c400c0d01c0c0c0035800c1040c035543c08181300c072880405002d00b80103216100c8100330070100b544800340921a07500c00603000d180c0000c0001d05260090b0408241700c400a054000d150b448810041d407500c4200700200d1044517000080340c04c2e8940642664000e5800820002614446503108550003211040303090305030207002d0903e02d003d0024000b0707112203554200b25006c00d43c862904001101e510381c10442c811291030710203111585840082e0f4010703c800380d603124514032540300054201d006030624024000c3c03d003088200c1845105415008072031090310b42040590300c2d400b06984900041b200c090040c2d021456184041100e88181c003001a4080e100c2c0b0310680b5080c0052081e04d0101030260341a144203030a0001c40806000e40d642e5404c2d02da4400c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 395216384 1250 395215134 395215153
    0x60905070e04050703020a0c1b05191404110f0c070b0a2111090d0f0b0c0415020a0809040902010c020301020c01060f1502060708070519120b0a0f0b070807051b0f03 72
    0x282c15203406846c0a040304910074070341c65205602c01c42d40c00180200502050a1405010882a13201d01d5130291002007460cd4140c7d00580c100740c003c3c0e42082c1007940e5043d0602101205a09894001140e0414544101040042d0a01400000b40061251651940201080c0700d0f0319031400c10015161310f903d00d01d07250090021141d8481034403101c4404480725080b055681c2404100c01d82031440203130142c40041e090100000011005004485401900070500c40d0350a405030b13192005420050414481000000300781d04c1c15034001506544141000903100c011074001c682240c11441098059a54070081400120102c10303040d401442e07020181c450802221800940f2008054410800c3c00200c0e00820751031406201a2100600712050807000b51406101c014603240700c1075080b80700300e0714041c0300800d5170601100c4081600e81c118a861035203407030003032912100e40c410401074840d407206000340c44c0001c000703004480c108200c64081c0c0429070b0300c40003003011200079407501c0c034441e40c82100721 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 395217634 1250 395216384 395216387
    0x16090f1808090105070c090c0306140d0b150303040b13171603030503071413030c0911030f0702010212040b040507060807080a0c12240b0903070b0a03060905070e04050703020a 77
    0x842d462980d0a01c0c1880e201c10840c90000c60240c5650815140181007500c10000240d055000b98101c0ea4441c03543c000360721b140006d012000a407410080c0001030703c2400504921107002c44036984010140c100c1e49803564500030580c564002c0b20741c011105a074071a041100c1980e00321b102c0d4048000c40040c044d01c00820800901031402840010103114020001560302070007a1607034040e1500e00c0c8071495690f1448200c200c24141d40d408102d030490603403030000c180c490061080013100c880c000304003803454a50950a06445070020062030440d03408210b020502c039050314001e40251702c6006030314000e0815203041e80c1001c590b60001010002d2590820204591003400e0982000c9000c0c0005104100048202d56151004040548003420300e00c00070f015003041c02d03030000403c0721a440c2e03600440c1c82d0100c0da40030303101d40c00e06c0b0341d410b600c445000e10002030000001c2100442905000410b15642c1071204182ca400712052030116a2032100c0381c00c282460301469510085503c0c0c00c62400441040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 395218884 1250 395217634 395217637
    0x5010605160609030c021003090b0c03100b13051c051014060f010e10170a110913141504050f0403020d050703031d0c12061308030916090f1808 63
    0x801521450f11846200d05160055262101a540181c042e281688240700094041c1403007120441d00295404000b0783ca81d1104412340e07025004150000010515000c52541c1a40081c049402075205a4400064942e10031110315116240300020b82c0c034020041c1481c070700345034440d010605083d04100034100c0074603030004060b6000c5070440f00b4400a40e400c2c00102d9100c1d0101c1945600700c25044012070340c0e03d400c05400414460403000a403002c2d60b482d900d082c140c85000c090915002c005104801c44c3c1e29080406c24812815031000007030340d640060f10941c0002060750141c0201404c4115100f49003030600801e940071b0341c20440e000080c106a60025641e01001d8509401c02802049100405120307400030b10b003001503070301c070102c840c1000c049a0b03444d41590000c9902c00c030a840420320880c900490360303500c02e60700c4010710f0812181c0c5440b0304031140c1c001046179200c1d005102201200101c40d161032009002e800304009401080551280d0407182040c04d02103002c00c0382682800010310540 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 395220134 1250 395218884 395218927
    0x8070f08280f060b0409030e040b180424090f1e020a060f050c070f050319031706040e0f0606010e0406240201150b0a12060e07110c0402070c030605010605 68
    0x200b6035007840414240b500052070800880d50380f2034200304402051507801001d0481b099000ca404000e40e112000c100000002191400e00384888640005800300300d51001190391003031402e204011400448140c20100c902e5040100d80c5031507144072000500c0310154a8140390384540d40c0407082c0403840e80000d42510703824400c500401c0908400c50700310750b101c0d80c1544d4540f42250304449609443c2d00400742d9500050040380e010b4030503440c407411228240da1840000c190180c40340d000d000400c5c1c4011300c03009002010281c100f0b032260340006800404219101c401c140801c05404d09040c5000018004004244060b119a0030808103104845214190741603003106071141007450501410180d02610940c1c406001d0540a101c000070324161040003850740c6801940e8801444940c0603007181100d1003070041102034826207000032401406040f944030000810710417a82c100746a01c0c0094180d0740072440850b02d8500c07401c0104100200c0c0e00445003d00401e00308542000d4002c001c0002544004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 395221384 1250 395220134 395220143
    0x5060711040f1107050601080c04020a0f0f0c0b070e040b06090618130c0507030f050a0804080c010905120405360a09060207060e0d030c120e030408070f0828 69
    0x10380d0103100b01c04540d44440d1a04041403280b0351180298180961541e00c03d1181c842d8900494841800c5031a25101f00da1b0f01113842e48448040c1a4040012654100b0030240c85090120094004000c0303071101113000c0c0308880ca95680c03540040400240030076078401c003803448d0080710203004280d1203540d23410654510301390403681010f241060b0030000d2149440c05681403041454210680c1c0c50369482001410b040340a52030b0140012000c82040b10140300e0138010000258418003c00c1c000780001c0000c10070224850000324607040140c89480c01d046480320003001c0320600190400443c1031081c01400c485802850700189840d101504604080c040e144650480360f45200082154440350300074038103103030403040840d00e41045282c01c10044c00c000720321400a1240f0364415402c54403d025a09a21b45030b5511040f400c14221a0301c0c01401040e070015100380410b01002c20311440420820004142e400100c9150500c1d01900324200082100c009240c00b8001c05004072600000d0607210086900 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 395222634 1250 395221384 395221391
    0x311070623040b0705070e010608010f06050c100516090503010e0303221202010606080a0524030f060f160216050f0a09050a0609230a20040303050703090506071104 72
    0x111441c40600c156001024403400200303001041c00000a0030304c0c03c0d90034074010b00c10300e646c0341c110a40b0720013030900c40d14020741e4a200080c0509072103000504441c61260b42120001e050000702942900c2d003c840c440503a4400c01c03500410b0715440201180103040a0f0000c0154580b1018816103170305c001002c50070505031480014009420040c2d1901c14680c000c0003803407a00d207503490002c0c06400e030341c862a00028500d03004945d000c0043d2180c5800b40c1c100f01c1c0507880700045c00d00082d00d00300c4141003455250191300315800002c1c10a100079031141146218501191411a07030420004149409540c219400b003140a0f04035002c2000180c10f8980446640403039280300c4000444000003900b00003000d03410700d4240801d407403030b0350030000a9500d519000e01000c0a00c00c115080010030000f844e140200e2070003c0344508000e580b140783c401c030060400e80004a043c2c005c0f0304090b403059008030000f9000280d20b505066002104001a100c2240e4192414200f42c888a1214000c4074215110315035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 395223884 1250 395222634 395222687
    0x5060703020307061a0d05060a0c050a02030306090a06080307080304020301150602070e040609060c0c050c030c010e09091905031c0605060703030e01060e0c04050405060402090904171c0903110706 86
    0x124030004500c0e014006120f1706c032444241c98065101c4a09403050f8101c9410703c902440581d01403000c0d12000e0707046d0385c010340c11070744c0d0384040001490001d400014059034a110100795580148002c013180e90240d01101c0d52070419205250840f404030541c201f00d1202000103008c09640460b030302080700c7c02892041c09a0316039007842401000c1300344000301050315050b00d50704480c0d000f251500e0784d60b0141041e2012842041c0038107451340049054940000c1054410f1400c2c4e14101c03075941d41061001080301c48410101c0e5040c031007036403504016290b82d4000300da48078031100e40c90104110030110600c10700c8034a1410380400c40d54090309000805058603001040a4003100354403100c01040300141c81079003401c118a2200342a4003034002c5038000c44c200800070b50b440c1018000c80707203465405003040103544d03100d468008a080031100c05801100c010401000b40024011440c000b17200c0c0101c0000d410440f034034024029820190007500e10350131004040001c0358100c0000400400c0b880d0b0103149144 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 395225134 1250 395223884 395223911
    0x30f030b0306070f020c0d080a0c06180305090a090204030803010b0307050c070608070f03050603070b220b2701080a052205010507020c030a080919050d0501150506070302030706 78
    0xc151450540600c100700401c01d01c1c0c0d500080340510140c0c40e409484415220390140003110800c400c0190440c601005449800c5100e851602c00560055800084170700d50b80707038009002019070034250001100403401c81101e10b0010300c40d90007004140811481e01d072456941041d140014860952038160100014540070700407021075400404850543e10f45541341d500c06401020143da0010000f103500c003035070040c64042d102e403034090040140201140e070714040e00070043d5840952418960303103080c6541c04060000c082000040c200a0754502d40301c0a0807654101c0020f0b07000880500100652030702c40705643c0100c141500040200b0001c07405a075600c01b44001e60861440710344120b14003110399414444103600c1a03015000690a603500c41d1182000c040d03a404602c40080d01c80c51040202904524020f100d240e02605031041807c00150350384000b46500c803040c0070039101c99465000101c0e0a080307640c070301401303010102c40081c14008242c5000b0356900401300001c00c4140c0d5a6102084071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 395226384 1250 395225134 395225141
    0xb011b1b031e030206060a1d06060403140c030d03181502040b0c01020909090c18070924080c031e040204060801110c0601140d0b0601030e01060b0a090b04080604030f03 74
    0x858000309034560b64280682d00c06160001003500781c0c018050800401c5140c50700e08440c00440b00c00c41420b0011440142035081442c0010b41103c0e4401020070000000414020070001038120ba800501000d28582c01071504041124003050101494040201c8841d903065682c640c055800c4814821035103c22006040284140d8005a04450000c02c030301610f150150010414100207440c44801a103034800000e07950344a12081680c04081c005070344034a0381e40b48045070fa00c02040d18000c001d1a64031001d44801828002e07a00405104040014087e15003200e81030760800d140c1c8483c2851490401805941260b028140c5042e0607400c00100b015580c40f500144054000740000f00845043d207640d0310010f40c850b02ca5901720b40100c0d000020301d80740c1074a003c5003810001d401c106540003036550324a00d50000428131814503550381c0e0034003881c000034070800e00601880700c00540d55662070036028142044c0f652180e0030300d903070800c01440a030401103000c0e5003083d4141054809070a29800c190043c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 395227634 1250 395226384 395226389
    0xa0305150a081b0a080d081306060605190e0a05060c0a020a0902070b0c0306030c060d180501060807091b030509031611010f111c02150a0c030b011b1b 66
    0x160700404034140601060b6012200a80c507112003025a04000780401c0780740710710445806801100007a21840c1c065034002d41d010400386000205100ba960700c000454210b900001c0016101142003001104031103034842a03080c4a04008040c0e0341c84c1c0000480c1e1002600540d0f00554020490042d826401c0045a84103503001340044040c90f10380482c04003d41126005846900700d200202e140e882d64002124001c00002d00a000d100347d0100a2149583c0071540450940f0b60700c09040b402c0c4242940d940403102c1c03283c4000f00354103151410b2245040e0042d001074040c07a02e0004200c101e8031000840140c901300c02d050100e140e81d42c05c0c0f4218150701410b006041c1090811448804004d40840380315001c040c2620b8000b621481d000048034030411038030069809038481d006400000d403014509902030800347c41212101001142d0800140000fa02c0150780541c4498a40c00c255405000e0702c00d01000a1a02c3e80508485002600035400d030a40050b0142d5900c1c0980c5a480c4200c0400001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 395228884 1250 395227634 395227639
    0x609010203040801023708040807021507060b0301050a0c1704031e0e04060e010e13023021030c0d020f040305030304061a0a0e0606120f040b0109110a030515 69
    0x442e507503c05140d102d002c40d03802d80141c0c1540c015001b4160f5585a0050350990b10240c0e680000c540e4807969500242c1d07004a00c05d03070344085003010440300000c1002c001e204541c03080901094a80060b0289400c1d10000740015410074146005140744a0703010200e001e190000810580c85500c450a0603a80d8400c0010243c0e46a81540d800890040d040f6401815201054504101c0903580d01509146403000b0f02072004440b9000b008a44010507504286000600042c000c0e80305220400c030356aa64518266440b0425414000d1501d03031303113400d2045000d00d1042d2811184081d0350b4546001d07040c03200800403804c07550301003407030580318085030305886001d001d002840e80d0321512070600b07954076007088500b154441d0400742d0b410307034403443d00300c0c03890f940c200180c4040100750804903074107210310004044c607401445c24001d048041100100325070040138042c9002401d401c1034181040000703c142c001051460a1941e070380c1118081104543d0300c0241460001040e03210030b101c0c0016410b400109a5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 395230134 1250 395228884 395228887
    0x1f0c060f060803031902030f01120302122a060402011707030b03152202060405040902040209061306081608011202010219050607022b21050a0b090703051302060901020304080102 78
    0xe0b055900100650055040080d110b0400c610343d4a0712042e84422150b50095a107200010444507200340740da84a410b100340181e520b151040d402650036608416540c01c400a0b115200404807150141212030509005000c0c05c841d01d000c1d0000703818500700000700c040d0700034442d0020389881d12a9001403a080c800401782e0351810054107848180103000e40c0c00012014803490703007184d5058810100e01e0f4656016103018105072803c01000700803d03004005a800c20703000c11541c281c56450400800b0900018415201000e05000006008041c0140020320b80c4102000003440c00d41c200400710704541802c61401e5000b02d040c0f00403810040303140c031042c0410742101000c008000c0c01160b081e10540e115030840d00424440b18400500714240b40b5840448030b20482001d00c541c1c41030004070801100d0341c114521041c150380e03c4c88103c840072100018803590b912040c2e03c031890700014403078100283d454148a182801c1304011301040d80d00400070301c29800001c501c0c806900a100b50b0b0003e000d140000c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 395231384 1250 395230134 395230139
    0x1140307120b04020a0909030e10030608010f02041406040617040c050628051303111504090b0108181c110a03020a11030609060c0d0f1109040501051f0c060f06 70
    0x50101000a48040b44036190305c0d100810b85260178400d40000c0754055803252014040d550030302019080210301c060405d0b44407240400e03000800d0245c4c0d081424070f8040180d440346040101c2002c1018942054803880d420001003004580c44074050074201e0350454145484d071907a1034011040740d65a0f0020341c02642c0419800d0801c03403408080107002c0c8001c03c900084000d901750031141c510501c1120b5001a140b08004d2010907001c2c82d5512140c6006498100600c03482d080301e10594006910a10030701ba29030a01415550b0b008070a03640200c071294510401c030380f50764031964403814241020a2000c0042e460a17034058422202640126183c2c4180c0714581287d040080d210490400140c801d925400031100003400c00090032480b496041025081d00e80758032414040d40d610101c00d88000c0c81d1105480d02c242415480741c02500701420710b02d10394a003070241c03c1c4030954cd070590040388107011302c00b4410440f00d5260101c0201c1c00007454030701c20780480d500d030810050044070a008111803500e1000f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 395232634 1250 395231384 395231393
    0x1030207020a17070608011a03060f0307030b04050706020309010c121403010b071a070516050304090c03020a110a1e03090306110721020705010c06020d0f0c030c05040e0114030712 79
    0x91142c05000016a84c070162a60019545c2c03440c00c1c411070b41d040200c00c0031603440d110603901841d04903000900851a400364440040d1514120f0307001a54440c15071024041000f500b04400701c003c05c194000f03503040c800d500c000031308060000700d0301600c0000202407800c1900c4c03240c3e00b4103141201030b041864981d40c444412150b00c3d00207903021030700311609842441600c210110388030f20441c2281d44e040d1416160900007120503094000446042c03106100206e07a20301240a4141c54001507a801601d91500c0e4200401d6004003111113542500030144240c0813858040d06040d0004000000642c9000507260440e007070201a400034000910303003c49640c2a446450007020b00c44d000300d04040300c41c001c12040c411140340622041015a0103060304128650241c040e0008a0b40190001402c115898066406442e0000703600c0d00d003955203810201c2440d40611603100f1b1905a890054241800e014141c8800601030103035403094044040091785503a0704020884c00751081e89904c02d00d8803201e290 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 395233884 1250 395232634 395232659
    0x3020c06041b06020705060702060a09030f060f050c091516140610050109141323061017180109080d0204060e1002061306180f0c06050901090b0901030207020a 70
    0x8920940e03190080001483d60300c0010410240c0e10014441440c0c01599800c1126582c004c001034014070001003030000c0413070080500c000c0041d001d80000b00d0500140b031030342c0c811030380010010000114240021201c0e5280e00408401d10200f00c2c0085035201980901402d03402000200100b0960349102c0254821501092060050b4420307030444801a0701c13100196500c0b08280510b8107001c0003011a4050b0b0320b450301d03168100702201000003400410142031503c0b007084001c5207c9040344040240010741c10501300c680d611000b00d2500160400e803001c0344119045000c0c154040c0c014407101040076a00f42903100d011b440303a102c9150790307035500300394080c0019401500c5900c020401c401e64007165400c2c04001510302d03030042c0d40038140710354400c200c111500f192000141da146030b031068264100075941288040203800b9a00c0c441642186280c42441c600c482c1e08108104a002d0182c1e545690b0444405c1c0c0544444800c159122903800d80120028000c0b0b0380040c0d4070861082c00080d1040c1000b0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 395235134 1250 395233884 395233913
    0x9170a02030711032e140108010b0108060102190323040602161406040303180308040b04091503020901030b071809020903010b0102010506010516020f04090308180f0705060a03020c0604 81
    0x803c2c02203122010551584800182c80d01c94080009414240800c10301401c50100d074144e20000d844200d410811003261000d8001118503952448460003035a0842c005651109003403000307000c035a0a0007200800401c40b00c81c000d003440718001c1c00381d03071184541580d5010036061104054446964440c029680d40100040300010f200710030340450380d4824851512140c6001600061030545180d4084841c10081c924500a01c0c1034003001000046000c001000180361200c0349985503414222182c003214802c0000721000d00c41c4500420068aa03900c08504403900584100c01c01c1d500c0d0780080d07503140746401c02d07015400000300c0c01003000e982c2940035120903031059008220465002005a00300c55082c3d40f49400301e40d09104135812110700c10180e803581132010b4042c1d00002200d2010406aa91001040700440c8180041103015650400000c0601402a0081410b003d14074030302500c98100d405854010480007442c072080358020340480c0c00d03040c4040101d446078034240c2002c4020a4401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 395236384 1250 395235134 395235143
    0x213050103140d02030304030f110106030b01050a0b04031e14010509010501060e01170f0c2205011806050403080d09020d0c03050105010f06080c09011806031e02040e04020409170a020307 82
    0x12516201c0321440040c02c100c03030f1412a0000c1d85140c80d240ca042d1603d4103107003108410450b941120110080c001e0042d90000d61003000700403641d5040104201d2201e031a60080d215808042c00b04002194440c51242190301c8940040c040140d910b0071f294441c03a0701d0840021032982060244110208154880d40c101c0314a0365a503088190300034011034503c46840030f04803111904001150600f00d0003544c040d042080303200550718161301c4880da490ba0510080604030449043c01041140e5604850740c071008466065a0348080f604209000e043c500075800058280080460802e1844143e580300d41c282c19001049082d40c1c02031441d084c008281503000449140d400c0c0390000070000d8801c22440190345060700c1c0c600303659850940c1d803035041e0802994541000004100c60480070b01c1103108102515035a40c0c040791400450314005410a107000c200c0f108039204201c100514007003200d60740d0300140d044901044074809405c22400c0313200c3c1254100204980040c3c80d92203150004002d00300c080c8503 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 395237634 1250 395236384 395236403
    0xe0702010b040b030d031d0d1715010804060c09030605091c230c0703080a091a04141201060306051806010f08120d020d0c110c2215030213050103 64
    0x41c07605100c10388084948140d05a0710113420f40c02080e029170001c1c11a80b146012000c0c0e05403d0009240c03422541c6101c4501140c40c18001c00e82c2c03144440042c603889010726030840c0f80041c0341400240300340b800400240c42140e444025404052145654a0003140c000d4414441400c6c6140b5960f00c1c0c5481800000a0744c11841c0400b0503640074643c41c000613541c0058000d0400341c28048040c0c50781c40540010040c0c00396690200020320814080c0100072950f070744602c082401e24440b40012040b0010243e5000d0040c04100194010b28141400c440d0040c2c40701303081d4030f0100c2c003100c0c058102500700400c00380c02e107030400001d68107540c83c04c00350714140c0c0100d8940b6643d82101618189440c041d03040340c3c0c1c0103001607100c0c04034030f84000c0940c031900d0503005203040d004140c074008444c140325892000616952400e00503000030001840a208103c0b160800101440c0b040e10107500e110031195012912080c0241e5038058a90f0a1002581c000d00401007500d0544210300007002c0034001200e16008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 395238884 1250 395237634 395237651
    0x30204092109081b040f060303090f1e06052805130e010e07110a171207110d030b0105070204090614010b04060509060d060506120906090a0302070506031b03010e070201 74
    0x702d040740d01d044604200140c04101d403549400019414558505030300640c485d54440c1c810301b880c1c80345030001d42c001c0d55102001800c180900d05110040d41c46500342565000300c01c00c500490500b030700110f41a5007000e59480420000000e196407580800031005980c0b0110b15041a400038001c0075a0300c1e101070541c040756103414014107004000e000d50100d248071000050846409442482001030880c02240c201030318550358003005122030003210448610116035602c3c1c494501400300d410407694206814408070090300c4035500c0045d40101c00405885000b841d000345d00490855138207540240007802842520306145001e40000003c0616441e98140000f40e04282001540c05071003899450034a0311b40d40104010f142d4105030350f040d2a490b03032130300006603035903c0c80014174402c4941c0300010202e1412000140c201070004011074941d421510b514000213901142c041c0035030750220380b03190700c84c3c46e000d404030395040a4400e0015004000030000c0340249001540728858081035000b84900403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 395240134 1250 395238884 395238887
    0x10f0e01020a14070204110423010c020102060f04060608070609032612060a1d090c011107090f020912031e0708040302040902040912032c07031b0302040921 69
    0x31500740c0400004082c2104490000b082c040101300d0180000c1001c40d20450241e040300c01d9604c194440f00c1c00019103030000400c0c4461000c0000070030400d013058038010f503541c1c002035110f000003044e4110000402000408009290f4055405814000f044408442e1034200280c00c0c88000d00040e190528441c060010b42d01c9500c01e50350170004048100390501d02e40b44e1103015078460290020350300c0a404540450110800c0524402c2481e000d42500030604140c0c04050500030303071901b04e5041119800c100040044000342500c00c490121000040d080701c0300600070004d0044001060307200c00c2d40c0c02d0700c048414002020308801c00d080c0000d6001440c214206032981d11540704000c281c00c0f01848108090324156104421060014101142c030010329942c0c002c05803440480040030070780e03814603a41d0350004402c11107a5450a4550920820103004059948411351301c402084050064041c10b8801c480030b02240040d50b000c3c1c814411000c16141038032900f0300031646160a00c0702501c0300101c05 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 395241384 1250 395240134 395240137
    0xc0201021509011d07030c120602071e2604050d0c1d09070f060f1b0b1f17100e0f0d0503010e0609060a09050907030f08040302040c02060c0409200c010f0e0102 70
    0x141d07809894480d00928000a018423408002d800340c4006500b8010000801c0d0a48a0400d01c03841c1d000c81084010501d20b444c480704161074050960503180d0103445c41344456410101c1e0700396030003140c1a810710140352078034120500968010500b40c2840301c2c03580115800001d6000e00a1085400740c9030540e842d461030036460703511481000700085418103034506450103404890403941342c0d000d6815900000e43c40e8400c0301c5100703440c1100c030402c114000c0304260181c0e10000001c0c0c03490a01c400048007111021651311a000401e030f08030603581e00c2e815081014204902c0302e01010341c00c00e9800c1d410032800080c01c0d0780c00901c02c04c501e00740500c0003e00d2616041c8001c1e032061000511280c0d04a0038580d84a000b0800181140b24512604101102043d9880683d58600b0b03c00c1700501c0c0d07107034254814002601d22082403036081d503201e40d040c4011a0242c200b6a000d94501c5c40300040c5035a010ac94035001e20013000c04241c0740c8280003684601d00201904502c41240000d42d041c890300c14910140d900f02d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 395242634 1250 395241384 395241389
    0xe010c03112d04080615011d0a0308030a0b150a0801150c1416140a090c0801030f0201020312040b0615040803040308130305010c021f021206010c0201021509011d07 72
    0x8070742e04510784a0040d050001110b40620290a00c9007050f0300c8003100d600e03254003650a21264280321822425940c3e01242426004030030941010710146c0c000c0104140c5040d5001c010203800020000407800c200d20340c085600c4140040148000f03030425a20f030300c45507101e07103c6000007070003400002c1034072441c4032800b0240f61100d81d03c507a05421151641a0b402c060388484034200d002d070f5030310740c1e218050040100d00038201540b00003c0e250b1850040210900301d6500401c1040d00302050303020180c0e08a060941141e40004985c24410204d00c0101e0030341c4100145401c481035807000f840280000e07007107024850801071303543d1032121200d51000181406103100341a5182d2003004280002040d92001d0300b200035940200c048500c0d240d41c2e40a09550b0200b2480d001640128035007004019000c25000c078000040e80e045180c20801c0038002d20340c0c54000c05140c10710119061203811a40b0801000c2400000e24251108604080901601800000c02041d104110041104c3c1d038a51020980408 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 395243884 1250 395242634 395242657
    0x18211b080904180b1e0a051e011511010c050712020304051804120e0f01030906180f050610180b03030d0f05100b03090c040506060d020c030915180405060f040e010c0311 74
    0x12175580c2d0710617982c040e21009000c1440030f145d61007002d004c0d42d80256064040c0042d04000a283c0c21003800051a42210b81307045129a8100410305100a0b00320084a01d00b0303407ca0301c4801c2320f40b05518280d01d14803546e807020380c224a08011410740d14001d00c038024040d62040c046819581103d0302c04881481060003405d602c111012201d10b080d600940c04040d01904c14100440c412084980c110400d0080c0c0d03c05965490407081c1c8401001004d02899610880c800c0c0028460b0742000f0001071490141002ca03000300b6503508134000c0b079582c100103503041d034503490006022504005101a018090a4802800034082810046050303004102524803030700521008240c0d211034142000082d19018003125048003041007401565810b48c0010000300420500841d610308243c0c05200c2c425100c00a8034110000c213011121702d02200d01c6031075444c20780c00c4030080f03803607140c000c00034001c0f400f03079070170964801d01d4101108030308030701904106060710b142e4070100244038503009041698400c8009286 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 395245134 1250 395243884 395243941
    0x60906030213051c0803090a03082206020d060b0a091410050f0a11120c061302030604030f180311040609110301030f0f0618211b080904180b 62
    0x30314105a40c20b6154030494600ca0304e03484d200c0c0d0301d41100c40c0d4801e0f02c0c20403841d08122850414560010a4688c00440bc0300c802010107007074003504e6015100886c0000c1603290005204600d920040c0c1100018085400030940e0780c2814220150820b8158807070000c44018144030100340c4d113402240340300b080c240760301d48610341465281c1c440e400fa4084d040001c2404000240794624402c10481c4e0f10f0064242842e040d5602440d525841c541400141445071f1107058020400050318042051034005515080c003190480c80d46009440c01c01d0401900e41842d80040000401c0c402d040003084210581a1000c0005540780e08240080c1c803500070412110007410001000000d01000301035081c00d00414030804846115925003090310b46500c00c03031480c4001c80c030000c13042c0983e60f240c3d418001c09001c0d0001d052140d461002c0c0040c2c2e811050382d11607041080140d418012070004072185140d0042040000302c1c3c0b003260258a160803c0400d4452041c690b002580b10103000c540c1c20300002a105011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 395246384 1250 395245134 395245139
    0x143f0a060b0706020d020c120c100501030317090c09160e0a03050304060c050a0b0f0a0b0f2b0503040e010e0a090b130303090213020414060711010c050a0c060306060906030213 77
    0x40041c5d40250002080558204904071510070f003402240c0d60402c154040d00c1da14071181c1055807800c0700040600340c0b00340c500801000003907044400c140d4101440d8500c04404e80c0c580617410309080c0c808455039002101d80040201c848164000a8800d44464445c10300512442c13061015891460000801d08ea00410003409924080c07040303620141d2068049409600c01959894140e800c2503c4038005140b4030342c00c0c0040440f25001c0c0400040c1d05880d421016030340a00020010380341d103400700d4440d4460081c2c83c1d103491080400e110311103411800300d07551683d40e94200b2420b10b0003441408100a244404203600d08018020424440e0b04400364645131b4407400280e065100381004200c09056540c140d080040e1180c044101d00403030481c0c80140c40e2490011140d0381401e0400101d4440c1c0020410900021900082070710340000c04c2ca010608030995141c814500f0355039403c060200303042c00c0740000740b80703030326030494010b91b9155551030000c1aa51581501030380030742d8003d50890780008005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 395247634 1250 395246384 395246393
    0x402090601141608070b010914190605030604080d050709180506010c020d0f030206130b0c0c0102070b0a0b011223040215040b030402040506060901143f0a060b07 71
    0xc511030140040186282800030f0f44504040040100c040f54030f00400f1030407100f84418621242d0040640342010301000c01441c545110314400101000d414948012100e620070f40c00741c2c0a00003628000d000c07a0034508203800c0040142e040540e40c98005030a000014802a11a80d01c0e001180c8803c8151038501031400e00b034030060440103014604222031852010056580d404d1100780c040e010340100c5094030903034100242030900c010302182000b03c403070b2401c60028075448020780c0e204001e4020346403598400c00c0b12501920030090050440c00c844000d10925840070f5000401009090b218103801c03141c0205040d041e580003040100440e000301480604200b8800c0f07107160300c648000c101040d80345030340000340400d801079040030703c841d50040200030840c06c1c1441600c1c1c008900b1a500c42c1031103495000240801c4034441c642c001c4c4400840d0306060391003c034411002800c08200a40c900400516042d245000828041d0080717038000f9010910268903880340600395000d075102d491804038140ca5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 395248884 1250 395247634 395247647
    0xf04060b030a0939090c05070b04050a14061005010804030e0f12010203100503010b06090916170705120604090b0601050a0210050c130e0603190f060507020f0d080402090601 76
    0x103558445034805051031002e00303001c845004501d00711003c10189100c07110300c0551300032600054a01031500030342e000b540d40c01200744c6095503800305164020b0713036407803a000e414415402d000800380c0b000300e5052400303030101107400c43c403c103003c40a032440b00c0c1e42d072001180c812000ba0b501901280e021000e55219003000781904a000c040606a8070400344070340c02e103c0c00c99100721070b820358000142006000d80c2c42c0a015243c01420111003075801e00500d080017401417040039040200b411000855034245a00a4107000001e181580d226800c80c6030295001c0d1060f0702001c001c1c007150350780800113003803440d040c0300d80140c1c0c0d60010740f052072980c0d42a0040d1210741c0004010000c0d0b106203601e0380070b100d40b10b006c0d0070710902c4038203c02c5032070302000c500d010a5052242c000400c050480400c0005c0340c0c030001844501005102110400a12036090021048014680240c1414200740800011903000695506031410040884031215550341c0c046802c2c6800f9a8029404140100400c400c1d40c45140c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 395250134 1250 395248884 395248901
    0x215040b0403022d0106080303011d0603120406020312010611070501110307020406120b100308090409020d12021e030906030105090709080a0b091612150608010f020403020f04060b030a 81
    0x4495400e0381c8558810f12060428807401342200c070000450104207001e02811000342005802541154105410510b003000c0c9070310132808010b4200002040c0b82d4040000b54240003004074415030342c0d912040c0003034986d071007000303c090407804401c000101c0b40c1c0305141741100e101982000d014030500300001103600010b000c41004d981c3c841400b44502503566441248018809900b000303210650b40d01e0064040c81d802032006001d130b8000941000403d80020403034110a404440000c0e14504a1000883c0c090f140d01c0041d00500c0e212810444883d00005c26405599140d1102002d00b01851803465032031060b00342c07643c0c101c0018001080641001d0040940001e001d0070845910b41d240c060403841c0c0080c03001c05071041c284040901c82040300c140003034172002064181107001d007406d100c148580d281c0c070024028039824542e19605410ba203d9407240025140036030007442040b000300c0d00d00010350403600090b071242c210813108100302d1529114460848011600481c215644e0300002401020883c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 395251384 1250 395250134 395250137
    0xc021507030e06071511040f0e09010c0c0f0605070207090e030c1e03090402160501020a02030a0e0f010c1101021501061211070b180102070203030d0903030f09020a091e060605190215040b0403 84
    0x40c000446e041c405c02034008e001d40503202c4000424070b0303c65947c50958128046481c144090504e00d81c0108845009412040e038000c0720106458a50040172880c00c1c006a10190810745030080e00801391030080002c00071440b201c012201150440303403801c2d1200404c2c01740058103500030009280c6070304103a0040c2800000b14200d091140703e13075444181c01da81c0103902001c0140c200107615607041c0d420081400160704103546010700910b603140041c0407001c103d032001d03020040c0094114907030781c801c002400180c0e900c0004420656503800000d0050302d03581c41400605414840c01c0c003280c00349030059403c200c5c1c000141c010251203101310105440000b082901d40c9540030021800961410401490801c00c0b0041c0000c1e0700c0243c2c1402012550b2000300540f4607405d101540003d40e444503840301c19110741010008040c000c00544101101503810140c080c03509203040021400d400c6405400101c5030603804002d8a1205071007240c03070700d810f8001c0071030508087c400710300882d04092115038454840e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 395252634 1250 395251384 395251387
    0x90f15041b0e130501080a020d0809130507020d05130605090a121203061707030809120610030c0602030a0225050301090f020a17060604020702010c021507030e06071511 74
    0x10801d601e032241c1074101c08240464070600b0314945034249115141007107449440300b0042c9504250000c1d03124126a0380180c03140c0e2080d5042c01c1440415021252641001000300c025560b14030000000b411044400d1030141c000c0c110480c41080c098800c403110044210b0411503080d041000c1910340d81c00c6400342607085043e5034404504100b6030100442c0b0740e406508610b4010385841c400405948240d040321402d034510700440c965141c400100301c01074a611591490300d42c0302c000040380800302220b15004880c400d0b00300340558420f0005d0300e0002c1d00d00a10785090a51340b107400030380e500d2180c0010303078005a0202c00100130340240c500f114940d008010b82c24046880d601d41c0000d081d03410091050724121003040c003120852400d00c1c00c2c07800800d001d4007126052031800b1411380c3c54000082c960b80c0290b07000100301046a100721143c1600f264018460b080c3c81d041c01d07112400c590001c2404a011924a442507030142c0350450548103a19030000080d1100c00110b840c4801404980b407030148180b00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 395253884 1250 395252634 395252651
    0x50903060f06030105010501050405010c1709061c1a090c0a0207090c03020d0e210c0c03060403020318030712140c0916120902090c030709030611030114090f1504 71
    0x40500036280036051400380003485040ca28105400c55806900c0241800401c00c002c02c440e0344c10424244529030480403408500c0941c01d2124414450141001c0d800000041c00071880c0d012407040700080d5114140800071507070078400c06c10030541d80340c4000341d0000d040c50010392000c041000500250f40c00c1c4c41610b410f03c1d960320101e41038136030105007003020940100d4540020f03581442164101f5945c2401007201480f11541544106015050114041000250507910010401c062680c003034021f41200e40c545014140251240c100101104c441d44c883c183c0f1100c50710b400640581980d10503071005046c00c40681d0f405c01c40c01f0b1000380b83e9403103001d08504e040301952900b86140c800d113607007032401c0300324902d4003001001d01320203404180c14140703043e2928000da110420000d902c100740005007035480c1c84054066542040b40d90000f00070310b0908161a40c0009440051130403540c5100c01c00400040300410020b000c1d104941c405420025000024044008002042032005014100252444 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 395255134 1250 395253884 395253889
    0x8030c03130503210601090b09061602100f120915050402040e0105040c0504060b0c030301060c0f0507030f1a0f0705031b0d06170607020307020607020a0e10060e03031305100509 78
    0x2080f404540c0480c0220704401c04c050b155070b41d181c0754803030000d180504042e401d0040500e0103004101c9900e00030080880d041525010b44060440e21a40080902032143c5030104006c00c90905011004005240c000310543c001a05000321480640c0c400d04143d40d0f034100d44485401000010001d85e84542c980c411988019001c0c494940218000c0c22800480c1c1c1c2820b090101b601c0a070303482403c6034002084001d4100e0004000c0c1ea06448561400c141e030080c0b02d00f000c03607100788a00c20107445030050310000810000c404081e00c64041c80740d8403215014882c03d011850242d4100e50640310504010000f8426910540041d9840741d0740e034ac1c5041d0301500c149280360f1203422131240000d11554611041c00303065080c422a200c201c0c01c0500401c3c0c607250080d4001d48900171244001e01865000c030700b00d400c55540341e03c03020240001d90002980e500e00074071001c03107008c43c44c8603a4000c104205541071050602104690243c500d6041c0742514507d42010307c412000c8100d020020480180101d44560307 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 395256384 1250 395255134 395255137
    0x15030507050d0c0e010806010207120f030c05100504050714031e070f081e0a0c062f01020a0f0801050a0323010509070f050a0e0f07030b030f0307150908030c03130503 73
    0x3c03096841c1c43c61484202c0014001103806005d5034103541c00313100208004424000030042c4184d01500b25a180d0071a40740a44101c540702070000c2c020f00680401d07200300d100d554052803040d80039500300c444040c1d44140540d080035001d40101d0b0190000341d0752080076034440031404207802038002103072192603980074814400d4116800801ca0303500001203501c40c0751603402c4980f0144040c9030107404200740270b41d10007102d42418070070a410300410580c20f000c0651200f100d858180d210100c1c010b8a4203920918038000c0d8020038030900414050781200142910840d8040e05a500c089d060700145421600c40c5400320002d1452210001c00c3d00002c0715044c1028000d01d0300070401c0c0002014000d040c4904c0e48448666600311301d0181c60b01c50002c114540100a02a400090b42d188c6038105460703980003140038280b045070303c940511481030341e0064088000002c010f0b490042c0285c01c2e9480c050b9404000303488006201800518060022800102c4120b0041d03401503d021030800600029036101400c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 395257634 1250 395256384 395256401
    0x8090a02030615011106060102071505040f0303170906070905060f0705010237140a03180b09010b09040c15051204120815030a110d02043315030507050d 67
    0x41112020189203e56000308031140c030300c542c100c00342c1039515000000035922600c0d40f003050030203251640100328440c0200c040710081c1a07030051070601a81c9a0030090a0102600e00c81f2440b10b1480c400210207070008150640a415160b4810b0000c1c2d00c2d240804c8507a80004802450010003040103c0000348244020034800d41c0720001c1c0c214544443c0d40200e842600c4841c6034107134540051000000790741c0242d800040c1ca000c8038243c0d803035030200b030340840044c038200d195080030018422404d000d10502d5404a0b11401c0018024000001080305200350310f00309541c0148441034280c01404400e440b059101c00300c040038681641042242c490004035003005403002d6070b00c40040480c1d230302c56550140e8885ea005602c1140c03c3d401404103000300c1e03a120040c013005043d001000840c01a5607651812260750b05400400511405600040040c0c1c0e0300010607402c0843c44100c50f051900500d2810001d044962840d2041518071031070b9000d401400c8001c011004010341001751500714a00e52191098 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 395258884 1250 395257634 395257651
    0x150203070c1e0819111804061d0a0f0606141c17041502010b0402090f090613110c011823070b040303170705131a121e070f0f08090a020306 61
    0xc103030a2414005c02c0710030181c3c9414012050301e071440156001c50340516030051b520000008040c0903817042042101c5841e0310f495510b00070441c001040c000c442c3e1602090324007c0c4020060319030790300801180c0c100e5045542c1c0d084a1500d80f0b46052003040458958500d000b2002d00340011504512603da5500c280c020a004030700803201308940359030900c01d0380c82510041d2411440c240c07100340060344151071440c0042c4102c1066000075555251100d07a200c4480c01000c0c244a4035680b511a001740e40c1043d44005070541c64401d030b81815980400f4a0b010301900302504401c001e60202d0004842c1001a01071100741c860345000040240d2060001c00040d8040e684400d80030000250500800002508040820000b8000e00340d99007a8824a6811168665403010841c032002c000825503019035614000024000c008000381c800c148145603142040c101a4550941d0b00c8840c25211607a0525228001511602c2d001326000d005913802600082c10104644002c05180c1c0041d1400c541128a40d2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 395260134 1250 395258884 395258923
    0xb2e0303021204051f11061e160e060a09030b0a02071a100603020d110403050606120102270d060606020f0d020102040e0c030711031201150203070c1e08 67
    0x81815410b010209800641101d014603061a040015000c09250b0409060605060090000d49030003000301240c4810f180341603404615180d580314051a180654001d240400c203c0010380d09111510b16052030785e61030b2210309490264409102258108040d804180541d6200c08404030704a40805886094620b8002d0380e1010300740b8010405a0844c008070000920b50400d00c8030340445071070382800391685898010303201e40d15036000c2405031840940040005200080200500c50040343c00ca1149600360380005085840c48081d500700d00c580900700a2901001d940703401c1000c00d4035504608150f000300029030101640d2035050845210385d1200000d80e0055150001d03908090028046501550001310b0074039181c0b2944d02000c1c5402000100042d200100240c0002d00404c0c6c8825104611001c6035101c2d80c0c82000c00801c0c003400e000e080c021644500d01c4412052000040343e18a1b60721000d0092190b181010100000c1c02c0060ae0035402c0f03894100c00314540c801044114988464140440c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 395261384 1250 395260134 395260139
    0x10305060a0c020d080109020a021501120203010b01020316060507030f020c0c0301060b041a0903010e1e07050a050d060506010302090607030221040819030509041a04050a0501060c0b2e 81
    0x280485010142d101d06540000040c00ba1054001e085541194140d5401695858001808a0074240300302503612003003807001c00100c0d05a00111090003580c0c030a900810614600f03600580e943d000b10303c806010070360703005003c4d00064641d80000f03801039840d090100361120301017041410ba07040310f81700140541c000c006824107031809018610080003023100701440d003030400ba0030a15564400728001003251000840784901c0e10254002c1111004040c19038408215804224240c091016054001449130507030100b25450031580402c00c58100418841c3d410360150345100c050840280f040c0c4c1410390a11846c4620303110307800100703d4603100390f02030010340041ba1342401345411100d28a0403540c0e806c0c4014040c0840c0000c0403000f2003a25042201960007910b000c0350300b0722600044981181c10324401c6c0503160310540a581030b50f082102c041c0000d650b41b0002ca011078409105d400d0008400c9401d590201e28102d60700c1d5040800c014440fa200720b21041c070001010031003409840a080542000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 395262634 1250 395261384 395261401
    0x1109060a1d04020405061b0a0c0806100504110711030c060c03070b16020c01140d230601110601150519020703050d182c0a0b031506030304060c08040b0301030506 71
    0x500700c2141c08a6007141001d0070b00c1c012500d640161803e400242e8140349a581c281201003005c003000743e510003007011400343c59404e46034039008196100001d08802100108580c500740c0505034154130b98450705414881940c4800d1103002e000d01a850701030166015600b801d8489800a241411f05500116aa8180b5280c00c806200340144600100c00c0030341c0c100036525501245031a500d45007460034101d044600001c0c2c0340d00d440740001d05200546030001c0c0c0302940110340c41c0c6e10300800e40341c0700343c40e0140c0d070306030064500c44450310b07404503160066030050201d6a04441c00440f01c0c0d8042c0b6249081001c145428085031005a00c00e03005039018a00c2082004000c00c48200d910620b85049081d00c0300034170655031484500c0c0a4643c075400600c0b004c0080c0100900ea1030010907502180b03280c0350410000100007040450306980c002e0107001c80da00e00300900c820320f031030041c0e001a00842c07501d85810012940c0c448510b0301154101c40030003002030308500040165000c1d50103000941013600b8004403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 395263884 1250 395262634 395262677
    0x3011b1202030c120c1207020c091302091602011509062d060f0c020301090f0b130c140d02030303010609060921021306090608030d0501090b131109060a 67
    0x200d41403007801001008815203244058646155030160020604d0711114614038180c09070315041c0c1881c0800c2c60410011076400201c280061400359a43e524544800780391889040080a002c4c0d0851810350100d19110400700e2407507000303083d03840000360028801188461030724566001e4410755071118000d1000000d000c0203c4610100a40400481c0848084007030a8402c28070440c0c0500c59407107240c052a1340190b20b403c502550080081004048070710302600058542141a00c40405500000b00940d00c05845044290b4100e8042c2d003405103403511011051240c162801c0e04014540780c10320060700c00304041c0d40070341070716100c500d45d40c0d090440090141c02246c0c4844c03465a4040300c02d06140c000304d008058420303010380d81149403124450b030800140c01d00d13501c19000c05141c8900000c01138408009800d120303001074402d2001c7c2e41e8840103034040d58020403c05610000d442051091100d0945c445200e0354259100c41d8201f081107000115175401c020782e80c0d0042090328003104c54060700c125 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 395265134 1250 395263884 395263907
    0x110706020f120a09030605040c050904060903030605040209011209020303040801022701090b041e0b0c0706020114060f1c0501050703060314060c1803160603020714120f071103011b 79
    0x340b02c54208003000c0401031500d0034510001d4003c40d0f458020905001c080361000c405807001400c0102c440c10140303071a0000300080ca00c142c1c00030349024000b081600c0c09008907044444165524800d0195901030300006010403001240c2c903210400000410344001e0001c1d01e481240607510000d03803400951001e80001111400300d0412003440814414101103106030b400b520203450400caa600381c0200c05420059040c0c11003003030314401081800803a40d0000d00d11061310703082d0f4024440c41c2c4000b4041407100d40250303143c40d400801c078903c820250401020304903864010850040e08000346480d401e003100d000303803854000244c96417014018006440d206000c1210ba900040410386003022491540340618140c22180080000800000d07540400090884248905102c1380c1c0aa40e0301000d0000e5102040c100c4031640021000403c11001054a000d44480101075610b000881e122020040d03100070003c640080180350b110f17010b51002d1213101e144207003078050140c688052542c042d00078560714 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 395266384 1250 395265134 395265163
    0x1513081002030907080304051302030c07060e010507030c0311090108070c080304050a020109150e093102310228020607020f010629070510200403051b01110706020f 72
    0x801c01004549c6484031524040303065000e0061300c0c0d40f00c1d8540300340580300b014009060207091101e10007003810103500c618025181510104000c1402200907029602440406e05c410441803001032101d50150070540da005402d1f240c0002343c2c01c0d00c2d0380c40c10038a0300181d42c10b603016407103c800d402c11960020b40101c00f401c44040705000c805018900105081010b016640c02181003601082e072000400281c0d40d01c01c1c65104202e030f481d03115648400d0588600510aa116200044c920001c19420886046032000307010b1040c184002c1c2040008060b40c0446041c55800360260f00500d0440781c15080000100820740c0682a1400e104c40003e20380901c81065240c240d1401004100e010020302d445a945001c6003041c0003480b0300e1594024480c0105d0708054501e0040200661481d01554000c0c010103d40800c1d03004402c020056410141c0240d001c0209664040f08035894541e0144100324001c0302d05140910b4a03130403071400b05041c6801a07000c440913038481407480c08200d00600084d25240c404 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 395267634 1250 395266384 395266387
    0x5030607110606011404050307090e010b10050a0e18070c060b101d040f0c051c0c05040306090204060302130902030114070e0d0614010308090112060515130810020309070803 76
    0x1428150342c548402900702d50511001d80e00030882110660181ca00034000107050ba018183e40301e200101820500c0414441940380c0094401307186032004c07000800005d640d540d1800c100d4401c5007030341d420340c041c1d840c1ea502c00c4001d070f0b001410722241011a8481c082c50381c1c07541d00741d01c000e00d04082900c0c0407011091203100d00b013903000d503910b500501f140300108010034164081540703032000c180103201070104440d2407402d103040320103655046801001d03444502c80c244e200101000c0642e40407078080c0c043c2e000000e030302084200045030b400d801801d40c850000740005041541d981c001001441ca840006003455100c01c032203005e601d020b120700c00d03901d440d80303090240c0c1e031401001c0200403080d0f0410300c0740b080303100d0070020082c000c0c1580045172600540c01d04007031658403400c10050340d40140300501d0018819400240500410340103250031544060111103003071580602075149608000454009142c1d00d000c0054500800c12600d4898100c402005035203041007030000d4100000d0340c2280c4090b500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 395268884 1250 395267634 395267657
    0x218100306081902040f0203010311030607020303070203030a0c030b030a030e0f061911031303210201020c0709110f0409020301050301050f0919021c030f0e1009030602070c0f080705030607 83
    0x81000f81c1840030030102e540c440b5141c3d1000400a1244541c2407006074070100010041100c0c240e1030741d01060044003101d40c2d036916900d00f05d9070307031000715403240040c4c00500204061a040303411248824100b0305010541c00007d1000c680b6102081c80281c00080d421070004005080007034000da010351054400514225081c1100e01a6100b441c05810820840c0310300d1083c110310030300c20750b800f0141c01c01d00c5640c0d0581d6800c100030740402055051600048900fa010300d5240144210b078460b010240c0504821031a01c8803a400074481c120403840800d004000081500c16100000c2020f840b51480042c2c4a5040000745030031509c000303007091320b80c5003200c050041d84a4002070301e2086014012000001c006c181c03001c2580094109030000881d500011030004254000480300c05112242c2e0f47c0c5018400840c0401280490040e40c0e10080351901c4014030119003282c009249060080c140c1203101556030f20400c3c44e180382c550183c46950020361040c0034600d814401d29810411914045030203c0f07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 395270134 1250 395268884 395268899
    0xa0b09011703180d120201090308070f0e222a02060624090a080a021002011e0f0e120d0c08010605160c1701060311060c070312020106090218100306 65
    0x3194050401046281d44000c0c00f45980d2059440c908640c0404204d414040450000e03010b80341100e42240890903100c00524140e06c1003e082880c0012540c409002190040a01c8505034001c144103821881c7c44e080b81a158110b406542c88950f041032030a200c480c00000c0115407001d400d405803003150080014442c040c3d850404001d5400351036840b0500304440041902014402d480e001a008410520000780068011600f000d0030382c000d0301c0c82421025442400c80c2203882c1300c0341f09204d070459001300c0c15000003241d020205122001c0f40c005078049604002610702006c030320035031a8446000a0541c1171580501030b9407010181400c10100369410650080c0003030240d030800307003000d00020106030280020581c00078002c008944000300a041e00c02e804c20301070021800260391650041072812110305055040700e2140008001402045096645240340780500100d0b490456480d8400883d050301d907440200082100480f500421001e92020722140d0b2031800554000e0529051040001a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 395271384 1250 395270134 395270137
    0x708010615050c030403020409031d040606050f070201020c04050408040303020d02011a0d08070c17010c0e1e0d1a04120305090c060307140c030d1808120414060a0b09011703 76
    0x50032030900030f403264900141d840c81d50143d54401b030350041c2408510001c2c140c002c9417455992414200b02d403004905201840b0a6030407601c40d40d070018804000008038611114068034101d44141b051b510b2142841c0e00103026100c0c25202610508800601001015010030104005c00c4190000303000d0700c3c600c506141041b0100441a50181c03080b00321b020701b00714040c0c0851b40c01d00d61041c06880000d4940c24000000512a250845e031036103021440606180143c2c9141034000c0000c010240c407400405400c0410082d00381c0140d0031401941034600002d4081030500c2891008141c01d0280d0b26042c11700e0f01c01c42070480140e500b40361904042c410410b101040107030081c041500d095a42c1e4440e10411034070311300c4500010745038500201d50702c9140031000c0000c03c40505044000d2040c0000800c080b84024064200141000401c001502c10303c455104200d40c0280151f0703c90000000225074075040c0038007202ca06000654802080e04640f910100d44e0340074218a001d14140350340070716601c0380c1d207 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 395272634 1250 395271384 395271419
    0x1b0312060904210309080a120606020c090105040905011803030b1e030a0f080c0706030b150f04030f0303020405090f061806060406050d020408070e01030b0f10030f030228020307080106 81
    0x1440c408641410ba03004e03800203500140d0201c2c42c96650032682100038910003502c01d4550300e076410010005085880024042e00801c40205040d0450b46000100002401c00380c3d0103c8203952a0810101400c1c0858190380c041c0380241c50204060310003504004102c0b0500142180d0003080c40e426102035240060f500940952221007000ca0f42c039541803004440c000c0200d4500350344102480410800c1d4141c10036044603800351100e00c0406c001d00000880b038060066411010700c4240310030004107a03e81040080a80a41001454140c030380b4046000074000703c640e600780703030380120a00010b400c041e50050b4524a520b007003200c49041800004a90344502d22a20081040104214410440365070443c0c000740060022104615920003141c80d00a1091205861000c403c1000480e00e07281104124030410140b04540091400c6540300e1180b12040312054045125500044a400c140c2d00380321011301c420001c40084002e142c0c0304140c50050950481c1d08541d05000040103c500250507210740c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 395273884 1250 395272634 395272673
    0x405010f1203180b0405090f13022404030b04020f0a0305100f0e030406020d02072310030906150f081f0e3a0507030914061b0312060904 60
    0x30000c5030030111454190600c081403020f41510001070301d040394038010700c212002611400401d540342c410300240c02000321141c0d80d0036003141c841d0100518150550441c94510800804444800d9038408816034000360022155000b030704c424441075203850103008035442c80031250f502503c0e065943e0103441d8a8170450484811361500c001c03140e443c8503030308003d079076400c0501160f031a203946981c0203603035a050342ea5070740240c01146004615000c1e5400d900b008454521003403810351a086007402810071004a651080580c4c88064500090f0345000d01228239200701007844090f41421a2100d40800c2a4444401a4403200780c101c0c400c0c6208000315040e0401020000e0081c16420030603041011038004072461040841c01b8807844e000405040c618110a40b07403413080304150a906549520584a024011940c2d031041001401c042e580050200c1d840600703d030741400d101b4010000044080d0040c00c003180c101042d1039011040001c0700c1c552054086401403054103168030760241e0342200341032044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 395275134 1250 395273884 395273909
    0x7020f06090409020909030a08010e04030806130209030f0a02010f0c0b01092c0105010e0c04063905010e0118020a09200406020c030c01021b06030603100e1b0405010f 73
    0x1c09035030340d540100000f81d000741081002d46440804141c0740e030b101e0040600030681000002c05c902540c842ea845c42154103440383c5406444e10820090700340d103000355601c202502042041d0702500e0501020300d10400b000001c2040c0030151001610201890b15001d0410201466480c0410a0780c00a80d0440d426107038001906003450604050400301c0700c0d91441c1100d01c00240350205241540401c0c129464251445400d880c1c2c00a0300760544101c0c1f14007800130b43c045607004100801d5010001c658a03100448100361103400144100a10b200f15068446954402e45071503680d0003170048401c65030847c0095501c0300555400074445000b01c0c0503500000e65a400c60403582d0301000d0290004008216101c1d03121541d6083c02940d4170000f01007107000307006240c40b00c0b105500004155152100c800d110701103001c13408040c02042d4000601096043c85000b1802c81e000c00c07a44644c4d507020060300060042e01841240032440400c0c003241060155182c01c004102e803100c0d003a1b03008166200001d030070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 395276384 1250 395275134 395275147
    0x60f0c080708040506120103110114180d0b07030c0e0405062818091103010b1e0a03121814090109050a0906050f15041b0804051f05040606080307020f06 67
    0x1d070b0a0081d5044a6040500011599202182500d80e1030480344141030f041603041c0c5850044500c02c02c8441e1000594000344101c0104550212000c15201301c090400448403455484881c0101b03025904103021940e134440c0b0f141c100354001c000f0041c58070255428015800d10304c011582186001400c00b40c510b28200707113004154000480f080062941958180c0c2c424071a01d1018001c0c0101c440c01c90b5111183c070301d4041d46081c180545407a0340b40042c504401c10b440340303000f00b01711442e204440d988500303004008800207103441c02240c501449642d40341c100d41c106950036a10707000c142d04480e01580203011400d034150343d40b0b070980f41034030002c00c030100b500d44510860070060100c090009151506200800170820003000d01c0b5440340c4402030301155940d41790307000d020486542c8a84180c0d282c61080c5401805409222065003040c8610100c0b100107840c5200da400040f046541030112980360003e11044c03150074010701028252143c055442c8c40c0c00e070b60001e1005031710040414007070280851078 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 395277634 1250 395276384 395276393
    0x16060302091003060312050c030f032419090b01030908130603051015050a111b10031e18080304121206060e191e261018020a0e10060f0c0807 62
    0x5a42da0409061b0a050f00e90411005500074034135054990000e55070b1211455030f4034904400cdc00344480c00d500401001b500d0800081c00d0203880310301a1349040c540c030382c4089000a0070030401040015403645203030100701e084c8407004003655070281250009500c1c2e00000d000c1507008a8090884400905029694403502175007541c080c10807602240c0a401a44003061052100030540e41c043c080844034048800074010054040310007004004081c0e00c2c2003408112a80d80542c4440001c0b000120050385000076565008002d500488003290745414080d94040041d410036130004070384850607000e00c505810300100403d4000001051842801140d110399610110508407102401e01d0b92000e078018002100540c8400300703175110b07440c504150b000c00314201d541c0410912189401c000d0142290480d00400100a00410300388a6410746c6608421801aa17402044400a1074692500c4c10340f460400340600c4011525405942844841c4405c140c0e15036001c40060403082c0c0c050301d0f081d16400706040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 395278884 1250 395277634 395277637
    0x4051810050d050d18061d04020f04031a06040c0c0210091e06020c0a0e071409031b19080c1504030c0f05130204080a0b0916060302091003060312050c03 67
    0x1e940200e0000d054070306101c404104200007038100e0315a4002c008420b04102c031070300864442c000c009010844241056010b00840700078003140100007608024040304c0901e1594025807049440b48030b074412031b586600b9071408056006104450401000b44a14009000440804e400a00c22002820035410541c000d0300702d08050304c0800201b10b078011407884400750516407405060090f20500103014500d16056610f031090720782e03404104021340c6848200340e0385030400d0b00c054091903009100201003620704101c0030911510322600c00c140d4a0441c01031098046652080c0002d0703c0741e84000344a030300c5000030300702d021103000d64180070f5042520030030201600407034100404103080050005018038511800000307a4078100e50880d1a4048030050314101c4c8920f00c94481a41c00404080006c1440f03820704503807240d10142a00c040400050040c0080180ca400502c01329034003042e422441d04007140303030034242d022505003003000908507114407458074080001601080000662202480350510 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 395280134 1250 395278884 395278889
    0x604020d0f260310080a0f060b031f060905060d050a12030902030f010605090c0304200f06031f090b06040e040602070c030f06050a02030f060d0c050a03060905060105010504051810 79
    0xe000540b1105041000c80960300640d22034401c40107000001c80c448101060301009140d00030424261000365a90b5200949401c18015505001d41c10700d0082440100b130700c0c07048466032520002040e5003440c00c1c1a048450181c00b140c002d1001000718000151b0003e403100c412604050110260205148200d01604861600a4040c000d0207030001c0d00030015003055060303038000c031040a0380d07a851081d01e00407400200c6010f8078240766582000c88005100c000e01c140341e200030b40000c1e902989140072840d1a81b040c3c400e401c20034126103001c80349844003480e01c000303088801014032440e5200000244c8034000d07402b0b102c140c0c000710804242000301d507504646603039502002c100d009658a041c40402c1c2c1c02c0e0110300f40c0300c0c582460006500b290152086034840e41c2c800385a64180e881d100203000318240451170483c0c0141c4002e80201d040c0d1358099030f5600552117520b000ca0006458a085800d01d01d060b0b01150501c02c00b03000505c80c0b90340d02124041d02c0040840300060560f290100c0c103c00a281d0b0703 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 395281384 1250 395280134 395280173
    0xe031006080a1e05070e09030d0e060a0c05040617061807090e0709030c1401180b09120d09030b1504020d050601030e0715050a11160806090604020d0f 66
    0x200c001500d000702040c80201a801401620800440e00c400015260700e80080184650800042400310000c08081550002c509004507030030915010220000c8600f40380340c8000c241d0100e0f0400094420600074181460341501d00f00b403d05242c03280241c039140802d048045800c25030000203c3d10f44a00f0203c0d0500b14071072134200d1403410007010150000360603020307020700820001c2c00070b640280100030400803243c2c40799a0007000d0b850701c84000405d90000443c20f040191880d940b440c2c080c0103c1d030381d00c068141400394079a41d1480300b00f000031045031070143e10401e400c4100c1580005400c4400d000c11250044119520b90380c5515060324403012400c0b401d0740c01440401c00321416100c035408030740300b1442a2020040404102c5400c0c1e0f03624414400c0c4880e02c01c1c03105600c218240710b40c2c01303040c2400c41d900302000e01c41ca4420b0703030038142030400101114100e0204030170018840c00f080301541000c10340000d4041d070300702900400c01c2c043d2500c07400307003d66610044881c00c0200c641d20100241041c07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 395282634 1250 395281384 395281391
    0x90301090c18090206090d080c0601030326090706110f030307020a03030614150a0c1a0402031e121b01050f0a0506040b0d02131d07060f030b01020d0e0310 68
    0x2a45010280281a8000c0d80307801c8076000d04100d51680c2d14418000e8880d001808203040c00c0800e410803454040407070703040780da000307060084020510b010003a29002e0341c400e40780d10142403c802c80c5281d12496001c0200720b190b02079070030711102200c0801c103902030703078035924040c500c081396401c09a140030030f18034008038a840b00104002d401c40c0c2c0030611756061031080d98107202c065516400036044188010543d94407012070240c40700c0c0708107482e00816a020103400e148900c4030458440580360043c1300d00b00c80c4060100c400f04001c61800344007018606031280d0b1001d040e0a182900705503036246c001e20250b04d0f00700018640b00e450118502d81410205060001d1240b450900d2002c65031150690358034004600b401c002c201c00780707014007800d242e10001803c18891403c041d000c00c07250014029160307500035030b200102c200071030710902d007400000d1303074800103100b41454844014030480c2014010307410107191107600304403680c0c0880c0c40100c4010924040040702409030000b0304111018811000061a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 395283884 1250 395282634 395282651
    0x90705030a1803022d010e03030a0f0c0801060f18081c02012304080705060f0f0703150b0309070f0909030221040b07051c092301021b06090301 63
    0x90000045118020548041c46644404661400ca40d190a81c00401582080e204c00030b0700350f075030381814207450801055802c100c0c0690705d1180c01c407000941d14118907000002008001c80c034a00400080c10900e1a003046041a2003800405562044c05400104109894488144c51040c203e51585400a641c2c0d062800da5681c806030740c8120441401c001c4448401d807a40704c960062203800140c0f071608214000307241015155101500c0014001c8440c03003030074000400032510811480b4881d500b0340d00203980d28144170340d02c04000300005255004060a00c0c1c109080204a9040b41007152264190141c0300d0b15814841c3d4141249500102c030922042c82c0001994001034000144081c025001c2e180810300c020901c1c8024240241d050500c0c40701008200701c0a0170543c01002007600503030680355a0010b060044821050002c2d0f00c0b8001805200b041c4000341e50005496164014800c0c58000d09200000107900d4921406d00501c1c612211b0001c0707660750710b52104640580c54010002c02c488603 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 395285134 1250 395283884 395283887
    0x11b0801080c030f03090103020a09080f0606010914030a0809061209161d0c0703020703060c05030a061d06090901061214120304030207140d080309010e0f121e090907 73
    0x140034460055075114101610510f42004030340d201d248000d800140d45090020001580a075202c0c42a4504000604d000058903003000d2061904c0042c88a010f401e0604202c8001468000325400c8101010b003288204034041c1c2d00000c040c10f00a80c00445140c40e10404030000b102402410100d0301e20a1628042100980d804030f60041003496050220410584404002d2602d4000301e68180c00c4564400200390307680c225402400b0864442d01c11152015120794480040c6d95241c2c010001243d03000c8248803598089004200c0039100c01020712901d00d0030200c0c05035a50b940505054010407004000c144d03d03d07020741211001e00020f00814514001900d170061020941d0000b44203075001700c058841c121080d2104807801560960300429002d820080c610360131180304c00d0503990017984010840002008034018510829140e8000110341c020000c40d139003050010390141140350000f0214120b002d400c1015a62050028104003c3c03030140301400c0c85031441900c899541c0a00070300c04000315103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 395286384 1250 395285134 395285147
    0xc0a0b010503060a021e090409120309020a1406121f06020309030106212409030c0b0a020307140c0307240c020a030903030815040f02070b0c040311060c011b 69
    0xd45041c2c0031241640d80c0d001e0310b14128007a0b03003010810201095440b000340c560b110701800562030020400205209107a5a0201c3c0c01030909106021079280d1010505501d040c0038280014100c82d0700801c280540100012841d2080e0001e0300c0008110700c02040c110b801940b5100300d000c80c40400500381c280c8a84000c1d580e40c01c04141c140c030179800c0c032101050b0703000c00740555242461114804480008161382e22070700e0200082c042e062461902150184c8520980501c2910343d0203070712940002601c07800c0c8008440001002240001d00400134001080e40c4107031492026403ca507011903d540b45204518103504c40e014014181c02d281e620700e05070441c4080c1c10421600d00022040102222104040e600c070070f421907000e00411031866042010070302509600c1d511025a080058140b0074810029080707038240d130280d00b022a4041025020400c1d003800283e0000801c4004034202403560f41c460b4003061b100003500d802594041690204a4000d4001080000040c90846002c15500780c00a01c2d6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 395287634 1250 395286384 395286389
    0x40f0506070c1b060509010f030209031f0507090b0306100e0d110a15050304030c03020a0b01091d1914100f091709090726090c090c0c031207050c0a0b01 67
    0x501284115107880300e03a0803c11a2020340b959801d0094600c015280300440d0303103002c003e16408100d0904660b03800c1c41900010940c4403540c0304845010310914049800013018001800260341003408000380352800d0366403000c8101e542c1e94000e100780004030b80350100020010b07044403d05d02035104105c0885002d5220f000107407210041190f45121425400001c0d10703010020480410220740445e01c102c40015099009004543d410355095903142c0d03850509031700107080e56980354070003a2080140022580708c82c44490041980707600c900f4074515040c20350034004200b903c100c015808030100500c10741a80c201c86800c03c02900780c101e00f0480c040c2071889001c40d44030501243c0140442240c400340c0e819201c000c0e084001a07035900405490300c041100042e2a0140507a480c1d1540c1e49210b65031a12036051a8003070300501c10403100f4488102405032000340304c0001400f01e0340940100205507100140d90b00c80c102c0258940c0f440a031180d00c20007244070b030507016420345c072000c0c8071546403030710304 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 395288884 1250 395287634 395287643
    0xa111006050f101d0402190f080108010c081602070b040f240804061d100b03060f0408030a02090604030204110c100216030507060e0724030203100e040f0506070c 71
    0x8100710745204004080788080c1e1050049113001c201445801c0c1d0707441c403800d004200070300300524001340000c41d43c081d1006542c482c000541c00c01d01d1920240e0340030703d0a03401811500300900c102410a00045c0a881e8020301950481806214113030841d8402c02c030000003880d020500613981e07600c44c48151108030b41401403909a1824049490301004026006844150346a07107401680d102d594880c40640b541c2200100149180c00d1800030080040c40000781803085000000b480300044802d042c20100020920690b655840040001150030b03d02141e0b0f010704503040040e51272101c2800941c15000325000a0340092400403006540022a070080ca0030100c601c040310990045800e84a05070b01c0360124080e04405640c800d400003034090030140038818444d805c0840c04102c0c90b0a50b92500140341c1c09098800b084580003071100d540c0140b905d0304544145000c0d451441c2c81074511425041b02c0c80340c0c940d10451007000500780520023140c1761166502200b61032050074055001060025062815034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 395290134 1250 395288884 395288899
    0x50109021512091c0507053301120b04030f090e0f0411030a0201050d0e031b07030308090d0903030c03020f0a060501090b0a180c12140423120a11100605 67
    0x398149800207a107180d1310007240000740c0000c0c10180840780c541001d0011184d40c8102e1101071346400700b00d1440d80c0d0420104001030b000310041c4408001c5100b06a00084044202d400080085109910110750181d0907052520b601019480100c0b100c2c840f41d40240420381c403600500c41d225003202801c0d4095809010032030050801c1030101501d0710032444000380400d00800c1110805000c2c1e4109038082c0c0e41103401d903170401d1040c1c3d905100410700142d45400a4011490910400d40c1140c00c49070000810f10041480700f13008100608001c20500015051081d556441400c140c0300700101d084e0b103100d2000356401803405281c010060300b002e000f418034a5041401070b0920307040003102c0c0000c544a6101000340070b040110042e0080c203600e8403400800a84030003107110300e070150180d000d440d10000b04281c01d600e0b0030700f000d00c2400c08440d404010001c08100400c1c60b100c2c002209138580c1c904004803607a07a02000c1007520752022500a45072280290028425407403170a91004040310429036680 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 395291384 1250 395290134 395290141
    0xa050106090c091706010e100e0405010c030c020313090914030a020a0201080105100206042d0812010603020414040f0209040c0201051503010e031b0102070f0605040c0f08070b0304050109021512 85
    0x40c00d80c0900c1e491343c040d40d0117407004100541031030355650f1300464010540d4505c1d980351810300c0c032012811201034a540c1c0d11285401c2089905110710120340189102071410103070703004061103181c8928880c481e0400d440b94428820301c05000d0480c80c0c0d100301c90007243d0382c81000c010040d407180d0409c90706901154240e4000500e5007400101455144215409803d45a0316a0341780302000840c004030350b81d10622110040c0b48031240300e08243c2d0041c0078030080b13902c4007d09042c651024905800010405005000412613414004820308000808880104600d5030441c1078400a026020900303034014101404031100d2601940068020040c40101075200c1001e01c0626090300c058600c1080154800c204551085500b10707070103d20340401000244c540140c40d1550181785122075000e0f5a81031303403001070004200d0b00c0c00c0c13028024094810b9001449245c43c0c082e5442d51707142d106040c4001c1c000030000707040001c291320001ca1140c0c000c0c0320b0505e072034100c0000b20040c0c00551200c15502c1881010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 395292634 1250 395291384 395291399
    0x311100212040c0906080c300708010e031e0715020f09040e03070b0f18060a06050108130503030105040c0306090e030408060a18021507120206060414010e0c07050a050106090c09 78
    0x6000c10780e184c600041a8442c40f034028800c060081d0b0f2215010500c482d5000c10030340314800c12305100c10a0440003041983e05206800d03084900810403428107500070003a4160144200b001001000b400b400c071280c03030304d10b42d042c001040c0345640300851550348001584582c180445000d060840302c2030b0781c1044000560504290780e4418904040c107900f0040e80082c1910030070000300703035000c80445007940c0c14001c40040310303181c1007007550107a1744130723072a188103101659115140a5002d01d210404508004054a40039180e00c81070280300d02450301d401c11031046074081d0b0088001000014401c1200910401440d40c80390050301980c00705008903c00302c1e0862610f070183e6140b418281c0c440c0000c602d82c85d8200b128660010103000b824800a01080010903044034007240f40d01c035990090305080c0b9100c020041159480605044043d000d403006105840d5844e90003540110400000c0744c0e00d04050401c64500820348800601641c00c02901241d0001039400462a5031202d46401c2c06403900c5118 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 395293884 1250 395292634 395292641
    0x1060b040e01150203070501020a020705100f0f05090f060c060405010b060708030105011209051014010501020307050c090406110f071a070f080a0b1002160b04050109030311100212040c09 82
    0x1881c204803100000500c9082d500b0318811200c0b2201e801201d141c048a541c843d401e9030416401c400158105403010000c508080f80300c8840000313175161101400740c26480107041c0c0010528100c00700100070542c03a046459140415005010040003291a040e1f0000b003184e440208441c03c840d15404c00300e45011b5030401034117685105500071034607030035a800c1500441e08441c80301416a4815207400078107011860030310036403103401800040450710403a4a80b60000e00030060384418110b40c000c210031404074a020030300200120085580c1036680e2a40c1c10f02d03030094201c4042803941200001600c0d52088003120042604510403180741e800c00843c602d03099410344003202c202020500038200d505407103125030b40c00b5a000c410080001036108050b0301041c9107030b188a0011015901820044036901c00c04144840106900c648051806040200080c240e20040c44010148050000d811030001814030880456803e010300031501c42c0e051104075818500c00365010b649013a108080170504020500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 395295134 1250 395293884 395293889
    0x140f040620030925060807090b0403080c0c0303031003060b0f04050702160f0f050d0f050609030a080a0e1f0e100605040b04050c03060618090c0703021e0a121e02070801060b04 77
    0x2c0040700400d01c0e010301a1b4070344100500c410708120400324081154840780c0c0103800950700a9840d0b54a500381000580d00d0042d407001030034406e600600030801c10380700b081c0411080c0c0303038003500100f40d0002c1940810608078486510383d07882400c02003080407081d400580c0c03420ba601d01444580c590b0350b449a582d105201c1a00450041040f5080103006504000210b80e003428407030001c2056143c03982e1a2903041c52800c0d11403400c5074100140c426030840e031100e025034118481003403c0008044d020140b0f03a84c5d0b060350402c04901c0001c01158500440c00f42d214a100d42d00b142c055521880300011090020241800b4031481580b800000f070030b850401d881854410398a0162075460b58403440100441c40e0000044e0002d4448040a140d5207901d603195028000d103c0b19000c10384501d000e15000e41821100070300050f0700407034603400d240716800000f00c0c0701c0090380184202207003110400d070494000d0034400c11112440034844100840c964002000c03400c451501c2c00802881c1d4aa00e40b40040c1d11071403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 395296384 1250 395295134 395295193
    0xe0f0f06091209010903080a021006062f0706080403050d09111c150b19080109230604060c1b050a050709060e16050c0a0b040c0504140f0406200309 65
    0x15201b4000030ba110390042c400c18141d4011603072100c03400c2c031942c4c0c02c0c1d0380181c20080010390350030760407010211010f1000174a040c0118440803c480b90a00b840c0e0fa0f00c007e885004108904070001c9400c0c507008030100c5102c441900e405004407161802d12007130383d0f80c0d4620524001d002101e240d01c010020040c0e8a202254040d182c0380c18000e00080d85c0d005482d04080d81540680200c441e500e80680f040d00040080c8038900000c03030b40314000d007010007080c000c03a0354a00300310b001c41540900e041008600544c0c000d500010010384110b005d8811140356a40d050791204000070400d03918103111000610203503503072107882140e440300c1e00d45000500781d170b03420f10542c0d41000100e0302140300644038289003c0741780b400d8070340581403860300c40b152407508483c02010354080315003a041c44203101454074008040c20095070103020104401d00440143c0a0041c50032500070030340804a010440280c1101d40014002d814280310604443c45844a42c0e0094034010303c81d100c5c400201c02e0420502800c40240710a1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 395297634 1250 395296384 395296397
    0xf17071505090a030f050903030d0b030f070503030706090c09380a1404020c070e010303090801020310060509031507180f05211c0c0201020c0d02130e0f0f0609120901 73
    0xc980d0284c03005c0940750f48503028002c003441603500a17202000035100100c0c0c19840400d52130b01400905041c0a0005450a21170f000a001449243c600104603050b142d80404001100500c0e801c0450400c80b240c4c000801090805d130100440b02c003c5445258207204c07440408a01d0000e0f4000512448a50070003190070a618810800403030b10b1a1100041d1520041c101628103103184054a090030801e801143c503c003031000041c424107610074501d0380641495002185181080f62010003413400c1c41c880c020030040b0009401c0402d85043c0841350121044a107071008908008501520b0540f100c14030503885041c0b0fa40004512207000c2c85101100c1e8040c10285564003503500b0410040a5400c05803100d11030751300e28031031102d00c100c0c4d80d42030400c090741d850049044034070009080c03c0d04041d01340d210300e15101d5500c01681e100f590840703510600d2040003da45054403d1182003100120080d0181e008803002c00740c6401020880b07500c5108000240c5c0e980788401d10002c86140100103610303000495 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 395298884 1250 395297634 395297653
    0x150c0b06040908130807170601060509100e0405150414010506040302040216051603021011060610020705031203010f121703040c0e101707060203160f1707150509 71
    0x1c081d03201155690040d60501c0c60903e0051a040c00748010380d210b90055481030108001c85c4561407644915150b180029000d55450040c0040c81030052502c4a84503021241520540f140200c00c401c2800304081c0c424002e92902504030310000e01d642030024040c1e42048201e040604880d09080d061724001040075040c24190b0302400001d4001c140d504140c01d00e40003160340814000c212a44406414481ca40e081d03a09501c1841b01c90910403d11038140403071400c44020408003c21904c2d4441c0095070b190905141c1130380124a400340943c469034040c06103490300140b5504280c0114180e03110712078220140d03035480704a41400b0150b8940908140c1440c2403540300d6007200d8004582160140501c8140c480d11615a120400c006641d450954003040000b002040c40034041c0740c3c0301100768070240440d18036000d400380d12486a0b1180090301c0f003c1403201c80c1005030210b101c034204d0343c02c032409100d00c00001200e490281d01c1204103984802c0360923290f4030f41d100e0714010144520303182c1c00a06070250 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 395300134 1250 395298884 395298889
    0x90621091b080309031002160f080a030b040524130606091401081b090607020414090d110c0103050a110304050307050f0c0f061c0c17061008011707090204030c150c0b06 74
    0x10442040780d2423803035040c0039400c0411003c544580c5c086001d4441d0340d940301409100030b41204c7d22031140d64011820302c010805c0c1150380405180c0c90b150044d1540c0881e0201500140414a84e04030605c14a89844008100300d5803001004007681c500f1003003108010315560065800d0701d005c07141b00b2030f100000202241d465144501038442e24002600c03082c2040c0003507000a05554001c4a10034581070f89a0070000c02d0f082c100001c1248403494109230401c03904180300c15403280801449a41810b40329000f00d41402a80c0d4000c910352001c9855940d04d03070416150103900d07030b844030304181c420313101d1190411180c107004105400c0800c0001c0c06403c40115400c04d0002c0c0c2d1b045281a0342e441c01039224a511400d003a4010111490784541c0d45c0510560030718104c050f4402c0107440b150050380340303101031008a504901000c0c10340b1550304035131420240d156041890a0b0858110650300790001c1400010040714019900c140c662820080003280c480f00c0e0101c07003070b140c0440003404021400c4c022075922f0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 395301384 1250 395300134 395300137
    0x60d0b130204080705060c011509231501140c0f0f0d0305090a0311010b041a100305010b120628090506061303110d02040212010504050115090621091b080309031002 72
    0xc0d07c410001140f41c5640c92400c01240301e07260312410400e6102d00c0c440440c025881e1400c8120084001d8501103814400c046549006110494a050102d1f681ca04407800180006a0300031100c490304440c05640410075558880043c0154014030780b0030000c1c0d02001900a00030300344210407410041a0700c1e40d2b03a4034100c07007008451400352020356a83c80d02060589650140c170507502100745034011103100f62402d000042c4440e40c2d40008061500c401840351003407000031607915901c0440c0078052911202c00041c2e4004284210443e1800484078035600c03203095083c0707c0c0c11149006030030000c568030712061084510484000c0080942c0c0f8410038030000b8940a48480f0303209018152160407511a40890100d0b40909036121a003201007004100525290085a0141c08940d10103070310510fa090014201c0d882502440041c4000c071810180309035501e5080340c0d0204400d20303080c00004c20606280c10303078000021041e00300c84d82c1800c0104402d040001120004c00001d0000c1030482952141100203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 395302634 1250 395301384 395301397
    0x403081513020c0703020a120f0f082808071103031602070b1c0b01030b010819020d1a0f03030a0f050309010f020406020f060f1b18060d0b13020408070506 68
    0x10a0100504202010071440075040c040042c100a0021034214010043c21410540c410000f11039030304080000130715425001c00684c3e80c42054400364030064600030707040b40100700540e140d4046114004d240804403020103042c448158480807104c0e103525504440d0300d184c1003440000d940c401c00100c3c00540035940c4580071020319106650516450340000c242c5584584910740c000f030700c02081866401c00c58420340c45007010034201080a140080000307448814000c0c03c3c03101c1d280c01440b0f100204101501118081825601c04205400c01d140c224400c5070a00e04000b4040c55603000300d480113080c000226130315003080d03454080001202d814111007503170000780300010554845c4200c0c02c0300c6035280081c0020b060b49801030880301098048003031400000901420545840b80c00b130000001c030200070400a2761503804000c4d46c03002800a042c0100b8501c072101c507008170000695020304411903101401030130044030b42e00f12181e2050301d828107030b005030300a641c01a041000100850319080005103070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 395303884 1250 395302634 395302639
    0x708040317070c0303053703050f0702060c390f010b060d02090a18050103170a05091c0c0b1c02120708060319082a070504150816170604030815 63
    0x39031046030050461281d40c00c10610307c4040050041c210b015018001e0710361015824203008001d01c0e144000950302d01c0c2c040e00c50071448000003141080b003c4032400c030044804403c660061492413002000041c2030101082c2980d0b80030742041c41210f6107060041450070500103202c2c80c14081c010702c0d1140298401d4007280e6009090120004800c00148901070a40c451a1b000044c0741d851424100e01c90800415403001124080003800612600301084c1e40d041ca005581c0c42c901c0c1c2c1904156440045c6a8400c00f42007002900c200180680e034039001000300e0b42c2528a5407444819021001c41030340902e5840c00d420204a000141190303100d030411a5110340010122040e5810003423088104ca442c0c40f5083e1000d4600140283d0f14946280204070007058004451050503c0d001465860710b40c03038001d140c801c60715000d507000c5020f68408003c016200310341c00d80310b44040c0200100c0c10001c0038401c44030f60034550310004407042c8000c03604a11603a05900d480003182d4885061454180030500b5499 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 395305134 1250 395303884 395303917
    0xd111905031009021206070507080706110c010f11090105070209071e0509010e010e060d050a150b0405030705120718110d05070206062202030603120708040317070c030305 75
    0x5440e903081103480380740c5082c0d200016828071240180450804070a4018540d984000148603007164400100d400c0383c2e4002480360748405051400e4000b403c040c07403038403218900c00318030104e00507019070000c0100c0b0b007002e0301044415000d5040031030358007034201c3c00740c04100248610005802e0000070107500880c1894242400400d035800384921510000c20a00000c50100c0d081030b040d6049030b0111303204402424078002403210040050340521491400c000e9203600e500100d805000e4580004105400060186003041d0307c0c0d9648001d00c2d003103440745034031078415002c2c000303142c1c2440244003a40c8000301c1302500381d5500380b40c2c0341a8040d244040b0a004165680c00c441c950340ca412011300030341c60050f070010920b82020380d8000d25183d4003800751841440c144854a04a00c121807844441c1132120754050313140d40e640c400003420305090041050200b900042c58100300021003000b032040d28425107603240042041c400c03c0301c0e90b005001c402010401002800e1020a00950250654030421201b0340d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 395306384 1250 395305134 395305139
    0x2030901050d1503140f0604021c030c0b07121802100f050d051602011b1d0f0904030305100609051305180706020708240c0a090801020406090609050d1119 68
    0x3404000c40310391081d5808800c45c03001d40c2905e00c050261441002e81040100040e052580006181005602903c00749424010880c02014041d809c208405a08800444202e180a01c000b50484295481803040146000d01c00030301954039024021505402030100c40c294581c81d407080e544001070503c8402031040512100580780942e018280c85003040d10b01d8401903e0840c800a420765904c43d0001c6850010820203111242c0d1041c0f02582e1192408643c800004080000c140360412000a450b04541c402c0c082005041e0140c200902400760700c42242507099541008507100007090180c20340c403150040c80aa2450003030781003075400c2230300c5400401000340c02851981c5480c0b0181c1c80031015030080d100c04c011103442072141c0c000e4100520400480000b02c14410640e9400061032120080c00102c0d8071355205200da80c041026014140c0219507807a15841d018002c1203071841400001284581d0218007401c148850890f1660320040d01443d4003100410071081d401001881001741070380c440c00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 395307634 1250 395306384 395306411
    0xc050706050a09090c050a09090b0f04020901050c01050a0203150109080d051c0e060403021006140d080c070f03021906120533090901090506010e130605040506180c0102030901050d 79
    0x11171000441e1a01e40320f0351000c9905000d403501d59160f00c00558645400c80c02e00c81601e403440400c1d01074400b2180180d48520040050b80c0750301588613840700540c41c01c010001a081507600540c01100c0780040811949080f0300110342240c5140120b482c1c0e5040710f800c20f6190307070041000e0305040000b56044884c481c1c031464254100e03001c03d09030768030ba03034000000d0009254041c84807540c50865032609124280c00c01000c601c0b1260140c485034012042c181d441002c1c44200c2e010b4030600002103055808080c0d417103040058901e070710b000c1030348106002c41003509082ca17103900680485803e6101c0740441784462036040000c01008103c13140005280441d80c01d25000c3d0a04d0519044c010303456024016a02d505219108000402e4005660703d03050542c2c0100d200002d0990440f0160f1800049607651100d0104180c8846540103050300c0c00c081c280402c0200118101c1d03c141e030600d00c0d0b00f07016411491181d075222030840003d0301503001001141e043d075200310010301d4402d11034940401c0c2c140710f40c2d54 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 395308884 1250 395307634 395307641
    0xc0d0216121805010f021b03120c1006090b0d3002010c020105010803180d060209090c03060f04050121051f0b03070b0c0d030f0b0909100605010c050706050a0909 71
    0x20032800215407881000b00c40c0510615000640300038a8000405040c2a401075501d6045200c200500f400400c200d41c620380c1e007081002c50f00e0307500f074400c140c032003c0c10100710303645224031001c18510908066012550710701c90311526080740c40081045280d5001501c917040c000c0303600d1807003024112910071010b40c190419401c1800001459000103103004080100a0841d0740682000c401a00208900c0a80000f91f082a0095800840d4000e104400c0c5207045170003449030850054210f211002001003403c000ca010f54494002519917001c90364010040200b240c000f40501c60b0000c4484081549243c006e0695042452203102101da0a4029940d01d02c42800e41c484012542c80d25149086250708007800408000c3c520204200c0c200700010040c65203401c06180d95808050361440482040401c581005800308400740c0b201b68241451109142c603100d0921258110300d050150000e0f02d944112101c446144d0840c0141c0003003802c00004031a40c0e400110a60304001000d800030619180a11 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 395310134 1250 395308884 395308913
    0x809040e060108011805060a0b190905011d16050903010e070305010608160602120a030f141b07020108150d0b01080303071416061e0c030209030f0102030c0d0216 71
    0x401c101e62400150300d094400c1d0030b0858a80e0074403030311a600082c0d0005002c41c0c01141580003c01ca4000200c0411032100b8401c9101600030403c0800045c0d83c01d03150b02c180d05031440346580d81042c100c0040b0544401c4001d8911012240344100d00e4850030307200d00003801c0100e40c024004a00c40c007400c95030518200841c0c1040d100c40e55649010400e0b038004000d0403100700c0022002035845803a03d400030b510307600c8810000038082000102050014403950103a80560b911407400c00400c44000e5200403d54001c84440c0c20300c062000c1a15074011104040d1209554141d580350203580d0ba140c02c0c031400403540c01c90680c012001c0c41c4940001102000c4c0180038110a07001192030b45020342000745904240c6020411420042001c01c111200b110318034144950490b00200d203000302001810b00c0c400807545030240007403804500c03000765581a0003c100055040301101c585801088d2014203e11041c1c1d000c149400c130800c0004001300c959000f03000c41149020314076441c04400d450740d986c0ca14020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 395311384 1250 395310134 395310161
    0x70305064605040c0f020709050c040e011e0501030b06040303031a09090f06070c0f0206210901020706060e010e012303030f090405071e031a0a0305010605120312060409080904 77
    0x18a003403006040611030081309400a240540f24000c1e0501d0280d1030380c0d41e60103880d0b130858a031800a0401800401220001c00d075075500303901150b94610024402c1c4014150b10560342f2201c10b0002610341c441c0c0240600355100030641443c8c80e1840d64150028200d001145600c00c0080d01445aa540c403840c0b940e00c60090078001c0d1054501d10f072100303030070440300038650800c0c0250f10100300d01080e818182d1252a0b907056886c5590707504000b00c1100070800704c003a4003054402000070001440c0703041d000f80203018400c0e8001c0c0440380d29130010611b80303502400f5403100c45a070500100281401c041c0b060200c000403141c41e8113017410304004a8115404142034481d440310000740441c25003454440c41c0d074407060524110f48503200c00e4035100310316102c44403041c2c201a207440304613035841d00d100b428400703800f030050110050580c0d80c500310b8080d188510070a4460000d0813507456030620044103c4602821020801c484c41c3d440d013041200800003007a058440e07450910002000b83c07510700c6401c5804149 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 395312634 1250 395311384 395311519
    0x60507050709050405150c22050109060309200114070c050108010503010506030a110303131d1008071814070903140a020d080307031503060e0607030506 67
    0x1400c140d8602080703980050a81c500d0b0500300404910b01040c00601c840c0a4a2000c00765210000100194042c0e441083d51060710342e041e01070400b10b201c001e6811281c0c00e0f201c0084072036880f5802d90840303400d11005030690510603400d00a42d00c2242c0c00084050741410325000820030504000d0361a000300b001221504100c4009201c03540e00090301c1750040804030020b02c06c610344000070035152007094500814040d480040c0c051107650500948829400c0700342c0d01c441041e034030141c0e8804070070b040d0000b901141d00d04000c50500718202030007005850640300102641c40c0b40902d4050001e000080c50300440f42d6940c2c81010000d0a00100c50103034445581c0d1030b90041c11801c0000303cdd040d0180502c060303980070080c800016147c000180407038540169801b5165562098154042d01443e100020480070200b0044204903559000044040d400380441d000399440e2982501201e03010784510740d101c1503036041d4a03803c01003d03220106c8003440280400d1584260000240c4c119000380459050111 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 395313884 1250 395312634 395312647
    0x5090312010e1f1508220303061503090507140102121204140607020d030e12040b07121b0b0702100219020f010c0806060c0f100504060b090106120b040e01060605 71
    0x5509510200d1060394034442c49094540100980e00c80b00a5402d0401d1001c4400080c6d5094010344d502110104140c200304440070081c0b400500900290041d81040907402101c51b0149220f441003901c0d0387d81c0607006004c0d160400316501c506880406032241144242c810401032450417401501c4d000d00f200700c200c1d0072401d05141160040c1d204004035811588120104000c459001800d460361140318280002c45140f080c0405003416030000110b021010300003800a031400010000b80070242c080d02c0481e0006248000480300096000203115505a40d0720a40011401c1d0421403038009090340100c0e090381042d8440c12007640c00c040342802c042c2e05250400f02025170144072100710001e811008200041c2d5214024000c82e074003410503401100c01045400d824202040500c405d50705501c00c0300c501101d10101000502001c807400c4450030308011480700c403410809040d40c140d81541c2c03070f20111807240244500003840300c000650340c010b840341c14182250400f0700ca628050400c9a13034203a40c40d0b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 395315134 1250 395313884 395313901
    0x207060606031d1222210314090a0902091c0c170613290a020415051801030c02120d090303050c030112060b0607022701060212030a05090312010e 64
    0x1c1c3c09601c4a20503802c40d04101031902581c1c022100d00303d1061080721016803c420f0080c401030601d812107101a20f0301c01c16008864071040004841c13910035507411040c0c0600c0c80001c41d090103061640d5410650801d42070018080f0307070300904040384001d40020007581381d4098014440c8078501c015120480c0c0e44a050010f1811240700c280b0070071601009250303e0406520912a030040e001005e000aa11102c81c0c1079240a40c1c04075081e0100707228011149420300c658000e0080d40035125500681c08941032a00106010714159002e83c01c0e8103c0d130f540380041050064019000c500105030450203038901610000700104090900100160f00004218a4a203405012503e010300740411804042c00100854052445501c07038481d4040d60124080d050007011075284c1c040d0b80002076004010b030110040501c5000c0e2029000321000c030342c00c600d40c1d99400040e46c0754600524004050041040064510b0a80317800107500314030a101124079190a00341402c2c0180300c2030300a2405d02c50164140101c21 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 395316384 1250 395315134 395315171
    0x1031b11060c12130201090816150305360118050c0306010e13052a04061406040306110904140103060c090501052209020d0c02010518150901020706060603 68
    0x4890b0b200784500c1c050150201d40c04046004281503000755911960404591240000700300501d0312004a400002c84458400c6441c5520b000d00400d002c0103418607194a4441e000b02801902040300c20184c6214403601220800902600d00800007041007000c2a001c3c024070070151f00024981d801c559500242c64500e080040303c0e0303401072003a03000c60014040c080d1407480042d000315002e2051100f00940345000340c10850403108070652034186440044161000310366490180204031001c008454903404640e0354440e1880c1c09a42016092105200159059008800c1c14110000840c00d001b54040000c043d03030b614014000345402c9140040040001d54091040402c0680c1403804130399083c0400200b050240705007000011240c441c01d24600c000240c64a00071f0040c0304000e542c1c80d0000610b81024000031401075005610b030034001001100224800080300640601802c000c1c0c12840c907261135801c01500c1c103030495508000b45400038070a80314120003030a20f910f0108100c50b0002100108 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 395317634 1250 395316384 395316391
    0x30209040e01110a0819060e01090c090f051302070b0c120c1806091804080406090602070f060e033a03090317221506120b040f0201031b1106 62
    0x9a04008488401032008020313501241080d1800c07811a6680c111601d03092109030064500d5a450580d02045030041e0540352070503901480424403c1240b0501c048800d80500d200300d10207100c0d0000d042c4060315101c1150b84030440e0300c800244c10113090b0b481d881c04036941941d8080010400049090804440e409225031003500603081ea0709042c0203403a0b03000844104030800d4030966001645a40130b541d00702d9240c02e1650800c00703900442c5420b15101205901901924010900c00d01d400a401c910000d9514165003c1c4e0056001030380c98081c1c180d81103030115141350760602404101c50404040c00c4d005e58400704088019240c1c910201120761803a250a01801d000c0604141c88200801c0e00300030207880d120301090001000d56030b04e064442602040040e02c0921390000b14040e003c0c80444c0c01d03211601060070404100035640c406c2103900100c4240001002050050300050115402c182c421034401e0040c14041129801d00e03024800e260071401400c8086080d0107000c01d05c16504202c01d550 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 395318884 1250 395317634 395317661
    0xa0509060a1a07020f19060c0f050a050a061b051b011b020109030306060f0503061201020f0a0503010e0708040c060305060105190c05070e061305040f0c06020a0506130b0601080907051003020904 85
    0x6d2141100c11001003400850003120240310280c0c200b20300300042601485203172078102080e02d88925152514a03150907003c10700340c0d0041c3c100301e081548040802c505001c4c80c00c1c41c0d2146464081c41d0010020845541c44032585c0701e542e10750341140041000d00540300707030010b1341e800020030050b0b520f000b504650175500102c0c20004098001420a074100e412280c0000040b03406c00c13800e00c418029035019106070320348082500342c0803604091030f6070001c000d141a03a0b007010080304d0326681c94404440c580c80445005e000c01801030800c00446009900040e0412410724149113041e20303031441c000920f11540c0c5130000094541c10660140442031114101416108000c50b03002d0812800281121340100c00f60145540c1d610003150801c060300368000d01c2c2c254080344921016a1b80c0c0c40184d1200200780060710306000324000224031044203001402aa90300a40300c00c080d4440c81c004507400c0b000103102d211396204032440400c450b5600300808980d200c0b5940c0c00340e555070f900001d000640e103900740d0350b0a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 395320134 1250 395318884 395318899
    0xb0906011505071e170c0c0603042a3303151a160c0501021e1005070c0609060f0b01050c1002072d0605060904020a0509060a1a07020f 59
    0x1100103600208441c07103203410141c2c09000742c4455900a10860102100910000c003441704820f40f41c039084060300d207030013858090301c4030140c42d00140480c911084500038590740503001c040c3c0f905a02d4000b00c141200b2502403110303500d61140652152884c01101600385481660100b2040300035081d0040486010780c542888140c01c035011140410074140074581c01d068010960b08040740d0f2080c242d94109100b802c140030070300f125003002d80c01001075010740d40c01401842000011884804070031140886a480100780c6c0000b4030300d401c0003c04000d000c00301000303001450a004540c4a02845244a000d42d0b00050300314245082030048841800b4440c0c1400401d000c1000155400306801032a00c5144101690b6021580b40940980701c400d901c0c060655020f900c4243c01c0d841d0a41e10078405445140200580e48894081040a42007100c0c000d601c4866034005200500705110b00a800c000040c1424040c90748604903180c41e5000802e10501d81c6102044800961078140b4003a002d100007076500c230 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 395321384 1250 395320134 395320169
    0x6050402120d1719110c07150c06090c03150b010f021207140c10021c0e3316020a091e020315150306040f06080a110a120b090601 57
    0x41c2007440351180d01da10003c03c010000e64452042c0b065000801c6002c1400c10404407180c0d41251a50410000900305100355040031074a51103151a12401f00e0a41c1c54403040d00c00070341e03100009840c0c0c0080441c0c0c1e8007511100003001564840f580d455661a04101140f1500901c1c00146400d14290401c0c0840d4012003c06541da41190111080560800030b956050b138000400c1c54a4000c054004a410209003074081042680c045410311002e6101d5800c072844600c1e0030000c4030008107085206500c401200354101c140c1100950752058813005000b100c01c02000392140d00c07000d403c0400c00034520546400701c6400c40c0340c015050b8004c3e00640004110481d01d00c140310001018686104481641c0080450303042c0d020300d03c2048090740700074250300c3ca019402c00d6500d60741c2c01c1a58810302503418509520251389a44c06904180d0311114020803c1000c2c0d41c4420841044410b40c542c3c019185a5000c038040410407800000c10340500c882806c103040510a0034a00380059000300101c08128104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 395322634 1250 395321384 395321387
    0x1519030506010c02041a03030a0c0b0c090604050111010603080c16081603031103040503070914061806010f0c0b070c1b060207032405070207090e03030613051305010906050402120d 79
    0x141d0566601a038001464031405240841c1c0107490130f8545505100114081070701c1030380000215440d9106030b1480c0401e445030334085026000e41d40d5a87d920100c107010a02003548501490305500340510000700e040c81d41d1b40c607580b1090303105104440303c42e002000e00400c000141c0000a000300381c660011b0160540c18000c0000d07080d11404018208818048049581d500800c185e4028040040599210f03541d0380100000621448405035615480c200000708989401c0c030290217501c001e66002015a6130720401100c4203804c07400400117210054000201040d4413001d05885042c1c980c66849040419080c480943c484100c5801d40d00c5015460600500e5030125410085aa11059826002807081c2256810741c030004510b1542510700410080019030000d0b60a0882da0f940741c00704681e88030008041c0d140c0c407048071855002291102468801051580240e501150403000d644800e04a640c40c1400d4415103001a00c800d0b440d403043c4401c1d80380c40c0030282c101c5e15000000388000e0ba01c0c000d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 395323741 1107 395322634 395322647
    0x70f03050c0901020a0318030507030614180a0210120f05010501090504020a090e09010603050f060a060e040b0f0402030f2b090e01120203010902151903050601 70
    0x1c01c1d10107003448200c908159041e400f90006030030390f840954100350300c00e400c00c0c0140e0035040c0000228000303101050203144219008503480720084503540070360901800001c40880c2104c8401c0c4201e200280c00701890780c0c161920301003c108901e05407070021500d07000c2e00e84942401d08c04a01da4410381c0c80310f8182c603401d0b00c4100c620b0740c5400a000c00c9000344040c07100420303803034a014007488442400007644684080000f290090b103a0765060f040070341201207440702e03030b0014040c041520028081d1001514590600e00a03918140c0c4540c0610080541510f0000b501c01e404141507440a0102c904581c518004031400c13014001c840243c04100d07903140f011050781d190310800150b445251414112181500003042c02c3c0d0038640049031424001402703d0f815944c4515040051310364011740030b201d450140c0d81540b1485842c21110500005c08046401c1528101c1040801c0c0e80005 = true := by decide +kernel

theorem cover : BRFrame.Cov 395143884 395323741 := by
  have h0 := BRFrame.cov_init 395143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 395143884 ≤ n) (h2 : n < 395323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
