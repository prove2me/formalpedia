-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1893
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:03:34.332666+00:00
-- url     : https://prove2.me/submissions/e9dc3f53-0e43-41c5-946c-b44225db02a5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 340287769 ≤ n < 340467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 340289019 1250 340287769 340287791
    0x612050a111c020f01110f151b03010302150c01051021020f012f01020714010603030203090402030726010501030b01020102070210030e0f01020c0d09060309020f04020d11070c0603 79
    0x42e0b180e900703607800c0c4030a8140c40014501036034100009241410042080507480c089685450100c0c03c8a04003139200214007100c080e03221070225803051601b080e00c0c56178541c005c03450307465000610000703001c1c45080702000310019038441130301e074000e0070000204040e01e80401400c4414001d071041c41070b000780860241d185e21003100d41000c03105030042c1440e001901071500442c0e845000301a42d040c80b40a19642c2602c211011484012080c800d80001d070b00c03004181040600340e801540750806c40c0c2c0c0f5009003000041c0d008000e841442d00e080390010307181d43c0d8015081d03c1154944241d000040b4035804a010801800f00a41c0d050300c10a036420013022104a006a00300e108038076000e0340c0a030504924603402486070b080707460504520720a54054901c0303030703003540e00766003100030690103680000b14200d56965126009100800c1e0516050191003415000b00d600003844091981c00340340c00050050b0010320941012005130480d48a4954030940c50800780141a6240a040c1c0028189008000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 340290269 1250 340289019 340289029
    0x50a0608070906120f051e100f0e0c0903010504030306060905040903091205030f0c03030105150313110a0510030506040f0603051506041116020108010503120406120612050a11 77
    0xc403903007a03921121000d5080032800c0c1c488420024980c40829100d01255503910450301030a030142c0da11900c0582c888050030790329030091200829220841380c28241c03c2146040380341180040310f940000b842c0b03e41d00d8406603c1c03c40d00ca0f00c5a0640c15600384003d200c00c061340f40e0720a0046440990f590114180c44404101c1984c40072400600040c2d1924028003035403220905010b900c501c0313401200e03d8a40c011114515541000c04100f010303170030120041040e0b05102e855180e60300c170303000002d41c85c5240100510315015911080a0900304a180200070142c4401241c20046c10008200c050052030140d0010302801c011102035001d94201708564a002000d4010300c010390390321001404101c17089507120001c07200010210340c2d0003601c0743d0040e6500c5801c0402803600880000480c51031150500014054520680c451030083e80329641c0e008443c0203041c1a90150389075441d1000812000d252070901408081d04007200e80380403142c0300400c006000407014100c03486616110400f07050002001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 340291519 1250 340290269 340290271
    0x120102040605223c21050109020307090603061a01020a0308070309080f0a0e180117100c171602030315010c12080106120b0f06030402062101050a0608 66
    0x42401889508070703064207401480a031001140d1042c0d03e195032206981d00e0800c8103c04141c0281d04100c0300d00704000070741d091100c1031100d00002481145407808101c04c040c010a4003250034001c07a1100d40801c242900302801d00340d001800c03a010103880346480e000070070170703440125412440d01501c1b08003220b081070980b004480580190008418a40301030781d00c0c140c001e2518040503038a24640f00003403181009000440c580510040c3c1340c54410001405d44d94041c00c3c031034444da0881140e0071400c151045880c0c10741d0b0310341407007403002e1003107080c2c443c0b4122100c0007002c0d041782070450552100d61722010381d034800410041c0c443c2880e103480115100c80000340c07900d000160001c00008243c81c510000b01840001c2c10700d000b45840c0c0e0f03d907c440184444800400e4001545d0000401506512a060000c14580303107004010400c212800107a01d5480f4030b80382ea00485c00400000d05656030301082e942a26612201034030801c4224880d03c0d1400404d0080300d10440000d540400c4540c4510001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 340292769 1250 340291519 340291529
    0x90a020921070608180f010b010f030504211119020a06170c0f09130e24130204090b01081c030c081504060b0705100e2d0a02120a0212010204 62
    0x40d010840c1020030407507a28800625085c030760910b615562400da5410814881e848115600001d07040c08102c0c00100800390340f80c00c100403d0b08002c14403000c0b844d040400211a54210351100194006800507562201c5c0c2c481100341c0d5005140c0d40104103034090000002c071500c02c882100d07440f6101d4038199400d910f14803500d8500540c60b4002283da00c0444010f0124484100d0b49906010b04140050900540105070a0b01d480d140e00e600300ea5000d0800c030030103400c07160210007040300010303500030841040300810a1281c90700e001c48407029919558416203145421042014503984c4410b4003640d65840b070b08400c511b45602c509a40a011311910a010f406070340f5503611801610b440010140c0340311942c0742075512035510000095007220072001400000d110788041c11111940b45c080208903460700b0503101c820341100c4010388000001c030f0741d43c545900c0f01000c520140703440e00000b18504504007100a4020605001803824400300060080f00700344215401840c001201d03400b80d0903406140321b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 340294019 1250 340292769 340292773
    0x15090b07050306010e1309061a06072901081b01080601080621010204290a0807050a1812051e120a170124050a050301030308090c090a020921 62
    0x8620440d01c180000d41d041401407414555041c500c400103140072454038285902983d032418000d0801140b8000d8850b002c201c0c1814a048940c1d00c00819094800ca0400030701c10300350f1060b4142070b080100c8010424002c1102c2d00f50322980c45a252a51780d01800038401540d05641e113220f11150300c41c032440c07807240c14103a565006a032504002e120071141c5401200d11302021130f09600c18000780910250000385042c12000c0c40105812461100300005069242c01c515801c01c031820741c06820000f1582c2040071890090356441c401d8a0840780030700c0c060f02c00d07990f06854280025907007034507007400e1040e0340c001c0040c2da101c11017100e01700c03441012064001c40550448400d001508034a40050308040311142130480041c08043d2000d01c0300d2400f6041011007409003c044020350040030104141c0e2012801e00500d89140c04038060114001403000808000903c000103414603c18407000049000c0a40340d00c07498100035802001079080980300034051520a603040c400900540300000c040f10350100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 340295269 1250 340294019 340294021
    0x510020f041203020c0904050607110c030a0b0c04121110081306020a021f05010f12051c0302071406010e0603010902061206030a0c0b1309050603060a09050f0d090315090b 75
    0x402d010550108007a41580a025461a074a8036022142c074421032144001d0a618544003102030280403202c805610076522071419807100d42c500003500841c2540103030181c0e080e6030303900942103414812034002d5190440e043d80e00004004164000c218041f00445252416074650b80d81190342c5901210920824040d83c519503010440c03603401404106014419038444140410305584c6040c02820f0702100107550b80c0041050303441200d2103401a140c9c6403542419031420f5160b0351b03a06c540c481164018458200303c03050b14103020381d04482501c0e5001e842c2343c0c1c22410341c01906171180070901c0b5000300100301c2d9000920b20300d018815a030542c0e40c000d0110f0300345030105046034000d0034010002600742c070640300200702246031400d507100188000210550340722071040420501c0841903220414060509003403104559020480d598410008000061511083d041103450319841078504d18044c0290049481025405498070701980d0107405888100105000c0070b00071520b18040c05005612450 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 340296519 1250 340295269 340295279
    0x8040213091e0804030b01060f050a03050c070c090e1b03030a080a0b0301020325031413030c0b010b0417030301060504030807050c061804050711120a030f02160510020f04 75
    0x15010040d06405482850398941c1c0b0342054800d24025071400755501040030800b041044040c91050f40542144d10b0046059903000c14054002d005005000342850385407400540c2c00c182c410103071a121600011156030b066920b441c41e900400d9484038049040c050000b0380c4015441170040300e200050040c0c006e515200419804492503074010b060400c1081d101e40c00d0100c1950240055401154201c4130f030007004112545000080d9490740c451420706040503480003030480700921140d40080d510410010901c0740c0d00d000c8802039180316006002800050001c107004145c000a841a5a10160300d2042841032000ca150b8074002403003060000b500c00c000500000ba6001d01810000e031040045400700a0300d0000181c4135005408400f03c102c4403400c404080b49401e00401742c10103e9801c00d011440c0c505103900da12600d40050b580d120401c00610948614400d0b07100d080c1e00b034048001151196243c00b020000c40ac00300809407030510a035542e81045031446d200300c0302680c060b011018980f0f4900 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 340297769 1250 340296519 340296521
    0xc01050a0929011811040602070e130b0c070f060504031808010608030a050a02030c0a05030d1a01020709020c0309030609030309011521020103180605100803070f020418170d0c08040213 81
    0x321a010340031740c8441003000c07001d1803507000e00068121a00600308403810140001c9591070018090f9401c80b140030f03048004615181c14003500a8440054140c2d160018200076101080700c400003041c2a10381070400007032540c0140c1100811100c03101744560142d480403110709940890180e80829041001640c020b40d00a000502482c0c416005603418012104183c41c1050340c81e0b40d042d10586c000041d9500344414912a07114034612000e0302000266506000035911401030040c1241e259000030201c1380403004106485101000400301c40e03840c50a4041c1c0342d00c036082038807801900d44c00c2102c102c1255440c090110700352200040c1203941c10088902d10340f188800d20600781d042c03550347c115051400c02c054400810003800303454003040c00c1c20001080f03a000c52003684100c000d6007062014a00151104800030a0307603404039004604004840744040810031034500050601d4180e15010782c4403950a005400c3d90b01d40e60f901000800240d4034292103800e012138000790301c1060440c0310030920141b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 340299019 1250 340297769 340297799
    0x50d022a010c05030406090501020d031109010f03110f0d050a050f0408030a09140a140304050f0409061d0607170105130c111e010b03031218030c01050a092901 70
    0x20514007000b101e4480c3d00c1d01c900b10307403041e0400c3c00080c0290b801485139503010040c45881e4003a92608200c00324003078020b031869010782c04055040251410071440c000344207401c0b09250043c0c140f0003aa440e480001060703026800510000e00c240d0401c00050071050707841c0b103035511500a01164020550321940d403071400343c0c03004140110540c0d6503100c01010808800145028064039001003447e50030609046403c0c0c0b001008000c400d500401c020300c19520380c4462800c01038400e58000c01e07024030030f00c0c0820140026840720280c078211811a1007100c540014404e026040e941c440f035001c0807880d10024400702c0240150b41d0401154809a001505207a006000411045c503002d1070041c05003c465041400040311002d09080b200c00c0303400b4004087c03060096840c13040700150b01e003805461a001200360001d042505011011001691042c41841101c1101d0f04401c001c10882c0b4103080f0100080c048110305035805509005503000780c8030610550f680d4058486240f188682c41c0c450345541440c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 340300269 1250 340299019 340299103
    0x403021005160b150a0b0a0c0609060e01021c0b030c10031407080612070e04080f0f070c0f06050304030c02060307110709050106020f07120206072d050d02 68
    0x412804800d4000b0a1000c603149100764124403050a0003041451040c006032441440b400c0c1c00001006000c0c0300e08100c50b400112801c000c003a0305403e0030400001c2540d804041c0545043c280300306800c0c44194000d1282c080e25500c00e000044980f402d100490f00005425509a0300c00c0c1c01101c85441e004100060740070ba41c1ca40411070305042407400554903002d640000100d101c0d00188995454500403024903141c036000144152031a01e01510b2060070060030262a000e00040d00403010307450242190703040d155100d8100e64524035460040052201072142c10f00701c044022020800030300c0350084a00032501561642607518290302042215031010f400d943c03c3c04260a151020342c2d03001d10010008041d0311310009020740c0351240181c10121080484101900100c034113100a0280c00344100401c0c1d010369000352200c0c0c20b843c000741455101364024051100f0380c4400741c450400341002e001c4061003007060710320381007007644180e0b510b007013030103030003440700c00d0441d1164441d081300c40c40d03200c401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 340301519 1250 340300269 340300277
    0x303061908010905010b1509010207031202070807122010110c0a03030507060c18090f02040512010207030e03031e0306030a0611040e060306010b030a051510030b0a0f030804030210 79
    0x307540c400d030090840b030b40403c0c1112241d440f01c164221a15001600f0080b1022841c0c08501d4543c1c85e00000f9161400350100806190050f46204030142c4200f0481001e000b41c0400c85045586686940c3c0a04607812001c96503000132000310040161801e19036070b4550b602610a40c8461002001590b0011070444030000c9032162201204260780c0c1d101000d0010340c00703030312a1603075500141098400d803440e100100f000d028400b5a15403d4103048007103e411544012030000d8100403400022019105075400154064036007036588503004011b42c02040d0b00b40c4640c44940e803001b411800e0607103a008280900f41032181c45c40c3c8180107000c0e42002181d0016004003038600e03500343c0b41d8035102294140f9240c241c0549011030244500c05000d02007580182c0100c0040103150300d04604003145110060089681030740344d402007002c28403104407401e03441c68001c1c0780015045100d00300400400031080c0f12032140240400000710200b410701640141d03900000200d28090540d024000706500c2461500200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 340302769 1250 340301519 340301569
    0xf0f0c02030628020306030304030b0705070b0f0702011b0e04020a020c03010603030e15071104020a1704150b0409080417120f0a030f0209010e3309090117030306 71
    0x41c0c0e024803502e032140c0000051000300c4100c044524038080245021180c6032803041090080942c0c0c0003003503408980d403101c20f00195550303101003104d150007002001050110700c0d80500c5a0034800c1115944a17000d02e5008104400450108201d0000e0001c10000803407180402a1b42c40d0a142c0c000300302410541c01100d8100003400007003800c55009900c15000190030306101245841c00c00704032200818000b40103401c000868498010518400361081c0c031490380044c80c070001c00e002d0303280b410750224001a460341c1403500b030502e031403100498002d01c1c14080c0342004022481c60541726080c401da030410b0019050500b011132425001140c490301c030120b8031030581c0e003d0709078104900921461040390422529064400409826142420310f0305040b14014400800300d41d81c09500707241d000c0c2007200d05501e83c80d842502407041c18400e41004140c481000603117a2000c1204008000144c004e072800900b51fa80ca40c120300e490190345001e1100f503002080400c1c0c1d14a082d450710b54518141900034819 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 340304019 1250 340302769 340302773
    0x6060a0918020309070f0803030601050315121005060d080702130b060a021c0c08071203060b12040219050102030304060c030f0603051501050f1305150405010303210c0f0f0c 76
    0x900344111200341c840340d40000410460f44814000c05000305108800c0099103420214002d4981c0401000c03641003180220004050444400300010f560f030703014080007800700c0c1200c44241c590265003090540b42c3d040001065142c1840c000e003141080e000300f601820412141d0801c034546090b5550a00f44980b643e2100269540700c400502c031400c1680c00911200682000b51a03644024002c9001408034210b80c660105070340404441300070ba07004000c0000d81100000503402031507240c0243c020b016020545882c1459001300b907600450003155145180401e03283d80100240d2940180e0380140c00900c040703000904207401c200d004030000d04011481c6a40110140304a548640c01900c90b580000e40f02201c00c84031407a69805006c0a560b0540003404d09004103090481042c3c280900550f1540081d0040860785152324402030001c00512442d44e403800c00404444a01c1d504102c00c120401c0b9941d60030510348a00c0524820a480d1011b02902e0707100180c580004081c5080c05120041840c400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 340305269 1250 340304019 340304039
    0xf0a030506130b0a02040b04060c0f2009090601120b150d030903150908040506070501060e0c0405100e030703200d081e040e0c160c0b09090c07020906060a09 69
    0x449900d015141c01424150ba040c00c2103c44005014400c1c040c1c03040109101b160350304801c841c243c0700c880c20070508105146c9020f0361120782c4554060f24030100d0618207141101c612640d0030f0300c0c0004032054803444c1c541002d80c0d52075031804e22031652104180c1c000300d00050660015540d0200071050f1591840404070007144071449012011000030b420307480280200005403001c0d079412400c10000700400095030740d40118601c40da0040d98821040030408004010b001d402c02c0010388200442030030142000742090206800c02d000751341c400c44401140034940ca00c11b0861b85c01c190002002441d040d80b035921110f50714070b5080014004c0203003a062180b41500c1e150242d0b4440342c81000740175600e007080c4040154102164900c416002d404200401c170400a448202e40c210f8024032440c0e0350352810039607124400b009001c1c000d00408000c5000104104a0006010f40e900b040d6800c540b01d644034042c00c41d82d0b118031980254042c1e07420020800604000703025019600c420305120070044c0e00c40c000f0341 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 340306519 1250 340305269 340305271
    0xf03030c09010f1803023102180102031615060905040c03020a12170307020705180603070f05300102070c0f0902030405060721060605071b050607020f0a030506 70
    0xe8041000040c089680d5074801841007078007440e0301d08a8030308082000112041106440041c1c4250b0200304001005100304042c1205040701c1840c80040c521803248000283d005400d110340b00d0310120512013215400402180c4520280303a031414a0501c5d19520184081104c6c6c10031610150390b200045044181403040d140140e000b403404850340362543c8100410f0407101d0304002140c200c0c070058040012519040354072030b12076026806403640d0300c2d81001c900e449155030010780c0c040c4c2070903030041e4203810036000f990041d0030640613104880d8440d0700c0380d01c0c03c0d003d91040da40c05c00701c001c00d468a80d60400a01c125442120101403250390380c0101c032142681c0010b84140d410003c800d104000c1560000040c1008040c001025415451305840e07280c8c5403000148031030180a43d100c4290b0402800c0c0c0400c01c1500e50719002005595101c2200901c030b9009048110340e403800424284400381d081d0b000403c01c4400003001a86005066401d000661078621b51258125240300c40120003d00c0900900b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 340307769 1250 340306519 340306531
    0x20f070b0a020c01151d091207030804050c04020f04050f010207090608150603150106140d09030801080105100311040c09090c0503091b03060631061401050903030909090f0303 77
    0x140e103c0e030b4031108690031aa445280071106000100040184521001c0b80750080e0442d00100d03690380c4da4110000c4d050080d581a900340a060029409c0b041580001c034550149000d0000c90b402000120b007030100b00d200e10749030355070104024442040a454800c084408110b0b041c41581c0410b80d55000d01c10a6a07180e0300000d0301500840003e80360310f9580b280041d07112038220300070136699a0003191260344201c1801140c0410124400c0c8007525042282120302c82d9009210812082e4858240201051021300419085509120120303281d040510700c54015280c2109911603c101903070104401850515592030030300003200750000d00c541c0d90b4842c400300c020301500c17072954a140400902d420110010702c0045400340c0c0c4055080c40c2d40780042d1096220205550700c8a81011803000310101006201640035513041d10002858113102540182084820800c054111110304000650702030044842003909a40148500700c214500000d0301c50b000701f480b00c242c0d100001c0d20100c85081d40d0003201d030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 340309019 1250 340307769 340307771
    0xd09050646020307020a0e06060f0304030306030b0603030702150c010f1505041103010e0114040902031c0f211505100806090a060b07023a060e060106080703020f070b0a 74
    0x1d00042032080301c246000414551000d146410b04681c001803a010a50050110000080000800381c0d06c0d00d40454080c4881e071100303903403240360a10703009024211170f00080f1341c100c4d0900301040e014113002050301e6902d540140030b02400c1828118000c03c5402038180c0d0082d82d900d585216213001c80c54031a4800311459501e81c00301c00782c101014882504d0001100410403041000100000c0001120b180e054580c0c221001c2130484000c0001009860340c1c80c401b075494024111007822003200d8030307100300c583c0c0950f8a4400762060003d8007034a0030217107840c10780f040034030900324030712690f040e46d211403144111041e81d01c10309511103000c6149001404100400b05a01c10103200003841c0032901c0a500110308130b82032000c181441c45814040c028400001e019007814504010031a8100120714900e0100028040107089040b1050301070300142c10098600a15140d18042d00800c04104181a01c0040d00d82041546880c1011002903000b0300c6032034541c81c0c0a0103c0780c0011700e11916180107a6400d00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 340310269 1250 340309019 340309117
    0x403200f06070f0f05070204060302040f05070908010506010522030c1701061a0403110a090203330a33050316020c010f2a0515090d090506 61
    0x10340c55203440c0c03014120009100743e071590703144903d0384101000c2001d4220315000303441e07511910100e40501800d80000f54030905000303c12910b968241e00c82d034401d0a1558034400140d545036010790817104291200c80c001542008515a800c008007820005810500f0241810590300e464a04e2480050740010410115a0300b907204400c00034010b070000381030340381c000f0302c517200142880521511451000a00714102e02192000560f560f1150000825600c403055540303240824401524081070308e0703d101032020001c43c240b0030011000001e1811180503000685c110300f030030351000f0801800d49a030f004407030070210821411101c03180c444507601302c244c41d210307200e0505500121142c12000380880c115404040c031765440d031b80d11070340c030035114002801c049504400c410030000803d541446281c4555450030704900c2045000682c40c40c4581000c0c0b680c4809440d55040c0540383c41c80740e603200002482c10350051240d841c1010040c1910030322010400700c2d00f0010321a41c1c0302d03001c04203160700c03e0b016035a03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 340311519 1250 340310269 340310293
    0xa0921140c030309060135010e0f012403080a031119020d080f09060a020c0c0a12060b0303120601030203060a09180605071103191103040e010305100e15040320 70
    0x450107015010b960001501501c7c00c00c40b402d0441104207152039407030803400341c88031148029800b005000c07201d030040d21405589414018080d019004e030030801441e034010750116007500c00f4036400c01c0e02d6000e51264500b51090300304901801d5002c40b60301c005442080640040c55042c1c0810703407140ca581d006460f41060344800030384480001040c840f2080e10080802c0510007011400903404803d8802c0180c450000b0b40849182c081140b660940059924001141c400b190b081c407881e60b140f1940c0144085145d18003071640b03c1c014100003801407025040400c1c00e0b5070094000d95808400544150381665807242e4500036101190545081c401801002405001c024085c0c25401316590800300301540e4070b04c40c0640e0382e10a00c25208022844c2c414110b0070140f080791612241c8180d08201c3f61915294a600c5190701420302c01224903205500d0041d45208060090280041e4070801610b200c0c1e51040c142c82e4902e00040003141040803049444000c22450814005160f420000428042e17402e8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 340312769 1250 340311519 340311523
    0xc0c06040905060a0b1204030c0809060d02040e01080705090f04020105090907030516030513080c0109081b01061a0304140129030705120d1215140103050a0921140c030309 75
    0x6508100201a4100700c0340364000c16011b0a2600aa410718010a545025051400700e5000b0100901e40c007200000c0c0e100392064083d0094000d4602440c0000ca66980c0c4a4003266510724a22031035800001d00c0e0000741e840e10301c04075010f070310074010b040c9a4070f8104000006407448008882d01808284d681d01071021008003000900c06034242c43c2010030081c00c3c01c8201c06841d4410080c0103000d64000100f11128010170f40018100340c3d030280c0c880e52640031710101d6400141207800b69581962820000140d1a916030301c00240c00c4c5421446603188d5112611524040e4110014528080d13480d0340d48011038610045088456505128101d00b040103074404042c1024240c1d800a03125141d040d94007040c600c004540400708a0803403c0900c94518604030304405001282c40f688500c00c4072041c00216900144102c1880130f0782640e0401440c2e407196520b4040350b2040030050800390300d0020200141d11140c1d1000d5603034000d07042203080c04900300303504000c550003810100529000401800103030101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 340314019 1250 340312769 340312789
    0x308060406030203030421052e05070f030207030513090c03061706131a01030b040204052410030b030610150f02100207061d0f1c12020c0c0604090506 66
    0x1103038140401c614640010307640c3d02582c05406ea4900b143e642d19051040408010325801d50b00c0010780c1c041c004010b004d55070081d0740096201600c0b5101000c030240103141e00c141ea220300000c0c0c0341c5000c00794050346e04030021340060000700c00340481003141681d24020101c0d054001c081d980800f080108907200010207403001a840784001e0143d4a0f0184244280850b080b50311480880100f401c0f403d050400d250400803004e802581c407000500044144940030b00f14130321480c002d860034403145d00c41c00071030558071080d690310003800c14100c08044110b24107040c8c1f140ea064850714000c180500b07800d000a0421405a5440754105000c00e002c0044018800320101c1c00c0d0340a007000d00700801003507400394030303107100100c0c1c56240c0d0b90009803070302003045c10342c444612107030300000041c7c044548144440c2d03030b0400701e84244400c1c407d03c82c030781031142103050356044440000d0303540b04c00201040c00108042e400c0720360348115034000c0e0743c000800d0740c960901900082c0b1101e80041032a0070b00d0f00c02c0c0015260 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 340315269 1250 340314019 340314031
    0x4140604110403030c1203110706050403021b09040311030d0f1d03030c03040816080a0e1906050703110f0109150e060c041205210405010e0f0a031403040b04120308 72
    0x180002c00104c2e4200c01e03400c084641007403041201d80e80c0308100301c0040441c1030070002440d03001f00d004014094a07078002c91186119408607a010b48d610050450f00581421200d40d0008801b400038000030711602c09040d8020324101100d0401294066100950b0341303c0b00710003481d0703541c1c002072040c010b88151070750701c030303505040282d840e50034264401d040034800140050190760f00051001d010381d0030000050444c540021140d5101c0d0400000100001c070a801018440d140e050810903c04142038404800c451140c0c480078a42400ca80d01034030019030f01c0d100e2290398050500300307032290318082c040c0800c558424130319900d01602016902045800b000c10240f2240d2001d410480300340001c004980999148902500019070135182092400e181a1001700b81c140030f00d08040440030045000c0c5c001e0350f8098070b445078800310103818400b000341d03401d00ca250312411100041000c9100407800d42000403000d0292403a0507214950b0b01001e6120b6882443e07200407081c0c07507000345944040c502d0f070004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 340316519 1250 340315269 340315301
    0x60901091808220b033607033206070c0809090906010f0e190b0d060c110d03050402150306031204080a0605060102061312031d010b0301050112051005100504140604 72
    0xc28055035916140503c28030002c1e2500c2081017805005103211103000d0304407000c1007201e805580b646001c01400349e140d00700b40b961030a10f8000d0b1012044001e1102000c42d0108020103031662003a1003103410b00b51600d0251101c84081000d0805a00ea1181d000e00c1450310030010a400c0d45098604109441070303500101c00b000d400402c1c0851090041500d0900ea02005400316003250b44000091183e070902d00c005000c03a140c401d0b2100007039040070b0012074261103032044d5400201849015025a0411100207510400f59034141e00c0204403e4083c6401540140880d00801010b08125245030b010b41c000505544c08426403100700119401051342c805028809403d450502081f15011812540742c001c0c003005180c504609900c5c801d9100218079905a0b2507002c10344140d41007e4000d00303e0f4500705000303508020000c1140700c1ca03030701c42c00000d40c1d210700146040b11144586100905018001c0c1c5019841c145002070a6521030040d5040d800099044003290308010040004566a02d41460341d60 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 340317769 1250 340316519 340316521
    0x7050d110a050c30010504031b02010503010308072f03210703030e0c0a0b0919030b1501120903020f01050106080105010c2301060303020313060305060901091808220b03 74
    0x9034010a400e0804481035520301214801250b000106244913075030310041d40c0250240a40540054104a0141d03011303866112a24121001e44074588981c0400640841c808000420005926000404005000316004c4103400240c1d0700340400190307007108840d0320042c242d01c0c0c021149014402c80c4140c202d01e2100041052203241038044600648070007505250356103100c0d00d80d00e40c0c14803c3c0e80025070f0041c51040c030b45440d138229030510317000f20b8840c90181d42c1f480c203403a100c412021600d83c2502e4102155080d00c2ea00d100d05274018002002001c1c1c108890031905d030039548c0b00c030300452951030b12039000b41082032449000c190868405074010001c000c2d401004004a0b41c100c0c007515503154000c007007200b6603841e2080400ca140140c0320105d0302986402c030b00105050b4003002500800c842810312102c8156510301c110161202a100c00781e111075044010000f0550951000385604030b8a003544401200c1500e4075500c81e0024503860003100f404100c8100c000d0303a40100c070390140a141c1050707425 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 340319019 1250 340317769 340317773
    0x201080402010503060a090c0f021614100e03010c09081b10030e010905060c0c0609010203070905040506010e120f011d0d0e190b1207021f18060207050d110a 69
    0x15418058000790512034000081001c0e501d5102c0c0700c4000c0c02c001c440c103021694590f82c4c001e024001d4803202c01c0c01805041b07400e0403124000020b140880e03035840c000c40090f0000074100203c1a22900001e001d01c828000c1c4110304d41c5080c003901040c1c40ca2919004211854005060f0a02040c031186030903180c00d1660580c0d1b80d56800d00074280314002c40c600080d00c5c0b159850050300400315100003601500c07500003041002c50400c002000e000300d0308810350b03060352514203540b420703800103903044008584c80d03c106002c1070405078171850740301d0b205140c0724400990620106040075812400301600d904521840701012900340100350f00b403511443c040b03030007048900d207403502d07148001d904008206031091510203503920444141640802c8004d2403072803d0380c42c0030501e41588203e13101074620340364200186001d0b00100750100301c0103041000d80c4c00c0315900100b500082605260050560080d04c00c14804941c00e071000d0883e403031154001300b00c03031500702e0805441508130440085055108448140c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 340320269 1250 340319019 340319027
    0xa0903110a02030d11010603080c0a1b08030a080c0f0313020103050601020a080910030902120313050d05030a11010e0114040b010f050a03030e0310020a0f0e0901321f110a0201 77
    0x48003500a03c0e0550b600e10600b032001b4050035240e84080c01d550310205802c660494081503001c3d03128880c440c00895046417080182c0c6600c824820961590014400c14200602420085038001c01c256503451800c01d00301130101058005860340c0c000014500745020455030103104880d044a800d00040c02e90401e5642d500103284160700700c8a028a045041212109000750004060b840d8018400f003080800000815030740d0300841002039a01c0d002900018a0381491520a001180c001018500e001d4a035001035509551554185000d0740d038071000c0e8881c0100c280715080c5620030000b00085642002e06107005500c006802ca10509440501d00300050740e1107034040303001ca075803508141c0e1f11090404c00080c201036886805403102800001d10450741da0344412801d0207500302ea11035507401e944082c1440b14192003400b9124100c3c185202c001c015074046459540310700e80e410a4014042110000f14800504c042c2d1401c200c04e01e004440d05400740c01100b04034844943d14010810300c1c6050300020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 340321519 1250 340320269 340320283
    0x702010509030a0302090a0308120421050f0a090e01150905040e0c120309090f04060f14060d052b080916030b0a0e06070e100302130e06180a0903110a0203 68
    0xa010300d175002500c54480d886100c0000d00550700103c509840f111103080300145140115012030b62100d8203400340000b80d071004007850b40307884141d4406041c400510b03485003040d8021704985040c800740e258000741400f40c7c1c000d280d000e402051444080c000a8180150003d80144c010b40d2003030f070034043c0007000c2800000c0c2c0d00c103074001d00700c0d0056000038050000d1404c520030401d05540000c01c10040001215490711b0460203644218402c010108020b405103044410014001202c0c0204a0115515241c142d0130124028001e90560781e0314001225401030305405d0100700c0d0a02c40d8250300044040790081002c9910410280c003130814004035903858010351126000c01440040d00ea40800c40410180d4030261010760103004641c070500308148058240b14652404611501092001c01c01003442402502c0c41007210304050b0b9801070a154142e98144802407036103401c420042d4902030554060300f10a4026036035441d000520b4082410010700d41020608403128603448008500c00603180000c001c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 340322769 1250 340321519 340321537
    0x5030d0e03090a1d0c03101e031505040b01030b1008160e0f01030c0911090402070308010504180f120c0804060c0507120b0f150a0e150a030f030302071506080f0105070201050903 78
    0x26600d503990345175642c5044158002423000250a025000841221a18682500c4c01810006107842141e9030150130b0300c45c2210700a00380e0390401c0042002034290084da582001c1e0802c00000d42644070221a807a106c038030004801803200c1030b5401c101c0504c0550003503802c0740030090752054170b60658440c684043d03064480d40c1d0000c0d59070074540382c060381d10380240d40303880900810942d540e54590800030a202828015184140d18018007001c1d0145288442034145505c00c0a460484d402c0d621031040030b42d403146640007400b501c4c10328240041d0348040280098059500c0c0c83e4410082428150314010a540085000050400200c0c0c0032446440c1c68a030321400059480341140c1d00c4400c00c200300150751100316003080d2121800704104002d5800c841c4107182c004c000c441c60781808070070001004400d00c40501400107a02c113800200f403182c0c0040002c1c9029410200b440e1a4910400781100c0559001c50503d8201d905031700381c5000c00703005580d04802148000e0019040c0344100d1510f81c40748a00d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 340324019 1250 340322769 340322791
    0x1050109031e030e0a06050a09050406080c12070f0b0705010b01050f1204030c14030414030109030504030215040b1b01050a0e1902030a0501020c160b04140d05030d0e03090a1d 77
    0x2c0810544100e1644c0204040500341c048216503460014025800c00e54444000c200170120104060074036104484c201c0b03c0900c01080003040034020f010159903c40002002c81c01056000702c0ca250002141d00001c02c00d8440c100e40e1200c0600306242154412036690341004410840c622a01d45034009503a17160041d0b40a240c0c480d2603900e01aa40003d44100041c08a07402024017406a131001c0040c10440b201044050380e541c018600b0503082b01c10041d00100410024041800941802440186181980c5001f1407a0545400c80280543c05c807540452020060100d06040340c4028024181c20030303505681849483c604100d219150001072541000644286001d013056540812240701a1178206c40210340d030700b100b1400300361100304071030102d140402c40e031100041c0204c80c0e40858044607030009160701010301a00400000020401054a1900c000d0080d010303d04020f2007401911541e02d0700441d511040349040c482c000e180365002050500c19005080d480b095401c258603405200c145c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 340325269 1250 340324019 340324073
    0x40309091a210d020708030a0503061908030304030323060603090307210207050901030c060e060405090a0902090a06181d06010803091e0f0d060b060a05030f0105010903 74
    0xe14031101e403000c03018a0340410050300440d548514407900c50b0036003500e9029a144500d0b0880182da0300c1d05144a4007840b0390003007020341e207950711810203940c20110080040e80c0201c0a000000b0082e0f0054100c02c034140c0000050200f099054801c3c80e00f021201c00c0d030030541b03400210360043c070324200910290013145c0c0000000c468000520846401c01d03800011020300031008018185144511240800580700d0b600c0d0100e07075450100e1b042d034102c0b40d1191f40e0400c82814000c04035900c01005000c540c101500340030100c2c0640e030b8509101c1c800e4035074060014000c1014010460031a030060642825289000800d101540009001d500480c98400c0e010a01108034041d018003120800351201003405900001f107940313135011000304210b4501316640004100e0070301905000e4855090402c2e4010103903000595182081281d00113100d010b00720010f0103036800400b084d071540c807a0b900e42002500001c1003003800447c0f0391a50b4050f00e42031802c41800c81c1541c0d10040c101603034000c240107414000c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 340326519 1250 340325269 340325291
    0xb0d0f06060f03080d0501141c0f0c0602010b090a02250206040b030112030807050918040213020301080d02120702030d11030d11091806010e04021c090809031504030909 74
    0xd0048001041c04002e108081c036900d050400b0f0795004000160003036030404d0000604002005405800350741c00602c01428412844000038407414007d4003100c080c6601a064408191207460640080c20765030000b007981a80d43c8100305503100020f0050320024818003005031061400c0300d03802c000c01d015600c038203459034075400058030350b00882d07018102c200710000010515070300c01c61084500c41c2c482d844108d940e840d40402075415002e00c00c04241c00c0005050740c00d05844071900000c0c1c0060000d0448480800b00c92240e1099078026000910310303a0000150703100740d60381000001b04030781040400f0341c02c0c2840380d8002500d682081d0340b00c1040080c0ca40c003001c0d01c80014011070b86090310780b2104000c80318074002c60354081d8100c41d04051013146d4110754541d02c14120000a441042d05070348102888038000c0802c00290404004014829141c810b01945141280f03d84003806010b10301c05602d50390b00004152420701c10301d02c955002c1e5400d42c103010029810455010640e0115500425001000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 340327769 1250 340326519 340326521
    0x61b0f13030807061b0903050c0d11030601170d0203040f09150f0e06040e06131e050105010e0f090d020c0616080307030515010203270109050d0c090507030b0d0f06 72
    0x15000a0b10940b800107001040200c1ca80c04070102005213004080564140441941c42140510001e007045e003202c1c0401d01c003407811582c0304e11024450840f44a0313010302d203000300e442d00c3c200340c0011180903a10ba02c1b110410404010882d01c2c41c4032440158500380c1041e0008c505900c1c180310b09800c0c0e0b40c4840034441d503032054401d0000688110011802c140342c0d560895254a0301c2601c2c1c69000c0e03490140742041c41000814807500c5a14401c260f1200180b01d030381d6190340c0e0700c00c003e040100d07101d0b00525030001400a0051074001c14106140324214102110342442c4040c000c0c118003495807164411105854003c54860302212049500c1c0d130b161805c030015a161501d0900005000c0040042000b603a1074050b44894029480c0001c102c40d04101240160303500d20840114448040440c000603080c016182d2000c494040d040c5020042e1907540c03404218041d503444421644403518035000e02041100b1b12819902c000c06107814031000718043c000c69000aa40f160242030201200017403000d20904d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 340329019 1250 340327769 340327807
    0xf160f02030f0303060f060a0e0d0201051909030b06030a0f150615020d0f031104030b060d14061602070608060d03030e0f10060e100e090a02150c061b0f 67
    0x34003980c00a001e2500d01c02c1c2c0f01d0b4401c640c0c4920403110795520114034204441514105441c940740c8040040300941000794000030200c0482c10040200701290b85031111103a00300018405842d911341050452030a5140304c0002080b0380c2c000d03441081d454011940350ba1050b80410340007048600c82e5000743c2c0c50000581800e03042860201c1d046807004106070b5000420758034609540d42c45010540101c50101d0540741c41c3c60500c003512206000602c04250380180c2c0b260051001084100c085420342e0f502c070440784031850041401e40005040001404003805407160207031451020705480d509240020305000c80240c803a80c014a9800ea1034070406009502c0314801c440749204990140440320030f00c030f40d1480850003240f030b00b9040c10400201c2090110915005424000050400b9801c0412481040d1001403040c4074a00c117006500f00562508403600046003030282802c4c1d0f603202c0ca03d004614226000d0052185e8a400b180129803920781e086c1030b40c400c15030120710a5600d109802807070400e494 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 340330269 1250 340329019 340329023
    0x3060f021204151b0905030c01080f18030c01111b0309010207120515040507170303060303070f031b060204030605010e0424110309010617070311040209041d0f070b0f160f 75
    0x81078404d00389805402c4401202100e004600321010040380c5c0d001100c00c1041901c10000c03001c445000705900f20303ca0301c02c412038280e00e18100e900b400003410f0b80700e0075a4070303d10550b10000f00018075100d0460081d5641c0c01d09903c114015841d00701c503100001d59800ca10b20900c0390f4800c42c42002801c015040c400d2181998418190102604003410702c16141c81e298441c0303020105400c4540804d400c4040242c83c0f0072000140994101819500d801c00c00305500c000480030080b5521540d900c00d58000850746525010b0600103807190b00b10318164088034010703002004000310b00c0003000005104809141c00c00b88900300c410480e403020036880d43c00b0300308a0442e08540346c404410405002015885401115900700c29140c00701c400c4007071142c544005001c00f500352415450014120b0400d0380003410340b50006000050301c0552029088021301849460100a8004060b2240c0390001000718101610310706803028507044017003640346128440c1c2c032007900181080700000c00a10040102940c1d04c15 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 340331519 1250 340330269 340330301
    0x602090303030f012607030809010323090c0d022206150302070c0e0c22052206061d0d050f0109120f09050108040303021b120403060f02120415 63
    0x3043c4854000300c460b4090240c3c01c008145c41e403c03100b41c4406250038151500001014004c4941540c8a900f00e030b500c0040b0042c1490b0300c403210031080042c50f070400040f8081c0f54600c0020b500380200d2841c2850121300141384242ca500c40c036000075039914640006101c00d9100c03d034001420307240c9c20f6000f52503154000c0b101a90003100b21068140c064004000851099011211090700c500a03802511010f480c0c14508203424059900c00c454551529a0140ca199411400c242d0713640002401034039054451400104d034450200028030118081c50028010301e050510040c051240c0c5202901c03140000688103400c1c1d8404c01c0140710090044001d0050341c90028441c1380c605003040d505680a0045580000e03070075094802c08144036a4410040c2d46c816920703024a5100e80c1c4003107000c0d4000007130721940c02d16000742d5048152000c100303940e00701c50b4200e020b5031102d181d420140c044808900c07841001c60700400000c01000000070205900c1544010050420810304104d1001401d00145050b002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 340332769 1250 340331519 340331521
    0x1060602010209011b0812150a0312230a0c081c1d01020301150804061e1b030b060a050f0706050c07110f01020a03030c0210020d06051c120c060209030303 68
    0x1959064004044842c400e0b01c40e0760007819520140f0032a031400e8100581040420b00c8408200d0100329071580c2c000154080c482130b550317942c000050000703205031700c01c5400c1c0d949007090984154103c90500d241d1481e4101410a4002c9903e02e0f0555224402c062000c2008a0030300000300807100095a5500c0c5180307041040194240060000a003d201d43c0845500d40e00310481d003800e001402120b040c1d541d03402901c801c120031050156212070300a0011540381d92105060910000500d41c00d118a80c41c0440c00f02e4502c001d40001100e00100c0ca01c18020141803105d4012a0b444600c212250a919464255941e4501d03500d403a285000380080200b80da42040141300004440300c000d054a540640600f006200500080054582a1880039405600500640c0011a009601a404461040c0141c0e103620030fa4404440c00ca80c0644100301410740e03035140134480d80c1002c4400030b88108044900090701000b5894400c2c0b106041c441000800803100e800c0000c0000d241c05a60100740094220794407 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 340334019 1250 340332769 340332779
    0x140709060e0106030b0306091009080708180f19030206070309050907020a060605060a0c200d060f06151d0a050a0e04110a14090a141e0c0301180e0a050106 68
    0x10703140c428883c2400190412103001d4603481c0104074075005a414000618078144401070047c007030140c0070b000b0349038a8014032001c004104c0c090014864425445000d000205060701006100c204480746540900400000c0340040c080002d102e009881d011501151908800e00d01141d022070703070740c204542108900062200d5103800046030304105107c0c600502099482d481448451302540c0c4000002070400c100c41c00116000b0155098409046103c440000d0415008030b000003100501c201ca585035910000c09504610b4030504015203840b03401501c2c80303010f407000101415010207440030644280b100e400a01d55070240810020f04024000000d01950381d603190b40500d0080301d09498403140b488445209140207010135041d074518807074000e440b01c494000e00403038181c01031a03100b0090740e550003010148460125140700361100d039007000741d4a80400c0c440740c06d40d80150060a1510082c401070200d07181c0c1101a10040c4150130000034120345503103090b0314284040340041d00c19481d10300302043d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 340335269 1250 340334019 340334039
    0xc0109060617151009020c0a0506010f1d0405030702061303020d0305030711010b0303180a030b0405010b01121a100210110306100908060406090213020d05060f03061314070906 77
    0x2008000005035000300a80540f0609504811103400c1c400200c24181800009502c0e03000c2d01680701c0385402c4130300c05215603441c40d15124080e00001c10311200307801c0c200885190b905500d03c1000d629500c049081c2019583c03076603240940c0c03100078460f04000c00e007840941e5502c100c1c10019500182100031080241c180684982e0058940e0030008a280ba500558002d05019000007034202800031440c201c0042100580c05c10741180465104181c80303400004030b110340303885070b003d40c0c010700c00001c004280e0000074010034010724a26900c03074184842d0091805400d60250070002c3c1c00c5d00c440c000841c2002c01241400c011103000380300145041420700810700003001940c80703140181c945000d88400003400b07880007801c6105800480c1d2141c400500003a20a801061500f8405400f045860100f02441c4090340c000b52040124256520208035031860b01c00100c1c0000c040c00d40241c22241003c41c3c5402c0f014014860180c0007010500042c08000410092030f00140923107081002016100c2d40804 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 340336519 1250 340335269 340335299
    0x206031b0f190f0c02040f0f1a040e060403080604020d02041508070e0307081e0f0d0804020f0109050f04050606130807080607022e0603060f02030414011509020c01090606 75
    0x84902c1030401e070811403003030003468080c0710f0100d9602d0340b0307014101a0742008040c0035103031060019140c4804507842364003224050741e0080e100000505240002c7c00341840b04490001023000000e9002006000100c1d420445680d0042000e40d0096590146034102070007903c169408003c400350080c03045041d8650052419001d01c0b5107039221021812a00c0800d9a0b0310b512f40185c41750340e0007218070038420b400050526080c00d00780c40c0c241d900030807031095214280100c50131650b002c035900b81e04020031850903d5020401600900300002140c0c2080c010803010300c0c240d5030a40c0141e90740c0000ca0300c0f541c4c401e0103856481c41895071900340b907a21510144c0c1c940030240300d40b00051007500081002640080344e201c03103400c9034100f10ba104414030b610682d040310b4407505800380d0756034682000c008540c550064a8803c0031081000d070343d0381044d01e024022821001080c1c403559140c5541b281c00844200310740c20480d400c0b0007016807500d141600d074a00404461000803c894608440020641441c0c5821 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 340337769 1250 340336519 340336537
    0xc0c1f02090f09090d030e010b090c0717190c02010e04150806151f050408030d020c0f010c0f030f0b0907080402130203040b061507060c05041406090d0206031b0f 71
    0x107114541c07010740074082030f024141d5005000344c000d00d00c04090148258048245464214004078070220060003080d00790506540040d03841e10006107682c1400180920343d001a07084a00c03092929000802100034000080b8030001003012112441041d6031041c440200c02400050081026020700c0d8145921000f0074030648241c0e003c0c00b80000c04a15111070f505869040181580c0c1c10780c205c0c11203883c0c803c4021803050080c0003051001050911040002e032007543d000010050351001104c125629007070a0400c04070050b8106100417080550040e00601d1a4081e414081005c05444000102419000c01815005540e01c020407044641c007100c0d050149000703990381c0c8080d1202586031030a911086802500c00b26031000800c1d00d81c00c1407a00110001d00038140740d82060710039a1003001b660070707c0000400284000c03c3c103201456506840c8243c80800b02ca2041c074000301940030070b01c8081f01d200c01a00c030ba54040006002c408002d480081900402094581d0380c004055052060340c01c91204 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 340339019 1250 340337769 340337779
    0x20328020c0102070b04090b060403080f0306180601020a060c090b07051c1404030209130803070f0801050d0c050906190608270606130209040c0801090e0c090c0c1f0209 74
    0x341c415254004150b400541d80c1401d600d900d410b041900344c4014005191031107030030540800c000008207000340050a50040e10320a80d55817410b1080030003410414242ca40b116807031031242804800da80000d0b19010342940700c4c002003003481c819042901d0040c2940e00c05890b21030002a6101000030100b8902c06000021001f040024602c45088a10300e9042c8100d00c4c0881c420082840585046001e041d405800d07036100e01e000c128590b46d48001500140c8400c1d01080b0580442611a500414142c3c090541601c4203000d441c425200c0742900b04c2148140c0340038200b650045a166210780c0001071000410b42c6020155540d41e010062600500700c900d07117110007559150248860b018180c100c0103851a000a281d203444040401410104007026601c0d0564200491400ea0300c1d0740c010300d46400c09680f60030501c0e40c07600702c0c0641a43d0319003100c4286904080440c1c9c00c20381d18019115080204401450745a4165941c404e1521185483d4904214400300500c840300b8403980042498003000d8403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 340340269 1250 340339019 340339033
    0x4110f03070603060f0618030813050a030602070c0503160501080414030c15090a02010f05030a1506050a030e0102040f060f02030c1b040c0c0804140f040501060c02010f0c0c051002032802 82
    0x6e02100c07400e640b0460301c80b28560011003040410690006444958000d0501e4006c1c87d030303605d0016034100480e500894007250042451406d00210440030002807030242e001c0c5c4401c2c110650007040e03184150150358140302c00c0101080501a03800841045484220b04599030350721a0454296106000c11512410b08100c0700011740442010812940e003d80c1a1100b41c1c030300300c61800903582030b04002d10000c8015502c1520310280b00c2d0620405008010365294265110b925400041c02d0f10f86000401d4410fa00400040107298581041e0b00121849031400c055820210401242584200d4130840030030701c100c00d003c40d00e080d181c9450317955280c0205c034204044400c030a0103548e030751480c00014080c1001072100300102040040e4202c4d030b07050014000c0301c55150110000702159000c0e000360000400a1300c0d190110358001084052105080c205018580c0d110390722407611032221700903507003e002510b8034441024020400c0da0140d00310f1a0400074070000c1c0c3e20070b405070000140311000043c89000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 340341519 1250 340340269 340340279
    0x5120708160e09040809010c0213020904060603050402030a080c0f0f0d0e031507120207050a05060402041104210809030d1e090506030408070c030506240405060904110f03070603060f 80
    0x80224602c01026001c515030307a0700c0b41c45100e43e0381c00080742c00e810700020005590040e5182c10001126814051006868804010502084a4042d04060145403400c001e001c0543c1d030006251000356400724413507985004c46920103080c42400800f2492503c030302c80109504040c0405d8008089140784e0ba440e010b4081c0701c0c1050355940e0f1203c11002c1c0190303403001040281e803140880e120081d210210161a04507540d480700e00c0c00c11851006c4c0c1d802d401c0706007800114030340b600440c289220564411810709041128034070080e250b00000107000350980d244801002000c10a550100344024180ca0358011a0300020f000000600c82d0030580c0c0d686600642c200780e004040700d00a90748007a240300e04540d26542d6220007540003250550740d040104030000005034003001554451403000f420660543c2c00314046400b42e0305e078013006610030390034801084076a0300d80c0441c240d40550003140380925422004081000d02c0000c5100d90b801d130141d036101103816a01900183c00b101d4010500a078103e0f514 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 340342769 1250 340341519 340341527
    0x120c011d0105180a0b0c0115061103030f06041103010b07230a1b033201020405010e0d0f080a0c0b01050f0d080307050c03030a0e0c10080a020a0512070816 68
    0x10400a80c0400d10a000e01d5444070103c008034803068101420035048251126050b2a040d0011103d41d400d0769141d200020100c2c8480940c28000c01503801c0003101c2c0c00c904a031107a182c0c0030042c44803440d003a04000103040740e07989403c04840c0d07020444205540b13503156051004103910031901a1000031400d0f42e5521034207483c0f5011020101c129000d8004d0420540c0ea403555007020150401c59600c0001d00400814070344413805c1c080720b43c044a50860040c0c1e0b9040200d07003440050b14415964418002005075980050f803884000d1000c45400d8506400744c600081f00320305800020f414108085001c2880300d070481c005c0e15205000d0195040d89a0380c80080082c00c0c1c02011250340c2000240b005800006c000101071030304448079040903030902446000d0703545160802c942602c140c60720342c0b180b46860a001e0200d0491b41c00160340403684030b0410350019102d407030046e0521700095400200611018440c40c10389501e2003c1b0300780c034206c0341800c500080c00c9107000c0e10300259604030740041755601d0f400303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 340344019 1250 340342769 340342817
    0x105010e01170a09020409050d080609090129060d15061b0c1a220e0906330409210801150c020a080f07090b010f05040e0c0702120c01 59
    0x182d50b100516684141404004e807599500c12a04a07441d84000c90008406101c12400c61440c1e0340c505c0c1c9289018010800d107044d02414401090f45000f0200311200b0f4000c455a00103840c1401000c099005800400c220341304181d5196150b928001d824503843d0103d4141038102c4049564010b4403602110440c041e003020500010107c10f942d810800c9100b01a0315100503103034801094604102c2585020f141c644101c1c0c044160203040480c05215206541e03802c40d4205d40400018901c2d4075094850549043c000f000c02c00541c403008900801102050803070200d450006031061010002510308885010040700b0b105010b409002411500340e489000520304940c01c0c40300850680c80d1964007036a0181c110031069070040714600c400709005038100002c1c1c0103149004000c3c5480740c03402c502d14040700e8400405078104000c01a00509442c1e02c142a50203460f000785183c146519450000c0b10300f8400c0c0307030700250011114110a12801404141d00c2e8920a080c0ca400450841400103119410a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 340345269 1250 340344019 340344047
    0x20607060c12060f35030c03190923130f050a0b1906030b030c0a0e15090106020a0b09011808070b070e0603130510050a0209040b06091813080409050105010e01 70
    0xc451400b00c00c800c0000b840b445c41d0000d05400d9651645800340f08641994041202d403400c0307a00018009032003581e005039801c8600241d140c4400f0b55414101d03400280152034038107201c3e101170b55041c0790307459442964444105d440c0400030421014440b00c1000070304030446003580b041d45444035003122030400c0f00d804201c09080f01d0100418a0070001c0c103400801c1c0140a131901841001d0490a264a074109482e018083e2001150410700d045400c41075401c4084021070700411180c0700400045400103000c410300da5000021128039030f2250b00550040040c80044420700000484c01e0341482151802400c0079130003041c40d06155503c1c0201070340d12510080d040c1d40c000c0000c20000b054004d40f10071185800d4460802d6940b800401c03da03280036150107443e502c0d00c41d41e001549240d00c0c50248107098043d4020f03103a035401c120344030300081da60040c905440c2e030b0407400940024170400d014009240b4265030100d005a140c1d51920700b000700070f1609002c0c09000ca030001c0003048480d8051030030583c5d000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 340346519 1250 340345269 340345289
    0xc05030609090111070b041407050306220c030b07022a040f0b04090b240607030c0f1a07031d1b040f090b0403031407050702040504020607060c12060f 66
    0x910344205000c81e1480040403141103550300e8980040042d03103100180240c502400f40c50003281401d003801100342012100908981e44070b034a04010940f40420b44961142d5801c8480d0315402228490b51504880c0410051101004402c08010081c000803864000e0080d9400c842e0f280c410010402410484100c410320000341d510b640c4203036464990407500b00491100310100711994240c0101d02994a442d0b400c95200352001c00f0090b082507403018070b007140740f0708a01078614102c3c0707030001c10200c0c40381c3c240140400060700121070038041e8460b003404040e80e22034681c41403100c0000c0032207040a0300303460140000c0d040040044c4026241c0000c51019806070001d4684c03075141c1509590346450750074034690056294240c03a071403440948a04106107004104682ea2460946001003c0b900b0000500c02404103640500000d554800160b0701d5080e81614005500c4c0c6460000035114012140010100350814001e0080d450f8084002881141c00e100305014580c2ca44140c1c0c00b0b102d01501418804c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 340347769 1250 340346519 340346521
    0x3040f090e060f221e0201020d02012c0c030a080705100902031515040905010f0c0807090918060e010f0b0306062b170c160e0708060111010e0d0e040c0503 68
    0xc0b0f01e242c024801340081e64200d400ca68046503181407401d40740440224901c552140c0c12810f558050011001d00361862000f00100d40d0021050b0310a001c1c0c5150f2002c3e03c82c042910a0441d0320304100c050080000282162001c820b14500303d030b41d9034072030700f4111040c2c01030110220001c001c0d40100885294000c1c003034000a68003900407096a000240380101806c2603890302e55482e00c0794407420308404e0040002140c2d02200319260f4040ea200c5411810412104100300301e4035580c0014808103540e50302030089664101e2410030030302c4800380d0401421961030030341801d0f2103002c150311a14415001070700501410070740c5070405485060848240c1c1d000284529440c503140c103030031940c0b140001403028280071603015072510040c009410207802034415000400c4010a80c0400c2400005413208025440da6410024000c0200b940070b0b049505100920300810f01d9680600f141c2040c684950000f04117040c40450890b55036036421204002186244c1d40180e00c03424140079040d070301c3d070b000c0c2c850301e20b1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 340349019 1250 340347769 340347781
    0xf1b1813151116030306031403221a160602040b0301080f010606050d090c0e04050a0b010801020a021e010f0f0f0f050c0a0f0c1a06011412042303040f090e060f 70
    0xc60f03280401c04408056507102c000c00000d1294001c5021520010011270f2a0400c0b0010700305403507040c58588800452600003084000f49078050000e07000c0303038815a103883e000381080e00c41780c484246000800460001c41d000c6103951822020314102c40481088500700c00d803044a15003242c031b443c013501000840420080301046869044440f00c0c0748500c41400e007103961445c0b40000c40d001030340c045034150445018441400009002c4502600040d0000c51a1140403500a551201c1c0c3c1980c50040b540c00b029014006203082d07104041e2001c00d400c00b8041c6d40c3c0298200e10080111005a10450386021016403080c2554492540300300f1140c884079240c03540410701501c00c01110314900703080064036800e13072001901d001d00100c6c1c1c10205070000d60312400c1c040009441d4002c2c07090441c0341d17094288000080300c01407810082c0c1003a002030b2000350b2100c148111000780d80c0742a82d800810b2100042c0050400401542c83d000c842d900c1070200101c90111541a48030b5030281e8220142401da5800305079 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 340350269 1250 340349019 340349047
    0x81801030c1106011a04080f030306010f0f090504090c051306060311120a0506030a050a0b09060615030403180b07030c050105060909060403080c070b0a0c0801080f1b18131511 77
    0x40e810107405d01c24213041c4e40d004114601030070404600381c6500080244551542c1040031561103a11078200100c0c25042d944000f441c5000900c00c0c1d81c032031510fa0a101040c000c1030203e05002c0c0802901032031154000e52201409440c80788103200000340f9103441e07400d00c402010b05441c02c4c1d0080302e0241a0584031491403001420020709a03d41c580074412072000004c0c41008170000c40c43c031503006ea00e4030307191a520007130800d40c0c0100a00d014601a82c0d11071034418010f411203500907414104074280032003202c80640c491050f5041040a41c2c40001c070102403603000382c2c012401d10b2141000340900c0c1d489200b48600c14505032010a920703444107001c54002400342c803455610540c00900d2a00b010481e4070303070310f040c1c640640d542c03203904d50b5406016211550080300b10303000d089103100405008070310002e03003540d0f40310085045403840c0c4034605049150f500c55100e20702e1200342090b02600341c10140a03058a1649100003110341061549045040000600030340c0c1d9041036603c0c4441c184000108591 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 340351519 1250 340350269 340350299
    0x11a010c08040503010603030909050105090112080a020703050304260c240702091006020f06090d0f050f040803031f0501080c03070314101404050103200a03081801030c110601 77
    0x580001c001d100119990b1001d00c102001540655a4500756078900f0011004959044c0c00042c0141021001400000b03000d82200442c0307903025190030350703404007940e0407801c210560700700810700d0000045c0058840031a40c850b4114000701c40d254507071500e02e640b08580c1d8001140e14550409048540100403003080400c030707902e046e0318032510f91602d4201d81c009200480100d4000308c040001c030f40140b2120794100b1199035801121401080da60420a45996941c101141d00c4c2082118410382c040c880c511850030b44040c001118a140e417140d03101c09050b512504101d41c0000500e01c90304460340c654218101c0603080311410b0311030710040e442d02a49403015078001442c450a1548528120105034400c1d0f40341c42c80b80b00c074000001d5141b410701c0c2c2c59050110f41d0898291040d41040014408100207007044100c008940c0760007d03215a481001c5801a51660301c06803040802140505050480c1c0143e06031091090742d00300034800c950602610450300354584141c295101c440180804041e001b104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 340352769 1250 340351519 340351523
    0x51501110f060702162313020706182907120209180a0c050906030a090302010e06040f02210d0e060c01110d050907030b0f0618090a0b09011a010c 64
    0x5918032503100068030b40b42c4041901c040005030311440190040e1445c10b02c9500c0074040c81c11103144034101a0205d01c0c0c0c0c00503114080b07881038094187d0380100300300c1581140c881c1c0d940b200c8248400181910409000a1034403010341b26280700e50554003895a80b90000e01c2102c28000e4143c106840d00031044132850031414591551b50f0b820805513000307647d0100103040714154000d5803005840c080a01e542610182240c8000303116003400400e0107580e810041d00d61000100038005029812410201c0c0548506920504580280401d01080c00409001c000301d85000b5941e080e00c0140c071a10645c908204440841501e4000040c041d4540b4460190030003204401840e06017004210821a03007183d24100705000c00100c00105081d411440f4041c0d9944000004050b010f80d601d0740e10b80c3e4000c40402404440c00840260019940ba40d45918021030200a25990784241c5013141c51907640f00c3c526042520780c08414030010780e0480050255414143e02c60004421031f4180c8401074480080c40803003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 340354019 1250 340352769 340352773
    0x1030f240b070b0c131d15030111040b090a0906150201050f060d06380f0d02030703030503100e0408030105010816140904020c1b0a0f0503070605030402040902030109050f0f0105150111 81
    0x30000718003103038085c80c001b010501c5030003070300c181082481c91802028442d403980c040c1e410540a484000c001000307441c202d812480c10340b6541c0b981c450000d080e03041c0c20341043e890b0034a0050017040d00e000800c0b040400300c00640017049030340c4414080e0b240c00c0c10704035422a40300c0880c075140d20020310b20340c01040d881c0f0070200c1c0a01280d210703035000413140b42c50a490301e074028581e503220484601d49121710700c1c40c0e218265010301b0a03c0712900820386400c0030380005401e10400101244c0c0001c0032030080b2001b048440c12003c940d003424038028056510a2003003900180c060300c0030800e0050142e10101500c620b688030006c840c14643c005001d550055555658010f03400d0120016201c0c05001166101e115102c04d040c0c00038081040100c100f40c42d4110151081440348240015100003840e0f000b03403506030030b103952650780314400a0003400011000030340650824034901c080101c0001e11044094001080d6801d03038003600ca2107406c03200112404011410f0b0f80c1800c4034654042e6001860507030107002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 340355269 1250 340354019 340354057
    0x60b040b031c030b010504050907030509031303050304230a140102030c07090501081c020709020904060b0a0c031b020312220b030402040c0503061e01030f240b070b0c 73
    0x242059102ca850600c0c1e284526401d26400e9031521a400710303007109007841800c041c14400803074080000107181070107250703440f400310324844020016220000321401130004825140e00e00952681c0141c851034409802c0e07004d600800000d8034918030503081015141030318662400308020600940d0010340c0d41517000800941f4000d481c28032402d405440c001a01007990b524203401503140c01159005801c01410000d841c010780c5034003060b43c504907040c0900243c3c8034003603100010020035040e4883e0440d224001500702c12030350000e5807542864003d850340391043c0c401a940c000085200314000350315400200311003003402e41c3c42c0b000d0034003542c01440c0e9207140c40e0310203400b1303140c1e100640202050034404010002149400d009a05054500d407030103506500300744000c50302e0f902c046403507441c4002031101c005106900c0303540020b21306105904144840360703030b146480040c030300e240700303038112111000c14003040d0000280e0803942c9260b4488a603905659070300110070450b412040500000d644808 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 340356519 1250 340355269 340355291
    0x2101a0a030501061805090712050c0604060e09070e010c02060d0605030d110d02010b0919090b070c051e0303180709110a110115062706030615030612060b04 69
    0x102a402851041c000010b13002e00301801110007000c40b05000001904101c00c12903404008250310701222010416051461418506181405a440c40c0c0c1070300100040380000e14250f000042c1c4083d03040650700c01816480340784c403c943d00750040d00003034040746420361140010709024000781182da07030050000980b980c50302d00207070030010001d5035440081c8441010024582092040d0005814240001c0050380c00c4c50001c42c171361102c01000305a1440e8991420482000560841c144050f070113072500da450304e0000030203045080b10440c20384031417080000c1c1032402c1141c000a03c511201241c01141950384000501084c100048a16251401440000180f400f0b41d402803150b500c2e90080d007241c85000039400100b44040182c0119110303810300e0080d90080b503400c403102d0103131b400740e14001d0121154140780303150007181c0e00500301c0244070341c86001401940c5039010809581c440001d04890000b9845c040341a21003602a4541c018040500600007450640c05603d11100141010819074004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 340357769 1250 340356519 340356529
    0x3030f0c030403051504020d031d1018090e0304050d020117010b0306011d220b09040b040b0c0a12180b04030c0b061008060613030f0602120a060602101a 67
    0x9420349045a071021034103208000041c0300402c41a04e22000343ca909107015000681c030080e101c0005002e0019401c440002601501a080341d600c2000c5e29031200c41205220050a410302120a039103004d00d54280400c50024601034480c0380c00007180103609150500c0100000d4020040c2c08070306110071842c100401015004907103000f4050f0080c40c94581c9401c00014105003049801484c201041024480d2207650302c0c01d49115064282501d05100c81c60074105c0c000030a004110705a20444000c10002040846982d2030310a910400300f404035921102001d51040c022103050030081418041d14032103044c007550010729044500108850187e04036260064910010342d03041d40040c4c0c110b07080a00b80320400369a180c1140050329072204040003280c0040544101400061044800254112515030084007080195801c8160b40369046220b25013400254050210941c59903182000074091044604c90b001c100c0d0501e401074180c59401c4d40d003001c0145203224800c0556680d00d65510304584032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 340359019 1250 340357769 340357777
    0x5090a050703060501050702090403030b010905040906020c010c090f03080a14030a0b0a1a070b130b011508070201050402090f040302070f06030e0f0102070c12050c030d0f0e01020d081503030f 84
    0x619000040e05081950004007500c0d20354200c0ba05001c010001100140c69a180040d442901341c079001071214034410040b00c0058280d4000c81d48103080030007000030f001c04ca50003010a0807921000f0006408447c80a0f10440040c0c46480d0038007009807020808250f50303000a103100d0000e40351401e0380b00e1040709130445540003500c004002940d6017014141c2800d0000081c0042d12400f503541c41550040d144015181c81400d800601c0800c1c00e50100b070840f2107000ba00505190b102900100c01d41c0c4034000c110310001401100000152001d010038141030062007000d004a4001d0a00c5110359100c0741402d01b1131201500460452107000c00c0001c4071700d49042400c0241c0b2056a000c1405440800e48515168203928100f040e030344100000d80006003a503900b5400c541d50040551a0540581442800c0a0705605c482d6058081c030014441e50310b43c00201001c031800380e900c2c6c0c140d00341808401260385490381c88800000c45c10040200c0c0780600308407405440c402d00242281c0c9002241200104c031600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 340360269 1250 340359019 340359031
    0x5010504061410030803060127080102130f080c062206081807052b06020f0d0612032a0512040e061f050a03140f07080c090303030103110a0509 63
    0x1d80d5403803180c850040c801185411285030342c06044804e056464405440c4000390031141031002c1c4c07004104c1489041107115071241d90100422034042da883d0740f054080c0d4407c910b45a02401b0103000801c8030500940b0712025500345800400f0414085001e1101030f45c405076190000030343e41a59400c420900c4503010014000c035aa9905440c01c214892010b0218089607840c920307003100c10240320a0300c940c80c0380610311413040e8444d140240340183d00c0c14403500e0900d010b400300e400085c07014178041032030005044141002008100b2180d8a415420b003000840f40c0080c0000d8024400414022307d042c3c02c00443c00c843c0410200700f508695803149802003003d5419a2010081810003640000c20b000950040041d40d01c50341340c00c1c100480d28075684034114824240080032612411140c402d85c401801c001c0f00e2921440c25003000c8c00f4003a2008401c0b50124001140000024507244810050f1030b2800c81c00f41c0118116401d56494540c00100040143e8200240742c900050301c1da162580c031030081d8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 340361519 1250 340360269 340360271
    0xa030c030f18020906030a030c0209071103030106030b180705090108091002070f02030f010c120e030d06030f020907020102040b16080f0a091a040308030f0619090209090f061c0f0501050406 83
    0x10503140305000e0801340c0181458400d0304450782110109800a0b400f42000e541210b00c1c3c00d055445001c140d4090b102c28207202036034440400041951901030784800c0c1049011100880300340700080b41c00212040403108500000c000748145420741d40244103a680003501002510100d00c042c0c00614200d82003d07070b05490180300c100b03115003503050502c1680706001c1c264000780003450b0713691406015030310469030754110940d4501582420440510a4650703502d1030780024405103030b80e070034400744004d28500c0c1a44500701300404210658014400c890460f460496114144035406101c081a01d082040a40c0e56040c200542c0e5132180c803001c020302980f00c00391900341d0114240f111001c03031151000d00ac606403031310400052002c504a1000d4a51180302003244030301035520f1101003107070010035100d07240d03081c0c5455802054410303094010304100c0c403090340d501090703944051383c000012a09890702504145c1001d1000207180302843c890b00c403503008008440b21455a0740e20745003107503403ca50681e203031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 340362769 1250 340361519 340361561
    0xa05030a201e090306060d0507051f02060f0f072001022107030b030307150e1e0d0302040f0605090105040b071a0a020304030801151b0b100b0a050a030c030f 69
    0xa2440001c107200c1c0b0381c1c0e42c0c0301c0b890034984030501299035400003521740c03481014521101b0381042000c01254000d84000b0300040e042d980003810341c0c1004403c40744900c1c007502420000800c04090000903902c0756818401d40c00c0039454260055030808121040440c0112400c505904414000d0004194a0788030020780b8100180101c520241c408014113403004260411000303004a5500209030b40465812a807840100c00c00304481c28005c003c1030404903030034001e803104080700817030030b100350050081600d0941c0c07555607000c60220101e1203180100480122924400d01510340b107000500107400041c103040e843c05803614070344842034116010880e01c4104030040310013410f0209a0044e0045101c040a60460820b80c2d8041d14481d014090300f0031940f0140604840940f1803944400044c0d140b10725108546000d05054101c0c80c002c030740b038541e00600c3c1140041c20f9950501250850344055940506050120307400f1006080c020111904160b1111241c0a072503402d4454003004080d40700ca80004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 340364019 1250 340362769 340362787
    0x6071112150c132702090409060f0504060b0a0303020312070e06030109020a090b03010308070f020310140a050708190c0c230c0402040503070b0d181202060105150a05030a20 76
    0x842d00b042d801400d0f4104501c10b49400b0742d00424080c0c0c01c40c401302e05000d62640003000205004004d0400c2c05007980e400c08001020203a2940d03c03550085000e500d082c801c801080d81800b1048049101c0100180d108206403040c040c0700080068100502d498000302d001400400a00c05030000c1c0c0080514581c0084d5410809400000040080506c10040c60440d80340d03484203505401200c0b0702501d85928881c5180c00c5503000d0017000141100c246082040462a07015040c2d0b4500807240c5460552419010640480c020f04669101d003c0c00c0101a800c0101002c0040180014900c540180808141010b0000e04180d149118581c00e0307031100a40c00e084c0780611464000003044090081d44100802e00c599100461140c066921005070307541e40b00501c1034584020405145003402035031000200f1b10403c80d0b18500c41c058807001e9030884500341d8981d81000b08800e030300410100c043d8000c0185000c090300602c040c6500c1400140c0025082d0204001440311030002241f54000800004800c0c913 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 340365269 1250 340364019 340364047
    0x30c0109030303111303141c0903080702040b030102030c0c12040e070c0627030201200406030b0a090e0604050601090c1b0f02040c020c190e0402042a0e0f06071112150c 74
    0x1008011702c401c08d100d0102101006080410a408042c001a80c0041d50301c0541d00c07640c101250032a4050000c6540f49840000175600384c210050065880c0611511004d400c8523034003d0340c0a03200c14403603a44581e106c80b003041d90007011000c401c491180c3ca441076101842807103107841c50a40d00350620900a40103901d0001e003112401d80510352000c00407401481030f83c0c03100b000d40f410745500b030070000b540210441c0000d4504489a1003070740e00c641042d1910000990110720540143d02c04e00454019980301e81c81c150940e851003c92100082c1000c0200e1803407007454400d40f0b42140514040481415181c0200b0107691207200e1400150f4481c0f5502011030603c2440703c0303601400c08202c4401c281c14449500f00100003c0d002a102c2d5466110059040b80400320b0910202680c0f50503080c545c04111026001150a1104900c6015607401e0b401d11400c01e00c04803105d81d94024000308140c0340f440200301002400340140300c110302c10410048042e1040703407000b90003584490400b039203030592005608 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 340366519 1250 340365269 340365283
    0x206011409331c44221202040216020301021201080606030a1a060102010b220605090c0d05040512070f140102042601140403030902040b030c010903030311130314 71
    0x222403002c030001c5107404114900c040c0c9600b5113103039005400a0414601c548100c2e99001c4a081010a18042c0030b41c807060100300a0100b030003010008041d0381038881c14501c0c42152403140000310450701000c000145855030080c00010342e02c1c0e8642107800c0c0640c0122342283c02c40308124450740d82500040c0102c2001b082103170341c0704000314020840d991050360380110300c1d11000045c01c201c08070039000c83d28580c000c2d08030f81040100600419442d070408850883d101e0040d040c07202d901c52074013601040d5400c0903030445100306000e04080340307008441c4c0d0148008140c000c106031802d00401c000000e5205410004003041405140402d2100d05a4203000203400e801091800316a0310400040284840c4020510603480300480c1c0c03e00007071004c1c802c0e18050041d001c540c0c481c641c11801003204040d050341c042e00056009940410405031603400307159a9a0709c4203842030110b140650200002071084c5c1003142c2417440d28400078200389421941504084164000f1541802c04005440b200302c000c01c520 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 340367769 1250 340366519 340366549
    0x1110406050d2d05060a03080a0810062307050a0204110909010b2a03040305060a0509060a1413110307080f0f03040e0c070201030e0f01020a0e01020601140933 70
    0x40c02c1204404409040005100d591071480f070f50325440000ca8903594810142c00950300b10140b5030b038905081c0d40050880390110b912464502181c000801c80910802c0c8282d5003c28030100030303489000c0d6900314065600881c0084800384216080c60006071540d0181c01d136011001d107482612903d10000700041031074160800a1030384002d02568a0fc2c000300040d00721082c14080002c040301e803040b400e0b2070440c421500f014100340720303c100b40101002c00381e000030b1003040148151000303a2111b040c44030941e1010300218070025810703008241582e0710360800e0074607684544000d0500c69010340103e42070021030307401111a0b07000f03441e6500800f401400150710b4040307004051407a00f03082c0a268040b0110141001d41c00d8540400c2060031640603510042241c1c0f45581210070011100328428040e51001ca02800041c1c900306070744416500001e0118145e660b4034481940440c41d0308184504a24000c0c0503903582c2000c2c100014406181b001034404100d03628000c6070440b0f422000348084180141d281d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 340369019 1250 340367769 340367801
    0x12021b0708010b18060603100e33010c030e030705040e010b0a05010908060f130b0406091e080412021f020703060605060406020c041104051009090c080603030403080c01110406050d 79
    0x1904c0202058804140c1d04c000c0890380c80ea00c90310b60904c1404807900c0c03a080010340b450b1200c10301040d026040c0110018169040300da0b050811078800c90340c0c05c1e501510065000c101d18041a2001038000c1a401002e42006011160b2031680c0304006020307202d07140100078050359912080b66070b5050107030100c0064176083c01c044495629044100ea5a15801882804500300117400300d508014010b5820380400c0d08510814203e013000c2c240f07140140500315088444142c2c2c9401245201181d90f001c81c04650007400f1a41061300e811f81081c40c10140900499101100c0a40301110320b44c00c03640504441c030990300400c0041d080d45018000c4802c01e82109108410038030040014a41c00141f03079810b5403064130042880740b0f0403030a0020702d0107150040d99100442d8481d401c4c032540c2c483c2040048440080091080b0a0000010783e0241c1c0b040e1210764040e00200400d001103802030f801004012040c10000403001c1c6080d402105540040c0c010600082d00001d80c660700900c9800b401c9000340746509 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 340370269 1250 340369019 340369039
    0x20030910051902030a0f06030506063105130c0b031f030822180905150108071e08060c040302030c03010e03041e0e0c09010206100b0a12021b0708010b 66
    0x154080010410303408410301e0790f80000000700f054485800c125454001c0c0c01040c010143c880ca04103460349421a13a56000d1b18180036124050000700380c007040320800c040c4405281980503a04500548001024025000841445200028030402c07100c001800a603c0042d01d905004071010080c41110220000b000c11501e014404904a00e080b01c8001011400700110301d4002070004c007903030384075902160803028075100010302d0040c0d40c2c0103030009602c00d8003505c0319032110214108440c00280100c403210351000a041c0602c0000842d00d09040007040c5160002c29552607003c1d141980498004d042940041410001c604040008042c801000c500900c00000504807580e42c0b8062403142004005100807524406212121000054000054654250310703044181103481d030300c204810f41c0103210344400a0354841d29a80c180050300e1a03940028a000ea4880c0100e908049010310017400b294200003c11040300c1c540140a0800c1d0350030702400c0560301c1d0000403400c4508002c0114011070a0b10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 340371519 1250 340370269 340370281
    0x20f060403050a0e2101020d11041511150403030605010f080f07030507050f13240c02040b040f0507020708010f0605150c1504030509030c0a0e040b0a2003091005 71
    0x41c0c141c644080c05454144402c1c0c551314001303030510401d100000c9030340700d541c9140f049000301900208185002c00005010415118a4580b540d104074440e41c05800802584c1c0150b09201309009050682004200c41300382c80080c1403420940c0094404401099440d103040181e542c200001c804140d55600f4000114a4508105880c481e8000c2c40441010f81c0c0c2d100241d00300e4040c5082c0c44100c0d14501c0c0c45600e411121010307000744105802010040c41070880e03c0d51002e9410031500f03540401c00c1d590182026401e9003031001403c3c5c044040c0e80d1080d1070303102846c0c403e420707413240c07030312501460b401405024a0003540600311f400003000c0346041c5040c11428002038551016030005402e03d603503003a0350341600406003810500a00c1c003400e03410f840082480107256200d4064441c00380100c00356010115107500300140b84043c0c2c843d004c040e4a4940010700801c001c0540944d00040d03200000c2228601c4ca5034a8050303515000840301030b5a0044240541c4900c20401d80c04142000d0808004c10304000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 340372769 1250 340371519 340371527
    0x1809020a080a5603060603160e040c091803080709080c0d06020c030a05031509010e1306110d0c11070b032806060c030809070b0d15030f050d020f060403 67
    0xd0241c40c0318480c514040320450f0200c0042c2084030b01c04a100010745480d80104060700300464158510034440c81c0003085071490301103121000101ca804140c2c855510301201140030150040c0180e46c40725605c800020945914014000e0502d003c00d4ac81540c0451803501803c600c0c0003600e44010029017060611528800064040003900f0481d0000003802c001d00e4000041c0c82101e01075001c500021038080e034440d80050180d0f0041c0c6004140d64044026203007480f1640600b4403e003461104e07030401040b030007000c0c84030409400d405942d010900c0c01303102d0060340d050b0303010702c000f41c3c606956044541d03d4590700c4445a84950b403602c01030002d2519112084105000c00350417500f1031101d081003191001042d005100c01c4d50001c040c2442002c1d0350303181c041c1c48003991030b03010f80102d0341080000384442004508141079581e0080c00a0038502400c61010080c24a41400446000016008808202c0c4141c051609622410050095600082c8024180519460fa4008682c0441c0a0100181e04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 340374019 1250 340372769 340372811
    0x50709030c05130f020a0918020a050d020a0e090103051b03060c0904020a020f01060f330e0a0905102103080609041e050d0305010f03020a050405071809020a080a 71
    0x2c110f502000b440c4480045000a01182c0581e42905100007082c1003d5074000c0415403c6405280c0c4d50180742c00884550801c0e44650380180300014020044100502c6a50713001d404490541d20384154090450703004620401c500381c00c10b03980c07640b0107142d03e01c1000044c0c0820152035405d5010300a1800c264a41c2205030041c40241d900c01c07a00824180000f5100304191142d500303e01000707201c001e41c0c0e103240031004a25401a64031691000a0407080031540b03138040c084c160188882c0310074100003c2c4080355072100420000754407501c41840003d41031280c1c000c0c0390044041000c1440b40514248241e1800150b0355101000407042044100102e40c12880050307000c4006d6680302e0440d5128648a4905124651503e2101107280b11800500100180300d00c2c110402c0d4030f04100e42e0340c07100e004100101d0315100c000c1d4480b110748000c1c809401d2581215400c104d460a0140c182164640102452910364005034002580400c2c1c1c1000c00354007900880c3c21008070352042140341012100d2010141c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 340375269 1250 340374019 340374029
    0x807030e09060d0c21021e0108070306031e0512270a050a0e0a020d0c050a020d0201060f23031e060112032f030a0e0301232701060315050709030c 64
    0x84045e81c180a4101c0070070703201d00031560042c458034444c4021540003504a20044843d40091102c9001800890091242a003034035001f103088803942c00e0f00700420307610110405045409008083c007404046203c0c40180110000902c1c041c1414490a010900c000803005403092190b20b021800704000c0c0c950740945030903244281454005a5500c101c5100640b0038646100384140c9090f03261400c10354410060300803004e00b5800e5540c0c101c2480302c00ca080c1c84140c01040c0d58004502000c0090345010304441c10104104040c406070307480c0c0400041d00386a903081c40300440c054818601d4540303400500c40640504210010044c0c00a0640c40003440748012040300e600c100e50080d00c90580c1c0c200448004944204041103070b99406420400402c0d021420020a010398280482c00e01c0104440858001c440048691300b42035603528110303000c40b4100d00007141c0318083d92144400302c6007001c0c00760310301440c001c0038901e0300380900d55413440c202c403c0105200300f0046500c500341b0010710140340c1103040759 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 340376519 1250 340375269 340375289
    0x170318090a0b06030115030f0e060a320709062307050102190e031e191716112709031b07031703151c0807030e09060d0c 53
    0xa03032801e60103070003001020703041d55000d00d000c000054007103000081e106c0c9800096400740a0704032584400b40a84d0a544410981d5800a00000ba87e0840c81d602c030700044200042e980644901030301424400282250601143c8020002007005294221a095005051900c0e104159591921064044207040e04040c0c8200c5000211202803203802d40540f2201c8450b0f11586484602c1010064125001100803502034055541102c0043e258800000003048104001c0d21000858015400c1c11001e00801100e10052451408c444040010003804c015150249e803040704820500303200d0000ea00041e0064440e004103281d81c0c0d0401a03000da60341c41c02d04003054804c3c0319140c84103044c0c01c50003034502451843d0013030100941c0d0759900003070b08001c590050401e4004250040803480251104590045d402c059424400d031050420482e040034940200c01c030400804010350340e10720503a0150f00c007640006e102d00b0f8500038929010108580015044500c1e01d0003048656034400c601032244252420a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 340377769 1250 340376519 340376521
    0x5060f040c091803030b04140109150b0a030b031528060b0a020c0411040b0f03040201090306050c090f0a060221040f1203080105090105090f070e040c0917031809 71
    0x820385408580c050b00351403605100c9040b040c82e15070884080312070280c0010341002d402158900306071041c8008100910101c0c1100d80c28141c1c2c040c05442e03401d13800c44004100c40000101c15044102070308103113840303036004200da804000405140802d0b800501154482d0078040c0b05a254016000780210400c401c20800c468460402142c0204000c0c0d016060010300015954a07190f40461956041e1104a034104603a40101414556602807800f403800891700402400000c01b020038061684644145403070b00b2a01c2d106c0d90b582098030000e8450341481e400c00324104c0250b01c0c00c0001190f000368150341e411035562418600940e42d08042e40204a0812041c0380d040c0c110600c88101c801030100a00c0c3d42d02c0e542d81e102241000c4040807101500000c0500002060030f2502c584202c2c102d841c024090a00c40e142c5601003280070001a00142c1444000c0c00400207030b03140c902031035850000c0c50300d5020819207031100c0c009a000781c92204d1441500200f01142207401c075000000000c01c3d0076100d241007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 340379019 1250 340377769 340377773
    0x40909050f1c0306081506150702031006031203050c0a110705060a050c12040302060a0e062218231009020c060a1d100203150a170105100305060f04 65
    0x10450301c9016505180590300014009480e5900b400111203059542003003d45d0341c030801107803540c01180014180d40340d0000885c0b00d0745040107180740249000028607141074085d500003840e041d9000c68059080703455040410501c01d0100a0040503031042c181800580341c14204121544503552949003882007605080004500800100c00605000f4107910f564030b40050010700359412440c1554032030f02c41e03050a5100d82d400800ac0c1e804683e805499a41403042c041c03001d40d05108421800d9400c102c040c49012280050111040340c5115054144601070b803c003910300310441c0f01004100701d01c500740000001d85144499001a4041d1062148001c0e038aa00c80492400c22241e03002c98030050020a1200041e4004288a8041d000c1194104501d031200e01c1d1814881400300011a0b203a04004841000c1c0043c075002103500143c00c9081c0401d01e40f1040c000782d14150660812500b40304a24400c006201c000d114594104852203000d1009628580e50250b44207402840646094202004501 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 340380269 1250 340379019 340379023
    0xf07030e0c03030c0a060510080304030201030f1b0c06050a1404060506030319121d03190504050d0606050405070c0c1202041104061e09290c0f0703030809030f04090905 74
    0x100c0002420f4a41d1441d01c0250a650380f9214401510b2540c500700100d400c4a902441604c122018003000c1c5041614580054000341103041c22800480c0e00d410b007100400400c84028603200000f51108907560f000b50030000b04942d0b004100702000340c83d101141c0a20180c2c90519a4899031051021409503500c0b0003181c214000c01418450946001c0c0143c0405504046222100c0c84004010899482c40d04000c1401d000095182205030300104158641d076001540026103003a42070421510b4565100e001c120b60141140c0281c881030b0350303080c0a1000340340600465400100f6031900300310840d140d8a4512a400441c819400b01c2010100040d0442d2510303004905850914440281c4450341c0d180068180030700c4205014074000b00319038004045001e40602c0b01514149106101482484501004003900c1001d003044044028046610b44100811034220f4203082c02d0050882c10b031452602401440003d01205946e410034080319001950400a403000c0340c6040c0c0c40030408180721706103e4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 340381519 1250 340380269 340380283
    0x9141203070c1415010303050309010c0f0f0509150a020a0c121a07091806210309090e100603080901091d060f0105070c0305010203010513021201050d08040b0a09030314030f07030e 79
    0xb421105131100000241504180a1032046481c04024071007800441001c440e81490800130101040603400c6480071948640054440080080e20070f070419100743c821207072a50000f40030400140e03c842e11550401070700c120240007c2104500b2681012601d50b14645400254000c3c901880c4202d070010340058441d03982c5000030007540c0403403030320614510004005010540610700000c10012482141c6c800101003040001e45c2680c1c95492040c2402c64103400382610743c0950070b0503c244030ba20380405415118100055200b4440c040e500d14210f00050950768081d40320300d4244004202d10300c105000886459840078049034044040c0001000507192400366a0020340b00a281d120044104007055001b58141d6070115041403200888108541c2a4800c140d90302e14003d04100040105007813160f00001e00a01c40d80d1010f0a041e02e40340d000300d40d034001d40343e40000601d01a504206040e000118030001c602500541e52075481d01c280b0184e0742400151400c020907685900218002405200c1c00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 340382769 1250 340381519 340381543
    0x4020111100c020a0201090b1606021c020d0e1c080a05061c0f02010315030c03020d0f02120106050a151d0105160c03020901090510030605071209141203070c14 70
    0x2c00c280d8828400c000d60f41e8460540481c0401c0b100c0f4800720b004180314080c0ca6059441d40150070b29550160340781c2c0040c3d001514050740d09441c10b061441e18264a001419000420600010b00024610b0129241209294181a0341000c04004c806080c1e40201c646134409652200446d5070707210540400c588078070501d100c0c80e400300c0344c0817030508001e0b0008074030814078000d0381c081c0109540c1c10b60400d40301640c1d10009091600e0b081d010801820040109020b2900071000c1d02e141040d150013094600011a01c01d4050b42d545207014045031801c0343c09840588007440d414006485903040203000e040c400910014210445aa000c107143c0c40380d01118161035402217003640c40421450310704d00c5680c03640000c0388908610000450b000940b442942e01c0740480301c48044026185031114270040501030801ca04001400940d4001021365024450f00d00344222820a0303203070848104e180c103040c0041d48000c0144001c0080c01410b44d0b000d440760203140d410108820480d145140c810b40b40c00301607020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 340384019 1250 340382769 340382771
    0x160f0212030112030909051003030309060204031703042006160c0306110903010b0301140718030804060e03010b0f0109140301020712082a0d051e090609070602150402011110 76
    0x819100c000d540603c1c0d601e4880c0c2c40340c4060036120400d810984004941070700750001c0e920070401c0031a100f504031060007030042c1401840c081d2a61282d005400001e01c102c18030320000001c0c0402c02c014200704004d1030080d601d141d00354000b020005101440b03010804900c410440780e0880500c5840707170704e45c4010f690060003081807000100305e54855822840180740701f9440c0550450302420107020301d501007400c0c1c4102d004a540d0f844030a8920041c0304041e0b0040d0400c41e40c020000950000080024015540b100188032240300109404d60785540c5038140216840040d55000e645c200b003088081e2038403090302d200410715a00100c0d0090081b2080604016081c2c20082c0e40f4580020203907008070030023500858000101500d40035a441c10f64003611900204201e41084030b043c4e5408980c0007103c1507003008412106c9941002060310179a808091500034905119150b4010042d4000500450024000c0141c0c2c02075180981000180007030f040c4542980f0800440a040c0b24142c0c001d042040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 340385269 1250 340384019 340384021
    0x6070909050c120a06090c080402030703240f1b0c021011010906090b040515010e0c030612030c0105071b030503011205030405101701090e0a030e030c0a140a050405160f021203 77
    0xc03134030340a00361512030301499628050008101d0340c8504045071041c1d030041e00820b0041c3c5507940d050705800080b40b0b2056489030400c072009480009010303074444000c810001207601c1078a8040e823071541c411400c41409018085044a006071100106108110164141410002045941140501001c410003440c0f41c0c64209408100400c0444480c040e500170303800c441140204668880100c00280520383c0c4181e600720000c1c0404d0050320065600401c05030020314032030418800d01d0710b10381100708032a9044c0d4680f820060f00a0f80405810542c0300d240406c1074290040d0f0328090b02920040c010704082c8207140000710103002040080b0b80060402401000352300054140050002105151400120b01d00d1400000c41c0c03a040d0080950042c6070b0703800751042020701ea80070703540f0102c283d650a07010300482031091004d554103200791008044030750031748034142006800c100100055420180c1310f24980000d00550a8003040c0300c04480500b81040081652951004d80c9801c10001000c00e408074004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 340386519 1250 340385269 340385281
    0x7050109060c0e010219020102120406020322051315170708060601050304030806012d091d0f040308040c03060504031d0f060d0c030f020409020a1106070909050c12 72
    0x5401048000c0c02000c003040105820703041283c800c000680c846005138480d449130811a0584180100140c0c41401286d4a0804040000c02076801c207901c00030240e0008a045106011642c411543c4095000c100c13051a90800c0c1c00658a544003070421140c00380c2d1031a28696410440c3c101101a04a02e80c0c4070301e10462104c1403694a0081c1d00072900903010b4500841c2c080d5020740181c030f00440c2d041d00c2d860004c0d80c5160044880341500000e55000700c00001c1d0000c0b0742c1c003507803842a03401d1003da61801c40341800d0502c401d82c94014410942d0449074a0410004043d41c48107840b50001d034140380200c002e48407400c4c041d03410050f540015140903e044180010940c110320040c0c0c03030002c818030024070b0000c0e107410420101c039032400300d6402400c100158281860207038041a5000c41c1403d00140c01d26040301200b013280c0103604610400703a80016480c4000d81c00c0143c00280c0c440b108020415881d02050040c0004d03105c0c03003140c2c0c0311921000840c0c290300480e02600c0c8500d0144080d544289000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 340387769 1250 340386519 340386521
    0x30506220602180a17030a0c0809040e0d0f02060c0433021006080c031209010201090c03050705011106011a1602030d0c060c05090108130507030203060103060c020c09151e06070501 79
    0x2003a4091003403441101c000b40410b00c100c2281c0c0300b41e170b1080c061400d04540c0d503004d40d82410483e030100c80c140000c01141c01190780303070b1241940b12540c900081003074070300d44400540303984c00c003481100c150352048041000d110180400c5505584607900148030a0081504030000341d000c0395003000c04913403240300742040684d0014101c1400b04e00342000b032040703603034925034207403601c441c5003c1c290950006030151200a112030300510080c1418030001519400a0b01c6402244120344c0048440b604040403c100b65070340003082c034a803100c2e04009000554500101c00c41c24000040451940b4038002c00d95181c1c407000c100c4000d01142d005000d480c0700d251524401494010003842c2152840e180c03440080e00640300d00c05488100728180c50700d005036250346890700304d00e0110305403c80312445200f10100060300c0502016008510031180410691084500641000700b011446c6000d0ae54000c20091031464000ca81c1988540644101d6040908090b10048003054669100d40001c40081e4501c204441 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 340389019 1250 340387769 340387807
    0x30405011b0c0503270a060c0b06040209180c07080a020609120315091026060a090206030105040c1103040807061202031b03131e0501050709030506220602 68
    0x880300e4000074458418020703a590600700b08041c1c265441031040140c40c011810f4003141031881c11410f180301840140c0001c0070075900d508a64001143d100d0041c081020344e0150700d8100a04440c00d6041c00d4016011030105845194100701c00d81a0340e002c100e10140e07d0f000c0b11500760b0002580c0d0350710452024041e69458040d2010929072060b140040d8080c040d0400343c80c010900102002d0403040f03400b0420000880188c8a40d60a501003440060b180b491040c2412503c42e8100100d9404e0450903985410b094000b4204507800d030410000900503520103084a0560307034101c1e00010026180701040b56a0b52a000320040745100c000340c086065000010a131084840c075070303920200344080080d01c800b640030a0b501011001c403403000301c88003402c0000c00b440c1e0201011402d120692520b40b12210070048842541c2490701840110b4004d2280a00031241e112000b4144404d02c1440c56035280d9540380700600d0300c804003d000103c2501d0001d96178640320360a030408019912900e00046214a100d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 340390269 1250 340389019 340389041
    0x70c03020c01020609030d2408070501090f080601030305032a03011716121b140a0806040b041415040606090b030d1209020a0306020304230109050309040c050f03040501 74
    0x1c5000c8690714107610000304540702e10380d42c3d00514202050184098040c1c00c5161040c2c83c0e07114100c401c00128454031a0320b000070803003d0014108940340c500003400103091600710400103c03c1c0c960501006030b0008490381140c0c1e061134915030f2651081e41aa61421000c6032a640d00c00e1141d4649201280d24009941078615101049110314001e07018240c1e0351440443d1949901d81120080042c0101c5038609184140200254880c00c0714200503c240d490480e001201c4100401113640c40a040014140000d011180000c003aa81060b4031000f4040c40c0042c0001e0643d07040070a00d090342a03084c803441c03106100003c49100c0030b042c2440d040340540154020440250302c0c080c41c4003004c0c07400003204280c05103a5210f10720581141030150001d4001d80209030303000031595000200181c0144015445a8051403288030300205406092964510000071410123a040003c1c0d580071071404811201003440031039000030710f002000c1301514940100300503030b50707207000c040304200910006401c5400303c51 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 340391519 1250 340390269 340390273
    0x90f030e090606120613090b0a02130b0c0c1203091003050f0708040804060c0302120c0f0d0905060409020c0a0b07020a0c05181609180603020406171c030212070c0302 73
    0x2682e20300a100141c0101072460040f03007820b2012070040d040c0802d100c0320520000f100030030030780055110041910801d071801c44c031142c1d0000d90068031008020725800504541140145400501010a030f55170b0b140003007081c442d6140704c0500d2030b5680200101ca5600801414540b843c104100c0003500921040740c203100daa80040000801d00c0e8402c3d0b114070320555014007030504090a040c4210380240340d40c0c908a0a40c03154030740d10b80c00c241e183d001a11200e8016802000642031001d03503241084000440740341031020025050240b60740359002d030f40c01c0e50104080180c6400055035114a00009142d0207040d408442041c400d40e103901203041c104050091114840b0709030303200240102c4004424580007030a41e40c1000c520742c4500e00d0000b1000d00074038685035142d161a400c20700b454159840198142a50305d17142001142028080d00c3d004200d00c070030300c0901d074a110b00701c907480d5907440740304847d400c10404100354914043d070b0540c3d018041070448000c05152950020308a00c0c103d11040c1c000d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 340392769 1250 340391519 340391521
    0xb0106170604020708340c061e08010909060605090c25050a0201081510050d06061e0809070b1c06050405041109070e090c1312050619090f030e09 64
    0x60b04260088030b0040d5032120000d031404200003000e000d0f485080848455051801e00800516030503d228840b040d80a007a184400c9403400501a0221201c0394031002252840000a10480d8001c00c00780d0441c0d501c02c43c003240c02c070040d142810081c90700c0d80200e64000004010301c090000d4100140920301c504a248611001c0750021004001c1c01c3c8030802001c1d940040c04c03001c0154800d0031640c0d00400c04488126800c4841000a86000403030503251001440210b03c468900b2150302808000b400b140c100100a294120715004024100d10043c00900c8a41030204804c85400c201e40401007015250468584e95020b202c212a20001d4116074651800d020010500380740078440d06025541c040f01171203403101c1c02c0c4237100b00c40c0001414030003030041c008000345840c0c0394030b060b070b5215080240111f03540d00783c1e41d100c3c040040c4c0345402c44d02c9480ea8600c01440082c1c0d001519942140482da48150b070300c0807106082000c2d00030508000c0500804600300c10801d0340007104100080802c90b011001c0d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 340394019 1250 340392769 340392781
    0xa1205040f15030e0f070308250303050405010501050f030304090e070b0c030a17070c0f061d06180a0f080d0b0a0e061809420103140106030c05010302160b010617 71
    0x140c1c8001c21720443d1160880a410000a03181d90b0045c00c5440c407030391036039a11040840389000201c0c1e000900b500429200d404104c00c00c45c0070301c9040d001d410101ca407840742d00d800e01c0200755a80518000c40c10040c0d9110362480c03030300800700504002450038905099456084003081604c0760029504800070924001683c1d60000900d1f40280c440c00310340d512a00040f0180d100d041d0452041c0030700380c800f1a611110100b49000e600040c4900201c4080103003240c2c10b000240c4200540f215403002995081494880000b6204096190502ea0400b2810380c4884032a5603840c01484001390269220602c800c00280e07003892005880d11425040390701c0469162040991415403070111a503034000d4001c2555140700c840003020b405040042d90305d07203800c00c0300410641040c15107241455001031005100400401c2000710100e43c902c07002e400203100091031a902e099129009010b41410316401140c03a4250096400a02210503003004a032110755960b10f070041c2c1000e15040340868504603c00c00685 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 340395269 1250 340394019 340394023
    0x709030c060f140d090203030315090f040305070308070e0a1d1b0901050f1324020f0606040b1c03030b0f04150302010c031701031104050a0b01020a1205040f15030e 72
    0x10a280d9a1103d03c6891445082032455501c4600030002665030341c10b02c40d003d41c904001952142681d04120318001c041c410030410495001809420251800010080025442030a446085505043c010100d4450603001d440c010200d88045401011202c00051000d0740d103c040b031160100100901030030b0f00c3c2d540c021102000d0040c015030708100100400649944504005c0440301041a200b0f03051180850f0400c4c1d445903141e000e8840e1000380800d03041d03944920324038a9070302c180c0c6000401030100031240302e030b81b03407a002402e45108568681201841e61240c0001641d001040c0499040c05441c520b00a00142241405240640041c030000c051504040c032912640707200c484072008070503180d9801141e00d480311031000c90810000d86616100e004540c0310050103984a100901464102c140c00d100c00c5400090940308074a06000391546943d8001c11071605d40b90300030381201e81400840d4020b84a510984d4810380038603030b101b5400500201c400841052070b848669040c40500b0180329015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 340396519 1250 340395269 340395287
    0x3030d110711040c080105060d020d0227030a030905040b15030703061707080a12110a0c03050d080c0a030f0e1518060405060705070203100903051b01020307050f030c0903060709030c06 81
    0x1401701d0b0740840184440d02d0510082c4c02c0340101440054035040c1c640c40c004060740c11664100301d410000d0445000c3c2e19a22010809a54034103030001c2078440c1c26501c0c018400300440c814140a46e96500804815445114040c5c0842c11805172055503400c0c0200c00400824285c4200d950121a0071410300d0280000b02d52003040b180d24034020601500319840f1628506007201d480401d00203807500344085040c05000d601c071541e0080340d0301d01c1c203246903050807800c140307040e0301c02c01c1003084020401c5603409142003550054029071030001141e501c841c200d40d0050901017070b81600c41c4070f84c11041103000c00c411130b514410000c10000c5034505851446003941d03500305840003821030f000304001914941c481d4018004031400202120001e180303014030003003107030310080c421790000d6800500d54401c003030a81c40800700032042c04005c51075864004401422030045c041c3d61031b4116800004281508840c2c4256408004000e00340c2c1c0840c1046280030b0401e4840381b0007100c000312135450000321140070b60242 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 340397769 1250 340396519 340396541
    0x30705060301050328020306040f150516181a090307120c12080f0307090501031a09070c030e1807080907030209340201021e030115030b03030d11071104 67
    0x280a040300117400d81d0728680c054114004010301404011000d82da0821030540101d00800e05010a00c1e00d50811340b02c01d41c0180803d03020300d4100707000e00034404a000500380f5505007501c0c03c0d89600008050042c1150126880f034040c03c280c0072945400002c01100402c0340150850031540d25a03683d0b88000c0b103983c61600040c100c0505000708000312610030a010030440e100700c4110740380501c4424510b407560801e84011000921150003481196014440d080035010a51100020041508009501141700415403c1003040b45800c4604150040e91251840301d40240240000b6403403858056007803100f03c946800046008000c01e03074406003c44c0400c196900a04202010340d03400707460a021020b46400c08103480c1c0300704d00b801c5a82e0300c0251340079000d060a43c005a0380d486696261040710b507021a903c42800c44c10801040021501980d40c21ba05000d400d0104440b1070740c100190450260b5001045c44c18104903144a07220707862401002c040344036041105440040e0424442211468190 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 340399019 1250 340397769 340397773
    0x40b010905091501050c030d0903030b0d0b0106030c050714060402010e120a0206031506181f120f090506101a1204020f03010b041a0301060e090d18051e0307050603010503 75
    0xb09204503c60400b0100403c4181003042c41d0100c4940359502d1503001e0341014944955500c4810201545806035000021041f07030301e99400410b039114070746d0302c0006110302e105150341c4541140e0300307500600650300750a42151010012041d45c481c2d840d00c40c8001c4501700d0004030000404942841c0100c00e00d00f00e07840c1c0710010b05001c0f2407036081c0140342d40082c189043c100050081044140d0704c0c24000d040c00e10341440030812041c0040140102c21061112118421801034140500181e00c00030306803600d40c0702d04000c80d00880040d5040c1c0140745080028095000d40c0040003a0740c001e00202000701c601c0401c1044070841c115100e10789500a50144000214201c0003180151500c2c03c6008211000200006400e500c010f0015003102d904200481d00f4607000c04e0158034507c0d00b889920001c05e4181d455600c00d00c1c00820143d1036400d0000c0311818030010304900156600003008410141002910786400354140c0040c84240204684509119100300c40003c200c604000040c0c0781241e6001e40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 340400269 1250 340399019 340399021
    0x10020309101107150207030305090606060d11120f160201180308060a0801061d09060105030a0209040501150902220806060f0d0203101b0e1011010b03010614040b01090509 75
    0x1d0280c01500e06410003404054040c040403001c2007100d107100ba409000740b240142d80340ca051a000e81502c9004140c44c6032a00207104111031a1a005c7c121100001c0051340041d015045242c800554000d21401d03184842c502400c1000d582c00c800800ea0080010010b10140c0044101d401c9003600c19409424100340000d02d500310010707004254494203d40002c1559031800d882c2e0551908561107644040103409030403501c0c112042d0100303481d80e040030038100035000d158105004280d507105045002405940a10002010700000b9480010a0058411401189960303200002c010f500a41031408051944220f8004c02d40c01c90350a64048904190151049a44540030046100f002ea0511a08004803811000069506100c59044202443c10014030700c2150480c84041c1380055100c00e0070300ca2101c2d0801010b55a21240d02e2614680340380c40c0005000c1001b0f031502602050020030f80641c2054008100210b500c03054070604202581c3c00c010864191004580c0640e00788070f01d9411040c414 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 340401519 1250 340400269 340400293
    0x815130b0103020c01150f0506030c0304230a110108010b0304030e060f0f12180a081603110d080f07090e0105040903050708030c18040c120b120a06020c10020309 71
    0xd0001540310105040050402642d0710b4810f00303440d51040111140a902082402070302030f50203003030016000555001e81140740030550680039110240001e4107020828603814848008107d114100308003003010740301c280545241014002e282001c009002c6030100002207050a0000c0589100d2501540c411440c541c0002c240f00d06540020701c1d107040320713008121f85844945200000d204520b4100031400091502c00c042c20924030040002c18265080484000c0229022106072010801008150745287d540381c5019180480d03105484201d034052030959800c0340d504403010324172502d032140c900c0030107039a002400c0340c82d01c8042c065a4101c121000040c807060070154000d030a098424140310b494021241c031030000541040ba060f40102c0c1002601038402c1401c80b06420a034881980c040c40382004000740501032150080210400d01d59800311920103a85400c02007a0b0401003030305890301108182802e9010358488404907070300c0e10418111000350003040c421a4800c2d54910080d20302110f481c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 340402769 1250 340401519 340401521
    0x5010524010c020d021c03051315080109180209070518010f0f0c05031b03040f140906040902130e16150f0507061e0c0201050a050402090117030d020d020a081513 71
    0x305026a0013103046c0f140300d6113140384c1400c0155524041d489541d1101840381d86a0b2074140160800b0301003168050205101c50b401c408003a044d1020034801281c80c0b00e4030250300d080b0101c00c8901949c03103c0184280007515801c040208185a50b0510301c4010b865642c0040d1083e2050b4405c0d0340000c0c43d0348448004851007802070019052080c000c1c2c902d070105100c0026080c1c00300021030851364000040801c00c40200c40310f683c004282c21a920380c85202d00c8000141203c800401c2613010715143c0f0100e008540c0ca00303105d5000c02c03000304020000340c580714024964506212902030554044844086550400c0c081c07001840c03041d55076044034003400c0c0b800843d205c1d00811300440e24181c440c080120200d121030904c100210902c0c500080c0300980d048001e0070f680d800303401030320214a003800344801361b1650f034007072415540d0b0000084c28041c0403410407407a602c907886240c43c0e200e10111382000122440d400030200e9502e1681e565645844001403046880202c4e000750b03500c13500000c100200180d00e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 340404019 1250 340402769 340402789
    0x40b090c0901120902100e03070e040804090c0224060118210c0f03050607080718060e0117040803060f0a060509040c140a0207150315090b0301090f05010524010c02 72
    0xb403040404d510500c1d90105110640c2d02c900f071008510348480800203410200440c40007410a40308800d040e0a280e10b034016240701c0c4c1e0144a101301c4d15030340e006c5d40c0c150081145e0340b5041000c3c45505910240f600074002101400e07603019001980e545100c11041c10340d0045c0005542c0340d00079005018140c0c00102c0240180d01e20200d60791a80b100c000a100a01d90103440015030244c000342c90b2a00e02504010f0514800502040034015200640d4000101c000701d92070a440341814111102c0a8010040c0d5102003020010f10410000b80104000c210620380914096203044d076005008410400800101c01c0301801640d000602c1440704015900e0a41c2201001e1b8030542480c2d04c0e00200c0c041020002d82c02421004050303409407404220400058030512203594176860104010054003a00040241051048070401078480841c401e00340c0c0c00b035224003262684210400c034501840d03d48a03010740310444486074504400e82c128015111050181d1840c410141c1d034801c0d103266903908101b00e0643c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 340405269 1250 340404019 340404047
    0xd03020718091406270d0804080d150302040c051c090f0b0915012103030207140712050705060306180a2004030623010e070c02030307080702040b090c0901 68
    0x82c880341d0300008280c2d42c039a0f483c4408085005006981780c68a0385003d101030b01c010210250780c0854811000d40804552000f01a02d94075062585d520b031801d00c1d02d02030054038001c550103454402074440c450302c00b400b01000c81e4803e490611030303410100e10555042c0034002500d0806920080224041503c607031041c04580c4c0310303c0c0b40300301c44895a1100101c201080f00e0711809a4884400e06000078602030320351b0300411040303103030801001c034840c0c40340320174003c52000a06158022410360101b0207000300344a0041e000c00c003140c08180c0e4618140c0401d02ca618005e503480d0203140d2021070181800c1c01181d10442003d040041030001d082d05600034040010000003540d540e6220555010700c40c40c090545030003078014a07a895504604040c01124031404031016851040b12507100707410420707c016411220b4005111034641e54203e001d540b841640c81000303505010020701242040ba040003d0295540203031000c009110002061011080e070036204204090424060000150b104000e1055064 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 340406519 1250 340405269 340405271
    0x20120f07120f29010e011b0f230d02060103080702010315030b15010905030d05131a0301150813060203090705090f04061407080105150405121b0d03020718 68
    0xc0c4144811500301c6500108079038055841c0c500325100e10f82c0c07021109a084a0164042c2c0688118600103030200c40c2142c0c050781800100600c0100710280d20381c0e4102c504c2d4000e1200780340c10129103080c103003103038450150a241d24142802103000d200006859000d9020395001444507908613168406603400040b0200d040549510982c0c005405122100c80118803901d243d01e82401c14203c651a2503642d2041141000750442081007250744c0000d8004080c13105003003165403914484100008403c981e048482500d400c40c5002d1150100380004504a80403402903074602c43c5007200c202d41549055a02c5007008035a104250081442d6900440d040414001190922541c44000c20744242c0700329418105000b213442040305000c0640170740d99012418103e080420301e01350102620000f01030103000d008226800c45482c0e0a54044225806003500174060230004068025a45d690140200041820f80342c0070307010712040c1005a452003840380c2c140c004e000f940303081001401e900201805211580313 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 340407769 1250 340406519 340406537
    0x8010518060708062215090903080609040c120302030d0b0a0308070209070513080a05010c0309081b07030609230f10200c15010501141206030c03010c020120120f07 72
    0x4100300701201e2170816414030001c980080640b06800b0304103000d038440150b00d41404a81000a42d000140ba40d00220407240794000d51905c1c1800014401d40d0b0700500c580004d645032a000b030580000140031172451918091100350003d2003403140c22030700380c4001402510107110190040c94030042e4641d02c2402440c05909100b000c5d4034620f984911a84840c00039080074080406008080c058a1102d417821b04090140d0302c3c20350f5403450584a0b00c0449441903080b2012140501001d200340300c0216000417051020304840e003800f0681884480341d0a400140f05101005a0b0744082162407201c01081c024141501711541c8400103440b002101d4080c00c0e110000e00c0140d95581e001030080008440c0c01032035400d030300790991540500c040e007099042c80003020111034410790040444258098454541d00c19881d2400401d10780341e64246250b07495401d040d403000030140e056000c10744218000c0003403d640c0039090300d400c00c41d00c030f0090804c0c4414030010005114804440c0001e400400c645031480c03013 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 340409019 1250 340407769 340407799
    0x912020d061b090807060203041509030b0703020903010f0908031305010608060a020c0f120f07020319060e1905190302190c0510030209010c03140c06010b040801051806070806 77
    0xb102d031142c80920308210107424207030107180d00507050009094008020503181d410120040c2d078a0089224050010090440c0c690685104c0c507401c50003140d0110100c0031604005402070007035006503041d9402586803200900d03a2003150b0040611440c0c03c03003065032a540f0f481c5806501044000801e5640f07640b610070008020004124071446582c0d50341c001038a030889142c460341401a8190f004209501a01e40e581030080030804880c000317000e032000c069640d072082c0b01107414601604007005280c0e007944180b1b0107200c0c1d036030015a8044002419a03100d00790f000600c0052002000d07001c5d04651000182d030000e10740b40040b46226030f0181c0100e418417030300b4a00d1450a0303851040c04070b82500c41c4207030401950a20801c02c030907802c45130505600340074403000000c00c01000c2c44009010040d015101c0c1c4104000388080b11103505110080c0c0d03c40c1d40e11344040b40c0043d03009106844d5250b290000240c01d2040181400081c00e410402910041e16085012145e41c0000780240c3d6002c074004400c000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 340410269 1250 340409019 340409021
    0x30f03030405030309071a16030905040c030e01050a150513091e03020c090c0d0510050406030b0118050609010b071a090a05070503010c0e0904060f020f03180d0912020d06 75
    0x7114030311400045075079140061240341800480d07031203a00d401045400c1c40354000d5041d4151034040741552545036500c1c00500303040315407d01d00e80c003c5402614041d00700c070515926410202e0900c0b0080024000c94441d1000e00c0200e852403203164400110404080c026494520166003908891200c0411110641e413100350b144940c4018508166100e00c102c4420940c060200005514080b5800e42d41c51400050040d82ca200700910083c40607554400150703d074071000407580203080050410410703540c603803400003683c400a00543c0e5040242019000c02d504c21402194441c40e4060031026981c4d1a017071010b482c5410110040710017203043d001c0c10050244521229201c0e01c440001450810042e040985c1000159040329010342d05183e1642c10103500400740c0102a101a00c00e400c4c81c0c0d40c1c50074540014080c00c070a581d07115000003491170100c00340300055030140c82c81206020b0032100c1030864035aa440d0071000740e030105607440302c204041e41110851184460018140f9201d00c2c40035070300c0d04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 340411519 1250 340410269 340410271
    0x206090619120e07060806090414030307031401090b0a0614091804030806010c030e0d02010917010c0f0e0d020609060909190f150e0601021203091f0c09060e030f0303 73
    0xa0005506000910207840c01c3c1c001d20041090b9a40545599424003500400c01da00c000d080e94020042c94000c0360800440d1454061608416410740b40ca2b4203126400402a06045030045d0380c20301e01500101c0c1070145481000d421580040c0440c101510745a01540c414080036403003061948140110306558803600710f541064851007800c01101d241c2494007600e4118090a03550411803c01083c50001e904506005420380c001c5945c100754040c180700480e201b403190b820692540302d1200940d1580541504601c0d021b42d02c2d40c6404c40c8944581d10f04541c80c4076a10809030b401980200b2540141c2002801810103600241680349402c0c07400c408100b24200543d9007540301c048883c985d020382d40071840756105c0d04496010038002030b44074000c040040c80341c0c0d008010025018201041650780200075581140e50304080054880ca07084150b5621102002c0d6805900464410440d00d802c9061040b420109104c0d22003c3c01e03136082c07200445100c2c8481506a07010320841c0034414003000c0400c055 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 340412769 1250 340411519 340411567
    0x1308010903120c0c1b030203010f02030106020f030304052a0303070c081614100315030c050f0105040e0a0509010605030313031703060d03030903021c050d05100b0702060906 76
    0x3040d54201458000d06040050030100c952910f000901d4284030340c004190707600f00c2d4200e494031100c1140c100305500c1c1d202650340025490b40c40d0140c0345414507001d8001d58101c2d8080d8017a541d120800340000d54503440308540c0202260807503140b4010261030815148420110b44494500c00c00185011a01c1c60f400746100355402d05060b04100142e10040101c240e14034040d10140d8040c510740034400045040002000c0e100d040409182c0000314800c0d0300600a0040c0a8404500c103035030380c244048450440d00038203001d840382814041c655401541244c04039140076070384105aa80f0701c1c103200c00070080640b8410041d5215403001a2a50f800c00244c46851101c114101c4036a21310320f800d00503040c00301c609030102c03201401085503940c2e421900b106180e8141c100440c80c0240e51908a083c044030000703c003503098181e00c501e0100c40d40900038007040c04c240c0c071040015881d42c0c1d1400e42d803002d241c800d007188140c0402103000181021400b41c061200060100c5042c00c0c0d1034015003400f440c0007244 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 340414019 1250 340412769 340412771
    0x8130f03051501170d03020904090b0c030a0501050f100e0109170f010f1503260d0c0e0d20040f0203090102070309060c08160f020d0b1611060a090503130801 69
    0x120481d5160750000c290041104c0410303440702d2500c1c0003032651038017894052142419400300c0c0301495030b2140c0d0805600c0310717480035000c10b0510344003000e00400e40080d584060040c4c41d10001140505000300140b084a90043c040c000700080c403035040307421000481950341085035505002070814080320f6030709403e82003200034100c250498034500d03007159110400741705080d00700195a8920380710701c0c2ca05426640c0007000020b4403e28841b1800c0e2040c0040194620000c002440c1c002e00032941e40215045480d55562003080540d003000c2240c4001c41c080003800fa001105524045030b04103c0d1003240d2440302602c0440e0b0460004602000c81c0c100700c9000240d650000313410400c1550010b1f604018081a0921800c868143d80700e0809078015a000307007104101d5a00424248580d0040002440d03900030001050076889191810124000b503814481a00d080c02410701040d00842c0c0b80d20717010009100400ca00e941d85203280f0050410a00d064803d800100301c80030305c4041850303d0102030460800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 340415269 1250 340414019 340414033
    0x1603030b030c0607020a0308030907080f06010312081021020301060f140a0e011203030b03030c0703110307060c0f021c0503070209150105034002090604090f08130f0305 74
    0x420701d4102403280c0100c900c200c404115501c010303600c0045550030350381c0000b04180c8998a000100e45403a0150300542514410100c110010200c0022680c1c1070700d01c12140241900c41c0d032581070b500740304103890400003100070a40034410f6002c91040311202806080007001c52200300d8012a0031030f0f20a030481c0c0d244083c1d60000f4408401301d070140d00701a9a01b5660590800d02d8a100b16a00041c18080d40d402c41400300074a03414148240c00c9514030b1385004041e01d6490144400d0b03640e580c00e036440300720350b41e010481803801280350100701c46007103581c240c880c03040a01c842c1d5505881c0c1d92072030800303e1f80480310158001d0310103000f418024086100340e00540d6620341900400080040041c41c942446009100d50f05051768803030266900003140058101e08484c4030b040e013001c0544084510010b0440c40c080360300c2002800780c4520403a900a80f1164116103507070050000342d8680400290400c0c3c5c4034681c1c4000075110800900c0461689a101010302e921800380d0350160849500960f403940c4060 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 340416519 1250 340415269 340415291
    0x40b07050c030d020a061104030b09011e0b0d030309140d05120903090d1e050f16090203041a09010f0513140607020d0309110604030c0815040308011208160303 70
    0x341d80c98260440c000c002070344405400950702d10036035100400751520740741c0403007685510300150742c09580c0c0b00d0750b40c407040c0c94400741e010b000380303010103150070f002c10705043c221a03400b090710581000c100c0142140500e50302c261001d1b009080b00480403910342c3c990440c90f4142010910a0000d091503558600340e8070040c90110244044025103070015980042107070100c15601c00300074940d03050303000161071411450a00c0360340000b4004400078040f4000c0c090a00d000c0ca4010404d4180c5c4050320900c440500c0e102d04560049000469001f40504451543d48a4503000041050703400007950002240040c0b02a44032000c3e02c009440400722810078030755100801c0601c401200401a10000410031403611201c025950a5444894414141c2e109042000d01c40c45040604e00380f6000b0304003564881e503900d44613401c0d41043c0710f170002c940109825031072501c4081c180b2034004c5d40c0581d907041e8540d01301040d0b0402c4810103a4201d5003130004005000c07541240104201400d4021707200025440b800d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 340417769 1250 340416519 340416523
    0x306021b07140a0e07050c060115180b090103020f131211060a170c04080615030601061704120903050105150a080c011706040b0a17070b040518100902040b0705 70
    0xa421055024800001048150b142d14080c0303001c450181c844c1800d107031150719040d0360318460a910041c250181d030002103801c44045641c5100805690b546c51106081509461420070003401002c035604010030404080d5072080e0080d00102e81c007030781c1441c41c0013000c0340791040a01d0940d0000041e049a02e0846c020300c8000d2401e1320b411442550b01524004c2e401000070400ca480214001d04090031030085403a45840000341c07000307070040b10111040c6080c162000860340d040040302501c41c1c80307180000304800e80b00380307030500720000d41a04254503516071340c1d2400401d03140325288070304000a850002003c940309004050240b0340890341c42c0310581103401404040d10035604000010f521a00020b1000e90303108420245c10701802003c0800340c5c8482c00001c01821601c09051f511480b0820080359400040610801c0d04a020f003c50341d2643e03030b440b1000303000d015078404c2d554081a48104481600f04109007030ba4882c40758100d4010b0107482d580f032641213811036004003000c001c000c68400f04120f03007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 340419019 1250 340417769 340417783
    0x13050306060d03051c0b100815010203042913090509010c020309010905061602030607050c01140f06060a030f0c090326030610090306110904050f091b0a0306021b 71
    0x41610030509000868501805620a0b50b0261020504100304201c044c03551b6030128268004c01400c1841002088900400f640d6040d201111040341841199920b580000101c60407250041e13002d407000c25141d1039020a9041019202214110412598907040c0c0b8580804019042a903c00112418540207103402c44d20b1b06101030b030940d4410404080740e0f03178124441c10116681102c0300b03030340c41303c100c040c81c905600d580100039012b01c00d01d42440140d6030000007800c69003002c3d000800c145c0031065074400a105007038035018542001c0100ac2000e42c1006001042106828180485c0700342c0803404520403035054660443c0061101081072080000d210b0740460b1121403040200c0740f402082201c400740d0310000c0c1107244100e40c0d00c214285078500600e41800115040b420400121010840402c0305a0021042c244100d281c240091078942031803050030300584100c4014800c3d41c020b20007203981ca581300034046e035218504900010004480b030006150000380428401e5007202c10741000362800078 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 340420269 1250 340419019 340419031
    0x4110405180c03070b19030902030d021509010203010303050f030408070f150c0e03060106050a020f101e1415030c120a0605180309010c0c09020304050c0307050f0d14070b13050306 79
    0x420001005890840c0055030040300801d4180503100c1c207000000c1c7d00814413418025098010001748040e03698000c60440048003c0c540088260341d21400071500701d10007400001c01080040c40031203210345a01024541c42303442420320038039042041d12609980c11007070b901141d081c1c01c1409000740090071402003100040d003500344100c4042101002130b1b1220030501a03902080b0b40841e01c01d40c0c4074400c11070040c0c08091282501d010780c50346150140500070807000c00790800354400c007102c1c40215500c04d07030010000540704400c2507201c684d0280c044500344010107501d8410040c0c0d1507002c1c4e82d442c0080204a080000401c9003440924100b029510010010407020150b0482e462505501104940d0b4611007482e055800300c13440d00d04044a6400c6030403401c40301c2d00c08010041040000510034041d603200702c04890743d40c5d6032001000b0751014200003268001098511480c000b075400c180c00702c03401545030250307036000351070388000802a0400e40038a42500300d00f5a00300a181800e0100c190490 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 340421519 1250 340420269 340420273
    0x30a0606061202071106090301020f0409020304020307120f0308102303070806040b01030b0702030f16020306010b0a051602060c010e100608070e0f1305010c0e0f0405010f050904110405180c03 84
    0x107100744c85e0040402c6160000d5801124001241f0740c440da020360454910701e882611064580d030300ca880070402500112022802407003402000304030a0303c3c00c2c0700f40307403140d5001403560791104040d50b00301e840c15009890008c0c4c1c146036040220b40311151020ba0314440f905116000810b281301020146002515809840709412a505000124400400d5070b41540d8109540c002c4c180c0314020120300c0c5104010a95001010100340d0365410303d00400540c007014000c80403144c10341d0b04c1c0c881c0355603103200b0fa50400700420020048801041c0035448401c101c1800104045d0900010305065400c1d01d581c9800f00003950003204e00e002c0303505c07807500c501400341c02ca82005115680c01c00000303500399100500b02880c80f21481c00040c4080540036455020150302ca4002d205044400c5400f604540903501c64510075032030042000c0f4241402e108280c1225160f03400c4101d100e01d40740500082590281060342c0201450524000310380341d40c0507603030041c4032089003003441184550851b824543e800c56464401d07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 340422769 1250 340421519 340421527
    0x5040e1b090601170702070305060720150a0c090305010507050306150313030e03012c25031103101104140315070e3001060b0a08040b070e030a0606061202 68
    0x50744d0190f1108020301540081180d95120400140c0c9000d915500041640c403403e001c011701c56034010108000c2c2c03034007000303010504a080b5808980741c003030f00382da40004101800d000071040700607030300001303895101d074200341c0041501d07a2605425150202c41c84404507a00109110301410a1083d0458150310102e4250460400b50044150152100805001c014200102441c555000e51201d0658417010852203a0401030180101e11074840c11454202c80c042c0c104609140349002d141440000460616049800d0450f910303810344000f03412210750140300c0c1d922041c6114605108100d04280c450030b45d25159072401400c10040e428030788103e402074002007446101d00c030a683c00260000881c1c1014444035039042e001c1480310018080b40a500075410342d80c0d0f507010300380100d114a102071940003072109545400c0301e6119445982102030008003100f00250200c0c0e1199404d5800409031304d480b103000c04904002070316250300c0341c8040d110540d441c403040250700e4100604e0342007000c0600c015414 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 340424019 1250 340422769 340422781
    0x3030a05040b0708040e0702060402240313030905030619180201051c0f020d050f010602030f0a0e010306031502030f0a050606041a09040903020d120912031505040e1b09 74
    0x2241c02288604005614081001000c02828074103071809807a01035044e403403a10300709a0080d80d8420559040e800b40c07003071000801030044031071034200300500c0140003249940c44d12281c042941c0c540803000e40400c0340d030078400706d82c41c0d4060002c140510700e6406821100101d10860794120b5031140b0703401c11070702c040b40c54420050f43c0100035100818946010480321030b8100410002510300306c3c0081403110301c006404540300c6030a600c114090345040c2c80038000c980c0c844a060b69030344980012030707107012024002058510310403a061010703c401031502040341a900d544080380da07101800302a03000e0740c010041000390480025020b030f00c100c002e5000c0c03216091072000f180c10791140307000315600c02e500c0c80030060030341c1c201c1022500344180180081007010f8072820001c1d151380691401c10000348890f0000140400c0c0c0707008014207150459120b584a030b040200c1640140115407201d40750303a00c1e440000136581e586101d01040c0801c60030140410750b05400d8124948000e40903454420080c400038813031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 340425269 1250 340424019 340424027
    0x80d090b10080105190c0905031002070519050322030804030602030a0b031f0b04021b03030709080a0816030e09040c080705060c0c0402071a0408190e0906010e0103090b01091a03030a 80
    0x4002c2030b20300001b034030340d07003260111028881500300c0d03505031050121403c26580141d008199242c0103c003a12507101c4038410442c61000341f010702800e0b541c410b10518a041040b1240c003541d40f00c038601925280da580e503031000b400d50420b901c181c45c1642e01004010380c5402d240115165801d04034040c0c017002c1c41c0783c4007902d800230000c0d800d01d58850740c1340307040c00041c0c840740c0c101c80f05464a100781004403003000740c01c02d0342ca0b4005c0b2210f400061241500082040001070303800c600c280d1140c0011b04203001e21201e555001c08654003503041184c840700e00c03100794843d50b409601a5000d942d00c444c1c01820b24001034601a01940514003a403010481d070080c007d000304d15400ca02c00c1c104c5015a032350070302e41003140f103100d1068000e1040c007a0303503010711080045d20001401c801003442d41201d001541500705981c0e01e010f00c0c02e0280c008807900000b4000b0b6100701c84024003030405040010b818076190b00d43c4100c00000340c105049a5907a00102d6100040c144698101c4010031001189460360b560380082c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 340426519 1250 340425269 340425301
    0x1e0c01030c081b0a02011d250609090507030204120b010906080d090902030901020c07060305070e040b0d02132c0733020c040c0f03110406090302010c080d090b10080105 74
    0x444040408241508028401e41020341400410400b00495a40107c000d94441d1005240c2100b2030008903100d02410207142c0b00001284c0040d1510000f40307207450381407406854010822010507500b00b0020948100e84e0301200074260044003c0791701581030008900480b012504485a1540119007121044d80d00000117001c1e11352202c0050707120b4942011450181c0900c110003e064010a100804d055506901071445102c0300d0b50703400e1090b00711100344000c4800f0302200c1900520008241e0000d41481c1b150003401300d8070404000f5860348003910518110200c80100d140c4210a403c1b1565111800c020340c10161501d071014400d03d02440c00f4180110070101c3c4064000c140c540f9200070301a0080c01480d0f15248050b000f8040144455030041501c102e80e078204008c2803912061010b8071032a0410345042d2812612078200d003504640054a80c2803e1300422241c14004009400301c001a50060308001849181c00d85c0c00d03070070103034001c0c0a0410030340c004442c542e2502040055000e10b000181d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 340427769 1250 340426519 340426561
    0xe06030a0311120f0d27060b130f02040303020106090218120c040204030c0806091b060927011a030f04021c0c060807110c100e031e0c01030c08 63
    0x6408004800003424208000e4403c041250b5801248911030b070f010200040a008020904c1086811103c01c10303845141c1c1c1c1d122403c034991000080d13000c0011f4080d400400b0300c1c0b000070045d004440681c070402040d00e0351200720010b0550042410010103409016034005040e03105402d5003170100b451018240384644840d00d074450040d0841c1c103400d5003400c0c460444a40e030058025940d031901ca04019890300c4a612a4440314460796000600b4000046540b108950b1040d00c160040084502084410340144102a0740040310102e0f010941c1500502502901d01080e620517480d80351402d074100e135070402c0da41e860551004004101070003947d082e080340e0160f812a10006960021180048088000c25005018002c00440800c00c0c40c2c0040040d0b126000650383c0e1120440c0142e80245c90300385100c0e8868003c84040325140845005051001c480301020702111000380501131800c2003480d582c1e010024503040541d07003541c196810f00030b2200007505c40c1022102c5042150240c0340386000c02d03101c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 340429019 1250 340427769 340427777
    0x601180504020a0842150a051c11061e1606090b0f0a06061416080a05041d06011709100e0c09071704030507060902090a0203060a0e06030a03 62
    0x3400b1542d85140d0000a0f02d800401c440004428445100e04a622028010704080080350900c42e060042d03510301080100c0010112070940326883d80808201820300e1942c1e0140074140c0100e940e4640c001100d5039245a085040600d608074103107500d60000d0350b58094082c0104020031544000034000316030311040e10301e1840e9600c4074908084040c841403100e0040282b410200c0c20f100f8007007800022805410300700000c202c161070f0f00c035400044554912400b004210006c801c000300381081d5025000c18a0340e6115090010556501c1c1315659000890700d0003ca103000c601031206152103d640c084001240545003058185000041c00801e908a2565a9161002c0001d01c0d943e1040c050750b04449a13001090080c0031f40b0031b840644442c0700000300e42c018042c8070b0000b840c1500c60003000b5100191151401140d440e6a2021601a880080180c8500751250440170040c2c80700c43e1105c1c41910320000060703c2c0e05024041208511a0b58006103010411070203103d41994082891500c07550f140c14 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 340430269 1250 340429019 340429021
    0x1212070323040303090b041415270c04020c0706081515030a06050303130303031b0804080c0f030a0305041401052412012c19030f0e0a06050d0e06011805 67
    0x6012001760217105401401e411191003804100103d07071001003000b481800c140c03100313544040004864050201c0785a91500e030200f0310407510f41050081e40030011070030030948581c0700c3d030306009c00c09a034003000450300985d002d6041009100d9224001c0c40e0403030403000d59610031202c040c000403c000241c0065200d5540000003107a26086540d001d640103201c058150381d2140304c1441c10100f220200d100c10780111b070424921440071074001c50825982001512024410f031900c3c0c075581466004817140784200d00c02d01840141c8010100054210f981040d90041760503e418a00740004119500b14042244e06080a21581541410924003600f40f0036140808031034061002400149121401d41220351804034241569a404075910b201d01452a110b024903050b80d03400c5079a034415084840b6085402d00045600080c49900010184051858035014017584600041d1180d01642d001c1000b184c800984860242c00e41e01030b429000d03482c203015018940c5007641c580c1011140c90313103945030a60b480b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 340431519 1250 340430269 340430273
    0x51b010807050306030a0215030a060b03130308071701080109120c11060904020702041b0e0303180114072301051803090f01020a0b010306090615061e0908121207032304 74
    0x10406c440300703800402c01c159000c500000c0d1a4194000e4580c9580d075400c282010450408182c203c0e40950140c2c0d00680428409447c12184031802a01c04020480c030711b901e450f460798074465407a02030320f4810000900d00c41c031403528150420320700d4230040c02e00001000f0800801e00800c07815603600405e4801c1541c4415943c0083c1c0240300b2868029405441c144401c503d00038161409500380030b96803510303c030014a1604040d900d00445205820021500090740c5055100d00c450b0401d40481990060824100b81d842c1414111400500b8030041440304003104002c60900406411144400881200c900f0998a0507107034840c44040354014201000b201070707564820402c0a02c0250070501078180c030350312031620700060180c01c0e40913a0300d14149040c540d296062564030740215034460f01c0e82101c0309404100e14101c0d0070322806034001d000c1328030300005a03c00148808000d17032821001f03140c0d50b5032203403400266810000d40074504140c5072600500e882c160380d081f4501591142040760072155100c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 340432769 1250 340431519 340431523
    0x3030c01091104111c0c120e0a030e01050301081908130f1802040605040303081302370b03040311030412080415030506060d110705031204051b01080705030603 70
    0x4091042856181884580600600300305041c82c08604039814400803207004c04103951405095803410407049940d5100044e43c0c440da2150041100d00e042440040700511040012200314503092022508880002c1c001c055201ea44040507400900b840c40c1154184078400f66140c01142c01c4982004840344000c0900494409540d506104100740c00d1446444d49801c4c0d2400400e807103035190410305142070260300e800074000e881c1902e0181d0781c1c0c6802d15155031030031100c0b07201c0030740001c3c0c42154007421800541c903401c11f0888100f0800c14000c950b120b4a050380e483e00b4140f000245011400c0c0c3c80d05014070b09000088a8003e074040c5068049203400c0c11095045118690140c0d0442000b501c070079007007144c81c5003d4400c07030f20a24425144141403400580981d0003c40c1c40c180c1c405810003070042403140607484092701c2c8003020340310340c1440c4c0700d6a2914950740c0211150504108800c0070402002400c1010b61001c508444001c2100701001001034141000a42003005008020002502036141 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 340434019 1250 340432769 340432777
    0x6060a050d0e0706090b03070f030504020f0310060519050306040b0c04080d02100e1603120e1c02030105010501021b10142a0703050304050909030909010902040501030c0c0506070305060303 83
    0x3a40d807080203024800c8800030394070000c1e4443c400202d10b050704009a850056001d0368407903541c80c0c0718811541110300089004040c000c1040f40e000c0c0f090760180e580381e1001c1054143c912420b07040040c0c6a410b143c100309146943e00c881c150040200f64003071089803004902c482d0080e501c010f00350119180e01806004500590700840142c0c820206801c2c2016400036550000d000c5030481044640724100c1481d403561a040480e1551401d00381040002544010120100d41c20524014580f020090001800c043c00d004000d222616441c042c0821340c5401e00c5072500400090008046010301c2901170aa90b000081065204034000700d81c5c803980f82d0040803105416800902c05a40d1840c8018801400c903d10007082413442203541c6110207017000001d4040c0036250490b0045050524000400102c450003c1c1021070078013007480055083d80780c000400d0301070000c0c01070241e102e608103400101250f0001280d001003080f204440703004154085041c0d900b2410514011603e6a50600400d1071845 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 340435269 1250 340434019 340434037
    0x3160c15090e250e0a15080105030d030b01090303050c0106030b0f0f0f0603030403150608010c020703030f020607080613091e02040506090108150709080111071505010e06060a05 78
    0x1001000c4894059802162581a12020205401d0303980321408543d400341d01e200c3c4030320000c5840c40c00290800b4028a44c03091511401005001c1003030321000740c43d2520241580200c04912403800601c802d1605105903265001e00c0e14082200c41b80b8030000800e5014244800390030301000181c030310034a403420341018000d543c01c054100702c58100702d501d000b600e50003280c0740510804030700d001c517100202401c44107001d034100600a50030705056842c2c0350102d110348800b46910304d07981d1400080210081c05404501102c40c3c000d001d00030301c1d50a02501d2903040d2000d0100b150490000c0100c00e80e01f10581d107130048010784032400303c648031403110300080400d00c42c09449032455520300520b0403070341c00a588280b84250344c1407045454490503c08440000e019500c110f40003106075203070286861440d1540b14400c0d10b4840002607495040908451501c1285983d824000504a091002c11042c44d109070410f0101000a5071401c0c06c0a40341d0013016012510407131000400301050751269013aa15446 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 340436519 1250 340435269 340435289
    0x2100507050a180608010611010b0a0b040302090903030712110d0921020a0807020103020310170607110309030d05090a0e0f1005010f120b060409020304030818010c0203160c 76
    0x2050814001e001900000395460000d00e01c0c5000100002ca0005000111415911041180d1b400d000040e91000d846040320b0850707640e6100c2c440800e42d12203400c02e0041003070f072440650311b60940c01844a4240c000749010400c0c1d0042080c030808907802200c0d1810044070000024007015204828005032081100384440302d400c0c044400c00303000032b900e0181301200d01030070210f406400000080e1b0312688500805808404240048005075021f034000710380c0911100e15a500c0181c9803c400e0f1012190f461110b24940c1c8541d04000080750083c000540007403240e00114201006200003903901c0301c400841d0300c20080f011032549485d813a03080d200d42c00b4004003030304c8100c517180c05040b42071162011500e609070952601c200240a500850710700c0ea0100703559488005401190ba20034014101c1070a82c103030810001c000003d00500300e88041c40c0954820b40d1813400c6404c201507850380541e145000145940d160001e503442d042d4001040320b94414902c1d1003101110030b00c0c10402c031003800640c8051885 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 340437769 1250 340436519 340436521
    0x10e0f0c04091e15080714060405060c030304060501050a08061f0810020c12120a05150405040602090907051306030b0f031509071e06030209030c130b090c130510021005 74
    0x1d0720103403100d0f4604081c44402004103070148544404d8110303041c42803150075000003400340001c0500c1c84a100e20b440001d40040c0ca8140d0b03030702c04220b0ba5440000d40d00b115400100a0008114050068600419003207484110260401100c01c4e19030102822000740822280c800c8003c42d078980d1840c000030312900c403d03942c0e081003241003840a584100328450280c0100c9040c182d514194100351141000c0400507401c280e5156003c590003000d01414410f003041c060120300420350380e6030140a2281d48203000250311462604103210b40824068910303c1401418403210b0124848449e503d0304807100e600e00401e4954881c0049001c000d000100346805000e81c05850803114104071800c0e018461000480d020b81c4e03a034607500b007500c4000940c2ea901100c0740c01d40411165110343c0103050b41030302c0181902c04000200f400038a01c60102035124202c00d8403445259514038020b824654841e68031986145050b100c419241a50a0b4501502c2d114048850b140e108003072080000300c0d8404051a005c202d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 340439019 1250 340437769 340437791
    0xa06171e0307320f0a230304120f0203010203100e0612030904021b121b01020f12151f02070905060306011a040803040803030612010212010b1b0312070f0503010e0f0c0409 75
    0x1780c00e1040f0f000e51300d42c0340100a40482c44460000a060380d0301e007001950916090111400f02e01020003000c4d00d1100040701c210016a8080c80294000d811121280304190700e00b0381d1651080300003c060a10070554030400441d61800030003214940304003103c1c01690ba8000b0a107041c0d02a51210a030440c1d841140100308081003044010070021301444110881c83c80f18140740d9090348512a540d610345141800382d4802c502e8074961880c0c204104081c030024090300700b00410250a2020107040300103500100403107042d03405100020103000c00346070074031861804e5008a030740ca442c10700c00c903011418131600c40c0c1041a202800c5d45c014161000c10352740c2d100d0b80c0c1c004442c2e0780d40055a1740fa2203240e07142c2c540500d440c014400c455284064000505080e880d1001c0c03c84036401044a02603002e00411b01e0283d4207c06000801507040d85d21034011141c20840700041c07145d44048010310a02034104018003000001c0c0020541c80711070000f82890540e01c0c07065207c81402994003a07102c0500740350407a86 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 340440269 1250 340439019 340439023
    0x503030a020909060a03030c02010c06020c060421180b0a050c1b1c2102070812030405070f1a09030a0c0303080405250e0a06171e0307320f 61
    0x102e400c00403954034650340c40740010880072881e00d101c010b0200b15100700380070055004010a6440707500a01e00181807561001c40300381400001c172011540c1e070303e1200c141a8025154521072952181c140b030b0a01d807410306500d41000050780ea0082004580000c41c5103d4401d12a0f011950000c8110381a00c8070840100e81c10142d0b00c1840f15030900c14080c050541d900e00307041e002c0c06001941c102c2c02c1169100c2d9141902581785900743c50633411802008008180203d00304080050601032189007a40c900e81801c2141c200a2590000c0f0032000304044104444d0456854107410f80c025541702c5070303030b50150b900024034180800d04004c000c0d09081800009260f0402a02031040d03010b07100341c030b0502071440c070f43c070910032a42d06d81c8540000452030280004840020030503808002d141000410a8980c010741004500001d120310072580620120500c0038401210062402c854000640c01c2c000240d449513203800c494644554440400c9a200c180c8001f50301c000d4a440c4070420a5035103410b00c1d000519 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 340441519 1250 340440269 340440277
    0x1503060608010902060d020a0e1f0806030606031c050918041e120309050c0d0501020316090305070e13020a081b09130f0512030a09020f06030601020c09060402070503030a02 76
    0x9a1500d00d03041000924110602901d62000ea009010b1403411011480c484000c0d0420102d25081014140030141c440d1214200d41c0c5170005410070008a82074500d01c01049560010a404d00980080050260b40c2e140024028000382110700c104625051480c41110301c0c1c00f4100815038040109807080d401031a08108460085000350f18240040e44900d000c3c8042c08201c060082c4042e40da6420303441070714841c3d80f2007101248150b0580307403c1080c25000a903882c443d0704041c3e031565800000d00040b44010381c081504c41900c2c0c04d200407120324646440c0c2e140c01c060300c5440e404440002c0011140c0454101a02030164000c3c4000e29240c1c83d010ba590340c0380000c494212200c0c0c1081d54140300c40c0b600200c614841c0d00519518444074440356030b00081d02003880381c00c841034862030400740c00c1c000a00014520500035024005075209280c01002600c030702444640d0302030b0380100184540c599001c6246c8150b881e007503c045500f07481d074202140080c490345801624070b020200a010401c50260010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 340442769 1250 340441519 340441523
    0x30f1e070303201201052407050714010924090512060a0f09080706020c0331090c051207021f020904060512060a05040c050d03050c07060e1c0f061503 66
    0x43c4092120b051001c03105110700061810a40e116000420441c030704048544030321440104014081c407006880c40d02e150700302000c21191a0411b000620890160f4540e08c91030380000d2030103080c1c4d645001820100c9640d59100e08078075103801d0907a07003016030185001c0b10080c0301c007500082d1001103c903000c0b03031100c0064405020150900c01742c09182003090189e100d0658200d03400a00c1c200055460000a40c452440d03041c581c00b042c0601055442181d101d01101b518400740c021841c40f011511105040079504069552458020000302850b8801c00b610180060050000942e80701ca0005078500524880c0160416202180c2045c4400058010b0034110310251428052039484004016007030488808003070440c2d0100e00000d201940c1c0340c102e103070058010700407100c690b912000416628400103109602045002600c00c032081010418040103203110b00c1d100d96041c0003000000c50311055035908140c0c00609007104030900c20034542045206174403e208020140d011031070311681105503c41 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 340444019 1250 340442769 340442801
    0x40303060b0a050f340b01050103050411100207050916021902030c060a0c0b0a0507080a060e0105010c02031e060402100201061224140a0e010e030f1e070303 69
    0x81c04032604420b4441da95081e0300d0fa542445038001d0b420440703421152082a0788443e0107500c2544468906880989540c02c00341540c840d025410117503504101a440541054505010000410558104411805c00464032000c801d41008012803411304a40c2110f54440802c00030f211212551416502c6400425000c1d1141c1850a1002040300145480c011b5003540080884161a2a0410060103414850f04120b082002d20b42ca8000d0409001c842030404e0301c0d03440081c0007215401041c0c0381d50240c1c01c03070750a101c16420104050101c000601c2054180910200070404640d0300380f05403403060000031540f0741c1011100c08204e0b40c030801035500340e0042e188040e20200ca24410302440d82036941c01180583c01a40d55600d054908030801024020754005c201401000d100034020020180e85c0034000b107241e418002d01c80c208866251045401c168503241c400042d610004c400d40300d88000400e5100d07100c0312403820210048107111b04444001c0000100c1c10201901540442055408a10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 340445269 1250 340444019 340444031
    0x81810090f120c0e190c020a02040f02071101030b210c150a0206011505040806090607080903180f0607050f0604150b03061504060801020a030b120102040b070f06090209040b040303 79
    0xc81d4090b140441c90000d8807101441100f48091070b10441c1079501725201c1052604580c900004150884000b1840303880186c2284122505519040c002d8403001a4a00411450400281ea400b0103040d90506040e042c035840391103031802540c42c241650f0fa00f683e8207140c01c038005100a252900e0b0b20f841c15410303214a2451a03000301d200e40e5001590b140ca05941c0052406900344829110082c0200e150743d02040010080880d200106004040c05000c03008020005801d04070005030100381c00030700d03038481076005015a00d403038000100025020710040d1244410700381740703030003107030350380c8038549010f402445a02260803200c80c002802d980704034040c03001d049440e807120085000b41e45140f4016603055000501007010070b003136170041904015000b440040e0b8a640c4d0060503099030000d88a500c04242d96850180d00c41c00d0006003000c0e09509040214545802d0240c85d0140340580396001d00f0003003041815400b0401154001802c480c1c0003808400d0030320b81480d056140b000100c4003200001d051103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 340446519 1250 340445269 340445279
    0x120c02190803010503120313030804021c050d0f0e060a03050a02070f0803011e05150d0e010e011a04050105280b0d05070f02060121030e040905010207031d060403081810090f 76
    0x1c0261781c05103100e800b201c01d01c4070589e2402c550001d8044d105a07444250501c4030380b004a643c0b101c0341b0304140708102828100c00f02c2c0601170f003082c82c44403158080c800c0003000138001e680ca00707017101d81d030710b0150078006041e03102d8100c460300034065200002c0c2226a2001040240566080654101ca189510480c540703546002c40100d01030580c804d06401120704107000b102e01002001402102003012000a40680c0300d1005c142561560354440010365981c0701d500c0c09950440700703942d40c010010344042c40310b13524200200b41e600c9a90740102040180c4440c105454510302d0f19854014007031808103580301c02d0001c0e59080104001d5480601280384102582d03c00c3d030010034424101c81032441e0a01e410130f000c2c10300c08000005c000d8220b00300107040c404141c0681c2c1d280711310011b050143e400182c03540850710300a0041c000104416020001040c081d092954507042100e09a070341c40f00070a81c07201c081d80c2c044803401d040b40441c0d40d88400b20302e000d4058207a000030300004407440a28800c00b00d95442c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 340447769 1250 340446519 340446553
    0x614090d0c0f090e070e0c0c100510050d080904020702180a050a05010905090c0112060f030c1505041503020d090b280b0603060609010908070603090605070807120c02190803010503 79
    0x1000713101d1007a0400d0303004021240360000d049034418808042c00f403501c003681e9040c6082c5803000915140041d524020b02a100100c1100c00e0054041511710340c00500e03290b100d6400a020315001d451013503800181020031500e690034115060404404065141c0c00d0840c52407014100445200c50824940400002c030340445004040c094410540942100741036800112688c1c1d14446011010b90b4840f50b0004601c14001c40210041d80a0080b01010905041c0394042e43c4106480040403c5800e0000380704c40315800640d010388070114240103943c0c0b00e03600c0c0034001034050f800c0050710b84000c0c0020403c3c3c1d248458151480740310580500c01c910f02e420003d4504941e069030082e40c2080060001810343d050160080480a805043c480b03031b80da546003401071922400750400c0300060b4035a0300010400640c1d002d95500710809040c451854505114002c1104203100d842c94581da494200c60540380d030080c0030415006034210030b2aa2204e06504180303400d6407080c03003410700038032070306c00740034004014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 340449019 1250 340447769 340447781
    0x20a0813020609040b120307150e0102120f040501090b07231608090301110c150a0603171e0a090608010905060603040b18031206040c090305070614090d0c0f09 70
    0x200400b034505080000082c40014a02500c180350040f00c0d25901403c105401c0024250052040340322840501c1c0944516080d104409014000e5a005018244000e040e00c080a5480000310f00003000300c0e941e82c102940588004440a001d5407551400d001000d90b100b8030122402c0d42c0d1914092410850001d2004280b2412242e28010000311980c0d00000c5d0064005041d810002800880c00300d051442d12415a8882c48429056900054080c400455080140c5a215002e1081005060314580700d40c03132203801c1c12101001c0610001041010306821000e0801c0400b080003545440300110300b4050030f0011030b80940c0000c40c02c4540001407070815400382c01c5c81410040c243d1030850300c45555080c0b0b4140058685140d40d41c0f207052401c0380440c100301a0215510030180c049a41c00d0605c21302c011600420f00701010041d1480003480400c5001480b401210303211301c6e000f520742c29000c3c0400c05134015001040e9201e14100c0b071180a0040e540c81400a98840490040405c0e6455070719400f182c0c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 340450269 1250 340449019 340449023
    0xc03061d01150e0d0605070807142508160507230f012105070305150301051b1303020603010b030108120408070303050717070b2a041401090b0d020a0813 67
    0x11000d0700c200c001920841c440e10f29041e002e011266107014a41d240000d0302c00032a907100c00280142c04025500d82e20000040b481c5040300c101900e00110003082108100c04202d0346450401ca40d5007041c1005249030461b42219041307591340f408031003180b070055207540841c41400748038441d031096680c2c0b150002d0102404c10500920394607007207403114010b540c0a004451b42c4d0b4580c1480e0466a64080994001da920a100d07503600050300f0310309041103580503040031071050302070380c90001005603001101e010404594501100c2c240c80b081290702c4d803610081c0d01d4000a402990100000600602140c050b40c1604d00c00760a07201c1c18809803880301001d005a2040d800194801070701040424082c2c00100507030742c081c00b044404001c40c65840030b11607121101c1281c0c81007110003000a002d4000d801c0b4000c440305800100070380244040113803c07030300441c002c10304101003084440c040c907801081c09500030140e10400380d40b20001081d03203100039040242c0b001d0106040400040342644d1070602804040c3d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 340451519 1250 340450269 340450289
    0xa05090402090402040915061a0f030415020906041706060906010f12110315010809010c0c02060306030f120301031e0b070e040f060801060504200a0516060c03061d01 73
    0x3035101d0302000300701c1c03030301610076600b09540c0d088103000310300911114000c1a01c0b1a00101d141071401200c1c1141850111840032140004e00a96030551081021a074226804c00000800b81c0001c0f04198021303c100102c2507444100044d0000b100542c001198110803840d409684041d030710383c420302198200c12190140080ca5a03000400b089024544c50342144020120025210011080000c0e29500070782d1194601007080c010103003a584c0c041c5a4580c0000d40f41c3c020302003680b80c82e10103400c3e8020702c200244142400b00000b41a520f0802c0400c00c02ca03c1c980c2280e00d51141c213500c0c5c603000d610a00040da03800d4450100f40c403030721581d100c10340022540201001185d46d0790740011200d001c0e085510591090725800c218450144d24051003000e003000c000005002407030482007008444c9082402c8284141b681c2c0185012203409054824000d850b04081c0e036101c1c0e840c91103032924000090001c2505240003140440c6950650051007034404c0142e14443c203000070340071222541800d104411000d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 340452769 1250 340451519 340451521
    0xa0503061002010b0301060321020c0f0409060b04020703030b03100912080a1416020106060801030206070b060105160f1112070302010f11072405040e01120309090c030e0c0a0509 78
    0x18285003120342141d000030b10002406404020001e400e46249902c1901c2c03005104035600100c0f08038111060403100070b4002000b6420508000c00c1182e10b18140181c803460381d464100c4180051600008400403000780f0440d17451125240c09001400c5010040c0d000344281110705256882c1c40c45041100d54006828801d012803802c0122045000180701d03808158817010450010404007641502407120820030b40007d4070300e400d00900311a030316403056040180038001000540c403450300312140c0c940c110750700c001e1075581c000041c0c03054441d0003054071600b070102c0c01070000c0c00085e00b51072200364468122008803404100801010251071030300c522107074016070b208000540c020031540b101c100c1381e4100300112115681c80306007003529a5012000c2c0c4510340f074201010b000c4640c4584000c0741941001c50030300b41001905110050140505107001401d4030804050500820804008052140050041100c4c0300401006008880c403070a0350340c8220015915039107451444802968ec001e0142111 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 340454019 1250 340452769 340452781
    0x70308040e040f0501090b0a1b271802070317040b0a15050d0302010204090b10091712180a05011b0b0619121214040501050d0b040203190e030a0503 65
    0x8607900140040310f05883c88100c030800200c0a004a100c114042c0c030301168980341000700e81c819503010a50400c1c6070911038050840641c0c01200080841803000340303880c82402d43c0644840c0195964010144100e41d4003002c442e94961074000300b489038880d43d21001081c0041c0840c0ea10300340d0603540141161001400985619070592104031a481e020060400c000c1d81c440c080354050101c1c000c01e80050350001002e20403128940190005c103601500d50304004400c1c241c0017046c03148079008a5084084a2180d030107440401c10405a507074560060721a520000104140b03080c001c2c00001c1e43c090a0700210006140d801403030300c03a8020b901c44810380c0112025a0310100031103401000e5603880703403540d54281d0a080c41c18442802801011080c2003c4c000941416030142101c14044c500b041040c2c000030f5420404402600c0c1250b10a0030030780e48400ca007007140000381000312581908144040200065280b1031320f4141c0d142c1c0c9940c00c0412611400c100359588910035502101c003c80c60410118503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 340455269 1250 340454019 340454039
    0x6050f031f05100504080609070b09190803042309010f1203020a0b09070609080c0d020907020f102f0f131505030114270912030c0a030b0307030804 65
    0x14a02480807480014548800c00142d41c0001200048000781e000328082c07000032010480c194202c8404002003007040d00d840c00c103441e40d210341d00a140c040d440c0f20238801880d110101004000d4010101520744961300c8805980462040c441e049801148106007401c0c14244841c0d030b541130780d80201d803004005090450304401c180d40141c04a04501c0781014604c00b18400300515401641c50a000c1c10140c2c0c50240e0081c40000c42d9080301229800c0700fa852078540c0d0b030311181c3d045502d505451403106603640e03100503410b1a0824052a4081c003031110300c445850603e030300032240c4590b28800328405043d045034942e40420f2083c110003603010704100f81155980d465002d05460000c020032801c040f41c65080501c409901d5038007240115001000601c0708404c1110145281d1006440c01e14140041441488611050080000000580c04c0102c1d801c205d0038024905462040140c00303036203040034981011958050240e210000b8541100c00c0c01e43d180200f0005d00303d0350401d0b4010300301414a42022 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 340456519 1250 340455269 340455301
    0xc0801060b09181b0c0c0307140109060f170402130507020f120a0c0b0a0e030a020607030f0203040203030313060b0a0f1701021905031009060e0601030b0a050d0602090406031a090706050f03 83
    0x44003e00c1101c43d81b00c0b5a9500b0060400941048500b8421400480300054104c04441d0845014400b5021022400e0b5034440107040429200801801c0c0c0350312a0b002040e0542e200c00f20741644103007440d040143d050380008202c2d00701817000c02202c1450303004107200c4400b4040d02c603c0300700056401c8100c01c040703070041050a400c2807403e500001c0c11180302d00d1103450f5034041085500503801801c10410f03520303058800c40b007802ca40801c040d40341d0f20300341d030000b5207a100041448004510200c80c2d042407007201d60200d80c0102024041c840c03804d45800c1200284030352846201c601d0040d401000d504140c06000360340205043c02e0700d00c0c1040c1d0419100342c030300b900f0081c5000640d03242c98400058520560003010300601c00e65000c0c240c9800d01d07800040694140100042c06106021020040d6480d00c954600030170b5048800140c480c01d82c440014081c1c8016440031780841d1010103140442d06d903e03103425000703441c3e800448070315075992542900c4a0050000d1000c6414060000030000d4603500460 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 340457769 1250 340456519 340456537
    0xf080a0b090f070e0a06120513151a0301020a200309030d0806120c0303030106030b06190504080607030e060c0904091401020a1b0b0109090c0801060b09181b 69
    0x41125a514404541510340c110b8403404880c801d2828410002c0d00100844040700e4207485440c142030401601401428035401d4002e0302c0d43e650000070300c4003200e00d02c01d000c986a000a04a0280c40c960f48a81d000d4440390f03480011000c544a8101a03c0c5014400ca0320341603643e881d450180c2d07500c8940b0311080910790001e01c045000c2040b500101d541c080c00103440704811500c91031074a08041c1c09010301d0344413000c4072000541c400000130b00259400410340341114420302e4007040c070880d282c011406601580268101403180d105100c0055600f040c050300603118100125901d40d500d54004a095420a01d190714260b000341c3c01181c0706d050198000c141050014001203035001c01c0f603a54503828001e00400e010306d6580400c0111007150b1004c4a01c44410092001004c841110b031221920b160040c0b18141c1825900c1031400100911643c0c40001040d421000300511941c80c03406d8052540100042480b40f1284a004c144007425030074101e00685441c4640c02554080c0b03014202aa8891040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 340459019 1250 340457769 340457771
    0xa02030d020a17060d0b180c040e15100e13022e0905060a12020703020f0f07030204061a0d0f02130f09050a060b0f0a0302090d11030601080c010f080a 66
    0x20100303103100d400100304a050981d40c4415070071030030b90b49921040028248500c1041c001c1c408002113285103441d6a000400001524068503940c54407500e45603601da20f80340c00c01e06041201444207004500368800c0690114180d1003552a40c03610f4078020f505015090100b020500811940c0002030300e22000d072480913003a1483d00c850700d08070807440951260034528820501c550000744070f50103061030008041c242d4003c4c1c00c0805622010f00904c07219540c1a40382035000c18000d040c94800c008104031038118406682c101011608102e0b00d400d4180401e90007a03043c40030004201004d0000c20103440b07400d030398149c180020202800f02908030303680c0d141c01441d001d10404801644c10704d0400020706403c4503603050145480c40800503140010828001c451a00400700b1002040800302e58a90070b00710324456661321002000c0c0c0c020f024841485821000c6406400b0800102060880f0032940c03c0b070440d40350344e80e0f404405903548608410a80040e0005180000d00c40c0610885600800c075080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 340460269 1250 340459019 340459027
    0x31207061e0207020f0103020a09061b080703050a0f0c0c050d0311030a020a05010506040b090c0a0c0503120103140705150d020d09080304020913030203030402210601181a0d0204020a0203 82
    0x190038101040881e6440481070350000700001149416070345075041c0c0314282000c2d400c1c1594900301810320700440c0704038401d0000d42c20860000031494424180c003280d00000c410f40741d0310541401800c0d42c11270210003010440202034030310040c1c0641008506c41d50302c504c000100030706100074010702901000703089050119000d03030481d098106202601d00c2c0d41c07141d40280306044e51070400c41d00356040a80303194015483c003d407180a81d124070740d02ca07600c0f442614400382e5440c072508080390000b4991501400900000c5002c7c16815441c90091f4100e900500300c0b115008036007076110b500c03400148a202d901c03d5682944c02c0e10b140e91840504040c90036881c005003444611a00c103810f840c1c1303228040701e13210000070402003145890116650429428200c85c903950659039006540c2c0d04c0701502c0030707210710501080702e6031201c00070b007200320b001c000c6034141c030b1565941e034212202005211910100f02401c249240c81c9030407086035000c610400060410103200400e0302400000c3d40000c20707502c11070000700 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 340461519 1250 340460269 340460291
    0x6050906180d300b03070f0302030c010c0203030f0a0201090309240810090218190303020a060902060d0e1e010c02030d0908040e010308031f0b12060a080a03030e06010e040203120706 80
    0x903919150304242d20f000843c0b0382c0b07000b008050600ba05a0081142c03001804400d10168a0000b0301c180084402e007030545240406000081c1b4600a43c0719614413820f00103007200e4034a030b06410030001e00b0b10944807264481d80f030b230242c1880c01d60321098110464411041103410203200341d540f581c200181d1942c1081d41615409040e0a0360702600d10200e028489860302003541c145240711440708030500e000d4008944c02d50350000e407680340700e007130103800380e92a00d00b401c0c01c0d03540c0c22007214007000030301ca4208806500103003441c1e10740c1c3d28021010107200105919a000e10b41c103010750320544410317502940c5009045d100f030350001e162408040d03a40450600c00807501d00342d5203e905006e14025290310707031a03191041c2d124500f03800700d85501c55186017505c005c005041102080d5a2018090b00e0b952a00e039a4060100e00320701c070a5409207085208581140080c50340503481071044c0c0a400d41034031410381e250540d4500300d40c8140c07002500b542c000d48010201c481c80101410f2217034800d0a01080442c904 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 340462769 1250 340461519 340461587
    0x1211100503060319030918051b0901091e0504050702010c031103060319050708011409160e070806120118050c0301150b0a02010204180b0f0d020906120a020d06050906180d 75
    0x501ca0740c51030b0f140d0720014027151001c102d0b4541807401100c0c4c42c007850000340c0800202500d8880c4030b8401c40e00c4a00000013103003c0700000803006040c014008000602d403500000340a044442403907004070b440c0c4100d001d20000241d0880c0d124840141c0101607201c1e030101158803150402d08251501d000320600800c4c0041c0a00031140c02022064021701c043c28102102401c003801c844c036821a2010404081104a178042d0650b5440031103805c02c0c103200c2d601c0c2ca01260080700c04003ca15415460b01c08080c030307071034480240441c81c240078a04641e5131288c40020f05080320540c95103403203160208581000703000618001441042c48034070015040694810b0503c2100390505540058140c86140442c2c643c180740c04600448902200c210505640b03540200315000c1015180384d00a80500a14114541c01001503209499000d011548111854203100004103c2550b80c150b6034010200480c0e100d1107801004030004a03071402401c40094035200644004e803100c03007299010744c950290200c0034994 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 340464019 1250 340462769 340462799
    0xe0d0203031b1606031409070305070b03041a0a0f0b06040b03011a04030b0c031e270a2901060203040e2215150510140309030412111005030603190309 66
    0x1140d00c011400f0146e0906000c00c1c09802402e58807254031540080000c148006080c0301120032090516503280c94a0420f450590340b0020652405583e60051140d58021341d0700c01e208003161800200010300b100f404002903072089200304400c4101c240018080c103110600e800144515030969607140c0703076a9903281d4240000403514240309440c0802004902c400c100c00c1904010080044a40c070b81c40d0030b8214119403000700031236840c42d000b410b20440c0e0000c410442c00d070019400504c900d8109410040c0da644001460300f2010b40c0c245180000210702d400001034800b500c1c504543d41d80c0b02d0f5600798000429011090000800307404451040003c0b40e05000c0e0750044611070364022541c00202c290706207002d10702d503000c14090303400c08801c4401c0a51107514400400f0808101c0755503525a02a494514042d540003182e0300842c4064a01c00c1107007032102400f42c540180c2e810700075120b8564042d11039000c1111060f0301500101c2d043e80c09140d0701300044180500c02c0c100383c03a01a4844201d0180480 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 340465269 1250 340464019 340464029
    0x2031905090a06080109110a02150613060905010314030304030f0507080702060304050a0201022e1d010c1121030105060304230106061b02010c081813020a0e0d0203031b16 75
    0x40d0390b005001b0708035a0300480c000c4001d800035180c94281400c000955618104103240480301d80840440c03600d54030802d41c2540383d035041d0b40c240b082c03c0d22031625600a040c03e1000301c840c400c00c1036201c41c400300b002c006d0300d22682e01503c0c0d003240c0010f10701c0107513003c1d88040c200301e411400411211005030b4884016602643c01003004000c402078a00c00a40303401c8507c04040c6d1116801e08020a5008002c0c5045003004000400800d461400301507190180b4494141c0d0750041d400c00c005108607550021000441d011014100e4043d0a60604001c100c010f042c80c111080010410050086041c0500219005480f45240c1b01400032003540d03030000c1ca2a01810440640d44410301040480d40c41302441c8030201100341c5520782c182c800c0d80040c01801030183d00511020b00410500149002103203003583c09070010744100000c240c580c1040d0001c3d80480312840c082030041500d884182418070100101c0b541c054000c501e003006110b502000b00c011012600386510616600c1e1180d5142c6001844c0148 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 340466519 1250 340465269 340465277
    0x603010f0611012c0106081507091a0403080913060e0a060501081905070c21090803090f040b031006090605010806091e180a03090f0909020102031905090a06 69
    0x20307040c03001c010940448240790018503030400c410781402c04d14000e5409070004d040388558a51240000b201c60160000b079000013040d003d640000c43c030900700801804e00c61012a5201c5040c0d40d200d02c41103003007000b08407401d10510710030700081c400245c0590050015060040c0090020321400404106807591504400260030090342808040030442c06908040d20003420000081e07c0d10250903810070a034a13442300243c039114004201d0381d9010fa158500c40a4114940406400b00e0160340e5400341c1c900d0f0030103000900202030018641402000b0340f1320b4202c1c0100142004c8001d0f05c2000064003400003410b90501a00d00d40c89101010351040c0d100034000a5008507901d407a00001503e80c6600400703950184500741c0070400c4000c014000720300c0000140d40c03444010740340c00d040038504842d600040c012a2146150076003d1581290398601100e40302640c48000d00d846001003015a0000d500c000c3c003582c4203002c481900c2003034200c05181d0325028540203003080441800201d02c00c0040d80820003003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 340467625 1106 340466519 340466549
    0x30405090423030d0c020c010306080c040e01060b0c0106090c05072a090903030b040509070b07080913020a0f020c01050909010308030a0b0a0f061803051e010605060301 74
    0xa211400c0f41d0b20f40c10a108060020070f24070742c1d8903015110b6091903064a6100b401103c0945180d0700181c901d1449001c07c2c4005040c2c8040c86c56455501c602001c60503542c0b0707002030701c1c104400c10000b05106140045a00807140800b842104000c01080701c00c001c680c0240300034510701c96241542c0c250f048084c42d001c007010500d409c03d1441c9410f140241040c107a2541003031110000840301000340e6203442c40c0455440705140310380d41c0c5000382071011402186800b00030b0281450042d0602c0c1c43e850700403000c203040741c1c84140440081400b1140103c10350b54100a015160303602820320070f00d0000c01e0310004003a0141480700509100c1d00200140410a507500300201c1c00740003030034503200680ca80031200d040300303000d005040014030345502c4041004c984c95882c004603500f05014007400750000f9a61200340789803080304a0070f50748404000900740c480d140154004c02090a2511003 = true := by decide +kernel

theorem cover : BRFrame.Cov 340287769 340467625 := by
  have h0 := BRFrame.cov_init 340287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 340287769 ≤ n) (h2 : n < 340467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
