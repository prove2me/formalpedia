-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1943
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:14:39.391327+00:00
-- url     : https://prove2.me/submissions/7cf5d3dc-92df-4ae0-87ee-d99f2d787f14

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 349280575 ≤ n < 349460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 349281825 1250 349280575 349280579
    0x1209060c1806140405330403150608070e0a0b041d06070f0509010c0c050d030309050607020f03090616170c07091b05031003060203090c15030f04060b03033709 70
    0x102c030f83d000303d108203131003070394510740203200030051800e140020440c0050302c42d9403501007401d840280d0040c0c081554824061500180700c00e40c1481003100b92054440240039041c030300307854001c1c01900141150764103034035100b9014003600d45000c4c8a00c80301011000890041d140c03c6528903040000707112100304034600002c2030031150820215544070740d00303185c00c100c01070490030403510003121980201d4100783d60b90320250603d80c5c5540312007851881a41516100d4031111030882c0d07030366010700e00d4412030381041007150280e2821000030302ca10310712280510124859078450102030648170f4400d0b94045000900e14540c0c00d003d0001e2000b0b00b48400041000d00c011004440450070000c11311014081d00001041c07002000105c0e05000b5540309078290b50700e1138181001ca07103036103404584034007680f54413045e50b40c0061a602a68842c605440070001c055990340c9444020b0000380c088150140400c20032003406480c4c0200c1c41d4542c1c010042901c52200000754004079040c070003020181040403800007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 349283075 1250 349281825 349281857
    0x120b06010c0c030b0c1210050a120b0705090d05030304060c0210110d0c02010e100b0306010b0313020f060d111e07030507030302030a0618090606051f1209060c1806 72
    0x440d40070b594014480c400c030f980c0d030305c1803041c010300c101c00e485070341c80b50208100180a40b0908542c41038803002c1d00c1c4c1d131401a80e96640c1d0726045180b00c000600b2040043e000450350b610440c0a08018034006100c1e0f44200d0340ca072640c0381107070b000391002e03038170aa03d454601b405160108402c0d80ea10003a040d0070080ca10b4010740d0701009000300c1451003403c640380d4441429452003504034a01d004600d41c196220060003c10010080c1000c2c0100b90190080000000f29640c010b0180c900c100100e091540034040550308000040d080401c0c0c1a50114081c80b070483e40340b159228445c207101045400f141d81e000c08020411a0f2400241d80070315560040101c600004d0340305081d513540300d80c503050140c0c0706c0e00c40070100f40c003500083c0c004139502180180801002c202c16003180c40003030701803501040a141c4482c1400380303891407040c1d41d0340c52001d458841e1460902c50080d091402d200182c0005c2d00088565070602514400440ac00025200001e44010b551580400100403c00d07818031549281044075 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 349284325 1250 349283075 349283093
    0x605070c08031821060c0301090c050a0c060902010c2315061f140703170a090c17030405060d0204030302120307020d0e0d0f05010501060221181801120b06010c 70
    0x264413030040c041000c1c0c401420016210710f0411009070000e40e2410701d0704e08403100e0260001d110b83c07160700f400d040c0c44c42a414001c2040300e000300f44903990303000c03d203000e521018098000c02c1e10072810040c4041400700400e0240341030740c0c4c81801c0b18104410841d400811145040f6820300b001402a0180e000d014855030750100060790310041e40174040110b00d40c01c0007038501c0211031004c00070030301002070100f08041d4408001070b1407102400c0001c1c042c8c3c035010502030413560407400c01000164560010302c120040040040e0303880c0501401c1320702d45529140400d80303a4100b009600d4925401250074420175406021030712013080c0107c100c03415850003103002541c4803d40c000d16018400c0c51403444010b51100301139028041c2c0c2002c080c0714004480e02e41207008010910800c40180102c080003084006844010f44180c0310000d8500c0c24060f6201e80da00f6602031040502c1c1e44142040f0a0105140e00001c000f402040c40313420481c0c1180c21818400400000101458100441114050b0009010790 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 349285575 1250 349284325 349284367
    0xa0303030b0310050a02120f0910020309030409110706060e070c0b0c070b07091e0521010b030d12050612100c1803060510060513120c03060203010605070c0803 70
    0x4540456a48a0100442c1c10032144400c08085681850204191642d10b90000c001d40520b1480c0009580d07580c108c1c1d8001c09409448840e03664000008100c407228468000e0f54102024805403841e003541d07141c800c8111858031042c0385d811000840c50b0400d02c60a441303020003c0ca03490203104d81c0d91400000c01800003406a000815400c00c500c0801d080c508603909a4440e10707402411107207181440c00b000f170203d00d0075209101c009020b0740041c0c3d007620543c0d941c000860794050021581c441e0382d800041c00b16000341d0840380c195035903160b40804aa41c108a4482c3d240560785480340c1c0300304c245288000381d500040510307005240d40c0c400001d41c03038000503094488a07400344000425150300e01080303a00c200756842100c141034100b000801446070641c0013500450030031180c410310f00e6881d08180c4031405407204084820f41e4400f030800800002d40e103001d401520038007014101d00d480f541c804003280c000f80c100c400000c0010804100700b12142c0f14039005004036000640c1040200d03200004001010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 349286825 1250 349285575 349285577
    0x20a080a0b0f071e1115042103111605240a05090d0e1c0803150112050408071704030f030306170f0d0c02010c05060108010c2a14241f050a0303 63
    0x902c003016605c2000f4080c8120071070440d07282c0d0700141482d0811088841c00b030385410a81c41080c00c0c0200f5400d00a00c10000c42001008c1c0301d41c1071005c0e0041e490442d043c0c00105450a003da94014060100e480d4030400e07a1082e055198440c504080041d18103c410003001940e140d80880030140b000b0380c1000f00502c90a01c219400c241550701300c4880c105005031240c004022140101c18488030300741c10024401c607039000703980754039045140c08103040039503000703540207040e00341c040254502240403500b11041070200c04074020300d490750320342d90007511700200682030300081e5407140e00344030480882c01c0c10b4041c000e01800030031114203408005ca482d28400c16107081405030395120311085901400001c0906600007003070f41c80c15a03540032884d01a1800d0b907070010000c1c0c40d5502158998403020780062031101209030001d2001c050340d55100d402e0b41320b681140210310079200c03500e0840355003002280900640580e1004142850203424180441500702d0416280940d102400551101e56124003142d404d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 349288075 1250 349286825 349286837
    0x180308030117030c062401080c0306102304060305060904030207090e121c0b18040605130f0c1406041404020702060f0406032003090d0c020a080a0b0f071e 68
    0x200d15a42c078594401c0108a80c00c5010358001c2040c0c400500320001c0010700c4049541d41c141c00114011181010200c1d8107200c0c80304c5c2840852075505142010305881c07501814030559112aa41604003030616550b511100440c0006042c080c00d6454003411340c0016041d00d140f40395007071540c4c020351070328402d00030010407076076030505041008010080f1690f140301c0c80304e0f0203a86d40c045034402c4110f68100768207191580c2c10803040841c1420100007007a903240b1050b403120300c0b5444954500010340805402c00009417042591280450342c0100c40c402e16511400c00612103610704961004000203002140707110740d0061108208888505096401c4201c003103500581d90201d6100141d039a024652001a103248082408076850340c26600a00b4154a40e5480702001c05121b5240c1c030483c481200d1024064001e0803010400c140102c3c4444520381c4014000c01c10307140c035140c0e42440c5c200303022000d4480b14440ea042c0714404c1c2400041d40d4224020f8580f0a074101400b845104102100100304420029 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 349289325 1250 349288075 349288109
    0x5120c0d080f04020d020f2205010602030a02030a080601020a060f381c0b040c0e1f05210d02070e0c04050a06050705070305120304030e04140c09041413031803080301 73
    0x545e58060140b44040180710162231003140e03004018801600380c001d000180780c1000400d5042c00042519118081075008500c7c2c5202e0500c100c98a40c400b0780043d06600c100380c2d18800003001c40c0105011001e010000007000308402d55404403d00c210311001810726022030451a44604241509440c8041038803440703404850200c9100700c142041c3c0c1c016100744000c4050000700030408480104450440c2e800402540b0b074a400e0242100c004422150701c03040443e8200070909200d0280500c4154072951300c1c020708052541c00b428800c4070b40b188001038001c00c0080c0055000a001583c0211241081d0750802d81400e0100c0c0078840309014450900c130700451000200502000250042c5921405560720300042070690196900150b80440c00b081a959080710682401d10440c0d4103091100d801d1007103a100d00307006101d581d10440d13180d900203460700304461201c041c80c2403040c003465500902c00e003001801c0c100280064911200c4940800320384c001000401c0640c0c003a00e040d00c00c0d080300d50005c1c039 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 349290575 1250 349289325 349289329
    0x111f1407050c0306070c0b07020d1e03020c07060806032a040209060c42070f030e0312060103050f1501050a0c021908010606090b04090b060705120c0d080f04020d02 72
    0x150040e210f0b0302d0b2191404002c0b820358004000f4034890f209a038410140c0d00c0c1d1440030790300e40000d007105034005803102a800c000c2c20952441e10307565030400d080043ca8500300504041c1001d40c107401040104410405000c0f8500f0200f21451201e8950780c00c580c400f4044d20700d00c405200d208080180300d240c01048000447d6101300803200c140e0f40c817408072007a4550300d40c005442005400f024020583c1e0103003410010342c80c40c6000d600340c0614401002c5180d59040810307a0b500c3c1c44221828100740c0d40d118406000c00d0700f000240000c2061106410b240d01c0e1500004042d110300824050540180c00305000c05507199161b08004140242000fa131105a2204102c540b80b00c010b10180d840b81e60708450103000301c2c001d080300c81520000e000a00c645a165142a01c1c0400307507214400380740904000402820311140d10801c1c1301f00004008514222480d01c0f0f041c60444c113080310300340381000000c85030381c100d4041107000d900000d5070905003107510301024409010700700100b001c2d000e2403180714501c0840d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 349291825 1250 349290575 349290583
    0x3020c060a0e06070c06020d050a021005070905030703080309010e0a02010c17070b040b06010305060604081b0a0e0709150806010e040b130e0a03110601030507120602040b0304111f140705 82
    0x542c0003030a0311351508003a04000307410301c0241c8104070147c0961659101d94502c1003003181d124141c0c0d5001802c08a80001048004020041002082050030b11740818955020b0040e03200071070244071095146e05000d2207103800c54014507044015070f44400c200307c0060340c0046e0300c00025034028148642d035042030415000760307100300c81000f4030b03c0000404010030000e05606c214002c11083e6010041c60307484400b4130007184214007500c2003e1780080207a15401c010303010000484840a0121884595264400b501038030041d184c41011803000d05091095016410105480c08000e161082e1181070103800070307110141444e00d05004644801d010590390319031840c1c080707058004800030003c0703040707a40c1980d49a000107581140098580c060b240e0400c580024041e040c0ca400401800c2004d1503c0d10039132103101d81d02c0040320025024800023034000e2404010790700c910b01a40c1040c2d41c01600e0010041455003400e961400c6c1d03540c00c840c4450003030384a5104051981d022419a640b003d250030724a10b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 349293075 1250 349291825 349291847
    0xb030c0706060b180d0c05270708041e0c090209040213030606170601051f09030b010e0118051b0a02071802210705070201080a090f200d03020c060a 65
    0x40035090080004030700348050010b000d60a05880003501004400d8200403170440d200301e02410010030381d5810b120518100d95038084590508856401042000c203907805c041c1011510200030591000402c82486609000388a03928210072980b10b4107034440d07941a1030055507000e030380055070340442c51a0258603581d0446401d0407007080765103401580e91034114003400c0c02e40a0401c600008107480c443c8400d0000d406410381c0c2c1c00800114810017808500c444450b10301c4001d500300000b00400202003141212118044e00b00706c03024100c3d0b58100f0581c1071810340030403030b0344402e50b1514080021050300b05441d141d210860307050581d41c80200c18000c0340391203000d402003805404450050f01c1c031081280c2c000d10341c5440580e0b0110724448842c0c040d1225440c210b07110008030b6000c0010100542c0300b21006a8085545074000425003090b89407000700d00c2c50018203c07000781c6841051030210f0f007011043c804105d000c60344007400e019240d900944554601c1c030401c1c0101004103c07503542d18040c1c0c1d40030403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 349294325 1250 349293075 349293083
    0x90d0b07140f0412230f0d1b0609020402040e0415140403021c03020c011118010302030405030a080a18030509031b0a050105071103010c0203040e090c0904260d0b0411040602070b030c07 81
    0x8449024140c41d2280302802140001d03100c0c00620070b04c003c0c05106c148c110a14040074840c1c06d031010b0345070000070b08410b0800b268040d1b401c00001c5120310604041d103016a0040019401914a001a210072220a0309078282c909420001f003200183d400541e81100f074054604245809e140440150043d000d40c1400500719400c011b004511088010040c2c034501a44200900410000c84015800c82c482910040c1c05600b0400080340030b0f90090340780356002201840c00103005442c00180446456010500300c001580000303004040c0d1904102c2810b07414a60400215000e107080002017407800c2c1803069a06000001c180721090007030210a4111045029000303008d1460340c501c5c000e44075440343c060024500101404140c1c4403900003901d20040c24041d2195029488648410420111103217030181200391b8480c840c08038541032005403c46140320301c0041841485001000203079031503440c000020000034401006501c1d80041d0042c00c0320080007405540ba103490701c01a01074418070728094 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 349295575 1250 349294325 349294373
    0x812090a060e040f050a0c18031a070e0612060f0a0807050d06060e1e01060f05030a022b0506040f0b030a0303021b070b130506190e06090d0b07140f0412 67
    0x116896480d42c0110f408a98243d643d9239464047c00140b450603020303404054551480c2c0400341078094600d8066603044916824900400316051f00003602d1540a601c2040313446125500344811814403046401403100c089510640c10790901f00103641c0d070ba9042c440c491007080101c510000b40b100a42c0260098400c0700b444803014a01580648903180b12407070100c0789000303190000188540714890a01d1030303910607a02d1600d15100c1441d0480a90070084040d00c0041c0c00c1c0301840030903c001c40341501c1c4982030040214182c13403c401000b00700c50380300c0c02c6441c1031400c0c035462003410f40e0007050380c440b5113915060040e1650716141d280008240444600d5003584561340700802c009c0100030141039107070085254024140d440d08184013a0340501000e500d4214941d40c001c000d05c60155403010300c42c4502402c403a0030440c406002a005068000b030035521080e444003070001443c0d010601404200307000f0041c900e450b10010444506104a1040c1c2d42d04031f000c0790408040045541c07003e00000c0c040c91004c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 349296825 1250 349295575 349295581
    0xc140307140c010504170705060f1e070c060b010512010b0c030f0c0102190e06092407061a010309150504020112020a02030d0605300106030203010c02070812090a060e040f05 76
    0xd03e000703213030075103007034500790351944031090030482c1740045450603540314000c0c2000e0b403a120240034801801030210310400c66194066400224618089407240140340e035410810089810b0400444403e0310885d41005800c0005881140c1010701140c11100d9110b026613644030200009804c5010790340740340c03000100c00224800c1100b01500503107041021020009098008200103403415501010410707001001404002c4441c90802c2003401e2041c0b07100d04d001541c08500c1c6c0411150f911030320b0200c50381e0395540c00070780c41c40d014440c00d00d6080100382000c1162407401d80381e001403100c1c004200902280c0f5080000c0c110791040070301c0d944003007640106548540240b08082e460303801488007005518a411700000d01c5287c0000d52000d1031400402c0d144060270340c503d018154404110002c1c40a45d02e9481c0000140c03403d1040f04114a92503014200c0e190420720004d040805000061084003414041e11030b503a61108241000c865844c149502e0b200d402c6400704001c0c2049078418151540b40c42c1c10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 349298075 1250 349296825 349296847
    0x60307020a0b13150e0c0316030611120417040e041a06030a110f0312040e180f0c0f040f050a0501050111030c07050d02130c05090a0503010c14030714 66
    0x90001c098461810046550303541d080c0c0e4050b10189940162091800ca99003500340e600310f500040803400c00d2410340b940300340c20130042450440715031405003003404103140c03c03c148613641c458ac0301e240006081e868501805035a221046107400390000e0708004840c8003a02d50314148000b00d400400007005404414038117400c000066421501d11402405007450004020b031801040246805a0280702c006400c4507040c1408a610b817840c2d02503425110740e0110808400c10000600010038500380c4883d1a8600354a900c0400000b10b40f02034001e500000c2182c0011401081d001d0f0b5143d01601c02c00008000000000c025002c0200040e8000380703064180b0030004143c0d0005816034400782c85040082e480121425175906c01c010601410f5001000b0a0080c0c1c07808621100c031050008003103800c81040c040e20601203640d6400c0741404210700040303604060910b151554001c02d012070003006155020704000c1c240901c02e610018031500c0020008401e24080c0392405a40d0b100070b00349030380702c9410400c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 349299325 1250 349298075 349298083
    0x70908060f060414070818070504020309061519030602030c09042a0e010e0603131406090c0111031b01060f03150b0a03020a09090f02130c0809060c0a080c040506030702 74
    0x42c01070b008606000c003000b60140519645130042c070386581d412000d5684c3c001d25041ca01d100003e00143c81c00344240005659032540042d40c0146480000303000f19091007200c144803c0c03980c0c030310035015110780c0d91481052a00e4100d4a01125041600942d885e0345681c070114013072081c49401030340302d0702c0e01140601a10350004203034044c1100d401d4001080107860400c0d90840750160300c40380001c0f40710600301080c0c18a1009960030600b03820400b9120f04103943d0340c032020820102400c42550010041108580040100790720031102805c013420210310103903000b0740741e12502c840c90541c01c90300301c1c0c000001002580710400406003c601c070fa011580f03910f07010301030068020f0442185810400b004100740740400c2403c0459500802d100c101074500180304018214207132044c2c03050303020160214003580710890810358202d1341c44400100c06821160280083c00e001d07000f01d800da80a002080080c5400c48101c0e00e030502541400c442c40c0e9034014901441740304039040944c004001005000e09150001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 349300575 1250 349299325 349299331
    0xe0409020a0308120f0606070305090301060b0a110d050a08041b15050c010f050c04030215040317040509070e0906040b030a120504170c1305070c050105040c1802040e040b070908060f 80
    0x500104155185e00320b005000300030907599990300880400c0000c000900980c02048206006400401c2d5140ea90311031072083d030021060603011403101c051100100206021102c52590319081c00c80c00d01c10815001008114010030080149080624804000c21809108001040d81c4c0100032900054160028030680101e2030029840d82003482c0d03461801010700030144981c001c58140c2d8180b41c0340d90208180031030303241d89502d0f01001c104408004600e007810030603295a5000100c0fa0b50354038203414010209401001c40c0c00300001c010741030b80c240c6d8802440d41d0300040200c80c045804680500004d04041c0490700051506003d0003007200081d4000e07000d001201d030100301c108840e814aa00190700d0314415400b00f680f001366680b0201c0030300c0495006a40150359441c010700180301c2d50340e13007a084480c2600c0940d03602c002020104242510130301ca1640d071151001080d820149080440d03880340300080e0004218a0000000031856481040104000d043e060f0403a141410402600f40d0000001c0e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 349301825 1250 349300575 349300597
    0x3030e0d02121e0703020603060910080d0c29041202010b030303091005010f061e0504051207051c0f0f02060f12010302030613030e010e0103021b0c041a0108070e0409020a0308 77
    0x100f19400401c201c08203180301102d4014100d145036a440f00b0400c44aa20020050109003060050224980300c0c02c00501c44654595200d00b0100529410000700b00c41042011224018a2803100d10b443e20900200c682c019a111003e2104070300c0d02c00e000c0c0e002d010780858880d05840080304001e810756000440c0540841d100700308110607604d5110062007d580d078096003020a0411002c504c10003c1e031281c0044103c04d51402a00f400d445400040711041d1a600d0a091540050001e00143c80c4c1040b00f003581c90114070b105954403c035a902d01c40100c81040300502500d00702d044c10000d5407039000031030b103511400a641c1913665006d01900e641e402c5003804103a0091090b42c0005510083c2802d0307a618541d0162a1626005070700401100d001641201340da04258080c018000e4a07410040300b00c3d0322215040140410610250034042168038070100d2031a01b030782001c5000c5880c1d0704914140d421150515042e2050211000468050446014020340140002a0020034403c0e2140a02444500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 349303075 1250 349301825 349301863
    0xc050708010c050d061203021209040902091905010b18090405150108100612021e0a15031d01020a1407030512040c050907020106081209042a1b080403030e0d0212 71
    0x13031b00740090b80d000c10600000d001da400304451410121050300a401c0c061001400800c1c040080d03404036249240955207140c0222940100005007070850082c1405010443e281600700782548404841074102d00011070f002e03030713600d5010500b8001d00340a119145040090160190b50b0349800340b6036a40020740c544d0002d180340180c08154040da9a81c442c51454004081a0040c00d40e008406605200700591652042c43c1c498001500d01c101c50038944261030700e403000500310440c04404c4108482400340e00010743d1042101c030f8050354000c800110ba001d48240f10540b20396035460b050b84c00f8402e0222140740c0600c4042000204104e0302c1180c0259941901e000d00e4584402d8030690036510240203c85103a004141c03030a108904600140001044c010030108900500210041d81c00e905030990b000c2c254440c52000540b41e42003094030620701e910082d4104403080704d40301c0d209540118000242000040c10307100035180d5030304c00d0142c0c0246d00200014a920b1209001c07a0341c44103205016480102c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 349304325 1250 349303075 349303079
    0x110304030f0c1e0504020307020f010504050f071d070807090911070c05040519390e19090f020409180308060f0604030803061804080903100b03030702010c050708010c050d06 76
    0x40d010f14100c500031105a1040300710381000e04020185d08020107031400c600c2504031201c0c0d900803d00966001ea401440905030741c05d8029501d43c00c020700c1e40c0007169249c4402000c1c00c1e070300b01c9045d0256401000c40c50011020b071521401154119a01c0e4402000c860400003078401122581004280b128410342608100c15a00ca080c1f106030340c41115003030318401584061100c1900250022880c40c06d01305824050303c102648030281042941c1081d440200084e020014115007140c41030011250858149401030f6141ca400d1070740d50002e028128102c0d8844281d940b250360b450301030f1000303400420f0051000c091501084030064981d080c003500001c07070075000f086207400c01d0629901d03c0031001d040035180c1400d5440d80000369101510058025003006540070312002180c0c01113000300d100780741c915039503111a8105072030142c402d081030036094540446224181e5000045480150342802c01c03403a606003a09003542002d4180d4800c55480d404c0032860440c02c1d60200043c05408141502000200d0f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 349305575 1250 349304325 349304339
    0x901030803010e01050a1202190f0e040515060d111f17061504030b0415020703050c010f0203010f180e19031106090c011404150305040b0601081603020703110304030f0c 74
    0x201d904c50504040700206044015081000000140418040c2c008049c25070301c8611440354040c030b501c10406201090203210421805201100069000c41e1943c501804d04500103010452511002842a0342810040500e512410301021501c08050010800c1ca41c0b0151301401d04524031510405020359500000c00c2d500e0000702280c6414541c00c0510b041c242541e0f5a014148006401074516845605442c0b090b11914001010890b119588650710744881c02941401c0d94405c0c50f509841d10b00610041c8820114442c85004032815290380da4640080682c02800500b002038481d6134034001c8411211a0140d03041d1140005407190b03a44654070b1595110817616400c0648031804686c1000c02d00b01010741c4904901409075848203586890544e0324981122000104072848000c641c0751010403080c8242a000175612620038201090146000c021424202500410030700915030301040b00b90a05200d100040b03c2c0002d00c100702d03039555841e810b01040030503601008032585040f44801203000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 349306825 1250 349305575 349305589
    0x20306010f080403140f070807050c0a1208030c0a030b030708061803190810090903020109020906040c090b0d02090a141f050415141c05160519030b0901030803010e0105 74
    0x1c1d40c0c0650300c0c0c3c0000b4507900c3c605015a8000305140706c48401c20b11150700031800c1c4800500c0712503c0f40340100070800c03000081c880d40100c242d118052545820200c140803891a80071684c0c0100c60030007250740c0e91a00c680c10740c010450b2102c4c61307806124050380820348240c005003080c002d411041d1503003c0400c80c414655980d12442c000342c00111040d00d40364580c0d500400f40e185e0000303456001c114049886d00012003c0361100071081d00143c0d11550801c1c19800c000b1851504410255414405502040c0010303090401d42e00c40c1c0c808842000450b103103142195415940d1101008080b81203666842140c000318524541405200340d800c7c103c007036851841041501c2000565440f0341d4141490b005621740003698015030a824084031580c1250350445041c0102400202c12420801038040054024100d030705c01000c11550202c0811540301081d00305c01076582c2c3c0350341d5000c0d8040041e480300d4110080c240c0903803002c1e042032400c4008010010b038000034605880f800001c505183c0ea07110104850 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 349308075 1250 349306825 349306831
    0x12020721060902061b030a08010f270b0a030b01180c0807080417040b0c010b1203040e0903040e0106020f10050705030103142d060a0b0108010b1e0a03020306010f08 72
    0xe49030304100038006101904006100c900003072040c0c0c00c0082c00c040100c5940c0614291a2043c2c10001e005d64107503070028a074034054624240e002074480d09000300c9070301c000411440d118101c244404220301c0c0341a280c019601c584809044000c4440d503a16021840c1e00e020302601c107540d50050a001c0c601c00d1580300d2200c0001c1b003a9500801500c0d00700054680110182040c0d58810312504400c48400c500c50040c0014076100304c8032075482450120b035a00f180c02840025103d004c10f5034010344010f00000946003a1420b1a035078444031f440d2108268958030442e4041614020380f14000641e4540100d00704014039480f00981c0e0f1415680943c040480300100c408402081040c0f0040c0045100d44800c610001180c000315442d044940e03030200360b0401c4044500d1171043d29a815404641400c0c040c00d40c0041104000340f00c02c044640010b8900c0005004461881d81c012691400d56001c00c2c000300025841e086100b40d441d91059001000707540110b0708c20f40070130f414042c0d40c00c000c0d10510200c1c2c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 349309325 1250 349308075 349308119
    0x50a080c0f04050435030f01060e04050c03010510020c3001020403030f08060d0b09060118020f0a0e0d06020706090605010803090d03050901020703021804210c0201050a09030807120207 81
    0x1402d46042c4001c0000c2ca00c0d0308902801080d00171260116112181004601954140045580e030750b14120000707080726210044d86025500301801e0081d103002403015681525002c0350a5002c6440b0ac22040f4503200308084081c2e40001018503190400c0701c8001609034001c403e60b044c40104141d403402034280d102d00d00c8006d0001e841e078001c010036103209224a540202c8001d151029580094030b8850750003906544480e0540c0048004026200701c1d544045040d5407120000d43c00c1840000540070540103034904030051112a803400003050f038401d64181d150942c810401c40d01c2e07030030604000740244282d00c000c480c00c1d40b81c140081080e14001042e580500c8000300140d250017000d9800701c482c0d822502016041d88030b2002c2c003000603a560224000e0b002400882d042d0301e454141442d070462205030751181c030b0803825021003000c0640d2241103400c0650302801e080c0c5c2d9a106501040303486000d5640040e0426001291001c104583d0140510141e0784617404c0b900c01ca9103030b1a0074400054010b408130 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 349310575 1250 349309325 349309343
    0x30a2009090a050c01030c030204090507021e0115050603070203040819020f011704030c08090310020c010c080702070608070e0405040602070b01080c13090c031a0a0606080c031f050a080c0f040504 86
    0x491030751b1007500004411001482d0140c245540c40c000141035800a03a419405604014408456517480d0980109824036040c0244a90b15203c14071600c601183e01035580100d00020001d00d07901d0080040ba801811054215507404034601824100801d03401000ca12030406290030741c3c140c0d0320440d0f00518034840742d00d2071541c0351034070768040d03c4501c0703070032401c4558107014090074289640a0000d4000c401110324050ba90b6038441d02d005084808038400c1d80240000342040c0540141e001602d002540d0644c1090b01d12900c44d61402e82d64807100000030b13644a4140400c100400100740c0141600e02e102e1900000d25988a020103521030500304050750308100a01a55242c0d9900c41e00f00aaa035406903201540d05604e0303844000c0c61005601e080f01ca0585c0e0101480800f112034422003008200700d11b4070801904012120078a86d1002401e24002903503410218450b120250039040000c0070004c01d442401c1e5640c041c801e4075070f20342c08440e9115484500d6403003010700306801403a00c00c540c091846 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 349311825 1250 349310575 349310593
    0x908040504051503071518030c0501050d1401030c170c0907051608030f060a0b03010b0702010c11180108101802010f0c150f050a18020f030a2009090a05 67
    0x7100041400a11198102e4825680400c443c0c03010f0244001802c20244030700f007014150b04014082e0100c2e001821481d030242001040440c600f0070201044d42c0c0c003480c1056454083d402040003420908010b0800c0340001d1000000b000411100d910441f45400007024170b0301905c0c241e15480e80511410207070400360150010f601d80307104800a0842407800440f00054061903101e4030b502d500304480c00e00e180d03d02242840110b140044a8000414030044105d2940d0305120200400e4000c080b8000d0501c4080031030501004101a035800c2041c1c409408048841110944016030541c2841001e4280c00364010318000380b6448d008404114035000b00310844008982c3c01101c0c066504c1134010100042c1c0010034001034101d100ba4072039030000300380125100800c4030155045600142c102c6074598074115040b4000036558104503034058044442d010b000c4110004282400307100300d001441d1442c01a4205c003020350f80c03428540307500310a549042c1181d0762051155a200342400c40504282d002c4401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 349313075 1250 349311825 349311829
    0x1305070f050d020409020309030403060b0604081b041805100c0207060c0f060e070803070b01060813021011030c2113140307150c060b1c06020304061401031b0909080405 74
    0x400022010102c01483d0660394022042260400c2d1070700c51030390300009010018010b0345c3c007413110111021240140b4091514031886d6031081401084048800c85585a1466654030b60284810801150401d454004507180c000d45442614058000c03951602c05106909480050610103458841d218065581d41c0c03030b107681240c0d800c40e03542100c166881e943c4541c1f841006001d810000e0440400440d152003542c82c022043d82c40581041d03040000300020032222001000c15452113603010740e09000018540182100c0011110a800880784800601d009a2020008044c00c50080a02e1103d070352038200504000c2c18403580c030003240b0758070001c0c07003e01005d05102e00c56060707010010304480c07031241c1c0c0d80d05008080395030804007000b18001080980502025010341400c81c4c40440d40755006098100505072000c071402c1029044075400700c002420040540d003c003010f0b41c00003e0301d800c1c0d91381d24030300310900e10840c003603060003401c1c5c00b04c0c0056980761a0244038400c5520400e120b04150518003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 349314325 1250 349313075 349313077
    0x8090d0c030305040213060312020607050f0d0f0906060605250203060f090a0f0309090b010e03030d0e030f13050307060c0803060904211e09050d081c020d0203061305070f05 76
    0x10041e46c0c00302e020007030880844902c0c480c4100448c071400301800b1201100c1d9010303061120040c041e100b0f0000410510350480e0041040f40c9504152513000900c3c6180c925088005000038040184114a05140031800c540c200b00a424912051684292800007103e040411420162002034055001401266020b141c01c40d00a610940c403104441444240c2c0e1500d0b046111011400e0300032030607411003444138100d01e0003441400700d000e0914804040d00000842c4c0d0b64800c0d4103410400340c0c1d642c095501c500345c090080368000e01d21071003407540301c814400c50700480421034884c0c40d10906c65141d0019400e4014481c2c847c0243e000419a07046a44107020f000302da2100400444070306440010715214003070007a040301c1c1d02c0141a03481c8070499a418038900740e0100e82c0503400b0140054004100310326591000d103030000c0c540c05060f40c0d846040394405240c4490726400d80d2003985001040f03011840000d0350103140308607003c80d01440d0800c40c6017039000864205464404c00600303214005640940204 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 349315575 1250 349314325 349314331
    0x1503020c0a0c0e04031b0317100e15010e10050906071109090a0c0b070510020d0b0a0603050609010e0c1b0f010207050c09060301021201092d02090108090d0c030305 72
    0x3000d0315031000081e594050020802d40001070b841e51060140014160302c101d55001440c40318143e40340448058034054000c001c5601440c006001510019403094460034005e401000ca80e42d12078101c2c141508a500406009030103103000484a140e06540d61070101402c103442c1303d0940f9913515021499061100c0365000e031000744e4020080519400403503c50156131407080c5131030005041c82864618245e41d4400e401c1c0e102d541586014040c010204001080042c0074940d1840016a513000c1422a030000d80010310140d80e000c40398103000100e06400d034002d103105a00031a035400190703880d180e1180ca0f03d041a5450b00c9410000d02900c07585084400c83c0304001c00080c02120403074055a00348500f642e102c00d008542d40d400083d501c0d9024103040a06642091045000358100b00d6101180d00100c0c01c148070340f03401d0720780700d084955007504e500140c5120856484007104402d5407010640c0065031010800a0000e001600003c01801010409030381000d09541c0740f009256040e21708a024010207 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 349316825 1250 349315575 349315597
    0x80a0507080703030e12030c1b01090b01150e09041a0709051e0109080102161e060f05150415060c0311160602100b09060d031e021e0106150302 63
    0xc00ca00d0000c101e203000a0715070b26200350390115091038422046400c0110b0400c6c0d00d50070003014002e10602600b00800d540034826a00b400401070084101414050642d1040c042c240a21560012542c0c4025644c0c200207002180c0311800700c60860030900529120458000d014012003036001081c08104554298100342d903031030025041500caa002074140c00c000016410710340d00c0224011400c0d40c00c89010801890761800840c14207c0aa0402d038041003a15030081444000c20b4034031034640c80c046c28804840307800020801181c000c91040320010407056503189401d0122841d0701c0d07114641070088040c0807201c4848a0003513440d105042c1c0da0040d814030200c051084004200860540800420390082c000302c5403600381910b0000f0103402c06081821145c3c54504007601c50184d0b0f1560040d258104209844050f45034809003000c543c040002d401c804818105001007024880e400200c502c08a00c3c11850b0500c0d0f802c00c800b206080b50800d01c01c005020400004044c4828082c2e800b401028040e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 349318075 1250 349316825 349316827
    0x280207140d030e0c0102010504020901030b090a15020301060e030a0201020a1e050307060506010e0d051207020609090906060a05100e0607171309110a0503131b170f0102040f03080a05 80
    0xc004039180c20700c0c8038001c140000aaa801d85503402c0002041402c002540a000030401d07820070341c011a83c0341c02d05000290002a0080219201707610401c40541c0c404c0e000500c1071a17854864401c0c0010354028411200060140d120f1605e1500e008507459050580c143c000304211a0b82d9500c800190035412408069644244041380115605200a22885d0310901d80058145006000503021694005000340241040039600c4006440040e4044c0342411109a0903100c511510002c1c807030b8458103030144c1c0c03c00d00050501c0690703400040e0290090201306c070080c90281c2c5880502c0740d0b22164507426400207080d240e107450749080c40c10050007420f004030301c2a20f03501c004000d1441198400d401ea0704411440d0b403400c1000604500c1400c180c5100e10104510348403614100411900010b0003c408441c2c00546520400035041540f10700d10301544000c04400365144606400c00310601800c0700300e0700800c0f4601c03500d08010301c00c56050310850340d5901011400d644440100e900803440e18428450 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 349319325 1250 349318075 349318103
    0x8161d060f040801050a0b0109090902150c0109060e12090906060906040b030a1a0f1306050411180d0c1a12010909110306040c09020c12160209280207 66
    0x21004000d0004000782200c203540c40c0e107810481402c440c0000d00c2c10380b80c0c1f0300c2c0c80350800e1140c1c1c1c050810805c07114410008101c6201d2400040d01ca07424403e00000e8100d40042c0c0c03415805010b4202c4002c0c907019000c10025608681c25481d10b0f190307d0080300110200c1081155a44c1c54103a625071307040303c005071003a070500000c240454260741c8950800e04060a004c010480942014080e041050050910200b1188086008a45000c0e50034403198400c142d4404d541c40343c1461070740321100a05006001f406500407107499910954000b54408140c000781241c81c50040c1003c04801d9065980465580001e9107070090700d820003020030b41410070010040000405280c0426250390281060034000212103200c0e140110701003182031000d5020f50841804c110104c0e80c11041c510850b02600809651169040c1d03145040c03400f0241042440500132540c4603070701d85203030000c5825a1098130101d130743da115481060412070044540000300070085100042d203054a401900c05903120f0980305080032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 349320575 1250 349319325 349319329
    0x1201060306020c03121602070b090402160c050a0f050306010608130b04030f1b170a0201060806011e051219020a090c120501061814120a030c0c0608161d 67
    0x80c1c8520f104180c03950001c50304403000403031841032503000b0f0090b510020300b605040101946540c501e10030b10310001c00110350520343c0c1d03c40b0b4045441d400151454421007001529040508031207a0103494020308250b00c02040c4040088000000e0341c030000c0042ca640c1c1c0ca0001c007103820103001424214031080e03009006001030354080b00c4500a40c440d0326034004484034003500a00040100b00ca0611050000c0e00e010042004800507031500b58508100c55a00c1031440d02c180d016003000c1c0e2042c89644219800001d601d20514024142c5100c40c440220b07881d5a00d44c100409149a04001c041782d81155095921030101001107075040d0348060007543c942030707890b4071040c03c640582c6500f0f004a075074400c0807110301005115403400340885040900045280b2010502c602c42d0500030000700c0944008042c1003a80d810044d000400181000c484041440d45401803943e250000c5c101c805141c00340c0041411401094541d00c9801059103a0316281c1044004540c00c401148100c01c455207441c01c010700319 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 349321825 1250 349320575 349320577
    0x92d0f0204110d09020907050307081308040512060108060c0708040e190c0309022125030b010b040303170403210902131a090c09130b031e0f010c050405120106030602 73
    0x3e00c1d604400041c3c0386000e401842142d00c402803c00702000010401c205c4919040907466420003e44142c40d00f95039000c0c9850303003280c4215000305501000d40e040c0c01e2402c6600180e4141a07500c588240d40550f2a8803001201320f00900740c0080c01e10750107100500003170031a5070a0303940c008003040d8088141103000101c1011141d038501b480000036100e1400b0002c1d414015002d0742051200043c40724400d41105010381ca418402403031059004400c098502800a0b00c4c980c0406540c02030700088455a603030a5010302c0b617009203c2100420302406c210400b5940010043d0b12075601601d985810041702c80b41c10039288062000da0025958401c500070140c1c444d401990140b043c40f401c00100c113a101d9490003102d60300410307603d03c00c3c00d4101c00c00840140d0704065840701101511016500c2c001d4241c0c41c0d01400411441c1501803281c08107941c000950001076174080c40e070020561386421002450507003070f09d95480d40000802c1c000c0104005504000c034403418038840035000003800329180d549540517 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 349323075 1250 349321825 349321837
    0x1e07081b030910030506040c1418060d060909030801060203040f12030c0b1f0512070603050603070e2503150510020309060304110f01091a0922092d0f020411 69
    0xaa80e1010440e1b6810640320751203c01c0000d042c210022092001407c0e45881031400d0b2210402d0f068140d0109a1950300607200c03410400601030140303907103c0940000414040805074000307100200005500c6002200721800c3d907c081e0030b030501907801d1072110401010401412400c004800301d102011803061011035005030100070314200c4100c04202603c0140d48190422403150002040c1c0c003140a00c00500d48d002c03280782d4140891541d03074080000e03041417a240d03c8408602d0400003040301261500c800d131303140b051800d4801e0f00300d6191001e0880840346074030128a009500f001062149203007600200c0c519440501c102c0b46820207170004682c1541040d2011140c860515400ea10301c0e16089841d419824028645460130b0b61402070514000c040000b1004c44241000038041e1040d16801c0c4013031344084d040d02c444103074101000c00441c014a1030440644e00001400901c11071a0120010b516003004844030b668909146030302e52003450089810304981c1300380c2e151030700c034980c402c071001401c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 349324325 1250 349323075 349323077
    0x41e061401170c030303011221030906050c030402030a0f081b0c10030e06011a07020d03021501090c0210110d1b0806030102070b010311030c0301020d021e07081b030910 74
    0x315514002d2072800309040d42000305516009061406000e89002040d24116400c0300a0126030503040c0c00c2107142d8540040000c0881c401c80300707001c01e200b40c05402c50807a040c0304007402c0107260303120080000c20f800140c60003945600490307011008160f244800044103401030f02880d28059100400d0405080c0c2c1c20409107964100b00034541c220318084103010441c04160070103000000c1c40f08500c649031101400f40a803420158030942030700814030815906801ea0180504202d00040e0a01030b5031402c02040d01d0b041003078240c001181103106809140e03500360141e0001c0000081d03003400c2c1405000a501c02d906e013074009100382c400701020750090070801d005150301c06000059540c4000c088800003003120303001e61300402800c00003581345051241101d4000429107101076807900003034200b50041d4102ca074150700106a45503800b1982d401041261200003e080e00440742c1c0f805807080d4000c0300405484d8880038000b0660310b20400f85082144901c000640340340481c0c0c5800030f900d000380c0b6683c000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 349325575 1250 349324325 349324361
    0x501140a0c080105090c19020708010f0f050a09030509040903230301180216140118031e090b0703050c190c0e06030624060702061210050117041e06 65
    0x10307a900d070044680d501509042d241d40c185881d00000a4445100e0307170003c0f080300744e005c88114103007032310a2014201030561000284686801c903014100909008007942a0486c030f4200030602c40341c0c1d18440d007010a0342c19114107040020310010003000303144456065050141c03c03a001080c042c0a00042140030000011a0b0749950400b041035010300c600c1140e0039080c41c0b0401401070039055402c0381d440710341e5120038110103591000d41d041d0702512044403101c0ca01203a881d2840b0805030042d64101c100e20201141c108101807022085038a00078a01c83d12026400030861007011901c5400104482e01e114400c030740c141d402c89402902150304103c020746400c10040030a010600140b19102c0d04036008900410780e90030041100740c4043d03c54207003243c1c00d103151f180000303198481e81c041d28801d0740c00401c2c0d40d4840002030001c030015802156100e49400e12801d02080941c0200030341d040e2000d40c85604111740ea503907039400440f02c10340688082e07a02200440d10001a5540c02050000b4150010b10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 349326825 1250 349325575 349325591
    0x50f010c1a0130230102030a060302040c050702130207050a0b16030f0c201e01060e09010519150521010507020d30092603040f0209040501140a 63
    0x1041402003900540c440a0307031191446000f1800e582c41582c0582e80107611401ca058402e90100c00380010141041c0503075002108020340c00d04103078401d0341100d0007903500740036011803c00210365910850100a5209454181946003504160301810000703105030112508114262106070484008a07031034170801d00d0404200e076032268136000f200070201c0c5489003403060501e506e001818410f8030b01c1014440380000003075082028410041c00761183c0c01201700780c0e04541504030323941c06000503000c0c2001c0a610711001c50386070300052080c0343c4161003140f07a80c6000010702c042e00002e0064400c030a010480c10340404620342d03a45802c503402d17900c070344241041e0580b0004071040c2500c800815043c155000341c4203450300315401c90034100811502c030002d8095543c1000140a15428500350310445a00d041d0000003000600741c4003178403a89075070520b010b01c424408010141031104840c020082030a11043d400117080540d0031359001071140c000461707007503448051a6000c0c0c00844904d522a601c030048 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 349328075 1250 349326825 349326839
    0x20d02090420060304032001060e010f050307140a030807030201090501060902031503010b030c06070228062d0f17190b0405150d0c0b1206040507030c09050f010c1a01 73
    0x103607402d116419603a1130304501d402c0c0c40c0030308851040e00041144244006000240040c01e40c441000351420f20f1106903696110100300c48c100005004031800780c0720350100407a00c41c00e4a4540041010014810310303000303046540da91a01d400150003141035640b185a2200016000e0041001500a5820050f12454002501022128491121406a454001481c0f0341ea2408a40d0310b082220030fa850329030300d004520108256a40b1220499940e031a82003000048000400100040707942a9498034510160061054081588030203580d0300181c200c0d14642c142400352018001c0c5042c14205204440101749004016200448204099201403110920340003101d21803624101d0003034408200525015085101d1260071400c030a10901407c1c0c00e080401c40e440d00e0840c080c0c5490002140c803000600789980c641c3d203044e01e4851180d4201800211120720a20803007800143c0ba581f2a29024901070034070246415286119040144017900314020951a05144605500c281305200e155854084 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 349329325 1250 349328075 349328123
    0x3021e12010e0a030e0d03171504020301090c020c0306100e0a021b0a06060801090c03021c0f0311190203030706111b03070c0506070f03030c0c06061211090115030207020d020904 78
    0x48410b10414152006c9008642d1000c2e450409024020078100e054403041d0043e420b0011290784160300c18000000803850700504c0d007103102c13640e0194003100c00746580d034810982c40314803c883c418a4003108590800c8440c0001e600705400050008006152041038501d18084c1c03680030310780441c07550084c10b513a0104000c900c144001021010000c100b816483d640329003242c00030b440042d129940c58050308191503441b031690200940c2c0082e60350081e400d01e02e07020300030f40402e4030358140b1401a13800089982c40490760041c1c030154028060b51803d06140c1c0c500004200ca02c5098150305400c0c844001c40300400001004000e1008008584642e407600d0200500300494200c10302950301444041d0014005101419415034982400f055030a144030085507071089411025100c141411070000740036620154000b2a07900440704d01c00e9200c00c04041c4140c1440a200728400b180d0143ca008001a00c00e601805105100620624a4203010f40014400400945090351110f212606004100510308 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 349330575 1250 349329325 349329347
    0x906041b0609090f0b030607170105040b0d20030610080c06040b042d0b04030b060f091b071a0105010801080a260c070306020901030e03030103021e12010e0a03 70
    0x300409506001005091001c24880c4140300f0f52619501c1d00c080c00135401000041c0000b03400c4903400c0ca4542001080201008180d190b8130300c844c8004226801c0c58001d50a100390090301800b405c0c2d403c0e5542c102c018001e0304d15042c120707041b1002ca941c0e0381ea041c880c050042c00100e030741442c45410100300904042451030201e100c0d03402004108002c1d901c0c0760688080740c0c95103544805080c00e400189800c09800c0e0190540ca42d503415002c100d40010324084c0095034005d61806549079603034010301209504107004e40358080d0f9124000703004006000c2118410741c1c8004109402c0905555a41c085100c242100380820a03202d0018400e65a000031100c1c0107140c590002d0482032000e460707602e10030840c9010003848a6200362030a15401190301240d0800791660300321070703500d40d0702d080100081d00300030b0b071080c002410000b01e01075101000040d241030f2500100149a8071025890380b0b103041308264a1203800117060b41009040042c280701e9048000501030141c03c8040b218540180f05c51002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 349331825 1250 349330575 349330613
    0x1306021e06010503070e040309090207060219030c080105060a0309050a0c05011e050301030b1503100b01081806010b0a0e03030403031805040207121d040204080a02270c07020402070b090604 83
    0x7900104010340c0c002441c10100c608a4002050546550500303c42c000400e8100903e0540001080070411142d94000e0450b041100074400505190b0503085054a5541c40c441001a070048014441032401c0d90081600c0003041c100002d05c1b02540c0c2e940c5007801c0440c3d60660380a0b50042c420446540c00404040c0501d032a4138103a1100c0317001c2500600940410b01020b03100d00841c40c002000e044031080c9070882800020101c3c0c40c444503200d403410243c0107003c0700c540001c0401002c211054240c010000c80c01e200100030703040980c241882110a50003445c081c00400000310804081c03a20f050000304060750081d03076500f164a0a07102541c032518140d60056006610400a00c8045803003012107003001038061030a00030450f00103081000a940003446190302070310000d00064614070000c3c403004854402d589032140e614000f41204a00461650b044070b01c9407100c000038251903181c000402a452009200504080d00703911540f607410400c0310015144e9000f0301c14041400b04a03003071000ca40d165 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 349333075 1250 349331825 349331833
    0xf0207080f070203010b060c0318091005130f0212010305010b031501050f0d050d0f021e0309100512040609031701080d1110021813140403141306021e 66
    0x500e944a200c41d1240001c40144003402181c4602155020740000004010090445445110160903580c490313102e009460015030740a0355882c81800c0140c901c0e4400e0300391a0210f00400e2a20b014891120100002100c40903540d10403105007030030a09c0a420900510440049158114503159086803028401c1a1003540406454101040c242c01101d0540d0020750320468002d903000081400051030781360041940c002d29051810032584010008142c2405600b00c0e0909182a62175203801021806480c0c1190010450181c0270f0500003c07280501c1d2182c6845c501d1302c04646542480c4030380079903003114156180d400a42c00d040d03009040e42c05000040d038054590303525006429581d010341c3d5860700240500f8420298031000140700d000050f90300d0410030340d50703400002940c1e00711003210b0320031720b2051025a001503584216132094848807c0410942d941944907900c00391540c0059015401c021442080409402100158418010b10b038a40060110783c0021500003444040ea844540150780 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 349334325 1250 349333075 349333087
    0x2105070b0f0f04020418170306010e0f030a1b08192307052407050715022404140d020a0b01171c030902090708010f17060a0f2009040f02 60
    0x84545030181c0250703040318001880200e41d5040645542804405000c00f848612540240e01f1004000d6100c0e0300300740d8601c84028242d4041103001d174004040690164003101041c0d0000c0c030000e002d1071140a000300701b540d0103a42d610b6804d14080e042d40c9015640000c905001c0100084500ca542d00d102c0c8070218030402c900801ca0042d920035280c450103120303104035480c031148903912951071004580e52400160ba14040f904000d81c2ea04854402c0381600915041d024071428070209222154951400300384842450907181140c03000b4020f001a100c40e198241c030400048030822140f600e4400540261101c5180303803d01004855059108075001c0600006810340c006010808040740c3c0401d891045a280811030304078000d080e6044000e40101803681400580d42d04101c0c254101d644803941b0641c4140c548400480d1010080c50010303441d030004011400000e1607811000220400210004045400c0040421411010040ca1a040c0e5002402c800e035810075001e00369240040b16410b40c07800b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 349335575 1250 349334325 349334341
    0x905030d0f12021206030c0d0201050a0804030e0907030b03010f0b06160c1a0c0d0540090b12161806030507090e1908162105070b0f 58
    0x180c8403450310402040c0400c40c42141e0203040c44002c00300c4040c0d41191103001104000d103c010094841503c80d00c03512407120076626240184060182c0e0607965941003001c103031000d46140750080e00032024071100b01a02c2c0300782d0311502c4005200c0c00859902094084400d4185030854412002a0200c141004200d00780d50310f032002202c81100a034502c40c1cac903a0050741800460071609810400c0d01400c2c070724103408115802400f800c200600c4000f60390f003010168800750354600c68000202d21441c0c02c603c07444139000d2072280510303888106600d041c400c0940140b41103040031064000da4407040c2c0d41c4a102459003841060001303c4d88120009190700d2030342014201b43c02406108003c000754100220540f441120303048a07005540c460100e40001c2d072103003140406400825242c200302d1144d11400001d8180b070124059503150071081c0203103440741031246035000000d000803d443c19200f4003c0d410203201c5001852541e090b20355030303c0da140d1905140040380180d014000e030501112590501203a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 349336825 1250 349335575 349335583
    0x130b09150f0f070e0a180e03130816030512071104050901150f080606060703110102070807060b100c060e0109050f0c19080d180e0711011d15040c030c0906060e01090503 74
    0x707070b806c12248403640c0c80180701110190103848448a0240408903030420100f1822801200752a003a00c06e40d842c3c0349003c1250a4240707000e01c030242c8070390b1024110720801e40ba050002d010711405070710002da550320400c021406654007510b010079280e40d103812403035810384800350721006844940301900201d45400207040d610325014261038810300380001d01d0410903020320071044000301c0c480000d40d2910310343e091420700303500688403c4d2415401d086800d00d0030721300501000c01742c1c805901c40d12030515040d1286002000f0818069080d990380d91800c101268040000c010a83c0201000704182c0003888140103602181d0310610302d40945034001400210340110f82c2c50306404481c5000703410303203448000c07180e1004c0071548000350300784000040c049000d610a00310f114069000000f0b01030101104030b0481045229400003040f0b4010400d0b061601c60080d00d400c0e0440d009000320500141c883d01c943e809030145071312100e900c0350344402c100841a04150341040920090030541002e44c41d00000c02e0311 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 349338075 1250 349336825 349336829
    0x30b010203031b04050306090706030507090e070c080c160512010507140c0a080c0105100f08031c0e011103040606050406050d030c0c151701090203130b09150f0f070e0a 74
    0x140300303501c0060f1889000d03002580c0003880000e0071900b042c106450802d4413000d0034003840001034140000105101d020329141d1048407030b402c800c5282075a9038001100c80441108049402c50b4003004507440d200c0042101580c809901590450310f2440c0908010052800e103503601040c0c1d050100f001401600410140d450350303400708882e95100480d1145508044035500000c1c20100c0204c0e94400c4250154000c511131112502c554001e20780340c0155501c0c0b8903462180c804103610070011034030781c83c65040004094a40200001c500c1d41060401d0358292010b2210943c84203902104201c103110a50080d90001d1400b51003c110743d43c140f2012800c00d01c003220001e01800001380c1c00c103081000804a00d0010064a40201c0c4660f012080040608412040c51894000c901c0d0000c074280c50329101301c0e07010344507002ca0703400d007111580d4907043d520000a2540f44140240201e804181c50014105407045046202d4203400e07142072510200484405000b21b8204180190300c9801ca80350f03081c2d2001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 349339325 1250 349338075 349338091
    0x5060106050c0a1217091f0c18030b0f01091401090902060c06010e100f050d0f0218040804051507050618011d06040309080316060b04061707060e01030b01020303 71
    0x1d91903403031402c201d103803e55001d4014a000d0450321419412584140d001d0000115414481c509440300c03490603540d45040000c540d08111488008400800d482d440801001d000d800c10000010f0101c071841d6594035603520545070780a00c0c8003080001249a840580502481241080038442130415901050414024644060366418800040d5500c0c141038505040b2180e08031145507031681c00d00402c0d07030000d80c1d0718080d8010311040821400d480804900c01d84402030100700030120981c40d181414400c0080a0b03810010041009908010391600c030342c0f10720b01072441c081e0798030702d084144881d054650011006da850144011800100c0c0031610507080002082c95401008800d1511801040c90302d18402c000c04131104410380201001c13818030310450103a21072240c070a6a5417101d079200c4c803490180c40300503460840c4000002e04d50341e1105c0b0f41000c018000140700d98032518510b9100348100d04101e007940c0303c1c00b410001603500042d00744040b9820301e400c2c0b00e00040400080e68138000600144 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 349340575 1250 349339325 349339327
    0xe0604180207030306150f08130506040b1806010e0601090b0c0a0f020a1502061501090f150314010311042d021c020f0d05060916050a0903020a140910030506010605 72
    0x10140f51107904210090440c10341d03482d035001c5009030098219055286060041030380308001400500d01001c4818003103800101502c07165550f6982c20902c0d100042001140c1805a0801b01048808100d00790191444403152069400c007440050650212a030209101903010403c1048032100071a442102591090114951460a01c006920341c64181c02000740e285010100b40e13841d644c0010901d000b504040d00081c08100c1201c0115081c05071402080012860344000300902a4201e4603010803145a00c0c0000b103c500c034900d840c40106003131b4400d6400b075040c410022a02d00c0c00f445a040680a02c60303102e4000741440c040c0e1b03007401c070a0042c900c5980d0743c041410807410714151104803094423111400c40d9104180402200a83c01141c4c030b00303c0c25032500001500310305100c40014010f01e9600400820300c18440001c43d910785c440220903042010b40070700040140c5070302008501600500140d007604185c1b6106000401000030701115113203039580c10800c082030300400c5150554a2500d085 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 349341825 1250 349340575 349340587
    0x15021c09090917030c040501031d0303060d03091a030123090a0902040b0a1e14090c090301091b1811040302011b0f0b1608160e0a090218010e06041802 66
    0x30714106801c0980b143c00384400004006000103040024426520242c0301004032808102d00400048100c5000d9082c941c030810201d81c140c0750448500c1300301441b80c54005c43d42c5440780140540e0004a08101154071700200c01400141414024415820300c1000d0b12081c4d034a40380d00082103188098036a240169844903883e040d910f968010003010b25014142c100c51559810076200b400340c650003507180d00340c1c144402080d0f04002d40d041c0c804000008040d00c10984402d451050154031148143d41e00d9903aa10800000918411410101c04a42382d009039143d407920601c40610420641002c031a64501018544510502025142965020310342155150911174581c181e100e80742d81e01514800080c080c0d0300130000c822036010300c41d13002d040c0016a4008013400076100240142c50149075441000025034603144560300e1506960002044500c3c11795690000300200c1c1d103c103085050400052900c0000b41d6001410403100b0071080c0d549900c0d091503d2490032403d4854000d603172401d0740000318 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 349343075 1250 349341825 349341833
    0x14040b070e0a08060c0c010b010c0b0a021810080a05161e110f07140d0201080f04020f0d0515060105031311030106050a1e090e0a030c1403030115021c090909 69
    0x40311002d4100d05088130f0050034428201e8400390403800c250401c0390f0030720b261511254407994000015a62112991015480d44807500c400303034001c0300d40d0060610660703902107010f036600680c01440340102d13114500c041c1041d0781200b003134801c0100240c03500244c4000c18040b2907485000b85003280c1d0150120103602a9449040704c050441c4082d1024074451001900298030700804c0c0802102c01111540003810084010300c00404806900603003c10f41c100d000441905842840d01d07441440109100703910b180741000500e182c10744407425a801e61140c5009131500b41c0426604c0d42045003401d01c5411440c1098100c02d0804420b4001484100e41c110f5140007928250460130240c040107120700b42007501c0e003800a4003802c58190030707100320001100010340c0c8001481a824018107a0028040d030001c1501c080c0c803500300000c01140c04040c2c00f06581d82c1c1280038070285001e03100c24015480602030308403009281503204074800d40310751042201085030325000703c00038045403104c14000c0740302a0300d418 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 349344325 1250 349343075 349343089
    0x3171b180a030210020d0f020c06030a0c1e030e06010b07050c0d0501110301032d030909020f0412060204080f030c0c10020c031606110a0b072109060209010314040b070e 74
    0x80002d4112800c0710602244d55001709000d0b08641165580072243c050b43d1000b03d0365498400449600140100b000c03500b0000b540c3c00c6051006114100841c1080d00b40802010781c81d0100c00b9900041d46da0310030904800001e104040c010011148120308114541c2c0329039490300031100e11244605030311151142048400e42044045001c2c07140380703945940e520b003841c001d14201c081d02c8007041c49001c80c003d4620540c40d4001440c2d43e4160b560f10032100c1c24082030070000d50001c000c0d41400e400601000806841c00b074103a044140c403070300e000758541e0310340780c0704515010440c4850402038005112007580900002421310404404030703011512403980407000e90030000101d0300d4a42602400026081d03451448030440c08482059030b460b03172207040701040503481c2d00d8031540051046004001091300350740329100c604290104c3c07240440400d80500d12120403144840001c84116401240700700c080c6d0307090312428680b00c0e6100410035207490590b9800802c0c8100800b8401444143c40840b01140c0300c0c50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 349345575 1250 349344325 349344329
    0x2060f0606071a040308040201091e032402030a060f050901180903030b040203070c050601171b01030b0a270e0a140309030d0225030510090501020702090403171b180a 73
    0x12030f0624031401c25060042100804660503404210404000a0418000400010402c06000d14080f50500391b50341d0180e03041c0c0d0701e0340382c11b050401d9202c03400c041031461000354016078101100158080ca80109040c01c8031075070740014401d80d0000010021041d07603607122020080c08141c0012290a203160503070007050a00c0f24150094804001c001d03089402c0341105c07440c140580100c60040c0c1e6520141001501c9200759031440750000e0816100181040b01d031203014500c14103001c92511840008030300800100d60000100180384903c10440ba0350b4901250103119400d8014004c81040200040d5110800c607801454050409940c0c0301a48007402175410082c4006d00b0798034040c25021001b544d42842084808810010610440c007090b41c1800440486e68480080c02031000e4140c0391100400c0c0003101615a95004c00c401d00060391405519441b5500c40d40300c40d195480014000b24040000400a040c0c8100c0005050b050001803001d64040d000b03108100c101d00352840000c80d6001c440d80d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 349346825 1250 349345575 349345613
    0x91c0206130603090c08030a020307030513031704180917031f0b090301180f020918030406030e0f0c2b021309020310090f1101031e0501090c02060f060607 68
    0x3002c07034100c3e4550024099540541180c00105c3d49070303010395840c0d100341103003407002d43c0c030030000d02000138007400181c0011080d08008180142c1d90b900c40b01a41412060a150200340000c2d09115640d0035a1880c81d80720454103040054001035030356150740e2181080500c01281000c40000c0214800d0311019546e01189841500050b98130b0543c05000d0b003200425911035400c2c241800311001100c43d4140c2d846420054006404c0515008e0280d42000542000d035184d07a4400c90720000c1d0740410007080100704036940040c0780b00d085010503081c4141c1d25080c1340c03240c101c44901410356684600014a02180d0b1021005829640b1140d03c9a0216204000d4200f1100e03d1600c058080c07660107081400d0081d8152290b0604000d2040d00710746d50440010320040b817404000340030030803800004e0020241070500007035910341c2802d12030035030681c080b0000c88a034954005200c6040355000700c1007800e07182e000400c0c007410b0080c407140c1008001800b0394003502c4c02181c54400c1c014115100c174200601c3d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 349348075 1250 349346825 349346857
    0x80703030815041e0f0b06030c030c04030818010801050f1f020109020d0501062c04030c020d060207120e03031e070512030708070e0904111e120a0b0903091c0206 71
    0x103c1c80449003010800750092404c0c03850004401e01c0b0410a002e055040c0c03c004210b03902d150340c0c4a119400c07540000c0c0099051400c184408400a644000144103041000480107000c201110006041c0c60341600164056202c1401e110501c0e00d40d00a5915030810149614685007014403040340180070f411400b0354089000342241003400010341c4914203031141003c8004844c240941c054202124151464030102c13840000075011911581001e00a9480101062101d0344030303440b0b003810790304440e02c00e48041c08a11069201c803034120303c1d40c420fa01030580185092000000004a002c1001c161205124800081038410441c050000d80741010501c64100d031207091105000780504411180c44010904600d8440c10034a4044200ca10455000d1050042d2a0444091210070491500d01c213805848c1c1101344040c035552100c0330421194020001c103038000c2c3c01e040c9454041c40143c403004003a0410000180d60f07880303c4104000001c007040b242c2c884610b051011a030b840c803408116a5038002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 349349325 1250 349348075 349348091
    0x11a031303020115060306090c1b08090103060e0f090f1218060f0703180506041a0a11030316020c040501060c0807050307060f09030e0a0510140409050a020304120908070303081504 79
    0xd091f0b40f24409076090312504204082e4100020b894221480310f41c0d070420300c0c1c208850300010b1416801084105418540411850340c2c8540038034400d030b8240c2d602c2406014820800c0440e0004008041c0380c8041d41c4010702d51181ca0b00710182c4640304400000c01002c101400b0a10192103582c21100e00d480442c6c0d509075560441d0034000e100060b4028010341400ba4100002a45c1ca0110150b40903680f0000c01c11440910000030201035601070140c83c001e20034595900344010405001651140c1d03100708911742113210101e002401e00d0003041105106524000040c00420f91001c0d01d200144da00c08801e40c0c0d50401818000e1541c01142001030482d400c04c035402904400c580c100b254011321070784602406c0f07500b40303080103011081801440e030800b59000d4003032445031080da16601da040724560f02c00d18054642c010b910641d00300b00d0701000b40300d40000c1403100700304900c0000301d11100c0da458a00e0b10a424031a60644440c030f02c0c0b00283c10080c1c1100410b50b000412103000050410080042044072 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 349350575 1250 349349325 349349327
    0x60705190501051b09010503181908130b03160807020f0f01060e0610081b0d060803070b01051e01080a14130b0108010c08010b0c150c12011a03130302011506 69
    0x3080782d0340e0303032041034401300d00c465142124151000c1e101c058403898256560300d2400510070101c2d810810301407242e03523050046852010420403546014036403841e0b98040e000303803041e6103581d25840700307540d102c0800800407520000b014009a003d190b103032223449a20740500407840c00b18002200c10321406000000202c5013015405641100e41c0d024405000780da80381e00b003103240d655207281c44010403200000220b4a040104030101c0380548107a00d1410f00c001d07203034500110f51444c0c00545140d4400a41e000c240100710400d140180000c83e070010306064841e421034140d04064180320b05220506e40401c107040c420340c20550040b515030000c038102d480c1407010300c00c000901d000103582807000c00002007070040060003640103000300d90311180c4403646003048240d12644400c0a201003030082019424402131284840790182d110300010702d440342000c1210305000c4406134070008854002c00c0c0703400f1880c4022020340754000d450350314484d9560000e0605034090229201c100080600c0814041401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 349351825 1250 349350575 349350581
    0x7030c080609060f0402010203070627060522150f02070204051306050901020915130305060115140a0801120219090e1018120504050a0b04030303051e0105060705190501 74
    0x500c0b405400c407041038944c42070b0501d514405641c082e00607042040b0410100b48a50441c2200f6110503c050003035814401042d20000251b071401c0704d0b01c0d600d40c400d000b802e02c2e0007140c1036210107510030100c0c24844981e540d0746003010701540c00364285440351082080b8844c954162141c0c05e2700a00240308a1600104074038940030f04003002c40b01d052034500420f056010500c00d85034505d40180040d403441c00f0740c81d040c3e4540d07040a0000f54440703c0c1100040b0010b0001e00241e4000e0071195282d0648124444000d00f03000b1050341d400307201700d00501101c0c907560742c8035015070304490004180b0509401140045200d807401020096800020f109001542105a92100c1c0940c0740c580240c0349035038488003203801a184007642411350162031380f20300404a501d80d003c04400848504051389010b40c5c07900070640c00300003940141515440807804000b4150103000300da6000320520b2400c9603080104142030702401e010701525000b9080410301d0810403000b000313344c0e110140f0034400c00b0401d030725160547c06 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 349353075 1250 349351825 349351831
    0x110304020301290d051006090e19080f09120106060f11060606040302151e04090c0806090c1c090822060c0b060a0302060c0a03081503030d0e07030c0806 67
    0x35031a000784010121201c00b0b842c3d00c0380b100000c41151210840c0c0400c00100b042900c00c0e0341c2d41c0104003010217012110300c5042e0042c5900f6001190031800741d96885d0800c511104010702c0710300d550f80d0762400100150201e5201c46448e80d203a589552040020034102c09290b0148a0030b0f602c0d2840119916422840306400d1044c196030f540000050f805a03552101310a844050b00904240001c0c03006262605109410640b031030b800600700b1452a1810b0115582440302440240e0000340901c299040ca000f80700c28102d007420b010340e140c20f00c00c01081501d100240008140000030803c0071081000d81040107500e00d070f642003070160b152103042c580c1690707212020402104125244007030812101c40c0d46407049403000d4980b000b410805d6156090441d0b4003d20640d4410070001d00800141d0b1908068026842540001d0030100740a26000e080c10401030681c030b18114030f6000030031039603400104032801c00058001c0452141e9520b0364a034075004007130300000c1003401841004034040b6400121244 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 349354325 1250 349353075 349353079
    0x3051b0610050a060e0607060207050d090612050601170a110a03020c0f01060b04092c0a140f120f09060304052a0604140112180b010f12031b0611030402 67
    0x12415074407801c01c4900d400300c0c441e904c003156101075201c00c18030b48503001d41640c07800b0700400f5240ca032a90b92201e0800c05c2030380070701000c00c5e0306101c1442a20b5010b011501c04406240041050303051030780010700898425076081900b8001d190002d10f460f0701c41c3d00301006013502000081e0b1114080c0c0006000303500042e02110242c801ca1040e1030743d5140500905c0101d802d001d82c1c1c107141c5810000b41307101070594180a0b0f04442e0301c8170000305110311490f5800e0b880d14941409020086598504080c04c1e0985014000c90b59101c5081c0d290202004144400d100c0c010082c03459645c0b038a51100c180600038942040d80c095004820003060020104001c2003419454202d03298401e10513040440014940399059004072080c0014001407600d0700c40c500d00c0f01c005042408480d181800b0841c01d50350380300d0356070325903120704c7c0a850b08008640841c14050070107140d00c406c110303040981c0c0191205201d41c0c003500b0011843c5040d40012070200d1100d44c21604041c080c0004410041100455442502c3c02c034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 349355575 1250 349354325 349354351
    0xf180112060f180203040c0501110102070210050304110405010305060a090f14060915100603090318061d1f1b0c080105041401052403031612020c060712030903051b06 73
    0x900a0307441c1d4404c170391180c0c0c0d100700304022460400e001110000e4205201e85084d40d070070007403500565100c05820200b0003456441544e2881d01e0b207428001d48510140d11030255041000510000c1c00102e291540141d483d14005483c0106042a0101c0020701c54007900c010741c024480382010f2004641c0a10030654041110b03e0407214501c01c0910307480403995542c40086003002806100e100c0d40001031118000c1c81c08034540c103056080c100c1d090750164041c41c0800c481000ca248442c10b080045919a501110b800c000c50030f8000b400c003141505040c3c2d4000300014844005003030b48090726000c2005400030b001d40a41500c0d9860540240b501391000d0300c0e809044107980a4540c0140201c500c1503512031540c99000200c039000f00401c403047c1c000c9560501040c0092012101c2101c9d016800f02d020301c0c0c1c58518054801c0004e420001c91b40102c82c040d20b010010000800c92040c40380e0300030b20041c80e00003a042c2c0c1c281000c5034940112150007120f00d004150207000224001a01401004d60504503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 349356825 1250 349355575 349355609
    0x3050c0d031707050c030c010501140109050102100209040207050a080a030510061b03110a0f060c021621020d050105150109051003020c12040b0c120f180112060f 71
    0xc9080c0401900060014061480b2211540c2604109a070040860700300181400f000f101004c6c02c5030440940040680e540b2801004010388003914038003510000e003032111000b070a0400007501c07100411000c10602d42c0000760040c031501d0f10350448160302d170448240c552030745183c0b40a9500c0c1d13104c500a200080d0410000c12502c2c00d420880004440f2a9219602c00f01d2900f040c01c2c01540c54940c1c20340a21443d115003d18540303090200f04585072150301c0c411403124940c40c140040350380c1d0842d25000c40d40701034032500104500300300c00d405070703002d51210340810700a6120f074590400003803400079000086c40c00d9000c200700c01504214040c4c02e0f03001641c6104481c03000112109440b600c00c49620451520302d00304a24040d50080040130300348d00641d0003402e0354a41c280456481603000401c200c00c00244179500300320a2080e000e1044214103018501014142281200d00640080546000480041140e1030b03000c1c580b520302c40320310300c8400e1107495902c0141442e4400346108040002d0201110 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 349358075 1250 349356825 349356829
    0x10b040612110d0b030c1011150f190b0d080904050f041509050c030304290c100203062101060501030e0a080d09080409020706021c090302070b0a050d09050703050c 72
    0xd003802c10012040c5003418071002d01c1203200501200c910041c0c15000c2d40d130b0002802d0700c0d0041c10741e450000d00c3d2101690f44d26414401d900e882c0c0072074041c03c100070941081c800349034070b143c080c160081c0a00c040c14450050700901c0704001c10030045c201e5480704202034908100840d0401070101c0c0001290b08015582c1c4060b10840006001c560061041c2002c85501d4401c3d409a80408103490045080300c410015a1300440e28642c0325030040d64850310110401d40811800070030720004903a48020013820280c02d5152030343e88840713032030b000000141c001c4001505074642480c03c030441c09070108207c962240c0f00c44003900034501405940e000909000691054003000111441050303482030071107103070840400f40b0344010001c0b035200b147d4100d42040001245e981c0c1e80003406046001c0c1c1d00050b5034080303000ca0ba0307450300c8000c0c11807944607050902010100e900801d04500700c410740207840350b4684480404889901c5117400483c5070510380804030052143c005190b00c1039a2141d4100c3e9810580981 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 349359325 1250 349358075 349358081
    0x6090b030f07050f0903010e010f061203080402063a0e19390801060e090d1d06040f03051011041421060708070513050d0f0b010b040612 60
    0x80303400c2000d9418000c02d00080c45880144502280d4648003410801d8180020703003500c4240e008403008c0e82d103c01580c083d03403007a4426440200070740e42a00c05201643d035405007040d44000c0000e80f2960001c90003001018080c041c1112400851080e01800316140c4840f91046400300d0075131040c0d52601001000c4d480d0f001900c50840c034001c80b8140c403074110517991020700c040c010043c61800c0000c1a601e40300200886c540d601041030480411108034107081c8e200303003146c901b82e100e000d40c10741100500c510002d000c20440507120182c03521700c41e43d551200c0000f00b0281a00b00c2190030640005000446101141d0b0183c15244200d00361081b521101c02102c05032034080c5103034020100b0800c410003c41803000c9612845260207007030150000040c035181c5c8905100c0d07a82400c1c094006a02708148075510000b140d80c050658180103062520280c2c07190122085802072a00880e08660340106000070769100081182d07218101401d05d40c2c4070007080e060360300544031310000b065000800986185180c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 349360575 1250 349359325 349359331
    0x12020a260417070f2606040308040b070e10110115060f050a0c061407021015151202030c0a12140a09140709061404060f0e07090e01060906090b03 64
    0xa481641440c0c24032031803800024103411402c400d4840c0c801c0000d240004a201c0783d0052036030030040300003032107814010700281c8132103124001c058001300304000001e9002040c079a0131541041c0d170203c81ea55003070004d507401c44054501c0d980c0141d1194451b801154004110000c40c04108002d105460a40c51800340ca040035010b50000306100c0c0440d0011381d4410405010701e455146800e084441241c2c840f00c3c1241c0d460301c40e5080268070309041100c0700c0d404110980c80095aa1000c000901c40c08030006d00100350b40c0104a186414501414107041c420901004c0d4100e14200455880c24090040c25456205c0071031200414044084940403403040d01c1096102c051642c8d051420342c1d105411705000b0001c9d501e0485841c00601c58101403202c1c02c00520007d030440c0b050002d45642009101700a1070009282c1611540c185a004d02648811040e0901118440008841c050310795405c140d84458658100b9282c0700c02c2c660000501c82c1e031103014501100c1d200d4079110707165500c030a20007545200803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 349361825 1250 349360575 349360643
    0xc041a0609090403140307050702010f02160b0d0204170a05060601020a2d060c030b03011512080c0c100306050a0909210509031b040e030a02070303030509010912020a 73
    0x18042078015003880100303030b503105100303150020300e01d42c4a00216244da0030907100c44000035408030310320045503008100d1000142040c002850903089110390240c00041070f00401d400c0000115050641044a4060354080c2c40d90280315064607a540c200e41e5958104110140c4240c40360401140141d400072030307542030704ca820902100380d9142481201080b10740c0c04440d030300c510380c02c05d0724100851603a10801a0b0719030300d81d60101d01070052000301402d4500070340310104510000340c01040b510031041c3c040c5558a40c030215054480040e000c81c1410300001c10b001940184c0303410303042400c1c03a6040d0700042c2078501c103c83c42c2c03290548501c1103104480c20300c28002c107082ca2101403007906041296200d0301c94001e502d8160b00c2c21700540007080c282070040007203140410100f20301e2140703480c0ca8025044d405174070740000c505190403140c0003955520b4070300c8007406144c0d0782c0c0042040e8030300a4210401c0e8035000903d007034400710b055070b0003913548000c49829a2658501c02d042c140f140c0400003203803061001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 349363075 1250 349361825 349361827
    0xc020316080d0f300f021c050a02040b0f0d0606080f0a1d030d14253209010e010207030b0712060e090705100f120207020f0904050c041a06 61
    0x4a41c010354104000403003440a1248804c1c12200042c584452003010704003800d19850401c005034040015600c5014503c140b050060040d18665002044c0c11031084080d00c802040c40d4440081d46030082c481c54011441c1140001080b489924091009082d400d940031401c000041d82d070401200d441c08103640303009200104402244128199030411903c003200100140424040210007528503840100c0000109031200702d2440725002c0e40304515400035150400000c3c20034007212600704030302d0a00404040c81007411180010702d6004020024005050910006040140b0320b00c1031960030030800700340015181001e8a4840d4070100d2040100c0c0d61150b014001034071014816150382c00c4d00007080107071aa455200150b40640c0b00300303990203210424094101c0301e00b80010720960350075060803001030052005004401d20391040ba45ca929801031080141c4885e9903100064803544010340096010810200340b00601c000820440c0142204841c10442200000d02510283ca8031500465100300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 349364325 1250 349363075 349363093
    0xc0108010b0d0f0504061a0a0b0f0a090902070506010f12020904020111010207050a111810120c080307030806040501090e15181209180906040f11100c02031608 70
    0x1103014020001c050b900203e11044008008000c5450840d4180ca469481c0c038400410000381000a40c1c5010060b5040c0380310a0a102440400b8440e540c80c112044c00c0000305d030507040380b01d413802c800a80f01130a020742d03489400d8140140d8a2100307008a5040300c0300c1e1100000e0f80c400c12003d80140c20350103007903000795585079001510b03549016601c0303880a54003004074100094040c44010705080c0708000d1480740c4200501402903005941c0046101c4104450074850b8000010381c1d503900f100d00b40a0110600c0100f803801800c10f1049900c81402d61101003400d4007015005248244900320075039081100340e90700d21890042d600885881c00158101249101100322031030b07809940400020444050000103510075490b0540508118203a4480402c041120b442c180d08000c15107141107003e2692420005083c64980001420060cd5000c05600100c200180070031b01d46001c0b000109030100c42c20074084003400c42c1e14240c108034464012501000c009010a038002001e41c0c00020040111300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 349365575 1250 349364325 349364339
    0x70302030603192a080106061404120804090203010902181005270904050d030c0c0317060409060e0307020301060b03070f14090d0303090b0703050103050c2e02010207050d020c010801 80
    0x3400301042952024608160403100110800d50000c03c1d403006418401d41e0b0740f17844481402c445003504203034100000c180048000480240960b415031300100d490036401c0c162031400140c1c51060741e01012003240007100000340611998003910001041d03d000150b5a10b40704208201c03001081240c0001c50b80620510381c060080742170348200c0945c482c10401005681c407000418400301150704540e140d1080c0356904000d581405081c03070020003030901144540441d94003405152911400340500458a4002105503a49401c88420a604464100180852040c40548a60001070182c0c0a0360903c2c03400201c460f1000308484c480c59640c3e44010444103104c070102d8074207804011a6401080a00c0012510381e5401091004c1a1103920000352141d1720b4640b843d00e8140c001c1400e0145440c0000410100c3c2020407484000c8030100c0c2c2c1000005c81c4440c0c80c00c280f007020031a110b00510002c2c0e44000c050340560007010716501400441740e899001120482e035070b4601c03a03030b50f0f400101c0c3c0c1001003244c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 349366825 1250 349365575 349365613
    0x5061806130b01030e070b04061706210312390313020105040e01080102090f061303060e07030b0c210903180a080d030b0f0a03050303180f0604050d08070302030603 72
    0x610b805140104080100c140b22503e021816001844658030001d030801820f03401502655110500010400f194074102d0001203c1e0307000d0101000490347c80050306040000d003442122141c00c041250210785050090300c0071500c0c1d140c0340a035011021202007407010120328034400c1d081003030103008503803842c0c1e47e402d504250000d0390003040b81030003414040840c0e400c1c40506043d001e0415040010f80b24080d60003000180141d0309182805014200440ca25103045080c80350240c80d0080c41c045407481041e003041d85840101c3e4000b030b0040b4110414003031803e0920707008084002a084009554500540c101000c400055501c034103154020440b5161491011b03116070a10100140006001a17070f0341451800d100740c1c100a000020350b100340783c140c41d02c4c0585a060050905a4840c15000d08680c0d82d2640e03480083c001c0400f0711002003407101030b02c0301004a440c5200101c41650348506080c07400b203658803889103170034003c500410005070b072051003442070b644a11801001003004005000303502c602 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 349368075 1250 349366825 349366841
    0x3022502151326060903030a15060518060f070309080615010c111f020c010f02011a09060307050d03050304050c01080c030708040c08070b04180515120c04050a0506180613 75
    0x7200301c903810010f98003051041d14407451205000d581e03a450b207070810800321100440765404010710312209000480d44074003500c44030b90452211031907443d01880020100d004564a0b0341258100003040010903038000e01c0346084401940071100c1d6a01ca6495040d2140c05c2440b030140095122180d08020540c0310f41c0c40c640045014200040c00300011140078210744c0240e0354130015900c048400d00103940d00c400340a5000e00948001c10899504071240c60b4543e44000d040c911800c100000704001e690140f106200900009100003600ca1803450050402e2700100d4090b02c142c050a2a120b203203500500c3c0c1580320b0b904500a8518541c0d841c1d4050720791440c0a041901e10015800340441e90030000c1064202034004028032a88407031815001007407101c08600c65403030041c00c04040c0440c600c40e0185d400c0c419001181c410b40003810074004c81d45458540040903034058100004d1201100c0258400303405401c040e1815841d407c0e44901080c036403031041e54525004801c0e103080040c15103580d03103c065 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 349369325 1250 349368075 349368119
    0x10b1504092f0a11061005030d030626011506080106140304050705101206030b0108070b040b0a050c0f010606030603061b0e1c020306011706092803030225021513 71
    0x101c43c20404030014644141225000c0340740006074000e11140c0b608200c032684542c422b2405005481c03d00c41c2001846003034240800c01c0b524041701e100100542074000000d502984185d070040d007642e680c0024079200082c4100c00100d5050399a0710982c2c8407400c1181c0c1308039085002420224644000d10990505002c601d40420488010201046040b405424015030052080e41620b5040ca29040d0034800c2c142e02107401000104000c0000c10203139403c0d1000180c0300c1c200140c5401c900c84c81681080118580d81d030b000c0d40381920100d125a0103900c00f03c1645e02441080220410019107103000e0700744d25000d440854502011641c661815444101d9800c0b20103d01800000659000c645081402c0c5c004100d40740703502e901603076000001c01589520915140003081520758415600a102c03100060300c410410008200c8070a05020f501290641916449080b211180d5880078044404405108070300c9802100905035400d21500c00741c852440746108400c078264a80421080f000495a034440 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 349370575 1250 349369325 349369337
    0xf100806040f0c090203090f010c0905030c06030709080d030903120209011b050309150c060907060c0803040c0b031608062209111008040c0803041d0702010b1504092f0a 74
    0x11a1310b94244c00514040e0018038020b0078800d074440d408034251003162070640c080040101003001203580001d0f0a2031401415600c1c140e40351a15131040741d00306502d412100c0305228070800381075007a40c107521111032540a42d03202526196188104026842030f1503455001407104a680c0d60102168031840b03042d6031140b0101d900e000c1103940880c1d03c41c03000d103c244025510200c2c0340005107409101542e030095910029104072800c150000d81941401da0000d0595900440000c0410030b000112030090400c1003461a181d1902c094005070000342110300703500080c441c1c0c010a01c81e040030500b03200c00f00c0c20120b030452058030300480c010091021400540d48103180920f00192a1116280703068611820740d41c1280700d203458144409103062035402860558010042003241345908044004124030704500503400341c03180d000480c09007868506840c0c0c420701c0c040c090342c018042c000041044900d0024184001d460f40300401d08051044c0786158126815510720307610201211009002c0d6802c2e5040c20 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 349371825 1250 349370575 349370579
    0x120f1803010e070f0e0105090405060c07080706061511010506100c0c05040903080105030d020307020d11031609270507030321050a0605040f0c021b060d11030f100806040f0c 76
    0x16078904070f0554420f04400075015402c1c0540050804014003500c81a91380401c0f40c00c0c2a907a0a6a507603004007034819140e408200e4204001c1e00342c080b60707940c1d130300064244007942d01d46e0711100b44001d903454041c0200c0d2040540003203000040c040d892003004020003105480c071743c012095402001500c8222075016081101203400d035624031511a1960007a580c4a032990304200505282500b880760b54000d40d4014004040160b40d40200c860900e41c1c418500079818001d200031a00d003107040c900301c804080d11410302007805100f561007080516a0100041c01031101114004a0310212040c041c0075504100f400b4000b09004110f031100c02c403158140e0000d40d06146403940e00b10fa030306440b01c010990f191001002180b405004101a004020604022003404c00501950342c00c651018841d004280e1641c0c481561307a4941a6100401d03c0c50301880449006003002200354012100030381c0c0c5d048001c000c100000030400043c2c090701c826100a08940d1243e8403031121946820104441036120f403500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 349373075 1250 349371825 349371851
    0x10603080c0a0203070803070f030c02040f05040f020901050103062d0806010303020a1a0708060f010509100504030b0907060914040b0a08160506091e03010b0402120702120f180301 79
    0x40500301d0701d400c060210803109104250401003d5884081a540140030a80220b009155120042079140c105208600c2903031011038040c3c880212340d0101e0754541401c00080c4603811b800c61001c144211903c0000703a88800054007100c1507802280c00305070580103d4965285401035065107003a1408581d410070355130304c2c5602d0ad0100d0907001100181c20484086003005616264454843c0c040e075900001890030550003000d41c100242054454480307000000400c1c3d0148040f1181a540a00300300c00d0240c110038044d120341d1040c0f100300c62000342c59000419404002c221101070b0b071015640c000c03500785495100c0b03646009010266600544c1c80311004a0703a80d545c4504c0000b400d2040103495031511090011140421991045002c3c5004124510582e9103846403e4503445038441011040301c09540840e004001c00d40203c1d40151001400001c1000281c2c4028451403060707003212007500305882c0c445240c2c020480c01403a04041800607a0a030741454005e81103501c8050000910b8003134000c9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 349374325 1250 349373075 349373077
    0x240f030a052407020d1e0e0604091e1404080d0b03030301030303060315060b0406030f090206041d090d17041a16180b07020d02120d030614010c051e01060308 69
    0x2c058192481c55a2246903281120300c40d565110f01e59001500035020132200103003c40c0105540b6100303400c41d41440b003243d240200d04c44e250040d4041c1000351100e07202c0c04001c004280c40c1001002040a00d804030032401c2d000d0150f081d0304c44100e00e450951351960740e00e0141c1e54025104410b901a01e41c4c0030910a0b441c10000356000707600030350b00407407aa4691b040c03c2200d0461414070b036080d41d04202c0103201d5810044100e0701140e40c1494001181c10080c0203c2c80141404900258881b0002070000b8140e4a422811100004545c2681e151502d40c0c01c02c2c190386101c4d081c0d504022402d1060040b511f40102c9200f168094004c122522013036030706078803c5010b440c00315294141c15824462901030b050b440312a01c2c55461400064507100381c100b0f4001c0500d40a0000b00903c6180700b241c040045490307242583c003886408900302e43c0c00ca6103041c4064081c101e5409107061160182c261140198801c1040c503000c9034104010300804000d003a142082060280e0146165648071600000000d803a64 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 349375575 1250 349374325 349374343
    0x30306150705070b0f0f07030206100503010b10050a090f03140d0801030f080f0409052e06140c0102040b040803120a090807030305061207060201090b09010606050a0302071a0c0d05240f030a05 84
    0xc1d00ad004580b410400c11100b042c0d840e00000e010760701d40b0000740c00c292074004130182d0462039410819141c0034941000c40307103207080742c1251055414000c00042000300c50540c00f803021070900e09075200d0b0b55840204031000c41007440068080e0310320341c0102010401800003007002d020003611652416451710701d40f00c2600c000395201c0c0341c81d0710900c0400c08a14540301c5180c3c0d0508009d42408403280c40c060005000e1035050722a0901d903200024500403080003541140d0044c03600e1440d0b10341b101e542d4003200780c60341c126401c0c031818042224005420300c00e0511825103519480442c0303600308410f94070308038001d10004210603080810002140d003d0234040103444004c015075400840c4501041c42c041c8034122000d4880c1d959a81017480600203140c100c1c017907a4a24100d0718005848906c1070403c081c002222003400c01d5681c180740709010142da580c000520048403030f45005e00051b12480c0881120051105964440c0d8513800360302001c6140481848500c400006c0032214105050384502e414044c0f0b81c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 349376825 1250 349375575 349375577
    0x140907026609073509060f06010302030c1215060301081b10170403140a0306080d0e01020607051308100222030c050f120d02030306150705070b0f0f0703 67
    0x1503440107081104001250321106800d944504140c28010000b402c0b907210f40810a910030b421489010b45941c41078030180703011100e0881c0409501700070800f2500c41c0801c1d9a500c14106402000500c554041d00840c1e001e04031000b48a03281000801921b5a0307088054288c0c1103401082465007100e5807090003440c0a81011800f4108012402180d4903210720b00c0580107016130740702c0104035102c030b401c01c0d940b0301000400c80c00d00006c3d80e9140b0302180d44220200340c10601090204a90b55020350507800001a82ca56004483d041c3d4061901602e10500c02d0031002e00607072190703000036a120700c0b560281c03608040401c10780c000030f034550841c181003040078070b80018415030115040600c20003022480d107140d0740403c402d584290660715841301810650290600800d030800032001c441c2c03110b141448031500c05d402500c91099165500039220f03030040e105144910055140c0170398440031070044a050550180003003002628088450400b904164400750110301c00748440c10001c82c441c0001c0429a1103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 349378075 1250 349376825 349376983
    0x703050d18050c100e06070204150305060405070515071221060e07030506090405060604050c070b070f090602070e0a09050a05060c07020915030604020906031614090702 74
    0x409404d21442d01d24590f002001c03c0007503011521181c0360103045884140e0103031030210b643d10102c103200720004440c1d400140103120340b50801c0203202020034100c0903180110f1b40d2414070039282040041900071904051f201d414116018614140105421011011440101c0e040000841c0c2400221091540b0800d0b81c0c0c2c010b00100501d682c0d1520032540e02400807224001107080640b601a6a0000101814002d60341d90001c1038141c26900180d40c1480d90042d20b075502403410102c0100301301980711001000c42c402138404980355001040e4082900c040c040c103581e407030b40e84052200103001254015a40c0340602d45ca060003140c1e051120503c1a00e2151842c0c0d82e4a07030900c1840035103a0020030030b001420641000594a40d00803c5054200d5011501d0409544400340000e08001d1a11401450b402c5081c5001410582e210305074200044100c9d010030455a510105a0311440c050b1403941e4110400c581c5203066503260100042c04051090760381041c1014240d0401440030160390710305604403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 349379325 1250 349378075 349378093
    0x603021809070c03030944190c11040e1606020307080306040c0e040e010b040e0a020901030236150f01050d020c030d0501090e0d02070b0703050d1805 66
    0x5040c99008001041528880103602d0084401880c8080e100340040405441e07040075001e0001202000d241c4c2150001801e0719180505c1000b8262030001e403030020005011204020100f04010a0f5400040452010743c20030702036100480d142c007229001180c00601115000c40706840d94891205009080b9004066100a141103052291901d6200703004550003000310600040302203050b2500702c0400e49010400300c440000030740d0034208040c031080d0010b151080392507070b47d081500b1a20016a007500c0c100206005d500e10702d0703241c81c181c0c2d401a4012146c03500410060800d08030321552000d140c00c41c50840030310f0f09440c0c0158842051403020702080c05d400d03c1001a900e48050b14058411190740100b0010301d40040c11900030700303900d80c0000380c0c08200081102010f0003140c41c141620b007002c0059613101e20a1100030001036000b541a803150040c1080c20fa4000a0101c05507041d18240c3e50901109a50403140c0750b0002c01c900064545408040f00030440301c1c2c186691040c031880240400708 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 349380575 1250 349379325 349379347
    0x304110117091e0307060c030203011406030f0106080601120e0105010609080f0705010e03010605060f0406080606030108060a02030a0e0d0804020102060919020f0d0503222301030f1104060302 84
    0x1000340540e001e9000455824090114400a024400125152040c40c5030702c080c0307041d09045000307581c0013800d401c1c01d2100c030000d0154594020f60680300c041d80b00039250000c1c0780511441d4082100c070402e4541007400180a818019040340798040414034140211450056040060710015104001269102c1d0300501025070000d210f10068003000c4000c00740c60761030284d580c0da0b89550344544c0341400410034056003da1000c0d040784025040c00b520555650800d02450403507948244504400501746201141c03940c50f045040300c0c100c903e140300134038070b43d20f50b42c442100950000e03150800303103079940d43c00701040c07076051266084c003468580b6240450702e4179000182c10040c004108400d681c200e14900c111a03102d105000c1080c80d0103582d804460642c03000803810f0446100d0f00500244070100f0320b40110903005c0c11a0f110500500341441209544100c40080711240380810102244410100503695201c0e0f40040409120840c011404d1850809542341517401b907044200000e4000a2141c0f241d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 349381825 1250 349380575 349380587
    0xc070b040f21020f010f180305060f01050d050706120204051302031905010528030614070906030606050f070609080d0c0e090114090705040504060611011b0e1302070803041101 77
    0xc0300b07041080030010b20580c001822030b583e208009041c00050058814264450140103822840c5c0b40d111020542d02c03820120381e84c4108540703911200407040008510340c10300005100501c0d41c800c8c000c0004905107942922603c0c41807540c0f80b10f459007400006002e40d20303410150851031070940c0069076400c0040c20716002c1e029000000b492a810f10004009688588000d848940304a084514640c03414040e80c00d0050500d500150003642400075802400d0742c41000c01e0b0094801d91078901e06150b40f19410340a840042c80380d080424402c0c00f90340f20a1450100401c0e80f1446200009680c20f21640c03441550b0300640c20903d94241ea50116200e2107030009590340c1c1001c0c084481d50b140398940b622401d88080703403203501e500030300305040031900d024003074000e031000380c80e000300107119080d02c81034000c040c0065105403038510340c00c0c01203c0d4200348540d440c8402048003aa106140301d0440380a2000784c0c000c020000b10195820070800020540b00400385000d9846005601e80708613240c4001447c0b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 349383075 1250 349381825 349381859
    0x3060e1509070909050c030312093a0c1b091103010f03060b012c040c23090f1804020f0102060f06130b0607060c080705090303040b0c070b040f 63
    0x1141008180501c070318000030100c0494410f07800108892031980b41050034a40c400301d500740c051002050700c0c00140704604889201e100b0300d50803a4004110001101c004568502171140703c5d03290000c585074544901465156401c06605100b600c4024039601c2840500710001c180524070b480040a1003c0e803420700411080450044241e41554182303843c4100210491100030440c69507421581010f9008110b0440b020203182292000d800d06450b800c4012880411300a1180d842d003181f1080950081d48454540b4540150441851482c0b180d41001540030001c050782c0302025460020301d0743e4600b255120009080c41404980307003410b2040c80308001c41d203102a41550080000c201742c41088000241d0300035002c442c1010743d8409405682e00410807a15940c0d003112000402d401400322540246242e008166509511036403960005c07695402081ea0705503054008000402c00c0e24000400380065900741402d0702c40441d51100340e4010b07503006500a11858000e88003c20003550380e0700d01c681c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 349384325 1250 349383075 349383103
    0x41d0114060405180a09050609010204090c1e36031205090105070f0c17160509060604030b04050106090219020111031003060c03062114030c060c030705090a03060e 72
    0x402c0a09100c00201100c1c450109a03154450100000f4056402a0000143c04c2c0c0c000060700c01e0343c285842454042d5003e0b001c0c0403041400c040111065a00c949650806c1c05031a441b1041c290441000071640d501a01105514102c2d24040055011a900324031a500554480c01410843c1c030f145002c55409c0902c2041c4400e05c03a00340044d281030398200c0e0441d0034091340207113070380340d90550f600c0c04514408c1c1c0c40d0056000b810b04e80490361840c510019125070300341c03600c1d0386000056a4039804c20150010480703820340c0002d020301080000840390b40c5905c1d0401e214000101e8008d0701c6079444001ca8221442942000d615001003844054080c400c48151030b40402005203140f030401c48481c1d0b04841c511000300f9007541c4511551106100380c1c86203000d0606a00081c15581a080b1704088031580d004003690504405540d2020021001040310582150714024160f0761359044e440000c60341004100400744001084281000e64990000e01c01452280e0000149024030586903460032190fa02c24403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 349385575 1250 349384325 349384327
    0xb09060607080f0307090b070614060909030f090a030b07092907020d05030904050a0204051219030f090f0b030a0606030e0a060c200a0201021903050a080705041d011406 74
    0x3101091009080780c084907a4000c40c90313078a440d402c0c000c880e0350728103501000c0760b8500424001e04105060b088140e21035800c029040316034a0300c03001c01c1b540d03d00a4860808a0740200003626030b101d10035014021401008054401c1c00d40c1e680c592020b010001c40d002c0c800540c0700d52040c000c140000008109a00c240c65a01d440b507041907a08045a20a03d000a071103a120542c1d00300411004001300d0700f03c1240503005000c0ba00740f940c0080041d4204ac00707894400d18001e0840300c6181c4000460b4000c080c14480780038044150381d00d00341d51a62200c02c03480c0c00c000b0382030004500c601c018200c51004055421031103039a407a000c1982c204176a6950041d008140c20690200304000380040c07d40545d94000400040c2d1101c190801e44030700485000f01e5003188940d64441452880218803802035074001e80030b030758000785001d2260508480360003000700812000e1102c1100a4450b0f83d5075a8820460b080c92440d00b40c8440700b210140c82c842c03e5900855448500520035610119254029000240da0710707 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 349386825 1250 349385575 349385587
    0x8010c08070e0105030402041116020a120213050a061703070b06010e0117071809020715020405090109020d1e020702010207050604122004150602010507140a030506040f020d0b090606 80
    0x341002c1e0341d0012181084400f1010805554513a400813400c0903407030040710b60b65060b000c7c0700e00c40715440b1a0160b1259034100d50009202d41207041d01041070703a00500c2c82d40d401c440380e60510000d03c000780020304080d41d01d44000c40e580d8401900350495003640c000860700c46006203044410803000030130160400450440040b0f103039801c5002c1615074403800307900c01d8496071611421502070060240001a2a58044000031002810340c02085054012491000030484000c42002648210f11800390020644001081408038a0380541504100c518000c514070300010300c00c02c00035440e0341c542820136038000b84034030031581c042081e0001046d0a4030a02d00b41449c0c600300b41610380d6541d20180215003d04880c5000d421640a0aa49200000c000300140060000004121486401110b02540c60400400c5100d4011401600071103101c6280030310b081c03484070003100503020180c0b1841d0829249d0206900100700c500191401020f0004002824003449003040004031001d411103005203820096 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 349388075 1250 349386825 349386827
    0x30212030d0e011a010804060b0301230c09060a14040b041d0601080402010818010617061008060103021e061215040b0f031c050d06090c0e03010b01121d03031008010c0807 75
    0x250113201e2109003070294003903440d802c0040191610380d007040d40c1546003a006100c49070401301d0800d410695120291200c0e6210a080b0400b0300c542031070903170b1088050094080c00e1b071044115030b21191514218a0425a0b03900b000c501396000380d0441100c00c040c905203169110700c08400c07140c0c481424600140c0609103900060a108406448040d07040e4280c803200101300c0007504480f0003410003c000d8401c0b900e071000b0007a1200381c00c0d60145001c0c4d10746407000600e40c40001b5014141c82c1c00a01c22020300401d208003110388604c3d80c43c903942016040c4800e411030103406800314440d403690010302040f55200d6040104a41440c10380c50f100340e4000104c1c04103a10000742d4502490b40802a400400034950390a40302c9005030015900c0c06030030201c011901c040c003070f00481c0004856459480700510418101403c0c0d450707000f149030004952261070313808124150803503048003103070030915801c07050b14416090035540125001000110302600c01c11283c0000d100f50710600740c092408079294185444 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 349389325 1250 349388075 349388111
    0x12090f03030509030405131401151202130e0703090203060603070308030103110307030b070905090711100f0b04020417100b030a0f020324070207051e041104030212030d0e01 76
    0x10382003640d5807000a08a80d0104219005400014945840ea61401100c040944032014400a80d01640f200019803402c030a52150407002e090380719102c03030700c0c0e102041764000d411860000d241002228400526640351070b04443c0914503941e408912007081b8010b041c0383c0382c005481c8500a502901080000c6100001a24152717544862021020514000044d01e802e10580026080141c1181071002c1d080e08941c6041c11200e06a4811002ea42c2c2c4140c01e4070362400c9081c0303540b015004080c034090f2590150b440b01c03803116035054001510881c9007020600320380003604200000f0328490454645035400300095404801c0800081c00400220808a41c440c0394a4000500190000043c01e0442d0340c1030040401c0304e8074400e601980b00025031002e030b107152819900280540504100841e150400d018114074143c58401c01c18644850300040c00000e204d108000d142141d42440f000c40183e942507400190001304900071501d4000c19403804c011100d0b000c0c41100307613a252007140492014511 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 349390575 1250 349389325 349389353
    0x807080d030e01060f1806060c1106070f0506070f030608061611030f070b040209060f0307050d050a0f06020421110108040807120201230108060103231005071209 71
    0x31502281c0442c0302c00c5001d015000f00d800404268412510103e003c030b0208040b4680351100b06406d000c0329503240750580749401c030518050120707580d00720300c00c40074100300d402082d4070317407040e1889140702d1466107445042c0381058074507000107407245a091900680c140501e03009001a4005000da074180083c01c9021034002202907024041000c000301035503602401075450851101c5c0c410790340ca003d9403170001c902c28400c5400300d20641c04c44000c22294103003c0704e850811a0050700920786241130501f00030039021910011a01c510078403000c007001038884148491001e124070005a1284e040c00d00340c501c001c41040100305482d21416101c4081010902003607404642030030400e65548450070b0040c618890240042d003100b03807800e64004503580c15401106408158007200707407004040107800e0341c003da081c4680b002e070740c2c8188014000704500f400d481c01b0310850b205209903589203040c1400c0c20480701600494100c2d0b43c400800080310b40020303490323520740b54000b0f0030000c052403a0348210145035070b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 349391825 1250 349390575 349390577
    0x2d0501050a0905071b1b0b0a14030c0705030f030f07020a03080f1021150608030f091f090609090c02100c1b060b040f05040203120a03020706091109010807080d 70
    0x810100c4c07443c44c0208003500e16a840f811a1210300c018600300001880c100d1200039803940d815407000201900f100c815100c0c403002035034600303d034220700e00e131080516003000d00aa44141360070404040041c10400040034403201014040f5220700d007544042000020080200d002e540084034000c00103541700c3c1403142c0c44001409845210303180c1ea1441010248103401504c02507505041c14042c010703d0700610509039200d040340321404401d00220b8000d42e1401e05c03401004e0760051105e61a600c41b000045c0c01003003406400b880c0f000e0794090205141900754003014020940d004c0051200e00c2e4420640d0b80640382d0140b081c0400400030200a680d607110f5980e94001c282e9138040e0400c203034445e1400c16070045460445a00e81c40407414040000c2070343c0e51200d4495498006902c040780f5241c007a01d440f03143c00801030070401c20308407034540d2141c1c0314038441020564200240d000056403813180c6031049020305e111000901105060025060040e001820310b035224241c200f0a1481c0025079070081281 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 349393075 1250 349391825 349391831
    0x51b12070c0212030c0f0304080a020d0f06140103060c0302181002070e0a0605190b0301050108100b0301090f0507092d0815061003050c07030c02030a0203012d0501050a09 75
    0x40c0120071540c4400d103100080d884642c4540d1180d410f0310000240c5145032020054506d21030520024940c1c0303110301e21418500750800e40f0803c0140c80c18074040090309026095410b004102542c81c0000c46008003415081d4020110050041c0f15140c400c001c02e0b0051400c1c1140b0308100d501d520040f600d40c91688030b2150346810000842c0d503100b8080040186400d00c065400c90412441c400041c1c495401894001e404c2c06040d141408420f056541c12038900d80340a52540e42020b00441e2004001450b1446000303900c140020b84e08040310080d8001c1c050920700244001003141d0301d20507148003502000c2040311541c0d050007500d020010b41e0660000101d2442d0248403841e548a1010306154820319030f6015521140941c655030200f4103124007421140e00c0010f16400c0c106404590054a0030740050300184074042c0042e000c0c440c0c801103240010b040326641c043d90340c0020b00351240240c0c0d290b078040b404041002d40100324003000e0281c1403108400c3c010340d81090b0100e0070700000b5100d4103c507a61 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 349394325 1250 349393075 349393081
    0x9010504050a0207021203091206010b0f090d0503040e011809021815031603110306090304230301050a0f0b030d0c060f020c0d0809060f0c19020c060a0c06051b12 71
    0x1e0354104c42d0340503400303072500399034007603442d403c58880d0080c2d200c4601500103403507840c0b000d500200303041d8140e902440e5440c5c10600c040906d107040b9001022101d401c1003c0d1041c50021940c200050f0006210308140c1d400e4545c148a581c13601440d0410000030841c2c2070010400040e510315a9550540c4c0e00a524115a0b603500010000c0800c00d42e110190940180a004500900c1d017000c504140d0f4095100d0048400040090542e200c604480366440ca030400c0c0014040840304141070018400503030780d549003520b4040000780c00c40341c094a11310113080e0346e042007141c06152030090129900e412006411060b10f503c0b0f01401c80c0c05107000040c42c580d5580101c030b00b403180b581e0540c1c0c00c4100070022a1207001c440c40014113482c1c0c09590a140a00c602800a00f4104e90ba40f021407040081002c0340c3e0610760911250060304542c20211029401400c0b40c9440c1600d510001d03100e14001c1c3c1c0c0e111000d0120781e041c17030303c2115000b40c05003000404800346a061058034804480441004406444040d9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 349395575 1250 349394325 349394341
    0x216020f010e0a140f0d030c06051005130b01020d050f0d11120c03011406070f080a020124050103110306030601060c14100c0f020607020d11030c011803020d0e0901050405 75
    0x1110000b8071903103c0da0080700459031624816228620040607107401c50070300a040104003c07500d0a04004000030064600100083c4903a082280c0000743c0f68400031119803282d0001e401c5449070a0443c044558440d6081e10b60347c0d04002c01d03054500030b410214502a616030400340c0c0c0d88a100c40b41c0102e00d85808078075541050910403103101e00c2e010340704a1401d0034906a00803c907030007803144840342c2d410f00f0403404e00c901c0c20104640c102036020718004151081541d8000a40d00052040001d6550700e10303d4031001c42c0c0c400c07200d0729036520300380242a40c0346c107000015085804040256030085400d204120a035140048c0e00d0b815a03c0c14103000c030300031500b031405030030711011221107513a030780506021102140f05a8214207400111615040781000f0220001c90390360200311030a40c0180e01c20030201d08402e000d1410000c0b00003848081d20310b4003842000d480e003910084442015428a0750003c0002c1c5036040c0520080f0b40309502c3c2183c0c3d046032810020340b034000107010301c44c492960340011450345 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 349396825 1250 349395575 349395587
    0x1e010b18060a08042604170f070806011508011409090307080703020d110c0a030201050d230612070b5809020306040b040302190c090f0216020f01 64
    0xe1200508240e5901d41c01480148032800c02e40d000c940710358111844103036400c0c1e007441502d507400300203656074282458450583d214582c2c40c0c280100714010b51038500c04100c414054000646403040081c021549007408d0481d013000c402d004003040103880c000500c030364040e03164044064a03003104c1c00c107526191600d001c2e00b10300c0750380b0307000f018550002103200405801003840800704120303403155004a4500440d2681301c18204815507840700b6254018001503015001901496446190011305a410f11015202a14a02c000e160706862000104000c9280c0f0400b0504903182d96405010664900800f13400c05016410f02101c810b60000421054504c80c441c060038103607454013850010380c3e85944012800c00d042500c07003003038002e0045110004001030090a00d059130180003480039031349a031070340103801c1c0d000f4200310210301a10034107041e040103c1c05a0f8801c10300481100540340e243c404c10b00121031200307000c801d0250060201003241400701e0210005c141d0195186400c08007032400498007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 349398075 1250 349396825 349396867
    0x9050409020307080a20010e06072307060e190e0103120314010e06040f1b030f0204081c0206010f030f06020c210414090103020904021005090d080306091e010b 70
    0x3a403245e803c0307140600041e542403030315410030080b41e00b40b0880d021004403071103c803138100aa0820400c0105900242c0d4080c0f20040203202c0f8041e41030030285042c94030b820802c03190300c141d000502c40840c220161401d52000041c2c10043c556810a40e850010000d100303180510002d8500300102c03030b8441c8624020307040001c50b0340302c802d0801c00540c0c56142c001415581a1000c5010310300d010401c02c0010f5061080c4020384114a4110110030b100c0007048000e00542103035800301c9502408002000d8074104045481c030700000c1301440519580441c000c0c58080141d0103c05540da08440400104208115807450070b50010009030340d4546062000345480340f410908800c03001030b0000400c003114010702400c1954203103100500588840c0d410001070020038080654040c900c84003103001460603448280c1030390820f050142c20700f0411400208855110131003990302070381c000304010300b501d00316145c19800f070303040500c0d46407110604080d102c6144050142c2c01e40b0180004840e000d01c1c400714031400c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 349399325 1250 349398075 349398089
    0x32160b070c0b0a030e03040e01150c0309170a140102091305010302060304230d090611030f2203050304060810060f080c091206040c2112050f0409050a0c020f010c09050409020307 78
    0x91f58681d91401c00513415402d12403141c45040d020b10315000d00c3e0ac1045111607003900355031060251800d1031818400c8944091200540b442103910702c50008400c5000c4d82030700c1c00c204c0300068443d16030030140b140003880c104001040d98907000040c00169501029030b0780064202c514401072011040c0b651601c0075061507148110300c18981c0312142d160340f200040c1e0556226698090100803918401e550341c0c02502d0001030400310074466400088058030070325214484007201072030050360741d45495041d40d1007500a000002e000c4810001516040304100c00200f8452402c50a001420a401045a80081c05100d084400019041510b40d102d0301094620300500040c1c860030304042ca803403186041d11744201d400c22600790622605111588078500e01060304000d0090443d00d500008486561220141c940741072002d10020483d00c007140308041c480d182e05540054a4040f580010385040ba03034554000d566070600403c0304142d03074400f0342482200c40030b98010031800300c1071001a08005d81604129 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 349400575 1250 349399325 349399327
    0x10e0402030907090f180807030c14010603120c0b0a110910030207231509190302010903080c0a051e07080f0a0e0a060c32160b070c0b0a030e03 63
    0x45144031010861404480304d200c030800010906031401c2c019502c0c2400e2450910384031500b5080072035284001415500e22918028020440a60300c40d03c0c4480d0b00c2c018004186c1d0b455102b84100540c3d40f030309080042c2241001c0000c89101e03943c034400500002c0c22015220f171200d1080d108010b02500b640ca40c0907005081e04030071103075170303000400a41080d030094500420b00101508142d5200c0e181c15400401817001c0c105031f072035940340303c007524002903c0206140314a1501c043c103802852196086030703120b0350000c01c11920340c0c1401008c02c580506003500c02c180400c032101005400508680a03600c2c000f046030309440011220804500a0103405001240006144099481c40100900c0d03501071940322102d455143d00244440d490103030003002e010501240d07082000c1040340312085001040b49045060091003c01c1c40074036041005111080c07540000268084844103128150241c070512550a040c942c40b601c403606900400d1180a0b01a403001900021a0f8425080107010400d054104c2e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 349401825 1250 349400575 349400581
    0x5010615020102070c0b0711090408070f0803041401060b09040e0a020a0303030605030610120803060d0507060306090c030b060d02030408160b0609071b0b06010207050405010e01080c01050a02070e06010e040203 92
    0xe8041d5100c880102c80c1a08011001b1512041c56819100c1081d0401404e40c800c42c0d0803000c0c4a0003600140c016200c400c018080800000c1030081c1c01d401a903ca40c0110b47c5034245494039825031210b40c65901200d0f410114103020420140081c0d420b45442211b000c02c0b1782c2092805181040312682c8042c2d08041c01d132002100303142c1c01da0040030440380190102c4009a9500c1d1800c42500b24a001e1040c00346a0908030380c01080022000e190400001043da8040e4101581d95610308100c99202c40046516000200200c5849100700348500001e0b040602c0010040000610580326100d4035528030343e808004074082c07102400c03d407003800540303220740f40c0c0381d04590601c101d4058084030044d224141d0640080e030f40ca849204060303500701c040e81142d0440303003075070b9204030300000000d110604501c50309600252654403401424000c04031202040d0055040c021424200305000c0e032050705102042113180c00007039000445204840b04417141c0c07641d580b541c400491700500c00c0340580f58024004018 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 349403075 1250 349401825 349401827
    0x30e12011422030801030201030f0b030f0c010809010e03070b07090b030103150501143109111908030307030509010221100e1b0304021309050a1203022505010615 71
    0x100d0302039071034500c66111280c2c220520044842c1d480380010002280c1100401c015402034004070004403d4000200b43c0c0d0b1001d8003c24a0a003545201007819444018a00d6655070003000c015007001010300203010208081003015900d00c02d0300301c004c00b680030640000d4102849000803002170551040500d950f035a484c1062030300c445245021116032840d0000014008085011211107040c001c0c0c442000002c1c1c245441a104524549006201c042e40881c1c1c1e84d8503980b4803903802c10740e00c22110705092500301810b104040110348081050781c1030400041c00134100000035030342c0c1304081e4940030a0941c0d810550f140640102d04214290004d01d200c10142030ba401c004c6141b0a5020700c03824289140d03109020380c1483c3c0140c50140d070907040e83c40708100c1500340c03100842c0d2107400500740904840310449010308a4a1208007500c482d00304107540410440000000042c0207203a28044d4100b0114920b03400d15003c00351a50308900707600c0c0701c600040003402c1d04131744018a132030070b500c0d603c000d480d000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 349404325 1250 349403075 349403111
    0x5030405100e060a050718050d11030706110708010c0e1309050a06020403030206070c031b020d0c08060108060f0403080a0b030c0a08030405030d02011802041d030d1b020d0c030e1201 80
    0x204d04e085141414005264503204008401380c5003d007042c5031684a1806052041602c1c1e1082e083e5280303003d0030131401c12a141040300e80c2c0108010b81e42c1030a00402282c50b1070418002d5008402c0c1c03030341400c00100c2c445500c0307030140000e4501111080d544030300c20001d2000070403005800414500a0442721414400f00b0340c054001c6034002d4082e141d0303a039280d80b000c98100c0a0300400402044200407100280c03c9141d080040d45440a040050301880d691034003e400009030303101c01480e0380680010310642c1c105110440d00003560203100a201d0505a42c09014903100601e011701c0c50307a690f4403020301640e00f08002d581c4500c1c01703030001c521642ca03480c4d80c0b42c41e03a10030702896010744140c215100c801c81c8140f04004105011204000c441c8040da8200006400d042c0b01030200ca070103035820900060024801005803c409540004030602c4c000c0705040000641020078040d074002144161601380c1000c40800c03126490311f030603107000f03207a8000240d038000d450b0002045503103044001001d610303241c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 349405575 1250 349404325 349404331
    0x6040b030f150703060e060916090b03130627021e06160b151806010c02060a0f03140c071202010e03070501060302030c10090e060117041a1503070605030405100e06 72
    0x3d07a00b4014103490301002100c90a0564031140c0250002002a80e2220341d40030315011022136140200302b490307669600d50f15540043c0d0f1120750100031b0300441390804c40e00d88510301b518a80d03860344403490098054152007029207420041d000340a107d412039401400c4400c0781400e041c000389134503242c05400f21701801c20003804a040750400094004510030240041004c0d45452004003407021422070649080001c0340301510407414450f07442409001070313913a2400703440d01c0b0600f0f031b03a50358078042507020003002c1d901e042d003844040110030720070700410b94280022130305225001282035030301946e6080100d006110555141443e404041402d03010018190480c200f1203000302d0441d802ea488010030029815880d040d83e002094000d20100309890b01502900d80c0700310141040358462a5046c400d00500c40112011614848807000c101010440031034115003026113655400740080c03804020964032202c034011802884404030000b010130600f00200c0440010040c000d1026510301d40f180b41e0390b901c046d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 349406825 1250 349405575 349405577
    0xb150f09090a0b0d060906060305060117071202101d09011d09030a09050118050a030308060310060f050409060603080a03020405030d0302090109060c050a05160602010608060f06040b030f1507 84
    0x850104900e0305a034010f400c00f0000c014850b84841405944400081c607040c40b00f15035a5403940c00000204030203100090081106007a2061002c0644604509280da242c1200c1071003000b8110800243c0c80d6071071a0072107030384079003080781074081c024181700b031000d46101c202a40400c80030004200301e01c908944640c0d041c031190b040700c801d44600003030544a009119000d00040e0b844c14082240303620420141c031901b0300702e0307812019030342d110401300d0039044043c1c02c1a0080740c44042400f4041c01e04100a015030030914008218040c00c04c882c690380758106105041c4101d4948480c88244a15944010021136101240359516902d11030040c0180d0018031420b0710030701031034400c0c9003002d01a008591400c90143c5d01c0d030000341e013444003c1c0c50021100c8030a6a0340d10800704500c000440030000030550180402c1c410780d80500d400030080c05e40e02103801c00105608040c09100d00c9103940601680c11120858020803218214004241b41841e070780d5032449e1611440c9031030441403990307240c2c0500494017 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 349408075 1250 349406825 349406839
    0x30303021803190204021b030706290d0303020a0216030f0209100e04021509060c1606050a090e070e03070e070e0d02010215040510060b030609090c130b150f09 70
    0xc260304240e1035411422002610803c00c502d241c0040ca0141d00400131a1940002040500c000e401020310390340043c042155000c0c0c7c1c50400707180c3c20b16441c002111035020400c07248401114400407840b8040041c078000d00781600440c105a0903402480100321034040ca0000c407110b6079503414503508044810381c042e4003841030000070036001d2425188400584d5400741c141d018548455083c440602c14030850318455441c18881294030f50b40360401007644800460082806510300100e940c9200f0391030380304200b4000c042101040b0b00ea085080101101c8900c166810700e503807418002c5d1010a10a4200c5502d40602100413669054899a00e07010710016070703605058480410501400c00c031000300207805a0f00888111400d4400c001007264000d12071401e8a0150a03c5004902600c80c035405c1802110008800c00096040011400c5d81c852911401843e00341044c81c0880c00340b02d00c580203c906183c85103820010342c0c8420342580d515807000042190781c0c0c03501c1d64610603160800176900d845800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 349409325 1250 349408075 349408117
    0x3050a121d15180d08070c0209091c020c030d03180b010f1701060b0301120c080d02070504050a021e03090f031603020d0216090b120601030f1a2802120103030302 71
    0x1241c802100f00c034080f100000e11561603618410f40d10b45c031000b0442e00401c0750703004841005803075860846015084a200402100c054018001d0b02a2145010f10003103500c00c00c603c10f142e40d0005400c50300c00c4800d00300001d00c4540d0714941990034000e0b50015210006a000005002e0b103201a1101101e03c0b0760164040ca07400030140d5800d89507184600e109011040c030060164400308a03441c0c01251094000b5104940d56080c05410142010300c6940503030004401088541407038040c007944101d111340d00311b182044002d2412000700780f03600609002d10002c000102800420000120380301c1c0c501007120b45900401185480e21444031901701c00500030085e03201150750002030004d003403503000443d8a0080e802c0000510041c100502095030141000c481c03600100d406010640c007071409480c0c40b648001e590b051460161082c0b12180b11031401c02420441c81005141207004003c04818400d00c21040d08200c442c0a802101000c6029030b81d502c0002081540543c0200a02e00700b0b403a8000c0b10321 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 349410575 1250 349409325 349409341
    0x50109120203060a0507020f0114090d0903080f09030a052a040507080601030515090109050714040e011e03120e040e030406050403020d2a05040b090403050a121d15 72
    0x2030403010029056070080700401c13503000442e04265032000c4c1610450700c44d050401078850944003000380398001050640103114003d003040c40b0030340e80c40040d401c000d01111715550300d1100c58801c50840401081020030038070810b55061014490301a000f4085078800402e0404000c01c0c0f940102101c941680001c000d04440e042a0042074451411501c5070b07000c66682c8801034003d0b02000303107615802401801c05864a6407244021800f030080c1d030000045903e400300d8003901012800740700381d11554050000308120b82d8043d9425042d20003180b1481407008104e541c640e5200080d03040203114107490004c400150b40d1003440c841e40c0e2403080700d06000784822a50440d459100303a02a07100029010002800036042c0710006180103071050380c1034071140080800030017510690801c0d2413608200000c08000310710741030141c0c0094850441d49206241403560300a81944158403012050003203c401c0040039110580c04a800010b5000c10b501030f03400d0001c09140c64903c1946185800c030507500101d0800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 349411825 1250 349410575 349410599
    0x10501020d1d040e0715050c060c040f1a190215070905010e010531061e080a05040f02060415080901090804170708010903030615021b150403020415050109 68
    0x5480d460410401c602d40c040244005840403074011060782c410058002100042000c1d81c502070540d80d03550325111500c4103040e604102c3c0251412598007010b010030700a03901c1640c810b10449181c801d500c01c0388440b184112807030380900881c00200001441429800940103d00c0d10287c00c201c1c0c0ea9860940d440d44016a21a007160095500040320040304816550103100185050303454201204031601c0031150380c207102c060200003061060001a400c10260740c01180c0d03041101500d0480b901440f8002100038014100240145003158588022405100b170400c40c802026402400711580c40e600c55020300300d01401c20602400081401c000605044418440c2122442d400003010707182602d0106110842e071000e030b82022030390003241d10020340c551382407007110b4110b0321945000c00c0b118601440200c0034a1b08641e503c0c01d64005200841c180710482c80301d440f8500c4125985062590100043e80c998041ca820007500140b0740300c00c001c0c1c091943d11540b4103c0300260396041e041901c8240880c46 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 349413075 1250 349411825 349411847
    0xe0c31090906200d0c0201021603020c03060f0903191106010305010213090504080901112407080903180118030503030f0907050d170717070606090b0f0105041401090506070506010501020d 82
    0x1c3c844107201c1c3c850b0b02002d03074001e881c1441c1d8501c0054181074203464800c5006002030ba044016a101c4442410507050a00055030f000802c2c104100d21440c0c0650076503141d104400107182ea1142000701c03400300c14090900058200300000803184031390b03180d1400034001c1d44810050300c00000223400000c0c4000c0c0600405100304d42c003415503428a82510015200b2003284c54601046006030131f4450541038051000d904504070710352007030f403c1c3c0c00d0080e4060484c40c0003030440346c45904100301009200e45102c04082d4884130a191003240e04c841140b030601e5510362900000d14600000040c41989040300344401e0080104009640c4015907481c108400e1104050700100304007030030366020100c807008401802c54607010720f900c0c1110b00c0b04d986950307042c1c1d8802d94040b5101070307454030280300002e441d100d95040d0740da083e2901400000d82000103021400b40344642e03900103540314844000fa9110f141c60600401001d80116180c0c4034619203582c50310424000d82d80148110090001841c0c810240003034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 349414325 1250 349413075 349413131
    0x507050c150423011e050f180d080a0e0a030b160306090e0610050102070305060109020705010906020a170a0606090e0c090409051c020c060f07030c051002070209010e0c31090906 78
    0x12401c80a140460748942103004107001404114008c20025111310349400040740c8120080d0b603690320031100c0034013401262043c0354042c50001c01e080c80041d6841d0710356030b004404010100380a000d0110704401400781a01f00d0392a007030030082c20441caa10300107036881c059280c1e0300030301707240c20344460049903550b07405d02c030240503540030344010000c0f4400c40d801012498001c80c00070851a050f0740341c89041c0e0340000403241c00284412006a100c540c2035401a1300f16200034804e100881c54898014590364640c00341700038040c0d41801241100e003d4404844188802a1051000045904003940c65018108109000c1020001d500a2241c404a0507401981008040c0c03828903036401c0e10104d039508086400c0f414052081030403c0417900402686108003d4a40e01580e203584510500c04003c1069100095020140b030038010b41200c80c00075150040c0040b940c41d8a01c2c0c00c00110034444a8024000012108180308003003000c100030741041c03000c175008940a200010000064002144035448414 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 349415575 1250 349414325 349414327
    0xc1d060f030c0c03090d12030513020a060509012f0601060201020307020703031d04050c030105040e0309090a09052506090b090a05090a0603080c010204030309060507050c150423011e05 81
    0x7070000b050080a030039215840d40840341000d02c16004a5801c0064181c283c0d0140c502d00d8441000a03070501605a0100c2c09161201220403294007285207140240900b00900c030010a10143c5a440782103030284521801580060b1846841e40031010143d41080207001401000d0001c60024014021240203040c9540100074681c55620119032261080b12240f0340c82c0e170040c030310743c0c015078031401640d006800220321940e40b540341004001c2168031090350069542c005204060a0303aa504450751b40c01104107901160400d500d14005003065406401b90041e184481d0449101481503000d58060350b426032603190000c4d40703070610f901007409014072142e40320307200140c188442e00b040110300c2e40020154070081052500d07965110240e8000c888080c00390387d80480c04006041d4407442c08401440725050003441c00f211500c8650b01c1d007510b20038282c010070170301c41c80c0c07141d41c0c030b00e1400c441c0201015112202c656442c5158041c0c2148548001800204650b408403200e06030b00d150b52140500a0300e901e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 349416825 1250 349415575 349415581
    0x61026090607530a24051207050a12150603050316050304090e030d060608060d080703141605010608060705071e08120f0a050c030a1d010c1d060f03 65
    0x1029810301d8028040f039415100306084039600740c8100d2450030940c41e0303410540240c580100d108080741d8010011740c10544007a00144e09081025140d1410340d0800c0d6003900c03281c10741d50320300ba2030311500b5400140c202800150005071000481c00c80c41803288220921280c0c3d086d01090101620080d000290440d0410003c560b9444800700801e05054403c0e000c1d00e080580e1802e90b601202d0a000c094042034000083c2d000c000b005038071034480a444581003501c00e030700b8400041022500c200800030a204800618401030500a024110017040d0944810b96204c48050410480780d80104085070035601344007000c40c04000c0442c0c09403051641d90f941c1410040551036240114441c015145103044010702a400070803a19001803144110214002d8500e0811000f14000303110018a00d4407600d1404007444402071a15040703d420290512004c07d0b100c620031012141d8000681410701c1942c81c021014083c9900800c603c00300f610203400c2056200c005805102140c4145003108000050030400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 349418075 1250 349416825 349416887
    0x2a0a08030a060b2502011701060f110d09180207080304080702101d131409060106120b0a05060d02130801060906051c0201080c0f0a020303180109030206061026090607 73
    0x51144005d0051600702c0311000c1440400103a000280c100354000341c21503015948560308000c3c400965200f50005040c40504950003c0c00800c90340100859081c20081e8200ea44541c2c1e019101165048200f213662401c0c14a800c09140d0711401040380191442e22500540d0750090321145060707041070200c2c00d80c01c4c000c0d0041040c808029490512007958400009106222140900388146000001807420f9410010054000c01240071071038100360400142e10b940e5250904404129203003998074944031f40080d10300c00064000c030595060042d406010010b250303a015081001103425850b010043c1c0c6498a06100080042c1c403240305003e08500604001944148000e9610030301e109103403030420728141400c940c41d9002c2498000143e1021040c4a4410004101040c2251040000b04403543e141e40c2c1c00383d11844014400c030310035014810b41e440114041c804081c8440140c400002841cac0308918a1950140107845031403440c4103000000701c0490040344241c2e0561451a0201c0c1d00c00d80c00c0070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 349419325 1250 349418075 349418137
    0x31204020603180a1203050105100c060903140a0c150b010518011e0306080d0e011d1f031517370605040209090d052a0a08030a060b 58
    0xc07503a2411940008041c651403001d200b43c241840c031610f940c105d0b00710709210050a0713640c1a0080380c0305030401820745e00d5040e0001041c810b03090384010046a000341d141415504c4070301c49202024032903000070f10418455405083d00003101c4c40f40001031209030821b0324510031550107032203403404150100044000c0400f8221140030b24a0140f60002c1c1d004c4440e0b0000c03408607004040c00000ca40c56440901031402d080c000b610b0380080b28036240341c540c0310f1140000e0030004011f8400c0141088060b40420700d0715100074548202020001d000845a6a1b0f00c0c0100108840e140a00a03007440c500d020610001d40300140078456950030080501c450a80c981c0070081a20401d60510b02042c40c40c40703041e00c404c04900c6c030320f028007a000010f034614160040c0543c1d514010241c00311030304201283c2d50140c1d01b0400340c50f06040c01074200203a80c2035800740d01c03510400d0b5000c10511440340500200030080d140c401140306501c0400103011596482e1540710380b40c00ba030070b031b18038845181b0403210302d480b00001c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 349420575 1250 349419325 349419331
    0xf01020310051309020307030b090c0102030909040206031e0c0706180503041a1204080406121b0c11090a0510060906080105010e010c0c181d0604020d080403081801030b03031204020603 81
    0x800016008a26070000c7d1800301c0650003110141344002c00c00c12083c00520580b0700c010350a0029602d071625402c000344003084000c100030310521002c40460340003034203c4400e450010780c036a0403040900f02000d00080d541c2140c001125010708046100c040041c01344030051140c1d80c0000250f00781424541e01029144004125000c1c000d824021032010417444400513008070300480340d0646c0c071800c1c070303030003d04c10469003d0385103440381003071002a4054903080c0c101080c00780602d070174003180f5560b00e0000e100169140ea01a4030504c0c0505110405180e03620042c041c0000820f280001d90f65644182c07401125031103004082102c509c010400c55014596400000700149005454607000303540b150303414806031b00500f00368007440c2c0720050f0401440c031450360341101940c1c6420501d0207440803d0b9440400601c000e0140f02043c0340c0404124040055401441d40140816151281d10f520800da5481d00200d1a00107418451000058100801100c3e0510280080e03910207948030340038801c40758405 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 349421825 1250 349420575 349420609
    0x8030106030203041b0909120c030c23010905011b0f020312250c020a05010c0507090c11100507020c09160309080405060a03051b1908060303091e030f0102031005 71
    0x101726481c0c0d807807079075544c0b0002d0b20010b0000503c101150500e1111041400d5202080c8200d034a84134011a80101d8048126944240041d5602c2c030390700b480c407000103510990160103609040b000010010103400520115103000703680f40800d2031560b0200c484508040403440980c00400007541801d072640c810640c007480d1818840035006541034034140580302a403c2d50000781e0f8000c1450218500101c0000003000c0919004000d034070580c640740c1c0c0311409407164000c1d06546e05244d034481e034043c01001900c04400301c01e40e285c0d00d000c81d80c4500a40802c5500500501451812500380d1901c0c80c8054018144103007851440701d43c88034160010281400c086e030707000700281300000b019079074840108000d00c0d190364041114200350201c401c4030300a0007090b0b6214201405141d6078000d03800f84000381c6070704c43d203400003440d00c03803c1c040307410341c803912000a4004141d0000c0d60010b410706004140500000e404443c015650018080c0c01c0b40400e446503003c602040c00304000a25100c81d160b0350fa8456 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 349423075 1250 349421825 349421843
    0x3010b03070f020c1c17130504020c0127170f070b150910080601080109030206041b0504020d0501030506060d02012f010501080d1130160605100f030803010603020304 73
    0x904c0700194281c8220385402c0094550201c0400c00c0180300b4801107002651300b07030f0160408002081d000e00c1014103000c0e943c042c50380031640515882c825001000d40c0000800c0400d1900e40784900c40d090a44800c006840c1c94001c100450045140c04080b1504130700001e940c00c1c2080c401e82d4442d01a0759024008211024081401105a98a400410780280350070340000c0c4210f4900350700c2d00c2c10304505174081d17881a4035186021000c00d40110b00b0a5006a1003484541d10309041310b05150365155941080340c010784046200d00701c5101d42d610880c182ca00a00803240f2590b208400c00020140e0241c00030f000440c01ea84400400b8005410780100244217151254045074408507542190826440394055138002d104034003500d500710305071a141b01d000c2806030400d640e400480c030070b00107c0c509204904c5070b118958460105144400d45001714021030511208443d9800c00307030040c25003076518010038002c11000065100c4c1e0400e8200403207a1010030b403411a032a0940960007034000410645141c50 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 349424325 1250 349423075 349423093
    0x30308160c0b070207060906051623010c030b1806030c060a110a0b25050f070305070602030403020d1b0f02090a06120b0a050c030105030c0d083a0203010b03070f02 72
    0x2d980d0988510030390003940241086464030500905072440359200d02d0a1080421041e800e04800300c000b040d9040c4c10035028036850400c4030356003c4036800354000d0f41840d4a020304866071140c4c1a040f865070628121800002849894910007038618181d03040c81d416400403c01c9201e03070a01c01d010b4810107005040101003001c2c010700e01c0b41000d008500464021504104100000d01031250700800e040881d0083c000c1388418901c050054810005200c81c207000c041801000c05101c0c030115525141d01c00310541d00c1c2c0c1021b00c0d021395076a042148400100b1a40301244d0f130400d1528a840728255001030359110783c221035800b40300b04d4100152111007901c0c0c490201103080b60445c100310310218031036440d0901e54a8501c0c1ca41c0215000078001030409401000100f00c02d94001500d02d020b10004c45155944a940b40f42005a40c45102080783c104030f404d00f1140044010008004800b1401c54000410350440c0d56441c0228402406465002c1c1c0c004d01c08140d0031032140b10240200031071801242c080403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 349425575 1250 349424325 349424333
    0x503221202101b0c050a0909081b1606030e010c0203130911040914070e0a15210c0c060b0409050d080c21150901060e01050d02090909210301030308160c 67
    0xc0d16150f01503507464502082000b1508000c0064001805158000c1140036201da03900122403181ca124005482c644003c080c44201c01403103a4443c0c1d090300d8003910110380d56100003401814202854021552a069803402240d0001c4100c40050b40e0710388a15400f0fa08005020004125242d5002da0001007800b000c102c2e40018801d00400168110f0300c002503103800306009006850200440d4040d044800040141208147d00740c0007202490070400b9503428400c0c00c61620300c2e64001b162040d241043c4024541d20303040f058403141103000c0c04043c8000a04a02480701380d41d10380d500208554000d100e005481882000c9054210000c0c000790f40c0f4001c00314020f400c10150103035900500342280d000748410039261100f5203c2d52030040e1125119585804030180604403040a036a062100c0050740d103100c2c000a604076a200b0703c000b02000101d042c845441503451180c244d400c1d521803071020000c01c002c1401c0099074104c81d40340d6035a01c05aa00c1d009100901440e4503508010b115090644c03200203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 349426825 1250 349425575 349425617
    0x6080117030d110301080d031b08041103060403030618140105100507141501090e1f0603021c0204230402060a1704030c0b0a06080c040203090705060403050322120210 73
    0x800043d1446480b94101015241010f0a00040e08103040c0303828400302820000c000410107004250900401e00c0e40c1d18184948510b9844000300c0d030501038503080004050301035010405581100d01203036080070408002030300300d03000fa00d502602134980b180100b040c0e00e0840c1e104a15401189000350408040740d507640004140740c0072514854001c0b07500130100c03214410b922401008502c5d424001e80020160b016102c00c4890181008544044442ca000040e00d03013102d001154003030400b17210384100b8822000c5030000d9070400c03803107942040c00c0450b400c1c6001c410b003c008851210a46210f440b66801c2180c0765021110041c18404021000380411008081c00c2c0d1140d4001d84074082800d0aa181101407404003c0c00d10640301d141c030905102d00100002c00c210805c10950300183d0300e4462905161034001c05e5448103501100c0050302200b000b07404800351285403100d0000250000c1034030b00042410115002d0700645040d509070450252034008003407144c51030b0604100005540d118242244 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 349428075 1250 349426825 349426841
    0xd0c0807030302011b0504060f0806210c03010c030920041512062d0b0f2101060501020a0b190b0316050a05370e2e06080117030d 57
    0x750f5035414014204802100302e8a070b41e48030707a01c6c00f24600b90500350041c16021091100800b00402640003a07602e89651142001e921424440201030080d0601519944c01e0b0444289000307508104000184500034011401d09503800388280106030300941076148102e9030f19141c035030310540318500340d1300c941c0084042c9d40240c5480304420111140030304006007901d01c3c842081694074880e40b250146074103204040e1401c080c0607240418404001c1c3c0009800d031036102056948040c0c01c540c1c481307034910030901e028809031400000703120084d65000160380ba401d004801410313540388040081c0415003800303200180340d13000e01c5000409a075160007003450300644607418008680100740a200a140024844c4014041140e80d5031096500540824a000030009680080c00c6a02c2040f080c44400c0c81c2608080c1c4030203203e16100341380120040611407c10f22440c00107011894180108012130200101a11119181c1c4038460b487d0900000c1188810004000d0740d000a01070100c14003000c0c090800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 349429325 1250 349428075 349428077
    0x51e01020f030a0903080702070e01060c0206131d01151205070c060e031b030f0702010f12050c2106100813140109030305090f0c01030203060d0b240d0c050d0c08070303 74
    0x300885280383c080c02c5100301401e60f07c15541b00741d008200350190071005038107491442c901102611410301c0440c2d01c0e40240003043c111032200309004170b283d8068540f500244003884000300310690362510003a5030300d02442001800146020300d900a4064039801642d0040d03200d24248801e441c05440c2c03135088403c402c0c0078003d42c0c0c100082290000140c03072105803c002602000e10720305907911040c0c21440c1b25054000703041c00307080754200500358000c1c1c2940d0f0880c088054144641d16025401c1c21403544201b5890784800c00c521b958022480301c45600701d201c0e07580941444125202c4400640c0c102038010120720340c42501a603400c0c000791400c0d0048060f000c10380004104e0b60014034020f02034502c0100f00c1c404a50010440c400c1001e400901104900401e00340103940303858a1001c280700000c2c0703040c013614101024050020000d8000d4500f4003400030018030280a0400804211070728941083c0a040c0c8003940005014038982501d04030750f014030901201104039038138603003541005084e0384254 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 349430575 1250 349429325 349429331
    0x328050d0207170c2b081501053a2d0e010e0604060c18030311071203050702010e010504050a03170909040f030306060804080301060e01031e0603021804051e01020f030a 74
    0x14610f2805c1c40010704002c1da024803046102c20b408800400c041d1009200403460084ea18411100364051303c01c85441c1c6000c00b0f4003030441c440440380144249107040c481c12808042043c4601c002c8014030850701c81e083d40b101820400c07010300e040041c5c0241c4a1110380314a50395235a010018100904c6080c144040d80c4000d400c06180506012080b0340c81148614240300100108007545452451b0f40c005032a45070501085402d00d4426681c5090400d4101000080c1280d65081c00d00d50400c001d030107410b100b6640c0c0e070500f6803044011161801103120f0681c03c910321050900c00110000305500c414a0159040d50501d4042000541c0b10383e0142d0b419107688108070001c1040c541e040c00354002800c0305040c4113520b41000d41d039903445484140300304000c111414480d0a250380c0310340c1140407405400b441014815140c0801c4000800d80340c84124807a65102c1d6107440313825800300c005c9100300c0d04403001d00000c404602c6801941c40c031101110b81255820482800c501115802450044007024400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 349431825 1250 349430575 349430593
    0x30a2f0610180501081c05121801050703060803090f03240613050720010b0a06030f0b0103060503250b03040615050405040b0106031d0703050328050d0207170c 70
    0x84031009030642e80c540a0745080c0001444402d80009030030960545110808410f0105080f00726030500500004509070100d00050001024486401e24004294800200700e0390711041415011038203140b05401c0c0a4200740181d2859180c003820f50f4411036800740070390f110384851050054a403251140d0b02e0200078013940030301032542004640d040b40f00303040010410584c2043c40c001f802840c10121030000b21001d0900c040c81c0302d013013034015030b00090001c0c0081203515181d250280c050103803400d0400989140c4246280c05604c00c0c05801d007182e0018024040c820855803042e1b8606c40e04217014400c0d69401100062411440707002584034501440c8000707410a040c0c1c000030f003070000c603500a074400c40c20034040c0004689800c0015045400c1801d000030982414044002504030022a10100d401030940002c02d200c80400205502c035401d070303104200f415494020780c0304039a8a112003800160300340300b030710000c20090f801840018015211841c90fa000c1c015000c03e1a882a111307445150070502c10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 349433075 1250 349431825 349431839
    0x40807052b15021e0c1c0e0904170a030f151d0c0c0d030f180305120901060b0a08060f150406110307060c0c051203060303070f02061201030b100503030a2f0610 70
    0x5080b90740d140c40342c1001707000541c003030000d00b081c1d40c01f01d8240c41441680042004c0141c1d21400c5090300e226504906c0d2203244040c00030b00145407400d95900004e04103401c4440380181402030506485601c5510b00080002e021001e000c92070081034480c00d0802003100182e00803040101100d030440c2030750040340201340c540f1400c00b9201000524039090f40103541440019400c07400352003e80c0014803080c100313075445880541c090100c0394440c50507420b0003d142d00c01180e0100d0f40a11030f43d800c3e40c0c0594039100c03200c18070601c1a50001c15000801d0700b8042807050901c00c042140c4800140d5040b241803000f107480c0c40f422124040c015001003020034007140c04208052120781071092054000605510b001c0d000300340c480c42245001030565034070f01d80c42001c550328102070302d0051080c6c1196211540c1c407454101c5214030162101c03000e2000240b40003880b8a80081240d0384a13880340c0c0c2c0e0920807188405e01800c15403d4100a40001c1c54000310100305010411805108405c0843c00392103041c80d10705 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 349434325 1250 349433075 349433083
    0x411120304080d1d040b040b150d05062e090803040b0c060603060402102a0606051203070203100e0f060415061730040807052b15021e0c 60
    0x646400c2c000704661110b2032405840b070b444c644840988021134000b0110700018001c0200002e219481100102d0001c81c1030002001f070f0401c07102d0160104060303169141000b401140b040c8000c0001d20340409080f010404680e40c1c0884013030182441c5c1c000a840c0c0940320b0a5130000d4000e40c000709404030388510040b41c200b0072660054015006845642441d8000c981811890101181031108a40d0440b0082c0392402c2c000140c01006044001444c42500d0144003414242c40391030300c40e24014a18120784d1a01008503104181d008000308040c0400c20100c0024181c6200440210b009220803556054000d0203013520840c404c0410a03004504002501c08403001500b10140d034100b548a528100400041c040b0071204034030780d08191024038800384480c4055012080b00f52450042400180800000b8400f0242d070300032117502180c1c240e11080e0800c0456444002a46112540034901c0070a0190801c2040c10410410151a25806100305009100c0c850069a40140001114a90024148 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 349435575 1250 349434325 349434343
    0x161d040b0a2c01060e090c0a05040f09020a0e0a120609020d0b15030610060c0b1018050f010b0f0a0c02030c0a080c0f030a0c0b0f090a0303030504170906040b03041112030408 76
    0x2050032120180d042c1c02146d04604000c0181c0380c1840e0008802d16281d002d070003501c00a040ba0b524071301e5515214400751020b03410500f0f122020510984080c00e1901d4110380200540d030710b8401044110f141c40c2c96a4014004850059030000d110094544c0451840e840300c84c800c8847c40c200d00311154181003030501d8448000c11041001c4508501401703900d43c00400c40078101d412600141c030907103440e800c00410b0310081e40003080889900081031640c0c2040d400807449442040d038111026a078030b44042a151144240c900381102080200e400c00c940580c0c04112400d001404139280d0039000c0000c202e41180d60341040d00968041c2c00355902e01c1c542a007c9091280050700900812042d80d030b0344c0000e1283c01e009030401040082010b1039991190b030180c0b40801c100908982640341e590074083e0081c441a581a00c848040c07409200440065504854112801402c02445c181c0303840c50f211201e40000d0800c644400e450f40000c00b099480101c0310620102e600701843d0303954548140d0354039180c0c0031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 349436825 1250 349435575 349435577
    0xc031a010509150603041103060103151415090a06090203010f0302040509030c0d0c051501030804060806031606050906090307080303070f0908060c0304050f0d08161d040b0a2c0106 79
    0x4801c2050f02c00f0005141d280b0344009448654a07520fa41c901860303071072046160243c0601c034020001062081c03c0c44036582800f1001d800301300c03400840a03980c0c3c60340b0007104c01030300c4c50348003500491070390a210000302d51000c04403400050103611550000182d074420707444211800790711b4505000b549000d200b800c1d0004084c0c0011447e044103007907103e40391102c10844805001940311040c0c10f20409100c03400f9844070b20107400348a580c480c60101c0d1250054011840004c111400103002c82c140000c1c02c00f410010200701c20b400d00e142080071203195210343c01c126009001030101803001c2d01d003000100040e1a1200166403030346005a001081050003200880402c000000c0c04c000c440e0002c9806130700300b141028041e5a0b40c0d05d07424401d1038a0018000664503100700c0c401c2c524420b0f80140503074080c10004082c584072800900e41124510b140759000038248900394910100c0385040c0c0e02c00007007a2009091003404c180d44800c0e81c11800c5009403552072018002562052a42e00405203d000d4015 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 349438075 1250 349436825 349436839
    0x30201020a021b0a15120507050a090e0403080f1005150d0c05032503021b061605041410171003020f04020705150916060c0b010801060b031603090c031a0105 69
    0xd00c3c00000e02e40401403182007200201d840042c0340702486940660007094050f0340601c0a402c3c4050010101c1d0701c001016400500d200d4404908100300303080300c0d80501e0f010741da09109900c54150245214034003030440304200040400000d01c0d900c0d01c07020340240d81080e11030b0588a00141d01d08100740c81d414801d040400c50708104001c07150b04641c12514040d0554107142444100a80054000b4031801030364080111280581100050000800a2240c01c100d4040101d076084807405403400d008134040c0318001c00d018030010060341043c0c01c110300d4041c858500f401e004c0045800e0402c401c0015210244401000c0d00c00f0320660502049200c00c1050656045107003000c03d03151305031208a0010f6610303881c40440e0100d02d1050040040142003805c03488007100700c0d9620300028064140860003214400c81c01c0c0700001758190b042c03082c0d01c01c443c20360074920324550b92590900002c800b40304038031040c16500c41364480444e425a41c04000b031840307108104005d11030f561105100c200c05030301051240072 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 349439325 1250 349438075 349438123
    0x70f170604020a09020c0109150218040b01050a030b1305070513150509040c11030a170f04030915180f080f060408090111010b0414040308010602010c05030c0d0e0109030201020a02 79
    0x2624460a0f00304c40000b03070010380b11070050710841e01400003100003525040c04604001c52494480c1e000303245144541300a9241c0b2240c000c2844160742901c82300d00d004c20300900c014000c2d40e000e07421a02500200819004905144100b21822150241c0321000007a80100c1e84001850303001440c6000b4210075104003030204110b20300104141b05440781c1c1401035131502c0401d1a61401132150410100b03901c0152601c808852400501c411483d40e00141031003a4080440c00c2e540e4041070301801590035030345d6484614248070514040000c03038200002000045402d03075019507000b4000070050000e07140c8505c41ea1b40b410195a14040c0400c5410308950440e4003440000354280d0221241d2502c282802061a042021454018444e00305c5098206051054040c009031800303660a10031440303501c0d445000e0f42c031800304900302c40320322018101150f001c00c08511103803d0b210141241040010340458070300a480d0300315082d610000c04c1100541e401003000c0980b1501030082e03170350030b004503041150101 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 349440575 1250 349439325 349439329
    0xf0f070807090b01020a0c090b1c020603010b160b10030b0705130504050604020d1a120f0a0204021602030d0207061e140f041e05040606261008070f17060402 69
    0x18030039116205041d69181240d4083c0d900900c010010950842070340c14419076100c000d04050030003019a00c0c40b6116500d00e80510f0468034010240568014018074216030034107400d00c0f00e0f42c0c00001592640c00302c2c81403140005410280c240d218152064081c0001c52551410040192000c3d04e00010b201003803098030043c40301400140200d60302254082030584446002c24024450b07000109000b03814419041680c1142d8401c20f172030b01304159590030070034440da100300f500c61000701034030741580c3c1206100d240075251503000b03800c50840d0140c2d0304641001d0340d8006881d09a400d080300c400b607004003408104154000f2011601080280400000b04554100040200d00c0144031345d9501d00000c2202c005440d0038400341d4010705001d1541250700715203440d46c010601c5d82c512983d07105504004020a0540c030a21a80c0300b0038001d00440d26a001800d00400c040721002840c0c3e40c2142c044035400035145904001800c01050442c51400c402401c00c0c11540740b2080e400721070780340c5600000c1400016 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 349441825 1250 349440575 349440583
    0x5070b07060e1c020c21070803091509180a0b120d08060418030c0f17041e150e030a0605160207080a030f0809070e0c041e0e13050106080307050f0f0708 67
    0x30007812600803030070046c0b5880324050204c8511440b01c05201d60200802c014400000501c03044404503880c0884555900d1000301c1c038403507030080f2508400584103180c1d0486001c1821600000030160100e9035049040209607601c4000352111410f030300031210342020365000540d064000360144d409003c0c5110500d0b01003407080003d0303801000c1000a040c280b040c0446072180300c003a80d03801a4280c81c0746011001048642d002030040d0040301a12034107169409110241032400c07640701452100e0300611509041d224149850313200e03a0075024401c400300004425214061080c0b01c10049410741403e91800280b0340b51290b0804a225404459000086078002c080e0b085241ea891030006107c2e5581e01449050541c16404a08000c05078024008012520340140054446104c601d508443e65078503c5809000b01d80320307002c11554440c000c41d00b01d211000104480e24000d000204080341d0302d402603880d660101c0f40685064101d9200080b140d6810b0003030301942d0b07410000a250040c100228036880d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 349443075 1250 349441825 349441843
    0x8190c080415050903060103060507080a02041a070219030602030a0b040908031519080a030f020c130f02160803010e07110606210604030206160302041a030405070b07060e1c02 77
    0xc2c020340d50206007905106904070307102002d0140903034005513980d02d840380c041c0000b80c41210110740c0b0980002e44103451842600c1c2160200e02d11018010988a0070a0080d48811810b0f6006001b8544091a40405c80090001103100d09401030340c0713180076000c0104a070007240ca05403045042040d1280411050310540341c100c890211380700409003800700003a0214100500e0340076000b07490400040c80b18804200d072075244e03019860b070070400142e01e40100d803161101c079a11944031070800084c6141400d10f50241071000200d04006250002d01943c010795000c02c07000403601944000010700c03511681d911540c0d04040c440c18540d80c10046000d0843d1541001405075010349c0c0104d0003909655003003000d035010501c401065454500f46800c0094560804440d4006204444528062000c2c402d20880303045a990455641c205004082c0142095001074025121072040c0c0401040800440b0001c1640c070b0301c184800910114914000b508000e504000002e0100340c2c00c45040040750045100e400d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 349444325 1250 349443075 349443089
    0x51003150b040216030c051212040b04020301110d0e010c052109071a0703030b0909070302040e0328090b0301061b06091514060a030c0b130b0708190c0804 68
    0x281075000400840c0c024081d00c11004404401c41100324141a0802e40d0000c2e4130b4002c40645540d1100c101d040401c07032064a003c11094550b4000160100d64051952134016100500104440d6080400310880350403809901400300d07641c0309001040f6000344204c01c44101319003022800c4c2090149405a0703d00204007080c9184008000a02110000c4c09001e01501701c01201640740540708092000d60f0300315441c12004240340210080051078030944041c80341c1c106400030301c1604d045500b03102c090300560b40b031800710340b00501c0b0b030904008251100c440342122002c0107043c0014a142c00a00f864401d41c0311000d085010401402400d51040802c490058440c442d0031407480301d850100c000b0284450060308000d840402d80259404581100a000100e20744040c5103403036210810050114030b1000810840307503440c0c00c2011503406005030a0044214041c81d542a5075540d0341c4055a103e0a41101c294100003008004c0341d0740c00c101e41e016101d0b103150113410724000da82d9080e02c92103240a200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 349445575 1250 349444325 349444331
    0x70303050a0c030c1a190e0712030309050604050606030709020f09060c10141005120a020d0f0803090105040c08010203040c050114041a0706050105010804111504051806010305100315 80
    0x180c24580aa1080d1079059813000a82e480401010131648178a0310944c0c0340080f0074103101e104080149a4011180f1030300071000035106080c0340c444070003002c4003020070480c2807648170007484000c00c00501000b4400d5025801134000303484d21004150814a65412801d001d42c03060081c290803c0c424001d4544a0364155600c8c0c2d56034100c01050780c07800e0045548039412070704111116030040400010103001c1d107542c4040584198030341c030411805041704151103c6c940c5c040f80800c400740c601070121040c810f0090401c5050f02c00c064031070341c00540c0101c1e0040301903915007050000304038160000100030403022008504500303055880d50081d81c00e0b07104182c100308004009410002001c01110300a008201d021b071080c4c0080016000190440c079030070b541d02d81c60240005030300c2d409107255520469110714444083e081c820100280402c2080306045210400d10000c15691201d40052407a00c030440e05207611494218001400d4820042c641403005607124010400035949541400341c2e250000004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 349446825 1250 349445575 349445597
    0x3020108160c112808070602011103040b1008070806060117192c0106031101030903120203090304170616021609050c0f0f04140118030f02042912070303050a 69
    0x1050b00c40085501c1200c54800800b514090344108404e0741107032285429a10b0b034a580348020ba00301c40384140070f01d42043e01080028000346407444800c0d4484455140140002c2e15000d110780703403543d076030060b01c00f5510820074080c1ca5a006128043c0070441e10940300017a02d0440103000303405101000106c5942d0712402c1e1803051090000c05420702d034006e0b800021240000032045c07070291420744002c1e80c9000111600b81c1c0d41e9446809003030000d5425403074011451101c3c2c0081c0c0004d40c40182a18103601007030001049404144501184a14540c0d0050405007401c1c116401ca42d803484607903c040d544410603141c09e0110f941202c00407a203241000040c42d030384004245020344281d06620980c86000964001c448544001410030742c2c07135840407042a0700c424001551494440112111040c4aa2008000055128441080041c4060f10201d42c005184200c1030380944400d40d400e4600800c00d80c035004600f0f04914030b0794a5491032000302003451445d14090494801c0c1403040003000115424 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 349448075 1250 349446825 349446829
    0xf0b04060903020405100519090e030405060f0a02190609020906040507020d05090d0b04030c0b07020d050706090302010b04090b150d2006040f0e10080307050706051b01051003020108160c11 83
    0x294008000103800000c1d180154254140c0082c19406000600ad207400d10407010400004203450540e80003501081c03030410b00002803125900400b0303d40302140b280084c045900003000f440c440300e2511070309003c201d2001620401c00940c0000b4a0780c3d00507450107041001032980040c24414100560420a80d9405090040b80752004140806001c10400800340410580d0283d43c0c1082a4002ca50960041c3c44500f022078446110752500400501c2c144500d60125045034000411180b2a0000150110b03041020070f0940b80d0203c07050b075155110301c1c02c001003180083d91143c111503080300c02e01e1031350038035036902ca1415403940c007440480401810b1403045612036008032805010304d1000303507600c290744001915082c00119603020060000400001c0c5e2054008182c48850342d000020b061111308143d030454154200b444142c3c1d11080385009070f401c00000380300d028000e80c03000f0000301e0258154000075140f00c0001c0c04081003802522a9021513aa03c00d58641c0710552200400c106890f440300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 349449325 1250 349448075 349448101
    0xe0a02091302063010051017070e130c08040605131703011a03090616030209060c07080d0e24091c020f0406060905060705030706050c040f0b04060903020405 69
    0x103002034108100160628840b40c102c2060100b109008040940c4070704018600112604c040d03d01c10003040d980c2e0f0b010b0019190142c0140254916868015103407211202e1843c90070300142d952001043c02e245082d000c5041102466140402203541400004502200102000c400500160942d541c0e04086050f1581c0c2e4401000c4a41e00101c20300004011800740042591080c0b0a014000a4000c403440602e121802543e208411704c034040e02d802d07901c00b40b40ba00035410403400c910070540d003000014a15592800075080c5800a40001c11210707040403081ca1900010100030340030f000d403500308850b007940c1d1442240d60301d100000c2151620106044400300c6070044100650f13210209480d400303811000542009101c81c021182d100d011410b03502848110341c01ca02461000400350103050180381803440051508506c540100d80c0341a41c0ca0f1945400c90b4002c0e142c0844480001404009501c1c08120706405000311000c480c0c607007450408040c0c01003e0600c0300901850701c0354001074110758540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 349450575 1250 349449325 349449361
    0x1b15090b070801080118030815010e03100207030305180c0d05031e030f0a0c080112050a0b04030e0901210b0604020c06090c2b03110307060609021c0e0a0209 69
    0x110403025800e181e440603206440034010080150300c0e1100c20b140c611040c2402104154042d01d13659401d4850289100c0e850004840c01030506c026501030b5111610200810100c1b03a5070b90b2030042e1144a245402402d880d005082003600c041c010741d804181e020701003001d44216004480d2101c0c055228a0400e046001c4c0c0100000555000c01110316034240d81001944203001003401d800c65603654007002d00460f4200c4c85544000740094006100c1c001440e240401c6a5000700e044500010003543c40c4590644121404c0780040d1801228141d142000940c1a000d0002110303181d8a00c0c10540c11490b43d03102211024125021f02c1e80411010388070703a03040780c00c0c00489106403442864991149650780c400741e420380e40202080d1406a0420b070945151034880e41801071030704405101524100d8101c81441c81016042c0001c1000000080c481d00c59003000704114400941c4801201910031004100c20307080c44c20b02402c200c8109004000401d1032207205a040700d40341604d4441034031450380d0300110 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 349451825 1250 349450575 349450583
    0xd05070e07050418140402092e0303080c210a090f030e0f0402040e1b12041101090927031e080406060504020a0f0e030102130b0306040c1b1509 63
    0x80c024415030582c004010801d4403201454141c4890100000e03000f00c40d0005480c0100b10210300204005182c00301130950001c0c06480e08207409084401c601010322043c2100351807000381100200101508401000c2d80080c101ca070950414886100b1511030790f22401c80b8003940c44614000030003501040d0300c0038142c6034104509854110b0ac502c0c0240400d007900d05242d01c12220520703d10224901402100c0c191030684011802c0d40c0c0f0f64000b080700c105259035114140640c00c0c0105107045420821b95449140500000d11107003030144005410407615030819640039050840c400c21003840d40031012960703c22a050405507d03501d003000c50f84034a014515611054024100c05001351340a200903024a0156104201050b5100c0c2048100c0c420001401e000c5403074a0304038440180510380515841d040640094941031250821413000415500701c5404c03408007200b80081420700e0b100740c0b043c14800341001a10500400c0400c04007100c0400c3c01000620090b4400c49400380c0703904410911030740 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 349453075 1250 349451825 349451849
    0x30a200309010504150605010509011101112b1104030b0601110f10060506040f0b03071701060801031208041110180f06110303010506070b0405010e100c200c0d0507 72
    0x252030301a010b0f241c02c2e0340944010315441c48040c0741c0a41c52084100320343d0305846803407500708200015900740b501c005007410b0700d541c2c44c0c812036181603040f0006c14074800344982d018101a03045441c000c01c4080d400b8840c21041c0703401c001282c0084c0c3c4604807020b0b290803c4500d0030582c1e460004030f406008034034500030729016030348898804040c0040c4020b80d04503081e078144211500c9009001e5030b409203208911051039501410811a01001e0056410450620f00070004440d141441101d00c0c02c04ea0188001803442c00c0100140f055041c1c07030403403a490324076080ea40d904190300c5030001206814a0144603030000d01c500950a0301594040701c12260f250820f81c565603584450522040940c0302e0040411040c00461402c5007004c011207042c0d0314010300c003600300555034a81c150b0004008000b00c0e019940c0705004c490980e03040101d070102ca8505040801c0750303420080c0051003014000280903c0804014107440708c0b060105503000100001e8414480c003100608001d480c00130541c1c003181074024 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 349454325 1250 349453075 349453081
    0x4020a03060b0609121c0e0901270903020604032c0907050d060305010c091502030a030b0a05041b1407020a0504090203160605030103020a15050306040c03240f0f0b030a2003 76
    0x5004504014100740003003d46680101c81b00e016944030120840741c9500140c00f100501091009100402d0100c1c9107050305c0d44501e420074900c01c1203070810030064001d0f9011600300400c25500070384d50403821440c15150294441c031010300b441250b0700c901425104043ca000020042d9214509a4010081c02002408525902d042050090104585250000700800404944080c4505a0140604290b401185001d2044108a004008031020181d100781b03803031b0700001d640d5158003d403000314003001c0c1c1c0b120903c005020047c100f1180003912801e500b0003442140c0250343d0340c0c480303142110b01c00c1d1000700d41a04207200090510072840403400040910410218540740d00c00c1c0034505030f03882076aa08004a0701c40200140c9010314034605000070703404000081c0141499000f0015038082410041050150207010101ca02030481d140d00b810701c15032000300002c10007000c000c40242414824446800d09008003c10305103c0180b210362055100c0d007880820740d0b442c20044014085203400b82e91281 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 349455575 1250 349454325 349454359
    0x6150708030123061602010917060f1006020a0605040204020c03030f04060c0302072d0804121502041a070c081c0201140601020606040f0e06100e0901020304020a03060b0609 76
    0x340081c01015550241c5070140b1079241840103028801800c0201307107070708084020f030800d450000107280403070400603580000a05201449864009140c02d00040c040c1e601d001405610781e2200205101c05e07521070307540708000d00394022860320601504050003082a680e60300104d0080c2c0f04030300358250306220020400014072a090b886500540c806c101c240914062144118280e01a00b40041e260301c0c1c1829407041606000640345a003074101c00301e414500d0b41e41e9150300005400603403241c0000e82c07220381f200d820404e41030040030301030041410450505003084010700c030181c0c0c1c0185210082000040c5074080c058136081c4240201312200c01c9480080c1200880c0440001800401004d50f003030944c204409070710f2100b018451481070380209034a9031141c040001a14512404050300c43d1364041e85003160700103011743d40c45050200f24001c1c0c2c2500d401082103c05400a0010809900c1030080c0401650b4242081c03044070340214000c1000351920001030201d1013910000b03540100070580c903c4041c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 349456825 1250 349455575 349455577
    0x7050c1e030c07090e030306011209060509070f0e010f0e07020a08030702150903070b06010e0a0909080304140d02030301090903050906070c09060f080c060d1103132001021506150708 80
    0x42d0707900709680324690703a201200d05450440484284640013400050110f510500100c01103013007089000c0345001290300c4010464038243c5030700c602504402e07418405841421038880c000d102504459080750314080340c42540010501031009001c4403c0041000796200700180305281d41c2003141c982d5241026000656103095100a15041c0e40400700010b404100101c1541c80507504040e00020320780ea14001140d002c02c031007015652000e0354620110740481544100d00703401c0d00c510000b580e41c0c1820709005020f03400078070f0181141d600000d02d80c0c1b4400d6010041d00e044882c03050780400d01e1441460f0544003400380e1410301c0c1e0400004035016040c080740700582c00031110782c40c00800071141c0310708030765803640d06a00588040307038051000c076542810440c1c001e0000c000562000100d194400b580304411398030a0300c4025950807002c141e2030a00810442c480319111040000360100b03591000040c0d00c0761940b00402c0e04030041c240020302d040d11011007102d440910f600c10517a40d03502a240c0480a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 349458075 1250 349456825 349456837
    0xc03040e090a120e012d03090c0f030602070218070c3e010e030127050c10120c030c140c0f060a0e011401030c03240c090801150e07050c1e03 62
    0xc130b400d5260040b008620082c2002100d03000c0e14403028842c00c2c241640034201500d8200d981c0e042c80d42740040e00079810903000025500c19040581d48e40d649004015000005000401d2508280014018403d4100805070741c240e600c011100e050213020078211070704504c51584e440181079195142c012948002d50f5000c0e40ca20240c944140c0382c15080241401c03503001d11010305800030725082c581d50040c110310029010070b11600c12180000002c3e00403605002c01400c00c1c50119144a0a800c0c5640e070038080c10740e00303003c14542000411650384009003189a03840408050080c00954550150810b204034880c022071482244c10909014246100504000c1e48020065103070808000744031220f03410040c100e0350805100c0c0c0321541107403180050024500051041040301c003c030810301e0301e00f600401e1200301032911003d491900d0500d1150030741d903082010b40c1c0130348401c50041c40000ca003114080d8000c440351414030388401000742c0e458600300c0300010888400c50300380361200340e500d400030003000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 349459325 1250 349458075 349458077
    0x50d060f0e0f01030506071101060b070b06120a1205070807061424091503070806070903061d0604061a060c0f0d0f020a061503021e0a0503030c03040e090a120e01 71
    0x14281e40d0481002c900070400e02000b4400e40020000c692005e2050b52151114004100006521569044078030034590200400300c8080c806141001103503d00203c061512200b4007001d80f0780810a541c5601100603514144d106105021410205014010003079640c501e501a1080210720b03020301101e080c192003161600c50a00030302214000c004141140b482c4c181d100070300500e16980310612000500d8201c0302080b83c15100e83c403000220201c0820805000b00000d0302d40000480c2141071120940b081030300004064840b10343d0740881d0240000701315a0181e0445000036050399120134800c290b61044030b00c250300035000701390b465010701d0100f00c45900d84c100f4030494000c924000310a03a0241e038140e002d140503130880c20f03060005c05c41e0f5400090300c0c1406c030205d140340d00c0d403a540081e08070030f0454200400e00042e032003003c519050090741d2002400d4111300440c240001e112216a0b07a00c2180603220f070501980011031101c21b8100000f03050703103601c04c1034000e8086110f0f000800c14038017404c03014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 349460431 1106 349459325 349459349
    0xa0b030a110d1e0201170114090c0c01110d05070c0f060e010b060a03200414060d06030203011b0806010e09041101180b070c09020f041203050d060f 65
    0x1400340d441d150b43c4006250103000040090003440c0201d00071048120040c001d980760000540c10034a030444410310182e80e102050030040c014400f040309290b0031302c14918520b58202c0050b140040e0818801c1019580d11242192070204010010304441c4907200ba01c40070801c0c40c1c002920960f44003001096000001c0c0c0032070483c0d80302d000c484000a5485c0f02c41d56180040c907000f085034010308000c1c41d040034104801070141c1000781025034071481002840c0000583c060308204010764000f070003000b4160b201c156624038000c5101300400010041400640d030b96000d01b1025008583c064a40d010a40d00c81e40d030404410300c45007840d4180501b101910170400014880c240281401b1102c1c65100e860380c0c13038111407401890b04100d840328014000100600180300544044444140d040c4540100e2401c0c2905c0e03605c1802c03481c4050a0030890301044002c9100700807402c071001c0711140 = true := by decide +kernel

theorem cover : BRFrame.Cov 349280575 349460431 := by
  have h0 := BRFrame.cov_init 349280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 349280575 ≤ n) (h2 : n < 349460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
