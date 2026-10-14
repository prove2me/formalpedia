-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1668
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:08:43.760823+00:00
-- url     : https://prove2.me/submissions/e4d9b0e0-a6c9-437f-a3a3-eb391d591b0f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 299820143 ≤ n < 300000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 299821393 1250 299820143 299820151
    0x6031f150e1e0606040b070c240903030507060212090616051612030e1b1008010501051e0c0f100b010903020d03050c010f020c01020c011104060c110d060e07030b 71
    0x9802000140030b0304058051035021650b02402000c0100e480343d50008000b40f0881c0e005101141d00018a107003003018a807201c804031124504401060480c485450441c0ca50400901300062908402800002e00035800b821020707010b6180141480520b04402e4920382041d00ca03104260306c8042001600003045a501d00300603080d207480c42c14031800401070286c010f01148024100a81801400354061007a8040400800b19100b1105013804007104011210b003ca00000d0040e45500f0480b16800d024900942c100e40c0b0680d141072800c00a0303008208510315030144645030050030408880017003420001d00e100d61f21510060a0f0100164800c0030443e1210781e003e82c14041035010400141c3c1d0342008260816400d810041c0d607034400500c0c0c0600400c60808400229803010403503600c0e490056014104102d0548002c00c940c5111104803041405141708190002e000500203034001014271505098908010301305400f5035113165940700549a0300304944065a200001c10070a010500c01c2c1e040d00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 299822643 1250 299821393 299821409
    0x1906050910150506090f031e0c03030a080609070309140309121b010813170a03050a0605030c0103230c03060a0609060c0816020901060f0f0806100806031f15 69
    0x184100c0356001da00c15030030310f106080c450130b804103000748184c40d1141540c0e07a144000b4180c464101040020010382401c4a100302c095200301901e0401034180042114076656443d241d51480b90750311401c2244c3c00b14020480b00400d0784500a0400040f41c62503d00d2440c428038000e16103038207a400a010340e1440c1d20a111840c2d43c426003001c10300383d100d5105448600c10030719184100741e49601500e102604203140041c000e5042c007003a05c580b8004140030704030411035580c0c140040d403114030505058580170b0280703541c15003001841c4600341d1b010b540281010000c0c1c12042054040039000c126041c0c8003183c1115190100204009603840c200c1148000b400881c14010005400d154000b80b4002c0203003802044140e0000d100d010b2214009100404994000c048007059a12504001e0044040222610100f030b0031310240c661203406583c0352881880054040040004091000c482d0b40318054001a0140500c400f840f1010301c06506546800401e010f011658658031220b40540124541c44240 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 299823893 1250 299822643 299822651
    0x8190908010b0409020f0f0d0f080d0b06070507060e03100510060f020f0604030e150c0a0204061d040219150f0e040902180a0209030312040c060512181906050910 71
    0x141d40704031086c107003290103451700d980812111002c11442043e00001600e801d510008400802108070014a0405042d035005d000d85150201030012500540b4801006500141e00510142c2c0c4105048416a10002d00302c41c030185d00c1d164840120f400907500e000e4a120404401c1c420650000d03145002c4001c80d10040c030700d00f800100ca0a03110240030b00020f0400030b0751002000b40e0b641319280c2410008402041541d070740c00410b1040c0c2d0364400030303804a010754108480043c00705001c50780e5004404a91002000c04da960b58200850880c071081c0c0c0c4400c140220101103903080d0710300723800c00b172000c0b594403060300c00b03ca0b51501514a00403880451f12860600c110b240068035180c44681142c40c0301d800101243d1590700050001c0c0c02a5a1100d03018800440c8501e0091682c6003138074010ba01410720164420b031078000031541c520841c005c0701400e000103004580840c1502d5000000701c078005c0c095034000080819046181012a40145c5a403510f48040c4100c588090151580c1e40c1c50f01d0000300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 299825143 1250 299823893 299823911
    0x10605030103080301060c050a02150306040b06130303050903030415200102040f060c0f021306030b0610140a020c150a120c090501032705010e060c030603061308190908010b04 77
    0x40e0181c1301c14001c002c1003110003c7d40804100080000b1107180303a005006032915100400262117030703041102c0e00d41c4220305144e0020100e080c21400c541001d20140f04280d0541c1c119181034440d40d21407061943c040c801000006a002c100441192008038140d807401d0300c00654510782d002c2c0301000301060380c0ca03910400c010440808a1011982200c00701d04024031094501d05001c280c885100340065003007402500800c158800991100d0240d0f032254441c0c11060b2200c005110040f4508219500460061100e0f15402419403010b022030420610444200c3c5040f4000308080c1080900100e820400100e007818003190407495603500c0f990030140800c503400c100c21005162088034811241415030b07810b456000b00c1c0b0a00c8210003c29020700c0e481064007414584240200003514036802e15000321350100d45080000381c100c0e0b0007944010300800303407510303204a100006441d10b80c0840d42040c040010780007500f10204599403100142e2500c0b50a03514040c2100e00f0b595640210600c11440c02c1044 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 299826393 1250 299825143 299825153
    0xe0d030614120307060e061006090506070b180f031c05042103140907031b030b010e0a0e0d0207031112030d0e0705030f01020405010f08090607121509090506010605030103 75
    0x12050411034080354880d96034000b02c2c0c1103108a20300541814100044111610030004015024a0349800c1012240d03a88640407039507c00d8038094198044401c12400d0040b402e160486604608036400c0c3c802040141154680f83c00f049100e0814560804a00d010380c4001000c0a80610002c8070404d028031b160640d1280103000310b0180481e601007543d5000c0699903c01d0380315441c04502c641c0c01000e2814140c0c40075a0315659840101d0b4a15102c610100c40140860440802c80ba409060740802e6400e002c02550010802450380740050754800020401900030400c402008119402401c80c0600f18140034084206045245002d02d03c441d50503010392100204444001010200000701d0303810903110a0304159107507206a515110340842e8280c1050117500030421194244c0321000c0c1b4050354101921094022110401140c02060008a856000308003109051402120029156559a004031000c0c000c2c0e4005683d01582c0b03441d5002005000c001003400b5010a0030104c0c10740d0300d1030f659 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 299827643 1250 299826393 299826419
    0x6031515020d201203090f0304150302070201020a060906090507092c1507080a1a01090303030207061103090a06050112081905040e040605090606010f090501030c0c0c090e0d0306 78
    0x80041004204100c03001e2040b039070352408001010241c1614142c028004d5280e0403070f0030545450301d850140903c52989040c00204440407039411141e5880c450004040c298000e40006600764194050707021500c00050151041c0700c04548984070019040c0321506000f031a00400e0380110381151b113000d03130350818881d078084003000044507002d03031203030003010254514144940035101c00f01f940805818460404d4006a0b0503110390108401005690310281400700c41014003441640451604a0700748042486500240b040c0c600410000c691070354001e00c00c18841d0b204451103002c85e0800b8010008001030760040758018801c03802d500c07000c00f0540e240d035403061042d4003014122004d03041f00e5401c1e45000f6001d0310001c151a4141c0b0b941d5280c5400c00c100078003000c480c00c403118020400010915805200c000001451a4ae584002030342003100540003080c80324841d50900049818280016281d81018800351100410114803650602444c0345070521028508060500700301c400d000d0f1104581c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 299828893 1250 299827643 299827663
    0x2030d020c0102040e0a0e060a0501050607030807020f10020a030c0206041a1003050109080d0e03190806030c061c1811060a1b1b0603110d0e01150603151502 69
    0x2401a0740d006200305150092041d40d0024000c40440340c100004840320341d10070301c00c038030402c0151507495664040e81e030210b8000740540766008605000da500884c2c030036040c0b02d6200b15180121040760060203651441c1c10940d000016106400191850f0003581c18011100300f4150fa0004005174142591502c101c1c054110404400443c4880040c0303603141d004850400850f0404000c01410440e420403a01c2988502881c01c6541c0c03e040c800d4030910400405c903003141d84051811125040b0035001141d10706809894280c1c1481101d103640216602d00c1c005042040800c0544407011640542c01001c0d40c00d820f124190344044c26160402003100c00050218005048030348035594074240c2d0054aa43c031a803400d048404030814001002c1101520687c0304174604001c42e2040d1941d02d00040b0142d03980401504020481404146c4480803d60041e40040910034004a0f2400a207441103501400c0c0d984100d00003522903103540010310740c00c0d205070080c10030303041030b400d100510b40c6000e503480a483c1c1d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 299830143 1250 299828893 299828917
    0xd050a050d020f0111070f0618110301110403050604260a05040f170a0f050703080705062418040f210f030605090610030b060a020a030206060904030f1b17180f010203 73
    0x1b20704500f00048c1d644400401c01104010400c000314900b41544074005800585020b986003400741a8003801e114181c4041346d074400014031680c0c0e070f00e549218122113601d001c030584503004000c0f03064a09044000c0c18900207681e9480b92200e260040408035408541e00c50043d030004c5000c0c245034600d000c101195a160001c0350043c4001562420b2441d06419a001422120000c500d0504001d0007040307840c028004064a900703c01d03108801c0d02e00318901d1340502d51784004017040e058001c4130790300b00441c3e019016818401c4a18070300d4071400140000c05448450402c00071044100072a0000e04c601320071a1103103020403580d4140004124075800182c04107104105880c0c0710481e092281d0480310705408050000e0b6102c01828802035a00e0300614421070140c0207150008bd9035042030340005105c0c5030943d54501e2524400541602c1c11800d01ca2010584444840302602184025154420b407000640741035030b0707c140361640c2c0005c81c03500a0000d4880c05108549401d04c0e80c0c00000d59034a6011700c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 299831393 1250 299830143 299830163
    0x50f07050f073c050f12010e030702090c0307090e0604020d0608010b10030908190c0f05071406070b0a11070609050d0305010519090b0d050a050d020f011107 69
    0x6030410381c0c60500020708000d114411944040303104860f084081d518a021810034030115900b4076401100d000007168034501c1d698541604000919101c400c5140d86140509064070820300340440703e00790351201c500540d656100040c0d900840c2030184030340d0780c000c01c1d9626050443c20242d80060141601c5e200c0c2600d10390b03c40b004640d66607940d5044500395000000104440e50740c49100c14060200402e0151140900b84100c50f01180240070b0035565030703480000641782c420b0a500754001e0300240d103041803c0103000f20046000a150060262102e40101c1c014000d040c5003a06001417a080c05138250702a5900b488901c001440c1402e42d80d4003e0007850b03021580c051048441500b42c0542c40002d41494105078112052000200c1d50142c118029039080c0881d84e2100c1c24001511582c29205580801903c0200100c041c81e60100b0419140200161a0121142c50f000c0c039000c101c00e42550590001d00c00284100d40401440c056804904001e0044045d05000e550346809200005000c80f508 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 299832643 1250 299831393 299831407
    0x20303070c080a0e090a06030b101809080405060d06080705120c040504021201090305031006030b090c0703050f1801083306191805060315010c02040e0706050d1803050f 74
    0x7030b02625050304409410312080d841c0030780906c0c01034580d601c42554843c9004c00410f224001c2c0d02004819940ca04000d8113424424000c0303180108154201560030500501c00421103a580b803000b00910f554810300420101d080036046420111070354080c5119055154981c803001e00d0105000c1050402200c00141e6a603443c00801d54404a03004840c0311946421403110803d600600034502544400b039050a980c1d448a00c00d8003140c03507040406600003114800590709582440042c94001c2c0700b86003c90510b1070681c0c5032219074104500e034012005030314440ba0000e590003040d00e80c3c0034445d0101c2e01074100c01c09141c200e4508104c14058010f180600c1003841da03465001c01c0302c201c10880174480740c40c10003040008040e8500a1140010303802e104400149625007207007038038058284000f1b000340300049070006459010381e018040b40c106880e5100b8a100801c180032803001030120f62030321036960515221481c110384586842c451405c0c40d80311540080703136010303080d95030a080c103841e80ba5030f0b880 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 299833893 1250 299832643 299832647
    0x30c08013302031b0703030203032205070b0d050a091e021f0e010816050a0507030e0d08030703060e1b030421050403060c0e0f21030313050c01020303070c080a 70
    0x34000400301104222101a0402140c2c000300070a0101103400060f54038800c2907207000e813100036501c00a80181d00c1440484c40401d403110031202c00290500340c401806c1c03c181d40d00750401c680c03548400c040d400080340200c44d1041c00d01505c4d030700030022503041151140940d0b13400d0548096481032600754150044540031511080c20301c41c1c0308184119801801304c04075034014100351948840c01e00043c00500454441003003a4400340441e14103031946810700d03014000841d10f40d0402c1d9001d074200400e40140b607446441d4480d0701c5150500460107a5502d190103030f0302a00b900c50551103041c0c04040b03d0104100e00b00d1003119250b03074203080c03621603a59443d941005881041c448480002d0910440021001c0540000081003264419101401504072445040d607040903030a03041600b141000c0c41008841c90465050140000d80f201d40000c103c206007540d0f803441d041115840c2c5000940c9002c6014030100b04404110724000344000d501d1458803503002440e0000c10080140003080c00f19401d90554 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 299835143 1250 299833893 299833949
    0x14160f0e06030a0207330b0f0409030e01021c02190f080f040503060c0703210213180e030f0403060b0f1003050403110d090308030405010b0a03030f030c030c0801 71
    0x308014880c60322400e00b20101e034000d511a1108407050001011080680d40103945084200801c0940742104528a00141c402801d6038851b0035500103910042a00156101d10031040070314000e554541a442c8600f001a14018030b00740c0c41d1b00c060808806c01020241e000580d004504001000d200c0a1249442c04880d003071100540101f0082c408074007a5500222080580108c9008804869154a404d812458284162040500000c80c0c44441500503000d4101000f60161016001450800c05130108890550301c2c2d00003e0207000e0120306003011601c2030050020030b100d4003001c0d51500608640346400d901c02c51000901854885107070301c8035543c980190022a4001400b14001c281000000170300404080307030100c000c1114400300155175180003603d9103c3c40c969481fa25201421600c3d14003c0350802407080740d41e90340b00d440c4c0203056100c2000c1c87c8011882600d940b64412602500039003646c10581d100c0701054500001125400d91151009044400c00e0021491212070f09400700c0400c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 299836393 1250 299835143 299835167
    0xc02071a0f0d060b0304051b09040b07120e010605090c03010602030a0c05030f03100612060506030109090203011803020c0126010311010513060905030717031b070f090c0314160f 78
    0x142d4540b000001340a400c4500071480b8a01c90000c0d101030f400d01e801410300200300440c805404ca616080020700003a294001e007a001103050901e1007094082140d8007013038840006a040203030751124810441414001e0300380707401a0b90710f0101404c2d5030400600a6690250580d01e108100c1c2d1044014280f0405104658910b8080f410301580d80c600400d034a86600300b40d00c12100054107126503072603030442c076209040a54400600281c9503901c1d003d0f03080f014008900342a030b0706560765480c00c036594840300c0d074001d02e45110760003070f000420b0108000345c611120361159483c186079841210450012103444079041d6a80310440040344904080102c0c4d8034011024840741d40c000300310012440c660040c81640807154100c0c200c48900e5111071880500c00e4120458103100c0d801800f401c0301012250b80615110100542103e4540d0b60354140981c280c45141d02010940765543c1110021551601a5070050901100c013041035080c042210101180490300103410800400c0b00940468400c0c2c00d0303d090 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 299837643 1250 299836393 299836417
    0x14040204241413090b0403120608010e070e0f04031707120f0504060c0504060819150b03060301050a0e0d121820010e3109060905010c02071a0f 63
    0x105a8480198800d820315900c01d0b18843c152503014000e040741540501080c0c40e42c42120712456840381e5901f620700c000041c610340e8009885810115031200240700c0c1000c080210401460701d2403924400d005400e5015000100c5981c80101f0040829041500703401d407031031041c0c0f01780451307035074400b040315030150080304414803c2c05e0000f41082e158050704403c0c042c1c1e014110400c01e8441500e030070758a0b4480c51185801182621380002c0708001d17242840c1028103402000800e29003c110022403012000c0d03040f000c1141c2012003440300c0d0741001d04c074260b80088024020000901a2170b040c55680014100140401401040c410681a040c0d08008202b0401030304406901203149811305607480d075881c403000040c142d1700e00d6458541c402d41c0001d42844001e4540b0015410050904101180aa502e89038481440c117401e46030033554411140703014000e6030005070004081ca032590075182c0144002d811035126007000d12420380300307070300050380c400700c0130151551110340c0d030039461243c080c000e42e090b4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 299838893 1250 299837643 299837711
    0xc0a08060f0901150801080607022e02070f0606050d020114130e1e090d080103150e06040f0516140f0f030a12080705160b070203090a080c010e030114040204 69
    0x40019002c524004c44100b5612601d500c1d03a01c402c0400d03a6414220365460040e0301c510102c0c03001081a0441c041034039918445800142d88000e180e03400d90344120030071100c0200c00003c40b01800360700c0c070074800600800c0312441c01040c16600024040c014000d4017400d9140000b4500650010a032039003401000c049144000525011803041c00c00bc080d0012401001d02441c00281410008209240790300001d80b070384035403a401c50316045100300d290213100701c0d099960b0404003031f680410006548914401c1d082d243e2045441d282c6a8240711425a0809201002e00800c2c00002c0308040340c01c080c960141c5901c49104c4d00040050300300103848942030317054040c407065503084c0240554015181c040c0d540720160561281042120a032180201d408213890341c900194001030040140d05401440902c11030741400840c8001520690040d4014142540080c070149200d50304000b907400314ac03d0403402004902d21100c4404440000100003c1c0f0940d43c4040010760030000f281406940c801705501c00d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 299840143 1250 299838893 299838899
    0x709020d0b1009060e0a030b011205070e0c040f09051e060a0302040e01020a0f0f0f050d2c0c01030b0618030a1205030601080c19030e070b0705030d050f0c0a08060f0901 74
    0x1901d0f180090141c2d070001144003400343c3c500d0400b00300716003c490788440c0c0d61149070300c2c0c58060114010201c0044500c0e01603102c00103040c0c0c2c0b103c518180520f07400107030700350360380d2406000b14085489075010344406070420f0108201c8444d0510035107a0510300e110810115510400056043e06c59504001e6020345003543c0801002015030241028268a44415020104210b01654152900c1c452080000c851055508410303214401814600040403004a075640b40000100c1d1b01d649a00940c4400c00c080d4507062541400c10044441003100a0030704009031591600810840d1203a00b02c612803014201c410034080781c404006044503035400c03d18902c00303840c2d42c0d000184550320a441a42c00604564003190600c0d8240d01154214483ca410003401c01c0c1189400b60058031038140d140300b042c06560400260120031340010301d00b0b0b510031000b540e61800b41130b000b0011a000a13000104c61840901048510302e0380c0801c07a02c0312402e40c107003000c107540c88400042c01c4854a070320b4550441d2a1070000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 299841393 1250 299840143 299840147
    0x110f010c020303010927080d06090908072f0f030304090903050301030c06210b190f08011404032718050901200306010c0507080105072106080709020d0b10 68
    0x1c1c50580741a100705104a059404034441c082030821441d040c01b661a000c4000043c085200424004c600700782e000ca03410b0340d0b0f034400703200b00c82c40701d80107480309400012a04200301d90303021007045444ca084118518038524803400d20b10802c40c00c80c0c0c2d07401482103105d009119681002500e0080c2090541070140d0300f03842c50001d00319002032000312040c2c00c6041000c074180303006041d0f030048603607011a10034075111003001c1d000c00303417410303d030103507009800c40700348103c480e1440d200c0c00d0181100c06941d04c1510300d0704000a00b11090f114040b0740c2c1042c00410f02000a41c0000c1c00c1864424580030106010006200f14800f06015800300d8041d450642c0440ca551082d07404c8107100b458503900800c010382c08010009a481c840c2207581c5441c02041000508660140007441004c1703001c0d408941e03080d40c59240550850b0350990300800403401c0c040c0314030410940046c1d20a205204402c050000d586400c80343c0e070303582c840c0d8010028000d401080c2200300c510315920450306040020200d039801c00400d040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 299842643 1250 299841393 299841397
    0x2d0f07120c060203040602031206060910020d170c03010303140d0f14131104150b0f04081e06011a0702030a0c0501031a0603010e0a020f28030912110f010c0203 70
    0x1101d144100c8100000e2403030010055808440c07883d00a10703d00168030346683c0d03043c000200400c1e4440000c0c0152044d54450798441d070b440d8000741d00104422115401c0c054418800246c050307000f403840b00304000f16290300310f0503079044031b5040c2051105480c40c031590340050301411404004507840c040781c005d1905220781201080c007103100011010741c1c543c407001c0b482c0491401400303049030200328041040f6092540c4040004900383e0320407803031151590003911143c1d01180c40c01d512000045024066200184002c480311141850482c2c003802140b4415500d0755030502c1240134580c0050070340300380001c000d82202c501d240d000341681d0f0001142d19042c041402c0c0c900940340028a41840090a0074000e07100d589014002020a030031a072806540b91003654000b440101e04540902052100726140300141a00e821124011411074403c4543c0000540240c451041054100080900810480780c004a0f403580d0074600404080c007801c80181c9440e1406505814540c079107c0701c540425030102c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 299843893 1250 299842643 299842679
    0x608150f0703020901081b0c070b0d110a1b0606050604030f0309411206180a0c0303110c03070b0c07050409050309101704110108092d0f07 61
    0x40c1140c80da864001045080703000f082d199602240304030010608142152089801e040c0304613841c5841c01103050102c1c1e0400105078007050886030041401ca0524034140910002da4001030b420301e043c0440500000c2165104041d5080b400d0003c22603601800b0a03a00917102806003e4400c0c0e90316941c5c0d19010310302006032501940003138071902c40850304a01c052401d07a841c8001c403003203c09042d04481e103000700400244040c6002c020307000300118180c4400340041100c2c5041e4015014916180f17039580f060b109880c1192005420843c2d004000a8400c02e80c442030f00e8051410711b0000345080c0c0107500d00000c595203560701d032044650008080d040e850041400074000300540b81d03266598001d0200b92003078004002d00d6600140a0720150381011902182c03541642e103410750050841c024040000a015501529246440900c0e9600d030358118501d2500684610000c111001c000420307048180141c00408014002580b44552015001c07c03062180d004c00209843e121540e4070303150703d41c11010381 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 299845143 1250 299843893 299843911
    0x13081204050d030c020606220509030403121407080d1d010f1104080d110a0c08010501140904020901060f18080604120801270e0604060b0a090b0303090d030201060815 73
    0xb81c80c06089520a0040501900550300249820303101c16003084803038021118880150b65107005202000d80490042c01c1c069a00320020b155074a0840c2800e25540301600e90b000f0910031458005180c1c0c0103148101d031141600302d40345940f96003503900160090001602c0000448800c0301c0390404038441940301c40400480d010041000f4948201ca040550240d0b00c01c1c504550003104441ea042c1e40181154038881003200c1c140d41000c000c6640c1d400c45c003805500000e155a54500052088100340b550542d1070803401c442138600d500e840d90020b00d0a40d4140111410020500100d58900d80100c804031105114009802141526601d4043e915101110117a03013180303040e0017648032140140d54550581d101c00c802010080f440c101c02d500c807800692044000d10b955580a10b10031081882080d00a600c11003010035031070751200c200205400d035500200102880d200010005a4001048a4240d0404d480d41040b400d00c500742640149030383ea2040c6401d0207000e8108440c149103481c00c520810401c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 299846393 1250 299845143 299845153
    0x403080921070b07090807060203120114030307030c0816060902041103060102060403030e101b0f02030406020c01030504110303040e0103050f0c0a050111010f02270d03080606031308120405 83
    0xc0190400106035109041ca8501d0030070801e40400d00c4644007130303848103140c1044540c1c01d5a40240c0c1e4030709215a84050010b0b000400c00e034040fa140c5414090052810901290200c80010002a1a03100c0d00100400748525055020300b044000b600f9906401800341610981c00321038100107020340300001003244078a03c1c001e004c1d0100d02410081d2402803034180d0040c00d00b035803266001d40c000c102c28090150300784504000d58203070b8071150052072145411202c080381440400035001d8240560303400d44805540060000b070003d25800030b23158001d03120901c0d01241c10380350341c00c00070340d000214a80d0302e13010301001401281d1a8051007105040713a00c0780c07007203840c6040c18030301090311031020b403d40541c44015480c0401140d0720aa2a801c0c032071170000c0000591041c043c0d000707000c0f40d010080c0b011201c001d1946104112a00103418049018240c90181892070243d070018107046008090f00d06c603020101c0810300d03820103400e921a03d04c1e80f20758003607070740d861501c4002c0c43c2403400c54007112a8422 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 299847643 1250 299846393 299846413
    0x110909011b121401030b0105090a060e04140d02070503030f13080a030f1b08040909050c03010c0206060a0503030705060601050304141002090a080d02070506090d0c0f08010c050a1d040b040504030809 87
    0x380c883c046040340c0c1c01c0403072911642d003403d040128840e00a00400b240503100d0201080c81e140742082607000b18401d601d07441c4045900210541001080082d0b0710548d0031041d4108920f480110840d40c0000c00c0c02c02e040d6541d00d419590b60300740709071030700000600d105004100b001c05402c083d040d01c10914649803070a803080c11610107000d8202c8500010040ba00070300003005649603d410180545110341c00361413001a910011a086400465003800164408400d10406003020525a005480c080d0702561a14034140c64269a440c006080c00c0c1c10030070000009810302001d2000c0480130b04400302138481d030355403c40542d0080d40046054600c1500101000547d046c4c00003002c0340011319540183c03a815180400b0041c0daa0001128543c05c05802155040001d00c1c10f0080c002800c201042c50040504018040d801c54000e8140e04003480000c005061030590040e24010006003110300098080719450b022502400c600c01110707820900b800184070400d80c01000c203e01c0f4810040403180c0c5001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 299848893 1250 299847643 299847671
    0x14030406240303120b040b120106050108090f0714010c0c09051b070b0a05040c05040204030b1602031201170109080d1b03180809030703050604050a1e110909011b12 72
    0x280e071100401103524000000b11300c189070381143c900f406005200050f01c80c50680840c1c8404c0b0647c0307407032440b6551070342d081c4899a00701406079000300e0300304002c1c5080c1200200269591589018210b042201c101403072120768030808101881681c88005000b01e1a40c2d41308040140005880101c49004190403d00a42403c030041e10749a50f046046010b80e501c480d100007006290280c0706171182888001d010519480b2400100000c502c1807008081a1a0030f80000d0368041c2503007800d0b0b08540003000228084072411201a066540704030009507031500c076803060350050240c0d080c0100100c03804240c64141141c541c0c4040700d004420680c2d40724038007140004808480c04045010381d00000d80600340007060000c4003a040b4804041e08031383c401d94a9444141c600b190403039080710640c3c401400c400070082c00a000356408603203a440706c0c26200c8640c4d035041250780713102191f6002e504280001a804c5009403c0a61420ba07801c1c40d41d0698601004014030202c08812149429802c0003090382c0495 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 299850143 1250 299848893 299848961
    0x13110c060c09060307120b03010c022109060a121b0f1107081c02010b120a02120c030705281e0602121e0409020f07020a0b0c0c0105030714030406 64
    0x4500920013851640d0f80c0700300386d81401c0c400e218003004554600201c1c0c0700762024400c0c80c004403250b400034080381d104801d003c400070311454800b62201c00e080c00009256182d000c15500003800504101c140700348a454241c00810150324010003810607803c04a82c0d003500044003059541442c1c3e203842807110b4920307031695500b40714858003e1562091040c0507280e00d01e038001402c1c49405100100b00c0414420010b010f0b140c0d00242000391340c00c4400d6a02c00c40c40d1024032a4074602d00c000160459142400003e602c6400502caa540912040c0b01600000d0702703869401980e2091001210404948a900640c52200c008080d0040440c000c6000304400f800019a600f041409810036443d00d9104120711030540c450070f00340c40c2d000c80c044c4000b15482241d400a8140948000b6455450311040e004000300d140486d444900f403508100008568000702042c0b030840e609007824841c1d540d40310001c084850382c0003000507a5a1900200c240400c20007540c0001c5010312401c1c2040c4640150058100020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 299851393 1250 299850143 299850157
    0x1003020a050d0b012c0103050705030115030b06060706060b0d0e0607030902030c0f060f04080303060102070603060501020d27180606030b1f030f112110120213110c060c 74
    0x83c41c480030040203400c0c070b1201400d80400c2503020f0504000795107078101440d548280c2046410780c02402003444181402d101c0e0203100001c0c04441d003c00da249d4ac0740c130001c0001c040c0000d40100300004050080c1b101503040f91b4020105100a60303524128a4401d0001380802c08034401c290180d180803c4401340711340200c0001d00d4000340a0001140790f0401c102c030b20a04e0001907078100d08240300d00803c080f5084c000d04000e001c680051941e030700d0002c00090902400d9000081498a4050709001c00d0b42c0c009200348101c40241018620a081810030b1040200f80d030004403002e103170032480032034070350401d60041801007100e0f20140522511000141c041e5031002c150250400e0441c405000c1c0400341040070300500320182000102c4003124080001503c0e01c404c004480410006001407a800c0c01140340036a41244460b180f81e80d0a1500c0c16058a102c08e214070009070340b440300e00e0020340d590712145404503280c40d4410010a030034403c007007549801c05074641110f4020240092650142c5504813005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 299852643 1250 299851393 299851403
    0x71407050606041508121c06030f0519150b0d020303180103060806090a080703090e070f1808030a030207020a0f12050f030a21150f0f0501020f0c0103020702060708031003020a050d 79
    0x204202001d86c0710703110782168031140c981c0601c0c1707003210340c044440d0310500006c2d6003d000c450000007c035051861a201050146000c1c4928250011000c902c494081100315a5124004103070f107505100000c0c10309d00c0d4410040d626010010300c0c0c141c280701484a1580c03031542070301c1c140841c50f030340c40c040d5445050489682495800045080000440b44401040c0d264401d06103000d142d620349207030145900d4200e51090100d64219002d8442580001c804c408443e120302c004802d9604111107a80ca900420260109150300468514119681d001441c1d020742140008040074035a949180006496452810303241c900a207604001401c01c0441140e8450955803900e00c1d83e80c0768451a100300c410940038050300541d0350201e07600c68590891a070380080c40c20184070190b5a080c100390b1901071030300d40c0c0180c1c10355004141c07071441c500b00803484d4103c1d0135090a0044e15805d1500104041d84100e0500a0410070b00008000c003000b01c1010010590340283c40c80e0f42c10503295010300034000105030b4058a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 299853893 1250 299852643 299852653
    0x3060602070302061e070b0a050a14101703120907060e01090b042603031f0918060f0b090a151203051206030c03011a1f090905071407050606041508 65
    0x1816144813a250a070071281741003014034166858903a081c841d9425100d0001c3d55031642c0500c502d03940c10b8025a007016000d05e610012a040912041010f07064a22440032558442c08036070542e42024026507800f0307102c0108a006a04c0c0c048115030b101d8849005543c04034654060b810b0495200300c41c1603055070a08501e00385400c0c201041c207105150035038401550a40303c07504051200c80280065800741007040c1c102c611118021007045001400341c0c00021009141042d000307400900702d03138410a0b4a41103240040c6031405818880d001c0c0060542c0c407a001501c050500c4042c2200b9070004a4403655040b0003d140354440380c4056813198901c2e0042c1c00074005101c000c0b032100c15107004036007188008040307070b04440c0207002007420b4455904c020819111151728041076801c0c003003080313003030301104101c0c1d440c101e5002c0d4006001220140a08140b8681d5800010035260040ba602e40c41025000f003629150341aa1402954982048030784500480c2002010100c0c5204080c1c1e10040d24041c00c003400c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 299855143 1250 299853893 299853907
    0x6081c08070507051603030203121b0d02031f150801061727341a1303020d0b070f1805010302070302030d1506170708130f0b090d0306060207030206 65
    0x1c40c80c1e000703800b050303c9030f0144881100749a840040102c0095100e80c025580b9401c050ac1c807a503170014003c200403071580e6506100442c851070300701100d20f500080c040051b201c3d21403803c0d82007400144480500b20762914200803401042510914210030f80b40d0351101d28980c1c84480407030b01c0400c01005442c98a0300c45022604100f11801d4400400301c040b4441c00100c8141d50711149450641d020920207074008080f4104c21041c0e100600181940a01b4800806841c020024010100c4c1c8c03401480c0d03c01011a2010a4074164081c80c00219001409203100c01c9a609042c07881040c15a40707180030680c1261048240ca0146600e0300b0008000c03200b510300640f034a4010750103035100b90130171400c50100700f10380035520105201e40c86d00c084429020150703603070500f0b501a200200012135181b018001c5020404981ea01c1101e00e50702c081407002840c864202440c1848102c1101040103050050740780400c02a5040010b14101d94241e80c0d809000030741d5214000d0780ca5941601000c1e4010303e04000704 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 299856393 1250 299855143 299855147
    0xf02010c03050c1203100608090705090613050c0a0e0f0d060e0708010e0c0a290a0e180a0c1b0611070f030305010f050103020f03070807051c06081c0807 67
    0x100c0c554a01a06207640f41c18941c202060130140000f100c203e00341004000e2000343c40d00500c9010183c2505d04003003903141490302d14550b80d400c0e240300d0944244181c80004c1c055407101c22038100381a0300714409210700e081084540301e4603080f1004440004000d4002c80740b0900e02130961000c41e25014001c0200b807065031301d80707a01030441250380024a120380310f80003030342076024480c0340b0040030710307602034102900c68000b08000c041240e402a0301604540c104c05403407001d9401c07144c0e403200d950560030ba651014504141c0c3e103480001800d55004a00c41d001e280e048800020130b5100d81001c400400544515510640f40740c2111103254220650f0784496070001340090b489291118444401305040015665858090320343d43c8904030b00084d211401000f400b01451032041c040d02090809506140c003400ca41c2c480750200800c40000c025080c00406e241034000d00446a0440321454911603070441c021211016254602ca45011480303a1120f0140455100d084480c640d00300e0b50b00c205042d281c030b0341d00f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 299857643 1250 299856393 299856407
    0x4050115060e2e030f0213080303041709100f0309080a051306030c0e0103091e03020d0e1c0b07030b1201090b0603030906191707090510030b01080105041e060609210f0201 75
    0x815617580d03a080000d020421811380851004015690003140c2d207143c1807510584c0d03811400c414003882c1e5801d01078521540d50340342e604484584246001c01501c620020100d0180003a0500603045940009461005a60040081c00c05000a41c3c07510000e6503124401c50480b50041d0615000507a005408155517110b50480c00456000f018102c80c0f40002c0a190b010241d404030301140560b004c2d11000d100d140e081282c43d0441c0c00d003156055049507000b0380c1410303070305600b09006010000b403200081c244c6020740d00c9096014805005810307800d004a810714005d1014000a59640f01e5080021b60285800821200408005803220342415507540c2c0568001b0b80c9058240309000300e101801c2d05100507400c2440c07141e00d00d6550b030240b0303619140c10300950b440c10013075034810941808514405a604800d8150458000f582d0000e40710581c0c180409c0035100f0268003481d024245500000c60b150700c080318100f41d45600c0040d0240040900d07540300c1038013203244002c00010380010b46001540c09050303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 299858893 1250 299857643 299857661
    0xe0c09061908060f070807030506220e07080304181a040510030b04030201020307092c07020c0607060207110904050703061e020c160602010603031704050115060e2e03 73
    0x404481802d8862000a08100d000c8035000900ea000340304101d0f41c10351060f5040d4020409007010081d504203c0d01180300401a01101b0080d4036106503112032100e1a54130450500041e0410b0703c078959182e619881d00d079071143c4603e80e845062416a05540b402910920410b032003255903207110800c840050101a18004202903404550300e500040030403200145c0ba84124484d50005030b4170303d0255800740c188041a0048000c5400c2c3d02c440c1c0000c1e141580b0784007400c5401c1c407812085565041340803803510388c0100c08150001c1000c1194000c10007107401410030f492041488004040d441c200b480290039040b54060250fa2040108002085440d401602003944500c040220000c200540b40140d900c8250100a43d5014483c4005142040c61f020000b50000d4030080c8481440e51300c004003100841700c0c0d890120407100000c00e041003825804900041d038800381a81c0c40c01e41d03a4501800d9042840200c030b02800096100000c5d680401d2400a501c030001207a001070701d648020203d000b801004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 299860143 1250 299858893 299858929
    0x140a05090d0c030519021804080a08091606180b0306031c03020d020c03090109080d09030b0c07020a03080307080703020a140304030c0203060c04090f14010515041a0304060e0c0906 79
    0x2d2008404104240f080034441110910350480003040c510510076944403420343c100c00c0d01206020b00001900101c04c59440e144546400f2070a0380311002c1e0503013410402504c000c25034801c000000b4403150000f02c7d0009020320004401c05065640e002c0c02284c6c0f00880e50305074181c00000d031020300301c00000d08496215120b031500506180d1280c00361012a40140210744507503001090400e455a481000000a0852034000c1d00041c64031020141c03650001d40001030541200034002440e0449920945080c19002003150803c1c41c1d03207090210160b401034400000152030310000424442c082d00817100458019602c0341801c1420044508260700b01500860800500400410150740c3c108001d03402850010358050b03132035140040340c9003200c40042c01c000c185420000705140106026040d40d04407002515100c1d1440d120842c075500c64400d540225025400798940c120901511402440c41144283d404002e15800002c00c0c50303407000d20614099000c646000019090b08180300380702c100c12244 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 299861393 1250 299860143 299860163
    0x50909030913020f03011716060503061c020d06090b090a03020a03050d0b0307060306090c1e0e0105070f05010b09090604240f09200613140a0302190501140a05090d 72
    0x28450150650082e0f000301c8402802d00c5180400c0e42042c407400da0500704800d108c1a0340b40c688140981030b40002000544900500306080d084441344138822010154020041c1200e000307070340380c09401002852810b5420000d024001802103000041000c081070b09074005142010465034111003e82c0b122940e60b1601713450f6103505021340c50401120001d8030b411b0b2004101241041403850071102d0b070b0819281004442c001c0c001802c131a44040c5001c403819854103007040640e903401a200c40c800c0450040c14401500306403c14414194449114940c08461907442031329004e040c180e4680e425100030709005400d01c084880f11141d10044070036081c5500010907846145002d4004072a641c80040c1c1d42204006843c140500c030402904040060031540c60707051411420295101d0745403809060300303040c5080764062580d42d40e154180011680144048a14285480c2d401d00da10b619104c0e140c04904000701608409800c41c00b66074030b803440c5035200f904020079141003041240c6801000d881e44604 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 299862643 1250 299861393 299861407
    0x80d0f14040f051204050105180d0c1502070603140a0b030c030f0102041a2106040b0406090c031a0d02010c06110c0604110907050304080d110307031505090903091302 73
    0x6a460024440d0b80602c0c466100400b040c01c0060808180000c0c1102802c0c081000380b05a03a000000d0b5680900c0140802000340e0720103000c40c04484413a00003606860014000103403e40b00d0041090001d100d42d400d49000b151354002c15400e659080c0041801e01c004035000854071413032540301080340c103002011140015441808030781403190325410390f0850394001030248a55802806412490044130345210714005100d4004048400054a54142210b00c81c001c16070031b41d1580c000c40701014009008000b50ba969030240d41c0207103441d450303480120381080c13001c64510300f0216201041000290410004e0320340ea60044642500e15030088440725610110517500f15900e8001e451a05c000f24001c010a00301410000c1001011001681c0314081c20000c0049e055881400d50350425800b030cc0864a1325140110a000b80c103403401045807a20012080140381581a00700c41400484800d003200690744175400d000c803000d0221071408650340100b000070b0281c00c01907601c007603034265610010f06000c6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 299863893 1250 299862643 299862671
    0x22103180a1b0e090d09170c04150e13021507020301020c01050f0702070f06121d0604230703021e010504080a0b01030605070518010f0507020904060501091404080d0f 73
    0x1000300990010030301000c07401c0c4149090050f100c2d8020440c2d000800403441882d8004066420a0041d45025000c14403010180e40040081e00520b0308020418009404e01c0c0c06c0000c5042c01707c1c403c40e001e0008140c08100e6546440520b02d20190300500800044401242018002e6000e504100e82565081195441e050001e11071035000d844508105807050600e40c200070714021240c1c20000002d190041c041042d00c0d007003c10480594401d41000c80c0f0300300300346003280d402c80120a4103e031030b0040000300010020b51a408034001400c5044110050111071501542c522190100a4100e803450f6041405864914000c2507083c80516203c4c2c600354036035040600741a00c4500450b08000c269005108003c80390003007940c880b40794074006061000c8040340d103a400811030811414041c00b5a0701150141c030034801c84003603580290850149060500c0c201008010901c20301040c58640840020340440302e0b4907044c011030700142028288195180d18900614842180c031900c039503108411141d401c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 299865143 1250 299863893 299863913
    0x60906010e27040807021203121605161110020f0a0206090d0f05100b1c021002030d02270d02090403030b03011e0504030306050108010f1214030316022103180a 70
    0x24813520003140c8407900ca00c10f02407414555035030001070b50401e000910507994048501644100c03a0f82d1200e520503084007081d11984135000c0d07210910380d20340c07205805129040008000800701603070070380040084010202d88850980140c802a03821050801e00035207454000341c00803200c0103000c1c03041441030340e40e030100c0d00f4441c41e021502d5420601d80c010071f402c9070340b0680100c048103480e00b132a2685c9111548004404c1c18100a01c42c04207016411701151003042a40c80085070352408550710004d0350740303d501815800d1418ae0b040426444086c041d41003004014001540c00703415081c407a1601e46d400d4010301a9422002d825650398000010b1480c00c40300b10442104060400182c1414141001000d8459980001c0d05101900004000341c00aa0794040115544d802c80050031040600d82481c58070486030a488a80c4004814809111600d6443d4403400200350211441e01070041144414a045048030b240461000e200043c80000a04940d00240c8507135800e681201400b550b64580c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 299866393 1250 299865143 299865151
    0x91002060a0c05070b01030201210501080a050c10080f130f0602040e06030111190e0307030302030405190e190e0a03030203060310060506071b15020114060906010e27 73
    0x5900503401e1288800c61842001c072074a2982c54040d191800035140c1d8002028184030090400808100f0303248070a02c076031805558031210410a10955a441c100c4035038440c002407080c5c6040c0100440c0c101181341c110011b41e007d4180d80c4420030155181000c0501c4610020100d008070b00ca0040300078002203000e850420068440c0000603184d5003030080d08071b500f5100901c10f90090b803411100740c800c8101801940d0b1039007005044e410340d40c0c1d008081190001c805d81034007038041c414480040b042540100140068070300c1a9914440f5008444513180c25281a10840004000c0140031071a50520314040c0c035070210328008040303030300240402260310b8a40a52010f400107507021061020b00e15041c000d01c5604000030b40240502420200065014424100010030102c01d4810204069a41500020007010124a000d59803503c500740a406002a1512082d101150074001001071900d03202e114080c0c0410381d20000b91175060380500007250304040b030403d80c081c010041007a46043c002c0250b845 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 299867643 1250 299866393 299866397
    0x16030201060f0501021609020a03020f03180d0507030c030804080f0a0306030201141c1505030f011b1b0b0411060f0d061d0a02090f131b1809110910 65
    0x1824600660368422502c103030442411034010b410070310145441c0f030258a041e11090400141c0d80c10740030f2000e41c0203101d0800e6030100900c010040182c450f081c1c441c02c418940b01d513020b80341540249882114641b061201c004d01080329440843c0105e807181c10400c1d070040c880c1d29481e143ca03212071810740541c0c20514a07200001d8480c502030085580c41540d841249400101d00c504000748041d000240c18072007440400704070742d01c0c02c20300d4110103080514001401c01409035040c20075000c070b1030381c0623108c1000c0030040a04a0116144003611800b03030403c4030304002c184c0c124a02c085a0b00c44000c01c40c0904140d034940c2502603d205a030751031500401030020448040f55032512540034203804c0e195298050803c00c21100c030336000c120340d002a140d5102c11007000040e59040c00f000050000c242c0340504a80080c0c50515800110503141c2c840d1020001e034001142000c00d03044011103402031006c14480d000d54078600d041202085503002212200010040340307041961003804541124003000034440 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 299868893 1250 299867643 299867651
    0x4030813020a26010e072d0f1403031e0c010914070f1401080612031e030a0b0f03190c051323011508040501090b04110315090a020d03020316030201 65
    0x4424101c481c3c0041100c0480b40080c01010034000006444c0e28540c0300d459200355000d1311180c582c040b00501500265040300c0d03052050740e2218420b88000c1003031b002d05c40c0b0110124000401d40e14000050780e030800c2080ea0102e019502041c80e40031039400940c505e080b6907481c1d00c104400100c1c000c00d01c4201e03402d1000201003061805528040206007039000030381e204040c001d614030503607025011540c803920640c1c140d44120380b04044140b45100300c079681c03080c842444a00b0000041818000d501950001d101130040c04003610270482c40d249001c20f043e600d079116a66880f8800b0490142e0021a8041c0e80c040205076074a501160604078030000e841006a41d9100412070207a2014250107007091481c500c0440e9070500308000940185849031000340201640043c081190135040070f02201c2d40301500810a08141c60014841c039084220903100f0302659503c0c40454000309640c5111743c401c4002001c01007001d80900026409125041c1c4c118001008030014100322031070340c1c0c5c608900c00c0e80006 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 299870143 1250 299868893 299868929
    0x606020309030d0815062107090303031b0804062c01050a050907030b01090225030c030e04090b040f14030c060f07080402100e010e0409110405010905010e04030813020a 74
    0x43c200240b20410805000380001840301c0000aa01e0345500d12005465940d541ca1060501950500005142034507561441040100311640309980004030b80c0304c0d49084c00480c42500c50000c0003070103e41c0c000006001c400018010600a8010340504502c0c00251311221030b100c0e811a4010703203070840c0510340ea9120814404203c5451084945c8007507004041d24800d420b55136050b841c100181700d2200001e40200300701c541020408110706201c280610b0040c0607521910340540009102001079020942007584402035003030602031038001c140d220210100590301d079980d81803100c0c05000107840781c4500a400303912803e4100004e180b007104610042909160080b90040740741c90090071502001415400c0c0310040e2204001603613014000c0c00d0103c1c0f0070b6040310040722000c80c82260f481e4818200010306081c00384154100984070303008c2c1c6050250740e0701c41d2801000e40e02e0a1007407201d6841c002c030000d004644244402034103c0107241402d02489403070740004e0140c0e60035400bc0400250184e60301 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 299871393 1250 299870143 299870149
    0x31b081201080708060a020c2d070b16080f0c03120906060102030f0a0f11060c0408010f050103051e03040f09020301050102010c181a070b0405060f0a0204150509040b040606020309 79
    0x4a0042c09044003c0003000e0404c07514a403101d00143c1003050454001c00d8122440340103020341c014903526800e18204200f500710802c070380d048003801450114010204c004c199080c601c011921120300c20752601000c510660b90320107840c0d001d6810701c0c027050020710614003a50424001004848410211100203083c055103a6081c68000781909041d980100001c41d14003a19805542c00070b451400c146008080d80007080d40d80761900e207048909d41c01081e0800c1088500c2c003002d00261081c9800800403401d10082404c122642800003401316070081e900350441e011002a4161a10f0100d41680d041650b11041d00c407074a00f1a42044a02c0303900800140040c0d6424458040f040135545005140c480f0100100d080e41c500c94003440750810000201e00703501d1b080b20000c450f80158040c2d2000003926180c2400c50300d911060b6041340f0b06207a9100410700e60350590007580c2c20703119408001c0851448105d000c0c2c800d40e0007443c0c0660020340700c400ea224641e4491040d50300902981d00035680d070303104034820 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 299872643 1250 299871393 299871427
    0x3030f05130b0a2604030207061d090a0203090d0207031a041505010909020f01020d1707021509030408011815020a0903060e0709110c030403060b041104060f08010b070b060409031b08 80
    0x405044001302ea420030002c2580015000226409070800301c480900131486042041d00303d2400300c2c2c0007409c0e001071000d9030f5080c2c0c0c0118481c844c40d4080c0c034881d9000b82d0040383c540080f403102400620300c00401a4010740300f090400e400c1885900da40401c81104941107040d144260710690a440d074509251040d42042850b0302d074001402d00c041c00d081010302201a16202c0660882500c0894810016000c1e82c02000b0007100c0680300301d8902c2d100c0c03604500e440c2c2c3d01c3e44035000340c80065003880c0320280c0322000351805008e5143c0c0b01a03640202102e03034441500070340040c00e140303080106010340000414903038072814010751a03a2020785003260410000c181540e1101d0000d0401007807c000090401e42c011056500390b81e4000c3c03010803410a44070005010f0010005a840500b1000500044443d001603941c4400511501c4401030307070781e035032103d100c2a010326000542243c0e24080000d140349041c0d4030015109100703007050325280c03448a0002c6518515110701300c1e01d61000050314043e5800c034003c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 299873893 1250 299872643 299872697
    0xa0507050307241d03070e0a0605040522050703021003020304050607020c0d0818060f19020c010e041515030c0801080d020c100c050105040305071b03030f05130b0a 72
    0x1015a250840c43c00080800d80785072840da508000038110311101c80c0f01541805a800900103048a40e100d803aa090324528410540b0001d06103498203400185600302806420b00c81c04980342d507618001203182d0080e40701d010701c480032619801422000b000503510303603410340100e5086503401a2203103410301d0203c1c03403d1000fa0001c800d540c401d010403059962124054180e41d07502c25146d80d00c90610f40e040400d1032112060480e40002d020680b507138203450f82005030640746011a4006001a80a035040e40c5903108802418005130f01112486441d00f040d0300300c0c1041c02075004600c01299500e88200e001005102c210300c000070b0b00c4403800c0003144e0340046917502401c5003802602040d10500d00203941d070b85c440851240616140500140400d0051420711103c5070808020f0145282c2031030006e00a5100d40d40403248220a440d00b240c070304500317550b201c06407035064444030107061081307a054446030002070340c001c0c1b080007150340410000c20420141c04980502d464090110403450f201c14104000d5403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 299875143 1250 299873893 299873909
    0x30a0f081302032a04020d1b0e06070b06011b05011b05031e0c070807060c0f0519030f022a0607020a11010e0a05030a0c030201092c15030a0507050307 66
    0xe00900050307a804140e0b00e0304a060301300d9401d060a50181c4224108101d004003981c031900c04542840440000e40002000d11810302c519403408a40c001c0544801004020198000f04240101c0c0e00042c1d1603e4025000001410704103880b4000d6030100c0500d0561030b00c21a41651500f030b1001c0b010068050500001c03403241452401e515181a45190050100810b10031a02c0c030000410198080c1034100c486a9400902d1541ea4000301e0501201400040c0d2102c8000745c0c141d10b40c90405842842618400c828910040c1000803580d030f42140035003c18502c0707400c016130070413074030061031481410b1b180e1400d424203220000c5900302c025541031800044c4528159040001c0f9400000c024210710055004d01742062018090901c000c640c04c0784d11508003d8041c420010500c05000803c0e4194085074400d90765125665120344140d03e2007480a40c0c40f600d600092040c0a40d0700b00c180220030340c8010b48010003229030072003400003440d01c6c0c00110300740d8032508030703440c280841d04043c06000003408020b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 299876393 1250 299875143 299875171
    0x915030302060c1b030703020304080d050a0f0f090b16110405071e09090606050d0b0301020408120304060e070b12060406030b040212071e060909060501090b0c0a05030a0f08 76
    0x1544001c0c1d00e8110041c8180181000020341041d9001d02c00e40c444c8010000d00212030b207420103498081c1d900c0d8880d00500c0260320031214000c14091152040783c00b101456551003c00b4413041d2019101c8024005182c0c0a000302817030302207603c2031004050006441a1035880030110740d10708000c14402d01600d02030307004034200340070016070300d82000f44032039003d11082500d401007000340e00c11900e075452a000800381600304040000e68035071000240400c00240c03e0304000f051201d0382058200c0c4140e208481d990781140382159486084040035649c0980541800f15040b0710300004a800c00e451a0403c9007251404030f4441d622104900005500120a0303034100141803c545903c0d22500c40148000e104865006200351000414016480200407962005041c6034414141026001d81070092000146241c50300203041c203114000e000403508181c64003034003075081c10305400f89680040782d2000c1d103120764683d1600269007000180440505591b4100ca040580c0f4401000e807100900107078120994 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 299877643 1250 299876393 299876399
    0x1905071e0c1106070c051002010209030604060e0c031606050c1606030c02070e190902031504061e110f071704030501060e06030109051e010e06010305072d0b13050310060915 76
    0x2100307902001b038803000c41e00e0120404040744100e01920883d400181c040c05001c00740001c00c12182c205000c2d1405000c00d9a03500742d01b000030f0644c1c88001c5100780400100c601020401c8902550080204d5011502a00d0000c10102d4403c0b844010360f03400704000950380e41c0010045503050282102424170701031602101e00700003001c42400c003c1c4500301d11581e40e5900c8100c00315581000a1a0014001c0c1016100c0e4541801e10138003c180b04102c00c0cc01185010110140354982d114251881a071190a40d0400d440f0f08501071807900800822218003c214407460341c0c00d00c01c60f01a1000314807400003c1a80e0381003000b00355100a016107058001c0e8100b031a0800054400304103448a140c050300001d034200350694200d8050b10910002c1845402014004400c0c4000402d0a100b034130b515850112103400189075403003013074485508144410f40100c0d0180120164a40201150030485100781c6065864000090411602e64800f00296568810801007c1186e004080106400d10281401c681c6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 299878893 1250 299877643 299877653
    0xa0e09010e04110603071d0609040e0d110c01020613020a030b0406050106021911010c030306180f15060f0503060402070b01080a03120b031e191b0503061905071e0c110607 75
    0x115100010541c7c60080201c00b003281c42d0f68043c0e405d10b40006005000c02c44080b80c1131a25004468418400904000300d03014210b68000b038005510101a40203091a6494121796a0201c4484030101c2e0301c00d2411400001050344040d000b40075600880f0001540c0d4500b0101902d851031030352006403200c1500d180e0101003030110000f00b840ca0400e0911030760b012407624049000781021b03000040d82e02c01d000b0043c429169280d00000c1000e150800801c160030100c012940b032a1650300c19400020500b0303e034041080c0c4107101039500001c0160000d410051180d45501c0740c000700340c104400d207500c5550b07076005041e40030800c00341c0d50701c484000f0040300d0000b80209032140c400c40810020300748081c034620403a400c01c000745e5140000145200300d50107424900031201085911403814103160115001c80d091a010441500940301000f0240030902c105043c1405480e00419840600c031001e01d03540d09062003580c0416403488181c0c1c0f10881e00d0078601e446a2130906041c5d045004020501004000030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 299880143 1250 299878893 299878907
    0x921080106090b0a1e030e01110f030606072111060f0f06060903070305010c02160e150904020f0306070e040c0305060319080d060f0302091e04080a0e09010e0411060307 74
    0xf98540c80c0300381e55041c10303074015200c101504030842512903402400d40c5480b40e0591010740581a518006c3c0440c0344418a4911240035001c00f501310003074100040780132490f054004000c0310748140e110340000139460f50b0703001440742900443c0c404180c50745403100746480103110341c40e480841009060900c2c205440b420850f18401849a0300511001030000000d64007001108000d41c7c1c8440203202803429900025150108a03d254200c25460034000c645510440240e511403402c900c20360021803107480400c0500403020340140c0c0c000340180c4035426243ca041c070a1031311501c02c0751945c0301d684081a0a0108840078403005c842098640414801c06030740124510010131108041c0e10400109410480120300c194040039402914216000691010034541c0b0001c0360300072aa440496900d0401000c1c0e004a034000d0703010f2805044000030000b501510140c0b07a820f83d98507114001e032607514085201c10000381c00c490f01c403415402c02c200400022400d2580004801d881d582e0031814010400307000c003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 299881393 1250 299880143 299880149
    0xc0c030b1501020313030b100801020f0c0c0319060203070309060f14060d0f0215130801090219030305070b10170a020907020106050904030302030a1401120606080c0105040504020c07030501092108010609 89
    0x449100408141d000108e8140680234001c1400210358492900860028590001580201c02c1c007441c0101426498046107011484a90b800012030b001610358508000351701c01040340d42815a10048600803e04900c01c9180014010800113519024181700800c9500001c010521030040c40a040c40040c1000240400143c2d069403e400c804c99001020101070240f018000380f45110507400054070001500b0800010f0f0017510120740c3c500c00c0c0345100704d04007018040503001c10400c000d000002031803078405540c0301c0040d05070351124540343d42503031002e86202c0c0980c0c0c0b281c2d8440104c01c01580707001940301e078028001340002c00000d1703c1c0c880070804c1510001d1000c0c06041c1d001c800a55181d0b143d820089200405804041d40c0703603114400030641240c10101965400c0c50401c02040c1c1c0c03e030005a80c0302c5100705844003801e00e0300d0078003084042e500c0491804440d00580c000000052424090420003d10a600b018413454140d0f83c0c109031402302002c080100300c2100010040b00c5d8102c4415815 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 299882643 1250 299881393 299881403
    0x605070c0f210f1b0f050102031213110301230a050105180a0f09030c03020d02010e1f0204032009092d0a02100822020609100c0c030b150102031303 65
    0x7180c03400e400c10f0410264580009062404003240d0514550881c3e1000d501392103640c0716809055844000485c1d40f4068004003c419040d0040419030000c441500f80c40c00c1d40c49883c0401151306030382d01082c2500d0070b91544203038003070070880f0201500180c1011640d1105130001c0c100555803400300045c1603005400d050342044054a80131542c801d01c1c81d042001c084234181c43c05c0c42101315514009104017203210b002c1d001030040121106240f44180203422100e440040103012001e061000440e1141f440c2d2f0a601080e54200300000004400400c2e01030444035000c0e0455000c040c1d1024010782d04001052002135070020000e030444690500c50191051155045800c40c0e0460714003c1d500e001d80e9008040d501407080720003c007406da40301040314400c072100c0c0c0540303001e40350a61440d00c0c2c02e80c41c0580258060b0050218400720300b0328130005040401c0364504461907681646034101c8a04060b0801d031068a201c0d000c00040c000303107510b603401204083c0b004501c2c0c609040a80c4d50381868070700008007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 299883893 1250 299882643 299882699
    0x60306090601180b0712110604080306030a05100b0a0512061302130212090d030603020108161b050d1403070e0f010504080d050304050d180603180c0605070c0f 70
    0xc042e445510038542985114450395125901c500f0038514582110710211440d8880c0d10701071030002d2013140c5030340d42002e502009048945560b62148180e8100420b070680610a641811004c1081006007901300d821000002852203019800d015284406030013141c0142042c00302c200c0000b10000b071169102000e0500341d000251548001243c0d522000e45804007075001160515020034902d600c280a110340004072090f41034071000a0701a9902c606c400b270b01050701e12002800062140c0d0380880c0e105000e28013240703841041c265401000740300b0304055409910602211100b6908946400404001c0e245000c3c10343c41c1c00303400200f94031411001c20303015020040750f509582e40940280c5001e05808815108103c03076001d8018450740003114181c41611800c040800d201340603080701c500080c0070421090001d41444c0c026005041d860a00e2121702c1c05e40d628800115050546541c0a4809682c0310b82d95112641404416680541c101c051941c2070171204200750090645150310b190a2224044 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 299885143 1250 299883893 299883901
    0x601060311161106070b100f06170c1204050601081506100e040f052d01030218040c030206040f06080609070207120201121b021015171f0605130b06030609 68
    0x10b401043c40300d9560403900100e804410002101d034420b21032020040c6140140c3ea075030780424030700811445464042151202c0c288940060010303119801985a03030024503201e88041024410507085900799881e270005401802030801c284460f28000390440b50040184c240324000070394200800b145c1109016004051041548858000f01015991120100080d03c0c0c4404e0301c8440151403400f0401140b44101045aa24070881625040e00e4014010410340310070340c3c01a003411600070300191081c101e048000001650b45030010070161801090381c203d0f40b8a040381c003607c03121014088521504d000380401038495800a2440120350300b0392040740a454150005a401d2020940e15002c10360030000c1200c1202540045465070000741c4e82110410303041115003000b00c841c60f034aa030b0100120b4a0040104540c111240c0c480821000142c07500051038880f14030304401c500442da581c40341ca07903000308014589580240050b8150310024440e0100d6a070004440e0710004200314480c45801c0081 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 299886393 1250 299885143 299885153
    0x21c0219080a09052a03070b030c0306030a0f0602070308070807020a02130204081212061e04050604110d14071103121510020c0a06090e0f150a090905060106031116 72
    0xc521a01d0b0800141d482e460004a00c4142d01c0705020107881c02001c9017995800e40d41000107205013100d0b800c110860031501c40c80c02402c8150300160000d941441403408000c00f04082890075021035114540050b1b0320303d85850068440b840084c940c81c107105440c0100000c1a80119518000c0c65040b9410014888005c000714000c0c09550030040040c4203a2003600d030fa59450800801009000d004c1230109651540200410384507480e20000b404501e00c00e0060207424550425504007130001c20101d031407405942581101d4114090909000d40c80e280e01e0071100e011413401d5a0058040e03d080c00b0603000028900c0d540e48120484040c0a41004001a0350b50b140400f001c59805001400050121105c400017035864520003007041c13181c0c0b643d18000540314049e9802d01c0848a201404000c0d81d980d2074510454108010700c41110448581c403110400d0340c403c2240c0004d0584d0507800217412080d0300348a490488160420000c2c1440c180c3e90510050004094554000710010300a00035005841e00d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 299887643 1250 299886393 299886401
    0x403080318100c05130915091107080d140f060d030804020d080406050301081005070c020f130e0d020f03120412090306060b0a03150e0c1803070306021c0219080a 71
    0x24003140c00d0b01d094103401c1e019034008005d002c0d00c018406800a0151a01d15880803102114500003104074001801c100d00d1041d078102061000702c0c0a003d81c20018651600806d0f94031410115850507511740290100760251001141c028505e0100321086140140200301c2c020400d42c009028804c103100050110750b1824601c1e03250325840b0100e19150740e51aa00588103400a0003444042d0040300c41c01080d4000c9407288620481d103030b40ea25403c0010503021f101c180a8601c4a1580000c04121101c1c0511018007410304214000f2000b4204c0000241d0300a0030280390324099406a0801c010400a11540080442c0c2203a00904858110380d580102550f50f140d550b400140401e043c10070004070914a00003911030200b25480078400c1c0000e40d082104242d1150040981289446011a400b104004094184000d180c0d40b044a00d0f00c92000180c44d080da80c0e40111196a000101441c04c1e80392200041c101e2041c018083d800c0180c81c4111402c40c4140302198400c00c040b410010344c2c00c480c5500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 299888893 1250 299887643 299887663
    0xc020d1b11060408010e0d1107090e03090a180c0503040818060d0509060a0606050c21361801030f0312090308090c0607050c042c030301030b0c0403080318 68
    0x7082e41e50720790b51048098003900f00310462a10310f0107a07442510013a4059065891a00c0c5030b00044d0003011b05141a882c0140040d01c0300d00481d101c14006451341e41c50b64484000981140106170032402a013480000990f144040e1035010040103000340000294810f040d20440041d12155030700c2b054a07107001c5000c2c0e0185600c010300d080e08000c20310003102d0000c42e856000f414075260621041e0303154402510070b0311034032414450650040c188404040784920044040085540010b86807001d0030040d0a500c0c070359402441c0320b80e0341c00110500020306121480014400a680b641040c0c0d03000599400d00450520002c3d00d45d4550000318420544605082c041c50b0180c050704214000072800c006215010840e480b01c224400c41103241c4003440d228042d900030701c1c0d001c00203003003c110388014040544116000c02c1081c0340840c02500301d51554180350b518034031800d002161250302d50b003007040c0c0b01c80001c0c0500190140400c0203001240c0070301d00b1281e001030f4100a40d000c410304507070101e00c0d20701415 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 299890143 1250 299888893 299888899
    0x7120204180c0308090a06030501030809010809010e030406110d030b03030703080912030103060b0103060b03132603010b0a0201060b0405060306100c1e110f100c0303110406120c020d1b11 82
    0x702c001c810421a00083c0944420640340701c0d0080383c64990980c1211000c1c040901013202c01e100048666103e0301300603034002040c00007c2072460b01c2c20151480c60b001500b000780400d05e0404541d0006108100c0344013100c0c081d05e400d200501c2483c02194584c882c2c407001400b0443c1c11800502d2141c020050301ca00c40e051015108e50b00e6039a810aa402001207020450000f07080c008005003d090950540340501d00c7c0020407070b0146010341c0d61184074421300900d4003941050058a58001d41e41030b010f94024502400d0291399410651002421100300d0703000396101c144140310a00c030a031034023000e0701d034000b405a034140754003952201c0030340301000d8120005196401c0e9180b0781c00148842510b11b04d030903205202c1c11760030100b44420410b5500c0c100c07082c00d030420495222800e01074425441600554004d08000501000c1c1804029841e80560041300c0828000001694000410f20034460301c0100d03440a0f258410034200003d0100100746220b07240c006c114608030050080d5072640c012000001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 299891393 1250 299890143 299890163
    0x31107030f020316060813020d080a02010e06090706020604030e03030d06080106141c06180f030c0c1203080109020d180506010915030809090a0b0d0f060e0712020418 73
    0x41c0c64a031101555841040703000b8001c1055075014041400b802c40705a0b4980d40741d6402d160744240481520520304001a680040c010510700d010803500c0005161100c40c0794004140006460455840c120300684202f50700d610072401048001d41c0030030001d8200b64145480010099108000381c03030760181410350710b116480c008001520240540c803113070440d01290703003c92000070715504101400b0000b01c080c108801a4100c4140042c0c1e0781e03130207100b28541d042d03d0312101d2000354590828004003110214089158a01c50000307002842c49440e000701241e4550030310104150360000d0600106125102d8065004202000c12001941100559036054400000c6c1100141080350760b4003028454070340e20920b03110341340141848103c1e80c0400d480e0800075040c0f5201c4c920043c072000c114000e2031b850402d503541d9a81001035403800d40c10480d050003540c20081401c51814000211f4013a83c09504d015030045808000040903d1404210580c04030340001e4100d0319810490800951140010301c2e090403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 299892643 1250 299891393 299891399
    0x9060d0b0918060702030a050d02070804170a17090f010309140102280504050a06050901141b01050f1006050c030c0d02060403021005010b0304110415150e1f0507031107 74
    0x741e40da1070414010031812600f4075150082c041e6100d21483c0d200b680041c504018541000090b60001e04a051041c50000d1401750749001d00582d000035003040c12503a400c130580d00414040004003500307805003405207142c0303030180320400601210b5045404905050701d407030841c4244110700c8586081c0d00c400b00b0080d5078031142031303030101c3c01e02603001600c0d199182c409030380c072844600c20f82c02d40d419600301a202041050030b00f1410341d2203422912545042024620480c0081030901010706118908e0f1400c00e5107422a000030f503030039641c0c01054074502d80d030701000300a03501c0d8070150b0550407a1a2810281e644500074a003982c19440746142d815611f21038003400301c08032680090558403c034021360980301c0d80c1c2d200d80c0c010800d8445c20300c107a030300100c002c0c001306000c60301c80301c4100d590900c0200000b600d0140301c03003500c00010044c0d000003014070042c0c92069803030b078014050b01c01c8181d0444a007000ca8544d039a80181c03000c0142010000c12801103004410140200004861407800c5021150321940d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 299893893 1250 299892643 299892661
    0x50f18010f02160b0f01030206031b070f030804061d070501032a090302010906140a0302030702030d150501120b03100e102a080f01031e081305040c0c050309060d0b09 73
    0x660f000c41116803414480005503a5160380c00d095060381d41c0142410b14507164001400740e80e180401100780c0440040040c02e00180360884040000e502c80e49402800b403400e801c00808880803000000c000754006580c040300c0500204841054071030909001510480c0944018007419640b60800c0781e20f004900c3e9400346942001048046078400d070b952002c03242e210101110b607003c0e001c00350050404240400304815003e600555842403291048a0802d0600c4203010169051140201c010400d100403d10007540e11040c1e280050b5840c0b4002d0105210fa80301081d80c40a41480703804445594010440f500b00d010702540c011105103003014021441d100b02251b005441d082c0800306022040c3c1800c0c03050b5402030103042d00c290f85003100c0c02020307031841e2202c2c00b21500c1401120081e2007404010000113181c40c0c06400c2c0f0aa1032074802024078200014001180d001c95802400d0101e00c00b226000244000304440820005503012a11203e8203100000a0082013507030651024002c01080303503c0c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 299895143 1250 299893893 299893927
    0xa050f040902070b1803192606030609010c0804020409021503040c18090f170c010f06080d02010b0310020c07050d050a121805150d02040308040f09050f18010f02 71
    0xd01680c3c052889480300d0825005d410f100c01c00411a503041440000f015148421514048504504100c48580d06807c0804500c0c41c989003000c00c05501c60302804610300b0f00300030059101d01c0e030030001c20907040d004401034012000280000c0c45143c4075242a421034899040fa401d44400c00d030700d201e03241c3c2824540082201c038103028200c481c10101c45110034025a034041e41714001c0d00b02c08400010314568840028a0880282808443c44100f1a4515811003403090b4a06502036400c00280c1d0f504140e0414104003160502c070045a0401e10142000d9401045102e000440b0980040c1d0341c01212000a0410000b940442d41c8442c1c0200c03404180b1002088006800c1e1140441c0b01528668107002d44070071360b61540c003d103800c0f0f00001c18811400d0181010401d80d40032080281060041fa43c0e92081e61b009030022124982c0106040284100b4100c00002804070000288243e20b00a404440182d400400714200150440344484480b8000e40c031503184100c0c02d0b0f02c25955100452010380d000c0b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 299896393 1250 299895143 299895157
    0x70b0a1d07091104031101031d0f0c120f0d1b05061513110a12090c0609150e010e060703051608130f120b2503140604051006050a050f040902 62
    0x440d080c1480040e00030002c0c030850f03017500d40c0706460000b40356180c001100201110344003c0301d04030108071541c407850401c200d000e00a200441c003c1c00b211103c4802d020030400510240b0106500c045880380780c4850124a004003250a032034007036240c1000c000103440894003914090264062802400f15202460318900300c0648107440902e91000d04912910071120482900340e9041c40600c5030322442441290225003400000c0000304030712002d034851f80034086c5580e0000000c50854581002000380301d040649050700c0c4d5007001040d442c00c1c0400038181507416110144100030020b6074404160260003a00c01d19070246904603500500c9142c508078651002c0310181e05921203540001e40d010b81101c40d0001d0743ca042002c2e4801c00901d603115802003502500c0c401003012680401098040e52034200b0700b4100e0690f50114201840403110501e0041c06071045010740c0c1003404206d20b0100900c1d0040c00c4441c03d26015a8807041100111064000c1c168082c1c00c0c5d06000030001200310080d0081c00e40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 299897643 1250 299896393 299896409
    0x3020c0c240a18080c010e300309010212070b040f15020d0e0106082e0209060c030a030b010f050912010f0911040b0901261005091011040b070b0a1d07 66
    0x11a50329213500c203554403400d46400e0700041d0303503007031010041c146011000c0c0755400180c038201240900a40506210303200d442d0b818490303400400c800030305680c100074095561040c400c08600c0d0008a486008240400910140000500c0f402c8401040030340b080b49181c0390707d1680115110868800303640060290403103c80e100303608060000c200180041a40198107500803c03101e8030b0041d0f60b42d18954141160842043c0a50034030054400751a0740d002010003c080b131025544c1c030031020170f0240448003001003280c10030511b5215840035a80100803900d0390041252294494080070340d01d24007400402944114140c1881903c00c01c0043d4014100040c000488041c010f00d103086040c400e10000910488601103518102d0075403943d0607403890161000c00100b0366404510307403408401a035106076107501465000daa04001c0103903e500c501001c3c908615207003031070203180c62060034142c080c110f400f5050740701490120361185a10b41c020b0040c002541d07610b01e28100e81003102a02c0349443e10030740c04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 299898893 1250 299897643 299897687
    0x40f0b0310051e0a0b0a0602060a1103130809130e0a140c0603070513030b070507060b1f030222030b090d080912030a0212010f0503010c03020c0c240a 66
    0x408100c0c80c020310348510b01c0c0d14144241d88030fa4a040340d008450290070b81c5100f59881003008000e032582c01207540508040e0b0010b00c040d080c40c0256504542518803805032242e024024454160444580121000c0d0031240c9aa00d4400800004035420f40f25991070600c14a0960b2410b0b00100210313411310001e0145140001800c1425000c075100c10700c172106a684080200300099420740500054030b5210401594000c01c02e84030ba45548544c0da091310f881c0e0105102140c950b0401083d40245048154265540106641081190180c1d518203081e20750526030045010502050b05412217129a84801484c0d102580d4034203001340c50724020346a14145026440c101e4100d6030089590358043c0d981e070001031561410ba015910b000b40c101801466005408005269201c420f006c4820f0107082904c1c19116510f00e0201007500312000c5140d000c00f03060040c000b0441034040072500a0b12128103886060745120944851040303450b2110101180e044003141203441c560f4401c0d0500f0483c00e211300400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 299900143 1250 299898893 299898913
    0xc020c03010203060f010f120e060604060605090a06110a0c15030c020f0601090f0b10020d0e03010b0d0b06010201020910050403060c080c0720041a0a050a030f080711040f0b03 77
    0x140c283e2204030f420a400450928905515500c1104100d41141007440c00d8400a082c1107030402c1924021503904425030300440a1241c1868075100e072a000b030100e410918030f05440c0c03102044100d071440c8500800d2040000107462025414003280101580c17101c80000340b10348451420803242c000840c204002441d00b84104c01c40c070300006403034a8201c1120024030460b0310b082940d00140c07819030803403c1901e89800c0701c110281c80354840d12108440980140c05903400010307000744a21040601e59100342e0606503264843e07120304520048a0340c1010b186181da603a01c0300143d0291061440380e80c4c005001c41044c40c103056001d000f900c00d80c2d00c2064140107202203c00200c0d880d0105a49824082004000030400240000d4135949403200c030710701689140700c810b40000e046a003174164104050700050034800c0c01d4940764421501030941110b92441003401c0d911420703411000705800905010000403104103002401e504060901b1004005100c400100b074100c8001c2c0a07444a103e004c0e104901000c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 299901393 1250 299900143 299900149
    0x30201020403170f040315060306050c0a08071409060702030c06040303110c091b18060c0106090b06040f0b221706070c1e0c03060e07060f05070f0303111c0c020c 71
    0x22501100d007a460309003094151f40342c050100207255103045c9440e40c0da101c00400600705006a500c070b200300c10400c075101c4104020140903864000d00c12030421540103140c007034503005403090f0b401640e016a201500c03100360748007107441c0c400700141803640070602180010030141c0c080400490520b0364030640f00d2605000c2c041c0004a0015a40800c441c50b1b003005101c40600c450307000e841c907207240d51002075031280300d031000c40d600742e10125118402d039442e01001d000c021014082c40302d140900355656860280707002841c00e000341c0c003402114024440001d030400e500e410551309980650302018420143c2daa5803050460740c2204400c00c0c281e60182000203952240609030f4064807681000780741c5c2218601c0100c0440542030404101c03600c01c1500d80100108002d481035094208414000b0030301941840d4001d07026000698000d810401c040105c0c000007480c440c0340c94051a0300d810080341e8552011400801401070101d80e0b400314040307407605000c0b03003201c2d00100f99401e03061302a10301f541480418 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 299902643 1250 299901393 299901397
    0x361707080a0c0e090a0204050414011503080f03040831080109030e19210203060603070308120c0d0e01060501030506040221090a05060703150f3f03020102040317 71
    0x7014000c10340702541001941e00000701d0641c0085107030f003a604010b21a038001401c548060f1003d642c09408480d40b0f2000441c00d115165001001c0300503402401d203581e4030391059225001e0007021200b400300109007000661420303a041c4041810410a4540345009074264119001110100e0800e410800045100c0c06100d8003000d40d405550380d580a44d00241408280803000c00c0c465800f000141c0d00050120180440400c3d0704482c00380c07980a060349004052412501900c02d07442a000b0880800008122100b26403000c00c0308420021035664071b11a0702414010a802c1307041c40c83c1040e40300001c424040d0300410980e10b00362000c000e244c0718207050000320701500e103108280d0a15428503102c141000c0b080300f503114060800701c49600c16076581c0d16042c01c10644007000440e407262040c500122420700c041e001b4100c08101d915005140c03080040ca0700da23102c005007040c25461440441c43c0f80c545910315035003460b00c0d042602a25040c0c58000c0c000e611511003a0350444085c0084100c03140c1c0c20007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 299903893 1250 299902643 299902663
    0x320c0408060601030917041205060c04050120240a0609020c0a020d0206360910060305510622050d140f0604020136170708 54
    0x901d4907644040056005102c07241c401d58100c00c01e0300c0c00e0540303051402c000b88003502c0e40c9207040c145403401c1d2803c90320300740c1d01410705540030324240810720640c0d90000719217125016821030034503480c004c2d2102e10f0800c054000042d04040c400096490300e0702d5082e1085000d0902c0000400180c4c0d9622484022400780211020316034004400c1107000d85401c13086211050300040003030b0f2804080c4100050b240005841505c5110343c1310850700c030b0141d02c0441c0317000b01040076203030321100b1b160403860380ca0848901e005141c1810f9460000c0340c040300c4481c280314101005101d000307100c03038003d072005003110044000f600144004a0a042c44690001d0207241c50002c1c0030f0203c5040554400c020441401148030310b83d1840c040c00c0001070550b90320014072841900840d0100510ba11411060b800c00c80b40400094040c0d0211080c4401030341c0c04440f10203242e001c1e01c6960304c19041410f806507203550020300e0b50703020708130b801000c61225a407501c00120340243c542164452036690301204c0d20390407181 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 299905143 1250 299903893 299903909
    0x20105160c0f031407090203010b041502030913050105192301110102120712020304150b0111010203010905010f05090f0601030f0b10080105041d0c0f0301320c04 71
    0x110a9500d40e041a4032405a02446025000c030819102d142003200a0000d5100f5140207644840514180000380b00b000040c00d100141545550f05103444030304c2070311443c810804856000c0300d00c480c0d501d20a009444c20044028807005800d0040c05500b0003404081c043c01e80325102140d00d00054503508a0100122031001c0888041e50a098030410416105000071a0501c11030f40304252041e031082c40100090640d903190800302d801d140381c00030003181241b0080c0002c2c502c10401e00c4045107802031391a600040b040c00c003040be1907004004841c158520200480103600110001c900303030204d500418140c50103200000e84c0702d0f039207004011401d40c087d18900d003800c8031000840c0c002e5229401540c4510b0b6410b50104a07200240c01090308001e080030600c001584210040c0030614060140000001d6a0311400c804014501002c9032181c540034039041c4a01c55480103203180b918290007a003c40080c001410701442580c1400b51070300b04000554042c200d4800001504410618080d2010340b4000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 299906393 1250 299905143 299905147
    0x903051510060f021b0301062c060604061d011b08040317030c0a1112040b0a0315181e1103010905090601060e09091e01090519080304031202040b12040519020105 71
    0x70b0009869078620313070b004591b059500c0b1903012442d081c0548143c9039400c06140304004031040714090003441100500aa441008100000c100403684113015483d00d5040d140710035500444440180c54808800f0b11410b900443c0035007100a115507040034101700d034003502110004d48030203203083c0c1e0f49200440b04546070707840c140301000e00c45100703048101301c0102e4501124100a0b40c4181c1c03000d41c0d042940104200c1c440081c80e10450b079450301501a00e0004258900041814a02420924411001c2115816568450065989100d03a03501d8110b40075420013000010170026555a00358401d0058054490600c00400ca24050014074181201c0c42c40c0e40c0c10100c0d803071180400c0481d84003e00044614800d40310b0700340010544400501180c104100000780c4101d151504a01b4201c1d500d0340040060111141000840d180301700f200d6125501d8070f80030b001051070412400007402140c118100c6140c0c00704455018175a01d003100303800386018400b1139442c0920b0b10320142205070140c000074001441 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 299907643 1250 299906393 299906413
    0x7270509010203010b1b0f150105120d12020d020d020a0f02060f09030406030e0a14010b0f090f011208041a07020406140a300c051203031b09010903051510060f02 71
    0x2e05118841203403202507d4800c4031550401d85001003003c141e903081c0b403001d40100200d15000d1650001e0391041009000c440f80a05005041070003540481500300d40c0000300784005001690484500c1e403050b86c01151600f151250091425040040400140c851a404141d8014120903c07a10500c0007000031850300b800c05c00c0032400b500e141e22070342510703109501c1e80000040520706820001d003091000001c18240702c0080201403200c44071047d0080f6002030500092051304481030781540d625107900c401804240c540841c06104076803010507582c03035075840c0764100300c00c02c001403201e580210360521109817a50f44103107001840306441a802050400304000c0b0b2115a12200c02285e41d105003403085501800381040422800c1500311a07680100790140014a010a41011450f42c14070045013949008511081c1c410308000501e141711902141005d030583c46a1070341c0001e554084240d5011402002c100760106006443d41c0c42407001500c00840c60f644184d0399003420007210783c0100985070f4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 299908893 1250 299907643 299907667
    0x5011104032103020706050a09110409110f19080606040c05040b030f1f0305210304030f0e0d060e060709080309030a02060d2307020d0e0a05060c07270509010203010b 73
    0xb4a1001c042c00d154080c01003801141c82445010320400a104e00030421140340d1410350074501281c406288914540b9030b403080407a460000d0312001305026500c203a80003890b40c0016210b02d415900381e106400544102003010a00032034001d000300d1003902d040c00040c41c0c002d42900d171405180200306152800307000085040785150a02a048000038200c55401d80c040040081d00c200546c1095540d60b20a0014a12640021000740b6210020701195411801c055500510300d400102e5039000f00a4200015041940c8001e1401d4105d54080010480380c425803a10b10f4448108a500c0c4000c101d1820002074070038004030440d21440f00c01005454503400541c20407403150408060b4110440d902c50320320b40340c01c40003200710100c0014452842d01614203804003e1404404800b000e040118091319821103486803101682075400c03c80d0207030f4903160f501c41c5c49881d1500e5a4032591020311042012403542c0d14903044000207070a0034500341700b40d5031085452800e07880700380b1605601c00780030080314800c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 299910143 1250 299908893 299908943
    0x2a021e03030c18040905030d061a03130f05030d020706060311010f09170c040c02010225020609090c0c070605030615040b030a0e0a06050c120703140a0f090218040501110403 76
    0x83c800400c00904c040302c0303481e01450341e005406428a080d07a10501801006520842180041500d001c01c52a52514010502150340302d8140200300305103a400c1001000414402d0b00d20691034810110b40320500c0b0305180010b40154030040d10205031041144045500c1039482c0e02041e080c9859000e0302a2604181e40e000c00360114402c4568002c659403540c0603910fa001c1c051059149500141e16201164007c40d0052200481c420502110401c00070050b1a800145c61501c00200c41d900890340d6240125003c900c1540c01014040c007840b600072460701d810a0140d40104819031300314a19035401c1d402e10549115034020000750820500004d0b01e90903842c0c006482c941400011307202500b0385a40d1398401d50340c055845580300d14000c41c14000741400304291a501851b14641070122000c140c1c18035001c4040a80142000340d15000b010265103455040b400038503501814034a0221103020080340720203010744044a0329405e00c46090020003029040c0c4d01525081140f014001d09024003032202d81d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 299911393 1250 299910143 299910187
    0x60816060807020a080403081b0a1a060a12050a0611090d0809190603020403050d030b0d020d060209060c03030612060c03010e1005130207050d050f0d2a021e03030c 72
    0x18428401c1c1e200005d2400c8000d0f0005521440085c4c2d103880140c146d03040180014190040c1a03170054590308081110100317160040f00070b050481c1c45540b01c3d10007082c00401150030041c161031800f0410020001d00142c40076110b40222030401400410010600040c4102d99441d540603151000c40804180c0303400040207030040040024940441148503d1041d6049600c2140841d9011408000b40182400300c9042d60b460340c50304210320310804001404011210300040d000300c0310700e140ea804100c0540d040314a1144002c08075900d9041800f00c0c0c1d95241c2c4111fa405010f011610031318581d410000400c0c60148004001e09811a030808074800484100241000c071035180c900400107003900c411101c1a980d540e00c8a0241c3c0e942044d0503c1403520168000a40c00c00c00204443c04510302c0e0003041d41c51004040e0004111950100c40c0b0404060368482d500ca400c40840b6800c1b4007558000459404003844400421041030850441989038041151f00d0b48048500700001c083e0b89140c401003a481c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 299912643 1250 299911393 299911397
    0x40f1e0e0307021f02060c070c17071829030d1202130e010306140f1603060302030607030219030603020102030307051b0d081005030a02030316170f0d060816060807 72
    0x1410b80b69000030b403032200303450400e0b0300809100c03100850700b950600a80358840c0d000c1d03004610701b02081d60303641d0112410303200c0c00c5180c001d0006c0100000b2401d01040740203003524420141d02e0072400003100c00500010304054000e5681d41e0720190168800e10b025641c2c01070090180924640c140000c1d610300122000d80780606e5420048035140e03c56007800709000e0204425808910f6045280c00e0b403c031850180030b12068180c02c070400c0b50715a20f80f1a010b03404007581d09104c514a40150055014103041d8000070740c18040c132000c020083da8140d0203008240401007003042a01109181034085032100d01020f4010781080000800307860003840101180c402c26100030407110946030030142080d1480002c080012410418000c0780041c0141082c080c001c102d01412140d6180d0b800603650344541400340003c81c001e1807a100502c851203a24113107a82c1811406c0e966010b42e840489a154040d00c7c0300036815103040004102c885c0c000501598404ca40c0441e0980c03141000340980f5400002424181 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 299913893 1250 299912643 299912647
    0xf0408030d0603060b0303121501021005010e060f01050301060905040203041106030a0b19050a030f0302010b19030303051311090a020919150f08070509030307120e040f1e0e03 77
    0x200020208000c001c103490110700001d9103070442c545182550b5146640900ca40d01c207021810a032110200da094102d020031003220a0a003c100050307081519803416545e0741c030f20740000000c02e10148000684241c6003110a10003040c1600c005403402e0000780110740c00a1007440b014001c40c10107a00454119000307a402000e413800c1200001c2440c4d01c1201c49103c41c1751510b64100c4d941c2002c262202042c45410b104d604c0090808000c120f85c0303400d902c030191280f07500c0d514090506000f0b500c8641d22160141001c807414001006001e00000345102c01c4001a1900d0002200e480d1284400000598017040c921401d418440800c20100070140083c40c616170700304942086030f560f18030310708034618a40d202d4101080ca040005a000340406080c5000e2003407025200060355407001c005940100181440c5880c1c4c140d4001080c03450144010040201184071300c40040160498a01c2c104054125000d119809403001e00100b42ea10900d2026680c0b440c54241d03030280961038200006141004003164 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 299915143 1250 299913893 299913899
    0x90314090a050424090605031f0204120b040b090303060d030c060b0a12021e0607030f0e031219020109050316020f0915090109180311150103050706021b0303040b0f04 73
    0x103400c46101101d03c003c1c492134540100c1288a141448000600c01c02100b049210301e042d000c00d8491001e00b900c10f160a00b20001c1d01d84010f1150b060346c0c040c000c140d00c07900b55007905181040315001c6c00d032015105641c2c5000060700b91035000085070310969028241c140c00c19129902910000d00f00241181c0140e1030b8003c0c00d48a45610303da52000b005041c01c40030340f2409500601181402402d0310b810078424a040042c0613850b0441140c546030352510b4401c084e00038824089610704070210115505008460a80340e0604005000c1e05203d0850000e1052805030040280d08035184400c2c0148250000d10500032442803014860120500140101040100403400100c165030111061400075440305507210700d504210700c506014002c902c104001101402d900d400304031955a13002000c100e841800420315001c1480141049442c80345945480d5860340b515a0712100b00b405140c005100e0700010701f01c804030b419050800060043d0245103460309060701178900d54002c603031541c41000c0c100000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 299916393 1250 299915143 299915149
    0x50a03260901020301090b0108221b0801020a09170601350312010e070c0f021815090c07080409110f0406050d050114182503050603070801090314090a05 67
    0x9500c00d00a0741d00050362581494505001c81d2609030606040041c1c18040264074030900c2028460f061010101d0003405c4103a01c1c100c0c03001a0b8405001500c0340e41c0503400144804150080c091440d890b45448203c240c0b6282403000d6609900c1c0c10981a85c48036004226400602d000160007a00146505a01b15008040398525500d41c1d04445040c0d440060b40c00721400f684104a405050071644090719070078420402808441c0b031140107012078104a200340115038ce072484003c250403d43c10240341620384880005104440016164040c44800e40010b441d82407010441c1c05c240d0f403041483d41000e05207903030b12001704018284641050010800341403502401c0f4040c100138203c43c1c0e0395650f10039400c075400c004c0d258180e103c1c400c0c0c43c00318903101e441680c80340764007a0303000c1500c50780900c030765100c04041c094a4449914202e0403982c0b02071070650f00b585034220b03507c106030550071116241d56582e0841e003200c220360400b900280c10480d500c22504007900080c18070b1000102a00d070003541351400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 299917643 1250 299916393 299916467
    0x601180305030904060b09010f111603060504020f0312070b0612330402060f03040c09020301080c0924010c0f0204020a0314090706050d0b0409080705012304050a03 72
    0x9075110b030700200709250703103180c00c1c040c0038064104c40c205030b824101c4100000e04015180041a02480581202601e003243c007041142d402c3c1442104501c2d690741e407402c01000529003034405a008070f480e070325100c0c01c9090000d03040c1ca0103503003032603654600000307601c80c1810102c4c054482580080900a0f401d00000c081101c0d0380c011902075000415056080040c103000401842e400c0d031540d04003c200405a900c1505680d0011100708011f81c1ea80d807989441d1001182c1e0360000012144080004100a84001130696000d0015507203c9060b403a004500d08600a400442200007000c007044200d2551040803c4280d0318030601c1d41e5400311a03540e00042c140e8100c10b40c0790001a9440710903460184092511b00c0c0c0026024001e040c250b410020020454400c18506c0c030b480b66181d0700b5003289030312580c0c0880340180d0020880b075150700c154076145002c1d022065444829a1a07402901e030307490180315100340a00d41c0480248584400c503501501d09a050300390020190000c1c0301c5518038030f40000d107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 299918893 1250 299917643 299917649
    0x3010f020301030b10141f030e07060e041811040207080f16020406120b070311040317030a0506090c0313031e0309030f091d1803070302031206040b1008060118 70
    0xc4e040c030013481c060004201c030300c1c0d443c0d01c05015281c941c0103030f098030703140d0018241524030555800f1124060b1502d041d80034010b10300d51940035202d41c900000300b00d81c1c45805662514000c03207090050b0071b0b1400f04014a00f1200c20040c2949038004c43d000501d2801da402480e0541c0300321403090415161800c030404d5500310200410420313180f2010041185402e1085001030f200c8220351600003c0b95481d20342020700003d0002c2d0501d40d440051001862403a03080c0d40040d0360185002c00f003000c0000b400035581d08280c64540311a800c00010a0700b51400f220300f5881110468001410b540d0740c613400c800440200381084d02404500307480030f051038149440031a60f41410340c4000c55520341910300100030092080007141040700e080b40920040d450031a00845412164006d1881510788140f240c0c4207580c440342c070786240c1c072002808408041e0003001800a25213a0700c110b401a41d20342040c44180d81094115503441140140c1e0300d44154000c00c01c45400480600d402600c050100702c8c14034000d17030150 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 299920143 1250 299918893 299918903
    0x40b03070b041410021009140a06020c0d0305040321060308030108030a020c2d0a120c0e0a150b07030e030106060c1e03140c0a05060106051b06010807050f03010f02030103 75
    0x40c140001c11800501c0b1103003c90507502407840f00c50400b002901c0b042c005440b8030040b911000001d00b848000f501a003060030003402600e20501c00c83c036000b00251300c160300031881401034051030f4141501a1146a10030780c0c01d81c66015035031070300f040707030310080000e040540f1201030740d0301c0000c0081803078000038501130324410009603616030f100304002e86002d88a000c424410f410407441400031300d403078051000c1500301904140007040451400a610b80015802030704c40c2c154110b4100043c01541d2901c00100d41c0f0710041d8000300e8030340540d0501510f0695038a405803111000007082121424801810620f0103443c04100c00c50a110010742501c2485c0d10800c0085d80c030860740400e0054079100c0c0425034040c3d030140b65000c4029039015003007032401c500c9448035020210740003010400601091524541c0882520303515a10341902500c40e41011602484881c000000100b0143c0c0001d20541030320040c100611895140a0800c111482e000c0c90054055488004524130040f81e8009140a18414 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 299921393 1250 299920143 299920147
    0x7030c0c1802040501020f1204090b010507080a0513080c030604080f07021822050705100c08070c030b0106022407020f01060f03030e060304030c02040902041d060702061b0f0702040b03070b 83
    0x21400092408000f0703042c0307c1d0b042d0880d1603070003034210002040740d007142c0c849070b0003042151200d40161100d0046a1014100c0080003640301d1805902000800440c119900c1100c2002d40310b620040c0d88410480032140c260b0302c03042c003240104008401820b2201060a101d51500c400f51340807030342c2440040051064140614140110100481d802807610000ba6207110401000342e141c441d6280c5040c85407038050380303d1121181da181d114402068589421400341551034500d0314080d58050502d01c015114115210000320709184042004400305815081040c00c0c5500340814196000340500041c00358480d0500b1b8070000607081c0181001081e0f51340e0051105071950402a1110304e00c004940c1c800c0c90100200000280c200b03201d0701480b5015070340040c00890500c0440c00820761004414401c08541c0401d0203600e10014010307201d400c1e59801c1e6011500d0b501c40c075080c04081000320700795182080c092041580b0500025241944c0028000701d621401320000ca4142002d0341c108944660300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 299922643 1250 299921393 299921399
    0x60605061306031109030c0d0201030b060f07060f0e1c210b040b040b0108070309061103090d0e03010b030d05070c030b1906080313060c110405070f0e0d050307030c0c180204 76
    0x14414103401540c1d079103c084c50264800d00290300d4070035914115100d01040c4042c030b402d5911a9000e01c840381d4028141c181d403081153b51010700350b0450710044038468101204021106660700520b070b80d030300c00320000b00320313003540c2c501d004414050701d6a0210810000c0d10303064107840c0d43c0d01d405803030100107880002009010315091006072440080d585001760305101040c40c1030703680710f0496503000803945000920740810f4034000001e041c11000c0d003203500e000801485040d80011a400100391619110940c00340400e405260a031800c0c500c071560b141d0002c0f54013420f0240200c00502c030702c078880d040d02d07010107403a56145e403c030352410380380c1500844c4031003485646559640700c0c00c40030b000b07103000850421260300301e180b000d40040d0185404005404002e4000c2201c009040c0c01c040d00010001d00147c0f030242d42c011300702c00d40d481c05d880000c0c1c5401c003d04c0305401c03c01249400580c02c28091880e2000340d0b1020358502000720411112485040000184411032240754502c5101c81040565144c0c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 299923893 1250 299922643 299922647
    0x21906020903010912050a0e0612040b1009020f0c16081c02031c06151d040e190b2e03030f092408150a06030e070906090207020907050c0c0904060605061306 69
    0x40c0c4041c0d0b2405007204000d419442c9c180c82e83d0b818bd120394441c0515a4542d2032400110064034643e0200c0d410301d00124010704841240c1001e03084600f1418103d80801d82d02950058a1410500c41c1a20541158003c03214000401082c81082c4150340116031400c508403801d541300341d8035161008000c3d65900340900a9080c580a00c0195050500d0b00c0c415526080900040d200c4404072258440ca94a844100004c2d00612880304481500002d000480c040380c20182050301d800c451000403a004c6540f440303803c0c0d00f0300c4030600c140c440d016809981c55003990340a80340c0d00070780070284d0306020040c036002138003500c1c40150b040c401501c0380a12005500c030210143c00b0741000b03072180c000308402d50094007180c1c03100750048045440c6072801045102c1d000348100c0c242500c68010405403810f001e00494803108540050031142e20940303140b1b8103a81c81d50300807038081c003412800c940a904000501c092500e4000e1000750014080ea4002078500d55510005040d41e10051500f035070b40b6449802006955 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 299925143 1250 299923893 299923907
    0x90506030604120e0a05040207150b06070c14011e0504030506181f0e07080105010317070c1a040909120806090106020c010c11030109150c021906020903010912050a 72
    0x204180e00404242c1000e649003410700d1441040a0304212040050441968413107850000910300034004654914490500b080207201c0c2d0441400c00c0c60510381d00e41c0c03090418000b00c2e81515000303c0e99280042c20015041c42c01c401c0e80181c9810800074400306180200c0c4075069107140c440d00d49445a8440c0b075480c10f1420305400500c3c464042c02d0051070495400404180c0b0b0300c0c502496000c0050b240e440c00a01001416500ca11600c2e0380300342c50010541ca141544240d040c0c0340164020703901000e082c00d00c0001c500c102407000f400380e0003a08080140304a2080080c101c02507002e00d05051644400314907080b07034080c01c1c05032419214017001c04002900600f406400503802d90380341082e981803220107541c5800e51448241000f4404d03200c101440081500000b4541000740281b0064980341030a0f120000c000030214131840ca0408007100503400001e104182c50314180f02c188106e00180c464400a400c1b022960703070155206d4036182c3c0040d22201401c3c0c420038051300c85030384418550000400c10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 299926393 1250 299925143 299925151
    0xa060801290d110108060409052401080303270a0f080703110109080306060d140103031806050301151b050a081e04030503071b0b070614090a17090607150203010905 72
    0x1074200c0303610801c0443e40c05540800891400c0c01c00d100e1646400b0301040c000d0140c8040604517002c1c078807020701424503865001c4003011581320900d40070b90b21440e4403500c0e40300a071040c0001c2111540485001c0d0b0f4004000001120a0310559015000c070340c81b030803403184292804030f5440400107990b8003016008000400c0c140440c100030403245400744d0741c01c1014400540f500d0b01c542d2000c40c500c0c00c1c01c09190403500700d58140321303062482940c1d80d1401034001c00c0308158a43c4070140d0a03101003009442141540e04a82c003c00442c408115006029030307a5001c1d0715140703040078140c1c0d800c1c500404c808005001155114841d801d84e11829105801220804c01e00340c12484d84003004200082400001950700680d041100e0358158400014400d1200c5856403000780b640c03201045580074000385030300080f40c03403046550b00d41307080da5050308031910303080345030801800c0d000300102d81402440e404025001ca60f002a01c42c2d4a815155102e00f88164000744407103490302d0300000180040c0c3c0c4140513580e04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 299927643 1250 299926393 299926399
    0xc110a0b011a1c0b120111120c030f04080a05070614040611040803030c1305090405061e040203031608040f090207050c010c020603011a04120b0702060709120b0a06080129 75
    0x2c1c4180f2900c02c907141903a1503014115941c445400c0f1070341c0c1da1440c1c2c1d52048415003400810138070315156500c50703480d002401c0e0030004032480000034110a90f240101c074803035031600b80028003e0b40c803a0395954098000100403000c100741400003000041862045400f00010492031a141d450301e8034003081542c0c1da852800310b9070b83c4207010411108000005076a04030600d1042d40b52034941a5500303040910056000c198010101070a102c00c1c4040481e1a0780124121904d007081d411890180991120003560000d4159000308035105101e480728880d402541c3c4203580d010f103400d070f0b036601c1e590480485400501000c1d07800901c0ea010002d0802080502034420b0130034040580140d000607000d0b000501c111500d2034084112150030020b03010031103024000303502c4091841c51041c1000c0c0403490b400c649040142c403071400400c00c16801202c10b54100c81c0c5000720b54035070075030660b41d610850401a01902c0500c0d155807012800443c28040c50351010400f1241c01703103012141c8408880d070041045d44c680 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 299928893 1250 299927643 299927647
    0xc0a0b0c0f090d06090602160c051906080702010b040c020705090a0e0c061b03030a29090a02090409050a120f050901020703061e110406030b01180303030c110a0b011a 73
    0x200034a03144282d40210400f00c81c6110200b143c0e08210001e8042c14034020402440000d0120344101000520803005000d01210a03200752100c061003811801304116010f9a01da14404021052249480952001c04e074800070400c40f01500c04102030b201d80c4c0d081c100150308440d01c240000d00f40300d8203003544424600c01c14004201901c05050700d400401d465107000707400c00546c05181c1c0b211800e040ca00401c0d2030040760380c0c234502542c800f801400c650107a0001483e4071910360340341c3c0d20310b0007001c00280350007400c4e01d00d182c07120b00d580402540a0000740d0303000380c0c4605841002c80d000740700218206028452020100c00000c0c1c00400003d0300201c0740c400c4c08024801c00b507443e40e0009044090303c3d848040024500c1c4089800c0c20100341940c4800741080c100b8100f404c09000c400701400c2110a50b44051010158140c01503c1910320030442e010158408101080428801e4109a0100c030b03041c10445141c0550107041800e1030b9515005544030140d110040101d030030702300c0c0100c440072801c41d6268 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 299930143 1250 299928893 299928907
    0x180a020f09100e070507110103020307080a0e0c03060405010b010f0f08012c160e030c0913081b070303140304051e0309040e1609140414030706020c0a0b0c 68
    0x955680d1601880501900148000900000700c0d8140880900001c1d84011814904904000c05c00c1c3d020017001c4540010040071654994007900079a8040c9034030b5201c105a6a861131401e1009000614010410b407041c03061900864509000f040e0180740504004030320f50003803000240c61100c61002c0a01040700a40c0c0d00300b5415440014217064030441ea01c408000e80d54010810001c4201455041c1c0384441c0409200d1503141803503e0310741084441d00d80100c1d07001740c1810540c0320b43c0d034800d805800000d10380004044000c1d0484d54009a4407d0010f9403e00180c826024481462026040741c2940115810300a26030024092040b0070b0b0300c051030a142d4502680c40d9a2994540883c80c580c1000c51640620165018002e0383e40000300a00100a480e044403041a6504003401c030743e0404601000c408940c1c20040d01800c10801d8810b50080410340701d640c0e80c10101058082c04680502052000c80300058250000342184d1790314000400103160300b400c256880020150964501c5142040b0348 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 299931393 1250 299930143 299930149
    0x306010302030a0f05150f0717070903030c05030c0102040618080c010e210f03040e01051c17040e0103060b1c02010f0c170c0d0f090602030d0c03020d0c0503180a02 72
    0xc462466000c41c2400c3c921220b490b00d5403401101c02c40d03e844609480c4104060160a147e01501c5000315607a4180c401042180341c0080c040162400c03400135000d850148003090146180301d4003603120f001103d02d485484074103a4226049034000100064682d44691607040034001d134640504081e8014021069100c000640050001182903014088007402d000000348005031101d6000e8030601641d186a482042d103d407694024024070f01c000320003c0c0040390506005268400c0c0040d01913803c00700090b1903c410151036441c00d41c0c8010540200b00c0807032000c0301071310041d000710302c02d000c0810031014510410a00b42072200341c030340d440c2d042e0308060b0002d0307a40440702502c412103034100b103421450300f4209000364103601d0359240c40084001401d106c56280c005040072901c450381c0d54034400d24104560854002c80c0d01e10600005a00901c080488083d0941c0000300c40a554100149845905003005c4241e4074101c0c62100840c0d004800c10009046d02c11040c001c02500c1c0c000b4000c1a6000d03800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 299932643 1250 299931393 299931403
    0x18120203121801031e060e060112090809061b0d031401081f050903070203031b010c0908070306020912011803030b0f0901090e2b0e0904051905030d0f0515030601030203 74
    0x29143c1096100c1c008900ba8103004900381204001440040c080c070390725074007180002c11003514081d0024002140140d4400030510411455942c82040130f890406d9501c1000741d95007066855030103404100c031411003034a0003048a50340d881c91700d480200d00c00d00a1a9a00c6200c0710592124005400c5000d000c02c00b8190003080d40040c071130703030752000920361128188940345000d00032000b50140320019002c140c4000380d4800b02c0303803109080300078004040f1254003182c244e01580702d804404c0d03000c0b207018000152150050007038404040c4c00207009005c5003559500f0341d1800d181c1702c90b021079100d01100905a05001d0100502c0064501888810703100340031a15004051280c0800d46640fa03030f148450303000601640744441034442181070b01c00410303543c01c040130f010440350f100404c0c40c1c003a4100701400d184058620a54110010745001040c15141030b10000e0403450480702404100700000440f146442400c0305402082400a6180740c02204d0300c0d065207500890903c0383d17010000410040e500019 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 299933893 1250 299932643 299932687
    0x30207150906022e1a0a121e06090c06031401060e0d140c060c0706030f050f060d031707020c010e03070302150a05070b040b04110109150c031812020312 67
    0x390010a6480b19502c0080d00c841009880d03105604108140100b217101102d50460143c1c1281d4084e105580d81c03480705540460901c0013005e15024203104c103091165a400e42c09914003c0c0d038040380480040c0c0d44d0648902040d0000b002080d0341c2e000800c000380210070700e0f40c09011981841c404201426000a07407486542000070001c014110503189221024002646244805020f0f940c5035068103040a889070014098440002d01c0c0c007880d1003c071056070043c140a00001d16400078030381c035400f080c01903400f03200405a062100e52090069602040700b11035100d04e205501401840409500040c410512015414820f0740301400500c090303901e0400c44000c1c0411101c0056540341da52000b9034517401100d0b400307004090510100014007103080c45080c499407060301d04210051115005484008182c0240d004c460109201e01d0000d60017400341d40221f6000c0d00309143d42d10900c1d4542d0403100180d070801c00300110800165800c6080c2041a03401541303942e00341e58100342c00500601c00d0104504 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 299935143 1250 299933893 299933923
    0x6030c071103010612020102120a0915031e0b040b09091c1b030207050406090513060c0201110c0a030206010f081506010c02040c0201092906090c120403020715090602 73
    0x28658041241809289041000142c0240100d5580302c1002441d1100840b0076400350080410140081c80400202c0d4145941500e54440440c00c0021884800020801000506554600d62030300c2d020484c840c1c07030784048003c83c04180e160982c000d00c02034409801d8260b008178030640a110b03480318041410f018000f030300c1c000c5400403011050202c44850340c41152005903d19241281c0906501044c81000d440e025213003800420741d9424590103c0303031b084400da41c110004448240000d0f446400032503901242d2b20011039142c000016040c02580a90304031907466200000702000c140d0140047c1d40105005035400e07000c0307840c24071801d0315805440924218010a0030000304141e0107000c0c500c1e40d09401074003c00030709130b1060010303000b0001c905083d12003c4c02421284610034070380b0181e00001d00d045010b1012621aa42404034150019040c4402c40c041400713407020350500301c0341130f0344154002d6005190652411041c000c0c09000f440f203880402c82040000d04c9070360f0300007c0c1d4a200325114 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 299936393 1250 299935143 299935147
    0xa03020f060c070b040303020609011104080a1103030912010501090b06090607030c170a1205010b0c071e09050c030712150324060b27010f120b030304230f06030c 71
    0x860b241c00d0042a8114104268000c5000b10506500084980c401e00c100b1001b01f02d07001c41d11480301003038000e501c80c84032660b0240d91104000380742104603140b4904007804890800c2e4000700002c42c500c908210340b10690390f5a400400002010b8020461600425030300c0601c0c041d8104003059240c450150701a00b4850300d0101d560402102031440a105a05125460344520a03c000140000e00303540007000580d09180004c5220010641110b07000821000103004161a003003401011009010040118200c40040050034101e1801654411035954080c26a2441e101c5030141805040c8485400090310f07205420120141400c1d00d54140c070740040d0301101ca030411380400032000104148d944511403e200001031b054240c1c50243c801110401540c0c5100041c8034214610b880164a1480c0042c2401244550040c00780002142c201c211000c0414010754941c0464a142d10940c4000b00c8102890301c00f400c40c011020140c6207400040364105d040000000004c2c000b800050254100b140d00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 299937643 1250 299936393 299936407
    0x10504031403090d03030903080601020c01120c0c0f05030a0909090803010608091f0506101409010c020a09050405030306040608210a02010905060103050c03121c0b06040e0f090c0a03020f06 83
    0x7003001562201c00b00104500f54400c0a4a40100079244080c4224081446040420519030001c114107030302c000113a546560301007480040b18003511b44c48681400303010006103540b011500704a40700c10000d0280004607074510408200501e4051540c0c030041450740b03400d1245001903c200201c0781102d03580c0c41d09481640720b0103a410704061030a001c000a100405070281c2003050160085031060030101e07155600c0a60221080e2852840c080100d9501c0303400300b0000d001d9600a0744d015200c9400030b400d055400b070702c030340080040780da0583d001e5071540d00100070401d40349000d00038a0050190100039011800811049400911902c0e05032a52401c0c045102c800ea203100b5402980d0007032b04201143e07483e5940c1c1c20029204d14456111a000340218500384403400400700823100f285444032005001d0000b0804020010a0b000740003517807000e400c01000413640040310070b035402940c035000d1080442c1011605180b520340340500d22030050840500c200050f07550304010140035082691955030b1240 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 299938893 1250 299937643 299937683
    0x60a0b07120e0d12091706060405040f0b180105100302030a02130f0207230a0506010e06061c0b040e06060d0605090709020a081e0f04060207140d03021e070201050403 73
    0x3000107507583e0004920140300040c840c020313591030310054840c0c40703150360300392201288940c2103074039960402070b40d01c40741c007090039810180e100561142c020018a10000041d50300c00e42c8095050b42d40d0301d200342c0c02194000031032400703121b12a0881c60710000c0704469459503000c01c1c2c4641e032015019200c0c4003d03045141e02d14206402c54840b00c81c001000b15500c00c07982ca410000d010b0320245400321000c0c1403207a2060b640c1d001071004011600040100350356803030000d1201d2418002070415400c0b182c10308c844c00d5281d090b00f030743c1c04950b0344076200450050000800c1c441100c14070100007220361300400500030300d40c4440d8071103950923810140202e45070b61915195072808a03142c2c40001181c0c80010701c0255945c0c8840c52501a464134041100401c5504058084401068441c0d1010b00010b10101e000605e6907030003031104a20410071401c0e91411000c13a0750030025265880d002290b000140c40c010107202210944e0707206c60745041c00e4142800d40e00020000c1c050350000520070452081c4059647d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 299940143 1250 299938893 299938907
    0xa06090606020109030201060e010e0f0a0902060711031c08070f050f130f0f0e0c2a0303070f031a01030c05160c050f180420190e060a0b0712 62
    0x1000500a0150315903a59000f4000c0240c2e501c10360040d40b80c02004240c0070107804007203041302d40c4000c0c60032054480c11169a1f1b03690001e8440a610359841c110540143c50391302c05070200d01d0003050750001d014010310130326041200781043c0852410b5107992b1045201d402580190b0480245e140c003105004541900707807820f10410b2a18040c41001040080c042944100340c4820b9070202100c420f80301359601c2c48a6a041d825000b02c3c1c3e042650900081d0400f1100805455110101c0302b0031000c00005010348128030a000404040703e810001c10400d00640190461062041324070f42008290800c0603c042020341c0b10100f641096124101c1085c10b610a07010344000003512180c0000b80040f0b890803098900c0b840c072034640111610039140600d8039012240e01003d1603176420880241d601c590b03403095420804038609858644400e0744589130307104c1e2507000204264075440d450f1568104881d001c41003000800c000d00c180d50101c2e06201161018040e5031030150300110741c52413604484410340e884 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 299941393 1250 299940143 299940149
    0x20307020d11150432060109021606020a020d0e010906021c02070b0c0c01090f060e01120e01020403030c05060f0c040611070b0315100504050a0e0a09140a0c0602070e040b0a06 77
    0x824041000d10041c00200348a1a0303030145480c070102100b1100d600c054642001015170040507410603c0100102c006a4000302201c15811400c00341114943e926a8100d030000c240c000c0050340701111100d042074100d41c284240300400d080903000c4506e0000002c3d9a50082c0600e106106c2c5440051480d56008100001c060241546919110341481d01c204e6551910b034044180001d41040d8001001c0403141c0004042d5103e07661b0fa40000f4000303d00540e2080091209195020342c0d41d03241c441203103020320240024611070354803e1105001410f01c280303030040151100c00c1c11030040040c801100588030440c3c08552483c20050400701b0121511810811039501c222074002e000030401440003031480c001484400c1c200c41559241c91548070480d40c60040340039103500210b84940900480040d180000c0e07100c0ea0210000c00d00e00311700c2d510184040001a4075060641c00217501400700540d884400d80680708610041000070300d0907400f246072000c0a0000341c1056080008140c0c3d000443d0000009 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 299942643 1250 299941393 299941423
    0x206090303070302150a0c090b07020a0b0310030c1d010e0a02040f0314010c030615120b0a0306050105031212041104090b0103050d020708030708070201140d0906050604050a020307020d11 82
    0x25500c40b0f080281d1100ca02c03070444044119908005413515625104000d800e640d25914012050b0034824078980707607440344400343d9008049483c0020622610342c0110300c1384810080e0710049500e10302e00f820100070300e07400c00e00424a03c00d210390b103554007411110381100c3d010102c0c2202620f40050034002481940c00040080940039004400d0001e0b052200074000680002080411021007046040383d0030303401448035007004031100c00c1c01e00f44074030b106600c1c004044c1d0f0001403035280c2d240010b00741456a84100c0341962508010403142ca03060080000328001e0660300c3e441c10324080b1502c0e02c40381c0b00801c018007111200301a10259142d83d0312500c0501d074020b240121ba56142c0c14910765a500980c5035a00520a9010100304190040190340070303241d00000031405e100e00c0e40d00540e2039510841d0006050807090101c43c0d20b01a1074080c1b843c4042c028400068541001c1c0c00381b00540d40000e00007800140100107100e85664000f900c0101d04042e40b400000c000713040f41d82c0741d003449998680e040c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 299943893 1250 299942643 299942647
    0x3120402210d031e0b0109140111010e060405071205150c04030f0b0a06090e0a15020906041d0114090a151508010e060d020d11030c121506010e030d0302070206090303 73
    0x8400c80d0190b01080e044021804d02c6003018000740502001d5668404000e800122000000c200700412500600a03200c014100b03080304d0484000e01030300b12402030f68104c03a540d0010052009004c02070040c3c00c05080c05070f103000d0110a068032a141c1d00c5109200c0ca90724061118006014400c012041c1c8000d190b0180c07541200c0d40040c100300c0f10080b0181c4825011919082d0006022241482a2081c142034000604103003040380d11915414006c0440054160380c0822442001d07071b41d104014406401d040c12400f0b1013204451700001d072840140c000c0d0527009141c3c4882209a55078916065000d2400880401c0c605201c10360326282d003900b41c0c4081c8400a22a004607481a0003000701810790348014401003807a074826040021080108201a40003022004441c003ca484010310744600b04001e0700f1940c00c0002c28000c586120004852a030302c0b50840070b0030343d000304082682950006005d2a001000a003d980020346030300912002c40c0c241680019038200315101d031410b03151031080040a5917 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 299945143 1250 299943893 299943913
    0x406031203090c0509130b04050a020901060504030303051b0313111302090f1005090603101d0405060a05010812070203070f0e2205071403030706060303030219020312040221 76
    0x7401500e8420710449242d43d02160106072424000e00c060f100341c120700c0310102002015203c0b5800030301c01400c2924a8000c0b41829000342c0c869250341c038003c001a656a599031899810300400316a4080d001000342d011181c802c81040700f509060700e80040710303d5030700300c50b400144c544010070842d44541b40d9001100c80c0e0300141c8040c00341d405000c9940c81130340e00c040121980c004001da440c42c0c3d41c8100300030420501c01c0304a5404c1c00005942d001b8100303c41c24000b261180082c8104040e00400e51504943d940f0070001040410300065801c1140c03c40148815418120b249440d0301c408841460316410106500095503810080c0500070200420141000351300d98521117410081119442c81031043c001c0c400d421110a145120380c4660003034084d0048600b030002d18800101b0101c2c0240d4103100601410021900034400d00005501c40c2e00c0041c1c0d40c1480c221074070728450760642584155002400400c001e0101d40c039450f40e100c0e81c11140e0105a400f00b0b0b5000c81300001c2c0d10802c0320b082c4102c580310 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 299946393 1250 299945143 299945147
    0x30a1506050f0103060b030109020304080d0f0c09060305160f0314010f051f0933030c020c030d170604021b01050106030605120a0f050c060706090b0108011b08040204060312 76
    0xc141600c80a541c2030154a100a00640903a40c451003a0700342030100300010000c614540d07001e5904544203a02c210725001d9a064032006031004120400350260740c402c4042406a000043e003401460142400d004a1801d21700c0c1403c40c3c0d08041255043c0141c11f086188054841d50102e402003404018007041541c46095542da0724405001d03450040d065041484042040c00000141011f0542e80c5c1132083d905004000700000300540542490030755001b142082096007408100c0115140e40c0c0008209a0014000785084900390036640241c210880c0764002c280e102d82c85da4101e9015044620131500d43d500410700038451950000301d5001040c100c14001c01043d0800e03412211141e90510075184c840d42003041c58001c003c4030050650080380b020700050350540305c00c103a40740188281c03039403c0300407004112543e0061100300c82036a62200100c2c2006101030115014181d0714008000000100c44002c00d00e00b140e4055005029501000808558030f540101020b076621441c0d84070360803204840 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 299947643 1250 299946393 299946401
    0x408011401090c02010213151b08030901050a0605010c02040522080703180f1e0e1005090c0a050306150f18090702010e030d11040306020a020a050f07030c060e030a15 73
    0xa02c4502802c000d52514640d00c1402610460901c101e81140c0c00361074070f00c54001c81584c1115050030b0040101202c5112200c040242405a00410183d0341d070b4030342a0704403402c480000f01148034841c070304002441780d40d90110107000350170381c19030b00041e054076220085100900c00c441341d0080700002864140400440d80054803086204c3d803158503003038084500204001007203024200391041e000d00d08100b512448611b900e81003003a0281042d41584a0b00d8030000d1010440d00020a010401030400103070800308001d0345d0011042d1003150401400c0c2400130b0040c4805001c4511400511009040c4249110111100c0c101c0b20f458155440b0b00c0304030803010500400c0101440742c00c075000003400175401809500c46006103c000b851610100210030310080110504c041d4036180180804400981e541c80284405001e40d0020220350300349141c043c1c0741c08003648010070b00340c01680080002407200c5684206681c1d250400811540405011031b01e03100c1500009092101440c2ca00b01c106561588 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 299948893 1250 299947643 299947649
    0x909010801021210030b04020603221412040b040e070242130305030a060902040305010609061d040b06121c0f090e01050d050114150f10080f0403050408011401 70
    0x9052483c50382d40007000e04205080780710241c10040c00d0310000b00185000002035a0100321560b960385008504041a16180145a0100d03401c040c0c40380303162520ba00c02c2100c0d50110400d140382616150500d1a100307540d019604c00c4034101c14038103010440f000d0084c800d0180180781c000320030510140c0408004682c516181c1983e10382c8903240e0351a540f12030010030181c424107020000e001c20391115a412500d641c801070207030309620340c0c502012448005c02d00040005600900010400c1403e20304440100e0f551540040075031040303e4450380f5202c4400381e50303075486030300480c0c00201643c03800081005900c04926001190003841c4190312014003c5036000c4100416540e0701d080c6600740d20040c1d980700000e000e00c42541100c0e1004022924204140202540c03080d400403820b100c0c255544950b031181510014624103950304184801c0c104181c2500704290200c400c011030121050002e402e40c88084c0210103144403190010b0280b500500442e0f00130100711000f01300b88444084000c0e90381d00280 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 299950143 1250 299948893 299948917
    0x81c020f0d05030412090e070e041b05030103051b1003180606170f010506011d0303070813060e0607020d0b1f0b090f030a170a02072102030c09041e08090901080102 72
    0x2141741c42080c482c80100e4150b03454402c0c03241d040d8491030001c1e02c507040701110b02544152030344062651b50642032950b0000d110141c4646449504615101e81040d104003a0901c03107a80a010380c4a940e80c403041d405001c80050f090020b07600d800000c0380c01c8070394001800a8103c9003032020000e214070b07070003126100c02d01c0c2c3c280584100c1003052158a09132982515182d0015070303120a5092450504e085152448c000202268582416541c0b50011034100342111900188038480070402540c02c130014000840040341c50740e10381004c5900003141d40100b80f02c042c1c20215010b0000c0d041050460003840c440740c040c0c6440900a80d07a980e030100c3c581c01040680e02410300110356528506000130f0621002d5400075400b401507044c4404600c840c3c000280c80e03011485003601c001143e121407082d9030f200220308070154121000ca40141071070041c05002441c080d10002042201141c0c441861003c00030b84c0d918070303141c28035450411712068040c101045a00c940b080d40005201c00e015030061401c06692 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 299951393 1250 299950143 299950163
    0x110a0e030118170d0b0d0c0f0f030206030403051b010e030901031505060d09031e030518030a020d080c0705060f0103031707080601080601050c011a09010906081c020f0d050304 77
    0x8902c0701c07903031140c080d00b000700b0000c19040c980b115092980042d00780c0f01444900000c1c1901c0c4500010b62110031440160780170b2140d40c0c0c06104191a0040d21809084051010000030b1302d15800b15045100040010f0100000072a060b920050b03030071545110b1038041c000a01c071164003403803210b849030b003c1681603020928002d851220082c100b65084115000109814203242c04160300801404602c0d408904100829854160110240159a44100060b40c0006851401409507032071040341000034a540d07401440f0b41890340d540010754a881c1040352030003c5843e195140d4041e003a0140c441c0c01069401078608001d440c412100032641281e010751340c3c403404802c29400724066000160361040000d56050f00040032540941c09240e000241854605d1800b400b108115003101e40341442d00b4489800c2c40810002403405070080343c09001c025100304003ca00d04203c16607a8030701c045000342c1c030503814411403000c14000d010b109040584801660b0b01a0383c0c07000300919a50040300e00f120141c2c3d01d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 299952643 1250 299951393 299951411
    0x7030f06060903051c03090c120201030b1c020409050c03070303080901060b12010b090a0f030b09010e3d050907060f0311030606030912300402090c0d110a0e0301 71
    0x22a07800c0e4000c59812101504194020001e1740c40d9a10391010002d040c16140d40501c0d0009040a400d44010040c400d860380386d4520500c0010261002d8202a0b440b4511280c01c042101071940101c00d01c00c0e030f04480003c0c03042c11324a0450b090150200c0b0196050207001000414150070111440c441c443c004000c200e440d403a46680f24040c040c010b0300c803416610300340c01880761007101001401d20040c002e01358002c40c2d0b03444001e41c03040c6003150000c07a0789422200030f120340030009002b28a09054548041c1040e23000b03266520044003c10051030981d10b0f21a480c40182011519501003411940007062201d464200d2540f07540c1c05142c450480042c1c1004001c41280b44284a07092030401081c039094034649032603041040a40010301200c209000307107040d01051381032003001403601c2d030301003106d10092104110407886000134090004145040d09002c0000696a01d66035035840110034a460380c0714004082603c008000c4090089542200012049540c5401c40b500d40c2c881d0f54110020b01c000d20f4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 299953893 1250 299952643 299952647
    0x30903070b01080a2f1309120903020f010e0121060303080a06081504080c0708070501090e0c03161709060a230604020a0e0402040905090105060102030304050d180b0307030f0606 78
    0x2560601610860380402c00c8911640392105c0841500d40c8020710100420700c1000240301c07580c407903140120081c0d0780c8101c4010407044654400b10217015081120141c2e02d160003041d84100401001e80c100070b41c0c100c0e040794907806034450070000c481881181c18518000c3d01e034040105184c0c0420b43c0420000c0740041c00c028030500a240544003120003500c0091443d80c6005000480540102c60300c1d8020b11603107846134010490b51005007089030050541a1410001500038035094110346800d0b4611400c200d82c00c001c0e04100c0743c10050010848560044405080703450052031024006c10ba44041d09210a91000040d0f00b4061720300c2140411030103140b02000c038012101280480c614114107000100c8a00d00343d405050614001e050000300c1c0c941402c000740883c0c0c05034001d41010382d515001e00c0074080007446290342c010f03006c2c0011172550801e5210103558140440346441005441e010f03000c030116420500360010001d000300d594881c01c044101030041d01400c2a08001c03e40b503c20005140340c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 299955143 1250 299953893 299953903
    0x180f0114151806040e070e0406050d02030a080901030e0d020d020d03180213061a07140105010b04090f0f0e0109052a04051e040515090309090f040204060308030903070b0108 76
    0x1207426072030301d440c0844410081c0e0507807a0507850300c1c1d882402840002224401400e40300c1c400c00d034690360b140104601d6020441211000d8210740c0c000e4251030012001030300c000503a22116504903001a0700e0701c00000040b4003811218113107032014000d003400700c650184c00240c1401c120400b5000d80303210003072202044080700e48032540c4031164061241040301505181550580803010310101003100e41d02c03070010080044c1d40c1030140c1540d600010300d40301442407249102d4a449181c0000740072a5152400c05181ca014070b000d40d0b61135564031801984000500d5128014418088d041803160400c4005400e0080481110640300d5000d6101d02020641e0342c0c0d903100812442681c07501c001120264188001488002d0590007110301c480d0340070b651310613440c000c0c40c809c84c8558000c100d00000d1641040e0301034400781174401117920510401030160f444e550aa41d1260380c5104c00000e075540c0d13000080150186620283c031800c0c000040c01100c89000c40140009402914034010503603031110340311b69071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 299956393 1250 299955143 299955169
    0xa0b0403020c09100902310602060105030607080c0d020702040c050405011e14090418081c0c021b180c210411040504050715030606110313050103020306180f0114 71
    0x140e40b1314090080340b02035405443d40f106800d080c0d00040c00303000d540010040b0791541c2c02c0610b0401d00303c2002590b034100200f40c050f010907030151609050800d0003030403003d00a01202c1d460480401c418803d120a54150740341250010820310030118071903009465030307000d4000c0d0703800a18295044000103980d40b4a00c0044c0d1410380c1c070800b0345c5c1e80d040800c0c5100e400c42144541e1054640003084134002d0034060075807074240520030080c1d41300d440b909524403010bc000341070015981030007a6409469004107210240d1211000c0038080490000006220120380344042900f04004500340015201e51001078140c81b64403071850729202030303064940d407198481203038001c0040550102a50444c01c00d9007080da003013803042c42140e0440d6214610400c15280d00100980040d640300720811455610580d0400c5e04c401c030b14040e5142001c0b050007070312006030a004041c103044c0c000000c03901507120041e20ba105503081c0714812031282420b01b84003107003a1083c4107650754040b83e00c6040503289803c907501c401c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 299957643 1250 299956393 299956411
    0xc0f08190201030f0b0d0501050717070f0507082512090b0304060f06030b070806010201051302090612030d0c02010e0708191205041706090d020c01020a060e030c0a0b0403020c09 78
    0x100d04860750045015107442a140401e150315001d000d91a615502c0c01064604e1140001084500e04940000d00c0400c8110100e8803201c4c06c001840080b5402420324805440c49103842e03550340a0394244240341d0310644150603002d0701101ca8500500c0f00d02c8001c00400c0380b092503042003611004030200ca145059000d10381050303c08001080001d40c1d00e901120151450900c041540d6583e0b89910110003021106100807234140001c1094569081c419030341e124000c44a868444602a00803500411008120038095260590014020003003002643c05068142d00d00f4894070140e004001d002e4001000c200003a40b14441c8082010f00010070440651038240c540342c0008689601c0381804e0050044082007849030810000c144405c03c40e1001000302e9103400108818185102d00300e00e0700c002090074008540101000305407580e40403940000700c03500114045011250186510b045104090080b6014400c13105c1030000c200c9060545485913000e5003e6034014803800041c000e60400841d10409 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 299958893 1250 299957643 299957683
    0x120c0a050c12030d0f11040b03010e06030d0c0b060f1507060501090612020d1b030c1503090b060112150e041509020d060c0507020d06050610051201060309080c0105040c0f08 76
    0x26903200c4c0742d030040c0d401c504c00c03000c0803079844160720b121001a031060b0482e90380f1500000062040503002d039800d80c4c200b00e050b001002c1021140200900040e05035900400d0b851808000c54102d5448046c0a108074100400400d00420314003145805030740840000c07582e960400c800010515014800c4004031610014108003500c0c655080146c4200070b01da0444482441d98141a07400005010100156200c0d04014101504094145540b080742141100c1018140b020160000b10744800c01504484203091032030708403000f01903080c0a4842d20510102e502c0c20310a0004020003604c4202d0f0242c2c2c0204c26a402901c424a044000e5030003a110280d080b0008031200700004106138400700c440c140510b40b1070b06000041d4002510b11403081c0054440319100d4080c41041e1805402c900f0f489112030402c40d2a101200d07004411000052051070b042c1591041483c06020040045482178240b4034020440c070710f0980780100c840e2203a402070030302c06400194080782e5000002905c9000c00600c4402503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 299960143 1250 299958893 299958907
    0x6010f08121612020a060609020301061710050f040b06070f0209100e0402010f030e0610090501080106060e040903020f030c010203070201180f060e0f01062306070c0603020c120c0a050c1203 83
    0x301a46007850030443c00c51151141c0800491254401d0b00d014007006140940c5e6035151445c020007050300481500c0d0317891220024000d641c01c0f4841460b04981096540e07465070560704c0002001000311464040d041320300050800b040042035104c04c00c03030501c2101c0c84c2c180c0c0c0e1a144076404009801e8000c04810a4843c3c01040143d03000e451460341c1c0341c001d481c020491211440c4107908003130741541c1156055640c80000d0107007500500880e405000807400810a9500e04500204240000400301d400795540300d4400c014544244904201c810844007202e6480c2c80700d079420f90007580201c07a190015480c208005600220080300c04900ca50030500450392090240c440724000c00181c00c0c3d15115208000c60850100001e014010013420b0092104401c501880014613240f401c90304003600c990400c00c41900002c001c50092403e480e510f10300162503a5190703903500c1c50460403c03410380b034450000c01c40d1240c1910000c0c074284040e10800550b03a51050704801d21050000f0180083c440d50070a100351 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 299961393 1250 299960143 299960153
    0x1b04080d08041b03030c0b010b03090a1106040308032d040201080403030e0726070b0c07060c030509040203040c0306180507060f090506030114010f0207080d0302030a0e06010f081216 80
    0x8590042c3c02140d03070000c1c802c000491000042a2644210007145510000d441400742e03001420340100b0f08503108914502e02920b8554603001061001032800c4201000e0000e1500d034407003698003455002801598904104020380c0c42002440800e440c251044c16a20341c004071480450390003960706842d41c1c5440e468980d0240c010b803034070560070111841035480004608400d55520365003006401c2503211100c01d0780c0c64040c02c1200b141c12503070b840c035010850031140e03030000201c0c4e804885c210b1070000120b44180c0350032501f80c40750312092036001c1c1c004401d12042c044090300c180222889032504200c080d8003941d50400701000d441000d81241c10403c4200005030007212031083d003030002d280030b82c0230035298400580d083e0000e07040035400d00043c141c5d80c62196040304111000001c0c0d4001050058038000f00150b6503181c010340e81c3c1c20150044007180c0014241e4004004081c0554169404c660b154928040001010302c2141054072500c8000d1055031000c0c001c85a108940503a80c01070484c040d210 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 299962643 1250 299961393 299961407
    0x3101107080739060306050303191101020c03090f030c010801090e031c02030f0f0408180f1008100f0f0e04110a060c02130221061c030302031b04080d 66
    0x81610300000e100822246241d48203001021043c0044003d03542c2814000b4401c0e252260740c01110905141a8081c080c6650000030381d15048462851000322400c1010101c07444c130300d5010312904940c000f20346088a008048050024001d003540c82d103000b04649070805a44440c4100c1c1a4045201d20f00144145501d85d000203c00300ca0b0001260310b0404200d4403012089241094a9920740d404020311000c104540d607441e800c8007440131090011b08050304c0d42e204510640700090001402c611041031f00e603c0c1ca2a000d500e9500c014100d40c01c0b9606504080d1100c8c6003250401c03e03a00000c0d901249031340100310701006440007000314044090401040c4c4204140203481540c05542d05090141c0d00e50385c03180160080c0096542d109080303042d42c0705004000c1e698801c1c41620b28014080201684032070703803041c0c03418074940492070714503110080880c840c02141c01140d00c0003486c460010003455010780056000d400e80c42c3c148440110500a203040f00e0260740030f001c00d941c2009455286143c81416 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 299963893 1250 299962643 299962657
    0x9010c03111212160c210201090803040f0303060609060903020d05030904241d060d1506090605030705060a39060e0c1e0d0515090106050310110708 65
    0x411a40d9814203160841c000d90041550f0302203014070301c0304005134071440043c075000385802418034007807080c01991038217001c0c150f0300f2100b5020503031104411491172003500186a0311790010380f06513032805c2504060044801c031060940109050800c0001d8051181e032850080304c0803aa02c080440d4155401c008520103008030a4031140301c14041c950899650b845200340110a010a4088034007903c04074510f0104903900942c6e214070145076000e00d0f0008801c0856111008270303540b0154260380d2a180c91802a0300140800152400e0000f0842030641d501041c1620f4085080350706890392075040010074401d101e01c81c40007d51000c3c445500d100000c64680c8945810300521503e440388a0500d0101da07905034080c0d5606840d00c2c0d0300c0c10030703080c103010610f00d401058580e081504012000c1c125505216249180500345441d0301c0000d0240601009060850130095900582413040e500741c0685190301a0300c0c070901921640f60201402441044114082c160406080881c0d640324405680c200c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 299965143 1250 299963893 299963927
    0x180b060409080c030f071e03140708070b0709170a121b06111305010c111c47071202120703060e1506031501030204051e130209010c03 59
    0x40700104010300c2c03c2c809030045c01c00f4044500e850380420306010710306a5a800724010500c064050100109520030012440d02460041081d0340d0700d120318142055205400f809405292107800b400483c90b032002c95081269182c030080e01560302100591601d50281402c014286103d80140300c0700503000e84546022442c1c80301100b200420740740c48150580c1c140c8a445502090009401c00c1c0800d090106480500303828a407064451025a9440b00c04650303401c501c6104d00c411184003030304800100c40601c80c040d404055611080b400140c2c0100346002d81120400c541c1454840d02c2d1001e40652100d4104000000c0c50b000e0b5440d401810b81b08880145000071080da0200115184a9088038286020307031031694001640074900303011500404400fa128681c040c2d05040400159955902075a401651502003902440c11110041e4000c0c85540d0001c0d0300131302062426400003d502500c2c41c410502a500580c100c014a40000c0891103800c1443d40492001c07610040803c0c40f0304040e0200c0300b500b07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 299966393 1250 299965143 299965147
    0x5070f021909090303050c2104060f090506040209090a03230d020408060601020d110a02090a06090c021c174c080105040314070609020904080706180b06040908 70
    0x30441021003010300d508660403850322009083c08040d07042c071400e03904c0145090315500f42500400d1111045007409582ca00b414a60804034041c411160712040d0762040b0404100240f003220324180d925000c04071800d03072180c1e001c140090305007403000c0f0382042155410740d0f9011450400307106030b542c07040c4000450089a80c1c207121128010603188024005170007108003c0c00146040b1000900e8a00000ca05d4001c010040c0c0e0180c804000000d1480303099070341124030010603620048100c004182582c040c01169081503da82c01f0281c01103101c40c2e81103640c990014005040e40c01c00d64010340c820042d046000c3c10400060540c0380d6185000081c0300b0441e88510380c10201e070341c03208000048000c100226580c420b402c0c0942580440d9100300502c1440001d20480c6015180585400092811110000000a425000c214846c3d0041d9003003a401081c890560901c2c0c180281c03da08000d00031990305180c200c00508565450070820191a4846038281d410b03555801480040c0082c4902150400d0003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 299967643 1250 299966393 299966419
    0x9090f0206130e13020f010e090c0c0316060b090a09020f010c0312050708060a05031c08040302120c0d08010e100902180a08100615050304120509031e0f0102040605070f02 75
    0x81c0e0300340f64000c0940031140c000094950042144440012092a05226240201440980340d8150603948907001c81c3d5640d03100c0030741014007411403142d1030071311400e081030f19200f0003006080c1e230001c1c68104e070581c0c2600d91640c1d56000c0c0340c110b4a002c100a50320056800c200c008540c03003044640040352003403400d08500080c844550050300d005844044c04103120744200844c03400c001d00c800004100840041407200a510b070211440080484680200264000041c0605000704003480185064400032940c035030141400ca615582c0d00d40050001850140c000540c40c03d0ba201e820303000f88503550440035124079200401340294403440700d4981d051040c1140098070b642d4842858001c0c0900c00190001c400700181060440309142c00c40651004032449030280c1a5010b400d499000d03a000040345100341d10300d00180e0705130260b411255414412944a0380c40710b640d0700d0000340c072644410f04031028105503145060a07030003103009010000e01c0500002c0c010851500e205202c040c0040c243d1403484903 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 299968893 1250 299967643 299967659
    0xd0201030908030f0406051e01050f0a051009050301151d0703180506041109161824030b0f2206030803070f090510091502010608100605010909090f020613 68
    0x4100c138406210740301e48003000240b16075070041c070f40c1c170959200c1000c0e05084441c00300c0040ca00107000d180e00400008040480c0f035154840d92002805d030040140ca6603401d1030713200400511083c003507140254280821031107020700c0c03000c1e508240d40003c16406103014081807141c95800004012300101a00ca14501421503e23007400d8240a0b40030358080d01070352511742000d01c2e0784121002150701036190041005451151a645003d2615480c603002e8942c0710000c2c00c85817801310303a40000404640e00d0038441d0402c010381c89200041031181d1420303c8194940d200300a00f4035956007026030000100d00800c2512990808206a640d03400c0c440058495200d84030402c040e003040303540001084045151804a03a04400400c0c0204000c03a542104030304402d600902080359403064404003103803d150062a40d0007900b20001924200c400c4612401940c00d4400242c566486202e0110300a072802090901050140303140b0190031510400030420580d083c00006c0c0d208072104504100841c0001c2007501e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 299970143 1250 299968893 299968897
    0xb01090906080c09130f1e06050f040317070206070e0a0e040c050a23010e0301090605070807120e0616021504151109030a08090d2102190807020d0201030908 69
    0xb1002e900101040e0055000344842c151024044020040240d030560300000d81c4904075100c2c81d80d004511030391340782c12000c1c11801b8214100c0010a03403824201008242540f0b99041480381f0302035580d92030114550300c840c0c5a01307501502c901c0c0041e00301400107010039000700c2e01c085013081c2c05040d80d10300036600c20110031b0080d000e0350112448982e40e4400c01c03141c94400d000d07101030a564a0712051030702c00741c421070b4112444041a10b05001d4900c83c072b18400d58080d441220200c0d08000148024504404010103111040381d001000c28a0b5881c41d040321032483c80b444544a10b410010300d100e4640c11100f9111001c00188001140710b02c0140e0845070022a444a00442c07041c000d0f0010101d60071581000c3e203801d03410401d144601840742c1122540c0c002400880c10f6080340002d941c0d0790300c4c0d20210305024403c49016100711000e8024000d420916002c83c41c180c074840d801d44145103044510380514441915000c0c01122052113200007510382000503607011031050600140c40c4460382c1c0c0303400c059 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 299971393 1250 299970143 299970149
    0x209100b0706020c060c0408060106031515090e0c04122612060a050609010c2010121b0903060c051608130803090a0b07060f15080f0a02090a0b01090906 67
    0x103600441d09500384c01c0201700305070f0400400e001c880d04080c00e10404a507500c505100d200101074994607100f044050700c4644030301400038440c540120494070040070701002e40c68410540e503420113038000b0b41c00200c601c1c240c80a880754050b124081220540b2040d42d282d8400c10a13001842078580310389407107400359006022280907084c4807240d5180c203200b042a8a10140e00103800740100b0032140300160390100701218034591107201c900002c203450300f00040c003029030507015820a030041e0100d0100c0e5003100703c8140d07281c0c20141c1801542852070250400c840791007407035400703c1c06d0b1010510000d030304d41e00021414040ea00d019401c1403401161605c036a10f410b04159400c1300700080104050300100d40715009096038000031071400c1c1e00c4002148000b42d0b284500321040c00d002c500d01e0700300180354103d2044101260802e101200c1005480d03448084148038061261050b01d440c6041c03c1c00100380c2c0101301c0d030010a0b1007255584c00d034103030300034000586a0604000d01c022011445140c0b5105640207 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 299972643 1250 299971393 299971403
    0x303030f091002070819020a02031902040b03010603080306090703020702030115080d080606090d060204030204050f10080d02100207022205070e010504080d05092e030506010c050a0209100b07 84
    0x6400c191400c80d00706961140b14a5255004118620104498204032104180c54007245c3d03007040800c0c1c00032401c1145200700290f0600511400641450061042d104118000c440400241c0342c400101400c13030301c0f584002002041c00348002903203854000385003079200c00c0b82d080240c90300b00140d000030708503440c127001602c0200164206108813001080045005869400d29254a04240340001d4150151a1050b0f00c900048124101000540c1c2c060300c00544c1d018009201c2401c0c0702039422041c130000c40c0d5903d08043c000d940007070b04038800900c550001695801030641040d552044038080d60103218182c4e040007002c07a0303840c2281003804080d00142500900000c80b800c001600a0586c68010200340c100001448140050f49022070904038500d0a420865a80e11200780851a011141c8030740900c0110b60407400e080c40c45211313140709010445954100030556072400190b030407030b007200c901420303a0b44011101001400e0614006400c2080700190604030390391080c25080c9036100d81e40842e1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 299973893 1250 299972643 299972671
    0x1801080307110301050402090f060d05031810050304031b1a04030e0907030b0f0d1b03060f0609022110080f03040503070e0103210c0606060c1719050306040b030303 72
    0x410b00550100420524a04030001e00050401d6000500041d0300504901103020b48803010400640d0b03050003031181c0c40e40c0702d01581c0d100ca41d002c40c658021101085007d0190141104011410b1b2040342124410740d8103450380f012103d50000200312030304034801c08441c14003105a00300200041405800c0c8254880d940300e8240c010035000b4008c0443c07004e0410818142007003054071903680c07518580400f6080a480702c00c610350350741c00e14580c1c04030409406a25450106000b0091007030740d03080354040502204091002c1d5030b662640604034492109901d40f902c0a000c02c1c041c5030300a5082043d0412015074803024442c0d1151022404c080300384001c01c400d135000140401050030140300c1c2c807001305044100303d00350358515110034052201030407121074801070780c94003c0c10702400303560205852a00300c1d908010182d140c260290480b908908140ca2248000c1914807541800c8011120701c1001025141d03c1b00720050015a0207400140c001c81e0f005441e800c00c00856181000618494007070304000e00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 299975143 1250 299973893 299973907
    0x30b090a02030406060b0c031e09090403020d020609030315120f010c0e0301050c0a170a150303090306050a0c021002070c0b130302010f020c03030a0f0509040e010b0a0f03020a1418010803 82
    0xc1e0843d019a4441b400d400414081c80761801c1012003940e070b9030120200030402c940c0f240b10741c01500d80310381c800295000c4803140c140002d00da0300003444000002c143c1c007228040e444041e41181d4034082101c00207200c1c0b0444400701054184466981411180078044448a044090005080d9040140602c0000702a2034079007940786800d01502c0d4024600c01140da10380720942c140101046200ea07006564020780d600071620003052a40800403000e81c81028495460702e91500030000c0b0700c240300a40740e140c2044041502140769115540205c1c4254005000003205424410041d40207503105607040e443e071032000140103101100808100840c8061260414207510015000e60001c2103500d08650007207002810300d890002c21502e070010b190820a50f0b41308401e10488103071044100039600117041c80d000d004040015000350391004d504a0b408900140c0380c0f240300c4190140d034880a58060500c01080002101203400541c0d0034002030044440d405165500301c1000300e0a80c01560181e000040318 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 299976393 1250 299975143 299975153
    0x509121b030123040b040c0305010f0c090e150108091f02090103150e0408031b0a0e01090506070302151f060801060f0302070203100e010e071d060406180b01030b090a020304 76
    0x1003c5001d078000030303032220300340ca00c5040441d114010320003002280b050f4041810711180740c40c4d16006540c884001c2c04483e40850400b8043d1800702c2c0c080010504220340070409480c825826842282c25640b40404140b101c401101d844401a000000901030ba6805008101d100030f84030405500300e40c00942d032002c030b540004088651100c0445441158101b052050951082c02e06411039000780c411a04c03500d0305840c03d55206607403200c801e11030500040030094943c100b0b100c00700f5004241c035451540380d0b80348144102c1f48100030009005822000d11003c0440e070746241d0640115a840e42c001030780c00005102641401c0c650461800300f1401e40040051942c0440c44c108a0502c0d89819420940c56901181d41e03050003102c003c04160310f0b00800e1484210942c844018010200304030b07000141d603090070aa000381c448000461030060b01c0e0004066083c58011001259180d140c1c060881c2a518041c400403c034504000b8105901c81e0489003aa0365074410090041b00e11a00060342c90500d0302d01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 299977643 1250 299976393 299976401
    0x309030c0f05100309170301030312050108060105060f03090a020a030b0907090207210210061202130c050714030d0f06080f160b0f0408070303080f090105060a060509121b0301 77
    0x807207608503015030014895a01d0b5601c4841c1941240e040c04a1910050b144c14450034101c0c2c4a004a41c50020000000781036010030b07885410012108200500c0c0d0301c03003041a4450009018450b04480d0401c40c0070703080c1c00d20000444d446001101a94106000356002401d59130555000b0b803028244482400200340c82440180001e0042e54421890181540c2c0d4800c0c0540f041200f0043c01441c150038480114000d1280b507814409200080111a49440d4154220031400c0401d0f03015036880001180301d070f1000c1c840e040d0050f216444050401406a07104001c802c40c00300300601e180418040413104403d54080c031000d86000c1d0b0000728569007440d42d4103207421107038013461615500465610106488001200090b00d42007000c19a9910580155100c036101d0740d0700100884c81035200000906600c041c0b4a40201d0700c0f031044549545500340c5450036a80190746169000a407640c08010141c0244001c0000d18406400a025000c3c148152802c011902109500c40d12480402c910300b40707000e01c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 299978893 1250 299977643 299977649
    0x120403081b01091110020f07060201020a17060d170409020304050105040b0c070f060c090b0408160501090f0b07031106041a07050a080a020a090b07060b090a0b030c010c060b0307030309030c 83
    0x70007004204404d0b02d405030400140b0440e54022030f80e103250248100d00c01c0c4160840003101c04100c0d47c0c0740c0d940b890000e000b035001c1c0c03000c03a00080c40f101d20540081070540000e07008280040c9445000700184c2c90b010340036001c03040d42d03490f44201040000b42c10580760028600c40c034001c200008007894282004440820300800488280004106030400261002017000c08190040e9000501d50801c0205176684125030f045445401c6010800003143c003400100d9960307620300010007406942d540c000549502c0198090300301411808201030004510b0000607013241402440c00b0000c9001076440c50782881801e44041e1009469801494407a080b249000c0341c0001c1e0f5450014a00010300314000c04509001e403000d09000d8000403803241071881303003e109000d460390310f183c1561150207190007801010181c4031103000740b0000c00014000c00551140c00c047e4032000c6c001d030116107c14001100d24154490048404645d168075100d43e031b807410042407020f548a41c8070380c0103580c1942849030703650225034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 299980143 1250 299978893 299978947
    0x204030c062c03060406051503070909150b011d030a1a1006050f0a081306110d0c180b0a03060306020c210405010f08040606031b0302100f051b12040308 67
    0x1541d0b01100d44000591a81c0b2a400c104006500d456012419036810034907102141c1c94440c004010401540c10b13840840d805118200c010006410080c1c2d503808e40300d8082449010907030075812010210103021080303080e107000409460082c215075403060043e40c400032512400030180c20420201b11300e907a124101515540c140142004548041c08000307208d0b441e0101d0420000001040000742403403c00a201c5900c40e4050120488400b40c001954005a8646a0560a0000d9001c640d406801d059509845503400c00e00c695003071251100040c3d01001e601c00c04c01da99103000201054041c400307059181004d030040c1503040401c0b00c0c1450032503206e030850101c8000401041016a80001a00900640c1d50404461907612410800001c00380f5600c09410b010032248000d048404101e40c507811390784200c071301c10b090722843c0c201150110b103071070300a002090301000b1010090180c00f40c00c83c01d204400d0200d1340c0d01a24104400300302c5e0040d600403141e0308030101d0091015101d902e18219031000d50 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 299981393 1250 299980143 299980217
    0x60b010e0103060b0d1109030a050102071709150a0507050d080108101413030516030c0b0a200310030609060534030506131401170f1b040204030c06 65
    0x880c9100c0700303c0c40f544180360601541e4400031b803c5074024030103403543c110005050300c0b541c001500300140030f0362002c14100d031421940c01c043c0f04100c81410a5030741c0d0484c003170b00004100e10400c200c820750341d01071030039002480020320248002840402c0344651296056440d201a035241004092070b1524000f00c9148071403d0407004086d240756070700b80583c08284c4440d039011020890405131014403400c1e00b40e9a154505200c0641819005800c18144a101e5483e08403180d8804101200710349aa20210b0243d03400d40d6282e9604500304c002454010501814070000c442c0d40c1d0f961034080b0fa0101d03c0490303130305858004115040121071000b10341c20041c5d02e581c604000c0c951580c1c0d1a000e0030050010241641c4002140702074540c070445c00c0081c602c42c501040000700711501c0d10308450007403041c0300c804490710707110004174100400c140b5072030b062400c001d001c8000e144074109800c0030844407058200c1d0f800c1c48000046545541d8402c000c00d41501d6010344500c407469102604c1945083e40ca210f03c201e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 299982643 1250 299981393 299981399
    0xb030a020f0f0d0213051b0901050d0c0509190807050307050604090f060e0a05090c0316051311131d0606030c070501060509070f080f090307200607060b010e010306 72
    0x15061482000302000c48660302450b100e580000c4610340e421401070341000b504210b0000e0094694449070284d851080c015801003100c1c440201144241480b450003c0c600340103401480103aa0003020183c940d83c00d200f414105180f0120304c0b88441000900c0d01d4030100d013010084d0440510008020748015000380104a080c030b00803c05500c41c912034504c0903556421003054800b02c5901071009032814001020941c18501d00084c090a02600c2050740d07401410f8200499150001d4503031003c10551651410191810042206003080001c1054013282c0b100c00300c600000381c800040504c902d003c11403161039400c0c40040140344000c0360003040b403c00043c0c02d0001d076584003070070b480d480966568003d035a24900d10b000380c054666948400e801c0f42d4040700780b080c1c0300d82113041c00344c00d81010790780c2e0400c9030790740c4000d61003c00d0240e0f01c411742c0790001c0217104045039141102051000701080c141c400348103100c020803480e9000e641c094500342d603030b80c000c04210741e409443e0f0312800200b40f90038481035007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 299983893 1250 299982643 299982649
    0x20103110f040e07121401050f010c0b060409021522120305031b1329040e041415010e1006030c080109021803070f09060e0106050d02070c0e090d030b030a02 69
    0x2c140c0c024006003500801c00201500c0c03040703403540060011010103202c4402040f80c5249000820b0150601c28900c0c0c0c0d0010100354072400c48070070381d00e42000c10b0a07074030348940040c40018010307034406036001124035140000c1d4107900c134010159403210501d600118202e00028281d601d003903402c4907440c01d0030307131034018082640312041e00e811043c50410071410240a0159020030310541c404a10011207000c80010240241d004a4500708040041c10340f4104801200030f00911484c0103c40782000807030040341c049086110403041a003581411600c000340380c0400508031140c00da003c1d181e6142c110040003a0718441c1c0045c2401410305080c1400402003984020308500c0050003040c034070560100f01c8090300c1c40340c0c14541c2403101000d001d0707503101ca4542c201c8041c440303418040c502d21a4101240002c1c95058080841c2c100c8401e0303603840c0c4c101032240017028041e43c0300705429505661001008070740101d442e200c1e030340612030060040c881103204d803502030144d0b00108181e51094100c0440b40015072 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 299985143 1250 299983893 299983897
    0x1101090b03090c100c020316060905030d0507060203071407050c03011404031707030f020406050405120c010f140f0a030b09070201110d0915061203031109150304060b1c020103110f 79
    0x154202c13a00700041c00140d10441e805241c100029500d4411078504070030524040000304143c407041c1d51038884094071841403556450420f001d1000007103003001104040382c030710740c0551f82140040c078051580340c81e031025081c41a080403c0c1611560001c040460280c50240720b4406290044507807078640b490581c070081c210a1603a8004800845102c000070010b511907449895900c814110464882c0d48070398004001e5005401114012400f0300c01110044100240074000c0361f805a4500c903c106400404640c0b00035a1b081c210713500c810038825402c810301c400700941228012990009481c41180041003414000a080c031001e69241900b0703459180d1260707084442c031004482002c6620081484c00c0703042490000140b00410b450a803020801c441302500c5218068000e035014440c00c070040c0648141d81c4160403010358000054411015022a00b01c043c540c0030703014250000d01c0740b880c0c1000c10600c204040300c00780c110241003110000c640c4c1512403211103004408030582401c2441501070743c14 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 299986393 1250 299985143 299985163
    0xc0801030c060c0515090a03090f150f09030b010b03040b100506030c130504050c03180705361f090e1009050a080a0504140f0a0920071101090b0309 65
    0x80780f100070b00024004100300113000b0844100f46030701e580c40c1c141c1c00c040d260102ea04046000541002e80041d03043c0395064910180c0d01c100c8031008804402800a4401000007903440c02480006407002002c9406030140600030001000e07240c2c0e4920781447e020380b120b000140900f02d0400c2412082c081c503290b20060381c2e880000c680c01141d50780c0300720303a64080840195118583c440c1c14581002201c55000c00654000c4614845002032071000c2151240c40b4026070213000e402120240250540a09501420180300c020641031428502d030419240b41c6d84008984504042c24900c06811840c00940039100080c1603400c000c0001c0704450192a4885d00c62020041244e9185d92289083c00301c01c0c40f0820001d54800c00741e039510441020041c000c0d4126204000c409004229406901c1c01e005585e210300c031500420002006d818506641c00a1a02c0340c01c0e2064a458a0b03006005040130800501106015a54003540c1c04030720800145078544981011780d050009100b48000550002004480 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 299987643 1250 299986393 299986397
    0x614120403120f0504080702030c010914150f0a0f0912020f190e0f0f07080402010f081023190e04260a0c060608030c1b0a030203010c0809010c0801030c06 68
    0x18203214400300b4090040442c21004840c9840b05010421003482c00400c0141c0c0300b80e05170781d000808000103461120051040701c41c2400e500c00381c00c806103410000d955004002040007410460602090106608200462004520b011201103450b0fa0043c210000900041c000044441e2046d8003050000d0880b554040c042c43c5200405680d18098030585005440e030b420390042c0ca07141a592030090720109030350f4020036103a2000840c62851203410080c1c807580c0c042e120300310202d9400508031485580140450080c2d01d1070302e0049154a082c074001050a080103c080c10f018403107608211608035a280320303003030110074520700300101e40001520a6011350448600c003402082c0540312003008032104500b122003940000c4000341b040c0c00c501513244490142c54104080741d10382d8030301903981c401d850445040c1c0d40496984454a802d2102003500c1007405000744a8690b80d0780e011a00b5140030302e9410011820410410039081e42c248221450124a8605045254515203612040e11464007072941 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 299988893 1250 299987643 299987657
    0x30a05090402042103030609050c090108060a0302310c021213050316090507080103112103071415130602090f190501170f06012a03090614120403 64
    0x800355216810b442c0184401c080902c41034a130703000703540c80510000314114007007072900101117a0625180b140b5032140402008940c500010300006481c0280300800e1640c0c001c3d414003010005854002e840d00c150b030b002c2001c1102090302100c06a884141c0424014201e07440c119001d1851a07000480d901003503144540150356403459140708007017140325000b040c0c16100b80e80007001d40301e80018240b0100c03910300c01c0c1000940c407038410490700000288406891610b0348441282d09180865280400001c982c906d140a8140d00300010302715004000f082c1c647c04500e0b07980f081074000901c40c040c5107070005100c0b070101d03241509510314a050391120140c4510740c04544640b003a12101d141e403010890050145c5800c0e06480116a1810308900606001544090428031001481d107442401285080c2c0300d1816640c800004548021501140c26001402d55060045113654000001059070081e034038005101c1c00c000c806030080010b5049082141d00c1003014890250311200701c240c0155141c41c101d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 299990143 1250 299988893 299988907
    0x200c0c060901121e0b030606010f1101150b0901080105010207031a1042090311030c18160915031508030a0201020705010c030203090d03050a09080d0905070e0108030a05 74
    0x264150050400e0101091a04184261078900c104503910130000480e024014082030805064490340e007030300d2140c042000481111040c1c1d000394101c0c16100b00031000040d0440004052401d02d0516030700c41c80011100148a004650b445000b00d800b5100a00041170402c1c9580d41d0681038025070f220b10000d811400012131071921544240070010300c031205540308564240030580340c000742c0e43c2c84170380c4001c50004465120100582502c0116503100d88846400511395103c201440b0141c0071815803601072103180c05240d1759a015004284880001d05412a14005901220002100d1000018880841e808012003510000317001c0c101c1c25185004106489214016164401140c00c1007065001c0421001300c06903055014002c41d500500007404a990b101105a04921055403510000c0d0091100d08044500a810040d044461048001a00384450300e03035119503041071820041d481e4540450b1020f00404215072005008400c1c0020519458a5413107039681c402e1002040c18010702007018 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 299991393 1250 299990143 299990147
    0x6021908130312180f03110424080f0a0b040311070e01081501090501030201050a0f0e06121e1501031d1014070914010516020a09200c0c060901 63
    0x145405201c03190310440700507201d1800c5004040012088000910006255040c0041054181040f1041d41000342c3d909419501e8152400d05a04449034005444646071010b860180c4600c08080302035162031400c02d0300702840141030130b00c00030249203150b0021103118042600b4100994005a00d07042800d4400b006121803402c1141942c000a0181c05d00d800008000a01081298a45030700008142c8960307280c5801004903a000e00010b40019800d1000e888120b002d0039a03c3c8401000c2d042620140003104009151540000b02124442c0711543c10b212850035100e5250060050010b4a28041e203000e00343c210460f007030350075003c0c101a100c040b00b500d003e00f0080c0c0158ac3e1100281610441e0804241c1040502a0030f2108a400803c02d000030742c40c00c2c400c0c690002500c032210207a070030891654004444035049140b81c86c40650f9143d40000050b80c1e6841d81c07a00a207070390200490b0302043da10544000070280e881e01c141d0382800f00901380c4026403f00340311450301400c07504a0b480b0001c075401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 299992643 1250 299991393 299991397
    0x110d210807171017011b0201021b01110d0c140a1709150c030a0204030f0b101505040308180d0507080c190b0711060304060e07091416030e160e0f0106021908 69
    0x240c40074007a24511b0400c8110340c1900240906081e9000c1203005807800070f070b0582260343c4024542c4040c4c00901a008090415400000c2005003626007240e000f803060800498a07409a8040c0c80400c40c01184c1440502140007070075480340b1808080c4c01620800a48680da10200030050515194000700240403a002d541c16500a15004407019142d03000300d00e841d09120f4010785505003000e560020000394060800c086031500b8055694850030315145d552400141c0d02b003000d500800c82e601c1c5080d0191a101c6030078890185016030002c1842c5440c1c004a0b41c00e1003000b0a5082c001c8550486c2c4034420b264118440c0211150801110b580b00445e00b050504c1c100c110b208282d21400000c284005c0c82035a4200f119941084c6040d901c507590784a00c41800c5070032084107250800354110001d19401114103c0041d150118207021411f2a20f04442a003043d00280c5420750320703811007105010142e80701c40702662062100d5900c0e0007550500794007955403041400c2081441e104001e01400300561801 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 299993893 1250 299992643 299992661
    0x10e1303020111040b3a0f0605060a050a11060705091c0c0315050702010b09040204230c040f090605030303160c080a050d18110d21080717101701 64
    0x102c015113071501d85a10155030ba00072500c80000003100b550700621950410b43c4030540a5401d9001030f401d0950b0203481e00644403000316044010369880c800120f5849250081181804569444d5030b0703078040c40c8000d40440c15031844803585510030800c0141c0560004110707010038508988408000611012594096240d020010710516105100008010102c2d800c81090010040240000d6882000c00c0b4201d5140b2403115502122510104001d81026481031095444103682501140c0c40314480c092840c03002d44030101c80b000006403c0101031443d40144000d00303444e40302803000e186454006035413130001400c07100258210f9010140c020b80070707600a900a079032001c0c450341c82c0d03060700348064216005481c3d07031032550b8203141154070b106081c2052032000c00d81c80048041c20041040c2440fa4100b210482101e1701d5080707050340e6245441a124004d5441c0b40c9641e080298903101800034400300140c00c00c00c0c043c000c80340600194010b88560701c3c090b6202d24480c503030305500015455015201d081c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 299995143 1250 299993893 299993921
    0x130b0c070503090a060f080702030f03180a061d1b0306151f050a08010909050718180c08150c03010509040206090402070609020f06120115052709010e010e13030201 72
    0x400015191b40024140069801c00d0300c4034141c0342c4d605202a81c503441075285100c030300081003001030003289203907404c083d103e1034420480c1c0284240740e88850031601c440b8181400700c6206a12420307000301c1040140d0740185801e0b41d032105000d420303010075501d200c0642500d120030310b80000a9003648030240720940c80d85101c82404001c020b6040040c0c402e42c400700290380001c903110004908804140116051983c0c440000c1640519140d102d000c0c04200c0001d24034440e491710140d640c0c0001c1c218460a041e4001c5002501040ca810011460080310380040d02024800c54200130400c0740e10303401e0b42c0c111101600c5005140c0c0c1c40d480040c000384078445a4036482440840d424091103056400306030094800d40b1889545400c0f10100b04841c0900025000203c450030018420030010a0b0b0742c1150311000c1c02c060b4141795000c0c664622100b1102105911f00409880e0404a0302e450b10445004100c40c1c1c03000b15503941000b4481ca41600c0013804d885807240010b9401c0c0415100750f01c0b501d2100004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 299996393 1250 299995143 299995159
    0x915020a050d1d061e070905030a0f03020705060c010e010b0118150504050a0303080601021e0a02040b0a1a0c010c05030103110f01110304060c051e06010e0c1306050d05130b0c07050309 81
    0x50b0a66120074405c10350300d03c0030005000d0014040d02d000c0d60304882590740003001084403615507960b154080184440c00c804600600e4000611500ca00703028004929120001150344248800d880c1d0840d0305446e131050400c103500d20a012000d1007208a070381518074200c40c20071680b4801000b81c6551096902a90f082281e40b5000801d041d800400d00b40203020036403d407501d4150001ca0040c0c401c3c142c41521031a504285103501c0145825442060715690103006440c0141d5501100c3d111000306014aa0680b2070024103400013803820301c03ca03061080e01d8200725003103505544400e0031000c4e1144c0040e002c2c40311000004026030003503400103500340424003100d580e9074903000c000309600c4581000b100d0314414070b651010445015102119201c0300b10b4018451a0b291440500302400d02038400310324920204036031034110107020180005040c1644400340d83e04030f003c2e00c0008490740205004821440c40703028030001100080016000007100c40e100d42c43c2c08043c14000d04520500440c664800c0784 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 299997643 1250 299996393 299996401
    0x7171e130302030d0f0206072c010c060e03030402180405030f0304060e160f090504080d110f040b070b09060717060402130e10061b03140d0f0915020a050d1d06 70
    0x2c0900c0141801c112031b400c4e81e8441d101c01034107413444500c956000019030850f00b00442c01d100c0034006510038540c14500950a0222525050111402e1901940898000004010a506144004512490034140c40c103400c0c0c07505840d850303204e00440c000440b28800000c003082c2400500d41100b006280c0140694211039000c0701c1c41300000c9000d1241c480c000c1c0c01031000003901440c511501e071165030401c0c4401e20300444100c40c1d41c0148071a000c28070015005020580c0d09001100c040c1001d800b400daa403990368000c82c2804100c1c00c9000f8005919070f840300042203036240c0d121850206510300c4040c00740554072241d0015005e4010b641e981115075000c50780000704e00c0110003440b8000c0e81c403107103404506600ca1000f11382207002003001b4500c100074a00c6400c00684200500c00288503000903443c2004041042001914107400824032000d445942034414007241036018415141c5100d811498003183c2003014013203000e281c4c0c030441c2030799884d94032800c500c000f40c0c44545403000e48004d555145ca8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 299998893 1250 299997643 299997647
    0x20f030c28140a02150a0504140a1205070905060d03121a030f011d240c1209030901031104060f08090307140a050c011812050c03060c07171e130302030d 67
    0x4074000d05a02c1619800480c01282144d01c08846e03d040d80780d5a400e24103400c2009101000b00000301e8180c02002d6584000341c44c6170303c0b868403500b081c411006004010320b000b0700c0c00140e81c00541603510a8030000c4040c80000d800082d444001109804042116800c02054060a80c019156903805000c1e8071502000e005065201c0d54100c103a01c45c0059210b20001203190381c604070301c040c0c001b10814070100038403001801540070b40e00408240320246443c6210710156411203050341d0904947c0c0c4003060004031503806008420780c509042c00810b00789450200700404030310104140b0303c103104018003c1403050300c00f40700311081e2036000184281004080c00f020b41d911008980d013561f041c054031020541942c464030268113024241010b400c43c0d581090351814802c603450004540d244180d802541c01620203100d90743c4a81c0d40142c0e4240c0760a42130800d0b000c40d811104090440c07180400c20005241c2080100705010022080c3c41c6480c0c80002c0300704e980303c1c0d10940003c0c1d41441100b500b00c484079 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 300000000 1107 299998893 299998903
    0x2a0906090f15080c0f0a09080d230703030f0203091615020601030308070c0c060f02070911040306020a05070f060204170303070f08070e0904060903020f030c2814 71
    0x150785074170029280c3e4002c3c07104d0404184076203020048030034280304140051455090001c02c80ca00350b02441c1600401440c1943c03608404540c580925111f9444100d8043c0225000c6681b8100765080d259500318805004d40e01905d55480858a003a00580d80e41107064260010441642103075411303a100d00000b410982003002180940c800f0440380302d600f0b0010091511003a03c1c880c0b200c0c4000b418150f05401c14a01e0354141090403420520000440d02240d8003c5001600d8040c0030408070b07844c0c820484064200a0305043c03030030a2103090303401007007100d4014804400318906064042e03141e000c121a1a008a000c1e405110300d041d000e0b80c00c40e0f80c0032520349451b401c0040900001032403001c0a540c151010756440c240d200400d07804016683c0d14000c0f0400840c00c0542155145950362040300b2607402503400030240180d103404105035001115807108504080b00540c00f0a19a11 = true := by decide +kernel

theorem cover : BRFrame.Cov 299820143 300000000 := by
  have h0 := BRFrame.cov_init 299820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 299820143 ≤ n) (h2 : n < 300000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
