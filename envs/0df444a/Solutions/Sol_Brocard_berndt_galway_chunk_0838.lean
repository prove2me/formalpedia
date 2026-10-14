-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0838
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:04:39.675282+00:00
-- url     : https://prove2.me/submissions/2b112dff-f836-4da6-8e01-f1209f2958ef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 150539568 ≤ n < 150719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 150540818 1250 150539568 150539581
    0x61617012d080708060a02040b031902130905041203050f01050f0f0406060306030308090c010c0206030613051504060f12060b060c0118140f060a0509160f090606050708041509051206 80
    0x42017406045080f000740144410b02c9404040300503650f02000c0d403904c80c442c80402e4081940244200b804401040c1556080451401e40c2c90301301e203000354420184a5241c140c0300c0d80450484d030003551016200118400100094070700a2074080030038800034854075401d20000c0008040341c00345c0c0c3c403a001090700c0340810400e0641003400c060740300380750030003600e00b284d884800207010760380c0b035003000b4401c400c0031010a0054442d100c100b507925010340310410540c10110005000103440151052040c1c1c2408804101c0c400309141080442d0072445825661031004d030f43d40f030b019050030824a50400d100340a200603001090142c040c2c0059540720303510f40c000d51400c000820300d81210144486510900d144410b85000040065007d18031540000e40b03511002444c40c2072002003031041040c40e0515002140b4400820b010008031421544100f0980e981e4001c255820b014400300030f000c07503000740700030084d11a034034644202c044000c0c0ba041d0941c584450009442060b00d40070f0240031f900802c20000c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 150542068 1250 150540818 150540823
    0x41103031308280302070909080403050a03030b0906030304030f080306010c0b10090c11060708040c0b0c01051e0601090b0a090b04030809040b04051302130e0a05061617012d080708 79
    0x1071441010803ca9110805034602941d100603510900c1540c0340d5503000b0308188403c18081d01e0182d0340c004241d400070551414000c0180100b0b0381464400d40808004c55020300d0004100d80449a010042c501e50101c00e4541d0206a000108901c0c140021410311500054506166a03c10502c104403003d07400d084c0080d000403a0000d142100500840300d41405c00c1d050300140165201c451380c9820513440c3c2d61460003072503003262548580c2e2515408540300c0d45011040d08114454030380b207664030f1034030220701c4039900343c0f0b9105a4080d07000c40c014030000e021011041c4010640f55095040c00e042250b540c00001440b6405948140c503a0310000c83c5101d110b1601d030044881001c000c035004e0027a0300b40310000c801c0c500c00140009115901c05030950400c0041500701260035540e00f019184a80c203a41001600c4000459509401840402c015501d080c080c2c60484680000e9084010041c1c0c20110000c0880c59401d010140280c04507007111001c5080e03c10750340c003074003070344000d802e2613841c0051991 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 150543318 1250 150542068 150542113
    0x40f0b07050a0503060603060d0206040807051503070c12032d0c0206150d02040902030102030f042906011101090507030302070f0b031312090b0304050a12030203040209041103031308 80
    0xc000c0704106280e1001d43c0902565002181140d050381d9a44407000040c0b04d40140403402504410040b400046c10900820703c0340072070303034183e6850340c0c03190201c2c0446034548003c40310400400c0b0704c0e4495001140d4080c2101c2e16841080c14005204450790001003611406007584452124014807205083c82d6140120060b54240d40001c100c01d04000444021000b001d0256502850071203918005540e641c0d00120055a00507008540c0c034100541010314108080f101500d800b1094898040c030b0280e07a01d039440b00b6030005440b5078050303103031000112142c10120224900c5503403074810220100d1018448807000358440c0d0024800103140c81601280c0001950140118400c00e00400402d0351009110054069200e00052240c110303403c010b40c4d1003906500000c10300d403000300400040040c00079804000d103001c0e414001c01681030000c2101a4842140c1c0290800055804100001c2082008001e915001015039007801046017581c80d04440a40c02070000794049150406034058540b00003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 150544568 1250 150543318 150543331
    0x91203070308070509060d050c030108150103170f04090e0d0e18040f031107090b1801060c06050901061211040c02121e1b010203040c0e060f01050304051005040f0b 72
    0x1942040100d44001d0214000200700e80140700000501c2e861503030322003040315000820307050200f00c00c4c03c01a1034030603290402d000c0d0b80d085116402040c0c446620011005d07048a90000350303043c0803030100c21a5065078100001030000914240000300b000003082c003a0052503e003510083c007221020400c02480000752a007290301544141040e001170340310500003154020380003003842c070304a900c9103421a4402d02014010b08103000d00d0300e010074081e040d0307084102214801c941c018600505200310204981c2c0038803074900810600c00c103140000f0110b4001c00c3c0d004016800009100b40d841d4a070717080512009400b264401280362043d2828600b51103103000007242480104240042680b5080a9108569100c041990b170301515031071130120710049941d031071010900c0e5400800c00343ca0303280c043e41081c1c4040ba036030401c44c000854a51071070060b05108840041c0030300304040b01c038001540c2a90004d0300039201030060b05c0d100d0300d0150716401118003c0f0f03c119401c400e41440d1b800d00072038021018200c0d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 150545818 1250 150544568 150544573
    0x9240e07020c010302070206041e1a030115030b0f04020a0c06050903163f0806190612060b1303020a08030a0824040504061a01020102040807060509240912 68
    0x28408281d40c0003400c2c6140400a090050b524503181c0000fa100c3c2c0500d50003982c20070803182180b0000c0061501040c2101c0d5450b00010582800d185c40319030a0009008030360806c2040004401d81ea4425084084450360142400306005101e0010800781e90003c2e40000c040303614106200d04008943c41a02d0b88414418060360078981c20b6041c0c54241c5480200141000901c8000354104002d004d490f400c0011403500300000c0c2041200d803000c820314224650030b004c10300d1500024020706000d10a8080286203d8141503424240b28003640e80001d1143c1b80c0002640c3e800000c01c1040960005040520f528515000c26901c0c520401c203056070903405c090b80c0354005111004d00550441140340c5c01100502e1902124030241041003e1480c602026070707807003804c0070140000d0213041d0703000417410400c83c0742c07030a150488100168240c2c40ba80c071804146612052041040a101e00054068000000c1c106003200085110200e05d038a88042428010b00000030307410020b140c2148581c8201d00031101 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 150547068 1250 150545818 150545821
    0x70324140f0a06031d060a0b0906010f210f060b1e34020d0311010b010203090a1e150e0102070905092d010c0c020906240702010909240e 60
    0xc1102221688030fa0402d154a40d000c2e0507883c6112180d0030a140301580c1200e0083c82c008200c03d010700403020300c0c47d0140443c1408240385501c200481c1661600a40f1a00c240c4a1452070400c00140401007450307803070b560340001c20300078001ca01401d0014148140f0b1913456901c201c0103210308400138030342c0306c0c41d083d000c00c0000a80c2a1100598020f4040445200c141e0315540c04005250a01050001c0d8001361204803102016003080a29540c02c84000003040000a8140160703607d104408810394002c2070844200040000840340004003901a00c070324140c541e98040005007203074220110380100d0842400502c0a50703042010a00030040780740180700310700f03001409640392041d10384914030000b4440c030086114150800614801051640200230840400d00010040c18550200300d1146001c0b40c00b16100c0e00d030906502000305080ca02600048040b210303d0185648a121b04a061100110b80014011110711031540c80c03c40c00d00c0d038200041411940c121310b00007130350400d07508094000c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 150548318 1250 150547068 150547099
    0xc06070f0c030c060b04050703020c06060603150d05010902090c0a11030313020d050106050a140108091b010f23090111071a0f1612020d050a080f07032414 68
    0x55022040740e09403c000c14443d000342810b8028041080c0b44a81080c101028450b4041e40365004201200100303040d03031420703116402080400c1c0300c15034400c80c0c1040c03005160b40d16440d1102400100c0c81c0300e5400001c50040c2640890076842c4211259502c840c0007080c01600140c0160b10390b0b01ca441d082c00074601d546056860b070004d00040c0350000e4001c0c1e0740d462451081000962007007020f4200202a052010b560361820411130807502080f40c00600440c01091070030800142c1014180400150003d500c0c00401c0111200b0b166025030703204004014040d1110b00c40d04c50690121a003c0c10000b580e1080901cac00035100c094400440e0420341d00c841420092a002000082500280005003680e130b16403148801c4404c0c02400034000003031700c0700d1307940004014100d003000e684000503800707179183c52681e003030280d4950151207601c0000c104940001a0011000030700c0940c002450f0800250b908000680e55582d0034810385040c8100c000590240314a64120f804a0720844080300d0300003402c2e400c42d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 150549568 1250 150548318 150548327
    0x15070c090606050d050c1606060513020f0417120f0301151704150b18060102010507080f0c03040236010902040819030e03100f0f050c03040318090c050c06070f 70
    0x84d580d44036544070003107110059440b04a074000c4500100410324010142484801805d152244e940300380002e0b200055030780c20900a817a40403403007a42103403c02c1d01c0d0600244e070b0325071002074216180c0180aa8007221444d0384000d00a158000100d80e91291f05010f444200001b102c1f0382e4200744400d14845403001020140c0c2ca83c5c0c05648841514411186051220301500c0b20502150788103040c0054442c2e60803218000611528090703000307200540b204070080c0e807031100903201c0820000351640024500d01c0160029500544054010500602c050071401490308196944024001500580300c4401c0602e1003018050028503400318502450200b5440e69808290001204041c0c4204510145401982403105400000e000da50700003e80d0301d00d010060003520200240540342c014a515503444c20300c50340780315140d044440b900c0c544458034161814035102c5890f20403241c41c9840454081380303a0040f141e900343c542e265161913241c03842d94a407c120000b0310001c2003000c86503e41e490b0680c0b2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 150550818 1250 150549568 150549577
    0x603190f060b2212030305040b010f05060403030e011803060219030506010512250207091a010503041e060608031e0a090312050c030f0c0f01060f09020d0b15070c09060605 75
    0x1041c0e03e0300644500c020b090a41402c941e803090100d0b865002c2180d05043e0550802407003544030784641c0441daa2038902c0269031030350900440750804000d01040c80081d00071104002540700c1410544000070300d0a02c1c078020700440e50011120381c0c0d00448c144000a1540401791008020b9003421710040c03400d000028900c2c040c0160500c1e40703003546d1010440c84103c1148000c0540341300280c0f0380345461301d440040d507540024440e80d4105880d00503035080309142e04e80f0380d103040b1505030b48003881c580300ca890b0b04424100d159070040d0382e480e403443d9001c0044d156118490007801072001840d11051406142d030301c0d0b0440b4490841c841e200400481801c40d80c407802c044152503001002d10344092000740c04803000d018104481902e0b11000036180c11601c0b000c0040c00700c45164104480411441c1e9010700d00740c1712548217600302142a090203001200640c0c000d0240483c9044000ad100c200e440002512074400307000c00000302400050740360502400390cd0801c06001c0001092005601d4180c0c0141507104 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 150552068 1250 150550818 150550837
    0x41a06030a1d030d051b030105060a1202090d0c0503010b060903060c1c180c081b060c0a020d0b0604110301030803010b21040309150e03120d06050603190f060b 70
    0x20754600c0102d8542c1c110382036040c0380b0075140071a5112448101c013200200400c0e1041d5103104000449100042c0c0350200712416035002030000c90824100c0c001c1682c03030891481211000d41d03000c0c00081815114140340c01206030280e1107094540307103440140349c2140d03232141040f4003e4800b00040e8039281c41c000b6074a81c000d03611806050352803050100c00c52000340061030074003000e400c110095040c00e840a05541400f80141401c000c1e695641d00081c0c6d40d0b407410055040c6810f000c0d41031030000c3ca80000031b003080c0a08101a1018100d0b19400100030310380e01881160400752010500c1511b003040d100c0da40194030800c864529650454642240310b00051144290380c46000611017000012910300590b1401d101c05940102e080500d8080c000030018010700381c200000f118041456482010038014a44010380905180300ea6481c400403140c4c0400e0348185815120800005c1c0d90b01c5802c000e502c00c400140d520310941c1d0030000420141d6010342652080b1504191007809801e1a00d03046030000003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 150553318 1250 150552068 150552071
    0xd03051b0114090c0109170a020409031407150606021f0f0207020901090912020c18040203150702030c070501080f0c090307030c06030209010207080106210c0510030b041a06030a 78
    0xa0300c540031a80036000d6554040540070700082072200c3c460000840e141000401d80740c3d1800d4684407a070034100505402985083c039805040300b03d016051641c03001112038000d03c1c00d05481c0c1c13a800d035045000d03404400304a484085004c20b1a00e00c1c40c1d07a10403000502034610103054070368018503c0310894030542c100b0302d100503030301d000004507240b01b541100c02a80c0c0c0581028129079503080480010812104140c640141c0004520f2103d4400f01c0c9410300300c00c001305000d001c40307074003450010b041d00010401c0f0707050312032400480b90403041c112076240b01d6030342503004540d211414502c040c1407410b40c0d400241800701807014800e01d80e40f82c01000d540080c2036a52039446603603040000b49403443c00c1c6d2024001c0fa1030340f08082001179054009044042c800e03001c440c80c01e44d80d100401c0c01c0710a00e00c540020140300c4114000c055000381d5180c0096401203a442011075156000034600c401c48100050100e90344422120403814203015110b500340000c0d5901c00358454038804182203203c0200410740c050f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 150554568 1250 150553318 150553357
    0x2030a03050f040906140102160b0315040e061303020706110d0c05010f05010806061c1109040318080c010f031406060c0f0102040902130f081917070c140d0305 70
    0x1150b042640c00a0030541c50900080340e58210400030002d2840304103005008071154404041c82e2062060100c4080352405807550343c859043c4023107001188c8034203900c143c4400c041d00c1264003c1160900490300520582d1948500780740c00303071601006078051414401480940c00000070301040c941c14038442800c005034480110701d0a50f00401c0062254114107180c1000441d0240000402502c10f00c0e0944e6400b40e0700c9005c1c2810031254180c01d400400b00b01001d5006042400c001418540280c0700703040505c2c000c1d91407503e0300700091198002c860300e0f0340f0200d42040c0700d40e4480b0030010305000601701006038006040d040c04074030400134103a0340217410000d4001c1c1c003d002040501c55041e900c100071510746440300743d010007035409040018080c2c42a40001304180111f809c0c0700088a40460040261640d000c580e04100000c0c100c00741d07140c011081810100ca98094010311840f0700c18914071003a5818181500c050b0443c2c03820141c00746190552290000760000c2c202d518031038408400ea881c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 150555818 1250 150554568 150554587
    0x50a05030d0c0b2e0f080307050703060f110f0702130504022404090204120c080613031103070c03051005250809030c010204120b070f09050607050c03061812030402030a0305 76
    0x845101c05071140c140d0000000d580c4c08070088200b000156280e407582c01c526a40e60300c5c2016600e025480001e801034018000030400203145078091030f440b400c40c58011800c3c1c012041e01423800d400c209038009000500013040303070071860001c0f41c8400c9969466810045400c054011806100a01101501d5031b881d000b9000d5181090b503068030024a03000c2d105550f0749440b40705024010f030f809401100c1034801d14401003560b100204100344070761324980052141c0c14082d181141e6000d0080c0122005000c00c00c400400b0035055126130015500890003054a03610b20203050045840041c00031108101460f503916804c80c43e6a1061241c1803140b070110641d03200d940200d402d40c41b40b0348460425600c0002d0006040204c8520080f03d2405842c2000c183d0761021001c2d42e80c0402c1178000d20003e5548101440b641c9055000351621500500c01c035000c42c48a200400d01c0d1200503548034110080b400f8080705858000c03c5a0700881c1e03420102d450540c1082d82c04030750b840204460003824020041041d910 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 150557068 1250 150555818 150555841
    0x310030f06090b01140102120708031b0c010204030804060e10080703020a05040509011410080105090109020c03191d040209090a05180a0f14010203040c0504240906050a05030d0c0b 79
    0x320190400941c400650351075007503101c1c12a4040c1842c6c094050184140d00d190b554a0603100540d402c007903c02e2960381c401a82600f034825400000c0c49811090042c1c0c180002c0901c0540051071081e00001d41d9542802c0b009000404200c4038644540d01d80c14880209035400000650804080d080c05603d5011550381a0703018001e50b00308030340100200c00000380a0340092602d40010600b5a007540485050840890b1100024000c19400c10008070040100c000e40d54001e100700a588000e881c01d11542c4070000e18601c1c00710ba625000182440c00246181c9503d481042d00f124046504618003000716000c50b180000040007212015074030000204202d52400084005180312402d40791141e40d940f80ca202c141e1482007042d01c0d060f411713a1403414102c0c014403c5901950b042123003aa601443d1404000140900300d80503019107507428007030480c0001c0b034104c10020300100760000c943c0a050205105002e03c4990010744268000b5080e22035964100c4801640c89400241c513060a9503031104220 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 150558318 1250 150557068 150557081
    0x3070c060e01090b060a030b0705030a0912020c031606080606090a18020a0e04180f0305091c05010c0f0c080a170f1f0f181b0507060605060310030f06 66
    0x20036140c1880a00d03150300806500c0300310624454040c95034103440e20814400700c0201800020000c54118000c6208240100d019550010007100082940b010b1170b51486000410701001c100135074040300d4545a146800e21030514103440740091501c910b86000e40c000c101d0000a0409802800001400c1c54a80c640c3d140c0b01d40981b42003841c0c03400d142040d002c00c5009500c14111500024000c0e8100e200d9803402c0d004080b603448030611201040d01694a4182810040b5603049060210400485500e40c031100c4d01034038900030f640c509040310951410306e94203440301c241000c020003c00860703001c1d002d50404156120180c00131211a104d0380300030016151207880903884140905200c080101e44c07174012041030f11410054001c80c2072907906511404085e5030794021112104800541802260412202211200d48021012546051442c909500b04000368051000104005070308814462580a40350050000390f034010f02d035241210f20100e4002c002e010003003600c01800078040500840b0380010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 150559568 1250 150558318 150558323
    0x4050309040615030b1c12020115060f0917030714030405030303040b0402120601060e010f1707020601030b090c0f040b0f040e01020d06051509090402010c0f080307030e030c0705040203070c 83
    0x200121521090b66820000d00481c410340040d0030443c80b64482e01b0860420f00d0301011240601001002c9955200180c4901c2c1500c40300715941c50084c080720901ea000c852006180948404001c03500c1120001c05400ea1a00801d0200198144c44080c8130400411107600d01e400a03d80600d02c1e081103881415441250300031a03141c4400310078802072000c40306615020740d208840010501c45040c19098440c0c0e000d104070800b00707003180c02108083d4024012482d440050303107003002c00c03032922101c3e4003202e2105803034402c0140d1010005100b0040843c42c0a40c1003400d100041810340140703800100c039041c8148200e4051600c400c0004425140d600c0900c032078050080c400c0c8105201c0c3e68481e8000d412540c0f000121a040c40710006250900c0518804507096910b10075180c00c0e0f4000c24425410030240c422410054070313022142c082461404001c03080d6200e071113003543d20b0621250082c03e9420b603891281c2c490704104425400030100203000003c44000303407805601c1e80e0782c804040d1210708954802 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 150560818 1250 150559568 150559571
    0x90305070b03220c09110909160e010903170d06081b01090f140f03070b030c180109050d060b0f0a0e01090c0c080d1a0d0303090b0901020c07060302030405030904 71
    0x401c6041400014521640e82c3c58980e90b002d07280203c1c11101c5006280c1e0181c60131945020030311484519070400c0440c2404111114580a1440301007400c20790100c812103c002001c0390300d10b00041d03104203951402442440c0590f025030031915030340003041e90b81c00481c1c2c02d07441c001100c54a400080d08410018000340381921400e031030442e00d0792005040c04010900248101d00c000ca2303130040c00700c01042500c00d22428105402002010300480e0042c501100f0f41c90310903940c00080c900701a20055101e00c10340510541c841e40c09500c080700c103a0b211100b55052186640050010742c032480c000c01c100c2d581200d000309540744200301048824030710070344480d080007070200b000c54030b0903800a081d4102d0b86950003c10842d0380084007150140d14900c1d00400605c41003040d90f800c9806078200140c401c070380e540440c0941440e80e00040303800b4524401140443e440f940d2440910120b104131950158469009524090740c41c030105848400318010a0145a408004901400760400070f03a121414082c10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 150562068 1250 150560818 150560833
    0x60301061a030603061810020f0702030a0c1a16020f150d060305060c07170a05040f0909111005030112081605010e07170601120f0605040b060102120408061303090305 73
    0x1600c48a5402250014040d115000200b22200b5107161500724100180700603021207920488501c000e90700031300000b41d204005018460240c0e906015403000725100385541c40d0b029182001c0e03c1c2440441d0700b521040313f4400d100c80344075884084140030000703904407440107540c0a4140000c0d01c1001010311807280038030118564525006c43c0d402142500d003d081211081c1d60344200941c40f40c45038160041c44007005443ea480842c980382c003e4009081281080c03403c103600c400c141154980c0c9070303020b0160140c0381d500d500309101103c4c45c100400326007600c0e40c0140c1c500401c1c016000b0310043c03085918051a01d41e180041c41013801c00e448110603001e0070000900e0107424203501915507803403102682d01550b50700086200c419244403c2d0300a40703c02600d5541c0c0303094180b041c00d50081d08240c6e00c2d1244c4a003040001025441140e01c118411015482541070a8000910b410f40030403006102c03940800050004150014407141c1c81182d0240c154000a09441c04840208069000800903c0f5401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 150563318 1250 150562068 150562109
    0x14030706050c090103180507060507051504050a120203130b031803031008010c0503100605090109150c050705060702061206031603060501050f0901150804030e030a0501050f06040b0109060806030106 87
    0x810044409a03400d018a524004080206c1d01d00d4001c002c103180d01ca082c080114601880142086500523000d80f440f24801080c8034112071000c840480d1182c2202c02400108144045101140b130003600c015803c0000007a10040c001c0d5041c010f0305110030010000448404030101c24101004a0303c0503a0345034141840c40c81050803050085d44080e500308412020701e94407450a4900c0b90003180040e100c2d80349011015039981d40312071002c90401881072008a0510600000880f0308580b503580d1580c3e4221a003840d07800d21740c103608154400e107020800f11015a403624203940022041c945c1c0e856007500d400001901e4080800c100348500c12030700074004107001065000034102e4000303540c0045500090f408100801100b4081c00c000481c15000e8020194030030241c041d802072180c14402410741032400002d240c50b4944c903048a6a039191420040c02040540000c0c0d0044010f0f202404045050390010b080b585d40d50003017204002004000808a0b03500b50014001800031003801c0b0320900d40031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 150564568 1250 150563318 150563341
    0x30c071e090b104e0c05030f0604060e0106020a200d11061605030c010b04020708161505090d110d020a0b040606050d0b010303030c0c23030f030a020408071a03041403070605 76
    0x100d54131407881c5501280c2c011040703000d000f00e2621140d0f1a070b883c1d40c0d204030890440306400303840e041d000742d5551000b207100700894000b50301038400c079002003440d48058030301529408280c402490311072441601c6020142c44560080d04240d600c08980c8240e284520b0228015001e11440c800c0b000b405405d001c0700f8004003000624000804800034040229000c09000581c41048801400f0400802c5007030301e2510f108180c0b418903880384d203c2950983d80001d407003003551001e4440d148a5000100298020741e00b000000380440c01721310203044141c1c0b1020b4040e480b00e0062078050300004d00f090008040014a500c414042d05000f8540603102440741068091b03210240412400300345008818586207001e03440780140c0c15840070104c1040508000681d240d0551200304120501c82803000101140f4134101451041c0c0c815180140c540346024111403800442d540036032840e0088070900031105180f04220381e40290040c468480401c02c00315800e05c0c6110320040600420714060502c0624800c2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 150565818 1250 150564568 150564677
    0xb04050306090607142d030115080c040e180a0308010501031d0c0f061606090203210a0807050c1006051e06040509040302030c071e090b10 61
    0x15012601a07a0b2900d04142e03803980161050008100040c42c042c40c8651520b00408103222521151001c1e540609840c407206144140c040c06100400300050100d164240d0204107401001d1801540c14142025684c00522850007922070300c3c1c00113000180c00c80303051198550f4420300c400889103841c0d00750070010030700c2d402800341d640000d040442800100c0ca009a0000c0041d0030318001e48040411502000941c1c442444010303001281840103081200001300761404c10f9004600c0030640310b010340b04142c249100c040c11380c400314040001e6103840e844a00c042c2e035111207582c102500180c07540310003501d6601546071600020b2050058445134149070707030003d2040381c6064800d00751082c10307003e2009480d00c0d20414240c01003000e1004000500c0c00c00c220340d820a0080c01920f1800d0a00c00805081400c3c1d504010b0a00c0e424080703030084880c00003140c00c001c0c1301e0340c0410046080450f0008070211520018030b020000c1e903411184540d483c200c02c80352007000c1075011030710f01c106405000a00c4082c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 150567068 1250 150565818 150565829
    0x20d0b0a0c02280609121701051203180f040f091101080c0a031812030f05011410050d02040b0a0804050d08060f0909010e0607030603031209080708030405010204082410030201020705060a14040b04 86
    0x41f03000061107080c0010700b01c00c0341680c07001460502d02c040040180c04041c035948103a02141d0301062000b00e46447c0720301e550a814030680805d116031142000c4000c0f035500464a810461000204410604004152181c0411034030303002c0382e14510518504862581210043d00911013102e40452464050f400310b6480d4001c16401d05c002e0780d031480328012000d080122107800400804a100d500c40c49103004142c0001040360041c1400d0b100c5242c2c140c150880c407140401b26002606010500c2003c11000c0d240300d4540ca002c05040c038000010441e41c000d0081118042e1074200081051b0301d40a4204a0300d01c10607804544040c030342120b004010700491b100960100f5402c40081036401c80b82c2c090704003660340184a0500d40642d507134800400782c1c0b00030b0007903903103550034480824030080a01c4a21408140c07403d043c5182c1610105031104114043e02e452081c0c4d802c0101000140d802064031340c11203108441c42c1e07407075821070001617400410600c0c40d0901c2c01400103003c504480e201d8080e200340d55 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 150568318 1250 150567068 150567107
    0x705120909061212090d051605090a05130b040302010e0a050c1005040e010b070807080301061d06070b070311040915030302010608060c070206090a03020d0b0a0c0228060912 76
    0x11503000034484481110241100280c0140a513a00421200c030020912007002030b248501000312502d82c2ca050200000d0075001300d1000d00002c000c1d62901c5040e09408c000c1d40c550030046030401e0100900300d1020001c00030f258601707070350002e02132500030740c441c0070b45040840540b240e030a801c0c0340240d11090022001d03449049a0002480814800c4041e40e00380c80c05203181c1e49007642402c01c0d080e500d0b040380c1c2c41200d14070303400c00805001a5012000d1070007400389440e103460a44200d207804800941d100300b42c5000f25802d0040da004a0300d40b44c0920340154060800241c3c44002080c1d40ca00c604c6035400a10144d1700302481c40341155600c100d95070861f4000c0d4000c0150986074664540c031024203503080424000d00340100c4001d40340c0072000f000030480c010004c3d00b040da580c1e030100d0b8a4210031030040d16003025403000c0042641460040e4001180c0510142400340640420710031010a0b511602110000050042c8100804e0303501c1192003039080031074524543e0186c40d008000c403105217040040f25 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 150569568 1250 150568318 150568321
    0xc0f031f0b070c0306050408070c0b03100b071101030b0a090227010315060f090e0a050604110903030f09060706021b1605150a17090f15130f0501020705120909 70
    0x4001ca80c040c0e50740e96a001071a80c3c03d103807540d01c401c0e0180c030001e0301c00e6880c038208008080000c0d4514440c08002c182c90b6010356202d140c1959844000c9040758004002da00c800c10100d0300252611350300520314402401c0006006074580003044950308690414803089100250001900c070b0f200c0e29400031000300b08080e89032014000d00442c191020920220b2901c0c0c040941800041d000301e500c965003440c00d140034403d007603840c2e40341c5e1802032060b07482400023561038085c40b845040038013440708012044c448261a00801c5800710340e480c40f4114001074180d40c041080345155542c40c0481d020306801004c1551124110a1000070a01508104140d40d100300b0f00721641c504101400002200d000603d00c022000010700d65003c0d030340c03010300f01c40c0c10807144412013030000d1962101c2c0c50140751990018401c0c018a152800d103800d2149900380d010400701d00800c044626445911880c071a4001c00f212040b070400c0c80c01d24064050101c0041840c042d142484001d06118000f50074840c0c000c48405145 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 150570818 1250 150569568 150569579
    0x90c1206110f0306010c0501020706050a061508041101200f0c13140c03041e05030a02070f0506040614070519060b04020711040c0e060403060606110d090e0c0f031f 72
    0x191184912628a072081400010213541c0200c4007403420398001e178000751419040755100d50403244100c032004189644c5200030300000f103901d8900b400c84005424001d0b1942025200d0882440c2403034001d50400045005051a0070200000740c3c002c0c099400c1201c5084078100c10494403504451044d44c003271a1001605c407007181141c010403401e02213078070840c081a1a103085400c0c6903840100192039001c0580c01903881985510419401c0c02e008402071521171600b00700090800585910150310031480500502043c2c5d56003085800310350813411301035034480034240c0306d003000d001d103c2024019000e0f201404a00200500c03100700b40d41d10030030303041208488070f40c104000ca00a07038502600e100d440c0c0b00c000c5500c3c00c0030ba00001292006081606080f170260300051019805504200c9002c0c0d2a21410001103810581c0c0380b004004000103809043e01d04200241003080910580410320a0f0b007020510400602045480d00d150084060b541c030301c1c0c80c241084466072180c041041a0200d1240083c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 150572068 1250 150570818 150570851
    0x20909311208090d050301050103090809030609071e0e0610020703080c0c01020706050708030f09011506031b09050108040f0c0504060305010b03071505040509040c05090717070819020a0201090c1206 87
    0x41404d2a0f103c05003180d00b400b00440080402180840c1c1a44080000c1d00d090741c1c0c02c005040c85510680c000308011030400081c0352030b802c4610b020002e2441d00410a00081c0c08200301e440c4e0007070003901c503043c402c2c45180c422071501107075a101801c06580010075908540d0301242881e054a002e800f12400c0540c0c03480d040382c2d14443c00801070240301080c00801e440712503003000c40d40c01070b5407a000411122283d01d40a00450f403a44d0288000c66550300008202c0408808400303c1c6464a04025040034903260010b40101001000140f05800d1854060200b00c1ca207506030b00680b0300030b4006c11859840349000350080820140b01c52107441602400668415091040c1d4007051656a60906182c40d00040c80340c8a0006001100c0d2000c14a034049000d40b01d0075a064810301460303407862100c2031405204040c1c50005420032040051050400a0003482101807510b21107846200507907038110000b0881c01400c0d44a0003e02255800c0c45c00a42c0440d1403a1041da4140500c0c401c001c0f44016112040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 150573318 1250 150572068 150572083
    0x24629043003090902091206130303060509150105030a0f0606050a1106061f11010f050f100602030306210609010203090c0f18040c0905090a110402090931120809 71
    0x2d0000c1e841c89001d104030445070b00640b072804006003006000002c40c207002c07401d20700210740f5200e80f03080a0b000d0b1018550315000d007200601d001d0b500c0f98072500301041c0110660300700c081c003107041c0b01002012410b50000c607449801c441e00188000c00101d500d650005040354449c00309000012100e49000528a4012600302d0040c0390050003924114506015000d40ca00b00219036001e0146034034070098640340a010314003840707a00701e0001503686410400d005c04004003170b204c2c100712080c204003440500d80002c11290841d20803503190b103405109030412150b008540d1a58041e6000b141c0030b1103400e140540246005805520503034404490314414030280711241c0f072a4552145401c080300d8808405507a1941d0400e0240d4244600e898503208448140c2c0c40907660000d203035209a01c03c01c103001290403184030800c011a002c0d440d1140820010b204144003605800c07102414604001e030342a83c0f550010110000211040c208441c507080c00d16503040d0460007800451a14400204040b002103110b5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 150574568 1250 150573318 150573323
    0x1b040b030906070e012d0203040902040b19091401050d0b04020a021006060e180a021210030606060c150e01020910170f090d03050601020a0246290430 66
    0x2082018070741c034010040003d2428211b420741c0410080802c0c0d0004a000400240079554030321a0b03034403008201d54000406044002d401c01c6940e520511007032503d421201c12014091a00310384542d51602e410000300402d50407240d00507c0018201d01d81600411300044211154000700010341c0d495900340d03181550300d003203264802c90410201c5944880300d9010f90700091402c01c01400c0401550514000072000d5030030710b07428003050301c0400030486c5c14060f06000e0b203914039002c18400c807540da442900705400000c80540940360980d5442184095040d543c001030700400410302e1031203a24000c2d040c81c0841224484010008000a860610100b945402010300d40028608601090b00440c01444040d1496045010b0300c0d2030000942d03108100c8441c00d402d1081c8140001c001c80d50200c0900150381400f04454243d810450540c6d0030035002d10045a8043c1d218807001d02002d40351140c10185400968481c0e030b0003140c0491884144040641d4014490307500e80c00d02c008001c3c600b491101c807107000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 150575818 1250 150574568 150574607
    0x105030c0102150c070b100e1b0d09060f1503050c04050c1b0a0f2301060807050f010c0f080309122706120f06040f020405091b040b030906070e01 64
    0x242d90190700c50260007980f161340000030302d00384a01556040d00b00c60042d6400d40c40079a9100003800211650003456400c125410301a08141c0c601c9040300d0558021a54455145551103110758107101d042e402000081c03400020420900c84089550304003021380c2d00040d110b62003a512880c540b400d15105050080d0221191a4180300c8449003c0140b08007040d0901d0707590040070031034000100300c5800500c0203440750842d000d40001906040c135240e2003420b031201d02a0b0601c4003c1100c40c101080039001d42c0c905440c00411280c0290043c1e6204402c604002c100400b200a0b04082c04562409503000752035160035a4088445c0c001020b2190103041e0842030703d03107100180a030a510b444e0344100710400d405020f041c01c12a540524401c800340403145a1401505442044074914051040c20720b40c401c0c0060841c2418203190200300c090300300501803048200448010100480c0c8907040d900104000900e160392440d0007200c8503140c2e402652140c01207811094941c2c02c0798080d140c60440340000d92003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 150577068 1250 150575818 150575833
    0xf0f2d10020715020d09030f020105270c09010306020a08061014030402010c060e0a020103230c0d06030503131505070b07032d09050f0607050409091a0106080f0105030c0102 76
    0x30414002c1d80041c108603203494900e541ca40c030f1030030140050580c010551200150008641c00c01602c242452202e400443e45040b0402c00355105080120404001180381d50810f441c80005151a03c5615248140e011540100010270840c41e50001c107400c1c20b8a1f81c4810140e03c81c802030000c0c2c0007035000800d0124603040c002907501e0b148040070710b50003030052400c05142005a107e1108580d00800c14071040e8004106030b00a40d6010f005600c1c0303000e0611201000700c2c03011100c140341c6410240c203801e02d07180002400345130000700d900140d02454001d8192691000800c03583d2419a032070380720340f05603046a4514280070034001c1083d50982600103c8180055482d05000c40003040355510720100d00e168020502d031030000e40d490340221000c000e10000384421990802034902031001650f4100780d4018401c000c0e42c030f6031040c107840444547d5100418103c0e643d01e001d00c01840b034000e00c0007070480c0007000015119401204a400b442d010415041c03580d8985007459150991a054540541d01466 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 150578318 1250 150577068 150577093
    0x15031203050118180f1103120309030f071406091e0d090302061c1e0b040216030c1115090906011106150d0204020705010e1c090303050a020f0f2d 64
    0x100a01c0325981343c1c4030b58403445255035032440201e0110142c1030301e801d2240803500c0d109082c1000380c0c41050036106816411450710f408800d5036032041c001160fa00c1c05010680104010055810030005002d8406481d11850305565280da41d42800c507810304031030704400c0ca40003074541c0400c00b008131001d940e03180311000c0d0031a024003029a1022400940c1100c0d1204992606002d6120b188049402410070744408480c40c4402026284242c000600c110310410140300341003540c1c0412056550f0604085082d25145d040003c02040b1807842c258101881c10f01004681e144c060080c00040400c03a010702103a00c50100458262031a00c0800a00341d2008000c11158131007120794055070200280006070510301a8045400c3c0d800c911400c88850303450300da2217031b0b42c04024001e010115400303042c4080001c00201c402400010f9903c00030f070074050001a01100c0300d100340710482d01242070f07104036102c01142c1204241d403070702d42c1e0102c01200e00c10751441c0e034444945c1030f00d04c41c000240c00008282145000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 150579568 1250 150578318 150578321
    0xc050622020d0503071a0c0d1e0c110d020c0d0b06030304030b0702030304030801122a0807080609120712030f090605160f0c0b0c0c07050a06030f0b06040e0a0903110115031203050118 80
    0x2d02c0042c818039240c0310076540448281c094402500880d030f680040d281c8403501914940ce5030079054800f5900700c2c051840142c1c84090a0020740c6400c24548812a00c80e9008030f0308510442c0c0014104d0401c0608000c101500000158044c6220340d0f04d680c01c6a9031203144016450414270020401410b90f49911a5044622400c26182c0b20080c110b241d29070340d923103c1c10301d0803d140e03000d59420303048801001100803083c405082c0d01c0d41e0210346d00b45085166502d542c4005514001b50044c169590742203001044107600c034014055011800300700e641410302842c06000707a0907000800040b807410303601d12850b1180058602c0ba0342e00203289e00003a140e54042012540220b4000d508601c207a000000f901e45d508815072000b00b031035842c0080c0c4500900142000e840b114003882c1d0003540e00300010001c0140d10890103612400c502070006461140b883c00312512180454450921340c00d00944120598144064034200c0e482540b402400e400c0c00c1405500f40c500c24810001d43c40d13031440020100011a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 150580818 1250 150579568 150579581
    0xc110103150801060f060f09090e0106030b010b09040c020c062d1201061b1703060d020306010b0d18021c06150b07060c0c050622020d0503071a0c0d 65
    0x505011079414400c201c04064034507140d00440ca641e44030841040141c0c10144000040c0115140c041089201028040c00700d0b8002c1c410500e449a4404454801c04400e6021034051a4810b0f0042e4555a4071041d40703240d600101003542c86185410b00168542e4000249050504000303042d0350b0914003005416030106201010615105441250300d444154103040200700d0390034881000052941010f50040c01881407041c40f04d011281c0c3d105100105441200145401188aa1407903999581c0000f082a6400c030711002501131007024004542984401d0281604020b401402c0114000702c030303034101a10a215034069000302c803007070900300c1e020151861544494010b100205500f4000d4400218440c29540106803144001c03c40030100700c4180116400c030845c40c83c00000d07005441e00c910303403a00b101030901c03a424141c1ca20100075071a05c20b94008100707a0001c2620003000e10700e0038150389917803010340d080b6801020521009445a01c28102038010812020354030f0500301d082500c3c1c2c005241 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 150582068 1250 150580818 150580853
    0x219032103020412050a03090e06150c0c040e060604110909072a06090201080106030507080a0c11010e01020304031b030203090d03172502030f031b0910210c0c 70
    0x2001c000108140c09030301d02d41380c0031500c50801004601024140185103a87c0e54102c1c48910410f001480396a580c0d21546020421003803413403076550300e9943d4481c1c1c600440e04c68155045424000455840c840214600b4030852081c0c1d814010612110004529403261298141d80541418023141500f40b0030b2800d0910200d0801d11384800403003503010204a0b48000b982110819210840142103591020310030b401010282014005400c000202030f000e0302c001402101c000c0d5a8800100f4000d200e100710340d107180343c0d0000030087d059100d500c0d64040d600071207050300400e455000000082c00500c0f105117503281c0503400741d42040320100801030f4500d50004107500300425a10318111900355039031254014500568001103940180c018203001805907070000003507400500244051720300900490354001c202d181e4020b141010390340340c0509801008112601310005503c1048a17170b41050102000c032031005070b0b03000702c60040b4030414150360001c41e065002a0250f1110700015441101e440b000c0803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 150583318 1250 150582068 150582071
    0x3090307170405010f050f03070806060906070c090608070f0e07090f090b0f0306090a1712010807140a050d060b0d06020f1b010501120807031b030c0219032103 70
    0x952901e4080101c05001a15180e800c00001c04201c07960300044115103d800e20f041c098100102801490710a010041140742130207040c4000841c6680e0700001c99007141d600503c00d07522244642014040240c10380515400c017442e2120100d0798440c00030f403000466544440103407156081c52080301d080e000c007030040424055440008981c2c050548100c1000d0a0a08c2d000030380a41700c50300b00001590401090307802908040305205001c0303c0401c1c811b0195410000b824090000c24000321050310510b12900c03c5c6e00c040c00c002080c1c0090104041c400c595083c034141156500100c1001407584030740c03142c642c1c08511203000400040b04c2e9001000f030408001e110300410f100c2600e0305416640021000d030190f07603001a03440200340704000f41142c0010340030020802981004005143e44d076070342001800c0380c54081802e400701031090703581e4141a0070108160480c0001442c000d08030546098080b40f140d0303e20341c50215190344901c1d8a108a03904400c14003c841c800141903d0b16198400c003500825 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 150584568 1250 150583318 150583327
    0xa0f0203070c090e06060103060b0d0b0105070503031305070e0f01060311090a03061d1603030c1401060e060108010608061003020a031410090e060f07200f010501080705040c050f030903 81
    0x254400441c00e00034102890080b13001e42c10400d929003000c100401843c10326150000c14400000014141c655040d400d041c00240408150b006996501810714002c040b403000004200501c0914440e5600d00c5106000b1a5541c40d01c40301d0070055a4004c842d00b1000222400c01001003034820b0700030000700070b9a01000f80c900020030000c90b10314040c03078106403003036601d82614044900c546035101e040006507001402184003000d4001c2e134041000c0c440034007002030440b514002d002001d80d40040041045008020160b944c030280c1036100c108403100c0d400b08038808000038010b802140c402e0311524008001041361100c261094000f0340201c0081402c15030354100da21071240514600f94050120a009203a00c0741c81c2000c580c0c01d8820b1840303240c04980024080c090b660040c600300c61b41004980c2000e195a0340f5861030910703c3d10030b400c0c07038100a00c500d6181c0e02c80d844040d0b11203410b0301c00010a6806e02030f162028002907030700c0b80d400d9000050381008611998440c1c4009150008442e000360b030701e0b1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 150585818 1250 150584568 150584573
    0x615010e030f0f060105040905071e0b04090b01020c0d0506070c03140a0216050d20040b0a12060605100507080f091002030d0c08041a0702010e0105100611120a0f020307 74
    0x1401129002d01510b42c0c01001498900c0c0010801d140c0140000c66080c40810540d076501c6d5154049440788040c40c14001d0001c44000c90301d9007481e8040c2541013101502c903035654800c140540fa03030600e001c0c0940210124010b95090020100ca61140c20400030803868032181e0b021111901c0c202010f60800204081c4510308109140040c100f114443d4010b1554110f0700c1c010101c07101203a0311540c0f052a8400400300018030315290031082518602d1100300c450110000f1030042d2040102a581c0300e8000c030800300c1d525081c9150465064010030003040010703281e40900c080c91003034540c084080b99080c80006c0016521000625070741c4d2200314207508002d48040410401d404440002000d40c1010034494880d440a12911030700c81c80a01e000c40c4c550600e07440342e0402d10342410780030004800003c00155054002d405c0014404d05440003003240d071a00c80e890300c0c1c41d100c081c0a1500095600c41c00d9039800030380015001032807175460703111500c1d003041c00d1407d4514103000c070300c22025408144240307000f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 150587068 1250 150585818 150585823
    0x40b070b130203100e060a020c070e100806043008181603081b0d0c1419081306020114070503040309150201050a0c03020316080903131706090a050615010e03 69
    0x101380c05075032001c074105c8501c2c0b00c5a0b082c800c0c020400c074030780c9105001c84c1e9103000000646004032121740c80626455290890490100117071034103c056580304840a00081000351302002c00f158200c6004002400030308120850030150207000c0390300050313851002c80c00a40400200c800d122041004440711600641445030403150162310642d04114041490210040625050040e0603907840281080c08030340e60000d40f004410000c05000341881030060207135050108102031076010f4165200c0b0b4050306905d4180801d920000d401440f8800c15000020418014000c0c10903003100c48190b41055510700740d0444064000074815420800b07040000521100c10409202c040c885660000c22076142c40c80f016015511031545070310825104100700030400120b8000840d4400251400d01d090b511400f15480c5140102034001c400c0c00740c0e2450018103030780d40e0070702c0907844041c0b04150384081d5034562800791604a0220080d146400c1400018161030341c10310107500081050600c01d280d008e1500c0400d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 150588318 1250 150587068 150587083
    0x100906030f0b03011407020d0801030c060e060403060e010e07080c06121f03030c060506120607080c040b04061107080105010b070b0703020f0a020a05161a030901111c050606040b070b130203 83
    0x101c05200b80d5052003d1309505008c0107900da102d500741560386d0f524540d82c80c50032403034512980c81000b02c0f1500040c616541e44044030025030b0404824003111411140090003014503684030501032140e1400044c5408020079840c01107100146400d040540c07502c0d8034070707148000600301c2000030b010010003c082c1c3d0502041102a40c00380d41d62110070b004030720b821400c5983c0a041588541c5c4013800c0c01d215a01d00140f40d9134408001d1a2203201c94075085090481c038015078004440c542c0000c14081462a402901034090181d9403080b220b4031582c4806e41e900325034081c062039500502c10440d02c000310f1558501190002041c0c5001840c0c07030002611040984c009150780d40058001c44c1141050000801c44000000415150070f40090318099030080314110b020003001900c8404000502008420b50144060b24a8100c0c6d03e41c0d5444030006070901c4140c203140c0c1c4802c040c6000301250705401c0000c140d030180e0308065483c500e4510691168510720200400c20180c01c8404c8107440f005031803e000c0304 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 150589568 1250 150588318 150588341
    0x60902131b0827010204151809050f0412020f06010b0d05180606101110020c010e0d05030a1515021606021906022d031b0f04060c030507060615030605100906030f0b0301 74
    0x100c403045230044a0048440107511000040e4140030134000740b01d40c14a180f540165005401d0808445403038000d906010032425401518040c000000591841c1740b40107000d0a2640c0d601040030340c0e00c5060240140401c18500542503109500080b681c4c2485201010560000d007032903041501580c00c40e910300f000f68a08041c0d016004200d8141a0100f40038403040400c1c888050403040842040c0104036000007008017016540303500c80080d984107035800e04405405d02d1030b00f03811040203501002c1e41c0d880100c20007500d0310540d42c10019a5a1000c140c441c10042c100504100d8000e003922028040d405c010b0340c0c40d091140b00041c62100c1d10000700c200354464294140940c0382e103480ea40c5c0150a20504804012400d400c1115903a000800c0044078251201800d102754583c05908007101e4600400c00700030f04080c0742000128031400d02c4558070019041d290780a000c0c15440301d0501c07404c03710007000c250202e1002401440000e000f0f8001d1417078101000390000d00c1c0c0e035203e400a42500c0440115 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 150590818 1250 150589568 150589577
    0x19140c0304090603200f010305060f0414040507050306010b0301050103091401090606030512090a0504200703050405030706090806150103270b010f0819060902131b082701020415 78
    0x10010007a0030802d2171040c240000741c1c2240410014081039011010320101410146d94200207060ba650710004280e400c00003038800c000706220300041c195840c0c01902d0a07603080c894840001001d180c0001c0ca1b030f0580740e01c986540d04591030070006402409440d070040321400c41103420b682007e5001d1089002d1745002d80c0f80412003d2860510600f4040d55a410100117241042140030303d40750084401c7c112802510006151039010702102003003040004000b90b00a0001020300034154040041c0c003d030f031022000d650010380e45442c1a80c0445182c82a021103802110000340000c0340041c94031078503841810040342048a19610010741c01c1c0038141d058001500358440c0d0244881c034001310b070142c004040724860050a0808140e03844024032076010031620300c9204030040040d6504620480380d8080c120032008440440d1100140032101d4400306007244141915440781d1141904d0382c00b0b03a00850009400b40000184850035170403d50720780050307640030040080e0250018829031480c8a06546 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 150592068 1250 150590818 150590831
    0x1e07060c020106050604050f060c16030b0c1c09051203090102070606080106050d1202071e05010e0d0213090813030602030709080f03120619090e0c0619140c030409 72
    0x5106044510040319201160b00d4490107101075110407080b14140c1e901110390f421503001610004940d4402c1811004080c0a178054841c01e81840b03054860541c1d12075400c1c0d07500c1c2d5580c2080e182d1076000d140850295002c101c6842140240194411154070b4001d50540315182203074040039446920076540148540e41c002508020300c4450311480300504000344c000c1c8045c84c60b24001502c0344001600103005246065501350394036008000f280b0082c002d40c1c4081015558001c005212480f80340f088601082c040864580c0e103181c80607501000980c0107121100900f00c9108610041a01c941c044880c05401c01000070a038140d0021903008510590340540c2e24600701c08000c00240d8243d010b009186d01c00c2d0a607104044000c8155080b6042c0d0b00d050b102c1c10740c0d03100c2c0020b10a07080b109459070302045511010411000b83d0300100c0200c1d603510101c0b90750f41105024080103102c0c0c0d284920420454000c07550185204002c1c1541e8001112031107030034000c4c41514641075900c2607109401d240e9a030710 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 150593318 1250 150592068 150592073
    0x503120c0310141f020f16050405010803070f1104060314030c070e0106021c031812030b0607020a050d0303140717060108040b06010806121501050a1203020d0e04021e07 74
    0x12600009042000c000c42d04030340110740130641380e40410383c2c80700104400c0c1e400881c2c090300c2046410304142d503a1048508940d002c01640325070044a00407107000b60305200c008901e07200000115155141c1c001c40c401070940098454010714040b007000345a00c0340d25070ba0000081505103001c0610b401d0180d01845d902d9040101c05450500c241e0b01c02d12007114008010481e042d004950919410486054107195041d00c1d50304800400d80129040e4415460301c6c4030701e06101c440516030580707000c60b45040042002c080304000c00c60288000080d4480c40c410410300a5040c0580428005032080c2804648582c4030b0100e900c0341c3e40100c1e200c4000440110000015210107405281c00040030300b06040d0a0615840341408954010401d40c14000c00b00041151500c603010303c4403007040c1c030f20140e950481f595540500082800c1c42000d10070f6075645804200304218464082c0c0c0b440c0c0c50740061615030000f9405450180540c0440c035481603003442850b000b0030494544203002c80c035500385940e81d5003652 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 150594568 1250 150593318 150593341
    0x140106050d08030907080d0804080306031219030b041a04021305040e0a03020129091009060b0d05150306011e0302060a03020c0105092e06090609021903090507060503040503120c03 79
    0x164010201b80c0d004002154001d508000055003003070704040d0044c1c2e2503548801003460007103405031150004100155144201c2c0c5406403602c003000181d03405000069040003040103071010b20b0300089400d0344841010b201c502d05607009080c00d417100100d11501c640d968000904940110a8100c5603400450540081640c20701c2401205003070041c0c2e40e00000c07981040c0c8085444030300c5803d4000c680c0031003c00c1f451400c401c0000d00400c001041030100544400928100c1d41019114101d061308000100b18411000c0b9091111940064003c01c3c40fa0f207020b45961540340700e012440d1083d007407500040b026850f0b4500400c458407542c0c90242c2e4400210024034211000203000e55417a070824001c9003190314655040103052108032070300241509034048200010115540151a41840c0c00340028043c0b0040d000f9240d19131046000514407401c1101c01d4003a5030740b20000030125000220f09106c503500a00c00707140c10501503030450f418500240c401102180054455031101c000100402500b940c84 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 150595818 1250 150594568 150594583
    0x9060e0c07030909110c06090304080c01020321070c080c0303060f120616140c07150203031006181d010f08030a0903060c0318030c05011116140106050d080309 70
    0xd6035a5034908201901d006151540c14007402c0e0311140c80326003a8086825000a0320f200e041c2880542d4940d003410b00605907240e125105618031802900c81100c0c01e90700110654090950881c054810301d14035a072a80c40c017000050600043c080c9418049010860300e02c05040a07540d503c3c01540d8a08001003040016145080001c0c4100c00a41c00c102c015000401c0264124074030b071410f009014804a0709403110005034041c0062104003040c041c60b44400000d900c02100c9000a842001025948080b03846e0301c021135403400b03036515120301041030611808401c00c0010844900c115015100c071410400583c00d05a000c803815140d00c0144044010603143da4000c0a03154010762800c45c1108001c2e007440140d120107402e6550320218204e590b402a04a0041c95102c0744001c00340814614004c0e0803104101c5055415610b0030303c089010800070b07402c54540781030088440343c4180f92507072030032016014498804115500c4010026442c5c4401810701252841400d00d240c03289000015030380380042 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 150597068 1250 150595818 150595831
    0x2060105090705121902070602030a050c070803070e03030d0905010c110106060e28030f1202030a090302190e01140312033102060f0a020d0207030201050d0f0b040609060e 75
    0x54010512001c1d58000c0301300d56a41842c0440c40090f541d40c212603905021000c0b040100481c00041c40704c00300042d40e802180b00d26200c59041005480d503201c20302490051000040590b070041000c100321901414040c1d1485c0780c02001c591a0140419100050700c0255000320345581d101c0d10b21004458000400034500c0c24000f000b084030510f04800101a4107025105a0140f0924101c036002c1c4400c040d0020b410946031000b02907210f6492030880350800f0f1451041d201d040641e690079111600c00701c01c940c84504180d5904860b01c1c215000c11030304080e1004504099035001c8000119520250030050091044100800060301b0100600d07040000c0c0c0c1c20407a0421508000300030002143d40c50300c81803811881104209001081948111101a810045c0d440800030400c0750b5400301c1e0b000144603005d110f17400e8900d09101c2007000c1c1e07a540c03480c0c08020702041040c000080c807111180d001a200d9014000041114951040440d08443e055040803901c1c2c0e840c1c8406010011500c0c000540010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 150598318 1250 150597068 150597079
    0xa330e040e0c0127050d03020a02012d14131401021504080301090b060408030c07211101050901090905010b1905040b07060902060409020a090801050c1608090301060b03010308040602060105 83
    0x80c2c0190000b801440030b64a600c80c07004446000c07811081450408401500018004170381c1c000c590308000e980c403032540b20f00b20f000854061440340603080002c1c0c03280b07900130030481885041d81500400d07111220409040728540c101809220040e42d1000341c1140102984c805003441002458002810701c1507000d110b18400001d0b5090000107841c130300c01c40b41182d540e06800a85104200c0024240b403003164000d40b214400032442c1d030321964010600c0004c980c4c00b038000244010480103440e1845050000162911900c10705018055009800410015005241851565890b007034008101d46080c0c002e81018000462908003180b044500d8001041c0301d800d126042c945400030a83e103602c1190001040b042e100d00740c020440d140d220650f00038103003144055485a1800c10000e240100c544560b4000350300704004150390703035a02e10882d01e20018804410b1101030803078031110030507031007411038541542d601d440c0000d82c100401c0207103010718400c0740d0030f59981345010402840c09070b040c0c114600c2407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 150599568 1250 150598318 150598333
    0x20d02030c0a06090503070206031618081015050a09021905030f2217190509030a0201080606070209041211060c12040309080712061a0a330e040e 64
    0x5440004a0703098840c1e01400221301581c0c81e02e4414214024550000d4124001005000000540100b12100d11030356130f17660b0348580300d91178048140a10502c1a003241380c02900d808505090282c00c048040c14a10803414025030b03862000c80d144036000c0e8042155039601150132400304000e00492110700b01e07203160190450810042d54007010030040d218050324005a8007008070344216082481c001c580020b442c0d14003101c00f00d404940c9034841541e007481715010a000860785400342e0140c803250000a0024403400140e40d006440d400005010701d540000300b0301c80b041c01692002c1c0c0452013030f07215010300c410341c0d5003040002d80105a90509041160418800c11075411880700583d0502e001491800301c040c0c03101e05080c1c0d0841d895030442e641a000f840d2011614410301044501080d10070f6200b044102d160080801c2c41003100ca100030350002e4001c20401003001c81c01005522071030038070003058090740c21082c0788406600e00d200f0240420305003030140304580b07814860000141000c2c006801030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 150600818 1250 150599568 150599587
    0x1e061f170c0403052e050406060e0601090b04090b010203040510020325030e010e0415060801051201050f0606130e13020405130f061a0303030405010f0c0f0f0507060207080712020d0203 81
    0x107404080000034245c030410500c441402030030791002d403101d60803103c003081141007500b00400a00594002e21a44104c80400305283c0e510401050703040300c132031410746400d15061a40101c0507040ca0b14850703046120521002c42d290380e80c0c6a00c0600540143c00071590348104004041c0f03080581c0c0440c0c40480030304460000405d4100241001a100901c2c01e002101c041c140010300502e01011b0064150a0f030540100c0c0702c030b4001c0700803410380c8e03c1200d000c0445440c000240742a224201d5425000071040030100b82a17003485000b90540522030703001c1d078038580c0d00e540d071402d82c3d1101281c00400e1588a030302200f01390304091050b15002008d4040f1302c4455030513919094035030b00796207000070049981e81551103507200c40d800d40c00031403c400038280c96413800d007820601c0c080c29014489034000b628258103000658091400e0382404442601e070a415280b014070280c5541d04a6001642c2c0c2d2a001c110700c40001e81101c005142480c841c0350805240210510024503100e43ca49800f81558010428081d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 150602068 1250 150600818 150600823
    0x1b140111030405040203070c0b070e03011a0a140a2d05060a020a021203131403070801060302180705090a06020114160e0f03030415080f0f1e061f170c040305 69
    0x103443c8243c2e00075a40340c0312810b00300c8070000e07070a5000e8a05c40c0003200b4400d0869200500c0891080100d001307012500340300009820514280100035880540c4030300400c205401c08452005c0070130300a04410703005540300d03400c1c030700c000b819402c84045d1183c403074803814040e4110010f0005003074183c0700642440541040690365400769400a032090a0070b00c1a0080d80300f0400444000780307602e0501103241c1c1c1e5942c0d20003610100703028800d03109001c3e2480220342600144182d41c01c584c0c0040c0f82c00c440c034690400c04040340d0780c081c016804122007040140d809441d80d06091008050a500000780910200c074201034110000c0c00c450720442c840742210350060f5200d040d0749441801180d10340100e22103080040c1ca036105640c0308820400102d0030807a103050700412003510402140040d1200345d558910405078811084843c0010030180d1051070001403c10a1a260310160140c040c01920b5452040c0c0c5120002d41c50a0360009028010202c00c408202208180c111525001c0c640c10142560b4030f054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 150603318 1250 150602068 150602077
    0x90604150603150f06051e010306080a030c030513080a150f1104091508010606111002040e04030e01020c03060a05090118020303070308060315100510020c09160c1b14011103 76
    0x309456107030807440c1318003001c81e48008018000102034040200e06100e0400c00c0c0c01c1c20251040c04649055030004040300081140400c484c0d065071205001c01c550f550582d11034200c1680010704464000000c2080300301001720711301d220300070201d803501009004010019500305418900d4011300b03101403540307807140c80e00c25941660010040400c00071850980038404007210746c400ca00701e60810345c000440c10307046013400c0e90045054082e56a140d00c807407580e506901c600e2184ac00035500300c00014001c01e20940302d081d8000070510580d6144100200000d14020f400d40d5a071000f10340d40d031700f03104181c0801d00c1151700418500f0b060004402c2d040e00003030384a014400300603040c0019503001030660303a000d01456a90543c40420348681d0304100d4541e01140b0700e28010b080c0039114035a5a5004280005069407822400502c01c8001d0355965070034285010070a85d070001880042980e2000094446242003460b903072244402d00c90900d4060340c070b640c4401d0103824505000b40c84580703000000011080780c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 150604568 1250 150603318 150603353
    0x90d090b160c0b0306040c0f0503040b0a1e0e0f011a0409230c09150616051c0215010e0601020d08090a080a0507110a050604030609060b0603090604150603 68
    0x9034440c1c031103038212501c0740c0299000801d0703010300d42c0c000301e2442800b401460188006450401401c0000d00d4245c841c5c0c040c2040000108500744000340000c1c0b0015001d82e80050411408242250400300d40d610b40c1c85c054030310200c1240c803611116107040040000c0c0d94010040d20080c800c00510364201450380141080041c040c0d6164445030090050002c504202c5010300000c0100c41c290010107241c641c0041c10340c4601c0b44a45c280840c00303866440176078a00203d40181803500d800a16050040309020aa20894950081e00b083d00229489140c3d001005170387c42e0090440d071048600e940c0d5003210141c1040814080c41c0d000d02100381d134005401c07082d502440c1418415134650250241c80d01e641e5040041a0a40002e080f8940c0c80d4080d016040c810310801850000e141d55030204503112405003c4c5a8201c01d083c00100080780d0150415500203010b507800240d03040241c00822181d50003121102d400c0d610400500c01003015045400e0f00b00d29040c54104002801c560301d800080242110740c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 150605818 1250 150604568 150604589
    0x4090203090a120f0207080c090a0b0a05040c0909050f0103030f051308070909050114060f04021c020f0304020109080c010c0b06060c0d080a0f09050d2105010905040b090d09 76
    0x1e0008841040301a00c442d400c5407001d0411004100300a0202610030008401402840360008800c0f60014120300307040c00007007104000c0e44c0c50610705002001d09442455101415000000380d580395485001700a88280d540c400100b07042c150031b034040c1c3c0c0380038101d00c0c0d01602d0840100082648a06404442041b0745842a5620380100220350a4012034002c016540100e0780c0000302c0f5a907a41c02140f03050b208400a000040100702d4000940750120388403900325240d4440004107203010f600420f1000100c43e41e0f000c00344204400001281c02010b4141c8202c803001080c04107641c2c00840f014014245440105410426440001c4c0002c041090041600490300d000c05c0403503403424140e81451018104803811041c43c1701d401000c9d5501641c00c152043c4c54100410035480440c0640103c00fa0010020300e0308071407403801200c1c0c1103480010351003d41031490910040241c14082d10b40240045c42d001300702070510782820143c0b0f050180217041107034400364012038643d401074644403c490301c5108 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 150607068 1250 150605818 150605821
    0x123070c0314010203060f0906150c010e0f0d170411041505060d0603030311070b15121c0306050906090601080402040f020c07030b0106180b0708040b0a0c1502090604090203 76
    0x415003081140e540000b880e903140c182c8140c103002c405501440c40f070f000c01c80b10031700410b4541080c00b0010300142d56030b40d00f00321500b80d00340307070030b010307980101400700c242e10000a00103c01901c06051050610b480a081c1d00203080182a5580c00689901d9007888403a68034901d007010b039a08070743d1001e180710460042e501c50318440340f04400001010002c04d4003814480da00c16924148000030185804210007113840d100300082400c40c4101030754a101d074010034070742040d1903202e05010003504d00c103416503101d0000c1c2c0340f07106840700c240403081c000b00003440c0c1021180c5036008003074281c441940003a03010b103503c40e040082d15602d40c1c0c81d264000e802800c0003070032a140c90003c58007a00e540e03c0912201307400022041c118043c0002c40c002224010881e00c407090741c0b1004101c4401132034401aa0881403040c030140991400301008110540c4104003491a1503512041111107070042020103010036820b03640302c401d00c01003030b65a500c00d01d0040400c61401c103403900014214010f178041c4aa100380c0c00700 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 150608318 1250 150607068 150607073
    0x50105100f060f090302270c031501030504050c1011010605062106041409071706040b070f090315060e070309170702060909010f17010504120c06090606060f020c012307 74
    0x1310300e0300696000791041c4100c1550280c00028542445c0a0100c211407040002e50500b500905590207110b00020314420b0380390210044001d001c016106550780d02498001c5000c079a100881001c4e152081e846800710101300900603421513920390f11041c0252410013900c0404d0744034070f056105000700d0720450b00441e12082d0104001f065050445541840002c0c240411800c0001c0d4010072281c2d0441151006015210a2074880d2400c0e01c00400200711103000c981c116008a4080c1200303c11440c0c000140d5079241c132500c250b0300000d01c2e800340840d80d40b2001d1213900d0700c807030300168804e4072820300348030070116541ca01100f90084421058140004550b0004543d101c0040382d5a400b8000c000c2112940c4504c0207109548451007540c400b040c031001d0314940808180500c900c126000300d040300e400350700d904054070300ba48690800c44116a0700d44240b00016114441c50010300165522002e40d01c1c1a007c002c2d2404180801c42410300801e07590030030410b0244000035043d4441510407070388502030703031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 150609568 1250 150608318 150608327
    0x270601030e010212010303120b0103021c0506030f06040606050a29220906080c1c150209190312051c020c0a0503030903071b0605030601031d0a0807050105100f060f 72
    0x1c5180c4c5003548200d00c000010302d5808071602c0f69103280344004004501414005408a120b0a2800c82c03507210070340214108004103900265000c24003900761222a1020794010341070a404840884005030368540901c21400c00c4040e0501610303483c02148001c1400d4641c0c90030054200c1c00c02071426200151044604240ca40e0001c1815403c068010040c0d889600760000b0300355a00507500d5901c41c038440782c0200c0c9000000d0ba00c41d0803858001c0b035007422803600c9a544001401c13803a00e601f41c1c0c00300203511276500c41110005035400300c00700f0f440c20f882c21807415109210042a02c0c604100e81400420f01c1415170b401c041c3d21800f044000142e445841c0b880507800c141030800094041c0c08040308100c2200c0c0c0c04030080c40101c4c0701c2d40e48408190b8040c460764052028600a0200151050002906e0755009a212400a12030390915002c3c02041c2c00a483c40c00c140c0010881729a100071800f1000c020382401529007003080d0a2031025008d080c030b03080445900c92132080c081042102c003604201d06015 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 150610818 1250 150609568 150609577
    0x3060302030c0f0a0f08100b01020601031a0a181b1401020c01031a1207080705101e03110d0c080f041106070309080105010b0301031a060a050f041b0e270601030e0102 73
    0x140d0380c0825175a42d80d034030001e45034603a142d0311032800f0303003842c1484429604c0410260705032907003d0307040341004085c4103000010110041130700061668031215002c1d00c10289a0700800d00b03208080348542081101404082071417181d0142c48206408040b20034660703008254802044800c2c41d00007110341654a0440c030a42041d4405500a4801150301c440000b01086035401d81e480303281103a030030035540c5050040c01d43d800c40b81070001807101d840520500703001040c2422804207525000c00d59100c2008a80840d0b4071000d280da07540340da550300140b480e030740000e1403641c8101c0e00500448a4a45605e039081c5051030524101e104100000e02c08040600501440d005000680b000700310a40c0c440c010154650700a0200740d0741441d00c9804c0008081d091070320341c0c0c402c00014203010721852600051190030b8107010500b0307134010b0f182c44000c00015001c14001c103418645590b0300141c5181d050501c903401900c50700100c01b5503000d00c4141400d1045012441e0801020700c2e00041c5070600d440168028042d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 150612068 1250 150610818 150610829
    0x604020f090d060b090c040617090c04140a0c030204030f08030408160308060108060301020712140c060f0103140708060c030402010306150c020907030c081303090807030803090d03060302030c0f0a 86
    0x454101e0042031041944c003002e00420140c0e800a040e403590303140c1c506940950300c070340b100003607a841103c000e82d03c13554900b9400000341c1007200ca8508504001a05468614008142c0004024100302840c50940110305602c4903600381103140a04503100e412034000c50003405040307024000301007410414214202c4041c02d52650b4030a013904150324005043d0301090740c5542c00500e503c00030034060301c0c0c18422903440542c0411050404d080c070074401d81e0502c0540c6524802c1000901140301c1d010021b02000b4454003038041b04045660440c503282d20740d00b02d0501145600c2c0c0c03165105000d034100010301c81340c00140c2c100e80e2030340742e43c0c0302d1004a0251001e900300c051096201421183c51799044815403004610899451880d40d42d42401213045401c001218000140b188011031440d441d0078424050041c000d01c4d103080038546900160b840c11060340d0048950007000020800ca1070703401e028150941c240b5250a10040b03255400294dd601c1040d4140703840b5a5072042c2d581455554652100010300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 150613318 1250 150612068 150612079
    0x12020c0d06050f1b0304060c0e0d060605041b050301090b0609060703031b0206061008040203030409050c03010602010b040c051209070806090c01030605090f130809040504060e190b0604020f09 84
    0x2001c0c5400030181800369150180e680108003c2040410380600354940303040100200d50842d580c42c2c840e072014000f00100101440f0714035402410945a0340100f80c811406017801042d01460001400100c6102210521041500c4100c00441c6584070701203e0440e0b1000300301140f00c00f80040024118820300c4502c66102e0000038484007003581640181c01c2040d1201c00308081d440c1d0b220001e80c0c40e840200d03515940481e0040012284a001d614119005400601101d0801d03454000307050403148103890000a28a010004108490703090150400040e011b6170f083c031000444440251a17401186140180e600c4900c0016440036400c0020000400b003480841d0001d00380900c1040d2203810301d07116070340000c0c100310001c20750b810129803407030040b612913440e070364255503520060030301c012078550884e5080001c01c41d42c0407558582c000c00c0e0095002d0b12001038402800766010b403400100049440008801c1d01b200008101200011944040e064038056961411030703602d02501e201c2d504e04a81d020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 150614568 1250 150613318 150613339
    0x60b0403060c080f090309100e130912020d09141201090602130f050612070912111201050f0a0f02131805010605160f03142805070203030712020c 64
    0x141e150080349031036085880c0c40680e0f451345002c03074905503022500202164410800360415040c0f1099031607803241d461804407903416080c0001500b1450b008a00044203850384032a42c28026400340b800102031403400142441800070101400e000c2c00c61080c4200f40003800d6403841141c0703c1c04000560104180c000300880c1d2031134684407000350001451021030f11001100859901e800b00440b006481004041500b44810351917041d04140c0010100b0003080401c65000071004030318a02c60034804e104004006403964080b0038020600031100d0081c0c6c1907070402003403150300c01150001e150006151745000c240d80a40646d0303000a4403030300381c0301b41c01000346281c0040c0d400410740042031805807944086c00640d0383c81400300c415000b00380e24501c41c0001c4803948400900d0500d40110f10b14441c0c10950030100340ea550003407290700905003529690f09110b10240080840c99403107400e003801424007509100076034011a0b030724042d1403001040c3c000031b9129029068001c000b8008091001441c0d080344 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 150615818 1250 150614568 150614573
    0xf03010203040b1b0f09130204080a0303090302010c03060e0417250501140603061f05041802010f1b02090a0e03040324050105010c1104060905151f0206041401060b0403 74
    0x42c1c03103007107982d8402900c161a080203544000070845e48078000403180070342070100c1070007000703510742c80c40d049100450307820040050070401c244a0031600c0790107510001001d14190801a00303544200d990f920030141b400380300b44803100c8580324641e045500001c0c0a050300c43c1c4c401034448180705051080c0031060a8505800b03445c500507c520420500c204002c0c800403c1540001c81180002c0d9106523054000000080d00c0b1403000d40140e084514941d00e081410b590341c4003203000c840312010719035901c5021104400a558019801aa11240700d00d021842c0d4401003440a10b4481c4044001384200503200120b00c22210580003114583d0051094990303a66892070400755003520b505070841c0d1301500311418505c0d5011403054504036070043c1c40d40d51401d01c45980380c401d00759400d007089602c40d40d2842c002c2444030440c41070511070800d00c944540403400c1c0c0410010180021000d805140c800414203603059a408035803181c001d507110b014600c00702d40c1121500d014048581180560b10b10100c0d0020030f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 150617068 1250 150615818 150615833
    0x61e0213031502030c040501080c040905070503061e06160606211209060813020418060b0f061c15080307060c0f03021303020f0a09111201060c0b01060305060f0301020304 75
    0x11248640b42030400c60740e514920320140e000c01c40e008940403909100401541d400b40c02e4660340081d1620509141030f844500c85000c0355415142040051070101c10000641030070134074802448190450500c030416000c0005006100e41030b2a1000c00c9101c0f8580400c000894000e08060140c500d4440758688101d8100700303c1c06c1c0324220a803803034001c980e229000180204c2004040d1502603487c03201a65a18584014600c1841c80c220381050b510003030040d1107084000844801ca02c80e00010494508150411a0013003112002c180b08880030040f54000542c58000050090101c5c8000f0505000442498007000b503664403558507408006031941c1040101d40c4003005c0d9014036290b01d204802105400c070202e010b03683d0b8681034001c948200340301525003c01554000700000b03150b034001d180c80300c002c80180c850030300c01c00e080210302050032280590f03040b40190141c4814a02807480d40d81c1510354200c040e10600c150020315950b0f2011036182c1e01c0d030005042d001c5034094000d540e2030401d840c1495 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 150618318 1250 150617068 150617107
    0x705062505030c010c090812071a1915080a0b060d171312031b060b040c03020c0f0307020a1e050d0311010506010e210703060e03130e010b0304061e02 66
    0x3c040c1e519000d0b444139514081c2d0004c1c010345100d440280328030600b810200740180e20025080d11b407041c0c034803441c1300d000440f680c203d4440d0300c100d24101c00400c2c43c000e0180c01d55603200ca05c40c06202010005005001000840407481c5070400841d040a45036000420140c15031f8220103031402910000352030001e07507038074014041000d07019600b5440035610408460310113100d80c2c00400044030108143c03000c20050800441450166034006000c0b51080000380440d0702e050381c01804680c011808031020602403000798144c5140c00f016528018481d030000358801c0460082007003400d054200e2204807852516031801401c00038048180301121414013030318429421150000c190f091600180b0340303505c20040c50301c120001809104201c03510411018801001929102c014420007000001145c01c034040c0c890030030380d180040c5642da5080e04601019592580210203481e0001d00104601c0e400c41080380d070f03c26000fa500007940920f800c520040340c0206000d001c1c0050010400d85e102c0707901140c0300c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 150619568 1250 150618318 150618337
    0x1806040f060801050306010e0103030e030c1207030b0f0f06010f03020706020f0315040c052a06040b010e090303010f0504020334110f03030604150801060608010e010611070506250503 80
    0x302e0490780e07a181010f542d40c40900940c0e105000f810700400c006405902c0703101030b040005003920120b010f0f840128103075074580703101d1600607405803108205001c1608441c0c0d401c282c8948041c8041c0c41d0006042c00310301c0b070140a46040201043d40b0301030041c8240d040e1195030350300c070b8070a641d50803050421030803580003a12008403c08030190000c10318601807140034102c5041d03407a000d041c054400140020040c0194003c8510030011203100740910f0180b0999214038410680400c0d1541403401100c0320620040c41c1c4901d586c030404c018080b10b250758490030100e5008030382c09a52a61000c2515000c440705680c14060104009915007000000702d800000103400c035680d044a5250700215242d8900c44800406100c1d007003040480d4050900d508044140c101c0e15000d21000c656a80300182100c9043d4002000140c0d40c60051029594114510340189401d1a0803250b005c4503503159034648500344266032003020006060b40d4400281c014a1a01c010b181d01c105034014024180ba46d220b500000d00d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 150620818 1250 150619568 150619577
    0x905010f09051b0906210708070c0b0f0703020d09030e100e1503090a0219030201021204050102030d0b0a08030a0201060305060601030207150b04021207030b010806241806040f06 78
    0x89a1594507100c2c0501c600d286007142e161541c0641c0301d280f215803003038020507049602007040041807444803920710120000511201114500010010030800001e0544420060301c10550008541c2d0480e0031500203081142c9007107140ca40c2c40c4160000d01c14922081107282c1014041004c0c0758100c56200d902e004180d52988000300300380d40c00c683d01c14001000d15884001008007003404000b1a010359030001c000e9040302c0f01d84030940c00190411031861403001d507121000300c05004559061100c0150994034200103400d050401c2d002039117a0091420a5150b20703503070b2101d00da050b5a4000450010b25103801500d86e0741d882594028040c01307442c0801d9030584038004c081100c075440b0b4400c03145050303008070001240c03200825001002e400300314641944a90240041240da180d0440b04600a09040d140000c80414510000d1300301d4100420b010311815054449044007034101640f01c80c047d00d5001d4059407094800d505401d591001c0c07804030340251700460040b0ba9110350140f05070075222076445 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 150622068 1250 150620818 150620849
    0x1303152009100305010501020a080705070b22050607030507020909011517010e0f1f09060612020301050703050c0d0c1701062012090d031e020303011d040210081f090501 74
    0x1401e034295134080c840c443c010b038030881d07400c030100d04910040c160061262066841079551140c0c440e55076004038400d4200000348100c200300d200c1c403055100c0010882658042c0c100351890300c1c090050b00030640046c0c02003900c80d00040d0070040a40c0141d070b101c14040b4041d02d00039118000702d55400c00c0700310120310561810b44030204013103001850b444180e030200300a0010001c03180340d140700c0080c1850028074168aa459202c0050050300440001c0c00d51066107c104840c2030040500f9204c01070803071401e142c50b10090041c5140090201c510717074040c41502150340000c030801120035001003220038821480c014000f15074280d001c482e070001c07000f20400c1a20704090300d418403074a80103005040319482904010131032150034000c10340c0d01200e009052001c10f07003a501015404140e025800b140050f04004010302141c0c07004d40101e100c1c030b000c0c041505854640b507804a9803040e08103c11307a00313100c1c5400015008540c1031880b0b46810320190001c0d06090350343c102a1010380001c0c00b4000301d0010f480c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 150623318 1250 150622068 150622099
    0x703060801050903070201050705030d022d1303110d020d050703060605030d0903260a02070603050c1314120d0305010824061302041a0403020a09021303152009 70
    0x466005143d0308000d1441e050b0654019510b0354043d0200302d83c0d44c0018000004171030150f101900d00070a144042c131740a580316040080d0040b00300b05551085400a01104400030790a0355003400b626442240902c1b58100400000e014028186002390b20190700c10720401008804075140c0e017200c0c42440c052010a0f15082015240d900092941002a0341c0d13010400c080f0710b018540c031000b9400034944042488108050380383e154000c80002025138003600c0304016840c3e0521030a0b0740204011100d038141010b010380401640340c0c61140001c54480600c2000003641d030035034070301c0d910b501c1e14007160f011626043c00030f80504002d01c180b01d00f90280d01c005810b01508a60384031a510101e00750411039585910802948201c3d140c50301c090306030309100104000c981d210041550107403180b4155285d9186204102010100f500441640b43c0103000c804c0700081200d1107c1e054951040b0700301e440045c0c140c01040140349480c0c1000e4940f840240580c0c43e40c0503d0000c00c0707400c0b030030307110003040c2008003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 150624568 1250 150623318 150623321
    0x110a050d03080712060e010e0708010501030506220605180708061008040b040c180b09090f070317070506011203201207080f042408130602030a09050706080703060801 73
    0x308080c0224034a94006a003080c03244100350806058000e002940580700d01d01c101c4184806d8200100c00d10524003403188580d040025640148800d10b01440149400808a8a2003500246c0d0040350201c004441803410b0103508007a010303200261030b030002c020411004100d044d40036120240800c2d0344c08041009410700752a44015900349031113141550300c1325919424800d100410998224150b034401040d50681103403000300d403584603480407400c0306840080205056000e810381559a0001048036900000483c1d5072040700c2c7c0001e02d0b40680001d40300d04030114810110000c00c1400750000100e0b0450200c400180d03402e0107550f0390810328481c03800c415021660184240304603070102119a07074421070a001006058400d1143d1810841307540086d60541d0071070340003440c5c85901e0004890b000d0b0300d550b44010800c40300f031030400502e090404031080004800000a01030b9900000082d00c00400b980020201c581c0c400112501e06590302c000406000c1c1c1500c48000203824540f0005400805 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 150625818 1250 150624568 150624589
    0x50a05010b0d0e251a16080c100e070501020d0903150209060d09030302031006170a0b010e042309281a04150e0d02030f090109080f0304061e0206071107080703110a05 73
    0x46c0c0c040c00120701c0b01501c41c900d854000c022000300705e01c81e5801034a0740c06031500171029090072001c0100440ea040c6400607080c0003103480c181c01040340d0f05400b0400303d2040d00131010024186c4c100143d65921000100764940f0440c0e040d4082603044c070005000301031345680114070500c11406200000794695070b04484000c2c07480c031158640c01c2c5840101c0c00f404007652002c50305070342c14113000f1020481880450b003501c03070700070705601880805841ca4400c0311400d050350741d100c001c1a010700640e0700400406640101450082c501110070040e1130410402c007440700340c00080d416190604c0d40d2900b480c1140305a40840206ca010038208043c502d1603140000b016141c1700032a170051800c00394a0000c2c0040c41e00110b0f039040c1000b0403070300300082c0701d001480400b107400d0050010315034403820120050030300341c00d490030300700f04c0802050b02c1000c403a4003186254010b030f05072814000c0803103c403248918083d0945c000401c60f0149890000402101d1402d07500740c14801c0e201000842c1d543c0c02007101c013880 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 150627068 1250 150625818 150625837
    0x507050702090601030f0f060f06050c150618040b06040e0c0a090b040902040e030d0e06060d02010e01030914010209030c10080c16050a0b0406050a05010b0d0e251a 72
    0x2091000000500e840c4216640c002e00c1803400144414400c001c4034161040101d50b15040d6680e42001d102d01440400c0c0342020384504d0521514050191750101d98802004200b166014030310700c08100360f95150a843c079103610265010300d001d1304040c10000071707170001070b0741880c460780c03400d6804000d181d000300340920302e01401040e21010030704d02204503000d44205020581c1c0140d8641c1c1d1680107030f455110301d61130703c1c051600960b210b20b52400710404a07031506840040c164491410095581d80e03040489591036828a44880880150001038001d8400514024440c0070130011202082d201503004e851030410480484002d007040c20284100289551540c00c000791601001072145142030009114402c2040600c020a01c086e848150600a082400321498401a010320082c8030050080319009a2001c40400c05545816400c82141c440c4001c1038a81c0303915038240010410007480201d0000c1c1480e1a0310000c240c0005d00421a11014060744440441c03120303007219003d501c0d80640305d007000b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 150628318 1250 150627068 150627077
    0x2240c07212c15130902040b120106080609180a0b041b060c050303010501140705030a0503010e06040b0d0618050f0c09010e460b0a08010b0102060f0702120c070807090507 75
    0x210302d4110300360b581d4004001640320388038115002803900120306c0200300034001072540300d855480800124460307010690109081003803a0b018030480e0358a8968164211818418890070351601403503070b44c1004440b50014142c003144404201c240203030001102840b9010103910002036450306000d60f00d03650000707006041c1e41d0082c801884994065005a44060000f182190030200e15039100c914543c402c072411000544080700401204040c5040030740c00c5102284d09001e41002c850204204021191000d4100e5894400c40c00605a03403006c800c000d1500070040e1500113001100c0c0541d50040c00c04050302501040000042004001c520640079542c1045510a201c2204142c04803114042c06200040d036640c0421024103003081340400700030901d403000860f08410032000c2142c0c4044c1e036800404281d04084100c2d03c680e0303021500a902804024021a03e80c41d0031604902c1c0010301c0816805944000031222000600024950126168141291486921000c803c020380e0008d454000125 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 150629568 1250 150628318 150628339
    0x60c070b04060b031204060915090e2809031d04060f0b070204020d0525030c090308070611040b030a0f060303080723030a02090102240c07212c 63
    0xd001c83e049003411501c02400ca804140e03e0310401111580664070501c0800c009800800000000044060001d5094144080c24a2901d14072280341e050003045e10b07012000c11681404041c13081c22920318051f00b03010302007154000c249009005060920142861034051116580e40d600c2d003801188107442e0211401603a65150102c40c865503008040300700e07840381c1c00b441000c1e48661944100351054066030f525a00c1c0d80c88220301a0280c00c01c117000070701003504244205407160f42003503002003121786c07000c0303443e40d10300301130034000000c0c119200011b5402500040002d400314130000139500690340c0e507900300040031110a083e0212442440001e0220b81c1c0c1340001103829010f82c210101c42c2c80240140f015040a10301c00c0051540b04030740c0110030b242e0100382803800e940d0421000b45920318402c0140b00106007400c0e00b0b4086500203142c940450000201007040041c000846070001c1401d02946410112120002d40509140d2102d141c03036401e207402080c03280c60084044102c802003c0e05c10000c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 150630818 1250 150629568 150629573
    0x51005060a15020111030f07080a091e030507060f051e060d020108090f01060b0406030c0806030606210a06050415021911070f0b070303050c03010602030405040b0d060f050108060c070b04 82
    0x1000100d82c0c80070150755a450b5240800d4503d00000c42c031074520145440c10078a021304001e0201c074005000d2403d400d1522031554000384038540304403e06d5560100e000c1c0f0440c420b00e001c9511f071298140050165003407810803c1c01e8100c1f03400c81d50141640460a076010b8120410700880d00c68100da01d02d9210881000b0880503500441180790091214000d80303a203014000205800e5410340c0c1d00c50b2003a060006020000194940b00d03400c00d801c0c00d8503000080d42048000641d8824000d42410f1082c06038003040030380c140b012410340310b000000d48140d80c840c3d10a41002401400700300c40640d02401d045400d42c1c1d28071828800c44160200383c0386405011000024110349030764101c8545262886011008600c0070000311410000303000c1c1d03810380b035511030341803500405030352001d00074040c083c1090006100054010060300c095400070b650000d024128907000070407400c4a044083c14152a02d40c0e413103420040d58020740d058507401421035010307840710314942c0070510401201600034060100070500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 150632068 1250 150630818 150630839
    0x20904020f120a15060e0117011d0a0c1a1204081303060225020a0303050d1b03020a0305010509190908040b0c1005100e0117070306020a020a051005060a 67
    0x104a40080c120a6455140704049000e10103404804510365104840e040c04019102500f94151480707000c082c80064908110f90079122010f00a005009604030080d401d428001d40c03144c1c0c12421010144003c40c02119102038860240c41001d8800046080b801700f03c85858000600b41070040307072103003498040400f141c40c40906024004442096040148004840400d901200a50f000c2d120045c1d54810b052580030b0107849240da00705000f50b0340024140543e5a0074101000c0341c0d00b6042c202d0b5240c1d60314906c0c0d402001241103c503001c4850000b01000c0592641c00b601c1c01c0440c80c0c4040002c0d0b44c07114108448040103c81e5840d071191a0703400d1200c0303a071480d00a0422544a400b403281000e0310313200007240d20b4211510401c3c19600506c1c1d048210422801200c1e044090700a070528000d0a00507410004a0140a154103114080544a0449904001000080d13800070f2086444226441c4002c0d258012410152010700c00d0188030101881140708540c05030500900d0320306410324050303021a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 150633318 1250 150632068 150632071
    0x609060804030903020a090c0809010908040b13050a03110112140604021b011d0706080601020c01030c180801050109110c030d0b011704111005090d24091a06060a09030209 75
    0x7400c1200c0800d0000041e06c0740622000070700080340011415a206141c0105001001081944643c0c188211007002ca107403031088505440d00218401d9450300c4040c4252907100c0d50b548141e802180508002091245848119003d00001d90300c0312005401046090241ea41e49480e4442c41c036152004144103180681c01003548036000103403c0528201e000d181400c441c204050b90703817aa4002071034582c1ea40c40074000707040505203d0419100038182000003e68a0302c510034402d050554916a00203513a014a010f0040d403440719201d40f03c10707a04d900b10307140030f003d0038400c0560075803c04188401c9007141900ba5200103d00c8801541065220380742a406045130100d61814410002040e02000156080e00ca201d14001c44c56a51020100c2040c031001c961010019002c10105000d047d515a035245000b4003c80d401554006210b418220740c00351000340700740848245d91408940300104490031380028040b0544032540203060b910001848001c3c450540c03e240003404610701880140340c0351802c03e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 150634568 1250 150633318 150633323
    0x12011a0f04090c0b0409060e0907120804030807050f0d02010b010e04050411150403050607090612090302011112040506090c0901090515040c080a1a0d1e061b090f0609060804 76
    0x1103844000c5440d10210800f081d0841404410000360500c1a0001c2c0d0080034014a08194417840a14290710300c00d032144a00c0c0250004000c500700c0d0071051241e02c07010340d0081c5401c407040a030b940072a454104d0f40e9107040301806c4264081c0e41c410640460040c8204c070480241a111604a032410f541000001c00300140100c5601c1400f00e483c100c04c0d1203070047c05084540b811600c1d682c443c154208035140440003003c0714104852641e00780407865129070480030006030000d022074048060b18003a409840c00c3e0860041c8108085088100e0f0031a00040b180600c0c010b0042d501184c9032008610b803520564043e29811440ca0380c0100840c40840e03004681c051001d0020324568020b0354006030035500003210200c0068408410702a07840d0191085c040c060080c1410101207918200100700e6030340004501031f24027680031100189003401c1040c0c82d07402a034001c0d010404008051740b500052008408950001450040c0201d1031a00c0300360f026040c1c0e03201d0b03202c86900d24a082c1080320b03c118014001c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 150635818 1250 150634568 150634571
    0xf1216090302011b051203040605150a03060903140307030204050f0406152d05070b06010906020d050702010c02120d0f173402032511010806060c060703060512011a0f04 74
    0x2801d010a80912480e44401b40d812a89556410141404019070300c001d48041e83c0480340746c001840640e07480b010340048951000010501d08c4980c01c094030480b412070703110042c0d1940082041440d9034158000c00035500212032451880c8014014002218403c0c041c1c180e00440700400e01c042140139111484400480c6030282050340c144003107000400c41d0900070500400e2004c21220108982c20040d550f20220a00e401605c2c03c1c0f40420080d500c000d90401030062140000c0c1407415a44141404180140c005d40411540360140f0320481c7c0e100000851000042e481c0b504100005218401411a50500c4403e490440e2600010150340b4290018071402d1009800c07610500030a028581d0070308d049080d0040c1d0740ba40c1c103144504140d4400c8440005208003c00300000000f08000002c0040200c20b107000c81039540c0b0031000c2050341c46801c0128034140715050030031031656030503004441a1078003510398144804406050b54240d036107001c440080c007a80100d00380003c0c1400015542c512000810 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 150637068 1250 150635818 150635867
    0x40c03020f060f16020a0611070b0333030d0219020915180103020f0102072718050a03181430011b0507050d0503060f060f121609030201 60
    0x4401d503c581c490000e400d0a526405180020f51402a420740700501040c20280c50710400c181e801d648aa07904d00902c98101c1d8040041602845400e2500500d0b00200c00d080c0c00701c002c0c00ba0000940e21003100400e1007481000050224944041090607606801040551511003c5d601f0070465800042c14203114001d00001103215a9411411082c106504000e20b0800d50550050220741b21003152246d0656110b00d00410101c540b000c00ca000303000c0c001036543e1000380c29034146409805607205412130144280c0c15041480380201d132040f0080d1003601c031202415140e0554001408081c410b0702421201503081c1203450600007140001d034513100601f8190780801000c0d0006000c00d00201d800030f45e65900074411040660591a40012060b04100f42046541c0c0c1e2010358a2060141140400c200030020612507129000c18151001000300074a0700c038502441030411540011100500000312200400d054240d10345101100030f445584500e4070600b960019603605509107844000c0e44005007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 150638318 1250 150637068 150637087
    0x18120f020409061508011e1a09070f03150609030b04051e0708060a02180d08040911030919030e0f12010606030608150f011a211e040c03020f06 63
    0x1ca1059024843c0c2000544088211850703000f0401580100c41c031a8500a407800600e0041d9140041207540142d01041e02c13940e0044508600c0710140103240c2104004040c4207003036400c502000350000b40340c6c0c1c0400507103041c584040c241880c036104610101c1c20f080300500200b249802d40e5680140501d0413200c1d8042d030705104940034041d240b1008480d800206090001c03203010b0205030303048410000c0c254107041d2040c202c200b000403a1200c0e10712803600c2d0718060082029140a440041828030020003145001903416851680225803a581c28001c401c44c1c1186502c5018101f821160144c1d540c1c6107581000052100d0041c200003450750000b2001000c05c9104024000d40002d450301e0fa0f00814103501c0c0030803241c43c5c02810300040d110040400308007c402c243d1104103a04542c900038a114030000520666102441002c803900b400d082c0070010143c800382d444405c02c9c0292000704409164509032000c10b1494034054270014055aa030045c00c0001d4038210029035a61040209124030340728480 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 150639568 1250 150638318 150638321
    0xb0a08010e0d08011d0405120a020c090f04032c0d0627081629010806091b04050a0b03100902010305060402091f090801060b03010305070618120f0204 66
    0x15442080680e45400440c010000300b030116003401445801c0c03556065040280f0b000c011070600d000e050107a040b420001c0c051180400059460780002000d0030341c9c9802c0100c0094841050a822900801142003c202407070b13030721580184078035051755801d1443c002580c8040b2000250420b00c0800c4043d0324258a02e40c1d441c0380d503030070b101c03840b40381c0004250f0700843c1c0c040ba203092888151802e1f9070039402e0704c00100c0c85d40800c5500040880da50b581141440d0701d8064002c41c16003000f0b04003542c00100e19445080d4521509040e95010300807144d0640c0e40801696903030311121249101d01100c1030894809050179084a07401490741c180c0814030815500c0800c3c6032025150b07060301c0c1d0903118051003080d9601803080700e800c07a006880075483c1070a0f41001c20808090402140c05d0712400b0400b24484501c00c0a5141c094204480240601941ea0103182e115404c00e020039a11802060400240507000741c0c00c10400b82040241d14149610f4070103040588022524241c0e081c02c014100240140c1c0c65 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 150640818 1250 150639568 150639589
    0x60b030f1e1f0c020109060207120206091b0d0f02030a030503070e01030603031706040f02030c041802121801090602030c2203020915040209060c0105041b050112020c010b 75
    0x40c40080c403504010011038151911444038070360098011210740000c010340c08003007000c06a50b01a01098401000b08100d00411241c440a00031610102d94032041007491201000441d0ba0341d0300300c840715122030341c425031030303074050984042c294840c60000750103030500f00c81c0501c1c0c80f801480c075203190a581c0d8000c2424a810f201c0110000b40d40041001503480e007222442420080038030b000c01903a401c41e507002e00600076001e01c02030010040f5000806135034682c2c0108400c0120340c081951603043c40e2030040c1c80f603041801040325600380040c0c080c490301c2d04d1f41f0075203601d8001201d20184c1a26a003800d0b89020042c02e683c2c01042d500c0e01005c50100381107000271401295812000d513903500d07105c4000d08000c1e841082e003d0103040510010009030b59110201900070102c1079107142c00e85030240009009110340c040d600e07007100b4041412011140103503c243e1140d80200c00c900c10514415021070f00400c158003545000c1240104a454003c030558058140031561000001c1c4581e0200c2c0041c2e01d1071103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 150642068 1250 150640818 150640843
    0x51909050a05040519030507030305090a051e19020306010308031801061e0806160305070c020a18050c0313030e010504120b09010e0f0c060901030204120305070b0106080f0a0504060b03 81
    0xc0ba0710902040000030800d044071810801030a140b46040c80c1e07001032840c450400c010b41015100d101041d60501c050010120030b03035125040b642041141341200c0303082c7e40c5003603100792036004001c1e41c0c80010000f03c1000e03205547c01030140102c0e80c00c0d41e03218000c40c0c0010340030800682102e020204070400910070704001e44110010b50000260410401074100f81c00d0f08520380c5d54200e0814803010000c117038240c0120103902d013008945035a074060125401020844044d5100c007603a600019a099129446228044001414002e42d6960360550700e86110954035a045000310300c28604c0030911132001452455414505285883e070340c0c012400c0c40350980b41c801c0d20140c070110b09012a0510034802d54801c10f050002614010031096006070f1a4016101603d024020000d040c0007907a119a0464014180c0002d44444180c400d040c001d100741c001180440d400c116000000c2603440c081c4030418460701c1e8000301203200d03540b2000700c0c40141601070812591280c403103428000c81d40d1706201c03160304000e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 150643318 1250 150642068 150642071
    0x4050a1403010b01030b060d050402031011031006020f030a05030a11030103230f1f060905090d0f050708031f0806010611190320070504090f020f1504051909050a 71
    0x815403003050b08548021102a060514005409042d501e45038141c4064000c0b187d4001010394407400400d040038008884480b80302e1410b0240d0f42c40483c0d01c4065406121030b00e00b0705103510f40703030030b8281d9032440040000d0b80075600a020701c4403441e108400840d442103c0450208813603102c490b0381805500203070801c558980040711440c43e85060360500209444120004243c101c400041c010f8a40400580c42e00c0342104100322050340c80105e4005800502106104000a1410906003034840d0f00361400a40002c801c4800c40410a00c59016142000d40144074145152115405d4551401107141100e204008451000903100803e00200d0f00030480ca4503a042d012001e070f041181005c8010b001a4902407440034904c000c40c0c0c0c0f04604504145068048d40101d000174030042c1e1034030400341e1119601600384080360007000030303549001c00f0389482650341d80002c4001d401044000c40e40c100841203040300511040100e4a090f144081c0c17000380810500801d551500c0f4006c06841c0b0485110340b295 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 150644568 1250 150643318 150643349
    0x6090f0209010e0f1003090203160806041e0308060103020306031f0c0905030615060c03070615030312020a020d1202070c0b032505030403030c1103030708040c170a061104050a 77
    0x550708440c82540203c82116820050b003038010019807880c9440c120070042507900c05601086485c10050115880c251000c00d4070210381c4c1e04c117460f40e0384500700c80846400748240101e50b502c61540c810007817410350649a0b41420b0365020b00440082d000200125070510801803e020048444000c410b030003c0c901502083c0d001812002401d5100c2590025010707510072000c004050b401c04003072129404084a0295035008405881465805100005440c0518042c0b01c07805002c4041d1a4800702c0c2e110361034490704000310b0f541a804074018440311502582195109495007446226900d01d0700d242070100600b0502151201c00710f410464020040003440003041c050f02911001c85e00100e01c010120305c001c44481690700078001d02000d08010203040c3c84881e40004940103944010551282d40f0482c0e0b10b07880c1170903005000303c000b941c5c26034491200c0c41e03001c80c4142014014080c0714001c5802892100382d15a80e03040100081c4c0c0d1251101070040c40080b50315035460003240e0041203070900c0650749 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 150645818 1250 150644568 150644587
    0x3090c01090b1216030b03160812040305060601080403031b0818010203010312030b0d02061614010b10051b030c0f0105010509100b030a06030204021b12031b0d06090f02 74
    0x441c0c40769081030042070818000c8902100e80e03205500e62200301d601d010907aa13500120705a01070070705110300c20303814005d01c0810100c0034042074000c02203916003001c48030107003402d142d1440d8920440c0005043d6400107800290300d54010328125400038030034500003400c96403500b07101046d0020300d0760800001e1515810b110264042140c842d4400e41c0600c021461941342d0340d180c0035034400d440401801e041d2583d528000c00d64a500403000869005090160794405941c103180f0078010a40d0101e0b854201c001c0a440030400500c03400040c10409001c64024010041c0c5c1507805800078440444c80c1c0d803264884134241003051002d07041071101c1000904025003a02000e03429104141c0005001d02126002c01c5480e030382040e1040d0858649601055076919049000400742c4250340000e50001c2c000542a841080d00b44055001c4030411000c0c0c1c0d000c0114003015404601c0142d401011642e22005c0c0868911a01c60042c0181c01000d4400211240d40c1e00d12441620350002c0c1038824250701095002c00c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 150647068 1250 150645818 150645827
    0x80307090f0807061b08090901090f1407020c01141921050f040807050c2d0105040302090402040225051605040b150c0c0d140d05030403020a06180803090c01 69
    0x1600c0e90001070900c881c01c1841c02001403101044d8010340c42d0f03445017558107100d031210071030b488801f015008903880c0d0b031070300d80003c06811154031056160b8542510303081840350a0301d4070f9024040641c00341c02908101d1004498940e880d419400c408032003000342000e03031514440e0441500c42503032141707141101e0b481514903c3d8101fa00304810b02f030f0305250400001c54000440d141c0e01a90100314281c94070014284980303400002a60070790469921004041e0010b0701d0b00120420b0f003040e995008480c9000320044030300b8066440b0094000c402d01780443d00601e010740140284c030481e1240e0300c2203010110840988150743e03000c1034603650442031042402011841ca010050704060320107100b900e03002d03808038505201c003480c014010304005c13624642e904000d028107025002c000b0412240d550b0a814403901c4010b950804140038400c3d11081c207403441c01082071707920403034258024100c40c1c507481e06c4a101800036100c00300854805104858002011400035602410001c0014111900170340300140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 150648318 1250 150647068 150647099
    0x30421171b09041d012405150d0c09050307060c0203120f07020603010b0a081608040b0c0d0608100c0f05040b070c0e0a0b0f0f030714060d020a0203300601030c0c08030709 75
    0x394400b00c031b22900e03000c4810b41800a08841084d40d00040e1a040c001c1c500b091030040040501d000c0742052030f000c01c0160303c01041e0064070002c60903108026600c01041d54030120030b04009405030040310100b458102040050441d02440101041c90000264001005640300b6001009514404500c1500e840d50007616140c0c00500442c00c1108001b41a030040c0c1042c400510043c801856030b0000b408004880041e50890642e2075010300001d91220182900c622942031541002032901112083e600d00c514601245a0700d02e1312814a4241411074004141d400300c80e05640b04071b5200030003d003000d19202c6043c403c2c0d0450f40c00294900281042054040300c680149101e1034120000020781d07580464104200c6d80c0044020781641811000304503c2d02505a040c00070b144045003d220780d076004001040e82074a0a0314480d00b0618007441c0081401e2080b08094442e10300100040c03141d40294004500705969040148002c40340342d0720140d10303a00482d0f1460000708a2407040011080f07051410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 150649568 1250 150648318 150648341
    0x92a040606121406011b030221040617010f03031121031503060702030a0c020a05030303040c0602060c0304081c0b0d1104060801050609040b1803030421171b09041d01 73
    0x1601e20313041c150002011b12814003c0180c02914011180c03081500810850324184000140084040280292500f46400c61b00c28813001c1103108a801c010348110400b0541a81c484200355028107017151801c0b0f41c1d403886185d001280e031107034400001000701070300050000b008180720100d603640751441c41d03c00100d54540780d1078042c0d4009410b2041d80358000c41a1000180c3c54904910a0b440a000041c9a14503070360099425000000a0cc4144030014a0394401c1d03941c1d80c1c00322030184d26400c900d030010f0b11003103401603c0d200003440040d00003680402c51222100c4140004076804150400240b41c11003640011107520194640b2410a800c0c10300550005003d100c1c000c012a14100000c82c181c44001000280782a00410024100001c2c100d2080613000400040340e44034079041c0b800b40d04444145a910514030704400e03100031014480e013500c039040f9864942d06c0109480e02c0d056aa42d18186160640c0010001d000303454180d213803072003049804462030920211050040780300d9401c6500c0c08514 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 150650818 1250 150649568 150649601
    0x60602010c090b090a0e0405060708091219030e011503050706051c05040c080f010501080114010b27040c05120f040f0803060117041b06020105092a04060612 69
    0x8115015030442040703812100b6800d110b0b13543c1c0245000107203014806800050b1094114000d0006020000583c580b04070a43d88480800707450300b5640550300d900480c9008907080d81006018000031070640004205003141c10041003409403c645d5a081d68902591203c40300401e800400034000100907030300c010001400c1061800084000e841d01c41140c80f8144882c060300c0e1000310b0304010203d13145000822100d801e54154400480e42140a480207110b5510701d582482074103a44101801c0e4114122403041c83c2440c60603280c072003164810f001c40b25091840a010300d4206003283c4a5000d60b82002c480d40d6240c079506d489501d184640b102c005041814442c05200800000032000314011056941001146071079682e07603c01216500c103d12400010365515009010403c1408894404141d03048070348400c407070742c4807507007242243c0c03040301c0c0b8005907031040420b060f950007440200101c880400e070000391840c8108001c01c0540f0f596070300c52800141d0300810703850716400354410780442d56040c254 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 150652068 1250 150650818 150650831
    0x40512060f07050a0f111606090f0b271504080d11070302010e01120b0604030f1406060604090c020a020a080303010608090106080a0b060105090d03090503012a050913060906030606060201 82
    0x101104008200101800311b07125044902c000b04111481c440b40d00a000304020545580f0010302980c800c0c4900a4081240c40020810410342ca043d224100951a0008031500b40c14010088481a0042c4c00ba0001c40711f00d0a4004140080300420203029003d0040000c015030400080069090454152054114040910050382c0c4913680401d07080c803d01c4d02d400c1d9254030984030700c020101c80c2c02483e80075600180000c10080700700c15070000580100411515901e0181006403640e0013100d143e5440002000300348010740d840c0d803021016804510450700d0b0010998013055441c402d581141c1b01c180e00120041101a44c017840d5150700c0b10300340300280301d201e1912500c01d0351031b900d0500082002c00b21070000381041e445030040d1261000b000300015104400c42c1000341803007005000d800d00a5003441116580c400c003094044c129442c80714000300c00d0b000c003404202c61581018210503486002c0045440c42980d25020f54000345c0940b0780d00007000f42c503528044084034015407203078096905014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 150653318 1250 150652068 150652087
    0x120a05070605031e0103050d031a0f04021804090606030c05180705161a01080601061b02040c02030702062817070f030216080d060b0313060e0102040512060f0705 71
    0x3140421030310941801c0c2d85a40310520300b8142c6200d0b01c00c400c001c002540f0000070506c00c00041b443d08042060314100100c100d00c4c00340d0303842d4040c0803035000c1d0802030444d00314086090503030082030001d404503d00000e080f94100040c041d03507018001594060740b40c0406100781306c0800300369001880c0c1100c0b91013410601d400f20700d5001c4002070008081c0301d008a26011401c0b000345c95060803540c0011404800310307881502e0300c03c0300028000d401c803500c03401e0700102e036050003840f503299041e0094580320858261603007000050408a80404214003080c0600001600c403400035100406401c844042111b030a0030343c4141c0e4440354001a020001030b034085c0000e0358240310b10356401008915180081c1008032070250003038441c0e43c41120203251100d40c0f0000b4440c401000e800101d2440800b4003507280c4d11040c40b40b480c0019a01a28000f014010f154002042ca41c050b0810200000002d13040c542e680000404078507d480413041c0b01e40040040181d080f2401d043d03640d01c42c203141003050820791181d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 150654568 1250 150653318 150653323
    0x70203060a0207050109080408030a080c18040203090102070b0405030415140417070b0d0f050a0b06040b0310080601030809040c0206010806011403010603050d0e100c110d11030105040809120a05 85
    0x362480050a41c0051480300b803000c06e401c42c0c101540c000c0425907955545080b01c50f81c2e944000d100c10300080d850400705016056000031034541d0b52000c048180310351660300410000b540f000e0034080141d0340c20444c0ba0000341c030f400c003213500c41c1d0b000d00302440d1a1445c250880b85480c60006459003007043c2030840c01011a0400159015201581c0b9010007900141c00000e140035456003020030b115102007502d020203101d94022030106488a40188401e4440c1142942540c0d542c200140d40103c00380002e10620000c88080d550054000d070040c44041d582d014200c0c00c02c5002c3c1c00030b0310134940009400c1954100380c003586000c00c92610042c4560340c980b249007912200b0600a03003514005445803c04680d03403d40102010f140c100061b24880c0102e598050900c40d84040f880d03001b0300070034042209050140038200d003050f401c2000f0511000802003040810701c814001201d244110011241c800d48003446600d00c2507101d0152607941c0c0700c1e488200308025100010155079940b10000303034800035001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 150655818 1250 150654568 150654571
    0x10e01120807021207140603060d12021903030204060905060c0a02060901051209011a0102070303020c040f0f020c01050708010f030f0206030406020702101e030614100504121a07030207020306 84
    0x24480d0008005080746000c015038816904069440520729162201d5448040b9400048501d0002c01901001640061098030302003240d004e58812000c079080c4c802b2480c0c0001440c10b0319081e1054840940d1140007644c1a40300810041d0b0020b5400318091042c55003188012028007400c56180d418074000340c614179034070248120000e0090502207035031905a401032041d1501081078a02146503480d003040114000c080c48500c0801c200c142e800e916003039500204003901980d0305580544407600d204020300c409040061851410307203507607501d481451f180c14806800308078144d1001041d00e081c1400000e000e0320040c0c200d00301a1030940810400030720621000046c913036061f6410340d16696141003010090288040c080e420401240c2894031f00e03540071402460700003059100e4a09201ca542c42182121168001c01507640c034a2651840940f40004840b103414040780381c550300d07050f05c6d00c80035604012403003070485184103400021000c078203950b40b0040c3d00c40c8040c074085080031f04640010f56103480 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 150657068 1250 150655818 150655829
    0xf0f05061f0e1201050a0609020c03030f10050d05030a0f05090d020409110303040b030412031406120109050d0216080a02060703081504020307050a1106090d0311040e090304030c0e010e01 82
    0x820400d0501c807401030452510100005240c050098079040c0d020340605401c45096040c203140a4020404104610950b00c5000162005500715924500641401c94020b400c100501000302c2000845640b5020852841031056000e151203403401c00e0098800440019008103004043c4004041502d4400032144071540451300451141114100b0141514402c0b440c29054000094081040d0441d48002c0d4004d5206403518143d071501e40808400320307011a50f0540100640002040642c40d000c42c3c1c41060300c0340c43c03000003400b1506685940c80c21021081010141e044240d016440c103d10200503401000f20b00c2c06404c0c03002c0142e001072824800c0000042c244101003020503020b0303652070005142008090802c543e2404d003403102500940040c003640c000280001c820048810000c45c101e8001c810040c014511803850074030540c00b03000080803407201d0000034000060300700c070100749142c05144444007035079466042d420100d642d00000d4201c08000c07101b40004102e20019109003504480 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 150658318 1250 150657068 150657109
    0x21c0908012307050a0504050307080d020d050903030403111f11070504020f090603070507060501080304170a1a060f21060f012702040509040606091b021506011b0302010f0f0506 78
    0x5c11840090b00e043c003894004540500c2110390200301a04001812036601c0315940885140c0c840c000400c849511903040e020340c141c0c000f484200001822a2510703085158010500241c903901c2c008030207040d05006004c0e40c000344408900c80038806091184074098101950254680401614100c00512521102d18040c51000000550461242e404e507170b510381d4000000d00480d6550540c555990b08140100101b05801d00300d4612a5500000c0411142da40710076030020700b00700301c90310500d01c0100812040c0c00116024209985541d5000000c41001e024148882401c0180d9142031500100818030912080300100500c0b0002200b907030640060024044a04d401804180c00d0001c0d005560240e40c02903850310a0204021054200c03109441840c441080145c0720680c4200619242100104c096002403a00c45174600244145540c040c0040c14104401622000ba5811100302d002041c0c1c0180d564031089030013404980030703444d000d59180e20305000e0b5080c00341c00074010140031240ca07080341d0b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 150659568 1250 150658318 150658327
    0x51006030e0a022d0a0801020405040f0615140c2a0d0201140306040204031205030613050c120621030c19170a12020d0603030311031308030403021c090801230705 71
    0x201c03a41138102c100500240a0585030b0b551100c00d58080c0d00325004182c80b030307420440304100c01040340c0320b45021940034008aa24002c48101c060b00d83c1704c0d0404201031414800c2040c161000401c102c60b0480017030185a405880300c1d8084000f51802c801e02009129482404109015030380c8240c517001c03818000034205075242c0381c080005000b0320503584000c02c1c0711002034040f000d403034108015502c07138001074a400360b01c1400404084120b841c100d07054030211009000411014883c8502503500c814081d2441502c91f0f80c0140036182c288680c50740d0585070340005107200d800030061100d00041090990703603100104080d40c035480245140c6d403424001107030219800c03818a1150480e10703481040d40ca41159110400521600540405e001c1034010030308021000745800700b124122441244481300c8811016819a10343c5050f920243c000d408612600201c800d0100124800b0121101c0c1c9031501c41c9528078115001d801d44010210020181c5103103202d0603508034601c0c0f00140c0c041d005103001e40c2e85 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 150660818 1250 150659568 150659629
    0x8061b030f070e0a0e0405060a0e0601090902010c0c09020717040b040504091509050606012a0f03050c01020301091407020c0328081c061502030a080604020706051006030e0a02 77
    0x20103c540300c46688001003c00008910070100f1000703014a001c6d07420b459440d62400c0e04030342660f581050b4046660300c1040100701d0521168814800381e071051514190011031a00d801081044a800c40c1000d903a00051840030044907107e81c40c8001200100c13241010318012140a1501851040902130360301c8800302030401008440181202040300000c000c0c40c003441c01c1541e5a8101155030f540812640204411013464a80d00808410701784224040025010b554118003420700701e10841c03d1000902c002030500c0e4003030010358081c102002c03001030500740c852310541c4d1014000d003031407080d50030400440d20b080c0c0b07000c80c80c1c2d2944050040d4401e0104400314002510640d80c0f0b1000d041d21030081020783c0c0c405032410440d44140b000f031000f8003000e0340b40c00000c0c1d001c1741b2410180000d40e0081200040c1c1901405803507502000c01400181424500e441d00c00564004079840300100c1a400d0092211a42500c1544044882c6200924040059501040445406010018603011030040c070801 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 150662068 1250 150660818 150660827
    0x120c02030d02010509010b010912020f060c0624090118091e0b0a0b01020708100f0f05040809030d090b040308030606070f03090806060906011409040b041508061b030f07 74
    0x1002980601290711a207403848000f8003c0c0030543d0a8105d650906140d6001d035031040c80c1d1034041d2101c50440c0d00d11780d0f02e6079003000742e13603040e003064260030110a1100e1a004c440c14020a88600d88441442039030512001004010300c0d0075405280c80f8643d09401072144003d10428801c1c0c1c3e02c124400021003e95a040405080d090601d00c4540300ca403070030004040102c861030990090481910611000010400582c1c0f9110b4501882c13160340d0013202200680d803502c2e0442008081c0c0300b2000655800009004410398000310307819180800b00007072a010390f00f02000344200788040c515001819605021403042d20b44a94070020348808004008148650740722011900c04036445106204082c0700751034042d0a00c042032054501074010200041c0c801e0030504002882404142d582190740c040e514001c4034590845011036410035a1458141c0c0240c0b40c07031040390a0602c0001600d21410701d090840351618100078111009256188000c4d01900300c00740c15a41c1156411100e070707456944842040301d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 150663318 1250 150662068 150662087
    0x1409040e0f1c02160f0e101e0905130206070f030c0c0b070b10081207110a0603090218090c01050309011803080a2702240d0c110303060d0209091e010605030708070f0312 74
    0x4072801c003980e03240001450340303488c1ca20448481910502c10f81e07071206490501c040d59400040e400c903804100c0d000c00a0010100021803074031a0900c1000703181541c60340020541c60350030182c90800d0004905041c40070917410310f903101414105080765681008100c0340c41d003e40d80d84d9007150400206242c010041415850880d00f82c015202881444e500d0710002e01034544203106134081ea0031200c5242c03201070282800d0b0700c03600342c00004180e000440380044038154401801010555665410980c5803403a41503504c2000f402692414110304203002c203582101d0014658a80d014503d00c104107040c0c181800880c01d15404450340c41205c0039640a14007183c050a01c21404250b001a0740c103030000c0c00307030301c0320100860303543d1035101d01034002c20456503e1005681c29039100361841e0242d0300600d080c0c403c855003c0150710583c1c0401c1d20050b0104058008110900390a0751a0030090000341010005280104500d0b00108441303498070820001c108041c0c00050a2160a00c807030207855030003030307040340b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 150664568 1250 150663318 150663329
    0x20906060c0f070504360c080d0305220b240d03050414060f12040809030a0c0e09030906120a11040803090901061409040e0f1c02160f0e10 61
    0x841c0b2070740e00c0c80d000a8541c202805124420761500d503010700311501e100007440107a159155103a080b03d80c5070403e100c07000b00c10f0008883c41807002c80b01245044040c884090420901e890214150500c0f003848900340c400420781d40400c0a0340f14004005c6840c060043d604081c08058488000316141130762340f10340c80d61400c00d40d00400156912001c240d4080000c108a030700005020051050760350800200d8403a540041119400a20229401040081c00580c105106950a614003140480403908200e00807a05880c031080c4032204015055881d2560360344100d40201840c940001c0400003229802540e5904580d404070710700040541242e43d210b00d0304e0740900c50841d40c44598410b140d030307034070b03440035180c1c2e401101d445000289480c0120500c0340b08244181030181060240024440103003015170002041c2d11039240220251681031116905181e081411021400414400640307000b541d5107200540f210080d03800c00c0b4940b0014406c90544021144040c81516490154003564039185c000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 150665818 1250 150664568 150664573
    0x40e0115060f1e0504090b04090c0f050906032103041a010b030a0b0301051909080702060d1d030c060a0b1807030218030c0d03031805010e0309041a0d020906060c 71
    0x89407540c0c0101041035281c00700e0303990700d8480c5441240704030101051501a4045507041c00184200310b001d400400352000e01501c0081c0700e03402c03903e03001c1c41403c01d0380c050703801c28250740d1043c0240c1c1051071805a00c80000e900401100040440075444032a0b044d20000b10040b01101013402c02030411041c00d0002d144d000712103d1940c680d0808029984142c0d0010822850140030210074103060140c1071184d42c0344a4161807801c00800c4180150005140884500f48100100c60041e9100c9028081c0300d084c0c284009030304007510f0920031880ca0b10506810b8950310070301240c1d030746440000385541d00180500010805206080c0802c107068078013541070004030304a008000030180c0c10b902802c0d120300c2c0000c080d80201312000c241610b40c0080440960000c282c00e2268010a019800c4802c01c3c5888840c0788480080700c3c0c880c58210707910010340d51850381001442241c0d600c2c15015042880e040d0300e003d00102c6c0c40c15000102540064000280604601030005995544500035600000701203010b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 150667068 1250 150665818 150665861
    0x10050a080705090402121c12060801050f06012111040305160311190302030d030903031a010507080f09120703030906080c09040506010e04060906170f1509010618020307080610020a02040e01 83
    0x2001c0e2024030315100c8c1c4e00d011490044c00260310001402000c0c01402034a101c0c05454461100444089410300c4c5501100503080c0190901d8211a1069a80d80e021490307078180c03580e0451500c9420f25030a50000480002a90340c00d1010880a02c00b041c061001124080410040001011242c0d1a2a40080d5150280079480c100c015016080b003100d05200750340410800410321040c81c15480c02800036400214140501c20004025600070320100d4640c02c1c080d41480311010000392003d1a884241c07043d41c020100c104200354200560001404442c2001444c0d41346c003c1112915000e210400c40c415a100d10100314107034010401d00000600152090104940303074035254010340340500c1000311100c1091500d198080c00864414117004415002c2c3c454a5010103400203a20b03005010851195a5000d0001d00310800c58540c0381c8900300403074003507100d180c0394401604c40d420042006008c1e028001060301c40550100d50b20b07207840c0d412103000880c181d001e64114010b001c11101004120548070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 150668318 1250 150667068 150667123
    0x120f0b130507050418080702040b1207080f0d0507020d020411040803090a050405040803040b15040204060806010e0a0b03130606080303091f0911101710050a08070509040212 76
    0x1030900c8540c038041c07401c031002980c0c1c507400d000890700d0041c1c0444541c0885109040002e000e400101350080c002400420b400d05400000750000b5629801502580c0c0210010095907070140700c0d01c0c1c00d034044200541105420301304040c2036071103101c0009204078010614813046660b268043d80075803a941801d20f49540d200e14081c0c0d96035010150091140303580f0000090580b4080c060140705581c04003803a8116105c642e2907803140e880240c8042400b4211100b4428181c41e1880504021f145980c0d4008807800e001c00094000c484005401d4052800300340c003405a9880b0200701c0307800108084c0850348600d40313410000d006051035045481c1e40d007c00814424000d070001030740001090140c1d1881c2d100f00c0000d00d0502169000b84006140c9200d9140900716440d141700c0d02c0350040043d080603090602401c441d01003d0303108481c1441c851121104c10b0145090624155020b48003a00080c42d42508003c0042c0080c440200024840c58610100c81c10311213052040c00742030302c0700703113140c0c02d0542401c2c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 150669568 1250 150668318 150668341
    0x619051606020405120c0f06070302120f0405011412150307030602040803032d0105010c030e12010507020c03150c07061401062123101703070b090d09120f0b 69
    0x52244a114182c801c090f108171030170104942c1051000107022805001060041c004213401c130f80b40c01c0c0c0c2940112514103001100010040c5003000030311781042c0c0c4d1203090400162085620744100358903210b00344100d010210900e540709401100310b00c4c0b12079140701e5040000e881c00b411600010300e0707180003140000e9400070000195000d4504108000e515108080f061a0704145c0d40e11101d08900402d0010001540100c040b206100e020340741c48a0401c0c01c040200e41c807070007002130380e014580d0343c2c0741080003083d418000010440d00850103440d518480b4110006290800340201113180d100041d0786080084507800311043d01d090700409455583d542c0e002a040c00214210350701004180b080825200e400d03032159441c41240e0078280801000200120849000300401d440303491864500080b41e1840c480c00c610075030351180d40040d03a480105180200341072001030f24480c0390b81d010301c161404840d00810210155800018648140c071200e0034100026400c41c0d101800c0b8042c01c0c414810624000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 150670818 1250 150669568 150669577
    0x20f16020a050d0f11040912030b030102120f07170907050405060a030501090506090712020a0e07090503010e01090201031b0c080c150a06060e0114030117010603050105070c02090a0b061905160602 86
    0x10380820950808002c041c80147c841c8620b008210001c2039001600b490300039480105992000346c0014103203140000300d14001c2c401a600c008231000000104046554801a1019029132088000c603a0b4108040640d56495040c007515200e20340381c800003030040d2984036400d401103820500030b00128805050003a02c1e81000d40708500f060003031140105152540e031300d080c60215409055420018509070111418140150508040000014000400f95000d0180c0c00000c200e800c0001039181c2d1031720024080702d401200c01c10100c4400c14070002210f4000a4418500f50130410081d03a0b80c0325510000d05204404100420900d00601408403043c07042c0e00c06826102581c4600b1054008031005490181c04a29030041c100d00810050044500081000308101c612038000b0650985a40d11a400d4440450750080040c3c40c0d40303060b00552070704e00c0c01203070811000c06c400c0060610340c0b40400c049120b85080500091202d569002c0740341d1141041303c0080c00c4030b08041091010501d44100030f50711 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 150672068 1250 150670818 150670823
    0x130207081908060d0305030606070f03020304080c010c050705010c05031204051e060f0601050c0f060a05040201080f091203060d120806031b091803040b040f05040f020f16020a050d0f 80
    0x1990100060007802419450b0040c2d00080c13004000d220315030742c01ca880d5440100501e800c04d4003480007000048421000c01441da2181d000395445505081501c2c3c501a08440d03054100442d0f081888040742c004501402030301d00a10700050b00e50b4030380c205a855440b501801e40c3c4021341074030800081c00000b244000c100d0b14410489403001e0000740c4040e540d4130064414030b6241d2131040c04641031358007940c0208421121001070b03c00001003c80303024142501100d60138009600e0b4000c2104640c2c1c00010103a00c000f56944c0c030b0340309041c00000d0a580b4005005441b490040001c04a10550354910903054810750004500c0314007462010001c20383d00082c0c0c0c41030301a22410b004802c2c0644a441d401c000c0d21030280030b4840a40d80c151940703080180e031140101007804108004030300d8242ca078000340b016150769440c00085915181c203000866208038206150341d0310600404940e080e400f401c540440e400003c040745041c050340005080d624199110700e6120841440c0742e020400320b441d034230503a1030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 150673318 1250 150672068 150672097
    0x1e2001030c05090102031207140a110f0f10020d0b10030209090a0507170c0c030c0d0207061404050904020a0e0a0f0b0a050f090c09040606030902040b0f0a1413020708 73
    0x14203000c070545003070140b000581d000d0382050000704074500749045550b501951034600310300000c281440d003043c41d50007a101070000452601008200e03940401040150680000050030000e40da4000981c0311110314100d254000c1d0002055183e00005400c5080a89401001d410003000610b00190003980401880c0340039203030102c0018011681441a244034102c1138548105254107540c9241c60b41400818243c02c5e41001d100c6005032400c104081c0000d65480702c0204a514041341010340743c81c81c20750040003044401590106c20541c6202038400b00e400c155810f00c880d440714800200c4159a5412a00898044070104841064250000c9001074600c6404002204400b41400032a01080c0207458100d501c2c01002105402c01c20702096001d4294943c26003001072510014041e02e80c1079005200117901d5444250035440d00e407042d20f0002c2c2080b034840c2441c045010214041200d01d01c40c4410601007804800c1107074a032420b48190700c5280320000c5540310854900181303217800c030b00c85e101c086a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 150674568 1250 150673318 150673331
    0x30203010b0904050c040e1002030a0606090b030408040b070201030b040c0801140303040825120305090901090e10020a0302040807181506020a0b251d06161e200103 72
    0x5042c5034a4842c01039030000c018100d1640000148009040311030200e41c1144948013503840c40604030f1014600403841d103800415075030310f0400000d00150b03058200001842007002400000380c860307421502122082d4080f251280c0340307800143d000304861445150407505012240c0c140f6548401080d069640b030310701c4520655614814180d40703010350b010b89400caa0088000d090758601040c2841300f20800071540f45011515000101c04241412038128080703200429041e0140c5085444280540103c400c200714100d0341c102ea150366150212510b5480c2c503800681034a4a51080d0119000b62007004202c3d5010755660424200800400030303840d80b202d2170103004002c0fa0003035046ca5011141c06a0003030101c100c441d00c0c3d26180a002034002c0da02000b4a0300650142c0010185031488070041e1b89404025028640d401084802c4510400e84560ba003003203a8170210303018a10424403c0d40052030580c044041d1180c000103d2007000707001d4444194020500f00c0c980701003100c0d044040081e602407200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 150675818 1250 150674568 150674591
    0x60c12060506030a0f0213030c15080708191d1f050f07030209030c040c0302092103120405010609050c070302070f1a0d110d0e010b0904260d060f03020301 68
    0x215a00d0340a859402882000811500302036a00006070004a44400510f006a43c50104a00581c50707801156600302c2c50344200507940f80f020b80d038240c010483c01e041700726180810300204900f5000340401c0d4040c0407128020801400390748030714004d013010049043c2e040130103103d240c0e84902d80c1c600e44100c06800310007100c000b80140a200d000e80103408800080383c6074030405401a40247c04070b59010322444010141559440c0990520340e0780caa180103036940305440521800c09080c0c2c00c0b8581070309098a8520340f18200001710758015540940c2004651114a0203d02406090303010007680d509010503c14080024002002c1d0584a40c08070b41407559114402c98964030184583c001d12910500b4107400401150000c11b0b0084c0035081c000b803042010510383d9541d0300400001c0c01503642c0c031441d44c2c52600d401d20440e5944a03044070401842d140540d5189500c281c40141140150440410302c4030034540a070a41c0c001c103030121404e11004c0d444212805a0004500c0305a01c01c0d03080144401e00c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 150677068 1250 150675818 150675821
    0x304032c03120c03032403011a01030b041b050f0903060106020309031e0a080702040f060b04090b06040315020903070f0801200316050c0a0f0501020307020f1203070c0c030b04060c12 80
    0x6508059002d5402d555680d00640e01048142001ba03000900520350502030b0380d03080c800c40380c0a000b00c03411030400424400006003104d111500090056260221285d402d014000a00104c0c40d01031070b0460b6103c000c00b090001f11300031511030710b406114810001c950150080042d0011800c140c04890200e01d200200442e5005018031100080d0041072109002c80d600400801405001400c04941011845880c0c000c0350002c0e40f189000303a4000c103040c00854158000d07a02110000c0714660b09140c11515030300e030060581d4801c490303415030000d018030040d02c085c0f0400c402000c0310082d550155070384562960207440940310125861040b141d103a510013800c20140e900440480000e522040305100c025036066100f90301c103c0c3c0b9031150000d04030000702d5500c40032101d00c0c40ac800150701c2c1c3c2000400680303000041c01708412603402046030301c0313036040108003901da100c00b940c03402440a103c01e0410840b407c1064001a100305007000411040c06942c0d0408000d0010b6a80c80d8141150342800303450 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 150678318 1250 150677068 150677077
    0xc23030d08010506070624050f010203040e06060d0e0613021912031202042c01150525150507090506031611070b040f03060b09010b0a050304032c0312 66
    0x80401e0301c01005100b5410640c4c05040320901c6548006196200044401544490007004660340e151300c03601030103541010f400d000b0a00c0c40c280010b6041500b841010760040800401036070087c1000700d40c0742c0b4010810f42000c0b600ea100c2105031605800c140103580c00d40040d440b02a03005190301308201c049000140c40c0c56007100c1140118400042d5296421141c41d4000e0300c000110503002d1202180c40c025202201601c044400b14028094403501d0034000c135600d05900180b840005444003c6401d030b0804200c0c1c5405400322109840c00441c0f2007440805031074045d02030456001d0381d0260845800c1c0d0381c4554040c404070b40b100300b0503d540c0c00421002d80310484900e82441c2c2c802411a1031580184040001a01e404040da0b008035241d00400840d41c03c01d500202e010000e20720704009001d00b920030004070b4113090714101640d41c1480e01c00c842c2d52162841d400d0030094000001001c1c10b100b60032000c07a1004620030070b0080c0a4000640030211580c0500f24480d0140441040c080c054140845 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 150679568 1250 150678318 150678343
    0x30e0a050a05040e0a0b091509010e0604021302041503050f0f0103080f130302060304082101030c150302070c09050925061b080a02010c030b0d020d02060906070c2303 73
    0xc4081078100800d00001c0d241100b8400050701c2030300c1d0b9603000905484107030385c41f510304200100341880034100c1164203030001501a05090f45490407a0610170004280154010307010745407018411a0010391340d00901c190742c095070301d00c2c0c104003221002540c143c002c5802902c9070724042e81c590f21507009a01c800d0000384801450f12030200004003080e07219901030003031b00c015000010344141e80c0307030041001c0b070340100c86c100e48020001914149424416940f10041002070309640e0942d8196a10103485036160301801207840782520f40d180c0030070700c60f4045990088c2d02190511102d0f68071040310020340340c281c2c0c80e0b80a9004200058149030b10991041c2441c0c200c000210404510340882918005589480401240c0c803030600d441c0455801c0c402423005034156400060307070400b840c40060803078100c0c46e0000c0c41920080c10580c0076a4481400309061901103480300d81c1ca141e520b0000d2a5071103003590060007600311400008120104004100c5080711591a8440c4504111b080546905026041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 150680818 1250 150679568 150679579
    0xa0f0f02160308060d080c0604061b0f0804241b020a020112020703020106080a0b09060f0609070e041b0206040512040b120a2a020705010216060309051903020a030e0a05 74
    0x506010a1103582c0d200d4211001804030005c04240f0b88561249603c030350f0088130705510503000d2100b0480c681c4100303400103844055400750a25001d10040088000440440801021201007001d11130021203403942c0450004c014091500d0a041960141c03c0d882c6128210100d80c0c00595281070000c6103400d519139050390340107071a041250195001707401c0780005500310740d6240e0000c0390880d41000704441080c081c008284d450f103014000b1a2800f84020000c84100c2401d4050040d9903d0703a042b81c54025141342842d072031641201d004103009007400050001104405860342031501d8000c00c00501641c0250142d038291620140c0340300741882070744034202c0f074910701300101c5d80003c440006c0c480d04115a210301241c01b4003080b42e0758100304512000310000840314441482200d03010804c2c24000d20003800036114126200d02802c05280c200e00c5080b05142c0c50321418010820148a00e4088541c1d003a61103a00480f10308009540f060412411000304508080c2d1a1840c603242000d002111002001e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 150682068 1250 150680818 150680857
    0x17160605090d0f050604080c10020406050a03050703091b0609090209030a0807060618020d050601020d02060a0b1311040f0603020903032704050712180b0103020f180a0f0f02 76
    0x1c2c407018100d450700035154441d04a280700001a001c0c0300c001e02981c0622240f07500c0d40090090380d400c10702004032203601184100420003806410030107079050000e03203050004440e6141841500070300b00d4402c000701010125aa0130240303c0d589000a81070781c0b000d03664449260b4948202408900c221003203580d050380951002d0b000151500000c2c801c080c0310740d9000c110310341d88681491070000840306090103c1d4000c104020031580a104503640640c0034030040c842e503c004e050280d295900a440c02c410b407030b29003143c0b00c4140c8450000101d41e100d4010304011581c4041908032054000e40581107400c241c0c0e08001444611074000e8880b00c10300180036503d00403120100d124010b460485600440131403082419003a81e070f81c8640c920501c6243ca8155905c00c02010b02802c44040345c007605d940c0d902c10b01300704021404c3c55840506490341620b014400c00454400201c050003280301201e149038002c4104403480d8640d0f0403c902c80500305805010081103140620240e00412031800410201e044 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 150683318 1250 150682068 150682087
    0xf070803190212120c040905011d0601030923070513090c06090303090b0310030501020a08060a060318020f030f160305060709080c0f010315030503031015023417160605 74
    0x80c2e00c940c000050300c2800c0d146c00c2c1d9840120041d50b00c01d80c000d0240040304155011103803800044660f10a41c2443d0401c4180708541c1c41e40b000c694604841c1c00b019500104412103c14104444409020f0080080860351109200e59002e080003000468042d001e92800140560041000304242c0e58940ca8000c802d60414942440c07681009121078845045280000f003c100c003031009242e9041c030303661104580e00e08130302440392050300c6600c2102014030b42007c81841c8891440303240c08036541107460040c103100b80fc001918040106194842d1809281342103e001b0b12000100000c80e8855406c1d03c0c025a601340081c6d403581a10721540101e50080c190341c51080c41c00312180415100b050400040c0224004420300440610350000c54055000009101c0031000c0c0321034160003414680849000809019002074035540d08520442d800385001c40c400032210b032102c03040b18030200d045100c04070f074940d2800c02c0310710b264070b29590f6207103801488001e00e50703010501520803c2d0380741522010f107001e00c0348 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 150684568 1250 150683318 150683347
    0x4050a060b0a03080f0a0801050a05130b0a030b0f0405061608010905100306060603020405030f0d170c040e07030c030b090402030c0d0206070c0609050109080313170f070803190212 79
    0x1c0709800e9110042071070210005a0343d030081c4c030100405800903502c0e254aa000a03100040c181c104074410184039030204115903e00269080020384450003184c16030701d00f4045940310300070760001861003524504000d100420b102c40340d4405c0780181c0444149072603155600c0903411900c441000004c109000500001141d40c200681140000754008c0d6050303626242c0e441103c1c0240c000c480041e4001404100c42e10741009100d40840400001d801851911903002c0d00d486c50002d1500010b20301c6030002403404070400e00b0f880c02405521118046490300740c4004006002e460b081c45e0100e441c211003060203080c550302c01849140d0282c000c0c075400c00300f0310402004021401d030899019004210080014072200011801007240b0745a010b404c0b03080070009420b103103481c4c2241500e948103210021405956940b600104e9060000348100c800410040754101180c558424041c1d10030391030002070b18070000008292038030402280003408900c00078100e8441000d0800e40824080900c480213810440 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 150685818 1250 150684568 150684581
    0xc0201170618070f090611070e0612030403030305070311030f07050309010b04090b01050f03030f0f0f0702060705070905100305062415031914040318080109080309070603020304050a06 81
    0x20070080c4052041042c03002c088500311002d600041c0d2a46200c0441c03a0450503200203855079003404402142d000c0c07041c1d943c84101e032042200c900f81880204240340c40e080ca5440800d0315038425a9900c90b100d09000d4007a02040e5104400240f8282d250f083c0031744000c060b00d0180d10100404100341d21600030441c3c0c95000548103d1080d5603459610205560320301c50b0f141d2182c4162162400d0398034040c00c00a0300544140c04034000c1e0402c0003000440381d141c1d0300301c17102810078105490302e98854040c9900b46001d00301e0025000840050250280040002c10b83c1c00c44100c20750034001951180d030007001540c802d210040c196031281c004a0b102000510031141554401c3c0c021401c4803900034001400360741c0a2030740120204001040c064001d00020380c2d101c02d9002000c00340b00b4080340303000c04014440e005101904002507029039954980622400d0002848480020711502d54039003090034040d8820740d10380c0c5c554070078101c00054860290096900c11038010015060600b65a02c56a015020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 150687068 1250 150685818 150685831
    0x8150d030807090902130312170117030904050c0c01050c0a09030209061503070c0615030201090b090112050c041707060207031e0204020d0e010b150a03021c0507020102190c020117 79
    0x1001d9000c91040b130188041c00c49011403280c8284140d2550420704501c1c403004601d1410056030315001e690713118003540c00c181101c00201680e1340c1d0a240100b00c500f98003078500582d43c000d0418007070142000c031000203030035041c2c0c01c64001c0106440300d40910203070b03104140100010030010101000949403922500307502c600d019000c06d2441e4018906050154005c4540c1804203800004032401c1c800300d44101c54502483c01c3c401005603042d900081c200000314400d48030203107130000d121003403640308225050344000c001e4414005400c01c0302d0559030a40041c0a912048c082c0e03550101012000024030b242101e01c41d4019065a83c02c41d06d900e506c480c0300300f4603180101050200b110058445200030880c8540e428000a0419040c900381401e40340c0b000c820510441d071010078008443c00c520101c4414080c142070041e52130840425080181d03100d0460722040c2450007041260712a01900280107003034200012921881052030b0a4403140604040680012048042001250343c441c0071243c2110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 150688318 1250 150687068 150687077
    0xd030f0e010203160614010e040803040b07121514010305010e010b0906040e0915241011120901081602030a12060b07060f06170a0f0201031b020a0308150d030807 71
    0x7000e4400c41000c0b200c884030464100da40e806c19400d00004145440780580580a42e481260034551500340b580e01010b00040c102030b44400c01310f5001405440c2c44501c82d4040001403024001c1480f18142d640c42c144a000e00c5c2945841c100b9143d50320034403410b810f8408541c5d181109909020b50790a994128100190300030351700300000315002d280e44080c1449150000b000b440c400348041c4030b4207000c80015045104200b42c0c00a0400c8090041e2014411648203646051441c0c80050b000c9800300d691104107400c5005081650b050400884000c00d09010300303807620640d5843d81c620100ca88214080c00800580003800080065403207000752684800c0d100b0004a00d0300c1d02d030981c40c08554011a0102c41c0076079124901c00c40c3c0300050181708000c0000d8544800403480c09842162070703600050340205400b8001c11141c046a00339400b2a001008203001a40c8072a0144400707540c440703000005801158810340002d0600300458146520400050309445441c001070350165000c81c0050300794424807 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 150689568 1250 150688318 150688327
    0x100506102a02030f01020306030709020702031f0b0d0303050609070512011a040b0406030203070905030615010309060204080105041407093b060c070605100e04021002010905030f180d030f0e010203 86
    0x42c0c0d4204040c61138002080001a500d060020405142c411540d01c411062030040c880c880260b03030042030069004250006032a47d01680c840040e009120010909030301407240c4240805241d456030090344074043c15140c010054407100c03030580355030080039650000c4203a000010702010409032103201024403200f51241c00e140d114100700741c0b0350f0402d411034000241d000c010821116031040e12000201410b40252a541c1400c40301d01900c41c00c5400f90a0526844044040030003010b030741207800a058000003001182811314040f41c0841340301b4440e14071489204008200c6043e980304004502c03105440910781c004105008020108800580441454144101e020702070000c0c00402d100e1903601040650314182450108100c9102400d4407155084020051059032070940000d60031a804a450b1840508007000c100d0152440340d200401d01d01010420b20b0900345241c002d0008021000c82d00341200e0404414010700c445100006000141e913401c2a011700c2c0c2c0221811f0709410f0041c810b80e441c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 150690818 1250 150689568 150689573
    0x604030c030216060804020310060b0f0f040f0306090209090102041d040813030312140c03071b12091a09030a0204320405070e070509012a05100506102a 67
    0x280f19030b907002d44041600c41c001c10045250a120015040c031a00004000c02818040b10248500501c4421440c03800009030079200c040c4514181e8006010ac000c0c100d8100d0344034901000a0041140124000e02d02100440c072181f106009907011f9801c4c2b00405004841d010f00c0c3c0644816000d001520240410841d03450050224000d141c01b850181d200c000750000c0500303100040701c0024400f241310303015800c00d01c414100b03070b8400c89803c00040c1c40c0070841c100d5459851110340700b007690000e04101500e1680d0f00340580001207001101c032050302e01419000f031000001424854440d04644c9500300808040c0180b42951107030215111420360b0150140403500c120342c0c03500700c681040140f0a903c0c1d04000400c141088140040d0922500413422801c01300c0024219000e4400c645040c04002200b84012134451008503407618291204090500003e01706961100101d10040c1c40300c2d802c01001803000e0400449080300300100f590307049103122803001c4005015025600768680342928101d620701 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 150692068 1250 150690818 150690853
    0x3141305092707050117040606080f0c03011a06030703050a0b04020412020907090e010e09010b10031d0610030206030a090812090c0307060c0b060103271b080604030c0302 75
    0x840d00c124201c00c0035140c0c4110040c0c8604410300314030034080c3e008100902550340e000c0307134040f0784801506280d0f410b500c80d85000c0010700001d41002c0a98482e14488400c4980c0000f55904d40c000b0960080219010340709002d030280c80d031107100c00c0d0011010001b28440c00d03c650f010690003580b0505c00070f42841000009420b0340d0140c0d0000d00d501042c0002003003036181400c0346a411607040d04098070b00c103240c048003054003001489401b1480603544000b8080d5030707080d04506c110103030060a0104412112002500038142d02c42950085808194801c203030000001305507005040c03e43c140390400e403541d400c100842c0c0c0010302d000c4078582c03100c025000180072034025027041d5a1107540001f180c54110341c03542c500519089058400c1d40400c4080002c00d8024640100d110b400007448d86807540c0d003030016005000b407036100300e074401d810000e0b8108a080c0c0501401c1e2551140d9960003001c00c140034100b40400890003500e0440c1c1001000c98000b80c01140300003980c03071203401501c05000c40c421101c0c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 150693318 1250 150692068 150692071
    0x7090b090321070b061f0c030519080f0a060e06060901230306090a0902010c02040c0e0d030f090806040203030904090510060b030a060501110d0f12050c250314130509 73
    0x103000c02c000f06115040102c0c4a0781160700c4202914080001113100c400c407501031420b07840100602203040c001a09040c805c80884200780d80d0050000d48209107114000d103005003c603500e28814101d800403840500c05401443c08442145455103616214001005100c0c1d000320810750512450140c034044070441d4201410b400c0918841d459100d1511038140f02c5084e0b8004c00110f0301e14a894403030390040c1e8100c1c4808000e9030301581d0000f5910350740e01c000d91344650f00404560344461594075032010036a002c0690540041c0c10303030f284401310303948034105070f503a150035100254550018801d11103a810194441c104650145040b0b4a00e0030b0075109001c120303421900720304c80000780002000007a1002e406103000400d1b00307281180c0c0c4158003202e140d8a0300c01c40d004d80300c100b29088100340c3c400c034400c4100e00da20f02e48542c820081c509080620906031307402280c3c50300541e00c0445101c0e18070901000d150400035019215500d1031303500c00c0644103040e03000c412207600140504201003071a403280b00089 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 150694568 1250 150693318 150693373
    0x81008010e0d201f02160506090c0a0e01092c0109110114033702040801110a090311130207080a03051023040f09121707090b0903 57
    0x60004240881006180030b040c20203005001e80142c60f803c204002c00100e1602c0c122201114080240b21101c010002c1d1140e20051300580a800d11018184400820101d0194007580c0031201380314801d000380140741e112803180c181d401d603416004111000c5980c00030ba224446c1005c070100403088212007900c00e221501180c0d181a0740d2000100c0c1000b4110a02c240703c08401d0800d0640103038955244000c52100401100d601c100c482d0301320ba0051086013040a40300100c690300c4402c2c0c0d62542c8008029003007813007100040d40c2403409a4401410040032110b00c2455542d4200009040d61104008d08100428a030740140b0400d480790904035032803025094a070710410246984903107507500202a40e2000e40600361034031400b2002c21250700909142c402e4040e0f80034015080c13010004c0010000c26401111190140c00c2501b80010003240c00c0140102d100e1300e44540c04d9100c80c421409107400303421500c19010440e12001400200b40b010040d180c00840101100e44041c01032860b8100b0a4100c0c184 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 150695818 1250 150694568 150694573
    0x6092208070206070f050a0b0f01050a091a030304090f0b101707022803021e031e04030605010801020909070e090703090816141e0d0c15020304032d020d081008010e 72
    0x1040412840014843d00a414134409c52450350400d07000a20030003007881544001680c5102290031112510b05504800100a09403500c0e41e070f0307513a5040c0141c0348100c0c40758002c81c58446011750614100c100081c10429560f60141840d810060351100c406010b050038040d88124440c1c4105c041c13180c030f80e12100b03d1400804840c1041d462402a2416000340c030802203102c201804c04158000001c103407801e01000306d4a9818500341c00c504400180b1454101801c00740c200000400d0040054000780072010302680d4401d03450b43c07201005c8544104406826034402000000310f40c2d664403070b0b040307200c8090045003010300e0074500100049000103c10710131035298241020400c510fa005110300300003c44108451a07114981036601d9850b0354020200380141708a03c0750001c140002d11510032108071840e8811507807070030700d07040240c0000b0351201d241542d0141b06400a40304840641c036200c1109080d00140b15980e14610140ca0001c8000c142c591044142c2d800010101003d0041425848982c0301 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 150697068 1250 150695818 150695833
    0x50c210f0301060315140906130f0e0102070b0106050f0f0702060c060709080601080a020306010b0a090f0803030f060a0506090d03030213030609021302070c0b2a0606092208070206070f05 82
    0x2101741e18140141d22206800381145031044903030310348414003580606c0c1120050004050305108100500c008410603042d00c2c504107042510600550051442500410021503d0386e61258111014800c051740ca0404681c18061242203001c148007901c8018401000d1604020886512503c0c118003141c10000060340d2841c204144035050107102e0142c44150058120300007aa00402da480c4410311400c02d00da8800992000e8940c402c40d5150051310011101e6000079030381d0703200c02c0e0341c075041070300d0241c0c80612010108803149896801c1404851700600080d003048070050070400b1011102c0d02c1a014990200b0800d824545030031140070246100d80c0d400560014140141302d9030b00d04990308200714910402900c070106509240003011100f03807622683d51001c12010712500b686171302010348940055400c52501119000c1241c6100c1d29080e00d4151071a40d40c4403212001d500c10500c2800c0340c42e032080b45140400e00708c20080c41a0744c00070344003901c0c001199607040c40c0b12002c3ca00c140d545420585 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 150698318 1250 150697068 150697091
    0xa0903080a031409030f0a1206080706050c010b0108070905060c010b28050607030801150507080711040b01030c140702010513080f060c031512151005030d050c210f03010603 76
    0x8403640e00045038130019801c00c0f9003403044a040380310f81d40701c0341d05011100b65480c807a81200e8018a01524140b400d483c0e20540e035540192003500305c450341c52a25402c010740c0150a503c9014554440c41d010f50f40d0075401c518000a10002d680810031092095489588000407a205d01140280310050700c502d01000b0300d011000451800c040d6080f0314411001049000c01080e0710520580c15150040403140340591040800d60301d41c0b140000003040290041060010b0240c2801c070600f40f1a0700352811b000c04820100110b046840340c1c40c0100106003520048031780e80c1c8000002d071854030300c107041551601c0c000c0088231000410991016400e6032003681451781a2105100180c1c0004464840c0750550500c201da602c4404031180310b95008581440302c10000440030009150f86100050100b412414421040740c001d50f21401032900030f00c20541124555441030b421a03415904c03540140042c0d600c030103d2031203070000141d13401d40c42c0c140500c0401d00c10180b0000950003401c054600061540c00740 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 150699568 1250 150698318 150698351
    0x90919080417070302150a0c0b040c0302090601080f041101020109061415011d010c020607020603150a050102031806030a09150618111c1805060414010e120a0903080a03 74
    0x40045040f50081e00003000161990810411054111281c040d2180d0500e80129100d10a00308080c244100c0c5070107020600c4206124041500c0c001d981342003950380c918005444000007618202011020351002401041c030740b49050068160510011944200907116001580c004034094a842e020040c203000703110301850445180c0074002c0c00c0400402c850010702010f8000c941d211103051144800c4030701c0455981d20211102207600401c2c468403424101c202030344690400c2a01400b52480b03000200c1d1031341c000821b0324601080b940d9096410703a040e1051152580006c0d001c0c0500c2603c98140c04002000080aa81103920310000022020314000320340041d004a0221b401c10145080303401ca1011250303100308d0b484400300301d082c1702607012801e50050051102c6103900e82c102406841510400c403020079142e0007a406505080c4148100300e00c00c07801c070703442c41a1040c442c0e88000315400001d440070740905000c0000d810054119030717680d10707042c200f07521802c00c0e980069981e011003c002c0409 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 150700818 1250 150699568 150699599
    0x70b10060c1203020d021b0319210e0304030206070516090c050301050d031101050106030c1404060e090403020f100207051005060f0f04020910020c0310050402030c0909190804 77
    0xe03203800510034580382ca50829010880d00003808050300003603003c4002c01e00380c04036607035480301c982c042c80c0c2550a4100c45440c0e402c00d60f112103600e8220369442c84242d21614a80302301252040d01e03d404542c4822142c00141072050008540f40014000000542d4640f005091028000d00117003040192503481c0390380030001d6400c072202c0b940c9043c0d8080607260740705050f80c0c152007040e11007c8044030942010f64841c02046030f0600650708040006c240180d2580215150804503103904088801031000071902e40181d0040c40001840340d071122900349401c0402640180c001d00559a52031401c1d15001d00f00550009040809500000c1050802108010401f0b0540d1036240400040c140200000c5007014260b040318480c0f152082a1016940c03194115000700000500b001403000e002c1388040d48941c2c42400343c80c40b9010b10303502490700310414000c1c1e030720441d030060180040b95251000c100901070043c100000c14030911920034062840071200c4d410702e40c000c44401d5107640c50400e00c0701c042e191 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 150702068 1250 150700818 150700829
    0x21e0106050a15020303010e070c02030a060209040b040614010804080d0c0f080c0309060c0c0102090301140601030e0d08070311160c0f0902041a090d050d1d09070c02040e01060b070b10 81
    0x20301200060810382c4c00b10030759056036100701c010b8071251944201100c040f012a040650315003c0c01c50380d2020000701d5401000c08000c26a0309020700380031601004100c2c1c0040c0b164500c070b9a05140c0c400040e601c038500080c0e100b0701c140d020a04000b4460503040450704001e03141c4010422158076010040d4100d40704640c800c0364a11128558600310003041d8481001a003402280744012405550703041c001c1d010380e0403500000c0c00801c517030703d54049480c0c031254054408601003840e100c40d54603411400314869405209079215807030983c4030510110000c01d101c0c242c1c651468800e01402c0c40800000680140142c02111900101d908120680781a2a855400300e040c4074410003003002400400c4c00410707958140300e040161100c50f000003203500c590301c42c40300030458020081d00350340380c581040400c3e440a6040004501c11503440041c000007042c00c2d1100d0003c21640031341c142c018a466000307508124420000866102d5440c1107032022034115100454002078518108200b02062441038401441d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 150703318 1250 150702068 150702089
    0x170c030a140411040c02070803180a050f01020d120204030b1504050a0e070303050c1204120c140609040e0709020315030114060907141c3315021e0106050a 68
    0x1026940d40d40c010440c0d2800c24001c1761a008840b00550081c030040c001002e882d000d995844080f100031484e41c10803c202d40d07204810840c000300f482d003841300d5001d00c01d640c181c00034030002d00451001d85010f8089541c501c0061340801c0044002800c84403807e0103100c074030342c110300c005820074101b0050f620000c041080c3d1034903000800d10000c04c00101314007100d805080041e50b075000c025032103082905040d9203290703040d0001000120904048803500c0e4090180b0101940c50b510f8250300c8811028056415900a00a00072001c1900c1c0c42d0f441024500e1040d012a0030007a554410b000a07a00119103403082015210300b10a1603080038043d041d0755605c51030144000e8940000001c0b05c900d005410701c0e00700444100c0d12004442c41200b00e4003021080d01070b0b82d582c0c05400360000c0c040c054441803d00440400c81c002c00360304141030b003085100041d8a02201405e410451000340d07110440400b0b030118070903c1014101c400380d02c0891801d000c0d041c400402c06606200034403890030703901e6010741d5006c0d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 150704568 1250 150703318 150703321
    0xe010513020a0603180b09061f15030c1101061412060103150b010203160503070215031501260a0609050709083a0c12020f03040b0a170c030a14 63
    0x142d5518140c0e030700392480c0e4140080d1078191030300c0e001519044c80310020400c0d9481001e0200c280d00000d0080d11910f40f074003030303200e01c0204410400e08010107803180c00049400c038108940a1030103600010220185483e00600034012403c45070b094a240d5842000040f80d030840340050307820050050081d151502009000c1c9524668038034178020b000b642c0001486580700e588060980c42031040361030603150740038441004541810000c0e160703480b5400491140043d900103a4400d20310302d040ea0310403400c4101401401d0b444000540b10300e9011540600c50b054022a40e000c03a45900c0b40040c0954600100041d00605202c1c3e48000c98034080c1190045c8841c448040103810704c00692034110640d845908107003800d5030510000344004880389000045078401d1614a400e6102201d0641940507100e07003504ca031541c400981e120b80c10900e9180c0301e40c2080009103c0b8000040003400b00b68a01c1c6040c0c2000c5200340c1b114840d1007415500b1645814000090111004203400344040d400006c80b89005039 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 150705818 1250 150704568 150704573
    0x605010f05031603020c070806061804211404090b0a140d0620030a02030406050708010810090503090a0f060e090105060d0b12030a020106050312031e1302030d030e010513 75
    0x107400020103c9009821880402c003841c0e01c650180c40441940c0f00484044507211506641c54000444505008002c0fa1350804c224448441e0020f01807034011100d2500c42d030f4036001035103201c8182c0e81e203e41170144c00a000c10380b401c00b141c001c02c01000c00c1c4c540003807903690580030002101103035401a8029040714a03500419030710b0000903207425501c0000003608065014203150b0303540e0304d00d40c0c9204080c0044108910080d070b580045100da40f007903008200c156103203078094600410030301030090650701c201c6004140040d95417184107494055000c4904110320782c0002065414580c000240020b00c400b42082901c2e04a40c03503918590080f5260180d942c103140114446000f0f2181c0303c0f6090380c0760040420b05803038444c15034000c800c0c0e03481602e6460500005c068043c160610816010f4031580710248012003401068034010a80c180c40b220b04140c2080300c003424140003800d07084172400d0408000c80180e400f0400c2c0405481151004500c05110364081404c540008042e000d000722244c803007400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 150707068 1250 150705818 150705827
    0x909060605030609040c030f0b190507050306060a0509040e0703021f05091509040f27050c010309240501060e06161203140405070807172e15090605010f 67
    0x184003074140d134001840e9840c2c2c2802d07401a455036201030701e0004140014014002c51511880c8034140c2c1034004100c003002c40241908a807401c85000c1c000440600210300039182c4240103010503122841c20b40c1c1407920140001d0111400f5005504490f4040d03c010000c6081c515641c1e185000b004000c0c0d0075421010030007a2a52080440c0940700d0f166040c06606101d1440055807203101004c1e09c100180d8003405030640091000020300350403803a98a68440c404110414101c038440d5200c4003a02c1d09109040044d030240401003400c4641c00600c0c01140310aa411b010100300711050400701003090752400034094103c025207400c580c0910342c00c0180c640310b004007070140b42c0c031036038055052815444980011801805880c421807146e4405c0c2e020302040c400c001602100303882c19070b0f060f00c4010380c0c0c8401410314410041120b0034581c03c032000e04d001c444480c1c0594041c000b80c01e41611014488411120f0484140a4407400381038955001840707220f40e1440ba48000d040300b82000e514202905e0b00141 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 150708318 1250 150707068 150707071
    0xf020c1005070b0f060310060b07151107050610050f0120011b09031103010b0901150c0206070501020304110111070314010e030a08070212120c0a0e030f0d090906060503 74
    0x6009a024040000c0303054490422211801c0e04449540310700d00308004020450002600d01ca0303c81d12030840c08420030203e80c0314900071152a5182240303025025a600c9402403545000304480782c1c0d94448411000c29144010099544940c000e00814030f00f2032070000805180380c000324010b40021580341c55998005e01c2d901050006051b52000b4444d0342d400c11805424503801c0e80b034006048540e018076542d085207250f0144c0b0300ca403503522009030721002410700300c95407109500e51000c004401041452240d049808500506240074107680240d0f801107011031303101c283c04460981d400004c110074001d0280b900011841c0900c4c2491004030000c0b0301d02e5503880705000c05031110b6070343c1d0540000d004d001d41c4002e0500c003081e000e0741d8450302d0025015299800454010000d4081d420444500144600071030b40400100301a555042e10b030782c071448800c1e40251000d1014800c19500186560390108071944060041000606206c502100000d1034940c01d0352116001c0b600300542032006a41200949 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 150709568 1250 150708318 150708343
    0x120d0504050f0d020c01080c03070c1b05061605060601030b031c0e0a09020424051b240603010605010e0a050d0201051606020405010305011d041e140a060c0f02 70
    0x816151218185941400041a0a40000d105202504000c182c0100340e103039510000740c071414180c0c0d48819490702c0500c0100c80000c0001da40d80402030016032007070030461401c0d07841070003580342548130070108409900c58213200f400740d0324042662007008800c00c00654080800e190520035002c0e4440800c2d556101d40010300b10354001c2200042256210760b03860303030104030002d001e8540a40d4130071603017000358024010103c120b8004002c051954405031480300800c8a10b035605454840c543c200c0001c5071680f100c80d00201c2c000c0810402c846d84030003c08210a5400300742914a03401c1a208040c2120203550100d4184000c00c0b91075001c3c0d1b0750343e2000d1021100251540700d0380c101540b0040b9100d101d5407407890398001d4000c0ba168103000381d9502070300c01d440c801c0c2c8003042540d884403503485e1001941903012506c182c6007000580041c0700410440c0d00e000d5080721144c2c030240310342e032100e03e4100307070b00505103c9a000711401024041107001e03c08250032641010290b1501c0c0040080d1a0384116216 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 150710818 1250 150709568 150709571
    0x90b1215010608090a021e0906030a08071704050607060e010b0a030b0a02030403030207050d051e07050607031d0a0506160503010503072102090702010e060601050f04050904050304090c0903060e120d 87
    0x5002804217008111540d03900600c081e1800d50340040c9071750711014607815103026100320f00002d1168100060400030403908498810300f0f000c240d035111078521400c00fa000b112803105010006241d141c0802400d2131a2107144041050700c2c0003900242103031005a01e00e4031546c64054100013041070031140c10b0700503085076000360b543e41c3c071420241e01a00c03910070005d20743d22031641d2008030f1551060203003d03041d810301401c402c03038a0003601030942405100b0b80540280c0240c1d0118034014060760000695120300d55a5012103110352107140d042138084c01c01926182c204500300036905140c0b034566110b4500c981821805c4d0350510010960741c044500400080213201c03c5200c3d170500c9446200701c0031aa0080c424119403a003044028040d2074803242a40d200d10a41010074944c3d03002d2001d50300c00d02070701c40e034590501f840c2104001010b28042c0094405000800000c280750489008001104540b9100e94441a1541c9040c1c41110481c181e03030940740d084003030031000d6490540211550103035113000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 150712068 1250 150710818 150710821
    0x120f02060f16050c0a0311040510030c0b04091401061709120d0b0f01021c141b0c030601080a0506010308030606130f081b0f09190501090b1215010608 66
    0x1041040c4100c06001403024408a191110107200b480400d1001e480340c01912030244204050150388802030100419a40c402ea03a52403079401c0540c0540c3e1b0102ca40c10440f00e00c0369a03074503047c1403004a5084100c10a40000d41401402042d000e51b80b900703095181e2030009503144c031800070841c90100b031449081d1041003001c170b0603211040041c0401c201208a00e640e884403050340060040860602c814000c0d41d4841e40700d5010f40c00030900c200f01c100da0826060800d158a00b044903542c10010403050034000500101801410315849071800710b60083c02441811518000c06d494014160b000f0310f80c0c1ea2000f1200c10001d00c01090142c116030780001041e03100c0d210390340010006d004542c00100300e05ea204400092031341d064102c100c201d80800c030a8a00880300445c1d81e42046141c038031000d4201c0d06200c01c502c07440c1801090103500548103001c11003e030040a0886060358428dd0111040544460801e24985828038207641c42c480003c0082c01100c646202c8500008014031503001440030721070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 150713318 1250 150712068 150712073
    0x20d02010818030a0e0f06070c0306020313150903090e07050a03020d06121a06010309020312071b030f0c0f3203070e040c0816121112030309011401120f 67
    0x40000040e1200300b01500e88450b103c0c000102040000c1780707580e105070000314140c282800c3c610308880c60340390000d240e140402c1c15500d4a0002c0c1d032000d4462400c80b6106240c01c004101160309085a10f030615001040445160800601030308254104000c444c2c41881403080c070a820108440c01c0000c1d41c00d01586400c50844848010312041e4041480b1151310030180c2d04200450f40d0042414810300030300ca0a07621a6801182260384000d0025010b40c03143c01e24241d014005000750107e144100038440020108104000c064442c0350301c2294200c072000c0d286420000388280880140099195000c0780e01c1c40c09104020b070041011080c210040c10400403000400980c00d4115070f140090f081340d01c0d0584c0da2010320110f450132181610302448d6984045111140400d003545040a6481034600650134400c5400701d03401c90203c1120360125180c5c000506484005018003c1154140507544a04e44030165a003550345402c0d842d46801c41500c014081031302c5125003820700382d0b00500048148070861 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 150714568 1250 150713318 150713341
    0x1031b08070311040905090f070501050f0c0a020402070807030813030c1101093210091e09050709030201031a100e03010609050c0a0f020a080f0f130b030a0612020d020108 75
    0xf4160000c090000600850707251000d41015000d051210b040780c5616241d01052911848140103640c000f40b820040600b01140c400e02900c030243c000000d03030ba0311040d40c0c3e000030103c3e8000c2e0400c4500e11000318600042c140c0060320294041c1e504020034403c884135542c02401080b400d03000800b06424401071040c10707445660b102002e404224000905001e1001079141c189906510389622014003250a0000d0b00f03041a040b142c4451741d44480f0b04081c28a150069107016010190764190544040021302c0e445074000c183c0148a5a143c010f01582540001001e0394400070a44a01640045803840e2a85070918043c0c05080d541c60902642d00c1400002400341049500202c0550b0800c1c050100080280009140400c02c070340701e00f00f8001c00204d090340c84812500c030280c0703007500c2408210b071900b4040004100d800115918a86048400c6c46c07612500407035038004c0c003007a010200400000010130321940c00903241e14161203000211980c002070381246184402410845420040389920784003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 150715818 1250 150714568 150714581
    0x140309010b12030d180c0e070c06021908011e09180c03200114040501030515060a0305070305060f130209010c0f08030403020d14071103030f0a08060a0501031b080703 73
    0x80c1a800810030007042c0e207a50380c0010f40006456858800c510510000c218034400020740c0c8002001c500510340040c2000d1404010107007018000c1403c01c41002940314070090400200b02c0d40490017414200c139008096501c1600300c58001e046400f81c195120140e52240d00c112a000c11021500d408038079141004249244001400460052000700800103100c40c0f64036038400018044000464800c01102c1c24484005106c000840400091203554480d81100354491b00007410301301da40c844500813a000d07038040102000080e55680520408941c9805140c1e0050700c210f480d00f1050030000002140f2a50004040c02402c0c3d00040d241000e07409990304001c0260464061804d2180f6400c3c41040359200b15000c5005008800100705883e0092041c2809244e44e480e03014246a00c0b581c6041e1410307581c000450307251105001c0580500340313600040c0021040c0ba070b0ba04046051000c2408000900d80e0025070505080140680c0c0035281c03100101d019846600d4150b00545800c00180c0003040c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 150717068 1250 150715818 150715841
    0x12160f1d132604080703110d0c030f020102031603030e0d03020c07050f040905060705040e0a0606140306010c1407180b031f0b04050a0203040212070501090605070302070e04060c08010f0614030901 86
    0x1001c10f000038040c070040303014011a409809490300742c1244104118005040e50702c0240b03203414007041480892544440b41c2d43c09481801200e01e4100c0d0103482e480038101960382180007a85400c0103001e16081400700c10304c0c01195050640c01c003007081c0e06194460006018132405038074141c0c0340b0002580c880d040707a0076898000041d01d104c0c0c2880070000b40150312501804180c00c450001103841a180e038892242291810380c1d42c07190644600500300c8250b4405452035040000344400140419058040c0040303079800813000707280d060324120303208000141240950341c0715840c00f030208a09403000300309180c41c031400260820940c0160804c04000307118454600750882e16013010414481a2035000b07500450003101c00340c00c48074480704040d40d20a2503004050004890b00400c1142c14080c1007c0c0017024880d0060342c100300d8032a44c040001040899041d10f50380d4650092100311a040010b060140100d100144125401c1070390107885915440a800e030740340030010006002d1300c0c0a6102d11075624 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 150718318 1250 150717068 150717143
    0x1e010203040513090b01060903020306060d060f060e180102030f0601081003060c0c1707030e09131e170f030105061612120b01020f0c12160f1d13 64
    0x20300081c5440040c00144c1d412921000c01e80004654103002c0d00291003202c0d030080043c10700741c0e590401d01542142040c3d04a0f40e10380c03103560812500b00c803400f4160203894402c49140003071400100c581c0001a4180a00c28a40d00c10028072080e0010360720219845082030034030242035220481c1031000621158005000a4600a03654000383c0d4018000d110b500c1c003031a410402e0040b0100780c0074040c07240c02e0000300402c00c1c00c4c0074012503007407417030080754040c81c03ca0410040c01c2003521421900e080d19100510611059014041048940e059420036090081071050600c0c01e840c803040e445100601445100300404a07900d24440b03040c3c587e4542140d0711451254040b49120009001c1500c00c40c0904050b5040807813441465100003080d0003403d9020703000707090001741201400a0781d203c100c0130700700313a0240e82001380103048481d0100c6c000303000b031955281c0107901d84001c80c180f00316224010404001407030107104d010050166012281e82c0c01c02042d0454644d01d14441e107002007030440341078111 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 150719424 1106 150718318 150718339
    0x901080a050a0e07060503091902180402040204030c090f0c030509030706020322050319020a0b0414010b040f060302090115091802070b040c031208061e0102030405 72
    0x1e5141000181c030303034010f9684a0030041c03150400804107200000340030040340100460180303880034151100d04590240d0016105c469503084151000b0320801c042820740d501d80d03044034020b65028140342d86065496aa100103002e400703580f82083e40c034040b02c0d0544503004e0f02800744620000c1000d103240402c113a4030280207400103040790680741030780c00403400070952200000c00c919000d00000e54441c200401200c600f820900c09540031900b10030080d00000e15500c407466000390307100c45001c00c64207104050b113004041c45c0c401d965026050480503100359030a5409601964003e45021040383e80b2068101134041c006c50074540040e10108080220350581151f855502c030040300090300c2c18205480d0300846e0030f0141d4040da11104a40e004000b003240b610100c100031480c50610745c045203041d9001483e202c201500d50300e500c0e160b818240300c1c80ea20910468020701002080c1e419403 = true := by decide +kernel

theorem cover : BRFrame.Cov 150539568 150719424 := by
  have h0 := BRFrame.cov_init 150539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 150539568 ≤ n) (h2 : n < 150719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
