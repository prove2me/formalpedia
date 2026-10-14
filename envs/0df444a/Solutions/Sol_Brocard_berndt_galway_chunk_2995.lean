-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2995
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:21:20.484137+00:00
-- url     : https://prove2.me/submissions/a0652e93-c16f-4790-9c94-76a1d4e6e4fe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 538489208 ≤ n < 538669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 538490458 1250 538489208 538489243
    0x12060b032b020c18040314040b0415030905030d05070e150d051302130902091006050d0c1412010509160c08070c241101061a0d020d02031905010506042402 68
    0x24031075480000c85182d8080d602a41c7c652061180d410702c0580c0c54401c9104564a000040000300300001a41041c0a05040e02e8500070071003034542d444082c6190040c410030b4480660725024041013580101306003d036890140c036020464010703180744910034002c40d00e50300603136070325200068418640b00040450095004100a85142d18003401d00d00501102d10f04134060304c0c0420200b52000c0ca0b8000880031038405aa030186010003050500018004080b217400c01c0c480c0c0e488a0001c1111a40094081c3e400b80b055800d5481d031412042201804020700301d4400045403403c0c22000d9607000320750604151304283c0090341c0e00d600d450408000c00056104100c100d65201d00e00700d05440341c581007002c004050f910900c4c4640c151012500b280c03064400c00214512004620341c820001d40e025181851002800606028406041405903403048684180c00c1043c6070344c0c014402c505110381c50242106a590398181403c11600c80103144000c41b5400c45101c3c0101a284418402c105180119416019 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 538491708 1250 538490458 538490479
    0x60318060b0303091c11011b1b0e0118150807050d0f0204060b0d15050916030906050f011503110901050c0c150d0b09090c04050702030c0712060b032b020c 68
    0x4411905d02ca00b083c1212800341280001c03181c0d6115100c2000050310b2220103410a40e419903490780c1001c0e02190111805000d9000021002e1550b01e005000748001320590329200a251603c0d011580040d0100c2c0000403922170601c82e20400098800c16607600340c8200c81040024204a040309003007880080d4000c0c244000444c1711000d60000c0c02188003414010b000029a07807100e1114925a4007070700e508000c2050008241402c4506500e03060411402c001a44c00b04584481d400d881c0120380081d040a802401006a9802650f500c98000c0340b6240410241c1c0c2b102c001c0514038400d00c4d208030b041100214102e4800101072105089050004003082c01d80c503c0a0902c05032a0010b00c007007140c2600e0f000c0741a074282002c00784940319118020280141d4044201040010305015000804510041c0a05440104100712200152800c1c10803108901e5140c41e21000756031300844080c0c0607030011150700007201d02320710008200864644000103007400e070f50412841c1c0f1560700204c07584040e4584 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 538492958 1250 538491708 538491739
    0xc1703041e030b070815041109040608250f1a0405040e01050403081f0902070507081b09160e010e0411070b06030d030204060f180f08031201060318060b030309 70
    0x1d0070307022030748903c01d80c0c00c95556803482659500d00443c0e460440104a0200c41c2003494a6801040103800030301481e403c2c4018100400c044915540050141c0e52050045011128010b02a2101c010304058a8034425090601d40c510940042c410000ca224858502074000c98210090390003920b8060802c000c03807c00c0700d26240c068081660148c010882c040b010811598000040b6080b407440301035908895841d1540d40e000941c0100401c1c0c0721805040c4011422800500c4521002020080348003e004550300400c180b80700c02420302400a505106080748480d0000310001d00d000003400c1c01c150424204021502900d51800389a1821600094080030081c00040f0745028440c140d0441e00d000400c000d050701244503d0040303202281c020400a0b048905c10100d1602c040b440d0b12080c0021551200d040752a041aa000034501d03030804a19000f0171000a9200b50040165180c00d00c50262a0000d940c8883c807403180207429507440301340d0002151020000c403030101101902204070a0b600c031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 538494208 1250 538492958 538493009
    0x1505040203091605030c030c010c02040603050f07081c1709070b030c04170105040f201e03010515090a0906020f0406090509010603271a040b0907120c170304 69
    0x40354540f08646412004191410001091403c500d13000c2c0c000c040c0c000310305005480c03118034040200d80c400d46420001c00001c000340070341d500c800d4a84004110060925405c81d080644485603000b4585030810303403c03252613101d01c0750607000703120100c43c0803a0f0b200e5203003031410031050781c0010501364000001d11110080900040007141c4070301000051601180c0303801400d03107600b079801500070700300150349201003045102c250b402c03000510100e400d110704040200b001200b0250000300742c00804240d82ca141d090030f0207139035484103030094649842a240400290078010140c0f003031240c1d90307890170180704000055046481012240c103c042d00d0b10741d1907000800300c44003401854003900c4983d0002030401d01034081c40000803901d222071074a2404250039942016270301034050354851400e8203582d00b08c5c07004002c024002d50140450350214906142c501e0710b4212030340d100d0442400c040380010041188030100380152100c0000c000325005c16149814a907006a411007083c09024190400915914 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 538495458 1250 538494208 538494223
    0xf230105010e0108010e0c0918010b09040b1c17091906022103010b07020414041b060c2f061902162108160b010905010e19150504020309 60
    0x76030760014008000b000440d2001020710901c1c002c8034041c1c0215043c1e80b9051302514941c3e20203040200e100c290110400040c4e038081e4052014a42c00151321841c0b820140a90041c0a0003928031040442105043d01000c400261000e81058000c1010706210071b0300038110b0b19400d03002004448180901c125510b0348444070700c11440588140d0006005c0c1c0100c201020071003540b4440e410b41160329092118506600c814012a40690780320300d840b4581244a040ca0b005238025403d1001c45810f90000b4400c5098540151052090074140d800001d0003c1c440c04040180105950f410440080e0007003441d038542d0413140b5800017011481100d080340700ca048010401e003560172a02c0004400f051038a02000074010601800700b04031001201e0703c0481c181c044818410344089180c080c409005147c40d0381440c4080387c011014400404c07081c0024041c0501500b081e08050485007802c110420b003d11503551814881e50b00e030760b00c020319280003502280040201500030f640e00d1401c0c03904503480741c02 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 538496708 1250 538495458 538495469
    0x1801020409061d060a030f032003030402030708031309020711120a060b0d0b0c0711032d3009090403121508030a1b020406060f090915090f2301 63
    0x425208070000f050031520305004240140c0118850741c11500c41d443c0034680800c05406100c20740ca441c61f0b14185000c035030704001404001864690400e0320400d07084c004e040c2c3c40004594400d000075105480d0000d05503084403c000b50050b501c20301032400d1000c1300c25006400d0b83c01001c040c614106540007190403400e10f8418601005502080401c200250f0340c00b01c000380003900c00070001b0382900d06800040000764010481120001804000245400b50704a06143d0142e400c1501d250311002c00001c14400c02084805800c500709401e00d040900d81070f841e6024111011121441c015a00d541c08681d103001000c0c1c8a82c1d1145082d04001e0220014400340c01501841d2503503c0c201ca40f00e4104040903648040c002d50314000b44140203d961501d00e5244c42803144080c0c07611001a03407548240d8000300085d499410012025080c040c4c030321250395000991440c1002007100c03c41100c20940408d44500e200c00007071030100f400c890f00080c4000c2e20024503039180e10280404050300c03a0300e607604851 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 538497958 1250 538496708 538496729
    0x1090614100f080a0f0f0b01141e03030d15030510050f0901020304020906090615030f180625050d09050c0306150904111f0e03010605060c030909180102040906 70
    0x40e0340d9200c070303800040710f03101d10f45540e00b00440180c0024005615035040034015208540800e1007038a400ba40e41030280d00074107451801c06144d4005060035071101d80c0c0400101c0380c0b4814001c0300740200781c580c803d80c05440341065444100410351110010504090b5412000b00c440c0842d55507905002888181c81402018191070005240c64105000300c9125990140c404519900d401c42402200e41e03024005039801000758101c114041e46060103503120b8050390110209030f041500c40d1424185420003c48a05c1c0c2028040180030784c03002480e05884510900710110074509004115114000c20000144480c28004690280540060307041202d0004800b9640c035601e55011480e94090345200c4580c2100010002070041420641c94080403c0050158961140c14983d440c3c844032080502d4008600c5030b030064a41420700f48a200050541034842610304089100159030364054074103000e104408100c0094a9244c0c80790040304012001d20003035441d2525100d4410103072400d800b8207405070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 538499208 1250 538497958 538497991
    0x31501081b0a1214010204120614010918120207090608030702090a06051516060c080a0e0303010b04170a020301021629130303020f0307080103021009060e01050a0201090614 76
    0x1450104030b41e034100c030100682000d5a104507940c4514600c1c400e204865035550a000004450090001417102c4a00c902d0000602160355510440d01e000181c05c2411401c0c54070003c0020485c60301e40000340c05411152107006d0b251826005c9180200704d4201c0e19501d410182c0000b19400c000024191651007100d5502090340d03000700000c211066032140e660702c04508252442c0c0c40200d03000414124240700100c0b062681d035030702c8080a40c0c140f280140000f40d00c00301001051100741c4a00000b010240c00079600e1035141416031502800745000707862410004000300800c54000300185040700c0c0d070190080d5165515548000440240c0f110282c540340000c3c02103000b0040314141c0c591181550102084540d114420f10100802000c407044050560070005c0030150b0b09250b02462040c62107541e00080c560440c410b11140d91100c0807a40c003407101c0c1700c805121031600880d44241140d000c0c80e080c2e031218a071500807400346c0049a0040d043e245010003600001a800101d54800d0802a4041e03a02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 538500458 1250 538499208 538499263
    0xc0f030c0510140306060702120a080717030402010c08220b041e030203070311030313091505060a0e010f05071515060918050c040302030610090c02010911090603150108 74
    0x1180c80d2243d509141403410000035100d4a80035001e44001c50000e0440c1c00e01c11005900e541c40d00121078030a5400f843d0210f204000c002c5400304000540c0c10620201e400c504150740040e2070320400c5d0030021b103a0040807a0060300b0041c4a01988004654a00010500ca03a01d2165071400e500034003030f103c9010310b80030510b101c40c0b2030b2000c200b003100d5015000b8403245165807500400a80da200e03400394075001c100300340030341320041c90010800741004510020303988242e01800482664140d0240303020717800c240019071680e5040304009410003020b0030200121030466100304c038548240304000304048425140e900f01c80300e0b15441400098110450141e031a030702ea0360156983c6140380326441c03c20410725511010b044441d00640d4000748400f04c0141815100e500284c102401260070409022a00030300b08610b459500a4400980840c00204a40303802e5403100c80c1d16415002a46010b90307101e03804500d098400304202c0c010010f02c50003036030301561250000d42e11b8004249210394200c00da07454001c41d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 538501708 1250 538500458 538500467
    0xf0f05100b03120f04150e0102010c03050118270f060b030604230705100f020c09160e18160e090f010608150a1d090d0206130c0f030c0510 61
    0xc1c6100050060581c0e508071521030080e503101d26140f2610810601000500007650b44d0b880b24444c0f41c50300c034030091a6a01000a0031612003410050425040ca00100040406219605a0716003895008500d0f61201a010a03400e0207100c0c45075000ca0707104101809200041e044490440d201da2414000c0d10090320415607524810b440250141d00283d0020032803240e51941c150a2030301c0c04050304c0318580c0d18800104034504046001c000701d8403000c00910100c0c1d051201d415040412600300100c2e051910300540c030080f07540005c90501c02c60010502031692075a04100d0031541c066074269003031810440c4800c10070820110307603001c59004640e21005240c41003d403449410280d0b600191a03203020022940e04401800b10100658607691441050316414401d1000e44800c01d24203031030f8440f1020340c0e070003d0030040c030418094020f010300a20040e8045030040d004110030000c4907000126050540d460f101c035504c21004441d500c0000820007030002d10180403200103c42c40d00070343d5400784d030564 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 538502958 1250 538501708 538501721
    0x40b06070b070c050c06120a15031112070f03120f03091e08130602072d03020d031106270f070e070201060b030a020c160617060d0f0f0510 61
    0x80c07060034514002510385208465100101d8000d004484000d880b180200329198081d00c6118240a1450300304068190701d0701611504481e9140046031951568a50740248440ea00841d8450306c1140000e030840d120401c0548060429a50390104295a0785400c800f0100034202c0c120110b000010043d01281c000e00c909070005400104019044504500d001030310300b40003204031744000051155060075030b50b40302c0c0300b03003c3c1c24260018540c01e4184040f8001704180c6515289003501002c206c1280205000c0b24502100e40c10b071100858640c0c00d203800d513a000403001d03040390540324180821001c1900241c42402c0c0480548243e41c038200754030341940d1556590302d0100100d9004031802c0140c1e400158907554840854400081e840d500c40c005d200b0150f0040d1016110b0741d8002c10b0b4414019000c0c0114100840fa0340441c08027285412406080340e0010030b040c040d0b0840b03110000708079846074a01280c01a6101d140410308040301e260800980c0f01c403080699452050040c030a400081d948501c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 538504208 1250 538502958 538502963
    0xc0406090902070c150305040c0b07080708030a020f0a090905010b03040f030c080c100b090106050304050d0c03030207020d0501050a1103060a0b0304052506030c02120d020702030a02100905040b0607 87
    0x20008107080034a000065402501c044034102c4114a000034010b07100440c3c40714102540c0e60100b0141458140503070746c0011500031003502441000790200141c418412600019403051489450b039982c001c100000b80145103440861b07000004084514640c40280e420a40d5440324003084540d0320f600e418039040c04100c0e401030203410524848408039004600b01000c140c4544a80c0c2d144c040d41c080c102c2d052802c0461030b82809030b03d9014020451418540c500e01410081c40e0007415440d050b120305583d0600f50310014103114001c0607207420f140c401d40444441540180040300c10003000d1400c00d00070402203448010107071400186400c040c000d002213a0003444002c204c00211400c094040d0310340d6001030421078951090001000504080880c401c0c000c00f429901c0b001142d00d001c101805480d002074410046401032900300700920010741c02c1c2e81e500c0305541001a00e413140b80c400b180c5030608510001e91300040800d234486510744d01404070b8055075001d8500b40908903603a0705202e0140107410f0b00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 538505458 1250 538504208 538504217
    0xb070b09010c02160905060f1507021201020a300504080a300c0905090c27010f0c030c05071e080705100305100e090303040b01061107091e05010b0c01050c0406 70
    0x402540806401c02900140000d040d508c1300c860800000d02ca40c2142c6441904c83c95001c107140d015440c02e1180c541c02582400001d5280400101e80180040c507050305890800d01c0d40d1080c440ca90780c50000d03800c0400e98820041050303081c00e040010b0182c000240a00004142aa03682003151494a07249080d900c0301070071810b4902d8040c0d80c00050b2940080301020000c0e035540018141c3c3e00c040d0300500600c014000e043d078910840e10800c9140390341c80340c214815800c040740f100315030b40e10800b02e001400c040d181100102c4090f10f4101c0e142c98501a000d841031141a80120f10020b03100304050300460805d600c5810660b035000015200c010501c41c1550050702d94000e03410740380c0030741c000e1a80702407100d9410104c580c03181011402400180d4450381d00354004003c11040050039001c070790150600d81052107404101c3c00c466556810280929030520391a00a00c04040c0480c01c4e5061010394a42400d0040d513840c1c1002e07150a42041d4007004c0c0c19802d02000c0b40c031501e100421070342500c0b01ca583c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 538506708 1250 538505458 538505503
    0x60c120311070f142109040b060d1b020606031f050702030c0601030c0303093201030b120321071d130207030e0a090605010c110a0b070b09010c02 64
    0x409800600758040e1103800710070104040e600140502e1203a00c1458428040c05030550103a203001890300340e8000d96041ca1140ca4042c03070135200c8500301550082802124045107442403031001c9483d50045003000c0561504102180380d1310f001c2c010560105e0490f030f40c08c5071455a42c071000c2558842ca840440139030f84140c80100c0384200c0342500800e5109403a401100d252003180710f8498030f041000da1094807506104603042c0b0070103512440050081030017100070303103074032140342c03e00c0241d01c01148082c16038080724860f48100783d00a400c0640c180500a0403812120090007015803660701c9000d0345249100000350419080c035035100300700e010b8042a900d8000c8450210b40c002c02c140d01c480612075000c44039071001d03110411207000400805209650f90008140c2c40ba051102000194200000140c24140309000c0382e41c2c02021211a01d82012110b000121108042101110079030000d500a0030001156000d00002105030b50081c0010402000703c2400311004070788401c0090240e0050468140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 538507958 1250 538506708 538506743
    0x3120a0305100506040b0c0105100e0109050a090c08010603020103050a021206060307020a1b03060c020f0318040b3c0108060103020f221a040b04051908030a020c0a060c 74
    0x140407540c02110b107014906155114000145503401590004818103400102858240c07070a004064016040c0c074000b2042c1c500300580900d04100501076540d5503607035200041c2d00380000b604401849a0010301c244040f984403e41c1c2800b030003d50000ba030100b401d00f808502c00681d10f10807260707000100c0071072664545510003004007591001d8183e0045208010240340403480040c0401d400300441000c0c140d65514518081040e070300007548040654010300d030042e112003c00f100722180f8842c1c1d0381458042844600c0040d00502021142940000d507505103540400040c0c812000008450040ea54032500758155000a158035680c1d101e0003d219880843c6603540a030300035050490b5404945410810130107000722159400e0030000d0360661100000b000b8100d0300c400c0c00c003450050352440e240b40c1401c00c280044148540c2c46000d01910144ca100001000074100b02800b070b04030941580d903902d0340c91800a50718060015414401c0b54841c000048032030040d41308509142c0e00c1031084201d400c088 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 538509208 1250 538507958 538507961
    0xc03110310050921030411190b07050a02040b031612060b19051207320d060203011e051c0303060521010506010903080d0b01051b030307020c03120a03 66
    0x418005405100344800316014071054003800c0c2c40f606855008204008040c068000915189015020a244100180b00c0481d000d0f08050103120310583d044400d9140520241400b00a194021081000e012854900b0000f0209070101a02e00131075003030060902d8003003019110000200391716240600c8010070014009071031490b41d5007601804000070f800c6001c6010031a031a150f03485032010200704c000e052019207071a009801c4400d10b2080240b1403c0e09154030149030540c80100e8050040c01c0c00e50b6a036461815032620343d920b40300600300f54404070151070504e020f50400c3c026040680303a031010108107500040400000c0750341c02003012a80c2c20104000e1210310006510580400d62644070201d00c540b10302c4001c0c98089640503480070021000000340d821110042c1510303040001036036003000403951749020b9805001c0ca4040014010008400594803841070f103110441240c1c0c100d00240c00108007101a40c4684215020385a4aa01440070551603009409236042410400d01008294a109 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 538510458 1250 538509208 538509233
    0xc030420150409061419030f08091005030a11041202090c0c010e030c0c06120612101b08011409040803070302040f0b0a0e1801090c0507020d06150e010501080a05150d0b0709060c0c03 80
    0x4d001080c98417410601203841c4022f1800c0d540d001c1030000051291522151040d0204801c44030403040c1014203003406082d01d413549440c0a4400c958100218034640601011a4040d0035224020044258040036940e101d802032035103101c40340110365031005103042280455a0080310721b018005155a60010013210054420a82e0a01d115030100000c0b00d00041c424540c0d81e152698281c0d21615089600a1540c00140c101080c0348103450f0b414003d40e02c4201420b5005a848102540c40b0b0755501c10803402800380340d03c0207a4142443d000050400c070000d00078030041c003407640d070422181808014869030798089100008041d09200041014403038a83c8101c11100151401c1898002c1d00d40008005c400d0065094400c2552000c03890922840d00301c60b600105055100039032a9850100007900e4460000c0044101039200c0300028080c07410450840c0d09044010041c03210701e140c1c2d007000252038904451030b00100d00c06c0c000c007081103800713074805122007580016071940c5641550b8480001006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 538511708 1250 538510458 538510463
    0x2030f120403020f010f0621020d02120a0506042f0d200604240804112b1406010602010603080405060c0111071a0c030420150409061419030f 62
    0x40301c06603034044000307001b0741c011180616408100b25081400f01100660000004200303503002d04100801070311040130401d655501240e143c1ca01401c0c9805081c10031061040082003402550100000c000c1c05990f01e0300803140d940740b00c800707517403040c400c0030420b04005940c0356002c2507240c09074000400b109201c03846a000c01070061322180880b80854076980023034000c0c40320184124100308405134810b820281e15402890110031030b0a05465501c410720005003464051503030402c14220200200044a0b0080c1c80000c0d200d130000c11600703024500207002c83d0401401e005540000462900c1406540300350381e0410f441c1840e103440d180401109a004030303481815075484020950700c4c2080400903100d5103004031004819070016070380210b0842801084903071040c60500038840441c0ca00944441c2c8840ca81d0304540304004880c0014070012651500c220000c04002000b1580d0300f00ba810075422185442c8203101c18446030010400f0308490340740124844440114200003254201580001d111b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 538512958 1250 538511708 538511713
    0xf0108061801021e040513110412060b0913140c010918180c0f12110d03022a0405011a0304080a0c060603061a01030b03030301090b040b1002010c0f02030f12040302 72
    0x6a0ba4403442c8070504003007440c0c4010510208003045641843c0014001e401d844900403c030744608c041d4201d0450289004882002e078004144804122403648284a550002000c809980c5405145c80e907010302011006c64240c822030b03d01808050000610052000c0c058450580c910704083c000c07800c0b0103601404170700c1b458880000ca20755403814290040c03010300413428410520300703004140b401c81d074065002c04040703010a004c1c1804101035841388040f60600325881d58925455040c00c91170311038810040701c0c006006d40841d924040c01880803061410050310203004030ba0340c5581020b4517002d4a603000c100d031341c000c100040008501c6001815094003c0c1841903d43c0072030f0300c81c0011900d458004075002941c99840c034080900d0401040b03201d0109180c00c0c03050000b410082031300c030f0006100d4008010384038080340390140d407203400c0041400320180462002041c001002806480384051000204000c6c403510b1695510201c00c8451030109041194a804140f40d9620061400104242c0450 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 538514208 1250 538512958 538512967
    0x904151d060a24030305090a0b0901050f0c0c0315011e0e040b060d0f05031b0d02070314010603060e030409111303030807050d14010f08010605010210091103160e0f010806180102 78
    0x10300040f20f010010314004e83e12691210640310034408810201d030009018564144807181e001e03a4880111501801d0340c0160715111b9804018040c54942c010300da140d494010800c0700a0303043c0c1c102500c28100c038421042c50224103281802d0340c100300301501800400c40340c140c0014001c40c1c004c2038001d40004000c1c106104900c2151102e01d241104184112102d0300000b6201500f1020342c081e60041c80488009040301400885d40a0b6440c203091200a25100320100703121100c200a600c100011a0490028044210490001c035244d0b40a40501c859184c07030142d114264262030810345075407441d90121a150181551425100c0034001800071040280412030f8a1400825011706101c400550383d46580c20350401c020010402003507000b0344120b81c5400c03030401081e070b0300041c080064180320b200010207050700c0c02c0600d8202d41745914076825100740c0c05400041403d042e402400ca50100403050743c192619042c41140c950b00b846084410340c000d10204a040c14440a1150307401d5680c400103181 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 538515458 1250 538514208 538514261
    0x60e0c03070905070206011a120702010204090c05210c030c03090307060207061d0f0a08181903110118050423181504030f080a02090904151d060a 64
    0x1460401e4002c10710007038455060044107038040003241e014052044950040300d506031130030203c500540003842100d9001c03201058009000307504542c06411000380501c0350b4038091401500580c00f0b450391000c58010780d0303100b500141c191200103020b50103886003240741da210701425030b40540020749210740d0380c0000c00c17002c40014243c0c0700900820b44074a5010504442001c440c0090444d0880c2d2200c06400864400f90103480104969418130350000449445400c024030000b645643c00b84c07503903040781e118000341e00b18811507100042164480d14885c90382c00007000044800c001c0503054206030b0b0300e00039404d01051600350041d507101d2060701c2c00801141c0c04100c04040c0c020b400d442d04130031092b0022041005840070300c41c0350b21010300d1070808400e901713060384c0081010291610000402240380d001c1142098141c045514086000b0100419402c203810301341c50802070a000b29954078584002107583d03214040c00d00c00e1117a605405000e00359104512138029240b080d44903150b05602000c0c4017030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 538516708 1250 538515458 538515463
    0xf01032901090e1605030309120a020603042a080304050d1505010b03090f0c0a0911070b010305030a0e031c0503181b040e062809080c010b0a0504020a0c060e0c03 71
    0x700796040021460380c5606000b0b07030400601030390740d40d4522213000b0b051249480c004200c0304c0e151016143c4014038060445141d0602190b08030083d8000000002d03c8140507d0038280303003411840c25030403400400240750051020600d0b00c2100300d19042440101724074075140340c50303030401402115100701c180184240031003191007d030090b400828011040c450520010001c42c80e8120b00f20008254100499001440359072140c400d03001180d4481c0f04c141c800701c600c41c00307841403968081028602c658681c80d0098603500030b203913800300140c6070606108807440d00090900e034100c3c0710078034543c030604114400c8a0320384c001044021103c3c15004c009684030701c100900c0421280200f03510503150044420007054400990303403400550710400500410108084004443c2c42a200e0844d010303e4858040e180500801d07900a4400d03000030905003107480c03040d0042c03078204c07808462100d151074942d410003049004d28000640020300c05800900018800d52000500004250480710b000310401c00091 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 538517958 1250 538516708 538516711
    0x518030105090f0606180408090105070b0405060403030510032118060503090c06070b1302010e1c03020f0f15101703070605060a12020f040e1204030201170f010329 72
    0xc200f94805180a80320318018041c140e00b0960880780d002c52188048204009131002400c082d00c8104009003044144e0301500484d082e15507c584004040d241c682132082e11088c2c111803e902081c201000585d0803150b61214400380c991091050300a0b405000510502560101d981d45c107109029524003100458044500014495643e4050352880e000c22054108182d00c12110b0040005101d91400a10007003e501ea00c0007511108007031078031090004039694826200040d030040d4031200c4511015454035544494140240c084a41090803c0c03000c0d983d0f00551540300c015500054041a106920603610135080031000c0e000b103200d035072542c10040b088803201c0043c400a5100042581c03c0082501545d90700040403540a0b8010f0b1030b1101350300c00e61540020003442803d034146021219a120b90112109100c0c0e50226507003194014442c0c42d05601600041e0f01060b042ea01341d8411030700c25151140b040c000c0c40340d80303161640313580e40c1d00101d0442e81020300703a42100440700c84454090700e02d01a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 538519208 1250 538517958 538517971
    0x60f0d1203270c0e010b0f16062a080907140307031a181609020a0c0501050709060e040b0a03030810030519060c08040b07050c0c090a150f14010518030105 68
    0x3242c0034640d40c60801c140244a0384101d1210407003100400040191200740c2d00500c05425800782ea6420541d1040c407001d02104000300614541000c0351440c2e00009211004240d056081520215504000f5290101d0803500c07010903a20204050148c0c00304401c00000b02407003d8215a161622941c4030342c110ad40e2050001403500c141d60410010794184091440d0350b044600c05000c115103d20402c01c82c1400e68095014065000541c03010402d100b500e00d124120303086002013125003841d00700140b45606510454000505180c800329003031815105080740c240e401044469094907554003600e40100041c90f005062409200000114805000d650b0201d4240e00856100d5025460504200e802c150045000c000c8005c0400c0006400a80d9a40d0480148d0625075265003001a40c5031800300c0061031142c2021084041c0000380d040d030381111a06034102d00000081e151200350401050300b044c483c2c0c007000ca100300e0040c8043d50140005295800303940102040d00d20744400071a003560b8056442 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 538520458 1250 538519208 538519271
    0x7021509040e06151f09140a090c020f010f11090405040f0503070c080d030908030612010e250e07021b0409060e060714090f01120e0d08040506060f0d1203 68
    0xb0501500d811030700482c172170001486a08015644c8078008080d806103000f500c81d0301d246140b010300141c3d1103217012002040c2051040c0300c040c0e102100292606000c100742c03641d070f42c01c110040380d030841203000321300c02e40b02d002c0030b800c0c01c190f869010400a0400503105035082c20301114680e011800910007081080d01031030717298212a01c2c04580902d017150010300f0b00b0405140c100740300700140100701120707000b4004880081319101030305010750040c110840c642c040c074811201d8640384071207455100040c1540f02290f1111040d85d6140103020040125503040058003c6440c201d06601a59240308801d28083c0000920018030340c0c803801101c810400740080759000740c04200311154440340e04200f03406c0c101812400c00409801092400c00b204c039185045c00090030420914840307541c0901041071654044995005c140b080203400000240c03010b0300c0314040d0000190440c20728903461451510043c01000d407410803a02d40501141781c2d20150010103031a08184808811412070040030240c0301d214 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 538521708 1250 538520458 538520491
    0x810031e0309080d0c1101021c031a030706090302060703030902030102030a0203150409020915060c031801110106030b071d040609050613050f2802040b0406090b07021509040e06 78
    0x4002e4001103481d4400740896004001a0001641c0140440142513010141680880002d00140e0800b60380000840b1003040c114000c809255050304440f0b003152500e0900103800942001b450740b5840c090140038045401204204010308140006040103030092400061140301d41d4001303802d9034000d45050b800c0c150040b0610480e0a050f1840c0030000102311000c0080e82240d2303000ca00480e40c020454000d407612041e00f201b1039100c004c1142c0405c030142d0196a924601030401000c41504034883c1800500950088008040305124102c1030720b4020380f41d80840e64070b00c001200e20008036000d0100314000c1d600c80107225222030060801030000d82d080802d29242c098280070544041c01c203012100c41c148818014504c481c51612038010700d0101c44002c440400303502d0700c00a2414803405920700343c40002e00003250404800a8829901195540031425a07585010031035409007140c0650302810481c0c01400342c41740c0b4801425550005080498622030011400341403d0040713503d940e80301c04801 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 538522958 1250 538521708 538521713
    0x70308040c090e0a080307020c030105130c0e012d030204181103010204034e08010609150f0e030d050d0c0908060411180a0e0c01030b030c010810031e 66
    0x2001000ba1000c41e0041210b5265919496540c10004401412141000002c60f03940c520034010580001c0001d00248070030308000541d20105ea00b48802036582c61801c20010400301c1d0880d44040c100c5064201c1c9400000010b011041c148600c40c0101c0b64194804400100503225801a0707900f0200010a0b0741a0510a0809800070410003040c140300784d20400c001c0c400182403408094040020705044101403c1520055000303807140982115101d1041c0580d642c0d004200c041ca0300034406907a5401c12030390780c5070026110300485000320b0002080c12546885480e10510020340d0100451a10001703140165002c2410000d80c40103d80000348002001d01d01c0e003100c0e000d1942c0a20b00751030103000306841e19460684512010f44003d01e06460380345002025520485401d600000a91200700d460070485880b500514a00c180580c0600540143c0c0301158040c1c801c0d90590a03014001d0801065501d00456061030000c0c004100000c9001c008008200300050304440802c2c40c604110f0b9800030350 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 538524208 1250 538522958 538522973
    0x302010c0e0102010216110a0306140106021020130f14150f04050d050f0d17090703020a06050a02011116020321070605190f0c1d06120c0d0207030804 66
    0x1441d2490540e030041108002068001004124003034114a03003442c1c0e83e2054000658139039a84d840944400d04202210075034401d501c0c1e44504843c1c1c1502101d8244000040d09070580381050101503004440800303401011515130300401c1210410399025801c2c81e1640044001040d09412064150105101001e8241041043c10100a0040109a05102d5012450020351040d8028207002d031007001242820850100301e10900072800c0c109403030b02069003603001082d2407010499002d41010500100d96190400318040f000d0b240c0107001c0d100241d08101c030132740d01c80d40085e07650421907590320008410010036801911410961520348040e450250042618020b42d0305110380c040040325a03001d50701801101111203903940068007080503515101c54254804825401038401801c00d4103100034000240d02240c034806003510b900d801e1240d0040019400c4005542081d0007100c100302a846c05080c1503c85a0f218142094043c58454290492800d90b041168224082130050080c8810407512 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 538525458 1250 538524208 538524227
    0x160b0709060305100b090a08030301090f050f0402030714060c06010f0504050115210f021206030f03072a080f0f0106170c0108071211030415020f0a0323040302010c 72
    0x562030140100e04142004c1d001c4980c403481010382c0f680300001c4901081d01d6100e83c100003001d030401641d48969503480407070090809440d11400052500c130014084981d80c43d0301c02d00881d006070040c4009818159142900307100091410740c081c0b410300c995002400e013000980e000c0e204038450341001e28a404184419194103170401001801124500d60440344d004031180342800a20440d003070222001500c210003480700c01641c1e200640000350180c06040e01000440c00b840041d81124050074040d001d0b81d482e40100680207201c08140031002ca8480b000b000030308603404094424448941c0d0360200d1a00e4908480000340c40d640000326103040201c4203120b040010308086901c04100d110014011f51074595032200f480c1400f10010210b4905442a1038480341d05480c0c80301001000f400015085164104903400c60303581c0c03640c1030254510810b80c02618094000c400c4014101100a401900035003040340c841130142d444021910070090360041c0b4203005501a8000080d881040310004051800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 538526708 1250 538525458 538525469
    0x30d020a050111032a070c06110c060901050a030b0411030405100e070e072304060c05011a0f09090a0501090602180f131805030f0406080f1308090303160b0709 70
    0x814410426180380c501c0d006040201600100d10551760310b0b0800c4201c0d40205480a010103040650115403a80c1120a461600d49550222440741e1950000c00080e40f142181290000d8004e01c40c60b404980030360002c4900c5400100301044402c0303101c0505143ea041154251100ea110520b4001c400001d449440c04000201000d08043d0b0304000c40d10544078000340c4100b04014810f4180035200001103c1c1c10b01c0d00da4402c440555407680c40000a0240304080003c0d6003e52070100355246010f01d041c0d0441c00040b0252000e80e003824040108110312074000c3c11221360f401406000e20000340c080c414201194400c000040c0c4412082c29502203104004507424021920218003001c039a440f0918141300b60f0601c1804034140c11021007180c2004030040d801807152102140c0b0030032034500240588207a90312560b500146980d08020580314400c25103449007203082048001001ca1603c500602c1591009000c8928240003050a8071550301c110038252000c45807142440103083d80840308000406 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 538527958 1250 538526708 538526741
    0xe0c070209070c020414070908010f02045f01020f0604020603100518011419030b0c04050612010f060e0306060d0f02090a0b01080a020708190905030d020a0501 70
    0x440a6000c12450540901240d0501070410070040131541c0d20303004403e1180341c59280210500b00350070058001e0319140190708080d424004410012800e0344255000c4554240c000407014110000c10100e0b40d83c00c40c2d207400c0090844500458012007450342d503003440d4066003c403079140440d10300b00d0070f0000410051030441d0010214054500c0b0000392081c0c11980403a00c00c0d60301c0d210b02d441196608840d60149811a40e50000c21501071701010656040b110b80c18041c0095003c1c610800084c100000310040454007108030900100c1c440103402036010f0007801e606803034280c5540c006109900036480401c8040b8800d0014845022070000480c0100b601d4105181d0131001d0f500020780700c5c14010000c902071610007031940c003402484100b021040c1d40240a42456052005e5101d000d40700c0c5895950102d100000410384190080c0700702e0b0100d0380c01c41510390814420302840066281c0304440c074002c00544c1c08000c03426075018070007074000b106260020042c008031072a200f401d40380500c400c040f045 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 538529208 1250 538527958 538527967
    0x6030f0506011215120303090c05191719060c09140a1a0405150d06060819201305240f0307050c010c170a060b0a030c170705040e0c 58
    0x166044280f8203208014200003258080a840b11342d0300d204000c3e405605802c00912070702d4141070305940651242401002c1170504a5114428490300b010291425000728904d404108010f08000543d0302d110030295090b196100c160040911080309020800e0350040d0b6160802e0141c15003000c41c10713004090300c400d45d09101e00b21400007495a030f030320310503c1e4a211001c07102c500024000d90494010b820018200504e51510605087d1150815003034184910324003403001c900e0500a0b00e0351489880304500c075031420601300a455000d00715440f42d0b002441950306454848211450103441006250780c4003045040c40c0204101c0c29600104410b0b0080c0e000702c4030b42e10840840001ca03800314004418080e9a9200c4c92400c90340b500c5601c817541c9041d46040004002e850b030241150003807aa50340380449158445100c0803080301d0482c491041c005004004290307000c0c2c0030340c000b0901400f5600344000301d5000941c01c0948104121036040c00500300203800d210307000000c0300030740d0003200c10750106003070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 538530458 1250 538529208 538529221
    0x405100506030a0c0302130f0f060c170c0a0210020d12020c0d111203040f1a060108060423010e0f1e060f0f040f0b12010209090103020904260406030f05 67
    0x31884040d0082036070030388800d422204c0328043e070111051408000490810582e8540c0c40d0f22200d40140940c01900a002c440010554852070180c2c0b055a00400c00120503507901e840c00040713612050408006000303085045000da600d80307410101414640d009814940c00d90342008094041580d10911428814040d00041140010b480b0540c61400d08040600c503110000c00c038604100c0300c90000c41c45000000300b108204058100350b00e101c0c8118a1080070204601c44101d0051044569030b00280d94500041c0861401d50020203240342d80d01c4d80800603120320224890008001d0300b0000c003100d090800e00991801d030600165100111a00c5001c0c1d141038489030b42095900a000340d481940d0000d80c8610030783d5070440d5141800c5c2c2c0100104020740e148141400900b04240113184a10b0070303d40e072000400418001c644035200010490b0358640c3c25070342080303507221000d80150b41149400101d40c071010a904c00250b40c4900c0d0104040d10780d4607181004050740c0c04020491905400d040a1101 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 538531708 1250 538530458 538530469
    0x603010603030519180f1509030f150b1206150a03020303040306201b0706091401050304050a020a0e090d030c140d0e030d02091903170d0b091504051005 67
    0x8042c01d06080704c07030000b40241003100c103885500e10556560b15010320000e000c0e555921000203c9400e25442101d03d400b0f00025624550207103c0a010842e0000c540000940c40e40c81e590002c0750000d000003400155200400c8515009400280b1140d1019042c0492800458001c0c1000303881118194055801d65000c80d840317010303505c80144102c1d1030394540202c51407040c2220003030740404119292104056a99424141d001c002d036003596000e88400031414074802c14000d82625480c10300d1404000d40d690044500d5840248152100d000c1e14261000580d0b659604000502c40da03111203c0d82c5c00c00c1c0c04211b0500840c0f6403408185440c01400d100c01c1034004c800c0700501d840a0040d2900d46410380b04030350103840820560a80c6000000d9082020642c40d0302a00025501350b46000210040c00c450401d0f4014034000030301080c41d0740300014a44c5814030010310724150140d8000c0b640e0781c007500204858203000d1311841e07003da940040c020f109080c5403242e540d1100e0720a100e00145032500002c201c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 538532958 1250 538531708 538531717
    0x5010305030a0c1a0a140708060a0b0706060e0906040b090307050a02010e0d020d060e010e122b091208060f210f071e1508011e03060f1406030106030305 67
    0xa110190036a04103100c9800329101201107070203c13841091034824180c60041080b0100d48038810146408101c0043c400c900542c864840a46805070043c01c0400b07024403504098000c4030310303640710700c0c0104070723110740d40e007240c1c003507148440107090340c0c1420310b00a801c0761801405101940d000344848008160000341d034002c21034080c2032402159160390041040b020040d503010b9007041803840725600b000455449100310003100d030b0007007040c400031910b145d4580b50114001d10b03403c0000d0002c00032013075403409031141c04c0ca100360b260a03145003501f10789001d0f144c80040a03100e1240c0300d4a2a00c0660700700b9205580030780d007203900c50703001070b545800144191043c06202051494042000100440420040d07001c29030303640c12100b8540da03c80c0200054512104141407491002c04001801c11688100c040b880101e40c40c2c000303480c1e082940c0441300b0300060100242100460f03000001203440c81c4910404202d00f400d0101d005904841480200349014051038000e80c03416504001095103c000e55 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 538534208 1250 538532958 538532977
    0x30c0503070525051f060f0506070809011e02012003041a041e0506090c04020a021e010b040f020310050306090a030e03010f150e010602030a0f181a0405040501090501030503 76
    0x18078001c20a28041000459410300422034800d050000d520001c8510300121700c424002401d210b09900c0382030f641c008003c5842034a401a40074800d0703000040c2c2c0340f006081c4c2c00c0c0041c58640c00c1840c5508452902007040d4000b140580d540304803a44540d004008807140a24408803600d1841c10240e480780074011204410a884054460101d001c1008980380c0c09850040180f285000340610b05149032905425540f00e001846074088038003484c1001c0c001e440000740b40380c010b407a41540003c1c640d0410b405c20744803d40155a5041402026596403254172074291582800507101c1c03505519004214000f900154843d40c401d0b01000b81c1000001001c4400707a03454640417011068040220703003d000560030354400c180c00e10712421400c0c0b1400603e0360440c0e01c54000c02c603107a680d032001a030b201c0c814021000c3c001103800342138801c0f00b400342800c0702e62407c0034030b68080d1003030f918a00000c4809591110408040d0001020409460140226400340100c0a0100802d5145039201035480c072500000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 538535458 1250 538534208 538534237
    0x1a070905010315050a0803090a050414130503040812030114030a11010513051f02060c0c070501051b01050703061701051e090a1e0b070305040201080103080309010e070312030c05030705 81
    0x4002e090800c286030f54001300805020403201a03103400c64941c4903001005410f0003111100e0300003c2c5440d05011f0f981000c030b000c03524000b950716401d044d4005070b401d030603090380c591100700030009804104019494034000092402c644030b5040c802d0040000c00c0103c1d1711486907010210103008180c8400c442d0540e40406d00703100340e54040700d00d070b10f00e85200c01c0c0d40140e500c808159a1100325035219070b07140303121084581c00c2d11841e903602210521303c0e0048107d4000c1d59072209600384810750103000204840d02000c20610555a00340c00840e00f50b5a040740e400000a407184010040700e0300388001a50089020f0009010700d142510b0354010841502d00006202d0480d000031400d800d40038450030340302c40e400513440c43c225a2000206941c02150000031280144c066001440f0107109200d842c1c081c0d07605035290021a40f0b940c41d00350a9070006010248655624180c940d4250030800100009500c100504070003410001c1c0050100c58035860440e050003401c2080240007a4000100c44503580d03139241 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 538536708 1250 538535458 538535471
    0x8150103060506070c06170c030106030902010c0519031103120a020306061306020a030806040b0d060b060904140906070203032215050c1201140d152003041a0709050103 74
    0x120003624680d0700864012000180716001d001205d036064042e52000c1d00c2d066103800d07056014141c101001c0341d12400586061005002c014800e0b040180114014034003d4000c03d84c1d07440e00740c101600c50403007098503d1700310120800c07d038101c4c2d0801c804207102d101540c28a41441c082481068004107002140c650000c00141641d40d40000e4600c610400d4200c0e0491030784508000e581c45521200640218440900244461030a4069440c00a2029010070b403204020398501000c3c00e004a405984080d050145041d20745491260070314110409c2c52851507403c000003028100103025010000f150400c2003049402c64001510b4142c3c2004e0801c040780046040c241001d40e030a034030400881c1242004144404d050b0460701038107020750003112211007031741e03600d82410140380710684498014628a680b20003080c1c1e0444614240402c440000ca072a060741c0a05000c2000c4000c10030b40e80c0207012003808103003c510000407441190252515169003040c000c050401c81d228894941016203491 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 538537958 1250 538536708 538536751
    0x41e0504020a15050c060a0c1403040c03061b030506100e090a09080d0209040b09090706030e072402060702010b090f18070f06110102131a0c100912050a08 68
    0x50703082c0209005080009402c05107000200154401500c081081c8a00004a03951075081c0c86020001c140030f4586084071000e007404a80103820041081e26085826600003000c43d00501407000401003030b50312041040300c012b00140c1114005041c8900898000c00040359280d0040701d40b10006504444c200303050366400300351401078030703401d00c1c024070400303011032103840c48001600078004001007254107116040902e000e0100045003240d6a071400d5104403020003006000b0f0384880c8600400d0300546410f03588441c003092482e107240c01007400c1c01000005e80364045505200950b0130984030710091051064001c00a14540c2c0041d10003030786844003101249420a02c01c3c020092003400b80d003a64825a07990780c40c16034201c003520400300486d0380410010611032040c402c4614032188980e2a06400c0c0c248030305908982c010707100ea044c003d1010032085540c0350b020090041c290100c4000886c50301d0461400c0d00240c03c021020600340103081c45001d400b160400149548041100c181504250219 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 538539208 1250 538537958 538537969
    0x1a0a0614130608010e0109050f160306030f2a0b090603060d20040c3908072f0603060405061507032604031e03022b0605041e050402 58
    0x12010729241c00740410000803000d40000549040781e289480342d003066a601c1c84020281c2c0c008440b000000c1481b04001034203070070791a180300a04101d911f000554162281d8410021300340700fa43c03c0c3c0d00941001d0f15450801c3c00d000b01502181e030215441003165180c40003e00326800740324942445540088009045074444100c6414065000004100b8042e8091540c0c2c44502c4118052401a8102042d030380542d80121003c0920300e0500d0a04081c240710540b480350b07410240001d030403404890b003015102244400014040340c4d0f004910b82c0b003224054900c41ca182070700416a134000918154185202a41e42a0035645d00850650b800b00d0301d91b6134000014601d40511000340400c4502085807810f140e8400d06c0790410907030014190b20251074450301000c1a8404403001000a0340303404100c1d00c40440d800801c0544031040c03c1c00750508203880c4210307041c011041e5580171881c105160423203c040c918041c2d14002c000545080040d0008240c007408507171203005802c500d00351203002080031903ea4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 538540458 1250 538539208 538539217
    0x1120206090402030c07110402190c142e060308030123100201020715051303050d0e0a061b080609011202030c030a0c060906020d020304060807032d1a0a0614 69
    0x8004565900e0521a05d00340383e001000d007a0744000304c5549006450070580300b220311048602c8200607141c0800182101c41c1e60a4250440300c807208136411445091040100d12010504071480c4400b002801195400e03c01c008900c2c018140c0c01e2a034104040b54102044a0650307401c06041c100c3ca80003524954049148241c03401d8002048800e0400c1c4568198007900481307105501340c0c41c03514030030781c44101524070550743c0c3c6141112448080380080d020304010038062080740c00114808241d61781d03903401e12040c44416500540c80701c4440450005407500781c181400203050a401c20b050060119006034014056100c01100a104400c2955402c10003855200d2005085401c1d42da114903117521110854821040070030395003407010401c1d90000c1851085411254000c2d0700307251038448101d074800070261441d0289542c070f19440603180d100e40e012080300c02039500c001075130784600c00965003240e01440310410136281c0d6018250041d5180b030922011502c1c00e14080040304010805000c2030b226 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 538541708 1250 538540458 538540477
    0xf03020c1203011a04140d1e080409050901020a0f050c070803180411040803032d07020604050c0a050a120c17070306050c030c030403140405031005011509030b01120206 74
    0x1d20150385441100d6000254162500010801c040810051002c640c0d07000d40d000d410150740b10f0044030021402c000030080100741c02880c01c0e103000000d11800c01d0250740060015141c0348400039040c400354210b809002d401c2000c90008601d00280690028013820b40403091208101d0005401c010950003045800013501d81a810349540300d0034021610000000010718601407405d1a40d003042120407601a07400300c034802c04c003442c03466448500711003e0540304c0c07084800c400701c20b100000005100468080c420121600142a142002d003006403502d00703002c0c090b620400384154188110303291798505104852040e01a00b800e10488c1c0b8061060400301d40080255800c42007001c0c5544000103082000c9a000b50002c01907500d4a000701d2025110840d2004940340c8c0c100701060000c0e108901c241b04910380002c0d582e00302901c030400242003116690203040400d880c1e00062052424000d4403005a000c2410b02a040515550b1900780031001403150780c4c02c484994480c01c1c01d41d01c030358044030f13108803 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 538542958 1250 538541708 538541713
    0x60c08040f12032310050108040b1302180c07060b1507170903010903021c03110403020907090323010b0901030302061f050604030c090f110328090f0524070f03020c 72
    0x4801d41001050441c04485d11546625041000591540150030007402160010103d002c540c0e02c00705a403c060006aa04036000b1010042e0301d81d4114001c0c4c00340d4083d05d0381d1141a5074800321804c244058849507c4101d105010580905000464030011038101950208001b0a15900c521100c0c10703a02075000c202e90036500b4001c6190805a0109250b0304031507400c00740c411400400d180840898038040d005042c029410401030005d0f245c4050050751003100b6282900301942c0303036542c0e649400076011100390180020125000241003e0180040744002070f070340b00c017041d0314684009540310300c0546000c1741c1040454985a0340c0051111110261a01070002e2781d0b1a50b880c50b010b030781412244250340e0424680a412500c1420301d0190400700000e89a01074290b481e03c0b0743e11468008081c41400200802222510b00d0081a00030304090034095a12450b004001d07092080c1850541b4140c298000a0710300748070300d4503080d0309442d038000c24103151240e004401040254020301c9080c00c0b0720042d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 538544208 1250 538542958 538543001
    0x61e0f040603200118060c06090809032a09040f030315030f030c1202010b0a0311041d0106091d0316080c06090d020f0a02031506061201090504060c08040f1203 70
    0x403d490100c80c031000c400c0e80d80440c4201ca401c09280001e425003d4a00000e0540313440e040828101d4024a00441c041e84903a0b1501c0403403400607207440805603110355203c0000c1c45e0000e58040c0d40103000710071a02544c085081740341541d962020f0944200b4000c041c5a510700244003082c81c0c100c04140070310780c888100d0006085030306001d000c0c8621142c0c01c590b01c2d84400b418480c1e0a10602490b1590b070030240c0300c0380c1c4a41c00c0d5500c10001e5484038025030740199644411643c0340181c02c41240c0580544400020303018100880c0400f40c402314011009a0881241a80c040705400402c030b0b041c01c413881d856929a005a0f02c0c149110740701d8504120014444e0005003c1c5080000c42c070007070b460b189a001c603062251400002a10749104c100080c0d4190000b81c807800b261342198400b41e9014a0040c22103240030350a40030070075014800c5c0c0101030015560030810041228601c6154011001424200441d25095598000e0842140c400406003580640402101402900510506140b206c02030a96 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 538545458 1250 538544208 538544243
    0xe01060308041d070903230c040606120c0503010302181009090503091e01050403080c0115080a0b010b0f040302061605060106020d1701030503030c0a022b08061e0f040603 75
    0x4210341c40c0c15428a14001300308800c0c0940c580320300300e03503100c1c07144010003880341c0c004c40c103451824040c40a14002d03200089659a1039102e41805011aa01c5003014200090390040031900305041100c1444003c10042c00947d480c00c1c0600b1043c942d002711209150340f440d64000044103203500c005501c40c05d020282040007000320203400d803c2c00503503e06600800d101111401010b641c40c1a9010400c1004188085150070008220b010f07000d2001281841f4414004502c0d014070354040c12503600f002c400c00e41003000d420b9031580103006a582c00c50810907441007540180c459440028414080000d00d14901d40402d0b1002d00803503040b2090f43d40d40c2da5128030182d00c0d0500c1d0175004d4005241d010224542c3c03031a6010441c144ca40040081d801e680e1445a000a01d40c0050388035025407040b82110366084028140d00c42808544143c0d40310611003044024042782c3c80589003600c94104542e103645400103030f0780c100c0217868080f1340780401d0191210100300200215000038000c440e446081c2c1c2103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 538546708 1250 538545458 538545479
    0x170703080714060c03010305010c0305070f052101060f08070807021c021908130b070c0e070909090521190302031e0c030114090108060609100e090607030606020d0e040e0106030804 79
    0x407030f40038234001e00012814100403001c40d44105c0e01c41000c0b95034400fa0816861051000d003250448155907c002d61411200b0704900800c00d0340154002041d401b1100405031340040540c0d0081040e003410211810481c030040d4507042100c03800168502040d04072640741d4800c0101801003040201c5a445001c824100a0301c55803004c02d0000140294440c002440c01c0300e48202e900e210b0308a200c510980d41068802003544601401c0300f401c004d106400802d5000e801e200380700c0220700c5180148001d4143c8403284040d2a0b4030703038000c540c1280178055074510665148010b4a14405e0780380c010b0342d0399904018200074807141044110b01000150402c04000400c00065059400300900c0f058040150f000700000000240212402500003501186c4c660a02c100141c1d0454840452400c10320b4440002031556841118488020380c0200103200340d02e5014464070015218074405822030300e21000c1c0103010f507549400241c3c003039070381d8410400e50510300b03500100246a0040c04550340d250ba4084014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 538547958 1250 538546708 538546711
    0xc0905100608070504290f131d070c03030b040f0e0313090219030e12210906090d051e031014030606090403050307020c0a060c05010501170703080714060c03 69
    0x4242c071900403c03522409241683e085443d410507640007030750781c005941d500100e60043e80000c49010721203c28901007800103000c2c80024504001c41e0185016100d034a05061500c0540c10301c00e0900c14050309a034440466120541c140c02c021601d068000c0c0800c0090807544001c4448a14000b00350703840400210041112105070b80107000c40301d868941038022440351b480702038030401c105400012420b000781c000c40801d14031417056458810050042e244a9403021010921545200c0750080c061410f03824042d810203034104c0184410b14107000c0242e500d60b5080350320b500788100070504a0700402413161102000c00064280754407801d00a41c110115040350140050180031078600c40001e0400003000c81c400c0f00b00800b2b40485407242d4a040c0c1e40d50b48041c0c02c0c1002c40c02150b5017440700d03032600600c0c0d00c000c1890769030b981103110712414181d01710b40060b000079182c4844286107282e05e2000103250402d80703401c168940e50740c804e6417500d8100400004011040381c00740d0010031201754a110040c6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 538549208 1250 538547958 538547969
    0x1050309070f12151b180e010e070210150512160e2d040b0402010e0901240503010f06260c0307030b0409051522061a0a0b030a090c090510 61
    0x32402c03600100030400990f06031800410b10384006844a410141c1b00300d1040c0d5156109100c000000381e01c43d00d1204070400709801c0110300014103010b00504660400c044100000342090130400c1110408150318046041c0c840c1900c07403584010307917803a4a9402d1000110310140a9070b05d02160b030351211a60601c6004840030300c585010134580c06104c00048445500700d4080d00220b0842d0b40ea680c1d1400740d400d0011304243c2c104840c00303440034102c0d114241114042d0400145002c200100c4088001c846000c01c03801104121041c00100034001114807850255a40350801000c0c410f41c1702d040c14560803c425840c121344100d1000e0110b0003c1003002075000300b02c2640c00748130b911142e01c188429160001e500810340d6205284100382c2280d15948140c0050b0015038800030007c1105030f00399450302c006002d5800710356400000c0c00108081c42e41010307510080d0303210140d0520703181c021b0610303000040a00c9200d98540a8a038204503018412402406551000304407038148112a03241c25503583c00345 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 538550458 1250 538549208 538549223
    0x1e07060b09090d080109050a060305100e0106061b02090a150e071e020c0d03140d0f051005011d010c1707060609020c0c12101409011109090601050309070f12 69
    0x8074480c0c28000ca4010883c03203036900c42c0400d607460303d209100104001032454400d180c0e80c490220000c0c070300307000d03c094058011002160707111503222a1402c40c0c10a13840304050003c04100f100090100700700d0b48507080d80464101c6050307a10348031807201500e442c026910b4a0219014042600e0007441c00c0300780140d10702d9407800618140c4000c1c00d8005d0004091510240e8030032100442d0303914082c0044044a4403a2802c21078403c90346a1065040d0007820552442ca0b84500c0030003203044544c071440781e02002d54903140c51010b14290010703100c096020030080b4600301480c01e28000344d0050000e19121580f00c1000c034a08003607a181d24034030380c200c2c4804540c100c0c10310301c00280b03d003120700139286003c40e03420180c1528214282004400c1c000c405010086010303607180100040b0080c454407004400051002640f86080342d615421111a0b04500180c0c1c44240303d17040003070b200c0d1200a90311a00a082840da25102c00302d41914161484d4007a1030b01202105001c5000e0188035205200305110303020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 538551708 1250 538550458 538550461
    0x191107060c0503040201050301050913020603090d121817041d0609060307030b0c071403030906160f020a0201031a12010b19030807030f050d1a0a08030a090306021e07060b09 76
    0xc111280c1c4000c2c4e42c003900149040c4010b00c0b8030f04d48418841d4004241000000c4030022550100d441c80d042290509429088401ca02c5140c0c1e80002280042d101e58410800c210b502c00d6076086403a6915200192020450f01c55801503261008200c0d000b0b451a480314160b810700c0180071440f55039003207508a00940c084000b03d41c4604001880800343d960241c804035090382c4102410410b03410041c81a1030403072030305241c400c7c446024401103014035400009040340345801c040c0140c0503410708540f14100002c181100181503400705c1c03c07804c450381c2480c0216128214007094100c40420414141d401601b04d070641080304c1c815401101000b00c01c4d1031030320f810440090141c14060891001820414040140354002881920714140840c2c13541041030a0030002d01c088411200c03620a8440d042a0300d245a1440b4034259604ca001408010011807a022907041c00500082040c84000c026580204d41d4607040031b40710015103000d48100f8070302c5071101100c0c00c02c030018104c4040103a000da941e007030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 538552958 1250 538551708 538551731
    0x30d0b0405040c0b0c030d05010f0317120712090605072708120a0507050a05060109050c042d0503010c0e040608030f07110102071802030f0f1b0319110706 68
    0x754a2182d5084409102180d2503d10200204c3e84203503440145400304001c01d1007158000d00c14503010307002543d01c080001c3d00794540f600d2128100075401c00102c00501c002400d440110781950791248047c81d102100004698502029194036a030003016282000d04000050f03511851501440c0c00234281841e0000c14050300d09607500c01806400415000070160b050441005c0d070090003404450703d4030b1864060240c0b07803581003072030b981012155a040500100b00782e180c680201d0717400904030a080c6242514003098419501c50041d008070003002004240d4211070446103600f070040c44041d0090105900c14403000b404260a585140e100d54609500814108400000d03644c00c00070aa10713084c0307801525100c01c0c0f40b1620441c0c2460451007219070106020000000045840b4410391001d41c23641049056038294100c010030891007000008108100341000281017149038003251022942c0303445102132119004024400c44580307030f00307284261800140c904020100c0a004440810148050303c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 538554208 1250 538552958 538552961
    0xf050129060403030311070b071d040209180612120703230702190909080703020c1e1e0a060216081f020c1c030203100e0103050d050306060d0608030d0b04 68
    0x400c0241e00500140018800030b4025070140c0d050b001070442d03043c00c04800340c1d241e01d83d4a0b001c80707018001030004c84d0b10a04503207a109a8243c1c021040790203500b01001d010100c1e804881581039000b2200c1c81801254944c1c80c0d00040310070204401060326084a490700c0581c40c09c0d1322807171007213000401c8265103543c901002d5900c0c071703040403003882018a0107030290200540f00c45007900d04800400d410400282c4003045100c0d80d03403282e21803000e00d51144150f007800b81c1400500c044d254026a00901025101d0403080082d040302c2c0382c122030100104c102c0864009985100304003058104c04085000700d2666000280d902014841d04440340302c60303440c1e11409440b01e90a108040d5031104410301e4014081154003d098100100001c80f44c0d0381e003081003840341c40c1d14081483e0703011981c0002488030314100c04038100041c14051007a0b280b0355156544041e50b480d0494140020041c0100115540d07039241c030201c603290140000c0900130303240c94255581e181d5000304100e082071403502d1020420f40c20036 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 538555458 1250 538554208 538554281
    0x9031e0206100506031e07020d1101020304051f060317030609011d040303020a14120103110a23030715020102031509060d03030b032404060c2111070f0501 68
    0x9085100e0310baa454a401e2014682000c0e01040103100d0900c0c903142d8581c002941c4510504d01507000380f0612031951000b6041c81d82c464001081350340101700300004204001001c5541e0452a502040340109402c51480140880d0300001c11554000440e1400b8040c0c50001d140181d1b07044510301003903680d85202d40094002000e840c41038020b00750024000c079004c3d9000d058a0b51036410001102082c002da92403150340451010700300c0102903c01031080c000354001e07190000c0821b41d140d000311401c05c21008428024014410b8102c0c1001d121140315031170034071400000304448a08110036019404019010f5042150b40405018600c00b02450620b00b80c001c13a8007030400a480640d1048683d20210054249a070300e4581500c50443d0f804416080d8845400c602d2000c8078803804182031500c2c1000c01c1ea440d028400c800c1112440103074004d62015000e85950f00844200004d500f54007480c1c84006000d40c00000d401d0091231960744c03040c804107421043c036424288035034002030f0307003241c6a1150301c82c0e2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 538556708 1250 538555458 538555471
    0x2030403020a0b0606070606091b05210a15080318040c080a020a170a020705060604060f15230c062503020c0304030507080d0f0903050613060e0109031e0206 69
    0x404000d400702c0c103200d000135000580079102c00d1500740d513a120b460030386a071079122940c402d96880c0b10921194203048071002d02c4006281007840d082068121991840226580700c0050404002203400c1101e03560298452060b683c20516000b56240407240c2c07207810900008000c0b8980c0c02060740e403440c00c2d00c5030a41038115a254400f03942c03940d0030981c00a42240f110a020b020049000340c44d02042d00105c0c074410258400007595030020707444e01e00d00380000500b001c2d00590919406001058003078030840180c61806d44c90b000d07501c40030607085868a0b180c10000f00381d045485181d00c0e12071105002410140c000b03808603151500c0712140d0785c0400c1120450808106200f0b101484580e219400410b8080b4414040700e060640b42e4070380c68100200c5030f11840c02a440607000c0c00c04140c01c040440504030043c11b080c0011495502c419881e0840240301c3c081184075039040ca820041c41c2c1d48212145503080000300509409490040c107000510a11460f91103640700200f00c490380700246d039038801c44 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 538557958 1250 538556708 538556713
    0x611030c061303030f110d0c110a0f0201050f040f0504060501020d080f0703090c0f06030c020303010311010804080f12071b031e0e09190501150813020a1203090305060702010203040302 81
    0x1510030700e0321040080700034811410980c80c0d5840741701d124018005c083d842011203d0707441d41c0c1d440c0724982c01c0413228440d0010062000b40c1ca4180d500d41d20101d030311034a481d088590100f510031580b0049a0502c594550881500004074004c109100f40141e184103941042d00c0c2008030703039142d0b001640c0d00d00318821070000003800d441c00101048920000f0300c0e00150942008903440360546d50f440031040303442e0031400b51400d6406040045a605014255032444140040c500d1541552074071090200381c2d60740f8505024030580820208002d43e0210b03150160090b40307071601e548003c0910042031030260780060019046d180030501101c55090a1180c00382d254491400e5004480103450407100003401c3e480502c00c00701004126900c6490901b44103a500032080b0344440181e5140d0411181c06800060b840f0b038815244a101d29000190550040382c610b40ea81d540041510004078640c0315238001c50383c42c0c00d4401400040503003140941c0d00b580e00c40c1d030641d00c5035079030300200303d00301e0100b1240540103a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 538559208 1250 538557958 538557961
    0xb0f0a0306140d14120d1a22020310180905010b0303040f1a0702030610030b01080304050105070b090a02120c010e0f0f130209091806060d05061b09030a0303060611030c06 75
    0x90713100c24405580c0c0510b00300350740201300740707900141340350b0012080c4900c0181c072500110308140303800d100701998600803140e1081c1200b4001c102d803412205000c00d9040710354000041034070b5000988204005103420b170b5442d201600030103904005003500700011075003582004440c441d145000b01c20b450941e034034150489039141c642000c0c8800c1c0ca0480d00d00308150581004401c015840a1141c0c034812504140e040079014558609250540700580c000030300358000788418030507aa400310031565541d410100d0100c5035100d043c40141000c0001d600254403070b207101303005402d4280104080180c4102600c9041d440032103041881001048004a15480441c0b4920f464081c40c06500c03e0424030303031510f801400d1040c4c44020464801c800e50320941d0903a070041592018220402c409544580190343c0c008640085a49581e507450f0007030f140352603c9840c02401d90003043c01c10b082e21600003001302110f204d0407013820f0250040600e8019540015841600324500780000400c980c00354482c14002c080b01e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 538560458 1250 538559208 538559213
    0x6021c0f0c0f05150103120903050c0d050f0d021b01020715081018020403120309050601092315090610050415050f0c06060f0a0806011203090b0f0a0306140d 69
    0x400c00e000044890041020450b40420b204100d44c2d0b191850111307040b88554198140107400e405070141050422a40130400d20018401080c2c443c40301605450925030381d00d1074901541001d2800900401c11310507501c21000c0168009a2010380145003d0040d100040361801261921040c0c004c4148104281089024040c8100c0699034410764884100f00d41c1c1c1c0c5c550600ca411040c0592088103000d401180510510040300381006114001d42000c2200707000603510316032940814421494090b41c0c0c0d40e4802c40f48040c5042107044a0f204d41d08070095894813850018804020b1454203000381a1040000c18600b07210044072401499030715158201031501e9242c80800002c0c071050000c01c032091254492082d0104050322070140508013a0803249401803c2c406950ad100041522070f44a111040040072804261241504e0942105030f803484d0541c00e040d241c0a03030541c0a2600d50b41e00040c21181c85066030080c0c4403006041e0b40034002940e5883e0240b0300140340c5d801840d44500002c008600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 538561708 1250 538560458 538560467
    0xc03090e04080c1906140f0f070e0303070302070f0e09100f1e0509150618151908060610050d0c0905060a050d05010b07170a0e0405040c06021c0f 64
    0x900c01c0c0305052251501e4265501503090803118440d00c1407901301c202200080003003074090300b0300070341940440354200d02d0b0140f41c2202207100a0140d407902660407000c1440700c1c1c844d00b010540401c000d000c6a96901062a00940c1d41c0003e01c582140d8910404c00411041071203074006002d580d060004000628103204040c000780924050361a007103980c4d02000c1c0c4000101d0701070360001580d41d003000a50345404403d480c104010612001c3d04045c00408106080c0d035660b210340740c4894100f5501d003240d5200e840044a420300700038417540c0054003541070784090350031006203010f84502c0d40507a00c454540d40240103020004104003400b158007071042d0102e85096174060001c0c41c0c251714004045035500c0380071421540c02400d2480001e400012059441c0005005407401410890f10203403505d080c3e03444440d19001210040e140098000440c5000207100d50203211010b11300410421490905140c082006517207445104054010392035482402281c01d00036007000c1c2240d8488451a029140c0b0848 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 538562958 1250 538561708 538561711
    0x501090b15181011060708012409030b131412040e190f0b0f030714090c070507080601091a0f090702010906020c0607110609100906061715070c03090e 66
    0x444800d03089911407665900e400c041c0c98090305440310198059140300139414540024030b071209200e0a08010090b0340d03800400d90420541c500c81c458422406917500701d560548540c4090b00c030340303120424840085440d00d41c015807284520003c4845c41300348081c0396102d0300c60f01c2d841d40c2400014002000091981850240e0010082c0300b048074881e07240d80090100c03002188065251070707444005401c0c0d410002180000c0d4a0228000c055251800d040d401100001d10a0301d030148030340f90041400b61000c0d4094035002a80201503540c1c090321075501e556242824403a0007200b906000d402141650240f40c400c4030710002900c00c11041c64000144222440080c00d098115940d43d00c082c40452083d01c040c210b0000c038040540720b00d00703150740010554003280e101080d080d00700340d041c0300e04040c00094801800001c1e0901059001e40e505085008007907a900901c024071007003082c03008a06001c2005001c440e0351014455041d01c5240f021201003030310740002404034548400901040c84100940ca = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 538564208 1250 538562958 538562977
    0x905010b09131505150904050d020c0607080403140111070b1f1203030b1f110c03030f0a110a0605090a02090c18060c031b03030403020f011406010c060e030f09040501090b15 76
    0x290410450b860209401b04801c0360f064a40e43c201c02150402c0a40c184070700c25200300e04807015070600c1156103030f4071028815440010101c140160700105444003e4100c02041000c3c40d0803107131154581c0c00d02c51069042110300d4509142036038a91460184441450300695800c10103103980404166410784c000c00b2521192070707002603941c264031346083c183c0c1041540000d0342e503100b149138800400b0381c51a02080e850f200344290418825251105a101e045d6a41d25074249800c5903c03c00d59030072903003041c1700e0300c0d0b0150007941080f0800c200d8200002d4030744d0001788292100340c216940c0c45809260703406140164094101d2000b04403e03103140c81d034041c001c0545110300352132078001500c0e60700a03101400c2206291981000c01000240b58060046511800c6da4030002d04c44062007000c92402410000c0c14075060220380400c140070700c500c1d9403050811040c2101140d5692856003c840015000040c0561095003040004900c01017540130f408d4444001903c80f1042c4070040c844103050703800c0380500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 538565458 1250 538564208 538564231
    0x310090923070e0609090d0c1403070803010e0a0603051b0f03030c0c091501140c250819020a0e0c0706050a090c170709020a050c010905010b09131505 66
    0x39064010506031034119018078403002056502e00c1c1c07010404071408001c040c640b08088034020030a86032800304244030780c1d145514258402881e14600300c3d00008050039044524440451000c0400100303900030740c1078541440071020f0680c0c542902c0026034120340801000e5030004845440203080c10740400e000540010300001d960a01000440c0c0745802840c1c4d00c0d0103950020400004030300706007d0b0540c12601c111385020078410110000703014441d060201c04040c803000a042015898140b002c0c0d0741c0340c03202c94805030b0204500400d9054100c40c900078404a030240c4050440e59640c0c1c149140c0416074050610300c0000d02d0020682e00c60600106a1441c5c50810041100084c000f0303c1014030a0804110000d6032884506000581011542118119900e00300380303952110f20004807201115000d980150303076610350000840300b0f40280c0070818810740c20400c3c010304110b010740141c445000241e650500c140d803007400c00359220f215070001610281001c420b0000c044076982100c0e5210511080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 538566708 1250 538565458 538565483
    0x1213030f08070210090812030721050118140f090c12010203071803080915090a03210503060a0b130e04080c210a030902030a141006080303100909 64
    0x45040900204003421660700e080000c900341149808182c1000449051a20000c942e05180f0b01d950f441070303080300c020854500800065a000c3c840d0a030030148820021452007203126040c4071002803e0203001b4091524814684a82c1018035441040b00300102c0d00c501c2e0415459500c454800d290000e000300f4154082d90221040d507403500307240b0b01a2505c0c681c0005075a49400d60000b0800e269103c3c503c441080450300403c08914290169821450103c42540403441054071038130306481002c1030f007500008042c500000340000300b401e610110400342c202d50084400040d08442d40d01c022a40d05500148141d42400450b48020280105003041c080342282c65072288098244034108071402c40c0ca004001807902042c04060042c40151800c18492900c071900c038200c0c0005c10b00681010b2030400d50b58503496419543c0c01c020032561030f40c108035240244000400e440da10f9901041d04601401e0038a00000303414040001200d10a814014240c1c0220b030810307100e0710191110f04019161841c0802 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 538567958 1250 538566708 538566713
    0xb060a03330608062409041d0a021203030103020117090a050316060b01140f0f07021522030b040204231f120f0206030601021f0204030b090609121303 66
    0x24507000400c010044030080691814900415503100200001d00443c2d030310141c089440242c0c10b00c0c50520407103584607030302c8603080000b2400920036080c0804144100f80040f91011902250191082e40207450241519003041c0d046652480b00f072000900150740d9100100b8a100c03140a0030360429080c0040d50f5602c070700b039180c07586143c01181445004603d284c40b074004008151145500d000d0080c209488041c02240038072026010700c402d03001101000291151000b00c0741c2c0d0807500d189500400429000001522942c4260410f4107052108100c2c4000074250096090382d41c42141e5100e80c0200f0b9a944540c2800040c107000040c0c1000e05a10324030b040c520481c240d11003440b65850b018002c2c0110040b41180c0705201c51a40100b000e00103101e0b4980200784540b03282200d042d01a2012980c903120000103d240401c1d000d812180c0d01e03903c101116401071550000c2044a00030840c01107130352540602c05841d003a040e144501d040e4014030040c583e2032100342c0030b040e14501d0400e0100d460799880c2c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 538569208 1250 538567958 538568021
    0xe0c06090612160e01111b0105040902040e0f10080318060405040c0c0201200606150f0a0c020301150501020d0c020109050a080f0f010209061608070204140405010f0b060a03 76
    0x140c4020620f031400416441075642d2150600303035110024600308201000400e02192218084503412400e508004180d0040364020411034004001c6100c0c21942c4039595001c4c8003286070240c903031060f172401c0c1d0070104030f00725101943d1005503018400507500d8070b80d40070958210928036990032900804180000641079460303200c1c1800c181c08603220070034103c001d480010101407002900c1c040b510032000400c100ca4000140142d8041030942e05c03000040170ba030b41158500d01640815041c45100000c40340d13a840c0c1e004981c4001c2d0340c400d4009105280c8190400340f4400c90364003c00d401039210411048a051141d0102c40840380117040104880b03403a400450800c80c0e0a802c1b8220680c42000c10348003026080001e12040780740c0b00021418002d00500144c85032089040c0c040344488003541c440c013848622422503400b01d5000b030042001000181c0009501103007158181e55a51070302e0020041e103d114060b0566294004040900d81040c40d00150010411100701c00788804c020f2030702400d4840b04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 538570458 1250 538569208 538569211
    0x31c03150303020f06090105090d051c0c02071406190302070c0e0901020a090e0105030304120606052214010e06100512070503090d1815030b030d0e040c030e0c06090612 74
    0x42e03800381504d030004080b02403401c80050500d5002c0d13850070007048026180030851080d200e1003864041c1c0c0c2c2e8041380c05c105a0441c0f1003503017070945a00d400601040350760001880000c40e010095400c10b20b485003400c20146004040700140707140071011820110900c02c2d8010308182d031103144400e41c6d45803264005400d589048900c05211b0b0740c002490f110280d08044d550b0014044e2204160656041c880401d4590080381301e00103001458015440410a05e50010720203060003600c40b03891041d000c40c0c418001c441210707000d4103562602000c0c00d16402e140a15078180e960055044045484041c03c0c080828100031090303082040c184240c0880c4a600c1c02000c0c01f410b5103035644c0d9243c6c10a800c0260420002540701400d00402804a071445024803189208868070442c06040c14299170f0720550180c088083d16550500510a403090441e8201002c007005820550b400c2058100300502070342140c2601c7c40031409680214014030a6145c01002465054405856641403040002001c00d11100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 538571708 1250 538570458 538570463
    0x1e181506090603060509061804140609070303140921010902090406090506060303160201080a0e102c0309040e0c120c010807080c2215020c10030b031c031503 69
    0x80103404010b066810b00404025100440d04401c1a05112000030452005003d07a425618042d10018003401b80b40383c0308101000312101650400d19201d80130b99201c0c88140070480220384401d410012040303041080d07030110180a00410010403c072103c802140844035001300e129900c9100307031720040c1c544203e8280903a12801c004241c2185600c0c00a0070050000d101d140a94814010208080081c41e05031011603020b00b80180316480301c00401016201c1c601c0c45c40102d101d00203420800030707115801401150340303600300e520301e140f03141100510103c1c40b42c200100720b9000340503402c200e241652181c03400e14612811a14010a0000450f550030304203401011141c10451180400d543c10144081d441313021468258240d2901d407a802c51680190403141ca5030070030300d41d107181c0c0a0b0307481d40d2068080c01c0b8044e01720350000c901442c000c0d071f0707500140030150140080500c1c220341d03c2d0180c083d0103145030005010f084103405100028884280c140d031500c0801d03444180600c1e1002d00c1640440c00381d070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 538572958 1250 538571708 538571717
    0x614070b070c1b2303010203090607120f06141f0203071709101101060605040f090e0f030309010207050c15030c030a060f09020c01051e010627060908071e181506 71
    0x602c10308044c000044001d2100b80264010010051200c00c0031510326405a82e600b001400b4a841c80400c00040000c01e0340c0018041c946240460304605c0e08881c080122001c032100d1940042d0551001c0f00e26491465500c0580c1c13040c0520b000140d1504540940f040801180c542032103030b0580001c144103451485000855034001c21080350510078001c4030058802410803d1901e0300d003181546040204e4410060501da031594183c0c0b9509061181c0c131046000082100d0300e07070510881c1c0600035400003000311054031460700805118100004a1540546c1121070702e07003117a40780300403031205a000900e0b03032402607a2aa4007003010311103220070b0000b45c0f648500058235a104840e210342141c60281441c0e00024009112a0201c5900c2542c0c50540710246071610b000c5160b1005030382c1d00712000e0542d80c4d2a92210901050b0258080386607004c0f2401c03542140c00c41030341e401c155803007140401100c0041c641e0001040c0240b1903c1c01250120000000c4001450024181000c0d02002c3c0340c0c22140004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 538574208 1250 538572958 538572989
    0x4090b0c03090f150a0b01170103080405240d021b0d030911040e100f090f05030a081e04021c1a07080705040806150a0b030705040614070b070c1b 64
    0x550421201083c42c1c0c1e10380051134881400d4a6042d000f0b503001384010030300750f103a0030b08a02d070341d02c40d1f46034154161f84404007244030f58480c03506200d5134019003d118001d00350070b900100c8144107003281d010368034070301d080040c581004010860301a43c0701c070340c03a84400d0807440c000c1903030300348104400c80c000301c4143c0d800244800316240880c003100045c03007a94402c500380715410300c4c1ca00c804900325024060b048000201e01c406590f010307016184000c006848606094504d0007404000305c01070400380d40907a15a07245968460a28880b00e010812803d5100f0011001038014101110780d10403081261003080c041d0307841ca9403000031b24020096030741000400c4c1c4c410301510540203c4c3e49a08060715050503401c0c207003090b280a64a0800915451801000f000681c503551991341e11940500b0001003103643c0c03445c1c20301d0003824692003482000e00081480c1c081948030454038050f01c440607807200480145490300d480407110341079420819181d0114070000110400d40c12442c80b0f0081803102e0641044 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 538575458 1250 538574208 538574221
    0xe0f030301031b06080702193e01052a070b030c0a0e01020c012c1503041703101518090b1201020301240504080703150b19120204090b0c03 61
    0xf5424640d1000d0140105581031007441c64010550710400074800a462004501600b408000752445244032001e2424a24800c2900c0ea06020003003004d101d02c3c0c0c040e00c00c540d00c1e107004480f0792241d130044803210050b050205291064140310200403100d0781048603002d40d1201002c81e250352058442d044266030000d450f2007901d80000000b60302c800240050b0050100c6040080e0008803040d030320803030607904106500200054031794443c004a40c050584008900054414002036106603000e490b00305080715410392181100701143d02c1107080c20303600411540b03440d0700c0414966a03007010400b03000f055103085e6004005c2043c0070000b45450304c004640ca4540c0018401c14450380600c0040036401080103103c0c006011440700c13001190043c42c581c80ba1545141252107025a40040546e4010f40c6000820b1052488107030001f020550000c01c04804200704200c0d03d40e0201c032181d0090044450200318080c80250340504160020f4400f041c1d00101d50360700300b40c800d4122030303487e101d1a0220a2246 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 538576708 1250 538575458 538575503
    0x2c030607031d010507020c01030c03060b0c070f08011107062d0501050a080a11150d052403010209010e01210203040b090c032406180702010f0c02011503060e0f03030103 74
    0x914102c100020880c1d4245110001c2d244c009943c0c4581c10300d40c0725154000c10a21a60000c0004c000706070000d9290402d40003c141c03103098602c03603003106002002011484010602c24052600405041a40f41c2601903a44d03001900c403400040240070003400000c15401c810441c142c864483c220000659507040c9420451090142d8000b5211584507640a00c001850501d02480450003141c040d03030881061010100c4600c0303000c21034000c5031b080409000205640d600c00880b4040300500c0c602e40c40000c0e4043c50700304d000d05800c03540080d00109107c0c029500400701c3e0b0244000903581d020654050101e01d030107a0348240c0e021280040204204041c440080c411443e201008802603c043c1841010508420107440480301c4843c80704004035406960380d6004013003643e0a1540401280741000c40a40200501405011003600304005011000d00c180715100b000d02c0c048100c004d403e421601c8040c02851b411140c40034a12036680041c110410810107540254070401314140390b03145a210586 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 538577958 1250 538576708 538576751
    0x408010f09031206050a12050a14030a030506060901271203090815010803120703020d0e1501050109060f0503040501090602032809031403040302160810110a2c03060703 74
    0x50413031401c1c0c01440035984100d07110007140c0e210508404107080505100341072040100005112500c2000844c001850100140581c0503060701c0401940d81c0e81410720400348144400d15001840009050b80e680c40240849500c40e40002d00c1660020f4035110840d200031040b5005a010441004003003054441c204580d4155000c43c2c40349051551503d420b5650f24002c0b0f0b11000e00030802da01c00142260310030740c150b1b43c40c1e4001f41c00a2182840401116417611b90f80000c21800420120000c10154061082441160130303c0e078a4030891080003c0c00c80340e940025100301e507103549803000b92001c07824030300185004050754803880200746d1201c402c442d41801800c1220300840c1c20310288002103070b000868003603583d0005100c0780d6a96540d103030403414035184500c3c9040001c954200442e01c0c01c000608041070702e01b020820011980c1ca6801c04c1071a00442c101d05d4002410300d0285940f0b1200c801c1110030310595400b0400300072103444002418110116007a00010742d865000182d0b2140150041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 538579208 1250 538577958 538577987
    0xc0a060501050f0604150203220806060121330e0a0903050a0807170408031509040c03140a06060602210909040206030c07080c0d030507080f06010f050408010f0903 72
    0x140607030982ca004c5401c90080707104440d410100e0700d0200c01c2c928002d0045401c4414105200f80030303a185100107005d5464580140c0e030f801c0c407171140040c050354000e2282143d149011054083d00c12000c5030420082c00a003040344084000e000c04504881c1d01d50590000002c500580c040034090500302200411100180900c201a0a0000c1900881d400404031f498009840c03800104640d1500003da840040c80c48103040c180c64014100018844003402841c000c50105283c448454070030340411407179080031f84001d0042d240401c1c0410020301c1e001d508201030004c000607299076200607107901046030050b41c000000350300b0043ea03a803031200805000c00e0128540c01221402c08031400e010070760150004000070b01a01000011031603c485107000c0d40c0344a0b0b804403119540c0c0a0252800d0340ba0041401c900300441c4c14003020035681c034055480c561003035074034510b04c1d043c0c0d03070318840119000c054080c480004c1c4041040b010544000a0081d1648000c0d40c4002191002c803034a4001e00011040014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 538580458 1250 538579208 538579219
    0x705010c090b0403170c0f0109020a0f1a0705190b0402010824011d030a080702090f190209040605271501051b1203070c062a110703080c0a06050105 65
    0xa0200c0d02c000010782e0107403904480c44e02ea0b09100d040104445103c1c0c01c0b22104a80308182050404805c150004e03103026109607108000329564510821241c0c500b07005081c0e04c00514409001c02c03890f1080901400c900580c1114624a401680040c03014580882911500c11280410066503040303186513811001c000b01c072a584c0c40001c10005503060030800358074100103c0442d40660b80160306008280710344001d059a01c040303100d103040c40e400c0d030210100700d001e4900c41000404121100054502c5120f4040440c007030312a64141140003540080b01d8240d019035203c2c0041040c1d221004a208091124503074210180c254010055100c08002c4c201c100d0812405045001a64031005588603020b400740c00b40b50701200100074a0038040c0503d07250080d468088200001c0c1540007404414103409507200708a80c0c0d503840c90a9010690020750605003640b01707c55520468410f07080c0d991070384901760a4581d4552a603480b034420380e001100c014080d900111100081c06094410b6500500c1c08555 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 538581708 1250 538580458 538580477
    0xf0302010c080f01051903120f030e010b010e060d0f110a030f3b0105130312090804030308060f090a0f0617331f0b0a0e0f0103060b0c030705010c 64
    0x52428400500605006e500d49494000b5070a00405010010b140e200c2c0352039180382e140340740040c401c02e2032036007590009040c154a0740601d08107110f1001d107242c069480010f100070780c0080c0130031a48034000c241c00711581e401c2015070707009070780c42044810803100305000c1d039502c203e100040a0700d031440d460801ca503240008407024272890300c00c520046044000905030207480c0d40c4070440c881c1c1c1c0018103030701c8950807e002c002900307141600240300140709446000d00e4148c1c04131030608030390480c01c0003800340301300300828004a4021400243d014600905498540c40070001142e421503080d00d10041c841d890340313200d50710107049014020160200b00400442c04c8440d070704c2141c0d075100d4602d0a17440c01125080b80580620722400007641d5a8600714194468103195060a821b4040b582d9090384594a211000c5480400317802141d1040a00d0f541d0300c003014941c00108403501241070b02c0c9a0615540d160009024203400f005403c1c40f01100c0095a210b01543c1407450942c0c4c510440311080082030352 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 538582958 1250 538581708 538581721
    0x2040f050f0f09011401031a0117060705031003021e120309061207050403050a030816030614040c23030103140303061003020307170112050c1f0e03010609090f0302010c08 75
    0x550b9405045404107075426110001207500408403c1c0000307003402101c1c4000b005215164119414408800e4110b021903030341c481134100212601c2a060314a07822107400f050000c1c0c4568003868000b2408504000c030181d032540081e240001402c1e07161203240b8a8000c104161500000c008144001c860103940f500355a080050780340e1060f150045a00500310000c40c00162040040d00e000d50380c0002142e4000c80035080140c0a90701c201c07448000c4640891312228020b1080c05503604503400103141481000c461740c03c11000c0e1402c200f07003800b088000441c05054046003013581c400e01e030140035070b0755032541141080d542d040b010190303003011a8020824003040d51a000d4101e0030f81c8407203180050312929801300841d510803820f01410405043c0308004600d4440c1d04164540851168044408644952050024050350701100c14210001c0810700d5644500a41806441540040000560f1616401020101d4240703040503a40111190510b004043d02407003012440500c03030603d10003a19014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 538584208 1250 538582958 538582981
    0x207050108191404060c020703030c0f0212010c1d09010e060d050c030109030e0108090703110d0501152d0b03040f06090b090d030614030d080702030c030f0702040f05 73
    0x61180504101c90200000e010b01000c04480014011952051045024080700c03e0a80761094030282d500c00e1a02d01140012030000580f10304880c0d040d160003042c040c1c40c0c1c45110480360b15000c20b0760044041c281c00c0318602c2c000e104d0081181c2e03581d00d42068251002601d860b550039100c5041c0e028405490042c024013801101d4990702c601c045940b02004401858298289038141d0342c002c0c3c056080060304000c05403c625040722840c800ea9a003d2a59200007105680341d0f428440582540c038030700520085400c00454292a5601400001c5500700c03000203869117009940c1d1059800d0303010181c84a8144484040d030103e0a540c080800841e00d04065080318a4070010340001c25180380c0303190741020050316400040b01c2e16040345c40110b040c5085480d182c1c444000102220000e07183c0302d00410b0305150019500d21903075014008108540c40c0e150183d54015001d058030043d0702c401d01c41211140405c100070131a04900b454100e8640015205120941c0c024001050a075400d2000300200f91445 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 538585458 1250 538584208 538584223
    0x30206100522020703180617060405100605030c04030507030b090609030a02060c1303060c0806041506081f0b07030903030e0411090915060408060610030203061c15240807050102 78
    0x40000050381e49815260545a01c1080c846c1000c01340030800f400110190024020510304800403602c1c40c5075602c00703042200303c420449074550f510a00c40d80c180103003032062000d146e100341e104d0a01071819880340c50b44d030300e0903ea0340d01c2110311191302020402c03120340500210390002200c0c1c0046082c032108500294441000800d82c20b5014008100c04c1a40d00d0b03c034010030020f64202e40c041041080007480204403080444185002d0b13424201011180420180a80100c03a20780d91040740d55103e40c1c0303420101c490b24147c400d4582690b48400f0039074082c1c9034010f214481c0b080e200d0b482c0c900c0c9035140141c20349445d000341910491814a07000a04410003003150404041120002c400390b843c04400004002583c0c41c02d501b0181c00304001c10b841c0c4001038203038001c00e400c452031229031150700e00803400c1e488100c03070503074214421030980b01e40a9000d9103140341c80c51144009015580800102d2001c9032070a041c0700c3e204004015251a1840b982502d20001d031120300e0107443c0c09810710300043e5840340e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 538586708 1250 538585458 538585519
    0x30d1d06070c1712150f060904050604090507150e0102071208070c0819030e09040305070b0c16030e040b0a153b0319020f0f060d090302061005 63
    0xd507034030141042903480300c43e000081410075090721182c0b4041c1c4450403000c122032141d0686041070b0001114035000180d0070040000922081c908440e217401d00000d02030180802e81c006071142064000184148401d00281120b81e1503440b01601031800141807000c4070f02c00f5419034203d480184002400760911120654000401503550181440d242c0242803035644031507e140604c581e80e01c1795440408102900500a0b5502030404810b64100200d0302825580200818010040c610014070301e03400c0c241d4060008030b941802d00c884216020012080150100c00250b41d00e0301c07401c6a850b045c4076021031a0016200700c06100c1c10700aa80403a201900c42c060244901405010408010002986608414000300040c440c8148428445046070380c1d400612a0180e4070406041e6041d0303001c107102040e001450100488003a50601c207007450900700b06500b09a013003100c400540840d0281c00c22203442030f8000c020505d002800700003989001e4102d24031600350b001034000b92a0345804a2641c400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 538587958 1250 538586708 538586717
    0xc060a14160c1118091f050c030112140123010e070804260c0102031501020a0809060f0403020d150b010507080d0b0f0312030601090512061302040617030d1d0607 71
    0x5007210005890310703500064800684582e141040480c082c0424240c09840c0417291100c0f86e07004c40190350040e90304c2125a511118020300040004801e000743e200005c500a9102e0b13101c518104605d00d0941311500c0301161a03465145011100007502e000907401811900710b509101d01b0100e030002c00c548000741000d400100100300b0031004040a105c2550024401244180d40d00e0061410601039001150000c42d081807641800c229940003140e005c50b013907070000d28646001040d10070002c041d04071524140c41041d0a101c0400142c881da1040f4034507502402c605a40040715400c8001030b103140b501900c2c10840c051105400040f0f2007410340340341700c190803c0818006c52540c08076101488910b80350758984950001001c0510b440401503001704001e0785c0e5691800c1c4c5510500110f00c01071035000881c2c1e1b00210000d400c0c80040200f1205e443d02c01800483d80d550356507035400c4000481c490000142d00300190880041220f0302c189464280078048030081520b4900100d40c468200901c46010301 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 538589208 1250 538587958 538587983
    0xa05040203100609090c08190f0813060c06050a0c0504050d080c0a120206090a08030a05100504110d051311060a030e10090510060f05011101020c060a14160c 69
    0x19074090110501c0303881ca2180070048140d580c0d9140002e054880000d0b242031206000220781590302081ca02502079481115420080d00b40e9a0080455000c00058030504410700505100d0062500f03041c00420b02135540c079101603001d040c50402c03110054200e1402030710300850480026005401d850441c0c10031605180c01000c1401c0159140c414a4102c540901420814104200751401d68a4421145034200d51700c0380e459070b581c282c0d15005800050941c001c01c0c800103400f00301941200f54400b0400381d030040303850340e1907011038280d40100407440110400400d1050b070b403142e80c0c800c0e103500c404000604c2580302c0658503451008420b0004060207490300160306c0070001c1c06600f0007440c4405c1c04046a080c2d0614140da100103000303c40702190b150062040c4405240c180d0b005500c180c0d07600454130a4003a240c40c1c0152801191407900303c510355001e0040300c1d1424014040c2510480820700c01003904e0302080c036040541d100003044a500c8800101a40080030303884400c081e21542c1c80312882014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 538590458 1250 538589208 538589213
    0x4020a030902030304120b0c03010302090a050403021f0515010203040f030f020a0f08100b010f0207150e0d0501050106080106052503030e03130311100c0210030615031b0c05060a0504 80
    0x41c0804800103501848002400103000c0070010340e5490150041c001c1c0c00a076203600401030140c3c40217100103513000c0704000c04501030703400380e40c411600705100e401116401c0d00c120308504944a9660804916039070b5803c10040c2d07803101c84100a101070000d10103145401c0c01c0c6140005004d4071800081e04200580003501c0843d1506d84083d40070b0240700003201503a03665492026591a000304106040900744000b0b09000e500640c2c54011040740b036000382c900f590070415403101c41d141c4184c50408200200c040440c094460b1050080138034028000890345604010002e04282d5060303105408100e0100f003581174505550717403d030701a80c1000f0360100b441c8480303080c05c8007c0d118180040310640000500c1515100c007a00300d010445e80300b504601c18100401041080920f0201d0000c004551104945c03001403500121404040d0000e00340007604584818012107401c07000b05200380429074451a03407495101c140e209003840ca0140ca0603103019800340c4c0d580360302d51401800c0358540e0382e150301c0030604 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 538591708 1250 538590458 538590461
    0x20c0309030303010906180c0c02100311070503121503030406050d060506040b030906070302030c0d0b0607060203090f07050406140d0f1e03090902030103080307110a06060b0909070201150504020a03 87
    0x80c1000904a94803940c40300803c5d0700401e0345200e0880701340c401c0d41c68a01120002d0041035125800d13500c8010403030300030707809000800b01102c22541c1010743c0e5070b0400d62251410400b070218917000310002d58860f0031184101c4100c3c80040c150032244100d110200300f4030780e000400c98041e03520f02c1c1780c0643c40d0085404444003908064001561191001c03030301240d810320000c00385100307a40c517004a0300075444400040d012803006076051039107034004006030444030003039820500386c0a00103028941703041400d07242e860880e0030903298441e0795080080a000c0c045000c10610001d414101c80400400386480d500b4000942080c044900841ca26610b10040c080030b1f00d22142403907003001507103641c40d0b20150300e80014080000c04a010640705000031402480e1842078a050741e5014a59600e5500c6142040d0f58042550b80020b1552103019803100c0041c810b0f00410000304048070020b911001c60600308040307410020a0b050444e80340c10604545099115142e0044800503240184e90310b000110440 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 538592958 1250 538591708 538591717
    0xf183e18091c090b360f040b01020309063006060d09081b0606030d02150406020310030c030b010303140a0206010b03130c08100e1203060103020d06030506090f060105010e09010306020c03 82
    0x450800c1c0203c0d009180440400000791700d51030100702242e81200d400e207000c180c125403000d0150025206209040c40d41060343c81025000c0050045a0a140e80d1000241c03690303018039504500c0410050754030b40c100501007a95203404c0c03e90156949589440c0011940c2c0c1e0107058142c518203502e482d00c0e44244178074801190349405018908201750801c41d0a01a03840a056400c54002d2144600c60f040240c80819681c038505445002181c1a07220790300d442029420241118410030b1001900000103003894210030300031842481070241c158035500740604002000507220a94040c01c100030040d0341c1d40400c0321070654411400e155281e0f200c0351004540125480001071200d10b03941c41c0071403c41c0703000070700c400300081c0716805100c01140081026150300000800001403101400450f02660017038020700303007030b00001500044555903900c50a284c1b280c10391300b0301d40c240c100d503020000f00d030720a211140c05480203003443c040540600010400451051101038400d942c0441c040c4482c141c240103c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 538594208 1250 538592958 538592969
    0xe071a0912010e0616050f040b0c1e07030309091b081506070302061501030e0319031107120e030f030f07050106030f0b010602010f183e18091c09 64
    0x20445860800896a59070310180c54243c900c000f11020041c2c00c5201b030b81240c284603102064181083e24000d142c04041e000318000110038000c030080c1102552800c00002105515500202000e1f861400c001c2c01c002ca003a001051366506110070500c000b0002c50348881da84da041d1902c0d603820380c0d460059036440c0c0d100d84140c951002c1c00180b1341046c0340d80040c00a000d0010310381c0700c420000700000107408992111280c403005070018000d0f103060400e854103000e8040014100410000044141c586d0700d9400303200704642c200440180d000b2800e6004030303039000071202940180a1161400d0213a5500e028985070034000440000b01c4104118003908040700a40e44038084400c0010689424120701e8824014100198a400300d19500b800c5a8066484542c40075110042150041c0d1900d844920b000b08200704400c00520071040d07000c15048100001c0783e031012007a000801c06d241005414110041100e4881c800c21044c0706140401240f070b00e45035030620110942e48100000240c5100101e64400c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 538595458 1250 538594208 538594211
    0x61d04140a06030308060907020618030c070b0c011805060c09061201060e0102190209040305031e0703050a11030108120912010608010f0b04050448030302010e071a091201 75
    0x307010250040b40c10090940780310f500e520f00c0710354481090186401f0304545820059001c400865141c0c841d01003203900f481c81c064192403502c0e2003600d2041c80c00806500011561100250404e11400284510010b01d05960400ca0303103400581c841d640e403050301400b00d80c444040042c40540582da0740d022a00c6002800300d2044445da0345103005070103207810642c0b0078054000d4401c4004050542009510581c0d0b00920b03410003078440d030714101c80070303000103042c10b109403040112200c001da000490148038011581d80840c01d0b25008240d00191110002300340c607000818001442558408a00e820b080790781d54071010340380c2c40351400180764481006489010780d440e0144c08a0380b04010b400400080380c07180c5080c402000000700348404c4031022203000d0904a000181d00714029807034a0b440c049408070074098514000040c0d071408a5402e1100583c0e90150441800c000300354082c000c540641c1d591202030140b0510b800d016070b4030b08070944a1002c040710001140346a6507070300640e2035110b4040700e00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 538596708 1250 538595458 538595461
    0x1023160203041d01030506010501050f07060b040b03160302030d0906080f0702010b130203010501090b0f03061009050301140a1104060507080a0c120e0f0a06020c0420071a01050406061d0414 83
    0x6000e0f0a0100b41c807035000304000840c055004004888500140b9081c080c5000d0b200c4c0ca07820002c0840c0480242d0107500c407441d1510079a03080011800200e13141c1e100040c600d01c0c40c410946004c12070364040060000444041181c1c0350810b0155501092001c001000f90b9a5403100328014151245a160700120101420134070b28815806181618400e80310300c00002d407105002d22190052100088144004000050880c10142c0d90400b40500500304008042d0310380000a00b5500405140c0842203a8101040b094091a020394050a07440c038a44624142c200240103000b0705c510f840251030b00500003000c2c180d4a201c1c038001100d50380c0041001094401011004020383c0c036500403544503900c540080c4c8441d10300030002c80c0446419400408101c0c40072410f00c0b010b13020001d8000064048004030031030b003025034002007080a02c43c0112248038003100450086558042e01325034040d91802c2c105011190b08221102124003400daa024442e070428400030740600301030303291f10310100035900 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 538597958 1250 538596708 538596749
    0x501030c1403031207050d09050f1005060402180114120709060216051311070807050102030f0f06150d02090d030f02070602030f0d020a1709102316020304 68
    0xc1140003030301c0a00c441004040140000c160b560700800030500c500c1c000e4400410b80703c50048005040c80c1d07a002d003000c9140910703a190982058040c6d504000700b0f40010340c030540090036511540781d12050480d011420952809040c003070104c03060014a05000302c01c1a2400d010000800341da2140d140120326010dc1c0c0b42c42d100041030b24456108603c05880b84000e15541c101c8c41008550a541c405010312500907440c1d00c548016040301c88a88180c92010010000030130780020003015001e000e0000541e803410850240691448014030018107903482c2002e1004590320521030500014050f04116298940451914001d106030201194401c0c50380d050201050340002140f4010780c903170707002d85044941d15034040e610b034840c654440c180a030080001c4585070f00c41d076000e070402e41c42034a080c0001901003201481111029902411503500001c0e80080108890241c4d1700000e004030f2001c41902100107030001d405201402a04e1000d403044d8211480a10800c06e540050001001c501c2c40302680e803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 538599208 1250 538597958 538597973
    0x607050a0b1302130e0c040b04060807140111070b071502040e101a2a1c090503100603030507030e01110a2609030304030b1e04060c0f020d02070e0405070801050103 72
    0x1140c220b00076124510b0000c40313a202d0b88103091070016183c2c00340101c4c0d640f44d010000141103168136239601c05d035070f1100410b4541082140d20040e25480c640e0f0f0050360192000980ba06c5980c43c80040c05601040051299034034a02c1910385c100d070f2002c01010082d90f600040700190190b50840000a5001402c00454480d00d95140d011a0b0032800c0402c1d44010508040100c2d00c10034290700f624a503518101f0304090140e111514480c0d40d520241d40481d2070118149110b81045d859400004d01001014400c078682444010103100001c00b040000d5441c5503000340c218000c0c1c080c05010f0002041d9985440d1340965018031400c0810419246d080b415072030092400d480040681c05050010411001c01c07125810440340c40302801002503081c18510360300c900d0403c400400076200c04e20a880940310f4449890082801a8800c2c080850f401c5041c503001803805964484407001c541c0722445a0119035008a03001d41501e43c844500710700c03940d4a0406c2898a4410340c0045095031800c4000002d101300c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 538600458 1250 538599208 538599241
    0x60a030b01030f1a01120f15060e04020403020f0d020406180207140601050d120314010303031a030c090118180602092412070c020a060504180501030f020607050a0b 72
    0xd0b00c04012030304142d20304504075448000008812811314140c10010740c0690959012002c010102140a0302203044020135035000d06d007000319048440d1828403945030018282e074050a016103007141407901d107400080c000641003103510b00407040d4900c0d480543d00c1c0d94000302c0c0034100702c0fa141c0042456004100340203510400054400342c0b048114014049000b041c0340303040320801890300000400c00d03105c040c20103503c03020860500d075540781d50091841c2c0d840e091a00031806924001011503c800c481e1850f4030f0150900352281e005089011010b9582c1c807410350660b5962041440e07214102c000040040110ba0861780106080d00540003c001c03c1380c00030030b11100240c6c0d030310010440811000c1c02d0311340400418042c48000348504018049440c80080c0d000c42c20707140200e03088410b030b0041207030314589070070040000d00d0000d070034482003040e000034013581990010108450f40c9141c03100c003a4200b002100a1040b0030010b0114203111041040c1c5080d640c000440740200c2c1000c40c10214005178 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 538601708 1250 538600458 538600481
    0x402371e0309380c0301050108340f0e092205010915110307020a02060d0b0939040905100b2214030613080f0f090306160c03031a060a03 60
    0xd42e0780c9509000f80000211034000c101440c9118290790030a4010344000c40f0080000108146000503040d00d10300d40565140284100044c002d4403040d01c400003802e40d40d00950110030300104207680402c40c0c0700c1d041015440a80c803072520545810500307060f145003140c2240035015600b810700c804107029444c2d08101c6261000801004650041010240d032030000726094000360300491361000c00360400030004c050a0301c2000300019010f554100282480c8001d940b070390380030001c0da805031903c10105641883c1c00e4140d000700980000032800c42400b41e10490080f411120340325004201840c0ca0840603a01910f2100c2c01c4a448409243e207078020200145036028a0340d100d0107000404066075152203490b1040980600500d650310040c1180302101b4003c126401c03401044a401c1210b0180064000e102115104070b40c0c0b049410b08052404401070407000740764540c101c0058484d80c1111800c0b4250703a0505010480094441d502c400400140c1007654101900085d0020f10701ea0540c0300d807500c60b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 538602958 1250 538601708 538601783
    0x30b0412052230030305042301050601020c0103060f030215042d0f0f1707080f100b060c0a0308090a0501060905010e0714030c09040b0402371e0309 65
    0x103c180c21002e0301d1001c0c0c02005030300444944051000c030344250405503100e4000c04c503200300840b80c0e41800b5244030188580c0082a59141c0501c40301d9a81402907040840003443d0600c025800d10302c1640c007000082c07000900c100b4184c44802c00101e0400241d80003481c080307040d41001d040503c43c2200004190450424032801c04a0110348002061014029103a066503004c01460402900d44484c100e81140d128144c8281e1a00140c9110200300c000d06224889001e0a0415208030703250f0b081e9240c090310b240c451503042c4050000d90030001051980c4030f4047c40c0c0309070261a08514542072101d81540a0051f50810b071006ca25040150082c0d41211400e03941c1030700c6562090000c49600100c0003804109600800c04110400d40b43c40140c403c20900500000303018040000040403607001400300c81606421030094110008610610324071660b4142e4900124101c09400500156041700c2101c1d0300c2c002e9042c80020188281d10204800fa84440c0c40240c4800d410340c0130808000141d000c2c1e607000c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 538604208 1250 538602958 538602989
    0x15090e0a05070f0f090c02150a0f0608030f070807030c0512040303080c07150203091513030801060f0e0d08070206070312150b2a1903030c0504030b04120522 69
    0x11100035043c6088514070b800e00c02a403030404100314003910851486c2c0085226514204d81440d0107211200e00440b4100400107078001c107000654140c641c60751103201140c005002c1c000040552800300c48020358030500307695888005103000e90301d003014208041c00a101c1c154846420101c03180050040d41d0083c0c580c00180c3e039405014802034840c0c418000c6c0702c00344042c9003401c04101030f0080c5800c00b04078415207450000c4803014000440c4121010b44880101c5405a024540c010002c1401740459160607052440343c200c01821920200d81741a0241039426940b00034464641c0940b90710590003846d0ba0395031021070030b00410303181140030a024890301e005454998022583e20560445458003449400c3c080828528203c0540f5110302d102e800203120024103401a0512682411505405034241401c2c01410020110f800191840d01401000c00062011600d5040b910b5401607100c00c40c1c8000c004900d50890303940c0506104209611100014000304561401c942070580381c6c2d15006240c2c0c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 538605458 1250 538604208 538604219
    0x90d020c1e1504180f0c170f25050304050c09060114090a0308042709020f060a14031303020c0301050f010e0a02160308011805150415090e0a0507 64
    0x14544030300005016925000c1030046030400c2107030401d5401807000014285a0740b6414141c0758030316501464200d82e0360f00c52040003980c06202c0c45071180f080e880c07c480941e604803c0d02c03541d801c015015000001e491400900c4044071070080c644030002034260040d04c4031095601604d41e0300140e80454041c01201c041640604106009034460901655022036103040d04a064000c0d5100b041c8103500f00522800120103d442c400003440201802800041045400c940c003401c903034004032030300ea40c050504d85d86002603510041c02c10b091410031100c03d03507103680d00801512501076154444940da000401082440d030481c031010407056000ea000d40311000050b00806080b586c0c101c82d1800b1100444006004040f81a0700e2103a11806840f0010300d410f040001c52007004200010450010f9070318401400394903404070400c25010100d4100b4410303801c0c0005600700d085403041c0203c0c011035840301d40c261540307151042e100040a400c2e8040102e0300c800705c40a034803404007a10541d000c0c40703410000101c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 538606708 1250 538605458 538605469
    0x6120c03051605160b0403020601031205090f12010902120601080c0301021611060d09080406110a02030a150b0909030304020301110313030c0c08030307030b03010606030207020f090406060806090d020c 88
    0x400e4207002c0d80400d80c106001070079200b5801400c40d4107002d05040c40c24200080360580705500450094004004d03d40c51460040c409190500c4140f0811109200135586611070080300d03005100102d031341105155111a0366801042c4041000e0341c842c140c410705140440c1e02180c128180e0358220b042d43c1003e0340040c1070500340e105a1204c0801006d06602c008045030300c80810301803889004003020710b003000d10300c0100c0940e581840e0903114007034002403c02023140c1040b01c043c14006000c1c040c02e0082d0b51500040e40300d0301501c078050102245280c100150502d21b5122182440c4010407007007a0303061400406a91341c104403422030196103041e951443c40c60030300c0296440b40c8002110101002850799003204c104211084c101ea80c40c4905402080c0d04105002862241d0850340d400540110074804142c00e40354503900038418140b041180310056199035409006140b41078075550402c1d11946400700042a480e88190a10b008140501c0f14072040070540c00343c18040703542180d441010031802c112 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 538607958 1250 538606708 538606711
    0x10111905010b0a140910080a03090e0f07050307030b03010b12010f1a09070e0301090213090209160512041a010e10051c0204050601180b070209151c1b06120c0305 71
    0x1e1411a003010f038410030701c0c040c1504c986c001c01240c5181c080c255940c1410b40f8101e00810300b1001300d61543d0741401082d90308401145c0c0404c4040e0143c9490501d141c01070624032024001904143e04d480c281442c03500c0940100c9441000a071200c080d4200e4210401d00070403a82c0142d1901c2c1d81055412203032040300d600c0740c510b003c00081201c8080d8807240400d5498a02e0181915095501c51038134030090b9450340098141c100207000085100c020034410851a404000e00e041454401a05014102a440340948903112040750041c0d06c00c0d00c07181042a0484080f000715100b00b80320b60000308690801442c014000e00c104501068180d8448040107a0b1018400581e1518400070340380074013610b02908900d4001406042008403910a501800d04004e0070b03403c2441840d02c0000c00fa01182098408071307521540c070103480d404401d00711000030001c2403194078006801040b4402075040c0706c021030b400e8283e60f0003440c4c0c81c204207039600d40103041d401d95074a00c8a00c3d54901085017903254080d01440703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 538609208 1250 538607958 538607969
    0x316151106061c03181409090607080a090323040503070f0303080c07150603120f030212070806120304090501060f030e0d0318020307080124031110111905010b0a 71
    0x15440c5100414040c40f00b0032040d00940803c5000b200d02040401d15050b407101910152522076003140060381400700c0c0000c068800210b0354805802c00000c2c0d82d0004086400402210000ca002c2000e42070071618a03004005160702c600072503080b0314034a0b945130020402c2351030640c1a40c160a60300da800140300313121840042e0205440794001000300441c10010640284a90800825180340d040c22404941c4d131500704a6021015010000a19400820015000c6860316095103023030500886041c2e2160040d100c40180080f2201042d19640e4003003513034081071600300849481d1652510724501800003842448003041d41604a040b442c2c1c801d0203003403e8840c01c08024400c80c0f00d0b084003100200000c95034400c3e40220505610016a02882084000d01140c400460007105107000b40b01100c0070f84400368188100c3c01420400182080d070b0003410344004403558020390300b01c000190b0b00307240c0640c02c0c01418001c0580350349000f21800d42042e01c85001d44001c01501c1000018429856614041c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 538610458 1250 538609208 538609219
    0xe16170303130323070506061309050c060c0a050f01380d0c0f3302060106050d0f0903080f010e07051b1002070308010e06010309080d0b031615110606 66
    0x10b070000c00d0040c1000d02c1003203622942140c00074402c010000054106500480d6a500040c0c1404080c0c070708446103920301c8250007410030082010369113165407085200f1009009000210f804417040c00d052104002031a00b0000351145803103003814a60003000c10820581c019890314003148000c2100070443d032042e8084040c190302d400f002e0400c000d01c0c0111410b08031401549510302140c40c0c00c0807a11074000b03108100740700d165a111001000c48690040b0320001609101010b001c2983e035001420034111809803d140350b44200034840d9001801001040718011410300ba01c40303040550082c0d0051246409248600036643c9603140420810400c4c0c0704000090414400260f0801000856884d6018990f040f50000088502c203034003640c006a10035000326200e5801000b410004c092011350001013482e08000304100c0b982c445169000c3c1c004584001980c0f648100469201000310380c1001e500342e0306600803690b035040c00500c1d00500160b5a0001a01c03101da42403002800122070b070294000410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 538611708 1250 538610458 538610491
    0x50411090a150813120c050708010218030106050409110108150301020406050405040b1002120d09121808030f0f0705030c1b10030501080c010807050d09050c0f09040b011403010e16170303 82
    0x10031204001b20200668246c02100000500004244014a410340742d01d004005560f00700820075003103e40700c0e40054011070510a86000007004200301c04207680003401d120b54203464030380030000030100c040003003a015031002501049003600800034104942d401c40e4140490b904001c14070401012a14028026a00051064021252100240000035807855001501003542e0f203900e0204c0209034441c5000c0340e0801d805810000103103c488000d084040002c46c90011845081c2145106a985c4002000c2000c01c16000700001031041340c5201d5200c0d01242d41120713980882c0d0101c401e0704101a84100140c01c0350980c07aa0190140c1d81c102c0e9a0342001c0c00d11158a20300640d8030303290080210080002c10810b01c00151410303c11854950300074402848411580010b02038060804400c59214026001c1000005440c840c40c8030305481c04458203031441482171000c280544070300c256102050282c144489080d1110200034411110707105074441d4204007000321540c59101c252140c05160750001d6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 538612958 1250 538611708 538611743
    0x30f010b090d1e0b010e0702060c0a020c0d061103151309051002090a0e0711010f0209031c0203040504020f07060501051206130c0e040503071505010f050411090a150813 74
    0x19089500a01a80c0c406841010f0307035245040b44200342c122403400c8a51200313005645070304105280d44643d440310000d25154114ad000780d0b031120401d101034030441150310302078100407540d0000403840c0702040301c7c82d889007071003d1019081c14014500500802c0a2840c0c455a02d41601a00c0030035508030000d0000c41d00268484000781d800401c0b1650446041a0300080250035412075610958643c0d440105508040382c1c032501350340030121030000c545e005221480242c9d03030101c0d0120100f03018901c1000115080042a030941c0215840741e43d010340701192030b06004a034000140700685c0308610820060ba2a041000000303035a100020050768003210001d44111002816400ca45004200c100801a40c0d05010013948100b10b400b00e40300e410202d0035808110010013910402d0b411040240042d42c1840c10800f4580d030b492203004e01c10380d2654034103000780742584100d80e85460301821844105071101c28a940440d03807201c0e01d80001e0018000079644d5030701381080c075007541d600454148407100140e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 538614208 1250 538612958 538612973
    0x100c02150702030a1d120d080a0e030301030c18090602040602030903070e070804080325050901021507080c0f1204111309150507020f0f1b0a0503061f030f0602030f010b090d 76
    0x2144250b0000d2030046d0800210500300010265640e040e91841d0483c5050701c0207505035042c410008260744c0c401c3c0300500000c1c0d0382d511004107461640b0f010b800f012030415518805440070f5400600030303e1000401142055020004000d50242a0201c9040175580e0841c101140130444501c0c0000d21a5408100020390795070045800c281e04c1240f10b01c114008101c02005843e0700018580400c8000070b42482658060112242e400f06200c1406091326013101c0c00b4009010040c4007525001000991202c0c8205120a80c0ca040304c00404680c960300c1d151402c00c0e0701010a00c000c9102d03208602d5030700d030300c3da0140c022000600d0b8469000e185204840789050090f14010f001501940502003a120040d201000740c442e00c110481e00500c2c403803c262068144c00c02100e2803450040c207c40d0020b00171600c0c00103000b50007188a1342c1100807511052051000e841d00c942004001c01c1c1c0800b0700c0d9080c810a070300038500610554510008036603a03161884181d04c0740d03d0020342c1042d104a099004102032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 538615458 1250 538614208 538614257
    0x50304060e180a02030109060801090f0204050a0e0a0b0106020115080c010c0206040816050a1d1504110d06033e01140f121620100c02150702030a 64
    0xa050b18100700c803940ba0103000a8030840748804080c0e030200040005000310b009040041c003140e0000c0105900320349811300346240041010380190b449001041c0040100d51145c1c1c864880c190a8500c260f00d00d2400c8004050203109240045d03081881031a0350011400401c0102c80c2c46070018a941d569003001511001d0b800700060b40d1000041c080095200702c240088000488a8aa05607245042008001078141c5030b410035882242600c0c823428042c100314485a401c59105104041400324120005018040e51021a260410082400e10144040e6000749090302c2c80303141c9545118540440303214840080e8442d8081200303040f8102821a90b0329881d00074040e0040c9480c4d100d00e0207540a000e19076100034850080344a0009110400c0020f02d10840c0e00081c0b1202002c110790746105c4002d004421011500004200000704940024410001f500000301d04d401e0a000c076034a1824007a44903001c0351200941c032046000000d80952010003100c44040f8207460b0414284500c640d40c130003607440c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 538616708 1250 538615458 538615487
    0x14070e01151e0315060329060d0c17160905011d220605040c090b1315030c030e0d200304030813080d03060e060d08090405012405040305030406 63
    0x107403a02c00c00480c8401840c46486221910003003110700c41d5040346100d000044c0d2010080501d06030900c05040300510505040b10100c000209400a0407000158140714258014162916000340b42d202d03950451390742810011000023030041a91000c00044440104640c0c0500080303651300244a1036004911003001002c204603000025a680303c045001d083d00700740c0c0d0301e8145440b084940102c1c80c990040c0409080300b96024400c118201d100681550300a0003050400340c0c010450705840c101e09030081c2c00500f40f0001000c9541c00111000c1c0c000c1041203c0d24000904002c2c80c2c4034844000079645030f41043c9666400c07a0f038083c2d1445040c3c0f2903c00e000c038416a0004100010225848001904020345d0400a1880b05481c007a101440c0400342e200390000c1c141800b00800c140300011fa480c60f070160341500c0942c1c5260091500614501c0b89603c00d0354407519060001c01e0124002801c401003050310684001164441c00d4207407a640600d2200501c6a8003c01c0244416031180100804604 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 538617958 1250 538616708 538616717
    0x1050c0c090c0d0617060c0a02100504030314150f040b0a1a0309070501080405030f07031209050f0f0f0a06150f0308030702060601090b0d1d07060c14070e0115 70
    0x516400000c0611000303442d2044200000b1410526007440c91042d01c0080038986a00241c4424409103544c0341e40300100103018060011488075030b414028001000761480070070f01000b4034582860040c0c0104450441311110a02c900300050240c1ca40c0031205510680040a58807000510000c2102821150718050340020b801400014007070b0010000702400320116442a44030f141003c49203240c000141d2001d8104220f0506000100d2404021102d10203c4807448a503134a50b142416205a495501081c03d554900a20103090240c00f00c0c2456010724200140e030104c030a400107040e43e80401d030f072082001e500310500b00c0001803000d51060f01c40c4a480c1028a07c042e03030f1100c0700040c0c65066070041d030b1003100020811010a074144441c0c1d034071007024207041080505010030360005000300c1c29001040b55071200d54202d4000014141c3c0107000c4a03001f11086951030f0100101a0a5403c02c121803800e0503003201d00303003a0b0300450080709413403194030302c140e07941e2a1007283d0381e80c912400106070a00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 538619208 1250 538617958 538617973
    0x3080402090c090d08070b060301063c06050a17010b090d020d08030907060311070c0b09120118020301060906080a151b0c230c010c050102040902210f060d0201050c 72
    0x303403520718101c4e4005001c1c030300c041d4840c1894100f500c49540000c20f403610a0340360a00900c441c00f401d440c0f40d415015540340341026030070191690b81d42003400c031001c19000128a90001582a4444014002080c0f1a0754038160586140d502d0104220203000b1260300d40703400d200c0c01025040036117141010074002031150078400c05a44440c2440c1d402036510400d10f0300483e000303000d955094040c28550005c40080c1c1441c0805a4944030040003190207034061001000540c840700380d65850000203500350a2000304082200100d072188034011051049000b54202500000c6440036449803030111100b44014006207405a510402400c3c0349100703081100c0d646115222814444d1a041009100541c0329148460603605002c00030075090341480c0c1d060300105400c004044004500c84440040c282408050207180d03250650181c0038a401030b0754090310120b08140c0d40c840094801c4c08148101d4001040c68440041481c0d200303e08403891038000301c014403d4401540729900611901c018501a906107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 538620458 1250 538619208 538619227
    0x191d01181a030618060603040809040b090c220302060f07030203040306050c280f11101a0a0506040e06150f0c1c030605031f091205071e03080402090c 66
    0x3094061054500803070408000c012850034007480c858001010012403614620300300e0001078680c400100001e1012074003185510058031a90401e80e900131000701501114034112900580301e80088514007508902814a0100c0c101c03100d54620a4a0b005004546081c5040e49908421391100c90202d085101c10800000403078200c0c861107000e1003401d1141c59807015141007622803101c401c0e596600f00d4040b000e055170044e421440701100d0384102d0a121400e28001d40415041208811507550054241070722154042c09948070060f01c11822680492841d440d1401d00c01d260061380100c417044501c3d035010030420300d807910242c031100221000003458034410312560340050700021a448660b03400711103114020a8424900140440325140400c00360b0303c0c1c00b0000e6914024902c00e0391a012071028a03030100c010039040000007640203245603400e540c3c2e81c00010107681c8968400d48400c40c1d01c1446170301d40d81d120f60006182e41d416941c2d204a40d103c907000c0191b0103d010b4840400f080c02000000c20 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 538621708 1250 538620458 538620479
    0x31404060509210c061b07152003040606060801180b03100f02030906061903031b0606030b10050105030f01150908100b0108090309010f0c050c09010b191d0118 70
    0x1880c203821441e090719980001905031801c80050b224400c80106d442500c0701a251202c29107a005810201401c400a040c2e041c100007403880e401541070003500214440440c104440056000781d1140c1001c01595035a8070080311040d0007801040310800c40194014148820340c1c1222070b03d680010166038a894010b0303040c0048481c0031000c40441c03900881004200c01080c000035a1089080c0e0b034003c3c0b00d8140c40c85554402c5000d004c01810312900031502549040c1c01d82001c03400c80d0340188100490b581380e041c6a01c0c03003c0308585880c90b421100201003055442501901d00402c1c0c802c0740d8440590030089246e04420042450004010800c4400186400300b04008814040783c104006014250b03840010041d00000340702040b0341d03004110f040103690f80a14254401b0920303107003203c0d2100c3c291a107903042c403280c604c0781544055084c00116515070648010040720810084840818605000c01d1300c3c0e1081146101c040c1d910a4202c0119550050280705220300102d4016500c03a511034008c1d24 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 538622958 1250 538621708 538621753
    0x130b1f020721060c030504111c0c1226090d02030a0501060608090d030b060a1404080307050105010509090c0306011a0d110406170906040f0c080d020a060c031404060509 74
    0x282c1140940e07500400d00106106044030340c0d09926081c0400d1800d500c83c448000e41c0701e41e8590041032a0f00b40311004443c0c0d0110342c03040c19070004480015655886101016003070100f0240c540120311001c0120844070024680e46411000a40c5414000140c0801840144813007082c0e030940282903a20740021401c0c8504000b61150f52100d071506d0609405107450072004001c600181f41c540000642d0300c0e07403520144c860321b210f9441c016400404003040300310079004032351200740392340300204504d0704019041d04058107840d0140d03514072a40d602c0326a5107549040c10b401c41509504083c0060183d002c0300040050f115a12120482c54628207000c03100441d9914105030315001d001082c18070109502015500030014202036042c01803d1100d006911160b02034001001c0c0e84039101840c04010209031280d00400001e0306481d11846403580c0a515800ca5544c116909031800c4c1c0d04a45050281c0b0501004e030081070f050000315910f60340e800009080280000403184562041060100e51410141 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 538624208 1250 538622958 538622999
    0xd09021306030303050c0a080a020d06032f0f061204060e0d0903150c02030a030b31060801020406090e090f010c020a030f020102040b1903060b0307030209130b1f0207 73
    0x50050700c2c60038003c0445002801c1d00706290700802051a0403070b802010250040000c00d801a076a02800d000403000b4111944000c10780c02c2c00350b0740040a0300076100d800c0794146d420201c01100554010401491005450315254050130070b1118500450000c021030354058490000010414000b181d00c40c07920360100c035900c001488914040c000c108400d081c052031140b40484c1841071414403c40a9100d0288000100402d680e46a21220682c1e0b0a613135076082e40e504014411015040e0795070005c099000c2d0204904035030521100080c2e0300d00500c02c6404440050780c40c3c00b64142001d445d02d40c0c2400260009540e48103443c80268826401c0c420b0400328001c40c1c005184042c0e070342c5000f604103410301108209691042c081088a03401c00c40c103c032403007044894610118025440181d0050196400c20745d0f22000201c104028250903a00404190300102c0308441e044c0c480b030074140c042d21210003106410858014015180e2000d0b03055007042c81909005491100e52200c1d0584104005001407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 538625458 1250 538624208 538624211
    0xe01080c01021c0801051e150315030c10050f130f080d05070308011a1b0708010f06030c0521010212061f020a03050a050d0e030406030c020307170d090213 68
    0x4450141d81c040240c0c0c0a10601d4042e400c101d1070940c1c00141500b841440303000d001c1d4160710045030801e140720707401c07400c009801400b1685e40d0308a1048906aa04103c410341c00714a200c05030000a07150015500803c04001070020116510020007116039030800880130440c2003080c42025080f00e030000f40c14024001701c040185441d8035041c2105d2030440c040e0849001d100042210301e0201c0d60111007181514402e80101d1980400d90205403554030511640c0c0d11405603030a0b4249000f04089030003022191009c0007441055a8800c41030700310391130f500c00180f81c081140d0041200741407600c000241400d00c44000740b44140202c80103400da13401412b401d0586060b41d01080035620300110800440000c2e001c0c20350304444002c801942d2202c2ca0000501803003004a02540b850348210b00700c071031b030446d10403040c011101d06016003656a0000c2c01500003090410603401c40c1c040c40002991300140c3c2148810025a0304d40100901d658048003003180802c0d11603a1000160b168011070300c1640c00541c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 538626708 1250 538625458 538625473
    0x90a090905070b04030c050d030e21060105100215060307080f060601230711040e07061101061d1506070215030414061b090409021203120c090a060c06060e0108 70
    0x900754205107040e08012400300c024030050001c00d81041d4100f0659034141e481c0365a2201e10b00701501e6407108107004a07400518400c010300c42d10300f980700000c1d200140360100c0b8081e0341c90300d081004890746241c24a0059010301a0703c44012264401070750854405401c0d200b520741c46074202d0b03007850b03c3d140300084a64001c205011841d40d00c001070090003600350312003104080e00011800301c64402d03030134068000d03040c4000c000042e640d01e91020003056201c0c070803204044e9840c90701412074009885a54025480c04000040e519010004c0381d0455074880c5044182d541d59100c030340340c60040061b029808ca6414844070005803600501c1c840845071050a080c6c4130b1400c5c0c0351080894002680c3c80d101038200d201800309419105500d103841444070034180d500c3e51103040c04070303001706040075010754071450900c0103009003d00030004000c840c0042c000b8030620383d900040058607105200e04281c100c040d40c901000042d1142003220703000c40c4602004a010341e90f074038884e810b03900281c1200215420003072 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 538627958 1250 538626708 538626713
    0xd0c0206161a130206040501081005131a06040f0506031306180203190201200c09070e130c0509010c0302010212010303020f070f0b04140d0b0a0b043c02090a0909 71
    0x402542d00604840702c03843d801c20541c0c04100980618803403d418081c400300860043c00b110030a0a001d00b9001d01100b5805020f8544200a0311000069035182140e802e0b410303e031402c00800710340680e000209901071b183d00c0c25040c0b080c1a8001000500403a002205c2040065201c0c011441603404c2900c1e5000760410500416042083c2d941e030b00101401c00700481340050b6000401a208100981107005505c084003030750341d04010784000c0301984044a0001c12001c80c0e003203070160340c040c0f40c2541c0544c041c90400d210300c8111103584200402080c1d09200c070b0700c0203603c40e0389020700580c4030788005801e00d00d1624680d840180203800440140e00502081c0c10308400030440003000344042e01c502e603007040c41c04035865241d03c540e001d00c09100b03060003401e030269181d042031160243e50200d421159450f00e520f51400808154000d00d2103a41401640013943c5a8a8402c11a80c11183e04a0191007100b1441c1621014500030021b4615024400c24101e03079241d04c40704006104800d808148400f003413 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 538629208 1250 538627958 538628003
    0x20d0e01020607120e0f0307060921090b09062224091208090d0809040605101220040905100e04200406031e060b120d0c020616 56
    0x44166045502c4401080307103159000420342c90a807495035001480c12601c005580c2091140112402030b48000500882040503981c03000c410903005a43c4a002d134900d44090041c1d41d1003a002c03100020b07825044c14050a50640014070034007000500080c0341c090403504d07001d403d10342e00152800000c40b40c03104000800d80144101040091001503845003094131402404005240c0a4580c0e81c181f1074003020208034000046824200d0003e210203010140303841d200d170040d8464001e15000d80d00b003035400241d5080c6000c844101712000d84500303980c0d29111050800400003240030304c1c42c44074540409901124210003c201a0220400210341c078a410290300c450400254007010300f0014103400c02012404ea1301080490400400c502001161002c000070090300c05030f0000742200c002000c41003c0281c41d800c64102c4035120b004103100c010410020841c44100340020000290044c405100c20184120000450395100074034035410103284050312604060640b0003111b03050300004c0c02070380c8080c80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 538630458 1250 538629208 538629227
    0x5070b060103020306240c03030907090b0a06120f0f0c050a0815030d08040611040b0d0c090f05221b08010e0402060403240e0718060503060f06010c0c06020d 69
    0x2c1c24150f203503007084000708041c1308202c0c004003540d07041c0c40103c1c94040324100c00c0310078035003a1a0449880c1c1c00c107540c4041d2a4203e0384126403100d4034141008019041c201c1c030000803661151070b29005d070109480b00740c010385005241e001035241e0322642e20f45680d8035032241c200e282d184e550703a050f2207281020000c0c080b01c4024010391580c80034075411010a40e40084c80c04404500307458940e14988542c81c0400141007940303858a64294003040c08502452940041c01c00300060301c0050119400800080c2d904048500580d1000000000d00384043d0401c090b502620502e2410309a581d000004e00300c42c100c0b0b014424408107196400000c0c01c0c1e26074030000d2030340545861000c3c0107082c142a13000032510301c25880014000c1c98128141c01880b24101400100886840010b201e50741c029040c00e501c07401c140c0102d28458500e00300c0c0b810000207902c5240305a8401074004d01c11500d515180940482000305020b04102408007520009010f4071480c800411054009084100c0c603608080d202415 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 538631708 1250 538630458 538630471
    0x109150209130524061306120c0f081b1c050124080f070c080703020607020d0207050a031104020405060c1f0e0a06050c0d020c07090f06030507060503100e0705070b 72
    0x1c3ca801d00140e00341000401d020604d41c810400560f1300790b030020403814001c54011019080c102500041ca66800410070807180c80d155104005904824a007951542c118181c20000071300d50300009007a0459411000c011000c8000c1ca460030901c0d0440407401c902e00b100c0d0702840071078651004200003508034000030070b810719000d20152100e181d410002d14105000b040f400a1440e90008138225600a8030070703100b400d03088019280c1c1c0d1501800e010790b841d01d09950749801803203a001f40c4008030b803010410600b5031703d00402c610010751440d10350f104c5251140c950750b58060b9003004006030b65036880c0e000b045228100e1016004c0301c81185007400d01c1d03c0107900c0910282e418942c0c1e100005070b000c200d100600f0360003900040c1c00c0c1c0b2640704960690044511054105e4800941380400b45000a00b40b011183ca15230244508611500c0250640b540da100c01001580891018040b0350300443c061a807011110001c010980d6950808481c011015149030004c2800022410140301030f003411242c0c00710 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 538632958 1250 538631708 538631711
    0xc010e1c0305041703010308070c0e16032c070305010c1403010b070c0911040801181211031e1206010c0510180b0106080612070f05060a02010915020913 67
    0x8180000e203048280004444000c1540d81c2c400074040162881c0d9160390490844d90b80c0740c6030760b140d240101280d44030450549252485110004000a050410710700c18442c0340d5103400e08640c0444140c020b00250200003452801d20480345440c0e99640303404c03212039440040101401855410024211142a40498104045140301c2c44000d100031007240d046403203411b500756030b034400b83c02d00211201b083c2e00b00c44901d9007041c03d110203450f03601014000b5541c040c4000c1182c0e250b0031065040b90584135800418050307010003202c03c180c2c040c0c10038408240064081e81c3c9415500f401e1803200d0618140b1411460101027942d0306110341e107030001d0364011003e003409091021141c0b200742e50b400c0c0912803a1845921000c034009018410100e003801558800107002c12540c4030f00001e041c0000c2111741502030841e42d4241c220b0068009a07200072541140324880e0070909010511803943e10160034401950b480d07540d000000341400507681c00c5c0d11440c1800507103a5000f0320800100e0780c120164141342a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 538634208 1250 538632958 538632973
    0x5100e0703061a210426030411040c1701030b0406060503030315040c020c0d0f05060f070507020f060c160609090b03100c110709020c1513030c02010909020f0c010e 72
    0x1c990f4580380d02125200070001c10313140c0a40020b142c607004000c0c0100001c0d036030100d00340010800c2031301c950303c44010b2084807451303080364840340044e00740011507010f4214400c011080640f410241c5c8075204170081c0b4a001c501400c44000c280d15038400030b0b441210000101c900f00018043d00d84034450141c00100c000d50714504240c61245822840c40f20802e12856459543d510128000c21044801110150070755545009905102000e4020280152a24010a00011203030200c00c420781d44942c08a803035803410000b458082c80070410b01001501d410400c100030340780455100700241c0000d21000201c90380401e007030590040000010b0342c40450301ca070401c8034140003590041840700741c52085c1c005c0090886240107003281c45030988902203061f4002c01c1c0b804a0001501d40051464a1110003140c0024580250342a0010380494004404140c180f548000092103851080821801450312902d16038031003180740b01700d034003060800c000c1e031800140880d051807081c0580b100d00381a41002d400e50 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 538635458 1250 538634208 538634219
    0x90f0f0317061003050903090406030602220f090504030e09091c02161a070206041e0609031104020319020c160f0305190c0e01030b06130c02030a0302090103090605100e070306 77
    0x40520360070110281178a803000507500040410654000c414010018002550349040500095200d440ca120407045500828087c400404401c641103480340c0221100c42e0340780c00310070001400c0c0600200c042000c03240e01d907419a81e40c041c205000d00c41100140c140640c4100081400b400100203031400c3d50400d155100c84286442c0c107210440321030b41c4d203402e882c034560f68445442e84288034000394400c1011030041900ca040640480850794010a500081d40c1c80b840c003551250050b100080134a22210b4802d2610b05094000d1504a04607400703040048103000803040c1a40c00c810b50b140304a40c0648250480382550440b810001c014030148034a035581140c40e80e0313482e40307407aa4102d51200b081d45404d80800603045003480c014094080f5800072940c4074a014001030a055580c3c074030601406240f00d4811035984a03000c2d100c441030300114542540e11009030043d40100c801981810707613074281080413400c0c9026051140110404841f0f440d8149107102d190088090404000c05182c003806100c0e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 538636708 1250 538635458 538635469
    0x10302011b05120a020703150908090121050109021309020309150915090606041d06010e070c0c12020411070f0b1008012a0e0a120501090f0f031706 65
    0x210303800707400190710403160307507003411407070800c490182c01e03041d020000e484059640c1c003082003400c2c0c92240d040c641e4045620f16400b4103076007800340c0107031400700b0800610950398028680004003104c004460740d00c2042c0e1404000865109074480581c082d0000341031a5200015142c1d000a400207010841c04c60800052203a51400705c030a4001c0c245243d500815500c1c081000741400ea01c1242c01ca9000900d030104000303880e5003041d5072080c000c504210980c1c1c035a201460012240b140114003d01e6140e00e0800c80d10505000540501c080c00b140000170f00c0415108503c01d006400c08031200340e007080c040d00c18001160306010300b48180720f5040c4216030000c0d030074410303940c21140c001c0c000900390b8907802c0c1846d0f8001c00f943d100c8036080d0720f40016040760002d030421001c1c2c10551100307040f03041a01300b10203039800a507038020f85510030700c40c1d841881080d41e00c0514951442c015000040c40100d07954804450700484607050715950b01ea0041501003590080d1290110420000d401b00541403004c080754 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 538637958 1250 538636708 538636727
    0x2070e07050a0921022e080705031f0503010e0a02090606120f04170c0c010905190b0f07050a0309090605030106030213180b0c130e0f04170702041401170601030201 72
    0x40400c0301000d4440c4e00313040d2180c00356040398000340524a42501c0d51992000700032408028080821600000d000c0d6900690006100300d2003500c2d11032444d80ca43e5111102032400c103e0035850203091000215958900744140304811400400404012600c0e004102907034100070700c032a200300b408201f10a040d4040d00d146541240000110f0821a00c551a110340804245400c0441c0d5141c0420816881c00300050400850002a201c045516032510288281c100190401101c1191300c0e840402a82440c80000c1504a5030043c2c51800c0241a644103420180104001d4002542c844400d010030010351040c50014241100204100340c95030303000c117450541c801030740401e04e42c0d00d80c0a000c1d90f0717084034080140790707601c0b04081d444d40c98061100d03545070300015840b8510303035410380e00407a0105590131018080c241d42540884070766100d40c2d070401440e0011450f101070190521030400141c580d40070f4004000f01c0d40c42482d06940c107106505411500c0410040c120358050b500410250340c0015440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 538639208 1250 538637958 538637969
    0x120c0b07110d291915170f0d02010605090a09050a02010c0f02181501030509070e060d0602040602030304060b10141308150f10030b0a020703140a02070e07050a09 71
    0x42c02182941c1008560402c0c50310082c4024011a00b09000701c1d90840c40f654402c0c064010540321050000c501d900032034100f00300c0c0d07684894140d1418010601e0300d003400c4402e0200d64049524182a101c0024180075080d03a4400c0507130344441060055150007940140c0c01a1007400402410045407281c0356101c10084c40170f03050000ba82825014008101050740d840c1e90054100e4042c5003c0e07504070035a00c0011100c5080440809071404501d601c2230041034001da83d0600100313116410000c01e424884e030080e0a1540c01303852420450005400c40c005440248101d8000d182c40380780c036040c1803080c3c8890703d01c058882c00040322081e60042d005000d0310303082203500c100d0a8503600004800e1840c0310040d00006a91b10507100707011040307104800a02e100304104519200c2980301d818000360701c560980401441c090100002604100895000e020b05a010317182180380141100725880c81a4000b5038007a006810400040c40710131440740c03026403c03122514149142424210004002c4076a60050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 538640458 1250 538639208 538639219
    0x9030c030a0e011e0c030206070e0a14030a140606030709020f030f060105090a0b0d0b0307050904060e0316030e03060106050f0d0908040801110c010b01020a0f020f01021204120c0b0711 81
    0x1c401591003080081c4c0340100c100e50310a40c030708540c68060980520504124010320070741e0001128248913403003071421500058040990300c0d0904101e4922411380044550300b520841d880c0714080b43c00050f814014104103001b804031410720605150401105030030a040710390040002d500350084820469502c042d00b20f81500e195260b05004071005d10075040d0083e4400d42c800d1011030301c90094002404040b00c1c2080800400c040c4600303041c1c940c1054880e00754000e490f0f47c0001d0101c1c2480d002880585c0e0404280c0b4600410b40e03c55007502801c10609800103142c1414040160a0070050a8090f0a0f5401c0282c141125868200411300ca8483c3d206209601c40e0054003c00c8030000c2502c0c09407c00f10b0090005442030b450840940d0407490001500c0c2d800d14440c640c05500101e1903111181c0c2140d11404442c2d041e401f0b02a00034032281016045106030340300304000310710320b202400180c801e40000c03080c60390b03007400d200108031520713008040c9101c4100000c00c0020b07610001e030344407000c0a0b80d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 538641708 1250 538640458 538640477
    0x10c170709081f0501150203040b1b0312090f0106080705061308030c012a2f07030b07090509061003090c0b0c070f090203190f0605030114040b09030c030a 68
    0x30304a4101200740c0c0070040070300c201101c0c520310320648280b24500312100b076410001a030740c4043d0f079074290680c2d00855026800030403081c407008181c44014426221080301403051208201591b5103143c0c00103040240f480048014002051400d001d102000b401e460024080e05052458003a2039040c2c40c401d00f07209010001d490202030009621200040520ba02942d03158028080d440e07029041e880c1580c0e04022800340304d100500d584c02c0f4420035401a80d40c50240081c3d51030f0400050401c0c0c00020744070088200311500001c901003051802862260541e00c0c81030400800c050000000e90f04a40e110711101400c00c44940c49032000d201e40b0708017034900480d0103031842c1041e03043e0000941114110410008400710007880c0041d19008035001812441c242507540c101100c100e0100b1344000c10641c3d00c403041b240c03d9003050740060800f5581c81d0000100b081d51040020308561441d540d440143d080c1c601080288012807080b00e070b0050192010310328106103004080d40728821807a80342d0501042c2c15 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 538642958 1250 538641708 538641721
    0x71b05070b0a030e030316080f0403021c0507060c0906080a090f08130f08030405090109020a0c0201110304050d11030c1f2304091a0f1005091305010f060f02010c17 72
    0x40001d5100f100139000e482e0380e4100399065203d901c4000321403102040d0a100464051485c13001003500c500d8156010b400c0c02e2580e0241240d480004e0800203080007803e100280108041d1310400480540503215054a280f4003000075103030981c01000790003420300d05481000402c0c1c9194800261550161400c1c1d543e03040760003243e034075002c01c0e0481c078210500c3c8440402d10940c00002001a5041101d4045c0c0b181e0340e8400c0c0340c1c180d1151440c07110020302903251040c01940156104000d6034a0642581d08054691000c50044400f00c0000c2c3c502681354012410075003018400755014003c29618900780c16044c02c00d2540b1695401c411a0410a007446000f1904506100c0780886000d1000047c0e946d40ea56403112000d0202030030284e17007810301c3d102c40c0c082600c0d0102103040ca001d0080c1882030204044030080e11990084038945070400450640c002c11528688030320303406010418141c00b4100d0800c1e000030000c8004254010641e89045465407440760050240500040c4040320044a9034926 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 538644208 1250 538642958 538642961
    0x603010f020f090906131b1b0309060c05010e120a1d01050301050108090a0204050c0304021c0c05060f13060306030b010b030c03010905040204020c0a12030c0219120504031703071b05070b0a03 84
    0x1b03070904031205103445920202d40d21100b007082c1007001d407556050449015030040c0d000c1c412140b00014040f5100341c1042040724020341d2205201800b500000401000000b0082d050100800c042c1021140c00562101d15503000020800d006803003907010640e440c0030100107000e51106001d804d05000b600000240a5001001845c05803076000d40148140d081512a400007500142c40491054001d1001950b003045980c2c2c1c18107425070480c02c6070b9905450b0100784411903010298407686010100074400032aa942007142c0000c2415940000b00b4074654140011020b0042c0c204c048404800c00a002c492040305c2c040c1c03410f44001c404000394a880301d1002a001303118007840240c0d203004240304d030801c0c00411040c10014880d07a40f81448020700d8484101e0300c441520307034a03003096102003c020300800c800400b01c94024402c0d007001072074107890340c4642d40001026014984000000400c000c5001d900c40d8180c60000b00c0305209043c44401c940c1c0b44c03500e840c1603004070308170200041001d01c01d16119 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 538645458 1250 538644208 538644229
    0x612010221010e0402010c060e07091119080f0c28081801060303020303041e0f0b150402030606070213060918060605030a03020607140d0608060603010f020f090906 72
    0x100215036550004444140d5074914031001000c001e001c60000400c9102425050710944c3c0c140d403242c0c0c0c8249140c0e5450000c102003940c2200a00c0b41c1d003000710301410144220801200c2c1c00007000d8036584182155003d6074040c0501500300510714050007482e0f9064000c0320b421044580c1d403030740c031131000303002c00c11404110f80e02d5529000b05c80c080320201140c1117103541c2d0040400710000045000360340142400d9404520006005070300400c00107011440c0743e010f154824918021140326001551924401d00100040030b403a6001040e003404a07a10084130840701e0380c201920f0075070541c50104d0010f8824080c1e40e0001c5e010b0716040a40d071260070308591003c00540354050b000c01528821980300c10b03500c00303910400c80303540707241003404a103074580040c1c40031000d545540100b10030380c5c95900c12189080c1c0341e000c2201c0c841080c000b064503000c5a0103500b020b4258440100607914001e420142500c0c60054501c0c911071040007175101001d40300b0304540581401f5a103904503030300c81d0004241003100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 538646708 1250 538645458 538645489
    0x1e150619060c0c0602030307022d061f0e04020d06020d0f1b140301030b01030807080409021c0b0108070503010b090d050f0c010f080606070201030b0d0f030306050a0914070806 77
    0xc550001190031030700150a1419640100a4001a251070b008143c1c1e41c0d200036a003410142c2e21030003c9101a294000c0408103a01d590f4084100d50542119014900013040d101d400e011072207500e082e9061303030082c1c904074001d018000285a46040c9070b00411103000e5117030b402901054000624a000780d2198100e20900d8003144810803004a03622344014800c255980490000380c0000007000d644aa070f0001d590507a0b0300040390040c4c13a4a5680c03075144962100c034007294011001c0c0400211407240b4405041d020b9404120721705140340c1d1003602000c80e01403040305414003260074180040181e2040a5a054801c1030480036034030880000060382c0340000103002170041c4a02ca001e8030320307a00d011a82a1441c10300ba200d401c0801c41982e4107444903501119542d4104a05000318800b540c40713504101c44d0044040c1003402050595181e03c550b8168424058001c651121000c00590070b04081c03c0d4001c1040d400200400c3e0912412294404809001038040050510210b016a40c0c4c070010282c2111 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 538647958 1250 538646708 538646749
    0xc070312020708030418020a02070906030803010e061206040615032906060301080c100c0b0f180a0f20091623070f0602090307080705031e1506 63
    0x568034580304480305030034600000107009000740003408050002c199801d6410320b2600030074a10800184000030340101c00701808610480400190302e200340e105d908091401012007035a60340c101030140071030300c030054055400f9820742201d0404801c2c01040041d08181d09c080c011480b9030280c810381801600d04c0e080034103a201c10030b01d10b42d80115440714000a03401c644c4002111940e42c0001c0001c81e000c00d00c29400103401c11070f840203407031074440d00300481031001d0b003001d9240030305680740e00c90311050461340ca601d101c21175803c0c00700c1d260070030088203600c50311040245018105541d0302c0d40d01e4280c540006054160f268041410580c1c140c00d800034446015050801903e4000216150401c200d880c04002ca1035000300104110380d5901c0c01c803103025021a0341858068160f807058044201c0312030507154607078240282d085541d0140800c80041c04901e00a0155a082604060508016140068141c0c0038001107416411000c00c4081005000c084070941582e0741601080301c8800400010364040d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 538649208 1250 538647958 538647973
    0xe0f030c0f061905090a060207060909021324110106050d080c03040e0403120b0a030b07050a140409020913090b07080703090204090320010c12020d060b0d0903120b09060409080c 78
    0x3c50380400074201d00f0408458400a10381d0700c400990310358405004810014405030010301000c00e242d00140348400b060317003500100c0b81d0394500c414410314282c071000021075080021464440e0b80015a400b0301c0c0380e100c008028041c42c00c1c000502c18003d041f070050200d01c010079440340302102482a2070080584082100d80e9250528005000f40f0104c180c0400d5a4a043e500202901b0038441c2c4c50140d035489618880c481d2030b403000586158200d0321000d4204070389003002c010120103c102800051015940258075004410b003001210400500e180d04164a400ea01001042c0105003507034005119041402254030340103012000744c001e5090103904181400c1e180c500b095030010036040798941c2111110100883c1c030321000c1c240e48180c038610b03000a1481c0090142647d465004001c2c0c83c0c0a11800106942e07104603030001500320b2084d0070062642c80d50b4030301c240f40e000411814071403c000002c024058001c0001030b1003800180090340115659904030007004100c1c0c080303600c1851210200c0d901c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 538650458 1250 538649208 538649257
    0x708030d09050d030207083708090f1906112b050c1206040c170f0108010605030d0f030902040b040e010606140403051e2401060e0f030c0f06 62
    0x29001a40c8221a14440d120181240510900c00c1c0d03208280e00c0f0914902d0700903c00c4001c0a541c06170ba040c41088c80c0c1000c0c0d0000c041a136000d803060526900c0d210852540741150110b8141081c1c000c001c03100d0b800107411719102091400c0b402c440990301080c00190100c0d41d8011048502450803e036455060000800003903601910090141e40c14081052140d0742e035151300703501940611b012142101c409480030440300d00c0e00c0c5d0024407400000c3d1604c5d03940f03881040171100c0850002e442903d0380c543c0580c01884801e00a015a00240100303400920f4000e0000e10000d000341007010b400c200709036541c2240401c541d07851700501c0c1003440041050014004154a0900070030f040c5c415240810740c0c0742c50540640c0314610541c0c0c100d9400c05c0c06014070090060b10411868801603400c0118042c440b904041e840308040c0401e20b40c0d203082d10002d46907040c200060020a00021403500c1007502e1024040540d47c0010b84000c2a0b40c103943e010026042d000c08103409010f4017500c0c43d419003458081107030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 538651708 1250 538650458 538650461
    0x18010902012c090c090a1203050306040f0e01090812010503060c190302091e0a141302210108062a0d0b0f102c03030331080c2104170708030d 62
    0x410310006c45d100405242e544500030300ca162900c100402140052001490780c2c909903004030184000300710041a4204090f18540c219540c5050031680c208022454442000842d0040c85c09003505500501250800321111010350181c1010784040e282c1c5102e40d100990301c660181e03a041d0901500c1c101c0e4500311540010f43c2a1038840c01b05004101d90baa0005074004500d0310880c0b0a03101610f40c3e2403c0c0520132085010307601400100458030001400000100d2080550500034003108018260710705004d66815044001c0c030864006076598090324a548543d9902200d5020400e440c00042c901804404144400750340b8000c81d60241039440e10f01c071202d400a194802c0c1c0ca041c00240480f0014901c071111055406503284d50b050b620900c00a0002c00703818180e038002128038011680d442d112092005d0180b8001001220601400300b100380030035404100b10b030850081c9208a28128540e02d503090000c0c069403060700b012407066885090308800c20301c490700203170481000350b035921060821840c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 538652958 1250 538651708 538651717
    0x904141006180603021c020f09041209120201122a1e0201140601030216060203010b1e0a14090103060806180f030a050423130518010902012c090c 64
    0x42c0002d01d515007503101900d940c800c0c0c00c00d80354018002c81c0308040654000c0c41c81e0129800403030b0443c0c075070002d1031800d6135108440c510851050120301101381e540c0400520134119a409080e20385158440800140c3e0016409000c00504200004030041041711114482c039008509000c80387c0d59030a02d108450388940e201e451040724040d841c507268001d6100b2402c031080703007030024244a80f00303010481c0c0e58400d40042c400104d08600703034140642e0585490302241d00a038400c2104070f00019608078005a102010f0920b18507203440d8078209004007202070000e1a0071010040c540c140043c1d0a600da0b03011354000000780c8802822603e8520b00294515039504403039459019601c20300310410890302000049071101780d030903503a4038201442c2c00784010404001000d50290545444410b0000d81c58100e000e40b40140a280c0c046054100360b560840c8001b00a50413040716410700c0351400150344c00100400d9403a16802c0703d000c5800e680200c2c80e1507160b014403003650010b0300605100c0694480400390 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 538654208 1250 538652958 538652969
    0x1b2406010e0d060b1e0915060712030903020c0108040b06150c07090614030102042612030703090611130b03040609050109030507030230070f0c061d100c020904141006 73
    0x3c45c5c1558000e03180640700301c03800c550950b000313054000164050703900203008800b03207402403c3e007030400d00e6a0fa1001140000c2a0720340002030b5a41d040e010a044c2d04108107405200f007801c04903042d0901c0c2d114504004001400709001e030041c120740c1c1000183c50380460b2600310150007691080c0f521001120007401c814825820906c1c01001c4c020b50a103018400c95084030007100c2052122400c208400030f0301d012030723542d241041c010503070060a01802ca50055205003140e0703500280c450711034a0606c0807074800641c2603201e848144203602001c13001c0346111007581c20407101280c40c0c0da2185045005040341038401000303942400303104001c05400c40040c0000d94426000d55261000400407501d0b0301c10356a41d1540c0c461101200c4031102a4a140145215401043e2541540c0324984440f030f11461154001000140d100c2d0700070b850004000c6800940b95000c903410205407803000002456030262481c06445100014041001c106001c3d0141e5548081c0d60159190381c44918400c1c0020111841003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 538655458 1250 538654208 538654219
    0xc0a03060509060603011505070b04060605040e01110406120908041508070302032802130b043003140d1b090e09060f100e0405031b2406010e0d060b 65
    0x10540c0d02d0700e208903c0c8a0b03d40030300103500b5680781421105c0500d140d5000303a01888000c00401012070f01c2c10b10701500c201c0c0100d070f001c039046d4980410f00084400841c00303160300d64542046401003082c0c0700c044804550840c9820f982c9414000c07050707001880c0c2d040c03006104803000100040c2c4810f0030595010400e0b140d48822100d540e03615416000e07440f048521000c4070076032540c0c036a403420320010341c01d0b020302d14000c1c01400d0401244005103440f40c43e030000c1c0036030030010504000140c1441e21f01c103001600e0303091010580801203d60f45039922810b81c01000d03c45200302c00c42942c444e80c0161004005042020301c0410b404002600398444408401c2c1c1c0003641c5842c1c0494005050501e1303600880042c00100034564400d03194a1080e0000791400c0b0710701d4002c001c0068240100f44025004a0140c4040c640c1e5800d000015041c2c0c7c0c85d03000c40f00026030010010520401e462441c0701104000d080c4900c1d0b840da961200403103880c00028645d0754071040c0d4240000c2840925400f540720064180c60 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 538656708 1250 538655458 538655471
    0xe0409061a0904080301032d0303050114031203060402090d020a0b0a0305011a07060506061e0c0d03060b160201030902040501031a10051e0a05030a051501090606050f0c0a0602030c0a03 81
    0x2030004442040f1000380c02844200b0041000035004040819000b116105a252414540030700c99560341d0071000940c0020b4942c3e0040c0682d00c0b0204902c0b410700070841c028815840d2650116015000040c02244202c2e03000c65001e04944030710300c01035421613004003692942512031952841c15007100fa850000285450000319203400c0700605101415500c14003282003013070540e51200502801000990002e0091043c0035588806040c042d150700f0902c00074545407285903409510300f80884030070400305814100e04003c0540d800d422101078042c5950105080641c07400140d010300b0441000030f4101c0d2030b05000100340131100c05598612011a000c12030180c031444030340e4400030144d005840d4000705224000d0180c05507141074110081002d0410000642c1d244000303800c12440041c1a92a40c0140c000d07408912000c84404d8003401c55080204031a0381000305c000d1040c05540300510351864009090202e0120401a024805900c2442559a807400c101811800d41004580c10042030815a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 538657958 1250 538656708 538656761
    0x210050603070b0f22120807060603020301020d0207170427060e0f0105010210050411010507050111040e090d090f120602090d03020c01030b0306060f04091e03030b0f030c0907030c0e040906 83
    0x91712002140c1c1030b05425440314046403502d80c09036100d031900715015940d51100000580303080c0003826110901640040c0c90304100d0405024003248a4000b502e83c003002c100600180e1042080c1c034454101d50900e0b000241c002e40903100080c8002d4110809815001d41004045052110342c40c5c180e07442a401d448440b0510403028083d254240c0d00200030b10901603206c0c4207948501c0107084118000c00000c40c94449181c2000d504da4015008401c4880340746040103107401c41004042c80745401450203032440e030304e404501e12003d1030901842103511445a594014008680c064507a01c050007410441c1017013462901039503c09400c44414042403c060001180e4500440e165202d468040c150722800c1404200f0032005141d51402201e420145840b00100040b1200042d420a032003609d002400c102d42400f04100b90b83c1203205507100e54424120310030b13140c983c425481d030071503002c2c01c0100306084801025030b8006054040c4581003841c00395030100780f240a4000c00c0d01c84007210145180e03685401d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 538659208 1250 538657958 538658017
    0x1006061715120717011a0307080c0405130209090604030201061a16030201060e0106080108010b040e0c0d051e06010e0610051b070302060301121a070210050603070b0f 73
    0x11648556600341840d05000c05080c0b820752240000b42d02e0040d14a90381c3c4400e03241002200c002c458080ca07a550b141480950125904000280c0004400402c01280740c000c03000d503551800f042660013a03403520049442e008103c03c0c04400c4a82c001d04080c0c251900d54042aa034941c2114264010b40c2801e80000c1c00b441107629200140e403507403d4680c0f0340460340c0301030120000c580104404540d44c8800002e8210b180a440602900c02c507075810342e45501d480682800e407400405d00706d10a51500a0341c0d01188000901b11142e4902651303224800c0c1000e08081e42400724104001c02e840c400070a04003412440441c969050380d580c03d1305a40e06440707920500c440c203c00214480d0210390208132150100c080c00800c00000003224044452594403030340440e0003504203a000b00108800d0071321803010402114010181100c89038100c070039526041400968032a9103209900320690f1f11404101152020700802001d404421055035803802400308002c2180d008000c4000441c0800c0c40e2900300340c100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 538660458 1250 538659208 538659211
    0x2030309010b06090f0d0821041505010b0307261512070602070e09010f09080d0e010c14091309050d020d090503030708090d0203010e01020904060e09072610060617 72
    0x1d010003104204172818030440480c41c61085e52503c0e805d1117800c42542200b111100c003040b60002c00a00c0d030500303160589007041c1b840400100c031402d050040c080510b000301a03030740c4441503140c40d140c1c0d5480b00440030409006064010390b085604410080303142040001c3c0401c00b042580c840c61080001c100c625182d4000740549001600420410442c80301040d004030f07000107204000044460790b8241b25022541d181104a8842e0400b1510107141c5603184900096a16074a000f0301201844600007403860860144202c1403a001044100981d00c0b040c4000c4032500d5101d6040043e04410b080240d42d4042c50032540300117101d05010496203074410000c24040302c03000340085092180079a03506c24140c201040203900040b2110001d4003603503090003091450f004c0301c000182d482500c1d405000030303203103113400542a030802e82d0700f40410000001078000c211044070960754a0232881e0b901000655140343c6100300180708480c4800252602580a03404031269070310381141e040d6020f114030116010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 538661708 1250 538660458 538660477
    0x702010c180b03070c1e030e1302030f071407050105040c14060a050d0f091a01060f0e0a140103151d0a05130f0516080c0901080304030b04170906040602030309010b06 73
    0x420f002145205028030388030016188100d04210f02031040702000100000844001e5001030f0507615040b001d0b003004411840140800305040d451444d000c00703414018013000d4048410000308a01c00d6445241003000d4070341907907001d0000d100c0d5003042e060040902e6014000c00080400389514a41c00c1d241140441e652088685c40d1942410350f400c0089006000b20305032100e449803581c198000090025151003c43c40081040041d1541000d00003401c990460038420140001550600031558443c000300702216070b041e580024420400004802400d0f000c550305505421010000c62581001c81e00c44020f00503041c103030705840e6600c4c40e18100350740c41a9948400b0004000042001c2074110303951070440b40c0a40110307103110f101c042070020034070401c1c0d0000703846400411a080311858001446801845e2100046080904588030000070784c0000d80b00404800500c2e4a4201c1907003000152007101400a020740e45890b541c81c0003944030307401101c1880c020f5103000c0e0341c90031501d060401d5624140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 538662958 1250 538661708 538661729
    0x709051e0907030609020d06110307020714180411060408031c05041106031305100b1c0c15020c040606090806130b0a110c0a061b020607081501050c060702010c18 71
    0x51458071382000500c0d440205903040780c440b0040342d011909a00410703000402240600303559180a01000303040041e29040011070190030403070311049940d5010008581c05003410203402c551610f242c00028180e502000c00c0d0401008138001071400c1001c00a01141320310703401c4ac0400c0448050851003143c10458008012101080101c5000d08048000d50350188207000010315030b1156444e55440d15503800280c031441d81e11801c0912407410084010b40028104520305052002c86a075100c829903d90700404407804502802c0030401c503c2000181c0024101400800c51542c039488010104035060150041c981f28407000710314040d0440022101d01c4c3e402810f041c0198580c05651800b61100484413040c1f90010720100508103070520403550918802d000c0042c0b00c2c140c482007050070035a41103450f800c3d90410380812000e26004000150712202d201c04d60132220215400590303841c05000c2e10060940310700420040350a07015840054140d50b540c42d00104501d054000d030038800c00300c0c0500001c02 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 538664208 1250 538662958 538662973
    0x3070f03020a020f0a0b0603010f0218010c0f0c0605031b0703171509090a110105030c030103030305060d15140c0703020304090506041404060603020112140f10080709051e09 76
    0x21446603001c0c14941510748195020030794a0b19000e032a104600c0d02c2603419040040c03d0120615003442018041c42000c01c2c10750600e610b0200480c401d56507030310000d040c403400d109210208840262445022079014110a0703003903440d800010001c3d0400c95203615024005141e040c1d0701d5401b041601d02407541562074160354803040841302d0f00c8840c060300031515040550031074601aaa800e415600c1410858000c29640d000341c02c203181040c0c000c0000310f0512400304113100c8a00c1c0b01d001140d0543c2d40500700403544e6102c40300441c0e00d005103204054104940146d219a6040258200c1000d4201e116044034907501e0b0000c0e0002035106981005002da40300304000c0180e000540c00c00c039803200000b880002c2c041c4140c00c2c480880a001c40c0c040700c2607965400b00b0b1003150f0700448015001250755600300031802e0f000c4000750040d4070181c0324062664128000588444004011102803c40e00083c1e4280c07913030340d10011001c0c1c00700741da10308113840b282020004180041c0c4400c5210310300c40401480003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 538665458 1250 538664208 538664237
    0x120c041d060412020f030a05130603020a080406050c040504090602031527060f0a17010533151605250501261e06100212181005040305120307 62
    0x1107104030342a19042d0701032106402c080d441c050015040d00d87d1292104c69075407049203d05c18407403440d0b800107020b061051003000c1e5084d502810050b1311903441040010740d9150002c02074900e0169a001c55400f5041124140070420903401542c0550309000040c8803002e440b400b0802000114601030007600307007950724041240c040d1a04141c10150142ca0000c1d888218004200c440d4001d4015007910782020f4040592070000f4031410341d0002091103110b12080302580121910155450600503614100c01418041d0340c1d451f00d041a089490100c0f070f980c4140214042c0035244c18603800395414081c0116040d10b0346000a400301001710400554644141000c0c01518807008581c0c18500343c00c0d05c070250201c14145c042005014001c111411040860201075101c1500c00c02032050780180f002800c4040026000a5200d511601841c69291510003c0b500b200382603070074042d11a80f080c4803420041449810000400541e40944140d884206d00a040c082080c402528500002414060748150 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 538666708 1250 538665458 538665473
    0x7030207020103090c030602120c0c1f3c0e15070903080d141501090311060705061801141015121a030c030c060d0515120c041d0604 58
    0x1180344141000601d000494031444405c1c5c14580044490aa0014441418022640000d0b0388107852402862070050b0601400c0c0d00c401070b94110104081c2200d80c040421074603030b0800340d040b45007007a204031042c0c48000300502c1c0c1c010b83d14002c8a0100314611101c0c00e07200c00d002e4415040d030124010300600085050700c1c3c21000d8003d040e1020000c2541e0040002410200104000c0c0300c50480070840040303824007045400805441d01c501c07003801d500551800d9801515003011250844820f01c1028440e0020803402d108504005186000b680100464541e000304001d4070703526108001c0201c0501310348840700700c50301a070f000540488600400c21020802c140d81d040108081d203800d901d0402c04100c004203444082140c0d10074800c245628904500302088500548003045004007210541c07180031034414410a05100038498950001415060030200c5405140101400c0414100d1100c81c1c0031303481d000c10310552846182000e2407140712140b42440084000c484001806403601e945d0303103448 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 538667958 1250 538666708 538666717
    0x917090105120a15120b070807140705011406040204030206071403090d050a0210020105161407020307080a1707170705010b2107080f030a0f14030a06031101090509070302 75
    0x241084020005002c07006542c410075800b8950002000c02d50900144041c20107001d80d0300071752018884c1d900e104000c1419440394036002015410408141c1d00d99a0080b504007002000114003401d0009954003001015401000c03182e101c03484441440d10f139401000140d109920020b58005000e120307540c0865080310900d80d1105802084900e0078000c5000700d08008255a02956550480d907019000d500340842d101604640920080050740f03080d03450080351400090091007048880103041d650420268102d44540c2d400508039500036a076240e495075504161801211045040b6002c071911240107425030ba206540400c8080d0704a45038034003040c49411102c400e6a046d9250540c00c0600d84035140d10024400c844411500f081140c003040a1810949031320442c4240e1012405840c0c055000c030684e800040b6038a071081807540070b43c000319000e6040c02500030720100c0000038040b0380081ca0f40007401f124440c1041c0e803100c000040046d00c080c04140309164010501000081000d0711990003403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 538669064 1106 538667958 538667977
    0x2a0316081006030b011403100807080319030c170a051b12010339060906030c02070b030c0f160506090f0c04020f04090912120917 57
    0x1103101e06158441d0000301540c0350b03100d40c0142e119a219188030101010300d651203003069001c0184e850900c4c440c0c2c14240c89030030310020305078802106440c00390320104131000310200c040100ba0301408218245200300604180e001c1d04ea030902034100350090040c0b4000289a142c80c00106c50f100d8214030301d00302c0c100c1c0148136a01078080c0001c2200e05585c2d220410110382010020895020880c003880d0000a103141c084000075010804481000c81c0c45554030b141c1441d50318441501100c02120b80d190050b0000b04043c0604440c00d001940c000f16800c00880c904811410f0265680d00107000e400b400900038a403007024803034104903c9812084000180086040c587c444c140d40d954070a80c0907010b0350700484c691743d2101e07111094074000c01d45c91406028485007480d10134201c8160340142000b1030b0a40c140a00510030074400c1d0112540e02c8410403004500100c01c0e011150081c0192 = true := by decide +kernel

theorem cover : BRFrame.Cov 538489208 538669064 := by
  have h0 := BRFrame.cov_init 538489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 538489208 ≤ n) (h2 : n < 538669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
