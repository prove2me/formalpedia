-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4705
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:28:25.451695+00:00
-- url     : https://prove2.me/submissions/f5a59d2c-2df1-45bc-9763-1f3bc23ef641

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 846043165 ≤ n < 846223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 846044415 1250 846043165 846043169
    0x80a0810091a09040510090309080d08010e0f090304090203040813060e13150b0d2f090f040902120610060906140c011803020313441213 60
    0x4607003042800100e0405082490b00c6041440c45100350700002010480304100b00744034401607000600561405160203801043c1a0041d080a4041d10741c80c2c0540b42d1080141c0c50403034010341d046d000180c44403070a4114603000581802e1403030100b00000b01d042500e9000450089108510080c0c0c0ca266021142070200e0054001408110b6403800000c00c50b074859a443c0102c10f9414000100180c809006281d402031681c0040200400842d250407428a03c0d0702881c52880d680303001c6c8103180c09107880c025110380442c03120f0032410800c0c440c07260141401040040c1040c4d0191001581d0f00076500001d5410207808204001948800200030001c825800d80030010000f509002464908040c000390a000c505100017003840d8021588140401c02500101d4014000641403944c0510a0400a40381d501c41006440490007402d0000b400e10a8074500c562022004580340061a0000004440c80d00c04803001c6020a0f09165501640040510018180030320780ea40305661140c05d9420b40c8070b0310100d9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 846045665 1250 846044415 846044429
    0x121302030d0c0b070f1b081308010213120c0e15130b0d020906030c09010b131e1424071a01050d020907020a050706030b13060506091507080a0810 64
    0x1542c502000603410304550754001d001030500400c08074400300e003250403030081d904580d8150f000010807402d000070031000b050b08503070642c100ca01c41c2c0e44450f5401d00782d2245544100b074411002c0e10400c0340701d403403001c2081e25a210702c03080c1c16420380e1405000341940050380c03c0c1801044003d8400424904143d0803864500000001c2c05061046c01c0006c42041c0140c0d806802030940368002002d541d0309101e1402c8040d002411442d083d61501580602c94006c100c001e0482e0b541c0e64004a45581c0e06040c0400d000e006c0744004048034245182002101c650041e01e50700440540b1001840e048140740740075205014400180c1c17141182c0c1071010414100300700001c0c2e12200e640044c40365440301c9001910582d010342e0909442c2d102c8103022071070050283c0024003280100c2c10086503850b4582c10a00f11100e04540807a102031a9901490840304984902a8002d8003080015011305000c402d509004001c10038003802d02d003290300e6a025a901c05000000064841c20409c840041c290341400054000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 846046915 1250 846045665 846045677
    0x15050909070c0308012303010207080318061b0d1509150e01290d02070b04170a1d0303090312040617090d0e042d0e0d080a0e03121302030d 61
    0x40390f02c019200c0c034810300820004403029000c2480b00040e44048a022107000742c003c643e541010b003818851600240e44c801c051481d0300c4003800501d01c0c002a81b038000d000d01055400003810f040440079140c0c0c481f45000d2241d45d1113144041c00c1c0c8840010000041c00009400f02d052240580091031429440d00440171505030040140100703030001001001d054480500641d1407191504070203998000c40b030100a0141c0005002810885524507040c0100e210340520181003c600c2150b03000f600800c04010700050032035186280000c44c0e621a64030358000030341520f14010311400401c2c2442d0181d1110155084001010010396a0007030051403010071103400f8042a007080c03e80700b521000440d854204020b40200088855943d65001901e41040b5020b03d060310002100b19401140e100703040044664900252900900808034103c402c540290f0744e106120394882610a00a04011700c50070400c3c401800754440c0d21041d0802540940c00d0080103099039040e03441007629050b0100390900030800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 846048165 1250 846046915 846046937
    0x71707090e0a1a0609010903080c100b0607050a020f0105090d06140c0408030a050904110c010f0b0f15161a0115020706171b0a0314061206070c05071505090907 70
    0x40c1d01c1c0342100c0303e0300440b4159980e2416400485844403103401c0940102400926103003098000541410404104401071280c03c03005c07010068180549440a04540c01030110000140307080d9040110402d41414214144905613002c10342d0311045c00741c100d913010b40d14400f01c410703050903100303450303010300316a20b910701d02428545503980341e0082904810a1160204006035103030342e01c0e0000c48044004806a6484522145100340a400510f03903100c0410f15100c105e03016401c000075103c0c0c1d080b602520766841c01881c1d011a030380c6588420030f0070340d10b021492150400901c890b15081c002200a41a094031075040c16609418150001d1704081994030001e004c00009411100a9000d8114069040800d40c0d45019211140c09004542544440e0010b1189a41601a0700c942011a02002c4101641d96032005014070b10360700d41000031180d803213080044c0240384602d2001012502c644240c50041e9903900c5000c140320066107486006c140080340020311806c05010641e4002d50a203403250080b2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 846049415 1250 846048165 846048191
    0x1206050d021f0903050d03050f130b0601050c330a02040602070e090f1015050f030303061009150509040c0813030e0109081501140a0e0708071707090e0a 67
    0x3074001c900402100ca0b88048810385402402c4034401103410a042d0b41e10881084001002010308a030300443c241548000700f08013082200c2c007000c0681d804044600d903900c4610040d1031070341089035420218420050083c255208100c00002003c0c4a00030703840082c29a41400211020014070101565106120401616600056160485043c0020ba43c25a11048515820041e80d100e04e81e1051080f40107c5680840350390104011949a0880b410785a458404100d0040000280d059040d4402c1c07010070302c00d240c0544017004070040790900407002c940d10b03182c2607004802c040c0303a40c02290021600070340d40e00349800303801020804c900d410703a0140340110720300150041000c00034041107414202c480640e402400071002600c0e05200303d40404030b04600d90f40c903140c024001c3c1d030700445844610b0f24180c140300003c070b0282d079060240b20011780d40b00d41040b14140d070000c0946080100306a002c00721003c00061850051a2650340c0c0301c0100c0c12f15800741000c2078082c16101006151809c506401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 846050665 1250 846049415 846049429
    0x7051c050304030e011b02030114070221270a0e0402180727080f010b10030b0a0e0a060f030807020306090f031c020409060b04090c09030c120309090c1206050d02 71
    0x70813000d08100c2204000303203407074041054030b010b80290558a09600300c0c40c0800241c04140c4221026800c5070f085041022010001c00c110540840071940c0038001500300120f800e18500800045460b0080f80c444100c0c0000c112001e503500849510041d50180010742c03c00c803013070000944480c2d403407001e242031a80d0004d00c03007241e500b800300b840700c0f40b20154000c1c1200031407007034010710140040340c06000200e0785c89402000300040c4c41c1c0c1b00365440300602c0c550314041d0150654450f00103240d50305a5281c50142c440c070040c000c1680602c141e6400001c01c5d6103450258401c06103001d2180075441f91400c0c81803500d084130181006040d036005803490b00490394000101d45003140840c83c5004412817108d81d0102a0050390840d412031130070400c0c08030f80b010341940500f040303402034001805400803540c010303a1003000310301000c0d0101841090600104000e808611440c82c4640340000301540d03941031300d41c100d1301040c0c0c1c4400000c01641303d04440c100300c2d01601016010880b52001a204194001004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 846051915 1250 846050665 846050687
    0xb041b0f050405150a09060602061605091311040b030f0f160509030304030506010803071a010e0103140a1a1f0803070201030c0c0f0f120305040203070302090a02070807051c05030403 80
    0x200b5500e0b00c0004034400c401140c07480086102402c071402640e00c44801c20040c1429003e02c030014880c8100181e080d140d140b00402c1c50041a4903003510707024640c424000c4901043d144104880d451395000728400710325034028001401720030706442d124100000120381d83c0c000a000422800c03030900610014151803e21000042d00c03a00703029640e105c858001c2400c40c010f03584050300c180079200002504820100080c5002440b486001a02100440b00d401e40b0702000c0c00303142110b045080040c8005822100302a04040901085800801180c5e0300c1e404000b00e1000c8550807407a16900f400102035412000341030710360303a030b03404400301608182203da680d01684002904041e283e408040c1e00d140101e00c0c0c01c4666822407040c0c4400c041508180c01740071030780d003000c403280c2418a444106c214031a1143c0b0b40110307401005070014510b9070b020014190405040788080540c2040320b080018000782c02811054070860180c076014040f039503400300e0030f03150048010502000300f0810000a900040c0329407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 846053165 1250 846051915 846051919
    0xc0521090f2505010f0801061d0a4a0403142803140417040e0403020a02100e130903020115081b0f1c03091208120108070b18120a0b041b0f05 62
    0x300c6400c603481880701c1602c003803190304008011404960010221201d00421040004a0103400308655450710840720480001c8a81c008040c0c40c0c00742c043d5031600c2f15030028040d10b0004800440d940d1f21705101e501c480100e0491b49055661140d11614202505040c1d5101e800c0401c2442ca060003c00094040244010980604010381003095030070035007500c0240022a02d14410b5151615001c3c2d0303216115441a0712901305421001e0680380302c1c2e0040307000484081e11814800300d07075000800151000000480a6549901c2c01d85070510300400300c60001c200b008000c142c4c0c291000c40c0300d1243c00350101000e001c1d904200e4540e0598076404281c8140120107402c4803152003141c01d04807114001c40d00700800c1c81d210b07503c40c0d505102006001e8191102d19000200f0036036030f104020303592131751035120748980341034103010041c14002c054450070a40321020348400b4401000041c41401c01c1c0d403028040310601c103d4820f00052143d054030560011038090082f5407590f042c0040311000b0303030712032207001c3c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 846054415 1250 846053165 846053177
    0x50405011a031803030f010f3c050301050712060b0a020c010507030e06070303091401050601021207020a120803010312030207020a0b0a031805100c0521090f2505010f080106 76
    0x140f581840508000d240101d40c000740d85c1c0781d0078540300c0159a44003e125400c9080303041c81c0040364400401c070b054018614402103011040f82c005c42c080d158400602801040400e50507000607131510280602803107034119a4a55030718035032112120003111801e130000c4144410038840f48100c19000140b05c107102e1000d00b030060b00e40429140443c0c4540c002e44421703030840000f0400b0010107425410031150302d4403c50622000315402d4042d00d0895004485a0380103174082c071035980c08100b50000400d0311a0003e0090001c580d1600d456030703041c600680003102c030310300000010814401e1208404100740d80c03e140942c03420509800290640b5424000c40e507140398005406070318103010780e0102d085c1e4494a03000203060005803c199482c1ca2680c920f00b0300c118288400f8240052007001260921030507124414244c01c0c0540c03105888441c018904034035449202190040c061040000220394000c81101030580d410002004a010503607074007043c140011030f8280c81106c1d41003403000303040d40d940345082 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 846055665 1250 846054415 846054421
    0x9210d090f0e18120a0318030207090509030702090f061f08070503250e01080105010302040609140319050c0f01080403050d0b13060602030d060501180303051c02160c050405011a03 79
    0x141d10100c4084203501c081e1144d244842c000700c0b10305015120340e0000e034604002058031600c55107040303d54800c0040044c3c22601c01030004898aa000f190844504400c0324100480781c4c0c0401c141400c190796485100b042d6008000035490b05403402e403100d20f01110581e81c080c03214000a82812809032003c418400c011001503018210915032021400c3c1480484110300301d0248081d154039040c04046001030701c044000300c0c00c0e502034000c49088490300d6660038040ea10b442440c04014a508101035414029240c0105404c0391050f0304906150050303019001041d030000c00c0046140714001505d040c06448010403000c08e400c202940e0103e0301070040400c0a0321400d0015040c03000700204c140c040d13403903e5004100c055002002d44601d400c682e1080240940f5080156000e81d0507241500c140014281b0500000784100090852490789290381820081c0680e2150180e07001412f991404d10318403940365051021507800240104415282006a5410400c0c120070000a036442c43c0810b140c00004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 846056915 1250 846055665 846055681
    0x1203080412023f0306030c01051b030a0909050a0911040504020109030b130309090b0d0f0302010902060d2f041e0f060305090f0f0a11010509210d090f0e 67
    0xa228100d0b10f00d00180070b059034420a4201100e01c000485120f83c1d050151100d003421480840307008400060040040c21441fa0046030140c0c000d031070382c9420800c0c1c0c04988000c0e9000704040c04061000d6100c40480710b0509491204071403009001c14401828003034401c0100c2d800c0c0340700844c1d480c0305030380120f41c558990006032040c01c205c2d8801420240c2000400000e40c0704d044849607418402d0381c03000d90041d540c410910640e240c440d081944100520041c100061401c10316a4503d4860700020900c40707041d400041107600701c0c841c21800382e626401c1041c1c0940c1802640411105041c5000354130401d0040074000900480c000c400360040051b203400c40b010f107808100c00080032041c5d420450309844a0008025004c151070b03507440751048040c0307110911004a03900c400f00c03118000814a5064507155101c2c09581c0f40340d40c81c18003600300142c000d1505c2d0800c20700c1e80750b48001e100b4107040440c840074514007880501403e080040d0201c05114082e0f071607403144200d405440c20740743c0c039854840c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 846058165 1250 846056915 846056923
    0x528120309031b12032d0b0109050d050c21060c04050a09200f040b030a020901110f0615010e03010e15010501030b0a0339061b03020d140d060b0d06120308041202 71
    0x9861b48281841c0c00080d4440c4e082e04005040c0c48280d84030709503c0c6d81d84040c06400400024020060741141e074608290b800c0ca0112600f41003110f41b8407801484400003000d06000064404085030b10001409121a0420940d05001010485020800c0c410b0820680961070045400259865400207001070844901c20648028000002c211556070806d0381c01100254000b001c103e001c1002e00e2a40342007280c02160480c00e454408025000325a00e008245d07404032100c485040c11301100c582d42c0c0d1343c152400d1160791140c80f0324400502e04507990802200d81500d0580c4031070b042508116111401741c4900c5450421250300004141d0b01c601d1055002c06a0452640358003401d54140706090900c2c205040301400715055500c44030166100c0400000f0394506041018016030f00400c01d03e1a42c5d0301c9002e0840000c00f00080650170700f07070114029401e41d15180c1c0000750340c04012441841c00741c500d20894009055030400c1031a0b42e040d0343d41c09041e501004001400810390800000e9566001340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 846059415 1250 846058165 846058211
    0x304020f0a18021305040c0203220b0d0c02070506160f170708070c0b0a050403020f010c050f0c0301050603012307050d0501030c140103090528120309031b1203 70
    0x850140e120711941480b4200a40082c0410081c11040103000240c03410702e072241141d00001c60b4051882c00c1013144101c4484580400b803140b0011200c8000101406800040d03c1007003103003680410f0303807a00300d68000c0c1341c88490b8200e5072040b07904002210322101211007078003046911410b4541c0e41c1a40b81800e9150042003900d0020b054030000d01d20781000801001071452a2081d40720400d00c5840d403401d5222030066050702008554104020b1002d482c1c2207887d02d45000d41450609900c80441e5281c1d0f01b0a05000c00001c165405003400120914080c0183c551080c002c0e0300070481a8140c0401c0c0c00860340ca203031407100b010f0303401c4041003149100d40111400c3c840071680c180003d5942c0e00d05440010308500c540c81203401c00d0080055150310074001c4911154110009000c100882c01000d01e206080840b0300340f00c030840d103d00500080f80411400b00007000e50b1000030f2180b03101e0034047e0200404400060000072580086400140c882c035508148010510b40000c1c40004212095281c09501d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 846060665 1250 846059415 846059429
    0x908040807030c030309090b06030a020702280521060a02280903110405160e06070b04050616020703050d08070504051c2d060504050c0a060f20030304020f0a 69
    0x30725030100c28010035510708802c40b4800d5858190300d50755892184200e5440c1e07252268000000c101041500c181600a4403105000400da08882410201d01c8030381c11046403566115100820b1080049107420b650f1414400003079010342e08003440008917642c841c480242409801c0b075000c40c41b8246030320790300e1290041c20501d00a04c40c0d0a1005c00014142c4031151208480d65001c4400241003810f241c0107481c069030307600328001c0034845968410788000c1d424048054100c50280880004607030864111800351380a00003420850402d001c0b02d00303031003180400c81019513102c164100006200081d25000c030366102d00e0140795a03200c00341c003118107204035840144c0c40f01c480c2c2c5107102584464100d0900c094442c0003a6003903800907450710800c00e0032694500c1000304e0070b00b802c5004a44140c02903a8001d01c50400d8500060b0a50001400c007840c58000c1400211782036480b41146801208038003101c20452038001c00c65018107240e84d070301d120091009006048a10308103181c1e48480c11040054848 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 846061915 1250 846060665 846060673
    0x4110a0e0405010501060309030c060507140417060711060703090519080c060121031805030105010b0c060702062205120a0302070606090207030215040f1505150f090a09080408 77
    0x580c40e0034125100c0162016a1107528003c00082c50700c2c00b07882503010f5551706071103002c0c0c100c2060311600000c01d0300808800a200050501c1c02c1100c01c5a8010000f0317001204001100c1d090101803580351250041c400f500303000c909228154045e000180d07250780105e0629000c124001c1134600320f810084845550030780c81c460342c80f6400420007084080d2610303003021803c40c0e10580e070340c5241500d00c6004510760107404140c82c000c0380c08244a641600408601204100141603035540440c0c2100c60980c002c0d9480a40420a50a080b10501840c2d0f0000389a20003015142421b0386000707005c201301780703009569100740c0c901c0d0010403c06105d4a401e0421126070f868603407040f044041c000e0340c010807048500303070724002c80820203d0707003482078440d89601a402040b4491a25005540c202800b500076a01c0c40892007101c8001045442150f1a081c10071102041e0342c01c0a00c1c00d40000c080c40c10355940302d02c0b800c1824803030584a25191a904c2002d011000c102c2504505000c0a144140d42000c410b80c09 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 846063165 1250 846061915 846061919
    0x801030f0528061a0112020c03070f0309150509150a0e042918010905070c061b08010b090d200301060b04050a24030209120109140f0d0e040504110a 65
    0x2c15119448440d400350030305021120405161490768466008001d020542a0b140c003800d181d0780d503019001d0700c0c1922085910b003401903244e600d150307030149200320001184030307134140440d4034040c0000b9061003860030803605144503040001e2548000c10740000c40c0104c0480c9500f405441501c2d12040c054002c0e000b0000450815450941c00811040c02034a442c1d100c4d01d00e10846c1403c0d1100103400044079001d0500ba42095214030103170402510031810404554800408200305114012410fa50310301c55608650300440c010380b8070141688000b0460300e050085001985880421220f10b56101d1042100d4224070041e419418100da020aa0507619050780466800884401001620400c0380c254601c41d642d0354003a4000070002d01c41c61900060b0020b9010014020f401800911000400c410040141070b00e615003107600a10007552051f4000001190710b00c02444400c02c600d0f02d00024003042c20400790b01400580c2d125500c103001d2591640010700340000c2e440015000b01004010b40f4030700d6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 846064415 1250 846063165 846063223
    0x40b0a0b0d09140c090f04030203070c1e0501050703020606010c1502070c031703010515090303212502030405011209050607110f07050a06051c020f04060e09070801030f05 75
    0x10b001d40049825400c03c03d011200110000390a0704a024014052021542d40800707008440001030400c03000e602c800d01404000078000e0017203c01038801904200c100c030f05c1201001c06458010342c0300606000c401c203c00d0700800c2e03001c20b20550108088c01c0026a0700c05528021041e4040a9585409540f02003680300400c190f610091044a00070964403440720341c505030150141c4000e00c00c0310742c8002d19880c00c510212103134000d0008a00018140c03030615a4035180d10181820711512a5542c4070b0480030041d508544c01560038884541c03401410149106185c00b0b50303a80303d9402440d0500c01400b9500784034802070b40140410070707802029a01282016130002e0055411200706895500520000c0d00641070005400c000300d070300080c031203c205450070006440c0c5500007101100007814031203400b141000c0d10b00040103005255034043d9070b560314101d00100581c10104000e4898001401880f86841d8858056419a504a8035500c0e1450782854224980003514564180305841c1d10180030103c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 846065665 1250 846064415 846064421
    0x3051807080a111219060f090f150c0f0e0402040803040605041814060103050c090904080d0f1526010603240209100518030609060a0b0a14040b0a0b0d 66
    0x240e80b08031400b11034015040d0030400014603641201c0d040e648a68805020fa517100151030703024500508000400c1c0c440c00021100340c0c1d2105405680c2c0901180c00342041111400013000c0700c00c86070400700f082c0d07010208018a846050760a50341044240c20b517002d06a0307074590448008200110440780d139540d48000c05000c42c2c00c10710406041121a0050b8100944640281442404032560074203181d43d40da80150014003011f45010321044090000c8034160f02c0b01c106650040c1c0c05503100c1900d07031040b0709001042d9017001d500204403e0814030f501300b81035084d0740384405440c035120345101060340c944108030790900a003030349205540c206a400402d114008002044003c1031001500340c480350303050210300b40c0c13141c5080d4035001080d1201ea803005034412000707801c01405115040c2602500b51002a10b0714009541c45800c03070b0484801d01c556007005101c0c1045c8908182d030700090300751818407140103100c1000c0e901400b80d9150f107d034085941e03540c000000030f0090722880649900b42c0c00800401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 846066915 1250 846065665 846065683
    0xc22060312020706260a090210020c03100e0613210f0306060309050d1112180a1e03060e120d0e010b04360f030807020105010f12030305180708 63
    0x50f00440602013034240c403841450690200d0090741ca00c2e00c0007a21810b8240c084c00402504910340d40300f281000581c2d1380400003584409681c010104001c070103003014100b0550414107040245481660030040201051490740a4240c0403500680102c1e0306080481e0114a085038801525801c8920742003a000191880031004a5a00b003201d00d071650340950886180c604080c1080e445000c1501106100e000c10700c021001c00350580744200361110144d25260000394250001c1200d000c540c07174103410300d0511100100403582500c0b424807e000340c2800400e540d400007078006a10789a44107134003070003040008101c034210500e8560301c0e00c0340380102c00142155800760b8069400d140c0050098600750044020000021a440100901070002c000c60345650f0b821241580c01082c0c286408503400e181d158507124000d40700c6000a20305000b001782141d2050b0007e03000d0413110b24007881a02c00d49650141c2c0c055050074001016150300c0d451180320740e100c460340b440500c501740c00072480e20808104458 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 846068165 1250 846066915 846066917
    0x90b0d0f052d150f22141e010203070f0809160e01061806020615040f02070c0f0e0c03040201030207060e100c03060503010501050d030813061b08010e04050c22060312 73
    0x5401c440020300140d0100c0540c4c159061100039004100c003106480881c40710b40359221142405050030342e558001c0030740c00c034007a8545a00451141e4007a80c1020101001a000030b0008500d145070a5002800e55a14554030808120780f0728001956050100310100d4520506489824801c0d80c0745a200480c003002d000f1400000c5404809072400135820012009a4105401130611956803c0100b90015098480349500c1a1504003611030b00c40c0a00c000d1203428054000120081c0c1440010380a03401207500540d1502042c204004100070703217400340c84e006642460050381c0c0c0d25040c1001c2010f07101d000a24a214050f000031040300c0e0525a11404103000e1584080c0607070382e1f82d075082500702e480911440350040e0461810343d000074420200b0039401950b40c030701820001c0031602c9400c202d61203207060011a210005000a5035038000580344d00411944031702c03104e94038050f030719691512807010a0314002d0014030140502000c148003040c030603221246c1d0401c04260350b030401c2e40400c4260f441c024 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 846069415 1250 846068165 846068173
    0xc200c1302180913061517030c0705040f110d0e06010602010b13050a020f040605090f100507150b03151b04030f030807090504110c07090b0d0f052d 65
    0x16a1440941c0281c2c0c80d98400401e484011949000c20f0000200e8001c00702c01301e01e00e0714680e001c00501e2030b12810000320700380910700102074240b000094004462a40040d01640107105ca0308083c240050640203a503019a40401c0f0280c440401b03401402403103407a54482e00d0082280b0756800f4180c1d00660340c5a0045017240d03002d90f69004240c1c22a07108003d81c43d0813403c0500359604204c150b8004a401c4025400014a0140640c005220681240d00008001800095400940d02e000c0890203800c490131989901d40080440001c0d01310310425a00829004994060b001c00ca2031603800007a044801905030f45055440032030040344a802281c807803240c00c2c0b0540500480241c01030944064a52080c45580346180688041c1c680d50303801451102000110040440d041d16140910350341802465002c40d00d5048510406041c0489a00900f07495490241440001e42d200030613458100e07001031100b09158201e0401c00d081c40c194006240c0c1d104044070550380d0030313603400c55240a001c407450113136 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 846070665 1250 846069415 846069439
    0x903050d0f05060a062a15200304060b0f060406122a0c0c0f030605070806030f0d050a1209050a030f081003111810060905031c030c200c 60
    0x401d04480042c2c55080d0002c0010505001c4c0701d008841c4804c1600c420b41e01c444440822001e02c1c40304040702c0800300c49070002c40da610320000c1c4650064004018800c061007220f0002814a0380c1a4003000b000070f045680c84440032071540d140c4600e040f000d400c0140941d6512601d4000240100460015007584907160002a064010325180b80140380208100202c80343c040c510012205044a8102510204030803000060744076120031004005521503400485e82d440c040700060a03610000f40345a00a40003001300d6444c4a40205584041216505000b5256408104112050708008828283e503500d444000000c2c4000060301d114500d11903076540e0100c00c46214102c91900040c1c5a811071400040810b2001500d110020078011001810b54039044d00c200c10403000c200030a6440d090107c0c2002814040d1940c480e00460180c5010740080080c0031111203031045104080c80340310f08150351070109100303291080c2d20749540e05002e864850342c1003640302c0c20152154600c81006100d40f610841c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 846071915 1250 846070665 846070691
    0x18030c1a150a080609071e091406100c1113061a1308030a050d0f0b040c0905040c140f090d020310021201052d01030e0d02071811031503030d0903050d 66
    0x41500c40c00454024068030703072500d4881c07c05600a42041a56640c070081d012481801e54270a441140e02110200240c509107030040c4140c000058841004100d04d9a00500100303071400d0602d00305c6d00d008d5030b40c00c040440e240c0f40b090080142d50020f180030060800012202c5040e14058030f901c6501d03144070b1003a01d0740d440c0c649a480c4550f40303059000c12030501914407400002d90007a0103042c2e82c1e00c00410600480400581150400c1304c0d0302c00480e640074005d00550900f8807410200c58464100360800244100c400f8805000e00b5503401d45000f800aa1070003a03407a103065414201d94054100c1e4a01c65868000e803000e5046130340241c86170030b0701d94000201d03454640b0008204803e0354941c18408c212081ca03018900700c91050050625456000480c0740020400840003002200e0f03024095260905c4000d245807900e200380030b0822414444188041e61344803040300e400c281c03240f6100c007000030302c1c80201e411406400e80b003801407450100c0420615400070000d24034071440400410801c011588 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 846073165 1250 846071915 846071923
    0xf010204050907030b0607170717040b0d27080d0e060106051c1409030a120e030922050f01150306030b1506070602030106031e18030c1a150a08 63
    0x801d55a10082e80700119222601a5000c0d03480701d000901540d03d8000181c554114403404441d0381c0502e0a00040d10a042c084485031080922601d12841071801c1d15280c94a100340c010078514030081995100500f01044210030150302c214450b80b8619241927407030a008085810010b0045003c50030000d184d031155402281ca541038031204e2720b0711b604245076031074420104542b00301c0f1841169910180c00e4142e0804540e050720460307464000f16519410b1440c002e015405a20100d0039881c1811690001e02c200031098403d00d10b000d0307585041c0c1d2180245d040b41400d185003520001d0300c0c0340000b0f01c0318459000c030049042e03824410391041c04e4007194900710100c440314407004d0b011416140c00f143e09440f0101c455004030000904090525405031500001c1343d100382d0103900800d03680c504a0310061001280d00d03075030138007015013003040d01c5c102252548056845080102002400080032042046041c001c4461400701c0340607070540d2800c4800710008054903140c0341c2c443d200030f890001d09500005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 846074415 1250 846073165 846073169
    0xe0f0702070f030b15030f030a02070801111b030418021314030d0e0d081612050315010f11011817070809060901021c0203030609010e2404150b0702030f010204 70
    0x24008450b9180346840b4440c0040c030142a0400042e02e0703941c4001d195400304840303907d646a06018595800c054a0702a19018081c2d0084019905040154010340e20100944422211400442c2e0600700c075004002c1c150320840c3c200504441110b041e640c41c000076907001c0c00c110841501d40540858540200e10300d0b03809813101c8503605502102c124210300344526040210000040c010000b6801d103991621247d41100c15119a6040000c001c00d09200405030303040c030541107604000b40745042c01c0030180c018490924185060110b91119113980b248944562509841c480c4002c01044480c0321101071081820399060b25104200101e044588681c6801c03102c0c2d95900801c076030b180101c54030500000e5003241110350b043d4003a0010280c408030404503d61600312150380955568540f42c0104104408103070824030113221403e04010700c030801d011602e4024024503540e583c1003180303030700060054545c40c05840c030081d40700c2c100020314018000c003a0101c248210140c07800174003500d23140c1d800c0340914 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 846075665 1250 846074415 846074429
    0x4050609060f1009080f10060b0408030403030c030e0402030112060605091005093d12030f05070f1e020f0f031e1014060f0d0c09240e0f070207 63
    0xb404584007989000700f00b196188a103400c0c944441560345280b9414083c010144503155042192074034499146031241d02d000c1d103c011f560034201814000c4456aa00550200805000942d080e04003410300030801d40010130001030040d5680e40c0c403510754900ca442c42c03100c100c51450900030046154500362041c0c5100d41240304440c00c0b0707240341200b0040c01c40f6015000200c162507007407001d03690815180d0240340d840422a849584488502ca03450072021996004885a1034040d121400187d8020030040e46d00480f480d0490b100c0d00c00381405254100c541900070040803031582091402c440b0b01c41c072080e885000311921408280350000b404140c011b44440954150080440f000100f03104090f510070001d510412200b4680070f4030142c80c2214120311200d050386942c5020000b0b40d140890000140381c4090300c00c45a50b6001d0750b1b0300da0803070741140203091065441d40400c2d000301e8184502d9500700c01030780000080f440c0e55640c01300c0b600c18040e108400901c01a1001030300385400041c000b0110f0741a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 846076915 1250 846075665 846075679
    0x30b011701140d02060c01020c010501170a0c03060e010e07030303061418040210111624080a020d200310050a0e1902041d06090a18080901090f0f03020405060906 71
    0xb6020808204151481280d0000302805841e0444100b4070240070400199000007d542d4100b21200d484034002101d100e10b43d52000c0451000282c1155210048a030b1044c0041844d6100f1401240504025043c5a115208a1b83d0010902d036164110b17004640c880320184840509250510040c1d1824900c0f00c0290b00200c40450014105850f540350281d4291070811000504644900d0921002484103103eaa08200e0144004030301009001100000307840c10000501c4844000341a80300020702c0c5584081d40402c80b00c55154032900310344000c5d48403004c5040301c07004c2c802d054881500251107480383e0b4080c01c10701191904010102c3c0f02550040c0401c103625a58907030101d801c01c0c0d280f122002d402c680920000954507801ca80c8105c8803850303080c0c60300171454410240982410f00814960a49003030600007103075074503680032600b455034110b551195a07002d24030040c0e03011070305a4840c03e00c2501c540000035105c0c80e00700c0300000340ca100700d40034025030300c5030820090301d2401a02c1d1a0380c0421 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 846078165 1250 846076915 846076949
    0x15090615030302030f07060b120a0b0a0207050a061d0a15050a20031e09010209030f01150b0d2309010608030a120b19140117101a0f0a030b011701 64
    0xb101700103450175a1056902003040b21000010414030400440c2c40c1600c0d41c03100001004000599008617881812104210300b0201c090315507694665503c0000f90020383d0328130461240c0c4c201c0d002421405140390049030f0301d01e03404d45051070400128040c01071032140f4010110355008414000c034240203000d101400400c080300744000115510150180c20038405c10b140c40794807540f00341c0c20a445104c00d2400183c0741d130100803d0600740440481c1c628100d92401d2617051140440003268400d4441c0707c0e00301d90b20349842840c140024107425401c0001c4004801d003071001c03080345090711031080501400900c0116900c010981e942c2c082c0030010000b082d0410080d0300061440d90225a80c410003c200501ca00e0381e250f03440140e030790150021640d0320080101e05090b542c101c41e0751051100411003a481d03a00d4070444860200010740500ca40c2060f00e140d00072040a15172003914401066100c0e82540c0b07840103000a401494060246c0740869086c4030501c0d15800f40c1348466040300e0645c001424412 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 846079415 1250 846078165 846078187
    0x70513051c030f030b0307060504260304120614100f121a0a150e150a08060a020714012409020a09150201020d090807020f030321131509061503030203 66
    0x1843e030740c2244101036450042c12240d0703600304500d100600c00c44d109c096a8034140f40c00e43c0301c14100521510b040c401d03c95a094880c1400004640440e03480c840070390000b45aa04d045405800d00d42119159040d51205015a01e02e04d59145030849210f5800c0301c1c00a659149c441c25281105100070b4032281d9021040e0600030345080d100c5512050442c4001541103004031585152a196000003086082031010090703480080c501c06480380201f210a036014602d0280e00582d2107400604080340660003050480c20030075442203006c003401001d8020701003044040d0002010071b03030004028004224001c0300140c009414401c80710181d1440e51206003290030410060405803800301c0d010110340d400c0000c080070342418420100d9180c410305445941d200d0314010400003590186119100f50020420099010f404040e41c00d024034110420340d042d0340d90040462025000c1100140a00c14102082e001450103544100e030701d20301c2041c0400c4490b04103030711b07620f41496500008016030b104020300000f81c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 846080665 1250 846079415 846079427
    0x150f07110a11010309081215010f0512040204021b0316030e0f0108070806060415020609070801060b04120c090e0c03210901080a0605120a061b0e0f0103090506070513051c03 76
    0x30303002d40200c1e40b0b40790151f0b40c1110210320441e0715000d42c642c6003e0b08400c6681c0040c1111104a242c81c225041200d5400906580c1801800c02403003141d0018184d0741d4980201c03414509100500240c03502c609031244481403201e00c0703910490006025400c045407038a05182c02c11b5a01c18103030b4400c1802d540300c0b08162070300540a0100c2d45e101c07205010020b9103004010000c0780200306680900000e0a00b00c4540b850b02e406600980426414028180a4801d201e025103041324015004a071010f80681003114482c0030b180c10005016041041901c1142c5c00024802140740b401e80c21a4070801040048070000c0480c82240d604c80b44080012001ca90311803504a43c12644440b80000d0f0700c0d507103100003414800c11400000f00341d00031125800500050388151948011f4200c6d411440c60b2030040c005006001042691740b182d00180c2e0f40600a1340f0a5020409103640001200c4090030301c0d450180841e01700c01104e8000d5601d2402c04617107405c044501c4c60b41c02c0004607030074004c80702d40d0740c0c1030341c4d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 846081915 1250 846080665 846080681
    0x7300b0103090524010b0c061b0403020301050c04140a03030f030908091c0515060f04020c01020d1508100605130207022e090501021c0809150f07110a110103 69
    0x10162900d401e4408220140a043c9810040d4403102143e0103040044c0c54903004140c2c00115000000d00900840e8107010035a11f80c8a40c042a80030000b5551030003410180c01550400f070f4043d0710700000c0002c1c3c4c0f01d245009000751211701d240b0f0105500b0000130030102071240d000040000b041c6000701074601c0e02079040108403902c240386950030000e0007808240d044004004048100e4030050a01003400000e09c030a41c21585003a8000d005450250b01143d03a41341c200390054020b540c0080c415000000030350503500d803252003060601c501d109001c0420b6001d00503014040c0d050040c07034140703615044039108240858002a0060340010025500c0380000c0d0002102030340c11840710148050400b415102d48078900325400c03400080341c2d81c040c00041c81d851a0741c0215055521403455400b8840c0c45200021801039249801242c41c0d65122486051126a42e03000d450760803000700f40300074091201d030190702c910724907078034050303c0200c1c624429501e40c4511400f81003d002d210214070254030903008411 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 846083165 1250 846081915 846081917
    0x150504020d090602070605162d09170a020f04020a0c08030a0b03070303050a080106030902030a0b09011b030902120705010503010b03130b0c0901090803030108031b0111070b07300b01 80
    0x26070502c0c5886507404c3c2e038070400d03040744e140e0344d00c108003c288072170b000390400b030301c5030602c0c00308501440c4c940041010074500210045c0c0740c0d4a0b51b070301200c07548202c0e40340e0060b2010380348815083c9400320f00309540e1f5038990012407041d0300030104400b15041920945c1d801a005645d982240216526240d00c9075201415001c100c41e181c1c502402c20b41c07010401c0000840c401d58595550b444a50001000e24006070481c0041600f0100c80348090f0382c1c00500003c840e6007103c890b03411a107403001160b00601000c1c0d00007915009501c5807040d100e82546c080e1051a0095955811705d03860700314200d488a24074000c0c103010520900050118034008001fa552044c0304146441b450107007030f12580c2120304215003803081c40320000361403a50f83d603109a0078030041421400850840d418000b00b10388078042e1000204440d2070b03407008800942000d41150341401c8044511503900d4036681042e0003114800c603441008142c0001c82501151104108420402900117003417000030fa1400010b005040034400640c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 846084415 1250 846083165 846083171
    0x72d20030a080106080a0501051509010e090115090b120103080d0e160305152e170607230403030e0f0a08010515030c0901090504020a241101150504020d 67
    0x118482040100810706050b20382071210362400c0c1c40180100b03c000c001c0c450700c0d03050800400c0341e6103071b40e130a5045180481a444d611400301e000102c50090b9080e41413a803002c40720b00001902030103121a9a20f0302c003540d490034602512003503415441e10505905010040c584001000801d1400c006450315195046010410010449080b8a4120051007008071160007501c2007042200411010090517418a0b511016140c458480852002230f0440900c56114a00000c4014189030442d903024003040c5034003030382131800460b6103980c41d00d044a144001c0358810070315031000c83c03000990110a4234140304060ad45130466604540030034900c0d030096003086410000c0c03802c542e00e403042080034022000000815117003c0c00c1c4074184000c810032540c060b410007200d01c02252244058103054641c41c900124903510344e403000c10214080350340401c0b0b102d10480d031600c011001e900e02e034007030a80d401e503a180e007841d0009651500301c94814021500082940400700b2850a20b90007030a407205080d1400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 846085665 1250 846084415 846084467
    0x13060f0509180319120e0c0114070b01080312100e0604020a0512090d08062704110904030c030e1210110d0c0306050405010f050307061b02060c06072d 66
    0x400d1641e00100200c00c42103480d044c085498551180e2410314000e1304c8803051000914007900305032200c030040604c030f041180303104003061455001d2044805d03180d03102c1000034a80da51650f40c0c94582d00907004040401d94200081010386131900f511409484034403180c9132880c0c50380e004000c003e50040c0039100504c58280403160101c1c49200d6024410801040508180307089514018018000107122500c40e01d881003080c0541c44480c5104107a80308140e40d204010740300c5051000d800304022146903030101c0100c8c204020180c0c00500800359034481c0d11201f14415803079003040411058442d0700c0c009139004040c036009000341a0040075806000740078882c44c050b034610100003600c3c050500c00011980319282004a428184152070052a0b40b140078401d003420100084e450f410944549001c000c030480ca100c1405a0440414400642c01000d141d91984800040d0307885010842e2400c0100700c98500801d03060700d4242c45191401880540d9100c5d1030310019055078640c0d83c594090f02664564086 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 846086915 1250 846085665 846085711
    0x1302030928140a02100201060f0b090a03050102042c070f082809110916050c0c211b0108011e09020f0c0723060a11160513060f0509 58
    0x3402c88018240014004a600600600c815488190200380841e803510700c0802c9040101100300c420b03140c0e2180c0e190342d2107001c4800260174060b16000034220354400500020350080490350100c070610107141354110086405203119101e8000c680650103d0001c000c00c0c61540e102d940da035a03100080041c01b40041141000820070481000384202c0b0403a07070360140400380700201407540a0f582c4111800c000514000441034020104c001180701845004118880341c21000d0002111014010307012021340c980b60502c01500d0400a41d0015040c01140001008900140ada0ba0812131068640d0a883d074a8190f010751604418420140c24240a540201e0006c809000910118038a0b824590726481e046404500301400c80c0d014660041f0b000d041180b074900707a0102015074860450300c507615a0844c42c81956490040ca402c4a0741d0f01480540c0e51122007200d2540c401d80d8030039105442440d15109082089800c02d0141c01440e030601c1000b00942d00c2c1662440d42e114240d60811400c248100d00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 846088165 1250 846086915 846086933
    0x102340303030b0a17070611100504061b020a0f08090103020d14160903210c0f0308070201051b03010b0f0c0712020f09011d0601091e03021302030928 66
    0x1040300040e0f11511201039501e40040964090015521a0094903441809541c0d42c0c20740c61084030180011001e8901c60000d01340580451012004001e2000703142c680780010050404080b61051041c10250540c810752000810764503081c0c3c0030401c42154621034991139110703000804620b0401d5002c0080c84031912480c001c540c001c00c0d144120640500304110f10346031903c0590520410082170f0b800810100c0c44240a490041110141030342101900e490100c070000940003018100c1008007891400f05030707008444030b1040d00c070340e070003000b9688500c0040c0f5006407d81035650003460040c001803000b981800c00508211410101191a144280b20528240143c0d0380c401140100403500c02c1d029402d040710581c183e1a0700300d844011030360510b001105414400c80741c101c41c0745140d1002481c0303640204044401f4100c125800c030390303010620b40d411001d030b1003d02040740110081606406c1c854254029207001300a0b01028200c01c441010740b10340d40e404212211413624200348800340c0403030301c0b400c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 846089415 1250 846088165 846088169
    0x10207090209063f09010c030b150307031104081b061c020d060509010b0d05090c0a030f0510020f1305040603020319060b1003020406031802151e0f040f080c010234 72
    0x280113555514040700c0309401c680e07404103000e041c5800d100074410b8554500e1100c2281803640c90480b5100d0f16980381c110020300d800c50b05040c912000240104103c000000c8446c42404048480c5090300c1481d810320401e801401016819548010b01a401d801c4494024058610714010300080d155601c2c00051444c0400ba403210740c910307400003001034402c00710740501940010904020100041110081404141144000340c00011082c4001c0208041882005d42c0755500d15003d640300d40c0741c028a10f240fa07102010192086000c148000703024101802048101c94001f000ba22a003494000390303204951001c003003268505d9840010b07810f00d0b541c01e40c00e801c200b0f03026a001621241400c2028044810300c640c048180120a401400142e651961084e450034003001065211403a183c1c403500881101e0001006007180880d080d40c002c10008080c0003100d01e14510f18068660304c16100b9240c3c00740488180c0107810007008000e0150400746100209944004480c20700510314514030240d8400e6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 846090665 1250 846089415 846089527
    0x2030c010c0e030f010903080f1509070305010536060a1a04051e090402120316050a120503070801120309080d0806011101060b0301210c0e0601020709020906 69
    0x302e18400300350a0401c00d660700c080c0c2c43c100070071800d26187c40c00b608240000b8545030009039030900090580407400d4074240040c401810450003410a11405400b038207003405414007461389041c85001001080040400024540e1100c034a1592070482190f4503102c020a5180c1000180b000003d180707001112050121843c180201d441d20b007010100206c8a5a180e4000d0b00c003840700c0c608035955940c0014451704681d040b1082201802003104e6181135000c1c40d12007240307100006140c20140074001c19042c25540c40f440d0140c0f0b20082c050000d451134001502c903840000c0d9401d0051004212281a0507d0240a4141366001d26682c02031145040711320358480c400143c40d5401d1201350b50f00613110000c10301c0c085009004640c2440d9004899000512600c82590010602d004680207000203200030a42c0042603030f40760584980c895403445006841490041c442c10400040311202442038500d820402070441c1d240c266241a901c0340204155404081e81007450500c0e4619145594040c41c40000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 846091915 1250 846090665 846090677
    0xd11030a060e01050a0623040b0a091b0212071101020c060a0f18050112020714070e0421090510030e01021603170402010903030c050316111212041502030c010c 70
    0x6600c2c00d404c2d11006018030f2801800e01034140a078151054500c0f05d8402c00d00044400c46a10f07200181c00742c01c01e10100b42d0042c0d8030072401b00720b189550304445a0529000400b0901c8504050101da50700e15040001110420512240c800112400d00340c0044040510458051008181c00500780e0b40c0030701040b90210b00528002d444813038001480605203503a101250482d0361030440080c0403214411450704400d50300081007401c004500000e8441c85a0a004807954103413252403940a8840070f5a0a07600d0380314560203c5003440c44043d481b00c803070b912562a1007105182509211300d0500c208800c0092545940071120300440034405400c103001223001208418a0300d04029050440b056a81c0325403c40c1c4d4000c10015036044086042140c0e85440d003503184007281d0038014218041c100c0d451818a4003819402d00380100c00c01034828400c000c80d0b0000a198401c8840b40c0c1d01c102c2168144010001800100914a42c0b00800c2c80b500e691401a20318100451a40130308594051101d5000705d05 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 846093165 1250 846091915 846091931
    0x160b0f04031709100b0a150905150304110d03020a0506040b0118020301030b130804080f1006080312011401051b0d030e0d020a0204090f0f0b01090b0a030f020d11030a06 74
    0x42d0208244403256400c00101c00d4504003001c000c0d881c3c4504804802080d5281e042c442940d45481c80e82000511301c42505032100b2802c100000e003140e0341446220b1050690103944d100c0c80e0681c2080328042ca40c000401417425911304140480d424041d54290103500030f204092000c01c0c02072041901c036034407600c444040b40d03042080c403880019590764040e01a070310500062000032408400c290b0003c07580054548440300b985003442c014030035070b041204203002e5140e0152000000150036100d1001011090200c1a10340582d1039690140b44440d000210003403004000c00030310034089222000043c54101d2600030748410150107100c0f65000211103501c203245809405038103110300c2c144c04c5205005015214031841000390b403007010403001391090383c0e42c3710307503030204101103c2c0c01400c0e55115444c21080e902e6801d00700a109000d1051000b054180918014149400e1140c0c00c2a681d1141e51090b880c4030580900c0f046030340b60f590454101080000000690381d080040c034000502c94480807401d55 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 846094415 1250 846093165 846093167
    0xb040902040207150f090c092a02010605030105060f031b060f0f030103060506040c140f040f0605032403030d0209060403020603011e06140a0305100f06020c010212040e0606160b0f0403 81
    0x103180d45c40c494201458040a040010034000903002111081e08000c10f0104a012034035210b5110300209694000d10060007040081d0103400ca041110021802088555506428003000181c80070589078160012181c4d400e00c003d0105044030402009081c007414080b542c040c4c20038607413100c4080244140701000410400100e40507250b8020829030741480001c0448902510428401c203201c800c1c81301c00b05103040c48003110b4068030b001b0184000403842041d59500050850345c0181d0f1004003101010b40648030803003524459021983d07000d8004e5103807803408850702e8000d41101ca200b83c1c1c011010030000016a5481018501804403c615030705501034040e07500856103541d0f884007080c00159074640000c6d0010100390f0b08110f929040104140e81c810104140401e141c2c0c025502c014500680824150b80c00a1598202c00c401e03021941404204002c0c8000c1e4001c9220310110844943c000440b03508111001e801d400060301031071500110195070f1072003524001c0b03402c2c0c124180c00b0f8040100341 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 846095665 1250 846094415 846094421
    0x604090527070e06040902150304030c0507030c0e070f1e020f1c23030705070f0209070908011d0c0d02011404030f0c0e04051c021603152d0b04090204020715 69
    0x10070412281045141b02c41e901180100c030210804280310b040100026003410f004007480148154410306485401e030310380c600007880e4002c078080c42100d000404c2c002002203000b84409801610540c030b0380801c1280840c811031a19a8446890046001c0d80359404c00781030040000115648141660f800d48081303074200200980340e10b0154951100c0c00c410481804409a0304072500103500e40340c42541d40d001c50a0000c400c1c028500001d422420080c10040b03019803080103501590baa0b14001e10503400840703045004190340540700500d40d042074170822507a2814074904c540c0700d071044c1008200301c85000b81a1a154205a1003621100c8800d0381010402c109540c4840c0540070200d100342940c01c094440c1c40d580c564100c60550540074048801c40c000d4002c011504e80c450014110f0380d035580d2071340303408000345a4241071014501d08040d11445c00f01a040c82c42d141081805405004010b250042d1002a0040070f064980050307980118a0243e01c1d02d00081c000c00d4043d850302540711410107540011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 846096915 1250 846095665 846095671
    0x405090f0d0c031b03030b12010b010e060a0206010b031305030313050d0804080a1d0a060e0418080a05130b04080c100311090613091d0712020604090527070e 69
    0x4000d1200390302c10000c0d400101c420444125000c0142d40c040d220325094004008012405607c0b0b050090090030500c015000310420a0080e40d4102e019041c00080c88818042c0001003800b40c0c0082c00140300c02c04940c40590343c030440b1048144030741c2d641600c0b0700703046d035205840c1c1c1274805554000035000d00c8001c1000020804d0a40303040000d9203400c0d00c0f003044502615401c0f90400041149445410619600255100c0c800400701d22640b03584103806403040c2500c8116901442c2401c00c0c140607054a800195a880c1e0040350282ca002070b07001d41240c16500620100c04110328944c8045030428500c0301910147c00164020308144040030300f00514941c0703585a141c20141480d00d0744030407031a90f0080e80c07103210080c0c40b07445e00c403a14504680030021158104480ea6462f080f510344802e0b201801299103082d01e42c1c2501d1269840740f07050307018003828600c081e401040401c0108643c651942c002c42e803041504030310b400007900d50b83c40c20300310000038504a100c3e5805036009014010403c600309030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 846098165 1250 846096915 846096917
    0x100608160b07030e04020a02070b0a021b04020708031f0806070e18070504060507021305100510091401110a1208090f07030c06030506060708030a050118150911090405090f0d 76
    0x42090015a8014640d00b04d00f01c0160041e0340104204075420b008218147c0a05041800355480700c45004000790f0b196071051002c4440c820395805040c40341414800c0b0341d001c0b0340000c141440c40e52509031581622035800c0d0401805030340c180002034106814003086024060958856803030301140010040c42c08035a40015100c020204184408150094111004c86055060654861486000181d04001182100030351103040508000d544100b00d541030043e07400c12245a0040d1540308001c0701c0303115a5000e4a510305080d03010050f45503010307000000340003902d0421076402000a03622074090600c00fa4200010407000b43c00c2c06000b820511010341d00d0740c5c0281c02003c0b50752030760f250b407250b0015502ca00424140c0d144040b43c01500ea1204071082c0341e411203640c07550390a1280c0800d0041c44244151019207040710100c0445042d68040e004164440d0601550620b0420603280d0061005d0401311603695010440101d103070f03d5502441d8424103100010301901003042944034244505064400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 846099415 1250 846098165 846098167
    0x50d0f090e162606010e0312030f1608092d010c020d080a0b0904080310170c0907050a0e0f131505180907060f0306090204090902040b12070b0c100608160b 68
    0xf8200081d0b15001d2540483c1c01d1802403141c100c00c0d401319081151400d480011100c00004000c1991070411485000b101b41c0c440e4003d00070f003110422298903905980c031440903000105900c15040c10000e9502c2c0c001410760513080c9040c03480c29007608450600042402580100d81241095074001000310b5110312500c01c240109258040040c0070030b10010002000f0000100202d006803c10981d8070010f840c0d42d40c041c3c082d1501001035a507a5020b2608218400c25140002450700e92044050310039110f030300e80715440c03043c00d500201720003174104600d4941c008039402c0c0f180d0000501c2d40600f241e9421400404a10355041000b0711207622a00d03956044850b94010a1010b0040c0014161046410303e103440400c140311a14200c02400e07050380700c07034011400440c02142d800101d07401801300c07074070884007004001100c100384802150180001c04c142d40007120b0800c8816000e10062060408203015914800361541d510302c21501c603074000300c5440e440045d40f059810107a034803100180003011846 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 846100665 1250 846099415 846099467
    0x6090606040609030b1317030a050a0605060f090d050105070e0f04051302130605090c03091c0f050705070b0f03010f092a020f06042d050d0f090e16 65
    0xb805981c3c4610006103903821040004004182c481c0000c2880c66004511a040e4946110504007980041d102d400003940b401020542480c011301c200000c4400c0a0a0b0340d08040701c006410945800056880750441c8005600100040080c81401d128109136190320003038040c008240b01440701b04012880c05140740005000307502e0a0003251115031541200c04200c00030300075181001070001580b141c0c0e00030b001c04041c07140c42400c00000e0b500c25071214040761b501c031091000c40d05034010141c8400c80070850840e00c40303105603c200000c0014502600c11122242e03035a114030718071940156000011000044014018880380c2c0100c10010003d042c1c05002c000c0110030211040711000c21854251803c03103604405032802800301ea588400d041d0182e07541441d01d42420502064642203254101003001504031800d100d40f010105403030f41120043c00c500350400e07820380300f00b200d460400040c0420110300140600300459070301d02c1600c3e04c41c008101c502e04c00b07001170480c00c03420403001000003850702c1d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 846101915 1250 846100665 846100667
    0x203091911040207170a080f09150601050315060f0c0c1912020a0321020c18010b220312020607090308120a150303020c030709090308070e0414070305060906060406 72
    0x284648a070320498005941d80020700d0600c0503103c000d40f060802d50030204580c40841d8000107041d100f1414468105034079910048125252071943c9106850a8801e0740810417079403090b009150320440c00211000c2c0c028144c00003c1d525004490340482a00c0000303082500150709200046061a003075902d0b010692200c1c4a4000e00c40041c0201880042c0c069100b4003076513501006e00b002150041a000401c01c841d0f28003001e20b140c000103110140c4200c0002c89000d0528000103001002d08800e044000e90800000000a078091021a080101d17400e02d9a0b40103007840d102400114401d0b44881040101190064188100100030f142031015003c0100302060300007003150900f0f242c0000c4140d8070355440310000024040782c010084080d2804101000705a00081d040452441c01c030212100103940704405c0041c1c504d480e130001e0010700104d010a00060040c1e840314207038440207001003040140b01040072104c85e03046901d00006500c500600103982050144107422000c1035481c2d074941030901c0c7d8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 846103165 1250 846101915 846101933
    0x30304060f0605010c030309030306030b0a0f0506010e130f0615050714070513020c070906090606020f24040305040302061c0f200f090a030308010e0f040c03080c010e010f02030919 79
    0x10046c1c1455205c8286408152207903000c1c4024503801600400d036400e11110303c40c0200240c8840880443c0350401007031403503008140c010800780c3d00500112800e01080c200002404404500a045544078080410390ba4000886c141d42d04289a98658841381e80e401c0c0107484403840010f08510f81c0107103000f03028503201c4903520010305110303030350160703566400046003403500d0083e5200303160301031405401250116040d08540f085400590841d860608182d02044e100c164103407500c22800341091280d10b082c244186140ea025000741410787c14103640350003140403517120080b4058070f05d01e140840026606180310b00c81e0700301d400c0001001083d107801448580400c00b5907001001800200e56041d02000d0303201129180400902004440c554034600907203803020130300550031001c0030000020400540c500040303129075000038100400ea861a224402e096122400c0d00c1059501d844204180c00340900441403503202c3d00c4e900607603034501308000a080c0302e0400360500e9010300c1c100039840400d80a032 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 846104415 1250 846103165 846103187
    0x1e020303030109091524050906060702040b0109150210050106050c1b032805010506150d0f14090c10030905070b0a020c0a2904080303040f02060417030304060f060501 73
    0x2140000c98511034180710005c4000e901000c5100c030300304159288911000c52079a041403080440d908915030316070b0f0402c6175440044030816080750042c8145009441d140d00b200c01801c44c18184500310940320384404400c401e80c940b800f00568000d920035200842d5900c1542e004002c640b816500b080c003860401611187d405000c4410711401181440c05a41d042c49850b10402c500700b804a981440f118945402c03496252069619518000c002001760801071011034604003040200392401c0b05000803140100342c60064030451a45d82c0d200303101610400c0c0e5000740508079043c020605c40803d0010010040c0c00981e0b00810075041800719400603a0000b984000c0c0c40c5110840da0f1a40305001040b40b41000b175048241d4042980704000031015507218205003010110f84585001e481c26007403602041c03045205d600300c40e5104100040200c2d820740c5072821100d00c001c0030303146410b0365060f10705501d50035001c101009400000c240400c0055911420900d2905e204003800307620710341000030f003080c2514 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 846105665 1250 846104415 846104429
    0x304120914043b0607050c120a02030d090f020a0801111e070f030908120a052704051008060a0902011b0510060b04050f0102011a28121e0203030301 65
    0x280040d060148568280f80d421110740211418000381088004034040e1110006810b40e402480080341c41a0b20440c00c03100030131901001010000200c051000c5240d0190561b24214001400400e603400910702421015038011301100041c2d10080c010030a0301040d540c05101a030389003e405800c0103810b003003a280d50141424048080200c2d044c0503070703d50320683c0c4004044803c4000040105a001384440c17041e14400c204a4402c001424002d08a41c400d821866001c00c2c4140102507000b880e240d80c0030549081c1440702031382c2c25000d00226003a242d0540b4000b0010f440d81600b4403c4070410842e403540180c11030030902c8410700702c0d0000703040750594180101c206040a0360700703400d01c0001c2008440c001d001c000200310085e60b400001c070741504903005480c828880c4e5990002076603c1400b8440c0000c20b020181e02c030f0044585d0070011600d40c07840d000c110346519040d00c8503502e5551000c4000500d80c800e44144140300303c0c80c000e4401c045100400410b4540a4407581c0580c0307000040e00d042d2001c3d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 846106915 1250 846105665 846105671
    0x5010e060702030a2108010e010b0409241517160804020114220501110601090216020301050108030403110a1206090c0e1f06030c02100b0f0d0602030412091404 70
    0x15070001c0b0781003a001e60030152005d5a43d0450351a549840354500b03003a03c030381b903543c0c000d240d0701c504005452507000c1c800c4c84044202880309001e500c0d45603001100251a02074640d248000c10000d042c42c080e0991301c00c0b545210044582620190080d8085008016000c10b1000621b000308101a0003461076070183e040202c41030002c1c0c11039004620800e00001110751080d140c428419a00e40d480c910040e40c0c00035100828030001321940240101b01c4110b0407000501456800c001304c48009400020110070198007401e450005038400f84945e034080c180c285c020b0755680d415424451501c86076001071a00070310400780100049050280110201e660205002c58520002d0501142411803900542c0d807030340c258414804030080e44076804100b54001c8130403003051a91100c040d01100c039017664820158018040010148030a54011440781500801070b05042ca182404036001900c120022240c1540c004248404e000c440a800b0341103002c68640141d100d4105002560300060b00b074429401151 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 846108165 1250 846106915 846106927
    0x20709090818150f191d011d041d0606010f020a030f0e0a091407030e0c090402040905060702030c0c0f010c060504020406050301050a091a06011e030609020a0c15050105010e06 77
    0x740e800580105126403043e2151214001159004a1741c01041c2c008a021428521115900d000d0858114200c152904020749800c580c001034881c200300e1003c4900a204070756030300b066940c5621840040c00300280340c001c6c95100c11243c082c5403140c00f40850341071040800701480720541c0080d00840d2268949005004185540e0058a0b08060005006d038440c1c9100008104031003241d00000d00e284004920f08007603182c100381a800c483c51120301c060150480d0306422500d042c4100c005401c54400b030000240070710341d919514180b00b4180c800500580001a48030b0a280c41000120320260085031002d0b00c81d0304140c00a0115003048070010511501c40c030020b0f00f0340d5200d40c05203000b400081c5c000e1205181000004004201d8048204c4400c50006940340180d203801394004d105410607112000d80700b42004455400d0900303000d041040503141c0101044031001070000e0486072220b40c031040140032003443c0480e09040f480c1228401640b410004020580e401508041da040d011b4520b207688035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 846109415 1250 846108165 846108169
    0x9010c0818030f0a0c06091a1321020309030604030206010501110715140705060a0221010f050108040f140c090c2a0312101406041a13030b070906020709090818 70
    0x7405c41e200508100d280032604c8040c401d40301d40c40c0e94040416034049060356075000ea84d964036a42080042d099503d85190701d20000c4034406113200030a180c0c0101c0c0d0030080c0420009190a104480450068120300010046541c0040905d9034401c03075000034110031400c2a80a050300c041c41c9000c801005591089901d40c103034680c049a41c40f640000507100280340c28141c4201a5021400d07140c4407070000c41d0b007660701c2c00181a80c0c5069031903804020360f406183c03e0046490001c054016146440800d010030006005c400003a0f09450700040a071100800101c10819100c1000745851a01c0c20204001c3e0160f1803107000702182da1205585131418150f411030032510b940100301d20266529420300074440d507541c5120641044441d50f0019503660070001051003c80d004500c200c1c40f4041c41043c00c0001003a010010740700d9100c422a1034900326699499034003001c0810765813200480d01490341884516414841c680c064010f0070804d0002aa89a13625000c80c810724901ca8900c40404408900039 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 846110665 1250 846109415 846109427
    0x907092d0e2215150609050f011b03031107061a06091020010e0f07091b032a181a1c020d0c051909061407050109020909010c0818030f0a 60
    0x40e40040804c08003408101028200740c0030b0203510013090001100040714600420955034400c4183d5a1003a002c40d13040c0550110108041e040741810384038000c0070480900000a8150035004101c00b0800d480c0030712801070071201c40365045008500030007606a9548608450350032901003440c003250720120840100c40c40c020125000303c2c8650810f80c42d030000d041c2c000b5860740255011801c0c1c030140c595481807182141c2c20000031010040d4400c1c0d242400c1350181d4020003601040f80328a03009190750364030340d1040b2a48015102c1c0425020200701c4400c50300910104040d00204896051040c5514150075060250341e0588861240d0b035800d0f80481a010340603035042280d98441407101020154001c0d10076000b038a02d00c29a0b188040149080c03031300c02c1190404840b425194002d800440320815025507200000a485940d283c0030484010780f01d0002540c42048201c000050710082e00800921204000c0c10340c40f202c01001640044801000c0108c50207c44006a03544e51402031300f20030740d88 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 846111915 1250 846110665 846110693
    0x703290301140a0e06090a230f06010e010311040c08130204060503010e0f12190c050a0f080c0d0e0f060c070819150504110907092d0e22 60
    0x2180e0003000a101c02e0f903620f07810182c0401c641070252403490362403082e0a540c40c80b03c4032004c0c0c04450458501c81c1200f007800500701c0d8080100d420340d030481c04036410640c5402000c2e4005000c2c100707048010400c0c001941205607a07040100d405001c449030704600281000409080300341000003801d4001c0c115503d03640100c0003080c000c0c0003800f65002d10900c0d40c1c2c031480030345074a0210f0f0143c1f25015040d4044203040360550104485108070031803025204039214042242e0481c3c0501c98101c1d014041a414040a5032142c405c44009a030f8004a44000741030481000c4074109018400c500c2c100c650f914000e03807180c00141510142c1d15401400d111a01d450303002d0348503088074001d800e50002000700d0385200d1010640601c403e01c081c6501001000f048900031034000e8070440c2085403100c03291404200b88c41d0094814505208005e490303810240700305002c01942a2040b00100130310982202080300c8400a00403410f061000d80703414010300e0144031f074080f00c0c1350035000705921040401048d4026615 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 846113165 1250 846111915 846111941
    0xf0c0f12060e04111c17032806031502160f11060a08040c050916030c03020912070503120717072103020a2d0e0307030f0f06050703290301 61
    0x100d10300b0f050600040410500045900030040740ca044640708080900300d122540e4440308001080d840c0c1c00f2501819000030745400a4075615808216408003040b508480c0340720900f200154840c03a515118030400241c2d603400d00158010b02521181c01c80c50300702e00d10803035000f90000310409031a14010302d510604100c01940680085441c2260907400200d09101d18811084a001d90fa140c2040040741c120031a0860442e0b40e26030411542640b0030380000340740100300d00300541002d0112000510015181130945049e91020104000350328041001c200c0d41c034080b9032007a260103030f0341d141c00d0b0100e81c1c0560000d001030400940d617010041c2c0d40b04c0500503840d25039603c1e8408009840b004029500c0794110500140100c03a81e6048a04060081c0304546080c2c0d0020170310030756400c016a000c8080c204403680c1400348820000c003190303400c078490702200c0c03142d4420608002c041c908403048460103803404040505e003a00c00c0079405c0c203910740001042c810031796805040c0581030000b409031501c100d401c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 846114415 1250 846113165 846113189
    0x2030417031314060c0421020901080c09011a190513120b0f3607060f0f02062202061c021305041104050409020d0606080c01030f0c0f1206 61
    0x8120150145058492195041e494100030403503d89903140811794100d0500070f01080b0401c106403140c08000d580d0300c0c01c0c51600118100c59000540da1000c240c1c806c58072900440c9101525150205480c1e000d0030583c010182450b9210984018901400d078480c12881c0e07074100100c0648e40100309941d131301c00c580034104140e240c940c0e50348402c0c81c600c004102d4428800101096010318907004241c440c151502482c0c3c48000c200d5071082d0b18817031140c640c1d000c4551002c0480c010701c2060001c880600015203070003541002c460b10003041141511500c40441d0803000034807400c3d4801c424001c81104501a17018040301d11400041c0d52841028020344480c0401d90b4050b80520361900a4520742c0845a042c14000e43d60b0000d10058805840d482032000c00100410300c428507007070780502c0b2114006800103060100c1c6a80b02c04c05c03504690072094003580898510501513030305005d080c01d00310402d441408640322080d0003420412164103141c00f444040009943d0803581503101c80000c0202498075 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 846115665 1250 846114415 846114421
    0x408070f090b03150a02031e01080d090510050301060305100810061701060608010905071e1d010c05031801021614090a150b0702040f0e0105092e0203041703 69
    0x2010314a001c0c030811001a04010360340a0919010448800e02a001c1d0203192040d0703580026a07009600003410f805807182624030340d4900c405800d60407030180c640d01c0001c1001040c0d81c04007500940c0c50354001032251251910081146900c00190380c1100c0e0681000702d0142c9417a103192280ca02c072504005654407641610040f182d200b0740140045a005196101c003074854100782074240c0d0018040e500110f04140010004003a03254040e5601221910b00440744002c00e2660013409144002c00ca00019604440d8022610303001a4041c0020f000342000800401c0e603554507034890180e448903400c010724208450520742d009000780303010107407030b480c41580441c2c4030516019041c03815021180070320013181c0003d03d2544a441441400070358148160111880c1c904d03102c503039a1006030b00301d8002d030303c5001d40c00c01c5941c01c1c0100200030400c00008112032603d110921301d8051018001402c691a626a0b044900907000e410107040d90701082c056540d5441d4140328240703020103001d80c02491000810 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 846116915 1250 846115665 846115679
    0x6100806041404080a120c0203070f020f0604032108130303020a0311040b0705070b030405070308130914040b07022d15010806060901080a0308010e040f0204110c0c010507170a0203040807 82
    0x902c3c0184646d1281c0110804006c0d822041300c601d00c2400c4050382c07040210802084030280100c00310f0b071004000200055494010170081e0300241e104032650041d00e00380300648141c0000031b9049035424600001a803901020201c810108014081c0c00d05070700240100c1464440d8000030307120510201840e07941c41ea144041011a4404601600c00e070059002c0410000b0307400040700c0c000da4000340141142411600e40440c07c1e84000c20040c2c460070410b40000700e0034607030300800b60090040c0e4040e2400e0310745401c1074000003e000304440211b422141e091072610600014035a80004698600d105c448a888541c1d46009481a0401c0d030b994242e400024127410001006841f0b5a001d07200034141d0307640c881030503503038005450000f0081201c1000500034010741800d01588240500080700001d600c94010400b15100741e050804503210000700800813810030081194843d0007864010f00c1c00000740c586614000c41c5a005058111000070500d9040d0302c2041620041e0031040155040a81e0701e0f14 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 846118165 1250 846116915 846116917
    0xc0904080a02010f09050a080a110106090603061103040c090f020702030102160c061e050d090614060907050f1b15072a11010e040608120915030610080604140408 71
    0xc5690700640c00c24851a50103031840c000d1300b030720701d500100400d045406552103984540000c00c0600400c035294041c4010982c00340104002803c203070a00068240c15420620140c809d101442c4811840410900002640c0c0d401d02504030303003070180005441c1c10051540c802a102d00c0d03c01950541c008614030811500035401d45160b28803a000c00d60246036140b00c241e810f86190403c6d142408003a034020a481409100241724002c1036040010309110290303a406c08895180403d40780b0002c0c600d04116880c02d020326003603001000ca00300541806401581e00c000352280344405007011918004030104603e041100511034452095100410b1030810300080103c0300110141d1a03140d0b030011044000c46100726113690994015071180100104400107444209544120a030000d54070b03000058804004c0c8131441c5002c0a000c2400c2d035403c440001c0205600480040f5408038104100344085a981c0410401b1490580d0603c1d141564640d0002801081007d8448900f004060108020021018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 846119415 1250 846118165 846118177
    0x30712030815090118180c2309090a0f2303120105011d0108062412090d0e2110020d050a0504050c06070212030a0503070f020607021e0c090408 63
    0x306105060052031400c208900500f03202d00d40c46100500c40ca9516200076801c00b00401d01d06c111801c020840990703074003005041c00e9226600c82a508003180e80da88070218802462030008a5030104241064200c168070741c0c904403130040c502841520010200304c1200c0300a10200490782644413140c103121241d64499109441c5104203501c10000800c0547c0600b4107201c0085d026001040781c3d03554107006461030b0034007608075623120f0611410f000c3c85004619030f252a00700c4500e052619035450f420300e105072000c05000802c0c0da030860004c11100c0d076030140c00301240000482d03851444100e1041001c840307034403e8640099034007030300d01a4240c5000540080242501d07045080003d17a90b032004d15000c9900c29240140650042ca03a08034141c80c0c0b610103400c4c0030b40010240086171014032100c45c615031140801d01e0225002200f000703400781d040b0030b003100100418006030002e4074003080000d407901601d010460100328928000143c1c00380400c002c031040343c1c02400740304140c1024181407a26070000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 846120665 1250 846119415 846119431
    0x21060a03080415021f0b010906140d020a050702030609010209030c01020c06180d050f010911040e0d2601090507020f061006050a14030403090e011401020a02090a0912080403140301050f0f0307120308 87
    0x2030300003027042c80b80c41445071030940304034160300b00790304441d410000c1e611640c0f185081060900003c4c02603941840014001e4101200040e5151204810b0500b00440e0480160554002858003011078940901f1540444071408821103420310840004503141d480b2503001d0014841c202c40781ca11450151b100003016030050049085142400c4204020703a080c85181c03100680241c1c0c00000c5003409401030ba000c50b0750720740000c290481202a58550240b09070300041d809a103030001e021490750103119040740c419141c8091b00e9a490600000c800d01400c900c500070800c10000764044815201d03054141d00d204a100c00035070340341800d08000709846803900507803001900400001942401600140420140c180c0103058950050340803c09200c0b40100111429a203031885400060402c4540c5800014a070f2103561080c2801d04005042e070f01d400c02801c42800c130400050043d952203480351400c0480844080030000a100046802c0800c00d5218040392000c0c019402c040540200202d40b150701c070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 846121915 1250 846120665 846120677
    0xa0c0e010b0a020a02090402010306120b0f09030705061b0d0504110a0503010b1302030a06030f0803090c0603010e06100309150914070e1b040b21060a03080415021f0b01 74
    0x2154400e40080c800e0502e1030000d40d03c00b1560b0001400c00408544e4440d005040c0000d0890707542c020303c0c020040142d0200d42c040c45003801c11020b2000d40d84002d401a80341d9004504000c0c60b0f0740d0b26503885002070844041d221460302001c0003140b0460449140341d0700c0650030700103401c09280100341c12003030006052050035200c4001c0f0356070405225502c0101c1005180a05210042d80780c04000c3d8006044000d078245c50b00e0300817010400040c6020090351050445550301e2400c440f02c0c508100e1540c4150340700d042f04000402c09401e1145240d03401c51011150f0140e060401e020130b0340113000c1894010310300c0e0907900007510701c0c40305640144499805400e103191002a010552612540039015003d4028040e8000c10859059444200312460301146c2107031070075445501140190f04082403d1400360a0120fa6280084005400c590030860907940080c0880c25584c07042d071140650f0080c92b810712021001ea1842c0d900c00c101c90703260041000800ba40420001d0704003800340c40c9141c402030206030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 846123165 1250 846121915 846121919
    0xe0717131a04200109060e0a090c0f0206010e0903120712060303091401030e1504020a1e050f0d030903020103020a03020403230f12040303050702060403020316050307050d020904230a0c0e01 83
    0xf001c0645580e0480141e564050003410410190352030584180d2590b0170607480200031030300340e829100741b810001094888802c1303682010802842c084050b080300941c1c40404d014099108000130646840a00c1d0903100c81c081c2c0d403030410450780c0c031008a03802d00b071481c01c180d80001030603003151840c2d0a40340c84da00d10030500005240103400b901c2003140d21389510b60002004101501041003243d410610080080b03240f540d940c102000c01100c00344515151081c080010400380c5010b0401544c261026076425403800300744d44000d010410948406414103400160881035640b00b5411100510340c003108810248116103800350001813242310750342080c03080240c40074030700d0800118011210080e4285520b03103030465500300d0301ca4010000882c3c008009104c040300582e010300184170351004481d980c0c00014904010103180031220fa0009025040180b1241d000d80c40d11a90140d1140d00984450f00350381d09000d607101c55200b090302044040c050b2003148000c2202003c02e40c2e0403a084403041c0c0c080c9907 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 846124415 1250 846123165 846123203
    0x6010f092916030e0628020a140d020615130b0616050a1112060c0a09180504060f05060f010315080102070308150102010501050d03110106080304090c090e0717131a04 73
    0x11146e407500301c0340c0e100c601c0d5011008440d0410403003214140c0e03106803600c450700e507910a50200035940e09548103802846a910801da0304100d120740c44650103107030010300f42c1600302180c002d11542c10b02c020460340719130f82241c40b51150310454880819180200c02ca11200741400c0d500c0c0d107180c1c2d90803501c00c0304c845140b0800e407816034800c000791203004020746440e480ea00303d04442ea902c038498075010b0151110317001a03100d428804070300200609190110f054505880d1010840b40d82982c415485440c0909000c0c0903124048041c101400038240004d46102c00f404080c04a112030340b203c2e45640c000211003042540c0240c0c41030003440c1c0c001400981e0380c65280103909032a82401070940005072412094003203440780365202000031318500001404c1d0b8603116010700356801600030b501d0881e107842a000a05501140c018010003563310515014140ba2100070103144902e45844140c0c0c1020b800321b49640503143c101c040c09a03210022000c0307000c48a03800c1c817020200321005c0c2c03001d90401821480c16 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 846125665 1250 846124415 846124417
    0x20307150b03060c030403020a0b040c0602190822050409120908061b0d090f0b01050109140603270601060c0605180c01030e151e06010f092916030e06 66
    0x50a001400f41c000e50f0b4650098000503003009205a00f180b29614170311001c900d5421034140607900a0004004070750401101a2030001d18812080401c4401c0102c03c02003610350050303a158030000003030f0000b540a1040c89201c501c40d00d400040c0d20030715000700d800420051340b040800c00251900d0303c994240c0d94203042900d1300c1040740e1159203a480c900340900c001e05000300400180b0440f0400203100401030301d40303084804112004441030050140103000b2581c2011400005107051010342c1065090380d40030650900028003280c5000c85005502c0c0b5520031512403c03c1070b0311012084494139030751075000815a00c1d14400c160b501d90b1524000c2003d07115510240781d03800416000802d440071f44040110700514051803001e465009800c411020002142d40c03250160030021000c9604017681c1c4101300162001815160510445480280c5800c4c0c100030701408454400c25031224026001386180001001909240c4102c4000551405681c141606000205000b40d4841c081080d112084c8002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 846126915 1250 846125665 846125681
    0x102010513120503041a1801050c070c030b0417130603060b04120f050309151b4605010e2122091103090c03150109020904060b0a02030715 61
    0x19160b801440000d040c01000190780083c80f41812402850176024450042030b0190303500320040d884804240c42c00c000034004c840e00001d03207507581407802296640b860040201e5200051100c82590b00060600110001c60354802186440095581c0d070048105c0ba40342c2903034000e40010030715149000c1803040300c002c16a41910031030b6680203016030141e229106405040d004c2100c1c24407007085501c40d583c858180e00001000f0310034903551644150f140c0d0300c040c81c0c0c4004250340158001003400c03404558418400e243c0201e40d070f100c8800115510507840ca58507000304903135101842000200f003040015440300603442940001e40d400c8512110104180c820345501c0500f0380321060165103d00d07054040b9007200304050041070f030741d501e9aa007229000c0e61800448400b01003004001c00c10740140c1441501c100c04000c0b400f801c40070010b000c42e220310080c18010540096404900c1c85115201d0741e1204001e40580c266a03a20ba56065000942c1e07075204500841e0f0345503801c2c1090301c4150460180d0a0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 846128165 1250 846126915 846126923
    0x11220f0807031104020711040c02010915091e050a050d080103022815031e090b0c09090f061206101a0f0a110a0f11011119020919050f060102010513 65
    0x900583c4030812002c0d400240c0140e80c0d0400007484100d20b95a14480c00a401741c29030004940c4c5003c81c1443d001a9042203542584c00e03042051070b07c002400309002e600300b82d400c550485004040703414901e1a0416842000304140304000b05150300e0741c2c0011155040f6407003140d00418401c1d843d1000e52181c0410303002803020070144e8005000b01d411420046490040c00e180010301d840b0340103000c0140c1d01d460394200c3c84c0c02d80e441d080201404103074259560300545c0c5580880ca0001403d003c01c0c00784500800264256100a01181255842c000191407031040001217500300d0074544042003c91207070b80710340340c102d034925105d40050100900644007610f2941c0d13621410011801000c0c0c601c84492980480300e0701401800000040200340022004d500483c85e084e00b2141c2c090000d80299041600c1400542c0b080300c000a000628040e071481c2c0e81d5043e03813540c040f41c8804042e00c81103045480b440c1500ea06110803c2030007590150100c0c03154070268001d0000d501c80b034620000520b41c0881c050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 846129415 1250 846128165 846128183
    0x12030b0f0f040e060f06041b120b04060b0304060c0207091802060d0e030d02071a130609020f100e0f01090e070f050f1804110c0a0611220f080703 64
    0x21805141041580307902100240000c01d81c081e11082882c100401100c82c10031003000b04061140c0d0382020311404540724a690060801950120340140600b1001c0130200043c64039401800543d458540081c0d00412403803021035141d00f010300d0900054945412104018070594030002198051401029950900742c5200e50007000c584c2c00780410ba03882924840f00b503c1e280c11503c1c0b8414030800041401001000700181c4401c603e1400800f0f00e040c00b00c030b0344400c1000f5028850100c00710310b080c003c095880440000d40b03800610208a201c442c2032602a132001111042656a84d08503c00e43c903814801c40704a01c031842c00100541e03048500b0301400318600b00303401c001403480d0b010f40c0504604198034240141000c0d1030707030b8020b4103592240850307501e0100b882c0b01000690404d8090101c6036086035414908006282c901c2d80d99a03882c000001d030140e6103035041050114154400c8642c80701004040c030220b59001c1700b400c03054007201c1c030400f42c0403484075100080b515804546502513030b034018091 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 846130665 1250 846129415 846129439
    0x30b101409030f0d050408070b0415050d1b050705120304030c0f0c03020607080c0f0105071d1804110907020a150b2d03070f0b1218060a0203010312030b 67
    0x202580040e02002e400d0710584108100c2c280c0100300300c2c1d03c4140e00f69202036132241407001090500b601075007e40c10002c41480140018408103a810820003285e2404644851905080002400c171900150641e88003890407000116840402040110700503011114001c000100c100054801142c002e400610b100302d14030b0020321215142c18200740141200d8142d540c413a00011015030040c1d00c01c4565000000c0d900b14140340c14052088420015002088646401d41001c0c00200c40380358081440c44000d046485075603a001500d9204428032540796940b41f82501d40052090b009452a0b841041c506000691442c8000b40c501c14450b8028120f40e010605900f5102c0a841c0c0551080e900c00d10700190b40c141007a0380308c01440ca14600c003261400e41e0046505150909205030041c011108002030b0510911a41008603604521001c12109490351007428100e14075049482c400c0d01c0b03000c2e081c28040c1e190071a4011f54166130003203061006000387c28005400b183c048414030354200301c60f6403070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 846131915 1250 846130665 846130697
    0x926210106171e0405150f0610020606030706050a0306080f01060e0c0a09030204050a020f0307030501090b12120f041a0d0b06090d14190c0305060106170a020706060f0b0901030b10 79
    0x1054004c0d1280c01113520203a810780d440d1100340400c4034000d0310040280100007070340c07401a8000408843c40d002401c1c00d0b0a040002ca6169041801020140040001e4201c06544240c1c0841d00410580c010b59401143c0300e4815400b8002c00d00c1307070202c1c1c0d00031800400e820000300300c1151070100309901c3d0800f02a10315401d0001034007000b800703010807950a000c250740c940502001140f04007543e03a4009415814208000c0848448013840c5020b12031072068100c10312000242c0035521000c2c0c20780c0945619900301141141d100d150040404406449241004910700c88041e007210004500284810b1a080b420b0028a0048000842d40400da0100901c0402c2918110718019891207050364100608028540d800f40c009102c00c4400302400302c010820b1050512100c0d0260010740b034455001d46100400c03c04400d0080c14005013250700261903402c002c040d43c440300c014000e01c0c034516030f0181c0d034a0b000c00c01070f0804028240840e040c4500b80b1060b1a080001c08102541915010803425200303007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 846133165 1250 846131915 846131971
    0x70606080111250c0303030504020307080616180f0b0d060e040c0608090a0212031c050906060108150a030b190b031902040b0310051801092621010617 66
    0x1c100001001c010f06140440c440c041072101071340c040d0300c0116840c03c00d071062502c0c101070785d0300a181c6a0070080078440360380c03100140c4402203c01860501418113228082e028618a02c1d40210103d4103007c200141c003007a00c1010f001d407582801801c00c41903645140c10031a515003150000c1034210050004d0004a0182c120160050310840c100d0728a040a54045078036844441c101000d1640045203103100da8050106104d0803c140110511090400314080c5554540c007611a6060000807000254811140031000d0f0b010b150060400d80c43c5980d90411410711300e0b0545401e090910990070f408415819409100403440c1c0c0980245503560400c4900d41d840482001c08030ba0050700c41c44030305c59a6904000b238805a10b8128000603642c200805030705804020710a02d40d04030b0341055900404200d01102070300da0140030000c0d204504aa0303100244151181e070b18030584c00c00d0840006204415060603140c181c444689a40f1000a21001c462415900c111012035070848804540005400142 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 846134415 1250 846133165 846133207
    0x100e1504062c070603090c0905041401110703091205060103110f03070914061507020d080c010906060e01080f0318010e030f0d03050c120703151a070606080111 70
    0x1030303800114250303641528000110601c0c030000c0c2c1080340300681c050450051240314003d012509081207a140c00e50342e241c100f0070052060400c00303507450000506003c01044414416401070b40208445003d0001910315504002b400b503001800040011490fa04100500b5800ca600107004180320780c07079a41c41d0344100d5002440b8941103c903142110220b51410007107080a0336441001007010408035518800c9004000c002900c602c0c54084001f4040700400c08403241150140d0b02a01c46400038184248a0f00c40e500342d501d40c0e90f2a0803e01001e209156000406440010340c0c001200d9990f054015990007600d49510402c7d042000400c0c442038180400405c8440d041c14050950300c0d01000090414121080c41040380d00421414110300c1d60601c40c5c1070b404450190312a06200c550000100303c0500140084240750750384241048a00290040d00c00034010040e000408509028001449410500040343d08c83c2c1070550229902c04103009506031001c50985082c100000603581c42c071404064 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 846135665 1250 846134415 846134423
    0x1e03090525050a0303211803050906070f05010207030f1d120c0603070801060e1e0d0606080102160b0f0f191104060f0e010908121b03070302060603100e1504 69
    0x1c000980e545070030380d00c2802180030b52603104054090416807100d41c40506110020030380707441c0d0040914030b41d4505079140190117244c07003038850f1007810100d0050f22841001400502c008801c080421030150001c100551007503540c00d07501e80e0241d8082c2c400580610002c8588501034102c0151410903501381403030444c07101c04a4520001c0d14000ca611944150783c03100c006185c1500602c101d942200603181041c6094541c043c00a0901740d00d08480100c0503811841451528000c1050281580029014081a000031995501c01200000c89405900f501304c0d990741d4600005074030303c0150310b40741d440360b0742008000286644440045861000f944080d518096030f5402c5072024100c13810181020341040d850f0f620105410316005400450101e03480ba0400071404c0044c09030080228100507548448400075031500700c0e01c9038103d09464801045c90301c034800880c240c018154001075a600549003a0180ca03031140e03142c61080191004020307107110543c0118904900c608007821102c2c1c4c40741c05 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 846136915 1250 846135665 846135733
    0x9080d0209030106090930080a0c110f0607090909020a03030f18031b0905090c040506060f0f03071b030c020135100815220506071e030905 61
    0xda405d1030b003c84155074000e40d4085410780e686200c2072075400b0000001c9510900c5c4440d44880c840000b030240314020102c480c0d131500c41910300d000ca8002c0d103030801c40340410300544c0c4520721003501c241c0d42c49400702c580c1000108003000004244400e441303600c0c031903600544140c0c0c13864110780741075541c5482085000100080320050041000310310a822001e580f01c1c5c90b5000b184440d1100030309240800e50410380d603c0b03181c03400b4001e0b20140014002c1c2d40700c50507030340494141e450400007156401540c00c8800b000d04d0008600362601040002184650380c1901c510702d0a4081301408410101e400b203008020800303200380c001c09903001d540711f6002c4074141d5241501000040c1050312220f192903002c40c00d080301202c1800b040070503030180034000e403410381d0040580e0000380494180c034100150400341c90417201442421681c64441c00d412606d41c22608131182814150001454210322880d4480102c241c0980b81d080382d40f2070701031180a071f41c00c40014892520300d03d100c001c0b03004881001340001d9007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 846138165 1250 846136915 846136919
    0xe0105130b070c1d0a050c0f0304020d0201050f1305040f110d0b0a05040905100c1b02090a09140607021b06121008071e150c330209120109080d0209030106 68
    0x208241e03401007040e0b84411084141d003885c100305800e8400103131140705100801d0200d031020980441c1070341c5d4046d8040b1021907402e252400141ea04d4820448005840c00000810660740414080464201d0b101600c0412071b00400c010f00c40204e40c00c2035260680c4003410414454541e031250012506040020014190035a0340c40005045a00460b012a00b075007203141d540c402d0346014031402882001c2c41c2081810410f0102303008424240d4180000c0c4505c5002d0046902183c80b58020a038140c0e000c101010140a107580082e520081285d40d000140304000001e000116542c034502006000a0143d0341400b00320000103035460310081603d1003e075003c50001034440f000708202401050074510160b0303980d007110340030425101c451b0401c0c1a18040c910000d4285680308200f901c4160300700420913410504010045002000908410302d26651000c40351658880c59000b85016641141d245040982c1881086d003039171b04a0402a044a101348004031061138103400030903421200900005c1c990b6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 846139415 1250 846138165 846138179
    0x40b03150607030903061503080d0f110703210e0606060702010c17031906050609120307050d08010e09010506030604150f1d1204030b060d0f05030a0f0e0105130b070c 73
    0x2030460b100a07000140c0011041051204030711403601000c0769000c00c030b90708600b5511000d07483d1207082010308400d50760b070028801d103048076400004c103118080034007540c90447e800c008100b031107120350310040204030340400e401c2603a41c0c1c42587c0784021480c0241400b5030361101000403540060b813069040c0300351110b004d0002580308850000c8842c101c50842e46070306011a10200720100e07003d441e1316a920300441403002d991007600380d0b2541c0c503080703030300c840090b012540541c154080c07404010218030032040b00e074101716005030310035040e1060140c1c0c0203840c0c3d03610600542038800c140c0b101e581540154000c40c010a0305204034600801211f000440c20417000401e80d801c0700d004404c3e8200d03150306006140003a6a0901001240c04c00c4240c24508043c11920344075800e200181c8164031900e25030b944102007003080303000002001d0308101603989170302511130050300c05071900030f0220016280580343d01c000e40c01501503810718061601031a40003418032100c0185980031200550f00c0c43d00010001900c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 846140665 1250 846139415 846139417
    0x507150c05011e0b01090803040513060509010605070215120f0702031903020c100b010203161a070206100e09031e121e15012c0603070e0102160605040b031506 70
    0x302c14010f0602121001c041c1150407100000385980c100138540c0e10400c003000c030000c04e40b401c1d82d208440c2210801e410004a80041c802c40d400b9a0700984c1000001a0040d0080003900b4040e000b603a03051500200301c2c404504920034260000752044422000c40e00340b991210340d0035800f0980f401100c1c030b402c0c0b402c402e0700e20a80c41003a0641c0001d80000782a02254014011142044003140c02400311030782060020f0344034099a05c2101d040410000107605018841010200c41000507074001e402d0f01300001c009440b43d10440c0d400e840c402c9030722400030b518640103003102d2150305010041d50416103001c07103040d00840205614415180d0501c118400b0309512030790389005503003018850003481e01001c001e1003c010000d0810340f1035090101c440d003141c0d07004400090b4008403840740040c01300060394043e100d49072401569411410110410481c1038000840010580c0243c00712071020080d01c0f00c1d211316004c18010b1000085049c401000308545d050301440d0811a90b8040301e6203080d0f00d1001c1503007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 846141915 1250 846140665 846140681
    0x6032a03021c0e0f100c02030319140a061706040309090906020c01060e091b150a170c0d06080712020f121911030109020a03031d0d050304050406120507150c0501 71
    0x519040005010110311341000b00e0040c03030a1096050242d20ba001d040130b034580c04001d2254280143c007080d144003c3e0b1066022000101c1c0125101b007450600401c0c48008007000d000d1816030700c1240404c964020030008040748079940c10b0352085012403c1c960030001802d10b0b0071041350403e03000e00c55000310300000e0103078038003030b00864020000030710b025980300b032429002000420701a1140503203400c09444080601c0c441c038001801e0b540d52055260412526440c52034075101c0d000800c00140710307000c0714500080083c00c9407604140041c0340c0b0340e4441078a5003528410b00c4009800c0062881c01401c06a0205414400c024580349940090090240c142194201d181d031019540e200803030704008105855210010341a0001c0025124540c04207684011070b000140074000791031444404103501c6244041c61200191245072074080624000303a0f80e4005009007172203641044004140740010b00a50059590418010001d01346015803010018039610844020007100c1854080030170424062905 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 846143165 1250 846141915 846141941
    0x3010e092e090c12050c06030f060904030c0501050708160f090513020705060c0c06010e01080c090c13031b1d010b09040f0c18050a05011205090f0d080106032a03021c 73
    0x1869001450642e0500c0708031741121f803040da41481480181c129545000d0303030140007503030303007080710307115818113582c0d64a543e4402015036080200f0480c03084d0f44100004e0044d4010329090880644443c41070b14504400e0394040000303804450200041d24011021041001404c10018500300c0a500c45504202d012039104103400000100c0c8100300b1400c201860041c0a654001803281d4180300e00030f9241d08001c0c0d6550722980d9211b000c41c240c0340903001101e4484014105070006155280317403040b66101c1c0d95880351070f01d00508000140380145c0c456284c2d08412940a00e0503d80e00b4171800041c940c0160f03071030680056031208241184446031042100540054603420200b140303005449440d1a4907811650285a02d80d07410450340e41c02c01c3c95800d1080103520f01054594a000d0100c1c03801808a13030481c45842883c1029050341c4d0011400c0341680c40d03da0b81484400d0107a14240044040f80143c03a00004801010a28007446903015050414001ca207400640b0300d14031001d0240e403c200100d203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 846144415 1250 846143165 846143189
    0x807030c0c091e09061d03040f1d06061b010c090303030516050f130902040b091207080607111908041d060f0906030c04290103110412080f070803010e092e090c 70
    0xf0050b0f1402002040c002d2070008102078020711000e50340a02c1034005015030740115008190400c40002050154907074030074dc04000c00104415503801803800c00c6a100580210f803030300e00880e8004040e9501c54403100e07580d0b21040d190211914103038201380e01803c3c125500d50490480401c441420703000402c0200b40280d0182d854003049810447c00c0140034090440f21380c400c480070001d42101180d000d5100c02c090501003100d050b0340304a1070078168640c6450b000760b48600000380400121601800513140c001000402c4c101506480780140102690a550700c8941460352180300c3c6011811079500103c0a0192100b60b181040807806840700c1c00860142c00c00c3d0740300b00c1c100040c17070b603230a944800500f483c00303008100c0084008013451103a03010f1180d581c80320884140c14000e55004030782d80d1072101130b08aa6504454240403015800a000b03500c45403204070041104030f40002442000d00f407440c41c1611002c1070300c0b40503402d1030206400d0000035545480d4203501192612011100400c8103070100b17 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 846145665 1250 846144415 846144419
    0x300a0207090e0129030a02060c01092603130804081f051509040f0611070305040602060601141b10021602041515030e03070807030c0c091e09061d0304 66
    0x2099502084010089a140514091142e07101508130f000458443c003141c4080f52454000c03034200001c0f860044d40001000401c3c1143c02d105500c10a00c1d40c2c052001d4440091005900e0981d03006035426008160a050010800700b0709100c1c3c01e509524461903999261039a07400080d810551030101481070100c000d13401c0e40c0c03242014000c0700d60140c241e00d0b22203607007901c0c0b80028180e050301400241068450441020800515034400c416000e4201010360320f542a914006096900c50f0050078014011000812419406a2600c1c07810803142c084040c1080800b17007030076549481c090745640d10b910400380c140d44204020703c010100d075000341920b43d0304880640148429103018190080c0e0407480003e041200244805178200d941030b0924010900c1c14100c14a28654000d00304090040319002915104046d000641624030758801c9006181e29136807019060101d80700c4140c20002251a00c4208641c80c019174402e880c0588180750004184105003480031030800d0001c0e0600c001d910016003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 846146915 1250 846145665 846145679
    0x2c010206010608010602120c0f150a15030312050709050604090c170105011b2a14092202010908070e061203040b090409150e0601091409300a0207 64
    0x1880c1c050110740c03c1103902035140c610025603c2528140c1146440000314000004a0051228003504900c10007162455204081c1400f40d143c001d4a116105038600860039007100310f40f0711058201d079010348499542a030f28142900180000600c03da080100d110008922603841202800c041d01d84030740001080a070148000e0250703500710000807901c2d44124010480c0d030782e00140180c1c1d00e0803054400311881015142501010704032074041e2000c01b00100d120074071503156002010464600b1100041c0020545050106801e404e40b00340d1213080032802458030205070b603e450322003035106240200c2d0003a9030350034460401e50250821080e00005a00384104c80c0b8001800110241010018510341032030904036040903c00c400d1224007e5850755140307002e10030765a10101c040101500d041c04085851040a62a49001d004404815140c001991400c4800711a95841140040f0080a5400e034081c0000c80b8a01408518000302c07011036003c03106540100060105c0b4002500100400341c24900 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 846148165 1250 846146915 846146923
    0x220c0302060f07060f3204022b0f03030b0409030c0b09030c0604200105130e060402040512010c0311040f03080d1d0a0506180c0d03020f030406081e01050901060305072c0102 76
    0x80041c409102101c201200d1b01c1e01180e2280c006034116580e800c8030409004100324094103c900d161448411906d40040c1700001400304103c6101b603500708a07000e0404204000c0354040e1134042c00041320b23848000d00007402102010b4001c107460b021a070030132400102591400204035801c54180c0c0078154415507400d0111800e00c900542400c106090114510088600083e0340c840d468071100180d011600544455041368040c01c400b4001c040449444800c20b4060140e0071021000a85000603802c0d901c0f10b09000d03074094070080d540445c5c0300d42c0b44d038440000a400207042c07600c00315a50000803100c5072010616030b859581c08809400b61804a0030001d00b0440001c10f880741001ca02a001515984040780f5040b01080c100c40300f4900e40c0032418101d141110314000d51a55201c002404503403260010b071320034484c425401d541c001180701c103002e90000e16800c0c0b04e2107420003051001407180a0290b000304d54400383c0b40c40e10740400241d180409811410418070410800c040c40561003055034148 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 846149415 1250 846148165 846148211
    0x60b130218120d2604080304030801050306101a040e100e07080f01231003140919030c140d120c0c1e0615090203220c0302060f07060f 59
    0x1100c910400309002e8100c0c0d00c604580f02d102c401c0041481c0098200c0c1c02c0c01d140da02d80c81d440c0f181e41040030b02d0a0b143ca40394a40c02035505401080388480001094600026980d10414200340c014003940d240a642c1c0100e10200c00b000f07401503009120100303482881964440c401c00d074414011000740d03d011502c01c1d502102804000806c01c0c03120821400c8195101003a0442e01c00030300d010301a619400c80803401003500391559a0159040701074411169154114105503001c0b00c03000310b415141c04029a5603128040c2074000c14403007021138075000c28007400b95000c2681c040d064485c034001244000d1810080f5021050002c64601544900f02c10f10f2031040c07010403c03103400c080c0c42400503034179140132a0344444001404a6400d00140042000b6604071001814002405410036910751080c80e0184d0000c4510301c200180c03800030741d1151003401c50107410071500601c1455100d0b0640c3c00b401035540c03084459000011003008500002103070386c4528090030000c076400164400725290030304a00801c43c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 846150665 1250 846149415 846149419
    0x4081b19060e060306030c030a0308060a0f080703110a1a070605010e100b0f1c09020f030304060504060c03090e07080411101b020414090a0b160503060409060b130218 73
    0x10409209860b0014804072100390304a8080340c42c0d6541800181c50402105825600b602800d121402010f8018003140d019040485000912035210f582c001c060040c54442c1d40030691084000f0004111503180c030f041200030113480040c449484218881c3c9020001c4110205203000041c4901032103668410304d40074020704480c800050078605c00703480e0210752900030b600e00104000381024652401d4007c40b61481074000c20980c4400490268030003c000110007a030082c030350b00e41c01071100d00d4080126015606a9140e050900781405000c03100310f00314840440c04d10680c0030002c210801041040c0c3c2c0724407020782d1800d01600c1c051511500b4101d02000080c001c086440391881c01e140c0024450303000039540070314202c00803500d0001030b01500762a1640410399003034405001c007410000c140d009403e402028011204e40352003a102403403050b042c11a20001e01c0c14800f14105282a81101d10100d01440000c68051080c000240000031455249540d45030b0009204a10307440e0100128018042 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 846151915 1250 846150665 846150709
    0xb030403110c0a06020d08090c0d05060a06050d0f030f0e041d12040f060302160b010810050c0a090329070518120307080c011107080705060a1a0d0804081b 68
    0x500704c400b941e5091034a401200344440b10000908074042044045400c6d90000d25208100060342840e6488600540f8a504440d00b0210040f495080c51804008020392080b040810180d080d1001c550240d22107510700304120750f424600b4070aa42c1c42c0262040c22a101010102544400540e2071402080b43c2400316030318030501081224011000b05002142e415080c00340e51214003901083c1e60141d00c400091011541030004202d2050004160103403215400003003042c0d40b01d804814010b40104c3d5a1880016280d000074400511509440d40d6041a0707000500d980c23041c608800c266224046a09100040e00440c44040c0b02c0e28066950840301401e45440c002207900d040340a450303100e605009015840d0000d07041850301425809002c1c8089000010b984903d107918210456074440041551303148603140220b070407210244070b410441030000d2054441000305209000140c014482c050360710300010b000006003000144200c000114031000b5104e04032084c941048030b0426414400342da0192 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 846153165 1250 846151915 846151919
    0x15060f0109060909021605030a08070207170a02040e03071218050619140d0501090207030e090f0403081807081c1701142701150c0201020c040b04060b030403110c0a 72
    0x1030401c14003404e03643c0d003100141e510444401c45050548002c0300007030161000141860206034400d00e102e005d050a03500340c03001d16039101003254a8640743c0158510340e41200000300c0c01850580e0010303100400800a90b414091207071900a45040f20044000200d03000e1540c6a00e0052011007903030251401b00e80c1c1c036081013820f002c25a4200000c18010050100a60780d0a0900c80c106054071540300003d00c0600080da14dd8800c1700194015281c110081400031501240c0307864403913003c03442101c5611440c0c140d41d496031402c4030109009011081000451901c840c4213903014802d084c0980045c0006054800e03184024800600c03803903001d007040208e46100b030b2220200302c005441c1180c0b800000070b1840e000d2140003d010300d0342c1200c40507284400d42812750603041403104450480c0c440006e2000c4800240c0c13010380d405400c0900c0240140c02100c0d0003181c91405611a0302c10500103000000c1c45900c4002002171a8420f58081d80498035005240058000c10010b0910302c1d54251501002a4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 846154415 1250 846153165 846153167
    0x515090d020a021009030c06050408070f0501020616090801020c030301170a0506150a0b032410091a040b0f031f0b04091a210105010503070321020106050315060f010906 74
    0x40c850710002440340c0c4010080c4d00c1e809106100400c0956007002007900a00c0c0d54041c0600341c2e5029202e512000d004890000603c4425081102d007103a0040e000380507245c4c0e07070340a442900480c0e42090000e10045010100340b4040903c0601007a03030210000755070340c1d4100900e03080b1102c05921403240d103900910075100040d102042c02a00152032640401c400c1c4081c10008905e214260807540540d100413042000080070f80511a0306090324031207580e1020440c2c800c0c400380e020401300e18408940e0381c2c00208420000e860302c0c1d00250158424107800d2079101c4603075015561101085c1d803003000020040c4801c42030790010b508511003c002c0c01e0001c4030300d030401e40040307030240d840703900703621780d610629445408010490bc454480d8010282940202405040707212201d200058100c1503207804001715141c00c0c0006c0003025240c200c1061040c0305948a0190403000c82c200000045540703030b01d800034103603d0811000c1100d04813143c407038504d4507001051000303605080c0320340b50410041c41c500700421 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 846155665 1250 846154415 846154423
    0xc05190b100311120c18070f021605220c1709030405012f1507020d05030c03150a08240601051206040b04090b0903040905100333090515090d02 63
    0x803200f650713009030f400c000c10342603420300450151640c4c104050800904205e05030880d40762041007281c507a105103068044040740c0e127545401c19034880b00c11508003400f00340b401080345442010b05a100130001719203041c880c2c2c140c6100803100400710f005036001750100c4160300140d96200c990707200250f052510b4680000d01d00700520b113003442c00d040300c0d00320b85404072407542c0001030949a000441d07484c40b010202041c003440c406c80340c1760014043c98540c81100c900c140112401a40c0750640c01e030464035150220100800300105041d0b03c02c409000006807040280a413141458100f01002c4c1d4554130481a582401d4000340102c4c101300c0100500750100120001541d00000241d42c009504030807030020a002740740038080544044030304d808108043c44000018070a4078204501408192502c80360440402032a00000309a450050702c000c0c50f14400e4944080c50940c0c071142e400709815124401c2c0112098140705441075089030441803219200103c2150f00040d03107000a104211880300c000b511 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 846156915 1250 846155665 846155693
    0x81503150f22020f0f04022109010207050615120d020718050105060a14160807050c09040c0b130e0c0d060e0606220b0a0c03020d0c080403120c05190b1003 68
    0x130406941c070f441e0910780c4841d20300c10120305020f40b0455a640c90706204a80590315481e602904e42c01200005407515410300075214059413210041481d91201201c0842c0c4104101811303400000081034501c64007010083c0604004040d0041c202207800c0c102c11102ca0103061062a0b140c90501d07004224513201e01041702c842c007a45161601d01440b00d410101e80600c01c902c60384240600d6071103003100b48011800103141082c8610121280307a0709a000380f0075005402ca80180c4004501402045800d209100906080c40043d6032003144a84075030120600d1a42958929007004c4e0208161440e00340c580306070000b5100306503103071410303142c1003002498a101c0c10708400f00881142c20807080c00313180c6007140b401920019248a840300400c0314014103040080c08250010710070014420b4404c0e016241e002052600180e2540c07a142c11074441c1101c0c000c000c80c0704c0f420403a01c09141d82c0840c10600c001d03042c013143c41440e9120b403410ba060015407185c000e041d13001c04021345030080000682690348582 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 846158165 1250 846156915 846156919
    0x9010e0910020424140301270606020303010b0705070e04080c011d0c01050901120518100606020d050c0c090108010e011529040e040602070c0608060907081503150f2202 74
    0x840200c07440d01c125142030801c106414810720120008ca10501401408150342d000c080c85040b032000495242c07001d417440c901c0b0380000768000700014008000a0030081001d180110210390070305e542d0707411164001e08101e50503030343c151000c5013558030100d082c01078400c500b4620140303c8070031081000c06a00ca040111320346050200005460038aa400382144240d0040502401c008030f2134040000511031954201f42c1c010342c010840e08900c031804512980058645d0b903402400b0340e043c071520640d0954802c2083c1101441244a0407945aa0b0328140d20702138540140081510b0307410001460030348400d2030706100800900002805045298288a5807141e12000c680c0300c00b500c3c1c0141145607101d00e0b00101c11100400c4104000c0c488030b5001400c1d800c1c4103022550107250303605811101240240c800b254403120000200381c0c00ea20a0020036080030260750161610492040043e10304903902400c02c1c442080e0504104050500d0600141e000e0b0405841d444c0c0e06092403240174551005c190024 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 846159415 1250 846158165 846158219
    0x1605100b031b06130308130f0b040f0905061507231902061e0304030201090b060a0303050316052505010608070602150705070c14030d030b13020702060909010e09100204 74
    0x8640c050000c0a08801107400031192135a03a88030103e1059482e00c81c1c02240d071308c052825000140f101440c01107074112841d0552400c20141800074600c041c050150a856000c91300d00001d011707240c420b000030902148104a0321242d4640030452180d84e45000041d02100e030403002c540941d604101022204072a8100c0340c083c2e0b2507030042e1145030074000c10740d56030151100100402c010136405501041203540101d800821690b192004c101452085000c02800039030305002027020402800d0f90600f041b81c183c202a420002008541c40000740004441c511740502e0054101c1840000e100b10b5003d800c21f040600056810010040d64a5468180c4200e81c07901d141d0020341e02c940710b04141c90010764440350b0311400a0303507070031480e0012500b00c1426101340107216034110340714000c0c4600c20310044080d21150440c000c42c0644002500040380a0740c0000301041148103039501d05207014081e10814020b0329a07401c025200b140303000c10305104118403920401003448102c0300a8141c810a034a00a501c0d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 846160665 1250 846159415 846159427
    0xa0606172d010e0303180c0f040c03060b2a01092312040b030910050411040b03030412080c06011a0415020a020d0c05120106050607030e061605100b031b06 68
    0x1c988039241503618008651030200c03825443c8801200542c040c6000e00d5580001c1c040c400740058a400c0c10745030b641e501208520314509503080542049809020a0800140c120b90f25a2075160507801510304400f485018135030b455003003c6450300c00b685510000c0080285040d5991440510301c2d07000641100c05224169501c3c040b001044030042182c12541d0003034540780d03203942d4081582c206981c52079482c09081282e4510348504e1051a01c900e4012503e82c0340400350f0000c5c4030040507e0300c21135815001c10000420580c0485407400d08440c400c2c00c01740e0f40c400c400c1c14954100807040c0c1040d00c0b106569581e610004241030103031010383d403541e8000d0341758504000c000d03840c06c01310321802034111280c0080f8030306001c40300711f100c002c40701d0582d80c030100410000046801c0f00c3c19405001d0344044284207010100348904071207030299038041c000c40d02c0c0811842c004ac2ea410b4261030112007aa1016600c2d00086400d80261049000c0c250010003400051500c040c0030326012501d92401343d000810f0b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 846161915 1250 846160665 846160723
    0x50c0402071704060e0f030d020703080f160c050a0f030818060d14040209100b041401051b060702010612120c1502070b0f090d02060f0a02040510020a060617 69
    0x5005010002c600d061aa200d90707032a005001000508110340c46a210b00003000e10350b040118061164100c1c590252102d0b50035941e03a8441ca0f0009548080c0742c140c20702080c40940b50300e54414441034041d40324100403520309030412000a01e1a0001d010a0b44420b50030400038085500341d9800f8491580501c95400c3c0203004200c0030f000c0d0060001a05040c0784044002e001c83d074503054010b42c001d88501d001c9a03900107000420011500c00d46101200030001000546240d01041c1000b8005140c1a460101c000d081400103079840c60090710540c020720180200303a1740910a69008103c1410340081c60106a241e0311182c100d011030b00000d01c409010100c0c2000104441c2400c40c2000c4030302152542e03114103004c1134800040350344448582a9101050000100144801d403480b19a4001c0a42c1d544400c0304d405c03504401703018003103060303028007010400c2d0340e0308140907400301d0155004142c810320908000782a10070541c4081440d203000161030581000c0442c0400030b10140c00d511071800240c0101e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 846163165 1250 846161915 846161933
    0x7060e01090f06051503010209011202070203151807050103090f020420030c070327230402190e0d020a090c12020f07020102060a02031e2703031e04050c040207 70
    0x2400600300040b0407a40e0080068940c8468014118007000c44400308480040c94200e1290400540c00309200c4800c81d00c2d101110780013400100d20241c151040c4020003080f0044400f01075610b0285210f0703900c0c1d4000ba0303103800c01c18140280b0007480c040c403500304243c5030000581100c800c00390180e9100c28000c5541c842c110b16003640d08460301203166807803401c0303d040041d68100d042d0481c0050034580032030641200e03540d0b4480b807152000b100070f001c8900d001011442410500b0119008040454000b40d581c0e41d644050012514414602d070080710f80a600105425840c102183c45039140d800c1000260311061000810381c1c000001c0001c0076a20307072030181e1f162800324007030b0481c884c000944c0500100116001d481a03520070303001c903030a980355000c0c448181c0c00111151102c100c82030104d5820f400d40c26449581060a941d00c000010780700c026410b0a0400716100304070140d00000a000c080008480883d0610300d1002d400300e050300b025a1601c1d16408561005072040340c0118008040c004806 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 846164415 1250 846163165 846163181
    0x180a0f060912080f0f0a0b030604060f11040e06060a0c051f0509060403021002130504090804150512150d0b0f09120406210b1207030201030b06040506070b09070504090c2907060e01 79
    0x14101e50034ad20301481e240c000b8040080042079164104009400d85003483c8040d82d040d641c0424039101c49a4078074091010315003045040030108005002c0310000704034240a403040558044690900b0070048003e02c034140e50002c2e110304200c0c0d22420400c008240d000c81e9a01810550300e0015a13110030312061810001180d4003c0ca030b20616207031100c000c001e040c400034002c0714100c07124412050700104090f02c5d03501411585440c000000d030005503814220f00d81c0700103051f400603c03030b6465000c60307100c0042001045036114a2000e408040c0100401c00b04203030802c483c05154490318240c20824001c00748c1245208440c410f0b100050010300d603050507000712a40d81006000800400e0b0307103020311035a4081070710080e80032030701d00400061a800c00c002202e040c1c500c060a480d01e0003840ea5208001004000d10702d603224015514042910303669800762411031750054500801217800c020004041400555102c1c007c0740304001c003080581c0700c48082d68500c0c2d8004800160b05d030f000d0050b40340075150308 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 846165665 1250 846164415 846164419
    0x4030c0b100510020a0501180206040303030b0a180b0a090b0f090612250501140307080403171003050c06032206060e013506180a0f060912080f0f0a0b 66
    0xf41c02c2c0181a40064034110480c01000244218004210180200c1c0720f1410040d4000208200a001090103604900c4154801404811015540700e9811080b030201c20030380e001003515000720410500c1c0461448001c0c08010208022203898040010848419500b1090080d40e0040000700156183d0381003003040010701c4241c508000402d501c541854840c0061a42104070202021509520848494210a28403260316103992a500400d640c0c04070028821800c001c0e8401031448400f03201a90346010f44200d1601055550661809031306003980d402103e400341a0a108110107004c080442d5010480211150320140b640e50500c0070260046030000350101c1464400051208814900300489416503864858000300000302e40707004414019440030b4650140000c00d403407100c900c1c060581104650200c131502d58555135002c080030340c80300c0140c440a556003802c0040c03003480c00c000800c120040c5083c40091500c80460701d5018805420f0a2809041600040c90364070b481d405040c0340140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 846166915 1250 846165665 846165679
    0xc090f1202130504141606200319020d170618060102030706240e0712050c0d05010b0a09050306040f06110d051501020f12040504091b09091a04030c0b1005 68
    0x90070190b020403040301c44000039210b070340540581b40641c950100107550541c0c1c4c4541d8948000500348041200a441480362408104445200c4065406420030044416005003542864000c0e010b0305501c110b92203250046400300802c01d195848148030400c370000040300c85419210b00740102d145000d0340380c0081c01c0901d000d06290444d400b1000c100001450704c4101c0d61819110354010900841c00da86281c04034911001c030b9203641c03000d0703000a64000400107410303040c2031070f4886c410243d40080c2c0c8140090307400094503040c0560302c00c080e000907180030760041c02c0710308040d5500741581e01525405000700f03588502031480030000100701c8814907031103d018011401c05100b04d54030b45d506081503030301610800c1d00c0c2814020300420700c0400c45280700c031001e050524100c1888054694010103c40c4008107204440501e25000d12000241c5558480040d20000c0c5180460592000e82e5480314625021010800040c1d40103000d19215580015161501c2c3c4540c0d104080155407078112035032080c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 846168165 1250 846166915 846166921
    0x402130b1c06091112071416150b0f24180f010c0b010b0703033902012f130f0303030c022e06050604080f061e01030219090507030b040c090f12021305 66
    0xb0703120301204d001c00d00603a400d44610701c01c8458042162b40c5040000d8110141c1c0714000e00c0b5145c5084011140d00780b60512803941200127008008070740c008400480c00840041040b1518105085001960042801d00c910700c071a103500c0f62440c15005204071441e42c10006100300401d0b21a801c070f43c0c00549501541c880780500101060310a00c0300680209900515065011240344140119030f490050305a0142103901309174219600300561304a0825030120030452010b18060105108008000280e02600b500d410b41c9002000c3d580c03841c0040c8115405003101c07860446000c1c2034540b42100d140c820942c0f1054414514010303140380d07800942c0c030070400b080c0010b020a0104299540100705c03407d9603000d550b400100c1c040418405105c490901154006000605007035125038206a0000400d0031010350341c1069400351074007152284000798840c00144210b082c5405040f10052623801c0400c052270034071480983d48101442072000d9015454844400c1d91500c2070b0344003200c0000c1e441404686 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 846169415 1250 846168165 846168187
    0x207060221072307030c0c0e16180e13020a1e0b0c0a08090d050a1208161e1205010e04021512060402130b1c060911120714 54
    0x40380004000c1c00d040c0a0000100c81c0c81c42041c00414550508840d0400341c00011021001c9401500003141486500500000455004140c0c3ca0041c80c240c0080c82d0145031184d00da41c0407004d101c44100500c0644880198460307041c403071850036602080b08905480e5a07101d0410042c03900d602020390411056900030405400e22552418026507034074098120315514420341401d4428048070204541044d54036100281098005288040c001080034207909241c0d280c0505000340100708440380070f03408494600750b5400ca5030141d840541402c820086607003e202c09040e8140707007410140c0401c140a61901c08601891414440a411440405c415030311610b00c1001d400d0309035800d03427240801400b24182503032481d00302c0e1813864910025a2090300d90b0780901c406504255a030b260144503050f00440e070030300e8280182000c8c0a840f2261800004814080c0307080341c41c6600003000383c83c103040020b103074a01600e041302c00c50191008188050383d644c503001c0b82c020700710020824420b400024030614203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 846170665 1250 846169415 846169447
    0x1081203090a03030933110c060103060f0b10030e060601080f1306020c190507090203101a040b0d02030f010e060a1206060503011b020c01020604030e040c0e04020a0207060311030f0f090102070602 86
    0x1046c90000e0170442c41120362a614107d000d03190040301164807070300c010300c00120706030480c8601481400000c9904484140040d0b140300c100c1c402c070000a6038666a022000034100803098000c0c00038201240340c1c5c102030035591441c2070b0003010440301810b055410410002d440c1c0c1296034902651007030350410070300302c0340110305042c041c10180c8880c40f901c603012992041078400c5a010380c02d1510182c222620b800303400c883c4501a8040f003e11a50188070015410300198020038103c0e0401c000165a85008204c101000c2d0701a00450010700c0c5820400c0569201e000351a820b0b02e00000307809a4509151030701d40060151900117a4142d42072030118000003605170000e5074400d405400343c92104203003a004a9aa900484014000844c3e203011180c0504003a4802e00c12031800e0f181a481d2164544041030991b88900c0384200164003402003080340950620984058441484074203266044c4000e02080001c80a00000c044c0da050001044030b8050075070403240007035845507095440340000303441e407182 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 846171915 1250 846170665 846170753
    0xf0705100f0605240307081005100806131a0f0619020705010f030c0207260604081b0705061b152403030a0c030f120f020301081203090a030309 63
    0x11644140080184c84120340d40c003851407603a00c0b9050965488007000ca40c588800707040c410255405420219440e00c800700140c24122680c5c46280030307420808207000c442c003644602140100e140c01e00104a10490b10340820012000711039404e44480034000089161040c04903400d60098006841c480d0340b42c012400004a601c00d0f00c5180c90b24481c85420707426100c00560f01c40060300082d4003800490141b2804003c11002950301003c00c604d810040b62511030b0948040e00d04da0f070089402d91441840d03002e80740c1b05102c40000f50500501d03010128015008185100d028826081600101146c0c1040b07410440607035161509c00c2400c05010000c08113500c0307010580d44500d4001e0070215800c0c008111f820b855034650b10340b540418262004c07151040810308410400140d010410304028890190701e042078030a0310300594951401c108ad62804c00396100401c80d840c4244100004d40c0f41c0451840e940d15010300b4041450515490491203540030307006540140070b6080c07100c402c002d50a01400c01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 846173165 1250 846171915 846171919
    0x815060c070e09012403030507140d0801030219080303060d080c0a141605010509041e0f0213050f0d060c020a1e0302150c1803030f0c030316140f0705100f0605 70
    0xc641c0103100511718129519101030380314100b40d82d00401c0040d01c034000034000d090042c0400180f80740b03200d44560034a1507040d80c0c000082e940c58014000d51800c0360003620508001c3c111036240130303d0b1400d06912400020302603803040e1540f0158100f4008a081107550640380b0701d080e503c5500e2180380c2120308661030000300005201d01880c00118240085418040e280c05031540341c103000030b400412001d040002c500030640e0748003411001c02c460342e9000c3c1c0310806090410241e101c00d08a82901104040c0c0c1d030003580f054400c1d400c143c286450361010b41074141d40002d004101e05050071000c0e0b103001d1141400400c1d00180c514404000c980200901c01d550b0310030360a480d050160207040c41e8500c0c009482e0b45680c1101041001c544c00c05148075200008030250a032400d083c0c0c140a403c1864008807089d17590b0780c03c00010030045d440e03440d000881c40d100c3ca00703180c1000c01c40541707950071900a240c40c10b0050a80001c1060500208000400c6100f52142e401d2140303201e1080004040c158074865a4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 846174415 1250 846173165 846173171
    0x4090204150e032a130c050a1202033607180f0b01080a0b0102011401060804030909020a0f030b04023108031c050408160b10080c010815060c070e0901 66
    0x1a15004c20440c03000b46440d0034035450101001c104458410b0100e1070950f10038904241001e820449020b00b042145117501c607a43c42c0e820301c9802402c030b2061091810038241c41082001400313854814004981148141c2040d0341000c0c149800c807010f14825008042440b03544400a40300f0501c01500084080c0d180c0c0c2030243e02e41c1c0d0601d00060f0340071612600e000c10f54682c0000c50410786e43d4001841d441301480049965501580b00d2540700c02c0a07088240040c410740d0804c01032680000f5400000c3c5011002140341c00750007e4000c2c44003429428040030152141c1d240000c507521601039540000149480030025000304c80701408500c00e04000006210b143c0900042c555408001e442d07403e07000d2012842c00500d600880c0004041c020402c890405040c02414401655080862421032142c0302402c4c1034104448880402d500ca54400d40441d444200050007603640607402540080103010901c0300205440005101400742e1181c0b100740b4400c070640060f00b01500d0f8407017405810901c000b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 846175665 1250 846174415 846174437
    0x10030606060c031d04020d020417010e06040c0303200d020a1e0b0c030a091a090717100e0f0102160b060f06070b0c07081204020108090601060909020f0409020415 71
    0x382c0b10280500300150201e00403c004d006003012000c1c1681950100500051801018112080482e080b94005400d40c10032182101d0045030244140b141c5c3e440d8600091050303180550303d4880d44015400014108180701880701c0039050151f0458200a480380d007652040c100c1540c0c002e5030340103003680c159034201e0998541c02020903180b80c4e40c100f00d0740280840d00c0550300e0320400041c55201520748050b081c0c0e18100a03011440100c1c0403410038204080c80c14907400d284081915140c0b031a0414924560640c08042c0302e000002582c80308100410808510b010f400ba41d503130300b0500c0380c0700340628a500009805071980218405101030611441d610701d4980c03100c5042c000b10900d484202c61700181c041000401040d01d501c8401d80c481120071029180008654400c1c202c0c1c1c200055480c02101c1003020b2004560b040b000c4607030700c0805072004040540c504200140080b44521804940030f500003843c1c40651042d608171070103009c01e100e05645c0d03190340e42e1140d000c0300f40110915002812925a0b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 846176915 1250 846175665 846175667
    0x70302060705030106140702120304120b01050402040b190c020312070620070f1b03060b120609071a070b010e0906070c120302030703140a06051008040506150a0e1003060606 76
    0x40c3c0e4141d404071b946030300e11038100c1004910300c1d502102e000d0741d10106a03148104050380c200700a10282804103030b020300501c2540340ca003018207010303040648640c3c010f000c244507a84400003510754002c0300401c100e02e1080400c0c0d090710149d031140e81c0a5090300908042d402e83d00900c500501c3d02d148110030401c0341c0c003e9070019a01071217580e161303680d403108100506000b0441000c0c541d030210b406040b401c0c000c8040042000300c41e5005900442e0003d031240b815041500d0100082d442900300c803c0035142502d0300c1c42c0c2103a11140140508200d5590404003415054003100c02d0302c400903440650500745586812050440d00b2044078252514070510001540b0544242c000381c1046030300c543d1451442070700301c400f6400380d00010162401c00da40c0d00c03416404034a0014103240039409148001070103508000030310140d2100c1041a00500c48440306000c0044c10000d10a80c0c0000600420408100f40d50000b50141003030790300600c1f00d40ca16600b4060070244000d0388008980c4152010400640e40b404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 846178165 1250 846176915 846176917
    0x130c0e0a050d030309030203040902210a140a0c030e0a08040806090a0503071719181d0a090318030b01060f0f08060f120a0b0609010b0301030f06090305091005070302060705 76
    0x70150000189005100007900980103e03800500ca030040d6420301344c44010350070803a00106100104040b2400148038458040c850703150f040300c1d0304a0244a00c8140c02052605943d01518060b000c540e11903003d044a0301ca40d020300100c4440b54161b406440031801c0c079421a40050103440c00b02d00030b0101050b00e003200041d0011000d51301030081c41c18400180c031840b103051404410f03c0400d0030704000041d402c5003000c043c60002c0703406407501c03200c443c0301c100c1800c94080503800c2203404000500070200e14880d00603520364040d00d000b02c04140011035250071030b418591680d16400c009511074000c8108881c803000e03070b81a101299134000741103050b11401c503500a4079010182c04aa84280450364a08040c0c0144c174640401501e4500b80c0c402400342e403840c02c1c81c3c0490036240e29200744c082c440d80f0301d01202080d0042007010520360071075056881c2d00031b401c100d0400c002e140e40d80d28500a410140210151502075030f00900300110400c40e10406003082e030100d0800ca0043c0940030004030718900440c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 846179415 1250 846178165 846178169
    0x2070c080c09070c1401090209040302031905130905060d020909060a0c030218010c0507030b0a0c08010506040308190c050a0803090d020105011a07080c07140109120308060d080702130c0e0a 83
    0x140c1c407101e841e805600c0e502264403c0c1e46007011701d075482d49a24009070325040c1e14640210310941c0110741c2c03020b000040d0808000e180303540d441000420406e04c40c0591001c410403096913444140024940c07121400210901c0007000c0094001c0410710400c04800404960703244a421845010300910120000c02c608038410403000c400711814444182029511504a00b800c00b0703c02d5003101d401c181c80f61156803544000f101c05c041d40f01d4075196080212a400155a8010034003a604582046d055654038200c41c05000c1602c0f180049201c034020081d40700308203000405130002d00f5120405c02034100361072594021030383c50000b0711a009008903001e105100e058102c0381c040340709481c040c1d00000000303600e90290005464080b400e0001c1c220b0782c9424410880140340c0101500000c0c03403803000140100040c0d90260043c6941034411001280e08034210551100342100c402e841c080540c0b8000f41e10307001d0f05030701a40150a40d2034100e4030b20301c10b0384202401c030b0040d200d9060700c3c1181420401c95070b8041c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 846180665 1250 846179415 846179417
    0x10f0503072106091a0a0605100206060d14030f070323090a050f0120010911030a0503030c03070912050703060509030a051b03040e090303270c0f0406080102070c080c0907 75
    0x900b03282000c101e031907103e001c0c594810194500c4400b1094500242a0001c2d10040038459480c0c40c200294540b03e0320b01501000360340050300c4240781c0034000074003800c4c4005001d4408400c008010b51002424003c99113417582e005e0040d529000d09060082c01009100e1082c4050007032500d440300e550221314103440301c07140002e040c50703d1107040006202c810442e8559490610106c5021071b20101400c1c1610205d00401400000710020213040811084142d520001d020b0f81001c00110041500442101d601090700041107981c0d4a42d11400c90381e45060350b1060302200c00c3c46013442c04201300800c0e050101c900450f01404907445486100d074803803082510600c041201000b1503003100301c400e100708a160005c5c10940b4101a0384001c40707d41d0350000c0300c1042540e00004108510001c40003403003145c9540c0344240c04010030003451550796920300481e52900c200030360b0301240c8a554440e001031020346000302c0290f4a50707a540c03a1049905880b4000d128090040a03654105810100513281c401c3c2c2c66 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 846181915 1250 846180665 846180719
    0x120f030e061c090203010b04021c0606170114010c020a0e0709090b030304260f030a180e010605030402030109060c0c020a0519030f06020423030f15240405010f050307 73
    0x1940c2c414002402500c000300c0c5c06540700c01800c07000b0f541e60320107040c441c006e410140459550401c6000100e4586810000901410070200e002e01d80d5506002d9041d50f0181c03001c00c02c00d0300c00d00016561410300900080d40007903078400c0070a40c50b140902d480d020f032580c0c0c0c40b420304540e101c071000300960b0012140107800d40e106210401049181d10700344008000701c8000c2101c240b170100c101c2c600344104c0a001c2c1c642944001038512519510840700c801c4181b260807200f0300c1c0c07410702c08115540281031049200b00000400440c0566400b9030051506541c4081e04015034096401c024200a5001c0303c264410b0040040c00101c03400c00500d055031504948441000301411543c4414102e4001041030355060703404d00001c641c803015440548603106c020041040030408500415281100161000e84a904100c400e240c2c0d2003884e00340389400c54510000040d54052107034801184403100c02440760f0007030074034000040e02443c1c2841c50303065503002d9054410194580100c075041c80fa019181000da2a0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 846183165 1250 846181915 846181957
    0xc031b09030b1f0914062d060c100509070812031b130f0303020c04050109090308010509130c0e0603060f0702071202040204080a030e0321030a0e07120f030e06 70
    0x1c201c0e161030601070341440240300b00c1c0d0345072800c1c1e0084950b820b0404c24208036a2040c00070750f1070320001f0041d01408003685007000080840b01ea002051825281c0e501490001c10100d00c1c102e01484009081d8904810401c23062410b1840c50f503a13122140310300139440c0214030340c7e00955642030301120f2103100c081501c04050201035240b0b5000350320841a14400140c48003001c1280480c000803200210f02a078010244c108415040200701e480c180c1c81888484e1500301448000390b00000d0b1070b03044640c11034002d4425039a035105000d03441c150b00c800400c02c0c0909000440d0818211202d03500803017080e011a00c10b544c3c1c41403141c0f101801502e1075000750740000c4080010091043d026a05103102070405803c05a0712281c86141501d13080341140070508596029059040820203801c441c454094400000c005031811495a440003400014900ba10341400440100307040000c41c0080007a000e0300030001e8000d007069a8141038081c82140019260708004443e841d102c026510610864419120400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 846184415 1250 846183165 846183181
    0x90f0c0207050904030203090901031a010504061203030c090f0e090f07120809010210060803031504060f060e15160c060c031403090c090a0911030303040c17010603060c031b09030b 79
    0xf800200f0880840c403040000441d01c0e01c0b8500014002c600c80d4414000c0020044070820007248160070181c040d0703103020fa00308200080300440300b45107501400c0c000750100c4a40c400725960036240c0c02c00542c45220480026150501c1d03240c442c8601d000800745c62040042030501e644668891003000c4000591003480d10100701900020254198140111582d05e08c054131910140d42107035000595940010080021880540d1100c04400604403000c00c01942003c2d40502c1801b42405604204104505200080e8076802c2202d040c014a420303040b40c40381404400d04c207a40c1c43c4070f2001c4401000004000420500440c2c590310000d03450b8542c2d403840560014605141d4100900b0840035205100600105495210005009201898001c1025401400d202050640d014036480c000c1c0c0c01081000042070000f80c00200b0f882d8214400d244c9522120740c10b0740503180750b800140001d4900354242e18859055413041c0d00c1911030060134030303039800c070480c1c250703100400c921002d86807071400d800040c0c0503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 846185665 1250 846184415 846184429
    0x1409010b0a0509030717060a05090d050c0307020604090902013c021e030d061d01060f050c0111070c0608160320030115020c06030c070303090816050601090f0c020705 73
    0x400040c42c00b1400c1450000010380740403900d501c001e0041c110304402c04180c2005000c0c00341e0040780c0f84014046810408a0980d5415040d070018003003000c041140e0700760030800c1c002c94004075001811036481d5501c1d0f049000c0100b4403651f0480c08146400003840e1300008500b0104900b0302d0848907040241c5160b003411001850b010310000443c029504403411880c040048079808003400e4009640320300d1101100001ca65040d0400140c00c4403c0500c0422102a1040107064549a240150582c09115800d44460207070310b1645940b0b5003002095070070303401d520019100e024020580504035503900c04040c0c556a2059902c00703c520810201008007034001c0e0040b03007000c200e00261054492141c44030030313143d40007030b0410002002140c1e900141ca9504000130840c800c000c8403c5441d46c00d01d8101c07580184200407000f401d05844041d503a040c41080d2044d610b990002c9a810003044819103010b9072078240074002c44401ca032030704980c504840f90600c102d0b24000b10540041196a080808000507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 846186915 1250 846185665 846185677
    0x30c0f05042306030a090b071d121203070c050c01111e07090e0c040f060f0611152d0c2203120804031b02010c11040e0f0f071409010b 59
    0x70464485200d4603810300451281c034117040002003074007062900b20812100a0040b40420407072608007900c82c141d54205001c0c40008032500700441a9100700141003100621051120b0f00012040180310354101ca0b4000130580f0030810b4030580540d000042d5a90b600d40d9030403984d940e0111030f0400300c40420642c5104050040d208640805540740e105400b80c40c03409043d900a6002090080f1207810503000d14148000400d0341884064140140010340d000340b44148000c001c140c040403006404103103d50580400d0b15401ea03645490b2403034418a40ca003440c9180c00d0001002003202d0540915550741c540140201c4070f0a1b40707406e40c40c00494207945d8071101c000c442c03003805020010003c3c04c1c0c0e0490403252800d64981c1c0090b8641414050582d084808041d00e040f0520842140140e038080c007081e483c80e5115102d140802900c0c1c0219004243c0f0f608005218460a400750020000020382c0601e032400c0102184d402584603514450303a90001914180c1041000d00140000c2c0706000143c01 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 846188165 1250 846186915 846186959
    0x306010e0f0a0b0603070c150e0a0803070c0b070e210706050703180603150e04020f060c0a150515030307023a120f3b0904060507030c0f0504 62
    0x40941080f0002016548140d46102c0860380c500502070400030340c48201c4104d445d80000801404202c211500d843d040c1030b04001b03001c0f03200003000914031802410b980c00c0703058001e6140100d5150840004e0008040000d03160302c1000542c00c100400100540c4c0503a1b940106005854a1441c040c1c05482039085040304409014990300b071030000c1800403603404020051590003003004408030f00903103003040ea590403030343d0741c08505420400075071610140c001c481c281c192480c550341c400a4900300c2c20904241001800c022021402e180d40b8402900401e0049030b103106510b40c1c80b0b88140815030ba074420254000c0d0025100d080013640740b00444038556506188040d440f140c4c40a000f000440c1100c80102110031411088003000403a034402048004031166062901060981e42034001d40041280d00000031451402c401440860010700c100320714800107481d054007824103103840c50140804982c1c80c000a89040c3c40641c03804c0c4126980c20780001c0644590723141c00d05000c0c00c1d440043e00d80c05041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 846189415 1250 846188165 846188171
    0x507030b06010527040606050a0806060331110a03020108040b1e0903120601031a19080d0507060e0c010804110d14010209090a0501180e120301081b0306010e0f0a 71
    0x1030100801960030784c3c040b1100f545403d0300c181c0201c00c02c02126010b070041400c022052201d038aa0316000442d06402c4182140c0c22522a40d9201c807008c01103e070400c40100c2d0207240b002d0541c0080510043e416981c0c8a060a8901420401c0610074181000d10020b80080d10140228000c600c042020300c2c0c126101014128800079044d4301104e443c4170644460ba0030b9400056081c001894944515800c00c40910b014894001d102a0700155129500c840c107103d000c4130303215445802c0341c4201401c01800f10724161016171840c110060026003254200780d070400d051107042403640402058001042c80d050711102c0c2b1a0b11a902e0303007040d42401707195094010b1400031904000c6010801c081c500881d5100016a8900d811014051005000307031060f8140d5050500520910300e0700c02c50811180314845000984490950300303245003c10850092412110000022448071000f040354082804411502d80000c1d04c03440034959903490034440c3c0d04081caa410b001c2620741c0c1ca5807031242d802450040e804 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 846190665 1250 846189415 846189427
    0xc021b060706050f09240a1503120e031219050a03090f12120c02030a0315210209160504030609080904060b0a02071d1f0e0a20070507030b060105 64
    0xa4000c90b10306441e60501c07a00e4280400c40c03250410818a004900d5030300c600340404202e100c1c4034201081c09040c02c0a071684515160100b0282490080011600045101044ac0207680c02802c01140b1900c814000d000b8640c800804038610411501081c00c00240c12100c0700803d0811122504041082c104243d200c00c003080c04039400c40e41201e0010b0107994401d01c00c40080d80094101075541c480600c5145c00c08000703200c00394021094030309140712401c000c80c2c1031042c4031a4021881036500468002c0c00030003541c55000310b4000e05640c031244291000620b0303403144114620b08005403404080040e004200c14400900b068014515451062201c0350030301184400203400d85041d500320004980b00494005000ca604000070002800140300522440c0c0944032401002c540003040440c0800c4004003050300401c50015507001030911100308285820040400c0001d0401040030450120004ca0340c85501c21802c012603804540c40710003400c15034075556814110a0000703210905100c018481 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 846191915 1250 846190665 846190673
    0x71206120b09030d1e05181f0b0604080109050105010803181e040c08071d0102250503030f04140a05131d0a0609170301180f06170a150c021b0607 64
    0x80358040c9030030400c800c4201403010744507406c69100030440724540c1407a150854415102055000e080c02107034903a00712020034905004090800c007512140c00c20380c0000c1c006142141036200445c8584104028401c5983e900701165807030050b2070014481c120700200703d83c030034a04521200c1e040a0a0b402c42c8440c00028030006003268907240103100400d1001041291540d0b010404038084144100b40324040d10103140000d42e80d10141d000c1d51411040c02000181138440d5280300001401c00508507a9512050718004105400c80d00c0780d805002d00b0500c451009180a05001042c0c800261500c2031030469000014081c0003090a203201c040305910703030030f00080c00c04e200124225005000118a51080d881c00d100c2013a0802d0f1558074040301400103216041c9012052044800041d03c04030394080e20711500002442107a01803d48000e208800f100b01030000b0428510040c0101200d50041c0f40001e02a401d80d6583c0d2240001038010180e140142c031188645030304c46140c0603010904005075a80c0e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 846193165 1250 846191915 846191921
    0xc01060e0f1005100509060711090412020f01020301031a190203240306130b09120403060b0f010f0f1805130504140a020d0b0a09051203071206120b09030d 68
    0x90100300401400100212000101c0994004001c2070701c0604c102582414028170703a0250341c011030301c100c100103410000d102c00c84000340301c0364000400518076810075140200c9007405030070501d005401441542444810184243c90403603410401c1000541030060802208640080104503500700c0841c5104280c6598070240d40300d50340303440e25a03d8030901103240420400b0005145071103940502d04006134403124011100c409980850262040d440c0c0603821070900701c840380a00025240890000203101e4a6040380c102000185d41003840381d02d001d001181e00000034100800810140400b4011485c8955000340c070b4420301018502607152100001041d6540c1060006a21500d03001031005205008103289483d020f1000106078191403036010071405651410050312455043d8005250840181c000c82007903603110301030362070010104582c0c0714140c02c15034820300090b011000c40420720342d0a11804050b40d1900070307501844e00f426910080d00140060074404a80418843d00e4a1000240 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 846194415 1250 846193165 846193171
    0x10e010615180f0b070302071d0402040b06070b0f1f03050a03030506060c07140105121f081f05070306031a010315050c07020d141b19060807050c01060e 67
    0x141d412580c114402000501071180034401c4120042440810004000c100a0382400c9620000303859403510034505040c0d00301b041c290700c00412200c056141c503804024446d140e0384070740d2084800b00661200c40b41805614060920000d0003030501c1c1d0041ba002c1615802caa1f40c0c846074a02c00125900c030b9510b504802d03886e26030b00855059100c030001104160301802000c0d4461000d6540e0f5040446038802d640c0e9500062051281d1404294540f580c6030340301e48222203c0349403044c02d0390b100e030400e444030004000c01c0d012840e010b500703482004109504042104107001428454030289106c9049134a802000701610540134907a840100000203140d10b00c001070401e16100003d2650740c5142025031103074106400b2800b5007440c0c01c0811445040081c2030341c03c2c241c1c05503851004401d80b444c0c19201c2d0890f00107821505d11484c407180651000f03110300a080e03994184e0300103444051582c403581e0303000c0391130144401081140c00003448061003135000d4a55501c11300004100181e0f564014403500d0015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 846195665 1250 846194415 846194429
    0x1506050d050106170c030d0f05070b011d070f092102101d10051c0906020d0204090e0102090a050108190515030c0a060807140705030313050615011709010e0106 70
    0x490080203400101c4484c44415849000a403007182030030b40010340c541d10300a00c154140324510701c00d0324265101d007054401c4280d000300020b24550f1282920410218a8a074125500300442c002540d0148126042519080540c07544400380d4202100450301e44100c4d01c42c250040480d26a080160b61902c070b85100d0301102c0d0704c4254000141019411604a090040c40c6c015413000d4000e0340c010b1340c0301085401d4009914071610039a8044a61080642404000078042900110b1035010040300d84c0d00910450303002c0c1030104a03841400054600b83d010f140784c0603612041c000020050343d40500030a541c00240c00c03102014000c40c103484d0404503032003510012032200c00e84030407149500f02049440303415901204e09072000e514080005008032001004081040303d10b010500e140d06001060313903002c84d405070640c0e0300c9142042c0c110f030401000190945d994801c0c100071601031186540d80601200041e03445001c46210010744401f0b00300b014002d61015981d0f8000484010400c0c468000a07000b1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 846196915 1250 846195665 846195671
    0x2090c030f0c0408030a110a060e030c0106090501080303060d03050c010e01050402010e06070b01091d0f0a06050c0403050a0f0201050409330810180c0f0801050c030705071506050d0501 81
    0x9842a031500754020891030855a08210074002c40c0300000036510303010000d2a00c6440c2003c007424031070a0200904005020350300305200c03100c450b00040f002d80f20031410b900080282a545071401025100c0c20710a41c40ca580080021038101c1c20000da480c3c0106000e8204146800152003005084408580415a441e507440301030004540e440949410041340c1101c5150820305107480b5105045410f2040410a0b95034401005004c0b022000c2c40c0c124140e10b200f501c0454420b250000d40700c8882da0400c82e4128a03060015008542c1d1409450035603410400410304410280d03100d130210324031b59500380e05005080c03000007680410b41c014201c03c03810030001d6a503544070070903145044164040412410313614501050044d1180000d5a12035103021480102d0b800740e60074100e0541000400d00502164010701022800c4120701d04c02074100e480d8040200983d566942c006005400261901d10020b0030420510022812880082141003003da4000540d039903100d0010703035500c43c846021205651 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 846198165 1250 846196915 846196921
    0x10e13050106120c0f1116091401092715060602030711010503090a15020409020a0207300b0603120313030e0d0305220e07211505040b0d02090c03 64
    0x64481ca52285000f041c5909000c1a2078445010301070000c2c03050302c5010080400040c06000d902041060a81c5034400008101a030b114004140900850700c900f01403050144000a0684c880f0b1140c2010821610104191103d04c041c001c8040d6081d07510540b1540b00c640028030104045104410080485030029555440a07240220007000c800207440c0c1480780a00400c208084089110840a51302810240e00840c081035101c0003070240360010310056201140d6200841d130001010f8043d0f513007407400c1855000362542501800d511300e00e070001c0ca500084c00314000186400612541001c001000c1c3c40384480640c072010140d0300101d4003400340780340b250f01a1381819004212940c5019054a90f03000000003a02d000e4524070900300400e8211900149840c883d80712402d00c00080c04070110140e41c241803540006000c0946801844601c0395003510342d03110140c41c0d104510002101030308144600345040108002071900c1030f95140c0014901c00304800503607486011611940e441d144054981c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 846199415 1250 846198165 846198167
    0x4031b0f12030e041406040b0103020d050703050403080f010311010c03020c1009090621112d0103050a0c02100f0204030602281112090f03030c060f092109010e13050106 74
    0x10440f20082c0d00a9140040d80c46041d4007000c51386901c88001d980c00301d400c4003507100490091043d10303c1c824802d445d00c01880350640d030681181b07005502a50b113204081d298060790f21203240c2d0a101c01050191a242c07a0000d0394040e81070550f009000340151040b405210001c83c21002c0d007262001c000607100c10081c0101c81051040c0c402401310a021304020541c0c3d0310f01100c505201000140c603e90410442041c207640b20813403407180f100e071598521048507000300074048248021072014082400c001c0050b14440f614400c40c03240b20003030741c0100403089240c41a440288541882ca9020310340030400440801e2180c002400f000c0da040301108400000080450581c000c4542903038108640a0307101d03890010001074903030342d0350008440b0b103a40303400050008062203516400c5540502011800c620402008640385201d43e0201c0041a842d90715001107a40320000319038005041034880f503405020b20000c0c0050300110406041501c00c090745040000c9070f4a008520002146444074010300c00c0d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 846200665 1250 846199415 846199427
    0x5011812112713030203070605040f05120418090b191b0509040b0607050307080f041d040201030b04060b0f1317070305010e010501031109070212030a06052404031b0f1203 75
    0x740c2940f00e070300c802d41000d6400030744911401d030010303101503100c502040500a080c0100c01c40550b05c0f6003143d10740c001b034090320189900a845a001d00d07508200c0101106055802054281a030044503131550f0341c2d40c44083c11111458a0400d400e0076640d548240bca0b021180000070300041d00d0705e549844040c0401080252600d404000f40541014412140052000020b030307030807580e1240640b034455401c4041191103000c0c0c0e0381b003001005111581d400c400c24181c2d14941c020790013070342d050000c0c4003100c050000381ea4440c80b910003c0d240c20440069841908009448a0540f070881c0120540d0b8440060409140c03000b0f1814141d00600001c10801200744036001020070000300038040c540c50758451051b00c155000c003450080c00600c1c00510010310a0100c3c1c180090512445507c1e03040c041728600043c4000e001c6c02d0300941078090a00f10050040b0010b425405040900f03519050a6580d500303044900300c0d040720130b001b14003000800c00521044010340901121030402900b21401c1c2801803203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 846201915 1250 846200665 846200671
    0xf030c0a0b100e070c1b0605210606091c020a0f0503060106090b041703071b080c0d05340312120b15030c041706070801050118121127 59
    0x90781c0c0c2c0c144000c00400380c1240850394409007905005c0c5810300c1c5410b1031042c0d00c4480b41c11070f048244a540105400d50020301503d110700048000e018901000305401d80030b20070a456142c0d100b1400c2c44010301a103042d80c501380c022008070702c1c030300d00e543e03d103601003036840320541c1100080c00d0100109003c176041c100540c07401801c00d80380801420303240c8107080115110354080d0f40e50351040b50b4a4081d034468100100e8004542c48041031035600c1c10b1904040d02e1049a018040460003030340500c103260324080c1020300e46150044040c0500084182c0090f0004a40c04040b07118111044800045825241c003108019400782e09803035500410584010580a508203210310380602e00785c0002060b8072161400d01d0320b6604004029540d85407034040e0210b9020310303482b1004204007100d000510389404219a4021030064880000c03990b2280010b54108040c602c4890700b11042c44000c002010003000411503a502030310405548003005d00201d040040c0040f030101124651040401001003e030055540c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 846203165 1250 846201915 846201931
    0x15130503010f060311031c0e120f01060303030605031b19031a0406060603060815070201110f120a0209180a29030d0f020d112503060b0108040c090504050f030c0a0b 72
    0x82004242070151f21700745402064200700b0243c1300010303480d1307211264980081a44441192401100d01c82c409018010a0204400107030504800060904000884081a80750303038042000d03006410046c8213500e4000c01d004039a0f082950750010104010072880c9200b4044891400441d1400b810020b00342da015501078003c00d450084100482440414404030b11403501c51102526114407004a024002d02c1c00c020f030a40a00050540c0c4505808009140014200149014690b03820744e00c0340490003000c400680042c0d81e2103084014103a00881a6404804400c0c0000c03070086208454544c0311a088030004070400b0001100d4032490304012855015102d843c10346d00d6040d441600a40303501c0d03443c0110084c010b000e5100e480c1c080301400100d00031504840151090003001c804034440d0b142510058904516100e0984100d5202d0012984216001503c650216183c01420401014020001d072000d00031001c080c18814002d100400140d0041c0000f80360010312410700e064003200181c4400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 846204415 1250 846203165 846203173
    0x120b1006050306060a0c0b0705090a09051b070804030b0109060509090609030f1806030a02030f0921090607021e0a050910060f0215191a15130503010f06031103 70
    0x4a54054110b036880041640c40c151910076002d000d0f031326601044001410b5a1410f8200b0600680c40350182c40144021240000425071340c011220071100103845411442401085140340c1c0700901009041c168401c5049a203000e560740c550801c0240b0a8008601c0562100310411041c42e19107002c58000708a0f80141c0740d282484000b036541c034480c15281440b00305011903030700c0d800c4615512541e58481c001d0580742d6246480c00302038000b58411a5255904500c0c400464003003000096602403e00245410740e06c41851a80c0031040d80d0881284503902c00300420440340161039201c82100034039820741040011440000801001311000d40200340030305a05405c0003201208031611404607030303035400c080d01c0c0303501e0700381040b41030100e95035400001c4031501003401200d040d21402c000440081c000f003042012250001c1c0e017001c81540080300c0e4001c055210f5100c03031003c0240181031321807d2500d4140c1041c0d4031004242502e41c50301c203003003800d5920441017081c0040718045050700e00d0114098 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 846205665 1250 846204415 846204419
    0xc030c11031c051f12030906090614030a1d0a0302060a020a090918051b010207060c2027061005040e2d0103060c020d021209091b04120b10 61
    0x81c182da0081d920318482c1c001d0f00ca40100329007070200c130b145403e0180015800c50025454400c2d4103d90080c0500440005a14850010b5018031a20f0100c0558046644041d07090b805000020a20b030401f415144915580b028003883c003403c10707144520055001e00c040d0100c41258113005e82040402071104040d1801003199090003030740701d864001a1341c140000000c42da420401c61000b0310807480c2d002000c41c401d1301241b590f141ca030020b5000f0201400d0b4203c400c01c0c1d440c8c44d4212000003803c41c0080603140ca8a101c0e200514610041e9004141c01138000042c2c9550009d42c01c208124003003000c4c90b103802007c14131029040c2600310f0000008282041884c03d0f1400120486034400204181d0350340d007141700c4200880e06054550032801d445511580e809503140d0074494004c010010409008d03206061807a1740ca1400803c02e008008005044a414200325109105425500070000c5000414280145810f401c80c1c00c094000340034000020b0003054041d10740020104805811020008044102 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 846206915 1250 846205665 846205687
    0x2060402041527090f0b010f120f080a0c08041d010e01050f1306051e1008060a060e0303042411030c0601030314190e010314060f061c0c030c1103 64
    0x840c001da00501c00c1c0c90f8854000500300c0070014a4480c0004106100c040880c00030304c00c81703c440d0b90581d250705900c00241903031a503081e1310000304020010080d40c0d0f400e05240126102c80003a1010000340c1c280b07140a00901d54036011164015001491103054864141c5112407421035910b005d880310180c042d411b5410000050921031801a20510448038000c0d05c3c0b00d81011504201c4c02014054402c23081c0c0b0300800c498a0313a042c031120140d402603500f10744c004500b9100d00c8103d40280b0303018103085182410a6403c8450b12001ca010a4040c0b00c20480020100e040c07803840c52800f15542c01c504a01240450000c281003444107100001d0350091241281039817001c212103044030303450300f056085024100c00c005a2805200702c0d6002481c100c2e018406003e030014801c0308000d400343e8040080c40d8013072408070600c901c1a00d0032a080505401200c5041c10102c005010744000354000c51509000360b070f440b030151503078011503500003600e81880075200b41d001010b11104405c0341020750304105081d00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 846208165 1250 846206915 846206939
    0x16030e06010905071806021b010c1703280203040501060e01062703060f060806130804290a0c020f060309061303120903181403060703090c05040606020604020415 71
    0x682d4a229500e601260307859001e10506048901d03103d00180401da80c2d440c01944800411a5003819208206980c1c101588030341c8170200031642c085a1103c62100c14200341c2c6e816000108620010500c4d5080081ca850b0101d8000441071240e0304056a6032030246045403c1d01d80540c00121f00da0034900c011302c482074108141c180541036211540807810454054003d900f4020b61002c4c0a03a494909965001c032882c2e08200107031a610303412a50356448858480413000d154150140100000340000c0c8810245810300708140c161024019200704ca01120746074440c0d2144580c1c10229607440315490840c240031034483c0d001c14048514034210319050542c95201c8000421503082c4031303d080014000c050040d1022071441e041000d04000d0402c480ca00503210305036265034043e4190081a000449081008410016480c054098007045c0c50b603070801e60140c01d1030441101c0b0700c0e0400d407000c0340544451080310014a00380e4020310356418940103010450300302001058001c24441814081000440 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 846209415 1250 846208165 846208169
    0x90303070e03120d02121602031b2b080112020d020409170c0705120102070807020d2604030b060118260f031e0703020d030f0219020616030e0601 64
    0xc01e108000031001d0000a0810341c0b0501c0d8606034840c0801d100305000361a60180101004441105c02503485d03880710b0700c82081d101142080141c0c070402219040305410760580900c0420f103002c8881c4d07903801400b1001c1c0d91203072240c41070f900c078540b0250390801a07100110a00402000401c802105402c0d004601612403420300a4000c2d900e40004004000d50b22070012803488205ca00561254031000c41540c40d081c0d00d20801e8492110500400198141071084035a4598084201e038588000c0c0e500340b20a6210b050020344410100c00440000100c04140d9020720301880d40782941c2c1c0c0c0c0e0441c034280300301c00030103060241000000c00402c07981030a502c1110f003e85050b04c4006460007401c01000349801111620b1600718064070b908210b003020000044c0010701080310342e182c588a254180b5000d68000c043c4041c0042e400b0301c80359041180294402d0041031900350f800f624008a8a862414103400111414016484041045001c0c0d4101d200c9414582c0c45e49018800402030341d501070f0b9076030018 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 846210665 1250 846209415 846209417
    0xf06080d1115013f030504050406050306130b0c0705030d02040f0e0610110109150e070506070c091a040203040c050405240f0604120c030303060605360604270509030307 74
    0x103410500380341394603002d21003030702c41000710540c1c44e44441c50018155005445080e01660900d5800704051a0200d0b009124454840103008110003a8a43c014004800750041e0140342c42040000e0220b60188000c0c40382185403103000d40d9503440c190f04604d81424136440480030700507000512080341d481c056a4008500ba80c90305011501d124000e91b8014030642500030001e1010307504040c005a005d4100c0300464101c03a040e220055134640c1403080c94407400c40018120154154288051002076014041000c8480c011508079014030b00494100ea0050b101507034207011080c4100060325003030081c50390144508406001c03902c01a031518449101c00f541e418400d01000002052a07255001038500822403150410058074250403d1440e00034a400260700083c103103807010030701e00e000b0f00c00c07035602c0980c01e000786200c0d4104c4110360880c4248071891481e002d0460510444694480340038202403d070b042403050b006008a108885040b401c0b80407584018203041c1001022000802500d86c80411 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 846211915 1250 846210665 846210719
    0xa0b0d0f060f03060504110102031216170705090a0512030a2304170c0105160803041a180f0c0d08070f120503070f09050a090f06080d111501 62
    0xc0305025014042a40200c400001c0424000051240a802c03280c01380340207441c12040d040412004a84901c0344001e00e401a000c8080410720028144107940c002048514040340c441c1c00c440c10210715040160b500780c0c00180701040c244094981088000000c2004581c000c111000710b00c0010745031b00a403061001444030101c050358500e005400502840c42d0540122075445483d840c1c81c11890808014100c0d60384942ca01315a9594007400444140350b04c0c1e001203103c1044c00c1d585260903035000801c200c80e10358601410804042e09110300901031116840c040504422801803646060004c4629020580c0051500481501c40440d542c11054100d08544e5480355a0b0410b0804016000e00c01040002980760701510703660302002446c0035030542e5850321a841110311003161281081d004d0503901501c00d600070444068258050400e066203880f010512954588038103051151601038400407500e8660035404d41c00c0d0603c0303e04005115019562107650418032a0b5a082140c0e42171450401c0c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 846213165 1250 846211915 846211931
    0x2210c0c0a0305061b070209130609151d010912050306060c06010b042d0608070c020d30050406300e070503011808090109150503150a0b0d 61
    0x10140036030551114040e15100055580c0c0c9040d03a81e50204680c031032088100c5d9030b500c2ca0208a400112200a80c0050100740180c0381c21485a001400ea50b2080f074281ea0744050082c0001c2d0b90843e07146006800200005e210903810100080594007006640e0300c07070345416440c030009445440c0000d05140203203040c2d5101d954030804160305120304006410680314040000138a01400c20040050f01e400440880b8500c9421106280c01440c0000b010401c080e801c4061000b01c4c07084c001701e64054000d10b0805010b1000da00440c035035222052050700c038201910b14541c2c1c2c800c826400d0091344040c0d00b5044862155485004040b40a9409008100800b0100e4240c0303084c1071401440c40503200c1d0308216513101c0c00038040c1c0014100503501c80d00c98040d030100003445240601c40e0580407840748103001c4040d10166904005d1f580608031041c140030303c2c1c20f008200c4071410101e208910700161030f0070703990303003401074000080c0754031006580e10584125030305010030841001500c400721591240450855 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 846214415 1250 846213165 846213187
    0x50412020613180f060e070311090a031a13030816020a06050a020d240308090a0e18071e03060c030b10020d08090a170c0f06190c0221 59
    0x21041d4100e5482e041d030011070120302452403403001a558500c0a404114140c2c01446583c1620020300c50340b181516440001070400780203800000306001c6600000f072801540d100041c02075925038100748c8900c60084845e41d400c51702886860b40000c032710a071447d000001954010b109140081080079114000501d544201e4000c00801000c10b41c0044203120ba407429202000c025006840160812810403142c032100110082003003c81e0410041200080f504648420f00380740d00500707219400c03280c1900c00080c40310110b00305a000344048000700580081d08900f1300e281034202d0304545224035400d0008031002030b030b400c540c0046a03807000e80814181d0507184150000c0c002d5000c02900f0208820030710290301c0e80401d01c01074858168448403540d0322a010344955800d00c12070000e01c04c600d038111080024001c0c10180002005480441e4208000c0e0601c0750b007401402e5800c03803101c03845c40400005100704c500401c14043c52510082044200e080e94050030309041c00700a50b4035050002c2c0c0c1d05101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 846215665 1250 846214415 846214417
    0x7120518030106030b1f0b0a05090609090915090d050306150d0507021c080f0a0b0a1d1506190f0903050322062d090e130201030e010c0504120206 64
    0xc200c0c010000c002081d520b04001600500c00c4611003440c1c54580e0741384898001d403050300420795400f4401035084ca00340041c1610305611201100e6400a0f05124546443e5a031144541c4200852405042285201e105070124240c000d4403130581a0004100c0a800652060503264000d000311219940010320744608101c7d8480c0a0740d0401e0b1a050604001e0410303000204000203440d00c5420600313945111034100c0d2003e1041d0340440c900b0040001180c036018450300207050740c0400030a1456003955890802c400b182c83c91710446030307101e141c408008c1c00005913034842035015802d0b241145400c10700303400d40e1600034030000c009080c0a0902040b115030b500c50030503d80695070190469035140a12003403c4000c5a03507901d002007141c00d02d81c01080041c815012400c2500644e0700f0000c0340d0081c4a00307001400030240314602001308084001429501c0c06400a0140341c1000080d10744040500004081d5128001f005103e40c0c100700f000707508181d100c0101d4080742c4209005000702d86a42c8000307416 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 846216915 1250 846215665 846215707
    0x816020301020a0e0310061a090301020f1602010f1b0b180316060e0f0d0c11090a0c020601061d040506030c040e030a080105090c0d02090d080a0e15071205 68
    0x558400314100510f07541107050003401d80c400303c0c01c0b00c80040a0b641c10300c00f0b4921500690b4010381c2c809804800003e102c02c0079100a240c010b00144c1000502120805590040070b803040450352000c18440a65810405e6000414014940003a041841c016100312174104001e00501415002000403800e03e0b4111011031951a0780303044c0da9645603203a00c0040213601402d020744401e40b42600504480c01c000940c9251444000702410001059072020340307402c3d02070142641c1d492000d000b008a10350b03030340811038402c01d0701020016950f6030303164000307140a805800a000b401750740000b40000f5221a8000850400210b4010445644003c0420708000c4d900d008240c00c1420001001400500400a00b201c54859958417000d60303a240e0810194040c2030350900c3c2203a42c10480e802492031542c009040e5030102031b20b111195065555419070a90240d010100041c1d0005074038a4186460701c42003105d0009202058101000c0380c907006081103482c01c00e00144000005c0f074290b444100a01151 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 846218165 1250 846216915 846216919
    0x30605130b0a090506010e0c190801061808030d090501020906181c11090403230d0c0c0510090309091b0906110606041104180f0501080712081602 64
    0x11410510340c15080c001100340225000c0d01018002101c0e49094492141d8164101000b082c69034078011100403406009410914004820080d2008015003003150851201255031484015850842c0041000a2985c02d071454403684403000c011910001066078400200318000084410403881c20f5402841440707422074010001040541030b00048210b0550301c0142660b5540d8107a000b1844281851940360008101805032044184241807807483c042d031040c400d0500c40035a202c3c0e04003091902546451410140c034000842041c0c440ca180120444582142081c03031651144c0e5645c00d032242464802901000c0d5604019024140b04030280300040100083c00c1065440c40070212800905400301900810040d000c009406403152508841d810300e407101908058039034508010242102d000901400c00c0184004249910710002c5110241c514a2000401f0983c0d000b201068840c141c1c03003001b6580100100300a03240b03002041c402e00c154011003003030303560310310700b1140d240c200d240d80e0065 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 846219415 1250 846218165 846218171
    0x20f060d1e20120a110405131d0f030433030204091a130f1e0e06060114041e030f0308100f05130209040209100206071806080705090a0306 61
    0x401c4048581c814000700240605000030030881242c1c905042c8124601288803150640c005140c80495170710500070b40d00100f40c943d10f000d03034607000110030404402c1d03a14a600d41e25407180c88240079249800405640840152110707010307a98060b0340782e005070b10401d081000c0c0700a0380c218101c10801f9030303884402038101c41c100d41e01070691700900940187c0038020b20708d450081d0014800c0c2808041401c2520018407022821480d201d400c80504440746039900360a4035120310310f1442d1280714101101c107140f0000065030000349102e891130325001400d000e0600064020001d1260109030440d000d0701c01c0c00c00071010b20402e040c8080003400c65584050f04803881422514101581b2140c1c8030701802030410620400e1740c40c1c104405040302c6520949a1110108540c14040000c0d50007803d51100018001410941500d0103d43c15041104142c001a00041c0400500942040726040448141494403102c3c5040103006001c41c040a02290184030740411085640e5950f03114040165174450b00c01c5c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 846220665 1250 846219415 846219461
    0x24051906030b06071e0c08011416030f0c0c0b010f08151308040603050702060a0e03041e0306020d02091f050a0809100c0305060f0315060616060e0703021507020f060d 73
    0x105c0011403105040b9101c451008000030100700500070501611480d83c100f82c5503484030144201072040e60310468061548504454802180c00e104a03c00a0260780342c09029046624102c01d401070143c201100d00304225805202c1000002411650441078014019031502d0345407005120000e550b5004080304800140841c00340e41c181c0102d03001e0704c2540c023240c11399100c13503d644c01582c0c55090240c1e400da009010030040c010000c0300940740c401950345110926510303519400181d91081e81c40c24061070b00094040d020307042c80131280c4800704c90108040f0414266810041c031511440541070704204255010815820050100d100010b9500d034081045000b017840c003074040c0100301c2c2e08521518095042e40f00c075040200d5908000541130004180680d520b80c00c0200d10f03040615031070848d807840403902c2c000403000e01c5008042c00041d402000458903600c1080044058046514201c000c10710070035005884900544201e15021902143c40301070304001040142214001041c00c803480d1403c03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 846221915 1250 846220665 846220703
    0x810090c0b220b12090a02280e0114010905011d0f120a031101180803011503110403080d0606050c0d030c02010209041a1c080412030302070624051906030b0607 70
    0x1804d000c02d83c44400a90b070b41c2e40c28031241d19a007050360003940060142d80d511104184c82020320009801e80701a0400175074840400445c502000d0b0040320005141c09420842582c00c00b81c05001084246420048122800214000e05903407121441c06034040d807d04c520b040d510441a5031014076207900f150004441c03401e0090060003918031030030340c40d440c0c024031306580b021150032b604586820490792440c40e4030f401c2c090740e51074440850320b00405903a03031041241004400001c0c801140504080c54a030f17011940064104c80307440e40100e007807181c1080440c608080118400368110520309000800041e100400c1c0d0180c41000c0e203035a4024584001c00020000d00e020601c40c80e03c1c00e0300d410810102d40b03034030140754a652503000341101c80140004c011030944084205000c0380b10380b50141c03c1c6407196864009442d80b841031012040b80c0b1251000b0003008030507001009000031105000c802c0743c0c580501000c0034880c0245070402d9141d81181900c0e440d09421550925807005074804a1440140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 846223021 1106 846221915 846221917
    0xf16060605060c0615060a0903060b0a031b06080a05090c0d0519030f08100303051e0c0d03050619050a170a1a010810090c0b220b 57
    0x1001041c01d0301c0e00c0024210340c200c0400140a43e0a1840c10030b8000c2d0304c0046071038000c500030f001903c841584801d90204494019200240c40b520303000100c0d26095030b070b40001d00b60301d5900440701000b00010902d40c0441d8500d40c5c0b000140d13111102c601d4286c84056030002e4032035220203032515503480c003040c100c003c0c80d20a10413151800c164551141d403400c0c10704410790200304542103160105800254041d884000f503802d0082e85800d42e58098445d0103007184800d1a030351401c07001c205c0031402200310380f48228030302c00701d80c02e81c03c0e0850020082e0004956a50084600d00700162013102c100c43e40f0415584020282c00351a0f04042a90648020000d1488180e1141c210740340041217040d00402d405018038a42c0d4401981842d00c0b0510b040c821808000703960b890070740e4140c0400c4c801e00c0c5450a13134981031002c603a1803483c1e0f031642024150503500b611032403e131514005401c0070308074 = true := by decide +kernel

theorem cover : BRFrame.Cov 846043165 846223021 := by
  have h0 := BRFrame.cov_init 846043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 846043165 ≤ n) (h2 : n < 846223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
