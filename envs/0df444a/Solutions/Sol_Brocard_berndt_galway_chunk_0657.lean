-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0657
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:58:33.049123+00:00
-- url     : https://prove2.me/submissions/f3d4b7db-5c19-4d73-b35f-c38d59d898f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 117985611 ≤ n < 118165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 117986861 1250 117985611 117985613
    0x30408060a020c01201909120308040515070206010303080604110d020306040f0606020d0509040b0a170c0d211205011706010902090a030215190302070b06031c0e0d0c03 74
    0x8080d610001c50f58100b54a400b034400b107a140c414640412a181c110445400e003120051781015054500e0711074030510048540000e00a40b04403030800c0003034820707610301c07240b4209031070324a140128414014244041070020000ba055000400301e0440c0d400d8a00303d00580c42d01e4010500034100311002030740101c030003d5200b914404d02d0300298080c00301910708015038025081c041c01118111b005180045c0c004090b582d618034401c40142c41c1500c0c000307000003a0014038100240e0403880652202034080070400c503d0880050a008840c49580e0a54142209034459681ca140390591a003401c40408130740744070918154426240320400c21000e0008101c19612103130003907807030380b00112200e17058800e410010032000554001d46040c1c50001d0402101130f41942e003003200706070000c40e0b081260794003445500d070021039403142d901c8000101d407001a40d810090400408030ba00003004c00b402075006022041c0048408074041c0c3c942459481c00c20071400070140000c42036002d186002d000803a00340c42c044 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 117988111 1250 117986861 117986881
    0x2010c17070303050403020d030e030313110301181509050606010c061d06090709060b0306060c0a050102071505010e0906040602090a0b031801051807030f08040306020315010305150d11010203040806 87
    0x40e00032806a0202d441c05146c0c08c0c8124251000d0181e903209541080c00031846031140340381141901c07480380d962076110200900c0482d0840314038500300d80d203a024150206091180e070042c18103a1032014041489108565100c0642d5072b94090001070411101c0c0c441003090018a41c4220340c5c50071510000300444094681c03607590b510741580c4001c014040c8d0100051742c0e902601c14501141d1a2008050440d0782e80c4007004100e41190038444031341d000764943e000002e6402e10082200030320802c04c829202d6021210702c011070302c05801601d542e200080610014400014039168003541c000f1016079501c1c0d44c00045007042c100c6610600c4200c0c804400d11140c071090101408030100e2000080000c0c5c6d03130303e050f0021480c1b29040440c10380e401521003031000c0340d80c1c1d07440041d5090248003050324055980e038501040341c0c41241d401d02e91840983d9661201d40e0316008054103c103402e41340e4450390100c080001c0c9040254640140004101d408094580c1d00074420348000303209070400d981052401403211 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 117989361 1250 117988111 117988121
    0x30807140f100b0a080c0603060307210303140103020112151206240b070b07051e12010e070e06130e0420010504120602030702010f060f06021203040b0402010c17070303 74
    0x301198038102036401c810f03410114002000c4840b10310040c42121782550034400b035540b0141c0056014040c0c0440419035031520b40045890035030804242c00094840e083c0101107070041450304107001d00507401000503070b922540a040e9940388000c001400701b941c200c0100c154910b5845441c00760b020000c20002d000d540e80c00b401a614403540840c0710440d41a1849011007094055500709000900c6018081082003440c964800018103104c0e14104030220101c242182e481c2c0c1f1140503560001d908003c103001441c8041c0140715004501c491424056400343c481086502041c1c000c00005c42c80d840000400e80044c4000c1140301d205c001c560070181002c04101a0615140500b060006c00060541d446582101c1c00c4800801c4008110485503079140082c0d4000360030101190348400c843c20f54030381a4447e00c1c004021b18140c0d400714a107803c078040d09080c1c1102c0d407068440000e20030400840c188034504c550050b4240303080f4581a4940c9000500351807060960a04c0d03160208000c0200350b003690007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 117990611 1250 117989361 117989383
    0xc0215070606080f0303190e06011203030c0f05040b0d091e0c1a0901030504020301200c1612061e0513060b190e0c09040e1005090d0504030807140f 65
    0xb8050305481d0b000241e95980c0c01c0404040f1580200300259a41c644100055401e00540c01d01040014804000c18a494070a03080a46030400003104031741050f8162055088500050070802c1c101060107401a0160040340f08280c080300c0005404605440143c0c8500e11b000d41c0f000700e80d60002010b40f005a14215007400417241c00320f10740004110130001000450b1006490072070740d403915590a00450107040c0161040ba0036648854441ca009026070b8081031036030200d081d10350744503604042901c0c50010305000220425035004028421601449480c40030350ba003181d070218a1111944803803096580302c01c03084010500c0c0c901170144d4034541088100d0079900800c02401000644010031581042203000031218070107000007000320f0105180f980f580245000d0105007848504004202a5101411030400da50440a032079883c000d40340c4201030704554403e00400080c421603002503c1c5202e01d020241ca044404180f600802c08880c010708401303c0036030242c6411802000c1c110383d60314034522f0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 117991861 1250 117990611 117990623
    0x50105160501110405331605060403021b100203040306050408040f0f060905011d1219031806020309090714090a03050105040303050c1c0b04110a0810050117060f010c021507 76
    0x44142100710245a650902e10314100500d038113146d1016482c15610411090683c009661441d0000c0b40c2c0601040d44118040d030040d003d8880d02c11041d0607120381e103114692044640d8020034603240d50000c1a9000e4950244001805889504240c0c00c3c5000340e60003a12561482000810000800c18150301120141c0e22001c9900b40c41d82c0c01940d801618240106810313848145082683c501103050181c110949010364112414680b04020b841c0140001076010600c901245548001b8001003e401440729101450404c120100041d00310a4094110030412441590b60b0180300d010400300d801920008180d0000c4503541c1c5071150103040c0450b0260007080c035020026008440d180c00303d400a0b68048064040c440700c2c41c6540307004094151480e0703040782d070b204040c6004400d0240284510095a221502c15150182625140d90000d40040e41000303010184c200c8407020300d4540542002007141d00000388410b000040303407100084034020b58001200104140e40f0802c0704002c000303c5001c0c403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 117993111 1250 117991861 117991879
    0xc131205100b1c020d06060f08060a020304030203070b040302192d02130f06031505060907030c0c170c0a0303051005030a050d03020306060c010905060a0b040b010207050105160501110405 82
    0x1954008682c001d00070180c03c4a0000c030140c64025000c00412140c910060404d00158145d0700c0b10700c1140d540c3c1d040164102d00d1410140034070304040042c10f078002c10480341903180d81f40941d80203449005141c40200740d81c902c1b03030100b401c1500900156076004944c80c242004801641070202c02c00003a032840080c8003070640380b0756040b40720208580303441640152000c20360441451407100105840c000e00e40d0310740d0f034401001c8005044640c520030190f06015020130fa50401104102002c60060050818103107000041c8520903000f441d181401900300607030140d0000480c2d81450702d4410350748800f00c81d0140803040001c01d07415074826800703892603a00c08140540c8440c2415542e41048070f025019a2100740280f64051094004590143d0f02030f15880c180f030200034004e070a558a01e00111040e8000e00200490f640e8644914002210100d5042c442d002c502c0d00040d4807608140038290411200041c0c0301c0c410325144500482c000d500c4002007100d072001700314201150b04640100c1d84249141 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 117994361 1250 117993111 117993133
    0x50a0507020a0c0e0c04091d0d08011a0a11010c02070806060616060203100314010f050a02090f0f010224040c0b03010f060309030212030106030f0b06210c131205 71
    0x10038082c030a60024140d550141400d003036000300c110051441d40c544200300404948508540200340c0ea070070051407002c400c952000003480c01c0c61003d2081400300304140c0e00420074401c03954403c00310601906003040d80e0b40c403a214219009482940380411960070004404440faa0018425040300d01c2001500d0f81c64a40100300a19449509803a1860340c10510038140800c51560046401c25884c82c90509182e5803603444880d40c404001403440165954461901488101d000300380d0705c488003100461500981000081c00c0c0d88000e40494010a100310040406074020000e04d07500d200031040d410090485614140c0120a0407a400c40d001d4a2001c400a04144210103682c142d5044403c4d801b40d450410038110010000c10505804503c00c04108642a554260045001c1c0050f0703038002c41c84080e401c546d442a01c602c507840d80e0140d82c0420280e8440c00a5900300f0040c1586106440117584822003a80301c00e0184c448491402c3e03000c2240080d40f10368503940800854032171001c1e24120030350 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 117995611 1250 117994361 117994363
    0x40b0309010f050702030f03181204090501080c0a03030503060307050406170106080102090307030b04030c0609080a11070503060c1815092706060702010c0501140106030e031602040207021210050a050702 89
    0xf040d150140541c1c42800701c260200e486601640e400044001c0c0c81c088100f540d0807070782c40c0c11402c141550010b08000f6007031144c2c00090203018090b080d100000c02d60303013081c0b07000b08500307424512002c2c1c20800c000c80400ca060f0f0b028044c08008110042092145588a6641c048125403400903001c0548ca8528009981281030003902d907100c0700180a089043d141d601c80070340c04800103104804010b0b003500380f4400201c849c4204200f82d8000c0154649510100c44083c080c24454038058205078000c41082100d680c0018076aa4012255903140da202c0014180c07958502c0d020183d8554801003841d003107e0300080c0d401c00361010709002c481252080761501c4003042600c415010100703c030144140050b9442c00c100e4014080b40c0e1040c0340120b0b481c070a513220315003180c003e0405410070480c8400100000c0d503160042d080ca04e110314020758580b6170340034441c0c2c01c01e512291000f4011600419401c082d5681c010005404038100002d03504406141c00000d0001e007021141105450718210216405900c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 117996861 1250 117995611 117995621
    0x5033a03020a0f0206040c030f02120111031806040f1205040f1205060606040803040311010c060f060e0c120a1a1207240507020103050919050606100305070507110a0b040b0309010f 79
    0xc7c0040090342000e046488800f0444c80000c000e07604600422080d25519200f4400c8140c0d07003002d28102a101e003000c4c0d0610a02c40e40341070600015502680a000105001403180080e0a80c0074851000c1101ca0500c16a40c0340144e602046d200080c00300b0002d03061184410380c1416902c1002075650581d40d040400070706004038080c8a20a600921050000a40c920407402441c601414a440703002180e940d40303c03d4540c08007003031030400e460b164200800032403040100c0c0c20801c01045d003801c00220348010392460100a180ca620180c440000854802500400d0009200b000e4840c40217846206601036541c1c01c0d038031444c456450240c07488403691502c884458142807035030307480614110864004401800c0302411803040780c021031010100c110324900000c0d0040307109801424075468868104240c0c50603038424071050609210410141a40c010219140964003da040c801540010b0105560340502d030040c0040d0a070001d008244241401c018601c00c0260030000c0c04554103245200081d40c1c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 117998111 1250 117996861 117996863
    0x2130b0f041505040e01080d0801090216110a030f121404030c03060c11031303060f0605030706050307020f030307033e0702040207080d230105033a03020a0f020604 72
    0x200d0103010901c942040c0c205291101c0089107061130602da20340303841440c0100c003079000d45003541c01441200820b81e0810756450051010180c21810002101c0c0b0268040d0702c440d0b001003811921440000c516502d0b205510003442e0410300a0011000c68070700410300312040c419440c003203200c40c00100b05244e0000c0868090300c1c2d001d224021602d24550713581d0044c20118160005002e81014240100da1040000e00b0381050000216440d180c0f0b107061440840c0d01105802c01c0590612100b03000e079482c00520300049070300360b02e000d0b07503a0340c0c4900701281001042d99422481e0f010020900808641c990064296504c1014041d80829401ca142982d016440542900980c29001c1d50940c0d64070800c3c082d10420303001620141c0b412000d41e03541c10f113a0388a1000e00d081507a942c681c41480942120400504010340b8440032520750500300080d541c2d8a4100c4500d0302003520450301101006864040200c1000c1007007602320080c15190080c000e0f41065002070300040101c070820062502c0010064011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 117999361 1250 117998111 117998137
    0xc0302130e011d0a020c0a0602030621032d0703020c090c27010e0612040606080a03020c06030606040806070e011215170307021c0203190317041407080102130b 70
    0x1108020300e66841000004003121030250342403158803006c8a090003041c00c2d0754455400143d48e850889c0030084400e48030800020440408100d03550644000021191209010650580c07002003c0d1000d01c08000401c58411441d1030101e8130004154000030f90701710001c0c08460184a80c2d842810305581030280e40010040341280c441722400c080340803550307107140b050306142c80e01005144002045150b0b11030003891590140340c0d070401003801765070302c0790398041e00c0994040d20510030240c5000f0b55030750840c1d842038450400000480c0481e88c0c0c00e404c40d4010540340d000d60b46076251401d40a0914445404800c0c0420240342410741c4081440c401c4401050400d0052040d0505161540c141c60b07101c00d204d1b20307440c8000c11000d400b69451210064005054801c441c0d4091031a1040c10704001d0564500d8000d1421004448002504101c0701c02e03800340b4141e00b003d1140c1d0399080c59180d09c0f04c82c031039072a224041c05c0b001007201a03041d00140f028040c03015440c0354090340e8200240d40b602c5018848880 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 118000611 1250 117999361 117999389
    0x807060e100807020309030102071112150c09040f060603090b0903031e0903040306020c030309280b1015020c0306061c020d2d030305130206190c060c0302130e01 71
    0x15803809140380b0340e0000840c4c41200c2c1420305a001003807ca138400d060541d10501030140d010003602d070480340134600038000c81c007509200091540d40c181001000d05122000503000c05e0070200e548aa500803150105680d4044c02410b0b501e04018008040111080e82e25814110000358004400812039008181080c921301680c000d002c4d9100f1400c0014004204500081100002051182c000340c207240700311102035581c900b08422a185060801d130400c003405024003190801c0f4050b01849081c039160083c49040017a82c9610000c0140354191704506505840a068000c0a903800110802044803e0b022030300240c81d01000c000c0d0a0030360245d1a030303010401502c00750060400f0705a006807148640b2000202031440001e085010001141040f4403225800e070040a060f45801415002140c1d514503202c00c101039000316809210b003241094001e1409181401a00d106190811481d0f800001c100549208504014080d610490700c80c0b0400d946540c0200300100350010490489039026a0045 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 118001861 1250 118000611 118000639
    0x2a02030d030509121809010906050a0e0c0901030e1509031e04031101031d06040503030403090902031003110105041e0806011502030d051e070305090601090218090603010b1305010807060e 82
    0x94680d02240054500c40017949200714191640d99a6034003030242d600d00400c000341840f050202e4200e0310381c03041004d40c0006040c070101c011000e0407141d0180081c60003040c601040c0312030916000c0d03400c009112040050041026182012002d4000061580c02e103941348600c0c4413900159015600020b028290018901a240c2d800382c0d021003144105a003a01e842c2c03442d0b00407100d007443d5080318280d032550400002c2100301540184100050002d0030703011030450401c440843c2501216000042c442c0344c0359440c4401030f0303000380700395001061244090035580c0c6070004c070a440000030b41300783c0080d4880c600001c108002d1186007078600c900594021401c00b060340708050040c00f030113045590003903000b41860005000d103286040c841c074520346000c0340070308049154034075105c0d05034050340c00e0501c188190036120011066049000008890a006c20303150780c4006401005540c80301c9503c0040c1d500d520300d2801c0c2c00d402803030486e00c0c104180d441103946c2e10000e84034008a40010381c2d202c440381e114a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 118003111 1250 118001861 118001893
    0x1020309030615150c010c08100e06100207090e071505070503030417040504060e060109060206130b090c0d050f1605180406090209090a0212030415050a2a02030d030509 74
    0x8800340e401000c060380300c008190b10359043e6005d00000342c610b94440300000c55083c0c100d110f02d500308240790000111180341c4194800c004002801c10740c460307100b00195102d1140308011080c00303001d030303003404208446181d03650320f07540c0c0010f2145103060024807013490200741c0104140d9103001c0d0000007442c0755907603d81e00d00044509040c0e2400b0030150a001c00304680d22144038540c090001c01c2161141414413100240000780c0c2a4810f8085500007010882d401d02c9071200d0300d000d039074008003100c0c2d0745d100d400b03d182c18100305120072600701e4002d21040f82480400243c110303074011440251802050241c47e8580c1c0780d03955000c2c40360012407000c201035440c042c070000c081c2c0c41400359200143d07402655002403130684040c0c85041c06584810790318800d610700a144091500031600c001c1d440d0034078107a80515908070101c60300b414850089201e400c2503026a17135000c032030540c0052400d900007100002c05007038400380d0400d0b4060f101320f10f400d070344003800b912500e4000e8010b0402041303007107010442c0d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 118004361 1250 118003111 118003141
    0x903091206090507090c170403020c010507030e040c091e08120d09020405070e27060103020304020a15050a0f02030c1c02070518010e13030804020103180209070f0201050105010203090306 82
    0xc4410698500e00c890110b41c06120f91801741101080106114281c544011301500c1e05180d8501c01c401c20105000002e50001009607007440e0078240141c8503d428101511060280744841e40c000c0d00342482c4203607562f400b54030388069500100c1c00401000c0c0381c100c2c81015010500860b4001e07444441032942418000c80544801c1601520201d00e110050b070128086d580295101d6011038240160344540d4500408020700d02c191850305500200404040445100405450b4030306055002010a0030f5403141d10600020305000c0c00381840360144140000d015a00c403610b05000a14146007451208c0c0c401300c00c40d6000603001c0300908034280319400c0ca08400c000c1000c990b043d4801d004000850f9250136164a000c0e410340e01200c01558540105a071f0003000040155401b0a00880d15030700094005007a03a400c44d40a2070002000b102e02800410320f50f0400d20040d5009104001b008102984134580072a0013015500904c066640c0f1704c01641e0300d000d081e4000c0d43c10741000000800100c084408 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 118005611 1250 118004361 118004363
    0xd080601201c090801140a020c07170a020406090b0d170c0d09090b030129010903020d050307110306010f06080c0f0c03041d1b1b060a06080c0409030912 67
    0x21544060208491281ca44540c421214010601c0c103100d42c4a143e801030400c600070144c1c0802817201c21502030200f407440f5001009080020340c082841d61008604018003c05003003040000300d4890307500c00100f995003200001c101e2040e8200f0b10040f804103002d0103180e41d99100600034000c401c05a80d40c3c003401c20000c032403400d0318860a103c1c410840104100b141ea041d43e07a5200c60200a0601c03071994240d030200e90042d4000d81c1045680b580130301c940c441c551000d02410b100207041e0307481d160048541804541c0042e40c0a134441c241c17113081c000c0100c020201103200f00c2202d038a880103001450303110a400d01c43c40408c05450641001003034003418000d42d0008540e01c1c1c0340d00d001a0200382d1a140d4016a501d401580e00c04035040c070034607e1903001a503c02c02c05d65215603036807412801030901044426009000406c011810b40c668298040705980c0e062150301c01c3d100b95152072412034000703080b00c7c1b02e01342203441032081c0003c19003803a1180402d00ca405995480c5828204540d61004041c4403030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 118006861 1250 118005611 118005647
    0x611121303120f1b050a1409030606061303050304060801080f07030b130501060e0c120c0c0304060507032f0714060304110a080105010303020c210703060b0402090a030f02120d080601 80
    0x3082000300c0c540c1004d8400c10242c1d0b2982511607524441c010000030030041e15200b03a601c01c02892035160b03800143c0513801030044910903070740c4c41148039030802d201c05540000e102e8800414007007880b54100c1c10890686502c4811522100c2000b19881e9070381e6810300c0040c0c4500108404144440c894a4803020440d015800104489681d00840c01518100b00e8259010301d00103c1d0010355031403138240c440c0d085040540301d01d0600703441312459901d0b0305c00e900c124414488005600f004041c09030326600c054800100d4001016100030150180e01000001c1602440c041c000000c5000ea4500109200104010304104d046656a03694000b00b410541c4c82150710090030710300020f0b5001c007400b40038042c511a5002d003c9d004161418810990b40e040c44450070011815000400500006002001c8903000800441d28080220210b4024031410340440d8000074440000301c10701908001080065109480580d107080d24140e40c941c6030f009100f190000182c807100814560f6100d10324031000c07146640c07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 118008111 1250 118006861 118006871
    0xe060a08010329010e330105030403030b04150305120f040314030f03090a0203011b1e0509030a1128060509060d09030c0c0e16080c070611121303120f 66
    0x1007444030141009034000c0741d00004003820805603200c6030035030505031a030450107402030758450240c640c0300e260700e40f1b1442e0411101200003014144250084000448081c100b00410f900c2d0b07c03480b5207005520700058819108403a541500540c40744211120b03901501011400e01d400e42c1c1e50340d040c010101254412520040c08000c0204c0b000000460117402c006005080c8200340b841414203440342039405451191010210f42d850b95000280000c103031075100c1c500180e940d064003080d140c5000c0c280e0b2458043c402d54400c00c040002480f00601800c40403a80245a461011001d00804090079044502e600d50407008024881c0030740003400c1c0c2007100038042405c140b24203045a084030303598071040e0001107a4805103018031804522a102405c110300e860201d5144c00000c030740c01000c0c2e1a058904210303030840085c07140c501c49015aa0b07440ea02440078040403c1e02e190351102c41c0c200401c103005403140320010648001d207010305411400d505032112441c00246a404100408140141c04401600c40d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 118009361 1250 118008111 118008173
    0x2030f13030b010e0a0b0a0e0f07020109050706050a120501050d0818130f1b02030a0c030203090411130f03050a11010c12030c1206050a12020109090c020304060e060a080103 76
    0x4021640c1c044c040d1000c07144001c0c13070005028015141496240c6020f4564608144030804030620111b41c0480040c10141e62915191012401000441400360080c040e600d07012070000d5001c0d0040000c070390341e0342d5200c1003440c0e1422500d046950a114040e804200340c844000080c2c08000607203810b400c8940e0715405040c581d030108036003411002003540100d5481d80480602810341c880d0112130043c0c44540c10720030540101c0a56a48030744d210560074426800e140404151081081721124800a4002c1c414040c030021180c000760841d81408405020708070001c1004805854241c007201d0b00403000704410400c684400d64036500c156043c0d03040003945212000400d05603102035061000c6940c0004d501d10000d40b009041580f10402c015007681801c2c2c003080341d50307901a9003106403018000500010b0016100617540400740303600251000307040404440d01290040040c104031407840e00c8019000040d0801c010305407041b400d0101c00300e01e03500010300116a400c0c04d440100700183c440030100d1284 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 118010611 1250 118009361 118009373
    0x4080a0309030b0c070312050a1e0605010e060708030a02090103020706140405070504060e19090210090302090f09060a0b041509240503060403120f050708040215090102030f1303 78
    0x484000303030045103000408004000301c00c040c1d40d60050040001d00d0521440da07800800d21880309410300c2051751078001088090343c00790310111008910310700031408164203584020142c031281c031482e808103e4807600755425044c0380782126100360340000814a956202e92400c0000e422150480381010390a0001c80d00041c401c0c851018003542411500308075103040c0c580b451900c040c0741c028501546c2031403010481800b4174070005420900f05150800518500b80c0d001e0010801c8540195002050004950b109500001d881c002d8a0096507001303841d6540000c8800e09020130b560312031083d4054400616004555409500000c4c00203202180c0d1080f2504100ba08c00d64070b400911426603140448082e01070090014942480900704180700c4034a010002034491400420240500003040030b0641c0703e9800350b0100c840c2c21511b100411550500d84801020800701300c07030807401007404c502c0c0d8901140803082900c2034031605034000c502d0b05800e440c901215801820341403591041c42d810202c00203c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 118011861 1250 118010611 118010623
    0xc090b0313051528020406051b1510060207120c030f1b17060603010b01021c05090a15110f2e1109010912030e010302070203031314040c02010e070e0c0408 68
    0x340d013614894440c1605040b20702190350703500030259191041004104541d084030030340b0080d07040407080103200b02000c1006420109480321581e4181402e00c100030300c00c0a41074034002540c1e200d03400c83d9002d980385c0120101c11110700c000a04514140402000012003d40c4600c119905c14480c400d040140b103000c005107020700b0341120700d00f0b040001400e42c244208009240e4812130842c0240b1030303241c4000c0084d455030a600e81065090134070440c60903c490145d012070b50400d0024007548405a92050175501d980c415100b074800040040940e81e00140c00000e190a500712004c014003c0081c90142e01c0e0303007540c1e04400704004000b0031040700d00000759a2003841c150032200103501c3d42d2241044001080589150441907108400640c40400b096011a1882c0568801e00f0016610f54180c00000c0c03460041c4583c0240c0c601056002042c0004079484c04107144006480c00e105003903400c0c000740e007038a4180350004211317071218000308030708400d4181c04c0f50000044e860343c618041d11280c6250a1030f03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 118013111 1250 118011861 118011871
    0x4081206040b1003020a02010b010e13270c050a09020304050c130b0901120203121908060607020904050a020f04020913020f070c0806090d050301050916030608010f0b040c090b03130515 81
    0x5d50218045500c6a028092904200400d2a00c60040544070000031026810200c2c040000381c0d5503411a00780780d60010041c549840c260a0300c4903124036a01d0400d44941a074003503d40a02c0c0500d000242c012400d0080d01e000c0d41e400405814000160010b1200c110741103096074106c60784401c1e0300e48490711009001400790503d2708070005c101581d40140f5180c000211280c46069104100c4180750f085121407814445200b464030f030006484010010303080d402200350280d4440c0d0b040e401d20040210024042e1840f520a4401802221410082104030b024604140703400c1070700408107520540c038980c0103006482142610324180380054407060b92044aa4103c0c0b541c6501503420b00c0440d1004010312280035840380781081c035560615001ca0600c0c83c1c041e100948508440c995411900d0182c0c008401900e0000020001500d10020901c040c6c070701c0d410503a000b2440d04000450840c0b080c01e41d4401d0b902c00240d01403850715003c0206024880741034080d074045c05000103032000304101c1c5c0e82c40d0b4010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 118014361 1250 118013111 118013117
    0x118030b0901050105030a0b0703110712030b0909030f0901030b040f021201030327060509030a051204050a0519060809030d0f020d051003020a050118050603010b1b030304081206040b10 81
    0x54075050700c07900d0840b00c0c1a0041d80c07095000400e00030014995120441d480405440c012840c502403503e0380d8114003d99000800b042c440105800203103506a1002c00044811550380081d91101d48d070003902ca100e48580d410309900c00304a001000d501a810130560f080000e0f00c00200d14810310b0b4007400f04d030451900e8440e5164080010001d0550000104042c2160380150321a181605d149400c50f0f40f410344505010700c280411070003c980c0c0c1c180241d017110b43e004800e81704000d500500600141d8014040e440c07148440f84004101802c0c400101ca003c40c1d0320010715600103060a200b80c1e180701000701070070030900c030412120200e1115405a000d0300c3d161001c0140c0c0303ca091488840c15104010b00d500b210400340c48042001d030750740c000080d0803981b0130b0926182d840c02c1c402d602000050b070394012075000701e0b00000000f050b0384801d0042206c0c11402c01d503400c08103041141c0d59120b10007900d01800e41a414480b9016440081c4100ca40001c0c00a20025205610380c0226a94080b442c20803404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 118015611 1250 118014361 118014383
    0x1051e06041a030916050609091312031b1106010e1f120201091202090c030601050909100303020106080d020307060c050405030105070c0b010b07170904150902040305070e0c0901030506011803 84
    0x1909030400004600c02d100d00000c101035411b0801040c054010a102248601c0601c0301281d28a1101c201c201c041a8100c10450261002d000300900034042240000649452203440003201e144903068120190030200c01170031459103800c50304500340801509480703c46038034558814a0501e4000c1c418014800041090040070841c0000341580515900c44c4940791646040903005075102010144e1052110000e00d0701c075240c001c0102c81d41e00a50300b4658102e40d022040c0300004a0100521003168482e0f8000e011560720384601d41d4440710f8036141040503904c1404154001030080d040a51b5401307407460024100380c3d03140006800e40314180d84580c00f044d5191040414012111003046c050403d0803419841c0c8200c1d507480d000c141c00c00c00309544e0075540c0030440070911340e116000040e401d21551642003c1c1c544406e003850081d4018402103400b8810323210001161100d01701c0b201c0c17058070442103150410080c04019005044000d0855040248001c01c0e0454051900141000b96008003100740f1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 118016861 1250 118015611 118015621
    0x3050306100e1918092f0418110126070c0606060e03120c0c040e0a020301050f16080105091f05060301080a0303060906120206070c0302090a0e0d0801051e06041a03 72
    0x1c0050310f02003d160146050552400100e402c080448054202000340f5140760841601d003141c2289800720807d0f4003c2c20308480d031480000c13040c000000c450103550714200180c4000d00564020345000e0350701e15070b803418402d20014030314004a40ca40c00480c60426007054030755541e950701150300503044800440d250020740344140c101000708800d4cc8651316031281c0380624404c0308070b039200c1500d016140700700e8a40310b01d00780306082842030300784d83c940c0a4020700050401e003600925001d4200ca4000450180c2111540803038810001305041303072070151101075142c8442100309654005a1001d58025401c0500040c290702c1d0800194021f1000030b003c0c007030070340f03640c9401026515103034002040d8508001051000141c0003c0f4000310940c12034006c0e9448649182c60324480c0301c55800a503201e54000c0401030307003aa6540100c03c24012000980e20110261241641c0c040800e025168101c012003203d103060000080d545400040000e28203400d10307a49234409104062000d1200300050070101c1400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 118018111 1250 118016861 118016879
    0xc080411030106030b0c090103150b0304020111060106121107240c18120510050f0f01060224130b04080408060601020703050a0303090809040f151203050306100e19 72
    0x52031180100c00a01c0083d04e152612950314102800480b070082d40041d900074035038000c0d440412600c010040d0100310690326642c00300107400071901640451300c0c0c14a00800d0303183c00314035941070b90360030703180d014580c108088098010045010b50a880301010001c600124919245d1400318440501039a075003008107100d503c0c10789a03500c060354140203c80c40c4003c1303886881002d040540da560301c44940c545406080552403c41c4c6c0ba00000700c02454201880259016044042d22440a0400c0d580d00ca0b641c551089a90703d40309090a100d00610031300074401400f542040a80210506491110789551034a03043c0e110038003994104c1354504002400c104881e4103011460703200100b40044e0214919684402d40c8a83c0304030700c001e00309582c85028204110081d01690413101b0040c3c0104616a4101c0b4040010f210320142240724488080c000a40300880788420b16071035515550300d5085844100074000d074401a804601c0038070241c4c20044074241c0701c2e10070309608151a0159038059a00d840240 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 118019361 1250 118018111 118018133
    0xa11091308040b2a1e070501090e0402010302071a0105040b060403020603070305151201090c090606120207080f04180e0c15130b0703080106090b030606071506090614040b0d020906010c060207060c0804 88
    0x11405c54200545c20001c80c0e030015543e00440300418007041c0c281e6a58070049000784a2050000c09084102c80e110040a00c5580c030b49059801c152410069904c2510410a20740194031000f540404200700040d0300511a0700140e420041c249200e04ac41140c80d000101244002c907a0100303c1e80d9147d170b510b428051281850402040d000108116090920300018440d50301180361603a01c0b900050701c08100401c820440707141c00c0540c0201030700c868644294862510402d10110820750802112401ca01c00200c0c03000010040241108602c202032400712800741c1240e95402c004136019500001d00d42544c0004003082c40c0b00340e541604640c1050360280030115150000750002c6410300030406c2a0729104107c42c034041d001060100d050302c03400c003040b0143c81c00f070b0400c049245c20104c000640028000721580f8810b4201ca041c8a40b03d5036406121090086080281d8001c41c1007000c5059035014016010300031340540300c017510f003c05035142d540c00d82d000c0c4688440016502010042070142c10808 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 118020611 1250 118019361 118019413
    0xd06090506030307080307020c030601061e1106012102090711070b0a08041104090c08100b0301020309100e101109010801060503060306070810080a11091308040b2a 72
    0x204121604080011030390f240036241004103038081c0000400c1801c0d008000001c40f0000080442c3c00d50740c1c407064010111100c0c0c40140400c800800710100305075004801d80405240c03088000c200e00da1030000c48801a01446020060081c0c011130a0000b68448580541c41854070751100c0180065080c0c069240000d654406601c141c42881210f20a9502c9402c0542150700107480b8070600e0305410001d8007d2126072001864034807010310016402c0700c080b5807400380c5401141d041082100c40005d140c281d00c011102c140c91034210000034915021150700100c8041c80090440e170b0f400388502118421507200c040980307402d80001c2078100d442e40e8014903850240c102c0e07140040c110b0900001080d6202c1700034007900240026403000407051000044090000c000601c100c544400860a0051400780c20500305030040e4014400507048543c08804903801551110005103041e1412107201642c0d0410007400b5a410408003c0c410300142003c030710060040c2c808060009400b00c1c40105504c0032425807 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 118021861 1250 118020611 118020629
    0x711030601060e01200604031d0a030320010e030403030504050a06030c0e10051e0c1603020907080a0906060803030f0711101e0222090911062b020d06 66
    0x103018180e8002c0c1012a0201c0c2802c00b140d18103030221445445c007100c80501d00e401d105110420060560260000c1000031003020030500c5c00f141e41d024003820507070f40e000c01f401246002c90741c140e5001e05541c078121000c44003400080c0307540c6091100b9046a215030300c10740c002407000c1400d010b00d19000241d10010400c500741045640d040003005450000f0070080302d03103c1d94090300056202c40c010811590580c0000c5c55a05201988004018840c1c0000851609900c0340c811054032102e400d07284041901e40041410032564bd4012040f2880000240314a0510b07484107280d00010f0f826010383e030701510b280009981c0381d207132441804c098884014402403c01100200520311580007150507041030398078010201c0d504c071417403001810451441d03619404551001981e001480c008604603441401340c24400c40c0e145659032810340583d100000e01500d0100000c1e03003844c00f0b10b80000249150582c004844201da4480b4030344210345800700c0d909851681e0009070401401d030003481648090701c2010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 118023111 1250 118021861 118021873
    0x60615070c0e041a072a1103070617090f0c1e090a09120806150a03060e01090e100509060a09020d050714040b030120070f060912080f040f0305131802071103 69
    0x4940d1344080e01041b1104090b143c44460200c02d100b601c1d00703110040140941283e11a55442000804040c80c00b0301c20700c04000184046580c1d040041245201d681300c8800800a4180302d008202805142010444000e09080f040c4030494540e0044a8401d00e8071500000d864101ca06080490700303030300028602001000020401c01c0c0e03960b059032840c000700e46901d9640b00c1c001003105800500c40c0d5000f0207001500c074000001c01751480c1e0400c43c6925040c50644007000c04040c860030a0b113405564480c00c540008001461502d50340e4400e0340707174031b000070460542000b141d101c050400d0f249401c02142070342035584804603400c2030f00030a2403a210035402003105280f1101c4085020340c043ca03450102010004a490070b0003620b9040a40042e0481001c100700c001c103290800101103100341c01008510b0ba0030005002d45403c46680d4415508000c505030485443c1e60308035000d50000140c012071804d0168089035040401e1603c9802e001009401a80c0e290681400c07908010002489442640030b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 118024361 1250 118023111 118023137
    0x70e010305060a030b07020304080105010305030c011104060801051507140c010906050a050403081305061c0506040501121104020c0708160506042916080318060615070c0e041a07 78
    0x250a030f240c100e0343c005501030a9074403889000c070300f035200f075a02041c0c6c19030901002206001c2c02000620341c4541e004002c00658181d9509800240600d00c04d00001c5076004004000500f851000403030107184a204041c9050100e0707507131419590b42c1800e402c049900554a0f62001c0d600020345502410b0903003071070341c02d000501e10700801d14419400010210800400c21590070b16141000f40c02400700106035030f4031484130181004104100030907083d061400d050116415040a04c5468143da880c0ca251001c94110341d142e0b01240351150808a401a90070024001e100740c051202c800680301c448042c0820320052607121070244415000f8501c18001040104407900313031076101803440c2d800e0340601418149504d90411490041e14505400006542c001c0f000704030301c4c0c0000354800c40314110641038041880134099616a82200c6c2c0d09d410004c1205030000602d00a8098059540700364031540041c3d03211b90f90248646002d80341141c40003c00200485030645811170780354021414a0141589542 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 118025611 1250 118024361 118024369
    0x7150614210601151e090e07021e0304051201140f09030c01110c010c0201290d020a030606031a0403170c070c06020c03070603090f03110a0f030305070e01030506 71
    0x9003641030384104a40d546503041488600241000340100e84140c0b078807980d55802e041c680070b00f01844840024001003100303004403406410010081d00582d96010003e003084414406940b020b01644d0075881074000d20852040078190f00c59081da10b50018680320b82c42c1c5014420100c07100f01d001c28450741020010541086054401980244209541136058981b8013040703045100d120001d050650905409011441e0f40200074a00d01034800000c0040c82402a0101d0032940303440d4810034203071035464441100c0c403c1e42503c80c68802d8001c01c403000d00596580014012525a442110312036201d500400510900b40c483c602e0120301d4813200e00d807034075190340c00404050300c003d001c001d540302d0400810081844c200c00c3e141030710383c06902641c460b529403001a54440102c1c51444c824820910081111071082c0a40c03042660300c02080300c0e501c651640c3c15903d03161080301c902424072941c0c0003000030035949041540114040d4600140d18204a88020300c200c50041000341410f080506202031612 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 118026861 1250 118025611 118025639
    0x308030406020f0408190215030610120b130603030206011d010e0a0209060d09050606011d04020702060702130b090c040b03070c0501150807050a081203070302180a030305071506 78
    0x984888016643c01410764a407259000300c0e00b001e807980c80740088030350180810a1081a589008452040170340500840c1403005210031600260001c1152020075902c5000e400003a80113407070304034082035034030302c00000c104500d040581000d0820b403582410401d041d01400360320701400010b03400300d69203410000e400345111410710840d10b0269103800010315000c1036905031401400000c0031603981e1301b664401c440c090700740c0e410306880034040c1c000440d600c1e602410400601c8070b40300f030102c2016031221081000a40000c01c2c10f0383c00081c10841180143d41e41c90704034101c10300130040021000d45440034060b0700030004040700341001c010030060080850a001340c03a400710003407030076480f16449458824050480045001c00d69244100c0208840501040450580718140e13450043d0341d40c2d0b4440182e031041810640d0340a404200042014107200b60000d00c1d04003040c0e03c4403842c0c2d01039140842c603071140310362040e030010f000400c030380040101d100c1d981514a41c03141010301240d81040205001c04d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 118028111 1250 118026861 118026863
    0x30a0c1e080702010f05040b070f1b2301020c0f07050a05010509060703143103031707111507020c0307050901050f040609090b0403020d020105072015041101021603080304 75
    0x100c59000485080c401d40280e400e01805c1c400034441424503140002d55928280c408402185040381c102244a11500d20025200540f000c074003040a043e4132800c480800e600084c4004400404041d0402082400200303c0640e6641c014514045c10304040c5092404d550030961142031780d203104020680c0d0140940e01805800ca0f41d07103035905914582641c0c880340a915810140e0300100d0b1050205221560703400700c01c00158403808501c0046001240ca414903804024041070300c0c1003800c0d207880303881e41007940e0019542c10100d80342d1908202e010303d03041e41c116912400c10741c07103020000003660500c441140701c0340680040c4203050a04c00050804081401194040c008c00f0304000100e41c0c5a0300310400814800400b0030422503a07090100e840101281c090740580700390019200c045105200781807140ea899541c1c03600d004a120317010b0100c50490910b00c00e20340f107512a02190983e20908450142d0701c502003100d04060014006402d01c00414203c038200c41c2900740401c0410100307402c0302d03401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 118029361 1250 118028111 118028117
    0x6010f0509011e030b030a0b0105010e010804080a03020903031b062205060a02091503010f0303031b08010b09060c1605031c120e1501090501090b0a0602101a060708030a0c1e 76
    0x500250f5001c13801012070700003199240c403895900205202403981c0c641d040e280f0a0781c502c100c43c0e09800054403403001c10b0b075000b4140e000400041107424070a501030130304c401008007038034a482d0302c5810b0307101c00302901c01c03220b12581c100f0410b010007030300302030820429107002d1030802501a82030385131580caa1b08020b0105200c2d079000a2600d010303549000000c281d40f5401100f01d926540c5503070450240510038041100800d2a10750704040007182c03003801202401e1103a44580140c2c4c02c0c11060651070b0012070606070002d406100c400e4206106000300140d9001c04020300c20034916000800d443c1510280000c03150383c50b00102c4010713040e440350788103801000c0d40c0c8010443c80040c02034946070000e441c0081455004840010034410384541016048a12000b0b041c441100c940c010410322001d0f500c14200503901203003558903e80300b503800040250084007401c40c0c40d40c0c051008a00b0b181e0045504842c8000d0001c10041070811612400601d03014a140800d0410a440315541c04000d4405c103030028 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 118030611 1250 118029361 118029407
    0x3140615090d0c1a040e07120908190f031a010c0807051c0909020412020103090c0302030d051b0a0203030301050d08040906060909050a1401090f09050d0806010f050901 74
    0x8040300034021a244400e025196201c0107001c1c0c10105a003101e01d000d02a041c0c81c07031100082058660900fa10181e5189220014054641503070039103201000000c00e0080c55220044400805e15100c003402085110406000e00030300e00c46030040460f00c510558900707062500420110f00410780048607509542824100d50092641c00d24400d6030151b4803009015101d02d000c000c0c100b030480c1c12000490a41c81e144d603a55240c0790344090b0164026400b910382d0350140d00855102541c440e80110f01107a001300030402c0c1460302c0e50082810030503d6400303040420340004c0c02c07501c40740030450721040c035603d540301a00700d80409500280d01c07448184201480b4010804807901031040c013004450040c001d442041010a179220030107030a5010034450100c001d403504d000910443c2203800385249128009003400e4560307007480c0c0c03c14010090210310014041d80c80c40312600080302040400614840c0351a03c0303049207000b100040441200d40c94140400500703000904541c2d0f000b804054072014480d5a07105 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 118031861 1250 118030611 118030639
    0x20a0501092405160c020d0b09210c0607030203070309170307180e0a050402190810050a020901080601110102040506070b100b0c0d0806010c0f030f030b030106030c0b070309120809030706031406 85
    0x6031f01252100041d00462030032003803000d5482c00050221340f1401400014010321400715070300800703009020102030560000d000082c41d07a07100b64011a80810701e030070000303040310b82c0791550107810081d0080c00e40058000030601c12007507008075408030608010f0003815001802c0c21920303844c0107005001103045a0f1500b001c2811552454180003035483d29210051000d03503030700d0b03c50f41d6801113840342900542c03800010548000090003128080303401a11a0030b03103030b00e0300001103415041c0c4a40c401c4c0e0956003880301152075594000103000381030081c4400403107414030785107110f254032850303002c800d80e020200090901c941000c10703095800c4480d420310840a41d41e000060b15503020109000301020a800c6140c3c3c00c042d042490080310201555040040303d03202800c0c907080380d08500001c0e15007031108208103c500d203800c00078050b0034400c1c5061441955a00f0091075010700c1110100c51801d0042407207400340c101000618010030542c03506026400061511401045019000e036024181e5040204 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 118033111 1250 118031861 118031869
    0x1021e210f0c01060e06010804110909070906120210020604050d0c020f06030406021306020613020402030a110c07180510030204020706060503030a051b03070b070f020a0501092405160c02 82
    0x1c0da0300e1414030a001d5a400480a420703000342203500600c1c50301310075000440d41c0d035407107420014840d545c00f156031800e5060750750401610040c020040c240c039200b54100807400e81c005014bd50014600c0241d40402e0440a104200565000d07180e400c0031075021100b004081070700021100c5200302e8904000101140c54008210303841032440c212034204500200388010055550f0051085402090f5070400c042d407180c81c2261641000d488610304020f04240da4405841c041e802140c104080c201c0006281e032007035100240c10b0300b288094100c150441c85c0d00700302c00c505180c0210f038185608082045603103000c110303040d004650390002074005c50b0f0101d8018108903440d4032210203042e0013022a030311384141006c01446a1b10507001c5108001c030f0440d40400e00340c0c0000941d500558401c0c2480415556808100d829104000a07082180703d110b5060020a10a10076480094000c95a420020f00200e00c581c03119210000b08000c01c92426041002040e10082050003812180c42d04c00c6106500703000003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 118034361 1250 118033111 118033117
    0x50603041104050c03010302130b09061507120f0206090303070507061a041434181502010212060306040221010f020c0604030f02060f0a050408040e0405010b01021e21 73
    0x100303030000e03d00802e0010710300e041c001450403244200e50000c030151a2511040603100c0b400203058002d01c02d18085601d03072a00e81581d4031400e2030070304038508240703440d10341c0d070905980072400402203840c01c0440f070726069040c03000c00c0c0c0c002d0000e0000c610314240802d000340303544075440c0c000c0d00041c1e840709210303009400340080500d0000018400c5c0502814404412402d60b000c2d40d10010b05000c031b41100c0c510200d0b40f41c1900000d0f420203038250b141003080c1002d0794151980c03840060101000d08002c602b4104480d02c208141480f03034001030f10b170161002002030310b84005d090103119912000c1001300580d521105c69070b281300c03103948102142c204000424050000326622414803400480d100c0c04c2d612000903c0e600c01c5001740c0e101c60101c10420070a9071910310607203508941419480000310300b40300d642c028642143c13041112920342030f0f4a08607046202001c1d5002c8034582d4423040000d00700d6078100400c1e03401d0010520400030b03501c44d004d40140c0d1002c09080740c89080101691361945030200d4025 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 118035611 1250 118034361 118034393
    0xd05040609060c08070b190b030106140d0c03020a090510050418032714090604050402011205100902030a0902030601050a0b0a030b0402040f080f010c0311090d02040e011814061005060304 82
    0x80300050b0b0410b81c3c1140701a0368554521f8403d82e182c10040d401d1171505010380c070100d4000d0740100b003080b2901c40070301401102e845019104e0341128040000141c0b1510030b00ca005101c204400640c5061102d05c2da9010030b4594009403265003000d400381c040e10400508800d0003541400c01c980c0880c851520903030300c4a000a6510300540c1304120020711184146995070500b00d0845a407032041d640c510400040701e4040d5006800a8005e4140c0340c820030540c0c3c44281c20031244407541101382c1d500c0000a083c0d0348101c880741c0c14640c030b402c885021403e04104031409400e0807030380118041d08200b11103003a802040c0100b0105500c4081a03281500d40d41d040310041c000c41d800812185845825095a89200824004080d071a0268180c85d103071107442002004240806158546200c420400079040c01000007640c0c0b16039100d4100324403603400d104852200c01282d0911030300014500b464610395122030b800c00e00982002080200c96124800d208054076002ca448507103a44450070310709203508801d40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 118036861 1250 118035611 118035623
    0x1050a030b130507051f080919030c0609020a03060618090809041503050601090c0f18170114100801110705150702120414040b0f0d0b070309150506030d05040609060c0807 75
    0x1c1b45592058684a200da0440060784510324107890300c05190340e481e01c2000f220020310600445110010344207501041d0194058080810600a41e0f00007900c0b044071a40b048401c90354420007001a401c6044400b05031208207030381000500d149480780907952050001480c031450340d610155028806010082001d190400100e0314550b840f50a0007000707010942c1c002010400241400a929100d002109605080c3c45081c000007864001a400207108510402c130080d500e90007601e8071011802e07040703489814840100c1d02c0300f1789002050303402c5500309840d02030b140b20700f00701c0d26001c2103002844c0c1844080024012030aa503480e0001c03410004024452100c60700700140c0090400144810131071405005c84040010000700410090200e1090340e803150009910368001011074088107100381d010546050104d510b18a81e80d6280c1e641e103654861001956840080c413160782410000c400c0a8052030500c18036040c01c2c501d01416010482c1706980c10011001034003030811804e0800c0d120000d6000c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 118038111 1250 118036861 118036879
    0x612010e01090807140a15090804093e0405090406090813030c0506030405061801021b0105010e070309020303041203021507110c010203030c09010c050a0203030c06070801050a030b13050705 83
    0x45480c0e46160f0101100341c40040c441780340900180404100c100a1b00d03071001599805c02c641b543c202e40905110582564411014000001d51014600400003403996413000241d008041500d145482201203400140f14140626034842038649802250f080c0c070300858010100c0d55862800340003410103201c004040c20400b00e040c85046000075548419203100703c58052047e500c900c24442e07180800c45000d0074540c81710340891003500e040c040c2c4d00d14607014140003515203140c013510034405182110361120542c0d5a940104801e141d90b044880d04040c2918052004002c1900020360701d004501964003c03038207032403013902014001c114003010001d5000080040d4982a04081c2944241c980700701000d005040c9140006d40c4044200c91246c1c90301e44d00f40b0f00f07021152004440790754880100315800d104460300e00c0c02603a010000380c5002480d90307000704582d150684000700031000680c465030142004403c01d0000401e14180f05502c10200100700e0340101244c1012854803807280d00098000c9620 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 118039361 1250 118038111 118038113
    0x206130801090804080d020615010509120d0f030b030a0201140f070f060204030204051303091401090b0304080c0d0f05070f03030b0a090501091104080d080601020a05070803091011060612010e0109 86
    0x1480140c012a00c40b082034071b07819000e003502641c035020100d43c10111041c4c41e00540301d04e036000d0701c06001c03045c0300a011b401049018007200f03490b1020f450701d600b0104900400d8214030f954140108810013100b60043c24140c5125030020b450304000c4000711594500c0031030500008050b10701900c020540159014480104074108000258131030b00091340a6410940020170109201444204541c1c2c0355480181d0703d490190440c00b000e0045440034100404650001038101004c00658012402200e20380e50b155856407850340740c000f0801120040c0401d081812400c140c012091b41c1c011500141001d02080562400310021701e810a0f04d15888812824081900d030700540c010b90596500d1a0100100242079402c00701900491003509040d50101d2044a0303254031a40c1101d810640c180110b6101405030fa50b001c0c01d044154000d140554004103000105141c00e14601900440d1800c000746500704140307620740c413400d004000034041c4607050559110860b0942c88030000c1103078000200120703001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 118040611 1250 118039361 118039373
    0xd11032512052703100203090f060f070503010b2503030903080705070f02040b0102030f0d0902010f030606021914030703020120030f01030f081902210313020613080109 74
    0x6511410380d0740750104501086a42d010700101d85040381ca034100c070311090410f00c0c1591206940711900c580c04d80504043c144000406001460160a1090182101140c01196185011802130903e03001c91380580c00d04c03280c960040200d0741510804881b03543d0f190b105651959a076094104416104684000c203801855416408660391900ca5903410b04541c8484330308031600d029800b00030380402c50320313440e040041c50241c2c80701541400c10b005070303418840c0880010100f50032045200c6509512159410115a4001400c890f441040e080c04c008807824100004d680300c2807018031040d0118080ca121080c09030100800d07100d95482412240e0324041351070024042e00110800c0c3c19591000c40c41e5918043c111010380740b01d0801c2c90700c1c100c00c982c13030b6845a04451014000644500318100314002091602440c0d01ea100c58080d00200145021074042d5900c25480c0b0240d891799203424803d0008510508440669090701181d03819181c1c918880c074450444070941c082c003a00c1d03103402603032010410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 118041861 1250 118040611 118040677
    0xb04050f04080d060b2101060e01050a0c05010f020c030c0d02060c270405010609090b0a0503061b090907090311010305010e0c0702030102270a0e0c032404060b0c1e0d1103 75
    0xb00c4003255101e981d070384440c25540711200240700d0303006c03403003c1c409000c00c44e10070701c0d4036007569013b02e001088074907945040c041264811002e511140e00005074400d400c48040200e80e83d0800c0d1171000301070350301d045903030f110640c05518001000c2500801c80d80c00b4401c5011fa0303116200c000284200b069583d280341c09400c2040e1440f500810781c0c20200d00c40440c0c40c00020540c11030700060058449a616400410106c0303034016040100c00e0f000340110756164940e0300c045849561284c072095481404d40c203002204003070f4202001d0405003400c0040c48045a20b0b440c0d19005400c800c1029164072081c40042e019003c0c02e202d00b0890b02e840b035104a481202084d0400480c0000d84d070500c000c903151b2307845503401d9604590496211030104045001c2c3d050304040c40c6501c00441080c070b40c1c01d441160025054800701d40c040984028007044034021070a00344001011202200c030784031490303484041c40307507100c4405501e180d0078840200f84681c0003030302c01e108869401e080c200461803642c0c4004080001e800d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 118043111 1250 118041861 118041907
    0x30f140a0605190605161407090f05090715120504050a12081e06151602010809151503030403170c06100509130206090307060e03010b04050f04080d060b 67
    0x190418000050b01c0c1042d140191490b0f40d55180124058240750080d00d4179806000c03040c808401003560540031481e0150065004101d01c1c0c06003040030b1408210405842c40600201c1c01d07549400c040c0b041c040d200080c138200312001d581038100c6400001034156a848420081c020805003800b080008009010400000c00c0f403080070881c0c00ca0301d01d074808031410142100d4111602081428111410b241c119005a00c120010540804640309100c0180389810180b80101c1d0000070a2003c011582c1180f00f81e9400069100244000b43c3c1e680700c1d00c0042440078007040b13141d190384000707140b45880500032500034641050080851100c0c0c102c102045601142030b4840500882d40401c92380c0904d428440c084071001031080c1c42d42c0e2151600003e10b800ca4540c206e80c0030304c08000f2211103840a03c245c2c80200030686031510400300e000e0516007580c086a8040e03105074604002c01c403400241c0d10000b500140c0000d4115114403170801c1c840c000f03201581210080140104201e84481c0178112404005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 118044361 1250 118043111 118043131
    0x12070312050a0903030815120d0f1b020f0406050319050d0203031308161209090f09030801030308090f06180f0d050f0c01020405060c010c0f0504050112020307030f14 73
    0x1805409401c4400d40a00000c82001030f01094080003c2485009016000125840c160007010100030000b2800e84400c09800d0031500032503e40117480e50803894400300089103080035800c2422018901e21080b520000c000d12400c01441c0f1300c240703602c666100f003000d00000b03001c807140d040c4000b4006580056a0000319074a12520002c1e01c800c078400b005907801104801c01140421704e4540d2025000e0b0030510038413079500407000750200072070445500d0342210302c8151110200242005513400586444220303a903400d03030400764003000203a800000141141c1d0903240c12800780d196141264103024120164945070f114a6003400ba41d000c10001c005000d000788012110040c0c4400300281e25400d4245498010138402d0241c40c032004014001000c143ea0100001464a5241c1001503a00e82101010110a0703558110983c00c0c1c2c3d0700b21092001644160138201e0903d032070a4002808915088049211540c020020400890007a000300340d003605400d600340483c480c07820000741d031400112103070110 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 118045611 1250 118044361 118044383
    0x170c0402130812040e07120207050105040606150203070b0f1e010b0904050105040b090105190518040c080714011d0414060415030308150f0a080303010e010f082a120703 74
    0x108204800701c42c2140d401c81d044a84a0751072070300585002d47d2003003c030b030380c82c903020803000700061070030303c0385902c52071052400082c0181801804456001038010800556204111840c0421000c01c1020340c0249445102d294a96903410500d48503940420382c42501034165002051410040c006403481c2502070700c041006aa891302040141d0b6104e80c160f9420524010051001d4140403c09513400400942e0041200b581c41c00416070900c1042160101d0382d00c494284020040e1448a900046c44480d009200b02402c3c11008292804004000c5041c0002d0b200b0000703002c004889100d0b424207009004000303d03240320403117160841003154940d20640ca044400b44400b01030b41c408605903605591440c0d03c07a0366908000d03d008d4001d2500ea5804002e40d410b2003581e0303807824402c2002c6c1039200f014540313951422840c01007002c0c040e00315044000031500c091005030340014445d088161072580070f20142d1070042403802c121031542d0344650084c01c080007504001000040e98003c485c45002e10900d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 118046861 1250 118045611 118045633
    0xe01020c0607020904020d021f050903190c0b09040f02040b0705011b200307060513030201050618072601060309020109050a06080402060f0d0903090311031501170c04021308 76
    0x4075210b107400c02540114213001050160400c0b040410402d80301070102d0b60040110514034aa4103401054800014400102140b9a0070180041d9900c04a43c00c003400000d0100e0380d030b0344080003041c010780100301c4012520001c1a07899801c1420703017401d2240115500c81d107500002c0b007180d2101e80d00b61031560801d001d0120380c1c80f000c2c442c451b503588165640c0701000c08840b045484801d240b842c2d08103620081c8000d80100e800c41c03107424042e0040c3e030442d25600300503140c00f03800c1d41c1d0010001c0d88100c91240c04100710350030b411603a079030000140ca810f0100010350841d520b810a100c16880c02c40d503101c840085101c0750164000900315000b62144c0b0f10040c3d0364410404540c0b154010040003c00281c0440c0040c14040082d00000c0c070544601070901e240c614011b8100d9100c604150001000c1040c104240181201600c2c3c42c54400c1e03001d408141d80d40e41940c24006014310581528140c40801c0606140c000d000e507012581c07000b00150358800c07844507000940f48060040c7c1845024036202c1d19 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 118048111 1250 118046861 118046869
    0x3020a06020d090318031106070203030d0212180c0f04050a1404080307120b03030a0c080d05040f060b0906031c02010b1f09120507050f0a0306091b0902090109140a05100e01020c 78
    0x105c1102c2d440824012401034500a0080e90b801454040360984801d110b082042c4c481400900303284012080c104120b454818100b088a881075007502055030040c0c003181341d058560684550100c1011b40d0041a2174480c448204000c0c0b40c00ca83e88000606040305000c01c01660000450003100d0664030070403124000840c0360100d89072000c5460345603004200b47c40140b4090a01c40003860b005040c128103050b1040c04a20554104540c1101d80e071071840058420015103100340320100e2020b80d49a441c80c130300000804d035900500c04128611040000300b16540070f01c00d4200c2d4002082c05040201d03010fa000000d4840082001084008a00c17401408200034410440b02081d85800c500180500c902d400e0600007083c0e10701c22080d030400c40007103010020030000e000f0b021900d03100f6002c0070f100405094056120b52900d0b0003918020740104012807040c0c0c0c0c80950031003510038800881200b00e0000c000207114100c0d81e803205802c200608682411180c0000905c20414020307020788480f500e18600300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 118049361 1250 118048111 118048157
    0x105130b03061303090b0307090f06030515010c0204020d020a0509031e060c030702070f031202010606050412171e0d06050109060f05180a080c04150503031603020a06020d0903 77
    0x1d0309039021100148400c48440d011610300ca000c3e051045509496500a2900354002c8500c030010840003602041900304180080c4000c0c85035140402207400c000308601c41c00160089400c0c1049441c405240555603158100c4081c400144001c5598084580c8054841e0300031444c00e521a0060094403080703000c26125038440d0203060005040103998502061045400c042c0c005000c500c16084085218146680d186028500460781c0e4440c0c54052035000382520207a8105074100102131004001c0110840c1b4181025640010740035080c00004020740c18900809884c60510140341c0d0f0604e40000006000744407000c14940c05108803604c071001902c204c0f1082c0700301400551900b90342d13911176114001410080f804000c2c0d484142c0d10030000240b0b03c100d580c100500030741000b1609580761409200e095011190540c440da4000c1c60b100001c1d0310f0f40180340c0c1c05064446c000ca01e600405100740f080e17a4440d40d1005045441d207a4540c1c2c50001071000740011408213050041100c9403040314008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 118050611 1250 118049361 118049381
    0x1080a030c0201050d061d01031b0e01060e01021f0204051309110904031110051905010b0406030510030b01080606120609101104030818010f140301030b250206010513 73
    0x140e4118a81e09500440f101da0082c151030700e4080d030300d43c0d000c5000c000072880645503d42e1800c0d440015411800c00101d2840c4040f42d1010040d00700c80100920b001610045044030fa160401020448054005078140140b03100c1c101c82500201010709050a0b43d07901030000e584080c1c1340880040600307442c440803104408405010350701000d19002c254544070000c40d9105100b460007190a1071052001707403411a20403074000045460b4010042c0041c5070030b000d240881080704040c041545441c2417880036201307500502e000c140c2c8950008000d90b02d14441e0b4401541d101401b0082903030f481c103c840d103c180c1a1041c81c4250b17002406c0c08070070344000400b28041c802e184090030f4100d203509221001030000c501c034100c1549080c04000701041000c4003400c0d84101c030005a02d54202940001010011005a40e106101c10070070104c0680d054601560306403079000986c030f901e40d242c502080c80b140d094544100e500c881040d0400c01c0855000c5080d034100c6400341d4203540c00d201000c15050540d120768074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 118051861 1250 118050611 118050617
    0x6020f0a0605040611070b1603062103030617030c060c03040218040201030e010c05030603010605091003030509030a020a03060c03061a121506070b011406030403091e090c120501080a03 81
    0x5000404100940d010503085132142c0f80004e540401c040290905070002c00701510200701d44002c00121a6191445100c2c40c5811b140402c51f40c1c4c20404441b801d1441c40e00071000801400501f0010103011382e00820241088400740102402001c00903aa00c0d8844d480c14206405943d010494211100342500e0241d0f13402451030589586c103101c200300a10005005904054a0384d8540d252103a0a00c41c107140142c05590303040c0d981c60b03c2002d2509454207948003500400c20a010002d2050300b601040090300c1c0d051800b9a0b40e0f03418200000e282002c1d01300042d603c07883c40c580000030400030750311020265451381c909106403950394000d20945881504110418a0200588600d80c1100d40c0c110f6880b540224820a1403c10080403922540240b9404c4600da43e02500601c004403010400d55004602100c84524624007680d005200000604c1030400342041d50382c841d2403440c006c0e1000302c058144a0020820242064402000726804444619050340381c0b000204000502007441c16500d90161 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 118053111 1250 118051861 118051873
    0x102040e06010f18090204080f0a03050a050c0a0b010b030108010c030e07050d02010504030605010e0907090b0618120604060c11010e03030615071203021803030315060a05041e0f06020f 81
    0xc010b444031034100f4596020072001c4840c00034500c1031310b035400c0c0c0601440e81c0d0058696040900c0249490450380340e010250380640d07036840000381d1081c11500c7e0020785161190310358503080031080c684060090001c15051040c800030841d03142143c051412210250024030404400200503801c031050340340240200e40241100f84010304040048210440c8107150a6260941d26103403901202d00a030041c11a1864000030301400c05410418003014004042040040400100c005000762160b050b240f070b02e41031010781d80c09059640701400810441c00c0c50648003540380615140c0c00a010550190b030219a60a5007003200030014820301c00c18003005e40042d4510740780c000810030491410030948441301400c1121400241c00c150400c41240e62645000d62112a1107032b1501c180c031070308480726010b680284108201034a2070040e0b40031100b0181c80c181da9031002030706c0486691049800c078481e940c00c0364007034045042c101200e250440d190032100100361078881c58101c0c1c541c9100c0c2c0c00410540c1c848 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 118054361 1250 118053111 118053121
    0x80403080105060c072105010b0a3b04060506010206010803090a170c0d0c231309020301020d02370f030b181501110106080a0f05010b090906040507080102040e 70
    0x400013000724500403001c507001c0c5681c2d0003041e44c0f10b12585204101d055254080641088024000c1c800103640c2160b808210504041c980c04000b4400500020500c030307490600010602441002100240c4d6480c1d050308928007404c081000d4070303041c0c45060051285c1400066010004002e840c05420300408070754000f45006101c1244001c80d0031101414054020405459542c0000d0316000501c01d68035001c01501d8022085458200c801c81001e10410358030074091a0390300c02d4086440040010340020720000d29001007802805041e290b040c00d140b0005c1c006604c40e51074126100041042c0c06000c80c0008403010b4140094042582c51000c138203000a00381a06000390440352030540c003c1d0010100300440180c0501030702085c2c40e040340314016000b101c4202d503803000c040c10003828004028000540781915140e56401e0301003000d0000e114203880f40003080029005150b5241d40240356a526081c4544101c3e19000c00355400c481c0c0b0301c240c000c0090226810300a803411222000f207611210398413 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 118055611 1250 118054361 118054369
    0x309070f080c063a0605010f120c0207031410060b07020d140a06060b0307020d090b0307031d03120106080901050907030312021e13080111030106030b060c07030501140106080403080105 81
    0x70400f4000f8083d0038110555400e24050541c1d405013a0100c500c1d1828000e011420320100d55007904624108404007980c1c90b071058010f0780c44542c01d01d00d02c1c00051922403440040381080406d40000348541801c440700308a03500001000442000b4501c03041068a644241010716481800310003500241403601d5400454034014002d0f8019400c4000c0e02e0300c26000d9940d00301207500c01e070800410f81502000b48010154100406900030207070b8100101580d0501c41c4400c15400000c2000b005c241d11031b6071400414048400c4c41020f030084900f01c9880d0100d03102503410680003409080000f0b08000001520364005014060007811100c0c00fa008803800c40d0bc0858002c01030294039280940c00b00100f07d031216804020410300f01034810455220318410907840d4012847c0d50100050360b04183c42d41c43c422402c68122411640c8600300040c020086101150550003035150782178107401120300c000144441904507441c000300c1080c04905a83e2150f80507a403500c000c2d240a00050008801170200f824 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 118056861 1250 118055611 118055617
    0xc0206041703061f1e0507050a080307030f023c0a080a020f0c070e070c0b01090509070e0a0c03051003081909090608100e01061a0711150309070f080c06 67
    0x3d403460703813000107020903c00d00d0104800034038001107542c107a00002e08000c06061689040307902d403c520740825625800c3e80c1c1c013480383c0090508500000400d545a00950210580c2074150b4000d54859560401074880000c0050410080e01d203051030b2803540e00e0240c2d0840059540d1801c0e643d04100062604441c0c0002c0140381840859081004507a08094040901800010040200700142c140800c90b00011005003501050008a4a09100184190355046d0642d001410000381c80d0307607440070b0301e840c1c400d5a9201c50240780208050041008840d08080604561074800384096103e0120011150a1030702c0050083d240900c40c2441c1a00342c81c52040403a165840c204006580b6000c1c0380041b2440e542c0082443c0c0d11415014121900d980562605651000300030080c00c0e01c2d060308400300300c0420195000c96030000401004202c0120040d4542c09009044003214091141184c9065803094030920f000c3c1c4103000380059180002c01d680415509410050245680c91806001c0c16030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 118058111 1250 118056861 118056871
    0x12120a0603020a090b03150705040302040506061603080906090703030c0308180313030203011104080604140f2e060510050d061508040c0e0c040b0703120c0201060501030c0206041703 80
    0x40d4480100102507515080e060018001c880000512500010304041c038121611001d00d0b03200c441c0c8400c2100e22608003056404880d01502c0104031981c412000540511034074410044e80c5100140780c4043c1030340105880d22901b81e4008a800540726904441d959a2281c440240041c0d2281c085c44002845180c20780d400c0002a0241030200c070b07041e0951401d41d00010003000545041510420643c9400d00030400c1c65109500e91074945828001d07003580b11440240301030030745891020001c2032100100917040c9001543d6054842014010034100c900c00e40103407640c886001d00c405030074500ca4051280c41c088030001001001003000421064070103400020300d20a140760764600020707443c3e508007001e07101000c16644410440c589482e2407400750840d0b8105a11000001042052151082085034141d40c110100e0603150760f500d10f0104c074090f101c240d40d022518200300a0401141d015001802582c1098a061211042c070740002c0741c1d20001114050840c80c40c070b4100c101c403028450300440c3c002c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 118059361 1250 118058111 118058131
    0x120109021b070b0a0315050907080403050f2109010c1e0c020301020c03090109151b21021f021201050d020d050a03050309011a090f06010306351212 65
    0x515009601410520950f12450301c2d42800503038040c0d5a640f521900680800784c5201d2819a410b003000303e000551300810340828040c0302408501854000e201341e85201400b1034205644862070b9480e4045d12400482c11036a1012040105021400c10b00480d8100c20349a1b58102220b680f082d032401d182100350940307500384009044c07042c026817820300081404c0a00d43c0e00442c0d94400c0080010580720300c5a00015500c45000140d01c14030b40c3c0040b450071603001806000c0c45442d958106021815401040503145840c07281c17180a003150046050191908054200b060702048002010268490548480d100701c01e50b01c0140030500c0c051046170100c1c3e001414010417420703036549480c0b4041b201d200c264049513001c4100040361900b4001d003120700303114030306500b110171054000c079801c800080c1161140021800000300d283c1d200341d11030401814540305510180c0c0311802e80c0702c18024108041c2603019225400e2004107100082c2c00c003202000001841e180055290b0f00fa41081c0c1c02230080209 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 118060611 1250 118059361 118059397
    0x611032b0606020619020a09060e0613060e040f0204082e0203010806090f070b030720030d0207021f0c2003030703030606030c030501030308160912050c1512010902 72
    0x421040d80c400c0388064000c0e0340040041c0d06101c0c507400d00720480411009403543c0100200380007a64003d580e14100c03100e03818102201440c0300c000503038600400c2c1c1448c1090a0b000300001d00540e202c0b152140f641c03015a41000307400c11280c001d80c181e220344e020341d1005034020264103d54040b0b000040407044080750400e0290900c901200060364000c0e804100c0c1580b0aa05001140301c0920001e14110241801042e05074504401000b050000034070240134460f0b031241d002e0074420300001c10f11150070380c8010380e40e80d120012a5100250041c41040c0d014072800d900759540c00320400b10445809100740c07a1015000f41700d44e942ca44c00300c034012a0100e05202c090f0702080d25102000500700302d5119440c08205a428924010201d4900a00010030141000010000301e07810041c0c69402c07007d88a06081c00c40c0c2100400c0d81c511503264400c610400c4112501400d0107804104010004d008407101002214a03409054180c003800f005602d0640f0703424010049141241d00512020b80724115060b5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 118061861 1250 118060611 118060687
    0x110a031536050108011e050906070e040e0f0d140906031b07050d08010303080f10060f180308040e06010503041703070c021306060905030a08120c070f060b030106061103 74
    0x90725030a0340004e00726034646110030924107184c0101455401240341c100301c42e14084501075034625004c4e0496051091000e40319120361500c0e0890804150f8000c21184155074121031a82e84100d81d214140c00584021402501484280d003285c40d0514024503660035510740b030381110200512425908000002000002c00103081401443c512a80c240c9500d005503240d0b003005440004001d00001100d100300081200000031400b1010989283d45000c1015404004c1c0a9031104440c68443c410f100d10660000100308070040108240c590305008040140c50382d00064030300340010b0341c00600703507058034032000d144d624401d002c0c583c8034000b4642103c1e440010303008100010125000308102a0b00c800091003160341000e0280d004150640050401840c281c03034601d058010040c0744124440fa081c04103030244490310590f02c8554001843c41d803405500d18051004200a00c0510700950801100182c4107018248209900010102440c0340c1808800803001740c4010414038104040048140c1c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 118063111 1250 118061861 118061969
    0xc0203070902070203010c050a020a0b100807090603170301030506180313080a0308090f0c01050f0d06080a120201020a20010e010e0114010503072d09110a0315 70
    0x1030014401c51000590399409401030500751049100c5210a004082040014141d4001910b0310841c0e0021038240107900c13003101c0e05180803901d0344490f00921500001140c035180a60040c01204c0c0301d420f504403038080310140c02d021404244005000c81d00540005100300349030400000c116004038003940c1c60946858184e11008505810040090344800140c000301500a01e645410071b006900a004c50b0703500001059132088d00082c401c0c10088045600c520001050068918007400140d06100003921140e240c1e6a80c80c94540541e08950340300b94900886006100b00d4850040e2941c40250005010409606403028902100d406668a11195601c607100380320f941140c881b503400105074408007168003d03103510180c10961003500048000c0100391080360f9198540c0032201000c08076292446d500c2001698254010140607051598004e60450444020101d00c0301988080000800030440d0101503845400748034000600500300045030300320390750000c441c80100c071340300c210b8206040c50031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 118064361 1250 118063111 118063123
    0x40b1b01090303061701050103110f010e0901060c1208010f051507060501030309050a0501031e0b01020703080d05010f060806010c030509130905060a0c2a290f0705041a0a0c0203 78
    0xd0b80020743d0b68606000380e02c0014800714954194130000c3c003c40d415505d61211003140803041510a250795403140d0f0303043e400b50078821b03c48540200300400ca5a5100006000b0301c448050490f078001c1c03050004101e0a00070505c180c1600c50600310400500d05000c00d11582003c09040e100d01c1c0c840c24480100001d4280c0500e030302961180d5a0740701072a290000344070b0200b14580009050506201c00499101d444001d0321a00340c400f1280404e084c40f81a0050781002044c2c3c2000d006458001a2200c3c00005908030904031440d1400d450561a640e200445504100352a2280005d00c48292031000c079100f200641543c200040c40d2208001c0e8058800048031040701e4101c0e010340140003005030542440c412611210080d082041140b03501d0410004416100103545602d40214080398007800b259902c0300d8030640425407260a03003034031031900d0f0941940460b00300c180380020900142000d4400e80039101110f5041d444023172500240080c2041c150025100581004505a85000569410845 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 118065611 1250 118064361 118064363
    0x20106050406050d02030303060d020d0c1d0106030b18070201020c0313030b0702010203060d1707060f090b0108190b0c0f0a09031101080114120c0907030e0f010c05040b1b0109 77
    0x10854a808148801d40e20340e07a0049205001602e044c401580f40801160303804402112110300001c040d00c0000c0c0c210840d9000603040610403a400f04141c074141c580418402039018024100b07a03603c19003141034031440302c1c00940041c07071907001c4030049040d0390b05640c1110190001504041400040302d1654000b01201d190010080c4420820b11010400a541002052000b5407940c81d140380401d0000e035060350000d041d103c40c07095034402501c81b002503a40e00d95001c03409100141c642c2800720064402c4003c00d540d02103a8000010b980c1c5000503a6210812055030307240b0001900e07817140082c1410007000700340030f444100040035060030500004e0001050b10340307802455500f50f007403142d2a03118100d00c4078140f007140401800170070a544044d0300700401c100c0c1ea0705140c190340c000150070009200d011681007a000c009003e45540c01d0381080350301495800c00c64110142100c512420380322200c2c071810104000700000c0c40044409001002079020680c080b00300140b071f6210382c608450007014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 118066861 1250 118065611 118065613
    0x90a02040515190e06120c1c0203060702010504020102060619050306270102030103080405060d090f0b010513020918090312040809010809031305040b040f02030c030121050615041b02 80
    0x41400b001c1c0381c03d00200d121000c00c41400c56040c0d090425032500802c002e00054401c01245207944644003081014444055000e051109000014140030407040c0066604a03c0303801660000b401007441407044034401c9805a008080c44e0f00d5081c1800051400441031100d080d070302da02c011a02d40c4040104070300480c030020800c6a610202e000a44050350b0364054110079034010401000860a0201039a01f9680d0480d5100d030358040c504815402070059110090805064010410901c4911701c55181200c10942d544d80c52809180014801c900c10008005d41c460355890300010094000c1c4042688031a6450440b4689100b032060aa040f42d4212021500c00304002042c000b0795030300c0702c0a107412000b10002075007842d081a0074500980141c0c081d4a00641c1d50359964031651f501ca80041140c0c0d05400780442d56424140703010249507100340a0000200c040b0024540c1d010554502d9414154110011b04629240d8150710310b00202d10300321a0764820345981a00c0d0080f140070074001c10507103d5030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 118068111 1250 118066861 118066891
    0xd1d0d140609150103170f0d0c021c030606140726030115080c070b06130c020f07050118030809010302130905070e01020105011401080a06031208040c05040b01090b03090a020405 78
    0xb201d440c90401c0071007044902e420a98010000542485da80146040c00c2010f500c1d00d550340f04440342007034040d20b80f180008900709800030203860340119401e0345e40103400304284d2910300640c80c20f4042d104035200e80350009000c0403010120040c01d60150943e50b00c23500d0b0351132504521000380700300403964521000c0303a050000010803c2060805a1245406050038400c0306454030009500b094012110b0161001c0d01c10b0340000c10310f5841c10b10591100345800e40030000a10a0200290344000c09480d15415115080011921b5030158403981c5c0301d28080b18100d00600d0640d40c80c0c01c12038100c0440c0c6418140c0a001c40102441083d1080000c1c20101c0800545450600d900134000382da58100c26056914010051100900344542c1c070441e12070a003040700017511648159001440c0d598005086140307240e0f05128041c0d400121103006a00501c000040242c891003044104c2d44076070b0580c2d0105010003800c0150282c904003451303200c0e1f001010786202c200f003a00424150344003224191150320b215 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 118069361 1250 118068111 118068121
    0x11151c05010501020c18040309031e051207050309100302041a18011106071d060301080114010603140105012a080c0f030910050325080601030e0d1d0d1406 68
    0x503100e4940100401d10003020f01e0610a40490011841d26400e40700d800301510004003454042d501c840001c641c0440c0d900145082c0000100d0310240224003283c00b8020688a9040b940400f0b0a96103203503081005545044038601c10040311030849071216050603000c0c000040c01240c80d085a020f0950704a002582c1c0f0341050383e100c1e8403080c1d00c40c140d605000711000c00600034000003900e10303808421414440c1d2314050000c08042558046010300d40d10034800000420a030070190807180c52000880040c5071243d032644c00507410398100d2985c200103e2551030042007998410006544038203000400d186040d0501091095a01c40c8034134180d696000000f8030912000b0700300190300c10400070ba8083c60a0250740d074001000e445800c0440410041c01002041800d176143c0f01081d0f0038540f4a03e451114400c0d0070780a05014001c403801404a4903101011030ba0910100340e01c03600c00403990b14020f003044080100b600c19140840020340181042e207a000004054000c00800703105408001e0015181c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 118070611 1250 118069361 118069417
    0x303032802130306111e0306010903060203040515010b03070c080a030e0f0607020c0415150302091002010e12030103080d05040305040b0403050309091503031204080d09121e0c1115 79
    0x3100c005e000c0003070401c21800c12004076440901a011080703e01440e03803500c0b50b13401200e60344002d030000703440d10b403000044c0420003c002a01c0e01c10300c0311145400d00581c3e0307540076101181c0030468070030010071803030101600017400d840e0040030100d2107800d00250510200c107145250240420303400d86164011028010b295804018001d55076908940c180418040480043c04400f11845402543e860154804844a000b074058403c0444098143d504a4503032540003406480c01540e040f082d8003644d00f49280e60000d44003202e040e641c0080364280303402c0040d400900140f034000c00640400c003081c840868401040c20081c0000c6000d80b00440d225220801040407200d80500b0244507400d900148407000c0d20044180e07084584034002c0903032940c2c1c603404c00300440c0c898a2000c0920900d04100801081641100b40d544100707103a0350404c1145052200d0102d1000e226030140104102808520001e08692108250180302404030b8002900a00c000c00440d0003644840400342d8000c440b581601c80 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 118071861 1250 118070611 118070621
    0x301061502031b1609020c150c0706060504150509041401020c15130b0f1503010c110114060307140402070b0a0204150e0d14031209061906050303032802130306 70
    0x7820000d0442844c010303040b201c0c08042403081c11480354001c200030f80c0744d0a00703001200c2c04680300f5040403041d1030041400401584a60001c90300c0078030b0200b0218483c105407091044101214118945640c2000200852840001d00880d000c841c0e080100e5480305081c0091314440c104400100413a039024050441c0c8101c00400e0001d04440321161030012416010b0703401e0300040401c00008440e114550302d22488446a52445d8056080034450349109520000c120f100c0d0340e521000b0011084141400e820700c5034299801645a84108410312001e46140b45503802d03004000c00051401100740d030360302c10700e00048422504290f4007107410880e000156110a0840e50949010618589148c00040420450200103800025004550800b440c0100704442944170151044040d42c94584074040d900d0800f10b03083d00c01d049000380031070241c586038007800e42a2900140a0340c00d46e500c008500c41c202551502240310380744c00b605114843e0842c5d00c024070080351034081c44808581141000301c2956 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 118073111 1250 118071861 118071907
    0x90109050105090d030f110106060206070801170a11030102070b0901090302120f0f07030504080303040c050f0301020412060b06040e0103030c02100509061603050d060909060c091d06030106150203 86
    0x2508003c01c495aa0300c400889613980c2d40760426607440c20012008032200d006079041859250702c2c010340803844a4000940c14811101691590040da0700c483c4a031411a0201d010b45129901c4454903000041b1000b1142e404180b005d40010705202c4640c603a044800401d8410303c449941d207004007000d2560510a2540c292926007210f40383c0007402080161038801c45451040344000868140c04040c4108200c1d00180081000c507038480c202401d160319011964403902e4402c09086070416110b08060003620200c0b806035a0542c0f60b0822501d41d1000703040d840186e030340d01c00300410000ca0660b01c040d2603d40a58065035501d080c508851050021110780380740442d0038031009204000710340d5502c004803002405410300b03a510128444c642a25075010760380601e010a42004804103418509601c030840490142030700788003848078400d0507221079041340a50680b80d08072080e02200c9920200c0e81303641111002c0c000192540d1742d001c8000d0110100400c580058000080c0860745405031103811040c0c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 118074361 1250 118073111 118073117
    0x314010c02060103060c170c180a05060a05030612010507020d0305131e02010207080105070c050c060f071707080415030e0105010807061409060c030a17061302030a0b0d0501020901090501 82
    0x2600c000181d03544005100c01000c16483c0c811745c580540c8513072554040d01c1c1d110340500542d4103100540506036000301e030300003039510f56000340b48540b072600e0804042106c03809040985415400c440481d003943c40100300c40c1d000560361b070108050034024452284510710590291030261502c41006003941e401910324054001000b404102017140b000340c90215248184080d400303081c180c070050307003015140d0340014015460502080540c54001d02241d03c028810816105072241c17200401c900f07030280703c144511102b418044840000c40c03c062074151402c0300d9240d1030a05010b65502c01c0c0c02c0c0e02075080154140b02c050706003180b250301400ba50420480c1000240000d40c1040016607980115114084c1001134141c14506080c2100045030442e250203800e13540e4031b41c24170a04c290780341c1c4030b1000c40001860442d840209041e1012480d030161400078058603000140520440294002500c8400c985903101000d07071075170b5240d900074500244540c0001d81c40300d400c0000503200030300d141d00141c14 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 118075611 1250 118074361 118074371
    0x4020918030f0705011803020610050316050f011101020c070f1d06010f0e0d0803010f08030c060406110c160503061302011b060b090702010213090b030a02010311130e01031401 77
    0x514000c015030b40315529030701d01c0701e03103907041400c0c02d90141c01c0c2a05012000030002460760180369000c00e44a12480d400000802015a00c00a055403401300c6020a07a0a403212001809145011091400040030502d070240481803050081404c90740711b0414240240d000c81020003120110321a1180101140c1d8030f5034031400309820a80700c005d14000d008030304110325150194400b81c0150814141d00c3c1380034080381440c00c058078010b07080390310070301911101e0b0071020300004a4200c00412100080c001d600a0034081d02d455848801500b22500c0030700703104805201e10320480c0300070000191014604031140f003409280c4000c2c1400d100018100107804a02e010344200076036040720b154414414000c10f5018038206c0f5052030300003813212182c9654010210300c10b100c5041d90540240181e0044e04103801e0314555685035840840e0300b505036113034041d00005c00d07030800340d0300950000e142c0d40009203505140035040d5245d0810b064803030b0060a40f2002c04801842846104005a580101c10304000c000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 118076861 1250 118075611 118075651
    0x1050f01050a0e0103060b0d06030b0907081e01020d0c03050a0e0706020d080c0405030a15050a05010302091338160c0807050102040302060310081b1e010323040209 72
    0x1d84282000c42060100380c28103c03405901c26840100181503200c0b40c21303114680c002030100500900d11041c1c5030280c641c000b28a03e5000400d0810482c0d000b440117007820b00e45110710308520f25417480d100d540b9550a10000013036140700c1c050302d105c40046e80d80001e42c0d440c0100650302212040d010100302540304420a0264680000b1481d000610f18100102c1640c1e0340a1950360520450304655090f005036503604042042045c03428035824480071003409541c4c2c440803140700b01d079024440070307500c03d100c04041484c400404c007007484490f01802072005201c10b2000d07030765008114090007070300212030210103c144460a505250f0041c2ca640d078450400008210010240c070140580134204030b00004610302040801d504440003551701801c1300781c0ba80b80001e160100b2044038070541c10355000d807005003002458040d40c541142900248a02c06010094001d00315942a0000442c10325554281401e410b410604c2c0d2403003500c2116001081070b242c6031050040c0c0480c040d2111508020840342d0203 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 118078111 1250 118076861 118076867
    0x1e14070311010302130f0902280503270a0507051302030f0a0b0d060614040509060403021b01020109050f010207030f0c0302030913270606080a021c0f0506010e07030501050f01 77
    0x100c1d1910382441e000d0380b583c0d8000c541c0303028140702e0b0b880240002c6c2c3c414000100e0f0840c0350050140c001c0005e401104030102034500c2c43d800d100102c18200059030400000c0d460000e090341d1521408182800012003130032030442c0d5403a0902c5104103a41e2039000000800040c80c103c00a007480c802405815401c6082203004103804100240c054400c071900d8002005150312034050340d001180e007242050003044d41c2c4211040e40060703030003c5207020381e080c0000145050b5000407401d0082d82c0c503900405812071521110141c180084000700c2c1107540b05c0c4ad540c4007103a0304010b001c004101c000001643d410301d40c640606981c24a0101005001a00703003020302207900403050780c0c91000d00b43c030000802c10800d22440d0040208e015003100c000001d480904084c01400c2440303c00c144035617000c002c400d44811125948405500d0007c1d481a0011000344880d0610b00400c00d00700c0c441d5403006005049a5503980c00d00000b40c000c80d2000e0514401c01c0101d5525005440c01000242c035004000c0601400003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 118079361 1250 118078111 118078133
    0xf090b21070201020c1c020319050d0b010503040f02040906020c0106090209030d0f171512010b1e0a140a05041103070e01050a05030a0b010c05070801020418051302011202071e140703 80
    0x48441b1400741c140d00d5400c03500a004492140740030210004495050000140c5035410a2040e1050369103004460400e40d401041142d000341e4004010080e071030b0180d4200001b804540030101c0700990244241d20750410240a55800b80803500c1000d070700c4000e118240340c941210150b1f284208150802c0102d1560b0700f060441105260707800c0c120855560302c00074941d94846220005030480607212201c50352181c1035002100c00b003801c80701c154895584018101c5102e00c000c2c0b80581c46001e4403020000c0844805d461001c41e50054100400e0f2540c910016007142d020314030700c40d52100000100640c20b58811a810309050013420018100300700310038000c1031030100410b0944120741c0c1e00f81c1441140e00811105410b15805000c449a490711174829500ac1e400911649030503014810032455a51a240550361081c00c40d032001c0c2a80004d02d400440b50cc40d540c1d6120070010b582008800d012410030b07640418285410f04000300e00c60190709d02841d000d1401d074401c021617000000107000242d01000c103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 118080611 1250 118079361 118079383
    0xc110303040f06050f040e130210031b0f030902040612021305190207030309020316080d020c0d02040924051801140609070e0409110102070510050403030f090b21070201020c 76
    0xf261540c080d51407041d506d114036040400c51340306000801c405070781601e1001c14030b18030a0700e07890b4200740301038016070540d403603800d203450f100400c9001070500600c220806102d1503403074030b07000c980310b03019030042411122203070400d40441208000440650414199220035050030071400c220707a252207180804042103039100508803503000240d140030305209800038030000d80c00505a07080103091369200ca240a84a10038039a0070301a115007003150900102d110b50f00607a002c4c080ca01d990300d961b42008000e040d05c440490f02c0304404500c0024881060308014600040340c400002ca505000c00345010f0050a80604040781c3c0c1000406040041c0c10f005280e00a201a1014440307a2903003803080d11021034416850f50000d1418070207106001c030410944801110a07002e68017010b469200b0321101489414420f000f06004200400009110322000c0c40b040d00719142802c05240c5840c0d121243d41d1108882d00b060084090801a00800b07094071a600701c41a40004c43c6091414402943c8070640d04007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 118081861 1250 118080611 118080617
    0x603020d060905090f1908070b090102130f140d02010e0d2108010e060a0302010c080a030617010203090610140d1407061e0206010b0d09030c0204020a0c110303040f06 73
    0x104801280c031560010005001144014042d07450884101960346002d0841d1030083d125a1a4800446541004a103200c50308143d215250110359191540e060001400204e105c3d9420441441c9010500b070007074000e003141c00d060410f00e03841c1250074200d00e005c1d0840c09104869041074080184c6e040007500b40310389802e0b543d03002101101d0805a450110301000320302904c85500c0000700c42c80d80111003078140c510148800d006600c5180a0082c038061384d000007408a00b03900204804618014090403001c45a490081229038032101c00621001c81e03420000703000e0f03401100713115600b070040c032500c2e45c4a19900707031044c8901e24045011001120390188280520b44071b5401105008160303520300e15100d01c0e4011a0501c59580308028a40c3c504400300141110803598800701300c501c0072a056040300c01e42c0748900c0c00d0003003413071094004100c951011001c0c41400c045030801619640086d00006150f501c0e1954485020300f00070208598000415200350410071080c021441e4101c01041a0f80e698a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 118083111 1250 118081861 118081867
    0x3030e010c08130e0a09030c14120403060c2d03150b0c0a0317040203060402010f05120c09120a0c140d05030403061d032127030712090f060302 63
    0x1005881c403200881001c1c181c2600003400301400c1e031030502d610044811103896540d165803000e1036101228100c2c02e0080c001800401c0ca000400c03800400003009400403020780d21140c2e002c04070341d2050360003036004070f42c141c0d1a45241540160082d03402400a060710300743c019100d5814145540b246050a6601c003131541c0c9042100301400e41040610242c2205540e030365a558000c40b203240c0c0ca8180750402c50000d61505101c940c0d05520b840c1d0140502d074040c0080425498550040d503e0819200ca5101049024801d4850009565041e540500603440c0300c0c0750784203400000d108140d20031081c2802594812000e400c001007441d5480c80071210810b90340006002d0110004c2d14614800030003420074800030801000f40095179200c42235110024100d40c01d1840d8076800e0781e40b039000320519030b890101d01d8070702640c1e070101300b490040c0d00c03144100703d940c4501c0e6007a1080d241000407010040c83c1340e1012604e44c0400c00f03400c003e0070b149415403c1a00d045072400342c440d103100a80303009507000c041d004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 118084361 1250 118083111 118083137
    0xb040b19090c0e0607050a1103071404051801050f04110a0501021f150b19030b092413090b0a020304050303011a07060203150405060609130e0307140d09060201150303 73
    0x51100c9400c0f50784020543d596640309820b10682d19462900140d5010400c211880340520f40010110121340c0c880710f050100003180401c1000804000b400300600d0b038410102c000c6071000a00c1018803500c421100c8028605050400d040c0e40010703514001c0c001e00e200c20303080c40f00b45c0e0002141c840403a40c001007542a02028880320001e007144400100301d1615003a030100350410715802804a903400c010440c4034078a2540d1040307040c3c0e107494011729040549103010809000c42408850400070000c40290b400b039a5070700114003400e9140e00400c41c6181c0c0c900d030980070003005022f82500240405425400d6051946880ba240d200600c41c0402c0300a11040d2940c241410605546015070008021900c0385402c0b5059044401820f40e2280305500d8072001890500d02074080d950320640150840307007550005120000101000c40d00140144418408100091150f034a5640b4900b00000903103080c0a2490014003440f06503041b40c1309590521030a0a400c80311416075200322034041c07a00c018400e0b45 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 118085611 1250 118084361 118084367
    0x60304050c090108100e011a042f0d0b060c07050108100e150108090708120a0309021009030b070c05060f130b010b0306030706020307080304020603100f090b040b19090c 74
    0x45914540144000000107415013010030705d03510200d022141800340026007040c4900302c401d002d02e010715011041182c13400500745940140740c2d41044040c030551702c04140c6043c402c0b1034039550720915541c200140c8080c1e85010790044601e06c0038283c507260b00b02808503c010362a54105e0007103d041105450000d4075100b44c1c0e5000c180149030845c4200c9150510613204410201000885408030300c081e03020510a100002d07030780003143d00100281c900845010880002d0b80c0c00b11046104060322040144056a80d0b0080e14510f42d096840d18018a0f1031898003440541c0014062014088502098000b140c00402c4c0c03180c0c08551a11800d4150355176111000d4a6042c102c2c02500340b01c1141c0c004618200d507100154000d28003202120407240d034600080341c0d02c0c4203001c0e00a014031002c0c004900141824000b0315003200f400919200280c1c0c43c0c03050010451083c0d845001125150700b01e868040c1842d10880300707160000d035550f000b410800801106210100d1280400b075a6071090b40c0c29080744 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 118086861 1250 118085611 118085623
    0x9050904140a0f050a0606051f050901090512010b0103050f25050d05070c0c08030c100b01021e06060a0510170402010e120f1b0109091104150c0b06010206090a0206030405 75
    0x35015100e00c0f050700007400d115541d4030044104035900351900001191519101c0308142c12030b498984080146110a441200d1540240101364180080b00c1e6000c106a52524008006078481000008017190700b0800101a10f0001d04400c081d80d90040034040b90300c14040710a00302c290f035500300031707964001c0b000210389a00c00d003000c044040c0c3c904000d03c00015845400420800d008401b041e40d91038480c14646e84a2040034004455984055002d048480a81c5c00040e2501c1c81401552245601c0b91000261b01450000f42c0c07010f9044001000350078078000e0403c0380544000c0d102601d40041c01c0a01401d580300d00c000c41c4c041140782c800081c00b107a120340d0419072008400750041880c0c11000c004540c0e242220281c01c00203000d680f80c003d50402c26031400210a02050399950740c0c4034604902d0200174091411000300ca014100408100381e69040356a801c18201540c80740c41c00c0c01207081c80758001a02074100e03030441d00140140040c9840008003060007940440e5020b03a251075500c2c25500d020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 118088111 1250 118086861 118086863
    0x6041e05060301120c0806060105070b10080109030206090d03060605040b1c2f0304020325030b160f0807021b040207021302030906100608040b0403121e0c09050904140a 74
    0x200c4000008500354484d0703950803020700d00c6185690380240d265252681c6030b1204641181c002141800f60f00c0114040300c0c0040d401c01540500c0ca003103a41c407540b003d4207503a8040384c1640540c2c0440d05201800c542040749040440b91843e0404c100c03418400010110721651003100c1500101203050050314081e552110b000010101e0108500c21500303c90034002440b4030343c0c154181c68200070703200b4040910300840c0e00c03940d4010003802c018412808207003d800016000842600e560f468040009160440014043c0c85c25490300507a200100200502c02b000c0ca42c988020030020340d05200c1c0c841e0300007a05840802c14000443d944407150000714009005071600650700c282150901e01c02031840b54000d40c00703031004070292201c2c1c0da00c04c41d5a0300da4114601c103000009800c1d00008021403215813003550024840d2900c20b0204014100070000e03281340030501a0790380b200780c4120072a45400d00c1010304285175810300c1402e0910349800a180b078000280040d10f2a904201c0700d0720344003c00e21440c0001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 118089361 1250 118088111 118088119
    0x1050d0b0316090b010e0901030f080a0215090c09060402071101030506030309151206180a020f0720030f120f0d09050a060509060c04080d180506040e0f130206041e05 73
    0x31a584810050251004160f1300740440c9481041006a00b411b0154506881c0c010b080302949034001d58031408076a00c581040c0085000700c000301c1c1c50320b0794240401d5001e00720705001049210161020895841d01c0508524071507803041042d14000389502d030f44036102200908000400e035641e200420708522512500c5a480030f404001031100c425503034040c1c4000c3d40684404a0156944420721003107007440f541d80300c5240c01d194009030741304c16142c009115006603c52606c0c20400f80d9a5442d078560444846c088a03018001d003080501c1c00c080260303020100040d0300400d611101147c0800f8540300c0d101c4410440a000a000b20f034160150700704c600d1180e032007030482e1400c2c516410154000c05c41601c400c2414098074002c50f0b03148000700700380c0b802c1c2d5034500050700414052043c00d0f6095445200c2803580d8180d14100000c0c00c0d65011301500c02404e0003000c244103450852200c02203108000d08070b01c0c82c4001a603441000d6210310701540c040e031300d0b419080c0c84070140e01e0003100c0301c0c0c0307046500c42030b44 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 118090611 1250 118089361 118089403
    0xd0201021e0105010807052202030402220212071b08030603030c0316050f0a031d0a052206080610030f060212010609150905130f0905010906020903061501050d0b03 72
    0x403001c015800b25048600080540d0390302c503102d10800451040041403002240d07080110955010038640c02960002e100070009282d412881e2080c00c10303e41c111445080300f40c3e0120341c4035022105034261681c8080240307000e15000c0f0810001e81040c83c107104014200010100010310503440401c100c0d064180284201c0e80c958448000e81070400e2070000d401c460600441031901100c04001507070540180c0e01d92695020380590414444001d4441100300fa0f120707000042c00105522148620b041e5280b0841d103070406220f02d000d03a201550788652000a666010a042010101980c8100c40a0313981c0140809c0b54a46642043d201034043c00c203080000700b402c81d0000541c0340c0c111502c08102c929100c0c110754540c034801c100740e400068520800c3d130002c01c0ca50074850040301c40c1d440300c0704900310740e40c000400d030300162074044c02c603000ca0900700c613070385d278001202d00c080e01d810410385900000401d40790018603802c40c0001c081707020750b16801c043d494a5070400107050340e003031054100c01d820302030070f20306 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 118091861 1250 118090611 118090663
    0x207020409060509101407080603100f02090406140603160507170a20070b130803040e0f0108070614160f0606090506040e19020d1b030309050402030f04020d020102 72
    0x420b0180c428220a20403051511a128a1401807180c80351b24100c0d4007003190b40d20f5205581c26440200400e50500400040f01a00f1540d84601a0981801e400041c1c0b036027030080500040b510560000f50f265801e002c0001c400fa0f80718401c882c0d10841d0042d02040070b1144032010344160091000041003244480501c40c4001c081402400e00b003012652603c21411803c3c40080b49000404091185508140c000f80035043c5a00010128240090744e21301c080c540e1480000d00356000303a00051141c040e081c0c14400e5007030182840c4e038094111040a400440c1c0351040141045400781a0880c031000702192a41100019a448408058000c003c44c0f115110714030f403800c002c0485006007140107280801050581c14140701e08100c8041c03010003040000c5030b0125262815006900032030f40540d00051000001e80e001d51071201e0020b2a0b08142c030802e09500d80907061700e4113a0802ca00482c4144104000e10844044060300b164040d80c1000e2204102d0004074200000780326290304485003494005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 118093111 1250 118091861 118091873
    0x21207020c010e06090d0b040201051927060c2d050f0609060108070522060f03060608010903090b0903070905090f0c03060c041701020d0c050c01140c041202040207020409 75
    0x70000150036650199a000301c0340410106008803808150400c10036a52000003485402c8107070f402030700504200d802c1c00b00d10551b5114400950920100199400b9400e00c150341d400c0304e000305030b1010004105c113400d0034020000d00030321400d100076180780d103200307221040301601c0c0110200504da032802480a650450800070795400003101500c007039105240015072403003000300e0300f076060b103038810040d2402503d004200302c04090788000c4c10300c40041000710801c1186c0c0740d1250500511150b20494105403071800c0c588103c5540d903210503c0c5905001d034450001c3c4d0f200515170b0a54080010258803040d080700401e1400225400c403030250351400c41401540c440c0041e40d030715801e4480b01200c45900000080c561100000c0d280c1000d580b10605c070601690500180041a90407000c0c0018104002c241042d411b49a507010440c02140c000600248030405c203000c2e07a8a03c450034404055541445017400d81d080c400c910640c2c810051007403814046540300d4044901e1580c0091081c0840c1846080031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 118094361 1250 118093111 118093123
    0xc17070e010c03050403151d01141f0909050607080106021b01030f2c010f06051c0f080406090303110105060d031b02060304150e1b09041104090606210f06020d02120702 74
    0x400d88441d88000f4200c0d514014042c002b01040c04e1448103a9076110180f000b40880800c003010607040035414030102d616003e81c0308103002203009d90010001030400307150150000d60180c004d07070300710b40008102d42e9400000341524111402c5c00c0c030b000914055014500d40080c821260044080d07410441f00d069044034041785070400402e081c0080200002c2c642c000800c840c061301c40d498100c4410700826108554103102d1440c41790045503c05480c4050b6034541140742e205c0d80245012420540701842410b42c0a900359500e030481d50001c00242c10480d000502d0340000d910014104031083e00d1086e1040300d12807c001809601524198480c2007500d4140090780c0f001380c003503007032a1400302c0400d40450000f550070207009000c2d0303990808104560620001d1400148140d425030140d03012110280c07114070550400d10b00034440029080d080c012048901440e0903941031040d051042600c000c200c2c491282651544c0c000c80041e13aa01c0c11181a2000c1d000e0000c003c8003554507034040043c131603008580 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 118095611 1250 118094361 118094381
    0x7091806031514040807020303040f081005010f03030c02091801110d05060a0f030618080d05040302010e0d05040915050303041206050c040e06040902010e0406090c17070e010c0305040315 82
    0x19214007040b008005022101c90000e040c204603000c20100340454501030042242500107001d0740d20b0a40c0300c481150380b0351020b501c60f29044d0f01c00c142005c00040a0b100d440c2c0500b41d0202010304031482d60f03e000f080a860614040d10840c010000302c0d540780c0340760a10048244229000340700b1403803401000c201303c1e000031901007001810030002940d07506e041610801a5a02d18031034600c00c60640d15120b0085c4603903108400c000c00120103941c086440c00b00504458a000800071402c3e1420f440c001f802d440320101c0300b01c180d80c4001144102c498000c8242c40685101100000e95070704203031565180800a0740c00305402d40000500810200840ba000e8000d031030081401740f0458440d029055814071691098600341585903005c51224a03081c0c0140515600501d0315540d40605180007034100e40b40c0d41d0008420301e6480482c00300f4650051010044143c1c000c201011601d4a003001510b031042245540f81040b5001b84c4103810075000c1c000740c801039500f240882c0000c920f03c00c800c2c0001c10342806 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 118096861 1250 118095611 118095623
    0xa2003071e0c061b140a030f0603060e01290613120303051803040303021b03030702120705040b0414040b0405120c0303011a07020a06050904020705030c03030718060f05030709180603 80
    0x12a1340ca50344182c0906545410703155200e844016000e0304400300c03a080245175404050701e8022981c08500c0c14040e03500554040c0100045403001041054210740c170103112174071107070019400d00c180d400d495030301c1d08402502990403030741d0303085c1c082a090741480300c681001600540f058800f10a059242e48010310910b000c00010901c41b42140c005136903405a4800240103900014248407502c652101040110402508403814403000750300007400d070031003000c410f4609d80c4088002c200c41d140c9800359a5000320180d404010501030704a401d600100c2c02403010303207200e100c80086020403d041007003050b02610320103056110300800c1400e680b2a40b0a00c242096007070200e0b4070081110042041307401541e8000c3c070b40c80a1924110040d100307600004005680907500303009800110700c00740002d001407030021014650304d151011001e008001c400401c400c001141034414042e0980080070304503880c2c4542480790700d9540300c4400315424695900903403900e00856000e40103039100c642002050f24490744c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 118098111 1250 118096861 118096871
    0x190509130201110708030301060c03030e06180c0f0a050f010203040b0d09050606010e21030408010e0106030203060121112725050a03050c0c0a030906080a2003071e0c06 74
    0x520590784d81c90860158030010740041004220a40c0a903255425082c441c0c1404200844581340d914206401105c0e158500c40305642e4400e01c0c8a001c1c4900504003104540f0740c00104d041030045400007941c1c2c000d582c02560725803a510b40503802002501c008002d04500641c0d10304010358428050400003104a03414415180410410340c082c1c203407040c4180025120000c1e00024040301c094110205020005c0d500007000301041650081c00f032010280500000800c203185144145482e01405a00101d00100c19000d8000d1280d00e4280d141c6040360007002048510700c085c03000030f12840750030f1780040543c1c000d214103508601c1c81803656489201080c80340d031007088004040002c240c5101c6100c1000034410428500c125000b0352206401040c2502618200807030307811514a02200e20005802040701c00700c0400900e680b09104680c4201f420b04180b0144034440300030401380c0520554030b62010408400510302c1c03880341d5910041d05000e46075483c0781089111014081d0f544d00201030300d04a00345 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 118099361 1250 118098111 118098137
    0x70c050307140d02010905060f0c0709050103020d02060703120f0e01180203031b0a1208101d0604090303020d0f06090b0607050d1808010c05040f0e0f06190509130201 73
    0x32034104110b95200b04007082074648201009681d41c0c440c0c8089050060b040404202a221500035010a102101c2902d07a510500c220301d038074011240d84840340b010b042000600c0140c0b21a241d01c0710803a03054501e69180c4a4628040e9180000d50466504145c9001c0103200011000d0b080340468180c050020444103111407e061600e15280300041d4042d4070421154001040455549080d41501c100f615a40b030003e0340c2e009050012011400c0007d1002030500ca22108032074860300081410904045840d42014510012041c0c010412480780307070f4480d03c1d641418066011034942c0011100301b080101580b402050081400d809000d07000b5103031100d80700d200c0c14110201c0342c0c3c068200d002050131400d8000c00301e5404102c5407003240e84600894000070707003400034016041c540e20b654590944480c1002c08800711500b60b80c0c4000c038000058004d0242c9020344090ba0f80e0088400e030b5200c010902e44030000e00c1c545e041e80e4441900701201504100c5007052b100b11600002d4401d980d080741074010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 118100611 1250 118099361 118099363
    0x9011406060a052b091104052404020c060901051e010303090605030a0e1504150209060306040c020313150e0a140103050705040513020304170a140d0b100c02010810060e01030b040e03070305070c0503 87
    0xb044274660100d00b444840d000ea50392010b4401214510028000340c50600c080d68900d0400380300b602c100c515a034581c818030040b4011001c01c500f240301101c0c4e9148480d07156483c010700e5482103116550034041f001003c07406068030b50304900703845071044003181d80702d2180d0424048070f0070b000c4400b40c921110701e1030020302d0761602d07000f02d4000e190018400d60554441030b0801000b00b4810640406602c010040104000401d00f150001401d02d40c0e01c2c0c8850a0800c034001c2c116201144031035100d80d151710014002c031032070f40e009401400d00030300e000100c1e5907850f1400d542d44d201d1500981c0e0302c05c01603051107040550b00e8009503c01d42c4280e03840103000b10000552021402030403101c4c0d01003041154850f10304060000501031400c0410000300d4013008510201d00c031002046d032000d001680c1d0030218019942c0100409400c00b8860301c02e001e017286001030040088142c103442c9810580c4450005446940e82e40200e80614040810740b41c0c2c55080745030240140c0c1c01640110b80c0c940540700d0003e80751038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 118101861 1250 118100611 118100621
    0x3090c0a050f0f0409020a08030414010507120c020f060318100213060c0f0828080105031c021507180605040b03010902091206090609011406060a052b091104 69
    0x7005030000746070380103400400996810074281550800d1340c561292016a0f1081e50000003015254050750340c1d141004040414034542c0c50000e814005c040042400040b0200000d501c035140a141c0010300725450702c000b69480000c848801da00c900084184a982c9803180d41d0700a00020642c11034084d00c0101c0341c02c3c0f0580c00b8103414052031910b080740070410507002d140a540f200d0311030115511402c090340d561040c9a00020804012a0814040c003110745504010035040d01c13401d41400d032040c1d85458002a03444030386460001c442600840b40840e01402000006d801d002448080ea849107820f85009280440d03044010200f4101c2c0400090264002d1040340d054541183c00704c0d2950b0b00f044c5808010358400200e0a0308014503101112400303d00740f0403940100c418002510304c6050a071081401e540e00300805400303151010013070194596507072044508800103410b20079224000c46440302808220010340e94007100300c05241030144a00c5030b100120b80761041200704080e07100c800521041710 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 118103111 1250 118101861 118101869
    0xa02010c02150c0c0708010204060305010f32010c050708010b0307150f0c08040b0a02011409010c0903020d06090c030b07030f0b060904270b1006020c01050d090c030b010303020303090c0a 82
    0x3030342100400c00c2c1e46140d20080091804c12400c440d101030359003a0312822a44103501540010356074100500018100d10b0790070740203240c0128400d00702e0031b807594030807007002c030710210410074803010341c14060700b079005a21001e400c580010a89801d2991404410f000e4500703e40b1543c0710f8090000c01080182525184d10b00000090b50b5519180e99100c0003510040424241903854400920001600d116031b0130052603003001540c00820520391264500d0102074000e0903a079203e904000c091074015501030002d90071030390100d9254800e80c0b07913030520300000d01240d00301901900f98a1000302c1440184252a070007060301d03503001c100d4a18861000c41c12541e024188540c0042c0c01c0113000b640c2d10b800d0301f083d00f0900c100d003080044030722804085c9088a50001080720440c01450800050300384102c03250300100400d0020380320f04806203000a10500c00c0744000e8040b41d03602c0304024140b0245000c02009158411007002203540c490070080d5983d00200c0d910b600c43e101f40c2040301c1050401481540c101c0e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 118104361 1250 118103111 118103143
    0xf0504020316030b130903030f1b1403100801060f080c010e090408030a1104061116050a060c06060801090807020405070906020d030e15040f022b02061615020a02010c02 74
    0x914a10300080b005052a071404d0396114000051030400304d80184a2150324511a850004032020005845d00950301c104400c5070b03006401c00511302d0a15000a070300c1c5614010115596580c6d9243d0140003908802c03031b00003c140e0741c81c1983c007040a030300300c5104200f0754038018112011b0402000044420280c2e01d480103030048881008240010501c8001e50740164004401080128840c52509180d0708150f001000245038060343c804004030610500e024000707001000c14030383c0c0c02c00d0045440b100d185d11642c810000c0e02c004001c1846070603404200940780c200000e200d861002d0a002e4480d42084a0a0340f28602e02404140783c14043c000103002c41d02d154015207240c181c03d0106500a050100c403c0399580640306514110428418546204a20403070750790111100c18014008542400030f0f41080c98010804c032040308441c50644071000a41c1256031a94410758450008103d00c1c24080040400ba0032851120140d600381d000340880e044268001c1001491104049a540013150500d00032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 118105611 1250 118104361 118104391
    0x1506030309010c2f180f180a060e0c040f0509060402060c0114090d0201110408060103060b0d20100306051e2412060406060f08060301061206060f05040203 68
    0x507a50040b502003401e1406826120210040028082c111342500c0c41991020f403680e8424072450300d402e285d444900c07504040240294508082c102081160140c0049148000400c010344199010042c070241e05070b01080602401a0242d00c4903541c84001c0500c8c0c0c4151708000446c015055948981032161080400030101c9494035020f01495602050456556548491441c20000094180d00d801070031007100900042845000003400c4034580204c0341452842000700308400e040014809054030f800c407500149041d100e02c00199190000d050082000c403c0c0200c08851b2040c8101150359941c0c00c1e203156003100c5230800300710121341c22402010b0340329401058032084024004a40f4065440142801c035240342d94184039002d403401c2c1c56010214140c0059007040008008400b0350b00540107440c10711813507041c01c0016007651203c00c124420450b1602c0090026070f400d40050f030007007180d600c0a6a80d102e050501101070b1038a401070300c816054030000082c60781480c0c800c50b8402c022920341c0c815 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 118106861 1250 118105611 118105627
    0x61501020303042d0311190309062d030b0307060206100605130306060e0a0c0c1205030405010b06180301061d0c070f17030f060a0303080118060b07030f0215060303 72
    0x5001e0784080346441102c84c0c0035130038001d11071042d00c034807a986010351103021101034072880d514545082a4980d2013900c206921180000c1e8014903003005072003803800c01001e80d01900110f80840c3c6004041c122418110001c0b00c4100c1d0307056840b4146180040d0166003081d620b840040e603032600d05803484a00d031800440100001c1e03110f14041c0c107080102c118641810f90341c90300c412041e44d0494000c1111802c6150a120710f0740c09038820807001d90346c1401c2400908071961100c6041407a081020020300c800040007404021080d40001e00306a0010109600d4842c141042160f404100d940d280c080c1d0720305500400c20b180f4a540b400c0300e001001d83d20f080c1d0b640d500d41d50724001c0e82040b4021980300520660400000e00d03480d40504200304409031080c0c90b858a080120f84000002e00010300440c031001c0d051000c01d500c80341190542d40740c18198a004110113251a008001581c848510b204000c40c100c0300b05644840703001d403403205036421102c1c0d0041c600d18141000c0c1050319850392692003005080b03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 118108111 1250 118106861 118106873
    0x807110d0e03070806070305010f17070608060103020702030a0c15021c050901120207150506060a0f0e1c0503210c041406041805102c090a1205030105010206150102030304 75
    0x403001c1600601070724001941e40321001d15041c1e060311084042504c0742c0040c46580700940207400141042c03c542403c1b401031030f0a903600c5400c14041c010400c071750f600005440c0d90103601140c0034660301404648140240b030620407034400440c06150100600d068102ca54544002400031550800d0381c842503080c0c83d0044282c2d215406003021606100102550a0309a2a14800b50101c81d0003280600842c00340b210070041110002045240f00b00000d100b05501540d00c021910f910418604001c942190703c1d01c00103202040d924440c401c2642d80c4c010300380c108000407010784104461214841071018403841a60a0030f603040341e0546034990140002c00480c2000c0740d01184000c0003400851410b901d03014030210301980b443c45a0045502d42c400c1c030091044c0f0100c0c0000170907502241411001404034406d008110f007a80350700780703100b50348007140c5041c9090050800701548082c400d0721440200310080e1154100740310b0b46000d401540c00288811070078007400178401005034055851607445d65240 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 118109361 1250 118108111 118108127
    0x30c021504030c0c062304150810050d0f0515010e0c0304030311042309010b0f0d23040308060d0c0e09010605101107122607050d030b010807110d 64
    0x160104010390500d10b01190840c16039002512140c1d071004404401954a00c481c8204046d11002800742017008101c180e12131150840714404500d842406a11905243c90186000b074200e241d0000038110700008000342406a010303824421002c2c0c80902c41020004032004009200e0194005c445400284190800a0042d54040d2003810000f82c4c01044640100d041d82143d0001501c01c1c03459060030100542580c81c01c0d0040408542035041c640c104000c90704d450140c13003e0701546100200b401044074156410030b181000a00c401c2030115110b1200c68081d0880c06d45054000c190702802103401030404140003c130a80d081205d00c220146080c201c591a10700041482840d55617614002c10075580303420369107460103040c0c2e80300c3d0000e42d01c13803c02c1e41c00d00641d580840c0241c9100b80c2000001408440d080d501500c11825604802c02c105c0e601c0c5000c0e00c10502c006013a0700480c0c200045998160380058810f010aa0b00c0c050300d80d891a50030365041100e402c0186403507004d07400d18002130f4810455 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 118110611 1250 118109361 118109363
    0xb04060e3c0411030f0115060309080f12061f050304020909010e07170708010b031b0102161211010516060e070807080114070525020a051f030507030c021504 69
    0x59034016816005401a41c01400e840840d4034042200a4108a00d02001619400002e600080142d4103580d407040e03801405520401e0140b6131030320001c0c803c2c02403020654134507000e554121f907074403447e182100c0300c00c1504030b85041c81002c40518dc07035042d540b1b98202003405035242c0ca49a15589036034080124541000301607541c603648903101e00300c2101c400d000d150020602041c0c81001100e401c0f55082c00c081c02500300d1045d0740e141c0001013107180c6d000101e0f50141003405034948001481c03580100e0820003114104100c070600d1003c000f40d100181c07201042c003540101105101c040348440111247d00c0b402a4541c7c403101c007034003c0400328450340d1101c01c02c07018003802c45445e20758901245090000756030055915035500c84500156122070b0501030790126851034046e16108903040d0304c07040714070307100000107020201c00603250454480701c08400103054001c1441341045c1c0c0d49190790100e400a0135034100040e00308000302e14144d02a0280b00003c1c00190040c02680d54440b981088160300180 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 118111861 1250 118110611 118110691
    0x50c01030b040b0d030c0507060212030103060c200c0f040212040605091011040e0601050306010519200d090e01080c0609030c091609080d090b070212100b04060e 71
    0x644901c3d6590b07840740c0c01038454030a8442c070b4081030050030107034100140383d40010155000340e140c5502d58400601101d06403035202c4400558800140012100041e07520341d604100b0300842140018800c1c00a0203801e101c008681513140f482a075401e01c010b90242c1c25403403100e515404046000a00d42e600001d80c0210303058100c4920107800380d02002501c101d1a001c680c1684002010312051207450031140c0e100f4800c2c20181e2460600c00d00080040c0b0503100e1203001314030180c80821142d441660603c50003020700c90a600804c82961905403a266403120b4400454040e280c00150100c0c0080003074100d60406000d04007105480d0300380900c941c010504954940901400000141d030741e000ba850280d01d50184560300c000ca400409826441d030342e04610403540c001104041903e50111420080d60b0007413417070503100d118520104080c0c4020140503d043e001d04403146840c204294860307040c400b42120240310480c1d54690340c0140e01c6094801440c8100d10141544918050804030600e84001d00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 118113111 1250 118111861 118111871
    0x14030c0c0a0209010909021801030206071b0315020415020a030519020307170301030201080a050c0703320d0f020c0715091809110405060a17101404060e0703050c01030b04 75
    0x1e800030f404072809812841480d0781d2403480c8025820881824902c4401c201c102c20000d506603000070700940501c1c000144035152000780c5018074600c840380c91000b5503024034501501d049084841c0d019400c41d0299520038038001701d1481c41c2501c00180000e41e250583c0702c161901c0d102c54144069920904800019884100301500004500c0d40c49240c4840c1110a41c030b483c1d505501c0010031102d0080c011046603424102407140030f4602d003088401c9154582001122050b0008200201044880080c100c200314600c094410480c0ca400801140d01c55501c20001c1c0030000c1c00e107100700d00550300084141d42c40300c1000c2c040385818000c444010007140c02c2901d01d06966551143c4081c2c1641c400d0f06071591a40107107010401600c20722900c500c030450341480f5a14011000c9000c0c24018440c0c54001c009001000003500703024407029101e0307a4170000902ca102c0c2100c41e00c2400140c261012500340c3d1910038805204807002c22118103495210000d840301d282054011405401c0c001d10080d4050b40e62 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 118114361 1250 118113111 118113113
    0xa05060f0c0307080403060e1f021c090b0406051810020c010b220c0c2103110703030e0705030a0302120c070512150604020c0a06090807020a081c14030c0c0a 69
    0x80000c0c3c41158482d03209150b07282d003546061000d50f4030080002c2c02950041d12166441e2403c440c42c01e464544031080140c03540c002c0550700054110006500c144246805010b0003803140c80991540310318041c16090065444919130b03200c844c50091440d001981000405415110035500245010011031303001280040342c007000034003041d040b44100500c040c028903424280d01c00724043c04217408614240302001c807446072156022001c20408420288c43e2441103070920301d0181e03200b8601c0050001e21251a03c40515003e00209011003c0c810144502080001c0521780040c0c9108521382c035601500d884c0766010f020b5500d68128540040c0c440c001c1480224498403101c1509a240c180c0c24018504d002421610420500000e485540240e004029880d0300340c00001d11210201d621604c000307845034503420320704041d000310b0900a5101c111f821000464050018420070a1003480d01c410310b207000d000d041910603005503941c69038002428800a402d1a0380c24018003100104042a0b40400181e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 118115611 1250 118114361 118114363
    0x20409120f020607050f040315090602040b0a080f0709030f0f02030312010510020f12090402040305030301060e0910061707020f0136110d02060d020c0a110d020a05060f0c 75
    0xc00100300003607041c00a94a40e66041000c01e81003400b604006203450700510102c8807a1045000c064105c2c001701c0c1a8440d500000ea002d0058a608480115151a21040202010b40c09000d03200006225000400c000160307500d1000d00039240d40d107070640711a07d140d1f510720078020320b8001566424180c0480c200941c80910003406171241f2a074507004075606180030000c010303503060190405c561010341031944160b00001e40d000d03031110de01c54258440304000006000383c8283d4100401c0d80c00040700008100d900590b1403400c0880c1180c10090079900c0310800c0c03403600783c18808c442c00106098240201c10b03c00709100d03a04910a44155102000486006429201c0c04100850a884a0558a44000c002100140d0101a841c10604501041d40c544841034140f800500e482002e102c0031650456071050b003151050091a8410340d100c100e0058020f84a1080c0b010a8035488124410500c0c6407528280409900d58000c00078a119802d00040c0429504031401280c1c2c5460200329268030460 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 118116861 1250 118115611 118115633
    0xc27070c080a080a05150315060d06020403060b150708070807060e010203040b1005190b0a171513050903071203020405040e060117060609040602070303091a240d02010c020409 77
    0x2e20348851695052000004044a034000c20700001965203034050115a83d01184c2c800b0003120180ba19403040d00d6441c0042c809190442c0020611440001c0000400105400c00514484203c48036160312045902001c0301c0d11035104024408001000b0010000741064081e003589030041c03100040c140c0c40704d08643e089a10503541a40e102900303c04000c0c0d602880030b121700181c1030aa61040e0700c9460600e0403a0288514051203480120104010110b140300c3c0c210000d90b0780d9101882402800c0202c0d91047c10702401841d14006c02d0541d0710094106464080c40303019885c840c0096152800310786070b00c10003140c901003071f00805400700f1000503035941d140103109e01d01c404400030307140707035450102908144404082250040e42001302040700c41d907204403a00358000d400c184096669240c9160440042218400041000481c00010f075000e03281d251905110b1261104400745c6542c01000d020a01090701c4030707081d07100c05015400d00041d4070a200701128a44040c1020a0740450f0756500003040d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 118118111 1250 118116861 118116877
    0x8090a0b070b0901110406031d0706050c070605040b070f030e0a06020c03060921070501060f06030209040b03010b060901030f0207050318131a063105030c27070c08 72
    0x40c0300425a001805242440140c0003410a4020000740104401c0c1400c0c0e4001c520039001031544ea4155001d040e20840d6507241e00c054440300b42c804490302e0300c6026000c4d40101c030300880244600c001c045a00ca0068040b01c090b00e0101440c941003412607500c00011883e40c00d01181002000c9600c00002d40b10344044401070b0000303030080c0920000d41310605180c000000c11041c001c0c0c4c400100740881910004400420304c2041d0b6100c2e586601605002d80505681e5104030140103440d00b0014206500da8050711480c1812903040c4170000e01981011700ba01e100a0001d54440003c0203007805a60007a030010001e01001000076040c20000e866050540c0c00040480300d0440400b07a009480d4a410319801104503800d070303c10084d07803c0ca50441c000907003803100c4d0607005060000c0c004100f850440c07000c241407005d192085510401d0712038440c00c91911352241a010303200707107518100e040c9045e10490240c08500d00c03041c02510000c4901c002c60b41005480c10051005055815011035103020007800c502c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 118119361 1250 118118111 118118129
    0x11b0207060318020d02040b01050f070c181b03050a0b04090804090b090c180f100c02031002090906040903090e1e0109050c1c0b0303070c080d0c050d030908090a 71
    0x20316205018042d83e814840da0f20039503018002d20001681d554001e0342c0f1594042d2000134902c01c1250050701c25215501c1c50848804d0081081c07810000e40c01060401e42d2560203546054030010383c19541a03a216000d02200203250b04901035210b44650310181e80090704800101f25407103d88042400c80f070b140a420b4503e035038006410b021384a114007400c0030310700b02691110420318040005000741e001d10601807014000d6104590f40035620120f4000304a070f030040841039240032188000e8012070004034100d000c1e0150b90211030307080280b0f03c02d5511005003d002d1a000780d0b200000c100c020044c4140032018000941c9010805000000c0380c40d10400b1a428103441c000f01110f05100905c00503407202903010f003040c082155000c511030a5940700503400d400030340d14844840e54039010306030100e02103406101c042081424040070020308422a0f94410035a0700b070740b003909012280c00c9200b040141840c3c1c85038125910f1644030364445903032035000d59040c1c1d06007100b04000a4154045a2103407600c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 118120611 1250 118119361 118119373
    0x724020a05040f05190e0a0b121c0f090512100e0a060b0301020315061c0e030706181707050f030a0e0f010305010513090c03050114010f060908060117011b02 69
    0x83c4030070000088043c100440c1c001c050f0780100c400c80e41c0d1040440c0501030b00314040c68003140000c0c069030040c00348554010010007401030041e4410b90f507989800a0900d440d08500c004904150046c4d6000408410380d640d0019200d00f8030080c85121030180100400d10711500325600e01c007542a103e0303400500749500c040e181d1211b4506240303090b204440103842c40303644100103219103001e9003606c2802411094942c5c3d5180d00149042203110f2190b0040b81c2c1d0704500301004c2c05a4100084000c0481d18071031001045201a05481c3d0f19280391041002004c0e007112100030a000311404018018a52042c0c045a0070054030f0303020607007140c20414005010941410201402e45000f400070300328a0028038003042030358900000078840300440da2682d054903644c0c60550381480030030394114020f15000402807003910003c001c08046464240b04003008001c2103a0041601031261543c00126049000106074a900b0000740820707004030040f01a0340d035941c41480d23070b502c2040080501c0758444150082d20b8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 118121861 1250 118120611 118120619
    0x8010509060f190903020c04050f07091a030f041407031b0605031512030915030105041107050c2b050a14030903100f020f0309010204060f0e060724020a0504 69
    0x460010050881022003036210304210142900809105900c0c00512020444c400b03142821303800c0505000c50107400c07a060408000003080e840400707034000c2d8599540d1108003035407040f802c18105094007402300e1010081000c5080b80b42068442600300703000700303001090420002c9142d40750900d1540200c65003d1440ca100321180c00c2d60707d400300113003554107000303145280c003201100d03e2010035900c84c2d1040402019503541c40700100282e40c3d1783d08020b04a411000040d00c81c40c00f5507003003446600e10942c00d285c19110324500c0c500a80d65029400001408914458020403166a06180b85d803000a6052500418050011038520303150728050b1020b49403036507480c20522022000da400760245a0700412072010f4039180064588070880c103040c4002884100d042d194070191244079031101d0b6000020003400407500043d4000d10440d811500c1e801221044820140c40c011000020154801d0050220300b0218061005040d031485890b2140c804090010301c0c540c0c1280c02a1002d04001440410184 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 118123111 1250 118121861 118121863
    0x70908070320010e031c03020f040605030a150e0a05091c03020901090f2105030f070302160504051b030403030b090a06050103061706011a040f0b0901020c0a03080406030218090108010509 82
    0x91400b000a1800302084038011001c02c1d5100c04000d4145d800507480c58030104058400e5040da60f81c000c4060342a42e40b00c0e0395000c0104260030503280032141520b0241e076072920b6034448000004172284c10341031101030741e520124400203060081c0513074183d019828101c902c0d40c051615900f001166500c0058075900308034001402c8503510b070032030748903250604400d00c0940c510f081009030b4042c0300210402d184440349000d43c11030041c2d9580074422a00402c3c41d0040640200303401b0064003d4500c0b01c040e19a0320030070441603900940707558402039040c20039900c45401803001503a11074081d0401040104012000c1840c540003201c1d2441650f540d40c4040c8295a498010540101400d0000d2000d14000f110790030f0b03c80e401841a100641c407130301c4103401d0070540c2800340c1c0e005101c4510b64a0310301c0da940d49410921f0388622030050050296500d00000d520307103101c052060300d400c0f14010381800d040c854280c000b5400200c0d00c003000128030801c40b107190794090301c0340d01801301d0000108032410881401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 118124361 1250 118123111 118123163
    0x1101020c0703060204031b050102030414030f0109050a05120a050301090f0b090c0409060605030903120402010c0f061b050c12030a060b0d020705010b01110606010804031b050f060c040315050709080703 88
    0x14010608041c07d04000c581e900000344c8050707075030301c40c0369800100403075000a10340004020603414550904915809000c000704d10241c6144c00750050301c9480c1511801002688501c00300390740401c2041c00188002d541503131109220410003d03000810500c0240000c02400c0210303411281c03400c0c005000d05c02c030a024002d890081030305050141c01c50900b0620b042d1a0301030700c4c4000d90f110086030005415607200d02d481c50901508003a1840c0c00d92010304002c009008a49400d244012071a4003500d01c591055045980b100070300703405070100c0c040300c001c201c01e0b56001504081540b502e600c00801c504d0641801003501e03900d1403034016070310003092815609413540301d14071505120100356902007a110110b920365100100740707440d05481e900c0349002c2d00d000300300c41803d801c5508080c200d10104140000c00702d41e0503411000303c40040d980d001030051588100e001c003d001908107001144010015003107250031000904201401d20780780c410407071524015500940c0c0c0b0b44042c0b40324400ba041800c0f60 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 118125611 1250 118124361 118124393
    0xe121b0a0f12080d1404030f0206010509010312080c0d02040803040e090304030b0a05090109080d020c010b090c0d150302040e0607080f0606070803040204110315030601090903020d1101020c070306020403 89
    0x38082210300e0103103095102d0b103a200c4090b000e010001507a48038a030403903001c0380c035080658010050a042c94100200349902c3c048103100941320f000000302d52460702c41c42450490f50b0000010701c03040721004040394010005410040159014441c0c2826201180040c00c0907204080045031a140782485c1800401c0c00036042d00495042000244003140072106a258419a01c403008a1903444025031540100b584c08030103808440c020643c448014040e4009100103410100203000008010040001700316054407001405e6400b0848540301030000d81000100000030406a20f11560703a401090503924140304c04243d41c0c0002d0200b00150360041d640d250000102e41d0184d1261401e6004144903106030000508891400f00000c2c085580380e07000600c04a19a4000545900b00000d540881c0a401030400703129008801c00403807010f00c00c0c0f040c2181590150b000780071044003c0d400307840004540c500c4441c3c2d55001c00c01d4000c03000b020490040114811040141d890345981403000c9084801e140c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 118126861 1250 118125611 118125629
    0x912120f0b03120705100f020304060e010b060d1a0303030a09120e03030a080a02070f11010207060c021813060501030c06090510121d0a050d02010c0206160e121b0a 72
    0x11404a641c500050503d805401d002c0e580e40d5451807410400c3c6072030440e50f40c68601a0070440076012403001a00518050b609c5010103010900c800d5020600f601e6104c055281c11250034003195010030440d82003d89840542c420000b50724181c4000b0a0450f4411220000c5040d10380304008200b010030052804800c00358a4000800c040b4400042e4480c0725001443c420030a50720080b40702102140e04030b41d4160380c024000c14114100d07151002c4100c48004a190160080c05070000b83c4a00450510240940c018400c0055440719440805468000360915003418408410400010394074400c0034040c40c05044800304031868044000c100c101c260700003034001c0707003500b1011101c1c2e1341203907100c000d003031401e14046401e403d00d68030f10811542e200b0341d000c01071264a1001c07090141c041004c11091481d40d000b4010a81c041800340d903116000ea40450410741d803007600e01410340c4225490140c20380020b008041c0803a80300101071401c0303100481c50420340f4103c48401e038039113401c103d582c0061210b24 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 118128111 1250 118126861 118126871
    0xc0403061d0d090e04020625050a031e08130f050d0e03071406030708180a060b03010f05010b030f060d0b16080615040e0a060b04060906030e06060f040f0912120f 71
    0xd084e0052503c00540001e024881c0854840321100c80e24140b0300c01010b41d51800d0040c0703206410305035605e00114000b80c0c04078a508034001e208000000c8080c24880c4281c030f50700596215400c203400c07180454042a9451110520352600099040c0020351a036030403503031544040398010003098201711242e4442521f40031685200c1010391142025a0b40c404800d09003500b041e80c508140000d1026003c2e82458580a1039a55004011030fa0b4420022004240d000300105801c0e040000200c130028082d0158040080c8006481d00c4074120081c3d41c002e40c003a107034980c0100c1d203503180740c6a4842584d03a140c004205040b118a45940843c080d0ba01c20401c40d0340e5990780f840c0506500d07440c425401001d4001e6040c00002c1e04001c0c05800174001030a6002e030130307640d441d50b81c08014000720560050200007800c00409940070800080c5107800381c1c034020280354104014400700b000600c1c4c2c04003e1005c580d118429440031904c1200009a441c8050312005035400084444004561300c1042034035481d4582 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 118129361 1250 118128111 118128119
    0x152802150601031d060c1c0e070302100306050607060203060108250e150c0f1c0f1b021801081014010501200706020106090b0409030c08030c0403061d0d09 68
    0x3880300da641141c800c0c240002d401048181c07141880500400b581c04900c80c16052044004094008200702c4006074602c411000d82c401100090700c88403000c1c01e805922802007070001d40f130b000054464268207030800181c0d56603603001144c2103420010054442d00d901108000d081d58110081c0c1d0750105612200c0a07001c0d148448010701041280145010080c000816080c0e075140c0f1903001d10240c003450b6201d611440c0210041395120307001e2250290324003484140841881c0746161b10000c2d04d55940b601c644850707072403404440145031640c000b400c0b0a16140c0400258491004c105401c054803480c0300c5066044c107504c2e41c40c00013010f60040803240360003134101d01040c4001d4224151102407810010442401d2200c0c13010003480303600c102e8039000c4e10100107426a0158409412200f020300c040c8141980c00041008941030480040c0100d580301c501c01001504c4003006560001000c401035003066241c0d12000101e036074000320f80e2055401c550700345a07502000c12600c1c0e0000d9562070025103680c10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 118130611 1250 118129361 118129393
    0x8010506090a0f060b03100501020f030705120a09090e0a12050909040609020111060a06030c1203080604091e030c1b27020d110a0908010501050a030809152802 70
    0x1005000c1c0750510f40e07079002e4601d841c06030340290740208803030160303e034490510410108802010340b1810f4050302c209050304c0c4d8452004801e456403180c002024107902000542c0422551340300a0340082084910380c408a42c1001c18840d406086800c10000c16403840c00340303486400280202d00c0a0144031090141804995420354502e0703019910100100d00c03004184016a00014801e00c10711150141c10104907107004654080d400710307405272030104503d90345c070070301c4052500103441e0140004100100003811400c00782c00c048586440307044851710003240e02001c030900000840d000c400040400124800340216805a0040320480e080e03152207903450031001c8030340c1c4401184000b4120760301403822400030007503038113841d00e40084850500900201c2c42c0d03010301542c030070f05548000ca40f811902203040c1405200e4541618805010301248904540f18401c0d1500704407500d55115501491400843c091440034024002c010006145030840c440a040408620046241c0031503200b4502d01130801c113 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 118131861 1250 118130611 118130629
    0xc03060a0303030b0a1a030403090b0a0806090702070e0916151e0504030b070c051902091305032205010f0507050601122111070519150908120a0908010506 68
    0x15143c107000035049211404165910b00a601105182481e940000c1c1904040340055110b00d10a40e11040c8003900e4401c0003009010b83c2c1c01c45400241098001600c505100c0704140e00081140100e40c00565212240c51105500700c484a803140c10941c005140d20010041c200050030500d0394010901d40100300c0140b0b03196100c0c0c60001d0b480d410901442402d170080307044038051a0046904a0302e40781581015060030b43c0c4101c11121071095a020b4406030040740718102c0343d81c1d0300500c44403a035158192580c40f100017450083e0f03007d0100700304c0305403081b071818442c00c00f11080172060a1a145480d0000d420002080b0b07c050038090300300a180002000803821905541c4e4241c03000c0700109880c100001c4041c400b502d001e005a20040d42c00700210380007140781941011a000700c6003490303116400d00008641c0d42c410544452003a040c148101203104d4840d96078031005180031395485590300c080929004407444407484211000034000300c0075038001c48600c050208840240020300780070000c508999 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 118133111 1250 118131861 118131863
    0x1d0a03050a0507080c0703110904020d0b0603030d06091a03060c0927040f0b0105030a0f1e1a0402040f05010605090f010302040801020a120518030a0c030c1208040501050c03060a03 79
    0x820001000041c1a001c0d405503000c0301d4000c280c0f16102d003a4011074943c2d402c1c5c5400b0079100c45551075566a036500d00340c0c0d0124861540034100e002e011700596504240c5030005010b865141c0001c0c4403070a42e100e114480c1400070181c84a000c158117109010350ba41110a484c4000d02940141c01000b64041002e802c442130a03009417203181c2e00311071071401c6400c103030010b202c400781c140b0300310080c0410312120040440c02140166140c2a13aa40d0725010560b03500c004440090564414644240c08101202c8611042028480d2001ba4508050341c400c9009600204603649000c4550144400c0d4100f42c070030b082d0903200c101000c0016506200c4040c100703018000000d4481c5030800c40d05410f6900c80c0d01550020300c0c105001f9900c3c0c01110802404e91450044030300902e5142500141c00d031602200d02c0020214154081d501c2c021050b901142c120820348070076400c3c4081c840c0e21786c0000e01b03c0703003840c48600d28950b123000e03181c149860100c0c00c1d51070191555143c2041030080c003101d941d90713101d10012a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 118134361 1250 118133111 118133117
    0x2102010506090f04020a090204090203090d020f19080706110706050603070e06060309070f090c0e030c100c050304080d0503040318060504090e0c030105070306060f020105010324021e0d1d0a03 84
    0x41e50f136440000c070030240b69003240d41e4850001c40c00150350310141d009103000c4c0400000303a480d09503040d44200e9a801200002c0d20080d4010a191000391864145410609006401d501e1078040f40d80c8500c000d9035501d00e0355107281d103800608902130201910036590020303005c4024048041c60300904ca02d80780d901a00981c0716a400201140d0b2052003001003400900d00f5141410312503555008240040c8824001c2c5408515003000545103031401048040d01c58a005002510b21075141e0011a40140b001500310340b244030070000030407641d804021400040075107986e1030f9074a24252500504000314180c4400d580c5249141c1405240e80040c1560160f03485650000750080041c01d80d549005110030507030b9059480c0000780300b05250700d0b030054002c2d1012501c40381c50700026050100c0c00ca50b000d20015100610060900902904c21000080190305250001d0f003801c460a280c4121209511500c074000400001d10403101809400ba10400781204a103107080c0404000e101919040641001020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 118135611 1250 118134361 118134391
    0xd03060b030105120c191805011802070f060501030b0a1a01091a072910080d050a03020405032a040608150702070305030706200910121107210201050609 67
    0x80745005c000c0030341651401800e02c03011000114215035441c40740d0141c140c0c00c044002e84001c8a20b19806128126481b41105070782d910944802d503402174003c11800c83d43d4071141401140804d02034000c1a0103503015030000307039041c2440528002154815000080601c030021020685130781c010b50504200e681d40c41d002007800c0050544030f18a8840c2c008014407840303045d1644c01d0704900030b1508074080311580055440d0340d11050340315101d0701e640c0d00c40d441c100d03801405441600e5208030094100c41000d401c0141c1825280c10020b03090884004080381440040b4a513501d10300d03040440000031030020786041000604280409449115110b2110252110000421011882040310ba0003c40d044403d50361a4901d51030084084e000c43c1111f8480b1b400c6a1000c00107290341c01048440810005084068511000703005031030040d4460116109070f566040312000300900d4038024034205110f0100390312680303001e07981c50f03c490415824410031603160204000c0d1540b102a0f070290841c034100f906d80c5c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 118136861 1250 118135611 118135639
    0x150304060f020d1a090a06050904080901022805010c050a0c1b05060a08090601050102070501050403020108091507020d021203100e0c0702061201031a0c03011403121204050d03060b030105 82
    0x6803081c140200c124070300c1c000075542c0c04d000c2d07608640c1d00d507901141c40c03400035150146244159003040c011700d5440110702000c1000620101e005004410f0180113641e60120385406144206102da0891800401c507180a8010410280b00d0700103442040c1c00c1c0682089503d600007000d036982150010100b40c3c405007040c0c09964159400d4009010040000e42d44111801006280c00010341c4d030440c56105103400420650b00114402d0156041a92514203061554004541e0300c180603000480c90b000c1e41c1e400b940c0203203020304a544102c80e550006e0250350f641180091800c2c0c0d41c0c090140c0c1d960b00510a20150303400740000d8034207c4010500b5814507440d1000d0b214124822004001c4d07118070001909545c12000031090f6040f00d0141d20301c00e41e2941c002181400454040f00c0680c0c47c404100011b200001214910001c05070015048a41c440018400501c16500200007003088012450070001003020802c962001d219185c94103204a81c40c00c00211704600042c00742034841c170550440303a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 118138111 1250 118136861 118136891
    0xa030605030303010801021314090c0a120e030913021309230f04110402030405120c0106081906050112050a030e0f040f0603030806010e030601050904080412060c0e15030406 76
    0x1001400340282582c0c0e8a503500c2065500030b502044040000302c400b400001810000518152101e00380940211020781d1428900b80c03060344140b1140c41404262420148010f0891003003000301400440119500d00240003081113180b064641c549a1034010040e03800341080a0b882001111400c81003c00d806404100107003590b2a036414001c0b6031024182003000c00c82d1100c40341c84c040c0b401083c0c4018a89071800503c02130744011074001c0d120380d02c04110403800a08000080402d0f01410000080e0ba80d00c4200c0641006464010801c10051078150a001d01c0543d210349801005018024420170701c8a5440300d46940007504042e05120b01c800c804005900c03801c40000210100400400499010388146070040c41d59000540004011000150f81c40d4090340c40083e00000080080000ea0f19040800a860b10000c1c400c5548003070a00c03000481d0b541c803410111000e4071601001c9412000ca1500419010030021070320306c10315028000310110700074941281e410079002100491641400c00e090 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 118139361 1250 118138111 118138121
    0xa0201020717030115050a0e0904020f040c0e1201050601090605030c0405090403051305271b0a08010618060c0303020d060f08010e0c090402151e07121b05120a03 71
    0x40d18580410765070141c085142e030001c60603208242e184001075289103501310742c11b000b8062084049041f4181401c09480c10300700c1070740d115200400c0224251910b00215040c1c0746a5074a0f80c0109140268001a40ca0001610740d0380300d00a1000300300d01d107880b400003403160100c0e204800a0004c0000850000b011550440d000703414041c0000415050900c0d000302254080b42100c20342242030701c400301d0181b91001c4411141d40454184103556402c04052540340321024110820004c004d804130401103907a0070140803c07002c42d03101c98403d03616020001d401020301c0c1050310528942c02800740155900514480e01c0365425180050b111000f6181e0360f0700901c1c642d00641801c0216010003e041641504030500070200320090340d00850303c08090100709074044d240294400070329140514080c4400c0b0181400905050030b0259010022039202001da000354004e6a0b50383c0c0014940100b150050255000f03001c0e81c03100b020703490960b0745a05440e119015000c00280b400010b4a141c3c003840380d008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 118140611 1250 118139361 118139363
    0xc0201120b04230711061f12210905030a060218130c0e1507060209030a0b010e04060b01020a0c030318080609010b0301060605162301050709030203120403170a02010207 74
    0x420021100c600083d0484150365038040c00007121100e0000b00710714414900040c0e441c03840c07401840c042e02c40c5e01000034007403140031202604c1e800000d00001c2c51001090000c1107580240342d040c001345103540f03580320f400d00003000003018021b041c00104510348000070208515900100016110700040c0c4981d000d1980d035034075040e4000041e200b4a10102225406220328884540342c040450030a08248440794004101c1c950260b0028005000418079a400402d54850020f0a98401c0c00f02c81e5200240b52100b0313086488c00454032001c21080000c1c40c0f2070540840d109000514500d1025996040250b40501000f400c21a03800e090380d0300240320700503240103032000701c0590f01145041e00b0034034020000c92640c00d220358285480021410f01400807688084080b1200d01c0b1218a991214a241e4100100c00455041100000e0141c0602032060a000c0c00e0141d94842c00189036004041c90311000c030445c4501c0c918104405c10001d01e00c1c0b0450300d1001c2060016a03140d03802610241d00a0203501340c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 118141861 1250 118140611 118140619
    0x131e111903050406090b09060f09010b010c0b07020f0709020c06060901050904020d020619110111040e0123040908090f040b0319050a08131e1809050705060c07060306090c0c0201120b 80
    0xa00403447c501080307181c8214001d010703409540ea43c600761740d4240d412003201c89002c074100c241e1045c041042d495101d40e02110070b00440b0940030303020a2141c9042e0150340a071074400d60219030042480030900013a81c10440481d65000d82d94101700009807240c40c007030002481480e800c01408119200c54059030100b0402ea803a41c0760045444c5000781041c10549200801540303440706c4043c45240706015102a5550340c850016181c1c08e00c010141030b110513190b066090310600c3d000864a50300c90003511803d900c01e58038680c42c2c5c901a010b000440b00ea851180380b0030390130144406007544000507404003107284209010f69205c00e82c200b00d41171102800780034000010000381100c020200e58040c030111040b840182e810303d4507240c1c231848558154004c60214840203070300b41d000c0c00710f16008504001d01807070a403000c2c15a51030000e0540e5015020312101d0350041081004000d405210b0700004221000007400040135a020050032542c1c80d00000341403207000d20240c0010900c5500850074548064 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 118143111 1250 118141861 118141883
    0x907050f0d140706050405030c04021e070f02030a12080f07021b010504090612050f010203070507020f22050709050f1003021308060403020a12020a0f11131e11190305040609 76
    0x21200603d550b00c2405a54042d02c100c4e03880360628100f03442144c48cc00c004e10005442d204000a5550f43c580c4034a50a4031503c0f00803405070701581d424045440740c60f2107180084100b504140000c0c0c1440c4008008060340464202040001e50300401e4040506076146800314910002c90016101801542c202d44442403030881e0204600401d144114138107070003001102c0c00380f000310180900f40d220485141c0300040090202e1001810700364a999210303240200b201460610320045442c400810b03004c00b2080396241c0d024000d099410140010141405441ca03030000034200020410100034845501d0401d540094442401d05410151102500c4030001344d460900386030800030340e107100012080c0c540c82a10014294541c1c00040c92800707040d80a0380c050000074194a07094420400303564a186c110104280740c1c0d220001521940580b03003020600d501c0115034804110041300c80500001c64407410401580c0e0180081e940383c41c50800140c6400700c0c0c0b940d41e500d0044054400382c10014202d076116 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 118144361 1250 118143111 118143119
    0x9050a09060608030307050403060f0e010510061107030b0c03061903080a030605060301051804031404060908070b27040603020d0303020a0e090610110102131206050907050f0d1407 79
    0xd80010103854007900c02448019154140c490b204c0c4000c1e5011004141e013000f08000240082d000a00d0000c540305000076400c003140009070039200200c03100300710441d54007014000c0b00d80107a08002c0e10b015440080c28203034110354130824100070180032801c110342c01200113801c4e55101190100040c0e01034590740100c0b5504d2030400c14540080443c00c02103800c1c0580440d9905080007601d040f00d0005000800c406203403e45c1c1c411324030026206804100c3c071100f803460a0b403040d50041c80204440c1e03580c0c0220303900e0024924280348164000c403413020410000e02c4481d000303004280d440e50b40035182c09140740c112480014002e004c2a030009400c8492004103c040c903415174054024942d4548806207503c001a00300a40108119410380e4842000541d0042c8540324034001400880c000f4001445d1011094021110100750303403100581201d2407640104100190003000c0d0400320300c400401d422400c20001440d25010350000c00d0284802002400c2440501c0001055404400040d2058039840b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 118145611 1250 118144361 118144381
    0x30a080f12010603090f02040e210405011101020a0804020108070e090c12070306050102120a030e1603021e09071101021207020c190e0a2c0102131e050111070905 71
    0x44071940914590200003e4080e010380644011658461041110b51000e81d003007100522100a10902610401c500841e0600000c2c841944014000400d5901ca61901000501d40c505640300d0604507401400f0740007200341c00c00c04c0d140d081582405d040340980d4408100f103a03c91178403a5080c1c0d00c0314100d000c1c002c0140000d00106510842d001c0c840c00725030b0302c0c2c4400390141c0d1803600c00c0d18010380c8014204a09074244902030915413885207000700e41c0c640185109403030005200081c0a0308000c5000030411440c043c424130b4500d03610110500169609a80002c4c65214000c02140a1044410001c3d084240a5048944c185170721104400b503030406110013076441c0f4504d00c03928001c8691036049d4100480000140044420180d0058041d070b6980e0010000340444000942603010100804110300c0c4482c0e0420402c02046400142c0b120440d0600506082959000040c1c0603101e4841d42c0e02e5824080196090361801e00740300d07201101940503103160541036884900b01c80e1400303050104c2010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 118146861 1250 118145611 118145617
    0x30c0607030603030f020f06160e0a15020c181315090b070905010201021206041a090403030c03050a0903020c01031a1203030603100213060e0a211a060609040902030a080f 75
    0x1020303070b0318021851101700b4143e80d5840052070014542d8483d400050251800440b9138004041919180a00030710307400100303051350480d4110141c0006c0320395003083c0c0164100000c01c8040012946410240f0440c2140312090200fd00b1000c00313103042c10000400d006d03100c2e034840044110040704021440450914050904082d6030440000e0055900000c20398414000d452604090b004200780c10340785c1c81d0400005012400304402c64403840103804100d40d54548551340b00702c7c040e4070045800104d842005088400c004d1105160910708050000400d50020301e43c4146c00c401c1c00d00154a911040141e0351030020700880c1e99226074006000200c0743c1c008000346001e03c1040e4102c031542150f20041200780e0186c92400c4001c40070b421020001c481c494a01d0790540c4e07101a0001450644070b00201030641100c1408481c0143c0c40852a4200110000100c41030130310005500344034149800000c0041c482e00da50740303115a440742c440005554041c0040043c282d1300c115880c0c0d88000354444001550 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 118148111 1250 118146861 118146863
    0x6050c030408070b090c0a180c0f02070909020f0603010e07080105030d08040303090312020c03041d22061b03090302100c0f050702060c0607020d110a0201020a060906020d090c140618040c02030c0607030603 90
    0x180c1481281010140201803000410030250042c00d421400c00d850f10700100321005064364040d00c902040807284d03c1c1c4000a501805050341c840b543c40c43c1c030107005400c104069005500a41c451101000ca0641c0a0f40c1c0c50f07081545454081020407032400d0403200d101c1c8222207024101d100003810b00680c0c2e00000140110b514100f0800c0c01044040c10710601e0150071078180611000140c040c00e00310405030044842c0911500001458074412080450b80c2041c03e02c0c55808030340c0d40c91444041c9501000f1850001c2145407040c0440019000001c181ca03a100e154001840707004030743c8200310354030f170300c16211226400d500710f41341481c4c0303800025039070b5060641d000040b51032a1441c40100c500858800320380e40d010b800600c42c50001d0f0307590ba0024a0f01c4102642c1840e0f0a100e042d8001695000b180003290088002c1e0907002d0805001c24024081c2904080c4103c1d0200803440c140d24010800407425903048500162429215000f43c0c1948903030381307052499020745030400400c9901070380048103070f03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 118149361 1250 118148111 118148159
    0x70b06131b0f0c051009080c030403050601031a16050f1209070915030f0b150907020f0607032a0903020a0303080109110304082d040f0306050c030408070b090c0a 71
    0x310200c400f40e0f43d603950032030064402d420014651036649429040074034003d104052252824184001450450f00107410403244c81d0880300041003400400e50f0a0340c401c132746615980c0f0b07a90401412101850740e45810f120b0a0000114112043c2e40f10749003030321a501403401850070103182c56a403c1c1d4070f03a8940c0c00390002c0b8910307000000c11070700d50108440e01640d61091400c2030706c460603154044da0740c0009104020340e12003803140e0501a03c4510200c0d000b1070a41e0018140c940d09040c40c1800e0200041c40b0a08040c681042c21040803081000040d07034042060301050204045482250b0b62443c41c5c101a40200407941c00200b016808840740c0d040b0740481000700180c2c5060914180184002d560240043d01d045c0014915226807854491940d04408115919030300040c03884103040e00540d00444543c101c08404209015440c003590b9400180c3c00649440c0d440c0940d140e5001c2d0040c2e03d00642240300c10000282660b13400c108404201000600c48440180d50710140e0203030180084142000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 118150611 1250 118149361 118149377
    0xb0603010f060b1c0f020711090609100614120702030a1803030e0f030f070b070302010f0e0303281b1d0f042a08040b07020c06070b06131b 61
    0x240c1a014070a400590310031280300d0713180400d000b94078036142d0105040d03c0300a5585081da860104014401012407900c1400c8402c0040002010446d00301401402c2c14010322540040102100b80e00d170b0741005486141c10818000107104c90148001c0c010400880d4000b6019414407070010740000180017540902d55444200c216030701111109c0300803610005002c00da0040710f9034514582032581002e07009004c0d084641c2110b10224403032825545d584440503903200003d03d0700c141a4207014905003401040400c1c040440c0d0b500356550380f0701c80104400500700810905020160000561285041d042c400031710203045c10f20451039101c440c42c0c0900e40414195840031800e0394160440d50410b00000704007021000b010303400d000140c2340780b26041685d0340700214082242c50390b400c00802d24040b9555500c00c00e140a1170050b141400291400056620038841051180d030360307404072141140e110b144100c050b1500b2002c12824013400756a420801e080c0a80c070007115100d214004520290b5545c0d202d6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 118151861 1250 118150611 118150631
    0x12010f030c0f06050306060c15010905071709031b07080609030301061706240403060203131101020604050a0807030c0210121a03120703140d050103030305010504050708040303270b060301 82
    0x111031a07040c0f003407001086045c0006405498490301a068012458066861072568160082004074090f0040d2581a6a131011310085560081d003c0800d0307070805007042e070182003030380440b962401080501d140c000301180c59103d271813406200310720040004600b00c68a6082110403181c45c0c0c1c0090084000048040766140c2102800c42d4096019443c0584064442d20721480c004488010558941e0700c032402c00c1000000240c1e0510080d4403401d0211030341084910180b4114220950703c9510034115400700080c40302007940407920b0009183e1100f81660340e480c1b00d01c0c06884900d902a00a940003040103401145150001224400400103040420001096010b540c00c07a5a98440e515010b038410302540080031519001401e401d806070800d000031022012202e88140c1c8140f1343d40181e01c0e1920010010907800d8060240544421602842a8500f02d04010186d00000700003808054640185250030718100d401c40c0c05104080d8404000c0124600700b4001ca402d050310009c0c020b42ca4511455 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 118153111 1250 118151861 118151879
    0x303020301150504294305100504020312030a09060606030c0f140909011e06080c030408130302060d02090a0e010302060403120513030b0702010b0f0a0b0c010212010f030c 75
    0x40980c1c003441d6200b181302030340007028080940e92841c54200003d040014170311b0b080c103c00208241400d05000400c040152903a01c00b02040a200172001072604425060b0000c6c0000c680e00900c002000000102c590f6140002031818002c40240c501046c0d001042c088586902d400c08482c850142c01c0c140801c95460904134119200d014001000500301d00038034500e00e100d0354000d01c800840004c42c5051040c3c0340c0c0021b14070038080e4880d8181100300704140c40c4003018074021130010056800e082c0c1903850076620703e400078800203100070402c00c0002041840c100f001c984820285070003402d03444c2c03504c80091883c4025440103145c5031207425100e1001400c25090355915040c1da5024064606052030341d600c014890821031022800c1c481c0c18000300d12580124660803000394041c0b040300740142402c200c00b07402c45000125441c054105441b884003643c56109011080b00e02c008852a641c40d9280d000500a0040c2c2620b400c05c8014080001012080a220700054a004900680c00d26640e03246030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 118154361 1250 118153111 118153117
    0xe0a0b0f0d0b0106030c030603051915050c04090905160b0d06080c1e01170a021201090b0d0803220807020a0501170601180905040302150a0204030203030403150b0d03030203011505 79
    0x1802c0003120001400054407070703040308072005098140410710302d440323580d8181829154006203295088800106c1c3c02d0141e911440d66200320145010013941c100103804100a00c1240641c00c8107903200d660100c20018200100d041500700107460100864480d5520445a402030146851070b84c2040070118255034041900399200c40014035a01c0e4151800380407001c407003011611507051150341641e04040301000d8540c01e204a10940c0300598443c7c010b481c4070780260041c0c00c45000d0742e00e0214074140588a58103c0c040d02a04101c401f170b04c03595030206010000140f0307801880b8120140364407108000c40c1c40c0140c660140b01f11a9002d1207070301c41d801140d402070b00c0101c0e00d5004420b48041081d03940035207000d001c0c2d40d40000000b000151120140d2041e550141e07400c070010b9104900500c1040200d18029400995101c001e500d0189140c0000c1d68070b000300d00001e80440040f0344141d0010110390300036245408050203000c07420a007802c0103002074109114031000200c100000c911f4807407140c011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 118155611 1250 118154361 118154363
    0x2060a150518091504080c010c09032402041e03140606011d0402042c07110a030e030316030c05070e010b0a030902030a02040218030f0f06071101060e0a0b0f0d 70
    0x125081c200015658105550320140240d0103500841c00c00c00071075148640d03518400c500501b0701581d500510240325003110051000c00080125042e020710010b21a105207240180c040b642d2090002c90f6401c1c004020300c503a034000d04c500301d45080c1d041200b00700121104200e03405006803560241021000035241e500480c0c0160004680c508011a00c854030500414000c0300540010b08081d01c44081c84025140400c5407a200d1860780b213090803040701c41601540c0910a031408420721903559a40d07030341c0c62151020040500510040f240c0c0c2d00d44040054403c100107d819100381ca00e0325040c0178020030383c0014141c0d03560082d8a0041215902e141260f4100d528180015240c004100d9007140200f10203d002c81e45401401801405a603840c00036129088403580e4445026600c6020580380c80800c00144044c1c0d0000c03162007107460404181c0f260301001302d08000c2d10b000c090f10010b500500b510f4101e8062500350301c085c03181d0076a482d80302e11801c2c20241c0c1c0ca1030b035500b807400c00c02c41c03549403001d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 118156861 1250 118155611 118155619
    0xf0f230d03150f0302150904050f1501020703080904020d091e12020607020a08070206120405060114010c0f0b0603030d02120a0c050702090103021c020d0b040308130302150712050702060a1505 84
    0x41c0404c010b080243c1000300c1c40050380300d5181094406800038094510940b0394410312460402401402e0a00c945003640c103000c2400100807603842d5039a40403140c081c01039170522540d40490314410b1102c441d080715440e84c2c0e1048441140c2c0104c1da01202d02c043e80c904060341c429440c400c02c542000d000040c1c2d00e000300980d40040c418200359030340e01565503124400403038000d0700910180c04c540010f0602d90b40698821000340407a5818040c14201c074503001580c0720304110411940f5404184e4107400480c0301c1d6000343c0058415074800c40400e1542c800c084440b0801c500c005840302c60175a4200e0a1805100b690b6800e0000c5410103c0803606070043d100065071090030b4000400051030040303103511800c142200307042da140015400141002d40b01102c285d940b111400200810540c0c00305940b9400041c40124841002c120b440080d9285080300042544c0354900303001c580060300400400215114a01041c0f00345d241c0702d04029103c2c007081da07544000b9401c00c054030b418844550703209429184060 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 118158111 1250 118156861 118156889
    0x10e120708130e150f0d0b06040c020705130203090c0f01120c020f0d030204030203160806010612091202150901061404110f0406050406080604090f0f230d0315 70
    0x901c41e0301c403980c400580d034007040e0b8075402e0010304014416071403441815509240aa50388803401403103080791803c21446c0c8150180c00710740300080c10322001140c2104046d10b0010700f18096640c144e00c3e21a194000692000102030640380801d60354000b507100d24000c00544046c581d00005000c0140040d400180c0403a40200d12200c80700d03c0766000b21280b10407441164041d802000e0f4240c103085240d504d55000075000942881942000c01090810b4600e0001d2854694903100040740c071410180034031001c03c100094441203450b01d5810038031145402c9a01f0030802c01b82104003a558240b549290401580a280018460041071080d1011640000d440214203400c010800000300240c001801d00c222040c8500b0101c0d400890141001c1c2c00c079a11815551810600301403c8150010301142c4070341d0510502800162145080c1074a107640203940ea076941c042450a0a8580441c12071580c030046040c9526580c540f002030002d103404000d8400b0403011901a48502c2040260b01803c54200c00f90 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 118159361 1250 118158111 118158113
    0x907050a06120f060b0f0a020c0307080316080702180702190201080a0c020304090204090b0a12121b0b0907061805030c0d03260a0b040b03060f0c0d02030117010e1207 73
    0x1d600f000300100c0402c0d000003803540e2a16600d0307100350402d0110050006001c0f600000003501009203200b601402c134010580c40d860415055901d2081d240c81017654100010b42d60100a080780036078140135802803107025208190080d0f110f42c0001101d0150051192446040c40c014889071520701264060b5692601d56032201301c03032006000030b410301c0011840104400240f42c402e910260000e81401d0310041500c400610410515121681001c091042440d039045c7c0094440740d400c041d0100181008508441280801041c2d59030725080034040c0d1f11035200300442408041507090950b2400e450303170360400d50220220412540c4030b0058580550203055020110315114150104013880fa2603c001344038041c0f00c80c0c2c44d884a011200002510a44080c4014400b25014004042c1d0b001d580411041c10300360700099a50401810400c84a100c0f1030100710b5100c84c0104a038409007100406654070b50355070701c40001559801c0c2c0340a0b450351a007483c010404602080007078408044400007424074801d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 118160611 1250 118159361 118159397
    0xa080a0915051e090102030403021606020a1104090206120609010b0412061d15010510030c020c1003020c0a0c0e0c07080307030c02010902040504151409120d06080a0b0907050a06 78
    0xa001010041d0350303038602e0f01c0c140794a14102e034816140b0100260b120309082c540a490010039103012004880400c009100c100e6001621710600b5400042c40341d00c0c5607281c0040350041c124184069000440001d0003036009003c03481796805401c05031602c82d103a030782c0c0e000d06d20507602a0b4002e468595440c54141004109190014a50303110301114296840d00705040291402c41c07090813071445e031407a4000400c0103242c04641c501f08100710303050500001c082410025103c11048251902c07405160600800640c0720b0b03030540b041c1007001821103681100c2814691b0310203040d80b2070f40078184015800684181e080d00103480c104c0e07601131000b074115140da1400380c02902007441038004541d46c0340211005030b80c80c0c0c001c0502aa000c1c0b107241c05640c80710102c507400c2d00c5c10108a6442c85484400703020302c021002071084800300180e40403507200c00300750310b01c21b020b004580d00c40c07042841071031524406d00c02d00d40c4840d17010381c07107510440d0f941c5941d4100b400050f50080c4240408102d01c0c8800350040b41d5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 118161861 1250 118160611 118160621
    0x2e140d0b0301022a0106060e011209031e02011e09020307050904080702030a060603030f0c02100f02120c06070f09050108010605030903090306070206100504090809121002040801020a080a0915 84
    0x30060025044c1250700b010398100d0501c90013003036400f404200310450100404e10804001d04031914102c2c01c15007035400060a505180700c9d583c090345664502c0031003454031404c07003104400c5888084520080844c0e00003406008410703000c1800d0085402660603400710761094814441e4090041e0030400e24082c00c01c001e042d4010300075180c500e070401c50a00141d8051118040d40c40c81441e000944070304508000788440c045a003060b040c03289200c2c0d4440580d071600c0445005004918100080381178001003207041040c011000004008040795000c4458804201a0701c540300640d6036030440881c1303000444510000e4402d0502090319003005200481c859402181c1c441c88440481e4580410a400702e0714205089941d40010f811004c18810702510740040b09c0000c1400700c0c1d081c442c0030380c03070341b1010000e20a08002c1441039890000c6554201420700c44000c206024240454460340d6528030680130f9400442c5140004285100207080e503c1c0320b04c1190101508240ca50055654986071500105 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 118163111 1250 118161861 118161881
    0x1008100e07020a12030c0e0105090a090b04090606030b090c10120203040c1d040606050d02010e040c09081906060e090a0609110a0605070b0705160605152e140d 70
    0x4001c10f9030981c00719007100f00300b4030000440d9500080c001010700d00106155858842c550422070100300c1e20169584038841ca0060f40e550f910005051141e04ac001002010b10b0203000700014140b01c400024001744c07002c0030740b00340641c0742030f21010700e00b1008004c02004419010004103400c10200ca00d45901070303000e1640709104001500e0801d803141d115000703c10004103005244400c9804200410401d8002c10004140540341d6019020413a400a024184506180390281d41e44030f9004c0c4407980b08800583c001c003c144251100c80c120030307031540403500d00c0010903141c6034140b400c0000c0c0064402c46461050350488060107140d00f10313070386000160030070940513205020a11010040c0c0d543d071171030080051035680ca0721960703640180f80180900300010880380601070f051000742d001c49031190391202c000e94040e030009086d960b0403000c2c100906004203800c0d08140088484417011010603c0b0341c0c40c400841e01c50560b04055008100d400242c010712100b9240d900b0b100300c9001e6451070700725518031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 118164361 1250 118163111 118163113
    0x22020303040306110c070b04080304030602130e01030309060806010512010512120307030f0608030c03030c0c0709020316020c0316091a03010f23010b040b0a020f0d0207051008100e0702 81
    0x70030780d6600c4160507103c2c41c0f042000440d40c00503511911090400044000781007411415080c985400c50f00303502d03402540f001034950f98000592402d94130244010300040c1041c0080404156100d040013803030201305006003008039030900c2c046151036004405660003103100240c000d000d0780c240428440f903101034407040031403841403500105581310598048c501c9103070789507000181d5070003c91098056603000c0c2d0015403160420170845128484c040112175000084186d51035886000c284120328140456000001d13540c030200a0001c207103504604848181c2c01a4201c95260a040c010952140700700480c003158040340c3c42e410000980141c100c90540e0000030351441d20001c152010070f082d201c07607040e1181207aa0300c448400721030900004071004111907108007900d541c10040c22200c544624000c0c0c080c00c0d140420704401c0c40c0c0c0300b00440c40d0030b4001c0500b911501422410082e507684064010580b083c2c0086017003d900c18403800b1300d588a8032010030011076551a0694565101c840a0622011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 118165467 1106 118164361 118164367
    0x2100203100905180105040309050112050613050702030c06040c090e0d090302150702030a03030603050c010203071a100b1b07140f090c1e0c070801020322020303 71
    0x40d00c0402c0030000d0715407200003004400401e0703848595015030030130040000b00f581c044010401c072030007a02d44100c0c0c5c0e5140f410601c20b861007112507503041031500506002c03200481d0001d0b41c000c0c5d440c0c01641d2606400c50045410500111002d9136402e46414081000907142e00c1501080c00c0c021004c2d1011460150005103d030056100203407207080640880e02241c01640308951400e9401030840d40e0a281920b8081c026050605c8169000d010f6904d0b80d9005500200489070003960041c441c0301030440c044200e040c00036028003882440c640b00c0c50f0204940c1d0312400100050070010340c0121512048117042450310840e900f04080c07007903903038012140300d0f1282440c0c031b9101300003140c10300040e5075610302c00c0c440d034020410760590b00d01540c0d41241c0211400350003410643d041c4000c0d40e000580b0b801b142800d0b8841030384d408004c0300100c0780507200c0100e903000425140f84001c0a580c9 = true := by decide +kernel

theorem cover : BRFrame.Cov 117985611 118165467 := by
  have h0 := BRFrame.cov_init 117985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 117985611 ≤ n) (h2 : n < 118165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
