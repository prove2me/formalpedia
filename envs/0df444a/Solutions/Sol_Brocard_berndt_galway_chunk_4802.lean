-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4802
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:46:34.416853+00:00
-- url     : https://prove2.me/submissions/f28f4e07-a016-4510-af4e-983cac664489

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 863489208 ≤ n < 863669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 863490458 1250 863489208 863489261
    0x608070e0c0a09060e031c0e1f140306180f100f12120e0a0801020408010f0b010813050718020315030c09130309030203030a0305040203160609060c0515150102011d0c04 74
    0xb0f00a07c4280c1e80c0000c0d11910001c282441d0030784580300160981a1490144600711074050301c040c0074030101154001c8040005442e643d91a013038182e62a03030200b0303a0f24160a100001120801d429658041e6031030002c480031030301108a0100b031044440c4d0b40300606036100981c84410305010302c1c004000411442c2c1181707031010f4440039140c1c1e0041001e8800166030394945143c0d1421155001d42681c4003a05100741e1444507030340321300d1081d0044001009800b6480da90300d84145020301e264005840e0b401140c12281d4144000d601551048102d1400c101200b5031040070151a2003104000a0340324120001141d484216a1141503d05100341400101d0380c1d01c0f900003900c0c50300201c0d0b040300040e48600410007141400d02c083d145c00e50034500749810b10341c1812000340007000240102d000b00241c941c0003030700b070183c20003c0c888030301d101d0b054245e21801c00f02c03038a021456002c0c4040303000d5820006c0c20034130b080308505440d0f5000c1c00c550182032940b00002c100405092041c8629001c80f00780c0050090 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 863491708 1250 863490458 863490493
    0x30702030d110c150c0403230d090e0708040201140901120e280b0f060409060207030e0f010f08060603090c090703020a03050f010506030a1e0608070e0c0a09060e03 72
    0xc5030114000b8240d10342080d14507451070600c1d08505188203031111428800c240c007514080d42c0942c3d610106168180310100c0e081c1000c58108020f011141c0b040001b102c50440e00102100161800c610554800d542d4119080e902e40d4415100280040c003242ca641c00070700c85100c00745c000300300140b40440f45c840081010390151515801d8000140e0401c101544800c40680071050f038820303281e05607030000300c2c0039202e00e4028030009101818181c030382000640c5682e103991015030001c4d0f2002c411901c0c0c0c03149060050420041034100c5000710a42d0101155540c06a450841c00702241d07904d4500b2695042c040c001c0540010f4040c105c244220301e8080c0c0d0366074501c510740740708100c0e0ba84c00680314500390a0003815500c029209455039103141d4010712107501d4640440741d100304604008195403403680180076415a0410100d59040d1a00c05e02198403007001c80e0b240220b554100d08040c540d1038600094240d0301c070304068500402c42848082001c54011215a2500c00008054444140701c40139002e6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 863492958 1250 863491708 863491721
    0xe0f0703181a07030b0607081c020f0d05061e1504030623070f05190e03060702070302090603070f0315020705031801301d03040e0f010e070503060402030702030d 71
    0x160b40c095219681981c451011071041e5020410345001d00c464803041c004519540302c2c18101070104000000d071021b03061243e0304617401242e18803004555401200c0c55961103a080340200740c400b1810b28000c00c02c03502e00107190081d04d15107031481050840d03001c000c109428200c0140e10762441d50901000001c6906442009840503203440640d04022400d03200c204014801400c44080c000b24448440d240e030741c8503051702c0c0e81c01128400a00000d661800517224200d0b5180300a6052080b071080000d030039404141e10007282e100746d84070421502c4510805860380e10600a05086148040003000810780092080c102800201c0d4018a0311000e0349507541954843d030f460594802000035548900d5a00603a241c0a545030780c4540c113290240e04117075008140071000c0f0080c00540341e218021810804494405a408046089030303aa5962042e2820010200300c1d2081040440711000048641d12010340e244604060741c0e6039891591000c04102c029003014240904610060000c150248035034800d9a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 863494208 1250 863492958 863492963
    0x20a0504050a0531060507030e1e0c01030b03190812040308150919020c03040b070501061a04080c1903051f06090b0307030f0615030308061503010e0f070318 69
    0x11905241c20410311054641c0c080490b642c4d0012210302c20700900003a240c14501c1036001801040355221914201d019160a0721600341b84d02851146103455040c3c0f00d020359960b040c1105954145010700d00540c11118410301701d98040d00001000700d00032116040d82da8610f44690580350901030801c40c00ca60400f012070701200400c9000050100d0320b0034520440e20b000300c0c210342104407440d0001c50049015030900b051070f4050740100b2a504807910038025140604001c900003030715450315043c26406860140315400084520301035440143e0407120848054030513031001014000c5454080c0202185a4002e0541c7c0b83d5000c840407001440c24000c00440102501503005500341c036280c40750031036095a00107070b9540c0c0b810200b940151000b20707149084030781001040b155550f11303003005400b500d0401c580081c01d0340d20380c8010003090340020180d4003c0c80142e0340c00c0d04500040c0d044041c148020300401510f550f44400107000070404819150740041e6078600031444c00d100c80c0802c00701c1c50408404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 863495458 1250 863494208 863494211
    0x72903090601050901120210031508031215010903021c0201090f090e0f0f0a02060c030d020a050304030210020901081302030a080414090a050f04021912030f020f06060a0909020a0504050a 82
    0x4029a00e0080c4c041400350408032241c0c14400c0040c3e0003d4000c40600c3c801d0410f0644640c2c070a80c01c5c646681814005080b20410380b81c2c0c0c0d4140c400700d10703040381c0c0844140e5400b545605000c0b040f5440307101c0e82800e495014004550120400308080301c50018060100d04100c1079550204d603070240d074200e03440140178102011401f04403110641d401c02c1290b0070040b069900ca0101110078403c002200034074990180c0d9010385d91152490494118410b04203ca108607000041c020440755102c00114030807030082d426106c40a1a0b12400c20503031140c00c020500080c9200045000266100e0790000b1161008049494035003040d0ba680009030042c0e03009442c03001400c100d885030760415102581d80034814040802c05464060b1080502502c007420207406000802c642a80340c10803222194041d140c0c51294240d00d826910380203240040d1f4005000c01402000030305107114000081c0e40740581001050030b000a802c203e203000040180a205030b0780803a1407072001a850f1201e1150354061040d4000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 863496708 1250 863495458 863495461
    0xe0a2004090b0f150708071e0218070e01050a0e09041511040f14030a0501141e090c12030d1d190f02010c020d051c02010606110729030906 61
    0x2203401c0b2011007201c940a160400700022103580c03454180c580035003203240e6464455500e400d01c052a4001e080c0300400d071010407046106020500e001c0004018800c444500e4448440860305044110985d07504c0040b03000030328079169543c00f80300034154880e510700d0b04010080c90b0f5000120040400d49041d500b0202000d070000d15030085001c2e500440006541462416142c91403e00c2d00c603c4a100e030710b500038104445c2ca00d10b41d605011900d981500315000b80300250341c1c04003001030000e0960304001500c4080c544041e06070041c44500c3c0c402c11400010b0481f0032000300c180080c0e41400d564900841c0030400244411132814071a540300741d00d40c0e4200300011090b44004525050040349a00c140c4000134486a000442408099000715030a1812409522451020804803011900003c0c00c50182c44161040d00b0074201f0a041e60686583c001e0005950700e25055070960400f441c00110383d008002c0501c4181305c481c00d03c994000c0c6d100a2044000e1840d0403000c0ca540003a524043c90307800850 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 863497958 1250 863496708 863496719
    0x10921020708190206090a0303110610030b0718080f032101081f091211060f0601051b0c040509100f05010609050904060617030705010617070e0a2004 66
    0x9a9540191050000384880c90030003403030965032501100e4011011003010a14011900c81070b003a030750070700f01c084c060766207181d00e0b4600078007050040b175440032071072090070300280c00c90031500310700d03401c50b5041032042c0c03044d4072101c00807101c031000009560b231514070040d0001400034080000b41c0b40e01a910026503294001d003a0403444039058189500c03d0412000014407807120b020550010b451700c0801d820728a002180201000f8185082e40902040889802042030f2600002600303400c15035a01620401e03583c50b4160201c001003a16810b00042c0140a82034240c511b550b1014090108441150b80c2c141d003d900040c01d49800310f1b0001c007035811000041c18580000c1c019608400d100003400d11113981444001000c5400130300c605880b0740c1803040850107010540e84400081c000301110002c001110f1301015a599000c401c0c00c80f4607601c2c0100c000f40120a1108241c1c038000143c001d410203034904105420341c0c8801425030100140d0301c1034071101c0d50341c5150540000c1490070041507295403421 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 863499208 1250 863497958 863498003
    0x80a0c0507090e120a0311040609050f0d030e0103110702040c110d0302041224050a2004050f120f060906010f0803070c030303050a020f210c071509080c0109 69
    0x10b03030002e4103960402e514104043d00c04a40c4070f4034082e42c40001038a5007050f1000f1006088010107440c01c0303840004001c04c40a50202c140e40607103030b007901d403003400030901018032540a540503805000a1040300701055198841c1d00200201e01c9074000c0c1c14204692900041c2c00c481d802543e14011555070002180041c000340014441d0103218103045090901d09111081d004021070401020b9104040c1d020f0003240c000d0300081d0040c031054004108900e010030488000740f030700283c450b00005413100c1e003101d5800304c0c60403a81540c0024023055250302110091240002c800f03400010180254503280c3c0d081c1004211161181030041c0080c203040d49000a405c4881d000307600100c11a41007000080013280e180313020302c002c03a0781c140f40014495494200010080c020b410340004101000541c5002c040003c02403111042c215031010f0381d0985800031202141e101d0a04020145101880312800300503032075100e80011030103100d4081c039208000b801142100d9400200f16050010600c01600385900e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 863500458 1250 863499208 863499223
    0xa02031f0f020c0123010e06130207050607120f060503070521190303140103050312090309060d1406010504210203100f05041202030c072106290f0904060c020a080a0c05 74
    0x40001441765050402c648401a401080180244028000001441240e6040f6844a0b0704101901c0407403d000800030703d080325100b4000d95190a01c480804a1861407043d8002c9990007402840c09516000a0181d03006108592070b80304002d10402501302039050051286100900341c491325000d0461030064101c51064401a0783d40502c00e00600015000204603039000c4011280007003a030382e81c1024989184280c11105802520100e00400500390035081b62500030000b00d03d20380156111001107131030340514452544c8600101035003102c802c0e01c179998040b0160015099519211000d00080241c40305803130128421030313071501003106100c14554900010203407807010310302c0c2c1011100c40c0703541c031841030007032217081407503001294110100360896200c01640000c003480500e1001c80034290111002071410b0510b0712080070141e81d458445e840c0108910003e000604644a070f4503003c0c002e001040501c815031103944016004608500c016001c08000c55440d010010800c1c0351040c05c0865 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 863501708 1250 863500458 863500511
    0xa050108060c0406271517090a15110a050c0d140d0b240a1d01020706080705130e0603010b04050402060901080606040308031e01080a02031f0f020c01 66
    0x1001c000c1c030181c040400d0031241220355920b8854142601c1e514010985507001401d20303c10b900700007000601d91045503019880068548520028071180104090390b034804030341510090b0094010a00001c090f0003071550b0035424840005009011081d40442c50792025484001080c0b0100744442102010800220701002920b80601c4100803c407081d0300c64016040803c0c0190303111080a00d035034843c10b8100480350714000400145d0410100803c4495000d6058070002854044045501c1d800e440303112900b0302c00c184e000300a014130b00303030041790510005070800042180401c1648041c0300c908036400c016026207044c4c2c03460740c01c20304c0030103007111030141285008500304010440940e40c0d5000340c400c240c0003800c0c038900c2030340c9400008401c0c1c0f280c0e80005092400110030b100b009280003d002c420001e1141400f841640c80301c042d990b4540c408200258140c2c03020203c0c4864000140d0070300050500d100c40403650740c20301030246080c1d81140b49035044c2c680d9900c803080c0d4500307010504070304001d8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 863502958 1250 863501708 863501713
    0x306111b010212061203070209130515010b16082b061202010c0813080604030e0306011202030a060b0109081219050304123509070828050f0f060a050108 67
    0x3c8080103004281040202140c0c80350703141d05081c01e0420400d00c110303500075600510000d00c900d0305c60040c0980d5482c083c42500c43d44130340041da40b44160580c070035905132a108282c190030458020010f540b00924550200c59410040c01411107034811310b1441d03000d00c8050a103107982400358a00d00e0b411500c640d400143c01c0500e02d486400540d81000351540704641201e013103a551680c801082051080300d50024031203110f070300c0c100020f1582c01143c2c041d01c000218266404d59030b9400058062842c042d02c06507158100d003080c8400100c0d9580100c6440e2418141004855a900c01700f0342001c4032400403524a000000c1c00c5103800b003066009020690507810f00ca4118241030700e03803004a190b024620414010f40030301824440359101d5800d0207a0407080030301c824600e80c00b030041c3e03210042602c0e000b00610844030041811000410080e002d220407103140c1301031240a4071200c0380036500380820f031910b0144018580e0070800c148406428881000000c0510303041001c3d0131400c88805a006180c0358 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 863504208 1250 863502958 863502967
    0xa080f0d0212180a030c6504060302180a03051513020409151d0303070e010c0f060507180509040809130c020f010e0a0b040b040302070306111b0102 65
    0xc034030810b48040c41000c3d003100c0e980c51410000303e45101c4140d000035242d603001c518005051040081d074208020052030200c1003004e0510b6240850040012481c424020b0b01c6a209580b03074003500c03c1c42e02c09102416004c8100c03c071443c0ba80850b5209030010400650000b4212118007070000c0a0180c2e41800d84100040340d145464041e120002e01200281e1803100c031010035102c180340110f0812040c0c00030000c20030b0704514a00122400c010004907120641454040c9000c86200082e12922000c041c000c0c500c0c40c1d590386000c07200910f00c0c004043c1880b0300085104003081ca40641e51104901c90040040c507428400005403d1080c4044421200d00c0c0e02c6000744000d40342d0001450f0069404210301d80c40d15802c0d000208000c090307402428945161031300c41001a980003482c0c0403800c07111002004000340b2861015103615544502920901e10000442c0001e000d004640d075000d80030340f040e209855241d03a1140c06441c81c4d01c40307130f07405000041440c414903a03007241140b942c0e114950007186030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 863505458 1250 863504208 863504233
    0x806180f010302190b0408070510080f01050405060d05060f0f0c0c03070323070c06080604091a18100b0316230a0f0902130906030803040f02010e0a080f0d02 69
    0x5010341400000c1c0144030841074001c01259071030003100513019003d900e03504d80b5100c81e6036503540c4000c1e1007040d00c6400004605100180241038560003501c014400e00c10980c00c3c034040c40040c00e000351910360400c49020805000c5041485814014074108030a400e50b402c7c040030400340f02201500070b1120b48400c00c802c0b2550760f00002182e64065150404031003014209803801c025640c07081c00d4061090000551400b00302c0505c84031016601e4903120b950403510b46105100481da001c000007000f5a03003c043d004456101990b803030f6841401d41d04082c01111540c07003594200704407841410080c0380c0f02c124498003450184940320707801c6400f6031450801441e01e545001b41140d003c001d050440980c1004038603a4030f03483ca1440c068100c01400d080b0050f51900a10b0080d030000085204081c180e09000c128003126014900449811124990941d00d0380e403070f8850705440d05081241845500d0350341a50507258498120010035122010b00220080908164103010212440c94115000500400c030f0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 863506708 1250 863505458 863505481
    0x1050f0102031b120f210c0405010e04020f0f07030e060306010f0e0109030c080f100b060301030320120d0c0315170f151006050a0f080408120403080618 67
    0x1103200f6107004041001c4886034240e07060048044c801010903400040c6000040789003401403c005c401050280300c81d41c04220704d034032403076000d4500b40d1110108000030001c0e503100344840c0300002c83c0108010700d440c1140750314400b00d071722144041c0714410020900e01c0c10305420281c10001d00100303807066441c501e801c2c80000c4c5814400340d9018148401d0280c139080d0f80c0d200d800c00c1c9c0051680200900c0006850b00d952503a17525005018000c14460180385180c51140c03806031089041d806444c03a810360f421503405035a0612820404280105071624201000c0001c11100340c01010803441c00d561002c2c11101301c016222000f500714181400d100c8441c82c900303000e940d5142100c003104011b50245146480003400d1400000c1220354900c00c460007149140302c0c03030240d94010b564039000d4450390399982100380c0340e90181c1401040030070f0810b84003c1d2202d0049011540c0300d481580c506182030107a0010702c0e0301c0c440640b0241e0000e90000100015030400c5d10310701102d070424600300111803402c614034a4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 863507958 1250 863506708 863506717
    0x51c08010b030c19031b0504051525060f0b1210021b011d190c0e0c040e040f17040509060d0f050f150106030e0a030e01050c121201050f010203 63
    0x700e1030000100040300541da03503050341d12241e000c1c4015441c46116070401009041014500703e218200c1c02d140780b41140c082c1c4125401c40e40c0c05040786980804040c4a0807698011400111904003100041c3d01c10108034401c81e94801c0c4602d2000514143d040c00b0542141c0f61b8910481c015001c06100d0203100d0b800090804150380c0612001d6035902154040e00d10390b01c49004444d41030f41c20705100c001c0300d580c021001e000b13407941c1404135407210b2a446128140e10400c408003a0506107003038024080380340804000c640c801ca88034000c500d02070303030345819015500301240c0c00d840080395001c0203c1048035101260000000080c0014141401c00d00061201c08000d02400c1c880c0c4d4001552000b048140c80d50f01152640203415980910a03c00c001903c0782c103266080c5803d40c9540001181c018000c0c405d80d13101d42d010000811004003503030b90664040c008017000e517060003810b1101030038140d0f04020880180c0009581e00380c9480700e0a50800e05c011041c0c010078498010b000c1c8005569900005a6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 863509208 1250 863507958 863507969
    0x801050705160b0901110d050a05060609060a030c022e0507050f0405061602040c0215060409030c0807021306080d0e0a27090f0b150a05010e04150b03090a051c0801 72
    0x80259100c0369002401010700c646e000740c1101c40070404203000d10450f4409032080091800503c03840d990f510070400305100d0603046560100c0c091000c50394461090f4045283c054150040b21007201d02c1c507a60140401500c0680c0d0440f140d18145040200b140e409816049115801c20600308400700e9000082c0340a02e00643d07010341d50200317501d6000c4421000b0b10405a4019008220100d5591030003510f40f042292103011008003230000c00d00c01e044c6441641e8081e6010740d07440c140e889040c0c5d204a4689d0100c88103030f0348205400000303846d140c0140f04100050034181c000340b45401500390041d0018004c251160f100b4034020004110801d4110140710007446412001d03410000714034003c50060508000161191400401d4038040203018900e03107000b03030000c12030f14400f44001070400c0704020640c0200345c005105808084858149030b00880c850a081e211040341c440c0e15160b8040d0aa08100e80c09201580900307485d40c1480340a101420505444035250a410511170720040e18564048c03203107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 863510458 1250 863509208 863509223
    0x105040e0a33060b0c15040809090a0209030609060105011101050408030703201801080a2003060616051c1b0f0201110307110f0303090136030804080105070516 70
    0x208211160126089003100080b4408014443c2c89818010140e005884000c0c200d1080c0c84005080382c007840000b42c483c5600c00c0040b486e1051a401340242070324080d14105401d9020300a04036595000c0c001d00344655640d5004000319071410000403c2d5280b004c8605c01c81c0d900d42810710001c6139016003243d43c041c09a00f40450751188003100480200b01200e64510740300c0e40071603208240c0030800301205099000340e9611260b611032a9030481140e403400d4040824440301119030700742040e842c001e036a00c40401000c181c101080300c0c0d41010070006103102120107401a00038000e80c212440e0007454554244d203885103003c0c0d008a84004902c89082c1d0240400788410354a10440e88a1450507011042000c1940e841d1580c40c90b102c00c1e24880c06100b140306240c0c2d0941101c40d424004161000150165035000c4890140080c0303900750b421206c5007824034150144440c884004805441c40298801d08406d0b5481d881d001c1c2060841e88041e0130041000b004200e002c00116039000d052625a420184 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 863511708 1250 863510458 863510513
    0x304050f010504050604060801180b1c03110d050c12040e0103140a08040e04051513061d01020f131202090105130b0a0f0509060603010b031b040902120105040e0a 71
    0x60b105805558000b40d03004000203001b15401341d0020740941201c21501d0550036240c8840d84030b005562000c0403144c0c0028003c00444002003108840000e054040d00300750300c8075401c1414050034140b038452a81c011900000d502e00402c082080640b2105e000c041d003803403c00b41499a40b940c25201840040e180b4001078a114450791428840c444403290f0101e900b44c0d507559160201d01094400312000d540030b01503a40004091602d10342c50610400300850000340c6880f240d0303603030f038014220030b0951482640070160b0071140d18401d100910f8096400c4803556211002d0042d2038480c9204d60300441140b81018059000503101d11a995040d100c0c00c82d01c11101040d1081e048009262015515603c1100c00600048684440d1468015100169070440c01c1c1d031b9034a01403201e00c0c44203204406200c001000011640128204004c00c0c40412000c16450156503050314020380c1c0044411050070704442004204c0ca02c1c00380b1038880510104d402900d0a06c0c81904d94440c001240700001c540450744e00f0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 863512958 1250 863511708 863511739
    0xa08041a150918060c070f05060a0b0901080c060d0e030904060303050c0d1e0e0a0e0703050a0b040b13240e01030b06010c0f0809040612120e010c05030405 68
    0x16000400c90306101440c80c0c06141c882050761941010082803402a00d1107800f248602c4841c0c250f901406810000a181588a00028024560100009940d08202c0001c82c400144083c01070500445030302c0d04c0410030180301070821446420691011920354080941d0440580784d43d820340d100c40b003141c0c0d800221610442d0100e815403080c00005a88107103400d90100c2090f03004000b0b80702c03031903289003110848407641d00140c0c0e6034111400c846414503480346403120200d108203100040f507c2d003c4c081d118016a5100c103060100340030b0705d9100100c0c1d21071003080400d9840c3d10030550140000c96080c002c40002102281d10b00598020300500107441e10400c02c034941c09409140710740e42290345101c01e015a40c401c007244801c420b0008403030740d038103400201d94198424400c9070215a0000444021401c15542e04c408a42c8800e2030716400c90f440c1d61001901040d00700682c00410f000b8082450455041c0e0001003588803024145070520400d40c082802194002041e202512000d44800802040e001c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 863514208 1250 863512958 863512973
    0xf1101050c0105040c03060f0e0703020f0114041502010f09020907110c0d080705070e0f070f030f05180705030303071407061d0d030605010c021008151504060e0409080a0804 76
    0x41e1030120003903080a06200c100945110b109086a006150070030650014440300341c2a242902d42c1f90199900c010002d10240c40c0840141c84c0c62507050404c0b40c000074442c41e52424076001a4450340364983d607002a100c0030b540a02801d2001c3d0350003581004030300b44960006851403800b900c601d0420185180078039840c201040243d05000004081c0e0400d10000d190003545a40410002c4441c0e00035800001603128107011503c0c050702d00c9142c41103a9a4441500300d844a4011040390f0425480f0111010640603e02c1042d025004080301410203040045e092460030386140d106034040e500400070003401c00c1d4061304502d4203031174401540340d880125042010282048051248203c0f030b01c010004100d040018150313000c014070340c40503c1042c0c5d1b1100107440341040b924019402c14540b01c41010342ea40b03e0002c069000c2089840080c2c0c40e000c0c3d201154881010000b94041020300140511070650130883e2590780900440d8140103010041d81c541149006084406043c09040401711b010022036 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 863515458 1250 863514208 863514217
    0xa14090d0b1311091018090605070c05011a011b080f130f08010902030a0b070c0b0f0a0b0402070c150c080d0204170609250b040806060301180f110105 66
    0x2103581d0400e18189141010503411852004451000150180c070001d410041ca20903c50342d0342420000c8003914003089000390609110800d83c00f10340e01c2078801d000404903c9002d002d5000c23a40c54a2403140700c1c2c9001800c480c110b084a4001003440308407464940e80c03121200c07500c41d03520700ca046100c19003881d15403094054494109003140c00030500001c0030420368040b404480402c030341e2402203580c0300401c9c1d003224643c0c6000394240c2c002942010102c0c0400c103140350013040303d240c2001540a19118141c80340400c0d21400c64a0303101d9414002200c4a60146c094610340071a411450a0407564407445001c48922800402034450000c01e1701c258010050542c03180d80052034140c0e81c18082081c0e60096015004003002605000c45540350380d40001603051141c0d0340c0c80300811051a01c22807905400c0e000c0240c9004250f4134070004145921003202174401032100c840200b20908203138007058259000d06144100c5a200c01d26100c0200b00010032500601d500310800703046007522600125120701c20f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 863516708 1250 863515458 863515463
    0x4050d0f03060b0f07031e050703081e04050a020916080417130305030d052404050603010b06070b0a0507020a0803010603050702031e030a0b060c03040302060319151401050a14090d 79
    0x11900031284913865005019452003603981112280305160105a0070072807007541d400041050201d140040c1c051149280c010032a9841240d16460616080c04100030485080b2025080140c403903086042c681c0009070401c80389181c1d8500710007980f00c0203051001c0281301400e480e40f845a40364400e2403103411a5403c42c1c5c2d151265006544038104907035203600c00003080481c28604400120b0f204603408900d04a9803900142e140c0968881c070030440505800741040d58903559441c1050071564508000b060010302c211410081440c09400e0740c0704458000b40790780195001f55120a0010b200c510459054481d2410b00003500d88848404903c0d40c0696041c0310b84a01140105400c00078048018600c603070408007090058144501c00d00c1820300608103503207641e9006020600041c82c0c004080c542c440d04040d0086101242048080c00b41d0300300c020701c054481c10240d4140070300386c1d1011100580c035800303090951605c07000ca0b4008143c81d80d40640c0428030040403c02c450b4944c0d4030000c2d288620f4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 863517958 1250 863516708 863516729
    0x105180c09040e061801060b1903060807140a080604171b06010b180102010c0e0f0d0b10180509070501030c0e130c0e1c1209080727020304050d0f0306 66
    0x243d41d02c1500781d072001c0076640d000b400b80c90450740000d490414000d03401034860159446007010546100303c58034641e00c4074404249501e6000104a005c800c0044c000140000c111042e41064140e09100c00800290040c05580d0005c07800c0002045c2401003900b0012000860310341d80d407902402e400788166410518588a0154100000700c0050880107445420300d00c25022058940400c01603080ba5901c0180f5000300c0c44151110b800343c503119819035044080035040c010303950300b1951341007440d500c103c03030016510503480302c01e100300c82a40d00c0340c41c0900c40101c070810050800c40943c554503800f512450b03040688491545a000d440351404001e10304e00030f0280f0840301c220404510240000030102e5000401c12011604145840f150a680600c541c19010701d2003400d940718105440e51070318660003423000907140001e1151082041c500100070f481c58002607060340b002c22094150710315240c00d0607640180103100228001090100f8001c1d120300f0071099039103a608040c1c01134070540d8441c4070f0741c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 863519208 1250 863517958 863517971
    0x5071b1703040807081c0b0418121101090c14031f0b04060905040317161709120708090931060b04090506150405041e020604050904060c0311030105180c0904 69
    0x6600c46c0039032444041e00a0510245000c0e8052004841c0790003644440584030080c58404120094801d42c4000c3c210b1900c81d00410f0703020041400d40d90141c10840d103402881008100342c04440d800440225000c030301400030406080b045020310315850318510000c81d84c0340118a025500c5520410003400e840310281300d40d151504010744820b02c0415030f500c0300c04004e00003c0300d1070514200f014900c101600c41ca4132500140303281200d400401005120144500b2040c500c040b240e8101074002c540c8030709403103681c0b810a40180240140060011500406540c406d40740c2c80c0d0801c03007000c00c15440400800e26440301c3d4207012025001c5040d641d41c00625000c28401482004158644100c90300c00100102080c0c07031051008a410884019028503000383d403100c24034100c41011314800d40010300346400c1988450000c0ca03030f142e0036201120404d5581506103044c681500070f404103c4112106a41598500008980902c6d69041c484000d0031a48000450b0f5002990645003a22005441003000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 863520458 1250 863519208 863519227
    0x160c090e070e070c0323070b0118051e07030f0501140f0f0102190f02060a050c06061819021e03040312051506090d050d020105071b170304080708 64
    0x101600100038450340941100402e041c902c01166030b0040103a540d0b000b4100205840032202c6100b0401482049102011070310045148175024201c901d006003400d00c441d52408807220444a4190151038030181017204010701c2404002180304203194a600c0c0d0030099031101d074110000d10328008406121454200046480c01c4e00350301039501c1841c25101940c040c62140104500c900d007915041c0d0060b800a83c80c401d14445141139a02980d2094100c00c81804141c0d00251503034102c030714000001580440c20103000030341041819004401610340c015900b5241c000c451038120002c003643c060802d021402c0e540b41c081903049440708c00c0e401c0c07141150a1540c20403600c41341d000ba82c082d00092003042d580300903048544950b60207041210707040300c860b180c902d05004d02030b00300761080c41c4d00c25410031044001c02c41c20b11900f143c400c075590000460745811000501000280402c6e540f45011a00c13480c00000d11101d0b21061002c217038603007152260356910f001340051003001002408040d01284200c003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 863521708 1250 863520458 863520461
    0x6090a0e100c020c18060d05120c0312010e1323010e011b1b0201031a131b1d19051c020f0402090f09060a0911071b0812160c09 56
    0x2d81503041d6090381d0400d12060104980381e0600803825080c10102004586a490300c051004001071040080d2400c01c00264880d002c070b50401d540d140c42d5908000350b820a51001c0349400fa02500b001d01c40207610b420510420791404241540003000c156149040102400c88295002c0e000d140b000000e012903030078540002c1c0644414281091204c407102c4c1d80220a0780500302401e8104421144a07005085136001103015000c1e1320036428100c0380d005030340c0143c1c2e12171a5005450030303406040402e0111030903005403031078400280040c041052180c030030301b004155122040000042100d500c425040c06c141c603c009095603511075940004c03170484074001a910740c9a0382d0303111802141c1c02c0c0314072500740061000340d10607000c0c15503000c900600007154038a03007103414682100300503140c00409070721401000102d59a2840301e82c442d0a020030070600b0483d03040039015180040000c05143c60f0f00e49080d01d9680d10640032110001007002c01d18080f4450140d0203013040582000c082d03c42c581d41d0345803000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 863522958 1250 863521708 863521721
    0xc0a06170606070f0f0c030b150108060102030c07030b1909050d11010603020105040b0a21020c060a021312061104060e12150606130306060b0307091d06090a0e10 71
    0x90010301000c00101507262250582d440d8640056074604900d03210303641c2009000721810201d58100200101002245205590900c2410b5049051a000c4070071000502401e4009180c641154000c01c0103894850000c10440b00b01e81c1d000b082103000d521004020500c0411802e259000103113800440400d01800090901c02e9012586600408cd0443c151403801c1c0c1d03403280400703400300d08200400c001d06004207004020007200b40c90150200c0203546900f18000c50712040c0c55400540201f6402e84006003848000d070002030189007146810071031070044900485512419a0110744080003c041c80f000350444242c108140750181d0742c0325201c0f07402030520301e07990469034015000441c00c0c036442200011200d45034041c2503001e4865540720030801480f03038460454200d08015007000000055084d004200c0a02409211140c0700d00d411079000380380c0c41e45503104502d041d412503c00c00340112042c281c50342214042d208408140c0d26444d540c809402c06103104040c510441d0031100c50340340741740d0094 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 863524208 1250 863522958 863522987
    0x318110a06080601052a2b08040b070302030601020f1005150306040c090b0114070503030105040b0a141c020904030e0915010e040c0201060b07150b0d051e0c0a06 71
    0xc042511410101c401c4079045644a010400400111003d00019070344141d8035204201240c2698400340c070301500780b9040b0301c0c0001c0c144410b60401e803101c0d019041d0702e2585c0a02454551214500b60f140c12850110103050ba0341496400000718105034400d01241801050340c03811611007020190414009100842c2d99414260741c0c0000c041d2140784c017007592070080350045c0b10003040601f0002114020500c1035800d5060104125000c1c49049464004c1c04a0501800207903481e503146c141400b00352082c03c041d6610a1200101c280103082501220414004058506034400000c9600c41d1000704041000a54004210401c2000b00b50b484400e00e00c264005480c110100d44540f418a1100c1c01340702035142c0401d40900421000b410664491511410300307100201d0510b07650644280142d00004c0241c4200388035101d034495610a901540c40418070982d240b1650404644489440b19460140140c1d85165040d2750507041000304035510f490100207080c600e803166a00405440b0901d01c8016 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 863525458 1250 863524208 863524219
    0x10050d050a121d15090d03031d1f05071403190e0c01020a170708031006031a09130606030204020301151112070f06110a0e0f0a14060a031811 62
    0x20b44032880d1041e5118041d0122040010a0140da03c0c0204025030354000c1003070903840c0040c01011420740c0c0d45104c071080d481c020f490000c4c1e05143c52201903054050035400c82d8280e0302109900103c191031411101419100d6003001495071101003040311988035104441c0d069600100901840c041504040b000d14500b85904121245000080c1c0b40c4500f5404e42c450302507000181c680c000310700f00031300c0c20032214130720100a482d00c0c0c1107a036907071800e80044d60024840039180c001400420b0b0180b0510b000841003004415030f00341400009079003090014101807034640702c54450402c001607500984081d55008200713644940c1c4821a007000c8001f441400c0c0002021919080381c10700001c22412401070703143e4160351801c0720f15101c0e000f440400c41070480c0e04a943e03441009802c030103000601000d2441c5c0d80d039504600411810018102c2c52350701040e1007214a188104191043d0454051601205647d1140c50b980e100303031b040d4000c00c1d0403801d02002404201548041000803c14031240d003508452 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 863526708 1250 863525458 863525483
    0x60504020a0e032b030e0a02100305010602060901060b0a050d1409010506010e040902060d1e090b041a0f01030213150b040306060b0403121d10020f0f0a020d080310050d050a 76
    0x1d441000481800841d440c410034100c65107031780303e904021510301d00242241c1c2c01100940c0400c60790300240c0244000260340310018805158180b00658000717002c40c0c000e1150504158016690388a0154001c1c2031180000b104641c1c03403501e0b04481000d06e0110311110480c0782500d1041d010344011503045001495002d440d0000e460144a942d02c035580240c0744a0030182d625240c900107000400c040c1103408440c40c0c1340b40810740795009101c1c0082c499810519207060600d0802130120100035000075510f108001c04c120101c0001d81541107a4044801c1c0301035042d646800402008c403003103801c5028040c0d28000c1400c201d208010f104492107030f43c04001155a45184100c2806680801480c03901c9004440b11054443c81032081c030b010603402644a00e80080000440c40602c694441380580c001600414041c40113000e1a5041c180910142000071072581c0010080003101000400200d0040b0104402040c3c0346401030182c4009400314041c50040d0420aa036001d00030b40440e06039400c01c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 863527958 1250 863526708 863526733
    0x114030102040b0409021b0304060207230d030806011e2001050708010329130627030c050f030a021005100e0109050a0912110f030922060504020a0e03 66
    0x400c0342d0840d0f045604003410a81400c0071a00a07603c564240c8104003640129054200705c107000400040540760001c000320b0307290621503598045000103284d01d002c9502c424914544401240300f80300e5526103449605a41c442c2c00503a2981c0e01040c805402c680040818010550080011002d8062000c00c41c00849d122400d000c0c01e807081112500c0c000b42000300100005040d10a440001440422016002c040003245420f00080120744980c0b05103d000302c00710600260b03100d02641c05c258845002c0766440740350070311080804032403401800c22000030003d0b010303c00244030340b1003121500805d0360340d03030700c0c80b13410007556040d8a0300c82014603881c28011801046450307444074115140951556030f180c0c40c0c5590b5000404000b44110181511044010002130300d034600c0d04284840b0351a5622003948903540c40b8070f000441c00f80190aa8010002c1c0784590ba102c0c52602d10791a800202d0f51081100384031514058203203607004580042c00420040d60a581002ca00c40c51130409030200c58a008969 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 863529208 1250 863527958 863527961
    0x3012c06160509220504030e1906020613031806050304050d02011e0905161e0e0402130203102c0c1305060a030212090a060506060307050423031501140301 68
    0x220344101140c4104003843c0c0600307124440e40c1180d0b51306180c04003180700b04d12200382543e00444040300081c4400c0e01d0010149450b4424030301da11903480f403641c2818100703403000e981c9003c041c0005042c0261043c004080522840182c009400c4100b11880304a50b601009403050b081500c0c115503e005840c21000207a10511410829001c08003950380781404003202d21000304102002a104e034002c490080c0b80141c030a4403440700401c07845c4036640c90041d8500a009410202e0380110300b00020301b0b0248005680c0d418403166880380c06210040c1c1d40d8a5240820225842660080c100c0d50768800001e1000e8084103416200e09885051348542c42ea0742d14000c1c046030ac10380b10404880c0c441008240f000c0d041100203810100c016040c010f1400d0a00016130740070a204070b640c9849075020040390005c008040c0a0380b40c11070020b41ea814110304180c02d02804d103001c0d07070141003000040030800e09102e810a803e00f160300d61002e41580c025000086204e12644004d0041c00003040c3d01500b490180d0805 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 863530458 1250 863529208 863529241
    0x7090c030b0d0c030f0212030c06010612090b011a040312050307170705030a0906020d090c050a06020c061909030b0405060f0f072106030203030c070e0703060e1503012c06 75
    0xb10b0408281c1909603518845c45c03014404040c0c1e00700713000d691060444a0100300602500c40340f20000c11166151410040c0119007207001c03a0500c90030448441c000805414440c0d0642d00080c0240ea02070714000e4030904140140d41c0301070b2081003072100c5540d5588e000001113000b09680da403090840c00c0c0c143c0c902c00a0030015602600000c0c1c0401c0042d1100780f19510440443e4814030025242c0070042548906030740c3c03082c03020307156045903070803c120a15101380da1000914443c00541090720841000900c00c0c0210050126082004030715104068410b2a48401465001c15400e007541003c0c10b1a0b6541c00c070484400e200c8800d200e010906014950010910a8010355514601440d40c0d414100014003c84486041241ca840d40400113036010302c060110540180020200240b41403502d80320014064541d00c28903160010503c8002015080143e024001003a580c43e0b09541102207070040150b5200008900c0310050300210507032404200c2501060301c0700c101c0301162903401449080e03d02c03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 863531708 1250 863530458 863530463
    0xc0a110303040819021e030903010e0c061603091e0503060a2a09031a04030207090905030717070f1101021b180915010e0610020c0307090b1207090c030b0d 68
    0xc4c44031000f40ca0030380415000d072044610550700f02602c0410102258207000d001c00010340c0012030302d0f01d0ba42c202446a80002c200f024010221940c0103808102c0c54070560505408404513280c5880c245070248025074021b040c9031040c8880a001550445868041802240c0c4640124000329203101e40d035018100104d0707441005e0740001840d01800038002e031703102400300301030001c6000008040313401c0800c11030100d0b81d05200003050b860039150082c2046020b81211300d0040c44e0514080101e04000162003c10350300542d40132501d410042e00c10743d0f5001d0850018581c1d501d042c0950300f048100424001000700c20b07021a000d415020443c800542e01c2118500d40200d10f404803400b1640f807406c9041e810030581e03002e442c00076a050004802d000402d8004080d030b0114241400550300b880490010903800030301c041c1015190500c002901c0740c1c490311414200075103406001400d650f5002401c03484040d010308695860f541e41c1520000b900152000f80042131414031540d01e10b0800140d280b90040e03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 863532958 1250 863531708 863531723
    0xd2330070b060105160206030903090108090a080f0304030306050402190f090b0d2c010225051f020c0706090302030606010507050d080702010207020901140f03010e120d090b0c0a11030304 82
    0x1550b44004441c0c03504420700300040e9400c81402c40b00941c4a1100841c01a541c1a0185664400310400075061080c09025441c0d180e12036004c00c1e020656030402d444441e04001201552500e441c10110040d110741d403c041d0b4001d1001a0b440564030910800110f116030540300c02c0069514210b0584000285201d80084001d08205140740f04070164000300f44100c0380d06402d21748c3d1034880d26508504550420400c116940002c40800310b060b0320744002c0400c0452005442009455516242c42e030550020940d00102d0004501040070000d03010394404441217400c4400c22955120001c01a6515100a0303000b8040d82e00405d030154803440458001c19001401044207a04030381b0f084516050040121045560910503980160380c1c00114034000e240400142ca4808170034020020fa010140500c60708c6680340051610b0240404504925024034452a603a00c3d065a0003005020b0404050000c1c4240302e5141002105c600b40c202600744640c01c0e076240c64001103070241003079903803005540140c0b268 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 863534208 1250 863532958 863532961
    0x30c010507020d1d19180515010c02010302090109031704060e0303040803090603131505161812110909012705070905061801030c05030c0409020d2330070b 68
    0x2c1c003042d410082c3c4d60001400c40903404000000b640401180741c0c128803942550003040c10017034040380c01100c1c0c1140998071485901011140040c00348641403000906060300030894124a0f070140d680340c00116000000341201d1041c405550301142d0280c01007001142c0905c0301c02c00942000015202501c00c01401146403401c094100244d81d0002083d280c1d03034001c0f00480d803001401d1010003c1c1c10048441c80030801e82024070b17082302c405488014080400204164003076443c21056003140071620440844160301d41103051106480c140980d440d42c101a512080c480c0c0014158066802501070345408581407001001090b02110340f8103001d0542c5c0d010181c00d21010070143d01c080d0708004001c003180346c0304401c400c0074110230b5400d9005a41120501030b0030840350a0034000c03030b042e160040710100b00da08031590000302941c8624101401e00d002e4040400b8492001d001c503207c1c0e031010401104c20303580550110790009150425802c0198208207201d0381e030b03040041c054400c110340c000344000a5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 863535458 1250 863534208 863534237
    0xc090c0d060f080316150c0c0317040209040212010f05040c0302030c090c0f13091a0f06041d06030109050307260703080a0504111305040b091207150209040c02030c010507020d 77
    0x31700c0d41e48082503035a42c520146001140e5003138031a210100c8010f4640c959040b049080140c40d101d2010759860703032903440908000040e0380f500ca0096020b607044a1034034501035804691401851140d28003e6a149054280b005203d400d1002c0d004a910807001c48540008a034140204d9039410749612180304820301c040c41c0c1b03004c4018064119011030661000c245551920b9030750603030710b01040d00c5414030300c0c1031900d0009090010341c14544490030317110755282a01d040c22448030411040380b48410100150080f0780340e40d80030b400c00f084603500642141e850706118184915209828009650f1071802142c0f1288071810034000d03102400c0c0c06840f98200c03039403948040005440000c10854040301d007603410780c100e0fa454030048940c0c0080a03900050030312b85032520503072119001e0428074880d8090718402c002c010a01c82100c1d10349521200c6500c030320007000030030b01c0a40039500601e50f0041c1080c41d080446607001001d485122010402800710340c0382d100060386c4a400324000e01001400c4a0b071682c40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 863536708 1250 863535458 863535487
    0x1e0a030c02041104090905011401080a020d020d2405160806120f060a0e010b030c0a05130b06121504270507030602030c071b0509060405090c090c0d060f0803 69
    0x59140c00a0000f0840c6140c042d03252007154066000352008694a140c6034080c40303400d1040038018044d9131010703031882d410312035074990700c050256000744140c600c0300c5804119110242c400a01c980c2c01082c00452808401004054070340321812448050324000010340140810512281081680c2c1c0303d60305152078110038000b8100c00c1107011101c0d840b41c0c10301c1c1480d80d801002118440e0305400400584007441c0d95216082d1160380040074406e0f480001100da0581d903451074002110b904807004a19148107116030001740004450280c1e20590120f5000301c1c2010049040740706103892003143c94009007000410084800e2001501200b10100c161000c0550320b401203070744500d000d030701103500e540da0720794840b41661b00444124240800100e80035080050f59500d00340d007030f81107401e8038910908160105490030001845144070b00d894a012819201c0180a060b090090240c1020000e03d440359854180307034084220300c2c050924040300010004010350b0240141c0b003000c00a1840c240c1c5080e032011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 863537958 1250 863536708 863536727
    0x30c040e15031203010515090922060906020a121503020906010509060409091101091a0319090606030213060302010804060b0303190c020108070f081602010e03070f051e0a03 76
    0x444a807020014200c40e41d0100002140240104001d40e501d6042034144a50540c221407180e1003d02d05025400944d5221464240c0c410303035501400003016101d64000010801e5071001902183c580103940c030911209800030118014141c0341d0780b0030400f42003460011903880441403440c1440f104814001850030000384e0ba0000b4052410300d08004510300000d03500d03400380e4800a03205035204224404c21840b201c00b00110a024240010b600340351050707c0302d040440d12400d50300910008000344c11441240315801d41c0d8015410100320401c0a440c0100c004c0641d40400d034440c1c100340412a0200710305000c2e00056aa0680d600d8040d40c6441d40d03203101038800404040e50601013070001c0b458154022a11140b9004555500c0c5020304260002510806024040c20100704207410317050304003500002c0d210341060000600c8a0700342d400d010120b00411005544403030a000000b100340a2104141701d20840e14041c1d025501c125100030580420022030580446a54100c8101040468020801c88 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 863539208 1250 863537958 863537971
    0x3090d020a1d06040501060c050304031e350c0a0f02040e0a0b011703070f0b090703061a1512130501020c0613050c150405150d230705030c040e 63
    0x464505860b09900202c2c0d1003510320041c2107645640c02c110461415010745030040c1003509065160864540390301d5203911a500000e8256803d40c890051400d168256150300c0396004140e03071000e00d041d01c0c4a00491026491400030405800fa0402c80d6810f5080c2102c90b0310000b1f03030050490604554500c070140c0001e180980c3e03c90354460500e01e52907014403541c600140b06091010b090b60500c0021201400b0f0741100c40c0059005000400c00188011034222844d604010500c2185c0c0d10504618a00005908028095401d05400c1070080000c5500341c088058100c0e1082d06002854103001101c0c041c0c0a80184012002c03004942d043c401c1d541900700e601d00400000d80b07458800200d06141010a441c85c1d4100082d501b4880d040c85802c0c08801c212401c200c880b01020f00f02c0c281c20082d00e01841c003540380b02d840751071400f0002500340030440d100c003485210240007101c9040c11005c6914200044803e4001d1558005060b42c1c0c41001100e22a000c40e03614a0308283c100b21070311056142c01042c4d07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 863540458 1250 863539208 863539219
    0x15031c0306150507150905030a080901150608010518090d180807060909180b07081306050405030310060908060103060209010903151a10080c0703170705180906010203090d02 76
    0x31803072403040c0e90001000c082c2601c58550310700b41d40c544a000000344888101d9100d14003030700c0340d0008102208a41582e8124a8124900c0d11040c10317007401003000c804030710402800481c00141d00c64012021904a0310201d9078001c1c10303074840d0050b5608207800c44010700030780c2040b80e03640ea00e01d014040e1203200500e08021480c016803034010641c5084201d80194000c5901d0100400220782c03580110185100b601c0100102208141d442e070b040390b10060003920600a400c00050000018540c9105905400441c00c1c400b504060130300e42d071a0792044c1e4054a12032911000403900ea8018a036010840d010340000300200e0780385445800080d000641c965042007120715001000c18188507070700184104940d0005400400c10200c96541d0700420384141c090404452200c5000350048440c075400b00030b241c00556561840c0c0303401c64159248281402d080d901510074424140d60020141801e0f5030110103d24420f6000313400c01c11441e10071544070780140d108202c00146401d10007200b508040c0b001d00b1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 863541708 1250 863540458 863540471
    0x30203040e070e0f0604060512060105160606030b09030703080403320a121e0b030f030f071109010b0a1d12010903020606090103080f072604090515031c03 68
    0x3010407103060a42c0e502c000590840c5012500b80f80ca2014014003040c100e44244c505407806070003501d00e0044d080e90004140c0f100002607007a034003c008613441000c0b60b0000c410882071501c2c1c080d0040419010076201c140740c0400003241c150000040324040b03070b0107440e9080c2a0350755035012034080445a0b0a400340e481d545d8a00440700d0003050001000d480303006616070302c6464103400100b0810f0710000002c1d081d4140b070724101c0d00d2001160004490341c4240c0003c00c1400e0034201003803408001030100b29992200003904a0344007010000380c202a44038680305110041000700b00810b00c4001e000f0180c015400b0401900c4060007001000c6480f00000040407010220030001400c003201c1020313050f4940d4490151208069042c0401c40c0c0c42482120180c41d6035045444184160060f070742da4580340100059601d0510407200d41025000241c01d00d1039401e200d0100011205803c41e2240d1f804250030400400c40503902490742d030161140250080c0543c1c200c0c21f5034920289000e01000048c03542e20701 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 863542958 1250 863541708 863541719
    0xc0203042603090d0305220602100c0e010c0305070c03060213080606031902180702030406030e03030f1b0c06100510021506060d1103040c030b0108030a0504060e04020f0c0109060501171903020304 86
    0x780c070f10114201c0c1204222030348e2401c4006070400c040616041c0402e490914000e044a41040a00f0456407080ca00082d10210f203260070b07545841400b1015154120b240d0dc000100007142d0000c1c82000040f9800408803a03075105820b03074402c0103445265041e000003c3d040c9101e140901880c02c40341c00107046180340c00103010b4842160308240d030b040340103810014003401019014040d403484201404015451840d0188a070710499502800e21104902031000070318901c8245401d5800300b42640e01511a1070800741c0245d0107103c018441c150184580010f40c45506001090315003000c6030301c142d806000d035110700410115a01412100b41e0880d942d041054481000101940c400d510440720b095605055040044941005030302100e05940100481100d8a0b80002600d0450300d00e414061100a80030f40018003070f0081d503008001904000c0303100e46502c1c005410410885005020401003641c035a404c104140e19103424449099003c48000e00e440c0d010525000d901074003900c1a00e04140d1900c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 863544208 1250 863542958 863542987
    0xc021507050708010c02161a19080103020f09010e0721060b07200307090e01180503271c05101407030b010507020a0e0a09060c0203042603090d0305 65
    0x100c0c030544496020395418000d0382400d108010b151906400203040781c0760b804400c05c80c921214080e81c52044000881200c0541400e03059518115011400075030324038029200500205c4244000d82c89103032990803020690400c18400da050710800d10320350b000c0303035540e20040c0c40440743c00c1e040100582d0060a8041800c0700707841a0000382c582c2000041d0750350224180032400040140ea00006003811203006800b9a500040d0042210401180850450450762610740103024030489510311030380c8820b00c1e100f04180440102151514440341100082640126801c0d5032400d11704039801c2003e030322409801508500c41045428440c008440510b588410b100b0191020450108150002031040c041041d4150041d990318070300030300e0300c681440c5d41900018001003c500c92031149206800104400300c0300ca400040d05150004018060301e442020020741c1e991151050351141d090481c03e441c1007546041003240d516034510021414442c0c030104202c3c140c02080380480500208104004625005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 863545458 1250 863544208 863544217
    0x1906020703030905040c050a1202040302090c071a090712110409031815021e0a02090f07020f06040807030509030a1506091b0804060c0e09090c031e0a030c0215 70
    0x5a020381403a524510b00075121048541183c0d10a6003041c0c0040034482d40501500d04803601803404041442d140b02251009105a07040a504061947c00708164143c3c41402806814072074040c451a519107042d0f0b01c051400c050b0f032080d0041d08080420481c1c60403021605000c14010b14001c1004248400007070100e071840380c812000719840100c9120444c0c6016030280c01031a001071090607007510074a0080d00d0300404908016007034003c1400700082c0e481000035001495010740000c00d68207000d2410004401c0840390f000043c4907006030f021a41501051081c01542d20189503818941c0d07661701a2960f402c84155603405110f40801740c0c01041c00700390b12125210041c1000510107003000c540701d040e03035000343c40074450003070820f4202c0303145500c05221580302d600302c00002000c4002807400c541240442d480b481d40801d1010078800c0455020403030f41c003000c41c100c044403410b90800400e400300c01d8440490788150740001601c100800d01a0070700018840c40140308195000700781d88008941d400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 863546708 1250 863545458 863545469
    0x10051210030611040e0c031b0307021509070e0a020c03090a0914070f0806040b01120e0f1902100f02010207063b07121a07020a0b0c031603020919 64
    0x600325410014072610b031050209102c0ca92445900d03290401252103040030000d001c04031007000000019411601c1100c6010302400d4610015580b03040aa400a6590981c0e00c1c21068542d180d40104100310700010301442150b102c04044041541c82040c920001e410a000040c441c3c0010448140199034900c4640040c094841c4c00184415240141c1242c2d040c00812400c10b012141c54404007580d0071000392640110101c0b008550245c0f0030004880c001e0002c40d41110940c02e142c0d4207807810710040f64450800b280001101c3c10481c422481b035407600c18291020f900301c0c8641078034010152184a1a9400d40c16a000241c03a00d115545c4420841d20b43e18a0110a060090620308114041024082001d0605400030348150000f00b0f43c640c60305011701c80c448480b81041c0c0c0c40b504002041d0b0400901c603c6100d001911841e1000000e91070b2010011308982c8043e0401c0081d40c0340280b401031781d0180d01112024041620b441e0740540007540510132883e480080d0704500c041030010403500303101504 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 863547958 1250 863546708 863546731
    0xe0103060507080f1f05100c1b0b0f13080d050403140708070612090f080c06070507080316020a060c3209191706060117040b06100512 59
    0x185541446011500040e10310002c2140c00302c280903410400e101071175000782540021024003410940403613006203060b84a01e4000350302000c05610241c00c5005085818060b0b100615024104400c50303100d8602c41c0a4690003d0050140318a001c42c01c8020f000100e0014032511501500c60a08138034000207080c0342c20000d08000780c24000c10044942660240700558000c000b11030629951540350562402802d00700b00c0740100f91072500c00c4541041c40c0d03c030707004040c051101c9110308100a07540d020900c1c01c240ca1195002141d010380c41802200c1c0c80b0391f08107034110f0079502e9902041c6010240c03803282da011449002c1c107100202e840c9120362440301282d621036280d10180004110b9106a06c2800640c0c00c49a400c2c400d08886250300441d581c50301c0489440001480456288824407000d13000400003801030070000f0256071000403400e0148009894042200c1c00c882c00150885008480c020701502a100120312981040e203015400c0c40c1d0035003002070425100d04010750081030115031188424 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 863549208 1250 863547958 863547961
    0x4090e0307021e1011010213030609110d170a05040308030f0906090708150c040f0e01053f0c04150f0e010b0a050c010f18020405090d1d1305010e 64
    0x500e002603294654400d096550440f1103204000103444443d1561300000340b004000380d00f241403a0039812036a03c01c02c0445140350140d00c03070810300001c01842c1011143c82845502c0305a00f842d103101e6608200340d108a41002d4030364006000c0c000394024a28500501c0710500011000a03054806548a402caa8155110510b001c031003161400d40c02074a50a403540100340c007405000c02c0807035140c0f060b802c40d040a41041e22109440c001c1480382d0b5002c5c51120b00e184a004c00d0148e410346a45048800c200c90742c00b42c22034688403039100340221241c3d8244890030350059034400d4900d45198a860b45201003940c080000c6030020409840d480400b00d0040c002100742840448108c4450034041c12400352810000d40c186080d6910f140315002da0902400310120707031189400000d42010f50100c4c1c03107001c1402220035584a442004005600482c855410100020625040042e01101c160300795a500010b400011054402c01c0c02c100400d950000300341c28404107079440302c0c003605008140224000145 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 863550458 1250 863549208 863549213
    0x60a081906050f0f1908070603060605091c0606031b0f080309101b08070b061212030106051305030111071e0308071b0b150f0a0e04061104090e0307 65
    0x1210315458405044501d0400c040c465511592818607030180d040c1d4a0150380c811100019039115007008150607403041c0524003007210a4046110400c88a00307807230500296440d4102a9081d0054050294200f90202c0001c01c1d8401907a24103401d10780a641c00080c61500d0380c44504607001c1c0b02541c6c00c4000800c80003040180c4e2070258040007400500061401e01e003880c40090071001c40c4207190701c1000700c44200b1076030300c021120302483c0c41035012204940d1407205141800700d03580b007201d0041c07243c0c250b5070501c40d46442c0032500c2a4a05022000070380786a0030140c003a9104d400c0b010700711842e0103a084020a250300d0034403e90030012010a0742c1c07911100f8618281444800410f0700b0b402d8640300300305100000350020180d40d08040b280c108840003001d07132420300c1c810049a52014040c00d5114043c170000504124074540f2481d8203581840400c001002840070705502c601c145140580c5280000780402d002e80d02007241c0e003104007e01c502d080e5072642c40c1c42c250342081c0c02c0403445400002d00f1104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 863551708 1250 863550458 863550481
    0x20927030c070501051e1c1e0e030c0703080d0b18100605070506040201030b01111605031e03040e0a02090d0812010f05030a060504030210110408010e030322030c02060a08 75
    0x242002d207865482c0c070070001104d078006034018400c150020310104920030700400480c0b8400c401f840c81c000801480044181c4e1142060409903a044100d10b004120240302101100302c40d001d07501d0900414885185a8400d91540e002d840412440390343c41e5081001030713540e2102085211311103404c21a240c184021140c0e500e81582d031001080c400c081110100003540070442a078480d8090070000355030200030005031030403041000c41c00b01d1801011501105426440100026600d05074111540c079080292032020000710000d055009500501c41040304d00e501c449000e030310140b01c100160512003880d01041006511102c01c454021000c210003408036042407640d401000340c4441030190500d08004241c0743c0311498409401284c4030000902070500130010301240a40e4888104408515180d00c44420f40150098134019404c2840040390b039000041600c2c0034400084801020b00c1e00c0e03d0340300507803e2902e13100718140030200038070b40d0140c1c0e100c002030042c0014a4889144034a01a40d4541 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 863552958 1250 863551708 863551723
    0x32003040b101503050705090a0305010c02101e0e240108010e0a120302070f0215040303020114040c0b0c07080d0905041d0d050f0f030a0b031612020927030c 69
    0x2100034a9900c2c1c104940511403010000c0c00300c8504000416444140781240e480c801c21003023682114101c1000010080e0540c84014105010380c00c0da85c6640e00007800009490313017203809100c5440c1d0b0b540e03448400ca4031f6a005000ea056104200d03070307009540326459401034900c1607032142c0e0100188010810b60500f8000c0d1078818104102a0055041a039501c068100812688404060340401ea03802000301c11680c0000190f0001c1c50854096a08134014145900c103000c21030055007003404040030310b0145a049405142c0c082c050310852806c1c01c011070119001900201d280384954140010142c00900000d5501b9074a030b501d108902d8244000d1005840c6805400c440051200000300308840d004a003c411b10f13a01850201c1c2e403140d182c0c100d5101d034014030400b148001000018000c100c0d46990041d0074440c1c0c10390584046c0781201401c20a00e03c1c0c503105046a11551045003001440c05075081a4800c000400b0a002030700d024015001240e01140c0d00011070f880082d500d10500010007002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 863554208 1250 863552958 863552971
    0xb16020d02120a0e130b1302030f042613030c05240a0e040e06040b010819020906040207052d01020901050d02070203070503032107031a01080601032003040b 69
    0x500340c045004400070b548040c46852515104004241d00c10464400c0c40210850080100100140804441c40c00000d0030310607005440b40d1711075203603c00b6038815402a40e120b8400454052174507a201c3c1c440c1d1801800803901605001c040c8441e0a03142c070100c0d005400d40c40807503014046590b083d882c0034036000a154010611070f600500303061050003480d60100c840318402040503070b200c20300301f0030070760b080300c08070783ca0f113070700078185400803091410000320703035100d103005e03454101680c2d0362107400b1500c681a1100190004200e10b018001508084020b1130b040213019100601d003003020b85407181050196001c1040480790200c0303403005003c1350b0304480d4448000e44000c51814103a040064003511446102800e810340101d402c42c2559824030004004010242c01e40e696180a44000c2006940844400e500380e9401d001090219100e80304000450050300041007510303051000540701018000c1141e4105070301d4980d12a004000c646500000024040079a5181e09051400c0d18039400001e1070b4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 863555458 1250 863554208 863554213
    0x1c02030618061e130207081903020a1b03090e0411010e06090a0e0a090c06020313121a13080a0c032a030507050708060c07021c0201121a0d0b1602 64
    0x9000c00303683d840c0704074012851400c002c880058402e40100391140c40001445008500c00300c0d00754148000e04004040300d100380441051482c203521015030072070140c80b0010001402c1004402e0b0360318004051010124000d080425410340d844000d4070140e40b04403812214048406503c48065810a840d0b2081c0300782160541d0400d41c0050206880e4070701840f4080c4007014210102d65980d00546c0110200364000c01503100c403030749800c4060b41c2d940c00410010860710354101c0000d050014014076a816a80c41140b88800c0b410328a00e105142030301801c51080558100060000903104500404203500561a4041004010709020b0400382c1c0c000d0002103480070300c00314040b13003041c0170310b01e43d001d5907050624546803ca00d0503c0c3d890300256410580361480f80c0c0051204032100b40c40036044c110701c210b603005000e0301d40321403181e10175800c0b010007404180c002101298184283d0448001001115200b80545140320700203140c81c1100d2006540c141c07002c01c00e02c10290149602041e000e20036000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 863556708 1250 863555458 863555461
    0xa02071e150804082502060c07030309080604210216030c0513060b040605030c07050f0c1003150911160b06091b07030c1703040b0106090501180509040203031c02030618 74
    0x203c900e218400c00b0b80158216145a51481107814007400145ea0302da005498580c4408440800c01d40d45e0b072043c0801e5000c00c003265000103111f5000903459120740c0d03000107d0305139581140c45520400707c94a80c140700794000c8015540384141001011002540240000f032600c07440c5c402030114041d10000000280d90800c2e00500880414108036800c5030414900281ea80d80c801101800c0b034002c00c14002c000380528a004060040700080da41d017445011038050590b622000030503001c40e000c1106510601c1c0001c02d0401004071181c2c850400c240c281c0808510380741d000400c0c0c1400e08621030007180c020a0010034007a45040c4040707605e42c00011a1f00d80700d600347c1c0b1201030b04035a001d21840181000100460001001070410000b5081c5a01022154030703030429140034025403800340610000100c41082c00102d81d80316202102c0c00ca43c90240c00d194440c24603060000c06200244203a0300f500c01003014007140002d00c01580800b41184a005071681048010018406001c11086005885100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 863557958 1250 863556708 863556713
    0x1506050a050913060806010e070f0f0f2d030e07150801030f0c0e070507021f0f030f14090304090b03060403120b040905100c0323010b0a02071e150804 66
    0x20200d07a200745040f203400008070b420100c058050321007a0811700c41d0313010328000041c2da0464400010f0081c5502c0e2a407503017105417000221075070881c01c0c0d62140010540c016030b600560260310b001c1c00e40892803680540746550980030141d8820b840905100180d83c0d140c00540f80c08051202d01c01038038007003003201600e07907201100070440301060201600c6003440c2407080782041980550340740203052454801d0b03242d15202c0030180c02600113110030313805403100040c00c501241c04001c006039800e01586649a841d002260124010000c0c04107903e411643e40368403c0000500b0703070f0510b1041442100a507540c0c2d01380800d08059461000d0344074000d521040c140000260419007000360f100e044000040d00c0054200068054044140050818050010401500070081c1c1041c51100e84a13141070042ca40703200e01c0000f851705800035240e180101d240c014498004043e008010340c00f450710484500d2621440c0c800849042d41001c4420111100c0303007000700f181842e031104901c0101d03003070070750651a01d42c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 863559208 1250 863557958 863557967
    0x3060f0f061201090c030c18060f0b07031b08040609090203010f1401020c0d0c140901032a0b0c030301061b030c1101021014070905091306090807020301050a1506050a 73
    0xe0180e502c51902100750962100096003c00305154003c101c19010039075074245030103000f11a008075000b8403007030740b1307010000d01c1c0601818089862000810341c40624100c00c071450754002040880c1004031410030410500c0760020522800382c003c0007040d50721880c04002401840096002020190050004000200d40c0700100022036405520b548900c26604004134108600300e600d139a8040905200c08041c0400441448240d030705454624038001407000411032042d00034840203080101c140112445840324101c03034048090740301ca003a607985464100104a0fa080660345904030352000c0010008240c0c001251200918000307040f1201042644006084d140e030544081c00c58002d0845201007070b4400c0010090071483c00b03808025204071000d0811801c54140e0350354000540d0303200040b40d070b850003165040c0a51046030800491423065641e400103405070150640303007407100707100900140e00d0a00030144151010f290000300c056a9581040039003005404c1041040400d010000d09035401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 863560458 1250 863559208 863559211
    0x9020a0f0c05120d0f0507020d030b01140412020609090901240302031e0c0a061e0516172a01050f06010203040603021c09030815060316030c0212130503060f0f 70
    0x21000056660300000301c00c0000d0010417003510340031440d0200300542582c3c0400c2e5030710f01075500c0d5000d000d00c4000ba001162144070342c107425001c0b4034080004100ca0511850205400f500c06000c00b802e0070b42120014002d03400031614030903142d4448240d41c182c403c07103a00e0442d65207130600c1c80e800c8103811a00800c1c1d54081d9110045a4450414a6401420400c00c504058504024007410350030f525404001c0103540c080001c481500c034118010034803d4028426102d00a001d488190305601d138030b40341c0a480c0084459070010078081000f4661102e07001d200e114034000144107110b035080da41e5110031030850300020880d0102042d400d0900c46283c1e408030172103040328900c3c079001da25100b582003d0301500c00703c61400a00b06191004075010560842502d83c460f00b080d01ca8550198554024001c02d03110403220309440404954901102a00036440302c19090b0540c4100e8400b881e008904141c10340c41400b207421481281c3c2810002460304004541e800f031103000e000c00650908040400c1810700 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 863561708 1250 863560458 863560483
    0x160c0e0f1303052505062d062b0503040303030212090105011a0705070f030f21024210090e030405011b0f320c15090a09020a0f0c05 58
    0x207031303241030914107425512080b482e5820100b92079913400c00f07400d082e50701e200c2c00da60900c01d0a10418104001d010b260000c500c1400003814041124060f150582a000c00700d2018910086002c22008003045040000d040658440d450040e41c0301e50001078a0203c200c002e00610b4030380c7c14480140091001d903207905c2502c0791103c0e5400c0e117801e02c0d49482414400700b500306440740050920000140b102031704580b504107005d04591400840d0300f40c180310320505120940ca015130300581250107d0140e107102048104020203100c961010030701010944200d00034070a0f030345500351106110200f441245050005c1640e100e08100c6620524600f903100c3c021403280605001c1880300c191042100c40c40c002e104c0720b0740308060b0000c420351460114541c1c0580d8501404a03840441003000c501c0f40c1c1c800c60482c0300071050044c124014908c0411a103c00c2000c1c694240c40018000f000e050348030a40c0680103051046405601c4910400c0700416909407404500101b000d03034681d0501164002c581c8404000307 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 863562958 1250 863561708 863561737
    0xd2307150b0a0b0c061e04030e091b07150b10080c09150703020303071704051c020c0a0e0105030c15070b04020d020a06110d0f0212160c0e0f130305 65
    0x6040c0056804403095100303c41c001c200141d09404e2810202d8981d108540c00d405561074078024610b44c902c801e800715401004071744c3c034115424807881c00780061984414580b80003900c0d00010004903100350402e0500f1941c1011007030100c100c00d8610b005c1c0c02d420003015944440000103d00005150020207841c890742d8501c0020200c0306070f196003854032501e50710b00002d00e54030501c901d0025560340c021110200095a21080a010310780c04901040c0560f4118000345000014007610039440c242c4500f074981035103c0c070710070002c40d0740381d4540c904001c241d400c40c4440c0e00e41c580b805050520038032080d641d00c21450240720640992205099401194100d508040603550f0751020403454000e100002e94071240c0c4640c00a07000d6070141c000704c0d4a0b50b815013038411044542ca0183c0c0c840d07a1611a00000d0f0f08070500300e8031845114000742014082c40c03542560400310548070980c0c1004203411411018460f1410800400c1603450071035001034411096041c044041c1e20018000c0c0901183e030107800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 863564208 1250 863562958 863562971
    0x27020f031002030408071502270103140112060e070f17010f0f02190810140102030d0903270602060a1a030f012702031203060604080d230715 62
    0x103440c204951401e11014000465481c00e080c103000b0029081084111030380305104400d401400e110340240c40150b4412101240501c50700d40741c9820503134551015038100740d40c8403500c00f5200c500a103283c0c000c003070010004010401e00e003480f40aa620070b4005000341d0740010010001c0c1e0301e044001004407401c400005504400c403401040c05800c0c011102030140b828450403000300001540207011421071080d14814a1001c11401d482500e4119075800301403854103010802c0d29080c0a45200c16001441030b681750400d454080802c4071803035041a40007515a0859801c030804201c902070708041c1a04850707805900d0100c0c02540c80304000d0614003090303241c0c000342002d0080242d42010003a03004080c2d42000c001085098001c003d02c480d056002500800c0e0f228079480596414034580307070090041c00e016000c007000340d03542d0343c406006103400800411000901941c140100042d03405603035641b0b1840981001c0760b1840040160018032520303c20440c11002a5040c00201c0454034126404100d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 863565458 1250 863564208 863564239
    0x90b03011b0f0f02010b130c17071e020d08040209100803070503130506072f030a1101120b0312031e01030f021305091c0908160302040f0b01022a0a08030304062702 72
    0x141188109c401c0a5007100105100311507070405444000410a051030b80380d00c2d040080704a070b4540302008648046100107000c2005401d10300440d9a105425540389940c0d580e40d212070310300d16031200000340c1d03043e0000f081d4015000c0e560500340000304021034056041c000b072915200c0003c00000004a5510307801c044029143e5650f40113401d4880004082c2d90b110a12030810b86203403081c1410450014000842980705100c80703200c2d15030020b030090b004120b00383d01c42c0f980459540c0040c06800400505142425400d01004000d9000c4c41c4074807402414a802071040c4119085040e4801200606107001c02010341c1c00014a50707800c00103000c44020840604100b03444103085a04008524001d014000b541c8a80315545001103a00c2a1400c01152441038064030488241c81706032070050f088031880300001c0b151a0081034120040c04031001548004030001840b00000e0f40c4a40d034682c002208000c1070119502c0740711003070070079080700981484da560b500101480b03a10350001d03c44c09801502408 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 863566708 1250 863565458 863565467
    0x8070f081015080906010501020601080d05030c04050a150905030c0108072318030606030309090c1819051804050705010c0302251802040609090b03011b0f0f02010b130c 74
    0x826040c540018020051007004110f00421900c64009100d0900005440e52001030098100d030490409445a0740c0102400c940c1036002500b061034a5009001c08200c59586c40c65050040c00102021145607800304005004200c65500591098101d14240380c407a98002ea03a079503100440e8944400c410007080c103001901390410403901032903400420544000d820400c0f0340e88101ea0110100d852640e20a000c2582c1e0744a00d440d600d4110401c1c40110b401480514060003005821450307541c0442c014501141c0c000d03001e049800ea00c03184001c030030402c40c28045640c0310540700d44800c0200516117606ea160780d44905100340390402091500700018940309100c001040303034400000f40091000c600f0b0240d404071403809030440c0c004451110060f001d0070f901c2140c1c100e41c06030301c0710440d1038503092005000f8180b0f4007555400d075403030700000c006842d100c82404100443d191038640060161480041800c5403604030718003968034000081241e6a1251105002c01d030700c03184040f60510305c0c01c1c070899 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 863567958 1250 863566708 863566741
    0xf0307050d0c020d1b1a0714130303030605180114010201022116050307020c0906040f050f04060506040b1c0f140309030d03060b1903020903070303030f0c08070f08 72
    0x207214900e058003070142c1ca6070124900100718015a190a2581d000c01a48129841841c00c0100041d00380082100c60b8138040d404580d0103031560800418284038000f8803c0303282e00c050400614013808030000e00030150584100ba004d0b04c402d8849620400d051070046502c114103000b1040e850f111920391091580c400d40407262048461003046541d4442920f43e80c1c42d454043e070f41c2c03064440510f0182c66089101c0c2003681d203e071211703a000f02110300c0c00340d09124010301c01a15058029407a01050a00114103024050107420f02140c825450700d840c0c10110222040038103140e1155080011144035035603207920200d5800a0000c0030b01002500380351460481404950081600e48084a01e0100381c0010002c0c0c40c080c18290255008a80090800c80c1240d44034007035080080428000210b0b1115030581110740d035101c5060061612845034000380c50405694401c40001e51656004000d410160080c2c10f4950103034100142c0361b0400200c0948180450349a40042101c5180010702444004e40741d031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 863569208 1250 863567958 863567977
    0x17061b0a08150d14061e070806030a0605071e03111c06050a0e0103060510031e0215180a1202030604020d060906050708090d2a0c081e0709020a050f030705 68
    0x2442100510b00d80700d11084c0d00c9543d1420280a01d6000501403048403140b0300f01e880310700b0146140f95465031025100000003504207a01441840c01440025a042c0728080c056a056202c41e030816140c0d41040082c0c4021a005600300741c109040000b5465440d819920081e80340b03044d030390b00000c1c02c4550000501d40d03a4040e0394410740390080002c0e110400344095050b2401400c0a00441da20304066004102c86448010f2130240008d4950702a4444000c1c40c403221840200700d01e1041c10780d84100001900003080c40c40e40228040800140e0f4540744030304800a0040311403c55405a6903000680c031000c00600107401021640d8a103070400000781d02a81e4440e07441a070801c158204440b00500c60074046030310108500c5040c0701c81500c54000e601010110010005d800140c440c501014900001101c40880d411200500046003650050202c40ca5103880902d0750340031803001112103454a000c581c01080325910400c52100380c01d40c41000c48149221500c2d41035604c1e11680e404880900c07541440 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 863570458 1250 863569208 863569219
    0x3030421020a060c2303031501030f09031110091203050c0c0d08010e0c09030a031202090a03110301060f0609053a11012c011817061b0a0815 62
    0x703d41960000d076810342c11070107001564a904420401e00505031000348100c0281d602c01d2000400c5c0c08400110120a42418500802c00c080a03012400135185008003c40101e8080300070300103940f00c1005145610424803130b0a00440225880b0041e0580300c46112204240c0c1b1000061b8807454650111610a001c5004031a9900c0e030b03514000b4440d03202801030049032040358011030f41c1000e004054800000d00100035080c3c200c8150340a40c0d0001c1c10117158407189800f40001026a40c4401600c8000d42c001c854a016a03c0410308040c02c681d025000035081c1040c0c14014440d00d54444100403c2e07034010f90f00b500c03c011180d1a040700207403403104284a40820302a0701d41000f8101d1005100940c441e45c050075661421100546e1120400a2510a90401c0d450320000c4006001080401e00006040c0710711008084030351002c3c1150540c004424040f104020b004076013108011055002a401c041303240c1e00040c01400b40414410a1151400c005071240032806240031401e6541450200608 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 863571708 1250 863570458 863570479
    0x3120712110609011b09060509130e030a020606040b01111e07030b0a1b0801060509040f02070501020c1c0311161103031b010e03090a050d080408010f1a010e0303042102 74
    0xa2407400b03840c5c3c2452803d0481d0442526895483c0904da4a40c1901c0f13042d00c59605015031030041c008000442c0604550141c0c8500206141c0202031004212590f03140d805004985005e40a01003621094107505041024204002c5400980401e480d11001d003e4115481c2c070009901b0301c2d514141d2207800c05448003100b4014000c43c00810380c02500d40c4005000341d0740002c000d944058078500c1091107900040344040040201a140c1640500954614840e005040400350b03150780382203821044415405901810481c030b2a03a600760030703242c181c107103074601800303a0105090000d00318010140f1400000b80c8602542e42081080c50307102c0b0081c100581102d0b01c603401300b01e242100707403480003050007035518105000301e42c200048104c9503115400f614070f0141c02c1c9848203101104010381c1c410345202005010100744041d0a000f00400070041da0700216580d980b50003442e5a01509111003418080f440d0348800d85910b000c400e540890f000401884221b200e4030150048a00c2440c41c029480b103682207 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 863572958 1250 863571708 863571721
    0x30203070c06081e010b0a03020c011404030f140c030d0e031b07180b030d050c0703080409060f2c1302150d0507180302100905040e0604050c031207121106 68
    0x1183e0038419841c00c0b1206a843e00a00c1407010300001c01c1c021440c116004029003d0340368001e030020130781d8401900000900040b441103c3c42c24038010744040300061607000703240d80602d510050608064845038212813a01115040240e681d00c10031605030a0700e83c580713228000031102403058940f21040040010300013405048000c0c1c031441c40b8080c904282000204010b01d01c99244204081c00102030003d01410407448401d8030702c0c0e00030301c16940700d501c10742c0004030000340040080c0000b0a940603020800342e040030400340f4a40665040941e2807450540c1f610034040311120022880f013006140003500c1e440300e0400524402034890003a401040003004444144001801040b200c02140010001611000c00c110b540719801c6d440e44c1c40c00314407440c0500c00f525000100311006000350404410943d5214041421356121120f148559080743c8100001c2c010180240e2a140030f0403006000c030448100440c2c07005014a89014140288203c0e60800d4107003d045400300c914840d000b1030310301c1e10303040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 863574208 1250 863572958 863572967
    0x3030f09010c08040e1e071b17190804021c08070201081f030b0a050901060b040e071e0531032006070c0311030613030e0a05060406020a1b03050d0c030203070c06 71
    0x441040700181c0203000084640f17104030522301e070218101c00d02c0c5505c0481515042c00581c00c030b2007040c850750310801865090101004103200c1c50015501c500e1803614090040000e0b664098150b2604400700350036080006032298201c8091542c24200084942c841b00f4034660360b8039100c030303052001101a10020050040100c02c84d8400c4101712000d1100d541d850000c1826200c4520560030481000e10040c4002d80c4c0900c101503008042d0714002c540c01e203a0006042c0340b200e0303c11b0b00d1800700310300191040400044014020b05540030104501c10902a4012003003405200d10000d4001d5084800c080c0b14542d0708001c00d81032240060205842e8100d03070410362001d42c4503120880780301c00c100b072040000d8100800d12921640080d201204180d04070384003604ca5540308018a81c0c402041400425140d071404068405000c0990040544e100b2610344227541c045506c45048244001550070000214001400e0340b100f410743c9071401481401e86016455405000001400b0240c00d141c0802c0700c5510 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 863575458 1250 863574208 863574241
    0x80c0a110615211c030b220f061a0f211609030b04060b0d0f150606020106030c060c0302070e0f07081509160e030f030406020c03030f09010c08040e 65
    0x12103200c81e440c8411401225402d44a00c50700e0070680004110190700e01c64604e608010311030034140810360324135000c0094240d100c07428001411002c0c0780034030301c072844c1c8a105008000043d07481c1041031504200102400380c030400e0f9075020b038140016240520903072410a1303c0000c181d5207559205c20190811641001c841191680e5424482c0340b4903154452088490f80d003120b070410b0807000c440d00c59032220009420f02210260700b0050001100c400074854011101d0b000f03000c2c0e845214002c060700400800d481003a03016008580c101a42030011803002c010b00703802c4034441d0420f040c503000d09240507400c00f211580b05008802241041000c505030032030016100d903019a907180d140d50b403025040a00c0d01c008510540c1c0254002c0002081e15240c41c890301d40000c0030b4107085851003c15400289405168420201e00703800224003000200d80401c01032000d81c500f10091070601032400d00100c224055100756a0401040e42060001d10440c1c0040b02d0152840305900055407800350442140c0070355 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 863576708 1250 863575458 863575501
    0x909121605011107120c21030b01030c020f1221010f0911040303050909090f160f050a1a030a090c090b0f011103090d141525080c0a1106 60
    0x2081401c00b40440c01c0d904513480c95038003480580409454110440d211051030201300d90750b545001d524800c07904540c90350351720101144da005ca1000510310004041e03a00090141055500055030707a0312250011850803900540001081e4860606190801100c202c004d500d0180508060001c910f8031004c13030254040e01d0a100701404072072014483c04070f040c4030360b100c0500054024080702d1128034056007515000300d084021181d02c00340c5207101c941081030700f058a11212000100401203041003030307500760080404956848405142c4820750548440345100c555921a002001410408040e44050300d190f80002815604a403250807031001030030741240c00c1d0320445407140400055803040c243e0115400f0307000061814000d02da4240411145042812036580c0e81402000d100e00781c0401210b26101600d03407104009007003215240c50300c3c0c803072a0400101c841c024441c9056680e0400b448581007240c90024030b54031140c0c001c0c210390b040c0210134091613034003401e4240080c3c680c041002408855 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 863577958 1250 863576708 863576711
    0x1e090303100b0f070210030b2101050606120c03131203091109040201050414040b30030901090e040203030c0703081b0a1e02130203010602030a030506090f0402090912160501 76
    0x20380b24100d00600d40035120f40000300280400c0301000609103c4941c00201c5241d04001c500309000d00b002030075801404d812841440120f80c10b00741904000d0240c5500202c042e2810352038041c4c00301d202c4640e00c40041440c40c3ca42400800b2038042103240c4440350140c0d4110310306c100787e06000c10000b40034142c0c452055a911030998201ea0480c40c0c0180118080d0394141c40c0c01d441e0524001d4103400c0d5071045000280d010b50744211601207a1107040b03912601d603080304c1d405181c41300c0085001a608540d0f082010199009010100559801c501074405030b07194040d02902c103075918030000b451441000380e0440e51b401101400402c002500d00038020541d1494145038a120000c50850340d600004880074000383d40e0000d50000083d0070142400015002402000400e00c23162801800c0e80e0003070340041c005038000074080500d16410b02c60b0300d400200444468030039080c03060800b0340300200504042c3c443e0481d2000304425402c1040101018410403400c82e440f0488440003c0e40d101e100c41c000e40d504e5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 863579208 1250 863577958 863577991
    0x30d0813080a08190b0901172a04060806070c060506060f1306020c0f01080c0310030c031202010b010302031323010f0b0f0a0e0c0a030b040608060406060b0a0f03051e090303 76
    0xb0b0050f0084c10b695280180c11102a40c3c0303002300d003086202c2114108082405a509482291111401e00e5100307c07414212050080050100380000c842c2954415249500f005c0180420180d214091130070294010901141c19140c540018043d445903030400121043c00040c1b0404204c00700303c4410440740741e0b409958207448c0700c0e03042c802101c4e259803c05000031142800580c042080402071074100e05940c2403800080c1d120b41c2d408203403200d00e40040d030344a11098888100143d09015042c0101021702c0d0550039410880c0c450520100d0741d150003441d84030048510741c2014508540700d01080326039002803100880800b075201c000c00340729610384d0084840c0b000d240ca103810300381e003003508640c03211600260301e03139400015040c180c0011016804164981010703d0103035485011b5403028208000c05070000341441c3c903041d012190305610030501a4010710144082941001c03010001e01094180071682c0d81d10400d2000d2600c141307a0210030b02c0c6079034409100c0d080ca00040a103124032180303031505440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 863580458 1250 863579208 863579251
    0x1801182a08090c0a140904060b0a03080c010c052a0a06050a0e010e0c01170c04090c11010c0c0c09020a0c0b04140d23070203030c070602210405030d0813080a08 70
    0x5040182c040c0a00150358002115402c0c14804486c56100c2d00079030000401e0607070300c00080c44040c81548160703220b00300480c485400440a201e20703240741031280ac2c45407401104a508000c8020b0070a20380901a542610340301c0381c000c040c030004840507845030080100c0d146c540d9064000b0140022540348070362070001c0003c001e0b030000404440300b0303005842e5043c2e0241e0012201940b500c00500d0f6650041c0140030004101e42203002c0c0c07107103118046e00c42c81d40c941584520785013141d03ca0f031441380400103800303041404a220112410291284c000000d65201c9481105950346000e1190040203c04088108001d11a01c050071100310109482501c00d07a440c10b4804403130380c0350740424000501a043c0c1d000f0110600b540010300c004c03840542a02d00700584450a2418902c1070f601c41800358120f40d210680b4442c044882c12100480104401d0030181001c01080d5102020703659001880020008540003000180e242c4140c241d020f00c0c04c65a540c00540300924903041560f44000020380a42c0d000070303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 863581708 1250 863580458 863580469
    0x1303021509030a020d03091109071b03050d05060d0209070e040603050307060629040603090609020613030309080d0806041a0604030614130503071b120c051801182a08090c 75
    0x80260300700800741c50081ca0007007007000955018152a02f03000f1480f0410703090b071022008140d28a03001c2d884140c1c943c140c2c60881010b07101c004010b107105800b0810305034010f985150345140c000d03005141c014455035405e00420024150758002800901c0701054000410091344c0100c004e940d80e54904414500f000c2c0d4040381e804c9208110820001c50a01c403c2c803416101c0d42c080c80295004d0035020801501315000309200d54000390a180b0000c44001003802855003064541c0002c005150007024150001c40004010b604013070501e51140d070320750102450034192800501150503004280d565201d649181c0b11009019400c650100790b1034400005152542408106041982000155142c03140c1a0b40e1250700400e0406041540d018000c40801c510000c40a4121140e20406c40018014100400c001c1f000703190600c62000c4545603001845020448807401030905104600400c03030310810007049150a2480c17003d40c41e032010030f09101e00800d501c21589405400d00303205450300742c2000d4080c0310 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 863582958 1250 863581708 863581721
    0xe0312090709050c07060c021002070602030f010b03060a052421060d03080a0504170313110307060e0121020a050d0c0c03140d0f06090c0908060f1303021509030a020d03 74
    0x101e040c030500c011008501c1071f40203016035050a10540d10910740681e0f02c01e00702d800569054402581c04410411400595010613000d4600f4400c00c3d4210f150610008203403500c03e01405000340d12852680700096a040000c405004030f0451994988525800200c0084108080042c009a906011902d1410505420100583c06580e0b1410650340c010040001e0480940704030750b425803244001b55003003400d6001d54058104054503040740c881e01d041030403000c103003115400d10035000360404210050700100325090340704082c2090102049003c1c10b0381c0b171124020220000d02400000c422031078660010045c0f45071030040b10b04000b810b40c520b800300c4113012188402004507196083c0100071000c1c81003d4101c0e00c14682d8007040301c1c00c5022051081e50a10340c0000c3c041030319101c2034100300d900440154050000e183c02480940307003002c140d520075a8007030008401c4402e0840e0f00380c02d0501c01d02c800502200d62108814081c2490b195180c7d4a6000406180040c0221070503502014464094030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 863584208 1250 863582958 863582971
    0x30110f0705060f04051513020a03060f060b1303170c010608070501081303020c0f190803040311090910231003020a0b1315172d010b0d0f0e031209070905 67
    0x10300c40c2c10706c0c000c0030068051024260100d00850308840c10010798400404201441c800c81d030115a00030040300c072030b00713651680d08010000c034018401c3d1040f24400207860011a50441d007111800841c161050f80d0318401e144840c01c4179400d0071000700f480080022003204460b001e0340c540c00c080d40c4501c3c10800103500e1090081c01600600d0000f800d40c41c0c83c84d040010300e000101301101c100000d0b00071004d000c800340e0081406400c0440e0030014040c560102c0030750301c103080d03401d039445150407d030050701d4840d10400c030200143c0c2c54900c0b80c0c0160301040b03400714500f04491208150300b40240c003400c0c41c2c01c0e240b004a2003016110404285038118005803404000014500c00030315082c600c1d502c8509803588800c904001280640040c9040e50090b203a0090106c4211013100801207007566581e1041d80d41040841c1e100a00104070031080c000444200c1100300d000000c1d000143e48410380a0200c0c000e5020440c4808107081e6842d04041790128011400d0804a5030400d03a203044807001e4075000c54070b5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 863585458 1250 863584208 863584213
    0x60904030c03030c020c060c0105090f0d05124201030b030c15070605101409010e0a0203090f07064e0209042a30110f0705060f0405 58
    0x107880003e009403c42440e03821117005035081c0b07104179404035040d6044619810100d030344400a0107031a040c1880a03103421300139a40500709100c1801006016840ba80000810216840000840c2800c0c0084d1151a118040d800f120481c106004032070480a8078551020040448410154003580203101d19050703201d0107006010445441001c00c41c01400410882007112070411441c1d0020703075944141441503010390812070f88181015400d43d80c85010f030520031f001b038035140010b00c01c0d4007510b141160f1010f00440701503580e0395a0b0200ea41890600c1c5d04c90360042c0b0030490042001a0841200340c201c402014840084400c20004e142142c4540042940480d00a99014004245200d52a801e4030741a6402624298040380858100c0e500e44a1440310526085e18184d610540b940311210320035518504002400c100c40500010303010711400d180d000d42041e014515030780001d9040551005491016280c9038251216104e1807540010008c980d140503500000b46d007040e840d40c65a006a401000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 863586708 1250 863585458 863585477
    0x103020907030c120501121704060912050309181b12070f2c01030c0807140a090803030114030f030406081303090b03040c0810060501051c02040509130b06090403 71
    0xc00354010888070490314100002c501d10320710b000d04c05004980c020030a0b010071071000c005500300700c2a42c0d50741002d80d001160003008100686035000403010156140580d402c4c40d50031051038814076501c254803405420450907081500a45651328500d880f9500180300328084010050700200c06110308123031409110380c6440860030b450f02c607095010b55a1501c2c201141100d500c400209814025142d0406001c6800c20f150542035a00d405510061015800c000e23455040040001e0300c17200ca00c0081c2001e244012030030007401032203503920400500e000425030b0303540d50b1980300403c41d54102240140c040e1161070380041c48a50000304840c1241d085a441c84c40c2900c3e03c3c80c1c4a08113080943c015020800151004078458655100550040d4420580702d101035192010090406075a460000700b000e1900c0ca0411150341c003d001c4600c994040d207013a1880c07001428264000f0302850708516000030b140340c1040301d00c0b40c5503254054458003c1031812110750360b9004120800b00c2c01c80f0020000740400c030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 863587958 1250 863586708 863586721
    0x215120a0f1b090e0c0c15062716050f13031103030a0f0e060403060e1006050102070b0d1d0a0c091401050607060e070e07020a0b090d0c1b0f030803071701030209 71
    0xd000c1600105c000308030a2900050400161401072003882e50124803003803009006081c40c024260003404840080000c088100f8103000140d4a04014202000108400f00c0841c659100e00121161601070445c490f03150440b8a0366a01010074034001142d03600076040300c4101a00e0004280e0342c0141013965a081003501611080b582400440f40042e0041c409000c0840054424008c85142c0c0910100821003801d40c0544201540c8840c0c0c401410341d007218100f03000e22100714003216203c042c3c00b900401d8480c1c515480038242c1c41407200310303a030034050300d00c1c1c8070100308240c1c0d4004120b982c8444140200810160100030740380003840b9041d40400104030900008003a90803031618916400140c580c800da507034101e4180d1000880b01140142c0295500c403080101d2801e416400003500002404000e281442c041d14000c80580d01030039101e0003030001c84400c205080010040d000807240700c00850f58070725000c0e400303803c283c50843c003052643e01010b00c0881c0030400c1d581241e030014501c0d00c054070b80c80c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 863589208 1250 863587958 863587979
    0x1103031b07050708190303050f01061e200a1b1202010f0c1205030a1a090a0b120f030409050a200c01020f0316031d03070215120a0f1b09 60
    0x200c102c405000302c0c03100113054801407188042c1441004220b0013100018500281215001008680b240840780300510460764020344002205000d80f1140d10421004c00c0203688410b848040c2166449002c66010032000c40492800500b0b44620084858002e08040d42c080c2c030403a90041c220300c1c0d80512000b81c055845945259241081820b202417140c5854844911504440e80d2910224000005011134044c0e07900c152aa808030071f0103100c8004c29802d0001d455042e018202005481d1200940b880d07030341d10070710041c0502c03070864100d0391443e40e8031840c6900c9030000c1c4507207611286000700180d4501100d0081561141c0c0d0042041ca2841d510352002031680c00c0240104075543d800d110b880b40080043c0c2c01140581040350030548401d0050070000c0c10384502c0311803081400030714003000320000d600006540307030564111411a4800d05560815405005400180969a00d40b00c280510f01e000e5a000c0c0410140d130784024003002c0140f0a0701490002403d002c100080c1c903d00d8204604000c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 863590458 1250 863589208 863589217
    0x209130521040b120910090302030715110304030c05061e0613060b210901091a0405011107060203040b0105010e0102070e060402090414090d180b0a0e03070f03031103031b 75
    0x207810340d10b41000d03191180070903150082c0958580742803220301407103846031003045414540c00000c40c090003440c040f56030083d16401540001040003103d040300350010540d035088030220705041c0000a407a45454200140100348880302501c060246170007017a80701c590118001484502440b100f145a104c82c030600034840861500034003425a903000201c1e08406210040000038200081c8651032001204080482c060290040e506603141c85546400030758200d400c80a4440c070280c0c1a04e907030b80e40303051040c0074041426040c0b060140c00070b020810006c003a80070314015409000190440d031388030801561003500a148441c0581d0081c0c00400c044001d02c010564000400380c40541850074203404181610482c0d080d030425046000200610500c04101c010720980152401c00712903a045095071604521900940c01c088400080c80542d607405803400705100384015084440c49580c1c0c1d48910018011404114000303807001050b01321301c00001041d031b80980804c207810316003406455041001c0fa8072 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 863591708 1250 863590458 863590513
    0x1b0f0f0d031806111213060c05010209030a0c1707061d150c0325030c03030b190e010501020106090908030609040507030507030c06080a2d111602091305 67
    0x100355400c200010a10921402403072103483d002c49400c5141d06281c1421710004034441580014046101105a5889a1012101c2c18200302c410b01a00d070800e14064452011115090300c140021402003140440c0060f04541454151305484019100c1d01078880c80320788100340000b04203040560100c559030b8070030040140014030051503142c0d907010280203034201001c04c040300e40010424480c440280c141955502507002c041c114102c82c0c40d80c018012102c41e45024080564403a4200c02c3e90310b900000c800c0710801001e002202c50748c1e17002900c81108090041d14010b5003060700000d00301600b03026807070307016500040003070650b50744070700f4811180d10040c002d9503684550107000004c103000703200c550040e50142d144195040d042070070140550f100600381258040c0343c03052021042401020a40307420a40c0c100c00d2010382071850264010f0b008000c1c3c1c02c1800000010103070b080324000c9864000241c801d95540b80d86644007080c0c0c0c0c0f0302604802024040780c01580350102c509409240c20010000b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 863592958 1250 863591708 863591717
    0x60e0306181006031101080708041203050c040b0c0718060e010b16080316020c011e0f020319020102030a141006050a021614090105060a05040b28021b0f0f0d03 70
    0x1c42e05074120b4140c400e01c0e8019a04000f5454001c01c003964031183c0540d2216481c2400e08141c00c040c2d90b800c0d018524440c4c0340082503510b02c04600c1c1f150f603a60840d00107041628001f61582c408007860b80e110800d9125105a11400d901e02d181100c240d80118012242e03c11b03101c0b107050f0f00e050b04200440e0311004580e040401d00b003003c4400180540c000d940541c0c001000245214440c00019240c601094602d40c180f00017860340c0256030b0820b045204e43e014071450070180c1e10b43c500c44180c5c59805183e2011034040c24200e568168036074158059441059600c0041c4a4094161590341312038000347c03000865800401001d010180c064001425001c07010310448080e003a00d1a072000840100790060f60030002c0c0c0c2e040001e5030f860141e0301140502001c4076913502d085200301e03000c0c14512540c441c00d50700c1400803d0401c405035080700851285120201108101008243d0007900c0d007070b55881d030b001c03045481800c892060801c4e0b04a048480b00c0a0401e810b4101c51a08120b0f1682001200b01d007000b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 863594208 1250 863592958 863592973
    0xc0909020903030f04032003120a0513030506010b0a170405030403080307050d05010e0a0506100906140d0c020f070602010b0105030105010507020418050c13020c0a0f08070803100f060e030618 84
    0x544c85200034030065009006510715420107010404904100b905903038401da1040890b002e2130350070302045030704420960400c1c0b0782e02d03c4001640d0f6040880c50b4009400350040d100002502c1b03208230020604080b040d650940b40b0819820601d003018010b503030240c410b034401d2000b4000503407070000460304060582030071401d01280911a1040c0c0e0400d80080700b0510b0100140880350324503028564200e0006c890560540d04610002031060b00e56115000400003001c0d241d045404054040301e045810104040c0494082c0c540e0203955181a03050302c064030312a4000010b0700d14410310601540c80c41c141e480a0ae564a007500440e995001a41c041c2d9100d0307034800c450a07000c1c0d00c9400300c000d8940308030003a05c071142c0504104400d0880c820189180c541c010804540e01e41c402254032000c85511604458541078203007846003560060000007002c6420010502c45000400010081180c50591005013003a45492045a001000725000c6401d91311400204468984820b40c1070340300c0c03010b0320499094 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 863595458 1250 863594208 863594227
    0x3020a050f03040c0f090c0e061308010216020f09071e030e0a030e09010605071a091f14060d03120b01030213060504030b09160905060303040e01270c090902090303 72
    0x40354000e5808403440041c2e8041044045000000c500046c800c0c0d08082147e0b50a5950241064401c048a01d1080000161501c0c0304e5222a441030041c05404000315100c1d248004140c1027039044070000d038460400124020110b140240311648a0351895071800d0010300181c04000521010b002e2903002e00d40c84040f038042801c010842d11145034000c5d600da90311000914240030300404181c00100422008202c00c80224403107400c2c0a0500000e58606009552801a21360810b0f0600418009910600040c803084130842c2c1c0200201504425121419032241020065203e05000c001004219020142c180081080c0c1c401c4060b08018100945002c094810210140c44c0640084000c6200030170103006024040511980c04100741005000d045078010421120401c2c81c4210605692a01c1c009025524103000307503002460b514000840a5850303207030074561080c0410601044180380c0200d0844110076008908051044e078480505d401e05004e4030314081d40c0902031160f0980300400c020b810 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 863596708 1250 863595458 863595487
    0x9020706060905093003090a110406051c06110c15010504090b060d020a0302280b07051c1713050c03070302011d0a03080a020133050405130c030524100603020a05 71
    0x204031f520002911060b0050b140125030f81610210050140385030140c240400c0d15600007003a402013440504014905981c0341075006081c602c0c540c2c4220b000041440c3e8086200000c50103a03c28407141c4d0342d115683c0b00c03010b201c1180c44429000d041109010040307840707030415031400c441e45800500007a14154694000c2512402503c441012101c00c03000028100d081600240c4040d08240e896280f40c181540c4426a94904500c00300c54038100c5001c134000110f0007421601d50299000c0a0a216441e26a00300ca0b500300e41c0c002b0079100c50041c145c0041760351801107007000a680d4161500b502c40795116554a0442c00070090264229030b4074000800817424210141c406c05929a0000c12483e004e2100c1a00c082c0045480c03900c20b520409640840c5004d03c90110b080c0d45080c1c400040300e542d04e040c5180710840d0910f0140001010311800b200384880402e00b0030b03002d45100c065121603544000003106010049039400c0203501010b0041c003429109400906078400039242481c1032041d881c20200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 863597958 1250 863596708 863596711
    0x60708120f061002120a0809070911251203050a150306050403020c0108040b0106080403030908031e0c0c0a081812070501120c0219031809020706060905093003 70
    0x1a81d05840080000a107416030110070b80d52481c2c40500940c00c100040c0d244140181000e000500c5145400a003500030204450401454104020300a0301688102c2c1c08503580205274141c82203c5100b41e40103408403010106003096400041c005c01c10850b1901140140005041d50314455203605c00c1080e000c0d00d101d410300c0514020782c80000d0505043c6400707440c0a2040c21528148070101c0b0821001c500740340f03400d5045075028103001006075907526046000340041c6500400d080000b006001090799001d0302c1c943c07040e0b6030b042c0d4030700c00da11150100c44090080d106180a0750f03019090000c0001c1600b4003070700c511568185101849001030700001c902c403466540311091070340408000c0050b50382c40a40c13900c240303140e002d04101440508000070b407140716103a2004985d9006ca101c02c0101440394103071200c040d40403c90080d00c1d81e152a150400303940403001c2502d00a0901c00085840040740c49030318045e8907400000d10003038100c0403214881c00e6205071070501031000c4460040c1600100d50023103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 863599208 1250 863597958 863597971
    0x130e0705040e0c030601150512040219080607021b031002070c05030d17060901060912052e1a03060414030f070b0f0f0c090d11030709020a02060708041106070812 71
    0xa043c0c00c04842e0038140340c000164816079904080421103205690040300325a510380d0401514002d0381e480b4004a124003454070203442c03c1280381035000441c0840410600d000308040d90954115a8080c054241540c0c0201c03000c40d4950000350703000075000780031350007468024403482c2c80c900c1196132280013074140840c0c140818003107003900761071540041d0f02343e060992142040790b81502c0c55052040040c0b4940c07490096508801d07108080c0c806108040207220781c0341c2d07003042198030302809014554044c04103a00540e81d0550030900501580c49414843c010400406030082045541d55260b040703015800d0107000d4440c1c0000c00042a07224100c400912040380901c0a207440d50412a070b01e94801d050040200503a00102410712802041c031a0440b80c4428040311081c0204083d424070405404000400c15071510900b48000b481003480e4001e8a58891680c0030b660b21381d641c400e000c2d00d40d0801124020000001c3c080c03260060301d4490041c11806003e10411401c04001c03001c4450405c2041e200b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 863600458 1250 863599208 863599213
    0x50a111c021504050303060d0201030b101d010206090606090c0c06040803040b090609151504061d0c0f040303051c051f0b091305060d120305010303020106090b130e0705040e 76
    0x4410201e404101160350940c1c0e1401d4021146025103482e912400043c00861003884c2000700e10741503a100c0e800c241d901d480001c2100f4608441c9080c0907001f0415004541004202c0d0400c040184d0f0000c079243c1c3c45150500f0113442d55036661400c00603500802403241c1c01d002010301818882c1d0400300f2010340304511500480340d49040605100300703032020003030205440e60302190404c0844040860340240c43c07a58403500008079100e01356541c9030204038151641d00240b0f000301c0025110190301710810100514940d035102e0b40c9848000c07040c1d500c101c40704144030050030082000080d10074002044501603080c0e008014031030759030a240544106076000040d5030012144600241c030081c0c00c400051040228452900c1003079000f2450548038800d482040d00c0e600e800080e9030ba00c07444085201581d00881c143e040085242c03029004104c04e02094005600e0308101158484c028401c0d102605801840e280034030102e030380058040c080c1c465030481180100307500002d0a0300c0310f0141c0070011242201 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 863601708 1250 863600458 863600503
    0x5030f0315040c0f0c030516061d07210614090c0a05040209010905011419021c02010606080f0411030609031e070b221203022a0d050a11 60
    0x1980c400c00c800c0540402d00c0b9a241c41c0e00510f0054100800c2502c080d4182008082412a410251868058a01c80910f4611286031076410011a0782c4080b8000703031502c00d6500c03980c4a01c08095a142030600401c00445c0b6034148401c00c50010b42900d0500d144100000f041410000400348100f8105940c040f10340c0e888600d0025940c40d040c50300c1005008161401c40c180200c00000070300d81c2200d445101d040c4201d49168494036260b0404072407241d480600c100e60220000f41009698007030308103541800b0b414980b8641c124030701c1801380c2001c030380700c03542c4c0c0c24105e072520b400181540c0c802030001c845500010200d100262001e118107403054000c0409103495408070041c40284103222400b078040102c0420a4900040208005642004059003000400f550540c83c40d400443c465502810f03050709448000c81456050b00207007107542440c0e101241d0040700041406a00142c405080c01070341103280c5000e0301d18456000f0b0403c4489524145080e098508205814960701a00c6045428030040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 863602958 1250 863601708 863601721
    0x909042a1403121602010509040c0e01081513020a030b0a14150f030c0c0a06090803100b0304150b030111030f040606060813030f0311181c08030412050705030f03 71
    0x186a0412031506402030188802c058400c0143d030311502515500741000c06400d0815a440340c416141c000c8005001041800601e0a001c5c0004a1160000740040d1045000495201e8410f0340b110071158060080403021f0140030040001c3c0d0040c45034042090341d1501e9010041d034800c00e015000741004201c5140704c8600c1420720019020364520109040300412032403417405070100450b0340c8000d58121080e00c81c42c031528020308100c182d11014100320306000d82d180900c480320f0300440c012845122900c3e91150b450110310a10f0204a4028200701e0010004030440e418540014464242c01400002c4404201d0007020003a041a1400c4458407250300030040cc0190074410130014001504012080d0310700003115070600e85040c1001020443d14111802c1050300a401031000b008810707040940701d15062540744140d1840c0026203100300c18152001030040d40325004440c006400400b1b0a00d55035454888040d140380703200c0c2c0041004800c00040e001719105201412010107141a4031f03543c0d05112 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 863604208 1250 863602958 863602979
    0x601020f0a030c0b13050601060201021801030c050702090c0c150406140103150c030b0d120828050606070816140601050904140109050f070305010609060b0909042a 72
    0x3600032410660045445001083d08000380407074540d0301904111040d035400c00d02d0f81100110010050440c880c0c2400411801c0c0c040d0050031103814150510170b41c1c0810320004500b910800b5480402191041003030030054281401015440303801d00103000e00e800c60b0500303c0c5184c23580c48040c110444440d1000c0c00200300b03d9010b002c1d50381000d030214200d04e5055488289920602801942d011a6100c404019a50080d003151505a50061070311441c1005402d28100c641f54425584001543c204001400001000100070110142c64803c20502003250fa0000040c03d0180c00550301c401c0501441c0000350b011001400d007a0104801c00c03087d1681c40c41c103180b41c052320702038401c02c07504a0001400b5a0320b410400640c0710350401c0c2200f0a003105410018010055400c000e40580038000485520321000645c05007200d120b4002000700c3e942d00c0303c1a1040f5500d0340940c000f54031302000074a0b400c1c0341c0740e0b1005410031300072034003004900d40480038120b001d441200c0c405840c0c918010100300c0038000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 863605458 1250 863604208 863604223
    0x110607020c13060b0a08090c0d0b0402090f070806060c0c0a0306020408060c041202040513020d0501270c03022704210309020a03021e04140108010c0f020d050304080d0c08060102 78
    0x2c181d0248015030602d1110030b1070b4001c50482608004030f0038002500b1020410440b550881c028018014040140c180342103900c104a50680c00340340350780080b031000c5014020151140085940e41c1c0c10b81c0d103500303040250a80c850309410116108407000044983d44841030700005602c145001a5514a0000341d50300700b00700204540100c41d02030008101c483c0c1c40e040c2c5030001c82e5040328009496907a10500c82078050036050042e42104030104114200a41540b02c2c9042a111045071030030080c120400300f41c901c8280500500b6101000e074104018141260701d01101d420808082d0050701102c0c0310042000710407101035581401d40d1400b1680c03210b1400790140040854a02800150016004500304480600c8001c0c0075040d160800b0070b240c440d00c100070b0342000e030051042c4040c0c0b11034098649140303000c0c020b24541d0352906c410616264050780109480c6401031300030b000f00880d03041045d1035542004006a0b0085020810003000301540d1003041010801c07522814014101440024500b412 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 863606708 1250 863605458 863605489
    0xc0f010c1704080114070207090b12061303084506070c06050c12041103010209031905120c1f060902040e0a1401050a2d081525030c110607020c 63
    0x6885d01440020340c0e0104980058446400c00826142d0904002c61080d4200b22110402409403c09010000d450007058110b114000d81ea03520160b1606800204042d0b644c02c0c242031091103034042403015101c1403650550142000030700012020b04a104e0a00b80340c1e040300c034040080d985160f0321040019500c1140e40060115080c507050905c9045180c40200001d0805032604050400b44034036964250102e407042840501074076020542ea29040c2210401480d040b50781c1e02a00104240110501c001c2d1489002840001c09584001d09ca0313201c0c9005000140221403510b512000c500725100303000034401060311100700b41c030b42c1c5011074840c0101c502000c048040d0b01540001040300d80d4609810344c00b030781c80004203489500f0a00c9200303241c01c0f503500c682e54100784500744000780c0000007240200200c2d0103110440f20075590960b59400300c040320b030280480e500c0f611800302890b070310030fa03c2101c11901c0b50500968000c1c24056403407900074202d1381c500060380b00d400140181c0c14403802d030800076070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 863607958 1250 863606708 863606741
    0x2030a1a070912061d0318150f0a08070e150d1a0f060a0315090203092512054e030708040c1212080708090c0f010c17040801 55
    0x7800c00366281c1c1503400410004c0c0c03440340c981c00c20000500300d50010701c04400b080c02c1100d5451740482801443c0d440c88001881c82120001d420998080d420b0302224840d40421540324641030210740b0550b144180946210704000c2c446800700500d07100d001341d00300c0101c102100140c031030010140000c241d43d2051490083e402003400307518596200c142c0e01e121507550840300141c541c1c1009100300d0051000c000003920302070744d404001031b16154603802075008255000503620f034911400e03614640c8002c031400c1c040800d0350880c01001900c400000504400d4810301c00e031031121480c091002d00c4001c984418440d0070b0504541c400740000c04160140c504c4489481000c3c00c81c0c20303407910003480c3c00002c00c11070901c491880060100315185040c03d010f4041038003940305961081c01e14062400c2c00c4c1256078003144030203002c1a061400344042e28481d80088004040904c009400d202d84082144201130500c802d400d90030001901f80300c40c400c1c00b000d030300c1005600e0b40e180c5420242034a2104900c0d0119a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 863609208 1250 863607958 863607977
    0xf0121091b06020a050d1116030602070303050f150f040b19090615080115180b040905100305031b01110d0921080a0c021009030f110f03180a0302030a1a07 68
    0x21004140c150011500342010301080c2044103101d4109502301028088682411001004100b0103502901890b8004d075010800c035542c030444003130580c20541c1c10350409000070111856602e0406a1280d03111405000030a0004402c2d0100b0910703051100364407461801d07448148030030526441b1b100018416042c0c0c10380c00807a050360161100790306010b094450580303003003e81c140b64000c0f0490321400e060390540005503603a41945c3c2413180c0113401510480350070301c2c2c04659642d5062241205681d0421302640c0f500f60307010f6403411000c0605601c07840d15500d4404a00c100402c03030000d00b180c081e403001c0204010080389004c50f039014403801c4102400c4018050700607000d901c00000c0340d003d55840400100403d45040030b80c41d01606501820a040c2070480b0354041583c800c100c10548600c2d62204e002d1034442d610703510303152103908000200607032090080c0c0103911510807007075001e02000b401090780380b5101d8010a0030421108400c3c0c44d9251003a13140d81e408101010040e43c003001d28504503405 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 863610458 1250 863609208 863609213
    0x1c082106060a050705070e010f1701020306060417210703260112080409110901030c020d050d2004030b0f070f020d05092d010f05090f0121091b06020a 66
    0x60081c81550350800001044d0402009420804c1c1c102422000e00145807540e036400f0010340c60f410340d024224a0000ca09158103041c0130500960b409008014100d9052500b81f8204000c8131a80681c84801403240c60846801031b446051586151209000e48a98403a22424082c1001c40710001d00c02240b04220b900f090009404484941507072410b52085c8030707055550a010005024a812100700c151a01e5090106c800c1c0768070042900d48001e0300d0510008404507002c2c0e0302c5006149200c400f05100700208070300d07004968046400b0b407800d0762400114120140803441280c101740c01c100c81d680c0144007449045a1580b00545d4480c2e298500080c1c250305d2140004d46500501001c50706000c1c01040c611819900c03420310b800b00c0030100d2441201a404007081100070105040c0503070115007200b084640030342c030400c00c840e200c1d40c000d45814548240d10004550015803004a942c06280452070f43c00031795a18001c051206000d0b14400b002c00704084011010a1501e5101000795880721240100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 863611708 1250 863610458 863610469
    0x708070f050f21122e0501110c1c05150703050406060506030402010206041401060f08010b03151003030c031e030b090a0e120f071b0f0e060f0d11040e16060207060804111c082106 78
    0x2c1c1c180885200d0f01c0c0394860351600a1500b000348cc80f20145104410401071840d07811b03401103200d81c1c000c84003480800c0d60f6505200a611081d200030380180c004e000010041004c00d0000c41103995140c0001440b0382d6a280400d50003003054110143c282d443d0004480c80b40f404101c0c60031100b400d000803048900307140012108241e45403200400b0b00810074006000e2500071186400c03c0c80d41108881d07161000c82500500501e82c0f0100c883c441c01503003010030340c1c844091040f010050300c10802003141248a480011080e00000c8109074500010000e030320001360882007040c00c60315603610205a450800d940811100002d03001111582105010800c9540c0d80101c9040514026280e40d070008145040021080c001c80080580040c288000c1e07224401001030102143d09050400514031512003e049842d510184100c0c0300082e440700c045008a410842c00084c0c401000780540d00900c05d65004508081140c5801d0303891040115541403500309018101081845035040c480c103e01d031550021782d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 863612958 1250 863611708 863611729
    0x121e03010807270e01050f2401141315090504021608030703091e0308061f0f26011410080c0708070f050f21122e0501110c 54
    0x8159150280705403200343d06101000352404071a81c0e091000d0705000c560b2501030310041da040c440c1c0520b644005042c10013021030107040202c1c802600314070800742000454803103582d03019000c0c00b440100580403688100d903000c40001c000d07420100c0001c1c129a40081c11811050740640e000d640100f020001d01d0100c1e0a44c0c105182d0300000c581d4480e00c845004a00908249600519021360141850f0101d41160b40040040d88a41d856250329a985402e00604003070249140c03e00072000d00c0c010b1401400740c10319480c4500136203020860025070804410096070000072a17203409100000500101c071004c15480b4190b50240c603c0303a942c911912004000e120300a0400c0880d1501042c541c1c02c1026101c121402150401154000c80e0584d0520230b48811100f0030f1041940b05130703d4000403501c600c0e00c448694010500304942006500b51641e45804070003004101e003814406402c85101a41341c0c0d40961602001070710210441c10140054990b5402a05880c919400000c58510039a5a0384000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 863614208 1250 863612958 863612969
    0x90d080403050a030b1203131707140d06020a030510090c0f0e04060e0411190b040603020307030f0e0a120509060708090301110d150e0603030306010818121e03010807 73
    0x543d803414101c20450090211451440c0e205503d20702000802400001400900c1170004014410aa40d800d03103c0e401d0032501681ca030641c0010384d04020001e4003150040c1d0500c400b078030301080104075a48010403607010b82180d1010a0740c54090020040316540410044c005002e802c004104020038003400f10b00480300c03d40c041002c0010304036415181c540059009100700c41c0b64041c2810035280c62200d031025441d03018003d541c01079072807090003508101e0104440c103480001c0e2a044c1441d5048010b9031004151406260321000402c2c030222582c4510ba0640c61040094001030045140c01a22030305502910f0341000014002000342e40d803a1011120002d9001d4040c6946211300e00c04a805000802c1c103d200748400441c403000c01c02a141c0120028055021121128503214024290010002d540480d0154014000207034154090348150360001c0300310010340700181504211601d49500e425141d02d80001c04200080030140180168105190b801c0c0c00d14215070401000c0d83d07841c141032188 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 863615458 1250 863614208 863614217
    0xd060c0f211104080f0c120106050a120f080309011b05090a0605090a0801020408060a0f1a0603040c080714090a0608060412050c0304090e0f0c0a090c050906120708090d080403 77
    0x18002c0b085201114014401e41080e40c8040a1101c20240c0391808400807c0c01407450090303c519081c41803041ea42900c200030418500b0900700380024010460202084900340840540b490205100030080c0d84174140c5440040f4007040700701c00e0625012040c5540c10203005051044c15016601c3c8002d0314280c9460f4a1704503140d042000000350002040d51205e4041d5100160124045001182480c811541d01100307104401c7c045400c074003103038400341c05505078581542e41110280380c00700045812501490301200301603103441649092524960080c1c504d441005103900e480c1c05c010459503401382c0b205508000712480c0000072a150b020080005040000e140b02c00501c49000340156448982c0280c200e9848035101c1000304010305101c13210381014400e020440540c01e1000401031240f52000d410a03c135249050602c4002c0c0082c0c2e01402c09008003404005a940c5544025101c104100e03031000032181803d00c00509055030161003201d098100c12119410b050300316201640203585840c2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 863616708 1250 863615458 863615471
    0x1d060a0507020a03120912080f0f0909070302031005090f060906011b2306070c120507021509100c0f02011805030f06010303020f0a050a200d060c0f21 66
    0x4129894407070100002c0d031001180e8030101c1400383c00130780c22070550880d03190602c050303456880d400720782d07070003810000c7c2202020424044240f408070007812904803d0105141070030711400009002500031a440c80009a004c0f080040c03840d880e2400d41c0c002e2105a420100505084030707000d15200e001421140034050b0302c0c004c41d80d176034850101101d864807450403c10142d030442c03414520b81c8039190111410320140300c003500404140032400c40d001e01c1c1251102d0700011002d6840d030042e0ba911481c603c1c1405800d100d01c2026807200c0c9403190303005e4400d009440d0348040310b504101d000018048840100b00003a41e1000000741c030705031b442c00c0403a024242298064110142841d0802e10703500516090301a2070742002124900284850690784030b602a24a140020740449640d488500300c064125404540100b002c50088a5808007850a02c141d0941140304503003c651800c10406041761101e54600311038915a40c0411460244e400c107141442614110417000c0c500070202c0b6a0703a800a03640c801 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 863617958 1250 863616708 863616727
    0x50d0219020112150b040b040e0a06150c020102100f050406060605040501020601120819020f0105010503010510030f06020405060c0a0b070c0b0402120a1506230307060809010e0a0b15011d06 83
    0x141c00d00401003181c5c100d40e2030b6101c401e400c00760b41062052200d000c4005010801840e41c1c2e0142c0d0050fa4101211a84280f0704020202c428030000c0744160b0541c01020302420742d50600f4010311400c400c8400b004951401c01c2e15061084400980c01081081424442805241e90114100c1d04444e02e840c0d4004490032281040c00140c45046000340b0013812000c250303502e0365008210b00c080e0483d01002042140c3e40d070403d0609940080310181070f2106242802d10020300704c045645205401100e005051a03100c4000c643c2c00da1001e01d801a0942c000c040880400c05203044440d4018030900d0040400d01d03240c2d0f42e0200207130000e44002e104a19010f00d41c1c0d0710a000300700d0300800c25004501c00b551010215100760050500b401103542c064082198100b40c01c1c00040041c601c5180600100f808520301601140c2000d03010f042c0c0f4842d5520f0319001321408030100640c6405c230307005800d5185542000340c400e84c02250701000c0241400802d0039900318881010510f804004415600d09030390b0301049 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 863619208 1250 863617958 863617991
    0x90320241b1c0f0b01031b08010b0a09030b15090108010c12020c03070c090221161112031017010b010c200d150b12100903050c0604050d0219020112 65
    0x9200b81c2021403818034120503161507900501d50050f8280c8082010700401e0000c0c4032100031208144000c40c1041004000e4a80d0010041030005c07442d1501c040115203e0380c03400700001007910b412110409007042c000882c90103030390190040107064001c120111030908050501c0303a40d113041e900c41c1680403034800c1103018140b045030103582e8821107011500c0d4503804c4486c000d40142c0440310350030455528860b80500c01000442c052001264445600c4800140840c1c2e00b414401034510750f4051082060250540d0300050360148088040802c504c0e800e01314000d40c901049424241e05a04203506107a440e44c1000c00301044503002104445c1500c03485109080c0c0c0c0850980c400c0e00084060440000d0100010400346600d0120310280700480c1c0c24020000c40d0300d0040071038281c41d0401400724240b496240d002c004503030310034103082e81440c02d030620b05800e11204513400e40e40d13900003c611b40401507042c81040f5045100c541d141420100f00d400007043e0107600050740c001c16079200d8141c855030001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 863620458 1250 863619208 863619247
    0x6020d0504080d14190201052703030406090203030f030a020c0105101508100506041211010504050a0905091002031302030f06071403150d2108010315090320241b 71
    0x505c90f80c18111207140748028000c1c20100c902c030803a640c00b0140c00d001c581c0c113052141706050070351008604540b00e0391280030040030150f408036450301c01000307a40c52150756100518840c0088181c0180c5441c81500da00342507820052685041c0c000c6180148540300070040035030103024951801c412565100c8406500c10881c90b003285501a0340491300240321480500e0300b90a4a202d03100381c0600c1030f960300042d2143d0003180107403070340501d080c00d041c8900c403840c1d801241e001810104a0301d090000e40c070344800701d03403054500100340015406004154101084000c00e1100c0c800b0080c611440e12503030080010303041500640e504400003011405a04024148090880008140004011046c500a8502000d41d4910120b000310a04800d500c00d010b0314400c1e048a4101180c1c2d40307840203110400000b03120409080301408400708201c0e5101004c4032903041c90390600c0e0001c080c60f0307180c1089000100322090b2400e8004108c102045044c40c0f2080c0e0501e0151114640944c40300096a42070700115603 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 863621708 1250 863620458 863620477
    0xa090e1b071a090d0909020906040618030204090b0402040b030c0105091309050f01060608090303070f031806050115030e160509130501090b16180b0d09020604080706020d0504080d14 80
    0x25040c040c00322543c40851400c1101080782c1380c01244603510f00202d0213901079800900c0c0c2c050001c4c48100101d0380251000051440380100140c00a031304e0391f0024007155001071081d221103005908120031030602d48070b00d102ca11021002056a2107107500000c0c00c0c1d1040300100e5000b0101407070881010041900004040e0341e009041d00d4180c5d03200c641d0603000b40302e00c0c450301e0000390040000c14501c02c00482140d00804007541e6018140e49402020b501400d82180320023044501d400b0301d41c2c04a15030b0301c56107028043c800a48102c07041c0450b030041c107070707803072501402d01b56003209481200b294022040d203822104c05440401540e528010401f40b600c00c900c001a00179424403045c00c042084010503103100f001c0508041c16003541d00081201c0e010081700d90b05164001d2540f043c04843c0a540c09020f0601c084a00428289074603804034000d0717003042d4400c0d03826a1081c1800d0200300e8040c466208102c000385803103400c041c40c02005907512808480c1c03000c00e2103d003080d4203503041d102500b102c64086 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 863622958 1250 863621708 863621753
    0xd0501050c09010e12060103023c0f0a050d17040b030411030d080c0327010c0206040203010f0b0a060e0102100207050d110303280b03060403050a090e1b07 68
    0x18041119000c207900681080c3d0014003100031002903450881544042c010a03107008040980c25507080c8400c1da074905007540442c1036841000c5500c280074448941c0e1403030114400c0c0c070034418004240480802181c0905114521311501403183d91503d910000030f00d50031036045c682680300e280010b17085101d03607002444e0326034000042000307100c5c850394000070121040e422180400610f039011031b40c500041c0c4070020b04440410101c1e4801f5a410a4a001c456402a002c0a010700d520280d60846445440610150f0041c000304429803a0a1203800e081302148082400409500d00000c0c2c14000eaa01400040c4002100e52124507442000000307560440807104656070001800c11642d02c094982e11880002c2c020840d80740806030100c140d0703006000c0c05c8100300125450031140008080034801c1a44c61a40d03420810040c2c2d0f0f410001c06001d0342c02511034a40e98500b100d8000d103000019044940d104000100f031101d550226005c0da6040340013020407076101d01030b603d450000710488101801420 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 863624208 1250 863622958 863622961
    0xa060b0a030c0f0e010503030a0c120306081e0c0301091a0901021611120a0c052106010e0f01060c020d03050f07020409050f0114011a1317010b101803030e0d050105 72
    0x81e0b0f076510f2100a80707903841d25002c01130313031384104242d41d910403d500400040e100c150a4030010f49070095454000300310f406c005c03942c03984820b090740c23914815200a242181140d202c10000803428410902c0c0204140e00034000c01e40c0780d07250490030084194601070002022000240b00d01030a6041d615548802d020280850440d82414407481c484142d0a034402c04403021800000403001036685e8040b54070041d241d850900c1e00e81008840b6203003d1511311003461102d00c0e0456080c00b0702c50741e4040e08040040002074200300f0b002090a00050704680c05104901885d1000341e41c2e81c4144200c2d00c1c0e40b501d4201d60f074041208401e0100d0080d03440081d0001d003840d604d0301c10064046020700702280d1241c003c1080c05d03c2e03059031014000b0284103c8824003180b030303042c110b2020041c00500103680c8050440030907da030740b07480b1410800304000b4004180d55454540b5050314140400c40094030651414170180b640e6000706d82c505114601c00203080c0001d2601c10030351501d074081a00d580d15041002000503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 863625458 1250 863624208 863624219
    0xa18080a20250801091a060a08010207120f0906080109020f0903012f1c050403050c07082d06070f021e01060f080109080315040f110a110f0a060b0a030c 67
    0x15280c02e401c1c82c0b0a00c280e031041c0070680d1001440341c414059005040c150100f030780c00303290000a120241c011070700702c4c544c5c80780032030120b0b402d00003820717414810020040d54403480200100500c000f03c00c198100105034204002860703010b40401d06480031454010382e0b800035019140194807900e585140c15500b00f07014903d840848500708558a0001d04500c0c00d0403115400d078481c1d5110b061410b880080d408180c08840405690015074864440d0624918046003c09168a0648640e1140f1a40e900000c00111007500d5032a07a40c504079824000100e8240a100000b130301d48e41c0040c0f402003000f48490aa050141c420048401541142001e800002d4160102c071030180015008240189420060008940701c051244507001900603691078219143c41c4020350505240300c007650703440f82d1500500150703d00f507482560341c82107400c41890741d500307601c0c58040d141c55002d0050807100c2c0c0080171513921965010404c0d40342180c0c010070000b10450550b0014500b4134550300043c1014003009400b050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 863626708 1250 863625458 863625493
    0x30b120607030507031506080606090a0b0a110102030c030a091104110903070b070c27060b040303080a1a0607020109090509010203040203070f06020d11030d11030a18080a20 76
    0x200602e9400340420f640f403038001c0c0c082e14203607410500c549031003080401070584242420354101f1002061175107003024020015000c607400d500081c41059000644c0420780b5008140c1000d0f11003400d00a50440c54841d4225101740801011320240d035448035400020044406d56a45500100420801000c07002035002d100701d40040e84072034000d100c0c504010818140307040a030784281d940901c5d501c140501b401c4101c0512261a84600ca000c496003040c507801c4001d070b0064101900c001e0031450f85441c55810700812940f0b02910480c5034034980b40f50102042c900c44201903106009840207540e400451004070391521181c0d2065007141e01c4c0100b88070141506400860140f4000c400301c8400984a010350203820100f8840c034400b692240c80380004441c01510b00b80f80484210f07090300d0a1901881c0c98009640c540a0101500320000041064a00241c410102e0881011030001d800600c01c0e52078003d18032030180c641090100f90b520f0508201c418424594441051006466007803001d600101f1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 863627958 1250 863626708 863626711
    0x5040605100f030f1101020f030a0e010f0509090a0221040b0106091508130606090203333a050307030201060e06030c220216060f06060804060b01030b1206 68
    0x15010341c025a40022030500280540042d00d42109440c240c00e50169034a4518000340c2c148281503000c0e0483e0046ca0040030310150801d810307291106103804400c64001001c540b550f001c4107081c0071041c021140c040e207811041c0c1d644900744450040e5030f4041d0510007800340c8030b00041e04648406190822007006101110541200c44035241c4852154070780440e0341000346141c684000040ca98000101d0318261180386010701c43c007445000480d00e0300c42920740e003681c3c811114080725454200798190100200005551844102c6400e8010f0074040c2d000140d100405d5074140807103258041e031040e0300308031003200c1c255580744600d81140c540d0a180761040e26038200d140203038051f510304440000e1414104803a58450f8038020042c03c003114200c8100803004c61228021442c45000c0582000f1030099407004101843c010311014500040600e042c2d015152030400c056240f90410204000c21a00140c4458000b83e0250000c5085119280120028406100c0c615407100d050121801c00c0c0001107001c9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 863629208 1250 863627958 863627971
    0x18130216060e19050a0f1104240504060b070f1a04150c0c030f1112130f0b0708250b0c030f100b09060703140c250b1206010c02030105040605 62
    0x31035000c50301d0036081d07450218088000c0c1c070170341200500c0360000319640f20454a0a12418200c12002e003044003103022543c6803207031040041881014101c41d450460401801000125021701c10181802c1e440d102c140904c1c3c0c4000c225440c0001d6040070081e01c60b00442020b822010218080d28050070b1000e441c2c40300301c803903a02d0300c3c0c507103003a20556510415940060380e0305510b071036010080d4101d040310641c800f0b042d400c44a01070301d441041c200c00e155000340002c02d003410781c0e82c4005042502c1d40e0035002d01030788603c80c0c4860820190000030009000ea074010840c0c00121170408148001a10908076102001440010f0302410004090b00070360107540144210f0180100903a12100c040101d84607034010b201e880d500500542e4141d150400040044510034a81072028050359043c0f0120b9030006d90541b0b4a0b6000054940380034140000b204c2042e0f640a1400740c0e996190403001207191255107038224211904030300041c0143d00a207000b100f41c650240003041145800d003800e400030709040e0b648 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 863630458 1250 863629208 863629213
    0x9030c03080a0b06070b04080d0603050d0e0301200c030c0d0207092f1c110a11150406150803031008060105030d020c060a1b03030203091218130216060e 67
    0x114201840d030f48144011240060722061500545440d102402a0300074003c5403d80010080d000702541c4d140101002035220301c0042401411480e1f01501c01c0c0250b13248680a60316001c9130100b1901030b100784110f05a040d225440e950702565418508610402c24018031074807581e0070041d84203900044640455001c400100070140c2e200401c6103101d09164400320031000000c1e0020141c1160000510600316154a0038441c0a035811381a01603503d0584440040384c004182000b050784c1112280d59211948409042d5030402c2604292001c0c2c0080c10190290396103040360384141103202c13401d6000e030540d00c007102d48030b20300b0502080f040c00b0540900105409107c00000d503908001030040b800120035000740505e80541001e0040c245c10802e00c1400304610b015070300c8482440d020518501c6c500981d0056502d01d40408410700d031074850000d000c2100d40400010344401c2c070980104547d9a4111016407007090140340c0c1001038010380c2d203545110080a80e0110412005610501886000009 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 863631708 1250 863630458 863630461
    0xc2609090f16110d03050c0405030f030c0c03061611070b04090c030c05460c060b18071110110405180601050405131b0e1804051002091309030c0308 65
    0x1000c50b600031403641c0f001c0d880c0d4864440b41c81d10b2070003500820b6203c603082d48410300b071560302c10000b0b14000701500f0415a54000080b000301d8824140207007a0700c2c80055005015a05010b42c40000201008042904000a0030506200d84005002d150000d021401c081030720f81e0b071201c46d00f40c014100d1104c0080440e1411103d0030b00e1070300500c280c0381c1c2d1081801e64030100c280390541c5111503541247e94245405001404441c0c900c0110014006103c800c1d80d581c60186082d141034400c0301c00c0680003920500100c060000008240e5080c1980400149444020036401038403061404c03003024508502e080c1002800701000c030070180a002107a81c1220b030301600d12041c000781c6410940070b4400c1400248104000e0085061080010500030a00030000860651488404c20807030700c240000740002e100b10446034460720b44122220700c000c04030f03a902e94442c1801d07549c00c0e5441c800c00b009070036540e07004156590680c0d2f0b0440c0d4520040301c010010302c145141403034004e0100074511000c4010524440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 863632958 1250 863631708 863631751
    0x6110a0503271e0409060219030518070f0302011b050d2102030114041d0111090a06031a010305070c170309060108030301230a030219030c060c2609090f 67
    0x83c140d510b40d21000d0020406400b00c400340000780460f44426500700b6001c010003000054244a131380d104c400e0645d400211801c16284100307078104840103481c0304e0f80c080d42c000c3c003030900d000b0b070980216682402d00c0340c0010321804198000d0003500402421a00603184000c45158102c6e0a5814100c1d04841044081039541c0024080340401c1c0a90302e260208030030044450304240e0b0281c070554006104d640d00d401c1c22880164291000705111502c640404941e8440d142805040c1a000e041c80341018041440d0a1800c548602e0014403024100741d00d480116403e517000c3c0d0741c1d002d5002e4024a2a403980c0245008003c01d903402070b1a080c3c91403096100004903a0b03070100c10f80707041c0d0300740300104407c1000030b0341e42d8038000c2c07201780006600900b030700d0001005994844011810101c04400903800a25504003010501410741c01201803100744141180002c900645d1802c6164003030040d8031802584c840c0c5507600703004001d511a00700d00c402041c80080d0a40e503000034402e05100e2846e01c08480c40c1c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 863634208 1250 863632958 863632969
    0x50a030318050705240f09131e2d020712110a03031a0d0f050d020727140403020a120c02062b0c0306030506060d0c06110a050327 57
    0x200300589550400e22081c42130340380101c50050145038000720038101248086907103800c0d5104076100303c1003180000d02c0821a0500c00700284407070303415903400c116150400121101505032002d044000c46d0340c820000c0400d407621490001c00c601c0050101c50400a091020300080d407044505568003207411821041e47d901c50341d00c440140305004003802e1310070b03004da4058020782480c64409000400c92101c100064445065130100c40c6d005010f00049111a0f04004e803e001d05039550381c0847d04106814401c501e071584062107188002101180001240b00800c8020720341844d0070b01014020000348014554006460001d4038021140c2d03920321912a0300030b40305000d1014000307412034024424580081512000c048c4581164035403143c1c441c011105510032125050310b50004a640e0301c00500610004021143c0d1140c02030b20807070210800d0344c543d820b00000c207100f090b04001803407044005404c014462811003e5200080700d4841194103080c4e171510303038038407044109400004104c041d05d01e0701 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 863635458 1250 863634208 863634251
    0xb2a1c0b030721060e01140106030c030c0905210102180a060509090c0a020f0f07080709150e042a150302120a051b120f2d180307050a0303 61
    0x8098401c0e400f030661848600d0000320401c080e00c0d0700744d5410b01d1241030b103000c3c010020f5002d88180348189030360400001508852022440b02c00301480c14640150080c0c00c85440e80946604940c0c1800003591100d84e810343d4012400443c1c810b50003c2507074800f4203944151601e10420403956005640e1b11010704480c00d004042c0459400748400d80030039001724944006180201135407068403e00325405000c80d1402c4c0502c4028080d03944900010003440700c0901c070071000381080c01070074403286400410340f4100b03020314003548110a040750007003410041441202081803c2c20380e400c0100c0010312600404c400602d20031580403401192480060f248244229140300c180d05004c01e05945071401c5450007030500405290010060740e041c0d81d5810301c0030300035001c13010400304812160315102207100c1a402010305013000c3d11510824410000801030184140f010481ca01d0b0501c0d0341c0d410301c40d4110301100f0001000d660000007490010700202140b800d07900c034000c1d01c06020300701d801c446010b0750910 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 863636708 1250 863635458 863635469
    0x11d07260303060918150a060f080c090a02120702070f0e010e1302132a050307090b0d090f03320f0313060c1e030501030b2a1c0b0307 59
    0x1c1000003880a02e0441000364101052418590003058040c0155103064441800414a80400000c01c00c90509902950b005001d001117071900c0c2e5490f001c0e085544032005d00c00207120f03000e01000100000d070158140c9060b20b0319000100c190b4200500080d490303158500442e4404110320340046a100b02070146181251803002054a840e40e0f081003102030241c89100499000190400c0c2002007505800340303110852400f4105050303420342904100415000c080f0311414031509004020354550401c000904072200c0d50f6030a079849080c0c600d807100501440b0b40003031100040000d400705160348281c0d0396406407500300c540c280b0040000d00c182c0311502110110340c40480200b10500360700361300710082e681085040d10310300c0e43c00180e0742d1070200b0b468204d03004000007528900403d8807004018080e001c051040d0a08200369415622103a00340322005082e210b60700103075213a4044002481c0424201c0d80703041c18820b40c031055401c070859445007241801d1004541800b01905440c500464003508880f03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 863637958 1250 863636708 863636713
    0x4091b0e0402090111010515181302090a0b060d020309010e07210f15320402010305090a05161a04080309010c0f080c010204050111030c070512011d0726 67
    0x2540c4008000196010184490420030094103500c100c01c42401030a00800521440c00b01d840c2e1584207000da0610982e0780c048980341004240078007141d140d403000d540160144c81c04041d80d914062160f0203010b00f00f11941d00705100203051500d0394941d6020b14058010180244490f0507060f20f019510611406031000c01c013004402000c0ca01070561501e13500c01d114194408101516464a112580d14220aa1300b010f444052500000034481c0c2d071010100801d1018000a0384480461001060300400c0241410766981c04299004410400c80500c030758020100d400701c1c04141c0707620307040080d02d11500440341100300d013030b248204007541624251030b0040011800d00c90b4074001180c2d081e03107040c8143e40c801c0a00c3e501c00081076240000306880440c83d40003695a078a000c0004000744501003c101c5103800038403588800c16008542d000489200712405008110409041401848070f81102e20714051000c00711408070740e000c100c10307080358003400d2140c54424041804c040521441c00d2010500e8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 863639208 1250 863637958 863637977
    0x6150a061707030c020f0610060e0a060519050403320c0310110702100203040e01050d0218090316031701050405160305040807080a030510080c06040506090609030a0804091b 76
    0x2920a40c44410b04400c517204840780c00a21003802400e1260913141d08402c0042c0580600a05400ca842c01008010690f5000700d25403800a00a00354054411186413840030004a10a4a4454000c0e039000c0c54011003000058861180e40c0e04003100603000e40ca424480040d800c00191002150341010200c01030098401d039100070758444010f140c201c584250705a001d0000f0005629074496603034540c211034000316907540c00c011800f440340405a10140c071421441e040f1038016110034405a180e8132035084001c0b050744031002e60754154001c9440720b40702c8424400d01c10051581c0424801d00c036408004840040740d803504240f1040d03c800325100e05940d4200803480d40414442c0d0b21466205019006043c10141c40f81d45000d00750b800035a85030002915001400044403081ca2550010441c1d5001001c0001c8010003290040c050303403080300d126100202d80c1c04842c0d2161701c12102a80c0f0000c0a0780e022030400c1c1741c480400d402500440244500d131400b618081c011019015010183c6900d0f0210342 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 863640458 1250 863639208 863639221
    0xe0901060512150a060b0f03250c12091a071e031e1b060501230f210607021c02060708060d21080a0e060c09040207050f06150a0617 58
    0x21035000d40b03692209a175038a000240e00d4005000f8180094951168540c0c030b04204c040b14003441a10448807482041c041140882140c024002d001550303406003094102103002141035070108100d6025582104502050030022001d010050402074462140c00202804003224007c0004000b8030080103e9003080c0e003004c0c1c40402008004c0003403824904421514921011201c05282c21903044440344c2d00d810041c0186040c40403024503402130300381a98040c102c0f9a00003100034010300b02d180d000d480441010030009944808924800640104482550800040003551003810b6000800c0c15801600c610405502c0490a1070154a8941c1c1d1a109600c90304100400c803001c040381221715403e0304400c0828104080d00304c0180307145030f40301c001c0e942c036200c1d01000c1aa1240840000d098000d1300400504d0015a0180c645036407041d900161680703d28500307546405201c41ca50741e0303c1d1055108001d401c000e40d82d44c06902c16804d4070304070220307940c40c0c4081d259180151009154808c2d0900003803403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 863641708 1250 863640458 863640493
    0x606030f09080f0906070618020f03031903051504060314010c17190207120f0809010207031d030102070c080a06140103030503070e060d0606090e0705030603061b040f0e0901060512 79
    0x18840001462246840700d640e807150f0488140058400c0c88d40c030340c43d0b4030009601d41068101200401503020318a018651406000303030000f00d03940c1c3e400345940c0300041410041c40610b00d015072030000e401044540d03101d0800c210880c070b2446800002e5820f010747e120703403d4880c6686140b0f080d15040864400d482d01c03030614080f0b4103a032140d0001e4075400d00c4070401146070092042001c000680f940f07a40440c2103d170080c203500c0003c0c5142c0c0745a0040004400080e8001d14460856105909150b40c8090000010f4064070805002800e89010000701140e41000070560446880c0320b00802c00c0903103100002c440313000303209110140c0410340c00e00020312001d00074032009820000080009240c000340030f003028101d847c180c2141001440b154005d03c02820000e03413150300401345007080c074158a82500001d030740e840000c1160a5140c592616071254091a40a441c064004c920600b8040c4d900d403c0c001c40100000c40750001e481d030800c10002a141403007040e100c240c0c0b201d80050f154000e41300c20301d5a03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 863642958 1250 863641708 863641717
    0x10e03190501020706061d01060e1324080304150314060d0c0b04180f180f08070b0c0306190e010515040b1602031b090f070e0904060606030f09080f 65
    0x40d150b54081003140006491885041e02500060858218810702050030324a00c4c0c2c416048203050150214095100e9034854503540641b21402201080d03207030780c0185490401034407041409040303014500100b4010008409007003aa81c408010001081c8180001c0f4281d440d4500200302102001c00030a0b010b0610f5200c05040302d00541d06110150703a07401e0300c0481c59005038800d42403121000260440013803940240032031881401002e11045505e07028800c40181074080c000c241e98184101c2c1e44c1000100c20994a000341c104070400a6480e01c5600350719154030444011707105052100d8070024490300e071070a82056552904406d40d4503070806080c4200000c0180e61003549200c00c4c000016645c60010007052040d80000c90703803011501d03902c18075242c2004081a05010050815040300751307290301d0300d550b0f4051104036900c0307000e440300c85080d2804d210307082041e038112251030304200c20b01c401600040101c401980d010041c00c40e5411102084542c60980106404c03030400c10a01a801c0110140c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 863644208 1250 863642958 863642963
    0x2030604090212030c190b1518040f021021020a0210090c05040b09040302030f0d0b030d02060f10050120010e032701033308030d0e0c010e0319 63
    0x414401c1d60b00083d80c0410050340203c282d91000800805240c8140481e015000852008411b0083c840d9241c0400c140c004048c04c0e018040c0600c1d0300200c0da0307040740744020804107003070f082202d041604141c05a900e441400741d0240782c08460b940c0c20503202c1c6040079000811150704011010405407880080e40c0b044130014218420704031040c0f520250341c46039a4800344215007200080c0c1c608018001900d5044214600c0703030520304104000b290300842215140d00710960b00c943d031001800140c10007002c2c801915600351041810240f581c6030002036041c002c41c920a606c001603500e0b0300340c65104645a0190038001440405003401006c02e0411207200c95445a002140074006c2d070f201240783d03400c840801c111801c203450305500741e103601548013181d80b182072074140401081300f9034103c1554002406001c440300d4014481c10703029030402200020303004410035248d8074003136000117001a012820342103916004907198841d2940c0a084400c3c0400c40c003402500000410703e0a540c11740b452803005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 863645458 1250 863644208 863644211
    0x1e010801090606062c19080c090105030312040303150b03010e040b061903030509040204090c020a060e030310230901080a020108060904120507050705030a0609030f0921020a05030d02030307110601150302030604 92
    0x240786c0300004c5404000142c2680300042032811015010002c8420f0180d0000b030180d0420400c528450384100ca80da03a00540508011442c0081e02c60304508144156002c030000c6100400040744d14000312002500490084008200c41d8507a241048815a910300c1d0b20f010300d840742e450400001e401000901414a030080005041c02d41d00c0c85078206540001d064100180c001240d20003c000c1184181d40c20980240b00440c114949444090505203203409041d22042290300b00540c0342c003a6070410808404050b01c1e40c0200d5968901860342c50803008400c9010030305007000140c0500f06103010510954014034418881d01522106aa29510001c000e403568050688085000d44003000101a0103100b148002811141400c00901e50102d40d1419170801082440400c4040c03410503078845100340c5450702c681e00d0551880040c605204d994000c0d6014090341e0300c0d8904d0550040301951040604d500e60481c02c0698100158488209015403800301400340b090742d40c1385200742d0155900000c044c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 863646708 1250 863645458 863645479
    0x3061303110d1e0201060f05040f020d0c0e0f030f0a3509040f0e06010b09180a200f1c14040606030303180c0b031e010801090606062c 59
    0x155410001062800c00c08900315240f0400c48080407441d10354800c0c90303407000b002200c0c2020101c003903825940c0305091040703446001c01000d064075a411a044603008180400c90700382c01070009000e03485a0040244a01542050007545040102d1641808400c41002d0b069401242d51122050b0340251200390191a0340a03004100c11b41104441c41c4180c01621066101e100751010401900c486144681c00c25040c14941e52090100096a5040d613660311003081c1c0b6036034283e02141640000403a0809001c13081c4080c8500d80325a0341c080780040f90340210040c5174010080d0042820300c00c5c1042d004000c6070410a0055a02a1690543c10f0215060000c520700d40c4c400600c05550300141d4094441d59507460741041090341511800314042070346881428052040e407100c03100d8070054450072030308242c00400206440420b03242c450a00c05100ea00100c6540c6582e0b00c18000c01010401b203030058544100030a5990080c00c134442505049500d440e80034400581c00562040c0340c141d40d541008080c0c4c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 863647958 1250 863646708 863646737
    0x610090f0608010509070302040303020a0b0a022b0b03070308120a0204090204030b0f01060f051204050c040c110c041503080a02070510031410050612130503040e070210060503061303 80
    0xd1000009040d59a15644554103010801c40800c8002c0d00b1201032501c108000c200194010815003003168121801000950341c0c0d0941d0fa01a00c41c40d1001040319407081a401030500e0505200b18020810449c20426000e1910505540c1c1c800e5000140680d01c1c10b010400a0030842c55106502419240c800342c1410741c4c0741d942d042070f600203800c2107072103035440c0040003102620024190f0040020b460f00000f22005080d0280007881512240c51035015104002424040200260420300e000a441080f6002c490380d0002d141e12042914141680a5070340d0842c841d1820380609203d4801d50500340101c2c1d4516500e80c03040b6401414020254091000000303465540c105c01c00669101d80d460226000d500a002d8071101c08009040030b40700784600e1000d0105865010075101c001c12100c0440c007c584034207403040545600700100410780e10000030040ba55a80786058203020b040302d90200c0746d02007540100711090361014085c0c250076610001c0040e00e20b440b03c62804440a0190915080818124 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 863649208 1250 863647958 863647979
    0x304290c0105070c1a0f07050708090a08150c0c100903031e02031b25031e020a17070210270b0315030d0e010c02012705040b01020a030206061009 64
    0x300c8160f0042600d1003a2031080c400060100440d00c418111020b80700e14010803002120f00025002c54104800800c000d4100803c0900312104181c4c010b140040080c0d5030303500c041d81c9034031240f524841540c02c08013140800a04000756200301d11070350013070144908003a14210051050030750030340400d91107264a1885103018a54034020101c00c001c0542d0328030b0111500548251901c112060b100300400080e41019402c810742e41c80140e4091028803080d41606003111030301d507103005905c081c0d5064102050040d400041210b80244250088a03400c0b1005a5000040c0034421001c0c1d009035900c1a80030340d01d4490704400d40c0056000c0c04180c0d5200042c07030300442c8192190440d6010213400418458a1140072160013a17040301140200700507410300b84018000680d01e00505d06216154450340116800303200d00034181e0051780c01c0e8074988409440b0030744040101c1d110b598002d45c9800c8050352254400710340300742040d070940c00a200d291200790900603090381c4e000003001008a41c2c0008501000b01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 863650458 1250 863649208 863649211
    0x40f0201080a0603061a100504030f0803060a03020a08010203070210060303050a2a08090306010503061b030709120506041b06050f1305030f03040608070512010509041103011d06090304290c0105 85
    0xe055030300c08102006c2c1401041c01180100e02c0c10310106102c00c000058002c0314a0041c2903010340c05544a489200c00f10f01c1302d41580d00000d52042d80941c0204140005501851050700f69078210303144003001d00f0400701151010701002d80092420030100740300718029100c40b80c003081a41c1c0f81180b40302404105070380844c201c090841d02903000141c40c000030319041010902400b400c402608203414a60700081d40f040140200507107051002c80010345141c062000f0f9402081c00080000c80080c542c5400c50f01c40f44121005c40e03403d504002c4070780000503e443c01006544c035949449140c030740341304002c4040d5001002c00c2c81c0d12458408000c14251001c4c8800c10307001d000c90b0001c0d920f603420f0040107441080d00401c0001000000e020307082603480000e0103503046500c05e841c401c040b13841303508040c00d80c140b030011001d4040d0b0a00041139010a009600c110305481c02c80e05484141d1030b940c0c1c8151300c0344074910540f55485913110305002c2080701620b4508203400500b00c480d150601c08109242074420 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 863651708 1250 863650458 863650481
    0x100e0a0605090f0618071206020309011b08061e060406020601061e1d0d0614010f14060706050907030f150b0402090904080a030b130f1103040f0201080a060306 70
    0x442600941006000d00410381c01100d040094a1902503200c40203039180d0380105000301014a605034841000020300030b48002d400c41c800c00c1d45000c036090400c00b019500c15202209290b180070b942c170103901c500c66400302580300c00d84c1e03c0841c0b030b480d01810400c50b1a0541305050740c00c80c0800419140faa16000200020b06098002c1c0c10341e9850000007030101c0c1c10a071202411108102d02c9403e0183d0b00c0131910031901807140c1d10540b0703a4241c40109148628021005066500d13000f009092481180340483c100c507001c09032649000e031a15409a40c442281e503240c0d40140083c0440c40003da01e070b82095502020090894120943d6511454240c04e000d14080c1c03401c4030411b044030711051840c0104113801d80300b6201545040720000c0030400c5250b0040c0082c0c80c003180030501102d0a0b1184d0818143e0b09001042d0807800070310641000028520f0f58003404441d841c04600950070005403040d20b100300e4111040e84101e080d41c1d001510440b8000306203903103890751440c3c04800a5418401c00d05202c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 863652958 1250 863651708 863651713
    0x40b030a0c02071a09090403031404051b030d21141e060105091f0e0a1d01051c0303050a231e1b070609020d030c17030423100e 56
    0x4100d030002900380f04498118050b81203a0300d0028419000c04421640c006030207441b21301255075941400c50091140000021048a00c0c01c00e00090050000d01c08142680c00c8a51112811441040580d20704115003101c0c00705403c4410172550030b00c00000c03d02200c0030000f01090b081d9102c2e051201841085030001c2ca492401303111000f0515855607141d600120070300308035182c06201e10001e0480544071100742d2048550094803017a1501c6442a00300c0c0302006081d00c49042d45800c0c0000300e044109002a02440441c800050070707284c980a403000015030510101d03007105203602e0440103404001c24134100c0b40d4940100d4107400b61540001c41d454580240d4010749800c100017132000e600c0c0c0c0041b400340c1c13a96a040a000b080c60700e0b22030541d074040e030303c04101e5520003c503c0c05002621400c500654440d40304483c2c1e42c24150801e90703009078148100d501000c02c54400001c00010b00041d2000350020111404040c80c06000719488968041008106e81c086202d20404906440030855540b4858 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 863654208 1250 863652958 863652971
    0x141b01090305030a15120212070e13050613020f0d060b0a14031915090c080105010f051507050d0302032211040e010207020f240c061005090f0a0b06040b030a 69
    0x220094450040c00c0c500e281c07185280d462510324044001c140c8071b40007910032408541150701002c8204810741c020121840c4078a454580503009a5240340c1809007504c960052100044041030580140b01001c2e40c010860003805244070280012400034003003c0701e00e00d0b0340300140b105c0c650320400c816008000005819a0860425040c0f604140d40344035000700d406140c031204000200300400e80c1d0444100594000760b841c0c01400e10f58207118482c0c0c808405c03546803d0020802c442001c0c5c90006803402078954950702c440c0915980c217180704980d400350040c1c000c08110125188280c000310340181688000140120b4880003500c82c660b442e1500300c0760310120a04000e0707182058080d030021060030400840c1040c8064010483c04800305407202d01c03511012548445072070443d12154880d0b0400d005d5035441e01c0803d4021581c0304416181c9803960305c1e00e000c00040b64a00b58101e144101081c0400c0c091940b182c032821b402800031078036520740c0080144804a0440054006180f048125200204d2803 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 863655458 1250 863654208 863654221
    0xe0102040f0b0a0c0b0604111c0608030f030106082e09110c0601030f020d0b070e031009081206130f1415091503150403111507141b0109030503 63
    0x542420b074421800c496050200c407214039001090303660800d03005060b140e000ea0328000010014241804040c80078400032644a80003403d80e0440d450300c1c81400f00030007203c0e4840c07101c0c84e5640140c1c2040c074040340007040103001842c81071001f01c1e00184214540c582d0248118188481c1c0503092006000d4101100402c004522a0f400f584c08485819801d0a01d4021201d940725202c4005001c00f5003002d000c0203c0030115202c03580071000041d0404921036140c20051002041c0b11900d02d002c5100c0d1107100c0000d0504501882200802580010300602c1c0000c030b41d07100b946841006005a40c0104201c0703d611800049009502c2c0901040701d001443d03003076000c040345410101602c014040c20103036a0841d0161a04803c842d000300f0051110013450352040d0009286c4001c0b03052032089985030b10180300406802400c01d40440140350141c41a00b4400d403140221954203d45080004114185405d2045c0c8520000c01d14920141d6041c0c42d44001c5035030003800c0d141134100403000110000100b025 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 863656708 1250 863655458 863655479
    0xc06140c031e01080d110705090f0f06040b06070b0403111212010801061203080a0204180b03010b04091709010504081b120a0512031f03060c02010c020a020d12050d0e010204 76
    0x1850b030914107640c051075040a521980c0d031500c02ca07400f01807104640d6903209092007044250000e00d802080d81401d8075000d1281410710300c06543d01091000fa001c0410350620303140c02000750541c4090034a40c140307103150312072000b0b45c44040d10540c18405003014494940000340a19840e100c100d1aa81e5528041d1003411414203005902a00316a494130800380314411703103c0c10040c0155013500d8016417030348400c00e03c48000d10507640036005610300815220b0300360b829500118070044041b0020040d60130709005000a0703072280d200040c48566401901a281303462800542281241807400340d0400340c0703940c0210b2501d00c2080e655400440010307100c02c000c0c81d00e610050410b202c1c10f00504441c0002d40d80d0a50b403049410020101000c011000881c203a0101407105808001c0d80c0710502c0f07580e82c2c5e0814070000d002642000c8019402c110304420307064000106460100da01070900e42a004060b1240d10710551441084001c00004000e4400f803848103002c0c4034801c079003e80005aa89141031080314 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 863657958 1250 863656708 863656741
    0x706230c190e060409020f0d06060201050a0c030b031c0e04090f0203070b0a17060d24060b0a050f0703200708060a06050f0f06040909061a06070209070c06140c03 71
    0x40401c8181d441040007074680c20305413401c403101e46401517107464104000156a000300b1014000c41890042c0004a01e03505402450080110f803800f0040000301680c210142c825004240b5059032041985901031169110407060304507040ca021038201035207c0024082c3e4000c5078003642c1e801c0c0300134480c07815498144911001030200030341d0585000e01f040c0e0060444401082400d40401c86c110000e02c0a4a843c44c05216070355202459100b00d00740004408414140701c1001a0407915040001c0380c01c4410b03400b285e0250f80591260303401c2012030241c848441d03000c200203d08020400c41c000900d03002410440040c880010050603000303007040182880c01078000c00c2c5c440010b04102c4100f20684034145680306604e0141e0316030503281c44101c04503884e40f01d19406002e59918100340c44080c032007154050110f418100e000715583c00314600401c24075001e10340007c0c1d485a0070728081482e803400b8076501038003544210304c0400c4a5002d2601d0002c404000c94001059501c000300704601058800e9066 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 863659208 1250 863657958 863658007
    0x717030304230d0f0c0602210a0618050a090c29030f0112140d030204050102010e0609070512010908030109021207030c05030c0c0f0f0d090806010b0706230c 69
    0x1210140ea00d880603d0381c0c0c0c003048901e0310034800c6489001852500c01c400c0341c0801c5410100a564030030a2044241c400304050b200024180035040c04078503804a03a0103440111000325000101801440c20310380018076029001203181c40e517a00c41e500000ea010b04984d8010607003228244d58162200003540b0310b100840010004214040082000c00c900d80c8903002e06650307440f10740c01442207682c40c0101d00b8130100300c8180b0961051442000e01144c2c1a0010403d440081e80207001419514030341654415080d6046001c40d00300c01401e04c43e5013003034800c11922407180000400d4032042c90b1640003c651084c2c001182464000580280180d2200034250300400300d480c040004002d201802481c4d40030280c12490600000a400280380004001c0d5a481c004607109848198401d19540c40d40c5140c80035042022801121000403070f0000414054120b40c141580a1f25001480da41d00c0300901034110488468610506124014030148002d40d215842014100c5d50303071141c1d0520028810451483d6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 863660458 1250 863659208 863659253
    0x6061b0a022812050304030312020c16080d02060f0601031104091505010314040b04031b0611041d010b1914070311120915030901060b0307050a080c16020907020717030304 75
    0x480c002140001207504880e05460300000c800c8038965104003030720600cbd040c02c805120341c8000b03407400c0301700340800021144200100d1307410325030190f42603864600803550480e440441328002802940aa04001006810b0100c241d107400d13141d200d108200d8110100154542508090030700155815204500c140d00c0a103030b802da29460710703a95400e500e08000304010200f00a03d003010060714400307048a54540d07030203541800540c01098500400c1d410a2059408860b20400512a10714003030044906940030407241c2c91030141c0e0505090a0700c006220740703204120524010054000441e0f01070918240301e81c0e500c1d480c0101c0416600e24003d101c0044200201e400c10400e03207240e07205403880300d4548200000c0d549030342c2c4000ca075600600d1244d00c01e00000c1310001c20810910b80c010300620500d06161151400c6841d12a440c01c8540500703035101c0c0c07004480e6108000945000f0040d41d621001600c11200219280c00180310134074041d14104407503505c00b106110030001c40302411103140451015 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 863661708 1250 863660458 863660489
    0x50301050a240311040504140604050c071a04020d1505100906061b0501090b07170906040c030818040e0102210c0412060902030d09091406061b0a0228 66
    0xc0030340c080001c00b03840c4400d0503601e0310300b91801d00c250300582e0010140104100504082d070b082400400c01e080f2005445546043c0008103102e0741d1004ae1160180c010010007012a00301c0013045030a0405407080ea4440350500d010350010742c00081c0f9861920030710070042100e04021a146c01c0b0190f0310341080c01021b00702017092101d6503008026150704030a242c0a090481502d08180703005001c0700802501d81c06c001410050b00303a80010034586141d01c01c0040c1c10055444001d0b0580314001624004c0039601c0b888010000318141c0405030010035160501a861240302d40c000078215503040c10884400c1e5008111001e8100440e00907002040d503d1510400303524000300c240e001803056029840080c54402070141c2848015170086035030b40c0d40941100d906100d140005848255248101c00140d41840301e42c0b000990000019801000090038140c01d18a4403041d81c103112a403003042c005a40b24111404001da9181e070808480801d05840074244900743c840e5262061210780c20a038400b04544d403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 863662958 1250 863661708 863661749
    0x10e120c010c031103040605040302211905010f15050102100209100f020f0114180d08240d0f14030a02030d0218120606040e1911150a050301050a 64
    0x1480080410302481c042540032014502560513800b00c800d2915503202c00f06010032025008401001564000c035401c1c2c0102c50020b42070103c000d0a10b041d16031b42d070000103080086e10612000c105010b4403410020415254404212003240c10900840c02059584001080300e560184083c149104000d1001d515108580c030101c0d904c1501e1303216120810404545080f40c40c0c0c4207010b400100c890300d100034050b1407070300d14200da190401950503500c04408450180c0702d83c0c1000901e01c4000c40a40c44481080d40e503040345603009200400f101460842041e00301c0b00d10340d511001d410200744225114201406541004805440c1629000c44103500400000420356000030503284020150324015a5501c0c240f8060300d460b44030180507641149580010340103086020503900d200c0c103420388003002010b0300f82d41d05507507036610440761050383c00c0c5101009001c140480c0b01a0201c0c0805071103c11841c88e05414001247c2c040d000605c0000d0000c0014880c9181558180e0010a01203802000f21440c03c0b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 863664208 1250 863662958 863662963
    0x70309050c09040501060e1501030b10020c0f0a0503190501060501140720120c0411180904020402070b07020a0b01051503010b03060102070f060c06141017010b040218010e12 76
    0xc52981c407840642c00040d00b0810250818409480d90044a1030141041d0100100ba4109050380368042414800811200e0030070119050320032807035a0080c00c00d6000b0340d082c0445500f003008003542202078210042915101008184030041000211600061071400c00030b00312040f64010b1410406405a24403012003e281541c929907000814248948103504c0c1030181c41040442c40382d00150620301510003280003040301c0d02d06807000d48041c0701c84900502491079902c01c0d0a038000c7c208a449036002c0d1941400d07142c059000d880500014079100494550740f13091901181c0110040c0c1c000d40800c13040204076403400740100815500504101f0103050003002c140014000c0c81c4900b5400710001e00207038800c010034001003c148810426031900c0c0c4500400c04600e10070700380e41060512290a800042038020380b88180c402d100d40090340c50600074021200d400d64820090300350348a412006090340e0324401001c005d02101c1e505071244401500140c00217030f51001d058841c429a010401440030702 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 863665458 1250 863664208 863664223
    0x121008030306060f1e0a0f091a0702010e03010612021918090203012a0906090536010e1605210720060106020c031209091302120606010807030905 64
    0x7182c5290319071340d6900700c1c00b820340a0342a1006160030314482e10004000700200824030315804e69500caa01061380241580c010b4010300c0340309000c0124810052003828440040c102241c0b0500d0011071789000b40300042d007075404980040b14140403000030501186000c5a654101c0b001e4100091541840c00e606d20101044212103204641e0300c900c05102150307401c0d40880e00058400f003e2542050640071040004c100c40c0f1003d03008540351010124069005030380300d4045a43c001e1200c0d800c09181a6540f40704415480c1d02c0c0c0203079510400380c0c4442000d400803903004e041011022000d1b07180101c03c0502c41c5907031503012014400100a81d441007182c170002240f146100c40340000440e03da80030b08032103c000200c5001585500312016550700000411010b04850300c0e070b42146c121038002010107460342d8a144905001060420500071141001e18190742d1040c4561034005020010b900480d14811007240b1801013900100c081000c0b942e00b00010b40c0e044000e84c541001100b12966400d03986a15 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 863666708 1250 863665458 863665471
    0x108012d0915020a08190b0a0b0706110d0c020c0105030105011205040305091806040e07061d060412060903032f160507240201090b0105040b0a0f0b1210080303 70
    0x315014500c05001021545440c2c0044244045680c3c0d02180001030101c1c000761112011603510700200945540c01713000d4a0b41c0e40c1c000400d8400c2142c41c020020700990300c14034044490540b50f03140d200c28400128003030040601031500104075114181700c000d04040350b80310300b50f040c0039041c0014449642e200c407024081640d4040009299181c41c18203031041c0c01500c075003981c88021010081d4000030180001382c01407005a805104500c41c0400d52511070b0700c0b0740031701c40001320002e01c2e4441c22004c841101c40f0906d006842c26103000e0301c80c00c02c0605c0e803040038403e8a20503100d8030800304140d418821740c41c041159035a81c0042c4001c03d90341c0084103281c604504080140844c1200240701015110550564800201c5100d2030341d40c0020605502c426000c640818003912001c1c641500601410304640c0d4804826a216800c15040100800c00401001c0d003002e0306800100710a180704000d02c000d011714031891510f0f00214440c501990100919a030483c0c0104c2c80c08101040c00081900d40020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 863667958 1250 863666708 863666711
    0xf0a0c030c02060406050409051510120b0604031a060102010504080a11070506131502030f0304020904050c040f0b040b12030702010c0327090506041416090314060108012d 75
    0x614102100d684586281c007079071100002400140755508540107000301d0740c40401c280882c0e560724190b00040b00c800c258090300a42142c0c4c0c00c44050b48507400052134005442c000084800c100e0010880700c0e0000c0d00111030007440401610912150314061950040017403000344a50f213002e81d41c5403c0c1d03000e2400007409000d40f03808801e0b2074180c00c0c003140003d010068034079901d600c0c0441910130070440502c04e60b0b1550011640600710340384080700311200203080c0080f583c55500c841d400c3c00f1407964001c000307640da40902912401c19550701c0c0130310700070a40c10b10004100b008110080008507440030600a218500c0c48081015643d00441035032204c1d502420306000b8a500c0c1e0600740c49034451102000042d0364440407050841400c4034142050707a115820409c0955110414003046070654054400c4c2000403034000344003502d8160b042c3d250380f461480c0c2401d00c3c1da03495a030390b0141171110003186425044440144503e1409103d112900b04000e0307201c119680b04201c41c0380c100c0c51800c0740000d555 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 863669064 1106 863667958 863667977
    0x11160b0106050f0315040219020c030c0f01090e0901020928050904150f150306050115031407050c0718020909011728060e160b0f0a 58
    0x290740c520380084c034603142c1040708441605000c10b284e90007902013080528000a44400c1108503030aa002496007000300020141406158034440d40549003200740c18556070391102e130080460700d481601021940b43e6045c00c5019104001c0303a16003041896840301c203600c40d0340314241e250300809662040d1031034944041002c1514150360107844030708202005140d100c00c50b8480c681025221800140c048198a2080307100e504941c4291503280c0e40300010040100444840000080d90307140401100c81d0415040304071842c0500000c00f08880413034048805a000c000800241038000c090300d204144661002c4080c2d07001403200c501a500308000060901c00040c540c940b407443c04070150441007100e1240317060200c0310507c04904210002501808141c16102d0146042c1140700a020b40340d507c1c81e0b1000040c0a035034481d00c0105000c02203000101e034590159107480a6030328041c03065 = true := by decide +kernel

theorem cover : BRFrame.Cov 863489208 863669064 := by
  have h0 := BRFrame.cov_init 863489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 863489208 ≤ n) (h2 : n < 863669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
