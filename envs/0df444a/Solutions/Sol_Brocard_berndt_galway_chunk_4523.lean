-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4523
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:53:34.998022+00:00
-- url     : https://prove2.me/submissions/3201e4aa-5ce5-4b20-bd42-f6694c0d4d9b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 813309352 ≤ n < 813489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 813310602 1250 813309352 813309373
    0xf1a03030d0507020f0d18080601060831080d06240c060b060406051c020414090702010f0e010b090606030403020303160e19081603020f04020715140412080702 70
    0x740e108540c043c2c4184112a41c050103c00890b081c102d01010040000b00040300350210300c02e80c60300c20b10080030b000780144810741c5854801001d000000d880d0314095000d0f0560740101c3c84480c2500e44540e6086601e031000080103141402107075120200312150036042c1100003903400040240b1507004060b100094540321002c1e1811110f880c3c183c1000c03205240d039117102a02070344411014201502144c0c492642d6010070700504580c0003100c1c0072441c1f07038500400043c003003004019840102c800040d12038142c01d854150050303002d0f01d411212002290b04c2e1010b5110707505415001021600419940800c00340c070b4800070f21003184012a40500035174000c00111700c2d000b581061403040071b44245080f01e41e241e000800100f030100303000d25902c04109103a81c01e00500009000c0c5480d0420340347c3c0d1046506146a01041340d0101d5240f1061049031b000c242e5800f446205914522120550302d8200001144240307086146541901d090b9a1030441c5101100b801d405040007501600030381e001001c46c1e651 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 813311852 1250 813310602 813310627
    0x51501090c0e0f01050c01020c01090809010206090a08191b060b040b241e0703050702010e100807050c010603080c0d0e0a0807052709070312020703170705030417010f1a0303 76
    0x51b00801c903c66608004684003804280300f11000d481c420000c0c030381d4030f02d070900c002880c083d00034204618982004c0d0740400040c5809084070a40c51040780ca54000c80482c510039903c01965035809418051001c005404006141d0b120311030300d8030100c408120042c882c100340700b0b01150f40350302e09101540c928843d160407280600540500b4990350002c5500c011120703290b00302c0b5002450210040340c4085410700031583c0109001c0711001051303650340784912031200028040c02d0040c01140c28001c00003000c1c04041c0b070a4000a016603080701f0780544d200c514408441e911044400342d1310020b04240c00d0900b02e80385c1505180d04644030300005143d802d081c9030401c29aa00301100c03003425140b44410603448600c0c1000403500ca010484003800c145485d50a146200039010301c001c104540010009000103000020955101c1a54030249929078000b032504a14611940d004651010803400c0e10080c84034054200d103134911a207400c203000103819480500d07100d000c82c8100035815001031001804404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 813313102 1250 813311852 813311857
    0x21020a0203032a040b070b01090506030c091816091413080a05070c0b19020f031215030105041b08011812090b04060e01081f0b030a09051501090c0e0f0105 68
    0x407044000f40b02c0300c20f00d8003070701d0074150300607400b6030000c4102041460522003007255190051084013401d2050745403400000e5100c000071507120b44520000c0001c10f4800d103c00105031401c3c0c44400445008441c07800500b8019076440c412007454500b480100c00107980c1d0355051500500d40d0a00006a0400558030f040d159000305c0700e400c003002810300060f004580002800001010202282962416502205100d5010302c0c0300704415035001c410b0802c50481c00000702c0d1030b44000060894496100c110001c154151404c171015819820030701840b0900204241c0e82c1170409014103280c1945036030310030780d40c260351a802030071122141003c040c0e004074020601d600400c82091600040c1c2c40c1d100c20710110780f03420a41229000a0348407050300c0756560002d1340d03ea0440f10002148600b8403202c044a46a04068040d00c440b00c200440482c61003146500045402a84003064640190181402c8540c0000c24031402c00c0c6181006040c409aa020301207100041c04064541c1c032446800c1001550190b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 813314352 1250 813313102 813313141
    0xf030c2b050715110a020c040c090b090d06091a010806060312090102010f09050c040c03021804020a120e15011728050a11040608070f0e0a0902090721020a020303 71
    0x8007060b800804a03841c81c8194a07a4084c05203001ea00c4c0c552841d0300901e0000c14000c8203001e1443c29a070544650b8002c1031103812503194604255a5101400100b4081441000000c007118200f0307040008103c0d1699294643e140e0a40103902240e036100c84480d6182e90541341e071505070304441c800c8805e03150140024286090180004071b81e06100715451001c0303401c001020741e078075000840c418040d4500350190450310741c16480c1c290b090a0510615a4101903114001d92080342d00240b90804217004015071103916158070020451601c5d041000d503100d07940c0300d00c0d041a02d018200081002c0e40d80b8540f81d41068012401011103030201c00d16000c4441d0b0850203044c0d4401484c64900000e04108504581e192081c541c8801c20b8801000340f200f9100c030340d00164001d40010030140308aa881041000807608061a001600c2d01d0b202c0c04030700140f8130003001941000640c410040700039008211111509114601600305110814550040340640030220005820800214001060185121229 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 813315602 1250 813314352 813314363
    0x812041a0a0c0b190b0103020a0905040209031203010914060402180f0609040c020c0f06070317070c06090308070822030c080f12070210090c260f030c2b0507 69
    0x2d8003907584034100042c00031208064400084140502c0344500c1c1e0261050010080c02c040d410300e40103140c0503003043d081e405103501440d4081142d0140d40c0d0108840360f06c13080440100c568035611303240d4680140a0700c1590b042100465804220360341401e2080315a00208503e0703030884123106d0804c011030604218841640202c06105c01501541c0754032911a00b0f10154006040425824040c05143c5501c007840074442c0106114842c0480d42101c400000b103091005114003542d11138a0564140c141c102014145924003205c11040580041e5028040c070540d40300d881c0c181c0c0c0c0d026028042c00d291118501c1c06044a081c0c0170001900070200320040c140b007100300714101505140440602d40007030340c610b002070700a0024080394540500c4501c00030074105100b44208840758507183c03a81e001520403a076820035101ca45402101d05820744a030081d8480e0142c46da20810000c4031035a80d0019144000345008100540c401c404410b000010030256941a010012824420540e856003107804190303003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 813316852 1250 813315602 813315617
    0x70f033005190c050a021603033204120b151011030d14060a0801052a1308011d03070b040201080c071707030f1d06091503010308040812041a0a 63
    0x1da0454090044a1010fa903102c0b44c0b01c4440d403100034a45001404540c011665040091012070791000d070581d0030900c040c0c4107801d8020000800343d00040142100007840c000441c02141c1929500d4441030010f018500b0882540c5075212510800528010b0b050b901042e62100c1d44030035070241c1c0b111207051541c18141e13401c05046c1d01d895400e84510a40b545212001c420803c203851401d000301e400a040e4500082095141c0206202058103004039804030b4160740c03503a03403008441c05104544a000420ba24515030b90780e50f8520601074120542042003c0d28062804d6940c60000000d0321184e9401015500c1e20381c4581c0c0041d00d0440c005000f201808804000b4880807030442c00781c2400000a210200341d4810741e5060040c040b40250014900300159a01c000085201041070b00541c07407070844000303985100c034030001141484113007180789a80001100003c107110131398010780211401c02c01501c1400001a8441c5a50721440c0600e40603480d44400300141103440d41d010b0081d9110134140f18a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 813318102 1250 813316852 813316891
    0x6060e060a0f1b150b0907020d02070501030b150c1506030a0b0604022101030803150a030b0610030213060206010f05120706030207050a0204110a020106060908030f030a11070f033005 80
    0x291098404c1c001c010b022500c4810000c1c02e801d0601d1000d91000d05131018000c2c1a612360002512145140705240c10180c44008083ca1591403902458081148420003580e0700012900300d0346400207101200d2a200c22400003414506001c02e40c01c820950242c110131003a80d8210412000390003c80b10310a07419980c8586a035980200f0650318003031405542c030240c480c600380305c0380585052004080f500403142c8000410002d100380001982021040380c3d5013000b1507180d5005c90003401000c0d00010074103031a0380c0000d40c494000c030328103041e60800c1ca540038840e41c5030303428020b40b503180358880740b1580d1024104100d498800d901a0282902c40c0090b10240c04441d0001015550303040107242484000158200d1100c0e02442075a00400440c1042c0b50070300d1400c00c3c100c0c1c481c0242100001d904038000300003800e0300b015501210309030030b8030343c0e403551991100d05058800a0031020121702042500c0c1645450728036000400d8100d00d0780c01d146400281d81e80709a107000d0480a411140701000c22581711 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 813319352 1250 813318102 813318113
    0x111606050d110c032718150303130305060915010e0a0e06040b1503010e07050d0c051f0809060610110f120c1023090a0c080106060e060a0f1b 62
    0x28422202c400d002952184070042c80c00050386020990f440002d02800740c41c0b007043e211241144500140314020106d19a90b0310903241041c442a010b50768103000020315542600110809030b000d4038021811100caa50304c18111076aa640d0070806a48a250354100411400962090650b84419100300210f0740c022000020780c034081050f5011201c40511100304041701d0381c20f0b402c00f841c8033701c202d000b4410f400f03048502645844075405254019081c00d920301051000000d00b18000f007a01500310748009001d4a010203a01003044001c4000035410703801f02d0140440010124004c2c0b10003807102084003e21003095070b03035036044170030280310b40500140c0ea00903c0703052280300041d40c01035806c207075194000207045042901d5000e2401606240c00c001c5103645004c01d81e00d2140803003c80302002c2c10780300d402d05140360200306c8100038900032050101107860385041d04414100c92b469140c4144104000e01000603901548121500041190a42d010058421103801c4103401d01e42d80036224034001511070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 813320602 1250 813319352 813319357
    0x1e0613170f1c020a090308090a08060412020c0316050105130905090d02010c031a090a1104080102070227040609080903010e0f07090b0108130503041212111606050d11 73
    0x65081030100490060b410211070810840c1c0d102100e0021403400d0350341140900b0030026404064860100403501d6a000d444412800380a00040300849449140c01d18003021003190f0150544014040c0d10ba982c07010703080000e48000c2c0300300c803c441d812109040c40b004489903040304100351014006c0980005000401b8442d6a00500040014106024000381d001e030135a440c41c0410801c041c600066450b820030044c850b4201c2010072550b00103151640e4000c071000d072042c0302141d141904002400141140150f009020051098401d080600d58614ac03039040e280c02074041c06c100e41d4038000041c0c00a81079510800c009441554107605200000d40840e0856943d045200d07026480002052000c90040003208003c05580806201492103030300001c20700c450180040d031050240e00c5e043c10801c0024030a41c1c000c1c3c0000f15404600700c03c1428920000801106c00d680030a60702440f6200318200810400c0b56000c4013040800c030549045002c951541c032140380415802c1c1e84196200400049400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 813321852 1250 813320602 813320617
    0xb1e011e020123010614030402180705041d010f030303090228050a080c010207060f143601050f1b0a08130e0403020a06020d090c0f081e061317 63
    0x1190541c03000040c2c4858a00c60f151280081480300400c4015805180504d0428070305100d11f48a48851012500000d5980040170310115901e00b0050215071100103401140c095418441d410040c101061404040c280502c09064040380c100340003281c000e420002135284040c008190000c20b0f04040351702c002040700d440c8100d6108a01c204500c0c0703888180e050140c950400503050702000c010010359101d07920301c10141800303075403c5484a250700584440b1403120517000c0c010317034840d00c1d0030821844041c1c1c08001d1500c025800c590030000020148410065401071b121940380025105642505401130724203003500d01010b40d40f4540e03c040c10b00030101c203913108240098031080130542c0000703100410b07040b540a0704040f104100119a0006900c14120341000b00181d550500601c8200078001c2020b02400280040d01d000800c82011100941101c1011040c1c0346d0f800012a10403006c821074a8241c159980700d00046051040405005a003141c82000b00e03041240b001505941250000030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 813323102 1250 813321852 813321857
    0x3220818060730030218240c010209040e010c270803120601091d011217031003030801080a11100e090f0603190f110609040603060f0f0b1e011e 63
    0x72036214607658600b00b10882c503c1c0c0382c2010750070440d030002607400312a03124262501c0b8007040f050a103400059550548070b022048180c0907a00d4820312503183c080c1d070200303816078000ca2070940c513114003c0c411f118440b0070308050303a224541c1c000d0000fa007107144040940103030400500400b00003003d000820007020b12002c00c5031039074428035218001501020480e40300d20300c0d001c00070562446800107001c02c0b03415118030307100c400583d50715030a1525040840b0b0701c090380d01034000024171140420b017445100840c0d100e0355031002d6682e00c1e080c1d01501c032074810100400b0f4080c0644a003c0c07602e8806004407105103c1c1c40c0c4000791401120000d80480029504071342c059414509000d0b10742414040400c4c0600d01c0062483c58070003a030750751800c4212440000e07185e101003100710400c03a600d2608070341c004070008005100840d1242001070081202011034140790f450602200390001e0107000344031203480c0042c1802040307401e06c0600a4800101017250b410480008040c052014284407048051240303075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 813324352 1250 813323102 813323153
    0x305040c0f060305180604020114070c050409080306040e2107020d052b020114070f020f12040608010f0302150a121109100e0a060311070204050705032208180607 71
    0x8500395100a08a01c005d207041e90801010000940d8000c0030b041c0400081e440d03c1940d552080c102480101c400e60409580241403e50901c00c2c003c6c1f480142d13003c1e03401110100801001000010750f50b10f01500c0c40201610240d6505443c001902c2c0640810790014240b00188101ea503240c43c101701d09500c0c3c42280c10803545410400000c4084c0222186040d40002c00c190640b0002d2901c402c200203003401c00300251612a81e0081d80300384101d0510043c020704480506120309a14405038200340160700000e0003232000042c03072154028101d01143c1d0060004c44040c8550440503565510040000d4140644018503020f540c0b08e1744034000d003841b8800402d41d1541d11503020801c1c02801d0014050030080180ca00300e0b0390703644a4103450221a1035050000c0d010b111a4603c40c5c0500172410040d43c0617280074200401c040d008402144109904e0303d0103034000c2e0400603e020814052038028046c00c0c411f0000d5010340ea100100840d030b0080080c412801d1400c10b40e6940ca018041c018040d00e4000003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 813325602 1250 813324352 813324361
    0x1306020609121e07021309081801080f0703270c09141506160807050c0f030d14030a020f0a0306180e0c0d0f0c030b041a07050a0305040c0f060305 64
    0x1070110b42d400c505400303219468081034640b0360b06041080d00340040240d41c0002d4500440d502c0c1068038045110300101800050104e00b03080d1119000240c1c2006144151083e5404ea98400d9061038440c540600040c889a11203520450041000c1e03125880031119880581317401c90020101d0713100441c440c4005207641400c0c4a4181d0a95040c21442c8102e03086180921420b8050240d0784811807106807410b549030310003218615104001a003000c0c1400320700050500501401161200350303417200381c1d0f0510001d05002d00b4036030354070324000918000902c022480d40400c24140f00654212104c01800344c00c4c0a0a00003500706a0322003008000802c0d59407204201c0341400d05d203420311510b00000f04225414a0858141e2034807070700714015106451004042040188890008143c00d42080c01d0600e2241c89250030608074100340c2c3c09a80c80100303a1b0b1080000039000c10254400c45ea550f0300c583c00e1490108050b8050709001d00121622142d5460100d18114803203003910007440703541d46c01315140c00d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 813326852 1250 813325602 813325621
    0x309090f0b3303070f0c030203041208030609060105040815040201020114070c05012d15120f0b011509050925090509010504090f0818030303010f080d080105030d050f13060206 77
    0xc2d03901c560718403110a1040140c00b80d0007020090141c0e01e541040e0b000c14002d80750480c02c511031034101d901003185003001142400011405103100e86026503402c11180c680f1401941e082c0118442e540c00c1c1d40c40041404071100d51003041e20b40003481030002103509503001c1e048458410302110366000041340305414000303000090140b846103120701100d622403000f07065516000d0b40c074406041a2040e4651062800001544146900070818080c04040703200302c1e85420030945240c800180d868051030000400d5503112491045180074007501c500018510304400c0c04804000101300720000c101001030394035002e40d2400380c0d17522180b4035502c2041250502c001c0181407907042e00040d00480c40c3c03603e05400103152520306406260813003607894039845000c4100d60080e80c6104440d0b0540004400000e0000d1078868036000d4440000c00d4490310590100304a42040c024802d903681136120f5003070420141d0155008062140904044510308410003d00e0600001554805e000503445203040000301c0c2e1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 813328102 1250 813326852 813326929
    0xc1b0e090c150f0a1209110109060807090311030c12010203060a120b011a0c011b270521030c07030309050105040303080705030c070f0507060801120309090f0b 70
    0x5003100c026240c0d0000d02a50b02c1c00b0b0003288541c08110600240040c20207002d2401d581c803a2070042e10522003903041d480c00320540e0802411542c0800e018500203d2000d014180f03142c801c0116644005031586191a217485090b070700c016181c4c06008610b441d0600e80c0391501c001150758808000503940342820b1050107201c15040e40540600540a41c0c1000021320504039207045440d6040e2414ac0c2e4848040101e1051080d0f0072040420b40c0390541020250412030b0552081406545900c0c801c101100801c3e4050540e24a080b5200e41c100301091095191004e4500b90003100c0b0b40c1070450744c40b0000403040c60360b40100c10040e0304d0342c0300f0712003007040607404120140034200c03c0c40c00b03030304003441c554014004080c0504007209001c008000249032842c514282c0e94456004081080b800459041031030b11403882e4014171300020481000881c40c256405e501c00d000307950540d9002112450309090302c0040c03031061071458186031100c8050301550744e8511110380441c941c01c950304c51524415561401032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 813329352 1250 813328102 813328123
    0xa14130815011a120a0b030c090f09060c040b120702070902040807031110090306090305070f03030209010e011e03020d0923010c0e090114010207091508150c0304030c1b0e09 76
    0x50f001000300b00c421442ca00280d5811800c2008040340031800440044e0901c0d035501001a0480e113a9070400c0036a0a5002402d400380c0100c900703940075503e5101558240384128040c4032103080c030030021984203101980360107501880c11f00c162a030654a03003101c0c0d0141c0e80694002180743c0e0080c2d00920500c070780c03c12140807041c01224842d0400d84151000341041019100c080d007881e5a4600d50320a050144c3c0885241990103d40c0c111164950700d4081c0080d0484182e1500145207a120503005c1c3d4056940681c9a05030801c604203201074001c1c089001c1e500c68034000c01d03015101c424a50024040402111030304070059144040c2c85543e003801421100032000320f5040140c260301c4500a40c0703030594968103640500850010a44004ec010303480c11806a125513170251418503181c0400e10240001d2054503c80001d842e5600411540f6540c150303800c1e42c0300c01240d801040402d0000b8042c01003502c0c8940708000440100d090164004500d42c011350002003140e80d1a001c10248203002d01111150 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 813330602 1250 813329352 813329399
    0xf130e0601080c19120f060b1309060b0a05090a0b04060302060a08070215041a0c07350c250f1214031204060203071205040f12050a1413081501 63
    0x1400d00d080f80c401513544071910050103402507180d06c07900340001c54025010b0240054132842124503900ca002004145182c81a143c3c0d502d0010081102e281551524080341d00007007000307811362901c4282d00001c000348034055520556400780000107031280c20161000000341d0703c40340319900c4e080c90f01034100003254440c2c112880100d8100300c001110038041d20300c000340d00d0301e0000c40c03940c8882070752000b8468600d000d01340500c080405031040f10394100d103101c010002003600d920346103171420b03c060038003a007100200c0f1074010541c48444144d03a0102c0c1c000c00d2001001d010503556548190341c036030701c50b10b0300200c20001c540c40c008400d105085401020a04080307006626100c4d1603501043c410030007400c028519600000032809181c45001d600290b40c801000420650400389001c0651109407281115800c204000300c0103028050400d80e402c2040c280c880c080c0f04171686480014951144404c02118003c101c000728031984100080f00386190300c40c000c02e030254144204085540e0b040007038481d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 813331852 1250 813330602 813330649
    0x301060f0c05030d0902060405060304320709111c05161403161814030d0503040218131e061a060d0e031e0703120603020f130e0601080c 60
    0x110000300300c0d004460400e000217000c0c0100e1001940a2045500180d8040300100900c001d101d800c4031240e00e0741e80800310b40d0155154150501c2d1101100d03246040701904010780c1004a01c006400a0100e0f24040c85090b24101f051040e074540d0701d0501004029850340c4404020320101c2c880c45c171910761140c5080ca8211700b6110724900905201c02051403d040002120080031075014503400c81807201d2021106e040f03a0f4407504040c8105041c040860322910400020320601c0e400b44040740e008940207001080003034949a06d1300250f4a0140c05007408000c4440060003045000c1500215004a000b495552072000e081c00c0050f039012268203103101c2880074150485a60340c0b0111000b41c0c40038000440c038408001a064207500400302c2c00c050307607030501c40103003403040c038140c001c101c40c6200f91103000c42411142d004004450b039a010080d009003250091403010b1601c071920504500140001144418810703c0c01420300b8401c1c5d01240050340900c01280080c07904000001550170b514194a1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 813333102 1250 813331852 813331877
    0x5060114071203060b0f070c05180112150623041e0905030c01020d06031a011203031e0e060702280314160b04020405071716090305120301060f 63
    0x240c00e84500c800050a00051100140308140203820034070080450348a82c80d00c0710403100c510646503000000071911003076882400b01d41450a8810020000900200400c0581c00e106800410741d509031000e031810050216007e604151038044e90380a40081c0201c00ca00c5006049050510400a655244920f080148002c45030300c0d558103200c0300b00248080403402c1c0e402400e1450031440394100c0c009680d400040c0b06083d504007904803104592045450051200c00d0b070205a0200400f802508411408401d500020a21a0304032458140600c12984181490004083c04a0703040d1101010320b40c10400412801a80612a8000f1f9407030f1840da81804402d0086030750500219408000e083c0800400b083c280c0b000c1e41d00c2601c152a03912680407090810a042130b5101c01c0084408078455406c010000c0c00044c8a0207003004a511104d0b031502a03500c500184c0b02c1c1200510400c001080840c640000118108004c0d005030a80c007060f110740d503035040c0000104148141d0031040d00b4010320081c0ea0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 813334352 1250 813333102 813333137
    0x130b25390806061f0c1506050a0602030f03070507060608060a0f150f170106080d1e0903080714010b040f021b0705090f15120c03251806050414040501050601 69
    0xc007070b4a40f83c000d001008964080940300b14000440c050302013504041c100c1d10240951f8400e00907144121844614180d0740d00003280d41e4840c6100c0000d602030b01740049040c0c01e0040015003d014424400844c0094031040b09070700e00380c0101da00050603038841d8120102d1103114461880107103054800c40b161103080c030400700080c20f1184182c0880f60140d00301c5080031802036100a01034800700041e14800406c918004115030060b03102e41c021b40f28034034800b02c0c08a01405070101102d51019406007801d0880d16030340c0064580c44802c81541d5260b8089a849a9851160f1916841607190043e11801d041d0004072528400e41007600300d544c40540c050010b0399400c1c0c1c41a03403007947c0c0d0000c030f5415968204c5000a0203a11601701e40c11141072040d035030070080042002a6880b00540c22180701691120041d6000c19078007101004a40d895001401099040800c0180c50180800c1c04140c09665001050840340502c0030340070745440007024001005000e0141903004402440d19000c1c03242c905410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 813335602 1250 813334352 813334369
    0xf090b1501140f1605060103031d01030606081f080106080724142104030905010206071e0c0609080f09130606080a1a15130b2539080606 60
    0x200199040118034074180340c181000004844d9407043c151081940d40380f0b8003410701400c5045a5900076130404411001c0e51180c8034200c00ca624640d030b0840c03292a002108a55402100190500401e0749003000c28980c2007400741c0c80003000040e0040007600d250031000c0501c01d0b0048090080310100b8103000000355807000e209001040f40224480d0395010400c000040100c0c005460309541e10b000c4100320615401c02c400f04119882030b02518110b40e03a4490840d1814126039103110300711000600c0e41d0039540b07e910012030541c410340e130014210740e0380d0312203400c2c42e088a500c002c0a0580000d01d05000e040036489501011035144c410b000d130714200750340940000c00044c16070542c19981d08201d04100010a1507269404020b08418004041600d4500c59540700c41d029003404202c8850010342451400c046581d03c6120454024aa52003070160020070390031440305480905040d110285182e9000c0c10b010b03230380c0f040300c000841e5803203150810001c1c82d09a50f000042e1500031404010700c90311000c01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 813336852 1250 813335602 813335617
    0xc0e070219080415050d29031c0e0301061e14010f080106030b1807030e061308040b07030212040b070507050103090b130c170c1504050102120d0f090b150114 69
    0x1c040590302034004d011552030084a0315400003a042c00310300070322807200c255904003180042c907411212200c03d03001e042d501c01544d1882c03003c4900d03090b581c00702103118119007106144000c002007040e59a41e070741d800c00d5144421042400d00552a0308001e80400f030b41c1100c086000a09183d50014181400a40403401c144075a1050540b158004c0d51160b51b11a0340704801384c007041c80550703241840b042c000c004203e00e800b4a01d07944200400314025a59450540d100c19504c01c0c00e0b0342c030301414580c1010942e00040f80031000e5106140752201000800805007000e07004e007040180c2c6400e03071401c00a1500c1e1440c1d120a050602c0c0c0300e000c0001c104c05116040c1e108545141040b2040428a001032444d1001d511441c0380c18040681c4c010390290200701030304410001c584504a00701682e01d012018402e0f8400d030360142e0301c0496447d5032289441c0203002550014500080d4803051002c1903400d80c0d580080489852004100f003000040f000030140881100070718080031881180340307410340b043c46140d5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 813338102 1250 813336852 813336869
    0xa08010e1903120606020303180c1e040603021210050a060509130f0b010920090d0209090a02030a0b0108100b0f04090f080708091011150403020a0c0e0702190804 71
    0x29140c07800d060044103082622480031904204259450030001d40301e4100750303600c440311f050380440303242c2502d40040c0c0008110001821070700c0c0c0c403c00f80160103880603180801170704079450b0000000543d40ea00840e0464041c0b250240c4078006918007000112000203003c0030b43d0601d0100240025102c00d905103911810140ba0880481c12606040c40c40e001c1da40c4006016900460001c0754980b01038012030220803120b803840b007031594280580c0ca0140a0f0100d4950007240782902d603409454510300c0c1607044050501900e45100b00c0340c011a09200d0760341c109075040d010b01c800401c00740c4000c00c03d081442d0502c0d2410001110000000385012030401d040c1846681c5130802d00b0188a0000507405c009903000a0613a583c13419490b112241f0340001c0f0140b4410540050000c02d614080e2041803060003036a40a13020002028686006e0150058030a5085100d042190000250090400e00280200700b100c20704516004030024503000070030034268034403045a29094001843d4409072800e403030104 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 813339352 1250 813338102 813338143
    0x6110912070609060e040213060908070918031809022106040b01020a0b150901030c051503010b07080d110c070911041211151c050105010309080316030b041a0a08010e 73
    0x140010f001380c0904100302c0082c0230400000103a080d040b0550604469212081d90a01c60385d5507140750448074100d003081c0c01c01903000940300001e4415950140e11540c8401c4150038aa01c54000108a0308040f0700702040c65000d00318110103998031140c0541c4144200c0d0148403200350080000e4807084d5071701c40244400001c401198410040620100c608e00d4064000c601d00d40c1d5034200220310303240501c10540a01403c003102003d403006d01048a0603141d6100c801441c1091550340c40172603034050030f01c0c544030a550324000c002440060303000f00000303081000107200290410f14801c04485010030400d040e01410802004881c2101d803145512a4000c48004d07000440e58012034640b940c3c1031601079000300b002801d01c100d00c1c080c2a025810100041003001030b030703813250015422502c01f680c024290300d10900c00103d42d0402400c2c00c90304104980340115256250b600400e056a01d089400c201d08213002d00e0038442c904069a20a004100d804e0080c0040429500841e495420044180c03d402000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 813340602 1250 813339352 813339377
    0x1b020102072c07020f030724060303030506031e1209040e03070309060306141c0f1b0905090109030503040f0f021905011806020c040c0c0611091207060906 68
    0xa212200c01050707030b802030400702d6800b80c403416540c1140342001c0408441e5000400c1050340300040350082c00c28100015498613505480b25280c0d40c1d0a100701303030b03500220207110301c04900d01030080d070004610949000c40c403400d00f20101420204c410f035049680300e40c000d440c0e80742840000f910205154103103007102d41c1e403a80c0d02c4c04140a441618810200f901c00010040100365101842c5001c071183c0c1d43e020401507440c0c0c098080000602c22400303900640d00340c20401c50042041c1020500d61044c4c46014100c0b00c20344c8e52564115488025040191090400304107901081c09000c0d030241c101e50080113400050740c0c01401c03a000241003e01305541c100d1031003041010b1210b0300210550010400c0c1903000350f01612603140c4400740601070004030b20300d481c45400c410564404081c0c4003075401500c40280786e601800014208154440b0410500c00b1500740442c039144984014001ca44500039907651240d0280451030590201d40c807225808400c0c10003826500580001c05d596403441c0c074040c2ca200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 813341852 1250 813340602 813340607
    0x140402240f03090c011808061b09030f0706020d0905060f030711030d020d141b1806120916030503040e0402010c120c11060f09062a03120a0c1b0201 65
    0x2a107842141201d00000501000080c00510543c601c0001d0341d9141e4202900300810b6144c0342d85105600e80c0741d00c01400310325000c4440c0c2c6021000d000b0001128101030140c0300080c81d20001100400654100c03d07018080c1d140d051100d18ac4c1c086c11414001d00484c0f414021516512800f00c228401340c2d4044041403500d48150120500c6103002070840c0c0c0c492010030b00010083d4000d000c0d00f03002034500851048040146042184030b5007024950740e101041c5041c0080180d4000c16056600005960103945e648e81d45801805100c0201c0c0070030708140c640084041d10b804442800504141045401000003d030008200d40c1986c14100d0300404a80f034510044c0c03903507184002c0c028018100c4190251000394000c121040d194041c1d07030720300020b0b1606400e00c0380c144500880c015031001d0401036520a42400c80040440c4914001016010030b85040a0040c460015007410142d070400104200941407451900340c022588070420400003e039190040c00d100c0c841c902c0c9401c80c035112282c040540e130 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 813343102 1250 813341852 813341857
    0x12180307170610061b1b0801061809172a0a0c0603051e090c190906090606080a0b0d0210020123220507080102120a14040224 55
    0x501504860900740c55805040c04a07040e003206000c188200d10000d206112468845001c890441e2240c2200b42051741c4c950300303120030b104025101280748810141401c01c0c02160303032005041c090000900b00b4140084001410b1103186d01c4488141804e80500102e607640d00c504828400341c03100c60b0765a41c0c0c0c1d44030404019680c44031075031828942c011171f200c0014003c88c0f00440c46204160401b00d5684440c029000c5035010754548603801c01d03098031402d015102c200c195801183c6141292810154000011504030341d8110000380240c900e00c08204201403401240c0190008041c1400700d28244280142044801400c4808064940c08008210344856080c9604281c000c0c1504070a0851214080c5c040e2840c0c201c149600035980080c89000c100002000d030080280c440120740c0a842c83e40c0c0207440c0c0d80205c60540b4680a40040000c2c604002d100030103106070038040c06801c1e407070725908510840309441d6040c04118444c90070000184e45d2071103004101041102022403400c0c00202016550 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 813344352 1250 813343102 813343147
    0x230c040603241103160905090a0605120309060a03020a05070c0603050709060c020307060c021c050703020f032b050702040504060f05090a08090f010302070f0f15020c12 74
    0x14a40500030040c0244080e482e0084840c002441c40c2455a000c160780403550b4070b00900340c4403202440820100c0c1c41d084082c1c0302c564001e141421896403903100007000c5180507195044410390300c1004008905081c94801c04412805010710304108030700c03012402c644114010401010750004a03070341c01502690544103c0c94000c1c400c0158140c8640b00900101000c1ea070200220b10410300005416106580b0940c130942d018025058203031401c0404e840d640415202260b0042100400c0404007d0707903440004041d0182004100080c60740c0148540c02004a203141d0094000c501d81051012003860081000e0321542003213161107488a4040350280549030f0025070050a2000340002d01050b0b800840001d000d11a040000b80c0f03e10600c243d8400c0c4054000b0441c4c1820b20007a14507103090f0104c21950b281c181805441d18181c1d5031608440d090303400044981d484103503072010600c06c10000b803071b0440c68409800c6203011740f240d200c1c0d41d591281a02400001d030300082c040c1c100b03d01100100c0d2a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 813345602 1250 813344352 813344359
    0x322080a0f0201060f0f09050a0209120c010e06090f09180109082802210403080c15070201200d0204080d020f0d020109030e010309020d150b03010513230c 68
    0x1180d0904200400c0c0d801d0700700d0464010b600b460404510100107041c02c004951641d1112205203161803c0c5078050407008254002a030f509000407243d0342c4442d409040a0408140600460700100c1e0000d4030030420922458000c590a0181e034000e07480b0801d141c540504200c514185035500c6000644110b94002520b415650030800c65000f00030002c8082d05040c0d201348961000c919031800c44848140780c00395a580140e00900d2110410184644000c0c000d18101d0b03207d41c40c180d01c0ea16811002c0d0302940850034644d100341240c1e07500c0040102c060360810014402804000c0d0541568a480c10440e918846c0520b0001090000f20030ba5074125001040301000f03544081170552000ba44416401221a07168092020f451040394410301c070301c041156050300e41d8440d001140e40118020300868800b01d800108031800d82c0c0114140d002003a600c00003019010450360000d0090609490010300403403803400c0b144480c603000034104442050104005280703000f0440650300168500529070070620781 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 813346852 1250 813345602 813345607
    0x819200d0503220b0c070b0c031e0c0c01030605090604330f12120503090a1406012903180a0b010612050f09070501030b13230705030c032208 62
    0x10032000040303c44100300b4a1041ea00c031202c1c0c0c0c0300b0340e02040d0f110b0413003e010a904120020301c01e81c0d40c500050221400c01c1d8040300e0a2003c1000380b4104e903a004000c2d00c202e04400b2a00c54888003040202c82e071400e0081c6010300c00c8c0791401001c03c41844001d00780c0d600c00e6880b51030407044180c941100411480d480c00e0648000d480ca04000c9000c0c51081c000c44900007401c803804102c0e8108584140040ea0340803c0c0c03120711512043c1c01700d07010f80003d0041c0646004002c91140403407500e02121015603d4403019000a514145002c140c1c803003845241400c00145900009450401d1025250310518841000810a80c0003100d1400e08155120003000d101403000003040c210381c055125542016208404c12403034071080c0d10369940450841b81000160301c0301c041446154847d40084c0b5210002400c0c24030010810613104007034440d00030219400644540d106144100091000b0750000000c0c2407492840c102840503129912000b0590070f07151125114104060f010700c184a414140c100e0001074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 813348102 1250 813346852 813346867
    0x92001021f0b04061d060d08090d110918071202010c0212010c0e0d1101210c0c060b01081311060d020d020c0d0801050f121005010b040819200d0503 65
    0x4000c02c001d0900b180180e01d8600f01080c208031058540003003204600c207120a50b900d14041000300540c40c001107400490501c03080721a500c1d000c0419100c0c0b44030b60111b0342140c107400240156aa0018001103210f00d0083d8980d0200001054410564600501c41038842089000580d0307102c441110084d0420081003075801044010b51010141d1683c035135400303405021145c200440d000042c0000f81005501c4100600319600071441104e84000e810042400300004034402c1080fa000449842d0101c0e10480c40c2e9820000244039904804400342480c05041c10110030500d840110180018003c0754050345083c0d55550f620151080c1c0302c2a40c0e01950340c2d40041c20000c0103904802c159414070f1280440343c1c400c441c09110b0440c1039401c05407040c0281c1e800c00007004400442d80704050900d0050423284260703500c00d40070302ca010b082c0c001c40003981d8602e0242000d1902c042c2c00c000c0b8006d044400d00c4600000d1501c2103517200c0c081111125006e03c0c041d0000520075a03503403040180315100011f4902c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 813349352 1250 813348102 813348163
    0x62205090a240c050310050607030c02040c020c03060606030903041203050717070212060405031909050d03020309090901380a0e150306010803030a091703072109200102 74
    0x100350744500c1400d2042881c1c24109031080d0100703407600d01200300031b070340d06215509180000c2d10b0311a0180c90f04000b40c20712500410b0480742440c00c03120041c2c00140d58568a03040401529803c9401500d40900e103241408250b85c4034061402214645180c03038501e2002c1c54850026148129000703000c04443d1010350301d1350240360340300c01d00480c0901c04070700d901001c41d03002040d407034412604040039601d0203c5c0034500e1904020210100d8084c404490b0000c515501c0e01c003c0344082d1480303a0015551a010442003020000b4014030b40b07002c0360305000b401a646680034800098400d4800c05000384403280390050300600f094044501e400c1500d0440000300e03404090005070144196011010218000d4818152150824000c4d01e20952040021940fa48032607030000f203070749000c0e40700d0200b0102000c0d1415900d034400d03103007240007e45035074590300340a00b40c1402440f24001c82a0812158655a4802140303200c98452800d40000341e40144805034008d0186541d541d01a481031003d07042861901c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 813350602 1250 813349352 813349403
    0x18091614040b030a0c030b0a110f03010608060a1d280902100903050a02060906070b01030605040c050109141908161e05090408160f0803040506062205090a 68
    0x109442142010a0304202d42008a02c1c40d0302c40350000280c100013070030350700c5071850803201804c98081c0d41e0307480b0003c40c1c4020b0450058034030040c0a051407030356945040070080c60408040c1241d8441c00b40400708021003a1030301100c0400d8443c0304408405981d803143c100500544c0900f0310840f034a141c0c3d940800000c4564071500c1900c0c07003241c484d04601d4102d078045032803503e140001041681b00440300c07805483c0000140120000042405107000b102d5920610042c4081e84202d03007490b03c3d41c044c0010440e0f8014400d020302420301e09149100d26001d2a02520100356007941c1c007a03000c03c45041805400c0710401000741a214003103842c140d00071040380d000c20a1611800b00e26040d00d00302000c901700e813402a081280e8008100000a84903a2100b080301c0e07014184000c0d21b162403036101400640c0b044e83c040c030420f00421031252280792a042403400d0000052000b8800e282c804192a0084601020800b84131000c0600140a69507a003107503103004405031010b040072264241c00d00c1e10107070701c098 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 813351852 1250 813350602 813350639
    0x30e030a27120c06020102191b020607261e07031808100f0605090c0d140a0506091503060c0c0f03131806030201020d210510050103110702180916 64
    0x181c00c428244d580508a08034002c00000c0159412004580203905100e2052012004141f031400d1040c1e6800b58001032640c0d00507801142c0008859044038190721a0000a0700030303100005100303190a0b800072b40c1c49a1001c5203848101314030700101703100041c140f0030642080c0004208100c004180d8a4a10043d0348031604034111041c1030038004038406c16040c5009090445070003030207441b01526a0050481181c0008003501e0200f655a518007a0001c83c5403120b900480c080c42d0000744508002007885036820340280f128403c1078445180e4a882e0710002815980300150024454071a000180c101d030805804102c0c921540c40042580f003001e0103002031a100711206138032101a0b01d8001d14000040d41c2c807d100207400b50708500b44085545000303010001010310b400c2c00c814420703a990840c01084800a60340302910006440003807019582501c5540704d00c0340c00300c1003e03080500c0c84d400180310110140f465040010381101040703029200308004084221900210303002e00d81c840d209403481651110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 813353102 1250 813351852 813351863
    0x30306100e0d0320010519060b03042004060f03080d0c0801080a170d0f1a030a02090c0a0e1224070519020c04110415030e030a2712 58
    0x210500c0c1050150101520004019000c50b400d06096107060711400318003001c0c070205100044074100406000e219140c032494032104e9401400b101d00304007404480301904440c252040400500c00400d80524844030191403c1240c000e0f10200d0001244c050402580402c030800360121000c0200503240340a000400b01400041007076560111003150012400e00c100f03039064000642e2003010903002110000d03441003005d070b00c0f441e01c05940300020485240f440140c60b0540e4401c0b610000380c9620509010700030b0b045004102c1d980b81a00003400111001d0700400050a002440001719401464000c1c00003800412010201020342d021a86400c034441101d18080c19107940a0390480d01c1c079002038011f2940756181400c161101c400c4e00e5070f9520140c0480150f1145000e400301c40da44901071001d12050f54240d8540705c51406a1410700c0202c14040783c0141418000f0704510820000150b03108102c003443e003d14512081c241c088145c020090345242000011a0042070710305c03035004010011392050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 813354352 1250 813353102 813353119
    0x100510050405270a09020301091a04030210020301062106050301090f110d080a030e0a21110105010308120a0f0609060e06010c12031d010615021608030403022e02030306 74
    0x21080c0f00000d9050342452050f04403110120f401c03035901d50300c10803d03030744050b0000524180e81d03240c0e22114241e00c600e00c0f003884050400c0100f0140c0c107202c0c001e01904115010350440d41020006080061181c0e0f2503200c0700c9100204082480440c0c10403c01401d0240c000c003c440d485040c05440520310440660f402d5189004c61a840c5c10216a80f03a420707908078100c2400c2c802d610604030702500b203068200032144200303040c03400800c0c80444070344440c0440030010452001003400251140010000038400783c0d14040040001c12008022101c0342804002e024145944003440d4400401500c031095841e030345480c1c030128215007254002d20580c0c04e516001c4221342c0e150300044840e2100d008004180c660b00d005c0d58114140030790040000500b41a59441211912030203260845000307502c449039a9542181001031b40350107101528101a455600381c1e200760034612055035910491100038080c0c00303500d10f0500d0302481444100c851042c0c1c40d184026501c64000e000755070313420030340d00f0501c102c1c0e80 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 813355602 1250 813354352 813354379
    0xf02070c06050a05090d06150803030a0e060c0a08040312051513151403070314013303030f0e030d03050103123908071b050126100510050405 62
    0x14206603040340c0f41960b10246020039801c2070111981c55043c0456070161100040042550503aa504003d05050350003144c4a142000b000b40559240c0c11400c0c000390032040a004d401401d0104640d591005410040d075581c03035918044503030001420014102924100c10302108659025019402d10342c101c660b034442c40720f01000d40c8121400e403100ca4140c01c00d07000003000318183c0c1c0b0901c2812020700405440ca0542d685d00e91503100849a440c00c42c15035940c080b0030019115420f81901d907a0161090a01060026440c1200d1a038003800081c00740008450301100507440f64182042009014007541c429481d0400c0180c06403000303000031034030082007000c0000d000d03115680840004078641c41c40c0954032003980300c000340ca018401d00300061224543c50f540105071501d000785000c921510b030350014640130551318200d103c070580029040001100c14141b0150004088025081d2000c1034240c550f1590001114407066035401307190411104007244500c1c98104c0090000c0722025100c122490700b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 813356852 1250 813355602 813355607
    0x60209030a122606010c1106090d031e09230f0d0308160305060a0b0c070504091a0a05240a0e01060e010e030a031b0318140414060306060111030403060f02070c06 71
    0x3d04841260000f444401c0303842c046038680162007005407001c1c180e64030740740c07502011581d4805110401e602240e031013001c1501000d88400c14401032261031400a01e03580c1084800d0745082640d02440601201c2d440340d0b41e0242c0d642042081000300c008028401c082464a8050950307002103801001d6140380b07100c1110141d009019075449828000d140c0c10340c580c20b18841603016040f4980b6001644607014002c00d00351941d100b42c00406009581c0c03003a42003010b00509040c40307030041500013400c0c24034003440006031000010f44a07808142524929001a00c40400e10740d96550b44155800c42c81d110001401682100d4440440c2c0001ea8074002d000c0c2024060640e201c12054005000804400c01403404882406881c00703e070748a4540012010300c2c1180740e0030b070303800d281d0880240da40720030120b000b41c1d2815104a0900304541ea000c10b60500d048000039031103100040c011810300002c0e101002c0780707130002e02c202d5000e0740d4064020820f00307440c0c4050790001d420400d0110744520781c3d560b0115a1b40d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 813358102 1250 813356852 813356927
    0x1906090b0907110c22020f1308030a1d010e0907091a03060d081b0f01021809090c01030b0f041506170121060f09060b0405060409080304060209030a12 66
    0x1803568010601c44800130144500d141e03441c00780c00f801d190000640490b481d0305000800d407000702c5584180d281e4400047c00540e4481d40d81c08180d6661003000784819443c3c02001408542c0c01c5240b02d100f0508a03100103a03055813145020551240c094800c1102c00c0c0c1d0495600815161144d02403d04010804a0b04e10b0500c02580e089502903480da4280001075a083d0041140b81400d0100f19904c3c816403010302e28104184018140741d03500810141c4045140c540f0180046100301c40d025202e00300f10f1801d0781c90b041c04401c001e04064840001e0b42503900d07040c5011569403c06072040204842c102c0781082d0030950342c0030b06c20000c4c000d0f07030421344100c642071800c50585101214414241c8105807560b1043c5845110443d0342c01d0700c070305481c0c0f00361095125140499000f0fa10100340344000d8000c000c202c40c002440c0502c59803034031002c0d40100f0b07615415030740d0140d8404001641c1d601c00398002440c0070b000c3c0341c00030003000704d2110980c01541d1181e0b41c00e0b0005ea200c00c1d0045407100312001c040300c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 813359352 1250 813358102 813358127
    0x5190501081b270f070e0a0506090f0a0f2714130201120c020607080a2d060f03080406021204150818070602010c020c0d08030705031906090b0907 64
    0x40110b00c8401a90b4038000124078040c902c484290741e00d25001d4151032000c0348003101c509842e40b00c02000c01943c0f540260002066030b80880c2d4040e0a6400d090001d00c00d4015060340a00540401c42222290307107480965001400c2800f01e01c000381d07070fa50b403a10290104a0481000f00d1800641d407070300d400d54107000d1005038005044800166039251040ca1440b104040c000ba4104504928561705e840d03036510a03207440c00c11980c00b502c400c1c6400000075004132005002c0c5030320340b450f0400103c07800d0340e010484c2107016051116a01031114941d42d6074060700e02078008020458004000104025014005208546050302950070303401c00388800702043d001e50f01c21082c0328888600c1d50300d059449038060030b03800250b007400d886142030645a101c0c9010380503081040540c1d542c02c5c000c213410360100511480d404e011120010f000b2403a90f290301d210f00000d0190344c180000031012500140141844240301d6000040400c10700e9078031900d00015145404105020300500404116124032032010001d10303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 813360602 1250 813359352 813359383
    0x6310b280f0e010b0d1103070302070201021510060e0307090e01090b0c0405030606040e010e0a05060603191e0f0807080304060f020901080115110f10110c0c1905040519050108 77
    0x76071030b042100309140e001c3c003c0203c0306540e902c11b005641c903a5a000d03500070b000701d907001a102d0704a44006403401c200206a40048400042004180c003600d202000c280c81003898007049900c4c07480c012924180060700880d034501e040100c07900700540154008014503000b0045030b9540d84500719074003080c1c80b440c0078440d0581c00c1032002603000c1c10640c11940080010000004115200074185410700c0c544103800c44054101c1c409001092170304200800070b080520310084442d07502552400d8403007241c3c5005403940b0300340b200b20205100c16010840b25294104000507030b90140ca2030310614917801101e044580d00e1415200060840c21442661014201a1120000d07a400c5c0a0300084403031200a4031005c201141000c280c1e0150180b003100040c81d0000010050780103280c81c0101500c40009040c1b1551341c00303020b646481a0006001c0362412002e41d00e40c10202e81a034029020f18500c1e40000d0381184c240018030440022003058400401e080780301c00c001c50703601e80d1101c50701c40c0c05003010002e1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 813361852 1250 813360602 813360629
    0x3020a060507050f070605093a0215010b0d06140f040f020903101a040c0c032d05030702010b0a060c02062a1506310b280f 54
    0x10302079884540c101e00e040c2000da08020301c0d000c95044542c00072000b141c80035118024450585800c04c90701c0154075000c0303044c2654658070925000d6001e940e071341380d03440c1c02070010038030344168020b000d0b098a09601c0000c42100d90385580110641e070340810300b540b03140c9103850b000247c0354401d20006103130080010107603280b01001c00c081101078200c000140103141d908101d18001c0341d070200b028400c81845200041a1401c1d000b50b17151005070b1501c0c8050281c0d0a1001c6d4000043d4480d0030440d01c10f525050030b961004030310050040c4082007004154841d640051400b48654000000e5403003084d06134006d001004c456001d00000b801c0905c035800100307600034411001071034000050110300303d0201d4100b1a1580f00c0c075103902c4141c1151420b04441c0c020419001d01203c40512959018a0580306003240010000402c030398955200d5403104100103501051a02070b00315000602c0c070070001042e03003004200d0070307141817400c4c0625070524000c45070310b020002e01503400007284070442c0d18032001e020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 813363102 1250 813361852 813361873
    0x9120b07050c1e0a0203011103010b1b160f180e0c12010b06031f0f0806071409030f070501121e020942161509050601090e0601120302 59
    0x1101d80c0c2080c414001c2e18020300312605103100d12082908600080c0f00b0003005510054018142141c03a9500401c40042c82080107100940110f4219241c030b040061041710302420b5034007000d0170100100c2c189441039a10080004101140c03007410801d4412186207100651074148078481110188248072a880d000341110160514103125070108082c0c0281c0042129207001f400908641c2c01100c0c1c016007003e103001e511007031950440300c810103800c145203c6441203040580c0c09568000003801c600402c031101250303060021402d400ea4900003409021034001e00072804d000c5441d00d6050144600080030a120040e951051340656202c1c40c41051680303490044440055001c0d5000302e204a401c68101c08404d051244900411030310806030300b9482e401040036146000348181c0315411404032101c10710000903000c0340709140409c0c07a0703401220340700e0044030000e0310400b07400d0a107000347c118000c036000095501c41035085042e400c0e10241c1900c405a89810111000580030080640140e120345290b5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 813364352 1250 813363102 813363107
    0x702010c0b0c040302090414120f19260405061509011202180106030e07060906021e07050406090518120f07110a03030c02010e060913110702030d0f09120b07 69
    0x10782c015200b00e0807180707415240e0b0007103060300c41c0035a400c6602e00b0841c42c102c6901581840000031180c40c142e03a8629000c07070304070411000d018440349000c0400010200c00d51705402864241c4440085080991022526400d50b002620303040718285d40c1d6010b0140000e011a203000316018082074001e05400d0b480e404c0a214080110306098202c6e0802d00090607503c042c41c0b0700c1f00e52402000240d8001c0340c100c800001b5282084917580c015018064080c3c4207000250300810321440310b40320680c171000200a480401d5241071420b90019070014601b040202c3ca060123a04844d10030881c00c81c100c078070000945a00c50756040d001e480c4605000c0103105011131030304004000e003610360050240049002075040012020080c9034400c030045816002a0821540c001209a1014204603803040c10040614085042544c224442d0034000c0c0e0b94145808005540c1c0c42a2482a600501250f903000d0499801030110b020381400706021441483e0700007070451a0070b550b0b420195118003040541d8031000000d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 813365602 1250 813364352 813364373
    0xf0302010515030a0b1b040f0312020d050301061805040510141f1110050c04050117060a05040c020f0102162d0b2a1b011505121603060504030e060702010c 68
    0x41c000c1a006c001003411815080394041c2c03000c0c000120760341c0c0d00d551841c40d20302d40c000212074002040d0b422041200c1da240340c000040e42d046404a00380940d0040060982c6501301186400c400da2262800c2d041c03041d8010704040704030588140b210543d00c044020405c01080040c95104d48440d00b01c8107a1034401a8490300580301aa03c20004403904500e84400b294183c41089400c0402c944d804102080b44e9a0701c040040c1c030704000c0c00d01001a40c1481c401007071008003103000d0b00c0d014540310340c0c1c0b002c281c42c400c0100300c42091030300b4001c40d2a1204c40c030600c03c50159482c800c0c0d80e030310411407158a40155421040450420480c0344100b02c1d00941d9400040c914014044600304100c0403e5464807000742904c3c8003281080200c3d9980c6200da0349580c2c40c1e4070404105940031b07a24040c0d40f580204c40e01080c2e402924811030b9020760b8154044001072601084031110040703d401810000100300b1076810940c0242d119888070f148641d241020f0084d0341c01004000381c000b030386000400b0013161000f0807 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 813366852 1250 813365602 813365611
    0x902060315060d0c020102091005090307050907050f03180c1221070501180303060f122a061d04052404021e07060b010219150b0a030f0302010515030a0b 67
    0x4010708102c480e8111101300c4080106030000741c0d40000b4200c2261420805002d00203000d0300f0594105000c400110356225018083d0031301610f41030003c140c1d0030f4040d03010341e050070040d00031207990b0b403922002840c401401800008103603c90308441688a03e0011103c08074401600001c3c01c010364608030b00950f6000d00044900b5020040080c0400310b070081c01584005028541084808034087c0fa0041c201c0340c1580c41007401e5007480c0d000b442240ca840108a41c155003040c1030700d14090240100808040034403a000e003420b103a50f02c00090981c2c01c1080c64068960f02070451121404071401c1c001a0380088940c0c040803080707011500f115480d81c40c4c2c4641251006000141080d0842c140c103003980b1070b0400b40100d08800410010b007000517500904403911000c1c401350a00e00c201028180c68000003c83c01029032903410a811030000c1d441e480b115000c40010442e8140c0740e52030034212a2801801001d0b0015424800007880c2880d0852498074890341c090001c090480300d5032503000c0101c0d000361 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 813368102 1250 813366852 813366859
    0x627090a060b0a1d0418030e09150103020702060421060e031804230112020901080f0606060307030902150d1a1509040b130e10090b0112050f0a150c02010902060315 72
    0x4d08004651078034450034009501400a0f921441b12504014103400503454403244034204000800241c0d09450102518850003800c026807140e8951000841ca402103410102154008050300b6585103403e40240803114020fa038100100303980c0400054407407051828050004548201d0320350203080a07070002e003d1420308a8031164001c51500d4000200d00f00703901078500c80b0740c2001594191701d00301254900621242008104907100c1d0400030762209801402203100c0c860100c0040d219501135044154403503401024401880090f21941d520f41d0042a400c813001464440c4456030644801325403803c0510041183d081210b480d0340d00070140d0700c20f0000540083d00c801c6030400da0744440b10609041c01c00028003080300da002e001145e1078540783c101308241170741c100025440800c3c40846614151640c9095012804515040851030480c14100015152103400c0f1305509001c8100200d04c449400d04c88140040788900034102e081c0e800700b14020358040030800105070403e00d80c0500744172156000d03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 813369352 1250 813368102 813368147
    0x3120e12060108030a0e01020c1c05070308120406140403020606211902090606070c150504170105090606030703021302030a1b03050109060f030b0708060627090a060b0a 74
    0x940c0e010703040a000f03034001181a8408100b101840d50040c2d00120343ea403082c070042c1041030b2030800041040d140042c41c030799028200c0240c201403100c2440718001458020803100e555650b1103d106680b08001c9030140c0e85545001c20000403100c1c030341c20b114001c5816900070030702e6440f18810001d15000000c641c15002d075103410088080300060207450b0320740c2090b404507400031000303005006860000910b02c3e8480d460030000388000a1801803404256010380c8040c6000700391b142403c0c1c54500c074503000390013000d00e486444800664150803a6200ba4001416102182c543d00c0c10306560710307054007009601ca040384449030900c840c26406142e0080c200c16010412030301074003018000141411f181c0c030000c3d85460050041c1c041d2402031500402c070300300b10041c04502e036440302d04110802510704c03001c001d42000461030590f50307682554440001d2446000108a12400c02c0655020f2440d8850040c0310010000741c07400b8203031041d070f001c8071811000140f03060300031032085500c882c41c12025440340148 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 813370602 1250 813369352 813369379
    0xb0f0907051509040e060c161a0f0a0605031c12150807030308070801030f02120c060c0c0406122112050a0608061308090f04060302040c02032203120e 66
    0x4001009080c40c0121010b580e540d0294018031080c3c403940012015a03500900c28020355101c124111140040c42c041e50074045950761030010500303450717494036540307110030702042c0000403200c3d44950303004600701d8400b0803446a640c8245501c520183c950411000b03920040c0300300c124003400e8201c43c641b0190000103820806040d010380c040246421071061503222140902c00c0540005105400090b07038181030302c8a61455441400400240d01f009001d000c0329010130480c2c160400516500110090503170f40c0760421090056030302c07800042c2c0303a8420f50502000252440b40c0010004a0301d4008150312018081c003a07401d4003000b000347c1c00c5c004110320031000b400049058412280a00b02c41c001c04584030b440c1500c000d151107405020040c6104c0810200340000c2c1015044400408041d119080303480001400580140540e40c0f010350028141240b01c181654007100424500301c000c8000380c0c10340100c2051260031850b03800002c20454000020401c258000c10501e0600d0900a20500c90200e4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 813371852 1250 813370602 813370609
    0x709051909060608040308250c030e21010b06090f040e0a0b04030201090201111603060b040e0a05010b03212a0109111003111801030207050d0e1c0b0f090705 69
    0xb56000c0000100c09200340b104040e4450140b6030800d4450512108816030007074000400c0747c280070304600b40100208440f04150243d80c0b014000c0900a05406d0b05484a081680300140c05400304d12095181c104503051602d4a0010b031088240040c2c02e0344e000c0c8004c4014040200500a8410041d2081079414000111240c141ca03114a00c01c0d400402d0389410384c8000350041c2c084180c001d090740c1025402c3d41d540e40785401034030212a00148041510041c003808a0020701100c052085a0f000380e41440b030502c40705422000074001d090303086483d40c80d84502d41d00c1108020b141d407810032140421a10804035501d81607001c484101042d6803400445c0158110b003100e105440484d0761045a004481180c986030204000c980c419040600800600c010005124883c030342450854034002000b1000c2a442581950070340d5038020100c60b01015440c4000d080072040e000308502c5900000c5c80c0d50903e007075062090700700130b40c070455010854450500b42260400003e2040d4001c0c8510704002410740c1c1c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 813373102 1250 813371852 813371861
    0x4020d02030f0a060f05010504020c0606010c021c080c0c010f02031603021f050a0c02030a0e0118090203010612061217220f08060c03070c0305070303020f0d020c150709051909 77
    0x511a44c0c000404852803807401054030b005a000e64440c80c0f040c04850107811000c2174056014800746440c40180d440e41c0300140003001d0b200b0314441a40e140d20400020001c00200500307200307484004035001d4001102c0115401c0000d9401d040058005000c58a11500c8580c1e075000244e10034010703940200c42e1071081c00905000348030ba83c81841d4403030090241001ea107124100f14640284095843c003050118040d060f018085207150412107251310b42c100c4a06100351081c003401450b13074290740d00d595844000f030001142c84c040c25130861a20a0000300c00c0500072444034801d40c0440d42e0007480e5842d8880c101c1c2c0d904008080040c400c0300c503107802e004481602145c1c0140c29190041c100041c2007070521440c0040081580140c3c0c0300400c18468402c0c0c110680354000795140c030f8200e507600c0e0741b4a8114040d001d001001ea1180031b000c90b0340d015001c000c0d00605511980c074400c54805104c14410b48804400580e00b5001040c0340340400d101c203080610303203041c990351856100310315070366111604002c40303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 813374352 1250 813373102 813373123
    0x10080d05090112060308090609040615030b010f050c07230d0c0929060a17010303023904020901030e0715030b030727060e0709030606091404020d02030f 67
    0x140000076000007a60b000144950744000540b000c201c65811076450b004c96100e0b034034840d0322642000c52442c4860361a60460400750039001002c2d50702070007500c0003501801200140501048c514200c03481e01900c100241c40348044c2c1000100045c6180585e941c20084070032011781c0c8650203144030f0040c140c42d40b1140d203041c0ca114043d00d14203946421000e1085820307003641d9407107140f5003007628240c0c03902c440b4440b590b841007104d001d40c1e5405c02410170b548400d05409074420b600f08100c000014035030041103100d03007079268003251003024601c54044400c0c0b00c80740c6820001c2c42d524100203401410103a01030702e42580181800241d80441c948214a041e01641c819076030181c00017a1910842d605005801c1c0800c801d80c0100601420860b20644400340c0d900c4000a11100b2040b464a925494005400812101080400509007028020700d044400d020548480e4240302000521120700d00c64030740c0c5d004c00250380d000c0c1a151a801c20904d01c2c0704c040c00380d0340b500c41d80740080b0100c1d5051007400805d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 813375602 1250 813374352 813374357
    0x1e0d030209151b0606030c060409050a021e030a0609090819050c0a05010e0c03011503060515060a030c020d0207050d0321022803092a03080d090203060a06030503090910080d 76
    0x181c8454072840f4513000300205070900039000b43c1e100d01001c0e02c9400644003542e0f4400e2000c10f42e9560007001e00e000b030062018000c030709440303000d072605284c446034020340c0600c006c0303002400520b883d003100f9825600c4400000305020400c0205071242411000603d031407601c5171800c10715201c002c10a2a1600b0655403054499965400c000c1031420400c01a000144009400901c010b08901101c0b44402a05210241c81c403034940303000500302121003003200c244540040003651141c030b151000800400c11001004054403e0b900e040e0100c41c00000c0940840340010500710034181d4541d411241c51400b170130001d8000d01c84a082d001c210300c40340050020000310345480005101c4d0060206101d2030b0001c084000c0c5481c205115003c14000d15150706d4120600d410b0091810202c0c01000803490340c3c3e0702c0a089071001040c0d00440f070501c1d1708102c030418001c1302104d0040d2108115002101c00301c0c400107000f548100002c42d924180420029800611208041229030340e615007182801e081c074900600 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 813376852 1250 813375602 813375637
    0x50106083403020a0e07020a2306100f1a0c0607110d05030915060d1a1506090901090c050c062502031e13080114091e0d03020915 57
    0x91450032607800c5088451030444041d01c0510715004610300403490b0003840c80144030240020070b070398004c1101009180d405032100261014a0402100f900000c0c0c90000d0035015440102da07204001002c1c0d0000d03100500c8020480c00d181c0b1080041112802c00d80e07190b076130070030711654466000078403040d40305038850744401011000c00142c0781d08001e00300c100e01007804801e10511011081c0000e00f0203200034000e80c0b82c4103d4072210700055020400d01d40013400201064060b5800454408030300303010f031596610085900d90504c0030803115000d44007500e500b004202004106400c0180c00c1800000341c241031017480d0ae1000002c6a081401c1101c50000c00e0320034145565210204461182e00d5660700c0c8007641c14046c0d41c44407261140e4108900045d0050045507092021098031491001031510358001c0048001102c883c101140048598550a014540007081400302104410001070f554034084c10780c0700c501c04010380c000e41001907151303003001e040001000b01401c3c0100406001320212560a03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 813378102 1250 813376852 813376903
    0x903171902220e070c031b0f0614070201020a020a0b15090f0403080c031e1801150f06090303090b0d0609021206031006051305042a03030e01080609011205010608 71
    0x348086490f0b4003c40451111904004000398002c41300030b00c5590510b40f51100000c0e0110701c070f4080841c908041e107000002e50801007005040d41c41460208400f800c942469034820f60306030300301d0152803148d50141c0c00007149400002c2800c0e1003950b025807480d1500c11105110b101003225408100d1b200000b140e0701c0030601c000c2c150803481c500d44c0000006200d5145141c12903070600c1d402c44000b00520010520408035580500700710351500700c481514020480220703007800d040c0404141e4440c519030140642404150f140c82a040314060300c0d003603114180c0c1c0390300c0c04039000700c01d52041481c0d5980340d80d0740c2800310f218143c0380018241d1204407100030406082c550205414001c0d858901d10b025850712908014035121825200104400c049000aa981d00c0d03060440d080d40e040090006900d100946140c81100744d41400e000380c900999503106200b26400040d1080301c81582d900b0b40c0701101c0c40040040118001001540e82c1c8100c001180007075440d0761071031a0100c00d21800c40c05910446004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 813379352 1250 813378102 813378157
    0x6190e04030810120b13080c0717070e0105060d02090d03030603140d0818030909070206010e0a0506030a0212011b11010e03040302130518032b0903171902 68
    0x2580100d00941c1850314281351854080840b00004c00c010144d01c0044001074091990b508503c2030320750001d00095a031000100d0035925564035005100310844e00c0b080a890000000030b000080c1c1d0050020700b44036908060420031160005032001001907020803002d06503403203002c4001d00b02031103a00d000c00c0150542ca000051003610f22503400d00c5a104800300302040e5400303840141c00c800350b075201c03c80340640484800c0c290701c217200c07450f600103242e2010702242d10b40c000b035902d040b901900800c10080e15542a04d00076600155007296156000108540c050f02d042d086c00e1201c081d404000042258402070140740d0b0a0308041d50b4008641844c4240c40881c20a0040540b01c2c844500076502d418110742c0061100318503850f603045050b80d04c4001400c4c0a031145440c4680944403c102d80e242c6096202250407800c0d074104c1c0f0010130702c800203015401c440e94000c05410682c580c88210181d8580e4505542c070324002032418510f50510307000039044542704d00c020140700b0120583e59900c00c8410781c04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 813380602 1250 813379352 813379367
    0x30714191101090803090f1003020d2f04060807180e0a0b01020f01060819050c090406091104050c0706480f0c080309030409020d020309010e0f031206190e0403 70
    0xc82140e0010840c0b00182d40da80c1f07811180240085428844071280b00c20300300e00074010500c4211610303103080100f1240031100172440b04520485c07002e000e020000c0502d1640e80340524815000410341c0d00c8080f59060380200303003182c0000926040b070110745a8900796644800c1c010764103007900b00d5031010120202d59052001c048502102070003840710a240100c0542d464030070400088440c11030340003140c100001403000581200c0002d18139031041c18141000402400240d004585806041e100307130342d8906050052620544080c140c1d6400d04041c0e888440144c160715843d003001c44004881110f540351144003030b60b04541daa40c508076510484800190315000200461414010403c071400310081d44050190b50b095440b80384d054498072006078052560003180c010f00f072040e0000c1082d600c15451580a14426181900203011400f03107224001e840e0151080e9602080d0010043c2d04803421140301c01c1a0403035005021b00e48410030080000012050070340240b01c546820105200a1540c05100b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 813381852 1250 813380602 813380609
    0x312010608091c21060b043003050a030b1201060f08010e0304050d08070302010f020703050c10050105010509041a06030a0501030507140a060f02031608041802030903071419110109 79
    0x1e900b40c0c9000f000010b4041426000940e8500a840c1840e01507003132290040401041076803007580c0c980351151604900408420141d02d8911401049000c8115024107240700441d05900d4580c41d040322011704801411100713030443d402908950a90070040801d11514000b00441d004030207403607007042449402c0d5840b800000c06140d101348000d21803562403080d898440b40d03004010a41c0c03150071f07207030503800f401c0350715050410070340b01260340000c1c150050001e00300000301d0000d44403038207103e0000030b08950083c003915000400500c0344d0001c0d814154040c039686803480303c0d2851086101c500007042c03940112204070340702d078840004200300901040020003a012403800d2801d810003007408540521600c0c402c95081105400900f407419009004581903d07000e11544000d00441e4244460140e1092003040b0212904030442e910300252482924092840030025514102898880c607088948039400142d07107000c4c149200300040310f80720100b07038450703c2405078030b2102000030009803040e4150350 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 813383102 1250 813381852 813381883
    0x20c01050c0c062a0c010f02030c100f0b041b110d0c0201050a09050d05070e090a080301090209010207080d02250b07200618030c060408031902031201060809 69
    0x481240c400c0404078204030545426200181c40341d0b024a507004c1007a0002c0140010300d84264081240c02034003048804541c1820780b141e441107036404000700e03500d10518980c00055080201d9944001030190080310b0000030030140402d1400603480080e0468120840e027560401c00304c26580c42080d0010444951454a903000d841d641c03c0c1680c3c00707070000180141c0281001400640c0c2c0d0001400780c2c41800142801401e01d070609a15894026a00c40c010b014903400c0180710300025081d03031800030fa12844690310010a50960340307001c049102030b40098907a9030640c0980080840d50100c20000e140c541205030b80180b880741850022045003900303040e100071645000300f07030500800307084400704d840c2d4541c8515401d5003a510140195010001e240c40300f035101200256003411907402e10800d904641d41241034850403540007013044050f210310320681c40b05070400d0007040342c26a000000c007121071310140181ca02d00301aa54a900c02444242c0001010903075060900c6020760081007040c041c0003054 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 813384352 1250 813383102 813383107
    0xa03020102030315010c0f050a06110301081011040506160c0b27012109060f0e1905011e02070311011e090809030a050c09130b0406020d141006020c0105 67
    0x540000b0348030720000700100c040500c441c0d0480c1d075991040f04c12003082a0040c1c0201c0d0701024071300d00389454401c03110090b6982800c2ca400c04000485160031139049900102c0107020b030217030344154a4045e002c0c003108000060000c0c000000c003070703d0341001407082c130007650301814464005e85000351081e0307540c2d0461111828180b015800004201200e06080402c520000407928035410049502072402402241e134a00020400c4c07140f20320a4020350f020502c0f40e038082c403882508040c558100c86400091042a82c0060460107003c1e417512110710350180108008110503e241e40c000b00b90360010300031003180302d03400a500014180d02c10206003410b00401e000340552201d103000007110801030b80743d040c0740c00c0d81e40400c2000c00000d0000c0b5110300d0070280035102070a4043c10071546454000360118081c144440c00506c01d2540c41c0c8000c100d0642c00200c40c089a1a9078940d04000d401c4078251211150303603541665103640c0743d140c20b80d204a0b03500240340711107401c1060003424480b4050040d414030070103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 813385602 1250 813384352 813384359
    0x702030c04020c031308030a11060609040201081b1305042f0c01060806040809150301030804260a05060901060b0c060103060b010c080a0207050a12112e05040f050a 72
    0x106029040880441e00582c50360400780320b00b42540309101000035420780030360300090b140c0d0f404809441d2031072494a40c443c1e00701c1200c070f00c44e80700c4104407440c550180c0c1842c0014010340c00750040540060740d81481e001c000c40170269034a150b42c000d40d595060442c0d004010419490709024050000c00d001003e504021202c00d074481150080765400400000081082001800250300100c001e01215007110800d0800341813000c9598080408030707000d4292801002c48a203244000c5034122984505414a000e140000c2412105103103c0780707548800a00c0e81c1006024030810443e5004c0340542c016110740c1c10300c2890750303003151020780c886401e84405004540074448080345580c1142e820a002007400820800121460a461400100007103000700b1644a95039002510600780d0700c0c207541080b00c0d507445545000d121071503584020909001320408001c1030405d0150815402d400c1c3e03070f00a1002c00e107502c069403100340003200702c80000c5d404502041070240758401c20006081c15562240308905 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 813386852 1250 813385602 813385609
    0x1090b060304060f150b0304020f1005120702010b12010510080f0d050f0706023004080d240b0d0f02040f0506030c160b06040506042d060e01080a020102120702 70
    0x1c0100b015000b10b40e500070024060142d500a0810706010218021a4a0310740b0040611a0000c0c0c40c01e9000d4040400004403a0401318011800c0c02c0c015100c035410010509403180c0901340007000402195220103c104160702c0b4001c44041501d4803100206040c40d22174044961401c0380d5000582c140c0c031041c2081c2203a1400b20b004000d80300c091810700c0e030360b0038030b016045024469030100401036440000c4601070000301b483c1c901141c545002c83c0710103203001d00d00c4503100c81d0825207010700030f84010020f90b03001880541c03003915107200e00581d0320003083d07101c0c503010010502e82d4041403102070002030b440034000c40c0d8455444602c1003010300b1410a82400040c07000c0039824055603001c0c40c030010200304d80402c0b040a958108681e02c5911700301e407442c1d01d40800f28610580b000c07401039040c2000304080c0c1c5494055521003191447c460701044800301c480240d07803a620801820400e980705030100701c009200001c00d000c0c0c01000010081038045200092400d404031681e0181c10001380801e000581c2c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 813388102 1250 813386852 813386857
    0x60e010605130806010b0a170402130209180a230c03040303110f13061b05100522110a050303070b0a0203100902030412120e03162a0e01090b06 63
    0x44091400035290001c0703018404560055403c01c000e1407258800014144035004000e0101c180c42d41c3d5012280c1710050700081c8142026134000f544159800095006600c0d075601404280744c00805046c02d07070003407016080c1c201900b5184541d115440e44542c40c45000014529042c40140e01c8540d0350038a840400514617000280c40201050b4444038801030306440802980c0381d400c0d000d06925980d280340780c42c44000340260701c0740c18003042440a043c500354080d1740c405e14615401c10080c04040d0f0362110fa900081070010440d9408185988040c042d8030404403490301018400d034a1007c0e85054101046040035050b40720030b22940c01004035000207020000080d4000c0b904180258a98440e01d10107480c40110342c2101500600c04001c00050128842c003414442641740c4600d903050842541840a4070318005c1b0303102c11940200480201500e10848c0902e0301405042092441482e000084c40c00304250160741c110322100e100280040b06510b03030001c6c010540706000300803015410003c9034160 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 813389352 1250 813388102 813388109
    0xa0906181109100f060507050c100f0f0909020f07050c040b0102030a0305040f081c06050f0a03110604051008011d07080402060705071a130506040b040e1803270301060e01 75
    0x80b801c15010800000c0c60600110192020f0707666452056211200102560001034090b6114070500e10b00003c141084550040c8440d078035920700e002d504028205403070079061040101304100903150300081d00c2d0789a101805802014000c100d944001c6070406510300305c05910ba480c030036454804080a80e0f0b80004c111010b000550602042559483c00c14084001c4501e00291689100041c120b0b0802061296252016096002005001c2d1a44140081040528001900035082442c20700214480380b4030300c5841c1070014641e40c9041d49817030101d04030184880110022a122400501c030007002d81d00080d407102c040031200c0080f0314103110018138465019001a021340b100013103850911200b440707420702821000982884111400103101200d81c803001800709103094902c004182461320104980454400c007a449041608000c6c03a6104000040c083c0140b401404046061411040c805014603010302101c580311300494001042c15040d00740c41c03583c4664940340007844070314000034071281074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 813390602 1250 813389352 813389359
    0x10e01151d19060b0712081b03010612060f0608160c050d27030b1f2603160501050f2503050702071707080f030f1e0405090a09061811 59
    0x5030b5900b100003100510041d007004c45555000070b5803c0034401e010f5a4165940442c3d510f40f01c40da138410401d44c0312121140c0c0c00b07560b104410030042040611896007070180507041c040015040c4d50f05c0041404800e5154403032004500b5000411004600030390035484103240e28180300440e00902e80e41d00d500d511104c24007138140a19101c00c48900b10145074010740440c109244450016201d0426000b4188111005460489001da001104001c03d4109104540c04403074544508020754200404804070307401142000d110501044a095401144501000e40035000009585c180340d03280c03180d0040d004010080074418245460283c110004280d24180300e14030340040d140d25005400c034105407003036221401c00200445108000240803c800003215a02c20031205880c0c48101c040380c49004400746003881d03079001c0c00513640040011003509044219101110b24094031000080c201340010f8a15403200c5036034082c5101045030610844003080142130120709482040d503543c0c0c1c1c42e000010b50040c003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 813391852 1250 813390602 813390631
    0xf070306050403090e0a05090d0e0f0d0f0524060109050108061509030f150f0f041e12180509240301090b18011406131d010e01151d 58
    0x1e16200f0f00c1c4d0705014202d5080b0003d01810440f0b03000700030b050140c9042c0140e0261000c44d034082402005140900d61010303180603902c14941d01003020900c081c0704241c0d144001c000025001400074006141d40900c0302d15020310102d1182d01f40c000b111801800c040c14860144028403076a178110008681c00301040729902c00c00314224070088100e004801219030140f0903281800d8100c40085071258a000481c42c4081060b0746a09601c20403042c242c4010444c00a101c001c9800708400101501082805244807590515184d0358180d500300541030040000714070700d5980e000720030000200700060030100c9000b6140d080c29460310703c481284a0300001d120315a036202c800c0c2d9403020341242410b00c0d0010108000e52070442c003440d001007400950020365500c1c0c210a4a81e4030140c1c15058003805002e0f1841d5480002102000000d11071040070302c8101800a00d0a9840342c000d02500e00340316480e400100340440b0903d814083d04031941c000e0603231002c0f0902031a41d802584a001d41e4040c3c4200c20309107 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 813393102 1250 813391852 813391861
    0x1d0c040b0901230408120f07021203070b10060f090b0d2705010b0922060e012c1e060412170f010f08150c09040608031b060601020f07030605 62
    0x1d50001c0404564044070401810346a94109220f01800480b00c005082e5a4240c0e901e40007980c140c07003202c2c80d07060410f400703001e181c0241c00c2c0f00b607091307a1026011080324500100c6494907410264102c50090086c90203031004c0c8041a40550240381890781800c042002d14242840c9807594001e4010f81e0b45000d0ba20541e0121035900c550035a0380b0010301c01c0040800d011b20741001b501a0421a000700d0050130908089051a69000070142c041e040890040346050240c0da21038006d8101d11000095035902d5003e254003a0507035801c1c0d591403003041841c80741c1251121040609200104e0104910b04401c21800780e203120f004a1200d52065005018601a0754100b074261004070348603032050005c08100040092240324520024140c03881c00c0711701c68803e5a1441c25070b40d10700d110305002c0040e580d9034000c0303490709800d41c001e071040e8a03000344081034050300c03505054030f15005181d0402c40a100d41d0306001150b00c1c140102c40e0820f0302031014100d101ca491070603540d9800d0a2000905142d034410010307 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 813394352 1250 813393102 813393107
    0x20901030b060d060e0c121203070e0604030b07020105071e14071a0703020903011a1003050c0f0706052d161b05030d1103060109091e0c091d0c040b0901 67
    0x480301c0301c4d40b0000c10017003000692840b960300c00b4600c00391402296201c0584007540c50004205c071007039800e0307581549140d8032507800700c4030f0710360980c0d4042c1c02074020b100200002c4c5000e25824800c0000d640006190310740000300404400d03c00c038403103007007060b0603100840880c3e002c51a00c40c1641000d82d896940c42c02803a180083e60105071b030420b9612501c200740400d00740d06400401040404030300030310920800c840c0c0424044180100240d10503102d4100150344d5000380c201035400b1440011013400d2010f0032004540b5503000c41c0084031029681e20800c0414000041806441e9810481041501c0020300b034900ca071910281401c200c08040c01c0c52028958440c03800c06011842d03402c0080d01c1c0c1e04a40c07800c10707500e030000c80c804484c150078034000480b4005840142c1e481941c0507511180e0403460420108024203d401d04103410000480760002c01c00c00c00d00426142074555910f0020280c0750142d00440a1300062103018496039040c140504440700d9815942a41d2045000076a03030384251005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 813395602 1250 813394352 813394369
    0x4020d0209040b040c0605130e1e161701140d0602040302040c05210c03060f030705030106030f02090106020606030c01120e0708100c1416050a0822060804020901030b06 74
    0x294400305940802007084007942c03641c3c2c0914405c031006a0415200d10307081e20b0500070012408000910242d08120381c140c10440c0c90380000b03000184800f101001c0070010741d5038100f100c070301000340c10080c9421019070340000c08581ca104804c904500c0b80d410301144401c83c401c42c000c414814809407810310103200060341190015640107000b0442d10148403006009074102d19281e80307020030802490414100100091881440d8615545180d07540f5402004905901007030030315054454220b0110b02501c00b4410700c0050342c00342120181c0f0840c244100603511805800800071500300c1800d200f6140c40011700380d4212602402c160111031000061003005007042c1c80380441d80e01c07403043e00003201040401c044030400f544003000d00c201c025400c801e0724101c400c5c0c0f001005005040204111000c0f02030010560203102e1401e507103112a003501d0b50721385500541754045100e00380311074020b59a050101c0080080c01c4900f4226224546a000602d102905100281c40c3c10741c00343c002031140d65110392 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 813396852 1250 813395602 813395629
    0x715090314130501082d2a03061f0f120b0622060e011e110a060c0206130b04060e1c030203010e0f090a11011404080c0109210206030402 60
    0x610340c9a500210040e60099210700c40c5901042c000301c08103401202042450340ca9603c0c008170700710031b81c80301e0640d00c601940050034400b80903900d08031440651a02d007044040781e90090300c0b0689034141401003107094500c410303100005400e850031090130170360456030f0650b204129052404421003c07803d0100642885c90501c2d82c0050700088002c5440072000804d001542c03240600c404441d00d810081e140c15035004607242c0804d00d40c46003403804e00c542906080e882c40c003174a020107040350300b0b040c07461a20304403150444405456104198889074108080d07039124846215280881c3c0c0c064560280c1c496010f4806019035898082f604818142000017002081b66010401c5000c40c2142d0000e0094000780244041850b03050b01280f2006d81d002c410b18001c200b810b014103810841541c41e6075044607010040d6050000e05a1141044800b4a003c2c100400d020030241400c50f51030300004004083c590094020007103d054000d00f500035002411144940c10ba8046035651543c1c0002241c210b000740c03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 813398102 1250 813396852 813396887
    0x1603031706031504030c0c05090c09060d0603050a0309170601062703020303040906031509110603071e0504170a0320030409090f03021e060604090212060a06180207150903 75
    0x24081010381c1303e24a5040c00380181c005034021030b12002000758084040d11072b048510300c20f010041b0310385052402009500800070300055819540d81d1041c0c02c00340110b0040d030104464100c108500c0d480044024548080310000d4000b0f0740c100100075040e0034811b88141c1d00100f180d502c42040024411058010310703001001c0325103541d41ca043c04405410700c3d0000b201c0b16003240d182401c500c42c4034003964805642c0000c00c9901d0540c080203219079900000c0810080103038920304000c2148083c1115040041203548441d070f110b040224003203500c0c0b80e0507026040c0394851904100441d900c00030420100d003090800b0024411090417241c0b641c02190444200c0c24900520481080100d80041c03001034840e401341c8a840c0701000001208119107000c2003100d80203000007074402c1c80d05500581240748024a429441042d01c3c0380540b41a1044824818199403500f06110004085010b07025541e1a100d055141030b1807a0388010007103162a1208142c00d48881818041501920320710221003586d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 813399352 1250 813398102 813398143
    0x23070501140613060f0e190501080109141504020415080105010b0405040b010f0813150203040b0601030605030a051507030207140c040f021207140904140108160303170603 75
    0xa01096031004000e54209116002e11072400c4806000703130140a00b00c0d0301002061401c2880c0c880d04101008004055940d00e03104400b5941c0c51010502c10035018106a400009041d20f86107407105903148a44d0001300d06500959501035403014165690754060b60543d4082891042480a000c904c403403030f0454007065081030300125801e050708021340b04480c022602800652120702c010340f25180300c1c4a42d00000385404002400c20210808441c000c41d03c6003440c0004101c440e0a2401280c2003660301311220028141440305030369040c042c050140600b24003a00301040d03036a6605034bc07900003404c407010007042e0900042800d0701981c10354401035008000c20b41d85011076180191502010070245e13205a1805400003c1620180300b904c50540286086201c540c8a80409440c240d030110710f81050468100700a034000c3e255030044150600e0355041010b000c1d41022540c5081810001e1440c03031201c1004001c2001c6548609101004a14801100d04d2a02d414002c2070522000004c3c080c1041c1b8034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 813400602 1250 813399352 813399371
    0xc0f0e012111030d080f01090513080f09060d0e0f010204150c0c0302100c0b09070605040b2d0702010305090c03060403080c0f0721090302010f05090f0415180204030323070501 77
    0xb1702c0356114002030744410059030380391030410040790010746110307011142140100c00000e0740307600104484000c00007021305001c595070000b90740c0e41c0040f0980b0b88098440640c41a4101c0c01c1240304056004000254101420048030709026815803240d6001c0080140402c01400340001402010b950040c3c4034101c0510040c030060b0259440110072500c00c0700e0343c80001c0d400b56003c20410140c070544e40c5e58034982450a96200310383c3e002a0300280c02107030a5440135681c44a1000c010140300304907481183c82c0c032481e00016003154070052180000d500300c0034105009540c04a0000d500c070f41e150070f10340c055865400b201500d90042c0201c044070301d40006018424401171207c40d460450010b00015840001441c080ba02c641d003d200007070100300b1030015001002d0040b005030054100141c0b03410000c0f0381c4480020184c1d030300b41015080110880383c0c1407110010300030201100d40031081042d490913103140d03001000c030002d0040100140c0c0e16042c2080c11685000c045403030003500b0000a100800700d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 813401852 1250 813400602 813400607
    0x207080417070603180b0a0b03100b03010e0a0804030609080d180c080f07030605181005090c06030c030601030207030e09070305061f091205030c0a0c0f0e012111030d 73
    0x42200210307184124040040e055119004e4048212440a050343c4d21a100c2d50b2501700f150300c050301c0d01820546541e032510440c8c40420088003980f0038003c1c04203207207010b18241401c4901c00c1e201d079055074009145480c0401c07c004100c80482ea4050f10029603d4282e0034100d4050049030000744242e0708000c1c07810b1040d060b95110881803801545101c5e00140d4640000e50b44400d0708010343d2403038012250400124038103510803a404860a04000c06542e094a16181004080810395040550320811710a80890801c100703c000402502d00c2455401d00c0e150800540c00000c0078241016000540f4000f0940706000c44510a130b0302030801d8109040007100170b0003420301118440d00400c1d1000d140220700101401944403554513032901c9400e07a081c008a031145c603041d400d09440f9031200b08081031000404203d032000c10b0340a0500d0079002c40c00c1100000381c0c0f01141c0d01990490624a0051180c48507418900b005203000703c2c800d288840340c41c581074407108001c41c0e000b54140602e40c0c004107000e8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 813403102 1250 813401852 813401879
    0xd021503010e070c030c0f14030c01142d13210807030506010c2306090601140a1802130f0b0702040b03010c02060613020d021c0b040c051c02070804 65
    0x18402c80001d402035071030142c201c03000b0280542c064000380d602e442c20350110f50001d90704c0d29070f00e00444c100d00100c40302400031882d69210f00340100c1240e55410b58140c1014000383c40d030303411010814541032640850034280300201181018200c501c001c40000c2041e21001ea609450f0a40d840041030441607440c1590911414901c0741c0c0701c01184010340090b607240c0c0319114070361146d10141c40740300a50305140c8504110306681841d03860001d090407605805610b08000c03c42c841e5545000501c5a581030503070409496541c802d51034080c200c0c030a0188010304228664a010300011000161074400d040c10120b441c0c1001c0e030009524950750500407a010f22040020001030303000b07807024003030a107490b01854202d030760300424400160400c0c00812181d00e0400c0c00c05181c49655000503003051f074a18005800c03a4040d114980c281a040003180f82141803c4c06400320351f050489007000304d058848806892440303034410001c1240440d0b44090300f59140d0358191440d4a800045180d19903807600116890071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 813404352 1250 813403102 813403109
    0x9063f0d1115061c020d05010504081b06010614090f151905070f020603070507150605100201051b0c120d020301090b190b16060c0e0a060215010b090d02150301 70
    0x140109545070001c000c1d03202c03110703002d004050b000350380a81d840e01c0041641e8200c40d10490380303e565401200c0200700f01b401524011402040140c2e503a801c1409255000918041e803030480790401030040042c02e400100c914160118041c1c17444c0c0e182e8020b400500d001490324480c59010300b2a9071030040701700e100e01c0546445421841c400c0c804010401c8161600e018154004005101e810385180041c00e1220255822403824100300381002c40c3c540d1018202d00c112142c0d056084c2c2e450200b0400c0b071401c41c6603420030020600007040175042400050398144091020116419000103401c01350ec603040281034001e00e422804940c5030710b1240380d801c01071f5100f03200b460100c5080040b000220300d441c05054110000040a00250720314200c9014510740081015215050300c00c1d201324042815401100c0d404245a81c40210200c0c05038100407a40d4556081081158401e054062440751040300c0141954203400341c1c103440d00705a1001400171620704c4002074101c02060344c14801c0908200c00ba5069 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 813405602 1250 813404352 813404387
    0x90d170615070f111c080702040204030b010e070801050d02061905040b0a02070807060201060806070819020c03090108070305130b1314101b0c02330909063f0d 70
    0x8440408040084820145c1d107004541c440e00385040001908840c01042c4039031010b000941001d41d240c0300c0d1060290300b41d2002c1d41e05c44401081042156005000d5400f410003194041120703600e5402044c1c45d801a08858150340b0120b40c0b490350502d01540c10f8500401a450a143d9a1201808000d4440003140300302d641070701c5400c0e80403481c00c1c010702a1a040c0c070001e500420b070507910328004480045024040c0c0601c206c0817030034800400128001030059583c038034019607491490700001084540000e01c00b2080611303100034809040c00040403040c906401c040c00c8030441c6c0780c0c800224070341d05000a0007000300c06120103600000c07001190341c3d01d408506c10300410110405d24216211443c20301d05940010315198078003c018030b4054050045050046e4100300e120400c651a040681e100f4113052101102c0030941908a15041040c50f511000640b452001c011000c820408007030494080b0503164901c0c258441c42442100782c800180074445411120248501d8401901083c800c0058200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 813406852 1250 813405602 813405623
    0x30809220f1a030a030804150f020a0509180c0a050d0b06070c0e010b030f070c0f0b07052a0c0d15050721020c06180c0612010e090d170615070f 63
    0x245280104200030080d8145d160007031b50742c0d00c2d50f0f0b40b0f441112095910008250791076940948402c00361010345500245500d4640c1d903844418100314269050550442e100e03070705482004040303001da0056074601c03206418110b842300d40202d015400b030304c004056903800c464003040030018071107486003040455210107420801a40c82e4580149176100840f0050038144030400841c08444c4110b00c0c0c2540940200000c00341c0c0c80690707407000301d510300907950400080c402080301c02084151101d280e8000c0074080789203a40d80f00442020380c580c00c62243c441d1007515038101203410311403512140804070000260400880c40d0141c4050f00c2030700810084103401c80c40003060100fa111520840301c0d000b03c500020032003591098050000601c10100d086854056502d0031080c90312524098000008820800441036041408804a6280c020000f50681e409081501009a044a0071402011498200801c1c40e50f0340400300c0c0d0305483d060704107101c92600103059024002482044082148242400349 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 813408102 1250 813406852 813406901
    0x9090b150603041218090515011b0312050c0705060f0403020111182107080a02040f0204060504090209030705270f010b0a08041a07020d02070f030809220f 68
    0x71680002c840051003240c960850b000420b000742c034241c001540a0102e41015034686e4182016504107560503404420700c484800320725a0480c070f958411007027200c0182810242600d00800303c02e400362140000e00d50f41d9000c0750304059144101e81e03003242c01001320b0304981880036801d803d401c4200c400b64019441c044a00100c25140d00403918903a111031030455400d1412001c00100c624460400540c08e1081002c1043da01018007610004091210140006001c00c0c01444191561002c030406004d204100910400d508203054400340c403203100005031203110f00e40c042407900b0f07401c0e0400c1d80d1203c58006da802c03501038080c1d10310320036400c560307480c03aa00e84a07901c0d05104208280a9504450b00902c4842d00c00ca11031501c040d03005018444200840c240303208a9030050800351000c50058020914014180f070301040781c07800820b99605200b030840c0c51515140e4480c025056414440e0000c519215075440124007051085a41240e003008170b80c0815041c030004050138144c00714411117101000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 813409352 1250 813408102 813408109
    0xa080f0f010e0a020a0e040f1505030f0607261003110f030601060f17040b042a0909050133060908153103121803031509090b15 56
    0x1030307048850041e28a121511000d12007400794000100c208200400c461b00451b0b280e0712809070380d24580400d08006004c00ea41c0309003a52820194200500943c03207588544904880001c030954400c8041c0380100d20030040c190011081c1e031442c45983d200000c1c0c1020b101c4450403101007602101c0c03041f100300b02c444c0ba00d141406055001030480660540100c2c1c01008180e02070900e13041c440700782c0c1c6005481d1121a245c000d400c2c003402da406460800c800c00800c010801072010100040d01403002d40075201410040c0700c01001d41d9402618442074070340101c24204142500111903802c2d0780200303800950314003030030510105078007025000480e51a0303000090490180e04102e042e900c4000c060b01340880300c0c10200d454504050008031428152400f1101c1040b201403400000c0d9a42c0f02005203d000141001800401c0000301c0980251404c603044084080000054903426414100800c4007500d00c050f01c81200d41e81c0d81310010190034002c2010402c00d004414900c1f40f00070030000004a03880d030341030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 813410602 1250 813409352 813409381
    0x3050a0c020c101106040606060206100e1612020c06091c080f04050304120510200712020c1012060f0522092f0609130e120a080f 57
    0x22003000d42c12104400300141410302e10a50b91803a14140428110044c41c019840c10804032400e0346c1c100d136510030500140f0740c14040107820111300d41e50386a6950805210510140010b88440c00881030444140078181c0200591180441030800454036440342101282d201c03842112802103d00034040d40310804042014900c01e00107041d5225404c1d6580d50a0001114401600c10307905803200784800140c090300c580c0007000307442c420400f401d01e070400c18000d1403d035203042050b00c40e140001341034082544000c0050f2009560490071001d648000e0310001e0b0f040200804886030440c1e4200c41100d030700c940156842d9002c0105c50340030000280ea85800c058000794902600e6030003420506959186038129114241e1404c4102d00060181c0007030740e036803800c20740c0c5110801c000d0000000e20400b11212000c10046d900e8181c4003145004a10000610000f40303064a101507542e17503400030071400030100280c070709229440c07260660703030000e081000d0304400007110031541660030100080c00c50f020303900300d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 813411852 1250 813410602 813410621
    0xc060c0316020d05011b171306050a0605031b03121201060c03211d06040803070c0302010e24090d051206132f0705060a110d0603080a03050a 62
    0x9503050824416680201c90340010042c2d0b807003282500140049402072141010100c03c0180c4030700048010384010700110700341c05440090801d190104050101c41407180311030581e1200b00081c460380c0b0341040c00010111034001c5500341c4102701e0505071910200700b444501540841c226180316905224071602e030301c0341d42c1d0041018400d42004020440c05030011448040c030038100141d40001804d880c0e4450403000088040c45900c80e0014201840342c00e83d030581d08680900a440c961a2a4480c0003062201810324000c0150300110502414030030750185030304550003401d4582043c0160380c02a90880300228040d0b64045000110f012008002110040c00e0110344030a42803491108400080400c01441035070004e2901034455803c80951003602d903200e1103416002c00e041a84510003400d0450410100c210380d0b005c00c15400401d10010300c0580c0a0f000c9180072a0707400c1030081c13980d45270103251100c40c280d41c201a804400c000202002d021503000c141d40c01c00c00b80c0d1b41d250040040d541403a5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 813413102 1250 813411852 813411877
    0xc0a05030c0120011a131b1101150b18010f080402060a120c02070603050108150105040c0509190302030111040302130518030403060b040b450906090c06 67
    0x140c2007080c42d4000c001d6811600c4a450005644a9041070359030709640d40c03550444042400313a6402071044c544281200541560040d082213403500351110802c64080701c503140c80511a4901445003141803d41010725a0304820a0b030445156507041d5400454000e4100d140c2d02d80702451194006500c41e01900c10001e44655030326903031707496035001e01c49540e001e00703503103001c0121541b40c40d940c0c10024000c07602240d00607401859a00c0c0303400801021900d044e002201a90400d4100c2c20b84141c6184000e0305480e0700710b5000803501c0071124140c400d48500580103411441413076250740d503400c18607608400c4900a90003404440d0000040344c000e44a940002540a01d004004507200c0b0302c65440a58030a054034112110110308280452541d0403540c421561180c84115403000b90030540110740890a043e1002c40c600c02c40c0b00807001001d908104510552504002c051740c00346403807007907210940c01e103440c01645070801601054844000700e038080360512038040d500c611800c2600c00c0361101841d42 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 813414352 1250 813413102 813413113
    0x90603030f031306230402011218021504030c0b0c0c030a0f1e02030303010b130e0103020d2009010f21020307050d03090f15020714150304020d0c080c030c0a0503 71
    0x40340d16070504a59a40103480240d90344e8012100816601031050384124000c12003c0d203890141f00040c0a11010400c0c000a54205081155005070b14102030640590441d09001c0d1140b10342d81c110305500440d84041d10840c426440000d024107400b00074a1102144001d84070501d041405050782c07000590300c0105800d8101000a0100710310740c000810202904c0c01002140000f0740010340356030000c1c0c102d8060038400103031582d501020002c0100042c503050641c00e06562568000070001c418204018101e00c140d4078001c05c241a5100c00c3c828100360080104c0c0865840b070b06e02c3c0248201501501c2d042020100c14603898001450620b15440d03401002402610304141c14403085001f1803104600f40840c9802c0840e461010350440c0005d012000d800a0301c403160380707400030b180650a40c012511401c0201800b100740c2c5035000401c1440115404196680d01c0c4d83c404101c42c803004200c007030320944000b03d0100b40c130000400c0c10446190304900720b07241c1041410400c00c002c06544545685940403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 813415602 1250 813414352 813414361
    0xf36030607030905010e0f06090d021b150c01060603090605061c170f0304050f0601050603040b0a0216061806050c09130b01021f0903080f1501030e0f0a03030b090603030f03 76
    0x39411600090384071301e00200c0c21701025500c0c103150007550700f0407160680003c01007000070354040280c402a006688014900ea40b80c2503c49440141c520030a1401040300540140c4007502c0340003181c0308003001d8002002142d940c0c080040c0180240d09046070702c182820041051071800300750010403200c40003854a000c207403540d10400d0000b10202445035105040c0414240748011002851140b401031029042e40c001d000c007254200241608058400d9500784103000215031411002c940c04520030380010f0351a114500c10f02c1c200142020001c02240c1080550503004840070380e07034203c80f84108414071043e1684d1641103d2400342c1248950850142d0381940c02c001c8203a0084132002a041c0181c804074030a10321901440c0f01194603150300d180d2144960010550300c2000268401d090059100c4e01e8244034980007040c0950304403281c105511a9100d58600c2c4080c01a4002d08019800b146d18118003854083d01402e454614a807080d83c41d00009074850034080100c4000004801c2594559506e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 813416852 1250 813415602 813415607
    0x30304021e060d1d1615020304180510030c0621051b1e040e041103011b0e0a0906081b040c020d0c1707060203060907020c03071503020f36030607 64
    0x1a141011181c014400075013080400c2c0c180586000116107440020b001400c294800490001c03802c10306c821984200410400802c4098001c03001e1200b116001c195501c1d25a041c0a130b41d90365400c042c0003080a0440010b0342500b01c43c4024030584000820191a40d060f00d41e0800c86004941d105036452131804280039200700701c0000d100b170208071411091150021500c0780c031240c205400254500944100f484188507400640c41e28008040b4002e0160104030704202c00d80300d0a0300e14250030b00c002000c0740805680d4900119001e002c016600700081c595410170641d0b1940381c0401600b100c45290608025420300f800381d01080000c40e00203003c544c01c20401203e404840c03800a90740015030032204420740600200820340700e030080328050303103d04040d0200071403848090980c2c8155807113000c40320b905803404203003981104d0380d0701d010b02c010000c1d4100a80c0a071140303071400b078580c070000100d2482d200302418031020140107032030709a8070513940301c00071110807040210420341c5940040001641c803407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 813418102 1250 813416852 813416861
    0x807032d020c03160606051513030f062409180218180123060f0306040305030a330f030503030105040504031403190e120711031e030304021e060d 64
    0x80c02c00308032480c0809000000c041605401411a03546440300c404000500c0e00e51056041c02c86600070252512900e1035904102000c540b000505011800041900384001940091b242000304110440124400c030451140c10320355001e8000140e14103145000589205030794441c0722075000c0c2c0030b85008070590010000030039000f0446240c6070041c1c1600e0004400a0041c0248502c1c8500c8003404101c02417075440341d007070303008214902400542c0d290144039500040d1071900241c1606160780d49441d230584000c050128120540000c0c0940b4009212806440b03150198911241004001864a644c403410382ca0320280f02c06805030f40184018400c5145c181d01480d002031090030240c07261514810401d20039001100c08403041c041400c0d1081c00c90300340d8012201c0e80303a01d0101410b0100426030f00003c007402048009410540e030440c80d0b9000c0e4a007088281c0c14000184070313958409001441c83c6c3d0703a036402220220700800508882c00405142103003c801d07540e90080c440c5007018010a4180e0040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 813419352 1250 813418102 813418117
    0xb120910113103030309030206150105070f06061211122a031005071809020901020312150a03121806090e2806090b0d020603061c050d0807032d02 64
    0xb04000850706008091402c4941d00851007510041483c2c04181401307030501800600b15078480d20186000c07081aa4000f00301c170980750b031299000d4085081c1c1d05149000b400c1c1c5802c070003489a82c030800b080c2030001100b10340f140107204a40d0086542e0107079041507190b11461900343c09803900f40f040380c0c801e440d1300105400c7c190405003c6031140c0c0c524400d0300c019900207589490100c1d005466421020401b02d100034043c1c107000405502d080d41d842d000075a81d1088002e2006c0030001d000101300c00c40d01c1c0c440d410702d44c10801011240980e460b404c283d4003855400082e45c000c5194468110940c120b640ca682007119040d48501c104285400040e84100c80c0042c0700348410304600003180d0391141c0220700000014010680010300038200301c1e4480881e165034501c03512a8201c00756040059a808045a40c40a401d403010700321a20b103c0045500a4500381c4010618000c001c84a45c4140d8401c0c4154031403c550741d4280f1a1030f881d4820080c00c001000c4200300455044944804114142d40090815 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 813420602 1250 813419352 813419407
    0x71d09010b18090f01230601080708150d120905010f090302241210050a1211010e12070902070314030f06060f0c0f0604060c0207060c1502040b12091011 67
    0xe0b070040c450709086845c0403841d16184803036582c0c016403404c6c90a51190380304c902824481e5107410242009442d0740f01c010065440c2480e1a503c0701103a45491088405603039000246021039501d514010f40801c0090040a00040305075121141d01c0c0d00c96010340d02202d4025200c4105c5065032602c8070341c0c4102c0c00c40c007044d5600080100c0840d411452400d0f07440f0304501e0040d120b26034104410440c2c0c00115178031950b06140500038580c0858034859919000740c40c2428400b080112540100300d50441c581420541e5010f504800110f10380c16400401615120740d8500203861143c0c84d0315103a0340010b4a041002a8408000608500f8510014290004400090f0f030810704042e48403850080910324814441c0c01510a0204010031802048a0400e5500240104600b4044018002500500060081c1d428074141c0e222946050b0b041b900500310094480f980c0d403075020040038500205444008a5200e040100d4005074203078072815440f00341c02c1d0400c80c90020000f10000403034200c0c2c40300701807 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 813421852 1250 813420602 813420613
    0x1b01050307092c0601051c0510030219090f0204060e0f04060f03080d050c190e0a030602030708060f01090f03020d020f0d031d090601050307050318071d09010b1809 72
    0x915024154602e0241c80c10541d80380d030003203202d07105052038803c0603040300d05000d0103000d00c0700400191080903160000b84a0001072a83c0d820581c912011140c5e44080e42091302c091705c403400d03051140a244141c446101080c001c1c1501c25001c0002c0340301741c0c2300316400180c4400810b031081ca44607010203e0180020004220980ca130305e044036003100d040e8011a111440040c25000e022803501030107034841e6000fa100c60900c002101a01c01d644003018843c420041d00c0f42c4600d20595030840840042c54021070210344070f280044c0c02800c000001d4845521440c1460901c2c8825840303000140142c8202054240b150b518541c2401641035900004070380c001c40c681e810608680b506600104054041e40e03409203d4101c030f405010010046d00d08181c000d5060104001c01642c0182c1182e410600b249021552590745840e0148401ca44048041890250440000b172198040c00600040d50a40c2c51424541e00e03603070580741c00c903854161041e170400381c207a543d50740940c01d42504e6603022a0080903680b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 813423102 1250 813421852 813421859
    0x507090305010f24050616080c1e100e03040909050307051006030b0a09020306010302060f070c17100225081c020711010c020f06031e0f181b0105030709 67
    0xe080d148808100f001a943c1c0e600c5031420004103d41030103a0501048042800c0d80c01c05d800b05882e44103a00c045a2484884100d11042141100440341041d5850090350340742c40b000079401003400320301142c50440c3d114111014410416070f1181c0030100c1000b000840c0b810740b410030f00030041c0081c10800d6501e4041481a003010620a2259040241d400800051030a00f94a811514854003604040f0500c4c031340038070100141c6000800906407601110361544554602080c4080341c41640c000800b0880c00d82c030009850a82842c0a500104104c006d890b03174500b94004542c12405100c41c0020070030244004000d040c0e810340c10100a0702d005269a41c41d100b80708529840e5aa1224804080d0340c1c0e000907190705000c411007074546181009d00c0d11503004003440e000112242c1c04008418812070380080454108414074690f4100900440e4041c4a20b24244209851100040754206070302d03c410403103101020400314415241100600c4011f2404101c07a004484030341000f4038603000e001c498100170 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 813424352 1250 813423102 813423113
    0x108070c080712020f031603050702150a0206150607050a08090612070c06110a081b0d061409090f1c03020904050a020a0905060414130b041d0105090a0201050d05070903 74
    0x109001402407103d809a8411030304000d140220b4400c2e5140c2d650001c0c08504240c04a0005100403039405280003600c90209000084016100020101c50850001100c3c0d00417034022642c1e80c8a141d209440443d00c2c8201800e1110500c9502c100400b05d4202409000010342400090300800f50003420160034200d620302c03040540081a90b1040114803180d0030402008814000e00280d0a20001000d0a01d0100e1030040c1c20040003178882c0e2040855250300e40c0170045180d042d00c0349070510020611849507101c00c1d1003601c028030801c2d9800340b50700702c00042034204005060398400803000d0040c00e0340001d910030502040720070000541016000c010410300350b580e50060500469542a0040e0395004441e40501021a2a0b000c58001d01c402e0008004009843c40d1907801c0314030a5683c6054581e01014900050140b41d02c1d0030703803013841e0403003400540d42c0c07400c0400c6c0300400c00c02c000c01294503072840056a5504c0340c84003d000410030440200c0803401608500e42042841c144014210388030360b070702c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 813425602 1250 813424352 813424357
    0xf0f150c0f0331030803061201111c05060306091c02031204080c010f05070207140d06150305060c04030b06062109030a0e010c0507030b0c041206140a0203090c0108070c08 75
    0x140080c66a509401042020700303070503d08410003030030018445203103941d40f004103030b010081c0360900ca81c000c440c030811001000e405c60500d900104010658440400301c0c404011408080c008420910f428001005410005542070103030300e204008004620040b60801d82c1906100c1c404411400140000c0e15581e00c80c01045001da44510002d544035801c14904608651070405001c0e0b8803400c00c0140015940c01003444416141c0b0000d1100c0740c6046600410045418098000c22903880e01c08901e0b1590003c0c5103250943e40310b07034203541c4a83c0720824052140c2c0280d000107015141e90702c021809a1030a20000c0141c52030541c403e101590902060101400741103403402c40a800000c0e11591081e400741c1d00c024464024288201c00c0fa0f1640c840c103548014034000100b02c1d8480b00082003010014000361002003c90f000803c4481d140c1d40741c200080d00119080340008114140803e888038000c0c020f4921481c11b00009080c6071401d41e004403611308000d0124414402c1010980740800c015100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 813426852 1250 813425602 813425617
    0xb150a020d03050603030307080708070212030f15031b010c0f02101d0102190b04060b0a09090b061e1003060515030612190803090325020f0f150c0f03 66
    0x6085152649074000d01074400080285200340c1041040002c91a00041c46c0e0b50005c41c5803070b1448141d5600c020070703864190310122481c0ea4840100c104102001040c0d0418410781c00b200c4442204402c0800f41030351182c8142c1850078a0000c00c1000d412540314024040010b402002102c81c0e014040d00800c61001c80a01704500003800314a244044001040c0030a070074141c2803008000602085840c0d000d00740d0030000040070300300d118000c0307010311225800640d2100d070010400b0307003142c4e40d4400396801002c12400450740c000b0100c00140c2a0b10b400004070803288000007054020308044020441810b29250005081c103070785030400f280d9500c1c5c1c014500013481e10031314556902e050031801c0015042100d031040c11035a00c0014500c48048905420140d400e03402070345a80c99840748035644d82903001e0801c100403403120700c5071030040c0125408019080f6900030b954001d1020b00440a001e226544400241c3d000619048000280304d01840205131003045802039662030301079400b1003400e40e0320405 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 813428102 1250 813426852 813426857
    0x4050a090605061906110708060f0106091d0705070606030506130204060b0f0f031e040b0103060c030902060f0f090d081201090902010f0c050307022817060a0b150a 72
    0x2000c1003044514440c8070340100c000c403081c02105180310203002d40e10b0003600400040000010580e40200b0040000402038407115054481c1843c01c805d6480240c9800d104c1c1c500000c803064000100d84850032180040d00103429071414690b950040c09842e60b40c4280c03011185076980c0c01c4000041070007032000a00650550302401164080342c01000190b8400f40c01001101c4000c01010f10002d021200700d48100300583c41c61500d0303503100032412404440d00f002d4900d402e8200000c120030046a501450b050f60310680c000c1001000346081201150b144201c003d421403001c002104404810700041d0442131111803059240c04941804540b000510600496130f41a0100b03024800203d0046014050300d224401002004041e4000030003e100c1c6081001c00e000307009402c1801e010040c0101c400707940e0050b00320740307190484100700042400c011400802800c1e00c5078010034011001e140907024203034400c1c018034a070f88841c1c0641c8001c28070406403035440f10f0b1512841038140c05810190aa051323098 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 813429352 1250 813428102 813428111
    0x81e090601060224010509061212280806120f0109080a090b1e0318190506060105040305060109020906070f030e0a1d0a051b070b18070303091505040504050a 69
    0x2d070203482c0541900160402c1c202c40000f001c005080c00311803504458040b115940c141d12100c02141a1208805c0b08032214050b030707101c1180348407224009040c95110318200c18040b401400c40c0428502213400130f40d0000b9598004511140b61060008083ca00c100301a16640c030b180c4640d080c21515a80b40403101c0c60320129103040712a411400d894024089240c600d4500030740f070590400d4460402000100b21030700440810302c0c0040000700c1c521590048803c940c0d402c0b0001d1100e101054051400301d52901c580c00025405d035118006403411a82c2c8000101003e9007803415030300194201c5403140e508008107101110101e460ba120090b884d5000e034a40000d040500c03014001700428a0304260742c0e00300074040c0d240c05c020030950250780c04121035000107407644440c2600803401011000c024440e001c04103202c003c1c001c08132500b03400340380d2100c4024100c4e04041743c426168141e5120141c08219400703010840f030035000400e0100c0400602e0301c14a090384800001d005c94905503800450320790344 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 813430602 1250 813429352 813429359
    0xa0c02210a0b18120703030906061a0c010b04020906180409021018050409080904020a140c010b01021c0215090312010321022a0a0302060403030c030810050a0501081e090601 76
    0x503126120025500710084c02d43e40c83c1a0760039440340e10034584002c003015600c00c9900244400c0b0f42c009005404441130601800c0039100740d00c1100c0d0840328031840503500c0c1104d410010301d454400c640060340d0142c1036034100124490500c04070601444496040f5440300d40540041e40d9031402c04100c0c1007984c0343c4413075203d00c42800d80c0b103180307140e0081e070700881ca8424040003142c0d2038015109128002c0301d0250303a61220303603400c40b000344200060f440724080102d00080d80400c19000500c14003400c0e07084030340c244a049025003c1e2200d0380d5410015801480240c02c44003480c4842c1540070b600307a03085034a050a20102c4041500b8242e0042c0c400300c2a0540200c00304d800890040d140301000e00c01040b44080c100c402111049070283e45220211040344899010f03102c4824407002150010203d545841d0f0f00d0401500c0d607200e0039000c80000b046000000c006d07c00100e8803c003580c40150103442e641c2d08044c0103507680700c800b82a100340b50549001c0e40320b042c29031303500d12482140e1710806001103516 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 813431852 1250 813430602 813430621
    0x190f0c0512090604030e040c030216050120070c140307120b010609120b01151110090204062315070816020a081f0f0e1902090c0a0c02210a0b 62
    0x2801110b8503070858418400840e41c41107042140c1c100031074000440200f450307005d80c001d10400c80c0c200e881c402554651401e008041d4441c00c0d4441014292281013010781a40300c0c0903124a840080c40c10303440d031009108a104614000c01a0039000d000c030755045844906951420f0b518000480c1c000090744014020507071702c11018001420024009400030311581d880f400400414000e032464250003458000b2001d2240302e110700c4464800c0306980d0100070102c11103002d060031207000c0e400f0702e051100024400d00f851500318407002000d44411200c0031500108a203ca10012509151000501105021071b40410013801040000250030b4009031240c818000c50034043e6003c240d5030742003041103050101102001020107507002c940050300d140c4e61000c50000f400d40103051501407003180e9092002c20841a403c1e11050f0080b9108507550341d0b00740211402e80f107986c040800160301c2c40e04010050504080d00042c1000d080c092149000c00ca8036900c0c5000c96440042c1d072440c40794414490900e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 813433102 1250 813431852 813431887
    0xd08030105130b0d02040e01110a0207150e030a060b03010f06080606031011070b060303130618080a15150504050a0204031b061b0510020409050106020f01090b190f0c05 74
    0x4202ca00a0081884107400181103115405000c0e004544035541d907040300701d00703520200080300d804c0609910340d80c402c0c2000b03585510780d00407408130390300c1c40843c54021030089140c00b5000c14000c008040340500c9031368400103400c10800031070b010364032030105001815040c0030710006031048100034042460070600301858480b404003065105440e0040080040b0502c4c03046407605a0058a40c0041d52220404a440d40c820960315402c00e0200000108910b80d0140c1454081c1c85455160f414041c0c456400c141c60386014000100008000780341004080380d00e0704105140c0c01494452125141c0c0d400c013007016204200c5400802c0380c2d00003402d000f00303c20320f03207035103080d40d940001d04440908000e000307050300500d070052610140c4804010410000c2c20043e1041c46070b04107100f9910f5642d95030000b000381400b03009000241c00388010758620b50b01c0500c00d2090b02030300f0580c00a090388404580c080034142044139201c07a591154165048071005025085200d07a048c3ea840e95120202808180d480 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 813434352 1250 813433102 813433129
    0x7051f051204030c151116020102070b030c07030f0f05070618120302030a14010803070b0414250e04051209012c040b030319050a1709151e010b0c0c0d08030105 70
    0x140b038951081001c400c03010682e041c2c10300d61101c0701000d854230300041c0d2a1a03229840492607140010411849601d8003000c1c00c0a2486510386d40b8002981000036142003071100c0404002440602482020a0380c0d40c000340c000e0302161080101444650701c07009208182401d40f00b000c40d40000500c24150021700c81e580707252400303200c10165941450703801c589a1003103a80c0030b080c60b80540d01142c02d06c41194101080c030b0745917000315040c81d00d80c0625400040419031540508007108100014000300d555400e61185510201600d00b60b0301103590110326030418242e16040240d012001c1c80c041500c604202100740c580c4c0801c00d0b00744601c030304000903907400e07590082c02a041400304912003809800d107218080c10303c2c140700d901c500c07071504110380403281d198000244403901010b11103815008602d070013039060410403086040e43c1d004042107014405074200c0903548202d5004000904400010300421407102003030700e100c02d01303000002d4040ca08030301003a44d0802001004101030f14140c200d051a4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 813435602 1250 813434352 813434393
    0x601050d1112040323070b070311070b071b020117090c030a08030a060f06360306050601021b0f0d150c110c0301060b0711180a1d07051f051204030c 65
    0x3c5030117512080c0c10a0140c00340013000c2800b00c0d0085680540240c00100340ba40d41801c035503845000f1810701a40301c1c60150340302d001280d01c0c0f2034035000c0000348019030042e0f00d8068540790140c0908055074410718134000c12448480c0210442968207503820300040d908a80158070403500c80c14819054411920303070390b101040495011508011030f0782c0005017262103400201c0340b0b0a91800c04c00c40d8054111428450300603030cd0501c0c0011080040d80e40c080307405203000784d007260342400c0100707070010b0365020070f0741d945034014010207090280f458403429000b10746226101c40c41407210408281c000b61441400680d0116400061085d1110020072030416134060840007030101c07030700d0035441d0451031041c032078050000d84400c074082410780c48006410428400c4002c6200c22450a010800010100910203e050720810b8070103401100c000035522043e600001c014501c125910010040e07103d1012140000b030080070b1103c0b945101074000e4040c411400380d10340c050b18403c83d18140c4d0081e840c03e01502403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 813436852 1250 813435602 813435647
    0xa0203070506071212020705010c080403180533040608011a0307082212050318070b040b03042303091216050103020f0c0106030c03060506180601050d11120403 70
    0x1041800c40384c100b10303810500300307035210701030750040b01020f481160005801c86d820543c0788003101d81d01c041d41c43d104a0192b5210418000202c01406007904c0d07910030140d10215070b01071111030118205501519201e00f07001201e40182c4000a905903401c01d82c0800042084440100003461055103401101105400b0701da141d45440b040190000130050081008030044078600c3d510008018040222203802c594403000f182c602040080041c3d10881c2c400f08860354410343c88800440005403407090b100c1c11080f00d42420305110f0388200e5600000c00642d5503244a58050b60440314644452101c10001000b40d0b68502d003030400e200014240303c000401c40d5002d030301ca404000f2078002c90441036031801d18000d680e0b00c03c041090070040c01400c3e0213108551814400108104400ca40c08040741c0c0f041d1400c1c003070b03035664008000c2441b070041c4007004048201000100720358495030082074a10400200051404007404070750005401252140303038540d07007040c2400281604005803240d600c1030001030f00c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 813438102 1250 813436852 813436867
    0x10c0807170c270307060c0812040f0213020304110603061f271703030702070608040606090e0114180705130e1f0c030b1c02010c140a0203070506 64
    0x14070145039040400e4000200700d01003400d642a200c111101c6503000c0030140d50400b03503a40b01040482544034680c0c403e102e003c0c0009140c500034581c8070007084d00096800d00340070205400c40d68000005004803644000400306100503546c40001618401c201d89006807245014580030210140c8001514402c0105108203c0507607034020101d03420501c9608607612401c40354206891140318031400314181d910726001c401d014070fa85000c80d42214250541c5000d8440a20101c94683c441652841c1c0140c020190130b00c82240503094081d00300b4030070f2038000361960f554031111049484140d080c280c50394407801703c1c540b04c002c9080e205801030a10040b0081c0032503010036066a4800d18400c0d80d020309510a0384c0c81000340c5135400400142c9805058484001c681c92455042c1000c0c00901070301d480ca000c2c1c581c1d01e010b110380325038041c0c203101411a0144410740d103075101c005520070b8400c034101300c42440300c000010054100207600141407801843c1291aa104250500005801050040900744001c9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 813439352 1250 813438102 813438107
    0x110903070b042c24100225060519120c170906190e030d0603080705070e06130f0e0d05030a0c020c06031609030b07080f06040203040c030b0c0409060f0503010c0807 72
    0x550481039480903008180a444071500a040c2040506036105009036915040e8640118281001f140b2941e1102c03181c0464100100284001d4064070000a6050011041300388541e203031080d000c002400c02c4010350300783c5481c04081e02c0e00240da41001602d54280004180143c14030542c001c0c10701c00c080c050500d0b040d03032001d0700600d5490303030452500c0d2226054031080e08244112a083d102d2600c00303111040d04d034240500740b42e000560854192040b0240050b1401490680c1e034060100184100440103c1d003983c40040d1061002c19403407556900c440c08042502040304901c0d4481c2c030384400c1e0305c0b4039101800c10221041e080ca180c0554000b400c0200e065940e09084a44c001e40d4104000441c04100000f100c544210382c1004000403808400e003c00c11790400c0c096881a40701e503c850000e91399001c240020703030100740d600078194400d422042c00041e000c0c04049510200042c0c00509203641c9107103000507611140e1140000310324100d0140001e040a005a441071a0981000200341c00c001c1d500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 813440602 1250 813439352 813439439
    0x90708033601120b190e0105010f020303040525081506010207050406030f080c030906030702062508132f04110702090a0903050d0e0c031c0909110903070b04 69
    0x103c9440d540c0d58040050075075128000d001c0c21148410550001984400300300360588000e000d40c42c0400c4501c0060400c942c0300108492041341d0090180240c0040001d0045800d4092010384860309480080491002020461051400d011042000702030900e4000a814820684c0005000d141054020700201d10000121a40d0036441098982d6071806141601d0460045500442c0d20070800014011142c2e0b000035054026101c07203c4074000344049080d072034080711034003840c680841e0b40d070303030000c0c2c158440310f070200e0b003124080c06090001076071012120400841c0d62a1001d100c4014070350b040450f061038810304030200c01c0c480d141860140d2640000e400076400500e2006803603140c02e05d070400c0600c65801d50303400340085003044c8a517160b444001929500d0840486000340318414170646c82c941c403018807a114840035265001c01c1428400c02a000d048007401402c2910401c00c00d0036240c1d01e08000120092103580400750700c540c10840e182442e050001c0b194510b50501000032040315030302100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 813441852 1250 813440602 813440627
    0x31b1a07170c2706071b08030405100809010b090117010e010608060c070f0507180507090509060d0302120301060320090a0e041515060f080906040b090708033601 71
    0x88543d00c480d0402c014041900441041500306030045401e50402c51458440082e500e210842d17040c00c3d0f5201c08205940e80607900c98035074062442c4c90f05115540c011038400d604411501c001081101006d000304600308001e030f12129030303445405a07400c8114028400e821070540000001d0101c2031034055040e80d15030010380035000c840310001e00e132820441e00c01721000030958030005481c4aa40e40d55400300805141402e00c2c0300403400d000000c0c4000380724003245016104000c240386065100d09003808811600d0f11012002c1d441412600c4449404d81d00c0034500078025a9800b060000c2c0800340c90b542468809500400c0725403d020307070482da03928401080e040e59a2280900c501d560760b03040409030480f281c28070b1131000346440a880c7c81e440743e0a612400355072564656500c40341007440100d4149508030741000c0140c0040c004100000c00e070760010342e00300c00d4000c12503243e20f803554021401d42c1c2c051054601e41c8241030610f04503d031821903007401d060810007454813110641000103403c041c404403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 813443102 1250 813441852 813441877
    0x41208160605070302040315050403080c0d060e091c0c0b0105090a020d0507090e011203050f0a090305060a0e01110313060b13140105032107031b1a07170c 68
    0x103411103814a640840405080c0c1000d014000350500c00c0d0043c0003036011303000a0b541281d0781d5451200180312401003900a9505680f02c00c0caa9413101f0000c0501c2d0002410742004e29120000021400070050a0034000c0c000c0d0809000340450003420f60f07209514400b01c01c024800c2c60640d000125040c00c28a40c111881581d0300c103450b40e01c0080301c034028441c040c500005203103000c06001141e64002d02e41800d541c00c03050002d6980c0d07290f07140b03030400d1041c1c03100041c0050820050300000c40c504001400d0010035500344085155201d0780d420381049c5088034101070040e070352807140b1002c3c1000d002c1c000a2141200c0f1181c41c508046c09407400210740741700080e00707582c0c03181091602521240360b220407888000500f041007000041007e55088002e100d4030740f10b84145c5031481000d40a8000c480e000c00144d00e086490080305a40c10b03180301c50f4200341002c44442100c100004a144402e5180503081c1011102520740b41c03e0b00041d001484110b240d00355811010300700011141200119525400080c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 813444352 1250 813443102 813443107
    0xa0302090c0a02010b04091115040f230306041505220f050f070603060806010510022509050c03090105090a05060601141e090901300303090512190203041208 69
    0x1030b2040e409489040c00c1a40c0141c0381c55085401d02020320b1042100100844030944591582d4031800010302850003050007001200e0b1003000740301e41c0d5103c10800149d0040620030740307001c45030003e410b001088a050b160100072904901c400042407140b941e121400710350300c0e022080d02c4110005e074044c20440052415520114200c2481b504125003d0400140c0c003c4411254651200030007800d6507116086080c0716110020605242c00e864a02d082d001542c004d00181c003200c001200e041810018810059030709170008903086503c0d0203610320034444000150381e0f03810110600740c21140c0091070110503070404010b13280007400114426801403403d1900f00140300e00c0881c7d03043e40d4880c003510030741348100f480039018980030b0000c0601030b0520215209840e503a610010518007100800602c42e0681c81c80741c1d114141da055175980f030900c90103031800003512040340c3e5840349048017800d4011803070305001c611a0901d944040d10b400c4100c0051014605240c0303801c40f91034010a84100080081c2c102 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 813445602 1250 813444352 813444367
    0x1051810170c030706020c01020114040b0a050705191e0509130e010f09050f161a1615200903060c0c0f06010e0403021204061b021203120f01050a0302090c 68
    0x10002d088a01c41d005041e00d20a5640e944060354408001d04440d0140d402c00010541c108280c1030541c0c4204e0304001404010354030b8402c108010700004192500380202800390907044849080300600415a035214845142100a1200e116002c484a80f1301080b0040100350019101d884403d0310700f815400340491034840482c0c00b0340c058040e480c1c0d01c816042c40c00031080300b80140010114621030101090303a280d41008115185200f0060003034000184400d03034101f008621a00060a11501805044170002420f5842854420420049100b400d40711018503800c4d040c20120781d00171907090318410b8030b0070107e40007003a140c01008241403030b511004107864061000c107122600030203802000f92043d07981c6900100104030415a0203400507c1641c114895214400044809079031013501c6501030300e400740c04044144011400101d81101c3c2003110030802070000c00150410b40e02490000c4524540001400048071050b40903511901013107400f00003584600c10940d810001c490342a030740d0750f41c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 813446852 1250 813445602 813445649
    0xd020301020f0a030207020a09050705161a0903120705031608040c2c01050414060f0127050f0406060f180308070b160309120f0215070201020301051810 67
    0x403a8408000c82a000540031600c1354554014111a44221410300780d140e2640005c01c1259011500d01000c1003082007012901c0f02002c910301c810600ca120035a10315401c1c0021700f05a500141c5014500390b00224001801c400c20001d0b603a030001d000d00c0c0490661400c2c040400c2d1050310390811405000810b40880c042c030800c40301000190108030f00224030225250944201c0b0bc000880b8811800130003000482c4c9494940107112008c20805a0a044c64031030138104019110751700354080c18007503100325010b030b80030001110a03141d15104080019591034603050212412664040511645c501002400044c1e00408580405440340c40c02440b1b8015000c00441810b8458202a1030b20001054030420020781d180d01521070401d03002e80309408000240182c2c241c510a840040ca071500c240441104940b04207910803c03200c842c0b044071310402110030a03152180b826640c0b440140d40000c018041400c0103a4002504202c044040360b0030700d04406201008050b0740500d291107203062090491840 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 813448102 1250 813446852 813446857
    0x3180c060301260f0a020306010806040f080f090409061b14070618050a050a02042f0f07061b0e0607120c02040b1c0308010f030f111c080418050112020d02030102 71
    0x10b00c3c0d011101c040c0c44c48103ea0340d0322071152404038480d118002c0003144040011607400c0c016036001e2000c12140110b90b41b4a0059013109000020022b801e009007482c0741c2d914025154164020350001900221a260541c440500b0400300700c10301164000c3c00740502c840e0f000f1592415081031f00003d9504031450045440880280050300500c5400c44940a1103004aa1402c009108803400c000e684841100844200c0d400c480742d1501355120b0804003024008030000f4604018038001c1c3d1450b04100b59070300303c122486e030902d007100c0d8548030700020130a03500116901403250045035414100040b86e5145c0e00d115000c0c009120800080c82c002c101103444d40c0d0030034040481c0007441c11034a4152001781044550260b40180c0002d00f1400000440304001c284660650750080e0914080a4890706c1d070a01c41540c2840450304a600741d100701a10804801c02902c800b881003221130341e5285820000c0c0c009011400302c50703841c83c1c0f8003c0104500d1a81c48161440c260b81550301d6002c007441400000e0090 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 813449352 1250 813448102 813448169
    0x20703020a08010c0813021c020f13230906160e09040b06011d03070909080c0a0818040501050d120c05011104090f0e060118060503011103180c060301 66
    0x180c416100402c188038107400001840702141d036814520369945542c2e00c032902c10404040d402c881c408041e90040070300802880c3c4440e0000d00301c080c248a0781e6001c42c0310b9440c000c005504456654072150200080781001000171007081c2c50a503480c1c10724410094550700044c0200400101c081c00e03554560f03008603604100510002c2c405090781ca410f0030485071449048131190b001507003c50391700200e44403900f0000146500a0001e10b81142000d00c004020701c5004020748800e202400380040e60392040001c0822148a9104540c64484e16524208441c10905800e441542004018007807503c0d0044080007054202e101410856034014040e248583c150201410550030300307403007014440e2004003c000700c41c003028003081251b00c440507150440c0c40101341074500342c200c10010410f551329100040c142d4203c0d40400140340303239610b000034216000d0254030a1690360100c10005d03081c01503007240b50541e0041c4060035906215400040c05444140103a0003901d07040b403e100a003245921044208 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 813450602 1250 813449352 813449359
    0x9050d031b0c031e030807050a0509060712090e040b06040c12050106020616110d1809020a0207050a05030a03020607110109060e0705210c040b0409060f0e011808031602070302 77
    0x50000c40c20840c500b40310a00003039805105142c1010360b0600c002200104e10398240d038030059039403903200301100c00e54404280f000820009012821203036681c134000f050000c0c411021000d05240030030016000443d5030388001d114451240c10000403d18402c4141c1d8042c9003250005881e140c000002c1e1103c0c941000c28241080c9400c00104840d5000504c003806003442143c0e03800c40d000110401c07190103428548042881d08141c1840c900c00c0c0c0503e000c00201840904105145521245d001e400c982200c8601e40041e03000c1d450400c19818014034800180c1000d50150007100c04076140a540e0b80409048a8104004882d46610029082d80400c55a69004074140b1020030b13040402d555881183c081c4034420100c58078401d082c50601282c241401140b900500141d284910801c0010f024587e41203401a80b91f16682000841d41c0c840c03013405000304440000c8003100881094212030740017400a18440d072104518001c201ca070f005070b81d8407488440c044040d540520f4001c900303110440d80b00940 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 813451852 1250 813450602 813450647
    0x4080a0f120e06070206060d051018020612060406060912020d03050405040207050309041d0607080a02191e02030f072003030f07051c0c0f170d060302091609050d03 72
    0xb030708040802d801d4041c0586900f121020b407921410851503100c4600010841e0348410390044080c4131035001790504440e500d01c0903590150540210304507601507648246440301400400c032151500c0d1146601809251070b1400c1018100000195900001703803011740704000021050040500c980221809010003800030354980d9403a203403840c3d0b26040381140320b01c55401c1500c00c5406090703083c1890440310020004000d42e495001c8182c030324200c00743c043c03510683c0030001d45419000c01c21501d1000119aa2000141300304481d580500c40c116012140c2150001c028201003440d00405403480d06030007040c1103c08265010303d01d403460b50b448003116014000894505030440c41c440281642074018410f441008022111081c1d0003859805550040351001c21000c0c041150b82d9840d101c2d09101d4203804840c4021095402c1003030700702d8456001000d4407420b041c011810850046500018a0723107a50301c8100919001130411911802800d020700c545035626801c2c948505104001c9440039264502c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 813453102 1250 813451852 813451871
    0x20a06081b16050c0913081c0213060f082715010305060403170603120f090a030b010906061e1115010f032d110a05090a060f05060304080a0f12 63
    0x842d8481100240c0e070600403046081d8103410480142c034842c103030811904d089003a90b43e49800305034005100701c2d1ba405265059040d032155961000b440c0301d104030707800210068074124008203116269032030201041000014041654603080c89030401504141c0c3e102000501000c100345048540344c070000001100c07800010902c00c001c40e0300da00a80c02540d510b400d1780c41d803c026400340366041d11341582640c88043c2d03c0410354481c2014180e03654840104516001000000400c0401141c0094a002c08844c0040000e00b0f0148100c00007001141000c01090003404904030081c0318100c0c15a003400b80c51290401d07046420710500076900702c3c0320640140c0b540c423680314918070000d500003100d400c80585041900e0100310380d0720038481300c0d03002210074041c807191350b4010300c08201c140c2035500b001c1c8500c07020441d69103002c1024450400300500151b03031440c221020328144400c1e400640a00010001e100c0498070402c11180d4140b12070904950300c08143d50f08a9052041d208000c0900d40f510716440d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 813454352 1250 813453102 813453127
    0x320030408250b040204020a031b08070315051804031404080106080c04050c0912032104050c0a050105040614090d051c02070b04031401060905040506070f0804020a06081b 75
    0x92424800100d12080c0300031400210b100b6028445202800441d10f100001380185000e400a01c2600030034038011074824500d0000c01e101c9161018044041000761041010403030340f5129904000710601c3c55030722460710f4800812a65002550700005001e0400300090915000d900c0541c240083c21502075a51952040741d58001c1681f801190580c0c000d06040381f02c24034160240a00807640e030b046941c034150100c002c00250600000703041080b804140302c071411580d901c2c1d8520300c0e40362490301d60702c10754901403410a003804024818144102403188040c40142d0b40007058605a4007141040d00c91f001207a131034601d8501a560a86601000700c0e40072100304400440d8101d0901000c1d0f00344840300c0a01c42d0281d8035074065000c0e004030500140710030008209000304003141141c001c400011410b84400388075080c3d5808a03426582da9101c0400c4c8108150b004184d08400400d5181029450403e0342c0019210460743c440c079800c001e5200c010035807220401695600041d42510500c1d0f44408100e041d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 813455602 1250 813454352 813454357
    0x402090411072301060e01061b06050a090b010503010903050306120309030d051209062404090b101715070302181306180b2b0c0f091d0703030320030408 67
    0x8038000900e543c803040c40c104105014043c01d40b250007000045913801c18034111030b2104800007003082080c43d03039408404034009201e40f900510404102150000950801c45819001a845540030340c0c50140b80c0800b03e5402416a900908225a5589200f1002c002e1514600800031003a42c14001e4800c041d003003275084001000b800200302c005580e140e46200009403a41411a14040f110f51150154882054032a837914001c01c0003c0000130003040340d80b260400d500c01110208c1e5046100a014080541c60240e0000400100c2d03008040201e020451071020001c050448403d05402080c07030240030302d07901e1080c00d400740d000c0c0c803410740d0300740c482c0c1c120740500f0b0710f44103054014101c4242c14120500e5030040404600007c0c0c002c9107404001c021540c400c1c0441c04a82c0480c90703184481d4000201010042001010f840b4040885941052141d074111100c14101e0301c40109055190700e0104404100c60044a03010700f80000c21407540148110100030600b0f4880000a000007040b0401038070401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 813456852 1250 813455602 813455633
    0x9070e0d05010e010b1806030d0809010e0102030906060a0b0418020d06080a0b060415030b042306040f0210210b1c050102070606120203030d0e12040311240702040209041107 76
    0x5c0c1e46d040300f0300ea0341c903a0700014000e448068040d0007007040c1c155298003c06484d81c0100002000080002e20941e886003240c2060f5401c001982140040c000030303241c160494000703045101803803803800745494921407034400c0c800c170380c95902c0341c01056048140100354010002014950140c4442c1085031030041c01c118030403110350340f10302d01c2d000701c180b1460340c03c80c191401c2e48e520002c0030a190b12542c4411800e15001d00450048083c1840702c040207200070b000c040d0003548070b55841c403560300c6948108010002c200c084c04040019035862145014a98a0044160008075900007800740001d40032079000503030b02000e004c0b070710710740414101042070560041140702d01070303a003c11115840314605c0802c2600684069819032003400b8041a400701540041e0403468100304807203140000d641007440c1500154400e48039071154903a080d80710300303040000007030800381c07a403100c0309102455480800c036004d80c01c0043d02440c1c0c0420405500c0e00c542d4452050840149034141e2079a840c1d10740242008502813 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 813458102 1250 813456852 813456859
    0x6190b1c0c080c010e040906061a190810031425050f0406030f021201091b0e06090c1602030c040f020307110c01020703021e090103050d0306060e09070e0d05010e010b 73
    0x1180003901c0b4002262007000b4050503920200e149045008001c05014003000540708107903582400034100040c41d030380c0e49000c84942131481c1c0b600412054480f115202611403028809803c00f000040d200c913403520030507640d0041d0108491416003200619100b60b040701e8180502051904000200c8104c441d00215076040702c0460800c0540814401910004c0c8001000d02d00132001210040c0b074006006490000a007000003a03d809584500340c0c4010302c2c01984000110800007400000441440389038400300554040245080580ca050031912880c40d20035003040440c202d40d011550b050018541801d001402404003003410f2480d200258070588201002c00d00d000240c03074440001240481380c12005801809207d1300e16002c5c4002c0813000b5031004400c01d079929401d421a074071600d000d0b010714010001050821244000a01100d119400c200148582e8a00c520800e9076210143c45e48864030b40707480e841182014002c50742c22101288010300a50824000c03031040386c01580305800210048 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 813459352 1250 813458102 813458123
    0x215091e032d030a0e030c070e041104140a15090203160f1409040b040b0603070306091d07030611070213021215030307030c05033603030c06190b1c 65
    0xa070480c00c0c0c445040e01c0d800c1080340b000c0c000a0b540441950084480020203020340c0e15101c00c84020f181040c01a03000100811002001d010601007204081f1781440401e45080100b41c4501c401c1d003040d01e5006042c00c0c0050b8a41071402040303130a04030500010403110030299140d0400109014600d25505d0b411000124441c3d14011031922401c501d46610844070710481c5081460403e11010340031203041d1603001601c4402d1441c0742d4444034001e62040c00c0d1541c1c0094131505000a070410b035440640144d44c030443c0340481c105c2c56400441d0800449a004030002840025030462040740e0203114030281d440505442103040c44040d9400420980c000c0075426003040d0780f101074070f060100c0c05005058060340240301d074000007800313850180704080c051403c40781880d600740c004031107140c1c8910312404c280c04000b0700c110003446140203031148540118080d5007000207080d0280e40c0c070f503001420710342d000c5040c42603140c0c8440c181c0d2161114041c01740040d800360020041202441008120403034900501 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 813460602 1250 813459352 813459397
    0x15140a050405100617390a12061a01081b03090c0a060903110603010303051b1e030c060a330e0408091c02012f0303090105190603030215091e03 63
    0x140f15000151b00d02d40600d4080d0185079030310300c070840000805150424081c20300072503941e002d0f140c1140441e21035400850040e100c410580e80c0f0241119400d814001404140030703032810000040117a100740c01001c25100d42c1c41580c1c4501d48810b4045490300068841c1c80420ba640d409120081540e0180f0305040010b100103051109912007440040c2c00030744137108004c0072440e04c224040d0210803072070840316074002c01c005c0911407540d030000c003e0883e8800222501a02c0301400300c3e540c4400031440030045a140f000041600500200031400d4002000d0701c01030024020980050107892031060061a83c078142c44c0080a42c2e00102c40c45d0710481d0ba06602001e100302c11100c07404c2c8298103a5450740d541d2a50200003001c1320803002c02c45c0308150000c2101540e050100040c40c4a41c00000002c40c8a0600403000d144910003021001c0d20541890000c1c00400c1c0c0005101c0c160842c202401401366a5050f046420513140c0911900c00c0440d41d6400d44041c000080981000d05040c042008020803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 813461852 1250 813460602 813460633
    0x9090308070f050405091f06050c01140c040902090307081605040b0f010f03020d09051212130c0b0a111614030d1418100c15140a050405100617 63
    0x7425039205000850412061040f410146600d54000c0c1d187d5021507003022030750520f00344030710302c1e40c000c9000290f011424030403c170002d025000122041404403e41801c0c00d10002007039101b40d01810000503000116101039072000c1001000500d5940140c9800c9440c030041c40802c280036208061040d400d00200144901e0100d050400d45907050311341068151102d0419400703504210311441d010743d507a16401001c505d09111018440b180c2d0522150f0710014a4800041114058101c500d41c0380c0400da40000580248a44410b40711424015503c901c9043c4044420700600c000c003211500420084420f040415101c83c801d442c8a625007100c018100c409041e950501c202c1400005401c3d03030766102c4481c102600421506448610300110908501e0100704840c4040550b040051031141d2144284813164058040070090900240032151168075940c5000d60007400c00c0c64042d580c1d502290410604000c0d181829010b4074003403000f02d96800d000641c00c0240c0d0f20f00c172040c2c0540c13044a0000306 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 813463102 1250 813461852 813461867
    0x191208030a140f13140d1e050c0d030e030403020a0311130b0a030f1106040b0406110102120403122009120102030f01030b0a0f02040b04060f032702190909030807 71
    0x100b030f00070036401e2591446103107582d00180860170380d02d20840030002c3c00a1a002c0c80501c184410302c0d1504040440701d01ea0005400c5c0c810f480402c01c000003409403084003070020034a007000090914003c200744200c0c040c40b9086215540c002940320940640020030030110f150b01081102d0215080a4610a100c506e4010b962007429080e070300c0300c6800d03001e1000818900040c1e28442c050480c014070190b00c600814165803082c1c0200301148800f0904100362540a4000034001035504025800c1007400c813040110313800064001018003140d000f82c03022030b08403640b0a03121900081624a0000342169241000c1e5000581187c082e110546140080e002c0500850380a0040307000142c05980c0b80d912080448040a8490307071030907407501c1e0400d60703c03d03040c0003a1000e1b00c480c03900140d490381b4040e4050a05601000d00c202414107149488080070103041c01411003680c21001c4e441c0340083d80c400a42d941c038074240340c1110001c010401141015680c1c0c0f21400d0710707100703403a11505611004010b50710b18 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 813464352 1250 813463102 813463111
    0x102010c12020c190305090907020d0807050f1c02031017070302060702130515092505250c050901122d0203150a0f0e0606191208030a14 60
    0x14400c810800c807110440e50080c209120740c0420355020620440802c00d291a800c0307010340c00075102052404451802c00040d41d0030613840d0004102410140c0d20103130015600412040c03d100d80801e94000c0307c65800219003689080c0da9035515a2240007400b41e000390402d0790300e0b107544448624042401e4588909903814145810020b055035403440e030030046240d02c11300b802c03a0420080e41746481072400c04d01995000c3c075009070741c0c440304c43d0444082c0070440000800513081d5400180c03141c81501080508112035071254030f041603230383c040d40013a950400d200307460290444601c0d00fa0f00b0144410765003258140e40003100d041040d079a880b409030900c905440d0014213001c2a03030a05c4000543c4c1412a1040034a1654a002e03401c420380c0c00103802e0080004000c0320010140c0b00b000344980c0c542c89005901035014004006140110b04c460391f590714010f14050186c0084200c031444440d040c1400001411448403800350451076103400500741c1c00c1526111315036810701c00700400d21000c581c60700d44071f03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 813465602 1250 813464352 813464357
    0x6091507030b13020c03070b0a1b050f07110105090d03030212060105040602070905060103110403060c020c0a141c122703170313140d1710151116050f0102010c 70
    0x107040303007a01c00942c0200817060280c40100310b803c0004034104000e502c00c0400703003800036000e41d074042c2c10707034003013004040d02002c11104100010300907150b002561a1150081c680300340940342240180c406e4424100c140c1d500c1400701540c2d404166142e002002141c00811b1020000c0e1501c900544490007503010b21405a08001024020740c00745502c410380c459014035010420200035002c940050740242c000761021034a1b228001011a0108001e0349100c60584410b24600d10b028130003d030140000190922a40b02c2c03607882c54100c08480c21824040d5040146007100c1740424102034079042804001808107142c41028840d44240b030782c1c0c000b0843c0d400c02d0b510030030004068215074080d8002007604186517002e0300070b80301140c901100c0e0350305450300340c009104000720150702a140d02c006800c1000049100030030003c0d0348110202440845160403801d101c80d44611718180d5800c0c1038000026101d05c2480d44c950f4541b41c007100803000701c4d0001e0701c5040040080e2001203007a58040040d0001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 813466852 1250 813465602 813465619
    0x90c0f03052505060a0905041505030303070c050309190312050703050a0503091f1505030304050d020d0c031a070f08090618030913051b12041209050306091507030b 72
    0xc0c0080071206030004409280251610380391560001260742c0c003c000c0480000d2020f46e0144640d00f03045c4540d0790440280b6001320170080c9050006a0381744402000c20302004840d642540400c41d0800588001090080050b00d5007501340c9100800080307144000c2c0d83d200c500d481000d0040340650708441006030540d440794a0141303143c0064449520141500440d84155202000c00303405030003102c44d400030071107070100d0a4160034101040c0e0414070f030003040c0300f5081003100b000325555030359500d610140d05643c406142600c9041801d1351004035880030f400b10300c481d4924507808000440d5188105076985440c8818020b40e80220344072401200c0e15030721948590089072050b041e0440500707011302c0302c0301182e107000550000309a861280c41c031182017154481c801d000040201c8082e141180048407042070620a50000c00305002c400a44060660494200d120101610030302030007019100280440324035081c0030200c55a24036000c8101c058075440000450311a610900807a03100440c01440c994 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 813468102 1250 813466852 813466873
    0x703140c0a11010e03010f061403030c1f0216060501090c050703020a17130909150b0d06090204090602160203060105040b130e030d1d070f0608010e10080f01090c0f0305 74
    0x1e02030011100c46414001c180c505940c0554090041000001070101c0c0810280c9c6000e5000c01d0f0040f8a0111a12a4001b401b01d002140070000740b041d0650b840b207003013180d80c40c3c072600400000d2041ca00d90100c18001441d20509010094204604071205100100401d01c5500002c881d82c0c02040e4004005810481e503040129581145411040ba411001c061809041494040b401d801a5003c44078594841030100140081503440218641c2107880910800c0b082c400090400071010900030099a903880304602951500c0c0d00140d1241e40c010382c210341e142500108084412441d20040b44a03108100011072507042178011303c90000030281c00d0b41001104030003400060b011800303802480c1d11042c040ca950000e188c2c01181c1740c042c69611700c180c400c0d00000410b810b100c1140c01803000d02010100070050103500842e0207045030b0521240c0c3c202600d4801c84c101809619902405d003a2240c01d00d65100e00784194860701d1100c0c402c0c0310304d03a905075580c2d00c82d072098840e600c00500b060b0001120072 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 813469352 1250 813468102 813468113
    0x190207031a0f0f0601021203160e06030106021f02161523060f040906090b0714030105060723012c0a05060c0a1e03150e10030206180607080703140c0a 66
    0xf6410040c14010344048842d80b03040f900c0c1e1904100c030300c0d024a161100440b100c56070041411500304c1c1040e03410f1461903040c08000303036803085600142c041d6208071115141c1e14040d00c0d81a50854a0301901040504503242098400001c140f28008000c0d450f02a407110780c1c0900d02a2110001c0500945c408556070717260030080c0350728141001e590401e4980e070340c0000150f014824000c0461048a141000b814181c030000c00303e001d0705c804108984d10810042c84241c1c3d508041d9107140d584a019400c0d00d02007030041d00481651524815425803c2ca9090300194452011480702503120044a01b00ca19845200f640d8400d40440d020f0900d802400c0411103204080c40281240009810280303140481c0b8010030340d02041c0b1803074050000b940e400000910590761440540100381da0300e03845140d810300c0c00003201070b400203100080c40350394001401d0f402d491001440d20400e420080c84c8a44071f0301c1604100d1515800345400b2000100340c0206100d40303240f44019104035900b100001d0611900a0380d94 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 813470602 1250 813469352 813469381
    0x10c09050f1504090903080f010f2114010c0e01020c13050411060c0c03011406010e0d0302120f120606070b01181b02030705120301080a031202190207031a0f 69
    0xa0360031241d1280b002c0210040302c0020401072280c403000180c82a0503080040c0482005022040c120701d034500104412014804d050055410803944100a4483c4281600400d1900400185a1010f8910360b1a05c0034042d4072180785034065446620310503100d40c1c0126202c0840c2601590311462291142901e51081c0d44442d0f40103101d144241b40c00502200007603220303000b0407035555196100603840803141c1020300400c5091000d00035928a103084c0f40c00041d01c00300594840364098414900c040c0c0c180341c070800840407000c9a0b0446107907582d200c0790b0b18801c9076129410342103140040d94045a02d40c10540122407172103030820000d8290340d08007944c03001210f074080102003900c1c3d19401b42ca020741c012802400c001b00b031160011aaa040d00c0d00c5c00e9402e112098100d100c501c04180f00401003001301050200d40c440c1c0c1450503540c041d204200c00030017400b82c407202040320321b41d0b40d0b0306015072500020102d055a0050b011032828022a2480d03a018a0048845001c8100c480b400f080c814410b03100c5c1d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 813471852 1250 813470602 813470629
    0x3042601020c12030a0e0316020d210906020105090606060a051e0d06051e0f13060e0109050f090c01121a04092906060405150d050703021308010c0905 66
    0x90320384520303002d80d1480e2059114076030420354400010b1100c0f94403e842140014585000914145501401140e000126072407010b0300807022040d5010410120340b070607584251424501c64180d0020140040c2405541d0142c0c40140d0301e4800802d113112000036040f1b1107440001c100034604034008008403429000460510122310066003c0d511150042c00038000301844158006281071502d0104610341d2001d4540c2c0c40701b1815400805540c0e15000c401484010781901c00d0040466000b25140062a41394480c01e8000b50a03000809c5c0c061840d00458051681c1f22102801174a9460450f6100d41c40750100c3e9000c40c0112003060b6402e00150080216035600c40301c00c8841900800c04101038801e06a41220390b102a11114103200a034500d480300e100150043c4000a8038040022034403910460107a03503c61310210400007440c5408600301c4401e0444901c042c006800c04003006406508212000201c4622005021440d01d00500c2020000025030340c1e1040c00f189410148000510b0308076 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 813473102 1250 813471852 813471929
    0x19050f01050d111e0306130506150c0f010b151207050f03090f0f0a0f0b2d0703060b0313240c120507090f090216140a03110304 56
    0x1000704200b8841c81103095001040c0b800b01e541d420002c10740403c1c520300d0701c120700080ea0140207014064494405a1042c0f180c00036001a4544502c4002072250710040c3c1044031084001401c80c0111001043e584a140541c80c028000c00d2019402c00044090390306600d05081c105110f840f44220a40ca0314030b030422010f041007464442c21103a6146150710840c2c40403003581c4640480c0c00b450390704204528041070500e01034281c00350300ea07136a0428541010300c09002e00700640301042e030010401440325595031500c002c44008070480d0141002d10036044401c1c0c004285040000102d40d02041c0460b84183c031200042400418140c0d141e14404100d540e41000310179000301c142c0c2034502070707200740301e1403408540f2024a0070080104e00ca0944400408100c100210f070f600801c84520001c50325001e888400d00d0240e04c0d5140c5d5811182401e840c2400a00200340d0081d004040160200314400c100e806696151a2584011000d035500d10492248041d0410b400c40c4000c5400d031304d0440521049105e0307 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 813474352 1250 813473102 813473107
    0x90c020a0f0303021b0c03101506050903070b1611090127060b0d0e0106080d0207060804150203100311150a0318060e0d110705060d0b1f1d19050f0105 66
    0x109003001002c1116a89005d0702d521603500032403140317801c001001000107090028414004840b440c140c080005204203414002c0204400715241c0e0107011000c0a003440110503134594030000c0f1a14140580d080003500c161070000c2c0c1483e840d0a26001d1917040e94004d00b0300540d0420381c80010310300c100700500c071901d49550300c90021410703000050081c01d04013902840420800340381102c0d0b60858403558404c1d03c155119580c071450782500801c540c4210380e8141480644ca690ba410020080c19600321840c06080c400410480c40a4100c8030600c196401002048110304003c4280b100c6541c4001200c1200c03a000d00030440850b00c6a0083c0c0481520500f16052000f02650348800b0364504580d104019004024a149210780c040452001507c50100504000303141c400031400c64414507842d081c0060b25007000c2e00103503e0748040030050580e054103c00d44001034020003004410021000d81c0640d000000000341440c00c0f9100114409680c03880b024001d1922041000c488890103006060040c01d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 813475602 1250 813474352 813474367
    0x6040e010609022101050f090910020c07030c0b070308180a0203010504050a022e03050604110c060403140f120a0e03130608100305060a050403020f0f1006090c020a0f030302 76
    0x28000c01d40203002010300076807646401141100000c2c4002d0f422046145898010031640d5140381200b245200e09691003421501da01d0758035424070100d09000103001d40000340e00304403803100080c00070850b4055041100e403d6250034501c0a6807003100030207800982c007040410110108483c4050014140074220780038240598046403c4d20402c45040d0740c2c64108004070019070a1030032200d80d03002010000707010140d042030441040309492034140b104150b0717108000b805e04e8603180d1000e05000008892641c8543c3c60100469030b54170111000c0340082c40410307407800f00120703032400e0318040e01004c0081ca04000c00e80720040e810000040c182e4201c00e40b22070381000e5006061000340304a1103045000c46500d4140b40c006050004050990039982c1d4481c034040020074004a55075070481b80c0004041003684841c10200c1c6482c400160685d1140510859018051800662070101005036075041c00000d40c2c60150030110740d1800b1183c1c016030820b00d220070002c3c0c4012080360903a4801e080040c1070410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 813476852 1250 813475602 813475631
    0x3010501021b014b0203030a0c1704080703030b0105030912090d0c0b04150503071205090a15270f08160507031208060306060f220e030306150a020d080604 68
    0x10001000f00c010000c08407002a98640c4c0300310001e1908100c444800e84650400d402962480018040b041503070f510038001c01f209101d00041102000902030341e01950805061202c801c1e4440e40085022070303d801c900007899400307082628403510b11580508140d4500341c01d69172a0f98440300096504c83e0700301101d00b001520442e030b10400390071000740203902c0e2410003060010b42d944555038641440307418002c008050b40d004202010080c0c01460100e035545071405414923003020124010710445c0d405100715244a242d901c43c08030f9411208c800d0f80503d20381003982410302800c3c1e5015242410100c0d6010106c1c6135140200041c9000c507110704011205900c0c0c260030005a07410441d114040201076003401c69010762005c1c1c004000310090101400d0200010740400c41c4803c5d1036001d04400003403002150b0540384058244031a0400c00e12801c1401401d443e03ca0b481226070502c92005041444203601c81b2906031000c00c0015002046091190502a152094000c01080d481519110a8640307000c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 813478102 1250 813476852 813476897
    0xb04050c12010f0b0304350a090b0403080406050a02070906030b0402131a0f130f1b0206040b13140115090b15070f1a091f0203010501021b01 62
    0x10898040305441d10790240041c0c40880041e4080103140d4507094050080d0756480302101d40055106c016003005580030384400000a40602070035803074844c0081219065800000200005521503a42c50143c5480b100054018010782c0030180c1006400c2c8014031816000d04001c0c441440e481c0115011145c2d2141d0400541d1401c1c4c00c2107820000307071030602045040092102000808442d030604c07800800d80d591b00240c114800b00700c0c0c404c11a50601c048544c41d90f48180660350303029101440780244031190304c00a08001c01d410544900c0f282c0d84181d0180c8040390312801280c0c0301350f944000e6160304c00b0103000d4aa01c0300007541c00c114200e008030024242449500c0800105500c1c2540040c5481000b100b12614142d0a80c040c1042c100300502c400700710801c54040907840310240c40a00054203009514480c1125926046071010b800d00c10000300c0060180e54110460401c00411020340c192a01640020304c2014007681c84130729886861000404603070b2043e80189800034062400c002c0700a50340 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 813479352 1250 813478102 813478111
    0xb1206040f0308070e010e0d02041e0b0f0405040b070e0105191701150903030302070804080a0305182719020301151e201603110316080d11010b0405 65
    0x545102000c800c058000d10040d90010403410455450903a0300c0001c0c1024441c20700052040448d484850119980d9170320a100a040c141d0314203100000b9a400034006242e2050660310078482204441003500d8203018807880740394000c100580039106e03044283d90550710f48400702d05029007402030b0501034410858100f0b0b0b940f0103684048010f1801d113041118540b041e00450b20459404036000140740d0482d8041007184d90524005969025030b0801c07255500035134100940328060040180103166000d0f01500c00035840ba11070980d10355020f801c1100241c0c25940c04400000700c0c01d00a120f0b5102c1108841d84040c403903d0903801d2000302409841241c0c02608901d540c00341010044a02c180e0001041310a00300b8940030303003842ca45454015103007914006500811140800f0000302c071341c00c01c1c4114a12000507142c0500516102d150041304046010030060080c4030395011900d480c1c40004500080360b1402c8080c104e07441c00450b0441e862980300d0341500d11992190040d504c192900e200c0d00348034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 813480602 1250 813479352 813479363
    0x10081606110c0915030a170c0d030615030c11060a050106020f150a0504020325090e0303160f09050a0e0a0c17061c05060a09060c020318040b120604 65
    0x5414004054100404a6007030001648141c00c1d03a8543e0f19810700039904540c04421404070b0400e000e002034902000c401000740024405555000d0303001c00d14016003900d000380c2c000c0d80c0304540080c008404031041d0b4820240342171194188103104074020f60241d20303522068900f20400307500d0102c030985031600079110820820703960f82c01041f41c2d85d414044052400440c2010707040403041603940d20821030300079208803441a0b544001c42e0855a042100200c0c264490303040e40840308200420b003113203480c41d104044000e400c0c03024045a00b40702104880c82040a859501195401e20b8400c40d010320000d0001024092101d4000c00d140c3d42d88180d0f280100b10040c00300c03401f4a00300040505840f035010804050000003620003a10444034000d081d4005403d07210304954a21040301c1e0b003559144060003400038001c09040c8802907081da004030123098001c840612121400b468101c1eaa40b040c6805034802200c041f0741041145041c4c0c00142640500070621001c00c500c10780500e041034000e40c2e044a4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 813481852 1250 813480602 813480643
    0x30609050907030b011e14010c020306091006060c02180c0c0f0c100203030403080c07030309123204031112030f030709060201050606030c0a121508011802181008 71
    0x10404c40342c07100fa02624040f6903070044252994080c4950b10550b0040c031194144400c0350440592040c0710042400c0e40081c12150141401c43c50b03180c039442518451141f040c144440896a140204002c403503899003d4461003161042e0343ea8000021809003040704050b10402a001007030314200498901c428401025001c100f98100410113a40c000c054000f0664105100300800b103030704511a164000d90401e070f0650b503240d00e8941100100110680202544240b0409a0f0000d070301c0343c144124100740070025002ca410100707802daa01d10310b1130b0b072942c4003100c10001400081c00340201680c554002810b001c5041c1d001c69911400c1d90407540e091a00c84001108224142d1351009031480146160300081120381000000701d10240300c001d00c900900030000032040700c5580700f12101d101c580b98000f03042058a100200c1c4a510000300d2046040c030f5803c141a205c048614480c6542805070700034206a10036a1801d240b081c1da40008203864290445440002a01607091000c41c00440b900300410342d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 813483102 1250 813481852 813481859
    0x304120206070f1710181a0f06040608040501020c0106090c020c0d050c01260c220b03070e0f10050301050a17062706040309090e0105060d06022209020c0d020f0a06020901030609050907 81
    0x4001f040d0901c1074900c29203241c4030300351041c0c5800d005c40341902d50a203820300d29903842e0305107507001e4400d1070072103880c56203481d0300004c5024175940100d481200340c0e8241c800000f02c050801c20396a02844020f441500501c408910b158007510b04403108650344843e054040780c1c0c11840403003101d0200c40c0f0010402c4c000400c00f96000882011000105660200c0290503003032070210545808002c180c03c050246001c50608941c0c0c2d40181d1794495031000b0003030f0402949203a80107000d03800a00c6554052680e00d90041800d002d007038640326417001100020003250382e6040820708040d81d40340ca48c007891401860ba1044c0800280030351032060f80252127111802c0e103012904000c840740481840800e91511040c8529030b555441d4000503660003010141c2c441e02558138086040008104000b036034884c242c00041c1400311600034220200400040c2c450280354610180d80f41d6000c2480313011a034010480c004c0024000c0d0340601a070386010b00d40000c0031034a901060080b00d41c10b46d04640554082d10040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 813484352 1250 813483102 813483131
    0x1150c021203040501200a0f1104020d09020f030a030c1e050d020a030e0607050c1302040801090f0606050411070305210c0c01050a0b150d110304120206070f171018 72
    0x1a000303d2600311b40e03503041d8200242420344900011000408850000c6019070506ca10b0714004c0380f1500c00240119515400d08089000600791102e04030301808804642d45494940807601e020002c0d01902c0e0418560100c1d0b0b07c0443d4001034440504488404404090200d40c04018120b203900d00354004010765101402c0207000010303d50f07802c80c4583e008210407000203c0110f11040090410b41e074908102d80204540f10103070003146c00214a03503103002c030f00b07605025508003080466409240e0410405032101300740000e542c00e12500100806041140302c001901c640010074681040d401107041043c0109054280c0d82d800383c651446442d03000c1a0340c1d4800c8002c0c03141d9500321070700040030003185030003c4c08110346030140e640080c509032010505a401c800b4540200716120445042690350745071611f420001d6041d60f020100041c812080000d07005405a0301078030300c48049440390329000c0d00402a0043d400c138000c1002c1101986400001030030940a2481c241c0c0450078400800d150150001c0c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 813485602 1250 813484352 813484367
    0x17041d09011b050901111c0e03010510050d0f06090f20090a0c050c031b0d0201050108120d1b03050a0b06041202060304020d0c030b0a0f0506010801150c021203040501 73
    0x8034800340d01d0030b0140c0e82010040c01c070000000d16a820680d44070b64204006036403400d520001100070f401003070008500003030201009032001c2801d440300360509042c9014182210004c5490032030000d0490f5040c000e03480c04120903d5003a200e0104180740f400e043d40c41038261180c40404907940c9a00b0344c0030904101035051403072035248110a40e1400700b07442000180d9110005000c0c0565135540d0b68480c2c2040d03101c0c80442d9030750b100c0507045950f14110240009003a10801505410074000d0fa207d1589042c810701419048880c0303903000f85541c201c0780f84c160846502c05c403154204503540342c03185000260b69043d0040300c06004c2c3c83c0004c140c50058041400d4460761070003184211820002417241082c1c000c1c4009040380c041d45c1117502c960700d03880440c001e9462814042c00d003540c1c0507c00401c0104820301c0034032421040c0800c1c00051059140c100c160343c0182ea595010440c14801448001c0c6d106040b40c244460701d140c1004082951740108100301032441030007045410005081c4990b50304240c9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 813486852 1250 813485602 813485611
    0x813202106060609041401180b03030f0a081504090302010912170c031807090e071208070f030306051203041d070503071826160b0405090417041d 64
    0x30240c084038412464191241801010944070b1100858626155240c680c04881500d07030400240c044d0396151100080440600102604080d013044401303041c2d4140881aa40500b45c00b10003203041819640042d80c1d41c1c4002000d4500100284244801654490040c00d6050740243c00014a204541c10588110030804400302e060203050344040080c7c14940707400690001003289200d4607a210071045602d4410450141c0707040344100140482d46c8042a480020340200503400c03a807005903542d81009241e4181c00c1c029081103420706c51200400e20120084050300c0c0702c0e1074005402615440060401c98403169169940e600214090241000501c64011036150760100c800441ca80910014030b140b00081040040100d034101003540b0384945030808015014800490017074110b400f103041c4000940d10000303c0e040c03040b100703c3e15141d071902094406551650181618050070036040c4240d10401071304c1119090320601032240107144071000341c0041d045a0041200c02c004440e031100d42400d0250 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 813488102 1250 813486852 813486889
    0xa0b03030406020712050f010e070f0911070f0312060f030b060d170a09030503124804120c06090911091c120201020a1107050a0303081320 61
    0x44244030054000031340c1c81c12180740c038042105020030f52030954102010b2400d51809507007854005040103601250304001d450f0180d40598003182d80d101150b003902c10364203001e024030300d041000b17501043d01d044c0004025030007810020b515040e600700c00f1044903583c1d444150004d1032a44140100a5070300d03c0b440d0020004c550a294510700c41d200c24041341c91038443c0035001e401c00502030a0a078082c404c1e01c0000c54000382642d855006408800000c1c1604903211070001c140304181c4485492030742401340c00f0400711403200c07801110942d0210315604e03a094400f030300b10b40c0c00e204c0042c05483c08842c00c0c0440744100314402c941c51408001400440c181e4005143c040c4c01c00815100703042034542582c980706000c5682020b841d0410790b400203a54651040a0528028080b40d103c00a0b0150010000311241d0f6039501c04480018103203d4961002c0c1c001c1541c0001c1c010410408a8030500480d50060001e0046102c0074030702e40c2e41c3c03c000512000c2187d02800115003045020724100035240c03014020320 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 813489208 1106 813488102 813488107
    0x30130051b01020d210e010603050c01090e0106080411010306030b13020a0f030804033002150f15121002040602060f0c1201090c03020f0706050a0b0303 67
    0x110580520072416500650154400284901e0100c2c8035542c280d2101040c50f08012410f0f10001940c050684810300400c90a50a1081e600103603c66001881c10002c51030024120380070a034045404407111000400030703a07401c03011107580300b0f5200307800314072651403040140c008100c99003010342030800d0a41001426580f0500182c6640c1c000c461802c90156602e00c2d0710118044c0340801004a00705010400c00900f00d055042c9282d03c8420003078442090341d1501400052040e0713052401a0302694500306045404003e00d42c0041001e03003959420303e01401142c01d6104c89001c2036000341440000d038004464180f000003803081d42c11409654442c1d40b504000e507900400e42e09a1428981c41010030034001002c021034a0b4850345103803101c81a03203014800002003030241458020315808000842e498001c200041455500c10300c0000307003504081c0e046008a80c0d401c040d1a000b41c0c002c = true := by decide +kernel

theorem cover : BRFrame.Cov 813309352 813489208 := by
  have h0 := BRFrame.cov_init 813309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 813309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 813309352 ≤ n) (h2 : n < 813489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
