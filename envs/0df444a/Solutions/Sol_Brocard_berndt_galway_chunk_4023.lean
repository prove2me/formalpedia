-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4023
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:21:20.718423+00:00
-- url     : https://prove2.me/submissions/3dcd3ab5-b8fe-4b78-ad2e-b62faea9bae2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 723381294 ≤ n < 723561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 723382544 1250 723381294 723381301
    0x5014703300a090e0a09170a0306050f0918120f03100e060a0b090310092420030907090c0504061202040e01051306081c020114100302060f0408010207140d0206 70
    0x50f1620030070740319400c0d007118000c00103440841c4a41c00b20f905954000c030031140711a401d90040d412030700010603c0d000301c0d00e070040c0420307a86840689900e03801001810003015955400001e15501c105404100303462140307000038040c10704440060203c40ba10b60072182c1c2c032440c049801c11aa0701c09030748000001c00c03620091000d11b86981c3d032a01c040d203690f40210340d60340d244480400d10300800745111121543c5414800d02c100800a100703038103d00e181c1c005004040301903100320f008885000e01c072241001d1060540e4a580c12503c8061351348241c3e2074042e5006280d494101d4801e864444503180300040c000141844240c2e0898003090302d04542243c00c500300b80c1401c40042201106000d01403040b020201d0201c92440c054021101130a0313100c054400c420360300711401c82042c08540d00c18002d9404d003c1032a0200071426007a070f2140500758000f8280314a55000e02280354018503529120300320070400480c80007001d00050007601d2080320000701415140300031904000302400400115003001c400d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 723383794 1250 723382544 723382547
    0xc020315070c1109060d030c0816060e010b040c02030301150905061b12133c090b090f0105010c0510050108072c060603060307180905014703300a 64
    0x1b00300c8132545401e005040c4000c0c1d00304131b03115020725004041c0001d0100351103003c00c242c036004908208841402800a83d8034902040191204038542c80d0050b0b00c00c4c001005a14801841e0401c09040d5051014055483d1408200c1d65800580103c0e6509080840101070b03d40c02c0015a030309130580b41c2c21604003241c039042000f5a803500c1c400c2103c088a901100d07000038103000d2b2001240172040420080180d21144185d407004103a01c501294645030113a03003449802c0c03007800300f03104041d000814003060f820400192102160030300d06842c1885540c8a11001038040d1003505c0c0030346104001000e180c1d00d000044101c61100000e03003440710010400f01003c18000110741500814122612500d070390b02d030300c0881c0c0703041c0b1186d00504481c0300b02c8018812000080e4024a89540500300a01100c18240c0a04c5d59a907140c2e1007441d01c0152080b030b0414a4036080302000c10959203000c15198141d100f10010f0314003ea1000c0c040d210034040c8880c0c003c801c412662209480c3d00c0c0596590408603403000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 723385044 1250 723383794 723383809
    0x40b060d240b0f131203031e0b1305151215060d030e010806030c0402040b04030b010b0307021c050706062c0108070315020c0a031d0603040b06010c020315070c110906 73
    0x11142441004960107001d42d08113035411020b000c80c0c03c200c02004200e0304008024102107445400000031240500348268018021503142c040c024126804240c40b0103040f01c0200401801d00070304403e07008208501780d4902091035102c81450f0001e1059030303c140b00d030385000c110260403144106a0004540c000039080345d03070400191001d00300301e98545d4500d00400e0500d050042d4142d4424400280441c1c0d0f502140094402e8034020881440750381c0e00d4154010b06803109440d040090782c4100d600c40303c0000d45050540c41c441403403070031030305061480d030310701d8240c5615400c18140580c14100d0151b081d424854901144e000040c0d00300c0c0c0c075524040303010703850707580702c1c0005010f500c00300d540c420b00000950101d07021210804200c03000e845c1c003420014a1041c00c080e01091209100042e40c60910700642500d004a030072003140a442c0e2101d10055a1903a41020226014000d0001041101e208044800d03c1001140c65805001700189042814844120311251040540f4401d114160321500c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 723386294 1250 723385044 723385057
    0x705041a12100c09090e030c0606151210030201020f0a0308071b1202070f08010c1209051c0305100e040b010504231005010f030203070e0906040b060d240b 68
    0x41c1c0c1a07164511000c00395040c040401d54807103401d400c040e002c161a540c002c07035030004c9800002e01040248541020903440e48640d07009026580d101c8000700f00381c1c3c40c0c180702010041c107501d41a24075002c64120788245001c0200c07114004204104070400c159601807044198900c0100094021401070750340146c10b01402600310020014000d5151030a9a13400c00320b07100843d007007603a050150010100013551000f8070f025028070a600b14500050051050103000c803c00a6030720b40700418820001d42000a124402c0241c45500c00d4a5512424106007138886003260307174660380401c0510701b011003480100b08941c4034400703510f01031003088041090f1183c0c5034159081103401007500b078002c00c0c442680104800c00728a14507074140a1041da24034130581750085850a80302d500380341c80f0f400420390480c0021030701e200109420100f000014900044000d0303000000a2000400c2a036034004a400e541146540c070454a60752041c90240b221242d10401c44200da03082c0e6024807508203140aa42c501605 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 723387544 1250 723386294 723386299
    0xf09071401110a050a05070f0b12280609050c090d0f110330040501120b010504120609020f100219050c0d03020115150e24040305060106020705041a 65
    0x800c821a040da01c03800d605050310000ca8101c41400c100713402c01d15150480e0590071659071141c183c0c0010784210040204044a0306141603e041c908007413078484079550002c0c001c801d44000d480c5101944659102401081d074020000094080d080101210440302c0140061080c503400f070018000a5448083d8a009682c0c0000a40362105051a186500d620701d00150340d45801102c840c07680c004560f42143c1c050900e004040e8081c2588a201030034035100d140540380c00107044e07003c000a0200d20390424200e107003061600c2c528007940c44901093320303205164115001c0b600d424200b000e61409141c2000f200d48111202c62031042680006075558484035404031000390002c5001080c003005200c4010710719409000e4080003061707480c0003802814400141c1d030f081c0950400c040b0711052150005600002262202440700d078048003045654401100452b2140d80401c4690750344980c9007002e4002548100b00500d00e84d410680d010341090300580086000c1c500d04100244088450921071005500a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 723388794 1250 723387544 723387569
    0xc0a0b19120605060a1e030204032a03140a02010e0f0303030f091c080a1503031b050c03030712110303040b01050f011116080c030c03060703052701050105090f0907 72
    0x7201c94510160400350700095000d000030811008041d00858010600040d134039440024280c1940241e0482c000d03804081d0041500000312004071800d1071240b0f5076100a00380750401503a990303894140c2540010802700e1550864140241196002104200380b010304649d020f8002c1450320120342d03030b0700000302802c400300d0100012030181d682c2030101940b50f91800e0042118800c40c0c2c000503203c00c3c0152403010b481440c003040300c52000344e0b170070800050304e0380b42d40c5203041d0443c1c1c010801005603000405441764010403145c403c19980c00c000401e1181d1055101c5c00030001c01140c082d01000d002d5040f0142a0402c004002c0001c1c200e00580d81540c0e400c50b2104180c046800040b0354040d146513124400b84a0744900c0500d4543c200c8010045804e0701e0b00302c403071009601061503125000bc8050b140c0660002c4040781003c0d0081e0007190b400000280c08943d1403103003048980241c440c914095840e84d40d10b8006004c00d042c580501a400240802010001e0a0030340085560799803510405041c4002d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 723390044 1250 723388794 723388817
    0x1505032103070c0c06170a020a021507050d050f0619083a03050a050106020a0b0406020a03110a050a020d0e031905010f0204080610140306070c05030702120c0a0b19 72
    0x80720400c1165030080041904c103511a1009000c40e010111003a5034200d2100004668100750b00803100c1e0b0013460340c054544005120b010044401019002d4000d05c44c06102841000da50303441014800c012104802149040060134024807002e50b440440c6400b0951030144101c0c440000d0088510030209810804049601c6804140400c034242d0f024400b40728051900140380d240d00118000c41a04c80708002d103907038803d81aaa605102d08004242c00440c6002501150040e4094a0308a1030b909022030500d006080d5864241e00c4280d0101c041800815148001981080b49003d010a40d0401c50640500310f00002e0381c4910a11080079080d4000c2c0d01801000020740019003403ca5480056464980f40c506940d180c11003142c020040085000d00004c0d100b030198041c02e840000a0041c203e03079100d48d035088802c40300e04902aa10762008105490060b2244a40143c1700c204030300203400304429540401401d90fa080e807200002000c00e00c03490f542d40e1081661091450a242404140c031700 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 723391294 1250 723390044 723390047
    0x3061d0a260c0c010f0219140a0507180608060601050301090e0f060a060824060603101505030a1d0d0e01030e010e0c0a12050c09060d02040c03150503210307 69
    0x2030646200070380c28480840c1d241c1c075414002076284000002601c1c0c03004d00d807034070640891383d400e495003964448101000c200300c082100700071400703007c40c0000c0c140c456403c0261122454a002c0380c0c41000082c640b4241212454068800d0703001034203038080074120700c0c03d00100081c035600044c018079410340e5480800107010882008803800411155044d079205142c10300b10749004108038420045c072030181030090381d401c104100101c003010941605000490700d0764410300466410082c480e01c0c40101605003c644401c9504113286800b140d540c62594900e050142e0800366010056a02c0148d681c015100f0a03800000c61245807a8a092405074044500d0388012809001c83c18040340040d4078043c6840b848010110720507404250a5032091203590b030f10741c0d00c44543d0340300303a0000d0130a41114002d00400c1c64095500c1b0307003010008000f50458103698002400b1070b400d142010000c20381c1c41d010040b4040c2501c00d000700804040340a48680c06005960150700201e40c051141c80c41e80000010f102903 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 723392544 1250 723391294 723391343
    0x305090a140313060509031917040b030a060501030b03060402040213180c09050604180906020d021602030708010e030d110f040f05090a18030f030e011503061d0a 71
    0x9078000104a0940098078106600ca070f006100c0290007501000780491058029000c9078403908014000b0200188500700c05a15100c61800480318125000450084118201c0140c80504a22610240d0300c3c00c0008034082250307030740c7d802075050509058010801e5900400c0740340e8815019503001da642c0c4215160000040d070950006000108860f54144880140b54001c1c80480425110942607a40b984204400ca01440c07054003011105121494051410342e08510442c0b40b0500c3c01500b0503800f00070950903a00030361625090400c0e8100074500f90f1404201c41d40040c09180700030852980426034040c2c823481a401d01955003503d80c1046046481c01004403442e608540a899441d44d486404801d1045554030429200d000c1000208003900e9031403140440400309001880d084150700c0d03401b500c000c001218284e09150b80c03030302d4500f59408203028008080304030103c120560fa046207003000840ccc54007501c054031000300804040180400095108200e03801050b070b1141041070f18000c0181 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 723393794 1250 723392544 723392563
    0x20609030312040213060b0d021c0c030c2a061d1207030f14040e0a0b1504050301060b181302070501140708060907091502070b07050601051503070906030509 69
    0x15120000d025180d1030762900b0038a015520031504240e200740d00000b80000c0d01e801780207003540c0c4001084114407041695000b041103042c000d140c0030301100d441c1c00d044225070722140c485011036220321248c0013444e40310150070448400c0c1d80e40e2100a00480c41094002d0359454001003606135540140711a14566180b0003030310154510449050100e0006006403d4100540071000300386030407401c2940d03500030300c4a40b00d0300e545010720504180c0340200c00c443c075400c041c0050361415070707030300780c040880d124a401103400f14090307200d0320b41c1c1d01d203007405040c2100c0c0b1039808101d00030f1003444681060188040c040136040c404403001003080244800742002841b9900c0c0c0244190301c0c01611007141700c000e2a0344e0b8400c0d105611a007805540340024032884200444840c0005000b00c3e2040c00245010300e0811740a03619441140d1003661562245044d0358001807094a9951141004100900c0c00e100501030540c0d01110341c03411818001c00c090314082c0240224801e058642d80041d40d24001080710205 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 723395044 1250 723393794 723393799
    0x112020105120c0705070807270b030d090807060e1819050901090b01170a032006010f09320c0c0d080115020d14070512040905060a06080f070309020609 67
    0x15a4100a40401260380c02a44103c605008042000400703c0c80460510111449c50300701c1b801220190f00300c4c85514418000896030303561f403200407009985041100814104c803540f10815803078184640343d0f04d003524a51125081000d141c9460f1403030784400e180356100d00030308040e002150302c92034601400b4128504c05090301070300d0002003041c5030b041500003040c514011030b6001c65503600c816005400c482906440445079100c02c808200113480390000c4280809604d4480d541190701802d13203420048281e114540d101c545078800c3c4568000e604c00d43c081a5203a11040400180c110054080c860000c69030703c0c2c22010400000c0e60145001e412180000604010382d41681401c08015001c60420b003c1e9a950b038140c003540b1107405000003094a03c0c005551150160202c5036861682c05900070101180c880c000e8540c0354111324203610240c4040e0083c0b02c00030419213001c4e001e100117003c05030b1000040003014002d012421000700082900000e040c900400da1a6450011401c80c1c42103015058 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 723396294 1250 723395044 723395077
    0x5040e030c240c07081204140a0b0a060e0115050a120f140a050613090204020909012601020a0503070513051c110306090d050307030905070f030b0a05010e0112020105 73
    0x11020000c141e01c01031a40301c1560b000503102d0b100040102d000d900d100070000c040400802403404c043c14901540903114100d0070f8014401101313014240720b56840200e406c0641c800c2800614403080c068040980346e803081c59551580350001242541502d10301c0201071100001d0b010340c503184155000b5464500b00001482000c6102e8441d00003000c5080d400d400c07546240d40401d2101031240174003070190340002d200307508104c02c8510301d0008110b44000ac0342e01681c2000610410b03120503680c680240300d4442e00001008404030a01441581d40341c0819461348100178141c485500700007500c0c0c12891900d00543c68804045d00311040340701c15003201e41d004c080720200c0c508400303044002e090054070a41070510803c1c800d40905580b03000030b44200306950031a00170146568880d00145030f0200340d524000c80c1601003511018280b58480d04800d12514056a051080c00801e0701c915800c64407000c401c0205604d00100200c2c0c02106005944003001d0030403500003968030401c00d4810301d200102201 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 723397544 1250 723396294 723396313
    0x1107080406021903020d03240305060603060c130909020105390715080619140108130218060424050f060f0a050d0212130b0a09080405040e030c 63
    0x210429003040c45448014032511400c950315001e01c0c4041d200300c56241e0000c000c886210007003034024000c8185802102080c190252074440d001005900041d40254042c1070b07181080c00c14941450002031444511001c20001380b00b00525102c01101120034001d40010503200303610040b00d240c40380a9102c0081750b2045440003000741c00d400500713058440c1007410701b0701401d400c01550719079800b07100c0c103111030841c1d034030360440d082c0140c941540c8114001c010020125100b0b107130380343c0791409800c088000020400003407507650300039006540010b001d400190700503000364000f61440c2400024132400344c44901c0454100d8a0303603000004200417089040300c410700d0030060025034886c03500c60300f8462000d0b4022850581000c0040b60b80300700440d62510b1030818000c3c0e098555520080c5002103641d03082013400001c61040425901a0b9048415902080307000c0c104104201c82c081d10481c8030618196880e4001450441250f080301c8044d200401c0c5001c0e00f0241906601807085119040d01812140c1d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 723398794 1250 723397544 723397553
    0x506121302042406092108090301110c070e0618040f050118030c05060a02040305070911091005281b0204020c0619050106020d0c0f1b0b180906011b05011107 69
    0x600b000e9841c50b65a0700101550383d0308001d080a2249a1015505c40d80003076900441d214000801c9892230140c00032600c011100d01414603a8440081901c280c2c02c185000c0c44220b400d56100c58010b10202c980b030484030b00daa1008061540060300080c0314402245c00142082400e40004500007440c0c01040741ca01600d04014200c0c0d22074003801c0340d0a024402c0010907130300161007540c055942140041c6031190408441e000200106018440181024803800600765101c1c034504114200690701e103511407203043c00f808080741c03032441d500c0c40e44004465010207181c0e0012584081009113071781e4141c0c4420a001140c028410044150801d02401e01081801725000500100c4502440070270412680c0e00c0b00102d0702e4003514460030000031441040d907800718000d070402d078103010b00a030121240d00c0d10303540210314075242e40d90068180d44e1004c905d445c044122608840500102626100d0680c0782c840c0000b030241034410041000c06107002284014001c3c01d50200000c01c01402c0800d41d59045402c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 723400044 1250 723398794 723398861
    0x903080d150323150c04050d1401060b09090a1a06090f090109051807080a080304020111100506040c030509121b010c0305180c1005033409050612130204 67
    0x980c1d4100380700389115652000c3d10f501c4180e21170641409803d0900742450200050340240782400d5071072200211815108070021b103c0e510040178034200050b500c1e080d070000e001d614a03004108042c881e151000329090109041e14000303004204039102940d031342d411400591800c0c100d503400f540260302d080000c200b40c0c0c0c04d584001c0c0194526040100702c078042c2008560307140070601541c0740d81e4100c5449100042c0c0040044c5030810320505213940c210040f0392010b460a90b99110038500c150b140c805001c481e0500c2e1040c1028603c0b03501d0140614600880d0700c550394200d40c8a45903040d60000348a54120010f80640c140d2603050a000740716100d000c00c0010040e140554110079052103800440019410000e001408418083d11001c003115002c481500e4641000300102e0a80341c030b0740c8507900341ca0070301030310032036031110313021048400c0703110f001005107110040e8019500402082207005200400c03140c4540d4130803072a400001301c2000070310200c0e000c0c02140300d50303220709040c00045800800a081c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 723401294 1250 723400044 723400103
    0xb0718030c0303090e040809100e0405040c0f050303040e0f07030b030d0e0418030e040506010e03010c08090607032f070b070c06050703050c07030c05210a0e010903080d1503 76
    0xd80b4a04001d0b210305e0f41e00b0b90b0160980740207001a40400941401d801c0c08103215074041c0301424020000c01241c40454140c540440e0101c3e40f0201c1d07040e080c0100300181d010340002d4070094000310b088c40d0400690350061a009000101c01c0016400020207003031007504140003429001e07050b01c0403602c0ca00c8019100402000c1500d21990601245030b40715042c1140003070303250f6099540c60799200031031020700000740b4014201d581044070070030503110240c4090240c4407030f40c0e4550350340d40058580b60810a00f0004c019040c04100b5003040c45510032044900045910164402103d00000c18a015060b25030320440b8002420580e022040080d165000041d81c4841405402c00b840980c1e221030b01181203c000711780301c915070302040c403031032001c00c1c403480030101050311030021a402071424400f07000d42002c09000c081031405000651400c40d80e0302c90340e4918040420b00f8110103490a50340e5500c0d442c0030b000100c04080742c1d10343c0a4501d50303401c08225802590001010211a02d9020001c1603112104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 723402544 1250 723401294 723401297
    0x180108043905060f0904050402121c1b0b061201021306031a09010e0714040308030406020c0f0c090a0509190c090608030405150a0908061528030b0718030c0303 70
    0xa12001690f820540c04803140302c640480d110340b500034800108001410090010f03a00403805241852030300c0400c11101110200015140d81591000b1400419003003c04480b02d0295080c0d8600400154076a000c464210740e0480f0b40d22482c10041d445a4024001d0144403c0701262100b0001145a01988200e91850000520602ea25000020304c1605502031007075161941580001078615032003040c1d1411030016584029240c207030f490702d0300c8140340c005450681c0e0f51130340010306001401e000c01141108403a008050550343d07a030a0000343c5003003001415140482c0c3c881c40041c41a0805024001844440f55403c0f1052107003410050301180c01c40c024030784214075000d404100c034203000003034a04441c130061518100d440c3c07128400760540c0220303084c001881000385000c14841c805010b640e00c82da440c1010703400000500e40800030501c5541d8645132031280102142075000a004290b41c040d00c1c1c0103044551161264030301100ca07a00308000d540c6048030303d03090100c1000480c5215000f05c0e80203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 723403794 1250 723402544 723402653
    0x7120f1b03110d0b060f041d03030f0f0c04060f0504050d050a05120c0307060b0609131b030b0607121b0312051803183f010218010804 59
    0x241024840c1d40d549520f00505810103400001d202403602e882c208003150b0002e000418905817000781075034612000008003510741c01c0402085058000b0141c001c0d800003500c2c0310245182030a02d498085440386020b25410010781400040d145d07400b0304200c0703004000240c181145182141003d5813140070201d002c03151406007141c008980346894061b03600e0851184003441c904080e27a55098024855030000a8200703030144100e60840c1d40e680d17140d107040c1040000124100040482065002c500d9641c40c40505151155004403600c4070020b9410041c0e1000c03107030f50417454114055540b19454084004502c8050308030f1820141e0001c07040e41554400038045c07103251128185125000028040701016a1090081001c1d009207400003204920000d0130362108017101c0d011801c1c0c0c0382540004809408103075400802800c0d41c121110b00302e0190300000b14103003500301c1c2c2c00c4001920044540c504001c142c03004a020300404002d030f0080c0060b050005609500200651016020414150f0104403072 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 723405044 1250 723403794 723403823
    0x3020d06050f2a1308070b1801080103150b031002190e090702210c030301090c02060901062402010b100906080c0723031b01020408010b0a03020307120f1b03 69
    0x41d2003061210074a00501c142189440101c10f1400ea508420304000d00070070003080010b03400360180400005031240d80005035940340703800700740c4640000e02c100b482d040200d142e00400104e2409001d41039418400d40340820540c034040d0000c0e10340000c601c424941300707200150680240240409041510354182c4911130160090010800c4125049400401503080402d042e00395010b5042c7d006071056110b080d25051030748540469146800036000391000d03a68aa004d001515010000307030798800e030804000c7c4261800d214842074140840c10410450001609007501d50074000c3d00084000b01c00640044500512844014503a0700c6512a2401080351132000c208442a064203d9240e90b40029103410540403190340d28100d111404203281139408103104800c18807550340719605003c21040009078869080c624580d0071121440d0a0b00d1050381c194004000507200400c182040fa41d1a0110300100b021038144003101803040c0074005d100301d04046404510f210980081e5056038000d203489a450034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 723406294 1250 723405044 723405061
    0x5070b0d1503051903021908031b09130e010204090504060f0b01111b0a05090a090606050a030c051905090915010603090f062f220b0a0309020a03020d06050f 69
    0x1c1142c04003810540001c4c0381ca82101409410002d140c80c4684111041c0340303803001e804903440010314000c480303012000042c0141c0805007042c0b80504401e9600b158504049800041c0d00d1a07401d20319500e58136140c200002c144c003001e505950050103c1c2a043c07205192502d000c00040180c0500e05034101c3c5840b41e40c9030254070500c0346010200c0648010481c1905d081c0c040080c0720004200307158054211040498503440322601d05028005810000c211000d0f14600407054840c213800041c01813500f403200304003150701010400103c4034160b5150803407003000a49003807481c002e50815600b10f900d41d4280a0718180000c1d604007641802c6400440d031b80d0701c0712421015500003140c00360100880c1c41c10200410140da01103c03100c0003006400642100c465080302c002c0078545515028144042500110000075001e588404000c01310341444440c00c0c44004012800740400c0c0d0000c1551350400300f006c41d00c8036000400650b40080c0b41c100000160301d4104050718085131501944001d210108880a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 723407544 1250 723406294 723406331
    0x90c11010e0a0803010605070f0f030806120c0a0506030c0d18030e040b0a09020c010e121e04030807140c03010f0e0d0908030a0f030b060a0c020306011a0306060306060705070b0d 78
    0x890b4005401c0d4130316441c140040313400f46c003c1135040c1e40070090380c050100000c0200b9142c0d4581d0344a51140c1c1024a880010080e1031104552500225007020540d20803a03540c0034016070a0740c2e412294036889072200b0026641c14003d441361402443d02d0401803000740d034002100e403903d0601c030780e0f034200c011102e40081c01706a808004075942c00c1400c6c6a0280814031070b0340c02402800890900004846115804030762425000c41c0d01689503800015010b2520f580201008601050f18482c1d03d18003443c40d52090454441d220014019010007a0309011510003408450b00d100c4d0010300900240c0e10341e6a8040080c59480c10b050107034410141ca142d440b5004000c1c0d0b508171034003400a98200040f0f07220544401c2c0440c1280801c06940c0c0c4440c410310340e5030b03201810100b03446031340c2c1c5841510140306242c90548181c000301d480c030904034040780c001c8ea000000c0341e038402019240f050310b0ba00c0b000e011403810301400c500208076006110f8003103580743c172800c007400440344058001d101c8030403600003007080c9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 723408794 1250 723407544 723407563
    0x9060f05152b021509190b0403060f140703060f0503061b0c1207150f0506130c210c0e0303120105310c030506180103060c0507080f280f0f09090c11010e 67
    0x1f002002c0c0001c00118505601100c1400b00441021400c1888141304403000281156100c02080e0740300c4051050020b09000300f8003410302a07000b407403c0e05081a8a1280f90614141c0e552940b0000a0595a40406206840c0c0514440040c0e0b91910343c6454940494400c008010100920708402102d40079564010980951400782c040c032042003e202140e40901003a103090418002a9002c06a40c82e24031030200f0440c00f564500001d06104810004044035941a01c0c1c0b4400e030f005004903510745821420180c1124001c5a5000724546640b0704040072a0407281106201e007042500005150b416400070341c1d0108007640c080140b541e4031f804010902c00c211480e103420441000051002509a0384136a030015040d003000c0d410428150b8034040554800b1880002d0110081126034910400484032400862802c180102034a5203000081c00c118201130520100300780c1d0000c040000340682c1090010b040d503413405000aa4a146010f01400c08543e10100701d50320300159040d80030400b1842524 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 723410044 1250 723408794 723408809
    0x30b130903030608030a03021c02040501053405031b1f0e0c03010603260702060706091502160308010e071e030f09060f05152b02150919 60
    0x1602024854240010a01080300310103066441c3c2000c80c000b0001c1026041030981650003681d51400001c4804040c0181501d600030240103100c10700060381c0040c20341f1243c5024031051520f21030004400040750404089003000c481c0c10784c80d003105111001c4010201c00854540c490101012401910780e5402c5d40c0441070443c0d02002450b1400f520503400000d81c10040004507180c0c200e1204c0002d0031941d550b1700803140f4084005500d0415036456211091098443c2641030405020340c0200d1160303c0380a5000b00b00b0b5540d80b44080c200481031825403004809254110348401c0d8500b2030303074440c1d24008410703404604484000180c501240419510510060340c400010b41242c10302f0215807002040c50005041c0c80b40344251122030781e07100b0415044d01070000801c0242d034621900b002c80340d0162081102456081000e0a88d88901104000403101031103007100c0b0301c06241104201030f1b6141c01c0290311071209400c624050b44083e025102200c42155aa03500d50400081014110014890f000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 723411294 1250 723410044 723410059
    0x302121b0a030b0d0506090607120504030c110301021201080f120712030b0d080a090f051e06032701020d050c0a0e01230c07151b0f020f0a080c040c030b 67
    0x941d65110703420043e94100082c0c0a1a401010755490504056085804142c40d40c04002084122640008000030411610008100310305064800620540000e00d0241c1400b00122218140e40c8003503049070350039001010180c01d29611400700d01e0710346441c226245100d11a8144040251310100101d60ae41c44d0301032071440c600074101d1815406808100f400b07a40c40180fa0040a021070403101c0100046038603aa58003d01e1800c20841010341c001d6078000a000740c01d400c000d203104648440308586c10040481c2e48a0b100c1c0d589141d03034607000e80c400b0104440310484414081803400f0540107000042e603402418080e5603581c91405040e03005020888002681b00c01131a940380d402960000040ca49850310311044203008814102c56a0151082f000142e01070842044a500401c0707030824004218945036035080000c40c80c54080905680c005060002800c103600c0c115600c0c100700c000b020070064246814195a01c10054480640c141d403030340030f00d040a9498038842d1080c841d000c00c5040080826 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 723412544 1250 723411294 723411307
    0x170106050a2c06030304050d06060f0b040b0d05091204030309050918060a05130b04140607090b040603021c050f100806040f03111e030901121103060d050c0604060302121b 75
    0x142c902c1500a02200e0701400104004a150b88a0b075081c80c03140f600800c00803a9040c9402c0c4500346401441c0d01c5688150420700051001b01194030444140c04080c20010503651116403480782044101d0792160740c03130381d40000d0010400d0b401200301d90845008840d04451651000131810381c18035044500f8419820441c00201c81140c0d0783c0c042c98104142c40201c03d54400c1340c0e515100034042c03e0b602941c8400e1410158940076400f00003850344494980381c00c652070351800030070001d10b0103640911814981c0105040b00031340c0b0401c1d1411484807140b2030620141c10813601c0c01c000301205460b031140c1c0c843d01d420003146e11440010403c0c01035a02c140e00c5141029584c0302181c0d88150b607003145c07002e805008103000400070300004901e1507070082c5020719a20133400d0005400c828a103c6960040d904080ca8841021040c3e01038a9200d00183c0b1850f08964541c0341c42e5003000120201d040d03024a022070081a0298140e000d0848101c0906c24a54191904114110304071403480f821040d82c1801c2050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 723413794 1250 723412544 723412619
    0xc08030d0f0e032113021c020f030c060d0b1302030a05090d02010c0206070804060207120503010501023a1116030c0602011b0e0307090501120506070f051909170106050a 74
    0x7813951240c2000059501d03048144d00040c010518024440310482d0320100381400e600d014034120040c04406c400030b1104814450204078540079200c0c16480040d580e40c0034040c2e507112a0304014001409c6e0304115035a141001080d001440250303500741c45031140718060003089005100f44071600754960010180396444250880f61528002c0084411035000d1000c48001200d5080d0050701095070b4807a140ca0b0f42c18040028500884200e1404440000d1130100150b04464100080201c10180f03200c1d00105d10b030701d4207071290340304244010181d1003a84403a0a54007101c01542c400c1d41d21030b44080d288213a0381c0304101d00303a0768004041c1204040d802d00a0242c5406050620740d1620040d0665154035a186000c004441e4240e0091014000c0c10048004001060002c203a100c002030900488800d00100010064021000002e48100b10341660032080b03800703007000800a02c00300b508080012440300c03e05028107001c1c81001d0103600a4500420865a121141005000c82d212602021440441c9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 723415044 1250 723413794 723413857
    0x3190b22020d0f1401080105071805040228020c10053606070804030c120302100c020307061802030706020d020c1302040506460c0c08030d0f0e03 64
    0x9404020b40d582d248804032602140140c0843e900340400d0380407a985481c05490a50354000e103000100040c2c00b5040f00c040401821400541d00b0031b030b500507250b0f09002d0106000340035080135042c038002c0c440000e812003507002039804c50215040e41e0b00b8500c0e41d400c40d0152014000c0d045102e00324041182c250030110034180582901c1d2088084100e90306c0744290100e80e01381c1c40001c05030303142c4900040030710a0102d00d0280b0b10040445403c002c0c08100310f40c03402900d81c51150711217084580c8036428040080d108000360340a0f19002001041941045800207800383c4c60300101300c0c000e0081210011b03015002065883e01071105070050458009448104881031500b0101404072990902001c501c1743c44440c06009040c100c90b4454444600101266038180006485134400d03140d001030020101c4521700c4c1901e400045801c0c103c8104c040d900d000d044918081d0800c000751700c00840d280c21200584c1d00404c00f50403200da0708100800009071519100e215811142090704520142060203180001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 723416294 1250 723415044 723415057
    0x20d021e041e0608070b070b0a0204030507173f0403140a140c0112020d0b10120606021605010818030a0507140c0a14120303190b2202 59
    0x526002003890000181140d80703003031032118031603001c840ca040700b58050312070a00940b40745001042664034040c6d00b171301588203c04c00107015041540c0464000302c500d8041e07401465000090b503803260340395200e404505d40d0600030200700e803280b2092010884403455102080d85500042d0740200c14006814544a8a400a1184011004100000125071003280f007841480b11b09018001c101c0c0340c4d00340451900d5180d80b1201c1c19402586129059a8104189116100c00713450f003d40c40785803601c1c14400400803c01280c3d0000c00003400040d20580c0090350120003d13070b0000c20080b05848a50481e0780b071103904ca40028503001c2007001d02140d030140102540c80320024400c03401c0281d01d001c403d4216080340002101041d004900641041a4400c00d4029021200300800c0d01c040d40600080b400a5240305090584045409503117094880440c5510044a00401c583d980e05180030202455800f90008403400b502c0c0110f4000a0314241c08880e004210289143d00000f04a2540d0710081d070150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 723417544 1250 723416294 723416329
    0x90f060c0d1416050705030d0212160303060305011a090c090109050f0a0503160807060e010e0112021e190804030f050307170c120105010e130e01020d0203100f0503030304020d02 78
    0x5001c4680140d1010303c0d8944564803070710203000030b80d2416042c5451b01075002c00a0003035404c040120100340210308292040d113803a440b0348034105c60503801d00340c00428003134102900039400d01c2d0b0710f08800d502e041d202c0b00d543c20307083e82c2c03510541c0e40b1480c0e00c0390300b4020340d100180007404441c030030012403400e0300310303500f419030f00601e422091580c51000074a004030300740d40e4075800e1101c02d4040180743e1303061001a00030200342c1080d002198822000804142d6044001818088000c004042030303520b640c1a10400b9000d40c0010b5041444802c90130656000352041d101c021801c4203d84021a1081c070049002d20340c561910b0101c202011001d440130742004010078104800046890504036000540030300508080c120503650700f104119018691805070000d9050000c40007070290705403111100001028000d074400240150078282079400384c854411803c6100d8004014803c0c0407040101c8102160018103101d4a8940d0b03610505849000480b40030354052a904107580240c2044e082206125500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 723418794 1250 723417544 723417547
    0x110703060b150a0207060e03030a091502070b0f07051608060c25080c010f050c1b0705040c0f120c1409060d090303020901020c09040f081b0a0305090f060c0d14 70
    0x40b203072009540c0107400310307000680c01034804005094101e5450030a400c0c0c103402640c6031000c0d0500260148186200346025819101c10312403100e40709108220190950720321031556034900c941d2941c10b94200e000151a00d02030f41546038800c9400110b00400c40d690000a0300140d9500d040341c84d00c1da00020304040a101c0c51082528100003031000503402e041c81069400c0c0c94030105045103003116040c80807810190720304400e101150300c0f14820f0380d000b060701d8241900008442291030b41010041d52140e130304035007410518150940c0040030419401c809030b880c0c00b411380e0303000003200c295010585904081484c0e0b00c5885041c1c07001e04020402080c3c0500b01a14107114801041c080b5110f0003c2500081c1d40401c007242e170703581d06001c402c80708101203c40d24200d05264913100358605000400400304100002c04481420701003a903080b01086103400e03554006802c0c00c0140242c0d11504205221340d18140707401d201494407138291341e0311120080081c80448001c150945504081c0c40405840010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 723420044 1250 723418794 723418819
    0xb190f0c1208070306080102070c090509010e060907090e061603181b0f0b041d040c030f0c031a1e090118111c031d0a051201050f07110703060b 63
    0x4004001003142103a964900c2c04914000000504941168010b8180e0b82d0040100c4400300b511034808030240d80210303000194a4071141c504a0040c800401440124002d100421069500c04201c85040b40d040034001d000c4900706401140d240c85085030703040d00c81d880026014804910a5004400c1c0007100160078158881c603499004440380203110500c1480034962050000310562080c08008045a0000d9420a41440c00e502c1c10340e400740d01c154162349410b03c0000c0c04e200175040407100564004140411140c1c60f4140b9040d03035603017400150303030243c47c5100582e50351754221013107445000c0314902c01d006000d0306030707081d00103503000b400d03c10040d0340310040404000c1140e242c02e5845445008640003074035600c014481d5110700c20f14010111220501c0220129811110b6203c10b100f42e0300b4000407101044000400c50545904070701d8001c005408500c0c0903450540c011401409682c4e803036a2150b58200d0221b034906c0a00c1003501c601e80001780c08000150491f0400341800900500100d07001d070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 723421294 1250 723420044 723420053
    0x14030604061701020d060f050f06090303040506070b0907120c121a0106020f0c030a0c0b0318010227090c0a1d0d080702010f0507050c0d1a0f100b190f0c 67
    0x160031032400142da0b580014815018121481040000d14100b600740205a25010010b1006884496094000c140001c1c02008a0750240200c2d806450300508490b140c600c40c0c00e2510880404544412040c03140003008036600d400e0f40e11800615501210400469040074000c240c45e2a00d8401100c8a82c2652a416400c548180605003c0e00c210740c02002030301443c007100c40c50309403942c140501035003020020382c000c1404651040c0c2528600290b96607661951224400948140341c0c0b00c0a55510204209a0044030950405012150070360710000c0b0082c02c01c10840000c00a0340c01c486032000401c05065507078000c0e10400d00441602d54080c5040034001e01090011020340740480e1100390002d0302504542c0c00000941200203980f0f49107007006035030303a52155035130f5481c55400d1103101503110003c20003550740313a41c420190074040704111034240740310941910481a1030b00d0300035615410020810b000c03160107865910511801e0300c00c11160080c070540314805111009002c008624101c1000306 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 723422544 1250 723421294 723421319
    0x30221060906090115080c060f0f04030b0105040608030a120b030705030319080705070c030f0c030f0f0212010e030403062003010f0e0105100f1215270506011403060406 74
    0x100310072005840c02e450014a00c600319a1140d43d16074603003a9010060082213000207143c407203a00140d9416980301c01100f0084010701480054000580d00028080108400000c0d62812214156410b012181d141ea09141d168054907020360000b6a802c0c2100c07842c86502d4118050031403019041d02d25032912840030034155480402c2145601c001c25401d0f403515039000c0106940705203180350082c206891640c4100503110035200282041c00c6003c086010321541c0109540110751120a01c811200d0030300e060b140640e41500264402c12629024851030030043c0102c2404809542c0654549070447e6152002455004044c0b0f066000d42000a5582041c8400031406414001d4000380c10034601604102100416048030703020300070b6500c08254650f000300e038002010000d424004241905a81560001c022140181061101c45180060340303c0c20100c00c0c4251405240301031140c0c001c0307811703104203564090707e00500248c0446007820301d04140070003460704118001c1020071b60907a40c036104203031f2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 723423794 1250 723422544 723422551
    0xa0906020c070914010602010b091315020d091401330b030403080411030c060703050a0e0418050c04020306031c031401061e08100501030905031612120e0703022106 72
    0x106564050651950300004113290060516100a006039844680401d80700840a01480301c81488011040f041016114160405240303d14003152181d81104001c8094858807000ba10012f00240360740c0b42044060080c4140c0d24030351501d8405540408403003400188052003182c80260404401240c015070010065000f140240d075180002c0c00c0904208444201c0040c019200381c0c040d1100401603158441502c03041501401e10b941c036002015016200d03540388030741080d400b51401c00710482442e04071156000042c000d20460b001108958148022440300741c071001ea03d036002580303c003442603164210003403d100b545004554008004400c813130b140710a820204c00302d000c3c0f2680c1280350600402503034000d180b038545112a810700d00120006500103002d80742c10903454080140502500304100c1d1090146504490302e100b4480c180712115900964002e40002ea604610041c03d00840c00f545000c810350a002d009017524550801c4440341e00b031556013f0002411080c103080050a000d968031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 723425044 1250 723423794 723423809
    0x313090b0307061d01260721060b0f1608070b16020a0c031103070b03160807050406080105090a0e0102030406051506040305210c191209030b0a0906020c07 68
    0x340150310000301401c20650f50801010030450110250303c082c0700000160b240b2500782004101c180586901014220140d4411070b991458403007803080c6030b90b11500c13500d0354075403000180685900320f005103002d45130311388140000c1a00911242000f20300e9400180300c04000f0f0402c1d0b200c0b000c036039500e18610380c000c00c0c3c0c20340340c55548800300581c1c1c044862600c1101c01c1c0902c0600321035501a0307104a180c039901e02002e0020b080b030b02c00b0224161801c00008001d041d42d00000b944a2030700c00c411104148074012100c0000384e6440100d894240560305803001d889064a800100f03a00305020300c19406001400000440d0703c0c2e5407001e804801c01e00c020760099010707030030210781f07490a0a060440c100140c03450601480c07042104101041011800c4190380084a43c0d81000f13000079803110000d40100c40211034140203110f060b0301142000c10300750103070301c0c1305095541003001c041409455032807042c8000303007003501701c0c000103143c505061780542a418819140181040840d002407860b0000903081140c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 723426294 1250 723425044 723425051
    0x1031e330503060c04270b130b10020c0a0b2b0504021e10080c07060e060405100c1e092111040209060906070c030209150111010b061902031309 63
    0xd070600f404403a502400345050286410714042003c260420295961b403080761a8641c9642821900d401a44038600001d1060508030711268a00c1d00411814228520540440d100c00080c0c90001c00c152200d56030080c03002e070155140500c01d01c4941e20002c000440c501e0340109481d9103400d9400c1d11440000078403000516440c151050020480b05500c500d00d0141084690032f0065640c101100007440c0e50b0b24080881c0c1d11441c3e4105c0550181440c000c02c25410314070440540c00000440520950080c0700300c4440038001d00d04242120201c0c62218000303031481c15101c02e01c03400c1f090440e440a02604d0b041c05c001d95161142806112000c161072000302c40c84d9000801d0008035508800003c1045904520b8105000d00007800362084003100c50050901080c0d072001d100c1e81c0c0c0300c808019078002c0c00900c02450300090445011a0900d46240803a40480e402500110144150595403102801d501c1c40c3c4410041c0425590217021801011440b0070029030b0740c0807410050640051207000e2010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 723427544 1250 723426294 723426299
    0x4050a170408060601111b030a0605040b040c0b0306010e122518060819022e170405060402061c0f0219050c03030403030906090b0411090601031e33 65
    0x2503041010213001541006031801240c02c07003003c040f0316524440d101042c2c0d21000c100110119090201505001d032070300d4a4842080140080ca00ca80ca105500c1a902c03100410f46940c00c20b01e060205550f000d0000e0000c00010b012820701d42d00340507a21140304104d818007900903800a4900103400300780c030300c0c0d6040d01c041004103840f0084401002d20402c40c0c240400c0d4208407000d507960904040c401420010f65141d0001d540b0740310780d000700e1850708901501840001c2c10008041c6403496048400250b0a005a0392035100403590717680c003030303a4001c0280c80c4680311602000940d070002600c5840784c9071152001d02c1c01202603c1400d110300094100541c440815240103038807542280605018171004002e0707104441c1002c01101e5200740c0c103040004444016090407002001c0c2c1e1300004051100250a1105120752021500c400060455511074180e58590044090702c048083d4001e5040083d4101800c4408580040400c00c0c40400c20160b00a8a903441010110000c54031790540000300009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 723428794 1250 723427544 723427559
    0xb090409210801060c0b0a050720010501140a080303060906041107032703030512090c0d0503030612070501090b0c1915060605280e0a0906050f030a030206060904050a1704 75
    0x10b00740144494184101c1c003011607228214109001890794100c1640c9a000401c2603000e00c0d440b988a01030b0030030820400c074000d40d10307a009280038007403022191841c00f032071441d0303180c29403412043d141d03d4005035040d41c940a090003100031002c1e102d00d80c840c1c1c4401303034500c140c038500001d0581703180207545045d5010007540030865105200b400007041d108102006001007a0403c00b00d0b106a90200c0301a8402d030f4481305954109810035400030340c082c010340c6044091110000166014030b8088400d2030002c42404441903179241c0034400d0038041035006030308204018100015101001415081d2244000e03515200c0c0c400b51100c007021950280311b5419440c036241c1c18802d040142030981401032500414601020302c104036000c1c08504001c4a107010240e9a110703000303c81000801030080515a40c07a64540000b0300b006024041c0625a0041142501d180016038602e000360150041c2000d9101c65003070110720b100041003510a48100d1107103030000741038030151085208003906426200c070b082910 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 723430044 1250 723428794 723428807
    0x204140c0d052a18130c03051f1502030f040b0405120c010906031a090108150c03151201020c01060e0108010b040510030201030b120d08071209170a17040f021512010b09040921 77
    0x54210341416070649c1d018102c8501c0f55501a10101c9150038503503070480c48124071310f115002d0344200c0c540d00490001210032104000d0404d4402c100c41c0380d2940703440070b00d0080d541e001a030a03241c00980c4403101000501d02030f0340310844491213940403100300da0151010407005c41c1c080c0d000180303541c04035a2001042c840c4122658205805138082491b50a200c0c2c0601e0071200400408e500c0346c0c2c0e4050a002200e94254110340d0000c90310002404110b139038141c460340c118401d1050035095420216404c44602e0103114a40c410b91292100f483c0850968004400800e103000d030403500860b062082d805503920811406180780d00c140e4600c03d80d4070b042c0c180241100c0d070006142100c1790406c485007001030303c7c000341c041907030086401c281d89890b000075044540a0703911a00d8140d060043c010b01c0140540d150014505600995844000e01c05085060071640f142c0c0c8201c4e8020105540180406940c01d002052107034002000456a80c0d240e80782c5c2071045064135000030480c8072001031009100d41151 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 723431294 1250 723430044 723430051
    0x40203070609080c040f0f0905060412050a0816090503060a09060b090c030a2a09080714012a1a0613050c090d0204140c0d052a18130c0305 61
    0x2800c50805441d10f1800d96490f684149100c0c41952610001882850503030312508074003000400c2444103000703e00704243c40b420162800d4074840b040103241107049010324210b07294a6091b9903850016920280c4070303030802907803c00010410403442c000041c00d6504001960003070150000006041103945050000c03141c0004002340200b0308003080000082c04131007aa0707031155000001048510440924400d070045c00301e444005045000c91443d443d0b50b101342000113803420007049408482d00d4642e0310840020b43c000c0c1c42d0000d03188070540200c88500d440c950042448900c00004103500340d94900c1c444c05001100c2810302c540e420b0400005240400c80b001d40c081d03000ca42007049041062411200d4071840c0001d83c01400700c0c4400340110740781c0380d002e03c903c148032140400490a1000c1002c4040e485020540e00090801c070204110f40c09007042147e240d1049000f200d0b08000802402d03041e80c010201d8a0508070050030901e000c5d8903898815442100341810000b1140d0120300090120b81025 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 723432544 1250 723431294 723431297
    0x411031c1806050301060302090a030605090a03020f07150f110105010e1608010605090d0f05030f071b05060706090302010219020c0112050402090c0304050a080c1c0c0b0118060314060402030706 85
    0x1407008100080c0c0143c1242e041d2015840c016030303203951000c08110070b4078441c0c0c0020070745850042000324000c404148491900c1c426400d481c00b200c13040e24aa59074180e6130140d0160384906010300310b42c1c40d00901e500121a8428103100410078618a1142e0841e80b00342d2011204920b464200405020040210700c25010342d420303e11029410a074000340380b401008060340c002c010b12550300c403d001e2a03030066445d0365840011a560b8010240b4900e203d07402500c4211500904103c5400c0b81c6007244a8010507201c1c090042400c01c1d400f0744a0b94064030100400b581555130030481d031802070046001c0410b08541c0e03a0010103094003ea000101001c580d5680c01216a1400c07092000582d00c204096411a88160a0030b0700e80c3c030b81e800c4c00745c03c160b4640c0006141ea900040d03101c00009000c0b80320710840a00c1103000900140980f0b043d85c01d0852068000c0070b031003408005200501e10082c51181c0024607400000f40180c17030740d0b20118800d0890301c1000080e40018100700440c40c0421001c2d0190459 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 723433794 1250 723432544 723432587
    0x170a0603030f17011a0903101409030f0703050d06050d0b0105011d0303181c1a0f071e1808010207060b060a12020f070c090902031c05040e0411031c 65
    0x83c54160b00e501030040c05043c103002c84120100702c108540005862a00400505844400300920500c80082060308010a4100a44400116103140200c262521340100c030046502d0140030b964100c07501d6000d61180c1c64a140d42d071a010500761507100d8555a12881440b68003881e5061100240050007004c04031081204900c81420581e00d000c13054a45030400e01d40b4076615400550300040d80560418128445800c03810815010f002842c1c02c80344012104100c11122600d4180d1480541c450841c0d421010400800300100b481d0f020035880c3d600c0c3c0d800303842c0c80f09142149421100c4074882c243d0000b030a580d0003246803410b0000c9071107014081c000850302c00340303131010624000d030184907d40d90007060141e0104a00c40c0300d0003c981220180b5a000b90f01030344203900c0d00e03c248010f0400d004268041d120b000741283c2d580c0c501c40d010028000e01d07503e40b20b08141c03401d41c0f844a5034400030011648001064090001da45042050200010f5580b400700550881c2100c0100103684070782e6041100b0a0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 723435044 1250 723433794 723433817
    0x2523041104060e06072306041a060a170c030106060203212811070c031a010e01140102031908070206070206070930060c1418090601170a0603030f 64
    0x30003c00c91912528240c0721140c44281500f88101021018520750a04009180e04440c00000100f50a885284a5100c1c1444c1101108903a0340d0408200c4045400c210011800e0200340e0903140d14403038902e440d008841c0540e8107480481e09552a5501042c00369001144003120002400401030980308600301041c66460203640310018080384000c10211200c030046142e1aa41c21604003090081e58a900c4a5a0b81e480f40361001c490425844180c07080c0785900300d145440c2114040d060b04840c0500c5803a442079003086883c041c041c1c90b06041506600c001c218510b02d02c513410b012404500342d0ba40f01d1001600d03002d2070103400c2220084c5440119005a000c06c8180f54008040c1001c3d41c16081a65162380001c0307500c0e003094030340f50b56290201c02c00e0000700c0c4c0030084e6581100540c0303800350741e03610480d00e020280551240607c08115501c0c61109410944900b0500c104551044051416018040051440403e030480030340e41d214400381c07203644c1482419004142d09000704400d1038680c12030311 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 723436294 1250 723435044 723435047
    0x2190b0924040e0606070f0503040501080702010c0804330212060607050a06230f090c010903051515090c070507120b0402190b0f19030905252304110406 67
    0x440c030b014a144440000d00458550f0304c17800140c0b8100e03a80a1303450003410310542410359a84c0c0003807048600083c081000078813418418080e03801c1d035a00035120031145880360740c0c4180e2081c0d865600d0907480240c8a11031248010320302140f140d01366000c10010f0b81c998811030315072a01a0000c03d004c0c041d5008011040000350005555a0050f80011001404580f1000e1103140b200455070f40102e0303c0d40b49002c1c0701400415071089401100c0480c00c40b4036240f40d038801556503040c544005001500102801606100b21000465000c034001840c4125140480e0002c3c54180080e12a1083d820380440c1c61300070800c003007140741c002d05407500000101c0728190b92511201500244028060052130f841405003414081c80c8501800300180d400740c442c40c010b01152001d03003014009200c102c082d0703404101018020700c80c5d00e114580100c00f81036107107281850030301d05104080166080061418001940c0c0034245881c60880b80154440204d5070070766000c210564241c800084080f0303908010810099 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 723437544 1250 723436294 723436297
    0xf052a120f03070c050118060c120e101104050307031b060320090a0302130b04051b040b2206030c0201051e060f0102011b1809050f06010c02190b0924 66
    0x10400d4508113900c09600d260032400741940114000305206030708000310030001150001c1101d06101d944410503196821100010341d00307081c01040450300b10416170000d0000903045401c071016000c154501d0305030b685021078900001035200741ea10200e1703021552120390b40c1c11a500014081403605002030090480348250a141035000d0361400a00011011400d0700d420300c1200c01035400600e01300c21407100f1042d903800f070b00d0508542d031310640c605400506000720740540ea042811101c0d405a05003410f20707030040025840b485c101904104800f00011108075542ca49401401d0ba594010a1203141c80401900b501c1024101c5544040c5410440783d800c9001e44490b13602000482c1d6200b1190702d00030051303004059800d40041201c1c43d4002d40700c0090f4120800907082084003c00f8440329a40e400b210040354002c0d51180e803100031580106406602c0354000e0314010380000d0002d0b400340d08442207886490503507404203540203804101006136140010b140102070030580c41d2103000455596610045 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 723438794 1250 723437544 723437551
    0x9070e060d0f151d0102030c030a020a090b030408040320030d08070c08030405060108120315090402062809060c0b0a090c050316141008070f052a120f03 67
    0x10030180541d401884585003441060903008a207803080303112030a8040c0042c0800850720800182d41d03200021240005200b128800c4a00610310750458680c0143c490203544191385c04000c108001001260541c404001180150b02c9010120342d501d1543c540074400301d05a07030b800c11000c41d241c0d02c1c80c0b880b61004603c4000c1010645400d030307955034400c1c1c1c007514110f8407000090030150002c01044100400010340c6e6040e10404c0003100d44a0001e030f078600781d041c80101c4000400c020010159016800d0440455070441e10003480a803c000c54641e0003ca40f0f2400c0590140d0100c180d0303000100c86030410030841c051300c082e152603400d210460304c50102c484405450400c0c1c086d40c07841c1e40c506204c0d09480c01c0001c0d01005003929a4800c00c034a8040743d43c10f050203402150942c9105052152814a0307210030b0321007003600c0d6a11242d65552098802488400181c0c05018041040545450030f0b50814680c1c1c0380c40070502d540030200702d2189481c003180c017038210780140020040b01001c00801c005a1b84c0c03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 723440044 1250 723438794 723438799
    0x8070201140408030403110f03190b0421020606010e091308030a0603021f0905011b0b0601030f0e0703050f2b020a02030610051c08030714120108031209070e06 70
    0x5025030722101040c9244140e40c00040309000100d0080701300111010003d0200310125104900b420011041540343e030310405031000d10206d00d040d0100010144201c1c568018020441819401c001f8031403030a10416036040400140c20420800156680200081100d46810b6440300040e2400280141c07611006440c00741a070a0088006183c925654020901031a40506500c1e444c9001004000e0305200111010020911213000440c0651068803905050840980c5141d42c1e8041c42c0c940c1c01d480380010708824105501d8020100d8024407500501400d0300d081001000c1c4186903050081c208002000642c3c51600079981d46043c3c95941c01c0703820b014408001140c07403903a200b03103810f03071814170a608000d42501400b0208507100100c3c01c507c1045640a030b85844007079010740381a14402d01c005600400c1c500b001d00c08a03010622440c2c00383c03d0038194244080c0f074241803220800015030300340e0042000d50b0002481002c140616866240c014a603174000388691400c0071102002044000d15050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 723441294 1250 723440044 723440057
    0x2070503100603150c0f2d080f0711030409020a031d102a1407050d1805060a080a1505060301030b0412050a0207051504090f09031116140301023a050408070201 70
    0x1449047c1481c1e0891043e00c07400114111035410413030281112000301c1d42c442c05010b03058001352250740110300c07000750005140040e5251034144a8004002d402c12030041c030416a9494a480700201c1c1d08500c41c602401120060000110803450710066806940c0385128240b5000311214050040903980c103403421182c00c1c8504050b00c500d041c11080e020700c2101421503c10788070300100f40386c3c20048a1600c0200c0300100d0300095164003c1c01402e103e030000e00d00002e001200000c000108035445920860b801c1c4241c500317129540d00c0010149c0d0820381090740d088090034217100c1004400b075501c101650181c14424240402c52002949a054500c649405004e110284c1e40350400c1c2001164003030b01038200c08000c081040c0b003561008026107141200440e12007003060507602c1e03001654540d14002081e1140125041000740d084088442002c035415640030f0041e0108201c94560f8039650b68004000008924030304501900305800c01c00c40442828039000c00d00001c91806000c440e1070540a08103003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 723442544 1250 723441294 723441317
    0x909050a09080f090301050714121b0c0f0c041e02030c090d11181504020c1204030b07090b030c1b1005130b0a02090904030f02070503100603150c0f 65
    0x360007400c28100000d18045001501e0f110045104001d4014944d00354001c200035030b00c024081e03c1d00c40d4000e806180c80300081c44410403000c844541c086d4814006440d0796030140c0024803006080e002204040c0c61900316000341a25103004100304044040110f0303042c40808030700504c225070b0b4a81c0d49007500e04240c000000554070345050088070220721028107d03980300004e608024480c12030051940e403280b00b00c514400101e03030144070494000e000d1000300001106290003044000cad4450b0300e08a40394010b0340c020b0362540c0c9004010380002c502540441c0b80e1490700c01c4e802012503007030740c01c034031030840c0140144566481407100313076201060425849890200e41d045924505060440038a1903242070000f009402d00e50b001c0818606031140ca00c8190f503486c0c903500311059010300d011064000c007240000a02003031081d003031034140030140e00641e21002d44440120f81400b102d0b90b1b05104c0c05884040c10020009400460300d100707034091004000000608200a00d6011700394014800c000715080d84 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 723443794 1250 723442544 723442561
    0x506031b030c0307031a1011160311030d0302040b040302010f051603030b03010c03200918090109020f0f0a031b091d1e120304030512040c050f010906090905 69
    0x350811115422955100e181642d0100055402100c007000043e0500d6035401c03500c0035000e11007180300b10081c4030105150700c809044640c4030700392a062449114001405a103603103e58900005140100075445404001d40700b41031600200b2004401007610401080181d603450f031060340c096039424030f891041820444000c64546c0284080c2240d8640c3c036220200030940c05030301c0403181d110260300901801d90511401e80c101d80300c41031000d1140c42c9081c400c44100e50072034000c1280802c001d0400c2018404002e0080d41d06404544880150795500c0105c819443c000410490744001182c02508800e4150f02003200c68a03144002405008800798050304412032500e0140507102d24a01003100d4440074448080e00002142c40e0030b504d0103525080800101041484a00703590b01c0801014850040c031512030075548003c20540c10003100340001c55100140c02038040c0194041c10349103103114102000c006040d41ca1104c92410322103507400c2005450b030420302107030448041850014490340c8070301c00b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 723445044 1250 723443794 723443821
    0x18180203030c0f0d050c060112060912020d080a111206040605120304030219230f0901080c13050702210906070b0a06080d0507020603040c080610210c050603 69
    0x303505000102e0b00d0401c00400142981d0b00d4060681140c415a0480c0c1c000d4907944545020103a040d0803403c01480045207200c00310140b1849144005202c841a4a845d81c803131028032500c00c010b811440e020041c01d279008003011f4100004175000c0280f4280704244c445d00c0c0c81015014040c403180c9000144155032141d012000900c0d02412100e80b54240c1807186840e5032150004034429028480070102e000c40c080007850a0b41c82e1180200132410360003840265242031003008550010000130300403030685520071880e00901c141d00040143c80840c0b41081182c400f11017105840c285031108200d0741550024030182c115010010f6226400d240c0d000b01684c034414a0112900100c001a05804203c0180e8840b4401d0200c1c00c400c20413961a480b0b007540311090040e1020015106008403405407800f8001140c20500c2850700007007540c1d55001240c10010210b030074001001c040700d001c102da2440703d050281d001e000380013542e001c02400c0d40c0745041d40c0d18034010307503029120100011b010100c1e440ca = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 723446294 1250 723445044 723445091
    0x8070c02010c0c031b05150f0301050d0611191205040203060c0a0201090515071202090105070b1807030b071701030b070c0305040e010b09040c0f0e040b01030b090c19020718 76
    0x224035403a580d1005c07070300c507080c0b03600c0c031415004601c580c2009004820307420545003107881c103152103895030b46807034200800460080001e65a5942d5500b020390380c080c640b0001c05e00b0b000f0148040750034050100025051b884040e03400ac5070301381070004006c010fa9010500b280c0c0014643d803256251181c0d001d0803401444905401011407003840700041c508180f004d00184a00d203039079140341030b440c0c00904841c02e034000c0c803017800e010800500241c0002004c41c405541d11103201100500c40f00160491249000140d0b0302c1510340f02e01c42c03001e0008180e0f115030320401c0000035004d00403265140d6a6007960f0440e00820400400c14404c0d55842058403d40490380101481b1084484558491a01002a9102080c0507101b00c0c5415442d03803000d401034007502c1442c42c041d10b03208912001d10040c40007604006164604145c0e840c20b0012150340d541c103507180102e404108494480d1003070050030131084a0b07481481e0075903011800c100130706001807403522003903500f810011454541e04402c03203c0c1001d258 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 723447544 1250 723446294 723446303
    0x2100512010306140106020a050c0907030207021e0f0a0303170601110f0724020a020f0f030d0302030f07020c091306090c03081c021801210221010608070c02010c0c03 73
    0x10000418081c6903082a49910f0394540454503603643c80400340e80c1e4002c23404c0003e00b0383d00100b100103d20b141035071a590b40b1488a040140c03802d11160300180d82030406194840d82e444081d41120854144855032440001080d00c50042850451724060007007402e20b05000d04840200002072216441010b0020000182d04211860b8001d5524041e4448a0b0390241036800c1000080b4000c044801030340e04c0d600496150003074100c10919409001c01c1095880b500f582003030fa1424004090f4508200503540059199401a200e06040052100a02c0042c0007002154449240211569150400d003504074813501d4200c545200f240c501203014001180e400781c0009484000002400318032030040c801d811103a8080f103030a14403403010200f2030060b0510010340785c0c0b80c121160310350b50080c0507964402e00f80041000d401072450000c0c10999200b02c410110140074480403a40221221345134a014203030f1401c10000501d41201c000b400c91880a1020341001103505003503040c0107000d4400c002940c1c20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 723448794 1250 723447544 723447577
    0x906121e090604030311041a0a020109050303010609061808190606090903031d0703050c011d0306040c051215040b0c190305010501110303041a06150a09091413021005 73
    0x21a034450311010202d80136070110342001600307440d1103100300c01c0f80c040d41d150880a841e051946159048150070410840040d907580e5130000300412402c101440c02014941e40b000c41613130038070800420841040b100c0e0390b9405003e00700ce200910000c0303074180092400c004101142c101c0350601101415240d40b0010181d881e190083e410b15034560030580450b00198030116125500d94441075842d400781c840940309801c5070645c00c005620841190641c3d09800c0070284910141c80c001130308040c010380f002c44983e03100d203800700420b04211554501c1c5081800180c10501000c0401180ca4000200014100480c0340001810700d41000251011000304400310742c0603410a120180040500f030107450f010425042410b44c06940001c203d920842d8003085641042a580c80505400d80010349a147e0003c4060070072406820040e000c1e004840740b658a4161880ca030541a00445d02401c029030104c001c46000c01c501d81c10201030540c04158144c41c0c00b200000c540104840030b0041c1031030210924079 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 723450044 1250 723448794 723448801
    0x705150301051014180a080d021b060702044101060c150c120f0c0e0d020102190501050f0601112e06170d05030609130812010b0a080c0906121e 63
    0x6400461a40342a107980c1191511805c64950308c8810140000040e030010150300040031501c07200c45250000609150300b081003d82c00542602c50300301c01d070802d008240c1d180e07c05091b80f181314142c2c0d0350700400c2c0c1c2c050300840e10481a0842d050500078001841040281c0c1030400040040c0d404040304900380410016054202c0203241042c04940092900c2c2401800c5103481c1183c4601c007240d02d116254084401111014040c0085400304168194058010b05408170701c040ca450f4003801c0d10860002800c0d2402e044d080c0900710000d8800c03810068110780c1c40c0c0c1a00000900c203540720040c1c20650401d806107140b940000c4403440401c03d2103900300750f80040d00c6014104a0151809020180c401a5100000407100b5010444420341e0000e500008680c0c012584411070072801c4c0941007151800d0300c60362050304884c2081c1d00070f0745103c4000406e000c800d6840900781c0d4024183c026043d1420405100080d01c60045414420744020440017040c004160700002c0020700b54030694810041c40e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 723451294 1250 723450044 723450067
    0xf08040e0f04060f02030c0a110316050f16050d0303020c012c010e0d0c17210405010e070f231807080a020705120921060106020705150301051014 64
    0x1c01078600310750703150500081200604840c02a00e1203614200002400c110300e5580445d05422100780c1c01503180020001d2001c99424165860384050045005100350542c800045140c1418401c1a0b20080d10400c1c00703200c1035807100b182c0700324075402d490056112410806030900510010f030507844036810f03440480c140c00790a4440c417a00902e080e4000c000e020082150070b92140c0c0001c00b480c00090f03034442e192000800dc0c500d80d00351030440f94011424190681d5001c0000d003416100d40960682800400081000c24081d140030344440300080c00035217240480e0302600c28024041c1e4909508040300e100c038a40e6401800d0408110010b03c0854004c4440b058020105416141c2000050300704000420740000c80c004c44041a502500411203046442c0010071150850733002d090740010039581c1c41d48552200c134040214080c0940180069501d011406850310301d150703000c1d9001c2c0c844c145100ba2102403400660341120000d0301c0300e16540c00c1c020408c076040d40760040d515807040e002043d05d02c002e4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 723452544 1250 723451294 723451321
    0x20d0507081906151413090f05130201020637090c0f0605160c0b0735090409050c03030307020f1e21130e150910030f08040e 55
    0x40000d034290540d42c0041c8842007040e50a140a00e1002440a11624000d2482103d4164648050714215410800791600e5610710300d0386644400c4805441d400700180c100618440c458010b04a416800901811a80044d4840c0b01c010401044441e0ba20600c451003650100b030858201015284811008001044000140070b088000c0e0307490100004046030404240000506640581d100c49041000c004403601050030782c028212010102c00c0c10006203406120060300030b00e4414849902c121000110001a501c1c0e19590079010b0141031200c0f80601480c1801c40c1d0b2760000c1520302091110842c206a8588942034038000d81511001081100300c40c0e0200300d80c154590304100761404140700c000400c0000f60315100105103908100500c6e0107c900d561100d54050080e14041ca080400720840460800c44035803082c07950048100c100080c5000d004958100d0307100c00c45003504507003446032074038200303d42501009007000d07203c0e18114181b262100c10b8500500800c0d0342036080e440c0480c03812a45 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 723453794 1250 723452544 723452551
    0x1020f0f0c060109090f141009050a0201110c010903060e07170318010e0105120a0e030409060815131202010f1d0d090305030f0f040f03030320030103080301050d06020d050708 77
    0x20703805a0000810141c607603000b040056604045150802421600c49400180e01c10140603203034404c00d42c45c030201a0150241150060141d401781c18801c0250002402500030940c1c800c0c0c00360420264058140e8001d54460203494000200041641c01e42905515141450300000c0c80c4180c234020551030290000010031240c802030340c0760b22031840d0010055402c1100d680b40203000c503009119070070740050b00b45070580d40041c20500c042090004ca650241c11907005800800d10070b610384c0c0c41401864070401195500710076884084160b880d0441b66000000321001c0002c02000041400307100e40c0f4403d410420003c0d07658070342000040c0d041a0300d0f99903912484841c2e03a060080d01c0e45071800780d0288102c541100c1c1c01101442c6070080c00d01030b07101150f00080f40c10010040610003c11110080160200614031903100000d00c1c01260f10072610065180c0d01030044041d0400040c000a010002542d0440307000b6940c00010459070301c1c18101a028004900408914060030061506c0e4040010b80c003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 723455044 1250 723453794 723453817
    0xd0507090501080f060603100209041e020307030c05031302010c0201090f0e0105120606030c0405090a050a1208130f060906060b0a020c0909030a090317040317190e0907080901020f0f 80
    0x40a81c400d10139030b600c81108450455040d08000c50101c4016000d8005065100b0300820000302062a411510760303140c1058174942070b29030f0110070001c01d140c140c42940c0301456203091440c01c600d86001640300c051398103003000f810030625034002421079006d01d176041c010340764200b0103080b000c0c0c0342d2007441d218607424031615108030002280c0c01d20f8080d01081c2c0501034a006000340c40c101040e202400080e1030050801501c5100e00b03030180740824400d0040801252068210b40d498503440c030030060101c42c000d080f400020f81c4603108100014420000310f181203a0000e00400da501b210f0030040010f0415901c08804590b002602100e00d03540403d1f4004c00310011107040c0d03180d40f0ad4021460366400b50b80c58000c04907087d0801030021800940400b03428090b02c16240e03280585994950440c40520302107203541311f00c0882c0d6501d980a9100030501041103905c1c200300102214000115035603c05440c1105201c000c80210750001c20a404491124112400082c2e64032400c003542d91a95001480641 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 723456294 1250 723455044 723455053
    0x200f07051b1f05160b10060203090d1202190f02040c030b030c01050f0d020c0d0e090f07030c0917100b04060b04060f0309050601180516021b0d050709050108 69
    0x94820a503226161854005880348000190382d0440814120441920805001c014080b916440340d1030000507107070074131400d9024203c0c2080f81c1021074084c501c0e0000f109541090001c01c0032900d6802420351040e401140c1c01c101c3c1d40d0031000990401040354403100c450b95000c5241014007048030181554a4400c0d181002000e22900c8210304440b0002c207829810742002c10443d26541c13040016181e0151003522503072600c5070040502040707074881e864609494000152481c8030a4011032420811070040d103058090303240641c0300301160a0024091021306541e1810840c0040c403072114103001d0301c88074500c10105520504c1c665500c9a110660103081d60400c1054a040c3c10301d03008c0d810884180c44487c07802c01d800d04030b0588a61040754001402c06a84000c0031000c500100070090080020021980305048004100710548000510000443d07d03500d1341c0760655a40054450600f141621040403500c0507440056002611980090518402c80700e010a19520b15400b640c102d8200f9000c94 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 723457544 1250 723456294 723456313
    0x40f0c030218041b060e0d0c05120105040203071703030103021011010e070f0821030403050d060f240f050f040806010e0702150c0406080a0603060c030b010801080a0f06200f0705 78
    0x440208200b400b402c4000f580441092041e4100b900d01c88000a105d0091281d4141d2a400032500000c808ac5000c80341d030391200f06100039800d040c080d00000d08642c0141080d00d4018103000c2d40d42e0310041c48024040c040c12050702180500c40d100b5414000310050080c01450028011f0703030b9850205004010402c040c000000a010600168a22490030b60007201140c502e5103c0003540260801030059007400010080300c05102c0d0700d4806c820282c6410603924078030324144590340c0c04000804143d04200c49400141c0300266811582c0010340d601d561610350307902d00a00c00340c03c440d0b00440d031001360b440c4071300d0001280400004506074403d00240c1e00701d4046070010245544a644155468403804400308014451603105880389a440042280b0100704c1075580d82d5800107c510000c1e141000030360300c4c000b203802d03582e000b0100c2d401490160000c1c0241a4561141c440489800310300500700c980d50031000c080d103001da084004045500501007030320f420444125544986c405c00044600d0301070003c45 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 723458794 1250 723457544 723457583
    0x30b06061309050705071505041703061c140a061b030603080a05030702010213060f11280203011508030408151501180f0605092106040f0c03021804 65
    0x40d554501c0760851032144642c5011a900003d0102501c0c08041000c00c01844000c03c41240e008040c06480b001c001545140c141400c1084000c004003038178902004006102541d981e4480c4083c403d480900000c8000450f8139082110001501c08510f090003a41508428017005502a050301030815520712604111100e04508a448078000104120310600c0911656441500078692051050000510700100c0a5060444440740c2c0d02040005040c3c0ea0345104843d4000701c51072054031542c0042081e1507403442901c580d01000d816403184101c00c420400709555094120500f02030018103080d900c19261502580c0701c1c1d00602803071500380300e075501b4050142e03004e2406a1080c1c024402e4005000b4030040110345580c4ca10306c00b0304051712070410105502180c280c2560060655880da181e54401072014860030138200145c400798251400a01141c4180200e580ca5015901c03240d00300b1812180d240444a500b495000607400423034510660748030a03041c90000e03000c0c42c0281842a44000c0b01e005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 723460044 1250 723458794 723458797
    0x108060f0a142403010e07111c030f0e07060c080d1112180c1527040b06070804060e060d0501090f0b030105090d0f201b03060c1905041e030b0606 64
    0x28a0a0f10704020401005031070000080280c118800e450000704e084408040940340294401d0403a1074489803052009200350140703d5072804070140582800100a107021444d20b400c018803c10040c0b050501480c41000003041c02c958100410b40c404124150007580c505441c0c6d040b680450140350860808120502a45424840414807503002041241d01c0d003402d1110b400f081003911081208140700c402110140e01c16641c04440480c004208807510702c10030002038650025845015403420881d501c0819412411542a55030364142060030512500201c2c0f8280700d80c4165441b000d15100005c255074401c0d4000c09030300d81c62582c0038040441003c0805080356800d5610b003060342e1003061100105400b5a2030700301491014101a208910840fa0b800005803041c5000e20b640d400540004821404000411803521016002400203140c034100e482c495110740b407003117100031111119165600b44208103d41c06800d1201c188540e003888546200d000f00981c0c002142c0c450702c4d1500107507860a1500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 723461294 1250 723460044 723460099
    0x603050d0f0c08040302010e010e180f1303080609061507080703080a0218090901020c0706020f061f0b18041419110f090f06070c0e01140f0108060f0a14 67
    0x3100f107107001d255600544050407210101810300151118844050784c403003448240c02040d09415441703070b14107402014030366040100001a905202c10428021a61000141d540b0903c00c0e44c500150362114800210032500306c6514030031041d4005180707400c10030354030007400b0308503c01e480301c280d5501c1c1c044240f02603018448207105140d20f05d1100c180e09180854030f042d008148200014a009071820005060602c175800c00c4015910003203c540c500d03030040204a03404000e15450210b40b2071425241c00b03140f1200e1094401c0c540d03010601b0081440b460000103103071000200100305855070000c4081c2070030000c5500007600f065a43c4880b0801619000f01c5003031042c10703951a4030786000000c403c1515007140940c603403c0303a40fa10240040c0d840e96401002018019060850810f1404101d83c21044058104180301c28007051a50000e031201c944e240b160050900f0003240c65030b0b9500101e561042120b0301c040d88a403103281c0c001440d00d040c00800200a030142d91800610884010b226100c4017180d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 723462544 1250 723461294 723461303
    0xb0603070804060e01020f0913020325050f1c0b12061f03080d0516031505010c030302091005040807050303090a03061d010e0c0a080a0b18100603050d0f0c 68
    0x10800900114481d2040315401032156100055110f10306400c2800c98001c5c0305140c040c00d4000404001074544196280b00141114809515503d004403941a01c1140a0012940e03001c000407240234a80c018003d4a2201300f04d662196124483c2594804503c040032034030702c2d2007502d0700b5501c0c0c5550401c0228001030314201e500034060354036500406041d880401e404100f90340a2a80c000c000a02404002c1003407031aa04000319403801c111031700c04c1d42c08000442c02c0040c1468806100e410412000c1790324100e480c2401d0440b000d5003a800d080d40648038a03000190b020b410300000014054221000d8020f4600c02c02c1121442522013083c5941d03403260794441c0d0f5000540660810005103260081a000c84e40048000d4045c030b004400182542c4241c10491026080fa101100242c1801d078070388001000400018080082d4a0b11901940c82010304000860010b44180d602548010030901b0560321525800700401641c90510f9600c40e14442607044c0000c85403a004041148a203462001c0c00e03030403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 723463794 1250 723462544 723462547
    0x51c090f0e160f0207050603150a0503070806040206090112150303020d0320160206030c09040b040605100f0323010905070e0a090f09080c100501080313030f11030a0302030a09090b06 80
    0x102d04058030104103a005200441c49948804251500d6100165010712000101c48407001c1200e404c100b68040c00f03170015030003079001d513204120000c0c0000b80c4a4009406490a0f0390f900c00c80c5004031107008070107146030b0220382040400920f00000c06c1c28181201c1c041d90079100c5400d0001310031016a01e0300021854456805541c280c06200d00340c00920f01d100d4000d0500328030703080c00c0d40420b8941d0011a60008242d002150010550500d03000f441405001150200105c50030400000c0c08240f101007501d003001408460160664065480000303140a418035810248000003101c0c4600e4100740070f408071003400d007000300300c1a50150304205c0281da0000e018008550424251500071701080b000031495640b24405034010a03c0348000742803060074900030b0030040a48450f181c05032038069001541d40d5100700328110501044245001c02c1d00e80c0130021200003086400d00c030401213015608264140541c45a10301056000030061840c0002510f980c40150350383c425690032240790401c0e00307810050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 723465044 1250 723463794 723463831
    0x51c0c080c03070c1503182a0e091b0a05010c15021608040303110c010e040f0e0d05220e0a0c1b050c1302071509051c090f0e 55
    0xc035016101441c0100308aa042902548034842800840d070302041c0041d0403900e02c6645554180039103000e15103886041c0c0b20001060341d07807249041441d509048980002d50484005854012501e8020705050350300201e00c1c28155003040d20740b03080c1020000c09910544441d0040d0034070500d42c4040700c8050f10b9000306850b580d201c1011b02c0364444d80c0310750001d03400c01401e6403500107107051040c03032030040103155141ca04500c2c01500052642840310401d0384902c1e03c810841c0e074084003840140c44180c40104051400700000c80203010651011460341c041c3c6424407007010b134072001514a4411100c42c0398084296800941010311040c0501c0001e88800c04c0001d0180f05142c021a1080e8800d181001c1031500c15041c0e0100c5180c1d010044a46d0340107146007a034589001c101d4400f075a403060300114a051000d54694403a680407d40c2002c0b00750b160043d610500c00107210122500d0031021980911807150a80100079040a008690305404618404500c2805c04e02c140713482070303002d807a40f80840b01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 723466294 1250 723465044 723465053
    0x1b0b0601030e0f0a1b0803030f1b0d060b0c060c0c0d03090c0305060a06060806011b0b0405070506160c090207020d02010e06041e080c0d05060f0601050d020a0c051c0c 73
    0x150710084012403144556900340500d08000025055020780390901d062100558031720400f078083d0340180761aa0040c01480102e0030102075598210203200143e44001072803804141c2140112401c0da094a850710300b000441c403102c0001000f16002c80c00907541140d99010a02c8968082d40e40d00b07041903840745a004514134026400b007500540140000d074411903880d034a082c1742280c21a02220031646442d02000b050b1b030840c03600c54011009081104134500d01c400d8000c00701c120300c000034244058007408241445401c1c0f148038090140039008580d035802280a9041440e90100200d0f4034050310500015484682d10a0703905680d4018040c112018090b001103da00141da2102580308004202c0042d0500e800c601c44400c003260348552682c450b1500c407005041881600181e8081c07400c1c1401d100014002113000740c1c0c04000045000c4040d00c5000c0121018022800a6540c1510000309440c140342c10001900025100307e00b00d4405500500d0260110030407450240c01040c01c807400000020b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 723467544 1250 723466294 723466301
    0x70503060301060b0a0f03050709140603040c2c0a0203072f03030907080f0c03061801150608013201050702181003150c12020922020a1b0b060103 64
    0x3000100003045058031000000d07015402640c0c0000450804040c406125400d80a030030381c4881c01d0300309000c04900d0454490380c64250041c1086c03194200200041c100010b05c044617001e402071081040c00c2a9a2800e0090200b0001e40507038020801d01c0d0010340144064003c4070301ca003070540c0c1c5004001010346054030b40390700e91481d2101840f010030940541c484040015600c10610400204070311482c0c50b5055041803091900d0002076001241d040c01291400a101500304804255030704004825045940c014000c1c2852401e14040c0d985c00083d205502014150580d41d04440000b8100c0014200d420804c0920103203900304c02107035041c20032560040780506040360025051095a10300c050f80300241040031900f0001c4606041410300070b00a0745440f145568600c4203081200c10142c039405040c02c41c45000b0101c41a4000540b42032580340d000d824481c1c0c243e4018a5445005848604d0f40a50012030850b030000d0b41d4680031041c0b54080c0d10600d5912070304141c000c2c07041d41300d040044000d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 723468794 1250 723467544 723467551
    0xc0f0501091208090d080d06080109110f0a0b0c03071130280b07111b060702060c0c040c0c020a0b0d02070c0f061b051504050709020c010f0f090b070503 67
    0xc0c03c00e02007075425407164140c0d40c07840340c81421030341d80c0c40d44101d0001c4115070f02c0340c121201f6607262080c0c1000241c400080040d02003803c6982c900d1800c49a030000d100000030f0340040b280c0d03040101c2c0b14800401c000010305001c61103a000c000700355951005012121041024040340325078a10407402c90350420340c4038202001e0440c0152002001602d548881390003042030214862840f104040c4140540b00f1180f9030000754910300f0351481030421411907901c50265031407690030782990041060580d200000c81d181a43c1c060100c5407598442650035449421031070708a4060741c1440360080c803152207000d0400a09900030301c40f42c2e0140c00c0c042c524805801550800b807200d0b41c204009070228845100035001001d00840c410b0f41c0030304000b40240b64008030100c504103441e02c20f0f100e20009801058130107151001006003105075456040c002e15041007503000c0c181892001070000060322064011604907c00d074141409404500700240c002c072410b0080c050414440b050200d04960b21910047d0703003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 723470044 1250 723468794 723468803
    0x31b0309050402040602070807050102060f0a1515050d0c05160b09070801060b0d060b030f1302030114010906060806030d05040620060705030a05150a050f04180c030c0f05010912 78
    0x4400d0701c4101160803680301e900050050f911014003000690001c0084101802080c805400e45081c0fa4181200801028000c08496a00c6405504a000309014070200a1500d201040c454103804800900305030300280741512440e04203e040d04140e03004604032104c601650580c1d0500c142c268560a580b42d0019103000150b0160074000200d00a090088202030102c2d1403d030f43c0eaa41380004035204841442d44580c00c1c05105200300002c502d40002140d03400140316050209503200d6100203030040c401c030450f1001c50198007001085502156000344162756141c3c80d106540e440300340800d0764138540c00d01108000b9004000c00d2041340d224000fa51020400320810200b03403125000b09500700134003211101d002410102c10000ca401c01801001d0b0000500d81c4241c1c40c6203d8100483c200c500e00e40076190040800031942c1215440396445409100201c0321035070925030312440e14002490311340c07001380d580b0402140d001c500c0520f55820361007103c80503198610132074546615106212802142500c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 723471294 1250 723470044 723470057
    0x70e15040603020309280602090d02040603140d02060f0103230a03080f0606071104051306020310061106070206071206092f0f0d0902030109051209010806010c031b03 73
    0x644048800000e00050490754401680320710388209100e20b4468545c0301c08011b40049080604e59101851800c410107801c82000350351011900c0201e0070f00c042c0c03a50002d41140c0761140c000180200c4a100c0c11001c0390000650707501107203000048ac1d07610410b035040d00e0100b015000410004404c0580b4501c0103c040d034020030420444004142440e58a240980114000358100840c1c480b2020718942c2c0840c00702c4502d418003070b0945448030b82d503650059a600660380c0e0701c003145005444041007041590320a90941d5a854022031000540209101d44004505c1840c001d0030048408074001d0302c520000c0c0e009007104c0c1e40e00c003011519410031101407846140d40342e401203182c41d1503001e040c01d00c000503483c488980c42d01031101884046544c4585041d01000e100442c90105031104803520b0700444800403900f500c007400000c0c010062004010141d2040c140703e884504c039014060076aa81d804d0301d5244180d81c500c0010744d4865075800c4018000b4106886c104010041d000920802c1c0303001c1d15000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 723472544 1250 723471294 723471319
    0x809091608101410110d08040308011502061902090a080c040b1f0e01030b130b01080f070e010c0516180e01020304441210050609060c10050106080108100c020303070e 73
    0x90306150110a00c0800a001f4004200c10315800201190051020b0120349007401d150000094603160003031b100b030001800d4850700303060507541d540680780c000f81d0080c1f250b0070740b9550b0024950f4400b140807009000c1c504000d08070100d0701e004401040c05c8510000f20030035100420a04070b414841803a0400c0c1070659804542c10141c54100b050001c0c001013440c0025074140341000501042801050b44124464000c208001f2a0348111b040d0201802824800f27202032040c0303491824841c04410305a1820442000091000c85001340040a000048402c00542c11034280641c280e11040f180508000f114850b265100a168490120201201d200303002c402d601c0301d0380300320304201c0c14a9a003100900214042802d4188441da40741c111900c0f0403c48241c40c64400440c61034001c8403100fa2007082d004c04c110a00010611400b0f444a8000d030b002c018960311200040d01446082c0100c1e0904d2240d000240082e00161080a10244641d001103043d6521030300d08a03000d5000300c881c3c9400151001c20b5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 723473794 1250 723472544 723472577
    0x114061c0614011d03071707080f01021312030e0d022205190902030a120909110403060c17010b0d020702061801110a15090809091608101410 62
    0x1c04020b080c40008144154036024001003c0d51101d4958114420b140302110303006980015508003107d200101c211500d0303108101990038502c55a029041501031803802d0000c1340e10642c001e181c2c510b1860404000c0b82d484286c0c07848040e150103001004105080c980480e1481c00724800d0032003a10040810f540d410601c0102c0c1240501d04001c102c140d0340320f4003401085041c0d1100156408407080e4100600340c0c054002030359a60040101420707008900c000500410b105078140c2025000010051016003626646101198810302c0260b4105250040c903034280782c422070540825640c851070200040c1d00300b400782490355000014480c500c9600300000c2d00141c5561028098008024004940410301140017520603500700311240e0702500309003104400214461407800e020710f070210000074007121a1030520003a00c64882c206512544031401c1101d00c0300b40f901c040080140c00c0c0c0c0c9409050b140c86071244c00e0703041d02d401915640d031005032501413035080003440006202040d1401006001580a9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 723475044 1250 723473794 723473801
    0x20c030c010506010813080f0714030301060908070b0c0c0f040609090b011802031e04030e0913020112051308073e0303070213090609080c030c01050603060114061c 72
    0x14035090351036208005041d030700400c3d025480507000740c0342050841c0a541d00b10251055400701c6082c104c01080340020301c6103c50954030700702000b038100d075902c3d6140c1c14042c0c14980b851107070351030611a0140101d1049100420303108801280f000900c400b8034a602007017000508000c0ba01e030403d40d00ca9001900f08414000c0802c00d80c020861100076506146001e84c060040510700e04a8600410a0100041c555a401c580d0400940c0350580e13107403074a02c0e003140c0e045941c13944181d00c00342c480144010182012101d00e0000d03c01d8032200740d050740c0f84a150060b0754017240e9110003a2060707082400030490180041c00200d10640d81c03100c80006004011004404c0c8038038079503c0c078101c1540400b0300044c2ca44031100400b0200c0003141007500d6540051403001004071a104807507110b840c0c0c4010080150000000e40343c1c495501da4a03000c521103410b54a07086080310904560070203011501b070b41804580103050714640d00501c100d210404c0240070550b4400380105000b40804801001884110311 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 723476294 1250 723475044 723475057
    0x4020f03011a01030605060408030a2102030103080d0c0f020d0c0303270c0806160309050a02100302030a15030b0412051c1b0f08040b0606040306180b01120507030b0a020c03 76
    0x2c0c0e01d80050b01c2240010200d58040d00218014034003007006004402d4004251810408c0c185495040d8a203101e20b100500f19410740582c82803400880080204000ea401030070004008c01020401c5405c880d6045404400c0800d0301c030007503042400109c510303900c58100d840e07945000e03040106032203908244084503030b0b00300c82d003412400115140c07030701c10007001001c6c9500034812600140510f044c070058690041c3c0c8507809410a16654003010700400c032050200e1341005400400610709040d0014014005c0c0d4800c903486448246800505030b10b4500d0b505410701900d401145144540c0d8841c0d541009941094140c04240035061203102401a00e16020f180c0894082e20003180045129200d07008a4061035014070510206143e10070b2190351000300250700503000600c1d40419100c18012401c0d6204640002d4001410b00c0201001804480c0842c2d02c007621849082d81a82c4e030b5080820910007600340014103076003111400b00045585000e8a41d0406a8440b005180c4201c04202915540c09039 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 723477544 1250 723476294 723476321
    0x1d092d01080d080c0c121312051005090111090d0204060e0705190509030d0e01030e0a0803010f080c060a0e030106180e060121030c05010b06130f1a04090504020f0301 73
    0x2140742c2032803a60b000702c041d074002d100c400035030b414208202c50041c0c64810381680080503071340c08510f91958841c100c680c1d4004150107503680900d0803d0341040742d250354510052101082c20600400c2102e83c0520506407180b200c0309a0908000a1174104030340f004005006036446034480d1000f0401445542038940649a19100c1aa6810170003000c0800480c444081e0800c1c08028843d02003d918086000415180e103454548a03400c0c081c40140c0041440c01c80d10303183c0388035505191042080d50401075040ea1200700300c0401d60f0303950b0040780d643c4040300008181c1100d0144800382e09139000322040000088000e0010801c2030300c1d50500e1484074040f02801202c00d8842002d0540200140f00c170a01600740380000314480400424521504034840740010100420384003072005102d8207501034101000010185641c450b8244a243c1c41c6005034010300134084000303200007411700b42d1160041c400030080e5622038201803070181d1420007040c000308180e0700b10050405034a80c6a82c00e01c50024880d001c1c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 723478794 1250 723477544 723477553
    0x8030307030e19030e011404060309030e04050907030b1902031509070809070b0c1002041401080a0b0d140c10110d090524040306020a0e011d092d0108 66
    0x1204020181c0e01c42d4800300d80942c20141c100d94801e0b105201d03a1005035098203100e0742551103200100d410022140b0520740c4003001050201c1c0382640740c1c011b806968065030fa26803000741c05004105c2103070001d9481c94641d0340040303420000149a10207180d84003e21110b80000c01455401c8603043c0e900c01ca4608510056820310070301c841c948074203c0f075080707a4140b4014032286031005d5155520350b894018071260510206a00840c7c14081003400b0403c090842d05544039980e4a044a185c1c0c81c14092041c04150742c10000f9904100600c80d00400c1b2400030603002082c14951a10405c0d194511074610140c041c16070300b1301d865101c4400c10b03e0345000350754170010203580382c1e100c150030081c01002c84020484424802c00481d17039141032842a0201501c015644c294014a20741d20768411944000d11440c00405d1503c0440d03007221401c817203001d007a2074800710310407050743c0780041904005456921101140100d50149402800e0703030807103884100d920f4883c2802c3c041d24040410300342c0c0540420b911 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 723480044 1250 723478794 723478801
    0xf0303150111060f040204050a0204030c15090b1e090f09070e03390f09040602030a0513030512070302160503040938180103060e1c021504150501080303 67
    0x34012941c448550b10714014040c0381c207000c0443c07401e82c0000340c00640b14030380b1000402c441340903560440f0021030f4000400048a540d400d2809040006244000085503002c180081d0700021a4112041c8a14207410000e58601c00200c44106d80c012480c259045a03031041240c0c0c00303407207060b4001d001d001c2a40f03034603114001010030585403a030b1540440c102d8131200340d500c42d0211088134058158441c849007100039031440c000800c03c040d680400e182e6200c0805c1040c80107000d5154001d600682d9400410311165940740c001200c0703010b84000c0100082c00c00c22220946203007100510ba0400124078000d46001103a50007041344820030f01050381c0d0383e00300280800ca0004a842000324142409000014540d217000c010001807458611981141c81d81500b00700b10b55490741c24031074a003000c1c00d0300c1c03002a58607410408014000950034034124443c3c1c10045204580b0010702c00c801a20540c01811340f5080707422803202803640600100d4103130400d0b00300039420b1201c0b801030078041c1201500841c1c1380e15 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 723481294 1250 723480044 723480047
    0xb0703031506120e1f0f090b0106050715090b04061505060301140f10140a020102040504140717040b1909050d030b01020d05070203070b0f070609030306081204080303180f03031501 79
    0x203908040d460b07126400a6005640482141c07481040141c590400042c801001040d44025203424000100a40250230005c01c0300b80c1c0040140007900e01580b4002030305807540840504a601503500601510180c038002030024050b07401032081044580c2c404209ea65840006c1403032604280c102022200c04000c0c10030103418074a1041c400d045d0101c1d10b40c0b9103003403030900141801184080c80501d88030002042d4440e54002d40449004120103082009561004118854100c80c1541c14600061280d0990300d142c0d0381540f047c2d4050340e0010120702090b1a110381880c0540001c4115011050300e5219001c0414014440080c0e1629192404601038048400082c1440d5212803210280801031002002517140000c08000f541e12200d8110354502c000e24942445005031840141002c2c10030518000309941a013140c0110741c3c9013030840d07607455080b80c0c0200d0a070046001d18040b6a0003480016211a41e41000c2c8403003110020903500160315221120703080d82d0040b140c500004d8411080781d200c55 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 723482544 1250 723481294 723481301
    0x11011406010f0504120f0c2313020918130b01120c0e070504030b1308070c080d030207030806040b0613141009030f230304060c0b060f0a0b070303150612 67
    0x34922403500704c1c81e02e400c10880701488881c07404040c0244440c2c0c0e4030300041061441c442000790042e407200214070080b2007410483c904800910380e0041c110101d0035401d915083c0244d030701c8144001e00c0c28052080c281a85512004c0c02000d002800031032003020008182140c202c1806800c511401a01c0c11603a400d01000d444250303030060b6081c4a040f0100902c3e6648901a0780c1a2030f400388010a458a848e80c0b9040309101c100c0d030141420700b00041d00c40070440c40d128034408030b56400701901c4c14003042007003e400320300407114003401090031200003459600c0c141d401001104802800d09081c01021440708803241000e4100d440d01d941d01d03072034841591130000040c480c0740c581c6240c1a400383e802c0d981d903100b0a190403500244800d03d65a90364842048089140308030702d840000b1681c0343c0e5a181c00081c40b8201c0c1640c1524442d041c000070981d6030910102c2c0311507124024002280719460403808201c140c0c000501034041554030011176580c1818900e44000038091592940da6501603220b00c00101c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 723483794 1250 723482544 723482567
    0xb07030527060f0c0102040e07030e0714360c040e160c1103070506210c04030224090d03030902030c1009050d080c010615090e070504050d02011101140601 68
    0x86403108001014155228801c550f00c1c20300640c01261211403100095019004941002c640c0641083c20444203682c19840081c0580108007118800ca9490301040f0b00c0740419146240c2000301e1240c1e480000c289194451502a02c48048008040c4105518010400f064a14111032000000d0401912a07802501a0403004014600e40c051014410180c03413104103510080114681401c081c015580c2404100020040904100c2e078403011055480c44881004040f40442c285000118110070740c0784042d2001c2d00e42c09004540c9403800c40c60312600e9001c401600440908040040d00c1645c0c6a6040348401548651004a020703500d520402d828200000c40e120b0140c1007140581c19885c0d0710030705031002c4803803c2d250700c10507034103900700f03200140302c0c12405444540c01c00100007008810844441d0040e0030b07907503e61703200d1500d400d0820b07600d8205540000028100384030a002c646406c20b10b0881071481410021076041215580328203680e402c0400c81d60f030740c1c2180c04010711541c10400744841c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 723485044 1250 723483794 723483847
    0x501090821090307020d1b0801020a030e01060513020c07030c0308031e041511040504110a08010503070f05042d09060b030a020102061501210b010e0402040e0604050a060b070305 78
    0x510718080030150b039a130145103000380c4100c882001407400d2004001400c00500004002e0402d000c1d2520b030300c02c0c003039480303800700800203450541c15410000301842507409841e00106a2600301110b0900344000c0e4002400c07032011401103500c0000040e02458801004501c504580707a120700d040120030001140c525000c0403609050010080000d01070b201c84d160000080400040e08480c00700c190405004d2504850b8015281084c4881000d8809002d09040580d41c2d4401035aaa00c0301e0600d03031a1034140c0301d115900da140d0703101442076184c0340d0011800b8a05600e0880c012110103820100c40403040c0308180c0d4850307501c06401c41440410700681c19145003e400400001b26142d0000759038220050080c6203903002d40f2103001c540d078450b9506044507001459500480140c80d80244014144114145c0c08034580c2c4045c0c0d00d00b4103060096400721f07039940141444e9030b91b0310030074000503101c0140320038001e039511340c80407800314901d0b406030081c0c2c0c1c000da5916442d8240c101602280c0d204d400c3c850351 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 723486294 1250 723485044 723485107
    0x120a030c0e0406030f0b070504080f030903010b0f010801170c0a0b0310091b2003040617060324130204020a0e040501051c0f060204120b070201380a0305010908 70
    0x1010489101c820651150300c003072000110359900d903080302c08c1c0c05203802402c5140604a44c003910f0384400005891110740c201c008004e056014010001140c400c03038042408200503200400c000801243c660007060428000e82d20081c40000c006014010300390441c1c00703c0007010052200140b0b00074022005014051010003000d200d500340b13469083c00c0440e0400401c03a80000500c1840c07504030010005c01d015070100c0b42c41741d4071260094000080743d5101c0c1c0c00060380c00700044952030f0016103041507403200d1002c02d8810340740134a007040e5008010500c0341c0e8008021000e00050300d82c1d2004102d18441d5684010b140003d2000300001c0d0381d81030b88030511034810300101c000b1212440e000740320f81942c0a44111149a001d1508801a01440d4040c9058a0055080d0028000010807085c41002d20ba4000c001c10900c22681b17101c0c05503041541d048e102501d080080c16268010304620404000512010102e5500d0303072454291040c040d8202d942c0d6a000c244405803445070380b480720510903100d0556 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 723487544 1250 723486294 723486299
    0x8180d0f121116030516060228080f070e0a0602062a12060a1d010e060d03020703020108061201020d020a090b0414011d12060405161214120a030c0e0406 67
    0x3500c5034050603051480401c945160301080502170806c940c000c0744404604044801c01d414188004d411241e0402c134400b0140402505040c012082000c031501c3e19100c0149945070909001c4540400414100a10010b076001240d150f80318a2901d008041d81e038000c00740d82c44c09050401c801c00ca43c0003408040c0d40c05108040220002d00c09076010f030440408480741131313659100000c4942e880ae034418115a4101b0744091a08550080258103031103610100300f03040e440d4842485410366241c032001c3d0040e00321410900056105081040e00180c0080c0442a00070a5092440c22a4000200490029800078000c11110b40110001c0018004500c0450900d454550803030450058032011904024090600c00340504650040c80200705024003803040600c41c41c1600750351400c0a0340d050b0307014454501000140b01e004140c0000f640c5149081d00262180e0b6a0784005080e407510710041e9a000303d200c00001e845101c000342c82c3e80481c03994040340044440c08050310b008001c042c00d0340a6414030405 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 723488794 1250 723487544 723487571
    0xe01050f03060a120305090906010c02060702040b011e030506030f0f120d061a0d0e030306060d0506040f0509071505031005010f140a050c060c180108180d0f12 70
    0xa89106803900c00c0c0180d0307a80e40340750018a03400350310741140010360141000002403507406409818640c8040c0c1d99030f0301c01d40b07500f80103490401180d14001e6102e07408000102c01070404d5005600302c0981818078a400c0c1c1440c00b00e00380058500da40710310004c5e81d21002c02241345030401030418444075100180030300344032a50348551110326400c04a107812500044240e0640680c4d8480f40040c0300e840081b80313030502c1641002c1c5059002d072180c0300c2d07001e041c04908000c0d13641c0402240d0180c80e00070205807505551a46074405003000038589a070159403429031052000d40e81c0a49403141c1511006420000d05003030240841030142465039003044028410411801180c0501c0c1003518402d0a000040030802a0200c0790b120300e2a40d411002c0d0400302e104070032550008090242032050030305542c050381c1d980002080c0c40c016940402410880040c0704211940948a8150050800c00c3d230300801185032090540340c0581c00e034410b400902c0c000c081c0031400350f0040d605000500ca2144c14400486100d61 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 723490044 1250 723488794 723488797
    0xc1b0910032a0605120618150a15050301031403030f010b2a010506150708031803160503070b0114030d18050a144006031b080d0e0105 59
    0x40200326900c0c0c01c0b005801d403902202240d2440c0d040d04902c82101d500e4030001012034000b0001440c1485000f400301e0142d10b40700c2c80206c0c41c144145a02503050b56001da01c01d00c200f26805004c0c0d00107400c18000700f50111499140b6000b220281c951503925451440c1002500c0c5400704454507a42090041c4500e130f148900d41c0d6070440f214013852a4071130440d40c1140c941c010b14034a04042a0480b2101800561010b40280348102c200b200c1a1013484400c5000e80075600c1029801032072890100002451500c08281035540403540da070072a401c1c41d04401840385483d104440c280c13959800031411808002a004117240500400700ca00044e292140e80843e90360704141810109014007803564003161060041914000d040013010f02e0846a50303201070b00000380981c074420340208212484003c000104107004845500f0400421001042a5801d422460045000e59100d180c4655000001c1805107a8507440c0110310420000e040345059003d610701a081140d605c1401078080000100382e0b0481d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 723491294 1250 723490044 723490049
    0x24140c03190e060c07080606040218060c030c0a0507030b100501020a060905010b0a0321140319140a021809070e09040204060806040302030d06270b150c1b0910 70
    0xc0c0c003422403040c280010b0320565034009940d604100003007595000880c0c0000c0003401c40d49840240d81c01c5489400600060740300707094000a004074024890186420004001c00c8120511402d690070008400101414460990710a48150b03100410900030b100880000541101182150701c42203407810b00084d450b007040a0300644903960355000c110906c4000c1d045020510760041205142c141c581c5070040401e9204c0c240b41c0407403c50080380040040c026800c202c0000c9060200504582e0b41c6040000301038050300707400301020745402140302030350810721f200d501030b14078100c0150f1920148c2030416444030b890b41d071003407050603405c00f8010060303040317020f110501038141d580c09407554440c00407501410069010380c509101e514204030602d54040b010342446048140c1c00d03c80542d07502900f0409080802d001c107901d02009112041080b45680071156610b00604403242865000300b482405030821030300042e554100010940b5024614018002001c0b01180d03160010708000880d690005100e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 723492544 1250 723491294 723491317
    0xc06090d0f0c0513060e100305060c13080303131103070f181e0914150a48020303040f08162109080619020a030624140c03 54
    0x700500d041c80110141a0050071018020000b05071080c3e07816001440b1912601401c4000b000204081c40724218112048030340220041400d40c039462500c004030f50001230800c038001e200b010000341400082c00558400c081660f902421032401d03041040c50690002e40061181c0c00095003400884400180320058030548680700c040e55049030038007001000021403480d0200c92049a004030b070140d81e040114038601c01e12018420030340c00144a650381000d10b4041c03080c03d00050000d80c00400c81d5001402d01790840c01d1070703000081c1d94181510010264450781200044100130301001c1440c680c400d00281d01944000c601d9403600c4e40310485601014040103041c81c100040c03a11003403042d0a420072103203801c01a00350005442a0240401d24840d42041c40414601c004c0050441d0010580912400d5031182c0400300303d10902c00c2c0002988400c540509250340d5140104107a0603224411240700c150007000d0701000c040c0100a000c041914801d06c461084c100b0560482c1100070042e00d0388640310 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 723493794 1250 723492544 723492563
    0x14060f0d0c090e0c04020301090c110604151e15080f12030606070813140301110a0203031920120112170a02031b061501030c2703060c08090c06090d 65
    0x4080d1401e04040382c801d01c0c02d1740140080004100c0301c11560043c40740d5403050b03c58584c1491061155512242c0488024203180a40e115400c070a800640107030307807111302c10b0b1111982c1b403d015111b40121104900030007801c1c11a42030600500c0d000b044440b070300d810207000400060140380d950280c9484000d110034060310010800004100e085429107400501c44d18111090b030361219000882c6182ca090228420340c02c10b000b40302c103400100111501020705502461031135840c0510805004583d040c0c04401e01e40d00c868007002040098250180d411780602c2030303903a40c4208250b0111805040e00b1100d1040622580d000c0051043c41031b2003030190695000c65103c0e0034400d816404e6000301b1903064809501080100c8140700041081031262114480080240c3d01880045007101c00b03104c081e0300455a68202c54078101447c000107000b201020b4130460040340c59540f0401903071507844c4140085480e400c00d01402c440c092004010340142aa103003400d001f048400551207182c0c008002e00400c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 723495044 1250 723493794 723493811
    0x2121e0615090d0b131502070f0308100504020f0a1d0307030339060c021f0b031213030c060e10030e2d010f060f030b1914060f0d0c09 59
    0x252803060120f800e8200d4003664207450502e0000803c0c1040c1d410840310404868003c800e601c02030700c29101510741103c1441c5000d02240d80c191070745d0f40041c04404144110301c4000603c1d58940c0004c1c100c0d42c20407401c2d42c1d183c03061420301404c40621111000c0e400784041200c00382e1030710005801c10481e6010f00c2d00c1820180c8200f0b0035000841d20582501c2494004411310b07911240140700034001500c0f4031010040c0504620702242c88400040c5643c001c0907100103a600e03244051f40054580100040c08d42d0050650386010401c59400000b070300101d4404884200306000e903040000004080d0f130308156080c0300040340001c6440f5400c4403214181350752503600300d2446034204044502c0d4540c0d1254544a0540c031504c140940040c0da4070b2083c41d40c20008501110301c0940507001c1114681000c44c9443d40c2140c3e1481080500200200480c00c0c0400042c2c2d00c000490189103c505c0c100c45007501c0908005080c00300d401100d014031390185200c0000a40010040040503088075416a8001441070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 723496294 1250 723495044 723495049
    0x51206060d0816140331030210030b030132130b1005090702011e06080703110f09010e01030210030b0616050c061c050a0c1704021302121e061509 64
    0x41500001801e10f0241e2404d48a400394004010308001c4402d564011000d03205481c452148100c05c10b900001502a18040005050043d00d078142400340d818085180c2a10801184c21140d10030a20041605076140c4280140e010081c491080f901145030300032a45442d00406014600e0220002d11046110300000d400c1c55549110301c0103070100900700c41050a01140090103400460040030b450724180c6003144820061348a0281180c940d83d01602da02c42c91a2110000904040309046e00003c400c014640d050ba50004880e011703001c0390410007082d50440c010300c40e01801140c40c031014503180200b503903516619641568410b0800721049400d0a84900d4036900309040c251400d0f400c148003003824000d140713105601c40065840c000c000c02095031103450340c1060b10f42030070a020100e500d0402514120b170789803403119409070001e0300400031500f00086960890340004200750204910300709024000e507510500314050102d148020726070307040c07000002e41d40d1000071581040c10000014000c2054 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 723497544 1250 723496294 723496327
    0xa0317040213020a020c0102070e100504110d05090f150403051207090b1c150605041e05030a110f0409020616020310050f04031407081b0124051206060d08 68
    0x10002c110055481e8104040c01a5803040d03100c0f0800d0241c014008007141794041240c000b8851079a50700054103440c5050180001030442c0c8103404080d010401c9010740e904034500900740211b5a1400a1103206854200242401050109101c00501070740c240030200340d1080075640c0344020f1000085082c0c036480d0042e503402c1d55035406038a0042c00440d06000500e1007040381d500a100041c01403014004d02c0c500940b82000900030b65000ca1405d00c0144400300003925501d1a4104124a050b15a505c070400a171500100300421548030a021400c881181012800d2080502040d031f028002004240e002882600450703103500e4040070310104c0841555401c000c02d803c3c11070030f41410095410410b541c00c29181c0d0403182074021800c00d400350081c0070040c07000c5070382c001e411694240c100351000c070352001d0180040814244075902c0b504914109090300180c01100c1181c644030b000302e24542000c4c0300752195182e80310104c6800030303000c00a107502c803c02480707038140d80244c585540c0c0c001c0c4080310303200303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 723498794 1250 723497544 723497569
    0x3051e091c1406012304180606090b0906030616090308030f070f050c0c1c060e030301030302120c060a1d0607020f010b0609090a02030601050c030408070501030b040b100f2616020a03170402 83
    0x34890b4107c4e2031b00070f200307180d80320005907a480c1109121509461050000107030041c1c038031b980c00d40d00802c0000d1004100d0100c2c0b50904409241c4004111b90720f8880f8501504151145001d4510703610501025640000304000c15565a04107030742004982503049489a640c2d65940b4001c0b807144009000c0361494404400c0c240c2e6000d0310411145403080c0b5040d40d40d030005d000850152080d500e4a1842114070f10035a100302042000401007a640e0702ca000c6d0281400986440b9a14070000d140d00c10b0150601415108030407031750092910350780c40540b403801c3d9400380000c0e0340145c80402c418038180d101d95450f0303a4001d6030018056a079484400c01203445110ba40840b0626010108000c511032902181d68000c4800990b81400742c18081001c000445002018a50744440510f0f4040f900a0040e1f101c81c3c0c0002250402e8007086601c04a05120410785445803040c2d521440b0030085201540800082080d200e84014680b80120740d40281241640782c1e1901c044403070440001c1c0443d560108000704 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 723500044 1250 723498794 723498821
    0x7150f0f2318010228080606160f1721060a0303030203100306060b0a090608061807140406030c021603030206010e040c0902270d03051e091c1406012304 67
    0x54500c010740c6083c541200a42c50303c1c1151000c00746060b00c20703200d5049640940402085546000e003024002710114041040845880d40c00c2e01628005c2030400c1f641a010904d44403000d0342d620340000743c2c0301c030f1034080c51400c0032954201c0c0b06000c490b8640c5c0c5805015260305040050380ea4440041c01580c842d20f0764801002c0301d09115010034004e42c00c50283c41c0f001119212034828545500040c0c1da0500204c07035646c0c100c040e030300390080b804100200341e85d0841260305000c525400c03620010100c40d0302075000340c00442e1720f400e00c0d84003030380d4108084c00443d0b50090b512400030b4150341d4001d442c0c18062154070407030000e0501080501c000310f00c07094000c08800c1001c550b180c0640c446104005000f580305800840400303000d80c0903041242541000a03450766802c4d182007127403458208520088000c641d8054410b00c620642601d81c1d040740c01d00c4080000c00080071141340d2600118901018a1594031a00048010044060603410084154180342c84111074902d0240108004003000760310104d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 723501294 1250 723500044 723500047
    0x3060708150a0503160e070e0d02040f0b0d1110050304020a03121803060510080a03080601080c0c0f0102091005071703070c150605010e010c03050708030a0207150f0f23180102 77
    0x8017040e038505000c4c1100c00300000f00704250f0314554251030b5103c00310314140d00100642d01940040c90035900140e66800001c100003131202a00e000325041d800311441c100c82100c41c1e051801c08600e01a88054000429464014614075082d07002c601203040c507220040a5181100d11100000c3c011000c542d1080244d010f0f500307090b61b81e0700b00b00002c0d01007520030381440080000045104080400c40d6040c158154552400907180c280045075015401440c2d45403072101881040d04001050103c2c0039818900e100143e100c28502d0b0401103005090140300317041c407004201e0320001405a8134902008042418100d032266a070320015182003801c2e2400805402c000a08135450101541c0600250382d0700313a032031070b0420f40c040b00190b0300d800c400d18001d008690107201e41c0d00000d448030011a40488400300150402132142e8511002030b070203410385a80d00d5100c201e500e410441c24401c082604030300000a101c00841e001d0034298000c24850301114803081ca20000b0408403925050000d02d403194130085 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 723502544 1250 723501294 723501313
    0x503060403080a06320f04020f0301031b03050a110102330a020f0412060e0a0312050c13030201110106080615090a0203010b0a200601090605040b03060708150a0503 72
    0x184103200454507541054503101e07005c18020b40200e402c8140300c503495000d070813001580320440408804c01784001e5000b02c041045000c15200d600241c0720481c3e200850a07269419898034581c04c0d07602c2d00920011003690b03442000851400207440d80c600360040c00b442d00383c0c451040101d08007400004501030740744244001e13445080405010045446d018805008282c6076000321005034441c41a43c00c4042c01d0901080c00b407458410329000701148541d00000341500080c0416040a104d400141c000c5892111200c1e1000d40c10702a15034814904074405180100c2d0347d4a6200b11003143c0400f81c1045003c0ea54015a6442580001c002c0c4c030100e4101c80d03451074808969401492102c400314010201c52011840783d0000d1700039203041e240003002450402c0304000f000c45a080c1c88501d5108411203042048815550510985028040011000c5203060a00c1d084c0b106960765078840b20300952219042042e201d500851643e001030080004c50549040c00700000c00114440e0442a814010349952 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 723503794 1250 723502544 723502547
    0xc0b240909150408030106030b3f150f01080118060221010306020414060304050a030c02150a020c122a0307051e04150602070b0706021204060905160605120403090503060403 76
    0x7446c102c03a050b83c1d092044c1640034041c403a84d54012401040000e0039103130802c1a0072114480c01e83c4500750354507441c8101c5807400c4042e1900c8900c09148200b5454482403080300d4900d08055805860413030003c1c01f12208501c203400b1419000000070b000c0590100c0c1034004400c021500c0880f0703840c14000c0143d1941c480c03c2000013540a441000e04a81d03100613015031906000007607070f10464218003d0500d0310304980307081d240020400801c0764030050020280842c0c01104000e08001c0c005680140b032202200c900b4890029003841c07041d01568001d410500d00d1510051981d00c4500d00f12903074181519040b404a0b2030035149030885030340b200e854081c40780b0022400c0e002108400c4111024810000b142001e401691014010100142c124820500032a4415001421105c0c82030030014600785801482c5c10340f0110503501100c111b030311810a1401c0c4141001a07809070240c0000c8032540601d4000c01038124401c2581003405e41c0240e0002505142c01a4034590007464041c0c00d4a80c40d05d0f01c2d140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 723505044 1250 723503794 723503797
    0x3041b051e010f140403020909010209090a09050d03060b1801030f090b06041503020a06050a0215010608181618090204091a100e061e0a060c0b240909150408 69
    0x9038006112120000c481503c134842116010400c480c03850b19060a6400b030150200f0014036144480d90204803402958070b0350300d4450b2040f083e07a00700185201c0c6a14040d8244101304032080200342c2000800e020301080c510403250b00d00a81200115036003803510060b00a07003e0b848800b8903c2d0b00e4401294113000c0082c01240c42090211400c1140d000b80e4856462141c03d9400060340144000e0000d0012500410061013044460b004949109803400302020444a090704902c0000d002c00082c481c4050102c02009840c00403038015010580d140315034950041000d2090000c048488a1108000340c815444040f41c1c0b6000b420030b000c140d809003480c2070a602d5205c04500003010720030000f42c1c3c02556440e24000d41d40210720701110740e16602c0802c484049022414030b030394070524100b205140d0f00c0d203440d04001c10072910360308050b290b54106000d0b8010010072160052200310341c00d40c0b0000443d00c809440e0b60341210164800c0c2c9510104514090240780200d030b03030715005401e201c1403054420 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 723506294 1250 723505044 723505099
    0x90105041223030c071505030601080408040332060103032124050111030a12091a070f02160513111209010b12010902091501020f012f0c0303041b05 65
    0x70b040305c1d003c943d5801c81828160b80c40030b1440002d0401d00201e4055032140d40d51035049400740c82603071708103622034483d0300c0e010082901c1320098036000100c01c0c2138143c10b1490601e45c40130b5100030b0007041d850354402500d4100c00208100b0406040e50b00e40840c002142d006060031102d10082c10803c501d1000e250010500340d0007500d01251906881c80c9820000004445104800d942e0b1040e0941d001315440000c0c040040c1d08452088816103403e4002c410035a00070b00c02c9506540b4004100404074010b0b0400146c1142c4014103252041c040c800c54450108003a0b0000060000040c0c2ca4200a8071110034010724a0600b84010110140810108150400c40740b14104a410011117655a503141c2e00329400309800a402410100004079842800740381c045d100001030060ba480603500001c480d003110131500e10030700d1a2000c0c0c110a03d41a142400409400452210326407900c400d41605a5907400024001041109a02030101701e00f402e0b48481d20003048003614200107004106c0e002c4070340f244041c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 723507544 1250 723506294 723506317
    0x9090d0807021f0e0c10020c0405190507020d23031609030b010807080d03060503100b01110d09090c0801031e020a03020a081c0e15092b051209010504122303 69
    0x1d0b0110080340313403806d03089141e800185c0081c5840c4e030401003480090b0600422003800110700c500c3d10415542c0c20300400d480340c0007580c09003085001110f4043c00a40810912502da041d510120070101c011030402c403608100322040c505000260010111b90500d0340750802022814080c1c000540307e4000110401a0b503080401d44441d08031003c0e0031400c0f20b40c1c070721030298560311082c030509107112258088045040180740500c005404074030369518101007640c0c11400548807a2042000d9206442101440c020303c1c40c1c0003a41d03500d1030b1214004400c224880182c0c02c03e52401090856a80d0001c1c0c03c02154050415074103241d83e030440f41d8880c42010a40405118034010050100d0f104101480b039290008184114903800440310b80c40d250030640030690441a07a8100829030054003610303043e045598003004000c10064a0400d00701041ca0700c2c601940039040c005500d540c1c1c1c02500340c9084d00d100c2c0b1800d90841e501d90030031031602c0c8400140e0320301484940c000c41c1494403000c801840c480083c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 723508794 1250 723507544 723507553
    0x807080d0305160f08060415060e040b09130213090501111b1f1d0303010b07020a060c0b13080d0504290606030a020a05211509090d0807021f0e 63
    0x35a40d035112003d001d9540440011440054811014011085d0680090015000041c010304480c0804038100d00c80c6c0051000c1188102e10301020711300350007001c814603002d90300c07038180d0b080212440d910f0b11030408000b40b040000490301007215000b580309003813040d0840001d014089510002403040d903c101320701040e00100510038070301e041740010b6143c90480c2461120080c1085070007000002c1084441040c00010001c51100c0860340810107140a000159801e6076251003520400c02c04080952001c41030004a1440c50081406880403030b80c005000f600e4241340540a1030192414400c28a501044034900018401444040440350024a140a400d5840f030404400c2c8070712182d1044500742d40c070140420001d04103000e2038015240c03482183c00c0c503070300302000d01e259a580c0800c001d000001e43c034882e030104400785070003c4207164a45825540c034000e80c240b41c0f14440e111000500c010301440307034950210302c40c1442080040506180078002c44104590380c007544020300308052100459118 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 723510044 1250 723508794 723508801
    0xc0a0503041203120e060402060f070c260706080a0921090806060f210a020913030305060d210e04020d050103060c0e010203030109090206091003050a0c0201062d0807080d0305 77
    0x140700d062150740e6540011b10840e50340ea42000001d41c07151030b11008500e41072286100240c0701c2520000034243d101880800c6c900b502034080b4036442c0316060f03411581e1004104105c0c90f0340014025800ca042c0705000308034229541040480703851703284400541144800e9815034400d034084160b9081c2c6107440c0540d0051b0b01c0f10020890489034400d83d10303600103081d14080210503103415106503041c0415040c1d412040d4030790002214101f040f02c00c20040c600810002c02011303070511940394400c03012610082d80708190f469204002e82e030040403a50001003c0c103822217060050f504c1042240004100359038600103103042501501c0288405c803042800c1046607212280201c4010f450090180c3c011402c680ca010780200c05003107038440680c1c0004040240c501c1c1600d40b40e4100444022b81e480100c0c2d01d09142d880d4030211010f1400d6002164580318080c00982c102503a00400740102010b101c080d00c1c410406070b02158490741c0b00e10441d2081c007200040e08180400d0840c117000e00e40d24200255074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 723511294 1250 723510044 723510077
    0x10f06060908030f070c0504140a0b0102070f03062d0b040b06040b0f0a0516060608192319050106031b050d0204020d0f05040b0910060e0c0c0a0503041203 68
    0x241601440c602d0307400c1031101414070f405040140c181140078011070404a50f81d41c0c00720b0120344000e4290800c8441c201c5c1080424181801855107555003071008025041c0b9002e100d4040c041d0600005114980310203500c503000f08101030b4100d810071f140ca95640d2440d02c40c1201c1c8000c1150140740e074082d80c102908a212490071205840803290045103103458000401d94991b00760b840094034406116044c400002c03150403008000180d04e10480300000c070107003050b0600349803040c141c806803481e12030b40443c1c1f000105071072908071400441c10244602c10000d0080319060a0b1202d4a648a101720700b195042484015045001141d01401440d160101c101c2213107107120981e0701946d0f0b0402c0e4002d00c0d00c0d005080c540e0051500c1c450712000015080c0d030451104050340d600b603406507900c000740c409104a0520900082002000c2e9410810019140c0429140031007c020070120540c080401c20290005042c00507104840d07001060b203503200c0d2903041401d00380c1c10071002540043c032007102540412 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 723512544 1250 723511294 723511307
    0x3060114030112020d03181d010902030712022b06030c0501020f030a0807140d29012f07030605010905060a05030a061e020d1a0a1a0906040314010f0606 67
    0x3507845050f601251500354091151506050004504114800c0009804400302d0040030018003120b1005260340c244021500e420400c06800201e0000d10400c10b025019400403030840c80741410300005625904480d1240880c181002c086014101c145903102000b400c4542c0540d007035a00c1403010000041d1100c004a030394500c542081c50a641c402c202c0721038002e000c3e0b10a035520009a203010403581588041044940d0822504041c101d501d0b000c2d05016140000640080d0381d079141c40d014908008800024070040200844129001c5010540000c0403141e01e007038650600007070200c2c0c1c2141d91301e1a0200013824248190010302d0724120100e5914644072000c1c2e0102c520080c0240703020f68240e103400004101050981d0100302c907000780c0404203402d0340003a081c116808100024201c402001c4044001050f90b400d078481c030741d01e42092141042030185400d0101001d4030240c1c6454101010131702c107200380d0704054050b061101c50945520015002030400454042050003180d030b903100107881e034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 723513794 1250 723512544 723512549
    0xe1008130321060605090111010b1c080909130c05030d050f0a0306050a1d0a0203040f030503070e03030d27050601060507051006090c090f1401080a09021203030601140301 75
    0x400014200e2030082445018990074006401e04a050402d1584079040d00302c49a0b54824004110040390880080d81c100b82601c50b0010100000d01621a844000822002c1c403641000442081c0702542d805014065050300e22240340134224040c141040e2180160700c00113020200d41e90005000d01061608000c583e4801c4110b2a8032800d0800c07443e0803524500d60085160481055034891707002070940c1d070350020140104881c00691540702004482428568401019440318500410500c40002e81824030212450740525100b61240c8420f0710489140740032460240d8548400700b8800034a4403140d008199100525400800ca00801c52031208103600415000e0295040b070401044040e000390003c054162050f810750b543d8503114141d030400c440311340e0800b030f1540760303130b0b032080c1c01108d42142c0c0f0340300502808103503a46600d142042c0422619a1800d10904010101000c40c0c0d58030b036190081044d6079402030012200101040000d907407508122041c0f400940243d00380b881801c0c140084905 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 723515044 1250 723513794 723513811
    0x30c1406090405090a0219080c0415090c09031401050a05070c0b01170313080102090f060459181b150310030c06030b1e03010b030304060e1008 63
    0x4051403041088014500113003090418000c02d01c0c3d0301c005079104610b030340346280e4043c09060000d061080c61131502d11514030050141b4a01264225144941101a0111000040042020035840100301e880c0030f207640c4000d1005011540001d4000010b400c00741c80341c1c084402c2000596504403040320303080100c02c0040d14140700d00c030040c088002c01800b003207203020850046920b84000c2c41d0b00b0000c4c040c02a0b00420050754040303903040051410102051004004860241c2890b06006100040c0006d1242020110440c0440d0105044048a05d06145150715680546c4440942d84169000c18143c110a401741002c80c0080c03044410b1080008580c0880d01c01000251a008480703e1091058280d107680100d10b80029901c040140001354441c1075a081824409441d510b003034015840e05412a00c24103041a0b00da13030590711051030782607080f0280072001850b0300396034020a0050144889954050000280107e41e43c5d0b01b103450b05030a2a405c0c2c40c010316a8008400c202c0c0c1d080c02c1914150b030f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 723516294 1250 723515044 723515047
    0x201090308150f0f0303041214070506030603032b0612020a1a07060e03190c0c0501080c0a0309030e06040b12160f050315090f040506070f021c0201090219030c1406 72
    0x1c0f0213044c0340e40380e00211003029003100d00c1d10fa01c8440d54030100d480540f08407140b00c144100041201d2091001c07400400054030304a0031030800d0000a034903030080c0301c11601d042e4501000c10385440010786c0080c840100514042100b2502e40340e04d441c044d0208001603011302d0140000140044d1b801c1101c100c1c1141c00b08030305040c901c29564040182c03074030301804c0c4510b102c02d11410011800c800c99030041d1841c552244a411003442c40c00b00c40440c00e540c0000d06001e4004100075400c02c0920071555050614940015060b010f40340c00c2d1042d24a803034040e90000400b04010480e0b9480710000e0944158000c1c024103140d840c4152000c1c42d510403c4500005034812000407444c0d8010005183c00240741e4014194014209000c107042d42d804903915062008107005100c280102480015081341d01031400401c100d1020034042e542d4501000d500e80c946142c0000b40c1d01c1c184c801c0d407060783c18507402051015450911400e05070a28075a000680e000c0d140c109000607c501031140317a04c00054040e180c076 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 723517544 1250 723516294 723516319
    0x513080a0e0609041a090115051b1c02010e07050d20060c0307110112050610080702010204032f030a15020d0603020d0b0414011503020d06020c0d020109030815 70
    0x8aa0086200d41d4180d00000244840c41c190b40c2c0e24041d8103502c810516503a41101022000c0000310001079205d45510488100040c05a5034820304650140d1030350201010302c200d00f54130b0140f4200c141c485188140801520245a59906400010158258100711180592120100000c01403000710081c465030300c40400140d481240721150812100040c506800c10506020300c909641c0709450488403845020300c03000c010340e048100f503101001421070402c00b500e4410b01149010070415000020701c01231000040d6407a01c00d40443e4040d5500ca0324101c01d02c501185072001048982d224180002950b4039400201d080014908900c203030008161844400c0c030104600c02036201505031601261510000700143c2c0350b0b002041521841041c181d01240f074503080040c03244408900410309641000140d00304070ba03a21a280c0262601281c00c03074643d0300c651411034000c0c42079007224102c41c040c2c08004241d0300e4040d0f101a803030300d000f030700c86225a81d2805420501c500c0006107007507000701c403501c030b1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 723518794 1250 723517544 723517547
    0x60206040b0601030914101a06090d06020903030a02071a0c070909050a0b072f120903150103030c06240314071a091801030506061c12120513080a 64
    0x11034210320181000030300458a0381ba400c0da003e40b00c40209100740c1c0049036141d1411070b0351094041d0b070544082c085001d40d0a0300000b40c2070344546100d0903c00c080480700c000031701496034111118070704010210b03070369840b10780c1003e900c840c014865015410910400302d80c0005502088940804200c2c01800030241090300b0000140000002555203100d050102c100092200040d01d026002c25280c0f21040440b50040104e0385800111a122501e01c0d400070071344219001810082d0701880c140c4c0683c44112200110740342c10302d800c0d00a10307041500800002496048980c50072040d01881d414070116001c040042005030000980f00c102034000c010410100788195101603100c9002000d6407400703942d4268004650382803252008100400260f480e01c2860300d800c6941503502d4030340380e0740c4540d80b541e19080d44840e4020000740c080c4619045130301d064507140005041032a84000d00f907600c1207442800130180003a40403076004a519060110301030035200c04c841120340da40061690301e8140000c80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 723520044 1250 723518794 723518813
    0x70201091a0c03131401021203070f030228110316020f01230406020c0301050105180402031e0c0a1d070f020106080718060608100b0f0418060504110406020604 70
    0x30001e000800c180520a041c041c03e0004085140c41c400c801c104950401803402000e5411410041c195401041d542c0c2501d40c1583c1600d52148117800d0801d164222a0020b40107881100c0d08220b45900044000c003450704802c501c2c0b142142140d480f100c1d600b1840c1b011035501d200712040d2072021000840510018986045109a0440c0600d00003000e45000c5400302c0c0e040e45c030b110514200d0480400d00b405000c0d030400038007803c3d1004600034002549480b01140d80080708070402408141c006001070295102003141102c00d94008464400030149561016140c5c40007030450307880b401b4024000210f07000f901941c40c1c7c42040c1d010b501e0000d034960060544e240304140c0101020b6541355180080c404400780701c070200904403010000701d08008a010305089410300d81001c010b0001240a0188060200b00754070700f6103450025141d034516030705582e1001030013280d1001030400b04001031a2098a1030f904141e040302c0099070148400802c01220103e00d002d039014050042e03000b14005404190302e0b24 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 723521294 1250 723520044 723520079
    0x506011404020f030f0415020a12020904090c080102030f010e0403050313140a0f15020c190206070c03111e010e0d260a0e1c031101060504051e010b07020109 69
    0x104010314205194035080f007250000c640300c0c001010b90700c0404c410312860304511000602d00380411071814851200c054040315403401040c100a07800315078015140c4407507120a500640104613071000c6c40c0e4420445010b0b43c0101d07000b040c07a5280400000c0c0c3c0000015209019071741c55180e00c0d0455880151b11200040ca505094988801c0b03c00606030342c403c1407103401e0f1054000e50714000c0d80309040c14407215010105040d40440352040082d41061040403a0174841c400c00c0c49103940c045029400011010f0144407005400080e29200c00410090700d106520315a15064403030400050074040d86441e403407010100c050114882910552141c40c09001a100320752080c15014210100303580030400507c1c42e904010390342c0c04001102003c0c203410119a2180141c03c03500c50941014000d8110070002d19100010103004480380c44030749440302074000c200500805002004985030610b07142c00000f00319048190850301c030400220704540e050089a2881c1d0701038643c070303039139910b440c8408200000a0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 723522544 1250 723521294 723521299
    0x703030c061e06080a02030c061920010213051306140d020a09091101021504050a020603090f12090f0a120b2805010303030b01050703140c120c07060e090405060114 72
    0x907200c0c030b215210984149005080080c0041515034942d10500d03191207401d4503420f00c02c0c03005000c2c00102c4a4000017192070039402c0e00e001000d0a04440c20002c0a04945051414170f500108070102c80c01031104081d400c0300c00c203ca0001c002007503122140100c95250180c801c1d240c45030401d40e00f00d03007804440680780c1f034409041c0c582803e03650380341c21040342d08a8008407034000740c1503c070300340342c0da41040348200e0840d0243c1081050b0078240d40c2c0345d581c0c03d0704040090080038088000381ca2080d05001d00d924100c420802d175004001d05d04e84400c5c09a11840a25100304240f100e8502542484620b40058800100e801c078194400b50300c400000801c002e14008510300c1c4080303449280318250040d252450103050004c40c0b1395046140280c2550f00302c0c00010304001040c840301020070740c000d1800300d030744004003140b903a44c0549001090806504e10740c2c588040c00001400407845500080000448805996641e600b10203141040060304043e60060034a900050052051910000c0d18a0154000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 723523794 1250 723522544 723522581
    0x20a0c0c0308040509010e13030e01110f060106180501050904110f0d02030618040803040221031309050105060316050a0201090f050d081510030513020603040c0609080703030c06 78
    0xa80e40d91854500650400c40710100e02140c108071a052100703800340584805507401c03c0c14035166a0000b040c001c0014083c0806c80540301721070860340514148601c0c03066102c00d955400e1150440345541f10420f104d004c000034101801040307690516800c0100b6510142e5480b803804141c08108400303492240d42005e950502008810000c85508004110ba82d0803000c0240e160302e044000c120010b00da240070210000e9083d01044002034518040700e03400340e41241d8004480900d5165201618100340e00550a0301c0000742c1080805c064441172811109122420f0141e0380e25602404450300040c3c03813042c501d00072500d54040d0341d4029809808030b940d1510000034140d40c1611181c54040c2e400d00700783d0b001c1d0051a2011100d1303600c0981c1340e6018000040129031129214042106034400303010040400d0f6407240070458403649082ca000309690000c1c8007540340c0c140f40c10003031054071030f520039a00070400c400d0740001d080c0340105000c011207425488100303d1456a4072810050400c802c41c00e24403080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 723525044 1250 723523794 723523817
    0x60402040801180311060609130507180e1e030a1d040c050904150605041203020f010507110712020901140f12100b09040507050d030507120e090105041b03020a 70
    0x9116501000141088040b000003544c1000744c84581141c54803045a0407203020440c050321a0000c0607001089540309100c02d95044c2016400c1c245d070780e00b1101680d4031070690150038000b45c1e0002c444003611780c416540c0d00401101d0341c0e1150710010103440490b4200b807041800ca5400741142d520f01c05c0608003004054040c2030006000c90b0704509122012401c08104020b0034109840f40401c03000340090340c003032a9814a05c1c050910f00652181104118100c81c240081504c20701010034203003c207400074800ca0500d40409016085068031803011031090090000714010401c10100c035990f0081c0001380282d08242c000c15411615081c01904100d200f51085403940f5000c0d08001e4808a00010f020841b1050140d002500c0d40307041914883e078011420301020034008940e080855a084a1075400704459180c2070718540900769002d00706000440e2484070158020704021010368080780c4482407681c9070f03c2008100c8d8103010486080034810792010002501035402442803a5042c1000e111545 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 723526294 1250 723525044 723525059
    0x9100b0319030c030909020c0c040f0204120c030501051003170a030b0d05010510081618150308040305102a0509030f01020c1b130209040213090207021f0e0906040204 73
    0x18848002c07000500c621840c0b41c18140c0c007000d501c001d400507840561414111440490755081d080145520031070380c0d80003880300c01000e90304480050414404507083d0300c1c3e0350f0a160304079202e1f503c0140c0f01942130200007007030040f41d95418000d4950011000040350076010785150030350801080d06050540d244000965030f034030714804001e118800d10000c21507280c948000c02c10b10405900810b0160301c9244424070018803060b80c0010f6030101c0101c051940c000420400207442c207075581c1c0100d88400b903008024452410000d00583e4003c5040310400041400440110f51701c1c150942200d890b404890001c51150011800412201d4501a400c24a04000290421307204002c840340d1a0343c0001e40c41064482401007805104503025240182c0d41448003007400c0c2c048580c028100d0300d50001e5107101a941d00c1d4191a001d0810300e1070140d500380c581020200a40c482c00041c1d21606281101540039034401507050b1200340d8682ea506c5071401c0c56001e00490303250291106900030303000c7c0310208150 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 723527544 1250 723526294 723526333
    0xb06040b0705071d04060b0114070602030a021e12060306041e050a0501020a03060306061202030d110a060213180b030709020d09060203160807020303070818031b0709060e09100b03 79
    0x84104603511044d900f41480c3c00d800300c61044c502c16040c050003801039400918803000761100d00750010b4006d60fa076070359002150300901c40d5610034000e81002d206940d00e003602050103030510b803100340c0314451142c82e40c4007010344e00e15040310001c14141c4209100600c0912a00c2d2300c1030880c0c41041241c2c1d8404141e031b5200d0036030708650040b0000a542d0313001041031100d5805000b005201ca86103200700c804958000c00d0711842c1031b8101c2028030503c2100107004440c10021400c540f50008000c54a680200300002d03c4445d0170b1240c44102283c40000500300056842090041c0030b000340100843c519149000010b900201f143c0a00251744400b8000454298001940f01d049010104a242c5a444a0281c05144050030381c5046601c148100407211b0780040c14140c002c10744100c95903480030072b4400c0b18518030803232007501241d82001141c1d801000002030700301c0c01c0d50481e40061004603110f02e071403c40b0304404c6400d941c103580108094101132405606c82c03904400702409540505d0070004a14929 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 723528794 1250 723527544 723527579
    0x1030e0c0d150c0c05120306030f060901090c090c0c0201030e0102040b030a0203010503120307020a030c140307060b090a0b0108010527160f030c020c09270c03100b06040b070507 78
    0x1103880a604241d100d03142d4441c0303d0301c245642c180381140c15403607115107682e445004000c0004880c0040800c03015a01006043c02454400d812282145480071032980078102040d0221240ca04080010902202c5030240d03000f442200d0f0b1b42d039040c1204a03001100600001c50008000c0d5600300404a01241e85000440c450441000050303544e5143c001132615203000d09802d69030007038052040c442803580c085246a156900b52038040c01c1d0b40c0460601b44903005528813010020701c0001000804c00555803c01c51251000700c88218042d035458082c10309036103140320b120b400560707443d0061040c0c0c0760082d0342c0e45080c1444c40e8000c108600d884003c10042000762a803c4000c0d100364a4080869840106a0030126043c5003d004200321041c0181d551182407618a01c110380c29800204074000d0040e825044402d40d10514146039034501d007064a42e04a0030aa030302a0260b030210500800c01801460380c019005020146814900400c942d040d80090100719140c0c000e4100008481c800c00c4a0300c0388 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 723530044 1250 723528794 723528803
    0x403091203020a05060604140114011b2909150a060b0403141b0901030809030c04050709061106011a0d02190306060e0301090c050d020f0a0308220e0601030e0c0d 71
    0x3103d526080030383c03030304d6001011a41716a0038038070345e8000e010300b8800c2d1324110344207502d09103100c403140390040c1c074245440e9001a0f041d03000800b90400b0b2041c4401120f2410044045a0032542c40b201008412401c00700d46e640384680c4541c0003540c003117840d11501c0d984881c40090015505480d0001212592300541c42554600380300703400c820b06100c1c1403041e54460304035010180081440040410401c080500c40074061080220b540825505c00340054050218024800c1090703103001c03000900303032410314017403c00002c0e006200c0c917010000028140d070580707060000d840001d01c1154046a4154803040044c2c800305c0d02400307500c8644c4108104d0079601c90403074070040781d05d174181100140489a1038000c944a607051900b10000b29000c01082c0040c1c2d8002c0d241c0300c44210172400800d03e0402c440c04560740000c549d540002c140210710010b000191021035100303d80e461008006c505111090060000740410348001c2190341d030107540441405501d403010354094110040c0007401c1c0d05988a02942c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 723531294 1250 723530044 723530053
    0x50d0302010204030515041109040302240a0b011d040509100515041a0d0201260a020c06180616090b030718060311073c030201050105100f0305040309120302 69
    0x20800030309204400c40440c00709441b452034035158903200c1d02d8840920a16001b0240c01c40410107040c420300c4402d16480c140500406100f2915010010b5075000301c5201011504e02164050f40b98070920001c044140d190040c5204001302303401b008024140903001050f04c3c45449480e440003840750040d0340c454911421100502000c1d002480103488a40102180003055403044040d00e698007a0712240254080c6841100490700480c403c80c03841140c444402d8041c4058200112020725400511520307551406803103503600c0d19600f01b0b401002c0180750060365000000060800c9011038040c1c07603140650701e049100f0554170103000340207500507100800011004101c905220a07508001030007401d4503d410803a02c00e090010f0525406441402000c80034401d4028680044a0490320b134465400340c004002c0c4a03290160440302070b40d10034200e0141d4206400040d2a20f04102c41c000d224181e510b1360384040340c0101c001c034010701e0300a10803000c4c48080d400110341e5001018464203100d110750002d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 723532544 1250 723531294 723531299
    0x50102031201170a17030a11070308040b09011d01270803070503090a0b01170c0307080c041a15130b120a0f0e070f0513060f0b0a03140f040b0f0403081906050d0302010204 75
    0x5000b84c23003c40a10818580c4c04100f6000040c0e440b1180701e6100350080c25060390754442904050241080c40c40c0c038600100507c03041d9021100641c071841c0007043e005103d070070300003401030b143c1820006154090100d80b070a00000742c041e400b802c000d603030100340b043c1540d810000907070710804450001e03044448104861100100c045c0800c000305102044210001c010251800001d15a60421460740700c0c0100c0e1108105510111400042c0d111000020100c20010109031903911540d002032900c17140141d02440e000803000034060807240000400b100485555031400303c00406008802001c40da405e94a51314031110810900c19200908100115805071034609401c0119030202c60955000840c6400401c01501d0144981803045a408250007500c03819200c900b50003e00407840451041c011000c104042c40d0100301d1130381d00c202c1c82540c0f1080140c940d014404061201140e00601240d11070300480c84031080044c3c0300c006223120780000701c0c0c00d5407a20040380035024466004c5000d80e4000c9801e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 723533794 1250 723532544 723532561
    0xf180f090804080f010509072105060103060509100b011202090f090c180604050a032603070f0f022a060c070b0702010305131101050d0b121006050102031201170a1703 73
    0x24450340f04014000e01c02030811f038102c55144c4140b03120f9a040c41c00c1d0015240d851001403241160700702d0b0060142d440c1503035a42000e6000d072000b203400660500480003103280342c01261050095a03039041e52000d01c54101500307075030020340c0b06003d0260303c5080624071603416504c48243c6440b4880c072100303154907404104036042000c4c11040f002d51003404188018071464072000e0310202180d400c48042c0c508000358403084030310303940c80340811a11a100042009809604108036641c9484103943d601d040340c1c2503407070403600d4041050070b018402c0340000100d0700c4d5800c1d078038400d00351800044c10185059002d0a60510380401503116907180070707001c55050155a0035200301a400500d1070035035640904103607547e04442c0c089e01c20030390620101090100184515500810700940c014148840786074145008582d03d07070000741c0f4650781c00c1c20807101068951001c0300303543d030450070640303900d440da4200f00304880750890110342002c5521604c41c0c010041000d02c14032103010034950341420b41c5c03400c01840 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 723535044 1250 723533794 723533803
    0xc020c090604060803070b0a090210030516110303070804060b100c0b010b0a05030c07031b08072003100e0a05121305010903150e010603080a051809010f180f09080408 73
    0x5003502c500c1ca029000c02c1104004800c5860241d840700003800e243c0d0300e548501c1e00505142c080650011314900c1d0860b21150140d1050f805906c54020b1350f01c3e02101003001321003800845180d50841c0c2c0051001c5510580110035054001d4403506003c50311212880205242901c44040e820003e10310710841014030401034002030140031030801032450034144501c09811444043c3c080c0c0460040019240d080c94030130500c0c0302e9401c001c0c9a000c106240340b4286901e96400200c419100c880e50340c000c507109003a0505030781d20600b00190140c0242c00c10f1101040007003125503055000d5020788180301000401c1805620403195012a026845000602e5080300032422504141d05002a010080c404500c0c250b646402c1d90300104000300302c94001c00860381c0588280d03840105952804141140101d402901501c0c502c6d08001e0701e042d900180c0c108011908100f0b106504403443d0340d400c01e1044a1028452550550400300042588180f00faa0070003207801e4218241e07465280820244203000084c003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 723536294 1250 723535044 723535051
    0xc0f02031e2506051e120a020703020c040b0307180f11040f0803040303020304090e2d0d030603080904150b132102010806240c071a19120f0c020c09 65
    0x2040d0b803a282040809406032190460180c021208110403d41c60042801122413040031044842a18200303241814082d4004a00403000b6001d54010b00d003085c1030a10459000700300042c0203004483c074100030507181d100a8204108440e40742c0c51885801e400a00440150281d00360400d40c0c1c0300c0c98803800d12200724040d0403401c01034104100420200b1340c0041507070b056070001c03c0c1c005a081752034000b0030315081c1003688408a5105802d80c804240b000c0160540550680300e0a8030008600c00008808540fa1400001d1440728103122800d04ca04169100840c22a100100090b0700c60f120b002c0c07404035401c42c040001580310381000521000b80c40d551884042e003400e1105c8802c05c403056002030569103004000034020316032021300100ba040b8800840404400092025540340c100d102d00c15101c031154000c0282e000400d000215045410f28200c800d2824101d160894981082c20b040f5080d0b408100e54145c0d4a031251101c49000b02c452094580200c85074008084102003502441451100117 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 723537544 1250 723536294 723536353
    0x80705030108070b0a0905090901060f050301060509130507051f09092a090b0f040f0602030306010219050c13020c010b031612050a210801090c0c0f02031e 68
    0x50004101102c8000380c1d40f0180c0704804501c4e42c0b1000402d00881d9010460750056038084a50010320940030019400300099580710480800c41c2500c0d081414203036071b2940b05450304894580e001a404884011142c106117100c3c0c000d841920b60b41d500040c44d03140c22006007a800e0240d29030f20401450304440f043c0f0060101201c140400b6205a407040300564569591241c0060390540600303101c0e100394040b401130480e00e8046500d4503a195803101040d0003c0c010741c105482c4440020500b035000000f40c03841008140d00809003203494108071001c03d9001c2c03038126400d10030340030041002c3c0d850100c505804115400f005844c0d07664014551300751590341301814001d800c044042c0740d107460340c8502e50701035412554045082d0203c5140c2103251200c0d40c40060302003d05a0800403100c400883c00f28400c545a0b0703140519a602c81e8226000c85802c003000c10f0214030500703010800641035000428802d40010203403000313a260000902d5402145059207401500034214100070402c1810319407910722044c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 723538794 1250 723537544 723537547
    0xf070209040c0e070f0c030503040c030c0b0a0e0f0303092106040f060b01080907171005160f0f0e040c050d05190c020a0203030d0b0621160c0209010608070e1f080705 73
    0x72503030107003072104901401fa00304540000080c0c00d00612000d05070045504c0704210702d81075529403410300ba60304044e200200041522000c0c101c5454000050780e0480b81c0103024500c1c1201c460708002c18068811007072103031820242c80c04030411000b4850603101e180500503c15132220a0301d0090b04950549007818188889441800040100040c2c1c2605581511200203010303c1981c1e0801e1800e5050034840e0307069401c060400c0707180001041c5e020b2001c04152070b01d0902504c400400c0e5074018207010401b0000707075103428000705131500ea04107203180051420024034103c001030141c4c0a94108aa41c03240503c1c030345c0c55058441d10240f01e04000303264544042c210b40d80e402c0e0300080c0c0364490407004904241c1c0300c480c024005d907603213401c0f6001d4a00d01402c00c51200402003a50340c0c0b052086812804008490b03208070039a50061a44154081d4010000a02c581c2420000d0380d034004064026003c10901008410280d03d60400200340314140c0380e144108283d40c1c040040c1154070007003641081000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 723540044 1250 723538794 723538817
    0x6080901150510030902030a05030702040c02031905130305060411030d022406040b10082401050912100218030d0c0308160c1502030f0a0c09030201050f070209040c0e07 74
    0x1070040c0c03080c096a10449109050340005403044010302140d42c4040d616000340d142d00c0c420000000010504280309550034051100d43c10801e9031203009048403909020152180714040722300c281e0040400407192a01c00c42c8458503900d4992034000220b40440d442907600005555515007001003400341c506d54401490000c001448007101110a0182044564403800206005550b260800110041c020b070905608802041008158200945802500d801c10301020075161511244408800a06840703080ca4880c1d050180841c020405181401c0c074050784032056403142c80c07030000b0020500e0072178241e00c40c80004020507003814400403610041c0300001c407503000026045a0040c0d4001e0401c1001c54031611800e406681205862200802d4000e803410215203c0364a41e003d1401013088038154003242e80c44610b01d0f400c0310507004124002c514210300400045d8400d0006290f83c0181000d0b050414440b40c0c04035158000035902150a807035010014003048942019555220600740f414010040b0f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 723541294 1250 723540044 723540071
    0x7020f15090c1207053001050c040605031e100305060a051015140304060903081b0f090118170d03090f0807080c0607081605180f030a05060a020406080901 68
    0x20030a0300b14500441c11000c01810103481441250000c0c50060080c800340c12440d044050342041081d00301c016a0301c060009045003805108940c0300d6030740395140903c0c0509003001034074185c00c0101083c04001c04100c41802c5200a00c500ca4000c22004418411060561070200d041900003841603c0c02407a000401c095409240e6986086400d201c0b030000c2020301817001100c40b00031201010703000d05070001c24802000480c0e4040e00910303000380c0e203800c41601d90024140c40c102d145540c1c4c0540b0340081c408400c801c85010f00174010130405040c00d501d4601031a9070202c460080b9031000c9501c80e82918080500c11050014144102d024901000300c00c100d555a02c030000c24008014000c4100400c41104128075034003224151a121030490b00d003450508001031046000b11810304c9003c251580f030210040c05034055800242c820281c1d8503110107c20709000034041a80d04a41d818411072070b0500101d5000d1060501910740c103040980c3d40c0742130580c09080032402410b0f1403d103078074000e94a9000c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 723542544 1250 723541294 723541303
    0x803031b0906030106030b0d050601290306010c1b050d14191e23060403091406190203070f320a231603020415120f020a09020307020f1509 61
    0x100c00e60b09001070507c0c1c51b0004500f4041e0b66050007032561156000100e00044140100702d44200070014130340b40a10361041c20300e668002621500d0205010000f10300016071b00c00300850244a03134102c122140ca6903800012000160081c00381e41000d840d911640c080c41c0b042c4031700118160002035005a180c140e541d0303c8072810101424501e1201e00d0000303d0104040e485102e0074000880d0100c0103480b402c80b80007515035005590460100b1008100010040c2c1322a00e05031074440700421060900355030005800c1078401c4941d1800c11400308001c840000703030703519003690300640c0100c200c01802c0c4180180c00e941b090342e0808001c140c16030b042070011031800004820314500c0d03100700039410605860360b84404c040748840403104d19011b00d01000e1000700c49114040102ca008840038040c17811a5299603a0b0380d105400b6aa105142d41c541700e6020840e12240d42601d02d06c081d04000580d81c0d80c0c241780c8200e1f081555441d0068001032a10b12a00a01300406e840c80780030f841c03e1041030700784411400c0d9103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 723543794 1250 723542544 723542549
    0x12210402090f1f0b1b071409100b130e0f01150302090307180b030c0a320414040203210405040b01021204030b06181e0a0e070803031b09060301 63
    0xc0d08807000151410000308904038040f031081c02e14481d120380390031660405801004600745288800030b268090b903540005c803441100c1c1810380e04c40d1070009401c1030024a03c80100740d01540781c00c407480003443c0743c0460700409107050701c4a914004541041c1d5140d00d00000501014012b00d01c0f40c0044c001d448440003074501409150800503070354005080030908003034455002200000200403403480032103071600010305404080b01642e0741400b4041c00c1000c072807010b0140c10b070703084058240100312071800b59006922407020101030042095480000303040c1c541a038043c000e0301840f0782c240030450070208010f00b4040c01d070700042a100c0360303900c4503404180640c0c030400e40b0858840820b4010b41e4020b100c020342c003180c022210b0765601e031a410f10301c1d9544400d441c100c1c040c03101c01c603a42c200000c0c03501c002c40c010300840c081c0313006018040c03050109915025201c0100c007aa0303030985d030004940c100910710080c081da801640d141d10300107060403210104040f20990104041000801542d9070001b12810f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 723545044 1250 723543794 723543811
    0x3042403090503032d070503180304120201081e0c0406030f020702030c010e061b0f0d021f0506061207020f100b090402120a080d0e0732060c1221040209 67
    0x20fa21030980b54240c3d000ca8a249000105c2104003444041031b445070003035200e448540ba0303085440d45040b00032940d910643c481c240c0c008a0040d0300500540c85510a290050005881c4103100e003000801b4814800050380d07000620701000408100c1e194041c01401b548640307841c3c0440c00c1034050b0300400c0e20b441143e0046410407161000504031a035903007007034070713180140c010b03c81d0902c800c0007815070b13600e4031740d121803c109104800c2c580414038800a189102141d4024400c464040c044800f500900005004554440c2d400c0c0080c602e1070010308100c40c45810b41d54000c2030110f040795021410003412000f2400003d00702040031300c9a4a98202d120340040e816501c0c000d01d161804c844034240241104014409070000424102c031050540109009410340000d44080740d0703580721482002500c009504510142038641a880905041c0040d0b075640f0002e0041850204c500803400d041501007183c1010b41c41011801c1e0300d2404c40400a41c507a42030306900051035091a4002031802d01c4020001031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 723546294 1250 723545044 723545071
    0x705070e0f16021e010204030b0c03090a14031908070f03061a07140a0b10050108040b01090b040b0307090606030b0343030b091b0609130e0304240309050303 69
    0xc0c54a10130000568680c90b00040e00c42031040c041e00c000c4c044d52081c401940c0003540c89010941d456941c0040360300070182d1134010b01c0e040000f50307a61080c2e9192a09080d410780014031003801c02c14159901c10345420391543d161680d502c0c103082b010700b82000c8103640300c0803d0310302181031260103007442040c0200070004020780d8803451180740c881109041c40b40b601005000300c0909030100140c907101c050080c1301690301406081d0301c5800448964004a40140181608d0401001060345a034801c3d07070001405400403400c0200007003c0791918019600c00884075540c0c0c0010013020b603251040405c00380c8100c0141200e0000c59070302e418000781d41d0401c4212070010b00803450704103100e8620002a034003034900c0c0c01042c40d624142081c1085086400348080e0060000300e010350020780045c0e1540201c020040c03818203040c8424040000d59488040314042d589900c00c001c440010000750005101038400c980800d0940000c104910045045060500d8200000072000070300c0401a079501c42221143e96 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 723547544 1250 723546294 723546331
    0x3020f0105090a210b090c03060f0c091206010906050406120803190f050f06010302070f1e1a04050120070f020f1807091e0b0307020f120705070e0f 65
    0x60908100350700c00c02e1880c40303084d8080702d00e4151254039000c0300c0c0030700c009a09503502c4150341621400b5900314070740d040d0060400100908951840d003178200496110a604000b030040100303005101c0a24030300c40550086004206092a0307000740c0c0054101501c06100862403d0f8412401000046d0700819400d404400605101c42010700010136015118040c001005500380c1c2000600041d41c10082d001e41e0100040d0a550080c0202d5400703507842141e100c1c0b17181d00b545461000115107005400540c031540703074000125402c4007196411a0b4a8041c1501e10f0604d890441d084500d080100c10708521010ba00700580d2140c02e09403880c0d2a0810141428412948005070b55030f0703480201103500c030340da6284003124030728540304c26407140d000c9442c1d101c80d06403129140003020200302c500603201e200d021818050380c2c1c0303030707501854020307180d80112851030307003054060b9080c200c03881941c029070074010903603509103d800c1040c80001c14032500e81c1c800318207024841e05486100140000d24003007090100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 723548794 1250 723547544 723547549
    0x712020a020a09091506150c050c0a060201140f010b04090c020705100e12030c2e05090d1404060c060902121f0f050601171302060304030f110703020f010509 69
    0x1000e054981c002e010550150316450303c0340040080780c2d01900d440511926100740c1520a2054205403280d2070707206034001c003982c1d03000c40300f10010400440c0d2501030488022081c2c0ca0f01d05410700503051640002c204802c400b01401454100144818402c20520b0010020340809000319000c0d501c5503000407843d851109000e0f468140c0c03d50005410240d40b4001c080c003154801c240c2800d50100f21104a409102c0c4040c0c140c0d80c0c003466001511903000f180c41c00540c0078000d111100c9403045003100715803000403400c5070b070300711442203890b458a40c04c191802e8443c43d91200b40c0403222010009181c2c02d040c01c01000410200d0210340040106507580c0018080d50f40d0b500d04030031131040c554110780d5440d840e03000518480d81d20845942c42207041880d0300740603840b64081d0603c10441a56040742032000c0c0031380c1c42e441103009000d4141c00c100e0b610030240543c54420045100314044d80b60550300c0340b50000002c00c1c0912030048081190418242440182e681170402c42101d80c0c24a811134454035000b00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 723550044 1250 723548794 723548803
    0x90816060b33040806100501020d0f0801090f0e01060b190c03140304021201060b0c010c08061810030503070501020310081b04020a0e030102040f06030e062809020402070c0302091b071202 82
    0x40b51010384030303080c20440d441e006c1040540a40360281d003a98040a289801600d04491140489002c078003000014070207045a0b500c182551071081c40d001c40c0355900c80484600b150340e0394101c40742800d00029001c0ea04265151100c0c02d01e005807401d00c02150703041d200201103001c0381e40507030f001120020101e829591001c29a0581045140080003c1c0d59113207529407156000c1f1460011079400c1c4112000c0b11401034000e0382c86000302904408554101501d041e0342d21034000c141050700100c8050120105104102502145115500041e62414545011007900703005521900460b400342000b9a60144500850400a04207036400341e205c2011078020345071510b50300141605503102290002d04000e242101c00d0496540c0d0710100113410341e40c0156034440d24211a00700110f060791000304214402031802c035542491105000550101c1e650008040ea4050041601d10500900c82031013989801405030390041c0d00c229102c50140c450150031100c5014403880a0509010304545001c118000e00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 723551294 1250 723550044 723550049
    0x50402010309120f020705030a201906020705090105060408100c2006191103160306030c12050c03060106020d050325021c0206010605070f06090816060b3304 69
    0x80c3c001d40004402800108a1045031480d1001481382c040001100d0801294105040350008ac40c44ca0030340c41d44810050010350111455041082140140d4400c044c84058001074070b01a4084c0c22820702d0001002180350068001a1084100b00400c0054100002c2c5e45910b8240500011803964140b080940f111101000c50380c00e170344c12030500703001d1407800400d030148100c505400d00b8488800c0ca150341000c817141c104040480c5101040400c0c3c450000d002d01114143e0585408120380da03c0b65140c440c0342078a0703880f20b20700902d400c4448c1c3c10010188070204a480060b0018210703503240160095842c946094a44180000040803c0e02d41c41e85004c3c044c40d511142d10084200940c00c00300135a100302d544844c0c04404008103540300003620116996040341da0035540c003401c090543d101c06c101c3d038000c1c420407909550b41d06a210300145810014000c240151100000e0a1420b401c000c030070380b808030700068031a5512154200300902100d031a00380510004269080c0f114107082402030078412138 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 723552544 1250 723551294 723551303
    0x4050d1103070605120c2a03210115020d050409090c050a061715010507200301150f0812071202031c0b040b060c1e010b130504020a0e040b0604050402010309 69
    0x810011903000c1c0c0100080c01d4107480b1751580c504960f14040300007031500030781d0410f02c85034428040301c280c018a400c401d940d03240c0400098a2034034442a92400710341d400107004d2404007100c40010064100f628103030443e044821300152480e0185440000c040e0700c524028481e0183c2e40d1443c0d042840080c0c003030140a4140604250340c00c60303c0b14400303400524120002c046011021001940ea0700c201b03500f250b0000c2061b11a00d0034981315035181c5410780c5d031040c0e00340800ca4282094601c0d40d5000d0245980700444003e159206c1420101c040107050803a80005a15a208441078201882c001c0210755845030021010442d44004207801c034150b100c1c1030800c919050b007800c1a1282c60704194840300e4881c10845042100c0c10b500003d0180700d0240404401e0ba940043c40c104101c06030348151015001c10315000002ca12515000041d01a412070340d41030812036546081008500300000040003411001d202c0d410035140a640c1c1424070000144070f640071301e0b101c074081003c590007600840203141e0f00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 723553794 1250 723552544 723552553
    0x82a0c01091401020d11040602060c030c0c1603050d030e03030c090f09100504050105090103020d02130b0604060908010c05070512070f080c0307150213030b0612030f031006050f04050d1103 83
    0x3103040b0b030103034000510341d1004610300395210000030802e9080720107c402e25000303130100c0e0f0b80f0a00e00c100c06401c020031280c092a010444440c941e10240640c0810680d1000c01c200520306604140703107031440c41115030081c18a00342c4007e80c4188008203803035214034400c10240d541d03480440803502198404101542222401c418404022100c002d1340b81600c0050304c0410503a0380c0d52003006003000e0203100c00b03500700e812804500c0c00360030f02d402010801420030401280030200c080210b050355119501c0000040d80c202c409108034403081c0a504154160ba141540c20300103113490310b42e1181c2044001350f1a825000030500b08010078400c5004d070442d001181c1c141c503980c2d0044d0f15522548140e44c1110a20f0b42550800c0d031b003403070700d200380c502d103074000a1055841400d5645a8041d4540034088a9000702c5403882e044080004000400f180b08001c45204e4803424602c14081c9000c0440d00300d50b042c441d052154030456542001030320100d40040f14407805040050420303014085200c8050354141c0038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 723555044 1250 723553794 723553823
    0x1003080c01061509150c030f0e1f031a040e07060c05190606090507080103030813020d380601080412030f09060c09050405160f050c011b082a0c0109 65
    0x104071043c0704c1110580084400d02c00351041003140d8954401100074040350503c8801144039202d0388600c600150068404590b50007101c2c80d0f60500e0a40f010580c2c00a45c03140d0040090100c4115224901030068a050151040d48546940c40303804501480c000c10410b040c4600900504011440711000341c8003c00d1010b14407400c0c42000b40081e402182450303400c1ca400b00e10303614411401c40e4101d94155890b1400340e140d1400304400004184000c2e40d0003000002c00c0c1001c980c5030305a0016510241c560b002c100c3c010303503071826400321403881c08150a80c01142040460b03604032103120303407090303000700b4a1000c0c0d50030740c0c010382c001c158401803419182e250584150812815600000c5421187c2c0c8407284260b0b030301c80c10403003521022500d10522200741000c14031458000c080c0080380c940340e41005070500f86060038540c01c44403a0260300004000f000d281101d400d400c03044030354100c1d1444118200c081c3c2035050180040b240702d5943c50036120002140340c0314403003e6008170790203a40400f55000e80344 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 723556294 1250 723555044 723555047
    0x605060708070f1a0403090605131a070209010f0e010f0e0403031d0303130606090902031e030f1c05060603090a0b060604090c0809010501080109020907050a180602030c0606091003080c010615 84
    0x507005c5a0480110f84241404201d450051043d154a016444010b45c1d189042c061041c180501c0c0c11928900c2010078001f040050362013000340c84c00391100c200f10340b454030315001012507041d8042c1c0c4000c488003002c0b1010301600c8100700c00b242e4440d405040c0403941500c24941c49080d0f8042d080240c07450b000c04414402d1001d10030700240d104601820b02444100c0c1ca5005203002c464852000035803690082d0030252401c10300c804078680c1580404282c90409400000f150742d554060840c0070300c4c1244000700c00c40380310300d6841034982240090b1109400c600c1c0201d0a0307030b45c81820160207013182c000c03000040d0960342e03200304031005011120010b2090400c0751034050603501c429103181103554200f60010035154814400c04980c9500100056010380360050b0540c6c680d40500c88010800004441c10f801c000c601c085030f60700400541e40103596604403100200c2c108a00a8050351054051005002c1015100c030130341d205494001501c00d0792216803800c0f49005289a521410610300b820034103c0105 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 723557544 1250 723556294 723556343
    0x60f0c050c040c0305150108070203220b07030216090b0a14150d14010e100303140421020907030b0f1005070204140702070603060f06110c0909061503010605060708070f 74
    0x199240703042065010108801520540002c544040c0140d0044c042c33540d00080011000c01415a040007207ca40c54480400402030f0740b0055054001d80c0c044030034082600d2054000d20020075035001e0402c100040c0000041200d00d1a110700b0310300e8184445200c00544e07a5a04c1000c20640d68404144da482d01c2450640c0a0080d0345180c0ca8078009180001504090380d41c086482584800f040344001d9065641c2a5202c10301080903081c408010300001c1402815140c1100750440307000b10440380200188100840281c004081ca402c1500784510199142c645580c3e604403c4012500004c116040c440125498041c804010750303c20704040d50360380340a8078114081d028140769400c1e2466151a0a41541600d90b1031091001c0c914009404201040c824508428040b098100b918000d00103140000e01b95501640c4480d415002003050090809220044502c6603100b43c000740512458000050254003800c4c101034800000003802c0c0c41000884568071000580c459911070b010003c804150400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 723558794 1250 723557544 723557551
    0xe030106091a030102190305090a1a04060c0c0c0e06153009030d090311010207120f0e0135010e0405060f01050f100207151d0604060f0c050c040c0305 66
    0x441c2d1401400116410306008aa040a4901c2c0715201c5288002500710000d21006028542c00e001c1e00320a0400030b442035000e410540d846481c002030390f0819050101c210750002842e441407000c00e0303850074005907490032080202d0380e82030600c20590340d40c5130214584000441120000003000692000740015612403500e920f040c0800444881c000082c8651031510280ca030f040d49075105200255210411f070b0405581c07103210f46402e410380c859129a050030383c0c20002c01101c0300d20ba040700110100b94041107880c19016246400030f03400c450301d40064080707420100c4120702c00309101510345003030300c0007621600c0454041502ca55507607940c541035514081c056400b20b80c10b006d11404554040c20b904000c5041e0341000340000502c041d00002c1101414280315004154007441ca000114900136140c0c210380c2c50f49a8845400c14184003006104e01e9150000305881601c00b4030051101d9640101c1c14044080c150a00383d0051005051562800a0030b2060681c002d041c4100c0303005071030f41500460700 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 723560044 1250 723558794 723558821
    0x180a1d10050903040506030a0b01031112070e01050316030513020607050a030f05040b0a0c0f080301090c110f0616050d32010b1c18050c1207080c100e03010609 70
    0x102e403140318110f40c59120703c5c40350a505c80c40a00214001c46a10781c4110311005c414100007070340d040d0321480b001c01904450009191020040200a0420381209940e40084d0003443e0903443c40c0b44c0f060070400b035a40150724103410160760300005900e40001a45150009400402c2ca030340301c94241c5400c80c2c4d64000c8000840c0068844d00301000c5480c085e0044d00c1c292894400014100307500c0c81c10484a0400149007610341140e0344100e003000c501ea50000b103008e03000c0d185001c036a07071301d16000250103c040074002d43d040d0b0740000206498400d01040030703a04194401d13407034110084255030440d800c6c0201e0920340503e525010001441c0172408080d80000c0c10040202c0e04a41c1c503030041031404080902c00c400d0310b20310402080b0440500600038121521004034001005140b82040081070050f00a040360715038059440c000e81841d11422003002180541c0040c00510304007074402d5101c010405030213004d8140604160300250280c1440140203102138001c01055903281038640203422002d24100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 723561151 1107 723560044 723560051
    0x12160e1b180d050102042d06140f030c090901060c0b010b0906130b090f19050d02040207060f1505060a08040f020f03073002180a1d10 59
    0x402c03140c00b43e400144c0316824480c07034100c45a14000d000c03100c0c0100c00314030741060616440041c2641c07828034000c8100e088810704002e01c0e0040c0301aa40a010001c010850042c408502030500e02c0b404683ea0061a6603406040d65130300c0803282c1c09400c41c2c052030014407000700d05d02c0080510a0002e0022440e0003039590450310104401d420101381c64000181d41000d070325002d4070701e40a40b8001c4840013844924141004c4481c0c0403842810301403001134803200309564842c0c0c1603418407a00503206000e250745400c8e0140080040ca690101d0914113403102003114106481503a100200586900c1354640303c0391031fa400300107503201080f079001c0c00d40700041c1081e84007406010010328071045a421001903087e1300c2c0c070440d00025519507080040613019009699102c407044503009800e00da080781d6480d0242c074840903044402003225202d0954001105480c80040d50020680f030804082 = true := by decide +kernel

theorem cover : BRFrame.Cov 723381294 723561151 := by
  have h0 := BRFrame.cov_init 723381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 723381294 ≤ n) (h2 : n < 723561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
