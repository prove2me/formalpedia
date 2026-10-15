-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4845
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:55:30.465986+00:00
-- url     : https://prove2.me/submissions/e6fd17b1-5307-4d5d-92fb-3c951252911d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 871223021 ≤ n < 871402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 871224271 1250 871223021 871223069
    0x109020a0e1510090303050913090b040c1e030308360105011509180204150801080105070206041106160c0f0302210703030518040c030213051c0210020f0106 69
    0x1441100e01900c3d000b560500110004112075901e110180030410041051143d0b552162803100b08007070018002d2003001100e0804404640c42980d08551041a030000040d01525402c0c1340800c821205070380c0104546151001c0d40d401200810b0209881040100c8514040b480701e901041160110f40f0707180508031445140d03003110410303040b0203519810303c0c1012208079840716001054840d050900c1c40f13102c082180c06806401903400480b1413004141001c6082039000403c5412207211400030302090701c41540a0341c071640f061320050b1428113114010700c2d1078144a8010400700d5072180720b00008203090b23100c4401811080c0c00000304182305900c100203602d072100c00042000842c4190072003a00c448070030b4503a070714410320004061001c041080314200700c0075103c042c20800c0c0504240182080300c84014000d51000b003461041001120b004500307402d1000c24110080200100150801c101d5002c1221031440981c0400c114070407058201050385003802080d004000c15050510160300e020055 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 871225521 1250 871224271 871224301
    0x90c0e131407060f0c02030a12121109100305040b060105180402160302120310050d02120f010f180807060506060712020d080c0309030d09080c2401050d03050307030506030109020a0e 80
    0x1c4130810400d48903410260390045120744006a0290888030351701c43c00300090760318000c07100c691100f680c42c00d040806d20020f854000d0501e03030390481d803074080140d40c84016030464006031009007038040384000040680d40610003e000c002c40b202103900286070402d0000e0241d13884507010081c2401b65416110806070104007036484122140e001031300f140f034086040a6440310701e200d1544035800750890101952601c2c1e515070f651400c0c5500703803091580e1400705030b4087d280c00d03480000d01910b1718101e010310303c15580c00ba0300e216a012030103a11f0b1036441c2c5c8603400907000c0078115682c072100400103030000907140c4100d0040c00f18250003812003890030402c046c1100b1401040348642110810070000984000f20465201c031540c10710002c0c0414850070058821300410400c403000e8815440e10114100903001002c8150801c2c1090400f180e88580c240501061b440701d00401092040c000325803513030f0098008950002d030140c00000c0400346500001d2100b480e5030300c680d44c020146410300903542171005032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 871226771 1250 871225521 871225547
    0x9061606050c0a0f03111209030a080711070905100e09150a0219180801060f2102032a0931020102070510120627090c0e13140706 57
    0x14260a028071210084c2841c2e81808030b40b8101562000c51003244108442070341d0032124031000760301061400940c1c00f583e03030780300410307070300c046400c0700006080305204041c40e0b040d1510500c0580200c9180004e00c00151201500c616802102d00f800819120030302041b061290107504005c1007440301e10028000100c030083d00540140340100070226404882106519500f0800e00d088182088011120819603003103820002041d4201600040c28401c40c1000000b600c401094500300404464000000140a402c0080d05034101c080100200300c0702d4000890481104264007150011580004909080c01c0320450322002d20b80c0f01e6100f8800400010003010000c010000d0384902c0d540d00040d54604242c4245031041141c0442440100d100e00d02c444491683c0d0354091006989400c0200c0541411205030220903850395031200c15074080340244456107030410202220681040f0b40c070071240c00010b08250642200e1402d00340090b41d0f105410894801c100040c11070117040100092074801c1c0c80e02 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 871228021 1250 871226771 871226791
    0x2060601140c03040605090d050a030f0e120c21010f0203010609321c0b04060e071503020708090d0f0501050a0c0516030e0a0b030403170702030a080c0906160605 71
    0x20105202d5001040760140e8049040007900c031665000011880c2d19442e00003042ea00458854200f00b5410002e49900e00116843d400e410700140000c0c0020813407158090000c035840300010348200d050002041e287c203000c8100440400081011450941c0c070f42c996041c1d6006d03400001000805d510090751009041e1045040982c03182d184900c40c4040442e03400101016084500110150f555001c100304890a40c04449424035050800c1f612650040314191521403c0105424020101150540a441000c0d1305001d8410309050100c000350462172040303076200d00401c40d102c0790741d54840740b500b4030600c520200c001740360035440d249080d80d0014003100385660501d151001d29a40140940d00c8540100d41c121a1180c45801c00301d07030103083e2070526604140e01c400041442500c000c015032040c0c4c040d0f242e80b650f5a600460000d6003040490b04000160011702008410610554069800c01c0e8659000c1d070401c03440c0800901e01b58061076140038042900201241040310b51701415a0142c0084 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 871229271 1250 871228021 871228027
    0x6090f0717060714160807050d0306061e18140a0503010c020c040e120c0a03030c02060c0d05040c05100c1103033c0f0d0b030f0706050a020712030206060114 69
    0x10180c5a610b0201901c542d0500601400110060001e4002d44000c8040803100c1120f01c0d0301340c1802d650036030040c80c017500c03d07005d10145980b446010740540381c11504541e0340c0803080c103210b50317290300324138101d2002c0302c1000f805100c040c07801c8000500e40c00107070004c4010700e080341282c0810819686050741c4154000c0c2d06216a403000b440d0040b8a07041410002c1c0c0c1d01241e1003040c807040504040d0481c0401c0364603040801c4240303c108002a00030556440b13503e08001c404004482603940308000c54088480341030400808508400380c1d0000c540140c4030f80380d030074145501c510000b541c48840210f140005451152040b09000f03610140b6520b43c50309501035032414070300d5403500e0380c046000c482500002198404a400b845c8c280804121900c1080070320940b41c9501c230a074800154400c0d842e0b005845e05000290541e8900031440320442501d1320000d0010a1807c9070a88441e0009500c0341c081d401224000109059041d54001071580f09502034191440c00800151003c070317421444031075200c014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 871230521 1250 871229271 871229309
    0x150c0726120406030902061c051b090604050f04020c1e160b0d1d030706090b07050a08072601030503040608010b070f023a02030601060c050a0605130506090f07 70
    0x7900844055480c5840c02055a440c81d0010800a2003800c1d00040b40701022041c5e104070303070b1203648540d00a4041840d103480c42410411181c4450040c0d0900580c4100d007040300300034615010741800e40c800340c0a0300141c200304140c880a030400310b4007550214070034440751481454403c140030b05920081d04003241c0b0000d6081c400d002c421030040440840403507940313141c1220070100c40c3d45912445c2c54401301b2266910b04130f28000c0040c010070300044030017540c080c020600060088003525400c8942d41e5030418940e50b8503d040380d00b091001440141340340000d1002040d4209004e0090285001d40b004650351032800c0d0005007011016400808101024030140000403140c24400100c3c5404407032141c3c400c1162843d038188001803980402c01141e1043e81000440241c0613003025050080b01512044c0e81d17030b8101611004100f020050058106049000011b0801e40c803c5411425000c0c00c0f268603c0e90b6a901c911f032000a40e004c03e1981d103c0404040003580810081025041e003c85642101c0d900d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 871231771 1250 871230521 871230553
    0x1080705160b0a090c1410051204020f0604090f0b030d030507020d05030c0d0606120501080606150705010f05040c09050606070b0106031a0a12020102070e0411150c0726 74
    0x395010007810940300b0004901802c0d19038200418603500100c451090b5983c48070408080006c2c040d0090140c4007130a50324070281d0245c02a0343e0401204a0200d0682c1d680340c8c2013080c1182041c0000ea804001800b0101d0901d41c2c41c428009070b004240380004010700440c0405d890096040300f001e040608250400900c9a40420081c0022443c0c0c104140c5076100c042c10002c0741d0240318410303020f451810030000386240e403102d0a1140440300302001c000c5640c0b43c0288946444003200c05a400c23400c10b1003c0840e1354480e8000b84026801032000107480420320034190705488003694141c3d1b03825030040d010300189440d40b14040c1c205c00c1c02c0340c50500c4c10800d40d0b240b400900c0d05204580c24143d641160132204a50b0510321800188024841e20800351a803004d82c402409200c8207034014820031a005c24102c071903d800f107010b2904a10300d000e0100e0498208007010381d140c50740d00d225010602c4488024401000110081c7c5582d440d50041130b100000603074807801060602c0a01948040d14000c0c40b064 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 871233021 1250 871231771 871231807
    0xb04090c0b0318061005100306080c011209050106060e120a0506070305070e0307090615050301050f040b060706060b0304060c031506110c031501050306101a250f0201080705 76
    0x2009101c2a01c80e0340701d407111000c59545200f075560500846040002401940040030251542203500c65068004003008604889a50041075074580c01802c1c81261076000d59144480b801c800c41020403410010ba40701402c0d81d03c1c3e03070300200110f23141d00100c2c041490300d0082000a020140d0040c803040c0030b41d481e0340f07a554038058070407810b2560f5140403079403440c85915152240d603406012a019140c1d10320b00c0d00000c258134403d2a452440050a41e2100380c40f5800b12412124018075440c90000318004200050580e03450182e800802086400300096107802001c000780700c02ca48064403450903040110599014090540415140201324624140f0540140c0c06890365807825111035110f0a15851401562540740755041c400d5147d51150360803002c0d8500e0684800381d05036982a1217580044058034141c1c007416241184144184840100c0740014140c901e00100780000350000208054079640b401e10029158500c0c0c04409505558002030346640041c201c3c40c283d89003600300c1e901407800b60 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 871234271 1250 871233021 871233029
    0x70c02010e180f150f0d140304050d080901030c09033512042108070f0c0c09020903010501140f0105030a15060f0f03090b06060304020109090219030b04090c 69
    0x32030988200c103281d4940068040e101864446152564145540c030700c15400c40c100c0d801501e110382c1e00b03039000b02800d1485c00113401e000701500364020701090b651506010381041407550000e2000340000107295840003040301405011303010306541c6040710000101611a441d107400248554940d003000061000d20390340000c0390903400c948244198800250100541c004a03130b840b40d90002c14034410f20030580c1e07180c0340204d11170900892074802107200ca005403244158141c000c1464500000c13100f41c00b61098540d042c075a441c0c281441941c903581c41c101040545c04c0703041c0841d8041140e62030307800d0900c5001e01400785d030450610410b40840008038940c0c46a54001d0420001001180081055801c20791002c4030b462210400c11f512440000d02402466100344001850b0704e1851075124028032500001581288180310683e5900051114a51001c0c10482c10800f210400080c201018405020498040501e015058100341c0c07000317049c0c612004060784500e25043e1160006190303480100300711 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 871235521 1250 871234271 871234277
    0x10c050319060f38090306090d050a0c050a0206030f04051009020619050d020403081e0c0a060c050d0e0304171906110f0706050402130b010905060d0e01110c010e06070c0201 76
    0x480d008082100304281031018841102e0321910241d4010100b0301a081c18070007a02210003a82d5001d240c09d80c0d4100d100700c0003010483c200301c499000d6108030682658140100300300ea103070745146e5020031090b6000721005624800e481c400d00040050900144801d05186002845482280e800142c0e41d44200d240b018401040c0780041d00703806014030140c95180c0540e0a046440301d549003050401a800300040000d100000d08034110707041520780a40c0c0d18031020200a1030108000d40d150801411564158000e000c42400242d540141d00c1c01794200541000d4040c544039890400707003d01a9170f1740c005403002500300044030411030350652800c0c10105e80115002c0303004d541ca4490a5228850071250079144100016a5028098140c201d10300491081e50310410340a060121041101c1c00d03116554006518603804101900d040700c0546110244282d000400381906826103084804451000c40c00b80004139803403000800030311818138145e0311000503000500e84140001d1202030181c4000307041c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 871236771 1250 871235521 871235549
    0x16030c0f0513080a1a060d150b04090203030714010c0203070201080a020d09140307031d0d030f11030d05040b07030207030206130302120a0c0b010f0f2303010c050319060f 75
    0x2c0d08044089030b1000384848016501c030705003641018441018101000c003c0c01c0d078968045442c82c107080c680d042e0a5504400f05070b14500440e141ca002514940b1040ca92081c0c60341224405660148010000b6034410040c402a001e0182420390956071003902103001c1d0740040c410754000d80d07000030b01d060340180d89800060b40c40c0b00003031204000302003a80f4040d1421000c000010141140040102100c1d8081d03140c000c24480c607010380921b41001c0400707081d08402d1051003500080c0c09140020810401b0b820300740c131003200032a220342c5160000c031044d03a200707619030043c041030020508640360080c0c900e281c20762800b070050301c02035552000070b85140b4000802442c008c2c1418400d0141c2aa018000350115684800042c030040200100c1042568000c0742d040001560500c4070400ea4119407101c000d01034040e1800445204582d40040d078054444c4840d030107440c3c03a80d000c0c8991a01021591610381e00c2e07040c66104e800040180700303280950946019024800300b40b40181140841c2c0c500b03400624 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 871238021 1250 871236771 871236787
    0x106050f030a180c031a04030e040e0a021203121b030f0903090a0e06030606040912030c030219020a03020d02190f0203030d1d0c1c0813080a0b16030c0f05 68
    0x100030446401078030600e0303c5000003e420480d851000ba02140d0003408143c0c0b860305400601c144078901694002c0c08249441da200025050a03004100140b03803038816203051010580215421170780c903080c070a406400000311418400e01116403da08148140040509401940c40d0241c8a20024006c52710800407600003956075001001180c0320000c01a082c2222507030f40c0d0003480590705c2c0542d40b8610900880d40054a0f5080c14495080c030680c0040240078203d140d00416401801541401010190200001842e00f400310301021480755541d4000c254141080c00c000381002d8201c0f005030215003010000c840c0f001e07180180c901a0b29002440403c0960746440084e1035489861000002141001c103220458103556410303070095400c1005640c0812003001c208920f06240c640382a4141c0e10700c0600d01d001c81c003400043e28018052805140186403a50b07a000e10300783d5121000c80e8428481700403c00500003101040b011700d01d450400340061280c1800240c449015550140208000414541c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 871239271 1250 871238021 871238041
    0x513060905180c04030609030c0606120c06030c11120408210d052206060e1b0d0b0f13060302011407021305070e0a030f020a08060609010603023405060109050106050f03 74
    0x1802561b2000c020084070000d881e0162040c280320805031f0317100785040c2001403040c010b00e001100c21030b40720a6a040311410030000f078004080c45100a410003050003d00d12a1407010802c0100034130050f030540340c07070300c4c03402d02014a49516190b00d05103040708080b440c82c0c0000000c0548403d520f03013400110b0140c0d070360884081d800e6240c405c0c0301500c803180407414083c4843c0c2d40c03084095600703020754000709a965000c440b4140c1c1d203900850003046401c000d4689810020740c010600c625000340490388072404a00000c030005950750001e01c030165a51001c10071507130024408030644d024075488500f0b207269074001459040d80c000c10809519103510002c1c4d82d4a100c0c1e52861001c650061408030084e840e41042184d1040803003080340208043e80c00410004000114540b19500051102449a0070714900b28040d41088010f201100344a801c0c8074001c050112046510384083c3d242d0b54207000b61818414079052042c0d1181d0045450207005001c41d9030700c4401c641107400085041a42c94aa0726950 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 871240521 1250 871239271 871239277
    0x3060301150b0c06010608070f1116061e030605010c0b04170c0f10060302030705120f0304062a020609041d0114070f0f08040312020d06060513060905180c 68
    0x109024500d9041c0100c1c400c030004015201d403c10801c1202d209030380b2250240c9032400d041d10f4410105041809001810f84640b0511138040e94150036030700d202c5601000c00000703142302c1e0045004954000d51034540051040480c02c0b60059516080c45824074110020340b00d422081805031200c1201740004091250001d9500000150407000e02d1b55104c01164190b00c0d403500d00e00c003000500a03101a0700e00100240914020380c3c1d0002d0140421500c0d2100300040e000100007a614980a41c0c0380300540300000344081e000030800c61300d0b017000c0c600400c0a40f602d805032072180d00d1481d80a001c2400c025880d24016116070030700540b00050500c1405510607003055403101c81546540c00c2014504505d02000c5076107009004035150b014040034400d40a07200300d07a06e80703802c00000d9284000100400c0c0f150340c3c41d40480146c1c260051405490f01c0303005081d80c200350800c0b00458000200807e07010b58041d1440e0090400745482803045060134001010244c800c04903e12440801c400b040c0070f08c51000403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 871241771 1250 871240521 871240541
    0x10f0207050916051b16050f0609090403020a05101506020f070b0a0c0209011404051305060714190c031806140c0f060106030b030606040c0509120f0a0b0a0506010302090a030803060301 81
    0x10404205e00e60320a182e50701e05130310f4002c0c400c1d0070344500009a01d0409110105e00001c00918640c20f04103140c0a0200f0481c0040c4160300310b110f05840c00f00807400c1404250009030301d4003004614907281400420b4403000c0340d80028110350105200a03d022000708201094540907001c46a892403a0728007228507241c03c1c203019501c84c84c15000001e0444000442c01280302e070a035000e2255030b4850060074140d6011030b5025025810241c001945203214602c442e100b0728101d64070605103200040f072030800760551b98002e40407501e202810414950441346000b42d500c4101072819000341802001813940030f03080e441e5007401c44080303640031080d1001e100244101d0154400c0702d0156030340780801030140c5003583c1840d0180c040c1c41c2c04030320741e41014050708041c20030a841d0365142504440500c2440764001040d40da0303074000c2d010040c1011609100d210740701805140241920308140285408540300901044c0c14107104000542064403603802e034a040380e030802412a1644c2d180c03004680544141d4070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 871243021 1250 871241771 871241797
    0xd020d171306030e0f0a02030a030c0206160602070303050c03010f030305071401051f05040605091f0e070f090e100b0a0207080d0f0806152d0a0509010f020705091605 73
    0x5002c1041681075000a0088040608030f511030389411044c9a00c03000d402c41d019401d5000031000d08040390180e00240d2141e40b01030580d614102e0303001000e20a4400e851411070f080303a000a40e000034550b06010396034004901c08282403455144c018a1102410544401424071801164580c28081c060070b4110300201140002c1c00246030000c002c66102203643c9448411401c014000320382800d081c412003041c0c4601804202d1591505c0704c0001c40c0400d404040360b02000864000f0441c0c1007807090315409100d0710f0303c0d58000b407104000c024201000c1d9400130003240080130204046140e01c06121f9045904028000782e030350180c020208c1c1407400540000d10584a90441c0c3d0624603405081000070a4a541d940740540d200d01040101c0c81800c4450750b80014810320210048811103000202d03800c06001a02582c40051440292560030141004000c50004a100303070f900d582204005250300c8081c80940079a0b810040052b4480202800c030840070000c0040c10711400c1e001d40c04031150508204 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 871244271 1250 871243021 871243057
    0xf0d1103031b150910320a0f020f090d02030a0f2907020709021c09060e01110c061f0305161406041805041a010b0403030e0d020d17 58
    0x1810b03403030561865821508500c9588182e4400c080c504010354041e289850180c500d4615480065018045080014580d040c04c1c0240003140102c1d0441408401200c2c0340192440c90700300d0f0110308854207420703040c1440380100007140341c528080044488841003102c140386100d034280003007031500800d0702c1c0040c40560303154545018031101640d41c0200700e07050780d25040b40803001500e0a1039a41d081e00c0c40405688686001e0010042d5a005040c00c8801041c2100d02e0111340710402007680d000b51002c5c0c5009036075040c074541c0071a080c0998200c807050004020b290450f042101030382c0d010024501c207800102b03480c522890f00030b000300601c001d54000040720749801d14010b0f04544414a4031880300d2860048014940c1e9080500a0b1000c442e0f0070708003000d0441c206210755001c2d12004104440e1004010290400c016940c10345a010b0700101010b262114154580900110a0a1400d0b84540127903403040006944d5114801101350380b00d0002c003e140f05041348581d5502071649090f01c04080c81c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 871245521 1250 871244271 871244287
    0x405030303090703111c0b0403110111071b03021003050a06030204090b09010e24040c0801060f140102011a0f0a030209090d0813021f11010f060e0708060f0d110303 72
    0x203210310660f8001c2e132820701740880766001c025180c244000c840f00f811804501d0140400c0042c1c1c01a80d101d4040d04016100340340c40c41d0028210341c410300d142207001202140c1241840750040c03001111901c1621700101c12415600010300e04c1103003a4a5208140c1c41d40c002810041d40e61704140d004546c017810610459100f841d1600041500315902c444640c40c0034108499001c000034002541d4ac80c04000382c1c090300c16100402c040c114028020b4078400c0342800b00141c140000d106880040903181000d400240c03c120b18800500c6052400b28116030502040c04149900300481c403108410880b031100d00d1000380c001040c8102c480d0303803019501050010802050000c0460f0b15010350b0001d03a162410b036921548481100c0d4a02400a500701c080442d90010303220340701c040c2141c01405410f07c004041c1c50412101e003980e06030311000f0002d6072205010441d00804ac2030194101010742080d004500c5d000c40460071891038004658440c403d280c2850003405254800d0005005020302540c1c0e80c0c00f10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 871246771 1250 871245521 871245523
    0x90204090821070f0f02010930090e150103093002030319020c070f12031706130f090803091c05030f0a0b0609091512030405010e0d08040503030309 65
    0x1182c62034034511206481c441800e040c540b1400c0d0703c2841582c40380d5241c28500b42c8201c843c024034000c0102507650fa0000c9002054049e0040c10948004481c0100c06031840002610319580001ca880b080c800002d800380400c04803c100a85d010310740810829440f00d02c1e2004a002c0c20b00c589010703000c84003140c3d401c0e11106540d01ca00c80b40540844141c030b07000c21200c0c400c03039070392208135a604e0354414880002c44d100150303500100f5480741e0b80d804450203652540c00201d07660155a00403500e410251502004041e000b603e09050503a6094404160f460032030301040555118441c440040da6568050303402c1c44059070b20699040350800d941940702c0c540045070954620f000703040c100c04a501d50310081c4039984102c007184d1280c41035081c09082ca0b1212342c000380207850401051588901d040c8014a0740fa21846450b03442520fa462180e680400c0300404e00041941c0c004000c1155041044184180c1c0d8200e420440003074015142120021700c5404d111580f4020340e0401c3c1e505010000506c12030b044 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 871248021 1250 871246771 871246777
    0xa0e0708091b090f0a092f04060303021c0201020f0c03090319020a0e0403090302040207060b0901050a050a0b0f040302061b0c04062412020c0a290f0a0902040908 71
    0x70a1084403403101403280d0194540700320840b29a80a514000002c001016440790182c00c02001d0301d02050004d0107a950b0b915030350280c40c68081b001001040d05850700c600030601d00160b50300f900e0800080d403e54030020748802d61580291045144e031344000001c07902c00d504a0b0002500c41032003503103401ca044002500c17584140369951192081364445850f00380152002e8422590081070090305038a07020401c0180c8600900c1038041c414021000805a241ca00017010384a10882001450041610400c4955101038004a0064001d20402c2c4610b03144d407540340c0140c03a4101c04680d11610001491100c0c1d225941000750003000214843c1c43e0030165021601040c200303002030300d503915007000c1400111601d92280ca480307880200d08180b101c40441d1440750010b101440c05241c16900030440e0780580e84408600c01c92a40507000307420a105088400380218031126144041c9000300389040442e0740c3e40540000c0082e45040040b80c100b600d241c1c070103180c1c15406007051184646500300b1401d990 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 871249271 1250 871248021 871248031
    0xd0f0b10060809010b06091003020d060311030118051b0d02030d020304030b161e020a0c081c0516170c010f050a2a0503190f061e080a0b060a0e0708 65
    0xb07200712001c1002420180219080940b0141150741050344460402100340307035000c00c0005242c1d00300281026001c1c5401880007030760090941441a861403002d2500312652030701c0700503802d00b103001c0803030001c0d802040d000407401200082072890040d01000807910f210b44c41d4020b5161241d500d50f0b00446030084042c20880b40501507109042d074030030382012240b4185002c0400002d2041224000544602686c04681c40003441103554204d5a03980c1c2c40d10404490700400344c1d640c82503451140700444206054040300300b0f450002d04086256050700c0d50514071150042080643c11194216941c030000cda40300c3d803181d0b8009020304200300c2c61120003848142d401d000202d0406454a60415420603248102e0f00c0364509100503c3d0344000848180d0005040844007201c0718040c42d07214a5107014603412400101c4000400c00c1c81c10443c4800341030721809541e800349180e0810009900003003030b9500c0842e000086142d0a907565000503074060706a0f04900361100940040c002c019500041c114030072 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 871250521 1250 871249271 871249277
    0xd29070504150f212901110a0803070513080a11100c110d02030109053004080d0810120510050105090103021309060b0405010602150f01081207050f07061d18060d0f0b1006 75
    0x20312111f0407403070b495909181d4050001003041011540e100d21400003000c1d00c0440f80d0070b44002a031500c50701030801481d01026580408851842e5218ac5022072808201c440c950811035082038107640c5856820340c030100800c0c4548012180c1030195142034002103c0a540002a0740c0c45a0801c846450108190240348440c01c49102019041c0b00c130420803181502c1420f0018620064000011690060010014070070b40081260010715503500c0c07215900750301c1c03084020300f40f1508500e55080880b481640058070401c070715070041016840365940d403000c00c40f008101107000046801c14401611002081c0c0740c1081c0f81200001c1e25990100d568224820001720112464441c498000e096500130b0040d0b0b01d0076008001e0100102d1302ea8001400110720500c01d4500e9020400390490402e8111340c4000c0105205e807a108603404203d107081c0d100540c0071151001850341200030844100c40040c441d901900c2c0002414080c4854000c03c0d81d940e982c07000c20300c0400d2420483c81c00a0000522a803008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 871251771 1250 871250521 871250537
    0xc0304060501120f021003150b0a1206050d08070309030c03061b030902030304090c1103120702160308030712150b0c0d0c020d29070504150f212901 65
    0x303140d14901070740d180190840030444d0044180e8081103c00c02840e03060340f00745980d41c2c0c1144842002030010400803d0741c00e000c103458898040000c1d20384134240d281009060b00d805018045966850800071095400c003140382c0c2c5405a80c642519511b20642002c2c1c0083e02e070900000803c03c184d005040c5d034814490749100ca081c1070400c00d8050700d5601000940c590010f01c8244110300d86c652020600b46554076200b074280c06201082c5045a0013004600c214180301010001c0581e0104a82143c082c00003035000b85240c5981c98000c40d03404094100c000700700f06415140b081e01d150b504010a990050b051665500ba030310303000861194400030030b507401d0703004010381600e000e809a02d080c0c110b20740160480704081c41c07640d610510450f0400c11b814000c55850103080c008102080b01034800c03001e64403182d99079828003241683d03800505c09500d0801007044048040d69610403400791f42c43c1e40104001f030309c04000c01410800743c8408800e02000704800010a208800c4500c000d80203280c00ba210700f20 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 871253021 1250 871251771 871251779
    0x80f04080106030611030f0118090602030c040e06060708040608060a05030d080103290c0903190302071d070e1e1203070c080601230d0f03020a12050307090b071a0c0304060501 77
    0x5d4500044501400c104c06000040107a48001c8401c1b44650444c1c4000003850f07200c50759107004980040d80d03803210607440410140050808540303041d812080854880341420f03503995032845207110314010101080220b030040b403d00d4817900843c01c054207008041e07681160300e07460020b010034000d100540f007003064090314400e03085a04403d012070203040040301c10650340302003a12505501c40f40ca642d42510440741050300c009180c40c0614661486917000c1c0c4103a07440c0c403c0010445100550004044508a060020058200490806150043d50303650000200e4018401d000070100400c00e40203031100b914001d500300c0100003042214032804a0300701c0a40c807400e0165070344809006c0c0e074036034110120240c00c05421035545103110100080c810000311040d507a8180c4004010801200541d111218070300c00c01468807001301604600340340c034600b0361034029070040003418640f248004c441800a1600c0c2401001410f1b04911241c1d041c0000403801c1201d807c3c00d10760720448040d2041454000041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 871254271 1250 871253021 871253051
    0xc030614060f0304080909240609062a03040816090b030601122904140d020618030c030a020a02131509180b0a0b030706030501050d0f080f040801060306 67
    0x140001034003404650500110907401c0005a10240042e2200300c0b040c401484c0d9a61b48901c868401d15a0758a860150740e250b25088c042c0d40060002c441c4034040502c9111016100d0320309031200411028800c6000344510701c424017000803150541f2825001c006404a02e00740f001481c400c00c074800340c6280180b42d41e1450b455045558030318807543c0c07642054004210928041079000e070400c1c0601045002132540c1c058464070700034030540c842a0844120300300f10038031903200704402d46146500f020b0040c0a44044009446200051031003190050a59003519007200801c142c4850b002007004480d550101464040e64030150304408a1050031030640c038124403a01401016101039904010440c1942003031402000b6000c59804941c0d040c0716014154003060f0029519030080800186c0001c2c0104140d09050070040107401c044241170034100104000c0d214107042070607040c0c0240c0c803040f20545602c3c3c064542e10411036030150385400883c020803003104c1944003004880c45040b041095465000d545 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 871255521 1250 871254271 871254299
    0xf011d0c0d030e061306170c0c0d142a070f031709180a270206030c03040c0807080607021c0813020301200c07080111030c070c050904060c0306 63
    0x16401c512201030390750020307000302050221a08001e10350350a0413041c0d00c482c8040740059000c840024007006400d00b501c40303c001900d400081c41d2400070b103007400d149046691602100443c0081150b50189000003c510005542d05842e0070703410b144c401807504040850401a440d14040a4001e43c800000c036010101d0950003101d511442c2e1418000d4040c11801e0280c019800880e04840f0140030850300b1010424802d10840303280f2070000712a62100d100500001008003c403c2c9502c0c101000000340c0e1741c18094a0f40a0101c1d2102941e0390750790301e080200c001c0389038040341c801d02c03c621000c10500008600702c1d10032040750307007100c0c0c1d00d00c081c02c1421581101418400d0109401001003809010303038800760081503001400200340c0100c0300c020051070000d0308900941ca500c002c100400310700024400c00f001481c03420001d01a400070f022208110f803001501e041d444500000b5a07100300800550340b040100002020000c1c00e00e01b500f003d80c003600300d040c501d13000240380a0000c58514106445 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 871256771 1250 871255521 871255543
    0x4150305060d0314040e091005090111092403180c03060115080a0e120a020f1623060708090301202b0e0c030601060309030c0b04140f011d 61
    0xc40c5482c84141d24140d4048000c2d943c3c00010030342c10400411070551982c43c0c54002c0c00e02900500301d50701c3c401000011224060030b07144403641024103a2208014550503a0242c0c4022134025001c070080041014001c0701d0b03004051404040030041000705400c40c00001c00c00029141035528003692801015207407182405030115440d5044c4501070039521a0200c640d03c007207001000501103540d2440b01c0e00c1d00c80c80c42d00c51101000c0000f8560195541030012008511550b4002c080c6222040007810346280c042c028410329810403451600700c2c800104002d54540406450710390b49000c20b00340b41c1041c2d800303c003050303010f582802c41602450001600300e680302da4050069504008085441d0b00c1c3c100c07041030055040c1008a00c00e00c60f00200c912503402e410482e007004003c2e859a20341030606205059000800341440c052080700401d0b000001d00883e694130004c0310106907540c0ca0b0541e10303601504a01d01d42d900c9010301d0502c11120540c040d14231042c1c10090039030000e03000a01540c0d81c08040316 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 871258021 1250 871256771 871256779
    0xb13150e2103030c0f12042001020f0d0807020a1a0106031404030c0303021b070b040306200904020f04090f0e0c0f01020a1203091410060f0b090909030418020415030506 74
    0x500135881440608042c03040d6240c014685183c5804203280c0d41d00544055a0085d003922084070120280c50079180e0302e400a0002e050f03070a015085183c0c540b080225200280000040001c1c6058030034803a01da42954004c1e0b41102c40c0082d40140340041400740280da002c2460110304289003504e2600052103a0f52542e00c01c100004207542c100c019401c400d90000712030b908030299454600e01405604003070311022803002e807510f196050540551b02d0040031103200100c404429000c00c00000200d0700307400c605803005a907402d029510200303140325692020245901d0410b20002408494102c032004d82201403c40b40100c11030340402c04030000840f4001e0140c2d003c0d040f400300003442400660703d9a1001d040006464145407a0119405c80c10114003c4540000c07180008410f4170344078070b4000d800c265882c0402c1c0d0b410044801824071034002400e104040d0341e00081c61580d400c10840700a4509a400e1050300f03102144040081c0d003041c002c0d5a01d58145c0034070480303041e201c0d120b01c1e446408010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 871259271 1250 871258021 871258027
    0x409140c070b16050409060902070215040602190203070b030c03091c0c0209130807210c080403060905011d010609050c070206041701180b0a0e06010e010b13150e2103 73
    0x1e5007041c107050b4107403c0d034002c0c0f00040c480040e0f241c1103440342600030413804401698502c00c2c1c0c03040000862840c141540b0a4000b4841406810341c0040d0741d89410b041010840180c51190000900e0846150b0094507680000010044164200c2c80650b010304000412114100b01300c3c9103e080c0b51301580d14202c001001d001da580090310f00002115000a81440003840d00121030729000c2090307010750029074411890603410300100000c004c04850030740d040e00d400301c0507180704d6660313541e81c5c1701d00d105c09081c8584032000da0092200070750103d003501c8810401c4140301c0710611545030291810b441003060517460000060441d00081049401143c4c0c01802240b0b0941480507554080c0444007070180d1a642c0c40004005040d40c000c00000124082c002c0640249400c1d4070101c1900d01c279a4012007141c000d60010006200c416600c28151181005075946511828180c070154007115400703004184040110410a1500809102d000c0e100c02da840e040740c5a00c140030031303241014100314440b1a910030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 871260521 1250 871259271 871259281
    0x30e0c040e030307031a0303040906030b0f01060f05073215160c031106070503251d040e030f07030806061602060a1202071208090a32030409140c070b 66
    0xc1c4d071021310a42c903006c01d14550b0400325004245160031607000110743d595502020b2003846048840613601080002e0b441c5901e60410701d00401c0c1c2d00c0e0140d1640c0504c500800c91200300f00c0188603800301c2d10701c800308810f0034280c10616501c001400c240540340c80d0240c0104074413404c449009a61007000f100242d80001e84034110100c0f000310003500d0a404004045400c800407203001e10605004101d0380d40c5150b00c3c1d0801c80011060103d0040006070700c44450580102c1131500001341c050000034205400328400801c401003000b6141004e20180325000c0019603076011000303180503084207030207035940c88500d0b0f6a500034092030b441601103040034200318202400040c0740000003042ca0140c1d42c6003c0b80a03d00c00c44100003680c00c2018122a40c0003003035082142a40c2c001030300c0b82e200c00020020103c807600c03510f500e545a0756403201500782c00d44890040c0184a4810400210f484407102203c0c0d6480e0340300700e22001018030039403204126003100e0104610704040e0043c0c0e5640c0c1d800168200054480e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 871261771 1250 871260521 871260527
    0x506010e040f0506010602030a14030114240a020a120201060b16060b0a06020d1e0e0402090d0f0b070e030d1d1f0909050c0712081312030e0c040e030307 67
    0x18821102d4030140900c0b440000d50910600d03009000d642c000b1612140d00c04005001084410f06c540c043e02414801001103040a48e2056210072041e60811080101410f600c0070b4003412010141c1e0000c0005803c47c822070380001c0c149803003402100c2c640d6200800e00022401d031641d501c038000c000d100038425020104075040e010000644034100001c0c0d81c9450030003250340348a4503408180582c0060f1500e050413030b000692460f104c080322038440305c24010300303501410045150604a000b0782d03002c00c00600d69120000c000c803410750424500e002c81003880c90502a0440d0440780310300003450440c880203090030001101c0318055030079210903400900c07030300b805038a4544030880701d80e1180400355584242d00380900c01e03c8021025a89140819040100c0641a503501410400e1801000c001c42ca01081c407840090403200c41700c0c44c2c01890360301e0309084504203440c01e0f4805800f0554a42c414000c0d5905903100c01d64041c18501034480b001e4403013003003104942c912403a00e80640c004200094074148 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 871263021 1250 871261771 871261799
    0x15090327080a0f021014030106030c0c0c170d0305090d110118081305060c100203070c0606150905040b0f091905010806060f0607080706020304020a15030f1107050601 73
    0x41800400a4515507554034603207054000319083c1d544200d4071041c1c2c002d42c01c1503075980001e4000c50a142c600004141c1c850300d0641f0052040c44209a951011101c42a1107549240c05103500403807082100e0f900d540e20030001d121040c01c41800752003010854144e9070700034019540f20b1090300000e4000d007500c458042c1c400c031041000e4505255030764420788008030b110b010032440a500840b03009486105e820600044032103540c21040c86200b050101400120300001c003c04405040d060158a075140e100c07040c2c448212a040052800e41440008140300c506840750002da0112a6030b08000c0d1943d600a01040360301c4060900c0e0071803003501081d256414603120f007a030000da20b801e2001c2c07107580741801c00741110f10a8002e11415042407040c0200f900c0c00810a810f07400044448074506500d550321190030344642c5c0401007403e90080006810f55540150940080681c220542c4000400d424002c00800c40c4d4861803185501e4541000d509802e00b10595420300c0c0d00c107009000590a00081402c412 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 871264271 1250 871263021 871263077
    0x120717010e0a090c080609060402121609200a03020c010b06030123011b140601060e01020a12050403020604150201060b1602040e2401030c05031c0f140a020703150903 73
    0x44c5042c040010f8a00c404c102e51842a6040380c09000c0301c0c105441041300c01c840d0369a80c0f000591088802110446010b00e204044410707a1100240d134503d50100c2c0b180d000044400d4101184002ca4100d1145406400030244030b08014000c000c541e050700c1c10411a03000030b01a91740d00c100c0d002c1c0100c003020030240e201012140c050500041d90f2324401f8102c8264454080100d034000007c1c03c1110103c9004c01603240941050b041c5441041c008000003503591071941005800740c04900d034001a12400b4200f201c002d95000703000c841c6d480b621030510381000c00c44d52551200542c039140001507440703c200306451005407104510300610703c0c0d540810000d40740c110b407140e816006160307600c0b00c02020304046e8a01c108141e024480990303d141000d84c11303a1020381c04103010341c10041990103900b0030400c3c0c0548a050500f05141d08030a000c2003100d000c07081036a81d517082e00f000242603403903680000303c01044034070078143c07210720b00d010114802c151841c810009000c24104200f49410002101340c0c500781c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 871265521 1250 871264271 871264283
    0x60b0a12020c1f0608120705060408070f0b01120b0a05091009030905060c01050615030717092a13230c0c061303080a0506010206061207030503120717010e0a09 70
    0x80c0990034920300f610601000c100c03045a42d5003800c028050b4103014009082a490200c1414480c0d103480d03881c1c96200c024001403840600151600c00c000889814248503900507040010300d6031580030756103155244210685a01c203007040090004035031402058840d0516401600003400b20709050006484591000c0782071149a001c08240d5440e504043c0020b030640c400003142c2c81c20003009101070721482c1003640070f001c20200b0401030026081265205020b800498940c290b90f1050005400d009180c0d00c00c68922211402d42080310040b4054024541411101c15804640c0c0c643c2c14002c0300c01000c1503424010900e400521040c0c80c44001540c08151003034030798a00030411200d02d0803c0000c452401984010101100900d90301071007950b403249610208102504201c0f0000c3d649810083ca480d100b078070b540800484088092000e60019a4080103d9031074400104034000c042c90102c031404000b41e00c58003100c045408240000d4101da452100e600c4040d280d5680c20006090007520540305 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 871266771 1250 871265521 871265533
    0x303030c110109050709060e1509071b0c080f03040f0b0c1603050a030201051005061209010f020a090e060402040609090209030102040f23031c030b040b0405070909060b0a12020c 78
    0x714050038012000344601c82c101500c00036092503002011144690406420202d91104010100c01c10012000036000200d40c20001944c40a404940d0900c1c0b40c0c80d80c20807070b5100d00c1c0c5501086100c001d88c0003516094002d55402404a2142c1c6a403030040d4491081010034a0303404112003c4520000e04014882c01e0940fa050007100c4056165402c1640c41107400b903100302c000c0d07000e00d6820302c500354200f07140d114645580e9107014000f0380280510500519000344450100d034480d00300354004030240854403020b540700d0640400180640c8154403908446048003070024529180c148211401d84100e5150b10310902e0900d00f80d08003d4106a04454041d94200710204200b0b40e214013100051510191560b40040100e03200ca078410802102d541c0207600c440003104000038249440024002a8036002a0711260b0100241c0508600d280268100c1d203801d0130302c0580746d80310180000b650300758042801069560511780d001e40c400d60b084100011100c846110540400750000e0025048074412204 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 871268021 1250 871266771 871266797
    0xc06022d0a0219090506040c0f12060e0c1c05130b07020c03120c0f161e050d0c170a0201140a05130b0301060207050a050d081c022a0c01090303030c 65
    0x100d0f50705035109055621880881003100407198003441d940a082a41c042c0700160341c410340070b4100d02c20b00c84500240051040e0142070035801b5800b400c018600392000301d89a04081418113120380c0300d00c020005084401809100ca6581809428010501c50180c2060300c291500c801ca2003d1020703007000c0c11070180b09004542d540d0100441d890020954420964803513002c04114071300141d000303040307900340c11110b0451103155008c04c101c4102c0d44c0d80d14002d40e4505500b50713602e9200e201604000da005044080c20810f00c00060900010380d0985140340c09902c22008580707603102240780000303000503a00c034000da0030342e04000041c000e00d007542e041481c24100761070908141c42d80c158128881041e030204c0100082c0354100820402080152100e0102c1810940490415540d0381d8024100000010f0192070221402500015140e0102011500c503000400a400480c00c04030b045184c414002e508822001c801040290440038143c55202e51603155560540140c022481c2c03001c140310011a03005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 871269271 1250 871268021 871268029
    0x60906030403050d020c03041517040b190609020c1204150f1704050f06070f1d1903030807030f060506091908010c050c07170a06090c05041103040c06022d0a02 70
    0x1201806c50391016684950601e152040c030203105011031800c00143c4004442c030100340d02c0070941c00903040484800c940d40e84e003200b403840148210011207041d151280011702c0e00b206501a000d2045068103450050801e65914a41c902490140060b5018054204100140100400c24521860341081f1040c1c10024209000f0302400300e40940e201e40186402c0c0c0748040042c001150b12503242d007845012000c1c01c0c100200b050b251419295000314a4030f000e124140d890740c0030085050321000d0008045031f03ca1500a0802009981c13410100e400c1001500c034421080c0240c81c02d030380016007214140b540540c200500000800e02e885004034000c417011800a00038050354440710b00c8e0340c80b8140c0c1d03500100078051603d12554050b038504100890800101d600104103a4a119040040440e03a6113150800c80c0004a40ea84695802440c0c900f102403074091220140d44a54094011108941e5403684160780751b41005e801020400510303d141100d000e00c0340d04482143c48050201c0390184c0c1580d0100d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 871270521 1250 871269271 871269277
    0x10203121f0806040209160207090905100c050d0b04110307180305010e01090212010e070614040f0609140f031f02090a1d011403030702040e0f0d05040f0f05060906030403050d02 78
    0x200b02904907004102c2941010b901064014920280d0440003031060080252112001c0c014210b0060315980c040e41846805c01c042000d2100703084041080c55081403010300f03903601c071041c0c2551190801034000181e182034801c000300602592205407840d528148119500043c108000803011030f440c2012011a100344150b0250542c28000066640d10300c0c0104404900745203180302440e03041101c48250354001150303a100f00d4000b4140840d41d40d942d603107415203a000f00c0d00001480c1da0480e034005000d80d4010340c01c2c0704903058030000e041070880c04000e1002020040741c0e441d4140d44070400a00000c946072900a000005005c001420040c842d00001c4070b021090b0b03c003c18442962242921144a5000b1a8010900110101800c1f401c0c200407030303243d01031010b019200c2d40e03440d40c1e5011110402d101d159030504402c4c0a4a08003150103a01920b00d800c1405500c1280c0000400460108440c0c41840295400145402e0404082d07500b04805540000d00c11820064184a600e400c10054006 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 871271771 1250 871270521 871270529
    0x5060103020d14190203040f02040b0d06020a030c20152a0301030b06191401090e1314070503030d020c0f0d1d0d03270f03031e030902010203121f 64
    0x54201d4101640c88006464581c1113aa07520b0b032040041c400000c401c417400c1040b681d070546000c9410005d80700000d510380328012001e0129400020101110b0b9491341c0102680c00f50743d110011400c94940583c00507840084000c44140d1100c13001c1201c1c40ca0031007140d90300c403002402d000b80304c000001c402c1010000940c01156109004001801000b042c4c40c2280d03440401560081110300680d40c0b0300b86070784900d02c152004603024105050f9164460881b001c041d04001035609000d050000d901c9029400d40141030b160310b50f0641e034001240d400412a081104c100030021410160640b21a2000390320190050f41903205400c01ea9031240b90902400307403c082c0d01c2d00d620026201000c00d8007640c07034484000600c84d00d9560398181c00641c0040d55500400c00314000b10f0a42d81e036188807490050f80719000090a82e40300b210000815501800900300ca0140102c016040b228120301582960103446000b805604280514043d8070502c86c416a07000c2490104402c81401503202c01807444100c2d00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 871273021 1250 871271771 871271801
    0x615070302070e0937061812030612080919080d030c08130f0222021b0c0a0e070315030f03021c0806040914030c0c09100e070305060103020d 62
    0x1410080402c50003840c030313030060204010700300681040d510500340c15000c0c00352041e48003010402d480d40340f0307500180b0b40f0f40301d030703c01010007400c40318002c641d5070300c02400d03400c40e05100a40b0500c1e403240d01c280500022148507401032061844140d982035025000100c0c0c098014000b042c00c06940c1e40400004001428000094480c2c400014401401d54480c002c01d01d0601083c901404442200c004a18849a8114205916030b080d0340c80001d80038010903150030441c0303060a400150383e03030441e4001c0541035402c01c81c90500d10080b402c280d8507480c64412181c0c0c0b003c42d40e10308100220503501d840c1e40c000150301c3c0004172071000c4110241e10705982d030820360300c1e4149080c103881010703010440032140440300700c40b400005111034001440d0540041c102409651510207040801c0300042d0103000082e61201030301e45401d2204c0d1003540c0d640b681c175041c611460001020440c8000741d080c00c04182d440c5c1802c20000313940c4620096014000290040307041540c200040100003007070344540e218a1100003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 871274271 1250 871273021 871273033
    0x20f0d060b0a080d0e1516050c0f120607110a06150501031406090a0e03250c060c080f07110d260408070306091a0f01030620030406050615070302 64
    0x35081c80101110741c2c0002105034480000044e08940119000e0141c0408441c421640407900040c1055801914129420006502155010014041360405824000380c0d40250300c0c00d45403040001200a00c3d0018109400081c04030b11224421440503902c20424000c44030a070f00141e481d0021908082c1c000b48001030075002c01d001c90742c0c0c94001c6280c0140902101c01c6a410050000b4010307440c0a420210030070303501c00b03507540281c00c1030091f180c0043ea20f05000c5114038070034035400b064184484040301c0155180d0400710f11503010b808014145904005141d0070201c0c12690411294000302081c0d55499020038409038a42da00400d840c0024450f072400c802c006244003080e071045840c6c1c041c103a490b400502040c80079910000f00c510860747c00034408941c500880c205a00d0718501003400b00440250b160401c21640b10420407075048170f10400e000c020b110608159401c00750310402011008940410106020403240c3d0041138000400401d030b10800d061444603540d203540201400c03005a0800d07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 871275521 1250 871274271 871274291
    0x40815060405070c1a0405010e1f060803030403020613021f030c090e1909080d0e03040806010803090a090c0905040507091e0501050a050c0c031b101106060409020f0d06 74
    0x601500f40c1041080c180590900f445903101410442c0d442d540f04920f1400710b00080a02a0941140c0007052080e81038818900400c0001c03140d070302c28940c100e8001d41c180000040e0f8000300008503407090f80c043c0c4c041c107030603112420340e80700c1072040e4841070303901c01c150311560444030fa0034007582e900d0003980d40c900181150500700090028915584020811880c1000f04000b0f4020600c50845064202000188280d0949001d507458011001030018107441c0000c2c80d40a11000070080050381c007003004131409681c0c1c030050b980d543c1c428108100c2c1c00c4091205d08010703165403a00602c4900105081208455407183c0108048600443c1c1c0107000841c600c004026100000029003c8080300c24180407816080c500060458850304601c402040340010b41500c41c4841404000d15420000b0159110a0030485402888240c0c011031079101d0341440300019140c50088006407845a8001c020300100c0d610341d000c006c020944603109907004210101e9030200b50369078016251150b0300c0703031000140314002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 871276771 1250 871275521 871275529
    0x9020604090204090b0a0302030718061d04020102150c04170124090b01080402031b0109032a08010b0a060813061b022a09100e1602010f0b1f030204081506 68
    0x10107082035008421b105018000745e1000b2a898040e0f503524504652410040d000c103600a000907030060038401c0e458207650086080d03518220340214000d90854035240d0244038540341c18032041c1c40c21040300c10b0403c0100031502184600ba03940203440000000e40c0c10740740782c8480c00312655402e448501c0f00402c0049c03002c01414460440c20490070710f858952450306a004c80e540d140316086044038100010030102c16030f0711039811b02014681c44268002d000c1003c40c816000c103100358440f0301d5003422030f50000c04c852805118501c1c0a440042c0b40c07220030740c60180c090300c8040010745000d010104e050000700104407075004989080841812500c205020403d000b81042100804003000340e064072118800104039140324603241c9012a1201340a4444100f044c40f80404d9a00030f1140c801180f00304104031884030b03c10718482985030020701c40b1101358281041100c2c2c032095138640c000c07583d0b49110305d0000010340800030083c19003001498251100c1d01c4920b003030f11210100c10200001c408029550074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 871278021 1250 871276771 871276781
    0x150604030b0f103005030c0d030906050a110a03050718030804091a0a0b0a020a0b0f15240c010209060c1c0c17090f0a0f080f0a0b070c060902060409020409 68
    0x1103241004407688414240790110381d0713140e407003002810320540000e0a104042c021540001c1ca01421070344100140c2c103014000d003400c603900f40c882600d0300b00010048212400b80c2d412004c0e900c52010314000303000c00c0560003400040c18290420441a040d402208442c18070303007021310301441c40b25403990300c0e0205102c180c030100f80d203d20442c4944407000e040c9031102c0c1160f40036105070180554039214000340407440c2840c064000b45c03100b2100000d00c1806c40041c4803407800b0740d40d2480b440017050401c3c0180308011000a148401d902c5550b8071014140e172818001e403960003244e6001500d404071100014090303401c084482441c07a040a0408600750104001d004240e050760304011074030585036142c5495800400c0c0600800100001700a03007180d4072480998034801c0b0007040482065201d0341025054100c90044540d2841120348020107150f00251140e244d0342e100c5810546a42d07228011140d60b50440b00480e01540c869208a005035526070240018202c4007400588540c40d080440041e54 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 871279271 1250 871278021 871278029
    0x504030c0b0405060a0f0e0306040b19050c16020a05130204171903030c05070209010e0a0c030e06041b031a06040614030c061303020901080a02030609060f150604030b0f10 75
    0x10420082000c0d1311240c0c20740f003e103242810442d1600b921038a09603015420740c0700300c40c2c1c035010300c504000c100443c5414882c0501040f440c40d00360aa4005a158120744081e543e1080182e801e000d44103042a1080c4041d01c5c0e5440a040444180d81c0d5401162841e80c42025202c91113270041824007401c00c001c1d10060145c0c0c3e10070010544201000300f9a450111920307405000c03d44c80380b034080341883c022000c0310300e03003940589003034501c0d13a640543c03051411050f210f02c5000c50602000408941c82402200c01281030310b4003034051030705c40d640c441d200164070080e40065494961400000308d4010401c1c4c4000d0024400030508030301e00b03d010407040390b600742c20210702c06a80c84658840c640300020391501d03020302a1030346585c030555000c0e50010a0010f503c000d500140c0d6a00100e4440700210385802c0c0d8500c20b50403980181c548210035a11000c0449407030b0080b81e84800060300315030025504008424019014500e02074898464184400d02120402c089203151018442e02103001c2c060a0018 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 871280521 1250 871279271 871279289
    0xe0102060c04050d320f070f142202030405160b070b06031f06030c061b110d2a09050c0909185b060905070504030c 51
    0x6841c1207180a0301c0c9014900400f0301a4031125007500c100070000850340c00d07515010303600c040320550400e9081c3c01c0d01810300301c04070180901e075801182410009402d4003524080108000c07c24141301100310720819500b911584004042140903030406040c2c000000800b84070f50160b564a01810300381d00c5d2203192203031810b0300d035040c02c0100702140603a005c0e1008280d1208984c0c3c525143c10340003d10303160110361440710441c051203148800c03500300d038440b1080b64810600c110f074856640605a84003001c11031841c0f9040004c07540708000400d0000c00c0c0e0400c1c44010070101c543c4049440d00701ea03005c100160301843c100c15062150380500e01c3c5c89844000c1082e800140301c50701d40144601c40c00c0c02000c1115005884400c089090501e200c81322030518000081120700380c0400d550002c101d41d0300b001110001480c10b039088070042201d201d000145480700c508540d1443c501e000030480d8200c0940303450150721351311074012901d0712050044a0192806941d0305460780d0550900c0303a60420251f12445038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 871281771 1250 871280521 871280533
    0x418050d0e01080403030e0f3003040201050a050c071d0402040e010e0d0f1e2019030503060d020901080d021513080c03040b0d1b02010e1b030a140d0e0102 68
    0x1a0307922055050b03000c1c5d41480c0101d9006280c02007e480c0c958440c40d440071a02074850804c10020085206524082c0341c1a800c1180c01340c010103c01152000f95400390024400300082414980590002d22a45414400312001c0ca6034481070008103440c201d00d0303104010800c005000075890940141105c0c026484001c104201041d13034a01c1d600c40e802c24819040c480f02c02d94480c0310324010001d07004120020800f1090b056101d02005083d42c0c0c6a10080f40d28801002da08001104000340b079100e20349608200701d4045803140c600307442c160402000d007544001c42034610001600e40c10041c41c02040c00200a110356284000080e0130302c00d40003c01c842c25000042003000d03200c29812402520341c0c105104d40d03030320108400c3ca20b04500c115044103001500000d0b0030482c900b5250711500407000c40c0240440c0c2400c0111089090710a01d0310341820a9008203588080842d0010301050042401002c40782c00401c103030345810441440e04548400b0340c02c034080c6d901845030440c1028042950910161017 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 871283021 1250 871281771 871281797
    0x7030f03021f0b1807121505120102070c0806040b0a0f0603020618090c0702030c0d0809090f040c122f03070e0a0e0303060a0603091a0c0a0f0801050f0d08090418050d 73
    0x31050307003030991ba6080b504d80a0505500399081d00b410301915028015241040b01c07100000e0103580400011642818407450000d16200045540307409190310100000c425140e0100b01c5010b0062841c000b1441603482c0300000046c0d81d041c2c01030008450740c501254136036820004000c0d850340000d04d0780d00d0041c003c00140006070384c046000c02502d40210b42c080301814290500707022a000d41c90340340383c2000d501018098a92034402d00180308030300c6050100d180e00d464003404005034011440080c01d03240d82c010241d1a10309198106840c24458040c0584604c0d01031000a141c64003039800f003001c4c2d11200d8203010003600d640c028548140b400800030341c51400c200020030081c0c00f061141008242d601c03880103080110f406800520403000302c1149405040042009400c5d90000341d002e8046002d0030f500e28107040c026030b5a01d0403164000d103220b00b034580410602c0440c010902084a0300034041010080607941c034030a04c3da07a50b0b2450002030050b081032038030610380995aa40801404094030b003000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 871284271 1250 871283021 871283027
    0x712020c06031302121603050307210503010905040f120509090a02090d02190b0a0807080a0603030806130e070905011a03090c01050c010e07140112060807030f03021f0b1807 76
    0x3e0301c2a6040c1c5242d034020841c801000c0c101604d6160190219450900c004288100000038207020b81c06804445170002103000b00c11aa08070104022020403024070040080400591111307500c18000ca040100340750302952941452160010104046000401c20103a213041c2101d0071503110086d40c45c1103240c0b601d000c00048508004800080c0714041f4001a0965204059074a20080403480c000c651194060140034020307190844003500000c1c601030009003525440d02032081100c1d003540b0740d841c10b42c40d56800d10a9607950000c1101e03000d0385800c4421000a000c00081004090006000820b1350514441c1241c2c02c2c400c036501001240b00740240800d01d0008980d009191000b42420b9a0301c154040c480350141000380b0712103542c2d02a51000091290400039410200182603032043d013440350701900181152014011000f456100b801d003800020740b400c083c1e0301c1c8140280103c0b1000242c0c0c5001e400c0305045080c1c1da4681d1030b10703401c0d20121070070458403c51050300d0450720340040d86031000c001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 871285521 1250 871284271 871284301
    0x5060a15052b110f030a1d030403030309290103080a0e06040f05010807020a05060c0307140a030605150c0a020d08040503061e0f0601020c012106030606080606040516031a060712020c0603 82
    0xc002407958810307e00d00480745010784c0c2d0700303080b41050690361110b80d00d0802400400748800299582980d6480781c4161101842c0c404150340b581c9441300b0000d90850f103038509550006604031051003a0004101c444d03507180000350005007000c5425070304060802c3c000401410020b05180103640c000b040700800100d001c00c4140d4000b058081e2292a51703980e0340200d03100c445410a0300da490400140c02d115503541500101e0a0761400c3d25500b00c1d0310303030307a0201100610410214034165044a0794400c0180380030708081200381e000b100d2940c10142c903900005d04001c0290b40d010075000a80d000e03100c0302c0e502c03070000592048445406408916103040042c0d200d800704500d080c10442c044d0542481c4160200303950020700ba481204000e019140e01d0700d8001010140207000a901c940400201186083d000d030520a2004c00c01c40b0b030b9000351102040e0040e1004031003644400c00d90140d107818949514010b4202c00740944c0ca03d000341e990300b04020f030410f080829040e005e060104100103000900c1c00c89 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 871286771 1250 871285521 871285531
    0x6030712020d0204020a030b0a06020c06160f0606150f090311060a031b050d3605010b0303120609060d05060117100f020a02070905060a15052b110f03 66
    0x90500c4212140300103010601842e8000703501500c085901d003076069059100c0e004400e001e480482100352900310683c0e032918401000d5500200c10000d002080c030021401c4080c1912914506480d0100c9540b007130240d900e540c018494020340846016509607220918560400450070103440890442c0c8646018180d0360112034002e0400080703d402c0540700358044e01490b503841c2129003050140c124010120303071003602c90000301428005c1094042e0350320341d02c2c500445001007041c090070700e041c4c0d502042085c110310280c0f200d560f1038005030143e0301c3c180001c1c201400081d034044418580801040750405000d011036000740e646030004000a080090140d040d55110000242c00a00089440d86040740803651420006d05050070094051202d4006d865948000e07025200c07001c0d00e48801070100c9100b2529a58090380c0c1c0d030010031002061400e82d001e00b8a82e450411b140c4018a81c20039683c3c65108001d04a151800054a140a103288180d1032022004c02c4140e1a00f240e80d11028111b00010780 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 871288021 1250 871286771 871286789
    0x23030402010c051f0606260a050c0705070e0105121f021317161d04060b0117150f0a030f0b06030708070801060e100521030f040e100806060307 63
    0x4202c800b0b101e010420f142a945000719800c601c82111900c1501401e200d10502c400305010107244080c08a840100800304043c40000c840280c1d100801003002e40005003400680300801c0004102094081c040040a07080f0301c4402c0e041c651402051265081004017005c2d004d81000600c01806484407140010580d01314501580351140084440c4681c101a8008a1506031400103029000d101141140360140b4240c0c40504403503491483c00100a06038140c8003403442c5d400b00050001e6032542c8072998406044c03514005000c0403154201c003d0310f0540c1e18030740c441800d13001d10740c4504d08603601c5401500107031900b0300b406185a5800c480045111001060b4845500010780c0e980c0341007000100400d03018049800099070b50400038000d2040c1d000d003150402c6a000001c14131105c40044504542e0041c1500c901d140d100800309040c48042100340010740010400d280c1543c22030750141014002d440c40c0444a820412641d00d900ca000b0b0b030050455420000400c83d1560f4007040031022544105 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 871289271 1250 871288021 871288037
    0xa05100c0606090f0f05091c050307020a0b2412030a08060315070c060501060e0612070311041508130f080c28030e010908060c0901030f06060206072303040201 70
    0x450080082e00e00341c0c1080384907919080c04450802c04507000392204003c11001080f45803240915070f41c4800800580b0064088441103590304e181c4510000c1d90701c48860300c10b0f5402000f5582c0c2e13201c4080c509990701c00d8003d030030105518501035040104010004101c0d4034418a03960060066264042d6a41000038081d503040021780640701400310061201d4815040002071400c8a4058200e407181041660b00c2031034000081507840c0104030080703044600400c942c1c10030040c001c291045080c01003a0724205600c410880b034040411a014101600b8084900c400b5002013101c020a0306000a05a640c1d8182e81040c4e04080344a48614819458200d802d05603901c403510282d40c40c00360403094101c00c49048420006004008043c0200c04070b12a50b511024540c0300f100468000046000b00c8001d6045240415007a0b00040018a1040c1d41030401044500503c291041100c0c1640d129102581051080010055200300c44036401800b1000c0c00341e02000030005066580130040000b81409010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 871290521 1250 871289271 871289273
    0x2d090d171305030d1b0908031213050a211d0a0308091507060515040507021002160506010f0806010807080c090a0225030f031802100c05030a05180a05100c 68
    0x42c0121035130004004414813118513a50500407402c8407a10340c160000c0c01c0d41c04d004c80d000001204580d03404081040c48441921291060b040c448484c46040720148100f44001002500c2078000e80000b8525401c02010b201c0003030800b410382c040c0b035a0040c03540c144041ca1005940d5481001806490b0401c40c0c45440d1540c50700070030342441e0100d07009464900041104410451580c0240d44a00e103c0100358006140540511090303070401c0d0b40e21005600248860665440781c1d9019144000d080203039240320901d103031285802c0c800b00780c010344400e40388008140410f5408010141c010041480100201403418855903120494114002e100b640c100002c5121160b01da0142c4650403880c0100c03405d4801c5c11035040c043c50500c1c142c1240812110404484030b82e000e44103803001e01603544041d0740008207590800105140c1c02d4903800a01403620404804500f082025000c949425150180d541c14400303465400184400700b2288202c2d0901e000f44510b40742c01034140b00030020350402048030411 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 871291771 1250 871290521 871290523
    0xf020102031b03040302190e0f040204020409020409021840050106050901021b130921230403031202280306030c050409080901082d090d171305 63
    0x41c00b0429648410104006122076002100600071213100312207110700281580c0c5c0d0f0940100d058480c4132403240f171910001f10240c01851405600c54402080140b5003512407044800300c1e0066008541025404a40c20440c00b009400c5220300b40d02c12034118066030030000d03040252802410384c0c030450070540d1001c241c0015440d40d642481d611460320a22140d0384446000700a508005c2440d4010700c540656003421a00c0d4090201c2096005060120300d0300100740e90034080c15400c074048a11200d690242034802c0740706684c000aaa07887d44c2d46664814070018007204001e0314015010308807a0801040001a0b0801c0c5462500300d0001c0000d61909226403000340ea9000703004500a0008072601c0c50110702c3c0c1e25621140c00c1c1c91240e24400384042c1c8031002c0c042213401040d0009c20b424000c2240445543c0a074000a03400101040780020021940b48103501100c0c0c00c414210000152005004107500e0a0151910940340c07441c0c000d03030b400e070388800022a45c0005441e0240d07d605428101090040c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 871293021 1250 871291771 871291777
    0x2c07030c0c080f09091012151b0833010e0102030403050a030507050609060c0a030b0301140108010c0f050c0d0305060312041d0606130e091203010b040f050613180f050a09061112040f02010203 84
    0x100560389c0c4000c14003000005041c3d204102e40340b0356010041005050406d00301040c5021000044161442a42510300150b804a10194009041d44003c3c00000f0016000f0020350b03070841d209985154491069150080c03a040014121180359008a401c120101032039a055980c000350074500450804603100210380107016110205118064400001c45c5030031054200c2120139841d9928081c114261080c203c03100d0150082c1e05003240c01110818140740d110b5003100750803c4004003a980700d001c1d01c59105100394466441030300010b0f80d820005078003c042200096101100350751161800c2c6019a170025500368a001e1b16101c142500d000c41e0300d0340d104000340e086941500003001e99030350f1214080780c0140c01038852241c0b104054100407070141000300030b0b038020200e43c00c40d660810f03091082c0d02104139200d104501c1119035480c054600fa00c0903004083c02545103020004850b1140c1c20300005407040c5120344801000100883c0301c00a112103080c0e94056040202c00200507050301c0100e007144 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 871294271 1250 871293021 871293041
    0x506190e011d0709110904050408161a010e040b0612070b0f1e070305030f0c13030f02011d030c0111010219092c07030c0c080f0909101215 61
    0x261814888850340e0500d00c2e00a4855482c58080303c032002c0c0e48528800650341901841103404800344a480480d04158000c00c1e0840d10514003907051040072070404000b083c0314142540c007075650103c11500030501c0b0700101c3c05000700351350709201d602c1c158450701070704103024010303d004035503495a0f80300d41c00091000d41d018000700309801341c0e030310085281210b1603000200c50006403400841e650094902c01c40446403801d5254941c1d90a543d5101d20a980300301d0010010083e12500700314448507000d0541c4000051481428401207100041c00014807402502044034400c0347d221038128100d80d00000c5800e4102003d05e802904044a4040c0034060301a00e00c071001c601441c614641c24550b000f40c880010750390030f03101c8000e0701c0b01c443c04501c00c40c9000a200880c070070b1591001c940c0c01482134201020818003410711096040190f40c40e50115401010b000c9044880030415000c0ca2801c00c0c990750b000844274000f1040c150034215400d02c51412543c0003003800142ca026409180401d400110b140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 871295521 1250 871294271 871294273
    0x30109061e143115080c0d030c08040b0a02010e16210c030c2108090d08190807030c0c082b06060215070c03020d0e01020708010e01061e030506190e 65
    0x10343c1841100f1480748100040b00e44a45081064104840220400a108a4403030f0001049401011001c0c08240a0a28425810040b005402801080c030380b000800050040480c07850381e940d0082c20013400c4940c500350511554008003000c1803c0000d4410400070b072a0319072000c010651010b00e2080000350400c00c01004e000200c440041400003514030030301103500c0410244001c030300700e03000c00b010b081040f440142400340c240701150799405c2074051081c491b44281d00d510300d0000c2e120180117500100704a050b0010f00c0080400012940c907004403d64400c20b801d01c100b80a406a0340c0846502a4131081d03181d0302c807000c60040e8010300f03030b030110f505c0107000742d00402c00300307848000080d140c03802e4030503170104401d007040400d1005108000006815030558080c1c00000394250040761000520740c074203411031203041c00c0455141e44c20320890000c0302044000083d0a0329282e146c0c28240340321032090b1745501c40b402080010400109016610207101d0306240e4040d107460342058010303c1e0481d0b0380005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 871296771 1250 871295521 871295569
    0x1171e0705040f1d03160830090c010207030c090507020c120d181805191805070603060b04171c0e01120b010c0f0503040317030109061e14 61
    0x41c040d0798441308031682c0010002d9000410080003036607a100302c4c020031a41005400520740481c14403800b400054102103071032220721640241d428841400e11601c07140c280042c80c10300c00c04240410010b2100f00c0d080c006081102c0c40c5445403c9203414504c42c42c80f13441c0d04c400008518510034010708034003100003001d010314860100c488594138548a071049010485c442210b0018180c020710b0b410455000f07003075242c0252240401a40170b440043c1183c00700d403140d01c980140240150140060540c1c400514840b00001d5060507440c00340c03694080ca090500c2c041043c40100e8114048a09551510599000c048402e0310018541000390b00f0800308010810220003000c0d0b8000103400c0844400d03651000b080c0c0140e40c0c00f804440d1030078800c0740450f483c064a0390010300c203204071010040c01030041d0383c1400c5c0e59072110401c240b505011188950380010052140042c10312818014003540d51103181e2040080f40c5002040c1124044c05d8405414030001004583c0c440c0b41200d031610b0304140402c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 871298021 1250 871296771 871296791
    0x60103110a27170c0103110a0c0c05041a090f04030509150706020a170a060b041517010306140708311403042903131b150801171e070504 60
    0x103012500c1e80041420f90103180501d01080d1720a010711340c0000700d03030f04880c0e242100340702040e00c05042d0100d0444131794514500000c2c0c40c1c0e8491007414440117031880b800f07203604d12170010003c42c00c80044c0460700084030b0805000102c0e61050544c4c00268050395500030950001d8400e20060042100040c010340c00012415146684a82d90f00740201000520294588031403e4060544030140111080d41c00f060100308840d80303900400c420003030598100000d0769002c480701030071200c400f41c000399000303038031102c2c008111908404904c1d40010b0f07514080d5024100b20555508940088515499200c41580f03402141e6134190303043c02d003c80d48a0302c40c0d100f003d80f90503225101e401511803031580e10003445000c0900340e0464418440101060812032541d0340300440701040d1742d141e10f400e660300c00303181c2011040c2d01d82c0050103401600c0c800c81843c0882c0e00e004001007806005801c0f0070649100d488500403102c000060031018606502800207004440034900e6143c40c000740d0000c0e9100d400d06214038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 871299271 1250 871298021 871298039
    0x1a04091716030f0c05120f0d0204090c090e042f120105060a12240608070603020702090c0a050a031e09081b1c0513180b0405060103110a27 61
    0x5260079100340c656060003001c00d1800d03201110f03881c0018102d500055404400b43c0b08580040036840c18161650341803941c000c40e0182284c000303801030a84c2540d2185815420f980100710741000b00b4860551a209140917611080000d8251401c4a2501d441c01c043c10080e0400c4021844801001751020602c801e0341208a4081e01c000d40d01d0b50f00400b010325000c524101030150407040760b604404031640d95001813450240d0b5541010034500c08c2a40e40342c02150050042c850030300108881c0e030340503071160030038010411094000380206800900030480c29034156005800c4d24881011402c001400001d029400a120315008246403800762402c80b02204000040010701001c10341c554090088490306000e043c1d41d07000c90710042d03034103206070f04160007068400d00090110036616900200740d10f9846200f00b8039000551a00303d00c042e200c0354a52442e09051080561000c001d280c03d02460048060300011845150500800c00080c05100701c50b0b00481d01c14404074054104e2950b400c956a01c03e20 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 871300521 1250 871299271 871299307
    0x4020a091e0e1f0b0d0b1f030b01150f0f030b04061509060e0303031e0702010f0f02091c080a14070c0303020c0307090b03030d05090c030a060605010e01031a040917 72
    0xa424a251000501100703d00707104031403507034a000e002c0200200141d12a10b00c282d074002c0c0429000010441c00d0000a00500c0c42c450003076100d91401030341d65050296080800040b02034000402041004240b50390754041d60300546010f6506001583c5c000c110042406400380742c11041c2058100c4048901ca282c0c003c02c003d00310340c007540c2d50b40202044c142c20161070707100950b010030010b02038910b41144405010100c50300f2240d03a0000040003c16121171505607000c1009010760507601040045d0701d41031492882540900c030742c40c021100482607a4042c4203008403410401009007550815a0403d968411950040c0d04800921403156072454000d5460782e40c100c105001c0d004000000600c801280159006000300030080d5081107d540c038000000c003001801e010081c8a0f801903000c10380c806108a4060070b0003000042945810400054001c58180030f034103042500c1c0c4025179a80c034048504203007031084100c8002c242405e680c10031030301c005240000c042514400180703540040700032400e4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 871301771 1250 871300521 871300543
    0x313060c020f0d030216030e1804030806092d0c040807030b0604061d04020108070c20010306060e030c27010905040c050a0e130219170106050904020a091e0e 69
    0x2215a144603c21044050340206400541d244801c28040000030b4003c0e91018204500604102e210404103c1061560201074074103a0101da0004180305d0315042c001c1809078030000130f00c0c51244111480280090301c01300500f0f2184921204408036510050490440700200401c404403409580c80f4107084958480c00e4480e5841140380c5180041d1030300300102903009505040101d1900b0383d443e0340054038a00c0008201c4400c00003114090350002c2c083d424101e620a0222404000246a050000d02129000d801c41002d10848540010040d500020b6921444100380d441d0b101c2140d00d011020036691040c1e803028100300d07050f000810074400d6a84560b105038054a203d414980c1c2d103a060200301d140500130100c0c8611600b00180900359000307078003d51503101a05c03105496480c620030007210304980e00f00d81c5007821410103050760304d43d09008010142108846001450405500140c1012060705c500794503c1e0f100c5136030081c1d0300c90f039900300c01401a04c3c01052203400e034856206920b420309124 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 871303021 1250 871301771 871301773
    0xb010513030b0f09010c091401031407110607020331090203090a030306061e0c052802190509010e1005030706120f060609050d080405030d0f080702120d020313060c020f 74
    0xc0015100041400741c6d0b0035202140d01c400c2c0c6094100070300720400700003080006051580342e2142660303513034180c1b801c644184695554012042c02c0501c0c0241031440143c43c032001c541c014056030038001c011440c40700c7c0c000c002d00c000703107000e080c00911000b0a01e4190b2001da0064400300400c40b817000003184403038515219940c10441582c5400059034040b401d4069000350150251010103514010b100500006006004550f000441d2240400c2c0003480c07480b039400b2004014140608600703107000c0303041024a41e814104456824480403506041c014420340759101c1c404030101d0300e5003034001d2000000c0c00014003519240360712004003a040040741000038070b402e450101400c4c441c04540c820309c1e040c0c0701300b40d03105422140703440204401c01180d41400d5030341000800001515640030441d080d10801c00e52262510340c0840d040151038144000c000c007055402c01c440d05110020304200b100c910249001005880362154004583c4010700340c0340c0108843d142600c258115a00012a0652408000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 871304271 1250 871303021 871303051
    0x3220209070917030c0d0c03021c05130e090a08070317040b1905061f05131d0906070503190b06072012070e0a1814240a0b010513030b 59
    0x78590130b6503440b03404819101a0001c0708506030b4540b080c010303030700002d00074030444a0710003940d0702c4200e20342e51810a036404208001820344100d01042d48480081881c00c0d0701100d1850302c09a020f48807942600001e108010020f52407040601440b02c034800454000030f88503007444c0a141000c501d00c01550030a0b000318048070200f210015034010035114020282907090203c0d82c5504080c0c50074046114141800411302a00c202115692400c0006101164506004280d21041310725000d10151040312550003441c10450115002001c6070740081042c134400030004460070003140101f040f04521540200d00207444401d20103040824030240090b090300808600c01e8030208615104003c0b01401c01ba00800f6041101401107812103a002c00d4004010604090481c00441c41d088219012509406005607000d060340303003006000b17140080811a0700b8520881d1140720401c980040600c0e0105403121280c56803a4418416034035040c4800c421038410b5a220b00d031034041c50350110760f0464500ca00d6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 871305521 1250 871304271 871304309
    0xf011112030f0f15330301030c0b07020a0e19020307030b120706020d030207050102040f080304030605011208030402060901020c03010c230f0714010e07030b040506100b032202090709 80
    0x420010f0380074800001940740703410801801d208090942480000112601040e440c00d694044582035540501000404d41c0e00e40c1949004210b8000e01d40103100300c1d21045c0300d6400141c461650680070b07140004c0d54850b441e0703161094117418418a070551901a03002009110855825401040000404560700c006107842540c1c520303643d007458800c4100580c0303c5c1c40702407a014020f6000b403003010f00a000140c9402d80f6025403492010603640301150303981c8001410400d11000e8800e46025001251030b00300300c1038480d110014680005070004e40705000c0001e84c2542d6038002c00201421410140092211603548070010780100c00c10740304140381c02d07101aa4034a85240c0341086601d8003021003415030a000007904e80740f40c0e80244030140c600c4c43d0b50300e62000c240014200480e2009502c5091a101d20385401d18001d802c080c4040d0030342d030190100035014840c11040006490b0722800c021104803580525120401c19810180c20281d00800380740c05122030039500043c0304c0180c2d0f01120142020f0165 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 871306771 1250 871305521 871305541
    0x21803010b2202160f02210a080c010e1204410a17060403090806100303050a180305010c140a0f1b061a010e03010207050c0f011112030f 60
    0x40d00786016030020005803400b4a80a10802c0e0600c6200801c01c018100021040c01c0070103002c80300c00070707101c480030b641c00282145821200070240d0b0780c44085400396052142021659644908801000346c5404512208082025404656502e201108035031344103055640d26103050b8864018072122450001e03400001d2402981c0324a03003408100d1000a8820203a620000419858449541e1102d002000000c20041c40821b0900d090000380c040c090504082c640078110903610350005601e0b400ca60200440201d0031003040d400c59402d130502e29959807901c075007104c01251007903620440036030955001c028017405501581d14051140c550701850200c6070540000e50084148402c00101d0319004501c0c4540302d2505102c80c0d02045201d081c2c0035029580303000c00d450300b140060840f0000c213501c070342e819130b4010710403085460207070700862134200703541c032201e03281c10240d80308a004c1d0070030349c040c1c2e00e69911074044400e80380c3c40c0348240c88900c200384607400c11076401515644408816000891141c1030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 871308021 1250 871306771 871306781
    0x21110c0609030303060d140d0e0a06170714040f081e0102030c1602010c0204020c150708070c1b0506040b03100603060b1611030105090109020918190804150302180301 73
    0x1d4002e005509641e40c850420004111403041294610080007104403904805c005081c0e080762562034004002c0801011701900180c907600803420890710010350401c3e920110402600501d03141f0740810120003940301004e01c2e02c1954172820017607a0304080000e074080081420b04a44915241c2c00f1000101240c2907820b0780410340f00c0f82800b24003080a500900b42505a498030301e403040c18070078100116900020120780001b540764015401c60120450004007840045a103c140340c108100c4504240400030229040c8000007800420303405a00c0714403a605d00c0820000306401010700b87d0701c0b0b81360000b038040c5400590f1075400000d0391810200d480d6000303009000c2a600100401410f00322045586144112943c0095035010172042d60f40e405c0e81c5080c06020b21030340100002003a00b104078030510006000c0208a03490015940f4070009201c2c81c041000c407558942c030302e042c02c50254641803a0300d02e0300c0369900c03440c0035500e201086121103406030080c096604004e00c0c1c49030071070000014942a21 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 871309271 1250 871308021 871308037
    0x507050a02031e150f16210f05060a08031803070509010807170102041410260919020d021005040801020319050a0905060601050f0d0f060e0709031e21110c06 69
    0xc41c0200010901c00e21194031002041c01c43c545010294841c02c7c0c0c64981481803664040712940781c030400c584ca4110b40c000d075500010291414400c0c20318080c1d2885d128000c0f9404030000d040c190410346a5035604000201c041d010003040c030f030384a5a5998015507102c40c1e03440b800508645040841d00140303410b10954040b1642034601400e18411082042021040303649504280110100f031780c1c00c20401c05000c0300850444041120650030701c107140ca450542801c5865540702401d804040050b00e802c00ba00c102c0c0d0b58107944507608181410010746860040b504a01c2c0c50350300c044200615200035144010140000c0740f800c01c900d40b07032000610241c030703107452000e0995070000020404075407107003009146c118595080681081842501c80098414409441c1143da440311014081800854010340d081000c600340000c00c1c514555542c449920100e1042040401348103107042803110705500e42460503200c03070101001031580c100c0a0300300041c00303441c1c0c400b42c894090390760083d007400c01c100c0d1961 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 871310521 1250 871309271 871309291
    0x20910090305120a17100503010b22051810270206120703020d180c05011b0b060411031602120a0207091a0a0303051b01060608070507050a02031e15 65
    0x400f504100c6003900c2e400500c0040c10030004200f020404103c5c8950103014511480f0016803241c5042d0415094030444209284550b61341002c4170036011a1601440c8900e00c1618049010b42d14001100d0944280c2014a440c6009000000c040182554400e2006480740a581400d030402c0e01d440444001c502d02000313400141c200100034034100401071560b13115441c0c1ca809403030003107410f00080584481c200130340002480800d403201080240300301c0c1c4001d005c0138a8100d80d110305e049508414803400b1800903112a0000c000714075151640e4001c07000306020000101d907281003890001c4034400d009103c0600501810340e00800c800c00c00c000b241d024642560060280505010f85100181109134150041d00b100714a0250360307483d00c1002800a6009403550703a200c4c07208941e6a080c2a204a20243c02645030210500c02c5a42045600d9041750003854059200c41d5030b8503180e45801e915410195140c4116020a03840424094820b424100190141e41c041c020241220000c070b54140d850810b4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 871311771 1250 871310521 871310533
    0x1a0f0106081801060b161a0c04031205040f2c1006140d060e070f0906140f07050a060605120105011a1c0c021605030a020f01031815020910090305 64
    0x1001642c82c0300c40031211040000080c038a69034008003200c0d900030710a58521154540e00760302413009000000843c210480d18655244c60141c070b5001c0347d4032503030000800d0b2410210800a000303100c0c800740c1e0081c01701071300110380c059222086500b4005072103d426404078141c0800141590343c91120500452113100c0300c214880c10b110050321140ca040c880d910100350140700d0b030301d4181407900651008002801e0695810304240e030008204107078070380c10036051004400d07007003048a5200b2031b1904841d007444142a2509191300c081c105e14400c01c50084e186209081000040c0141c581c00582240c1c01100d41011f035460782c407031950a81794244a6500c0c1884070b1840070039449401c0c0000c1c0100000340040b18103c0d06041ca03e07a049036815120702c00180d02020381d100c00120100c100340e024010417801811151039590009813080286d84095040503100d04030000c08010402000d0041c1c0e40c00403c54003140a103101e15402500f10307464051042d420f16900200390350080b001c0205603074000e0081d0170 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 871313021 1250 871311771 871311781
    0x80f0c06070c0b151f020123070201050c0a080c13031401060e0a090f02040506030a020a060c120903201201020a0810050a0b1926040203010c210e0f06041a0f010608 72
    0x1040148100f1170b0155504c60050244051492075507000c21401c81802c01000c2c1041c000003030844000030100e90201c6d004000580e54550001c590075801001e1f1041b00343c1d5000014400d0807010705940c0000d017001144070610180260641020080d0703000c190381c040031680c5058040083c0d4070010000b40904200144000150419030800760740900060101c4025650a9020034903011955201323200140074510403404018a40b1150300d2000d00618000c0c4485056417122803150949040a0711990f0070304050f942d482d2543e50128000c2c0c48400d0085480380c64044000d003151000f200c03074100107a58007401044500d40b2584500948500c00503031414138030222980d180f00d0718040c00b500184440780046183c1c00d0b00700e84e240090512004c0010a4508251040c5070139182103a8107001400341c0c0f18800040c4040044c95689400014800848d102c100c0b88070060400020004104607030043c00c04110a03c1045a9100015a480c0d046d48140e0782d00c0740d00b510116502802007400181304040859 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 871314271 1250 871313021 871313059
    0x3091b0a2102092a0708030604051305030a090807051504030305130816090c021b011b0c0e01031e0c050904050c03060103060b0406061b080f0c06070c0b15 68
    0x4616504611618688000c0d900015080c4108640259040c3d400608550002003002c9102ea900680b215004d41802600e40c0c4041d081c1c0002003440b03004594074030000d15100702c1114842c06007a0010240c9685018030f500c0100b815076180a4030044c2c0c812400002402e042c07144440340765601e85403035207080c05d00310395044a0030351000c0784445403060000004100010288402c11098040400e0026260700d00403281e416602007001010641d044424113001c0301942c010780d04c0c070201e002d203040d0a2480280c10507840500e102c0b0b00203071000d40c50f4100491400c1c0080c01d4103041c0c901071110030300141128819103814264455004040c041c1d4038008002605142c14440c2d00329100754280c0305441c041380042490064240d0007079841e02d44410042400b07041501c50340c000741949280c8450403c0001e8154000346d41c801170000e201c440002003004818200350f003540d080c0d481020a035030150410b407400516281e80c0c80002e644113a01000828558104100d50019a5002501081030141c0c070312400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 871315521 1250 871314271 871314299
    0xa140f06150f030c09061e0301090606080f0105101404090c08160512040201050d05070305190902030c0d08131805071b020424090f061512150e0c03091b0a 68
    0x145820000500c0787c0c203d10b00a0000d0029091154000c2548035894030103290b0641b56960302803018003501d003090088545041001c40d0560754152240c40c2030000070751044035466448940401e85c0e0202190102c1c1c858003a401c0302ea020710469071407082d2516800c104020300504c00140c540810380806c0303d4009242c117074882d42d41c03240c0141841030030108040d4401d000d4a404491200020303507200200440c1c000042002e0030f00c21070300742040102e01040d80c0400e50303c001d003c0359180309a00b035000701003c1203002400c40e929404034000e004082580c601d1000c0111021803491408281030030002010355100380300b80072408008800c0901c11210640a10004000001420000882580303c00708a450543c1003a03004000f075110010b0700c4515220030740225011a0005100486606c028400d0b05500080f02000c10314100c1d000103000c0d280981c801e0135011541e0005c481e200c45c250400001030381c801d01035031141d5240350a075000030f40c021002c90461140c050318264000c0101c0014000034241e103180c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 871316771 1250 871315521 871315537
    0x607051614190302060a200702040209060415080103030f0c0c06201603050f030702010507080c0a0f11030c1807050a17042411040b030a140f06150f030c 67
    0xb0b41c1c82c14400c0c08200310041c1c4210800743e015900c990103008003041244950300380c2c0e90319508881464584a502c0300e40b14030442e04080c1c0304d541c0102e030000b904c0c1d40e080100c03802044010041042c0600c00341000d000104248404e4000c42ca00c8800241100c2c01001948851507200b10000405414040c0c10b8614010141d401c3c080401862081c4070346010070084550440f5143d480c01e80b0306840c514250389450b001c0710300101e07950014803610380140d8005007520300685e402011907440c1d04050038401c1c6004560b080240144096240110030300106000c84903005030300f9030503100c44090703440c140500484181500c0e092040200b001812052050014060398201c1e0310341055a00e0300c20040910b070590581d001c1d10100261405400035052040011005201e010b03001e00c090b0000c07450f00c00d1a070145100d8459001300001c00611040c0d05984099423456044005540300d0030001e540100f00c58089070f042e40180041050106450800000d8030030030710188000c5441d5594144540400ea000056 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 871318021 1250 871316771 871316773
    0xc0703020f010c02011a041b11030c100b0f040212041101020a0f050304090e0f10020717071a060f1f0c05150f060103060b09010309030216090207050607051614 70
    0x1111501d103001c00c2c0500da408821680c0081405a030007010090701c50240445903118a00d00707880b4520103807a403012196010400d0070101d403d27a034505c0440b4154415070b4217141040c007603001e4051584034541e00080552206440c40e0405505910920040380700c1c0320a0308003140c01c2040018001011074444242c400340c10300c141c62481260303554592103070b07801b901e0171982a000450184030320441d0340300b480c0342604908002c0c640c0c005d107820f600707071620a0488000c00d880d40000308001848403204c424003101c81c0401d10180d80d039240c0e0905025819640c02407401c10a9110007155441c40e121440780c81e540c50041c4292740c5031181400c028032442d0703001440c4080c0110008000c0c04140d040c04802004052500107001503c0d1541130f1075111280203204a041c14541072007406007046040c1510003204007802e001502214600b4140e203400f520b2900d01c900144c1e034141c04280800260081c1010502c2b850844045840d400c000350f98a0003102102040303503140303c501030045081203000c4105200c07104 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 871319271 1250 871318021 871318033
    0x806040f0216060203061e09010608060a03080406080a062909030c0409080307080a050f0408070c09020315011707081b070b16021c050f090103180f0c0f0e0c070302 72
    0x1000061850444980a541c00c40d8084200074007420590158003150000705400b01d4403280000008c0e00c01d0a040c0100c1d010018108006040b989072074212202071a00300d0491500c440c0c0d0f0740c1c0c1c0103055003422600384050720b0810000150f07900c007104071401001803034001c0029030075001010000b207030006441c0075410311460300c012243c0e481d2071041007005800b902c240d507030324904550080d060365405081d2012440c03401d010418160407400faa0364100358013481c01a5101618140404441c4403a00113507103861001081c007500d40c0705134045040c031070400c0c2c07548019254508000078201c40c085880c0004a1203007000124584c19107201d48408050140d00c0031b040c00c0003919550048282100c50543c6041e40c2c1c0c3d0304001164041281104801c0c0c0720740298008200207034010040d02543c01d0750b00440364007250404181c0c1c004d8101413200680380d5206182c925950070020820045042c05440345a140400450180030340c210500566030113484042481d00c454103c3d030403981c0108010750443c0200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 871320521 1250 871319271 871319287
    0x504150203090616200109030f020310060b130e0c0714100606031a09091b0a050d060c1e0203090d1e0c14030d020a06051003080c03280806040f02 64
    0xa580a04209004104280480115450440628066407170409180710050107038070916030307100000384103803035004000c820101c0492010038a0040c120051401640c03e203c1c020480e0307032452029007a481d9075280c1c18a100c0fa40c0c0c454a8682c200203803440c80300f4207800c110341c00211f0200780e8a038540301141c170102c03941d113201441c0100031140b0540040e00002e071180c91058070001100e00884074040d044400042500b051040d69944900d10800750b074107002840300d21100c6a0b03603042c51100400002d0040c0c038a1900920340b170710040080e182d0160104940300100c4a41d4000c1117002c01d0103140e00e4005500d4019a01e040201c0040c07502821210714007800c40c2d4138160b080c81008008064861200d00c40c140c2c1c20680d260400070a0709450345d00035400410f500c4440340d8001807944800f5044140005c0c00d4580003030041c0d142d09642c1025100c00c40025000c42000c0b03001008009151181c2d03004000000f1005840a2808680c0c000400143d44d080105285180c036a00c410070342210034000610306180 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 871321771 1250 871320521 871320529
    0xa2702060c030d0b040f060b16060f14041202070503073515010605031b03190507050c010b010206010e3d030b1e01180906060e04020f0d03050415020309 67
    0x2640708007101e40d84079090710044c1d04203030003560a4009101c1d002c0c00a81c2c104007460201c1e01888d2031414109191406400034080164400c0c952502d807140c0c140403002c1c8050b075100c2d00c44425201101c501030321078014040c2600c04100315040c3e441c0200035040103464100d6081c0c41c8904085008084c11169a00b0b2511800514030050303010b0182014100b00445a0444840514164030010034840b003001042183d51140c03c0480c000400c160790207460303843e454407151424035900e452440d61407501082c0906c2a4000014126500c1410005d003c05119070f001262200400e11070b034003800c40d070300e80400e000403200207400043c14003401550405215000c0788001e022607122585054000310b0f030f010300030300408416030ba40c08501d079620003003030040c200300c00c0107400380501c240d03d550341050182e00d00d03245442e00100c0aa5800a00c14010a601da003819030790f003c825201248213520304140b418183c148070504151480c0c141d1592800d0903d4840a202050600143c041c11800100b1100141340e03a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 871323021 1250 871321771 871321777
    0x130b04080a0228030816050301091e05070e0a09020c0606010507021207090507110a080a0503061503090309011115060405150a03060506010f0203250c120b07080a2702060c03 76
    0x40030401403030034413401c024000800141074284520a0440001001078214007100c1c1110401800042e004404020542c100e000301360180b00854149014440c001d9441045100315110840f503d0044540d100541e40c200c1c4035049007640344c3e4005000080907903008201403d00c40b40040d201c3c1c0014013604070164100242d541144080b59940d0040c0307c10113034402510b0140704000c07801000c074000d05449809032805046002000c2000c00800100d05445070300d0608500030401d0040c0d40c6070b00f0180c4455440350054815140020752000d02c014860f0b02c006000b0404800588607035042d6200c0390244000f0b07140042c40c6054155058094500944651183c4801140213400009041c1030507000100148000d2040d0021580180070307183c0300e03002902c2c4042102c13114a0060001d1a09884c0c4142140740030345c001d4800c2c40351027001c80c0a2200d00d4140d103109181c1607a0315149035907050088403c4480010076a03041e122028022140c0a4081c11404007003030005101c0c5003015000e14106242d64 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 871324271 1250 871323021 871323073
    0x1606020d0504060c091202060721120b0f0904060f0e12090a0506040302061c1d030d060603230402061303140d09030b340314130b04080a02 61
    0x81d98401c100018444688510104001c640c13414034981444c040d8a0b02004010071070182c450080010240c04100c0c1c0c0f007903502781500d5008a8441d10481c0c41d40043c092684500d161804181802c4a401052070001c070f8200803400c004003c00d84545550b00c07110700500004401640c084d50302c0d1300c2005005001c00038603a0350102c0140041e5121340708028411142c026a1190340154001c1c40b0910050780d8000c01c0d00d203040702103070400349040182c0034080c0251040768a1141d180c4000c50440220075000710081c07031010f80d411001d001c0565200011811901c140c801c2040c41c0203900d5001202000c0c2480c041d4206c3c0c0000c0240c3d0505042c04600c145510381a4012240c42106801c901e041e00c0c2c003031204901e020b403541041041c19145403685d5080c40c10013092504000300d03040044001c1d5102154500c940101180840f00e03085042c64084c00074030074454240000c03031035600003800a041c4201460001fa51243d4500100e4842e5070702e043c810f4100c0b20f040c0741580078400310042c0003018801101d540c6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 871325521 1250 871324271 871324297
    0x11060310050f030604020303071506030b040c090e070305030d0c0315080109230d031e09060204093603051b0304141009060807031431050601050105160602 68
    0x19207040104000c00c410b0708030340c07030080d00210200030250740c0220558034565081603844c018a011b1110420042041c0e4100a1800c3e080307c1c1808140050300800400b645e00c4400e080280c0c0419074411507641c5d440340b00040c07a0364000c001045008456402c00100d501c11400c6c0481e082c208203010282a44998014502582d1341e888004144800a810070280500c0c80d4415503000888840e2544c4903855960100706140e1070f002c0101000c005030f10800f0694181c0081049603c1540c81d08001039800392007400c50312804c2c03400880055103014403120030b00c8000b01c034059004014040300c0c40c202d1503005040c0c050040c2480907502420350a03c2400052210401075603480f403e01c910300512a074680d1703071180104803850801c2d01d49038000d0320010aa880c141058903065450b26011806010406441500407001d04244028541403500d0704801145a81003035015500208030580c07929440c03a070103007050b8040c01c010001d65014000a00c84250004000c010554198541d401a68031034440c4c0610 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 871326771 1250 871325521 871325551
    0x71101110706091101180302060f0d0504060603020108010609060203030414030f0d0207021e1305061f03050f09120a080a0609091a0f0601020a151d07030c30110603 72
    0xb0440d010703441c44072100f002d08111004040c0c2c200701c942c081046c0e0000a0080c3c8000614131901c002e20030903241d400f41000001d07c42071801d40b0b4a540902030510089000c030340110004143c0324060000300c801d46580754010360560340c803501c3d811100d0100420020480c0000c200c1c40000740c0080c0c000b070030000364414026950f40300c2031061022011000105a15010030030ba02041c2c1740c1d492601380b5800305200000468181c5841000a5810422400803429400d814028121203a01501320b20720030a08880300c0080c95884071400d030344460031030203440401d1a040211101b10342c0515011030b040300102e0000510541c40c2e401078070488001400507a4005413100b88046924240460507602003d5602035079034900f0001c0002c1d41e100c1d22558020003442a140d400c1d540204c056102ea035562000110071040d0405a28100f81c03660050701081e80c1d0162640c00101e406203015000351500c03609041da0310001001d46d824404941c9204004030380980800361311a185949000245000c1c580251030031103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 871328021 1250 871326771 871326773
    0x20a030c1a0f0415140d0e0106050f0a05210331030512070609050a0b010e0c030708070509060d0c030e07090501031a04081201060206060913050607110111070609 71
    0x100c104810107a0701018202009180d04076000344042d1012500d10035032814404800480c01d07030311400c240c400c03030503d510082000c5050005030f8114021410380318008100c056140c405002e540c12014a003107070803d41030107082050b401d0000d1114080c0c41c00c05081030140005110042c2507a012401c4100c2c085401400c0503c1d10a402d030402e1649090341c40c4100344a0710b036554258170380c04011003607003c680c0045500c6d820f01c44c0035002842075903404800c0d200302408524040305050400c0c001e00c4034015a80f00010684603080707080364080c0317a40340c0340c40310a59683d8400315650344c00001d55641080c0144407044030031f2120301031583e02c00507644001c10030035248001189401341561240f54254140801000416042c811000240c0048403055008d83d8841c20145403d220b046428a41c2d01084800040c00365400710b00140280c070115800085511001d0048400c0003805c04003a1294100c40c000c0f030301c81c0f07009050309810303490302100124041d07400320200001600081404d5540c2d81d184c949800c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 871329271 1250 871328021 871328039
    0x40f05060f043807051f06030503160501050708040b06060304170d1b0f050417070515031b09060a0f03180507053a0201021f020d0e1c0305060d020a030c 67
    0x644002200da0b060b0741015004d440341c0e40d4444180240d1a00340f0603101d0140704051587e000390004c0c40c1c000c41146d0f80c03150486c60300c1c3e18100103408140d8440d442c21000c82e044501c21a44a40110f030403642e9400c580d202d880c06c200095101610440e4940035055040c480c1504840292a5078101c084000031304d40303072001540d40d10364400c080308401c00502400c0e807401c1c0c40e00301050340c0c191034080351103466400b07866810518000c2c00e82c0140d64130014001180740480d24250086220b480c1000808180c1509000548624012072950315408107040c0042030b8103610030742c5041000080c0b403602081210810300f404402e00040390058440da04100d40500040c180061a604030140400c2d0317114107440c110401241c400a80300075031009010100510003560b05c01c00503107000a4000c044035900d2040071030060025807244e000789040506090840e08030490200c1c4104a071480e620700d10800400c0650220002c10000300516070010241c010200580c6407000c50038081e51150070800840b5041c12001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 871330521 1250 871329271 871329359
    0x16051606050c07120e240904060b03070f02030406050d24060201020a0822030f02150f041b2601090c1d010905060102030403021002390303040f05060f04 67
    0x40c002e12180030032942540c1c55106d042c0701c904414040554209800d100c225a091148030035072a406400c104000c00d0110201d00154000c10392500c80c0c2d00b102c103011b081a80c9030b0080740f040301e000c03d82c140a00110801940c10100151400301404030840c0e03803601448811035884c1e0440310042c1c2d8046000c83c88107410240d0607810000e0a07080351400c41189203140002d003403008000741001150040070a00038000c00c041c009031814008501d6280c544444040e01d401300448064841c0079916030741c0c440c1d040180c0b09441c03e45d0740310340e24060402034010a0070700e04622880300e01380b69943c56001c68085040702485030301a20402401d07105400480841c186401010381214642914003001d010307587c9e8000084a040300d9050310680c880c503204010603800c207445100040402103458030701c3d26540d1030585a00c08100782c04000c158904051a0a050303582c050b60056100104001e141441149031445c080e001d40700c04040220b10305611025881d080c8804062460071181207010400300a580400403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 871331771 1250 871330521 871330553
    0x30f050903040b0a050c0f0d0e06030f06120a05030f03011412190c051e0901141c21050c060a1815060b0c0709050f16051606050c07 58
    0x5002509151404640300c0c03080b44503040b0000390004049064500410a5031020140c08090399041c0000e0b607131b02602c8051407000e201c001440441104010315000d400e4a0203250044602c84051755800d040c00140807200d100101c0c148501448000000c00800041c03854001e1560000d482c0d5140208001580780030f000e040f44900049820860300a400042c104041204015454444011400c03c80c030004026000241c101a40030074032204405403822040c1e00350000e85229105aa072010039049254010030a690b200c04001d20f56180c4c4141c5101030501030b4003620118101444182c10480302041007076074400811408602030051000c184541a07001e181403170244001644e0035040b0503100c88a01c1c0040085d00c0d0309081102d502419413141015152038182c0035521120106019075941551003020f902d02d0800d000512606500d41e0428040c5451010120000c41011400d0340daa800082c900c03602c40d0b40304100d11300400c1083c000d003401604485a40ca580e08040d0034100e1011005600e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 871333021 1250 871331771 871331801
    0x412110c060a120f1103040b0703020d0e01020315030d021f020c070602070f08190605090a151406180c071505100303020c010801061d0a0503030729090d110a060f0c03 73
    0x5112031144100c00306c99001c0d074802801d51082c1d6441c0d0090300240901d01620b05000d00c0d003d00741c0403504055004500542074001c43c180401510810141c0ea0f00c0810107030303801038005103010b441c08200c0c0c4041c080500780d083e00240c18805460349040c40c041d01c1c1e134010700060b40207240801c95440c1d483d064401502220000e01120407039050103895001130104002c040c079070b03940005011458107108007001d0342e42c85000b415078070341254540e1000d021382030704048080d4440c0c0045000e901e881c065030080721041d40007800c110303500c074241040036030805402034401e000d00c0c05882c0d0051040c1e100d402e204100a0000c800c2d00c60442c240280340004103032a90f8107018404c0014080543c001c0341d003600c29106600e1109040e001c1c00003181c11004a0f034400c80c2c242c4030202d5110104040151040e00e048000d40c6202c0e90a00c582007142a01d50060300c00b040c1c0358100054854465200c0c1440701c07003e1001c041203030341441c4590750f4075048035404d910100c112580c4007100307120385606020b00a440d1102078 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 871334271 1250 871333021 871333031
    0x1c0b0901021216170c0a0e1807030e10050124050c0a1103150a0222120b060f18010e0a0204061b06110f0c070b030412110c060a120f 58
    0x1400c5002030745000c0d2561203504000d1401812084c401c0c910074665099288880c400c6003070070f01e400358954002c001960701203030780618082981d04022103214030002d4030090140994807021420340c0103154083c0d11030035034000d03070001841c0020180612030081418625404078411040002c42941c00304440442c10414104480f07079101600183d590342c0150800d4200d42011940300000c0e00c0c000542e51200c034261550001c000b40741c1041c1d8007030018882d440403005d40340131254020f500204102d006007032081c4081d2843c0c401040d0900e0445074040400ba080c041c00b44030982c006845500000180d8890261039001403204100300c04080760004e9910400b50b081a007400c02c090502d0403110603100c207034a180b448003c01c0c0003040d00042200141e0103002030740c580600c0718190325a031041d40148407a10a00c500025445004012284980d40010780c1900391800713190200c420240d12015841d50703100312042c8040d90b541d030380c0c01044e5010b0140c8414036110003141d45101902c800801c4490804e00d40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 871335521 1250 871334271 871334287
    0xb04020c06061909150512070e0103060203090c1c0c14060706050411060a180803070309031b051903020a0b0c070e070c150c02061f06030f0207021c0b090102 69
    0x525281c1158044407150307583c00d500c0016901c1072025602c40040c06040205100c207941d0000109415600161501718600c0e815170810342c0d44410a200d0752403da0040c4004002241469014581201c5242c0c142c800c80a1400c2c001074076050344104410407460044c0f011810003291080c6000202140e05440c458068400001005ca008112014019a807140009010460030144152110303500808040e2240105031005260340700704c0d1400c01008440290101c3c0f180400000c0d510001c3d850354524120034259902d04600810318000b18050348090000400c1640d90701c50344071480b0701d990b940c5101c00f51650040249980d59a4000380e00901e04101e110508003020038100251401803060301c02d141c503010402c48054400c0340000e0419000008000c1c1c010015801c42441d601c43d070b9080b298180c84542c01d0a0000d20300044555545c07080c000708000c010300a03084040b5034000b1010050600700981c000ca1500304003d803482d20000f0b50000200308001701c05c60055004511100214105010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 871336771 1250 871335521 871335523
    0x1206030309120507030c03054804021c05091506060f160c03080a0f020d020c0907020109060603060c1e080105010c0c1e06030c03020903071503111605010b04020c 71
    0x1c0c5000303001d0081180300034001440402c00c1140d0003194031080704112103a07641886904c40c0300d00005003800c0b4000b4074409101c1041c0d0b00d995841c200e0b44100c4040d1018510342023608942441a001d90440e03000c3c001d01b07501d104940013a0400d4607100e003021403186400400302c1e06200c54440419035151040c001d01c203064030352360151a542e891504200d580c40791503802602584109400042c040c060142c00072081242290151442d0b20b841d1300c507184410b004100590700c4101c40c0c007000005900452010f035091404070480b40e0440c010303000003d8221000c1e202d450070341c0c1c6250402d82d00e803501c400c1801c54090f80b01408504040c0320381020425180030400c020000350040c07041c01c0c100035403c0c40700820301c203070307000000700505c2214400c1c2080303801014801a0003032a0311880010070326217070412682d41d01174001ca54401e80c000700900495424900c2528100000e40c451a00301075892242018a0b0044c030014a023011000c4081c010a240340d00c0c0c01d0303081d6111104102e006600511101c2c185140c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 871338021 1250 871336771 871336787
    0x5071b0f0609060e0d0201020a02070f0303020a02091005030d020a0b0708060121021204050d0f0e060a0320070c140414010605091206010f080601090606081b090a060801050112060303 80
    0xa0720440109014865040080180183d030712250385a000b0300d52032082894056005000000468090340c2d01d00f07a0f18070b01214941020301c4003038050b0300801d025000603e4809000d82c1c0c1301c49106281d0800f00c2d103690200c1d1801c4a41c50303102000d43e10004066091044201c4003981c88121031900c901d80d89003502c0020800f01d0122510441e00a0191130441800d0007a0140c82c19011003122451140c80c003401c0450b600c01070b0100752404540904002d0241900c10f41e1409060350000e0425481d124100c000cc9004021340454000208411010200030300304031402040d582d402031801c461000e0410300c6600140714480307581845145403613030743c0c40d4803000e4411050444505007041901e0314521008220285000d100910340f501904001080044a02d1062810307900d20000301c6510703030b8a40020340c003152198002c4901040481c4005007031301900f50b9070b400030890440c5440781819010300128003208596008000880c0c9100d0062155582c41441885081190101800f000c1c0c42c6450181ca444 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 871339271 1250 871338021 871338023
    0x80105090a021e03030307031b030b2b02030706050a1805030d2708010501060f11030301030209060111060411041802130b04061a040303080c180d150f05071b0f 70
    0x11901c3d8000082c040211220f0f1400c0d6005000e41e51b5a00e00150700078010824501c1c20502ca4122680400040b8860b214400b220300000e030440c094600307106848a02c203c1d00f40d050341c502940118031900141c030280185402400c007520340c03030b44803008500042d10b200300e41032448a80b8014581e0400c2180e9001401c012232080b54204410341040c05007140603060101c0d20b04034580912034000264408055002074102e4105664201c0d0740d06050304100c4071480c03405180c040c07950040c00148050b2800190090300000141402c60160b401d40001504007007041f03500f6102c4624a0110f0b0b81a4100782c01410b80ca2a07c12020302c0c2c0c8a42e403070340000d5030ba14031001e03031400965075020100d5590700c40d03502100242601002001c8c50401c0e88003962010b6106000071000154010301099402409000799070f62110760f019400c0d141d44010051104640050348265040b81c2058002e2024941522440d040c01c144014041510b2400c400050058095036403100c400f0510794580c040441c0302c966090303403d2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 871340521 1250 871339271 871339279
    0x190c050d0807030b10120c0203070f1506120b0417070201080a151d0a06050f0a0b0711120a050c1e04181b060e19030f051608030c0106080105090a02 65
    0x354803001411402021000c0d000b03170b0495044079164a10030303000074000030048100d1000348800c0c2c031100000ca0722400f032440000c0c2081901074401002900038601900418042d51000881a503950014064140002420344101c49800c0501050009040f1840d9001e65080c0c0034515007900d40d0f0008041781c40040c01c40c040542d84943d070f101b42400c03c0c101d240c01810244402c100c050641080082d520310141c500c1c0c0c0055140480006150500f40b03811844540e0083c01e50603c1c500d8442da52100360b0045004640154080c40d55a0302503031102200080f2450600082010801c50b15200d803400042e01405481030100401e445c803074a8140d41038071461841640c4c082003c00481c901c148030050311071030043c421460b8190b40307028440c502c14100c040b5242e680d1070351000b00c5c440050218501c0546201c40c4840e40401c01417003ca80039012000d0480e105004403071510500100032802081141c2115403950000556500c0d4400309015030009001200c00820903410401e44042e51030802810007401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 871341771 1250 871340521 871340537
    0xe1e04060e0c03031308010b03010504022b15020a11010e190317010605031b0c070306110904050702010b10110d0e0102161215050907180b030102040b190c050d 70
    0x301d20418018025240c001504407074540c000342c030401008440c24000d0070440d41c40e29804845502d4140031312401160040c00760401c21071807418210121440c418811080084c0c0003207840040d0700c02c002d009c074083d03a940005807a00c141d801c0041606118141c54140742c0c2c141001c007006008041843e0700c1c3d0002030929a811000d82d441d080e14480d113545034401d920024100001a059000300055200740340455810041800f078804407801d03802801c101040680c00108144006280ca03403000000100050b100c505084105001070155407088400b0401030751102c07070b8600c0d581440c04800c030b4800444e00b005030002414803080b039a2400150912000c0005216052840703900074003555079200741030010400c41a4603906041e80540050f803080399002c0c69140203014107000da10a03580991170f0b45d4003401e0f0b1589800c410b20001c9a501c0a508400d0360341e40f00c000c5455030240300500c001c01c000720000d038441c8506844100aa044140f940080c04200c5a6840000d0350102c2c0501c085142401c1c1805 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 871343021 1250 871341771 871341791
    0xc0501030c0806012a020414040303060506030405030304031206051003090521030610051308070e010605040e070e15130f05030a030203030f31021216171204030c0e1e0406 75
    0x1751904811030080d40107854200d140704e100110f0308443d0700c04c5011f910144000c56071041400b4a611081307c3c003074100e80003407000c41e001a106200074110ba004224010a0703041d101e0002441d5561001143e1000c43d07600c158a404025040c007441280b2411008205800a840c041a10342484028505881217000c1850900c800d13003d6001c0d0381002400f42002c0e01c0312900c81004550740d050b180074032541d000041e000025060f12603000c0381c0c2590704d6002c00a695441d4804142c03103440310249078a0348600076201204400300410040c00801c1c082180c641c0c08949031840d0f080e0b2895490700228080c4c0c12042d51074000c41e03000004c40b0742012180e224401d041e13649904c0300601c100340c825464019441075001c1c07000714000c0805480594000c48810b0a0320080c014007540d03586c0c1c82c581c0300c5946400c014003084852100260304000c52545010f0320801e0032405c15242d015400341d08100da03203414840d81440314405040c80d856000d9004010040d007000b05103100786560a00800040c51103031654400700f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 871344271 1250 871343021 871343087
    0x10030b0405030f0c0f0c09070e0108091515120d0e060318030a0c0b10031707020402070615031403070b0c0d0209031e2a0d0503160c0501030c080601 65
    0x801a01c60740f00b0140e150008a8086521407610010498031803207103441c107944a1410f80305040c0101c5e610780f00c1144000e072041c019204020020900805801418400d56076910300d60b890b40d2180194040000480c480441040303881860018401425880740d103401340c0c07450b04140c000001940c00c5940a443e5039a0510980c01c86284e03004045103400007045905840e9008212101c0840c49846040703140c1c0d4400c8180b08106c00f15200180c0840c9096204039403c0820b0f40050485600103040527162465946801d425110940c01505400c81006410805d00500c4051452001608000785141140c01e4940d0549180007030002e4024200c0040c040110740403e604440c050792014043e9aa460a0480108542a2401e8164a80e40120212000c0e50701500055030f6845494210121400210780144043e91030310140c06c1700c0d180f0040040380143c2400c40400b07406540b2401108800741c3c1040001400e40c0c0501d841c410038003021100340700c8181e03044100400c0c10074010f0200c2c1c04664901c5152 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 871345521 1250 871344271 871344277
    0xf030316080916090204051518061e12010e061914010908010c020604060e01060e0411010507140d021011310b070209010b04081002090a0e0106031a040510030b040503 73
    0x20f8034848520714000540000c4a402410131118211000040c4449000c00341003584910380d010512039244c0900d00d00685480809000e806400040e0031b48008511400603440d9848007681c0010070f0344402c01041111440c0b80495441141590110404980080703444e17031350354090248400c49503a158103482c1036440b8241001c010580eaa0080c8201e0000b200007035105c0e801602d003980c8440c10240b0b1420580320502030002110982c0d070345800d080d521038a480c0502d003401d006640c1005410442c10001ca0b0300d090340f860941c03e455010b0101d603210401d000c0d140c690580c00d01180d4908103032040d810401030030f050707032132184055214a070303500202044105032900800340401e9030710382440c010034000070100c054000a48290341551803641c0f1490b01240380d004a204050099016503c100008105600500787c080e001400c200010f6855041c1a00030743c50980008000903914441c16110b000d05c11681a8030450039034042003503041c800c0c20004940701c3d5010103040016003501080070080f0400c12 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 871346771 1250 871345521 871345543
    0xf07200a150807030e070501142206030c0e0901031e0512070215130b1c09150c09150309080f070c0312020102160f020301090204050a0c020f0303160809 67
    0x2218625101c81c80742040c18040030121001a1920000a83c440e000e40b0910400750748050050010034074001c011116040700c1401c541403e0010f000400c05a9210341483e00154102850b9540081c18040010b0131140381000640400a8072420400552a07041c0003605494215a80c0b05002590307013604042c1c0c2a0252000300309105c0e400da10103000c040000a010024800c0b5102c101d101d200407840a064055104071500800354408200213441c4e81100130038040c2c0c1c410101002c2079440c01001000c0ba2000c80c0c06407a600c030344004011640d00705100300d404040c03880c14000100d6081a00b8400401d048491510030716039104401c1040c40014400e40320740c8030f01251a0341c2e0b140940d103070426111001d840211049a04d94614501d2180103000b61040c50301003c0c100c000218440d15280e0020007ca0b0060ba010b543e0345126401507203c0340507152180904080114409060007c0240b80c0302141da03011045810a20900a841090014280100c2414540280340352281c0c0405810409a01c40c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 871348021 1250 871346771 871346779
    0x6040b06070b01420305040312090804030b06100801031b030c1503110a05160f080d05090d0e0f210a150b0111102f030103060f020f0720 60
    0xe8104680301c0d8515113104102d1805182c010340060038840c44092080d0050381240e84024030b005600c80d078021070b403085c003926101c903284400705809411210b0440050742c3c0c4240001d4148203100044c0030094000005030755420b03103282059802012400103000c02410059144140c81b8485407802e05540610703080f07090301c0c180b1646c0c0c200c20b442c5c085080e100b40c4046401c2c852a600b00041000c25200c2440146e120750f4541690009040e2400b00103541c02c8900303481c00800c0c0341c003249500000e407140007140b80d0b000600d4100442c001d480d20641d508080204424241b4540780c584840e43c44002a0000791462415583c0ca4200c4d40200c041001400c0359506c1fa1004490500040102c8800602e24241040210700c0120004541081c401e490801c5185d000309101d1920304602d03880803040840301b81200102c800380f00c1143d4032032a03044201c1c56030030b4408001401070002e0303072141c80365032200320000f18502a801d50a80c07119006404015102c0450008020455226145c4480400d84010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 871349271 1250 871348021 871348043
    0x506010e01240f05131d0a23070207230f0906180405121c05010503060f06060a020f0d0509130515220c0809011b120f0207060603080c060c07020906040b0607 69
    0x4000302083c00c405082c0c08543c00da06e00c021a603421450304c01c11702d00b504000711204103c0e100b4400c03041003001c00f601d200d00310702c1500c0000810b51041001c2c00b5403080007980c1f0f440c001919408020044507030500743d521a002c164280030031a42c0e032649041a000601540129560703c07403c1075030400708542c4030340482c1c0300d002520303031182d5103801000b0854804500080103566255020705035610b5044480b042d070001c0d180003003409442c082d0040c022002c064411035889845054030103080c0340c0700d000b14501288000c02c0d032012a10b400710800100070307014801044070303252803c0b01801c0340c2e940f139000b00e0285500c0300c84c141c0100108100f0a03400520040140110350758004001d0030720744c08a1b40c9080b154a00b030a4019890314840880503040c0c1107a076010300c1d420007a021796000705114030660090a500300414400200700703014640046001e4000355407a400f401100b142055001031410120f200d0401c0140c00603a240c0c25040e0f0482c109480020740a00d50401042d00751080002c0606986103030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 871350521 1250 871349271 871349279
    0xc0e0d0305070c0f0612051b0705030721030c050f0a051b011404060e011404060506040b0325080a080a080c0f1602010311090a17030909040506010e01240f0513 70
    0x10f020b0504407445e55441c5900320165145090490f10141c965074224660103101d928100c1200d00501380444c052010307240780200b20381c0c9004203500e180c9824007400000414811885406124600e020b4801741442458400c070a00042070520810804005100002c81d10f403140c0504c80642400c0400300030000c120f528241a440c0048403011074086590718240b41400d0020207042c003840a030501e010400b504662a184e4688018100c000d03d103d81042c1e9486107040f541d0350400c4141801070200800c03143c02802036415600c00071325034001c00010b030710001c84000090945812184001d5951820f40401d803200009652144242410075100c00b00200d4003511504924981d11610761007600c04100d002c509011084103805880106640b1141c1c44904119400b400104410300581d22415a85885403102c00252580c2c0705403000e80e102da208100501601e090100c0c1140505401c1090003100409002c011800c24604401d6004012184c0041c105d214011810b694130f804020321070b2620507850b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 871351771 1250 871350521 871350539
    0x13030816110604030503030403081b0703181a0d0e0309060a02010b040f0b0d0605100b03041211070e010303180801020a020a0302010b0d0206030c0f0f04270c0e0d0305070c 75
    0x40c00259481c00c4485807101d8245448003c490859900030701641c190380e00c2d914190760412005001c0500d400900d4800061000c8400c014080e035442034646901c48103840d0001411012550042042d10840b18101903132069240b055076070841074400082075441e96000902e0850041a00b503035004403001c036448a0181d010b411800c044002036808125011011030320300c0c02e680d00720b50680e070460f01c1310601c1c02c027003801e43d0030203548000ba002140c01450b1750349004d0040ca0b4800c40b01541c0803002500d610301080e42c40b2140c1c00c10700200000421800381010407540c140710062000400b48020718646003409040d5a411000800905000319220500c0e040041d444440c0c4920480040d440e0079244001458281222240190083c0c003203800e40c2d440c49610f440a922803014286c3c0c0000030300002000f90300d114014006880d1980304d2440312601c01072040250002c0d191481c404908100ba402c81c1c05a00003001c0001c0c14045803480890030302d0b81000d8039288640c0202405030210f1000101340707404 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 871353021 1250 871351771 871351807
    0xf06080109050a110319090b180601080318010509011b1b060813060c120207050c040b0d02092a0c0105090f030a050306040218030a0c080c03010e06040206130308 71
    0x10610001e01065075810f0040080301d11384000c0c00d4a0200c10300204040c01142d04030705485c1c0201d04000601c192441d00d6401c1c40410031500f540d02002074046070340d81c030b038014800c050040030080019410020b940302d0302c4032082c400050f880d0410402041915042e0b101d101e50941385151030521a980b0202400c00090103100c051420034906001d00d000280d0340d03c0f82d40074512602c00500c0551542c0c1d141c0d034421014003a581ca442c0c00b0805111004e040c1c41c840c910042039018445d000405c6128030340700c140000d46064006041c8100c0c400000b420158070b40001082c0e002c0c01d500d00207030b4000d0308030b00b07075100e401d08540c0d61028164000c603161848a00c154810b50080c1d414000b00c2e400491580c0300340e43d4034810121510002203081c4080b4000307007003e40103070035450008080c541d140b55103880440c1c90481688810b69108907182410416a0700600c110f00e44448213600074010066020b0b03600341c0d50075018000034020000042c0c43e030020f6034000000c80103180c2c40a902e030360740d07150008000d055107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 871354271 1250 871353021 871353029
    0x40606050402030a0e190c0509040303060806090c09070309082d0d05040b181e1002161a010b040620010c0801060806060315130b09130606050303120f0403090f060801 73
    0x112800085080191981c006c0d040100d0788117415409240c104028040d41c45000341c012001c0c15214400030500000c00e02c5010f205844420081040f090342004110440c00060070507010b2526005190000c148848201c0740c41041c00e00400b03480c2d90801d14404410390f070f0120780c00d03549480030482ea942c02d0082d4000d079015034010441030340181c41c1d1424400c19611400800d015642c4041203005111a101080350101880d03842990b20320701c1c00c0082001130340e01010040c0f03d426594401141080051001c50084100e4a80360280941c1001c01400c1c0c02c1c0701e540100310074028140030b035107080801d500213543c44c500c13400002e00c00ba1201d4180039050100a0184c0302c0403500b00e030001586401d1403020769108095016584030340a5500c0c003880b095044c0b05481c43c0c2c04984030741a055064a0b801c060718040c000031303443e10442c0400c43c100031084901c00e4000500caa0801c0143c070f01c15080490219400884541c6e4400d079940311031605071040121540401c10503071480f00001036860b002070009040b1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 871355521 1250 871354271 871354273
    0xc07050a0b07121d03030402120a020604030b0702011503030f110118110306130b1311041d070f030210050a170130170a1715041d0c09040606050402030a0e 68
    0x80303019a40e00c124110003201341c480469100b400090b015203042e41d8204030b02d83c945003c1d121041420b80114000764810b40094a011001509002041d9824400c100000c40e9501048000b241159801032800304582c403100308200300c003061980d8a0800b9800310f13541007607288001c101560140780054400c50039000c0c86101740181d900060707d601804070007010140c0d104d0180200380d43c0d9640c411020314211002914030300668030030326141e40c4440c070410303458845210038804146040c60f500d83c580055504030b04035035901d204007003005803609201101900c1d0305040041d2908012482140e203100c218100541042d05d0000010305401307407a51b920b2407641c1001045001c2d1003480e102400d50001800014200311070524500c03066480600903041c00451890044403054184ca01d0302c040c0c041c143c03598202c4118001c075a450902c0c6c00e100300510303d490344200d020174482529401d600c1d8203914034034a025046480000302048815032254000c0c0c40c0003802191a07090180f9014010009803402c2c1000d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 871356771 1250 871355521 871355531
    0x3060902030c01090f030f03140a0306050a3f050715030c030204181a0303070b0915012301020111072402090d06020904060812121e0c07050a0b0712 65
    0x241d51080381404c040e00c049000000070340b4030f991345070094100c007648107074100071191409030114a010300051008251680d000b1135080d041004110002c10b02d079004821b4400301c60b01065280407100d87c803c200350041c6043c2ca800620307920318007000a83c8180014018003d6500124000b00041241e008da04050741c2c0800c9030682030401501207119600034140595045010700c0034030790301034102e0002c12400c15820f00c400c00445001c00c0c034603004103504075480b1750810104501c0220411100c202d0166000191050303502d07041c1170309a8130b4078100c0e040a0090090800c100300764000d400900840c66010110ba5442c00b0790b0501c0085003166510081000049000c0b01001c0c090500a590389200002c040007900105a691440290707c110f071240d41050301c4020020f40c0c0e48091000070650481e918049580b044803582c840903504008101104c088c010316100c0c58069640c04080343d02014400c2003035519109400c201d03103030600c501e40007810110349108100d42c00e0340c0302c0300c61600240100c1e02030203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 871358021 1250 871356771 871356793
    0xc090a0e0f031b03030105010c020f0f121b150901140910050901031d191401020409020a0f05031b0c1c11010b01020a110d0c030611192f12040306090203 67
    0x9105e200c02c0c403d03c0c0c005000d180c0c420000d4504001042440c42d80202200c005c14a047c01085641800c0c01d2810f00765085800540507004038100308110740c4604031250003141e03006c0401700c0c3c4a13020f03989000b8100310484000a4280804c0c20896081c1d4500900f02e01c0c4002e07040900400c940e00c41040342d80040d0400b44030030300c800200151700c00c100303c0703000140400300c0e540c61480c00014075607070054500603120610b00c0000d680071720041c0301503c0c21100160f5241002d5a0280a0310481003500c03003008410010400100c0c2c3e440042c0300341c100c410410a6440d0750805c8900d260140f8050f00c07101044540c1d40d4864255089403005e82c4054501c0000c2c004a500c40d001a602d6450308a000f4002003450300300d00c08585400003c0200b00e81c400c6a12598454480e1038a104554080b9200e00690400248800300120341c503480c0811046280341c14058000c4440b0f4003600200122145603035000315040303440d03100000f8450b40c000d401c464421070303403941d50302e0811034051b113002d25040e406030154062000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 871359271 1250 871358021 871358023
    0xa0b060717030109061512051306110703180e0f251d0312031b12040c06080f130201080601030b030a05060402090c04060c08090f09010b0c100204080c090a0e0f031b 72
    0x802501d0306d03a00c5042248804082032400351000510301c0c4681c50240751410000350080c4650580d40b045100d80fa52070348200d00d0090020701c0b0035120b404030004134a404000d01b0002e80606648000000090403041e1034026400c0b030000890088030260b00e40700c01264102e6a40901211000c140c001c018411126048040c1503c03594a00140301c52034108000045454020b00c40c07102406100c80300740d44c03404455012820801c0020364044803080c10903c410410164085140da82254008030040c155080c120b5004020002c444402418403803800f0014407242e01990000c131a0340c9000d4256880302401d4034003e6203c00c1c00b120202c1c41030a03e40e02045101d0b90b45c00948080c0c88054881c008641d01c1a19911001e03001161403130340c80105114008080d46400d10818004e010a82600b601c4d840c4820780c440c241107105040d001d0a40c8180010080c0c4180011400000c00050307030100190744900e9804006003003500d250751030900ca40c00300200d8071800000180b030250900b6100300c2c5900381510700f00d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 871360521 1250 871359271 871359299
    0x30203090304051e03010504210905100305070c0213091e020f130615030509010b040c0e040902040b041d061e0f1f06020d14040b030a0b06071703010906 67
    0xd00000c1d44107110920072410305468400500308030000b8a0500105400040d00790344080b0707011502d0725010950380110400e22203030701000c0052030400c00c00281c10074000c1841c03800000c08080825485001103410a13000b0b0b40100b004076000342c20f050307021001003104c034007a04807402c01b1a00000c0d00710f4040000900914200d01c030700d600508401039040094108240300784041c2110b41001d6440d40c000441941e50071a210042c002602d000c5244e10300513403210700312007206000304d00450030107101100303450348040090003c440442d0300051550721400030400074529803081e5500580307000e111000400401106003240314015085599940d50b000b0741e040c0600790100001007800300c001c04030720003d854208140d44079009000300111940c0c1c03170341000e10444e1180e000d40003503004510071101c00f560280300a40c94808401c022440c185c94000d669400744001071408041c10740c1c0705151400d5998280803643c41640001c2c0300d401c4a041055071100c250b00a00c00c18031b10a141c01c4000861010352180 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 871361771 1250 871360521 871360531
    0x6030b0106200c121216030f020d0e1c08040308040f0b070c210b191d06040609031809050123010804110102070522050105032b1704060e060601030203 66
    0x90510344121100780541100032072240070300b900031110440000c0c1850000f07401c1e4100340e070f000701b81c0055140c10050420054502480b085400ca0b5904030041604030780c905101e0201a1000d0010100c0e034512101c40b5480500001d0440c0030024000041c000400003030700561301c2c0d4094541610b56514481e646a204820004151950000d01004818440c190107030b41654100c03422182810b050742c403043c50300000c0b1141c4c8414a0549445a0060800e20540d0500c540c0080d8a96401005c20185640c0d550b0050008014035102c070990070030548504d860512810a84190805039511146c014002e000240111650054058003002c1840c60b01124045030314010303140c401c1d090710b494481c212002404000e090561146030400611a2504041c02102a1100c3d04018070802c00341c441105a410680c0541c7c4646d0004c003900c0415070001e24000ca07501d034014000300d1081003200b020350f91025090742c0416140120700400040c401c0c01e811202c6c1d90f03006001a035045954020041d0101d002c2511 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 871363021 1250 871361771 871361773
    0xb010303050307090f030b1503010203070c1712010b07110f10030f0908040b0714010c090e0901060b03040f03020f0a111203090d03021513022407050106030b010620 72
    0x400219005100a6400050514003090000d0b1039000311118040507900032200780d0804010001001403038052401d01c00c104400a51840c20b00030710060a84445c520007a004e6001d0004005400032044201c801400030500010f61a680d22800303a60b154010910a681d00081c01a00d00240c0c80c0c00b5284c0410404000c00c00880c0414141049000b8400b03008403091082e640d0b000c440100b04001c001d40010900d5809081e038601c02450b0100031803c1045412103036030b047c0204603454541101964080e103d4041e001c034280c0e40c0740d034001c502610b225402135482e400004180814009203501120b6914045d408032850b508000032201e985501c880030250143e0301200d20b541040c42c0c080410300c00a9003400480b420035007030800184075022215000c0700940c4c03090007000700501c0105621980b003919900c07803045d440015000f10f41c1065050714440c8200c2c072101c41441b250030b00c24080c1c85410342c0107002008943d4880c1303000c040c58003080c004d020100c3d0040c800504142808542e00b950030705008 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 871364271 1250 871363021 871363043
    0x8120406120f0b09040c060e0306040b060603040206070b070c06060611120c0106031e020406050d080313140a03120e0a0c0306090302031608030f13030206070f18090605030712 77
    0x180400042c00c00c1c4180502442e202d0b403100c01c1c603503541040313540164040d00b0700014540c5040c6010f0480304e80702c2c5005010350007080c100004150035954243e4041c005403a41940c079035031440060024400c0708001001d0010001c1406a4103034001c01c881c8030988a113004105140e10707200107989280d0003660000d1164042c6107044d40b0a8103a001030800c400140002003442d68a0385d907240504404200c07007030380750342060203500194502401504001c0100b43e400c210003031001d454500c420f20001306400d00403440610581d08012960b4894212141d103101526945080c44c5001400020450321401426040c9180c420341c0e4007010900150781075000c4020f100b40d07891956004040c101d40c1a055082d40014007003071021600c0401d81c607603010301c2000d00603580c0c5882d0642c4c4da0b284901130180140950000805000030307400199058111481d405c00480740f00300c065007214200a01000c0807402d4680c03100000e40840e05e07401400607200c04605031440240c0380c1070354010001c46901c019243da9200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 871365521 1250 871364271 871364297
    0x905060a14220e0c1305040b040b090a0c090504120e0604260f0a0c080601050f0904051e0a03020f2b0e040230062b020909010608120406 60
    0x100c10040c0d0361603082c0360081c2000c0d00303210b08110780d02c03500c0c203282c2900300715401c001d0703031501582d002c40310502010200242c0c01d2944030002c040b00010b00003041210020003150a1980c104411507a00c0d5108200320000c946617500c1a003c2c1030142c2e421100b445440003240c81c80c500591801d48140c0c405042c1e142098034150b0702d44440b58440030b207055803410860080c1c900103024407100424402210080c03200744060300d0701565040080c1d2003543c5176001840140402c1d40c842910f20302e07188046a0307a0f03e194469040150074002d684840700440413039207120550001d80460b0744841c150080d0252424644484003450f00d401500801014540f611668448480c2c0796440c07081408100c1e01c1c205c0002041c103000310302264802c14400282806203107014142c2030f07040301d40714000c101c203010101c2241411400b02e03080c200305402c0d0540343c0303881246001203010700d842c9003100d05400138210011406d0012545000341001d000d111168080c54051014014101c0110380440c0e4003a41c401d2079000362 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 871366771 1250 871365521 871365529
    0x8060a03050607030b01110604031701140607060b011b1b0e0408070204020304050a17070b070203070210080c0d0612020f06070818010c150e0609010618200f040905060a14 75
    0x5c03000140d042c0303c00c20003074800419040044a110340d01c20340702e0b200070040ca4400340400d504144e0042e05804000c4a0345407143e15101d05907080154000004252840382c180141c40b16800c00d40c1442031540300300340801c1071044942d08104520b402e03869050441c0d444505a903010342040b20060441e0108012010042c141940110750003800f50007512020340e40c0383e4481c407031000e40e55070344841c4810106034107044c0400b48904e26000444c0703000a5103008515030205004250864400e418404038000043c00100c41008641856012010401c046a1503003440394046100c1c1d5000d80c014881302d00c0080886c1492800c42d803503203801654003800d1095250203d200c040385110349078104500c1d0a11600050f12180200b0722240840101141030740850801c0351400340d008000a42503810f102040080e0f0041544c9490700342c4140d00089215290340c90a103c10041d00d96610940040c0010741010980861000d0300582c0c8410f41c09200e01e0300c922040019620403405a1030310514801c3d88a402c03490 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 871368021 1250 871366771 871366781
    0x7031a0d1e080301091e050105090f07020c0613080705040b09040f020d0f05030c0c01093c060f030b04020702100804050a051c0e0312041a0d0c0f08060a0305060703 72
    0x4120807440010044580e00c21005400a900210b4a5616580c0f945403600c20300356151442015440208a03541c94480000c110100c00743c4403014002c04800480c450724800d0102c1121b12a0141070709680d10822844200300e10014891206680948103012030f4038500350041c440700004c0107040c440c1645441d11005000c00150204980c0f0080014080001481e00c0000e8110240104091500e400390300544074145001007514a04000f076031b01040c4005c071803000c61407840c0341c6000440d62401c1c40380440e40710812504140401e00380c014900008003e03601910044420100d81d800340052807418003440282d00410360000d42c00a0241c1c0030301d441030710600c4e03165071190180048170300144040c0c0ba00d0b030400b081000c1c0d21035600c280b41c07800003030941c0048007a403a1001c190010152000700721036041040c00303140615201c065100000058185011054642c4480c80b40780170408007004000280040358200c000c0700215000c803000608618154004504894008000e400c2035a00c806c0102c004107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 871369271 1250 871368021 871368053
    0x80711010204030f060902041409120901020a0507090c090f03050c10120504060e0d0215061504031b15110709051003080c070e091b01231207031a0d 65
    0x590700740701c0000410000c8184c200518003034600021503140c05e0040c84192004411007941c5406841c041c08041e04c4000384812100044d07c2601c1d443d0803500c00101e0600f501c6410140c4544650840030502603c99407184003091010785904e81401d0b66280d1454000b2078520000e8840c0d0000355490b007060a00188100c015000e5280c02518441429006001c60710261400d91342c032a83c481c049003c80c07600300204d800300c922500041c0000c0c12424400700b24035400510b485c0c0a00c038960711255a00040405a074051548000f900480d1486043d201c05070f8403140c8102c074000c4c100300c068868a00d0090760b850070f07181c410201a10500d410000d0f0100900005040200c00304011070000003c1a2710380007414803a0300c55000340001c10b14108040b1840c0707601400c04010383d0884100d0025400d0144420440000203003041403072003120700d51003070364400d406121110500001404000450080c141c0318800c0d0b90f1074504105015416507628109444c0b0303004c0c160401e940041e1400490382128a1035010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 871370521 1250 871369271 871369273
    0x919111204060f15030c0302060c01180605150607150c090f06030e21160f0f030c021008011401081f0f0e15100e0d1403090a0f06080711 60
    0x1003400314035011034410031901599042c0c0e80c0c80c1c0300c000f42100c50045a50385004022080c0b810b90543e151600d2101c031a10000340318040c0090100c95400013904008210152000804180f80c00d90070410003510040f00c03800c1039418810030000407854050f0982d10025007243c58a4030790911092200c00420001000e8010304c00381e500300081074207100311040b002c1c141d656004117507103031140c0345141f03000352013040b145d05405001035440304400310009072120040342c42d2001600c1481824030040c4e4660b0300c2d5025001480f65001201855001380c0c0c8a02c00303d2003501c140d0710150380c200303085a5865080c042c0c80200c0c0042d4a05010540c49000f980750032400c40201c40b43c80306082c0d465481004040d50003e41c44006a034010005403444141140e40200140021100c004400c00050352203030b070b000390010503c8184040031440791900442459119408540408007200f40c0a07034640c0c17034001062030340c80b801100f032002c500d2080582504044400a4840b441c1646812009881d2007d9021110b525 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 871371771 1250 871370521 871370527
    0x703081b1c0e041e14180c151e180d0b130203030d0f0c180f0303050703031b0917010e070312021f06030c0509061003110c070308030a050105091911 65
    0x14803100c0c21084002c0c0301c2008009920303149194001d560b030200a0810303464140b10300d400b120030740c800300d50921048412152300003503d410804070b20311030003641b035070902d405110607510800d404105c0c0103003440c030050384040c0700e01418001080b11819010a000b80403402000200e11210003114284551610080035203050905102d2520202c458a0b41e035400c0d0b554840c0c1120443d03e4010f00100d40400359588080d286c00d04210990008090a110003401c100307000038102c0c14980f0030b92102441008420088914044000f0018403016250240002d0041c0304241c5500c114014482c162035940c281029140c44d501e03507240c0041617103209041c441507005044682d100d19040b03c1c82140201c001c904001100c0303007542461904040d0030b80205020328410340600140d5902e0710311000841d0403e103030200e0311021007503071a0310311300039009107103254460300c00d0110820014202a40c400c8840071800c00c4a070781da6004205510364250741c0c2e40c0c0c1d201071140b00049070f0640d82d0401c0c4a442d440d00c0019107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 871373021 1250 871371771 871371791
    0x151d0f1903140102030402090106021504242313050a0209060d02090703050108060709261608060f0c071e020105040e010e1f080c1306080703081b1c0e04 67
    0x4044090b295010016941c004100001c5143c0700a201e8091b061910040190b4201c0703040601424202a0014051075490f40c0d1034046040c1d07190084002c1a03104d81c050245080c010003450280b506540740c0f40c0300c54941d03000035a0b18803540c608a10f9050b005801044003a003160280b00c03030803c0142013540c000301d0041c030306000360701c980201c64014141990300041943c90301c0b94003800e008000d001d0b00104500d004080280260740e4200f20b00d100003812040c105666850000392402050105160f600c49000400003022900402d0341841501100007041d0f859a80420803c00ca10405000810548407880c4036441080a01100c4c440300348181843c070316094460010500c4401c0990100e00500310020400180c1c2855143d403045030316000f020588034078184900c2580354421805218001e04074003c00203c02c400d20b0304135200400311a0240c0c2c45407038580c01c0030b031042d0384480840200c2154410004452850000b1140988103003030f0828050400c84e41821211a208000a181c0c0503448181a00d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 871374271 1250 871373021 871373033
    0x220902061c050601140406031a031002090a0b0a082a0d05071b0c1a0d0c0306031406010f050108090a240f050c1b070e01151d0f1903 58
    0x44140d5401d02600c6030440064070940007a10350090006040200684a4601000e011800d035810b9503803034100401c5030101000b84009140c00300701c40550603c54002044101c18880c4e0081100420507903c1404144d200d4101c0c03041c612030410350000140145002a004901998103181121900080c0d2444000300c204440314075001014080d0546075504248500a90801890500004c03440d103102842000340d22139040200203485003100800c10a4800c0080032038000131120f010a503c41c0402013001c01e6800100200130340c1c082100ca4652120030500d0140000602c54100ca04d0700d103209030840d0401c40115690701c0c000d00402c005105590001001170280d032061480c00c0840c110000d902401e5620b40c4041d580b100d841d1a40f07561a0405011250780d12400320f5070308803024640c0d607050041094440f8a002250b41c001180300500000110302091040500b506110241c0d45088514803c0708800500c1d45810000c283d01502c00510002c103411b0910010105c01030241c3e407a0b80456981c0c40d14 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 871375521 1250 871374271 871374277
    0x30304151e0e010305131703070201020c3c060112030509090f0a111612020a050a030807080109050f06040902060409020706091202120703050702190e1009050622090206 74
    0xc200420510100b036001d81d6418414035901c20514003081c0c07605505500e030f1091440080c000498418030000010b00064002d404036950760300c40000f2038816100216019041d20091002c03a5400c03d004100480c0d035042c80300c0901c0c180701c026005400240d107060000903454138440030803010701205004040040d503c1c21403080c8140010301165203185000761441044a4104d00c7c550740485040c01700c10100d10300122840400c5a1000440f0404205002d00703925101841d04000c225102d009020302c1095031105185000e136816480315145641c031071010000b80d07441180e1402e550880100010928a01500f2941c4050300280150349460303142c850400590780194400c5c1c4242d6107c400b82410008802144d066110841c4040d01642405980c100e200e0321850f00b000d410054007140080079075a5241301440044503a4181c2021503940e04c000c0c404040d03046840914411441d000007816801d0380c06400d104c0d203002440c2035215200d040a4001c02c04441002c4400c0036a1071446100689400c001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 871376771 1250 871375521 871375577
    0x20304030201150b0a090e0a0e0a0c141c02010509011e0c02031b01090317121e100302010f0c0303060b160203160b09090a0905060a020405190503030415 67
    0x1198a030481c091004241210342d010920700413007000480309050713103d035450050780d2500c89101c580f5200d005c0d00c1c0025040c42ca28a0185c2e000b02040c0808200d5103802d510b0441c1e026126502c00c0b4003000c0704112111181d2460322207000e944003540d20040d80308100038440c01105040902ea034100043d00d031a01440000d0001000c10032044056040d03280400c0070340d048600c1801c0c0c100d00d01c031501c40003c0c00b07162503100040403070118200050318202550103036600d00130180c0c0361060903c0e140442800b480d0f144a020b221703188424003c600c0142601c009482525010b855200e12522545011680300192010513410160703034610201c4e8103540321008145e0700780340d4035002c80781c102240101800c1c46031450000400f0001440108820110402600d104003801ca545003040c2d0754600003072001d0900400000d00c903004103820009510344a40c00f9005a407400e48041014a560801424401540e401940d81c1035000b1300007082101d0106801514850355443c18620f0310012402504500c2403a000d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 871378021 1250 871376771 871376773
    0x31404180c03021309150b1c20030f0f0f041101110f0a0507050405011706040f2109032001121a19080c0105040308070b0408131d06040e0d0c150203040302 68
    0x340c0010500510f800305805020084076551030043d242d0003100040d480c114420102c2398451a058140142c0100e0b00c141d41010303a0322050340ea14001c90300c520443d00c11509250007100f90004503010030744079510140304945c018003114110a9140040d9070034006100122294410ba50259001210602000c84894850001042014200001c00041da10f050b08850014080d914501c452458001410358019030010031003d0039947c0f5080020401400700b0f581560700d040c1c204001d41041c1d005083c0303810cc81c05a25003d11020620742418003501d002c134581e50004018074082a0b803134800ea03001411400c81003018885102601c008201a44000344a048261624400407c4460303c28004021011024a041403401d401c558500c4a00d0107a001d01030003402ca0540010300f0403010008641141c080404003200c550f58800900e040c000c0204805a00d03200120081045800d050007001c03200c40c070b09409405107000c504811214000d855005451007a008030541070554220b20046001d180254 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 871379271 1250 871378021 871378031
    0xa0302010509010f0507090e0907031a0403030609020408122119060f060c030c050f0111180d03081918080403050d11030d0209041512031404180c03021309 68
    0x30395003a00b1103d1350480c0c0c1c01e4803030600c004c2001980d400490a01561042e12484800d80c4605000ba0300c1e0500c00d400c000e100c1d1001651f07484529031680162407140c1d100385e0701400102d4854001009901542c0720b000029404081004004620b0b10090300d003a42c5002d00d00003a40c11682c1400608000940c1c508840c03254400408550720500d01510000d02213142a6100091514400030200400c0c41001350421034040710842c1048010301c8900824248000203004414404400030030305c0d84601c01001c6042416410714055081054540e22910b405840d11403656407030b24512030880100c614180b03c95a9103039600b00c400c5480801c0c0c3d20003540074081a0b81ca13503003145400361409448401d841d0900002c6d0702d003005101000003c640a10381203c0d80582c8841d00030b00800c000d40944901100ca10718603041c0880c65101a82c10881d40d14021380e10440d103041c0f800321104040c03083c3e02424042c3e01c60096042407000450300b14018210340340c07400600d014200b059114440b88075401c00d14581d9110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 871380521 1250 871379271 871379281
    0x114090a1413050105010e0f0f120d030e0c0306011403150a06330e03070302090c0d060605030907030602070c05181014030712020d05150604060f0b120a020c0a03020105 74
    0x8098554101100342c4040000307504001c0003034600004000720912910342c030001d11140342c84030024140c20905c080e0050404410084155071140c3c2c15901490009140100c4400307003810005200c0418132028003e44901d90800d0500000081c080380a25010b01c211150802c0800085421070300c200d40e1000c0010b001414201d00030b000ca032a0030022084650035240b000d101070b0f40c100d50602c084902d030a150310103500000201e401c2c41103036400a5841600c03a000c000480603c44010510030316880b808020031a11090241e0301c0e40000d4800301c1560b40010014800520301d1b60081c5850360166100482c000c2c0e494000505505c0d03101c0e41413000301760715001e004031258001c4844016100c50400e041560000201280d030360000d902c078100d40e05403150800e2080d51a0008040941500701007581c2000c212400e01c000f21100070742d0218060361070000002464070080d80006d040c5c5d100076028510b00205002603080c440809003118403a5a402c0005200d080b0b0f0800034a00d1062103600041800e00d00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 871381771 1250 871380521 871380529
    0xb0904120512010b090a0b030903031906330212030f0408190314010b040513021b1e0607020c150309121b160b071e081810030c09050114090a14 63
    0x6d02e611045107042c080c41408a07910010080e00c0d1320144502d03030342d105080181081406000c590f48240301211908403492501c100130000c0c8050b0104140041c100071604030f0341240e4844a21205449404051012560310b18050300e090350058010b40403607043c0f15070750f0340c840000aa18401d5001180e80c4000300d0b0308888081c0e8116005040c2042501d00b81440c202c082250000d110591009141d40080e00b018041000362046910f01807440031610015886040c0c418003030940c41d0792908503c03035540003c640c1d070300c0080c80c1c030a8600007502c03400e02d0714014034030010309800c003a0214525000e482c8568a00360305290207010143c00c020410840c0000049019060180320b0702c80400501c00c6080512820326194101c4455503840b2080d54081550342807203820080d011400240034400018174007a00200c44100204a86812511941c0a6102c03002c15022039407070b251110086010201c0400556000303000200a24030010b030f081e0f180c501d444000880003021780d00140f42c3d11a01c0c00e001882414 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 871383021 1250 871381771 871381789
    0x1c050a05060c2109190f150b1201060510050d20180603060d030c02010c0b090a1a040b01140d080301090c030c0f210b040c0c05010506040b0904120512010b09 69
    0x1c0d800e0400c1c002410700e546910380f5040b4542c240ca8000117440b002c07030104444890302c0000315420650000031000d1120000703004d040780c2c469180c403524280c2d9880e030141c40180300d0141100c0d0024007190780582044825142608403018107803540f59144441c40385014595010003444541c00c520342c1e61000b6640600064081c0c0d80ca10074040c0005008010301510b4581210005503011b0506014074041c600c0100c4082c00c1d032030401419015603c3c2400708010000625a5000340308071007a4000004010301d0300540e100458001d4002e462a40041280301c1c1d000b040e0b07410b040e0014000040000c01922041c6a5500aa00456160f40d45d288100649a418460501d0015807454030441d441c6000c10010302c024000340494540b5540c1c500300006140711a4040950408060030078484107202c80005000ca11820754152020b50030000001e40928084c031682102104c01840104207407241d4442100f2040c0c1c0380000d00610100300003000f03400d03450300e0405000b04140802c0796524803148050040d101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 871384271 1250 871383021 871383067
    0x100302151b06042d151b08060306090f0303011e080a0c03050d0c0b0402040e120c0a020f01050f0a0e03010f18020a0e0c160f0503031008150f34030f18021c050a05060c 73
    0x24202882c1d334001c0c1c51002c0100c071704440c080d01c106043c4403502101141050340c10f5101d8402032003000000c404102c22140c0810449010b0420340e40d0124030940305456a410382e4400401010050700010018540b40d801682204d800401305c2e984c40c403007800c1c00c4c01302d540810fa4107843e55001103203c0c021850645800094102e083c40c1060403d0b6502040f01100e000c1c8001c043c2c11b004501d0300341354854800f544500c0d00100050824004400c2c058020102e1042240c000da000f00e00085000c5100c04100741c2d003500580700040d01c00e140c141100301c9801080901c2804841d00c4880350108408103804001942c01381c6604511600d00d249400c0c0b582c0d28007000081d1600d41401d224007000b19036458020101d074403154880508501890650340c11032650507035141411901003040030000c4459056100c0301140c1c002c1c078820002d05c5100f508070300710000c054000a601141c81074a42c0300c480e12160020f410702e4030a604540780b000741507030790f541484801c82e54140b00c01000300d80c01a44c580040c3e41c0140e50 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 871385521 1250 871384271 871384273
    0x181c0602210a09021008040302011404060603110f01051b12030f070f030908030f28020406020d03063c060806010e0603100302151b06042d151b0806030609 68
    0x482820340c04100e04245c150610001d00030040002010300d4001c0d08000c0c00100e001d031082c2e8852034185481402821103000a0300e405101c56414999800c121341441548001611802e090105480399102e100c1550032011041c0e00481c1d4403070f501c130010f06000e54014400c02d48848254605a58020400341d00da200c0030040600780a0198046540401101c0d000b0341c0110400034640d9503038615100606445690b0b8180c00020030419403040307001c3d07029005451180d403d40d403038070f0010102202a01c540703014100f81c00000318201c41c0c4440ca02a40f4150700d22100a50401d031510710303691118141115400040440c8950041082d80c9da0f10074000b286461044039000d00f5820711004004100c2d00d540002401540018002f40c1000c1440c0150340c02803111419a42d00c440300d000c40c0d0707600c032074040e01c00300ea041c3c094101c1c1150807054010320280c803401e00160780010003120349484480345480c0020117549680c4411000c1e00b107030780204c0701c8014400740e1201c84550912030140740c03520400030070710481 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 871386771 1250 871385521 871385531
    0x904051003030507110a080f060a0506010c03052a030a02011b050408060703091103160f060c050d12150306090b06042c010f050106021c0302181c0602210a 68
    0x40c3e0008140d0701383e6500401c0c0320030118418004076603004140d400c8555a48182d904200c070300072000642c3c5100700c00380c0005228544030a001580ea0020303003400100812024481b820261850500d04d03e10b850059241c2c2c2c16401100280a0450340b10780e40680060351900c3c00c6681351001e05005549541c410700c1d10501e080c3c07030024026240c0001074000c00c205501c0301c1c103500a200e42040190308800c00142071365030300e05c9200707448202000301e8443d4024224028000040d050f011301b21040d0001d030000e018080101c0e0201040302c44002d250018842e180d5950550780c401616410060060b5118080000b20b82010f81072000380150010002c6102d541003141c14034908800080d500302c0201c51802020340c0c0f64100342258050504c094503500b20070301e00302c00000d41c07035130002d4040c0b0000c10b084010b2041a840d442c0c1107060380b14200310045012100c522401e043c0c10048610f4ad103032060b400400d602000309a4600c010b0fa4401500c22090100c0243c010300fa08101c0214a60441e0760380100f080303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 871388021 1250 871386771 871386773
    0x1050a0f03080304031404090e0f01050c040509092d060a111e0f07030206160c02030a0830090c030105010e220b070804060501050103050712020307020f0709020904051003 75
    0x5040036003404020682180400450105801072100100807000310006a40b51a11905200f004208082460110740708404064080d200f043c0b20b220701400d0111002803400d0308020071b00544480141901000307102e80101c101c0380c450306107460620400000c42410a00003240c60711454002d014120716112403529a000c81d10b00320140440301c442d00440040c070011900210200c21500405110071007002002848104165000c10514030801850150000c10755100400301c481c14035051001350150304c044240e0003c0b50000019100401c000080035440b045454400c0140d181c1c001c620b0400b4904100500c8075542c014030000710f286006034001c10066142030519000004050f04138000401c040b840090142050b4803054142600090805140d00b41200000e181600031502581d070b8a01d0070002042c0e541c424011980035100c0c80c2da45110000002c90400000e40c070141a840070341c850000280302d00041031102c4001002c400c00010780380d050a00c144826100000c0c81400d20500510303080c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 871389271 1250 871388021 871388039
    0x24020d1d03031003320102031e01080c011409030d0903020307052205072601050a05041a01082d040606090507120c1202030109050a0c02030306010e06032a070b01050a 73
    0xf80c1201d40061107200018021003407200712019004129029000c03000c40081082015001107000b1855881c9800c210340162100201d130440070f010300f103e42c0d0000507010a881d8450400c0c540300300c1030301c1c41061810303200900007840c008001c005200490382186080096103010f110400c0207007410340f0030000e804041d04802410000580400d600e4666070b02c00328401902c203088134410110310340203101c0b420141300a0744015001c00d00c515845000c0000c0c02043da810b081c090000d8030309140d00c010080d03206600064070404801003d03901c1c03040c21003991048482d0301600841448088640140c0c590409007004030603212950080400da50030502441069540000d5266140107601c000003002a403800c0c0c00c65002014510060340c0600200002c030b5200e126600c1035000c0c040c2a0020000b440700303100103030b0f100c0c0004c0300d00034081800d07424100b1060600744000c541c05a80d829000c3c000e5403d9032400e90001c0000d550b0721418110100703803401040113444200307000d032008440c550842c500e829568 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 871390521 1250 871389271 871389301
    0x92d050d052d090d03020f07090c09050d0201140409090302010f091e061401091a010e1c17070b04050d03091e050102090909010c1403040206030424020d1d0303 70
    0x59001ca40351050041c0d41d000802c080d80c2940e280105141a03110032030400941c1c0310380c0064040c0e5180240340000810320141d110790400c0709400d445182017a45488104a1358402ca080c042e070601600d1705858101403944001071000e030582803800506141d903820004c2c00c56034440c0c2c0301c00016180c15120800304282d540c24181220030b62180740a811028a041005800e40d10798036000c8210b80380001c1080e1200350402d41440c0902103040d56806002d030011520a409048129000300c00c0340000d03c07100780241d80200c85240100c0c0082c0c4401d50a483d000c0c500d90000320251440440d0205010030801305000d8000c200e851858184243d130303020b49545141d95901c0700c041e07440201101d00b61041040a40542e092100006c2c241440c600d40100c10754048c210001880c00003800c2200240e2034000400d0a4070301894014003420708540e110b940c2d22a02c1103010701e00c10903004010543c20b50480c00350006200c03c0f07104000c00f140c1305200044420b405c00c013001c82e100701c0d50824010007042440100b01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 871391771 1250 871390521 871390567
    0x30309060e091e040f060504050d12053d0b0a0314010311300709111804090c050904060212100302030d0807200604050c09010612092d050d05 62
    0x5601c0d00b84c480b460100403000ca00180140300b1814a4104401d000d80402c4142c1004520340300c0e1210030000401e00c10484c3c0e4106c500d410036002f80301d108031103c0650b0800c1c48030607814000302607009e070a0200d203184c84100d65000356a00300000130001d1115902d07000b0300529807000c14440c00154150f03074036801084090b0b09401c2c020031041203e940503403105101341c0e40750782c13840ba0003209452103031b1622500c0c0c18090103210f480711b09011090200076104000c8442e1401300701256007808603002d003000040d00c2c1c030076400c2d1502113072800085000c0c0d813081980d0303010302c2c803510300181e40d408460840950080d00a00350b031105c0003cac0c6010000b5803000719444903800081d107002c500c1c0d40d82d0a20166450100201140c13027101d1240a041d03040c02000030042c2c00380e4041e00868000c81300708001c00c60408001d0040c1c3c80000c6c01100f0002c80708a041d0000103443c0d200d005c21500f00120400300091000d080008004121030354081c202c1404414060003060501a1901510b00000c507080b606d000050500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 871393021 1250 871391771 871391821
    0x100f24090506180d38090c0114070816050c1509190f0b130f06140f0c030304030e04230c0904270b07020307020a0603020c010e07030309060e09 63
    0xd81040700d5540c03104207101c00d82d80b080004000c4c48683c8000703040e03c402181000c60014000a5690913170071481201d611a01d8200e00401103000b52000443c1c034003801140070070105c1c201f44111400150160090b1800140727085441d000e008543c01d2071481e240d4100041c5020724161030004c1f00c440411422152002015a07078009101180d4400000344450350f4000c20003d480362001083c04280030f40140a00707505034202408440d207a07100c9090440d0780348141c07404610003582d00706030f003c03060000e400004011b05e0301d80d06207188420178505503482114118000b980c82d20b014452441c02d807007880d030f4450420110051404070041150080c0d00007506580d80d8800129002d196952903400c21700c1c801d000d0034074501c500040c040d55a021074054040c12160004600001040320781b00009507004c5c540c0050441403031a241820640080d802107403200619500c40042039a07281c000c00c0b41c0c000030343c8256103003062a403030048003c2400d2041c1701040d2142107140e00b0301c50b0300b003604051507021801a103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 871394271 1250 871393021 871393057
    0x1006060801052b05011a0a05090106030c050c0a030818061006120b063405060a09061d0d020c0a0623070209040b01090b0609090a05100f24090506 64
    0x52490350480d9032500c1218160f41c1c81c00389000c029043d000130a504281c0204810a6240c00f420081d1044440c000da0350000281030041103094800e401044401c4005e003030181c42c050300320301c0c01424000c4102090b8045015903090100c0000030064401c80030440c01d016054506000014805840080c40303840304000701c511a00341d40490503030020407140c200030940340c0e4510021200c200c1418002d11420301c1803412201d101d00b03690522041101c0194010f000e0b0085684900440f0010002060180c1e1302039562250b403110390451303080107a044000b10001f1305050080e114028900380442039103d0082c1c00554041201c0b5801126400300020074a212046c440c0420489580500400c10080e500144490600050005441d22641a610a80402d010050f00a001e1007110721541c950103800c00c408400040c203401c000d5200642005041c0c03010350243e82c1d40c45640d480485241c2003c1c1030305105128030101c0303400d0002480d22203403203401d140031020300e0240082e0b1103005800b902e0090040309 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 871395521 1250 871394271 871394299
    0x30f091009051807030f0c0e0f0105040e0406091b060206191503030503041104021c05060301020301030f0605070c0b070203040801051503120d06150801150e0a090b0d140a020102100606080105 84
    0x2031b00140d407860074182d4200051880e0000007401c3c0d84202500034003410240307400039091351181045038280c0f030908101c2d01054550b03603240d50061407107040640d100d0b1024030034030260500e0400d0101c01803480398021b1045090800c02e06403c5003040d02d50380f41ca24a80110036080da50010322403c00c4a8260810580320369460800c210a0342c01454490351141c40000c4040e040c05c0500018a145240840104166541c510925080344030a00025001c03580c1c0114140000b0140c0e0003060344101c6c02d190440c2e0741565035841c102c1503d403d940030000358102150030b1042403424800c160344200384d0446101c031411a03102003622100c0c0c0780c2c440c101c840400982d00003480e6180d0002002005035920b101d0007207210b0640107010280070b00a00c01c45481504850180b5803242c0050b001c1d545000300a900d5840c500740300d0600a05c150304506800c20070080c107000101d9a004034018403001c100024010754295440020304042e44001408030f52403805105101c80c50f84107210701e054500aa40d943e541c0035038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 871396771 1250 871395521 871395527
    0xd0504030b0f45060f0109060803041a09030105180c010c0809010f0c0813090e1b040b010e0d0c030c0509090d080c0f03180d14070b1008030f091009051807 68
    0x3c540c2c24500010900706070404600001a114450028201000e10350b90303c80341c00b0380549030184141030256100384070510981041d0603203000c43c40a544c061902d448280004a400d40c3d0b01102d0901600305115545a180320050007841c0c49550300b41b810701c07007020f0300303a41e040c070b060184540c0d503030420942c0e0f20002440b6006d4000040c1d500d030000b280c151150082c210780f10b208c01680c000c0c410f14038140300540325488000211038510304410380111880840b03ca00303001c0201040d01449040000c0c3c40020002c40d00c2c2d1030718148059000300358403d1010b00310b0800c1c500c3c091056000d02e000d00012010052100800304602c03201c0c08140c50403a19a844142c00c04020b4080c1c00d0814508202c00010b111250f180d00d01210019100c160030784401420030300050b070b44103007004010f200c40d100402128000421544103071754481150f229003540b640d11540903901d9900000a844283c44000079290864640450800c92001b40b600e800121942054042082018501d500c081100111030100b801140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 871398021 1250 871396771 871396861
    0x6061b051e0a0c0e06130501122a06020703170a1d130f1d030910212d021e1b060a0b0a0e040c051e030d0504030b0f 51
    0x3401020f4003200c0f603141c00114400000c261102445500d0b98071b0605040ba00c240100ca0407500801c000203111201d603159101c4062405203a450401c01141c03c110a0041038031010300030705001d030300074000706045207814a01400250f1940c3c4580005100c01500390350320880a070105040403914054580700b04000c82d9000300290f400c0e50a01d0f007400e003da031440b10070390701070000c010348510340580900122004949a21400b04550b070441c01890340d00d01d45a02819054258604050041909849503e50300302107690560381d61000050340c612980c0d0880546161030800008020f04501e00462440420020009500010208000450407419084185841c606c0c8001c0c0c0900351111494220a1603000741340b0121401e1003000c5180c2c0200b0b003101c4110715540b2460380659009211b41c100703010061094666168890000d40c000c46903003c54509005c00010b82e0290303100c03541c0721411850000e00ea09070091440c2c035800c040c0c0c4200000205214000c03a03441403100d5410f104440040260701c0d100e4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 871399271 1250 871398021 871398023
    0xe010506061b0a15020315010e2805030a120212030601090e0402010e1e0301061d01120516080309130e070b090d0204050103050703061812210e0106061b051e0a 70
    0x4404c6101e0200701401d981c00540c46000c0c00201c01380c056031b01d8801940c0403040d620703480f9080710140200380c00c4102011241c200e200078505002080c40d5450002914011400381d007280c44d80610302050706469010440b06803042002c0c6e503198110b1400600080a4030b0140c030494603c008880d0104044d6400303031a03040c0101001400328a038034002070101c0d0b04d5a0103041202d5000e0f6203081000600d010b241e2a14805a5400d1460440641d00e422aa01a038540008003581e080c080d102c2060042072202d00e020780241603107809581c8070002c540400000040d166403c1103d5400c01d40301c1c0704010b401150510a44660500880c0c07504914400f081c0c000c0079140c2e009401625100010052010000b0590101e034480c603420f105c01c0244100030141d00d210400014501100e041040d1070842c0203d02203105810304140140d0a54600c071090010303102c0c2074541c401c0a95440c40103010840c2d000c9410b0b03601580342030b464010b030f440b26910030390345190a4280c808440000301c10a8007100e8180301c1d01c40d100e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 871400521 1250 871399271 871399283
    0x11d060d0608011a030c010c03050708030907120507050405070503011511120d050906100302030604060b040209060304140f01111b0114070909051e0a090507031e05010e010506061b0a 80
    0x8800075070310100000300d801307518030910601c0079040b103640c1303c1e9254080d4594940c5c0c0e00303428100107940b18407407500080c10034601070290050101d20311a1807201104582e005030020078203d0702c6c00b800e110440e1005032840041110800050014401105207006042c1180c680303201400e40720704100c0d041125004140900080010300d0080e10500782d088140220615001d607101900c03644190700140350180320003501900f00000007808121036a2084003040009480503107054802c600081c0340f0352040320110360841c1d801d0070f442d181d40400c0182d071a0390303041ca80007040240303510390f10a44a405040b0010601c04401040903c81f004207420000000742c0d210340780040c0c0d003400a07020b4010b1400707004090959141a00003003040e9042e0380321200b1190703512440400c503103801c082c44018100c030b184240e84074421240c000000400c840d00b4103004186041800100030810301d030990a54500740040c0a03260b04007410301803142d460b48100c803031020503203003c0c90307201c8080313054107080c4a0313280c1014044c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 871401771 1250 871400521 871400531
    0x6051b1617030c1201050d11060d0212010902042606010521010504031710060903171903050105011b0c0b0918090c01090e040f080906040302060c030901020c011d060d060801 76
    0x44601c05034044c0600d01e4070824030791040d03030700e40303040c8030700e0341034644e8090070000e0341c1440000750341480c000810040e014a44094a4148191a19500508280d00400343c3d41e60000e400c20400d44042d80108501e5011489121090554050607a0300c2d40180aa144180741c60442807814140c1000c000304503040d070b40c3c0288010303e05410041c02980e03400c049862040c6001000900c9400000d60700c9082e20140c0c3c0381c1054440c119110258640e0004004440303449040015174001c0c441017510503460b13000e656010940d9810038000401e880710149101c480c1400c155010000110301c40100d0043d5800a600582c8610854001613200c0f401404000b0041c040c500034170104001c04501000c88001c01e0702d64903005965040c0820b0500d0080364042c1401c429005100f00080001009202c035800041c001030806807203400040c8603a000410201d0958000034001465503010310040010103000d00b0700d000051b08061485800000c040116841000c0c0001e01c8528100d195001d00c0c040d01015008200d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 871402877 1106 871401771 871401781
    0xf0307180902160c0b0f070609020301180606030c0e07080601030902120106120606080102030106050d090507030f0803042a091805150406051b161703 66
    0x610300d80200010041c0550028004a4024030858040c0200f1442d00c0356100b01203511450380b1060910207000089416000d035a90300d90808000324504515100007801004079014000704090313100540c00900c0869401070080d40c0c821209034030b0158441d00001403040e000c88181e40012400d0000803415407083c0c01007008607102400e007080504603041d03e43d003564001d070407056a4021981c2400107000050241500408012000b1850b41d41001300060480c41002a030b02605612075950200300401001444000e5812941e1640140743e00e2500d003015a00a6406440381e0700345001da40445103581c032440001d0500e0595120b00d03e8a8030a83c5409480b00403000c05040c1019007071900032070380c03e015100c0f02ca5402006460f2901e003d1622200f01c5001620041c41c02181c1035190700030060f00c1044070b000d91607404501d80507100c1407a1044603041405912075042c18040700b844 = true := by decide +kernel

theorem cover : BRFrame.Cov 871223021 871402877 := by
  have h0 := BRFrame.cov_init 871223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 871223021 ≤ n) (h2 : n < 871402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
