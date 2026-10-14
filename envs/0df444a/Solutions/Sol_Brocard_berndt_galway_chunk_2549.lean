-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2549
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:02:23.241986+00:00
-- url     : https://prove2.me/submissions/5c8596a0-c5a5-4021-ba53-d434e3eaa69b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 458273381 ≤ n < 458453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 458274631 1250 458273381 458273383
    0x61504061211040f030b0402031501090902010206090102070b070809030d0204032010120b032a030706030507050d0221010303031e05040f1407080703120f0c200102100e 74
    0x468040700100901041440003110000c500071809400341c0107213203550820103d520310003400d40080c00641940c034618400d202d50501c0c0ca074241c00083c060381d107030400c030002c5590400906a102c03400304000c6040240315a201c83c1a844c003e0702c81010410f05070082488030500f40122200d07501501411940c03260b580c940038072107898814050000d4801402c41d404d150070103044600340100b640d5100082d005070410140020003807001219018411004100c20340c03000101030840720344480011501c03001200080524001d080e8105008044c00e05c0b050000581e04217094a41c0b88620260150305d0b10703a49086400401000d0304a503142030340300320002080c0b580542c0b00c2210501e10726105110215a000d014050794800d95005150031164005400403404c007c2d0b074488241c41d45416100301960700c480291506206400a688030318145040c40143d50300240c072069907100909024135044410740722305101225065a0010303010095840c1c011070ba2090000d03500101d61813408100c0c15110310859 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 458275881 1250 458274631 458274647
    0xa140c012a110706120b0402070606051017010e0c072109080a020a0308090a0f03060219030b010e0108270102040905010e22170c0d02070e0c07060506150406 69
    0x112507004940038900070080c0305084211040307280e0070041865a1802d1012100300504103440841c1c00d948000b10788140d52140002c280d09802943e000c6041ca050004101071080315003a032400b07101d80000c03004105d41c0e2081c41c080c1121844084880140d9407250608294420200e008007030071484100408801e0600c0c41c000d5508107151b841240181c1c60302d40d82a529050114003075030002d075030745c0e08200140b0400000d0410102c05070130b01c114281c1c3da010070f40c8000d90b1a04110303046a0041001c0b0150680c1d61044441040303035140510186110100181c5102c200c219000e040094010000303091517408585001c4001c00c0341e0301d41640d41110364425000b0f401c240201860a4105000054900c114402090040101c00105215409080b0403840c5081c181c03072084803082d881510b804044034814000d40040c00d52030003e80b1180519040007801c040c190b401c400c085aa0f09400d01010180c1141603800946e03001d00001100d40321000080e80402c0c0d51a5500e141380750014010622980c00510 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 458277131 1250 458275881 458275931
    0x915050906070927090606080d080c18040c03270213020c120c160e270c0f040603051009140c01020d0f0507140601080c12030a140c01 59
    0x1d544058551520458810403907204d903110401035000401d07007844e11440320b01e4601103010400200d490550340ca07501641c840d54881500303500081b0ba951031264010041c2948520076141c19440c050543c810301d00c156144000c0030340034030f03560340801c0d001e0750180d4488032000c811002a4000004010203d1001c080003050490065825016000728241a40261103803250000c0142403803140c80c80d0408800c0d000b803402c40f0744a10982e0340d608417628603030705503501400d03d9041003902403800310810341070240d048500b544002c0000550f44643c0501088000700301c0000c03aa00280c1078030110001d800341450360406000c0303028442040030000c1096010011062103250a00c4504d1100340700c7c561190004191a400360700200d9075420614418040c0000010150410b03900740092611101044c40e2003120146540d4030080c012b1002c2d20f0200401d011003041200d100d500000c00c40080d030b840e8040c0d01c0401081c044c0d03030007008204086d001d041c0c0e904500504001c200600010001c003160b0711010345 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 458278381 1250 458277131 458277133
    0x101b150e120a17060d080705121309062306210109020901030c0f020619020f0c011d0304030215090a080307050303100f0320061303110a14130b030109150509 69
    0x10080f03525442c0040c81c6100e650700811905482000751945512030b403000303004a80c0c070701078139800319115030710540035000320610880c0c5a84464208680b072002c03100180c005031107000050554500362521001c014108002c01d45210b81c03202d1074103122030404041780d00311688110050b00081861400c65001e042c190009990610035941040d40680e101482000503600582007640055000702c600080900c8501c0001001840e010201c001d85c0140d401c003808940c2a65103a4003c110544840c3c1400847d0300c1036a0007071481c240c9141d0009030700302510710038111100e4000c030704401c0e141d4030308010f10300804403d4203a03903642945e0302d80780c2c0e200d41c800c0b62003002c49013810101007560381000c0c0c06001902c3d8020f00b00c0905038042002400d0483c00720001c141d00840400c001061303c4035282000000b948540b444010a104000030042d603c62160400d00007000d4240300c0c0a80c03641d8214810301c412040740c000003585003808000c41e014003981d00d00a00559101081c00c20a000d09034403851107680154 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 458279631 1250 458278381 458278397
    0xc061504020a050307030902032107050111030c0a030b0301020403060c0c0c060203030105060313050c1002010f051b040b0f0f1201081b0a05040b010504050d11101b150e120a 76
    0x2000300412802084603240004109100041c5000d009621412445000030100c9840c1340900741211800140f0000f14a003440000c25400c0812009004200d003161394070000a082d841d14035144c01007802122204401c040d194981900903480039070454014680100040c005017038140b02c00307007448440480896110031700080000d0602e2011080d64103a510003008286141c54545405083c00245082554103002d02851842d107030780c4023988451419901e4001154500280b0840800c490004058504581d1090450400f559400040301d043d291071980064481d504640c42004500411745900b5411200288115402c2e08a8100904940700d00040b075401c40340c001400e84100002011041d000722004d04103000c070b071409400000c041c1d00c062401905280c0c0e2500000c4061004080645507101164410301e198140f00204a401c0e41c0309081900c542146155041070411702550040c0940c2445501500c86604a410054a480a041c01c54603101080c2038007805940c001044600818915 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 458280881 1250 458279631 458279671
    0x3020412080a0818061f1806231804050c041a040c08150d21051903090213020f070818040b030706050d0515040c080702010524060d02161b0902030103082a030c06 71
    0x9d0200724600720040c046069200c01d200034803084010240048405004a80c51220076071154807496800c240030301036889410840d1800c0c0b00464040b4400d06003040700c50300400080344000781c1d21514405069440250210706810000c9510002c6003c40460f40c0d03440c19003c0161303502070040c00580e0705401108403d19a10b40c0113500b02e8003c104003d40040a0460410700582c0c43d13409441c3c01f0303114020b16850010b69030340d407004c0da500100e07551800d00c90742c004a03c440c2c202881012400d0344c050300180710080c00c2c900c01a105018200c21240140d45410014101e1800084d40034200030340a042481701e802c114001401c0b000f402c9402034010741c07800c0c0005048025a27592a5100e65643c0d401c000180071800c1440001d600010000108607020001c030f112040039a840d540d211402600b82d804412400c40c0508017016055000c100e02074018030040c008a12844c0458041c0120402800c074191000c00060903000c0c25404c1c080302c00e00001c1003840d8802000306d0703018441c42c1c100c11071350506011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 458282131 1250 458280881 458280929
    0x30c070f1a04290c0d0302070605010e0601080a090219121203020a05120c070c030b091902100c05100c112109010f03020412080a0818061f1806 63
    0x70303d00c03c80c0303140e0344a144900050841c1c1c000074001d50810a81081c641926004068034202c0b502c0c3c01907000960001e4000207000141c86014007500e0a2201d0030118207142c00001c00c40c040280c0844c9034155102981e50071555400006000511a045c030008101c0ea20661616040e07144c0c04140c50403602c8041400c407851081c07084504000803503c40d41e0a14020020740302e0f40540080c0364103c07000c804c03c10f560200f190200500e00075441106503441c94904500c00505041d126000c0c00d1107407050001c5d88005030354190180852064510380116141410700b001c80c50441400c1030b00007400c0c541410b02d9841c0c2e90042404a40d03401c0f1204407010529502500d810cc5c600b000040540c401041c0703e0445550b10078140052014980d01c0d000d030034140c64000088011011501c21288100009030f280025500819038560180607280030079610000504402d40b030310401086107000d00f01c841c440300c0320f18140702101d4000e03040590b941c51641c0d2055100c0c50003000d0b98000d4101c5104000805500214 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 458283381 1250 458282131 458282137
    0xc040b061c0b0d200102060403020d050c03090910240813030c140d030c0c15150b0418050c090a210c08150c0c1504060608060f07030501050a2402030c070f1a 69
    0x203415801402840000d2f442115076802203001c489160004020364101580c0701c44201d03004181a2500c907513010b1410100d075028005142d640c52815400c1a652000107800a4500344e1010702a0102c2d145003483d840c0446e500207201c4802800c0c0e09405144501c1c1c0c0d4400104a82803400a4808014144440360107594a03181482c3c0100f80e54850000c613030b11400c0a0300100c10583c280080c0740d21090301c1d5252000355400a4010282c248c481c00e06050b1100410300074079030001072078404203141030105004070310846030a00900c041e04c18141001e80c1800b45002c01c1140c5035400081680e401070b150041d0685a21901d1f000c2825000082e02140000d03070003c0844044010300d9004000030100072290b03603c40d440c000d10030741328190344200c0060481c2c0240030003845008010b0700c28210b440c206101034100c59060308482d002d20700744030050091240c074680c1403110303414401000140e4445c40c0000c0f803461203865003a4050740142c000020340c15140914034030a0f03070380c0303000c0c030005034080c041c0b00701d0540c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 458284631 1250 458283381 458283383
    0x20a060314041b08030a0203180108040f060e070b0409020408100b1e010c0b0f10090c0203070206090d0c030b01031101020105060a270c020a03020c040b061c0b0d2001020604 76
    0x103450000420001842d1000c80340c2034081000c0f00400c580c0e13540c460181181c10424440d000341e0000038141001100f03d4003030755030382c1c802400c1c4920706080c9600d403450801c4111a006140c0340c0d950b40050805607042212200070942080764039626900e44000501075005403182500c00c0c4284042603040300d900b40603095582c600900081020010b030240032940e4115072054038140011203081101040c0703128100c61103180e201c04950382c18100f2803c441c080c180c107a40000207051604030a0721005074003000f1220811b4040340c1c141d03100c8140c0e000040618a54020082510088840000402ca5151542d50403280070320f8000b0101d0300d81ba0016400c2e80c108441003580004c4e901d80074480100944c00404d104409480f0440885100c64040d13003c40301001c44100240c1e0212a40b5010160304000400d5117420544052041e030a030b082c003045260041c584640070441c01c07001e50100c1c40441c0d0340705104990005044500a0aa0741050a074502504401d144901114040741040e0b50000462500039 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 458285881 1250 458284631 458284661
    0x180f02071e030e04020a03050603060702070503060a0b03010b0607121206030b060607030309060e01050907050a0b030609070516030309111c080c0307020901080f01060f0b0901140c060f04020a0603 86
    0xc0d0001c401c100c000e10108075421024065054400520740c1c54a101614a001c102e4400241c141020310425280a0001748082c04561040700b040c4403a45022400540022500c034020807080c80c03a00010303000d86001c403403542e005032002c034040090083d2000141a0000740d91918421601890b0600041c1d40840c0005007980e60751101241c02c60030403500521481d4024a40041c120390107a0364030040d1840030182d010300b6074680c000e0020114050050200604007100c031515628540030600916001c0101118811580840090b485034010302c12640d0140e9030401903901684035240280003440c0c1c80c202903c614003d032200c456a424007002c0d003040707643c0c02c11002c41150115610a10f00d83d026420707101c201d0000303011aa005860f050581e601030501c0101602c03000410b02c040901f114481d80c011210b1b01401c60702040444115011102c8100081c80d040c2000100042c90442c1e0f84160006855a4400c1d4810000a210700c070400a0145108a50f030090186e695081101500c0250300c204c000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 458287131 1250 458285881 458285903
    0xa0c0608070c030507060f18200102060414070e0c13121a0402010e041104050f0901030b181c0c050f120f0702032d0c19030807030e030304180f0207 65
    0x10038043e202030000c0612801011a800c40c25264203001d0795070120101ca4014800c0b0024230401602c8403049a5030b0700034040810640000800003540c44101174070241c07006040d000310000104041c009078019000e020030560b11410704e103410201c0390b4003d13460542c680c441c114022500b44548010000d070650440d90840301701a406107103000c00c2c0d00182007281800a0203540b0007081d1078500a1640f071703076066001030707460b503186c1400e01100b4403c0c011000d2060385880e00500000d40d00e0810542c0281484504a1520b08400d07081c40c07501d05000880c808041c501002c1d40303480d40c1c0c449408002c02d40b0401c15110850608150b2940e112110780031070306110014403004004600d0318015003a600c0c00181220000500c100d1135441c51400622440c2d10183c0900341c844a040303041007142104141039070918808c039a41d0ba241d0306410090b020003000ca810014103502414460444120a224000c06503980c860741c0355158030080043c520071444460030070940b4445003100c3d10030340f00125040000084 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 458288381 1250 458287131 458287133
    0x130f03030f0f060b040302010912020303120703021c0519270204060b12010e09061311040b041406040c0206010807092406050322240612050a0c0608070c 67
    0x103044054840c0300000d54604100707000340040d0084100504e1201e121315a1281103000050003d2881c0e0810300c10048627901c0c0d280141c4000003100c000d00007180101d0515103800c60210003910800c40c00003a40364400d049040c5442a40c0d00041c090000303180001e51484581c200c080544001c490000400400180b103000c11003104500d0007009440184000f44054460419011a421200001501d44060b10046c0000000e0700485a00960060014000c9241580c2800014a12180002d01e200900c0d803142d4156155600000941d8400900500032810348021700603c002044402c144181c0c246081c0c0f4101c0c0d0f0020a405058443c514040d00f0003d0807e201840502906d6083c020303a103217001c00c14503015117a4500342002e40701d00c0e5141c1d640c9041503584018506584140c2098600c214007940d0000f544c07047c00c0c01c000740b03d610101052541040e0111006281e154080c0d51018211040a0100080400d080c52180e104040c080e48080d00d60000300e41c511411118440131a0345010200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 458289631 1250 458288381 458288387
    0x60e180a060c0203040b12160c080f090a080d0f030c2a020613090507121802040f111b0105010e040b1b09152106010c0f1a07020303070305130f03 64
    0xe580c1c0103141c0104c83c42c0580c0c5410703084441d4001400070150300c45103414428050700d401d42402c0c1071035581c40e148101207210344030b4000601c140c01c1540f910001c00100614151144900640103081100a80705070308407407a000740c1340742d00c2c0901d1040003d1405010740039290180e0540480b0040c01e0b40e540041e070b842e10300d039185c0545103480e00340d9000c0b4040c40b5006000e0200d14156014141c45040881e244c145908054044514a88001d8449007482c4015068204203000100c4550301102c02140350800fa0714604000c00b60200c0000e0250b40000d0f103011504582c24400303032981c1c482002004160390380c80000081c80800e0303a005140b01d000c00b0105d0620840f902060070140089400c551904420f800021081201449081c2d807044010403041303002c100b91a440c200103ca07c00e4001d40314500000000c0000001c110000c0c11030b000050b141c0c8c18005290034060304215080103404841c20b212901079607070b40048072aa00060b08110000d03e180303ea0602c81e81c1e81590208004a058803d40e50075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 458290881 1250 458289631 458289641
    0x20109091e020c0a080a11160b0904021303082d0408121309060e0a0c030606080115020307050303040f0203060a1b05070201030e06070f020f16150c0c030501060e180a06 74
    0x1060461051048290204801c000280b110074070f0f5440703c81d45001c40f580c41f2403d0a084180900d40207100034010489403605504840c48402c0466005942d80000e41d070a80340308003030b5040030700381a80125000c100c0c01103c540d0040400b01c5039046070700001320324186050301d1245018000307882d00b2401c5541d03466030f01c22024140e035240c0c241e80820380751344914a00d011602e140d07006a0707003245210244500628544600c01147c0410b290a00600341402400707002c80c4070602c1032107080c6018801d85461207100f8400d036041907038010140ca66070b081c24200181130000f0010709034480d01a003804561404144d21a0607900d0784450f401c40b0003054102401d98580c1c201d0002a0706068882d4003608070241e052082c94803500c1c082d11822402c1841c4100245410134401010755940c8c00306440410203040c441e03000d0122000102c4c3c03028040d400a0080301c1380b20701c03400c00404d5030035200c1002c003c101c0103401420503540c039080460115500c28048100407003641c1d0741c0070f0f5160848007400d000700b1225000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 458292131 1250 458290881 458290897
    0x50f010302091c03050d05060316060509010c14030c1e100f020c0a05280b0402040905030408030406090608070c0f020d05120705030306180606030f1003060216020109091e02 76
    0x8242644814241608080c0242d99004c80c0002c200242c0c04900e1001ca100e01070300300500b5001480b0f140010404001c0b0715a89002d1801480004205958127a00c01e01403540500e40c0040d28070440031100510903901c0c0c01c03a007000c0c52030b80100c145465042c0701e800c003c0c890100044004010280f0321031078110052104407070000900e6020000c00041040803c081d25209105a00030580f5000c0b800c0c0082c9208404c40011401800c0e825500011a482c1c8000d2a00250110380010b0158003915041d407440c840c40d405a20103000c040350008009800c403101c0800c460198845003030742da46140c000c4030b0b40b2555403801020406600e80c10b00c09428007521441ca00c81c41170701241c0c1160b41000507119a5081710303c0881e20781d40008100040b0382441c00c600c242c515035184080406040c05000521203002c01000c4050043c001030002d0342500780001e1303900c021900072500715035035280030588420705510b00d00168007040c0302400c001640016449044103280300b1050030703e84210f942034402c0217548082d034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 458293381 1250 458292131 458292139
    0x60102010603021012050108060c0403030818070611061b0f090f0a181107032114010e0703050619211b051c0507061419021b0307050f01030209 63
    0x1074040010707200d000110400b031005840356441c1d564072025010949a05800040e10350704035030103100000c1244010b45040e80d42c141030150007a580e010804406611030104807085103c4c9100009005422408a000000200f420746015594502100c221504511031054400400300703d8038440010140241000000c020011018140070200246100741582c0200740c1c0c28003902940c0080160030b03c42d001c420b40482c6165800c4c40c206441c007510380c42c025440c3c40d24070201044111102940ca0303201000030386c80802c10b075109584442e03407920702d254122590000310f03141001060641c03402818003034001854a810440305810170318000008035142c18a201c189000602d4240040d0207240548407200c0300406407040c1524010401180c030840b0100f400c200310f14501d900c80800c00100f4410295600d5003028000d5030140304014809115201c581503141e292450141c04180d400b1980d003816402c2821800c1c0c5001741501003585503201031052a61200781450381e07130f03050750080d0007501541340018 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 458294631 1250 458293381 458293391
    0x20909010b1605100606260a110403060204030b160c05101e060b0706050609040807020d02060c0d020a05070812030f1005030a060c0201060b0423030f1905060703111206010201 77
    0x20f0358213898010640000030070151a44400e00105900c03160956102682c04654041064290750f81c0c070a18030041c000c521002e840c4e0311004071002c19230342120001c1d5800b034030031561503a50b820301d0741c1a0401039500342d007460321858061f2a928402c4082401ea25041005020707044d00c18003040004000d028a004000c5054480d0200e4070340f200e21a02000304609103c542d501e00c0c80741350810480720014a428412100741091001080c0d0f0341c006e50b8252541620411a17038145400000d0881c011502030704854814010f502c0d404582c00304003068a0762007402210390081c1c4501c1c005440d0706201c50202d44804c81840003d1108034450543c5410060a003482c02d895512140030904080c0d40388c01c26200320791904209500c443d070912850300206800355409003400c0c20500f80c41140b0b4401000400c0156000300c0780303201030380c040c003028070000c0c8000d080b0750f420f050158443c000d80c050000107482070b0045400241440d8024041e2a854000000d4440d1804002014180c1c00c4030300940079904541da24 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 458295881 1250 458294631 458294633
    0xa0c030e1e040507020105010f031103030403080d1d1b130e0d0f08070806011715040e0f070509060f0d0c120b0f0a060509060112110f07020112020909010b16 69
    0x50801940044407010700224403a88500900c015282d003e4481021a85032100410100c0070307100204007542e6000040308145066500001c1c0381d40215040503000c44c1c80001c11080c0140c86902c001b4100c082e44810036444110403d5507030321104110000400d4412200a40b211403402e281044449158418001000c070761080415207411103100200300458400c064803041141c0010105038846968a404000c2d403a02e580000c0c080700300b80d000c100714812480041240200b010b200640c1410019008220024502103241d9948010244010550080c0030000c81d10b0b041041481c1c0c403416000c3c04280c0c2005000c1c0600c81c58540f12481551115a4014041096940140e143c249140180550300042c00d1803092808142000303441600c03517a1800d00b0400054075414641c3c1e61250090818107942c103250101403000d818103101150b00040300080d0500404000400761003002e0013a0381c0e0300c0380e240404965604038444c01c010030754840201d4004001c40705081c4002c10960540403c8605c0c46102 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 458297131 1250 458295881 458295889
    0x6210312090309032506031a100e041808040e06180f070f080402010903061d03070b0103030206011d010b0d0207050f0601030b0a0c120906090c06030203010302130e030a0c030e 77
    0x503103840301d040d000041c0410f2549403c10581038005522440451030b05140c44980c2c500800910804007855151191014441030680e4203001c40000605090358030207440c58001d01c0070308844a8180301d41d00d8620429041c1c1d90786001200700036070056003203140c2410080d014409590080c104e0398486480901030b958032080182039400b03800d00f40d66181950401c4400944028041317200d00c0c082041036030800003d40ea001e5108401c40380c024800160400c81e006c84c8003240c1c21080d0668110307210010310720081000100c241812070f030282c7d0035034459076200d01410b03e903001e89807410f82d03401e480c040045c0104043c2c2401040042d11942d0010300c0c114080d680d039410000ea4075248085a0003210041007401510302c1d50304c0c0c1c0300c0000c0008004c070508404000e0f00c0c40421161203116540d86003070321001c004079503105841c1c05d9000380021034025560140180617500c240402c90060071400340020340c00c10940115610759030004055420b0208580c4100c030503601801040e4104400031040303800d542c41d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 458298381 1250 458297131 458297167
    0x1180603050a0f0209010509040f0f0c0b0703020a110604030c0b180d050f060714070f080c030f0406030615050405061c05160e0f0f0d03020106090c030b0f09062103 72
    0x3104442c801c54018850040014451050b4047c0c0d00441c0c00208000001d82e0400c4140c1004e50b03c030502001500c8103041003540d0750720f035030020810040f0000d1000240b540000d144d461080c030501c0b00d1024006142c0902a06004d030744001429a11100700c144074205003000640143c1801d201c021000d02c40c180001503850f00743c1c240c01c0d04e070780d0040c191071404000240000d40d40045141088400c1c403000980918240c0301e820750182201224500e80c81c1080740003012240c041d2203003004c813600c0c0e528015441d821580a4802e00c80402c0ca0080c0001c2c2c020b101e5064041e519003a03803101410320b443c0c0710a10000d80e000321501c00005046020020203504207202e0f243c004e085091702c020410a5240c00034003040880c00d6010300c13440c0103803078141556070742d003104509c564010386000b03409030124507099000d03240a420044099003019041411305d80d25501c10380c2c0e01daa049a800b130904a614050105c0400c05485454011111002540348041541b400f00e40e4000d0300030450389451500d60006000d41 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 458299631 1250 458298381 458298383
    0x501150f03020907052502090a061a070302032208150105061b2103070f0905030a03030209030f2e140601080910020309160b04080604020f130e211201180603050a 71
    0x1ca01b0341c1c40c61056081107540d45900440b014000c000560402c480307011b190084140080103003000180f0982054428000c0e224102c11003036110004100700c00c5c80c07030b12041c400e015846440c8607044240c002c603000b9208480c101d6102406907440c00141300142040001c00e0300b0320450b603200359907130f00c000014160606070f040c608860003691203081000c40281801c500380004010001002424080c82d82d000c28112407040c0d043c00c0041c0e42e840c08001180c2800d42c41e80a020301d078058000300084019000d030718842c0c00c1ea68650f501150000c02500c40c4116100320b080d41300e00003000340010b030b4194050624141c0149200040f941140301400000c016070388203c44403402c541010360b0062041d1a030301d81d46d201074029a8040d40c00c1500b00326004d66110381c0200068031403010b15540c00101e85442034039030704a030207110061091000310991140e641030918907140b0550800e880c1d943c44514040191400180e442c5c040c001c1503440c0c5182c2d100001103800d100500d4030366503c2e0002c00aa402c22802c0035072 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 458300881 1250 458299631 458299687
    0x601120b10021b0402040503030d050411061908010515070b091e010e0106080a1208040f020604060e0108070207061d0a090c091409010303080415090c080a0501150f0302090705 77
    0x3103e842002a80c900104246550103540180024803981c0d030080b055030715041c43e094000038150740b40d040641c291101500c08075007207080001c0d4446080261406e010b41000340c1e031038019059076500180200113200c0680321744c0114041c4000800071315110900c42c0c0100d00748088900300b085569120303141c86101c200c0e0002c107039592810f014460f42c0070300a0600a00b8100082d00303e100f40764541a40c80380785034075828208007403c07000500f0070012602d07041c80990043e04003621144c8070f10010b84108818003066000c100c10034009800d00c0d200184400581e01c65070f0f5508072900d20b42e402518445508a00d00382e00c8259080c3c0456045034a10909184c0c902c0343d65200c000301d251881d80c0c00040e41d0186054020703418100140082604141400c0c3c000340d00150035101021410104da0017800140b50013065890f05031400240c191b00022142080e50080c8020000c001e0f607202191384540342d034450741200c4090308908101600c0d01c548800d61004460078014034000d4440b488120b100200000c204e18 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 458302131 1250 458300881 458300893
    0x91f020c120610180e0a1109281802060c0705010f05030108030301170a050a050d030e0102070b0703090305040e0103050307030f03140c0c070305060c031f0e0601120b1002 75
    0x2031900140d000e07004034200d03000c0c10702403d10802c10800c0110502603c45103a00a038403203445660140d00412000b419802516502d0400d49800310b42480c0b040d403074a11031502c01e00400c2104070b031462038040383c1400c03072605031400305003600d11805040c0040c203161508641050440141c2ca58030020181c820707421014120141c00c201c00900128451841392042000600050150b04000002c490640e022907202030b42464120024074608120301c0c00040890080310280c070708000000a0301d04040320582c406100d40c05804210900301d00404034054500c1c1e43c0f060120b0b01040c020fa12001d40745000b03140c5645043d40750311a5468104080e07004443c01d81c800244401070550180c0035034282c03503461a05001e08201c0d0a1070441e44d5002602141107100005644038071030384200440002140e002c0180d030785a1610805480460704101c1d40c90190124100d024501c1810303501e4000b05680308108000301e00d4403124011030f140200201c0326103403a40c1c0d81c004250180d50752007102166440036070007011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 458303381 1250 458302131 458302153
    0x402040b0318030f090103110c01020c060105011215031e02030a030228050615040f15030203160e1537080f0c0402030903042d060e0d08091f02 63
    0x81c0c4000b00c0c440c61402c2d08180035580c1410014070469503403101c00d203804100c0c00e0740810184210700c00d000c1050300f150704c001000403529402045650480d082601c03100c408690402040083e02d2010b80e81003d280c3d80e440c0c0910004094140c0390031303942268902d18a01840e60740c00b00e417510500c0041031380540d20601600d04981d1807203052092040b0009001c1c041d0140694400d0307681e2a02503c1010325070ba05800c484002e464662100703101c0c1090140520501580060128111500d0700099011303002d40100041514003181110f422030385542000142c9603a07022840002552001459034041c50542c1d40c0c0c0041750000c140c01c80004640c0011410004a11400c0041130700c49901101e82a088101c82c4807805e2000315070b0001c000720664016a030ba94400441c20704500c80c0c3e0b0440c2c9403110049103a201001d00604c182e442d80460981e50001f00758640d0030903640000c000f4041ca9010b00541003000008a650300a0720709080e01501c800c00c01705031180b01c40030081c3c1030309444006901000c4112 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 458304631 1250 458303381 458303401
    0x1090b070837020406022515030e0f0d03090c091a1005041505090906030d0f03090303090209011502070b0c0c0f010302070f0311070b040b1902070b030405070e3405090402040b03 78
    0x40e00c1e403109000580d503040c038200f00240c1e008c1d0901b0055082c150f4800007400c4007103090041c10040c206e107400386c42c0a807502072009401400c0043c015640089102008660b44045214456401c50360610700600403c55004002d10003c2000c00700b0100007050000158241c1c2c059001c00000700ca6464080d1145e0306c0c3c0d0705000380002c2c0140528407940c0452445030850360880040d100a00851502140340303c101c0c2802e5010300b045690003074118002d5000021403100c070007944010322140b0750903610303825519140c2100d10300074190044020740050b0f400205234070f0803d404011984d0107050140c1040c0c07064483c03605c10b1526082c00e4000c1000e00044c507031812400d1100c54041c01550944505013810403640d4012401081d180400b8a41c482c4803291481e8003c0268800402038281d1645d0780c1c0c81c0524046c2e80342d400c00d100740c001400c40c080100d5584050f110344001c442e800708c45984442c0480c06c27203001010b411000035409202040001e0380c0c1903212030000f030024114086040c1c1d62401e041c1850 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 458305881 1250 458304631 458304673
    0x9080f0f04051c02010c0803100b0304062a08060d030c05010212090f030a090e040204090b0405030703180501080703090318140f0a030f110f060c01090b07083702040602 74
    0x1143ea80c4a0415480060b82c10890b00d02c00190828149a1655180c0350004442241074100a0074404048204804c200c11600011018410300f0021240e96172000760710789050000c40600d4001c500c1000005403503041600801f604240289800c131580215922038600720b07440342c0300c42c03401d080a10041004040080000d042c855985900840c034000c100e0302c0040c40044140180180d0b85403a0002c0b40c150355680c0c01000440d9080090300300d050400d031408680d81d90102000b1000318040c0c405400450131042c3c0208100d03401a16608203540d24124200c00824a407034049044c000e4004d91a4400c0b11030403014805008094007113030002400e0401c000404001c4c080325841003020380414000078003010380c07050b20305512210b612516810b01c40014140e44260700c1d8160030090101e180101007005400c06280c0303500903140d0110704c1d00d40c50b0040340c24020442c0c0c600c6038075607540c030700751406c108540c54603040d180d151041000078020800c04100340d82c0716611840059001c0030712000c00b990b582c80b00c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 458307131 1250 458305881 458305909
    0xb06030f070e030d0f0309050c36010e01030b0907030c06020d120606020307240f1409010c080c1305090406020a080903070c171905010509100b0604050409080f0f0405 73
    0x502803801c042600401d04022080401304141c2c440400b41c2c20481c0c10401051066030052142c0c10581501918a0030340480020407880784840110040740034ac00400312a043c1d400220400303e180e070031a1250440101f028052001c1031048903800004508080020b07405050311b13901604c130306941184010082c0202c15150003015140000800030a90000211520b481c1d00c000c0390305140d558500c01001403031460340c901c9089030601c0280f054090141e8040741c803100b1b4100000d070160b01e900c4641800c944d0020182004101c14001045411034014049c3c003610581031211001d1039124030108950550070384080354481d402240b041c00f40b980010360b0640c401c00c103000a500307006068983e040c99191502c12441c220040c18001c11381c004080c4a880180d02c0028460f130600b860030b140030350080404132481c0b0290702503461f40310061411405071421200c401041c141c186414031040100414807040112042c01007040320302850f41d03600025007079a1401c00b0050b901c5a103271a017840011010554 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 458308381 1250 458307131 458307133
    0x1060f0207050906330403060c08070210050901021b0606040506180402010c0305042c07030b01090b0309190311010506010806031c0e0607060f0b0d23010b06030f070e03 74
    0x20b20054840e81ca0b110307841841240e0302c036152454041e0780e03142c5007141241000700820040d01d40080b04054802441160f1145030200303c540c040c524220340480081d100240180c2114280181079840740d00000c2d0031248500c001890a600c80c01c0000b000340c18580240c28a400410801179149001d00c40c0ca540140b055403405080c882035008243c541e40d004000905001c0f14280d10302c18140b140c0d054070301504411410541c1344442e0000c01e00c004050002e200c69062040f40000d0109100c3d019a00001106848401c07100b420710b035030b50074070b50002082c10b8458494030b011003864124089815160b64041e440341c1c210440a01122030955500405c110705004507034050152980b4001071020515040303c076100d501122001e0300b03c410700c0760b13844820350051011540b03c040c84a10380c041c1c51a0f00404a08002043c1c00c0c0050002074400000090b082410b541c3d50300c0034500003012803940c006289400081e1203e0542c00003081e5400545101740182e4952080121082e0030495500507100c00310 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 458309631 1250 458308381 458308393
    0x1404020a090b0120010b1e040c0e10110c36040305030c0a110609030a0809010b010e0613030204021801030c17061002030c0727020405031009030c0c080601060f02 71
    0x200068203007030ba4107000754104050151071311520b402c2035019904001004100524030ba409206500c003000b0080b42c1c1c64401c614046075214000e00030042c2d00d40d690b0f4050002032465186a00070743d400350404100b241c1a0060019010680e6a02d2062845809000100c05070b0840141802c04504484c0ca8008020061810900c0046500042500c1d03102020310041c42c0d07604010001112620500b03900c0f4030180c4610400c5c400e6113103010010f4501584199200c10990384c4444c040d600303891048030381c940801ea1003603060300309080100003008034030502005070b002c00b5580d6001c81d00302c0c1d03c0302140c0c18490034800c580e10351f2580e05000780485401c1b1850112030f2014508074000740d1110141649110b40c0d550f03900b1000c658003d1041d070f40048580710507282c105545030052501100e8103420744000d01164152104541014800c2d981943d901400910108640e07400010050020080540502c21449030b9000000c42c610390010240c982c00c1c0103800c0b154906000500040d04285c90101135400c04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 458310881 1250 458309631 458309651
    0xa031a04030f03020f1206060c0109050d0e010206040c050603040503131d0105030109240e0102191403070203030411280905060612340903050c0d1505070908011404020a09 75
    0xf88060300c0240c0804030303080d00d60347c444000040741f5118101c00503509500705032680f4144440881d25495120340c0792240c0c020a213401c401261112021100200801400e10090140381000c4002d15030007031160080f02d02c1c1241c80d07180c00c40f00c01070f240d0003110f0161004101414a100c4404464010b00054000748010750b45540e030030300b01481e4880004a90302c3e40800c00c50340c80c180c5800000d000603602d40219aa940c12250310708005480040190114052003101c1c00c2d040b0f01e00c022a0700c40c12141d809181982c07260f968a002c10000d2103040795020080242000c0d00740400d40c6031526001e10050000341d03103440e00d001c5074103803000200090312502082c4596540030f5245804d05a0044140c01d0810207085c100440b00c01c110781d902d0700011165003c9240c0b000c5180c126040005881c0508200e82c0d40e902d0340070400248103030b104401490400718030300300c081691840d04540d0b04110182070203181746446501140c210340c41d8484c40d14050b81001d0600041d8201415004040d08500700203101a80e11 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 458312131 1250 458310881 458310907
    0x1206040203150105091807120c030c080303130f0302011413050601062f01091a01030302060901050c040303030c0c1401060f05030312070804080903030a120c0305070212090a031a04030f0302 83
    0x14040861194204006e014044050050304040e001e0b0581c51590345400d41450540c07010a0f0104803007148400382d012912450004c2528400e81154580c2c0351640402d40d036400200c400ea1404a0641d921013024104442c0c20156242c40342580040b203103e01600d074107006180c03001c180d00500c2885012114240000b0346034107012010520850010608420f21801c0c034014420344401501c00c900041034161141c001d1b41e50107048030700039400c8902c241c444c650101e0803a681522043c003a00410841000003c1c06504001650002802c16010040450715401d442c03280600810b4100d035036404052020300012140d1102071702e010390080d03013080440724201f0f203044006032941d024030500070700140402002504661402d20041c1c10749448409480d400740c45001c00045400205003410001c0074031034424491544180c0395580105411207401c4c413004030a034008030b44560032015a000c00b02c0800c03410b01e0303203882118000ca074039034092820782070041000201c1034903c01010700400c204143c0e121 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 458313381 1250 458312131 458312149
    0x11706240103020a091a0901020609160306050402010203070b0f010f06050324120706050a09330c020a0e1015170705071407050f04090803160e1206040203150105 71
    0xc0c00c005a813003602c814151104000d0b6030204801c01d03c0050910149400c100c0940104042038003100c1c0907403141d209050b180c60300700400c1c0005111507101000031840c540c00064200740180182c030310300241c135122500c1d0b12300119400d2000d980c4400041000442d051912002407403989042800c4d17041c00807503040401e46162038420049a0f0f03980020300c5076908041410304201d01d00c104c80b40d9135a541c00190081d040700002d54003203889404005440322160b68603a544404840c82a407102e09160f5541d05280c3c400d040c04400c01500000c0e1500680300c10300504080d003000700000d0f07050310304420200407824464001c07140c40141d0200c0560342c80d4101c0c10304049880721000302da900d5a07544004480f5400385035405004407140303074540c0100b0400482c00d4030564070305495200d0540074103800e00095800d80e040082004c07008100017a01c1c1d03a24000404246e11040c580a4005114840021200180b41041d0350454001c0c0041c0011031904006003038a01496800092296140000080c3c080b2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 458314631 1250 458313381 458313451
    0xd020a21021219090906080c040c030f0f0b1f090e0712060603020901022109130e030c070626040b060d06110714070515160b011706 58
    0x1180340100000d20500070b0080701c61680e44920000d4948490031503044610526900341c0002c61201540442c250189000325010b88002000400d00d4042c0e880c1408010030740c0c0e681a034201591407020080c2c1160350b00941e4401030f0890404154007140004024001c0b90540284e440d031030180c0641c80e0b039180c000f07442008880a903185030700560b0f2107110540350300410500b40b50040d460400041042c0341c05a029103c210002c0e400c55002c0c680c42c082e113440149002c2c02c5040401e105004200c400c0c42d01c400304000c8800141d501043c10a40c0d0410940785411a00d907801c01600069006c0c4800c65102901d041290340089581400c000c01e0b43c0c4501c0c140c7c00c0030b00301034148241400011a1074484a1114000e01d0340f1460811890b01d404650082513048040e081351060702070161507400c00c5001400006070340f0010321000102c0f5000300b400846910800014403050303441805200441c0c2071907260350090606254090595101c2c0100c2c0e420804010048481c0f105002d640e150b00b06040e16000d0151 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 458315881 1250 458314631 458314673
    0x4030b061012051305010e210a03110c0a150204030b0408070318080106060905030a080a1815050a030f0213030602160b040c0e101212090e04140d020a 66
    0x142203107034801c492150242d000c207000300d41428284045a1036940006000e98061802001040d07040d0f81515140d10b00004026540d056040c951040c00c29024010800c401450078001400c240d10f8a8540051704800b20102040e00600d01c40010310402c299410b86140350750750110b150500b15550070200801c040d101a0204102060210030036010b87c850707491024540050b01c0105641c0e141160103010340380620800140c0100700000d1505002500d2810a54408120750038914400c4040f00d442d541015414043d0500180c0003504403102400e04000382d030555079130383d0745c0c0d19286005000c1d104104030400c2103510421000c5220700d10b000e4404203482d0300040150396011500d0400c800a802c919025100185a1007400300f0051001c0e450340407600218581011a515081c00071002400d0703201d000c18502c0070400000004600364400340941440c0d0412140c0720b0380720b014060414501711012100b80e030ba01c2180382c8142c0020010f82054001a00c020000051503559141000d00307412485020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 458317131 1250 458315881 458315899
    0x60c070c1802070b1014030c01200a0b040804050f0d03021b28030605060a080d05070c030b0106181a07140a0623060a03020f1e040c050d0b0604030b06 66
    0x40d41d01c94048950701d035004643c0400a003001c0300600020501c034031540743c1043c82c000d8110703540c0c00d020070000c692000507180d0350810384003d89141d4890181007144141c9018541d40c01c000520f0800b0310780d015501400d4460b40b5139090000b40680c248600c108244141d480c0809100000e80c0080c00e0740c010894581c1c4085d0030a0004040b400b81010500d0038070f0903c924248125080b0440c0807440100d070300440b0148400d480d07500c02d2001c2da454500611955412282c291201c181c000c0300180156481800e040b1801580e98480355010079080c0c0040c2c0004014603130882c41200465020f40180c4841c10b107040618500c041d284600e40700c0c40000034200000810301c400c031711105100b90722400303421850901000e0303160360740d480780281280740100e48490602c0200d060b43c1007400fa01d1050343c1d809000a40c80e44100001c00208001008444175442d00d60385441660352158000c1c0004040c641c1c403003170345600c1c80100c9070040e0303500482841d018450a201c100041542000c1d03a581241065801c010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 458318381 1250 458317131 458317169
    0x6120d020f430f060e0a12210c06180318180e030d0507050a1106060102060703020304020609150a023903070305010908090a0605070b07052209020c060c070c 69
    0x104078400c5a103c524005420320002a00d2904134811501100d42100c442c4c9010741c03510000c0c4942d1604490150043c80e40201a40c5a1103c0440b882060310043c02d100310300c08815950402a203400503441c089403c410140c001c00c01d9005002d4441668423031203001502030804160594041d20141e0222009895011200702500b05004407401c5120440d010300080c030701000050a0340d482600d18038005588040002826032011038000c0c040d5030141c0c00303041542c440c80800c4000e0741011384140c2c2d02c5a0100080c81e916a916818240d03480040100c0c00c1e00c0c0e84016002a041085850720500b4468020000403040888031501e18460f20245200b140c40420081c0803d18000d580d0308010f0140d849e003502e00090143e480c0c080c00001108450310048103884003012a00c078021101d00904240102010a032041e00960207803000f040c42c500c3c00d405070400ba07000c000e510401303a8010018035500183e904030b1b8910500c01e181e4000e210310001881d040c0140e03a01184000c0f00d100c0c0540290300507404078 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 458319631 1250 458318381 458318503
    0x9100b01050a171e0f06120a12050a11030a020d110307020114070c0803030108031306032702130c05030907050d03020604060f18120201060f1d06120d020f 68
    0xb22440c0c207103021081c074500e40710070a0317100c02009440c0c4034880d03001d484042204450000e045d9884507170022450881e6034510b10280e07400d410215170389041c0f0040c001000d00043c002c001420007000701d60300400f15942c41c0e08028100c5007050005d52500d800801c01fa40150340c100068240a03c0c0f902039155485107e41001040c4200940202d285404004000034141d9000800b5100484c0d040c01d20405c201d0303548000f0740072142513408001801e13645125842c0c442804000311880580041c00c5880c00000f01e0701d080b4111050b281c0c0040215201000784103a81b5020000017001e00301c03e907028540112540c030082c1d079481c0001c0000705001e4546134074080c21003164100101c24586000140c00d03c03d071900d005210007808108000041d131801c03800050112682e00c0d08800c40d08040c66907174460001d001d8220341807100611042c0c2101e8400411507803140c040080c011401a240d0140c074400aa0840c3c960a010ba0521401030b400b00036440c1810507981d10103294441c0040c0300d00c0481d84032200c8850 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 458320881 1250 458319631 458319661
    0xa020d050f070312110102070b0a230a0f0f020c120a05160c15030b060a0302090109050603250807050d2c0304150206040c06052109100b01050a17 64
    0x100560052040000801c5060b29a40c204e800d540c2d00e425280000d03684586080303010340103004e08412070741d501160300101581c0c8101c40d6019680081250148030446400d030ba00001d580103580d03d07a40d0040b801110318244036548a00720342c0a0258030b40a41c0c2c440c61903544c5103c4508580e44000007407803007062401101198542100107011172461100c03401c1200a140d014410704002d0041c0007290604644644111500150001c0030039042c010803d5084000313411120002d4144000c50001080d2542c80d5409035210b0b8041d5074246035100c541c10300c00c1410301c1c00c40130858280040c480901c00019041020750b2800402c0c00d40004609640e01d2000c401221074280c5003080034100c00281c0400800803000300b0584042d452000084403480100304e907070b440120390207009161011400e00c006031082c4001c040c01702c0300384008481500f12140178992400180c40d6aa0385078000366201012001601480781400c0c001d0030072900b8018004405000ba80001c840c0c0d0301b10440d42000100580000605 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 458322131 1250 458320881 458320903
    0x50c061501050c011b142a070b0301090c1112040e28050a05090a020604050603091501141e090a0507051c05060f0604050604060e0a120b190203090a020d05 68
    0xa21800305e804c1540c10b041c0b0b001c100040d0004448040d80c2444414100031101015084a4020004010641800728510341c2c012000028081c030303c00010320001da00d010b103001c3c0c0100365000401c00080d8001a0205407040c00c100c00b541c110043e19145104d00d06c0a4074200c920b00b00c030712222075607041c19491800e005e0b11040102d280040001c0354000d04164040d601c61070380000100700c00e80380c02e01c2d0a43e46644d40100254801c00401c8280072a0a00740041c64105040d282100c60488400749102c60103102600009541c545254003d00f1615089000700d03500e80e0741003002101010028041981c0c12002041100c0c0f03151510080b440d00c522032002c5a488004901d03d880c0f480042c245400d02404007500c11920900d40c0c00c0114141e440e01c40119011075100601a0780b40903e042025202c10b1006664250300840300000050301071030300442d480c0c244d4414182500a0700d440928104407028241d0340c0b0309650301c14810418022800100c1401d515011a0950711044207854071a16141c10014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 458323381 1250 458322131 458322133
    0x130203010f0509010207060e060c041202121e07061805041a040203130c050f06030711070e0c0403060513030203040504020706020d1409060a05060a09050601020a05061501030c050c061501050c 84
    0x200020f591040d4003508040c1e10070307441840a4041c0500d00d50341c2d007406460010300640204810030601c600450740e4422584050303c5034060111036034900307080042c1c1d0003440341ca80346c0811101007130500520078103014000d1410b2003001400d66940701c2d00e102c0ca01d030090303500940c0c0d5207010b174000003440410900683c1008106540d64641003040a0300300c4020b20341201d040c00c803228086880d142c030340d8402d068041d000d40400d0843e982c00e1411144815078800407040ca010f644400b0582141321001c2ca807007100e04245090782d0311700e0341c98581c1c11944020200380020003409100c0c1d00180c0e01004480840390110390258842c005400e02e000248603101c80031360580c1c600351001140386184803140e4462043e030001d8038035039035500701e680d02030740d43c103c4e443c541c00029030905021002180d0302150300003806204860711108079680301e074a4400d05a804e06a140080000c8400c0341d82d045c0648184032555140041c10808904210b55441074060300c44120401e8405081c001c0382d01c603070142c40245c1b131414 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 458324631 1250 458323381 458323391
    0x2c070c03030f29030303090c042a0f0e011704021917010902010801211b0902030702010b1011031b011b030501031502190e0102011107061b080708130203010f 69
    0x1103000c0c9600e050611a102103e0458075514442d14000c025684a546100086c0101c20404801c1000501e100280007112414081290401c06001d100101e0308080d980c480340c0c042c03141c0f030b100602481101030b03810341003151061420b440c55414419264016a064490300c401c0c0c04038500c04010094160004404c900210110745150714054006402c01c42c002c0c0c075040540c0e62035a000000321101d0400301441c200f035083d0f041001440e5054455400c549515814000390386401d44003090364000e9464a0050f9114500184107150080d5000b0b4070310000c0c10890805400d6503201512800b40700901c05000255000045916400303411403110042d4440408610101003e806401031100303000548140f02d450500341c0b2580d4281c0b00310340702c074014105210304021f030303110080310450a65088c19046548034070002d04040000400307000107902c03c0502180c0c0072100c001c4005041091098242004140010b100b5183d40240d0741c2c64100f444070b4030041e4045058000b0a02411041258892480c581 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 458325881 1250 458324631 458324651
    0x2030403052a0115170c100c08041a09040522031101140f04030f0e1c060603200414070905090417030a0c0806030c09220605070203042c070c03030f 65
    0x14482e594162080c8170910b14a07420b160060682e100518214503810040c142e40800560707008031341c820061445001d2044c40c054513003410017403403080203247d002e03114008903409502d450540a211361210001602d40c2588440348088522140d40308030150038402d1601c04c0d5a071000c003c0d00444628070721404825460304010382d8942d80e1003805c480550000390b00481032800e03284a40d6041500300001442d884a810902d000c49561000f403440c03c039003056a130003000000031044c090380e1103000003001c8800c04c00d10002d0300380300c1500e2030240e040e00c030402940d003000030b1103800a00000a591080e200030a031665246090701c49544408010904801c0200812140400b9604000381e8070800340d880c85400e445190900d0f03660600015a0f6900514650010b40d06a0029045c540c2030102400f01e02c9041c030841d210380c0c080b80c5055620030b005810000d424400b001c0c50446000d45140f65412070000f07002c00941400d80c039000904020200005100345d4428140701e50401d0120704119a0104010088 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 458327131 1250 458325881 458325911
    0x501060b03070206090d080702030a0818010507030c090605040b2221030f020c031011090d0c0602010b09090c010804080f0d0510080114010b091503130605060402030403052a01 77
    0x88901e0a0783e441b54055540040b4416483c0d03a00501c066001541092003101d0246c40d9803074002c00a07020043c1d8410340d024451000d0140368011120764a0004d8243c9250000812401b070b40c1c1c01c80803d101c0104010001c48038140201c0e10168040c0e6009208506c20784040a5a814198005c0709020324440310414101c4440b02e040d02d44a10984a00a81d0800d42c0c500743c6c0c50318010842a0b49c541c0084000780395100702500443c4c591009001070520701800103000403041c0c500b164064480d0030048400303015640e02489407511451b004c580300c403003a240c03006a090b640d1000c40aa0740c100850000814104407054003915128884000f0040d1911400030142008040c1191605030b040a8440f00003103246062042144032044100c2500d2280e003400700b100d0b86a4481005650401580c140d820140c001e40380142d8010b00b54810890402190307801c055080d04e034041c0c810fa106910410600000a4000c0102c40c0b105040104a000b418189154000c040d0807052a4030f00950030440c0100c0304041d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 458328381 1250 458327131 458327143
    0xc0a120c1701031113050f0613061701061502010501080a060b060d0608010f0b09090a0b1005150d05060102030f0d050711060907050315070903140307050316050124120501060b030702 80
    0x21041d1200c91140a01845d104192802500c5e500100104800811f4041c2040700454503410024200400c246a03603040400300329400c0640030701903940d10761007406804d80c000d91604000406e44001d200c40c0d414190300740d03100c1840d10700007055035585000c0e4068603180d02c01a10350401c400c04c0c0402c82d01d41e43d440d0050181026410010103103292040101d07107840c1441c0d5030340c01882d640c0010581c24400f90f40b00c800c00070000d03000e25030038900d003900041d1940c0d4000c020380d42242c402c0811520740f803000c0d00c000145d0340c02504071415500140a44007001d41140142c0e514001c03400000300b01502d0351310f02520b440580d030390003a01c00c2c001c8000700b08022038005001d0007281c000b0b0f012038001040301805c050b05075001752043d0000030007a0400b0800b1a110700b007031a00b400c004105403803421016076104c03032440e0301811140030380d0541e040403d41802028807800003000b41584401d404d056811070702010550a600079a07078404640ca00030130501c10250b1040010b002c0c400308440c0d50f4102110080d584031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 458329631 1250 458328381 458328413
    0x5070506070f0509040c030605190302030708030712031d0d0e1003271403040906171b0405090109050a081b0f0a3008040b0c0a120c170103 61
    0x121034440441c40e014032420099015620a41d00c075030400c018003040002070600021680c0030140c50b410086002d03940d000f50101000340044409400e546144145802c0145542c03003054190000c0c020348010030ba486540c102c440c2040d24000131070070250b24100000024082c0c0811070b030320501100e41481504541001c180100484101d0b181d071070035102c11801c4d110611826082038a031103a00c2c5469000d88041c50180c1d034400c903501001a500284035514580199001d07412081d11203d0400006452013000b507901350030100984082e03400200c600f0fa0401f5842c1010740541e5651000940054081d440b581c0a1a840402d43e4207075032031401c0503030860f04108d200610991a000c11010041000591030260520300c6010700300c4180652140415450440707079804041c03ca001403141e080c4002c00786030113034140586031401e050038a030803d00c1c54214010584804030f80b0800041418540201d001c10050b9064180440c0310b0600c49030888220260500040d030748500c0100210800c403454a104140d5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 458330881 1250 458329631 458329633
    0x1e0a11010f060506070f0320030306100305131b090f02122d07170118110301050102070e091203070f020c03121b0c0a0b1b0d050f0d1407050705 63
    0x10318044902008882d454420350741d00c103608008a000091200a107484124001c1c2400c207211102c411100c0e13a0807480c1c00202d81c80e03401c00410000d60b40b4108624603810002441c04022500d0700c0c480b6a2800c060181c0c02070114050302c940008004951111840604070850382844591144018070001e5040400200019103d020009018982c40200b01c00003c40110a43c411407045100c103030111032003d0038850400c580034800180000200b007100d4020150380c0c090050056021041c00100c0c1ca8a1800c00390030a010001006140e070b0001d612402d84140701610141e80e1070b03103008070340740491030700101445010220405c950a900400c2091031720300e4034ac0035110700f100c0103800c0507210900c02110224200061020042e0120740180c1e88003415106070840f903620100d00d000500d86581c0b43c2c040c600b1100006400048848203558207035440000c41c005243d0380c01c41d0744000e0724500a1a0a8214254001c502400c528489030418660810b101130300c0130460801c840001c1c2260722069066030740b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 458332131 1250 458330881 458330891
    0x16030c120201141e0a050403110a0e150607050708011b020129060d0609050a0e06310c0b030103120e01210608010f0204170706050f1e0a1101 62
    0x4100445061050348503416929100442d181c15440000c1d90030114200e02400080e02141c212503644d02c00501203220b003a1905c9480c1d0f4550720700032460301100d01d4101d00804c060542088650040b00005030046c8040114140008580f00404d0b220300450b80007404910814100050645041d800f009209007400c04680d940d009142041c0e084c0da0a4401c6043c4102004100003400d407101d80c4c800100080c004c00e80b52506020604440071744801e80c0005401c00c1d80e82003402490041d84c81600da2628809010341114680382004454503280f44071082c4040d0450444521410181010954819402054500c2460b1a8000c51503aa002400704482d801000040c2c1080c0900070b41d407000080c0740503945c10b2200440c44032103184148951680852850719188041941d901c02e00542c001c0f113590036401030b266031504c14144602c0031020503088a0343c000a2043c084030b5440030480e21440e504039111551080302c40c1c0700e1031410491890225001c070700450100e010a52100320812101c08000007405 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 458333381 1250 458332131 458332139
    0x6030309130f0506060c0d1d04050a0c0f09050a0e1e0f01140f0918010e01020c01020903010b04020f0a1b021003090b06011e1409060301030318080c1305100816030c 72
    0x1498440c540000020391300883c80c0e61f00c0c1600c205600e054200d240035690744c40300a6100480e060b40c809a6102c0ca040d034841444001d250fa1003851446415032600c0c001101500d40408035800c401c1038040c129544010b6030000da48102c0240280402c9e03c6070b00215400c40ca44401104a656020300443c000013400103804111840c0400c04410701c441c0c001c00d10125611062003020b0065000c52251045540b07841c5546070303003070003807000d000f16103503400000daa200c40c0b000c101400c49103120092441036106001011002c400c0f078098840440507418440c140540c040002c21480301b036101c00075840540b40048505032689500441b4a1600c41d0404c00e0090310703108015540940b103110466107000c0d0705100182d059200e140e207099800d0b00040810710303040d0707a480400d415610981040d004600004a031610201003441c0c400e004008070b074090000416079100160035240b0540601800685a401192401244006040040c402402204c891400650f90498210b0040c4405d54450000702c7c1c0c006 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 458334631 1250 458333381 458333389
    0x403080a180e0114010e040204080c13090506011502070803180103140615090d02091f091401050f19031103010c020307020f0405070c17030a060801020702030c060306030309130f0506 80
    0x8000d0310798007040200140c4c200700300c03c0c1ca444044480c0700c0c100024100304150310349441c8001c1026021f400c016211615950080c400b103284540b0740c88046034030381000100811404210a0b0540781c024120303140c0b21940c44c0003240f80851355000b0351864000003424684190305075001680101080e00c0a20040d0b001c12803501c411141140c5040c0c1103404595180c6c560420503006103d62203005000200044a58020642c80d0b00212104140b0710652440c0461405030000048018131542c14180f10500903000310600042041c1700710f074090f110100c3c00010590740e01d0401480010b0060001d0082c039580e00b45034510502054255000e0f518201e03100103020b101108680035140c02400c52030501c0054410702c1f006110003400c0d0800c009011203680001440d24800841c1c46003000b00090b1241415411071085030815846542e07184e20401c500c2c00103132030105191a820108444454903a55aa00468194442c03030030204c1e444070082405210401890784000c0076650591010011a62100180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 458335881 1250 458334631 458334677
    0x80a0e0a03080601090807090e010b0d0c060e1503190b030d08010e09031315020601060f0806091f03030c121b2907030c0f0e0d1104110403080a 63
    0x809822840540300828011400b06401043c18075210207000d40c1e540c0014141065034000b1181c05484058950702540b09020ba910b1901048031000c0d01e802065690801d40c00f0a80704640501c00c0c2e84221012a81d2054041034000c80c2038211160380c0e00e060a002031581c0044042d0f039100f249021465543d5041c0081c003140c10858940f201415642014403a08500e100240805e070303148402c10a0744194010701101c07600401e00c41641d9030411091034001303400d14205030416420802d14403016030219a00040007600b04900342e802103159210f0554544116003000c2004000c440c22480010416501c242c040d041c65008400745000304a03451412180d101062050001c80e0a010181201003880101c9400661040601504c1200b0180c00b4543c030b205d104803006c80220350749010121140760406081059051146800798040119200260f01c0310000c02002e040032403010301180762900e0310b074408a039560900b8486502c41d036407840d0078141d0707500c00343c82c0b400040c06804010501124900784 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 458337131 1250 458335881 458335901
    0x4060e040c0b18061303020409050307030e06030f0c1606050106090914060f100203090312040311150f1e04120311070803070605040206121009140408030f1b04060906080a 75
    0x143c24515410001004441e40011044604145c10440300000590ba9403068220092040002e1900d500d220b0402804c43c9081400190045104108100550040202240e0301020070f20b0300c542c0324141e072000005013040c040c0c4003d00d06407074040042070f50f982061440e0f044800700c00c424000c0510280b4000c0c030341c0005550b00ea40104801c02d9805c2d091400a195040b04081c0b84122428415040006440e0100300c0344015022200014103200b40102c1c0388150b00c010000703440004000307081a070484013509c2416403a1b44520030109030084051084021600d0122000c1d0000d5104c940740e2040b490401c1860038100c0200c2c00d200d4200c0f80320360b0081500b0045414140207503040c10204c0d19010003901f401041240d02c000304005c0041410141c1e10594028481001c0c0d544d40941425055003c68500d440c0754415002c50a080000080c06941201c1d40007880d48103502c4c040e19440c0b1040041216440c841307d401c0b002141c003140c140e0788603040604030b031748582d2600ea03552500b041380812a171005003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 458338381 1250 458337131 458337157
    0x30a0506061027050a08012013030204050f060f0d0302031603030b040504110102100b060913060305030304060504020306010e0106081b0f070506041b0b19050904060e040c0b 76
    0x18107919104008203240040c40c10900c2101c02c0c540a0744815100342e250041004103804002d00c40350a0a03c0454050b1035040d0003049202c00d038111420000300340001c09059000700250901c0c4008202001200444d40074009001606001103400220402154150b0141c1d4134604081f2031860002001c075411034150f00594600880d003106440900107001d019410300d51214020406500d0f58072030365214034002c0d050480c0000204000906080348103c41080da541495810322081e80c0c5c0c4011110750500c00c94417200070704020900e000c054103041d0f02c0a407450002200704030a104850300905c0c0b04a10071807d47c1c240d41e0301da190856200b0020f000c0e03000004d5540c00041d018120609001012011118013079080001400044016034041c403c220341c0382c0c0040090000b000002e403440b0000100900030b0420300703410140f2003034260040c00503184408901d225080e4042d40107070200d41c40000083c0092002c15169046601c85060556046481c004480400540720a40805440480344552 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 458339631 1250 458338381 458338393
    0x30a082203140904150e18010b0102030a2001060e0a050f0403080f04020d08040f03030905040b0d121202070605091015150516050c030f0703030509090c0d0906050a0b030a05 76
    0x42c1100e401d500040040c540095556178118407448045918a0003001020840c00251508509a82400d4260079041d58503a042c896907058503a0040240ca140d20b065150410183c10745103881203045a804901e0b40320355180910205a00300b0000000c1c0c8071b48000d08040c049900c8541c03c8101c0c800d421500500020000c03400329091031409604d25030054002040004091007d486d240c0d03083c0e00981c02080c5142604000b0010180c0021a140041c541168204115410702d80840c40801d034075000102440c000d8030b02c140b6194010000403100c1090b00d00c0464440400c2d10305100288404d4a03a4604c40c0300743c445001c10030107140103801c120141507401c1d0450502c2c14580680c8010070307001100c1071181c140514079610b00e03641e10303100200380103600509035045030a0a040c14140f0700107030803c45411a86040c000310f50001c0448200348426244078401c1da550300c0c0d1000b010701a04007040c0d00541001d00c2c182c20302c1240d070480f0b0301a10710402c007000b1030302c45001059500c0300f8250008003103070018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 458340881 1250 458339631 458339657
    0x2010807050711151c1803031d030309100b09040c05060a02030909093a0f030b060d0c02191e02150403050109050c04061d0c0c030a082203 61
    0x81c0e03001e01905031107001500e1003241d00e9070020b0000c2d560680104030907440817031080400c0090401243d010300000c20b080003101d81c51620000305075080c650103411700d81c03a4003800000d0b58070201c00a903ca11990700790303912402d0100285032035200050b0038103441c41c1070020390b50345442c00d519445e00031580042c2d21046280b9090034018240c100d1907210b41540005d20140880d900c074035000303501c290400f001400c042014150566400c0141b150720305d0030711554140d03c180c2d4001d01540b4001038003483c00d022890505c8440d0442c094a600c081094100902044c07041142050b900080a9a085502175402140b602046048880030014024100050101c500c03042e40060341100011035001910b012000090354a4070881e5070b01c207500803100b582d55000788805000e0b05004001580300304907814883c542c80c0c000d1960344558042c81e210001100755020698160004c41118160314401098940321194000040c02c0340e241160030500180d01c01d000e458003c0003c0200c150265419107a1140b04440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 458342131 1250 458340881 458340887
    0x10e090705221109011b02030c040207080309120a0c06320f010e06221805030415171f081b010311131211031207060e1501051306090f0c02120702010807 67
    0x40c1d86c5c040e40c1500a00319080ca46803210f000400078140101d849550f2410300444a9140c904c4d44a80b03004828003e1010301d800315405401e2414050700f0136004034070040d0041412500781e4240c6051a60b032605034107002c0606041c0c0c5d1165209000d1300300020181d80c0d072001e007001841d80403199550b204041c1c071204c0a440103404155040c1c821121400180740403203181101451103109000d403060751000c07a0800c49901042400948686203150201100c41401e0f103c00c002d000103441d407a0f0181c41d07034001103102d4020f11810070042150700110780c14044804840c8040003820316010740046e0030040000403881c00384088501034041594072400c030328604030321204241400c00d130844480101c2803203c9407941c2c04010025225030719401599a43d82c283c038011f02101c0e06696201e1103504085402d400441034070320440d044650548072124441c416041d084002c0815401400c030341c61501041080c1ca05007540500181500741c0c0860b4103010742104129640e008104009002070740810008000300e01c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 458343381 1250 458342131 458342177
    0x12030c030b150c071e1a090a14240406020c0303210714070b01050117100311030a050304030b090c0d0b1506040b191b0b010e09070522110901 62
    0x30080c090f6440b0a4560101c1c200340c041c030031704400c007801a881013440032000c503840d007002000501ca104c0e46807881440100325151840d11070070908482e2828040e0f0543c8503405e000d6050b05208003411140110b03d00043c1c0d02e90054040c05006216080b40b820f074a050010071682c01840d003903201c80c40d490580e1122400c900c030041ca00d00820080401055807003446101810907688661140300c0190b040c02c000504d00340b0001d0000e00c4000004c0706100310b81041300c14030000d0720303080701100e130424203414003080c40d0400c1c10300020058480064000140078a41c0c5809016441140960300325000c7c8401300314111001d544080c21034401940811414040d030300007804c85041c0070b0300709402c0940e10440140240c10882c100300c0314405442014006039030004452403020002d40aca84442d510584550340c0c082c0050250801e403543c0440420084041000000000c040c010040301001c0d00f06403603114506a0344900740902c070305106400c110740c3c1c00c00d0141c81640310103070b5441d14907a003820400c02c1248 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 458344631 1250 458343381 458343397
    0x103060b091e0306101d1614130e1e0609070c0203070302090108030a110706140d2a0201270f020a0801240b0301030f02061e040312030c030b15 63
    0x1d00002e100c281a620300340700c041e21441e803d5030340342c1039207107072422250055080c00fa03524144881170040054a010140b1901007a6905241800132407214090107e0356201e00400075a40785408a4001016881c07281180e00c90422181c00356106807a0591600103040d043d920383d540140d000c40081d41551140da64249021700040854000c45d981c1d80106000c9032082c1c200c0105a0800103032804400e82242c428070810803144001d101d41031404200606645d40c0050000720711400040c481940840354101501d803440fa0a002010742101103805540380814030071820155082840c00d42c601d501864034001d9a12410039409400062980c03001c24010682400301d911503080c00340442e460400740308116516001300768612410a001038a900315082907800314401101c1080144001690b003040060740b55410780d0300c3e070f40762401d00440c41c011044a00303403903011a0005c00c0000511460950704400e500043c3c90800c00c0c02c030b200e5011000d540c2d29100c25904013500b2969000301da40d64100030040380b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 458345881 1250 458344631 458344669
    0x2160e24090c0c060609072705120c09011a07060509191101090909080a03020c0a06050703020909161d04020412121707020d05090d0501290103060b09 66
    0x1080400c00565208000e54607000c600c2004a000952004200411500224100c40100c068a42281c004240c3c0032021104162100c405601c44911114455194082c05008140900c048031f40c19585a680480c0141c4074469410b81000158034151111010200440303420340c10700d4001507482e0030010b8800030b45410804e100c0c500d01001108101818000c00601c1074407100c0d0031082c2e00700010981c50302070f04402c024510f05070044001821010890b0300300c1d00030f4140580c803841c0d140034950800d0b45491024101d54140010400140d5055008014861046807048010744803922207001030380c0c001103020081001800e40203440c00321082c038440e52400050025251684070151207001c0340c1d0089044802803499590ba0f40b549801110805146114050b80301d103a10700294001c4d40c1d1004412400c043c8000020b0303000258940a00c15402a034105009111070b5010711584810400741c03e46e00091182c0000ca1100b403903100b070150404854006041c2828004240d00700f003000c00518500100d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 458347131 1250 458345881 458345941
    0x61821021309110111060a090c030b09010b150c0607142101080d02010c0212031015020609011512030e04090203011e20030c0a210c02160e 61
    0x140d50301480314504000101e40840c11407128030b000364804410307000081c18482c881280c00e0b040b01001481c60342c04070001501080c1da09850600782810f42044d000540300c018400c040003002d20054004d1004480152002660703844040407040541c02224003040c8160046000704131620720030204d144a4040d42c400403403505c00d0313074501c11110511208240b444010300c180100003904c1c090000440c8499640024000f4008084000f91503840300c80400304240b00100100d41c0310000404d100d00541108681c4041403002d02101a5a0300401c44450380c4170341c200041d8007500f401100500f0121441c14090b00c0002000e80d40658122a80c1075405400c1962a107045c00580d41c01d00810b03a0034807182740203040403d2116080801d0300c41e0007072804004c00070201241020354801003180c1c2e1040714080d10640b1201128011030b03501c00603440d51f40414001045101d900603443c1e201034080001740d005c4505ca1700d020300350036488010f14851006500000b4001031410200d117603094102030070400b00a20 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 458348381 1250 458347131 458347133
    0x309010e0d020a06050f093d06150c1101030903020c09010e010f0807030b07120b04060f290702120f010c0306090513050a02040c0c05030c0109050106061821 69
    0x403601000d48070310801a8440030600080c40741520446400500400608441d031030202d10041d0b885c203600c0b9070145220300542000381c62200c1c400c3c446612007403c80026031115400548440948030038080d28001a410000702c3c44564041c041101e07002d030348182c46840c000c5001005400500d64400103400794020401d03245055a1402a00c0307004c3c2c07880101403101c0c0c1d410080c030350403001e030280c04c04001580016402d20108510203c0349034822050318218140d403003007070035060107040b2605103e9042400c00101041b03002d42140d103002905c04804a2051250700300d949104101e11081040b038464000704041000b6080c00c0400c0c445e510428400c40d43e10090207844c49086032400a00d0900090b5a843c05001006490241c0c0d50041c10160b80440d103666103403101e644900c00e10f00004c3c441c95035050300c440c00a01503817150801e2500803058035210a02d41c101a406080c101d10300721001d502c0d203400400e485001c0e507909500b0140341c46030340c041a0304006c02a0714501890302c0000c1c0e924504c12250f0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 458349631 1250 458348381 458348383
    0x10e0f04062417040f080405040509010504060510140f03071503020c0705011d0f12070617070c03020304170304090507030905070f35030316090803030601090b0309010e 74
    0x100824164100c0940d0295640c040c1075840d6120840208102d1a203100368501400b4040ca2900030381c101d103211724000c0e81c41c6003070b01d600d04c03c0d98402030b0020300300740802881c100103500c2244924001d08017484255a420000890701c2118081c1441c010304420442c100350a0018480143c100c014007152a00d64455084800614259200c0b00000c2d40018420201c3ca00c18410100284400e0811810443c0b003c1d4414102e2814040498003c0e00110704480c01c079a604800e1002e12102c0c030042e1401c80d61160f9006000085098000b095071001d0000300f40070318070030a00341c2cad03169815074051410301c0d00302864640c40701035818002c10180b105000224800005101d1079002e55055140025102943d10300341c1c0c00c005c050b61281054020700501040300400009052030200d00c0d90381070050219121044c80310880c0f4400c0c1e601414800801086a40e2158a4012062403400e03140e00cae410a55500c2580c0d80c91004654141c0095012032080055030f00100145801849000011030212000b507070003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 458350881 1250 458349631 458349641
    0xf0f0f0e0d081905040506011e030c090e0a0804080d0e09010501051b0304080d0f03050a20070602130e060310020403120e180c250f030c02060d05010806061201050708010302010e0f04 80
    0x10341b0319070010310041203850720212200000b0454926000c00e80c81c6161902d102080341841003447d90341d02d8281c0c88040d1507045c0070010035190701200345602c40307864000b0300d42d403850811140400300f2261301e2094401c1c64400101c50480d20b0594480349400700002031010325a40c9d65200c0700b004c0c8014000401e8202003444020012646e0390b48401c40c480c140c190040c01d44d50054807403030643c4e00c2c1c000c015090b0801d181c0b0106122007103c103141d599180a01c1c0010080c400c2484040c6007003110b810115030141c011000c64022041241141c8800031a8510319049100c0ca100080c00c00000001c11100a40180310380100080700410107401c0c05c0520038442d61044003143d00050304000000c0214004000501c10000d10b210855041d00f0040983e07030356000444840c8014085c44480c8560608640d652030456404040c030043c2401156912000695102001c0d10150301c01c103240010018840c10511410744600a80e40d038140d1180d00c3c1d40c0044d989000c6101d8980c7d0008661491140c09407502d0280d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 458352131 1250 458350881 458350883
    0x114030106050a1b0b1f0f120215030c090f150711040c090302181f080a020112020a0e040507050f270a050102031b010204090f0f0f0e0d08190504 64
    0x5007aa6500301510084c8045a18407103140c03510240300d40800400c0e07080b510243d10042664044d6801e014806038041e6202c02d0f98041c3c802814190000305000311060b498100581c8255540810030022034400105400300700da1078032030310109215210440c41c12a1340001010070203081080c0c01001d103403c0781250fa00c035990595000c40c04082400880c2080c0c07117404061a40c40c40d24148542c11a400510300301d0400340310503800c070710090220b4052000b0504040f441642c005a14140b10f541e40030061b25251941003e03400b04844c55801f10b48500c1318002c40301481d2040d0703a5400c4415005040000821010700307048200201403202d240f01d440030300020002c0c1400d8211545201003250415510700e05001586402400001820032a590b0000143e0310104c01d840c2061403107140408080380280500d034040720106090001d410140e00140d0700100348a01803103814030803c00454005825504410322220343d80c3e122a43d601f00c000e10511001e81c11000c0840004d1000c2448601101039a0341554 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 458353381 1250 458352131 458352137
    0xb0702030a02100b0d080f1c150506030411030d0f0906090b0306100903020415081207080331121b0302031b031e03190507050405150c0d08100501030e0304050d020114030106 76
    0xf03558046234001920410340f1038200c81e81882158640d90580101214500c2140d008031004000b240801a0401303800404540140c102c0b004040a010001c11940106030f56101098010402240707003403003035401e07005171b4200e1003001e481d6448100034000780480243c143c41c100b155400c004001a43c81d8096115611451501036801b941040629400c00600101e40a5071610401c419000034050009072580145111051000c0b07058010722117010082c0c1a004404140b49070f41e007001002003134000c5000e000060796070700d4024403e8040c02c613030340b0051020282c00350b4400e00141d207042190442d230074080190b20050b0b0b0300700190640011414054808c0704110808013208102d04050320a00c00140350490307507400d2055080074034000d001d5202e6806107900403407840c40340c500880251001c43d10501b400d20101e0320304c100d0555004200c14402e42d07500c2804125100c0010301584203000c1d02c0000c0c402500954a0903103400208a001400b03203030202c0c140803030710180301d9061032090b0246d8028000c1c0d407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 458354631 1250 458353381 458353387
    0x1d010614160501110417070e0a0e030c0d0206070305010518010308030703150b04150503010e0a02070c030b0a0c090b070b0c0c07080313050405010515070327060201090b0702030a02100b0d080f 84
    0xa4540400c4c441024003a443e594020380d000c121140310400300d0b58101113803030000a2b2010082d24124254420030300d903170341300c1d2240e07400151150303900080052180500d503500304a02d0340c81d8810441d03c0590f00f00200c0340d80580000502c0400c21034001980c10038941d082c000b51b90002105200c20080459105103a290001304042101e2905070300c05201c1a105441c00515540c1455008a07507010090a804a8181d010a0031001c101c01001000701844e04054606d40300d26154407044040d1141c46074810008914003c00150505880305994400764000c40444480e03980d000741041c5134002c42c0c0c09031114418039400190510080c0014060780705801d109100b010700304820300007500d40603401603021310b000301031882c50004400b091392422541485d02603105030800e8100c58909543d003065002ea950718820000c0c0840e0150b02c0608940c1c03058000758000d41e20041c0c141d031a40248410320300540c0100203020b03030b0661117a00038064982c00a18003002c00c9001c1e102c0d01c4a80d00304200c0002011400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 458355881 1250 458354631 458354639
    0x801091103011a070f08031f0f081506210f061501050405100306030b2d09031e210603010b030705010f120906090605011d0106141605011104 62
    0xa004056414036018011481c40d49069801842111031a41c1008208400708002c010842d80000c040812608204c8843d104d042c900200c14544581a000380700c1000c111400281c0403040240f80e80840308800040e040d402920959411a0f0390700426041d401503414103515110b01e852440b09034910070100040009a66400500f49045405423407080d210842e0004c3c0c0102342e0f400b0044031f054480555140c4c1901c90099015070183c212a00014401441c0104010145010410080384200b40c40084041c081c0d5180548640400580b000f4006401c20845800c0308481d82000030150192222420b00d001c0c80045204412290620700680244242060007146d00d000d01909500c03250880140075402c1c03514001800c4c0801d08e84e04503040c0500310890f039552294a500000e001a08200b040c041202f583c0361500007844240100e1807000480700c03040b90910180a20b00d4141c645a03200c411055290b40d8080d225500704c040301d54100c110080e50580094020b014948080c6120107205481d2410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 458357131 1250 458355881 458355899
    0x405060405070e0f0403050d0e0615031203010f090209220606030b012f0a02120d031104080601030803040609021008090601060212030a0c03020c030a0e0f0f09180712030801 76
    0x940d002c0c0180100724014002c4104c001007000350021380c942000c40e903c17440c0d206c41d440640800303030005040d40100f4040118500c1c484c0302c29024036008400380c82121001105421042c0028010a03005000036141800404030700d80c01803240d104014160030b54030000803910081600000f0300300c1100398440b1010860140c045c011496400401d00702540c0c1c5051841040103280e404028a41a000c9130000000301110140106000241c02034040e50401c0c4040e04a696a8001c0080500000b45080302d0031034091139190a44017074480c600e0282c000da92035a20343c00f0700e0f60805041980c1c20342c4c0e01d2000c81c006a40b40029039440c900e031920b50b080649003100c102401d0920580c07040e015500080711000001e20b0b120101ca03403101c58110001a080030200c000c030024014410852000d10001407901d000d5038201d044007010290440300b100d1601035007020b00c0922600310f2070340d603002880e02000c01e500d0001520342d00c480d81c5080302251080d941c3e5409050080c500103c3c1980481d402030700521206031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 458358381 1250 458357131 458357143
    0x70c03110405070e010f181503020309060a09050d030905030d0f05060a21020d0507090e03121f060f0c200103050a050601020a02091009060b090112060503190212060405060405 77
    0xf2541080f2189450000c0007800ca02c0614841d03404100200440000d02601c074185e60001d0b011151003442076184001001d0029030040c0c075034080920880000555000d42801083c081c9580700000c1c201d00d800e500000e0b405401900011151070105101c0c40d4a200010303c2030014024180001140034102034051220191254003c45070300c82c203039043e482807540207582c50840da41d410744034108240c4c0b03a03080503405c00103240c00c40c03040309003000160304240c1c0d070001c040d01c600d800c80e00150840b502d4009840050310965800c0002409054004005981c010061503031404d80e20305003102d01e1101951402c95000c04643c903403448800c0c034120702c10301d96454170400b60700403804d20040005090080000c1e55603560ba5a0080c0b0506c0c12034001081202029048001800e0700f0f40305200e91922900c0c0446d0b01e41100d1032503400186a00501003075125680031307a0341140c10103409880300c1442d01700a0381040201d4041660062100d1000100c1070304101701c10b07881580600060f110300c0c181480c01e142041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 458359631 1250 458358381 458358391
    0x31009020315120607050f0903120a02071a0405090a020a050c120a2003030402062203110112150b300a060e010807090216050d1101061d04110303070c03110405 70
    0x242c0013504001102d6080001c5485041c0443c031120b444c0c88031280000d24044044014650000c03010420401e100e130000b8042c2c094840f11806038405200204a10500c0c4c01a4480c441e4800000000f007074401105500400103115280340031031914480010452400090900400d8410800906000c0e4654018408490040811000d19128903a891010f50324003001d80041d2150100150403c003034a00315284e071000100040c8407010081c0e0300d0410000c0e49503800c1c48603022400390034900350303451040d100e10084813024040c0c0406003410101a5401500a01d0450100b003c06504030045500c1e98801c1c0e680c946800c00c0301c00010310b007183c411000d0710b19a40c007583c068040c407401481040c1c00861240180ca088403001038643d18900d9071024170a40040002d080e6001c0c1c1070144014503440603c40b2000c030b141d035001b44416641c5903003c072400c000500308500d140d840d0001040c0094060300c4035540c022402030482e82020282d4036107040c50241035104a600700e1501410000c1030800f401069448 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 458360881 1250 458359631 458359633
    0x40c03151a0402091c061b080609040f030e030106080106140a030309060302070f080c0309010e0a080c0f1813200d03081e0703020c061008030f03100902031512 70
    0x20801d440010080c1c80c102404644200e40218022043d0348900ca600e10500816108502c20446079061017401082c050540200303004082c0d074120a10790040e80c0311809014058a04c45e090f035a03607215401c0c10380350040124104403441c02400f00380e55007401100054003800d0000030700304d4a820110035404083d140081d01403840c2c03000800210390400d8064040720a00d007005a540c241c0c03840c0841c0035190410005103210b9011603000c0f40418000040d0405250a0700c800d240074028201300442d031101445a42c051f0b0b40280340d08000c0b4107001c1c8202e61a071001030102c4104c60048461070b10b45420484800704501c1114031000d046c46040c4c84408210219035003141c0c07074000b0b500b011801410500201905000484ac0422019040a8090a0000c900500715003107400c01800041c0a03500021f00740803c2d00c03c0a000c1400d0040b198003031011180d0803801145030540f40582180c079030304000c0070b00711151540b40c0b0000d40088140000c5200b07040b410615140800b01a04129050904120094003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 458362131 1250 458360881 458360891
    0x1050603060f041e0203070f0e0f090c010309050f0d17010915150c0b2a090d020418060e0a020a08030a02120c010e070e0609090607050a080a090803040c0315 69
    0x10b1018200072194100760041d1030100a04680a6007450308103840c42c00941510038a02c5c00a01082110b601c4010f5990413038240482c0e440d40821100c010005440d080c41c550486c0d052401c042d802603100d9601f1500c1030003a10511820070f42d55a09050540050300302083c41d20b0803c01820505810241c090a00080100b2800e66484140c0e500560203005d1500b40c20041c108161003a0702460016001c44e503c00c246401c14a00035220840a0000d0f030583d90030b0b1419603642c81d900c042c488054805891014100005806e81c503003c00000d00261000083d000302c0c04800500410380d6400780d00d0a0190510042101030614418040d1104040d8085a50b0b0703041440b007544c20581c04100c1c00c00401c15415219195802180c403540100b00800c200d118600c43d081c0300060b44003142859501c5a8005c60b0000620703a512000142c48a0701210300b074000550402c059040c0e10700030004590440041c100000320b4000315030300c080d01da600964003551204101c0d642001000030300c4401080c107283c940d1003402 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 458363381 1250 458362131 458362141
    0xc18090e0a2906180f270f06060117130609140a02030c0402091f2601090c0c0206030c160f030203090a0503011503020915060f0a09060e0f24030c0c0105060306 70
    0x90307100107441010500000000300d001a0910b01d9595410100c46c41070034180b203a60b005d15540c50050807054405801810005401580202c4162600b401114000700071a42c458040000118800c001111495641c0803203c012501c003c054025456088009040e02902401098501040802d45038400e500402200140382c0312940400180840c00800c04581c50342070006443e01c0c80e80400d180030207601d08084014440020b64698101c0300c4001c8100500c00240c0012100c6009a0001a400040030004611a8030a4600030800001a50500c1c1d21301400765554100282942c082900140d1020503125403070302c0c103e60088000c082c214000c2000f9681401d802d87d29820511000c0d01c990030000014002039a9400d810842c0b0178003c01d8030b59640c6500100410a42080f07440c4d000240c01c1050229809010306004078540c1c0000306010404980c480c200808084401c0b07025083c9000d0644542c903d81d0343c60b0242d4004c420074000d4548510900240508598000b0100c2d0320a0b40000203201c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 458364631 1250 458363381 458363419
    0x1e03060b150702090702253215040506030411010305060a05030606010c1a01060f02060f1302060702061303140d02030708030f0622020d0c18090e0a2906 67
    0xa10b00690648003242d0f183e450349016420081050031140d0311138940c0e1414001e03600700050000c2502c1580003041c8640b02d40c84600a880c0d40550141c400354100300c004085107140030f20911004100c8003540790b103066150350218421390410795044440e441c40c60300083d119070f01400343ca0360098013a10b0100c259403900000a0340c45102030070340d905000d12544504144083e11080c2d5282c941d510721070b1055940e4070900180f50390a2001d400f4010f000303100208081101d2031035268000d0992240c100440c0c0c60b25000c0080d29404098100c0c2d0001c020801f00002202c0008150003c600401645400205014209081500801042d411504100030520000d40d50009498104c0c0340e682d01d00d1080d6807550f0101796941450f5580003e0b5050141002d841d003a0960000e01254500c3e003824084891001c5082c0c6280c8016900044600d0f0445000e01440407981c2c040d014810900c0708a5009050030380f101d180100140c45074054090340301d01c24052081c004c00b04281c20507030640f0400c9811001d14414 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 458365881 1250 458364631 458364637
    0x303051b0715150b030c040e0601050304032f1b040c090605030a02130509010e0a0b0d0b06040504060225020f090609040b0703060e0a020c06010f0b0406080c041e03060b15 75
    0x700040e83e0390742029990f040701c40a120002e4040410002c0d0749040000034917801d500548105248402000001211135102d00c00f96400703564181c03103100c41b8092450342040301d040302038412010400310b0284803c20820410814074105d0700a4103c0c80048146002d0205407805138040c0024800103500c20403019030720004a90344031881c2c120051b00c40c501c0d042510381d8030010f640240d034070212080020408001c04a200d60195130031540c20804094072502b48295042c0802e006010800740d000043e14030b06140d0010f551003071140b20014500104242c001001940e118024004028012801011810300c41441491580304a520118928005c1c00144240b070b002840101442c0840d804a070340d0038083c1c0c018001500020209210701d142005012009401680c070040d00c51040500005001c040d42e401101502c201312110380c074003401c01d0401c1c0c9050328058a65407460404100c0028010b00300c0c45070140d1003503d86c030316000a928504000741620104924144518100041424042250421 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 458367131 1250 458365881 458365913
    0xe1c050d02070803090d0206070f050303010612060509011e08010509030903100e060103170f0304150b0103050f06040c0e030f0706080a180327030605091902030304120c030606030303051b07 83
    0x14590180c0706d00c5c400301d4598000d25030300803c01141e0781035050800c030300400558141c0b0304030303601c8440750340c82000d191090307400d18032803990005860b034014050180070303403000c0c820006452407400c4400c2da00c0e002030f402c44100b2140100f80341c1000c600c820300d91400740b100b00c1e85511034140c1800442994034400d9242c00040c80300804130038055501c15182048078003503440ca908155045a06ca00d400d0500c12171081c1829581c0d400325181010345440c030740c060302c1202c3c007903e50307400e14140713030740d01c4c1c809020040c0441110201404000e0751010350070b50382041a442c0501411015000c02e600c0c0c85009003403108060b103000c60481c100b81241142d07000c4004c074172444a0f09461b01a03041d124820560860001001141101081140d804000d008041d0040c0b8003c42d401d108803014501482c18209121200c1c000003035054000704020003480c0d50002142580900074000d100085035030395a0502202e16540c8203d000ca519a41048108004904d442043d01184405c452402802e555030040c5c4040c180a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 458368381 1250 458367131 458367139
    0x1032a08100f15170f070f06032a030e120f0c0105010509150907030b041b020d051e03040302030f0a020a0b010e280605040e0c04050c0f030c09010e1c050d0207080309 73
    0x9004c0d000b00d03808203e001c00e09001402501d060a40b900d4a041c10700e01e040c003408020a003400c0102c0301d2013410425040c440040300b00f00c100130881d1103000710058001c03100403404500c02d04465152149088005000c1079900d00396007a0f9a010703048402d425100164000d9109010b01e80810100c02c0c03150803070400c0c04004991a0003075540e002000e40040005840c1190400d01e01180460202610781030388142010a40844441c544901411650b521420f03480c070085001c1000258503841d08080a190400c1c0301c1e00589007002c4010b8140f107400d402c18028940140e010540d030324140a042440301c0e01600701030201c9030f440c0c40c04021028080c1d58507120194800c0c40c000c80c2d00c0510200e5070011003e048000c0043c440c8071800d04080399200159450284202c0c41c04010030040d01c0500c040f2501c43c400c48140d64115680c001c404c1005402c80100789061042841d03241c0002d03612081051a80b121080300200b00c903090b42801c0380380464444145042d940416018400c1c8000001030300c000c403604407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 458369631 1250 458368381 458368409
    0x1e071a0408040306050403180b0903071e120b01090f0b01080f040f050609030d05090105040c150903060518060f15042a0215070201060b0301032a08100f15 68
    0x803400407181d00c203a40c005000d00c0c0c900b80c188020568420028115040c00c214407815007621200f0468007481102e2180e90700d940300030b00400902c1000071030103c0400003103004803a0b0503914405c044c90151a0241145c074004110f0061201c01030a118019514264001c03c00203070b0040c400281c0b04400141070706070400700c00c20002d41000500f4039600d540b50f84c000c05964241c100004029a01d801030300400c030640341050000341d007107401481141d200b0f680001c03540d0412490301401c080c00300c1e0b0318a501c4027004040700b0080007041c01401124007680303640901ea01403544d648020b43c1440c2c400350241300081150000c0c84184c0045000700d0714a88411100003401008103803030491401c804403d041c0407140d80d00090540c45801003581040c0d03a607030420700c0c595a5100e06080382225000d01408010000510050000c00c202c60500d42094525038101c1c4944001115a03080c4101c40d64804001c5034040d0501980c1416103008064080705500814484480641048500140c071401505882c003004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 458370881 1250 458369631 458369633
    0x90e0c07140a021f030f0b151c05010f050a0b0a08060603221109010501020601030b16030b030102160203011107020d060911090f06010206010f0803031501031b02031e071a04 76
    0x207020100d00c0d43d0f0300400805880600b000c041e00d061004000400104c0d10300360f04107024000900601d56941001070140642600740000001b607900200141221002d2240103645411070318860b0318041c00503820444c039964030342000c02c40ca12002e030b04a0818000e05004600c180d40d0403d1455800c090308448081d00ea941d21301c00b030b4030304a198a0b0314054042c8006000414000003c41301e40c20750000f80d440781041e80e01c0c0d1005981c2e640007880018081000d0000045100c114101c1001410b80700745004109021800002800da0b04421001300c175041e5203038416001c41c0b4092003a104264108401d56080c42c3c4a40c000440301303001c050001e00140d45400542c03080000100c003800b4441001031284001d82400100342d1007020b0f003115000d02600c02c0c1c0c0e00108800f54003102e49022203000000452450340c1e002900c5d0740c403e4028504a05041d19a40c0125811030b002e2041c6000e05455401161204400c1c41c0c01c124510382c9180000680c90100031030004100d85610400c001045045001130984072 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 458372131 1250 458370881 458370883
    0x10e01111204080601050a0806040605070c0c0e0f180a17070206031f0b270a08071706151c0f050d0f030e060709210501020c010c090e0c0714 62
    0x8400006449000d41d515807400e80507144064400e40c3c100384200c0315640e0322241480716040b8640909500c2c0c1d84807a000900041958000507400602850294460b40495560329495607140c0c1200c845004440d041103002d00ac40007241e41e03c13803002d42615080b80c0038010301c0c6440701120480a0640c0e031a9400d00d40303071103d0b030008a41019a0160046030b8038a01400d1841c41c0706060f1140c200c03080da5001d40010300c0c0d50504142c0d1040302a94214003801075240407100c80c15900004141d070000400d00b00082c14840901482c401040804081801c000500294506252000b0180d81d202c0504c44003152890f281d0040d03409141342d4880b0440803200d030300e041510415940b49002422031040390403006860b0760100900043c64085e490600181a2481ca4192150300480c0c0f854001000010108240000302819181a00da80c0c0b081c140301c0b0f41551201426030f070054a0b4049207a446105000b8503940c008107540083c80d407221020118108618000854031035000c0103410500443e02c65014220 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 458373381 1250 458372131 458372147
    0x80a120605121608030a122304051b0303070c0605031906120b0c071109270a020f030a0b070c02130c2309030601171c0509150903030306010e01 63
    0x4005050a0342c10030044501980c0d003031030b05000620042d00101c0000c400c140002503921883c030b0b40e00c2e06582910981c0200c00204103038240d4010b40343c110182c80b00c2044402d21018010f5002d003001d040e041603440c2d200c00c400705c2c000180307901a42c0104032040c00b00d1566178220003610540d2400079981c3d10b541c095101c0714400c404103400d008d4680100004e81e45200c40300d1443d024410305207444550380e0006110380750701907400040d1200001404100c194a828161140e0000300b000b0014100c2c41e890040c46c034000306107240c07000960f01045030807081d80b8010b80d4806084500720010451016141d5030500341c0314000c2c10440c1030003518940034045558070300110621601000041000b210032102c0100410004100108400d40404016008001100c2200c0e000c0801030700410f1a070f4230380144180144002603070440c0c607005000e0440c0540407107804038102c01d170850751100d4494101008200c10030000107040010702d04100210596070b2800300540f61b2045090900c150715581b004010b03500d000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 458374631 1250 458373381 458373389
    0x1a010c0b040f0c0807030302060a1a151b07090f020a0c060b130908030a0b0f010c38010e06040501050d02010e01021f0204031109090601290307050a02060a0603080a1206 74
    0x181440c0d5004c542200002020000c41e0300070b6007254160707111102201c2c21241c80101152042620b1032a03500b0504101a0b41c90304503a54000f45481d0144c048500c02016515403500e000b140c010580401101c40240106192140001030862900007544030203042e604921800905043d2038a451054039958168203100308201140c0c00d101c05521391406040b142d01c2112941203440c6015440011820308100b80d9028540684400b0764030303005a00c0c4c20380c540d41a4801c103c080015441001481c6d4a001c00b100720410f40076040e0403d80d414520200c46a0b44020031280c01207289c20010803a63745c0d48090500b5468081c20b01034600c191210040f401c0204070014402d1011001c02c1c144080c0c142d07a4010012640214208802c402038101001442002911f0318546540300200500000d040c0d044c0c0a1040241364140f55181c00740c10081e02c241e90402ca840101143c0081044228140c06000e225406102048100180c90641d90350340c0c2e42d40601802203041100171030000c00e080187e588081e003d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 458375881 1250 458374631 458374643
    0xd03061d18010207080304110108071106010b090a0302060403060e120c0312060105071a16030203100603020901050d0f05040b06030a0f150b041119020d120f0b1e041a010c0b040f 78
    0x2d103003a05148e803044900603081400502c0c52400a4001c62042c81d590048181d118003400b031903460000003040c980c010442407a802480210000010b1751208024001584102000304090040c13540040c00c1c40700059411290640400c06841d001d040841180c07461222000c03403600644503040120ba0324007400600800341c02c1c0348035403d1a03d55910b10864070600c098008040715401000d8114103074003041e20000e01d0030b84a414181320060180d0054184110185800c42c02c28408902c050f05403a40705442c9240595948244014000010101680200700fa40200544442031760780020b40c4d580740300058030203228501c40c04150314907500920307080c8100406c140300c01164207180b21802da00031070f004203402403d820100180c0f4008070341501e206c2015100c28080c0c20b0039a0f0000050495400c151081c1a1f89015a820342d41d074500d900c003840414140000810700306001400304039185a40c02c0808183c00d640700303e640e41c6c0c3c0720030b80741401c55001c03559020588135480d045002100c940402014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 458377131 1250 458375881 458375887
    0xb10021c120f0b0307080d0c33021305060702030307061a030d120c03060f060f120e0c0f090c0a050717210a05010e01061d03030c0d03061d1801020708 66
    0x20318620703604080c0f0358107012030039681c0c9241e640c440642d65000f45007060022407103c6039240701240c1804122218842410705000074501d400e1200181d00e811141410344296000c076409042407400b00c0c2e8034001d484160740e6186844211340000c0d959025681c0014091521240910455034110b0a8204014030280856042c0110300c071f0b01601500702543e6000309945416189840341c1d12901480007180e030000f903101e10550902000303c41c0e05c49117070b01403414442c64140c04180c18080307214001003001d0303c8018000d48401c800c10000840b90b00807000d4480c40c03416041c425250400012110990b500b0308200b65520300e00d00d010415044003c40c6452804008109611042c2c0b408801d04c54655000c4d075045c1c95669039a1089040b1b0318280540680d81c03580d40010b0100901541d80000d003180c16904004000d000302000a02e150702c080306140c3c80780c000a1844a61a81600a80002d4900c010720381c1070804801c050604145001040400b6800034503651544207030081d03040754906908100b0440e9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 458378381 1250 458377131 458377151
    0x40b040c050c0105060a140111010b030706111005010803030a02090f100206011a030112060207150504030906021011090f0d050703060203040210020105060108060f01091806090b10021c12 82
    0x250085100b5030b0a030350030b02000072580e14208000c081a01c00e4990b00c02c680208a00045400080201c4040c0403503507505c2d01c2c1001540c3c00c10480009001e565140384292042c40f401c1c1e030400c00c80003141200b5034100801400103450100c00e80e54010a001c02c0161a03184100000b10f0440101c8911707500008502900e1081d182d001c90118117a820540c1424100036503c407103161180f00921454503a840341849030f03000906550004c3c68480d001d09601d1192039900c01c0202c04984040e07608030045031207010100141c2c1e806100006018000003810410304181c000002960b1041c3d025642c401d43c00207840410139650400c003141c2c00b0b82c0140481d0401130b140c4c40c04000940c800c3d00e081e813140d1000c0107030216107441401820311801c81a911f00740d40303407980401d1040c0c407800064620306010400102040105070540303503020428a01e03d0200f000d6140c0205481228032481445024008011040030707000d0300091641e895030f003d584030070445c4c40141c5003202d9283d62a189000602e050540f486c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 458379631 1250 458378381 458378387
    0x6081603030e1503011d01080d0c0611071e060c03140f07180f06140a120b06041706160e03031209190303090c05101d040f0c090603060b03060915040b040c 68
    0x106c042004030420010713170f42c071060345940d0344400f440d02e500014002c035000000207240d07401c0300403841d5900030400d040c000b0726540c1e2048456501d020a0028a100386001c0a10030b580c042c2c00703514507103814100440320041c0814080540010502849525002d01056155110380794034400300f03120202c491000c2d91a05e00018085900d4070070704000442614500f0036842c1b8034030841fa01c2403e203844140e03d07032a0917032408e4040d28508014641c0131509100015a101e4001c4012580d403000d500603102d5460540b0f40f0880b06c20340302c08400b00304a400e40f18040c55031000030440c1c4c02041c0080c03c0b14010380d10101040d1030646640580003418110811100425415402034150188a02c02c2070700c034280c854060080d1a00307404012130025040d0592124520401d200384070100002600c00f040100044071213605482094282a000030740200d0100a0117502d8403a54014065131070803945035042c003000242005401038000e81032410310591400e07807592590300505c1074607400b60041c0042440c002020b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 458380881 1250 458379631 458379659
    0x9160303092904050d020a03060f021b010506030c0108130f1a09010e100914070308030402032e0c17010b0a090501210504050307140303040606081603030e150301 71
    0x40d54041e12541541c10a110240007042010010b01299418107203001c0c100010851420010380c0c101c500100017101203162801101c1441600c5000566184111200c001c005080e8803d000440d924100c140003c90340c000c9a14500c3c9202440d00c1141b03512019403083c00024070000c024611107501510f241004001400c02c0456400044581e1069544940c841d098801c1c4c2c1c00b0341c48094005148c80c1501c076142d42d204a0001d03014124807030318000f45020540c40e048190b0001e41743c2a00c0402000118601000820521a00c101d050000b403d132000c1e607910b03400300d5405410101519400c030300c0c454502c01c0d10030008c00050f0360b001074025603480300e00c071065030710000c80000001e0b0140804201c0754001e0403003180310000014581c1d8108849181030005001c050402ca5043c0030400c444000305141010401400300030b40050342d507a003068035090f030031a603d9500142442d0083c059074081052161800030480f034040c2021021310b9545070011340c1a030a10001d04803404800b20000c00c4006002d924 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 458382131 1250 458380881 458380889
    0x30f08130e01060c140f060403050a020f0312040606120b070c151e0617121317070501080f0c070b0c0d0f0203010302030c03030403150b03100c020a031211040902030916030309 77
    0x1030f04a05c00e4030560896200d10010355595040d038050000300d0002032062004203802d0040c0e20607144250018030026066074080320b0301804a1841c24240700c00d0200c0c41c882c171401009542001942c0801c103035699864420010301d11410b000c0c0c10282c2a0611041160b4a8418009074200b008000300400302d06084da00c1c8541000c1c011407030140d01107100943d001c0082450310700d02c0c0003405c030f420b00f041004081da8403541900c90000030741c01001a442d2440b20110455011040180030420308050004069410013441c1001821024082c0000b4440a40845042030b0b00460004d1207a0703160f0105240d180305241840c10241e150050a800075141c9501a6050300c2c8200c00f5075400c2d41000082681e02c0c02140009400205603080500040a017030388101000030000d030a9407000e000c45e404080481d000c09880350056040112580f040542c00b030700305680c00907003190070041000454000d2920b40554000e51122560007c00324981003000c201d401c25003d6180c00e00f0b924642c880c035005080c1a41441 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 458383381 1250 458382131 458382143
    0x30a0515060a020712060b0307181a0901050d17130f0803040b0909100b0a03060303020c010801210203070f120c0e042d0606060806030f07030f08130e01060c 69
    0xa510003240c0350020440302180c00581c0245021810300c0180c14941a51400440e800da50b68001304203551800d0180340c0040040301a0810166405403280c815600e1001809403000e9102011210301c0d500c0c10641411340b1415078405040300803a02c0c1031a41f102101010100400c00410b041d210700e254074208606840750800541c0850b0ba550508a65a0065000f04002c0303803002d000c42809424000a40c0381c2c80600d03000450b048035070396902c00c641031740503a0f05040040e455240034002d1640401034480e844501b860003254640c500400301c40d0f24482030350070400550098041c0025540c00b00841000b4242c00070006403099500c1e0521811070030303c0d6408907000607100b80c00286c0c6045403000944680d810564199204006110b1540c1d01d003e21030036079500302c44200301d0700081021071140e01e01810081d02c80f84030b5400e1600030107241644280c03003c440d5a020340c078184005604203280e03000313995102c3c1426807a00b00a18071002044c05542000390540070070710002455550042c02c848110703001341 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 458384631 1250 458383381 458383411
    0x130c0f0815040b130f08040602010f0b0f090a020c0f0f010e2107080702010306090c0e19050d080a0507120c02040b150a0c060b121b030708120a03060b030a05 69
    0x8010115101c9040b01c000c0c21a200e200c00040c0003079102030168041e1445060704c400d111400755218034698010b50002c2d00103030754980c90b20040441c644201c00404800300da0410083c00708400003602785000902a000a0b43c01250404018408201140d0b40c003c140702994070360701c0c8a0020500074044608100f507903105040c00e8010b80551820740c07012400380220301c58508121901c40001076448010101d0415560b20000115401944200289241290350f05c40042c424101080b80407400c00142d4a0b407540410010030059640d8901540d810354070101403510390980c014192158002c0704c4010700350300304028218800c154030043c0e1040480c4202c4041113080c001d132080c00a10300c1c07403c4011807031400c2009100e80382c60003201c803100440d1064102103502200640400d03880f07812039480c0852035105054401003000c1d032030011001c021040e40100282807410506039907454000f1903150001600140200540c0c1c0b00390460000340c0b0003230f90115940d0034120000c0780107020803103070041503910729 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 458385881 1250 458384631 458384653
    0x1b0209071409152a070614040e01060c051c17060f03240108070b0d090c1e141008060d0f02090f06042004180f18140102120708130c0f08 60
    0x540c0600004e0345880006001d09130410005403001080860418048501440005494407030320306940d0183c562640d03012681d444505d0f140e4980985400324032480303004080d9103078899601542c0020265902d40d22002161034a8000c43c0c0c250300c00300d00c100d030940100c881035015a50b04240c40c400400c64481c001c80280c1e65000e000d0b803100c0146c01400d851b210100064000050a60001c0241c2c500861450038241e9695034034a800b5018401202000315145008100b02030410030213245101059406c0e15a107030803003100070020500100f4051242c0801c0c3d0340c2c4018046894414406103901402503a042c0c04d006520240d407040423105c00e4421814256800660f0808001c0a00c004040c1c400b003a040070304100000440746400c202d411085a44c4500c40d000441c10b5004612041d1074040103552000e070113003080b000450340c1c246542c0f080ea004018550702c2c42c124150a5a00445919041c0940e8071440480544080c4074140a484c3c2100c0307513070115594509207903000440740c03444122500341801e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 458387131 1250 458385881 458385937
    0x603081b070e1603022209060503010209090414251a0c0d03052211090f09060105060a0507140c330901030905070e0105011b020907140915 61
    0x85015003402d40b115500865a850300e0700c542c1c00401451420094108403141d8003d03003034500901410003055040010810086003075103d9440035040030340c000e40c90701c4010004180401000340004040011016003c0c080400901900801c070610181075021440424034003440b150550050241d540c0c184c45c084a01c0140c01021200900808000307400000c2c51303031030290001c6c10028445030754954200807841074200c1035605103000c14400d151013181c45c50340809001031524010b20b10302d9800d600600788041240300140c410b04540c003c84840e5511080004200c2e041c1c0500c440040a6100a030402202083c001c201601d140c0c206407032806013800e01c1000101141666403c044203009044041007030740c00010002c000c0d004040c10b02240809003a0744072450b18416600084215092030010301280da40041409040c072841e1204085001c2a41c00288403010090200818004014124281c4c1042041500c4204170024142c9458048819032001c1c47d0b84894000d041c00c00d0001100704003110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 458388381 1250 458387131 458387143
    0x5060d0203151b0d0213050301090f06050a150b030a0b040b18041b0e010f0803210612010f090212071d07120606030603050d0e1c0c08010603081b 64
    0x1800500416040e401090340c0c188602e00500042401c41d80000036010010004005161300018200c005903201042c80c8044200c0c0ba02e41c000c03501c60303410580100045651415840c24241d0040c00c00a035a0311400307640801020900c1d40c0d406618a0b010002980c514440c018600c14a02c1d07500501c070341a120700812003118005174100c1d40c00035800024011962980c548640e1261082d0b688100c901728501c0c0504445000c1e9000b035844d415154010b00c05408080c410302c0060007224011401c05076200525041d2050321407001c503801d14000e00182d00c41c0d5414080d0010304e1802c1c802040030841d000c5070103019045c00203099008140d00e410010901c80c0003e90602100c04140141c1c112500e202c0c101d0640e80c8000d4511400c0100b0903c2e91180c0207001d1041c00d004041c2600d00060840c51882c015007458215801c2d00c041c041c2e503101080d03071500c40113100500d00f041038581030308510712458010b07003211040d00415440d40c82e000b404000c01c0721140040c94803080c0b009454205d001d40110090f5108 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 458389631 1250 458388381 458388383
    0xc0305060f060d0207020411030a02030402010908030c15072309190323030c1b01140325030f060e0708011703161e050706080a0e0a020d1b0b0d05060d 66
    0x2c404000114280c6610b40c05070001c54070090020a110309035400340d4501e030300151414078038a940001800115038104a145006091100145080000040c0015152900304001905058205000130000e034404d0303a202c10900085640010780d0711280b11401708035003144140c04e004c1d40c0050390741c1c06050880c08446089951114440100c02c255101000c0341000d80d003041c004500c01070040c4000000e007440014a9020003088000710704071280c000400400c4442030480c91004200b0601c08518808406803005018180c000140c42c42000170807002000c2a002107040341c1c1c64284007080b10101c140e070480c0074401c9030361640e1050340c8901c81d004000c0e65184102d43e03d42d1042040c10301ca401c945a071048118014101d200c0c00415604004001042d818011105900071132010310055801c845100e81101c1c2d100e2017005440304d03034103d09a481c445100040d1040d8450f071410000c02201e511501411822300d031130508120f80e0b401900071140c1003415035608a605101c0055020705060fa2503000302 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 458390881 1250 458389631 458389639
    0x60e0a0c09200f07030c08210a0b030307140f010905060a06171009170409020c010c180501140415050c1b060406030b151603020705030106240915030c0305060f 70
    0x90f403006441e607103c1c0c1c48944120b0a0215100628002c41c641c14050a070041081c85c4050311117411400c03103148148002e04400f5124a46401c0407151389000050f64001070344078012a91000751340110a00d016104030200102d9820450350a0401101044060040071099014450540c450400450340b89103002486000d42c0020600d800c0303c2c0d160340107407244034002c240b18a01424800d242d110146d010303810501d021030700042d081800e40402d2150704002c400d240750841c0a41e5090100382803ca801e8480c0a0401103007481680350259100b0071240240f9407503070500d07850524400c010340140c00800710b110a82c080d8a04004110f03100c0641c00450080042c417052905080040603001003c5048103280c0080c0514a40c02c0f480848400400d10b0203e0005003044021061400900d800d07500e8001502a90402c0ba040280803641040c80e240100d48400c0c510700f8005403c012200b051460307102415007680000060140d5402d50320003131000d40b041da810b01640d960807041c4004950390002c0c813908 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 458392131 1250 458390881 458390887
    0x18010b090408030f0c040306020d05070815060a050903030f03010e010816061e0302090d0c05130204050f0f010c05010603291302061c060e0f0f0f040b04060e0a0c0920 73
    0xb081c03610f4130034603500c8116191081d09298807507e6441c1241c001d4000c90345102c1c2d454040c4000d69410a0178a0350011100e9035190380f003800040410581d0280304030500c107220340410f00400a0307409005889a410007035800d152a1340e0741d00721a2009030000e01c520145400f40c0500880c20303100000c01030003550b110741c90b11b02c0309603000b80121098005080c8440105a402e02006540765a84d082d214905805520075015030380c20001000180c2c0000c000b000c240c544100002c0180352203c19249510900440d00c01801c4003102006031854440c401009050b9480d000e000303c1041507440c14410041041244150b42410501c0c080f10003810958a144503125080c2c0040010310b4400018054060844082000240807003803020545041d5048811801800e5003003000c140124030358940d005d40c400b01c1c1141141800c2484140d160405030010305000b81c0c4078006001d0107040e42015078140381c400d00311100b0044e1410071684d0300b0b4681c05070f101c0da5800d0540ba40741c1c40340c0c00c0851900411a00e81c030b81703207 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 458393381 1250 458392131 458392141
    0xd0807020f07060e0105040503030d050105030c040905100b0402090d06050a050708280e010e010207110904030f050702040b130902011106060f1e0a030807110a030f1209050918010b09040803 83
    0x40340c2000420f84c60402c0420000841e03036880c00c2c40984135501e29074601292a504000c1014240100000658019854014a0008240002910028040d08200c002441c0c0c2105021401038407400c007400b5085002151003000b041142e5001d24400d08281c402081030ba10368a8003200c07080002e41c2d00a40f03458881c1c02415803408240321000c030301d0040300e80014040302040c411609640001c1543d6132965400b281040500264920b0040c4260b011204032800707181c00c1d94081c100300c0d0a88035402c20014046044000c54a03030380d00441201c1401024001d8059400ca02c0c100600903005040380051800350780001c59100000e5064080c9078001c2800b804142c902d0240100140202241013409045014200040d00c400c64500c0140d8080c80740c203590b400300d90400f4840d6442e031040503401041d00e604200049008110314900c400c0c1c2c03008468100182c01c3d9412240c40800c1e8104681c0403000310140901002ca94215000a481c02030090151004200800c425041300302c8002d0021042040051 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 458394631 1250 458393381 458393387
    0x194d120c1c05162913020f0603010e010e040609020307033212070521120c0c06010605090f0a090501090f0204050607061d0303090d140c0a1502040504020c0d0807020f0706 75
    0x161551038144c9000c0c4402c101e030f6204a140c4441038440d50b00303440700c02e0741110a50400c00d06600c03005005495480c6994505804409207200510490065001032800708080000301d8020042054000b003c584c10140c69080a0401c18914a111410746441d1210b5003880c10003280c1d00c090050920b1f014120507211b881d50361a050740512030407182c902a031540b6900201032000b042d541e0b03604c040c5c0229110700e0030610402c040f02020781101e100e00c0040c811051000790004046041d00c00520b04180c6031b00050001c2042800c050b0903060344281284800300785500c05a201d2030484098800a02c41e4050b00243c4504a101d280a1a03400003810040c80c8045941508400d4401301000d600902042038038000360b0641d00103544240ca0354000b43e1a81c1180c40d841001504809488000701d450035190f0440295a00b22003a0020305103500c2840d04400c0f556198180c40c01020041c00030341d41c070040032151a80320600c500900c0b000c20054008101541e100192580060301203a005180484c1860010303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 458395881 1250 458394631 458394653
    0x170f060c250b04120c05190c031a040620041e030b040525080606040507020f0d050c1207081b03194d120c1c0516 50
    0x4408021410640d0000600c8000003051203010b8a442c200e03c2c1414036100c00c0081611011004000d007400c079010111300d011a0340c0140c400d030700980041080320b034a80000001301d507902c041c20140b4000300182c1d446030502049440346102c2e840803c102d642c0e04040e03402001001c43c10010030901032000740302c2c9120102003d04030003612900c5281031966540c41c00c240a20407541203480c0e0708440020400c0b0308040600e007840d846e0980c03021110358200414240d0b0342800905092242e501c9601207a100340c028001765460f400349805688285120060290940d440201c02c29028405d08044110b0030030084183d501080e0f00c0416035217800310381c0e6600306441503000641c81e100d010030051140310b070078100304486030040c1c1d07a1190300465440001c5480c2a640c4800c0000300d400030224004c9007004454400c0a00c41200202c803401d00c00358030314051400c3c04003145604502030010310340e214104000750302d02540110007115002020740c00c000b210503004008400c05500000c4081c1d1000a81d82052 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 458397131 1250 458395881 458395897
    0x1602011b081801050c0d0e010204050904030e0109170d021b0105042903010914060904030e1314091c0f02120706150b09010201060806040206180d080d06170f060c 71
    0x2800b89000c00400c0b06400c4540644e440c1502100000b504c0c444a1114043d00c0a40f50743d005c000c6007007034a0b00f80450074415008100400300089000035030010380c00380c8a0b0201404881c0d40c1400030f003c03a5444940e403045069100405842410790302481518480302c60080b494042e51881e041501e4660716a8140105299020341c03940714070442c03c0c0400e1250b018600130101ca60000c54480b501c10440c0030340c42c2001d0700c800e020b80e501008200c003003500b0211003241e80c0e07029078009604d40e101d002e1140086c10001281880400c2c10f20610025400c00510090000355011204031250f0a000054841d84200401c40340540c0101e2403a12002d140000a002d0351800385001142c99100200e9602d9081410741200b02404808554003004d940d091141102401d000700045c8080e080c150002502c0e400340803512841c068100c41038132420345602c29080c4180f40e1003c91942c42c0c403030b6440c01001602a902400c60710500c0301d00c10404d41c5800251103c070320003041001d40450f4842000104c032550240003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 458398381 1250 458397131 458397151
    0x1207050f1b0a06050306180c120c0318060415021305030109050f070f1a092101020a0e060307050304120513060c2009010e04030c0b040b1602011b08 65
    0x8214521805005508501c8054000003505070002410810046103a030441420040d0500030024180c80c0d90415100c250420700407540c0e1982c0303001c1c24226a102d00c104110395001c80b602030081e40d1091001960158a040d4400c02d07840c2201c807c0259581403c460107480680340076840344503540f20b03600a140000700c070200f201400d52980c000c242540e58051046a09038004805640031807802c0c08188040c010000958614614102800501031039070b106010111000140400c1c0f80e0f504c03810310071140442d021004200c0c956003249036000350010b0741c5c01804607034008042d24491502004807480340c211912000e00310784994880c400d40303002071883c2500344442080100441c0b8588018100202030a80c0d60050001241ca00314030450009008155803010003101c41d841c0d84c2d51107441c0c505607030011910b0071241e6181c2c14112410403c80b6030241c00d655440c0184014007041c091f12038801c0d50301a1a41440c1d4034070400403400c075444003481400c0608510602850988505601508032615031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 458399631 1250 458398381 458398393
    0x5030103031d15191e050c101e05150105121005090109020d0605060405030d180f030b071d061617121b07020f040f02070c0620030c120705 61
    0x404103004120000b0043d1500f0f00c040766803d14103d0f48540f600501c003261902c11080241d15030042620010122400184100031841701e20a207010814850803244000060100034140c000400d200c000b0200100480c50811000400110f00c0503031448080b02e040c0d40301d40c540880071408107200c1002902841501c072200300002442d0717503007a110902a0044141c0140c0c0c401c1c0d2590070b001124003960181c2d001c0d040a00041000f0303500403441d0710503494281410b8550507801030b07641c1a51580364004501d1a00c000c40c010042c45480d0a25500c03d04503038940101030040c000304a000d6450100881d40d210908008140c25040c1d651094880c50384507040c5035600c0c80d0040e50b200200e41000d40a03488104034001000684130903001002041c1c203116010a141114907001304076052188241240102d485000315a170640030b580c1101c8042d03030000320b802ca24a0b1a00c000400714030040094040c5505503203400207009401008850100403040d00400c941c6103055004019030b004005c0640c0d0600030301c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 458400881 1250 458399631 458399687
    0x20c0d20070b12130b04030305060a1e03031419020705040c0534020607060f061a043c03030905061602120f03040603050601350a150b0702090f070503010303 69
    0x200c44017038050f601c40e48010606160820510000103403d80c0064403801003042402c455002c0c034001e84007601e8041c50450440c120002c1110018400e4009d0600044a01c0400854035580480c5e5482621000c803420f000d214982c11003100d89010785661440c2d04245a05010b1021a00b00d040c0c5164030110700d20086c412409070006540c0d07410004050340d66940712010032001d065030740306034005440308403a40e00c104007480c0804110b6002d24080c819400720780c8041d580812074541d13119020300e121a1089030324a4141e180c2c1c0a88051648401c60100b585003030045014a40341d000e66030710a401e403680003281499074003001007400707801c81002d000340103030321041e14204410710007000601960789003c5100d00381003000400c0e0101d00c0302c0d11640e154001c0c034946010b07011031052000b24941e4890340c050640700e581000c00209064404010b80c400047d0700001d0842480d4043c0c04880d000b200e032500d660b942d181d1130549a207070844901c0e0000b0420001440040d020381c10419030900070361940082c05681c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 458402131 1250 458400881 458400893
    0xc0203010b100e030105010b04030b070503060a0312021f05090a08180405040c03050c03151317030709090e07030506071b06020319180203070506070303020c0d20070b1213 75
    0x1010041e0000420f100e001c070007941000d000d02401803000351003046c039280c950746819070022009081da50410000002092a540d507a04c2000d000d1034200b8221450340e911904060340d600c400d0340c41c1852424005640340400081c1e0b11030203220310f10303030f1020b8244541c542d85e4a0300550b000c0b0420308110200ca055650071038a503031080718891403180c000c1241d01030a50034210700c2c01e4100a4058840c0e03210301d83c41c00720301d400a00c10b035420050088a03520f07400b60354500000401c7c0d141c8212002d020000c8104000070350b00002403021210081e204010260303152a400380c4031000c4d40806041c0d544980e020505192040002c89222882c2c0c0841c0103480034139650304416607100313a550745055100f0345401200134689100e032240c4054151000b401d1902c0950209858131624450180318020210b101010306010340c045070056a0302409407039802001e01c80140a00e402107182e40170bd0340304821120031000d0002215015588035106007801d00394009102c51007420002c00f69400301ca600301c502000504 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 458403381 1250 458402131 458402149
    0x300106120b0907060e0f041d01020406180e0f06060d1104060e120709180209090a11010c051c0903081303110301110301120201021618050a0218010c0203010b 69
    0x2120340c80900300452541840d04a030203010b0000456500500002c0014075004111080c50a4095404101d5100800b0000c1d0040c44410020204c60004800200302c174141075001703005481740fa84800c04192812031507a04159424040e072261008428082500142c40300751031540700b400240b07000c3c6454090400c2d8400e54a034005036a00010700407809001040d045032060764000000c1e1100c203d0101c809031200c3e520380040c411010510b954940c045c414141040f40146825000740a00790a41040d0211036600d20030700784150b80f480c001055590709503100d41001c2a0090b00b00005024041c441780b040c01448907220341d041c3c24031401410001c0060040720117040041c031100c40da03a00c00c9196080000380d4031214544c042c0709915010281c0e80305403070300c425203041d540114200b42d006001880141d241ca09582004004404141e000040360790103071182d13901500c0d110b5024071840e154540c1c154141e0250342c0b40e48902000788002c520095118813880c000d0075000500100340008154040348010b5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 458404631 1250 458403381 458403389
    0x7020a0f08010c090b03070e0d11040e030d0b09040210080705042706050f10201509010b010c0b0601052d25050304050d1401050106050315010c02300106 67
    0x80d46820703803c2e5000d500300e6800002020362081d814514500710b00003c18001454880b00e205101501c1a801480101e580c2c2240c1d03031401401c10003403020b102c41600c0c0d89801c900b800c3e095880c101b018107001428801031050045074050a080c00019605209650045005000004001091000180309000305e03586c820050005210414540d13102c0081400f6155075402c00740c001c2e480803800c81038986512040c042c1086503407621040c40d40c44445540080d422041d4100b059224162038100114185050035024070441402002410714110055684005102014040704a1007002035241d500500040c510082415100a1020380303070500012010881d001c03c08034180007042c44019800c83c0c6400c0003080552480501c050306465076025620300c00ea01815000300d400400c0c2c0420800340d150886052950b0074000d000968449030014466007007158a43c440021020308c050144d4028079221144a4002d014410700025400c5001c031303000c098005500030408000c8052049010070311071103000e8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 458405881 1250 458404631 458404633
    0x1803070b091507050a0f02011d0c0907030b03070b030a09020a0621090b010909020a0e09030304030e06070c0b2d0a02010e030f1815160210050a020a060207020a0f08 72
    0x9401e02074801d9140000b0303128400582500c507020f00c040e450708502a80c00700001440c00c22616034407800c0803800740070880c03045802c0e40d40401c0c03103c0c1184008248002c220609503145240ca994580c011000e540700d60501c0354058002c0034051103c580e00c0401540d02100d140d40c0030520320b01c107038045440820640e00190001e905014402448030610b001055441c01154050044500c82d0f114540306003418492600d0b06541d0b51240c0085441300743c68bd80c0108169000114076244c00240551242d004130f4080b00080d16030031440f00a803504000360b0f90300c1d6400140c0f00d5441d0b41407443c0c944032139000c40006015541060038a50490381403014032030300403aa40c4400e0b40c0b603010201b0003909503020b0810300c0490390001d002d00e602005403a8161405000072000c0003480542000c0400c0314403100150400201a000404264184050108500291094032811050107481c07004a40b070307004e880700ca40700513048550342034081110340d00034104e0507000030310200e40310303a640c0c80030316040c039441c2d00c070f42c200d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 458407131 1250 458405881 458405903
    0x150b0d1a06070c1a0c0c120c0d06150b040e040224180f09010e04081c0e0a021003020405032a0a030b071b0201120e340f050603010b03180307 62
    0x120f0300200c08001811000e0074401e070a00d440055041c1e2151b5030380c0c200030f01401e102286034021110401540300c003500007814000c6010602d040c9180a05400e0118003810756009800045443c8810101c5084070303801007081500e526560300700800c402601012803a84206600d00c20305c0c1e00700030401801107640490048045c903585500744210100f442c000948107105003001000720000c058809030f407041d4090702583e07503603d10b41d010610b00ea80705110821010301d022034801d9502c2c00020f800811380e0080300c035003c2c03828441000f14264420742c0a0160140c01222030f116034030302110103882d6a8429a0a0a2501e4603a440800c00414065000707488401b8940c0902403229001001c0e02240c200180e015011404280c0010740b4201003140704200e0340d0303551080380d00b199809000c010850b07204083c1d4100c00090100411500040c404d0201c0c50a03086208005200300f0901107150442d07001030071060a6070700e44903202029410042254040c40740b2441c035541034590a00c01004568403aa0f09455 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 458408381 1250 458407131 458407139
    0xf0906050112080403020d0302120d0e0c04091e03050915030f010f050d080d090b01031b0e01080a23240105060c100f060509040605010603150b0d1a06070c 68
    0x8291181030707000a00745000d4000b00c0c008660721408440c00c0d60340555007805444620f2a04918001000b407504803e01c101043d68032142c5450b40150004d071140c03904030742070691000100003c4480143d070051451082e01d03008681c10001440120021b4020300f019030134100841c01241e648815524002a03a0400000300080c500b0407800f00c0d40909103500c80b00801a0400000c80c3d1940c50840e0060205140441d40c120000c000d030300203c10499109461200c1c2d960f40b4a400300d50102e04850520401d008010040760544840e010b0394101d0341008001c0c804046c050315002ca07c000031f4504030034a0080030314000b64280b030402c1220709000700880183c5118004100b040f02500c4107801c001e10400d003c010b03491004c880068500218101d00307200083d03401c040207814000b84160751150ba0000700344c008010902040d507218078100c80d000c2d2001e01042e140b44009841822450203166401e410501c00f13030b4001009544000341c12848201184e40d01a8104006441e0350400103084401c0d040106041c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 458409631 1250 458408381 458408393
    0x2f0102040801270804060309020a1d040510090203060c07050111040e0a110c1e1903110c0a05010c06090c0b07060c020705030607091a070b040804081203130b15040f09 73
    0x1407285100d80c02c002c111003c0b650383d601c0013449284a410105625142d440081d5a5840d5000009040e03101c901101d05a0988180c08941000c0b10306030f40c0e6000d03452140758444024060b0410441c0c0c000c01910f410395800c410070b801b0b0f402c100019201c540d6a00e4403c4401c1042d10b00030006000c0c021043e205c582360002c5c0d0501074034490602c1c0d20308501c0074010015065400110325060510780c1400c41400950304008519003a001c000350302070a48010b100d0000c1c927070802081840021818199501c8031501c80c1444032142c3d07140300c1d03a40003c01e0441540d01142c0e842e40302c8156188146591070b0040c0c4e407007100141c150840c44054030b03116078031150364210340c1d010004e0000512064000e0203003840e000e03030f018258410038803c081008070342c003003080e1203005800201d405080d071100c280034041c1880e08019616820502500f1002d1196a9036140f5903940c2e902584d10540584960303441c0450b10760359100d00d900d4068128013a4540468105281d03654a0080f240e603030411000002d1807040c142028 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 458410881 1250 458409631 458409671
    0x806150c03090301061e051e0103021b0118031416031407060c26010513090c12080c0d03140601110a1a0712051608090a0605100302010801090c2f0102040801 69
    0x14600c100901c05007900c231098000100b00503030809003001a02c803000c4504d02d2282045074000f5250f01c0d4608003505011030010540c20300c0080c0659281441d04c400401c009440740b2030b10500c7e064299007039a00c100041d115041e000e9403804800c0d0500e0602d04c11380c0c1d516051b50300b030307920240c007161400c0c1004014050058007040c2d100c065007200080765152402065129468041140c3c040340c880500c042481082c4800400070541e0200c0c0b10b082110a06100c10710f60044034101081c0d026541d83d500d0218807070b0041200c40c512024899080b921404015101d50502007600c503c1e80c0a1034000401180014001400800d080000348146107003500b002406403160424080400345842c05020b03c0017070301c040d942410101e50501281685400d11280e151629900004240908260411800700c140245440c21a8800c2c0c1304c02e20240d0300c5101103000c0c1c2d25080030304000252510101c1c4d2413414034003016070207002c051f46600b00014070001610300fa60b1164211170600d03916000b000000800b50101 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 458412131 1250 458410881 458410889
    0xc0e06010f170c0901020307080c0307121706010c0c0302060c01140711071703040b0d0911270604060803130311100801030b06060412060e0105070806150c03090301061e 74
    0xd0b4000402240085403a009410301960700742c04a03a140e16640204115001030f504510060f40b02c4070344203a0150b407940500d0048902a0394403500078213050280c030036030104c0a840c041c0e049042e940c100044513601e680c04002d503070800701d40b0400005a00c0703040c0100340f9512980008103003105c05648440c29030001411204c200021800000c11030a00411260141d0381f0041080e09580c4501c1002891030040b41c100c203c01040014510755150410752007000c2c0180f02d02005e001d4009140c0c2044504c0f40c880e01d20205800c00030f0003810301c003d6808061079001400400026071152205100d0380303103403c010015184681800c00a00602c01c3e0090000507509085446904c2d00da40c0410040040340103100c020003024488011030740340c1e511f000942d0003410500c07200c2c8003110f1035801c001000e0f0100c0080300081d0b52904001c94207140c800d09400e8031031070029006114190203613105810a5101c00341c0d441141c0014000d102d21070b039080c054100100a05420610125001c5028100402050384 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 458413381 1250 458412131 458412137
    0x21e01110c0303090609120613030807030b1c020a090501141302030c091e0d08030f07020d0905190e01170d020a030801090908070203150a0e010608061609030c0e06010f 74
    0x800803541e039070000216800f41c40c003941d2007921440c01202081c80c00b600b003441c0020500500c030800500c1c40646d01d0407a40359000341da404100d612004401e40407038006815480d003003501840c40b58200d1840503400000940301504200d00641c1d244c0a0700d04031203082e0082182804094494084c528003002007905100301200110325508051100c07002034811040c1490180e0048480e801f02d0401107000c0301b42110020305407403c49403651810704e2140d07208403031010580200b04007040c0c3c800c1c070010f13500c8100b00d0991511040c1c03030b05003010040601c210b0f88458034070b22110500400c0002c00c204c2e03418003d250950039140c0321480b804905041c0031000d1008800c43d807202c11440d01082d0700c0318500303044030080c1100141d00c5a580c10a0360851103603a002a401d8480e0070b0240c1841c09a42d46041d105000d0144200a5040003a14070340c00e8441034414408181e02c130b1400b0405c1c40f03005001001000406003855000c4a6480c2d86244d40c021881e8071000380340d1841130801c1340075604070094800d0008946 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 458414631 1250 458413381 458413393
    0x201061a19141306080703060603051e1807030503130803071a06040207050a030f08100308030a18021203030114040e030d09020303090a030506090f060c0a0e040207021e0111 76
    0x1e100e42a20310380300340d103003081003828a40d80c0c0540518101c400110b11400703c10050358980c040a0130108041e982000020314092000030800e10900c1098019884c0103c0042144c4c4880c044043c0d40c3d402400342680300e043c880c108081c00c0c004001000003144035001031911080c0340b02d080d40780303072400d035100441c907402c1048000c00040d5154100061801344030000451030302c45074086002030080d628000c00c144585004981455000110880c081800d6955660303517a0300e00610b402d14102074800181004414000328041c4800d070341100355045030490f0024203000d500c0d000a1002c4056154107049500000018000c405424034000010041500d06110782c03913010f925203039039225600e100300c0400d9a031800c0c01c00f196828402c480d07404100400c07080100e40c80f81052611a41d042d500d01200c0d03c00d0a02500c610040860014811000362480b142404024581a01c1d83c0c101c600825a2240c7e08001c2c40700180c0d2500700c0410070310100a55464100601000506801e01c840b03c03034216035120f1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 458415881 1250 458414631 458414647
    0x6060f0e19050c0d090326040212030a2f160f080105060a0501110c060d1d060c0702121207080408010c1701050f150a0302220e040305030403020a050d0201061a 70
    0x3c0b00131a0505200500700080310b16135800d00702d50302c00d000c1c030324201083d11400b030303404021500306103160049000710b880e007850404030700c407c503500e100d4441001c0c04504125041c00310345110174141c0020009840d450401340100c41c041c28180401e040345840300442d00d107424814407120f101020054081c0a000b008107081150000d4000b44240c812941004000001000b100a062180c4100207101414050b12415038420110150000f41c0c2500c0d103000c0684c0107101000000602d03075001e039a900b15142d02c0d04c20b140d001d126424800c10304044030b901c2030111300e41e21001c209006100c5240071319491500c1d281401c84042c01c1d21012400c4204001510005e510240c040c11689411502c0071144042c0c3d03150b2200201c0d8161aa0144080500c01d0100312040c01680507001402500d10008141e04401c5d041c600c11900c2c0b1049018281c2240e007940001400a030082004641040c040d00441c2d030310f66038a540d0a417820004181000042c0d44840e000c101241c4255040500400307030810050500c01c00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 458417131 1250 458415881 458415901
    0xd1107090e0105161404181b030e21181f0203030f1302090c090f03011104030507061b030e0612100e0106050406021203071407030305100b09130906060f0e1905 70
    0x602d000b404000704114000c0441544185c0c0081c126003680e404442640308040c40c06002440f01f269005040e014503583c0c1c000d8035144030301c000e48440071030bc0b66070708150102405042800741100c545401034a00070601d504428502c1002168950750760007590b60745000d210702401400041c0c490010812031184410040e6107031420b150f803180d4146403054440149800150585043d2011a03806510b084800c000010303080300107000707807070007001102c1b21a0b41c0c3c0e1004035002d6490200001404000c0b421401c0040e1280c10760340710240b802401682001c286042c030b280e8101081e03460040d2849000420011302e080c0d4541140184620304144d4201850140084d48074203031181c0d00400500d0020002d0b50a50161240648048800e400d242e00d0318198035001e4010542614020540c80c0c407114001002d18502e4211080881e001c1d00c041520308130000c10f10b02428000c1001c0b20080d44884001c550082c00341c041a0041c074580c0c40482d11410601e54020a040c03001c0440c540c11410300c030420503180381c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 458418381 1250 458417131 458417137
    0x2040605150d05060a12151404020a0905070c0b1312032c16030b150a03020f04020a1e0e010e030a020d0f03050c070e0a0c08010303020d1107090e01051614 68
    0x8041c10011038655503501c0080c0d84000d00790000c0315007800542d003a000b4408020702c84901108654420404001c0700c40b232900e036042e0102c074000d501410a1006101c1e64074180c00c42500046a410100d030021300c1542c403c0c400040841c2d102c10944401c0d0b41d40303010711501000c0245031b00e9040c20300300000e00e000003500c0020911006100481e1b440001e2002100c601042000c80b0f02e80d0403009140032644914150004040a80d5101d189510961160b030741880c080c240b50084940c000e041c111042e0540c800d210203500326540001c00c2c0400c000c010b151268003c9040341c1c0001d01c40d03549800d003000b21000500045c01c0020098001d9100c480e1900041c0c40300207110344030750740145c0d6038203100c030952900320350900c640b02c610f41141c082c080000413003c3c3c0c4050018044c41100c071041c854846c103c00b049804002c2441b0140040c1d00000105810074040c001060702c4045503401d480c00261100e40480075558040311300f01b110381d034900030082d00c481d200486900305a22468a000c40507540c92411050f80 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 458419631 1250 458418381 458418397
    0x50a0c090b09060405030a03020c0312030601120c02010902030a0323090906010c051e1605091006050a0309020306010f060917100c090830250201020106080303040f0204060515 77
    0x940c0040c1800143da00c000c00d440052a00504075195078002d0710f0003d440d0718910355030358044c0c40f0f00c0a10030250603030744003640e201d4041a92200b07036000d0160304000c0580740003001481035540c1c034986000961004e03c840d0f8a000d019488418450b48540004003800c103070001d40d00007a400920401005079180f4001076040042460b008c00791210906000381001d0081042c080031841c0805101100c400100e40b482606000c0000000820369070424090b019108a403c03d8102e10300400c1808100c2c018006002e480321286400142c4c0a8180d021a01d0f015081e001481100c4a50600b0017116500c550070001400740813030381e07044400382c00c01c20700d5a55081080c074006403601c600b14901264407410301c0800908907031040301c0c87e07500048141840d4480100100e1902e1480c030f01c0444924070803030308036030640324920a400c4148910409480f0710240608080f0f0440d5241c0d800000c408000300043d42c000e501601000100300c140348100811242c42e90300c01401070300c0180d00c0119015001c001c2d80d20300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 458420881 1250 458419631 458419649
    0x6070f0905060c031b07031a3706081b03030703050a0e0d06050a0b090906060102070e040f0506010b13091509050a060306110c0609061312090e041203050a0c09 70
    0x40c11030084042e056004403035100e8403c1c1075400f05c0319601200041d88801700d030b00a10070000c00d81004400403400b224100d44d409000510381e0015611008802c02812540350a42c038500c1e4050803c014507001d4907204d500408442d030203400300003600e0040350398403e000d0178124004c1d4941013590b0382c0038120b4061b5140b040103028200d0803040c5140c845013100c504983e40310360200001d01d00b12080f0001415002844d6000b00e108074000303060b0002c0000c03014040c01050b00105282e518080c2011101d8000a00c100c422455900c0540c002500800c182c0b4007a10b8070001e0b907600c0e0ba283c060644580b11a070f50002c140a4200580c40404160a5016000350303010540041426684c07154202d0146c545603100902881ca400083c00c6208000e0000e4110344003803400360b40982d01c1e800355459803101d040e1030502c19140c060007000d00140444001c025280e14034180740315403039916052411840000c9401340c85000342d21005800c40c1e41d040c0b03d141da01c01c1100108002c403410700d000043c241d0300c40d80a4079650f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 458422131 1250 458420881 458420887
    0x10506030112030f0504050d06020a0206060a050901090905030909010905040b0c0a050a030911150a031a1e0a0807030b010e0106021b130b04020f07020306090a1212180302010e06070f090506 83
    0xd0a44100206d40251601078586241c20045190400c02580b141e039080006001d0f02001c01c425141200340078046a40042003102c20f0303404c14441400030600f10a04540600c010000e000300c641701d031301245001b4181050000343d42d24040c2080711803040002d01c03404514038100048410340f07822400f40d4040403103501e00010f01c03804500d851042c240f014010154400202c8103c020010040e10003800b2025842c0c0d81031103420020220020b4580301140c1440e4861518051120850780c502c1004a02d10001404038840359510b82c004e40c00c3c036403150010b4030f82c1c800340c50051090142c940c0c440d074010304043c801065000b5440c4151040903802c10f050030703c02c0c01c13002c031170340c206910030b030080b114031f80004004541d06e171501c26040d0159441064120701034011200002c00b1448003040b00820b054001840c40b1a0b541441002c40b1000780e403500f03040a0b5651043c1c500e5034001c0fa44d0725000080c2c0700703130000580c0014000320f09103801b03401000101040761031402d2540f259402600c180031140180c0316107031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 458423381 1250 458422131 458422157
    0xb0f1e0c1213080d05090c0a0506030606030a060519080c06090f01270f150203031e0a090609050a0b100b0706020d24030c060305040c0312030e030c0f0601050603011203 74
    0xb82620001c00007400340c94012519074070381d40d4980c0c01103000b80c403ca0121803e402c010411300c8090585841040d5000205200181890410100079940010039210000c0e04984600010b460161181c0c210040d20002d48801d000354102041003068552007101e96a003401441c10000b6850a04404014104038510704104241040e0001403032111190143c12080c03070340c41d603001110703900e414820040701d014420300f07440420b8008811603000d24000d110f66101541c1201142c1c43c0e01030301500306000b45540e080144d011800c81c0c8122442e640c0303d1000341c044511941004041070130003504100c18001000c0c0c0822101c50405c0448504c0f581c842405a19540d2001e040ca005000710f4101d090888501c041c86e11103650540000001d8030320074103108005030340350390089045443c111002401800c0000003031010800080c8101e00811140ca00480d43e40354804046056070000c4201004c180e000d100c01d070540102c280012805030034107490f46070075589400000c48690285600140601c400c2c018810 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 458424631 1250 458423381 458423401
    0x2090a155408010e2b0c0305120c0304021905010e13090c0303090e01090b030a030e040f0c0e1002010911042003100e0609070c08030907030b0f1e0c12 66
    0x4000211004070032031071650b945080e6400b0700714040c0d4150290240e5075460485000c6a041000c5a504403840389100f6148854107031101014001d00350240901031107150340081c1640c541502c0f40700d0814002e903c900341403051007080154008143c000030030b2140e040c0f100e41d0340704d0804858003d0458581c038500140c0c40c00c120040803090f001504500d0214004814160081d13500c60885030f0b15004850303140c0c0c0e240d6102c4226808800c20765819040380768400007191103000300318484540140300141040d000d281e50011a400d00106102180c0304202120461800c85041103100015000a12800009641d5844c01881000b0742c540304540d210b03500210421110365541c840c10000745030651300d04009400402072425481401550440c2c0000144c581c10706005490040c540c944880c80d8161190b521002c0c00e0f00010f007020054400c440c000804600c0002d4854040e100690302c110030750910044848060b581729a404455030410000e1100300c1c025502110003515030300340860081e4444640c01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 458425881 1250 458424631 458424767
    0x105181b0409020d0203070813240e0328021501090908070c090e07092c011e021903150e041e050c03010c090f0b0d02090a15 55
    0x304841d480401c0300824990250b004600698668440203501c2d0354200000c5044601d414001b044407039a0f030320000c1d512400f0a03da0100340e000ac0e00100d25031a0880750107140d90014084c06100040400700c011101c120b00f803030b04e1030241107440a040c4001002d405000d61220600c14505010780d030308800c134140314880043d944d0095001e4010f40100303a540d4050130103051050500c00c1c031406245400109407a80e0320510840130100c038051034401400c425a81a042c180c560f00704029525005030420032505040c41c3e08940b01e40030340040e04c5484500981ca03903054400f1210041c14034100d00c03a071441140450b003200b181c04080701003415540d5440c19880491034642a60402103408120001308000401c01c0b000304c0d801540200410704500741c0c1250725008610420070040100c1e60140a13140700c2070020412148c85940152401d02e58201003002c01c52207900404d4110000d6200f12135140c0d11a40c40d50f8403a4152085a81c55503d00c007031440003c0c0715850141b480c1c4d00b21841512400410a00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 458427131 1250 458425881 458425889
    0x507020a080706091a030103020904030807030608070602031308010501082802100e031605010f03020a110304080d09120201121e060b0310050d0b0103030309080408060109140105181b04 81
    0x240c90b90380f959160003411409a50003004103081141105100707964206060724122a00142039420302d0f1104c0c0c50079909800007800040c10552590b4020608060401c148001070106130700960752036101c44440001920305030003051243e4145801040b10341030014044d00d100ca8050f2441c185640c0c4400d4982050181c08002904580e85d4030018000c1c40d04040a04894082a016200640d40b84208820f181506020b250301282d0194140c410716842a80030780b5a20039075050000c80f0010380c001c0c444c5540c00a50110031140d01c00050b10b00e420307520612500040003400e034501440502c1d0390001c1c041040042c034940c03903140d6544c070071a203190040c84141040d850b02c00d000c100c410384500201d800c592046039011aa07811a1000003814141111850302d126040002c803440799080d03903400c902420305003109030b0b4141818000854520401d1100e01d008064050000034518055040c4c007035001030503030180f8403c49599015454034426040c905910044241c130303410344030452082d184614021504 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 458428381 1250 458427131 458427133
    0x2031e0304390b18040203070c061d0f0d030624260a0b030d0c0f060b0402120c040305010c050c06180313030506060a0f05031005070519030902091b04060507020a08 72
    0x5000111084824002c10206484404a84d0644210001e01040e0b06c03068410400080003031228001051260744040f4144041c001509908507418110a1424501407454071940d00034107444050143c040c0310b480f0040c699001d8807010720f0039604041245442d00c1d602071050181c665010246541900c00795408855107204440d414186000704000a24025281c103001c3c0c40348100c9984514028410000e405500c10010b442d072000941d6003102420281381810b4205400b031140a40758221440d025206101d40348100751940d00c2c3d800c1c1700703007550155044c0005111042184044240e80807a005611121041c1e00403014111600100e140d8403c494440c0340100144101208004010405502640d41110740c52191615901030360100f02c518415180d250b0301c1060411805c00b442c0e040baa0b03020065042550420300d18a05000748156120341d0400000d69420b90340c011480c003403070200e801020790051602403c00602c65020144141e009031414070402241d19400c641d0386080c850040c00301c5030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 458429631 1250 458428381 458428493
    0x103110604050a060c060e062206060803160c06140f03040309030b01090204080f010b030715020a02130c081f090e0f1204051c020105090402181002031e0304 69
    0x44001440e41e10740405c115400f501b0501c00c14a110000680340d805070b8651120800d00b000f4010320f071119043d103004100d030b0207030321400c0000c0c000743c0c280050200d075800994406207102e0035280a0b01d400409030480414805048100c20010801c1d4003943c01c50340b0009034207940ca8580781020b0310712001550004102c0303400304002203030300001a005003045800f241c0407203e01600d030042c3c050903201103010007500b680c0409020020540d844140d0081c000b510300503100e2803003031600403d051038484482c03031900940b2030f59007899441d0b000d00c229a104521441541a804224600c640c407201203101c5c50940e603031501c1124090b0f40c001d10481014a00c583d04a40c190a00000700d117159411500c9442d1041700080c942c49624202105000a09039050b034655103440c0250741088000c2d002021074096169024040d400141c484032810201040247c00641e200e203400130013175042c88080c48e807800245a09106000001c0c55101c4003040387c1c1c0811011340140e05c04a5122540f85010004403030181141c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 458430881 1250 458429631 458429639
    0x60c0106060e0307170307020d2a0e160801050910081f050108030c061f1701050108070b09031504110d03210c12091b030b0f011205060103110604050a 66
    0x2005040e4000054080d1400c0c140d0b9a1017581410012034003d40d140e8104014040c01031030031102c428912441204808000b14105211645071800c081c00310035000781006007400201481d00074107a20a1a003462245400394036040103240305410720403640102464000b00d1020506810914017820880c0102da24a1a00a4515420406201803403000c549810004100484084100c51310020070000030f01454403034500480c85201d0b442d60699256154003030224011031800b2072001d05604000c0045060350601c0d00b80c9051000680c0844100c000801112055403800b00f001c0c142e9041005204249542e1401c00240c0303041d5800c0050362250004858904050f0000c458005003507944281c072030f050ba00c08012a048944000e1640e010412809440041428681100300e40074400d03030160146110a90410070651690b400c121031407200401003158039284188070034014146100f400300c0c003d01a4950944800042c040a04010031035840310a09489410484006003000b605d101d00030350356 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 458432131 1250 458430881 458430887
    0xc0a0e15220509010506090306160c14010e0c09060d0b040206090607210201020a1b0302070305010e01061a0406140d06030210030608010b0301060e0705130803040b0307020d020a0c0302010302030402060c010606 92
    0x2941c051240720f86aa400081303180e081c07070300070342c0d0100e680500100030b103071a941c12000507500300c000d4000030001c4035a00740300007800041303194072030080707074000860f0010403140f905042c02c500c0d02286000c0c0000504001c1542e0b41c41e141d00760101c0d002401881d90303454030f0003c00c8031031085e1a00c440e08a0300008076541004031008101e000c030280244140452882548224240e01c80c41e02007400040440036a00b041d00d51b040740c01c1c000f180c440d00484039801e689035260b0742500c045068001e000d9558900411420b400c03c2d81d098501150701400516060410b02c0c054040103100048016071480408c0300c89442440d0b40c06003010715002800307941d9001030500300130040d04036030240280765400e0100448c11814140120800d0324400440c5120507516003008540f940c0002810801998440c03d00090b03074402070008001400d03080300c21640c0c034034215102074034004c48100d03082e04543c4030801080100700196006403e4030b0b0309181c0941d69403502d000182107805140b415909551a1410000d00150 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 458433381 1250 458432131 458432197
    0x1608070201140301030c181d07090606020a02060301140a12150c0305040c091e0f09020108070207060f030203280b0418030c060509012003040201080c0a0e15 69
    0x4402d030b84840c010710004001501a00080c80b00501c0a4415a424480844060301c0394210320b541400000b101f0f40d2440442e907590210301d1701c00c1300319040010f05005a001034001d01015100710300052000300611303404a0441d200520462504c1002601f8204456580301e504070002c0141d0480300c400340c005070400400d03485079100b000c64843d1424250b460640e0090140a1003950004c01e0381c108580750008540241c14208801d0841c5094400788040e115400d11450218030800c3d00d00281c01d02c414070025200050107001a000e41d8800d04042000c036a10002d12100682c0301d00e030242e202c0d100c140081610307128008500443e2401d002c420b600410860b800302d07030003020448050000180d02a00c044400c4800c10380580002c0d000b19070400804c06980056420101103400001c4011080c0a203844000e908030703618820100c008240320a540c4d02c2045c0342d401c207074078400051420038075800c06420111425403440c090350200070090b07540b0103032000b500c001206030001510380510407001c03944048 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 458434631 1250 458433381 458433383
    0x30a08091501050d1106041d01080c01050c0604140c130b010305070e0d02010c110307030b16020606011b030903060204080a14030705060105190803121503060601080a0f02160807 78
    0x40300d144a002030709500c4403500380c101c1e02c000d80350140f6240151034a0640c0240107000c2c5410a10030400003819158a612000c1003040c402a45490740d4100a2528106801c0e232010504220307050210444445000c21441c0d00b043d4400c822610340000014140c3c140018484004e601c04d2914200c510201140d8109078100c4409a90400c910f80d070b84001941c10000541015030840e08120180b4015402419004001c502401036000c1c402845800240340c03d07002d8000301d403588080c80c00c2c040c1c1403803000c41280c40e11741c0a001074500b43ca80880002c00b07042d07030070150391039002c500b500070703001d01d8041c0904801441e048241995502d4a0b8500595118000d0004684110070a6001059030f9008015528495441006000380307900e404100b01a02c48840c0a06090310312406000940620800c0100120b80c0d16000906a80c40c003012124042e4041100c100d001e90801c204005131607031703c8501c6560085082e00001020a40444800b0003030140340d803840444003219020001380009040600686 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 458435881 1250 458434631 458434633
    0x1020d021209060c1803030f21100e2202120106170703170307090849050a09080111030f071110230708060415120b18030a0809 56
    0x1644948841c83c1c0e940104440901002d03400744a04040049506a10400004002e04607401d00e80c205110b0309082d03004503800006480c0011740f260b42e10808040c401d501c241280d984034456403400c506108043c03c000d00d00002c038418403c202c03028588002400c3c82e0780750040c180705031120360f1710b807014002d09140c054054001004002003003240c00015010701030380d40c0510351590342c20a4009001d025040504101c0912041440100d0320a02c2006644012038105141c0450780c0202c038107044521060f4003114907050301c078280b0040c8112001042d550540c001d072030070640d6442409005c0b5000b49190704604815400c1c41c407084801990000a94007410351a01e0620303450721404425a4030b1103480034580d41c16003160485030f0750301c0d03004c1d03100030303c00c02201c1d0424000c2c035416103040304040d10807210103011407440f00600c00030742018844c41a40000f91807e401c0924240324281c141900c0c1180020704081c26213000620320322606901580d01081c89e81202d44507060114040c003c0c030404c94902c141 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 458437131 1250 458435881 458435917
    0x140c010e03030702010509090c040e0903031b072a05130504110a03050717150a020a03060906210807060504032105010b0d0218030f0706140708090603090106030501020d02 75
    0x19918001c8203c03090158140c450b07924103a841c1c802c1c0f214004000741780c10300000081c000051070100c58040c02d841244640051940c0303180000503200440312400e4803050010051000b00c000501c0c0c5075100003031441803480406005821040e0f1010407425405c102d4020b03214035402c41041c092500003601552142000c0c203440d88485c01070004034090b41c400a80f00e640010310400c802c0340044400252106c54509840017044030380d1001030800b0090b10b606210760342c0000e107000c0f440d90510400000c2c011050081c00000d280c04880b40c04941c0c04c0802c0e0741e009800c4040c290400c100c40e011178a44d1507000000b480145007504014100c0e21042c441028041880901c02044903078521403941610300511041c0d0802c4034034206c40000f500481c0d10041025102c00c23240b642d955041142004011101c2d008100150800e02e000301041031034100c00d103c821003800b07100e00140452050394882e10058078580e443c1c2e51b42e480100d002d00416400603106500c00242c1d60141c0c0b107035400a202003600010200c070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 458438381 1250 458437131 458437157
    0x30816060614130b0901150315060f080901050f0115030609060b0319020906070303020f07020904050f120316180e070c0605010821030714040e040335040f140c01 71
    0x503220b020340d1355980045240014800d5069030091035890421500e00026624000c0561100350322403070b00400d020500108400c00450380c0582c1d0320303502900e02402840503003810740c00841444410b000706485400b5990205003110710a50002c0c000384840c40040c000d05070f60782000d6403a83d10a4814401c05640c1611032102c3e180d81c0d00072141e03400c1c2e0250180703250030090348085000390400107030300f24049010000030001d6a80d80c80c00038012806000035108815051040034079051a11000b0161072400b401048440381c0404101d844204042c1420a40030160981c1304c1d040d210203802c008503000608050041503a407113a03817107000501c254000c002a0b40c0300c228441c0d45114a01400100e00c541c070502e103a40d00d2204c1c1c007a50700501141000c0980c1c2e105000d19000d150419000f907950b4180c00d500b00300900d5072118040c201c51160622034058041d0071002041c4010001010304450600d0b0b0010404000520842ea4002504045441e2441e5100041a1f844174031001506000844c5940303090 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 458439631 1250 458438381 458438419
    0x70201060803120c0f071209211106090a0807080607260a091e050604050606090f01090504150e010c0e0102010c0e1e0409030504210804030816060614 66
    0x60f81c0c0348501e1094003038907964264000b0142e8042d20038000a40070501003840020707684074183d00400c06544a00c0c000b0350600746540b00c04c445a444199480d00c456440380080f80c01d00034030410242080e9907481d9610200707800705500581590041c0031511549800045804010405a001e06001d13910840009604521404c05444001280c00820610400f040480d840c1e58854981140f00702c80c4000403110a0003905a4520b20310000e803584d4110804000030040280106540104c044a10362680c1c100321207802d42e0720b10140169001c40341c3c2c0c2c40228061081d512025490a038104006010304105155003902078024051020049200400030724440e60040c06252150a45942c660725040a000c0810a4500c840d41d000c0b142031b0304249800860791200e0254083c69806621401d550300c3c54809003400c84005021541c142802510407036000960000c01c0b141180e07007000401d41c03219203008140f0b03001c13407140e68002d0005162000005581c1c08120340c403460b01a045a0104400f500e1002c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 458440881 1250 458439631 458439637
    0xb131203050f07051b03040618051804031107030204180213060503060a11070525080304031a0717090d021002092112180a17100c180905070201060803 66
    0x19610350b41c0c00040340940f080300900140e01841d10000d02c2c1254052035141994021f412810006480c420306d0301c0c0684202c10554000c000c03c1d01d6500c0c1c00f0349807602c080107003c03000c0c1005082100b10701480c440b0503800c20060340030b0342d00100200f211500c02210314000c0d8055172802c900800d82840078200c1c0715028401c00003141c0c00030f030150440d03a036003120303020040010390f1031002500014020000890340401c40c034440344075048140d4031601400f101ea5a40700880382e1000b41075600400040c000a01c5800500c004c0034004000405d0a40f0380107410b560310450501007076400d12001c2c0411000a00009054030101525001e40d1b51000da240b807580d003a407041a050a41044620740b50300f081300e0489207127504502004050b220381c41e4036011242410b03400138504803101070350104c410780680740203041e08004048807800341700140c1d04946e255071559204501603034490b50ba040d02101060142c410f8010004131540100d40007a00d803000d00c002000240d440d41300542c42d00302e01092200b0300100f2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 458442131 1250 458440881 458440891
    0x1111804090201020a020114070b01090509071e0303081012062f040b0c1f0b13140f0604060504020c01060911030702060c0903010f0207050a060b010e22090b13120305 73
    0x1414030405da0350015a140a1811890303501ca0204002031800704d802420028060144d052001c5842d013031a100d0ba43c0303050001e4103d03410b90405460744034141c446a107144411254103091032006a030700e42160f0500210039030303c050b40e6100708010031410407041e075100c4448e101e440c0c0301000554042e000c041c500f00c60b9400e03441c0d04440c4108010700c000c0c0070490240600350034100444845032483c00302c01c0c6244014001800a954803001210b0203440c260307007003050905556200700706d081c0c5982500d00208002800352080c1c0c0a401000c5182d985840d0060340c050b040240040d5070301e910008810f8020212440348606040c42c024070840f0341c026050071680580407941c001c110584902610850951269240e19450365842510112801c0d050000d05419406070000c3c2003030040900740242603402080001d8104400c0c07080e103071480c0c1c0c0c03420b2085c1c007184a80c1c070482e02e00844c20b100c444000c0c083c5a501400160f20503003000300740b19a40b07441a02d101e00c91480340d00111080903043d0f05642080e18 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 458443381 1250 458442131 458442133
    0x60e0c07170427091a0711030a080a090c0305012315011403071b031e0905031b01020c060f030103020a091404060908071209140307080c0f0a080111180409020102 71
    0x42c09050b0050001044a00070081d1030002540c042681d0b9603103009001a0174281140d42e444007000600c1d50005042504160603002071807030695648002005028018014000141c0c0d804400c014000150602030241d50721034000c01040c214508400c0344029200010361b400321099000403c64180c00d01d5292283c0010384801201c0c10705554415101e81004210500300300c59248410141144500340488403800f0303840385221600c00241d440080c000803800030302070000a900802c020b803000580d0148501c50883d02d1a048070000300100d081031030450000e030f806080810111900d1074100c0003035040b030b442120b40b8105981d88182d0711003514a800100031085030f080001034081181500071204052080c4481445c0107c06d0740d40c41c0100011500310f50006528040621180d04664074076110b03030004400803e0702c0c030701e04900203a84a5000c0602070045d000185c1c405041e844a8102d00d014040c9040280b10f030303401070702a100d0313141c004d9440586440f103007140d181030600b064403c210ba040d4041e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 458444631 1250 458443381 458443409
    0x3070611070306021c050a1a1002060f0a0b0a150905030d171b130e130c09020a020c150a03150b07030804050c0424050102060919020301060e0c071704 66
    0x3840707200080d00402c6401d01c001c0b00110340300f017510400781300311440744924000c001240c0300c10020914a0039801e0803014003d140817801e442d055600007859541c0f0001c0042802e4043d0740781a551800b500c0070356100c41d04503d442c4004200d18103444442d000c0b4000f0b0390360307890b41c0035603480400d56120490822000420036904c01010212602910194080c0e0840c6000008241184514200b40e000b40388070014104448014800c4400020b009074020b10040c2c540601d41042e9291005e802c2d134540700f20305c0c580c0d42c0041c3c031100c0d07d40203115046805000400c800000d0480b5040e003251603014a50070310000745040d11484090909000d00d00c29182441185401c0c420b00307030303829911540c001d0001d40c0d40d4400c008041e2080e83d01c1c1d00650356403041643c0c1d03c0c2040001c86103040d0910415030081410754022204000b107001000070b0100000c1048002d80107012100d00120b4010940b03a080151040440c3c0104104e02d0003140007440018498048440605002c118039401d0780198014040942c01e50 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 458445881 1250 458444631 458444633
    0x17010f02030f010b0f0405090705070b06040b0f06131205070305070816091e0f0b0913080a0804080702060708090f01031a01030c03063c030b0c07050a12030b030706110703 75
    0x810185c120300140985d000e181c00e40b641d0000f01e0160301182c88500144000844c02c1c10007403c0c000d2180c008e001618207005c1c1c4120f89000641840c02e0750300580c094280480c040303429007034000b4840002e00004800c49640360003401d1041e02c030082030100740c1d194807414074001030b4024000361203960003c006104e00d0003a8201050b400103052043c8801c20040b441000100d001642489050f10341410581f00080c084205014082840030013801410b00d03121039035104000c01c2d0880200c1d0601e9009142000c83c9690310301e000200c5000710760001e034004030b0110710481084070110007072801d400c040720b003150b2008858004400340c409421494510103050101d0040f40d5010350001310b825811410b0201c4d480e525114800e400c01d254207018100e0544c1d00c00001c0107000a0700c0e42881c400184c0d07066001c90381c00c41e240c2502d201c0004c0d0002400361000609241032002c02e016568040340d200c040c00e143c190000d940103014088070001c0b54400d0180700700020b03000f4001d2242102c540103e8010309105499 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 458447131 1250 458445881 458445899
    0x120a050c040e030c0f030406030c0825090b070501360312060308130e130f030e040f0e070302120f0c040504031b0602040614270102011517010f02030f01 67
    0x310841d007264402403044c00b141c518140a82e22403001000011b40d00c0710f06d00480202919241c11441040c06088014081d03580322290b4840c02240882d13400e40e400d85507244084803000f4565000c0842440085085400c00c401900041e01c501c0115815170030180c002000c1a0b00311500c0403008400c4003185400c0400603002d9400d020300e1001925001a89a5880e11124010352104c80e00c1840700b00f00500034030aa0001090507504a15081d0a40310696060399607044501d01c1403201400b40541c0c0030145131300f03981d40d0304031008044180b032050210140182d01c00b561503445000480c85a10341c1141030300f1b00500000d45002d03085003a8024000740280f6410304c0014100039100350b0400600f004007031034a024202481180c548102c800603611850000c005019200c42480580108000c20200002c5408165040ca002540c0c02628034030012180c0142e0041008c440702001d002042e00002072444646201d82e100b40701c51070000e1002492403c0120120312084a440b20000e174280300501c59090 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 458448381 1250 458447131 458447141
    0x1211070905010b1206011103040602012901051c02040324060501020f0d080408120c0a03050702150411040f060f03110d0b0c0d0e060a0615020109020109060e0d06090f02120a050c04 79
    0x10047c144050314500c50503110781140e22980249000d41c0d11600c9002191942175070b03806150442d04061055171070004002842442010700b00740580503c00340d17880002d60254101c800031603020001c890315900e9440841b94529100d2803200c8007624125002070b03d54004280303120805c44d420098045000000019100c01a000d401074503c91418402140c000044010f200e0241c024001147d486070305d030480c002d0640307400508000440d0000310700d42ea01c1240324005e00d504181d1121b03104610f0300d0302c17102060082410241051802c0d0904800240c1d05a8000f09041501c0c00342a03031050700501c9406016500c44902d500510040c1e00c1e200041154101201502d0802c1d02d50901040003450345c00e00320b24140c010746080da0b01da5941c0c481000f181d00c01c1d0348a01c241c6007850000307100b00b1030b8a8001070701041481c4500018041b001c180c4c04500c2c5e031091460451958045800c00400260f81041d005030b1100c2c0d2412030240e0080c401648910200268151145921800600d500002c080c01e100181c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 458449631 1250 458448381 458448391
    0x1140123040b0a230915070b270a0303020405100309020d0b04080f0309011e0c0e09070302040e01030501051524090f090403080f15010504031e1211070905010b12 71
    0x10002800450000140c2100c540245002c0c8050944481e022420070030f84c0c4000c1400030200d032004110f403000180b0400500c0c0d42c0718240b0f0004294100103d441c5504035041e250040c8041e0040200e440202f43e0951301401c1901d01c15546100e52030141c09007601182d040c1c06010750f0007000f981c07031031000400368028958082d1290410b03505000c40050400c0d4250000e0300c4a81c000c1e5140d0865010003011815a01020307000c0d94420b0007000c900480140080d4503c100e410300030f080041c0003a1165010313030101c40081c542c00d59914200e6a41e070070302c14001c04064680344600c007110809910a450110821109640e9084907841e078a16001c40031006940a9440550441c0c081e001c0ca41d03036a5610102544540c0c000c1c0c4036483c842c03402184205100800070100c106580820703480740c4642c1d80c441d0544007a02d82c030010702e40c82c1e01c1381141500408200050020084102042d000e0b030401d40c000301e4030240540d540c0486600d02c1e00c03000c50314140d407404d004030006c50b07006104c071211140050100b2038100c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 458450881 1250 458449631 458449637
    0x3060504020411070c08010b0402180d0309170f0618030a0503220b04050c03030a170402030109060c0f11060103030c0609020f03011d0708060402010917030d0501140123040b0a 77
    0xc00030101c20003c2d5904130000a0f9a0110414010409240301380035a441014040b20110b1502410f00d8404401d44100104d590090406203148010036004180b15030242c0304042071600384080744810b0396540c0e40385241d55681e07030040d8408911280040415280d00f4284140178600780b1b14003035000c59407900001c1000c00101034260010090341c000380ca81000060096024420515280c10500c1c6040d03d52202c141c06517004001681107698007010551101c00c66440c1c1d100161130307500009004d0087d407a005030049240032400400b9075013001103c0c0c011070b020b4032a0600c214800088944906092101034041180b4020020003d46990700441265100824034400700c094900828210742c554284502147c030440135285280750304201890040c10700d000106190700e41903000810340b440b64841c1f00c1444000e50079218032200c050081e1801181c0a072010040d546e03403014960260440b05038100c2c046600010308486004207000070100580c0b408151911b041e10300010300410741e102803220020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 458452131 1250 458450881 458450891
    0x7081e04030606090510050f060702030c031b01080a060308090d03120e07090f050103110603091005130c06020d1e14070b061518100309051f0b0a060207030605040204 73
    0x144a55910182000c0e60242c100021624144030301ca00450700302038040c01d100c043d10740040107103a844000204043c042a1902034640d4010b101191804581d1280150305005140c1c1c03044030ba180b40d00400d981b908090f40d86c64020380390303124114101c50142c0009440200100250422414055403100e841031280c90041103800300900000b00310f07281081c89140035045071404019480840c022501d00c2c103a50f0718200b006501d160351ba54149801352028600420002c030010f41191001d1115001e0a14080d00500241c0340501e00c1c00381e840307440d1404540ca410b1484002c25158030005403403007100c086441c0d1483d0000d009454101e41c202c203190490070403172000907004420444c817002e40802d6219130b15a1410f800c0000070008100302540880070f0480c0144440c1c100d140d0001c030100d80e50107040d0b50001b821100341c0d40031006008003100c007400c1031290345900b049140703c1c01084c40c0360504804040107a8044c948c104565a02c003032242c0310059000c4101070012490075400f5030b8200703100410000b5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 458453237 1106 458452131 458452177
    0xd0501140901320c090303070b0108121206150c1009060e0307021e0d0c06020c013e070e090a0b070f080f04030e040e0325080708 57
    0x4200c0301201040008207100c00f11145c00300042d0640ea42c0b800e841c108a64415000c0c407413810948599a10099440071031820380301ca03113024140c1c1c13548545444080000c2650181290100314000f0000010703180c90400c40c04c0c011445125000c5080c0303109007424421035441c450511404d070002c016580040e520442c4e0901048000d202060f083c0c03400c0e0740401c1424644143c01000c0022032107020880c00e400107694400301ca4240d0344d0780e0490b5446460201402d05a600740000a11156401100b6800700c1d0034a40003103200e01d00319040c5a507511030002d070406007525506200c1e0800403001040c005000c1006500000320f0600001d14082d2110040c0080401009200f21295420200e0200741c0304040032082204018002e000e860580da030360070b449074400301305c0008400440e51176544a80a4aa555220a82102209007002c3c200e841c0c2050b9540502c0403090111201c0407254 = true := by decide +kernel

theorem cover : BRFrame.Cov 458273381 458453237 := by
  have h0 := BRFrame.cov_init 458273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 458273381 ≤ n) (h2 : n < 458453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
