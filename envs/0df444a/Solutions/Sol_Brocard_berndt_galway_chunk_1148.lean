-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1148
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:27:16.056173+00:00
-- url     : https://prove2.me/submissions/cfb04560-50c6-41ea-b911-5c3857926088

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 206294964 ≤ n < 206474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 206296214 1250 206294964 206294971
    0xc112202030f070f08040201080a1803030905010506040204120209041a0c090316060815010216270603080f0307140a020109020a0602030c100e0106050d050a03080606090105030402190e0915 83
    0x44c041c0d01800c4070640042044c4070160019040c411003c0104820030399540002c64580b0142c1c50090701311044c1e1074014014000c0c0041900d15500e49408074186181c00e0084130200c0b079019072122000ca50b075070200540484050001c81e03c41103404880c0341480305582d10f0032310410342c104000da11344208a05050070b2042e00819881c400c4420760081c41929004030300300b0b0304400242d6074a0b00f2050309800503807404011074400382c0c3c0c8101c005000642c1a904180c0301440051100c03016003a401015142c0058500d1800018400350080c0001d884421a0030301446e80a0071902e0329540001d246444000305500441c40200140d4548501c00154103000b82840000c004030300c001c0d440c0050301803845841f54007000b00055902c0e1505c0c0481d61000c0250130403000b4001c002c2442203000e43c90b24000d6034450381c8a01c03c030045020000055005e1405409956500c141a1a054030303556655081040f000a0407845001c5003900b00340204000c140344000a205181c0800101061540c506141c000c0b4603004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 206297464 1250 206296214 206296217
    0x103030c260a03051b03010f0602010e0601081e010f0f02070b150105160311010e060907120308010b071509030801061701150c0f08030c071509030c112202030f07 71
    0x141c010600c1206007411520310404a140026140c0c0b259462500d140144282054100001000120720707403401c10b4103c0c00f10b0301c1d140c0080040104010000391284400d110b8203030b040c0c0002c103107200c54484a010102a0380b2100c2c0000840c281120845400c441e0144400c00c101c99002c500c10007004500c0c0451904520707400b030301c5441281c640000804c80c0c450010280c414000d80c1c00e1000400d8040e071100c1001c2907003039009000416030700303000c5541c944e0225a900342e0740c840d2510010b403001c0220002901c0d2034140e0b803070b009c4980c01c0060101c51a404458100c40406400320100e00c404401d03c40d09048522035500d0a80652402d14000e183d03250404815041c9440240100802940d961301240404a03a04140121070054206807060064900d00a0303e1034000004101075106504000e0030050720542440801c100221403490480c1c41e0800d0040110701541400d90104544030b806148200c0002c121070080112840c42ca10000d6015001e80341d001e801009219225003481086a1b000e00103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 206298714 1250 206297464 206297513
    0x3011e0503150c0d06030204110909011502030708160516080c01030e030702090604330608010e06090405031905071a0705120903090d0b040507081207020f180103030c 73
    0x203504001500c00c038003900c124190f40700061400b08690407600140700540c0c008204100820501c1c001a40580c40701074950300c204c50300703000070842d11440c80a40940300b01d0b690045003000015070300c8207910b030b1184410f0441b81c0c41e0703090300d50b0010f42c00700030300c0d03810380e01d80c5510004480c90904010300c2c00e0011200315046c0740c2843e01c0101c480034000b060314146501101c003620300e515010b0120740100720080441c41540d1951210490240c2601442841c49d503015040029044c1d48a03000c44200c4803e02509910141c1b5402003002858514280c81e0450300610aa9241c40c04061009140303101c400328250200320049003100034003070a1020040240000b001b400d081d07160000b4020030074032880d1500603024000b01c0100750f04190401c240c407002c0001500d8030300c450300c641c10044c2144d40100d034100c0300d6202e0074202099405010500c45c81c01e1400218842c00d2400c1c0d94200070f40184000400c0342c02480000d550400c1402d0004454000c0d030280d190040f5103140b50a102c04408418a00500c0c03072601c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 206299964 1250 206298714 206298733
    0x509010b060a05030606071407060e0f010c0204051b1b011d070e040f05060403080f070905030715020109080a0324050303040e0a020706110a020d0207030b0a051b03011e0503 76
    0x41d00c5080320304001c401e00e0f24036038a58842000a90600070448007406003d0300402003446d0210020351181541e00c80e80383c1464511900040001c2034611002181c000791a020207100182003541200da0860039231081c07100218240c25800c0b095401c6021204a076814088800c50014001e1107282e4081d40c1101c410320500d210045800d0340d03a0132901c50340000c0300024000800340075406058002c426804820b8525500381800c2c002c100c0c0c2020f4500300b580e20718150205440302c2c01460380761701302e41001d400780c040545044a030004010503a042d501c10f40d500c89040b030740058044c8004100785030554034006000c3c00c0c0d40c400303002008940c082c85288408072003810300007036038004140c80803202c4803035560381150380d11003054019001c2e071000100000d041441c0e6442850b41400684a84080b9500321070010034122022650303008940300c0546003002d980d010500c10842a04920350001c0c810810f1404428845000f9000758000d03482041081c54000425003400c80326107034600200011801040b800d0b4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 206301214 1250 206299964 206299969
    0x1006020f0703030809160b1e0712050a0302090a120b0f0f06040506040f020a0819021602060c03190c0308010603021801030b030f011a120106030b0403030218060d0e010509010b 77
    0xa8003404060280b00d403060016400d10300410106c0740311140d5282d8000074940ea003118615641041c1c140f4407518070b540e9203040c4c4245d2402c083da40c1494001a448c58a6000e02c4403d488683c08614110304050f020440c01c0010b4544241800003082030000224268401d410a61180d100103080244804048810b004062403078604d0950814003c80d40043c09854820014000f00b000300c0001e1183c6001048110001d0341246c100341c03241c91210300038000040b0300c0211070200c0c428800d01c40940d0400400381d45c00350900c8809840d807491440304032464506002522441040b0591104001500003036410041542c8201c013580101b80c2401d09500340701c1040c20080b00400100c052504160743e5200006440ea402c11000c8030220a11000b04416003406201052801c00b850007180540040c0203001d2450b5414422101203c0d003007075001d140d98513140c0c1d048000c0d50192184400121a41a0440880d41d840e001003035a00c8820000088855050486d91309542c402000c49016925000da14202d58 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 206302464 1250 206301214 206301223
    0x140403050d0509160305060604060f05010c15090609050303070f09060c0f0204140112110303090d030c110303160317040b0105061315030902240412020f0d0b1006020f 73
    0xc12040c0702041c281d0364501d8651900d41c50910103c003030319002800005000e000300e4114018a0f059034140b00c0070b5140c06c1004460492449014001043e500306007000c20300c913440d41d0403418864080801c034021245c0301c91042e10030307001d03080c0c50f16080081070211660700440248940400c5040c01c100c1b1514042015181540c03d00b0081c00c080e40c421038080071583d42d944070203040300118002c1001c0d542c494840c0404000544011199181c503008030307421031724001043e0744d58000010119003141103030b544e0488084c43d14805c00c440030b408000501409a40610140482d04102d0440400c0d5803094100104a1449121030b6400168820180000703d11046000c41c19030f103060350320555402c03291100c0600001103500004c01c84409007003c4510340e230300d9041400d42d1030086503106c005e0700c040045c2d40d150140f07100007001031007030821040144070140801c1840b468001000b03140511010700216a1002c00d401085900014140c200064440302038440c1d00540000d200804104d20701c0d04c10107a89 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 206303714 1250 206302464 206302477
    0x906200d08130b010806100501030608060c091207030302011505090714160f05060610050c030405010c020d02060a08090d020c011b0609020303120702010f0b010e040903091706090114040305 83
    0x30428500000b941c0381c080225564121544107414110f950b0391804110380b540c005071003c0004201100c40007555600c01c2c014481a51481c2d005001151107420110406500002d2004e4010700c4030740e00d40414403000e00c50400158000c0d0004030380c4040d084445070005000b9004248034110700d000340181c0c681d01a80c00d040312407081d4491643d50869035001154000c1c0c03003000603c0c480c40700710702004004010510030b004500c1030b6451072072050307850406e46007030103841c0c41200a03034014031081103158402c01c0b8011030280090407078204038040d500418802c5c1e105084c4d03400403402c1034062001c501c00c1040140c986000303510180814076492400204010340302c5010559540c0c1c2000c509060040d140e021584640e4000c049a6590120a40010600d44220303587e001551828141080c0d007a298000c0344031411059440c1181c24191230308020007005410815010081c170100d0104808a1448480f0800e0038510010a15403511060b42406e42c1d040802c4070580c0780030b42d0309000010b40c000317094441 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 206304964 1250 206303714 206303717
    0x112260d111c1a1c05010b030a03140a03020d020301090c12020406050405010e060408190605010e07170a0e0303090c040b1509060318100b0405060337060c0906200d 72
    0x10140d8510603c82c0328510b4001c840c1e07521550030409040100804800103040b688904003d00584038200c042503103d01d10311300041c0120b14001c10303011100d4020310051045c2021401d0041c100900000404201d820913084a480300d507540903400c00d07564012225400305001c65400350720b03203800c04070010014040c2d4843e450500c0404504008130f90348110a980140c4091021542011024103d4184840078000151403c03032810001040441c460343c4000c5c4100c00c81d4507454810721400e0106911400e0040c900ca034003a41d201e590207401e060520046000342070002c01040b049448104100c1150003100300e1700c0c03081c400101c1041c4044044070035240c0c1c0381c0044400b29101d0340c2c1e110a0146809042030103160501034a840300c0066440340e40300e100f14a105880800851303440c42c0a1541d20411500b8401d000f00e04041080c1800045444141945807c142001460700c956920030342551445e01d06a40425000310040c40070691010b04900403045d1021a540050b070304400481e02d0741c2e101c01c510700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 206306214 1250 206304964 206304971
    0x61509040207060b1201060519030201080705250308091501120f080c010510030c090207020102120904110d0504050c0d0321140a09120203070b0112260d111c 69
    0x10a103c126030103048a0403024280403000c1c0d04115105000b048a806000c0c0708541861303520415641c60b021000a40b81d06866220031612418010760b400e4102690145501032001c2a01c450a08440e44880105101e40c4412000d17040c0401080c0c00c03c807182040c0f042c050350346001080f10607c8054034100c0d09070850011803000c416801e105126100e14185041158240421310122400020309007003140e008802c218107150325038080314164820710b00003074016400034441801420301e400c01800721a00c014400102d035408404075002a030400d51111071030350303660b104000501000340000000f902040740c0203010681250750203404d2109050021050300502c0e00d128080079481e038090146400d242d000740c02e1510b050729060000c2c080405040320b81d18107030002e80340414000400e40d00600e600082a040c1b60b800c0210860722400e01c08010b54500f03c00c003404400c070200796103039414260080f5030815075505681c0503840075683e040c00314045a52041006894440071038031081040d0003c42d4010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 206307464 1250 206306214 206306227
    0xf050a090312261e01051e1306060e040e07030804030605070512040f0c0e070914040b060a08100b0f0301091802210111040311060703030f1407080615090402 69
    0x3103c030030042c00381014855040000b10b500029425584922449400d105006800701011001818a80c20b00c10b0941100c104214204408504900d03150803000180c0b130000c44d4a90910318906031901a0f2090012501700d180c4205182498050103d1060749140200036a62866a4400350b034425132201404550b5100042030380c0a1247e0b045401e40000390030104a5400c00b420000700d0802e05050407110151340a50016034045071400192040750540c51703d2010300e241c00700d8104020300100845a21954803d1000c01d40d48c1c4100c040d100305085a03456410500c0c0c040a8042c4502c000c2d0400c8140ca207080c012581e5010507442100c3c15105a0000855100304143c449003c51b80c500700c00a41c0400041030560f60420350321710100610031260020b200d02c0c1003c220a81091045010242440d80140b03d65101e908040b0014a4294824a40060100780802e4248101d445040c01021940c2150040c0450319070722014503a048242217406081e40b01c1500c111009600c40c0941c6a0301594011941 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 206308714 1250 206307464 206307467
    0xf0112020702090c0a11010c0203030a0f06030c06110d0201091509140d03020d060f050a0303030e03130305030403020a05011706090714030f07110706050d0515100f0f050a090312 78
    0x151036075603901400140141c203150390001c1d1550800040e4400148800d44100c0b944170f814001d486c5151201d40145142d502c031a07040b1006002142d06030041d0b240c64040000c0080e00186090f4010140c9a8a41412141c005241814a4001c01c514801c6a05110b0190b0204d606101e121000c8400c03c0f80014000440f03180181c04105c074404264080d024045801a02d01c0e0141c00038044221404002c100d81500c86003043d4a007181d82c000da6411034140307403041c80081c1c000d92200d45050300e03c0c4c003100c2c00e224690200034010b0341560000c864a404c003140400c11402c00c114810b028000c242001c64440c1c8a0000504034240014000b41c810b601700030200b10194001c091425146040151031990b0b4038041c04148410001910100c3c00074408086075a81d0150110303001007504d11980c1e640c0d1502003080304103405000c025110b69150040c2110000b1195203120952a0109040e116034040c0050a00301801c08050000392505003c2e08000303207504164428011016654001448511030a60600 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 206309964 1250 206308714 206308717
    0x11030106021f061212091d040611040f0602010207110d1e110d0305130b09030619020906070501140106230714010204081606030c09060806040e061e010504050103020f011202 76
    0x6070300055010061a41842032543c00f800481c9855100c40d15107503031340c2031206050204887c400c41d5902840c008100002c1c12500181d10700883c00001c20300f016102e0188001d100102d030300c502d025039070019108c82040800754950b00152021102000c2003505925880d04450504dc480080b0206400302c0104016040305030010000f00a45018107004240c50041e0055102c04084120b0070084103001407514010f0044131800c03080076002c1e0619454143c0e1292846080c41d02507080141c0070701c000145600c400001c0d1041c0d6000d10008100d81d000b00780f10640e46032060308010100103903086051202a4a844044020103403400990795945040c00c11101c0075030074042c1c5002d80d500024001402c11000101c404207501840019242039a84244c140d044510f00c054070f00100c0c0d1140802c00c407941c0100e101070344c0244040c01c04a4680c1007001d0381400e108080383c40b50146041c858041c56a0000320310164090441600c040109504680000d41000c0041d06071504110003004440d905510540 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 206311214 1250 206309964 206309969
    0x50a0b0c070f060e130203010303020a120e130504060c0906020d0e0303090d0813060219061d011d0c0409020f06030414070602060103060f0513080903070b0f0306010311030106021f06 80
    0x1c41c0103807003d032240c00042032075603615041e03817041c0318220140b9000e400314800c42e8102c03a41074000700201e80a41d030f034845002448100540c01c2c032001c2c400a910a031100b1404409400010500040758030345850010107e84074004003a04002c2800d0081c04803030b40008001c123042c8520b0034807040203590800003034654840c00484035086090401484208079061000e4001202800914200c2d0360300c4000484c0d43c0d80681038400646038440c02158007041117541701c8841074034a0f00360180c032070a081d50554295090f100d40c0d62851106011781c0360300d814040c05040d0714540b04980c00c1c08961416000500082d04052141c0c1c0300d450004080783c00c110b0a02014807a0304c0c8144203175206c055494002035100c440920058271000d041202d14104a4603501c1021302c11005c51000c11954812a11141003541080a4203034046c42080808900e8480d6900030b428012401100d081d07492030f2040004040e07070188901003082c8a0309000500c0b1050b004075100c0000f190072800b4080000c15907117054003600056 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 206312464 1250 206311214 206311229
    0xe07050d050106030311150f06040b04050907060e030c090c030705040302030a03090614030603150405102a031b0302070503040e070806041b0903140c040c1110020301050a0b0c07 78
    0x25040e80410034190081401c583c0030341c482e030101c000c1000183d40c981303401040007440d144000b030018041d0075100f01141d800075005403000400d0f9020f071000c64100e480648400415074040841042400d0303000036005180503040e009000044c03001404280c40708006459180030540c0880055840d074441c0041d00e0081d0f4000301118200341c801d08002c0d1aa6981c0d00131900080c50f01c60300002d002d0300724030442c0d0040101900a10310084010919410544007510881c0d06010b12810316103030745401d0181100f04613038180f070f090412010485100060a00080b000c061500b0104201400303080d501c4030103c0100c2e0382c00c0c09070340d805c213134900a0300310312071908a203d103440c6c00400e200c900c5900c0143d80e8070481064504024003000601801890703c0d00c070344024000307820b00006100041003103030014041c034010f4044640000ca040002010f8424079408140041c2d15040c0019000d01d041128403d0005865000c616650400700030501555550080c0c80001c640010720304100b8208121840c000d2854 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 206313714 1250 206312464 206312479
    0x1905060703031d03030c0a02060a0c1d040f11090117101e090c2a05030405060a030b03070b360d080c01052502060f01052101020d0c080702160302040e0705 68
    0x4202100e400350000c911040c01440782c00d000ad448901c4e00c0c8586c56102109446000b01c4209035a0000d180c4415100740580050f104e85420651920300d006200d40e80461012a645403c5594001401c0501c2c081da00744018800200780300740700044000007401d99130004030541226400d00c40c1443c80492580c04200128544001001c4855010800c1c03088100400e03070820400b00c0c412103c4085814211000e0076a80003040100480e140c00c3c4011300054501d8100890358084410000c1c1c107000081d801080b17800d034009010002c04903101962aa4041c40800c0142c1060900c10007428000800211502501e0480c01e80d03014802124180c51000c03800900a000700d103491030f068142800092800c290511955911000c030740e001051040c4a586100d4008543c1d0780784c04c0411080c400c0c80c0c031840404104100c00800311071800e00050505d9140b520010903103a00b1100001e00c2004018020000c54000350701c500013080b80d020042007104d4048502007090710003052107a003450016484940d10900 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 206314964 1250 206313714 206313721
    0x60f0c03070303060b03040c06080901090804080f070b040b040e071e020c030d05070305090f041d06070909111207030221100e06100f0507060207111905060703031d0303 74
    0x28004020400c00c0d21a039070922000b5521510102c081c00150340040943c1d074032200600442d845401c00e0390b444002e0100200b040d05168075503417180da1240c0c024842c190030410709070240f214104044001810702080b00e83c5020b2a1243c00e50f00340c0664015060302001d007802107020288500200714440210345c060030444030601101a6442040c901032502a00903214a883d80a00070400c1d90700c101d402d522001d184c150000c080004052030230300001d90103a41ca0301c0c807848ca0b8130502c9588147c40c641000600d20b078103007a00d000c1c01c4a03202d58003904980d414401c1112820915006480c044801e01010f07092980307501405502030300801402c00c082d480c421800e1002e50101d10b0b9018050f01c5205c00e100740041d100c42c1c41c80103440044540c0d5800c90110507031403511502c100c1c2c005554043c145040b42c1400c0c01591100d043c0c4e8007041c1d0a0750304450000300e8000c0c91a001180c0008079450300c1d1485429032419011840c1c4ac010044054203250752007500c00c428040b5000f207002c00b4106d0344182d903520318 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 206316214 1250 206314964 206314987
    0x30c06020d051b0906072613080f07050d0201030b010c051f15120b090102040f060c0221060c070c0807030b160c172a0106050102010b0a050d11060f 65
    0x701140d642c12182c0d4501522007500203c0c80840d050148094410340c84e2000350b0b2241140d03074805e44011000c00300e459102c9020346211001900d000100c060340e040140380b40c07140315403030050034161300210b94204600402c100d03a9031a03026899131b40d082c240402c04008810040e260b0803034920000d0954083c85046410414124201900c4040560004c114003a07402002503e21351b218054040f100004180c01c5010812900740d0380d500075500307030000d4545522800302d003151011030340c001004610103640341d81c11840d002308400c1c0c0c0401200c080b483c000c040b108029a9604001e0b04c105050400001c1080a001ca082100c0003d040d26004850040d5034a00d041d0708410780442c0c19400b6081c042d1020018580f1032001c3c02040d40d00051000c600c2c500003910303129154003a54070f044014401b03086100685e401d0358200d07402c040740c94000150040c980400a420b40e03a07403100722032042c400040d050180380d030b0342c030b501003032890300000b01c051100b1040020510510403036840380034101d4042488050304 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 206317464 1250 206316214 206316221
    0x7031d100e180c030103061d0f0705010908012307020a0204050c0a11160b0a030b09090a03030f022a0c03150603070902030609060f04270c050307081009030c06020d 72
    0xc0d00564241e800c0c02c6140d11484069030082e20081c2d0740800070001040802c8803034111076414801902c1c112070407012910300d54070b0301810b5140b803c01504070907000c026035a0041810001041a0802440f0a6021070310141d90349007010100700c104c45008011542a0b0b1080084103806640900b00700301e1402e0490304074a054000a403a00c0c00600d6a400d4049159804510826404c840b0a12031341c1003810701c4500d0b03090350881740c0b240007016610f000c50380c0207640e2020b455004084030f1002e000c0096003802c0c0207007683e000300b80740d080c054010082c904006010058800505080000410600500610207828526005082079044c45441000ca42c002c0f620b90080d4005c0c1d008400321380310242da9107101c0e400d81c0411202154800d12000c00039000e800c020a5003090803200800006400c0d10030b403403141d0710f070712984e02c0904074500088410081010300b000d04000b61000303c004102c020728141415941d04c0c0009680c000712a185d40c0f201d030405002d801c0c5d00c240203a1007078041d034032418100d5401005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 206318714 1250 206317464 206317487
    0x21603050c270103060209010c0605070806040515010e010e040e150108070509010b0d15090609020c0105220807210e0102010c0c0206182209030215060607031d10 71
    0x7520390380003220540b010100715500401c03510765000000380e1854441070000d42200c0405414031408140d1500003810503c10396204565035111020107040460500c0101e49004003000d02c89442c0b291640002c1c0e820100c500310180091802c0080300750600d000c500a0500501c03000410321500fa0010398880360761485606035010700c8120382c240b65aa000b04019040284a030f03d030890f004002001d90a907450308071038110303d17121500c00d1507580c2d03e130b655000f1542c02d41e00c15811b80c0e0307000c2385c000030207a002c2c0659500508540b148007196260160340102c08000c00c10002c0c200d240000b082000c21a511502060042203a0fa50411103403a141014103c80042c0310f4003401546818511003509000d85071484000d600500071504022000701011440038000b80c009034814182e0003070303000e00a4814880d042d044138101001c68052034900d80a03207440c43c02565802d090029004001742c1d40c48080540f10540d8040c030341070420604020003220605541907030740303803c6410b022a80c00040d8200980d00d81 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 206319964 1250 206318714 206318719
    0x18120b1014130b1e1c0b0c0d0212090601090b090c03070c050a14060601030f0e120904090b040c05100203210a060b030a0614030a03020a080703020c06120108070506070201020c10021603050c 83
    0x2800b603070f01740700c01090091000010520100040030444196080d0042c0ca00710344010340041c0744c5003070b40402140c25201211468116030240b40144500d04042c060301110560941c4c101e0f030103080c607060480290000400c16000c1042103000401440710402581a0040d00b10120884401c40c00a4003921100300701c80540c003084c2440306003a11001e41e0b10030302d14440d507220064540b494000305140040e07030014100ca50300075110828280426041c0200354041c030f20948a42c00705901d40002d024a41c0d112920321030942d04184002c03001400d0310b04140a420800d480b00c2841913440c1c00503100181070340c0c0c1140d086644040100044441ba50b40720406803a0302062034040c2d0f103c00c2080542d02c601a440c0100182c0000c88001d000507034260180042d03512900540760155501c03004a0741d01d402214240b000300f403c400040210500911085024120548080c1e00d010302c1600040e41c1e600da1491380c540200e0b5500e00001030a4400c2c80414042c00420003000030886d50703818400d54502c0c07010455031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 206321214 1250 206319964 206319979
    0x130e04060b1801060c0311070b040f05041107051f0603061e0615200c032506030203011406031803030c0a1106010303170718120b1014130b1e 62
    0x150342e1502000241210303120781da880194441d0350350449041038501c038002e68610138440c0200384600f4600c09000500f01c13544101e01068a40000c200649002c0708a0158a00c030400406c0041303140820301c45440560303000301c03012500706540f5a00090405900c05007400f03180290382d01140f860be111120340075140da0018002a40c40d1121046070403200400b6101003800616071070300d24080c502d21094907900390000d494440c1218400710b4181803c80d010320003045200003402c0b40d81c408200800c005040d05d85021805c40d1f04114820744a10100801c1a121341c80c00b00c0020401400304141581210200d025070b03880c0d0503c8210401c054004c0f074a100d011a06640745604a2800040d10324100ca40503600d0003031521211004007520240a444a02004a600040c02290740c664941600800b00c1564071383c40c081c91828520403155002d0031466503107102c0003041041441408580c0c501c060100d696200f11980d410f42600181881001184c0004200160f1030924103c230800c111400c20594414 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 206322464 1250 206321214 206321239
    0xc0f0c0a1b090f05100614190503061002060105031f020c0d05090301060e150906120703080a030b01030509120f04030c081b06071509020a090e1605040c0206010902130e04060b 77
    0x4509640d0121340c07950f1807120006040106522500c00191080e4440d4051f528003040c40301030008000c110f8000e400826000401d001c1a401d081d01d000c1072840300d501c0a0300792941060002500e40d0030148030603101500c03c02c1e01c51890700907030303041302c9413100c0c0002114041300045030040d1040d0003c070742d094480e500c1d02000150320f04503032510911a039105040304144a16800821a00d03010150169410403180d04075044041e00400141e0f000d14021100c498442c45130703030001000d4943d950100e504043c20b040500c078400d0781c00107807440311001040200d81c0341e000c800c2c00342c1ca00f4015640050000e8100c4000043c2c1c0503004100c03000340013015890203218848032028001a071017034080040216031071140c0e03256106010340c001c209581c80100020600c1c1e5440c40104280d03000d10090203101e4125110202d000c0c4c902c04900700c020301c003d030f030b040c42800e103180030103500c5000512038203150030740000e40f001e4040c00300d00c2c1010140c1200813a0842c1802c00e814100010002024404c0c0030f15500c0b410b1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 206323714 1250 206322464 206322491
    0x20c040f0908070b041e0807150e0a020123040603090c080109080711030304050409060b2803060e0c0607050d03060e06060406231602011202030c0f0c0a1b09 69
    0x40030714890704400b80501c3d10b009940e55020031007008106996440784000300f40e036a208202c05410285001d619540d4852804d030800d200f2100440115a02032031505141d84000798022400c25030300358090030301d121840f0581800180314514903061301c1c4580f0703001501045031038155010303119042c0681d1500005a03101c0f03540a0880e41c20f28800f40c41d0040600c8100002a4000c45030031484402905407424150b40f500418155618030278110748031a107402c0a241103003040c082d40c481220a020342080101a6422a40c514500c0f60002a004540350b9440c621200c404001001703a038840030300000c1e0303103079218106030fa01c62407403007501000a07080c954009290258509102d02450006021030701e03161030100199014200c4030100c180407401b08082010030091000a40350096882d41f098005100d64800103000010b031b00c52150010744113005100e83c035000c20080e2400c00180b17200a550314840402014503044040d00c009040d400342c1100e0742e6409a20b000c48204481c858407045c0f240d080380581 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 206324964 1250 206323714 206323721
    0x60f06020f0f1c170403051903110316031401030308010f1e0e060d0b0a0e10110301030f0312020d0b100507030c021005040b030903180a0305120706060e07020c040f 72
    0x8110800ea8400038001400c0c1e621485030401101807818000a040b1300c080f80c4000d401c00455041d00031072004a03049100da800e045412403400500e150070001044082941e03070b024040a0519140059a03101c0704142c10301a9102c0d640d0145040e440c1409584e503494010031601b030900415807140000400024205441d503c42da080b40c0c10100918052030804d042e20001000050085511440b10115800840c28082c0b00900805121a01140c810360340758045282208004407400854501800c0c5816444c3c04801d583c103481d4840100c1d07170201c0312403e00301d4180c41024482005103100042007071000e5030f01c0d801102d0f00007017641c4c0654441c1b0f0054040c0c0b4a805050005004101d583d200c01006141005118603201c00906003182499110141000c00b60011142c40d42c10754000162800c0008800d03102441081d421282c0c0c0d00841d0075951800d0302d4035194600c1120741130740801c1030000c01406801c03100c040c010080e81c0b19030b10325240130001d5880c410803030401e025074944220062118413601 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 206326214 1250 206324964 206324983
    0x8190908060c162a0e0702071206020f220501080f040515090f030409140f010506043b060f060c07051507020405010605041802040609030206030402040f060f06020f 72
    0x1d03042d0300b400d003841d0019034455000f00c41210322080ca20074030004070781d00031042e40307000d14010188001e1600f0007a81c0a030402018000340306641c8840d4003046000c0d07240140e01c8043d688058003503240c6840303c501200300e0003822044040380014125a05c1c050044041d201c00310391013642c0c0c1c104c40707442c2e0001d0010400420b90f40981a50880040074403150500b2001c2500305141c10116400714010988486c10358205030040600203454610406400c40c0c003d403801c0e000440608152441d500d01000940326200754460b0503040301d0342174918034500d020110303801301e01d407402d41940b54200c114941c003181101c0f046803c54400c1c207400c0e01c1c07403250341450825980e294060b640140b41c902e040200308a148542c02000d840b05100c10030108005844500032680240042c4e111151694109a03d0f0b59005001c0c00303001001601c140010407050b0752080d045800c032a01070710340595070703240e80c0045000303080d403003040068140c10035a00003010030488000d20201d802d80da00752003024400300e960769150200304 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 206327464 1250 206326214 206326231
    0x1171207030503060d030e0a1d010f06200a06021204120c03120b0d0503280f0903060b060c010c02060601030f0204080c0609030a0b070302090f060c1b0a030819090806 73
    0x603c002040c07810320440c1150458000e0518480c03490f42c510010b0f4145009401c42903400402130348950014400704003150141100805c22068a41000f07c0185220303240281c6800c07600070094845003000080c403a181c1ca5980100c0b041d942c0b60303800945070b0000030781900c04036134a43c0c030825040051441445140c03c403a0b49640d0b1301c074560708648041c0c40036083d44d4a042e54820281003070075000400400c000c00381e148200520440910480c4d101c00ca2000c9101404000d00111500c044c25041e840300392441503030740c061400901110b040004c41c54034090105502d00962030154000c001035000551144604d1090b40c060100707203507501e07409060340104d125510341a40940810192843c200c0090940c1002c05011542c00e889581c850203410f50b810f9610001083d800101c9481c2820400079141001c83e041d1500c51616030f4a011803659003424155481c01d20350149115205d66031544000002160042c1e4090b440315810030052f00d400e42d04883c80c00114074900d47c00214914040b91883c480c000c203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 206328714 1250 206327464 206327467
    0x120702031309051009050f01080c06130e19020d09020306220b0408090307090501030b0a060602031e040b0d02040f08010509060112390806093003011712070305 70
    0x2c2c40c441030041d1401070143d040b00e000544000c18124442d11400d80b2543c20031051900951400003074509003000e8040c03050052004000b42101000030310b540c60201c031041d12052282c1c1daa02120180c03180d400c50140c0c42003500000e9280110344040d081a500740b4000c50581e50541ca0304c800701800700d0a41e101003a01c48000b040000e01103100404000d921a025100c014503120602c0c000078202491a080400081e95070f10051040c04030b51f00d041584408000010014641403101c042d41c4c03400380082c4c0c458461120400540b14070f40300003e80d00100112415552100c0c0f01c10341c4040a50440c2c011440100b100102c002114001401501c1c041c051074000741a141c1d0908524817002c0350740442c10756040160301142400b00510748000303044038110220313200790016544659158210316501c01440780d4880c0d801d104c170003080441d101d02c01701004201d400b0060400c1040181007a9818040c2003071040100002544810601da01004450ad40041c2e4003032100e000b010703001c580617500010380010700 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 206329964 1250 206328714 206328719
    0x3080304020613030b0a0605010302091819051501031109100f170c0304061b0e060a0c06140702071509030201080621010b101403070f09120303021207020313 69
    0x151000156001030024002c5840c003200062200b65501c1d890303008940c017500280400c50740072143d1007158050402441c0c1580307002c0741100002c0303030360003205002400b0964150101d0000d034003120301c021052030322000c01d005620b0400c184504801002a04501007414203d1078600102020203c4101410007800c0722007018003034104540409900300550140140d11220140c03041d00011203901c40c503801340340c6d50303a80e150500d040f01c15034048043c044001400d104071100502c0c0c0200c2010240c030f0055070120f031901d9070941c0c111141c00307110380040d14140c544100185001000400c0c98444c1e01180c00315520255660140c490f4004000c1e0200d00190782000c00f400107612551903681c00c600002e10b82402806220150f420000320068060344581d07642d4090006418400e240ca90801c00609029614035071800c030000491100801500401028280d038065881c09000503c0c0544284801081205481d01e00903000350f0000040001801c1c40c0c1c0000391003140700104031020880e802010218151 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 206331214 1250 206329964 206329973
    0x503070b07050c070e01091d06010b0f07021c12020a12080a020d1404060605030c0303300705070605010b09010c061d1209040501050906061204020d080f0a020f0601080703 75
    0x1001401c048100a030070081903480c11000c04c002e101400c0901a480d510354581101d4000310b40a0217540c08942c40003040599400601148039411265140382199075106031400801c1306218401c1300070b40c0802a0106429108214040351825512400e0300210002c03110700700340ea80350010b00c00100104c00f4141c004044600c035004040e0008400307007015082c010340001c00c0c07003a56020b031000e0301503020310340402051104a008402c0200419805130076107c0503000072940342e100780c0b5111003149004a4980c0816088210a0804c9200da489411007505040700300503c20f510440082e0343d424203250012a25041510403500c2104058651010702c654940d01d9034064800402e0b951665148210314585141041c401000d80081100c4200c1d035410404042000b21032040c0c00c20345c055840502000038a895000c2154603c42c0300c0c0d41100606d5980344002600109501c5008013040d0000c00d4400300070400e507001d03240700d081c0f0383c080c1c43c0da00d41060101a0341d50310900c140707a100d0303000701d40c10804203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 206332464 1250 206331214 206331233
    0x618061b17220f050f060c09010c030c170c0d1e20011104080109020a08070e0705030901020f0417010b04110306040c09050604030804060206070503040b16020f0d020f0c0d050307 78
    0x840920072082d61039215503d9072084901c440380240c80e00e030044920512948800e2103c5944141c2c40d82241d4104001c02c80020014603601e02c1c000c00f4081864600000c2c089103102098a160125001c59940c41d42240000e4898800da2050740108a10149550f071044052441c0b12000020366a040310030000701040e0fa94140080e030021115560390700394059203c10700d070020000740003135100104440c0d4592050180b205c801c1c0c0d12000c13868200400603c6040580c83d042e03500035020b032400680700d803075502da40c500a104d90641501c800c080010005000d001e0352100a08105010008100907600c1c601031001745c903440720055200400c1000018107501c1c142c2d1150200b15124600b6903600340e22030020502950081d001a1200140494104152541081030a07802882441c2c42d50441c101560741c903010a4000d041d400401c59165000c0440718403c02400f5541c6248a0841341e400c680c250003e500c0b00c1801d00010703c82d015050380071100d8186039203030f0405030b540400154908541901c030b00c00c00713 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 206333714 1250 206332464 206332501
    0x610031509080c010c020c01020717070902091906091404020c06010605030c070c120b01150e04020711061617070506060402090f10021006050405010308070204090618061b17 76
    0xd0b0406110309081c1003024030840c5140c0605030014402d090041002a00e4030100e917000741004d052011a2503007000b8041100c60480c0c51140c00980c407150500c000803825a0303907a02104011021190000e0620f6000960100b1980c88016048000030003400b0b22080e44070b540101380041d4070038401003042c01c0c802c0d00155804580e222615003010714070341c0c5900c64040158000c176a0503035640c50700d5091290503d50b040c0103103402010210001c000b0780c2c002c0d040c1e8429030300303482c46a940419072038240001030036180541540202000e90300d0012410078440d4404c105402d0350142002c41042d980c911904c0d0071950f049820000400c210f0341c40c0303001c002c0a54050010180c00c8103200c0e121a40741d8a82c40720000d0445d03840c7d0050089001e0700a0041c0c00c482c201c0e8031051003203040c44010008903100b003049410f01a010f56000c81c0030350769403e184000c0d0054007400208003a42089510a000c6180c0c8000c8000c074501d0408041a0100d00080701d21f400c464521910848100d00030481601c40407400302003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 206334964 1250 206333714 206333723
    0x705040815061507080d051003050a080703030f02030703150e06030718060521010b100c02094c030c21050d05040e0907030507061202090d140610031509 67
    0x380d10b0f44807448105640081c1400c07a50300c040810704008a00440c011140c1c00031654564584d40c43c9075440d0070307646e0260400007400344000003031071f0418548070780c122001040300d20300203640c0c03414004070060080008000940007145148404600c4260307040f1280c0c01403000038000d00c1e0710f81c20410002149594081d250003c156103110010b00c85d121000480803200104450441312001605614259190710050351712a078155402c5854003500040c07004d50843d010ba40c0c809041d51016a02c032a520000703114014442010a0902d100f41c0341700101200d444800c0e18442c404a000d0065410000107a02000b003110940320402d0280300250a20346c2d990a81c01d016800c4880700c60344400c0d04200302000503000040e40042c09002c2e400d0603860058000d07844100034404240b4640300d09448814501440c4200245200001d50074000c54060303480506004102e085403400c103151503203480028502c054024056080041d100b4034919040720100c80d04070041d0186084111038040040001d0103040300c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 206336214 1250 206334964 206334979
    0x41115070203010c0906110f030406030e030705070f0603141005010c02060403171201080f0606132003070813051b060f030906040b0a02070804140a120605010509070504081506 77
    0x400740e9400d000c0e44c03030b203c0000d8132001c9003e820180010b116450413004060240c0c41501c00c541181000422103080781d01c00c0c82d0000d0300c40502c154030b50561041c3d000250241c4140c0001241d07a103000c032103403012118252800c000e10f03141d54400d83d20742d9000f118100343c1d0580d165000c12003540641f8680b40c11030b100429052070b160b160b41e1484250010406170580502d4003141103070400304040d92141c050a0324800402040b030100c5c0d0015a1107130b00a000e14007840f02c90301011180c1009412441c802d0004c200c09050703014030400715014a4001b101c44e50006060000420482c0300a01d406000140e0004050400b50b10465600d0020044010485401050410950400c400500040c40c01544c036000640790b1030520382040095950054484c5c0d1005c0d104202042c0064040000c82d4121055038600b503082480c2040000c0d8200f010b6071190000041100154080101e954492410f907201212418815282e001046504c0c1c020341c0078000340c0794054654104030030415206070b68003480081502 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 206337464 1250 206336214 206336227
    0x50f01090e091006060507050604031425020907030525170a140604020f181f0c0b160906030203100807140a0e1b031b04141206041115 59
    0x7090314080b40c030394205401c0300f10100c6500b81c8074010000108118508a0705244440e00e07441d4441e00060001000c0c00900c6008401e50360007030b42542c2c80c1080c500400c00281d0f2156034401c0c1c0032144568103c0c46030052f8000166014020b10a141c00b40401218034000101c401400f40c1d0712220880c054800c1c0b11840880c94402d80480d05803c0c843c03818440041603905508059540050010348201e02c100e00511011104a00d0101034402450549800c10940002d050200e86040d0480d900c000040315002002406250081000c410341c82c4a5029184666624040c04200c030100d40300c1000007030038505003006494441d07000785802603e030b92183c0030b0182d6138102c51880e1808130741c0480c0c501c098980c0350f68558904061604010400704400361030342e19100c03000d0f80c0ca8840790405080e4074680840400c1c1c070000b002d680704101c0315003030701807658654541c20034550011040503e207100d0b08403000c1d032203803818000c01d40d03900555000c08000b03444c0c4a00707070400ca07500701800f4642d60ba803182070140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 206338714 1250 206337464 206337479
    0x130b1f0801090c051f1d12191b1a071a010f060201060602010207051020070c15020c0108060f030c0301060e0106110a0c030609020f030313060e0307080601050f0109 72
    0xc0658841c0f282298440a07482c0206200320380c8483d01c42038032410005015450000d8018581d9042c0d42110440303000240310b4a4000350032022034000e0740140e03210f500030800300540d60020140300c80d8040c4020102106c000c0c03841c41590300c2c490056082e002c28140c4c03861400031510007d8080c061003030b5160620b0340e41000a1144220090b401854002c1010b44200700d80351302841450007030045480254138120786600e0b92503883c0703c2c8150b0510016074500041c1094510521100c25980e038581c0c01c540e0745d0000d07051101800d051800340011403005071140c01121800010140c41c40380c0d06841d00388895980d9002c1011031102036201980600071b80c0882d0405a17020310900000c1c0101c7d000c0c86041d0b5040c684000c101c0c444030380594886a200100310000b140c4a40c2c0e4a40490b6407050007c01c02e8038291003c143c480d821181e40b117400d840003007000c2c81701840b01940e207000d03030b1210340d1281403101001c410142c0c0c2d0201403081100d41e402c0000148038600b00b1420141d00140306041062040395901c59 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 206339964 1250 206338714 206338721
    0x9050a1208030c1b0105150a0308030c0a09231309110f0f190312020712080c010906090515100b07060e0a080a2016060509030a06060801060e130b1f0801 67
    0x10443c885d940d03036010081c0c0c004590f520f0891603601900e110222074210303651040c4610000d0072100d14250045103051105203e42c8418000d400b510a079040544c02004030360385402000c0c0c55091207030b89800c403595166a4948100900140c201a00706030700c07031084092101450100400a8000003089091002611090051401000b4001c0031900d46071850404c98440003a101000c0119040540c00300a4400080019a00503400c00c0402d0b5803840c803111210300502c00e0347c10060000d030030000300c2c00c18454007040c4810883d030080202c0b540342c0e844103010f101071130150090066501c0305002070008a24564448010f582105085172620079451b150002d1a0f00038551000000c1c0c001601c2c4c021202488617080f1a100b0410010000c034510801040108041d90203200200030300841c40014a940420448005e9a007009003002441c0d282c01203203020b40024012143c03a095500f01140c0c9400c0d80000c080c2c1c0303040d081541c22407030340c03a003515194001c0e01c903500364044c5030316151011514484c00e20 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 206341214 1250 206339964 206340007
    0x804110a030c0611060f060d023d0e01020a02060d090203030d0905010207030f03020901120c0225080c0f030c04051009020a0e0414090a12021e060709050a1208030c 72
    0x2265084d202e0003684803140343c202c005000c01c042c81a00e8040c4140340e01c0381e00c2100700340c55040381d0805007862444070b0204002055907209694440c1c0ca444446071240100c401c00701d0304407030740e10183c7c043c02490059a07580c00700340300250030610421218490388000c0e403094030602d2000b4207603440c1c040d41c20030000584404200a566513540081c1460400d031700980364600b5200f0609040d410600c10b600083c2840301481d247d16846903c40600002c3c0318406d118204507158144456902000c0280710008000c89500943e0014854045184028604a500c040c04004010010903000d04010144001360401500076844050a1040424038101a0010300340c41c407555507803504440c52500401007a54a06984014040004420b1000504000c5043d048041c0c0241c103c6034454a09034007286002c0b003040618018540064103005104408a42c4030300448842d6550040340740c40307008001090825110310b040350b8101c52000303000654200040d46c0d02c0588500721a090410700f0740010074030700c20030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 206342464 1250 206341214 206341217
    0x120304060609180c0302040b15070c051014040b0c0a0507090509010b090103050a0f15020d0b0f01090e0a0c09050402120415061203050705161e0b09010804110a030c06 73
    0x1401c0c18001c900180c07245401048644900305001c2070315032518000c801003800042e0045856241400c910b841390f90180400c44c469065041c2e83c0d24660404414044150003013910480d285001c54600c14402e500c1a055200045815480c092034142310505542c0300c80f12104040c0201303001100494414403010b0000e00c00c84501044c9071030040e49090850355029a0326119981803c01403000c981c0000394450030380e911040c226160050707400e0001c101e808802007001d0300ca0000940071100c052640114000c0c0c0019250300540e82c1100e80191021302e1140600c440d6070441500140d100100c54100f40d08000403070a114078913070748410104050342d100240450301c1941040900c001c01503603000c0343c0c400e140002e40c100370040c105003140c0303113551104801504000001c00c00c1d42c20303c401401000c00d8440c2c0301042e815034503511540080b440071002e0005004003c80f80001511003071800448256180503500c0301d01607900d42d81c0c0e080070902c0d03011115411079404c1700c010002941d0100c1d1000540060b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 206343714 1250 206342464 206342471
    0x10615080a05010e0112020906040b04060b12161710030203011109090a093f11061f12050a0b0108060108070609030510051305011802010905030f0a03030e12030406 72
    0xc01074801c269101a8442c00654801c0310040118003840d00c50003d20a604440080303040e101d540c0001c0103001c1e001c00007503000c1d00d00308000890800e80b00080030040c0350480380700c130540d5542c62000300546038031070403801145c007400900c10071168403001c1983c0501d20719014444140c41e500440c1c211107103511001e0001000103100000e40c81c0216040d50300c41c44640c000d0210701041d070b5032850304c0c3d08609030024207904101c542d1484502d8484121211703001b460207000c0322060304074008200e558400860113185c0070b407001094004884080d0443d800b00c141100d81c1380289008426100c20300340c04001d5605010b0b4402080000d004081054002c001c81c40042200354106140203007030035801e9122906001c0740c0d41c1c04000240001c17404a8001030784000014450741e030041440b2500d0401d41004119510302030b03a80070f94001007030400418034001e0360358146403030303d500c107040d6100c1107440d00f045075500103038448002074400c1d00408104800207090b6055204010440d901030341040c0c0d03040b20450b0f02c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 206344964 1250 206343714 206343721
    0x1006050a080307170c0708010e100c090b03010509070507020d06050106021213091a0a08030a081e040b0c090a062003090a060507110d03050d0501050a1d040501061508 73
    0x20180340e964040c1c1405405146820b03e20741d1007412010b2491081c444411020502c02080001404100014400300009100720700400700d01c2910384240c041c1c6291814900f92481080034402d001c1c4030251400300b900c0516503402e00d0100a0400743c010440d03010480704000d51001612080034618240384a14008502541020800303810a10301e8401e04403007800601c0300d485a80344081d00700e001c0301c044440000c0c0c02c0d03c0da09401007095034804016500200c2c0d600000610380d2000006040481c4241d0750201d0a4581c07546401007882c0e4200c111600d85000c201007404200c2d40c0b01e005e42c0116114450915001040b0041160350b04c1e1940440c000c1141508102e20050b1586415401a0102e0025520f81310307605001402d240b2680c001c05040207030100d2403100300090885c03081500000101100e65000a5280040c4294803007402450b40340d003031400001d020f06200060340c043e80c02140c0015400303a552440c0c0851b041c00240243d45541d25520001082d0030407186644440c0d0781541c403d0344a18 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 206346214 1250 206344964 206344969
    0x4021e030709060315050f0a03020303070b01150c0b01091e0501090c02060c0702010c140f031602032a190905010605092707030507230c010606020111030a110c100605 73
    0x19520341c080b009150500c41415a28001c090f90007061b5101181c22448200360040411032901040c2c200a4142c80005043c0701408142d50100f0704840f11070303420ba010f03e02c0c04c1c4003c40d803640d150b04004020303800410051041e0601d40d00b22100300080441b0710300e014031300055036000391902a032110051540d00c00c5484505a410301031107a0240f032142c400c610313215440d4002000c1c1c0181a00181001c0201410802d54000901c40310488164800413280c07140b20584407180300c080d500310300303e100c0c1c0301d1008082c24501c2d4100010429050117950440204140030500c00c5040320b034816013540c051021400329a245d62489890702a0001d50788081d00c403545801448045c421300032280a0f02d102d01c0204280e00c0485500040c2e01c072100740b030041025120f840068900c10815480308507117041020076004104030f802c010349500b0241c4802030040950380c420581c2203404604048410060810028054001c80e800010b84480409440c0e4545004c12a02e1828001e203604500c035501c5d00e03100104440d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 206347464 1250 206346214 206346227
    0xb01030f1b08040218010e160c15020306060708120f310201120c020a032003091207050a030f050c100e01230a03090b1f1404021e0307 59
    0xc103820300d010050548580d04805007220500400810050a040020115195210800d4007140d407003042d075410b0b5071502044442c0700303c03c0b03402c1418440c040207040d451601c20b02c80a001079800140d1031b03c6400501401c440a98002002250055820842c030340000314030100408240c0c2c80d1250b09280c030304080221195003040a00b0410361180000d0b0f45c100029601010900220300002c0c4400c001441840181c3d5994a1201c1048505141030507100c41c9507004940a1045072181c0d503036032005010f0021504180780c5103100c1240e1684140480c80550034044181a0011010f000300e51481c2d56a100240d00810140c1044505200f003100300d80801104001000c00020222404094200c480c1c0005212054800c0e1050400003210150071481500e00049003002da0094030035580c0303582010028029205940702180d4040c40e602c00200c5030300c604000481c28007501c07819400f80c3e0b89000b036009840800c111145a00c25401c0108400c0c820034031011400030a80070310680e403680f0306502c000c0c040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 206348714 1250 206347464 206347481
    0x80309030601050a18150302060706140a0501062007030615031709011b060b030d0c02011b0807170412030c02031506061e1b0c031903020303070e0409060f0b0103 71
    0x13404c0800003c4c00b803d260701807981c80c00003403214000380400440b803403100c0b49203182d0b02c081d400c140c0000c0d120f010700c90f041e004940082c82c07031040c45100e80c59000288041700d0092207104000340a001a009520705c0381c6503400c000d5034060040340e80058032a00e400e8111482581d00d2641032034129070400800005400052030301228008082c146203202c00080e11445d400d201200740306124841c0d500c1044003951010030711100103812110700c50000e01c0c0181c0006014038050f03003c140000503100400608407000103040780d00c4141c80341800e41941e641c401500c440b001d080100d11341407001040d41846d05500001e114000d42e80c0700000c01c260b0060604045003240c240011101ca2070402c50f40d0344600c000c503031103400781c504603180fa12080040c01200d0300035005104d0b082080258070034400300b00006c9100c0016000c80070390384900c59110003030b030020101240007000f503082440041d5459000303a110203507144000d0808180320010765250800c0b6150061004001907072030343c2510079540e0610030840c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 206349964 1250 206348714 206348719
    0x2270c0903102a0c0b0106030b011106041101090e060a03060203070219050610090c0207150201020d0501090b150c0606010518130e1606021506011701080303011404020f0a080408040f08030903060105 87
    0x3400002c075220038517020014020041130644030340190000384d05c0b411440000070780c50001c1c0c60b0341e41000d00d06100d0100744110701e580010303600030010500c0641184514040c4030b0042208002c1c0349556034900107904018014025030188602e40035401801582d03c1c21103510540240240b49400f48480f0503900c09600480500d900d07280410407003640003d011801c2d80c03401901403440307003403c0408a0280c41074036156180d4a041800009985a6540142280c4402294201e00e041f50307140116155005180000f402030f4054000b0402c5540148000e10001040c15280040850294080f444107101690001061503540b40c2082044d0002c1c0846040b0ba610300c081c220a5501d0248025a1050b03690340f240400540100495842d0303029600b0303129410150003e511856030341d0f2a030135807207800c2403140c0000d4010605641c1050b2a02d40b0880d1000700741c03607050301e0400035080421a80c0b003034001e100f120b40c5642000045400100ca12010005141c40c500840e0303030701d00303a405160420006900050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 206351214 1250 206349964 206349977
    0x3020a05100b030d0e04060906060e040b0603040503120405010f020703050711091302010305190504031805030d080a020306030a050f010204030201140301150f09090606050702270c0903102a 83
    0x2842e030f80850341454801036485c16284444003140002c00130b14240c0e00441903c2e280c0300000400ca500311040c0e591442c0e003110100405002c3e0390503c03c0c0c41c4001c0301d00a02c00d030000c1000440c000406121650050301400001900900c11145002207030700000b41580490000714a50003000289185007224140c02c0d0380014090030840d40001c0c5018104c030009042c1a110380015880e509100c400c80c0304d9400350700d41800036040030f08001d4900001c507000e007507160b13041ca500440c10707007000100d00c200200e1584d00e045443d560f03244078000940019181781d5260040615410100c0c4007000703000d40c001685400180d41d5461440003400c070050203500d01d0700003801803004104695017424401001882800d07c00d011044007803040303034014110340019892503d01440814056800409040050300c02d0780c407a048218002540f040f1000d4200010031690344a00c001048189a480030b4201307440081e04940795040000310b01c3e02038540107290f000000c00245123413540514082c1502200c43c2c89400d000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 206352464 1250 206351214 206351231
    0x80d05030415140705070501090f1a0106020705010c20130506120601050f0d03020a0506070503010603060605090d0213020706180302010b1206041101090b1b161d0a060e010303020a0510 81
    0x8052808000d0456040c0000421086c0910600b0f421a840b0703c0d60010010040fa109860882e03520404045004034610581c0008125940000f56002c15100705071a41a48421103a658020010114048590400b012030000005445112401442c0c100b0b80601180520b01f220511003044031a514545a9500c0b800c010131940d114020300300034800051710800034281031414164074007565488024800e00c200300420a015a001700030b941a07d2456506100c3e40e40e0703c100840d55401218a01c55001c80d030b120000c4018600540580c1c501001c100000d4201a015210710703003101e4115400c02842c00440f00000200f45d07081c07040702c281340401c560b580c507501c00720401c5a031351f0300001300010080560b000051005a010b946110300412080f502300340d8420100f02d6003c842c0c0b5000342102003d100303021f241d01c110f18140b00b046080d580c0605e00794040c20300d004551608510060304508032540d40d2180415441860760382180618000c1c0c0042402c49654a407051034403000500304000c0c5880d00071107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 206353714 1250 206352464 206352491
    0x5090c030a03080a0509070b0d050405060a090203030a23041e050102010504030516030507061a04060e0106020a11061308061b040e010b18040501082503080f070309080d05030415 78
    0x200d5801c003154400024086d036440482034a0519103400594103e10302285440b1908100d4000d188658861029103109465412100301680e49450000758507030420b01c00080594420101042707005a20039071031140d1940810300e604240c0c13140d00043c842d460041c00452800c907d010040b00100340a100800131840c6c1624001c1050280403000850400b403c520030007170510840a955000f07400204c02c00044501050f0392610000c580c52071130140d0704080700054000c0c2c03039580e03160403182160043c0010118950b0b8043c0c8008400c1d40c2c075580220248445d80c1c048c0000d0183d031001c1c3c20400000d04032400c01d02e41031006005254031006000c0420041030081d82151902d031170460b0420340149494881c5084228902501e01c004140c01500e41400001c004c200083e1040c0c032940506044000101100700410f501d001c1400083c00100040000300b002103404801408954024030304030841949510445007480e40d10a400400030300c3c00300601c01404108a50001d8100c0c080f0020000302d00040314 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 206354964 1250 206353714 206353727
    0x1d0306010b131d040506150907030c0314040308010602070819080c190602030a0b092203050c0f06010501030b0609010914010509060c0f060606160803040c0801050a05090c030a03 78
    0x18110554402065a203040c411620307101000d050408591900c3c092024000b440f030340d01c200c6056401d03200d030401069581035013803020303850300f24042e10f0018170750380e0300400358083c1910780e5808040541c1c400e14001d10f941d0340e51000340600c1c403959034841da07075240c103d0081c945000e6400400c445e4010b44003c202402c011245a45140d900c40c408035118070081c3d0381c040c20f01000500c2d8107040f200303014205040044542c0154407400d842201080b244143c00103009400904071400030441580200b40c01503840340ca0007010b05c103031003450500d1410865103142410007050a810700740c01e80c000e0300140095a00b40c0a0501900e00a43d1418140180440003d02513680d610500c0d00300034030107541005a074070171001c80e0400500580607698404206000581d10b002c220f0000e4094010340c5d010800e1072504400301d031241130300000006481740040d00e0304400c0d03610182c01104c0154601500082c0384200f805818801c04080070000344500d005c3c2e002509000f84025014826046543d810740001d0b00300a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 206356214 1250 206354964 206354969
    0x30e09010b092e0c14070501080c0c010905030a0c170304080307030b0402091804060b0405010e04030f0c02120105071101111204051203040822050f01030c091707061d030601 76
    0x72034807000d00158664100a0158006103801d1070b01d1541c2c42000c060350020455071350b01e0b11440002018983c818400380e180c060340e0081c83c1c00034a86401184202c2080d202410804094030700010b41d151180d69018a158006101d81300498503160a41c001d2000c4a040e10408000001c07840746107182640d12940140710041c80f000a0564403e01501b5548541c0d05840405101034008070624090400700c42c8401d100b2681103030801e00304400080281054007a0a04a0360740701e840111130b840c1d9035419140e00c600103511608010005025001603076840c91175800100d905000001c0794103004000170b001882091121b03060340c0c1050000c00c040750b011011180349800d24a44404141c840f0714025040c072a01c080e840b0344008000c401c1c441440402d60041158005c141c0c0d541140d21701d4652844008642c521039142c1c02803c603007413644c581d406504404807030011403a00b03030607254894010b42d41d14201d440d40d00405074840c40b428401250800e45081c60300000b032981d4180c6500c8880025600c00050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 206357464 1250 206356214 206356219
    0x1204050c100e040213180905012a1412040609030f020c0105031b04030501050907060207080c010206220f03021f02041202060a020304080f030310060c03090b03060f040204080a030e09010b09 83
    0x189416500713030022204001c0c0882200003a02c002c0e004030100090038203d1f4056809518000d007100c0c0b280c50100003c0c8000f1540008582c08024004090360302000c17040134080801410045080c81104109207140b040d4880c0c02c0005002160b41002001c50300141d4400003550302000c081c070a10f80e00203083c0c0703501c281680c614030740c20382541d500041c55000303544c0000c007258241018009050070100b111011383d816075080700c503225528101c035030b91003d070b41d89503d0240e00b00c2d40c041500342555802c81208911610b15032000b0107440c0e40d03000450302c0611382c1580143c20005861390a1142d680c40010280004c003025400c060804802448040c45c01030028407424001450b000a00d0091044c2c4004050110a0300d00c1081c40300c1200e5220f610450710214100c00c1280c000c600f00d40140c0e005003005d078161b038170403103500e0500074081c00d15400501407a80c030011400140344903a44a0000704003500200c3e024000c0e0400c14034018000000944400e4810b04000005125000d003460584034080f104 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 206358714 1250 206357464 206357467
    0x1030917190e1e090c0720040c08070f0f11030a0201050f010b0c0601050607050a0f1412030702030d0f0213030602130b03070813080904090f050709061802071103031204050c100e0402 80
    0x7402e00440c014070a840e0000d04001d080c01c0e8a05400c1d0120003540c541701f41c1601c0901583c11031120881d84c1c000100e507200085000001e134200c2d00c034411440065010f819040542c80000c9602001749141c03c1446494010303910b40d800c001c038044013180c190340100052822241854854007246460310f03414066140598008a484018050104240304040e0b40010326410104080e040109003840400342d40300c003500c107842c00048212500c0c0e0840b48283c4039a400345041118203245200a00f01c0d0908452a00c0e0302804a03428051140310060000c500c241c400513900c0907024890001c0b036102b5070160403170344014410400e8a0ba08140c060768805225000c0304401303000c62034003c10900800112540181c500000b40013002640c1c14400000c50080c001c030f030940c2d9542d40c3c4080907076006004c6c04242c00c0e814445403032400d0b07170741d00904000c0b0f00c12144004146034a40210389550841c2030756111075813061083c0401e0220512081a0082c002d4030f010103026200003000e081c03142c06072213450280e03a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 206359964 1250 206358714 206358721
    0x8060a2f03040f081204201e2d040617150403030f0204230405240303040306240605031005120a0605090d0f03050609010501030917190e1e09 62
    0x2c5600e181e414258070103181c0d5100c1d515000307541c1945c0000c4404030f9210601e00b010300000a9040b01110320709600824802c40c200d84944042a45d40004440740d80040710405050b2041c0110754240c0c03040c0403034503441c5c0c004a00140800068540300d5002000030030024a2409105c40c0204054801d40d802100b52030098640d40b42c00c07001480c1041c200000349102180200343c0e0f200001c090301180d0520302a0501e0380040300100811102e0680d008560400840c2012545003503074004013000f500000c098078201680c80d1225400e65045e00ba40141e03080404554043e039100c940c507140050800303450001d040d450070410518200d01c1c1d81c002d040c468486800d428440510401114107129440401030002c0d0421011b8a5650704003198041c01140101f0040b100c070314800e104e00c500c581c10007000000b45901c5e0200541c0180214902900c00614035200103075442c1d8400f0003044030002c001c192420400b442c600043c80f22003000e0800d803250100710703104401035994521142c1c24803804c030340203034030341e00c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 206361214 1250 206359964 206359973
    0x31f023412050d060e040c0603051905060f0405010e071407030203121012150609150b0309070e070207230108041103070801090c03020a0e010303020307110301140108060a2f0304 78
    0x41d50b420703104440d0904c100826a9144400182d0050b84a6003089820b1501c8050607015900211001020792000c022610840400c43e0001900000090300144518054001150558000360030001c10340944100344074441d5480f841d110000d1002d405e406050100c0ca590007501d0b889480140010300711610049040700d203503125150010059500303100a6524986803410003814060f5003054101e04d01400041d4104040c042e0043d4500f0804070541098103249480c0e545400181c41c207402071048880104402e103074419094015640c0c0d8000300411458961a6040000300c84032417010755400140010740790340c01c108015001640080000c4410305100c0c0400d182000c2903000d0480742d801d00c096442888103001803c8242c90080da0103828441c0c582000c8001e5031002c0c44000c0040e0320410410000c6041215400d01c0c0c0c2200400105968400040e1215124020b800054498014109204141c0340c2840365022010196604160b4010700a40045111022005803451680f00000040410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 206362464 1250 206361214 206361217
    0x303030c090e18011508030f0f0408031308010c030b1503090a081902120a0e0d05010902100509090703110a0309051f0e0f030702090103060b031f02341205 68
    0xa080c9031a80c4001440c000d0752400f1480004141c10a59500e4210341c1ea4060b52818440d505982c12100258a040201020503641d684100ca90021a2000f4003000c140404140003c08031041c8450340b81c040c103401c1c65803a1382102c2a450300b81090501d0324000402d00d0f15003101020502c4c60003400c03191250368040c086414100340c4100189020b000043d070080b03041010315082c2e000d0041d40c0c01c540c40500e42106000302e610440e042c240205500311a15285840d201d81481d0065205000114903460a94041407140c41b00d42c642c2c1d0082200070a0352001c07402c0071030010794030000e280ba060010b20012400e4000c2e9100c0c040b1f079070080685032028042070100c104031070390285054902101e00c104c2c46002c480014040300541c4080d6000d01c0c0c80e20500a000001541c01e4150020454880c0782d1a503951840100a2030101d5500f50140d0307401014581c3d5a003a51039032810f2032000140c0c0d140e1062034549200040810701c0040d880c070205071510390070040d0483c0b980c41c41e4809074040504110b1541510075 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 206363714 1250 206362464 206362469
    0x30403020a051e071a0328050106030504060b180c03070e030708030c120a02030a03020d0e0303071e02070e0f060102010603051204031704030f110109050a0b03090d08100303030c09 79
    0x80384545611521a00c00c1034000c2c3e03414401c000191500035845042c1d410b640c1498424280007400140f01240000c800011015543c0c8076800901611000c02240201580d400360300850109a81328100401c0c81803e0180342400300040755034035114450171801080d00300021705080071000021000a0f09507000e600c995200003401070885569036903404010703580354060680709a80340108030031038001e84a403000342e071000c5403a900910b0401c002d0741422070084d00b040d4032056956484554512110200340000e40c0100070035a83c94a2102c0650090032640c0c0341c0c03036002002c560204070104000c540f000040c0c0c0d002840000080b84584804004030f0140c0301a40018007140203418217002140c0c0c00c07038000c204a034800ca20105200c1c00c00c130341c101d086000c0d5102c080d20040090b00f0350ba001403801e40b000c043d2510141012400c1e551100702062004661790031210035818000700303100580d4000c208000c1c0b20740d40c0b860b10007a6031500307070212110500301e1303c4000c0526407540802c2e07281c14080d1105031302 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 206364964 1250 206363714 206363723
    0xf0e01060b090411070c0e040f060609050601030605010206010b09010e031c0233060108040611030702030702030c030a020f1002010912030501030210020f0322150201050f0a0b0f06030403020a 84
    0x149a101e4144100980c02603011610882c5810741010364410043c060b00d0000760041071074080d0354580718921201220041c01128059000d0105400164007449080f0181c40d000c14001201c0c5400c1e00054111409070300300c1070541d40544010000245814101c1c0d040440a03c1c0985520b400130000c207140403c44040c440103813406500f007000260340003e205100700d020042d01c1400e1a04070703040c064110705241b048048625448001007280d4043c0d810141c02c00e1003210001440c0f000c0041011050f0426280600182c01c000350100030341c0303400c100607940308202f18042c04c00744030264000381a00c0c40c58003040380514602c0306007a60b240c0c000e40c0031100d070540292000c3c0356424041d000800400d8240000c80c801d02a00803450700302c510000b0003403020002c050003036140c0401303000700c400c15401c1c80301c0c01945005400c10100ea1002c0c0a0f01d1814a08190740011405040c10b4880316900c0e0001803a641d440c91504960007900c2c2da8140f24000c0d01d0606694540e070702d48490070300f01c2c10200003110180 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 206366214 1250 206364964 206364971
    0x3031306202d09041802032509060e011517070519050c150916030614010512030d15050603040c030606050d0f020427030207050316050d060f0e01 64
    0x3000425000020310180c04103442c4496612858410000514200d21000b0068803080c0401c0406040c40c0e8081c0384000858200e1080140391030340068588041250000d00c094285000c010020489803410740280c0701400c41800f810f030030828080d1174000c05100d06c0d000003030810800e0b20043d004e0680c40d100c00c0c0c00100c810b1403602d84a4400b4245500100d055041d04240204c9400e0551245048d5040a4100409428030042c0c07190700d0380c0c0b80c90014101a2150103032400c0c0d00c441050010b052030080d4855080411846d080c0000d100c03d000c0140c3c019801980c03c1c0003600d95100b008411502040390350080007a104c40840744000c3e580f5001e4212641008000043c00300340070603801c2200c210b81c17160209009198894081c010b100c00482c600510381988007240c00014503246d0812000e0100b1201c079040c8000c10014418588451603a003a0056040000b0030311a030b0500340414012100035030744802e1400c1c60306021480c2c3c107003600c04c05014181e98820300175070750083d50000c03001c1689600081c03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 206367464 1250 206366214 206366261
    0xe1c080406030207020f01050a08041518030e090f0912030a06090513061a011202070602070516081b0109090c0c080f0c010b04050f07051602030105040f030e01030e03031306 76
    0x90300039031021344c0981c07081d940300d403c032851580301d10229880103000760f0350f44e02d0580f5141c0d076116000b03035106c0f0b60042c1d0703688480504449646d003040c981007035402552400c14554a5130b0034001c42e070074040c0c0031504185615082080038800011510106004c81100c2640c0b55100f80b0210002c24058109446041c00c2c0414804007265442c030b203800c000d016000030003842504294486240c05001c0001c1d01050390f18940b0b0880702d040b58041c180107800750b80098070b8103441c1d5642c01c0c10880c82d66a2a00d030407640000a10000c40d080010209103c80403001f804151855800600405850b100340c2000a0311801c891511038032406868490541c0300403229210781c0ca150300c5190365005283d8510315586801c43c0c0e88614030b440d009850003500c0108040311961140002141c1541c0016021010021500052401a1030904c9054420fa018442c010404401c81c034004051501001819040506105e41c1000b80301002c01200c1d0440115100744145003814a000e0f4041c099040103150341003c44202c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 206368714 1250 206367464 206367467
    0x210090b06030d0207050f060a030b03030a030212010803031905060d0f061a090c040527010e1e060a05012a080c0f03040308070206090103020c19050c0a060e1c080406 73
    0x80c24007540c01101981e08548803100100d03a206100c1c82117950014411400403014102500202400798581c9404240c1c00c101c0f40c003107895544800c0c0b558000a034001a200c40702400400c445016141381c401452a50800c05612113440b03c00c482d49440769665200030502540c0d640b02900c1f10305502c1a480701100346d003810080d004200c01e45100000ca80c1c1c1d103070304403150f203462032005201e0480520402d081c14200014401d841c02d2894407950b003040d02203035001e200000c00100a00038210504502602e00e00800d400e940b44001c1c0740754010344130b00324050007480e42d00c0b640c0c00000d603082881c0c002c0ba03650307203400c04070300d03806c0c5407450181c00b502001025418418041e0090080030085000c4a1800e540030b111280c1d648140c0c800504040340070300040006292044c01001ea00358140b40c0075040012002c442414200c1c030600d804c500c00b200c056484100541407081c5800040b0456802002601d8442d000d054206d00c034800508c505503661400301c0e10b20740300035400d2015030000a440d0700d03151035200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 206369964 1250 206368714 206368733
    0xf130507030605040606091502030c1c020d03062301050f1c060b0403021e01020106050a08030a080606030c0a03050417070507061b1a040c030b0c040611070311010807021009 76
    0x1a4140020700341000850075040c0350140101b1901103540714407003580351001404440741c1e0810b0704021400104100044100d040080340761030440014590304950305280041e1604503c2502c640905082640c20004948000351010a4200100c005005102c200004039401d2090703090b00c001c0300c0e501203280a10f408403003508040d04040c01c2c0702003040c152900144d003014061440001d510450300799404515490b0802404401e50040c00007207286034407a00000c9180041c1d03002a012940085040d02c5290341c00307400c0301e8201d40c0540b039035842c600300301d43c80c041240f140305607100905d5110f2021904210080f0061503d100310b6281280d01c078442d0340790843e190501407142e100050141c2620785c0f200a40c1c0e42680c520141e204000c401c0b0f0540d41040d19103040c4005109a0f8101201400040802c6100740702d0381c03261000c0d2110aa4035424100050280035901880040781d5105d800103200090381d0007001c026901003400c0c155155560355004034a05907034400d52454050070032030041d04002c3d0408 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 206371214 1250 206369964 206369971
    0x916052205130b010f150f03060b0a0c060b0a03020f0d0f02090405011b17070c02010e0d08031602030405090f220507031e020a05060307050f041205010b030a031202090f1305 76
    0x29551043c5981c1c07801e1028031a016401128141c0c0c8030802e07013a00d042c1c0245a41c02e40c0390700d81d007000300700c2e1136840c148168140c00c6001c00c00082580d40903030b0801c00c003c3e840360004141c0100c419620060564002c10724800f040c541150103400c1c00c8242e1003d004101d10035000e002d50041c842c00551500d8a0524007070b00042803242c1c0c21003884083d40b20024021031030340003208070604240c1d40761355960800300e91012070f024050381841044076182c802912201c000ba004640a014000d6603030030001c2140c1d034a91005000c5004642090006014955402e644d25822145024080040d51602e40c105001c0720b611101c0c844580905414000801c64049504d8088a00488000c00703501e0705c02002d20310300c035400740000b540540c2c401c0c801c0c440e601c0c11402458000149207009400c000c25800c42c815698440d070860100340d13031002d03501010800d0901078011501000d900de0682c10003540e801030081540c404e00d220240d0b4010402060f941c136281180c08000800408400c8a5541d07210650700a050a4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 206372464 1250 206371214 206371223
    0x1203020f07030317060f0d11010f020f0a060f0b1206010608010f1202040f0b06120f0702070f060305040206070618031d10030905070f0e0906091605220513 68
    0x1103201400e25200032481034201d03505034480c4a044010804142d0046100612096219074040038102541d2214403070255aa88600304510740c2c540a000054190242080c0d400308540c440700581d1080180419009003ca078850000b194560b8007203c103034094404805090b4110325140804103044e400090680d04039803054407034283c2130342c980a0203852190507000c2c0100c01140b40b80071000504243c2c0c0403808458032520005000154000011600d83c080401c1c0c1c0145414942480460110000d64079000412400180240c928120f0441040e882c01d200d504241581d0f8400141035454a20442d41d00c00d42c485801c00c1030150b12882001205e00d40e00e01640024a4030107114052010307901a100d0b1140000c003060402c82c0d0184040700580307041042103603140034480c40041c58800580b140c102828420201c0c3c500c0c1d240034050700b4035045000303008110302d9018840d0758007005000841401076403801e8600814080740400035030504c1c80070741c81111040345010200134000c42d5560107907440c0b903c83c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 206373714 1250 206372464 206372473
    0x3060c050f070b0603120d060504060b0c07060f0e030d030606110c0306011e030b070203041d0f1605120907050301110415030e0a0b0a0911010c03120c030b0a120302 72
    0x200221000e0045a010000001042020501041582c02075907408070005040b1110b080039910001c2142e040381c0c5491141036183d100511151900380500301c007502d00c1d102d905040041c074107401130307507254284a61002d00010280c15451140304083e0300c24020409812140100003a44008009242910584000900c0d00c007402074980c030b011428060000000f4000c240507405c02e022030200400302203940c800c002111034004000381015861612070760054020310384940c07a00303200400151520540000d5800c010f4104581100b521040c1341e002184e021011000d8050910700ba102440b40f0139030002c00b006104100043c05200080c1c580554105400920404c4c66103052600300c0d00550080f414103141800c00c04901500c01c2e8045440d034040c05040b03c00003442d0341c40c0c0700c4500c0c5043e905000a0394031070500100307010803031103240c00c2c3c01c1080ca08200e80e1140d07038a0080c0130900c42104e16032159198050003040905c207030400300166034010400140c0e180d540d150301703403c840801c0089015004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 206374964 1250 206373714 206373731
    0x7141218011103070b07050a050d0e0604120c0b01090c031e050402130c020c040c0207050d03022a0d0b0a0e0d0203031f080a060f06030f03030509070b0a270305160306 73
    0x10b010095450056202040d003006881d8800140c80681003810188200b00701406818000f0416005550000c5402e00c0070f004a4200b40c1400c844d039030031a2808034103000b000b407050400100c3e0748a4041c1100e0310300d400000c074102100c0044001d1b01c001640050000c841a054180e144429481140143d1084502201d10701c16001c4510a071045007035648056002345101d0a184d040582003001e00d44004d1040d90445500ca4001620500c2303044802c1e00140e00c081403803130740d14101e00d20540400e40441d040f00d02d00380c19100000c071043e6241d00e000b4222a60f100c081680200b030b07604141c03412050364003078480c44050010000c0d5690012180c400200a10107154440c8a1402d0020426104d4cc81c0182a41d40303400d0700c40d0005414400c2111007482e58490000000c1054a040d590402d41302365004201d900b010b121140c41c0070190703044541c043e81c082101604454101e540c2041410b580100c1071031524050000c84107112581e80040c21074050181e4000e06054222a0398080d039200b070604110000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 206376214 1250 206374964 206374997
    0x3120801061d0f0d020405010605031f15030207030908061305250303050f0c1603141b150d0612020a1706060105071e0305180f060714121801 62
    0x109011641d600c41003034800000c42e90b0070030742c45a503001d000250a40c14030410340d44c007040843d4026440500090310100c2401140000e0700032903041170110b8401d100310315041c50368143c0801e00510f401c0c41415070004409003058000d01d00b61009040e1202034030100c1c40d010070b01d0b045506090000701c1c1c060145c0700e500074404540710010401a00200b00c110754260035950107807055400081501e407909030920400c1002a4100590384000c150700304103112031841c61920240000341c0c007841c0852601305d058200340c00d6000344074101407803004458071034036040b8000b2180b03c00d20901056416180c20100040b40525105240003a0140f081e1110041c00d076950904a0414150309000c0c070b4603070000000318180d50301c110003400070640504d10b00580c445101a242000744500d500442c040741d00800c200c03e440e030030384020480702d04064070381c0c010000c40640020814403c0d01002011503001305510405c8010400203040304203206c0c080c099842002c4100107a9003145008243e00042c00c0380020610704 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 206377464 1250 206376214 206376227
    0x30e130911060c030c0715080a020c12090d05070305010203011a0705070b070201090905190e070509010504092603060901050f0f120c03070b120106020309010f1202090a0312080106 79
    0x1207070000003440212201004200302c552184040c0d91042c8000d000154017241c0501820b4000e205074258100303885410100075040000c010300181c0d80c0c0303105101d0448412408140d810f01c4003090784240b5560b400d208002500d51074410320282641c8a118008000c0010550085050382c10007407103441c280b41c1440c5004950b00c6000f00041184d00300500801c180d20b0050050081c5030702c1410404034407a202c85c52101154011500c988171030006034284120314440d44204182030070450701429120b8106000f00302d85c0a4184246070081e5901c113089018031030703e10301040480c20400100b0f10403c0c041014209150400d6440e1440b500468000050a14143d2040d403480c02c0c000d4070f0030096040000800c0f00d240300c120390030700a0b40909040c0c0d881e076a5040c482c0c0300c09840308442e080c1c0c4958000c1c5039a2043c0d28160848010740d8820014406d03242e0b006807000b801c2414034680101d09241a44001010780540d0048a40220300710402100300304518407144240c1d0b00e40c0d611060345a0740d078003048405 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 206378714 1250 206377464 206377481
    0xb0a0e03090112050c07060207060f0b03010c020d1209060c0207080705040902091801060306020f0c011b051e0c070612180b06060a210207020109060503040b010b16050a030e13 77
    0x100d46040504842e0b0f804a400007540207011005603814465151146c00a0368081f4000312449036540e16003983d485001c0c030130100d610000b40c00170010280740d41d030041d5580442643d400d0a001ea118490841c442143d0081c00800340d000034244801070320b08001a544000342d0090392100c0c05009808191380c1040e200e4034803031a400a002203180c0c2c03038152403641d01520000d00011030395258000800800d119000820703002d210b545200e030741d0301003041c1030a084591100f103541d07105030010b40e18108682e0042c140c0b4426004525905200ba541c002d003094071388584510001d050090b0000060307000c2c1c1101d00b1402c81a1131650901c10321a201600101d580c020030700080c107054002d0046201420b20b01c001d000201f001c0e090800d129646012044607594440c40e1144800742c00003a0201103580c4440281c00902c401d0604505508007651030b50071444050103a640038040224105054400703410350714045a82020950711540320f1070030010603030610202c442d405810103005200380e01c0e2130780c85000e20 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 206379964 1250 206378714 206378717
    0x7051509161a0c070608010f1703070228060c061407022a150301140306010602060609040f0803130b0c2802010207020a0905060102060a020c0a0605071b0b0a0e030901 73
    0x501a0506500d910080d5520310101c01902c0240600e480f070031000c2109401404403500c0e441d54661400480440e01100303604041e041e00c0c079180400c6520341001080d610502e87c1141c0c8426600300446141c0f901c50016a078014800c0740c001c40c0000c01d290012030400c80e0354080d2100703000c404504958103d007403401707640f0180140c1c031040d41c602829030100d00032007141d54003242180880c0c280328006880d07600c44180d0030156403400070040007500c80b000c4002d17422400139400f4000d15854110007944422004100a00501a0000003000c100c00c480c21910317040d0b0321000311601ea0401d50800408511080d20486405103c003010a144103603550a41b042001c2940310182e00c4449141d10290b482000c0403684150741d000e00c49100160b4480800c0d80150084560025592038008002890100060640c5480c5d502c10403085402000120b4002100e54020f0800704403500c504e0022074120384101d00050303204092519180402400100090241d081e040c0d052000c0014050516140d21a80c0301c00c90 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 206381214 1250 206379964 206380003
    0x1707050a0f2606040e01020c030c0715080c07050106050d05030a0306090b10050c030c120d050615040b131a0c06010e1608091c05040302040c0903020f0d1707051509 72
    0x1842c088244441d943c0190003a0010900140c1c04011509a0f00a030041070a96000410b80c4040d6540800c41c1c0d800500c40700d18100c1030f0701d42e04100508090400707450041581c900080d04001d00a0940240000341000307007003410001405d080c40f5890780c2054500d80700082c2001400520b0410302d00030007144000080c80903e60414004090b51075274001c0c50140030902050200c48811582403161004124021204564482d4070b6449003080303030b02c024421031044400d100800d5603880d01c0e0069805448660f1700d0560383d26099258060fa00c00c90380e0103060549019050004140443c401404800d80424219541a6210301d1103201c1c80745c04980b07540c028144802d2409400c1d100d414603070340181d403010030b40d20b803504038458448203031240d07620000120710006030030421404c0c80d01c00d44400070241e140c007040950440c0d0001e64161010100144039121401f641e00600c84050b081101c111480d1108aa44d6411840e1254482c84013412072103c40d0b44c110300107420143d02190b1602400c400d8203900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 206382464 1250 206381214 206381267
    0x904060b1504330f1e02070602060c030c0901110a170c010b030c090f100b04030c0617040312020a1b1406010501050f07062706050609010801090302030f09011707050a0f 74
    0x1111044540c40490713042016100e840760782250700b102c00400c040146d07070140001c40d09052001e8507240300030341070200410301003042100824000003500d540840074641041c807409002d9100346001d080000151000d1580356003e0b540d03a020340010104c00035031900902c48e451150302015190080d1040c82908095072200080442d011543e07a01d40c480c201c070b41e003511200e0301e0ba2200e070780304d8005401c03caa1515031804103210b00c40c2c204a00061015400c5444038188c82d140d9001482c04411800c407844403900402c0c80440a4020a0401b1a8080c0021005820551803d0004d11440050207180c410b0003900004501548600101c0d502e81c0400c1c0c1c6035902d050f9040c0d80750740c0180240001c40d010380e5209001345443d0000c0034070340c1d002e2a0003000301007502d0504d0020480307205010707448504140e15000b250800240c020083c1d42c4005191514552591070b10301c0180c603010b0855003900003250340c510411141c1c0e074000016042c490400d944007441079100b2042a54503008550707410301c020a141854 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 206383714 1250 206382464 206382467
    0x303010b0f0c030d0b0109050f1c03031b02010603060c03151202060f0304110306060604120b1f151d0d060c0c050706170606030c090904060b150433 65
    0x508010700030711501072030300000c0d44015040d07070480444500d4054807040402090740e0f010780c6110103844110f0380300d84044c4030000043c0340402400f26640341c0c2d800300c500c800c041c14040d42c0f103401072001c0b07003562404804041000074000c01c0d00d4081200d1083c68a0300c500c10041c86445002d842400c1500c09850340b600b041c440034402a080300301264080c0c42000a0308111801c0e1001c0c60180344030794015519200340030b08060400100a00b01400741c0070912041200c0300030000303142c03205504104d2051890311010811241800e00c85076991460000010004183c0c0c003103841d12082140355501e007801800401d0b0624a03260140e5001c56100349032145820101c0c80c5603010b41020300c154104081040320030b80e10581041c02e01d1303000c80d0100c0e41c8164079561004450180aa200104480745455842d20188908081c098501224002c80110b00003400f000816131282d840c0c00d070300401603200e0307002030011003601c0e0b405409000315082141d80d000108860001042240c0301009a00c0c041038000b0420 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 206384964 1250 206383714 206383717
    0x306080106060906050c28060b030a03021207020f0a0e1803071a0a02070204140115020a020603040609051911010e011704060c0e0a090c030b03030c06070c0303230405011a030303010b 80
    0x400d013030040014507c00030030742c02c00b6926001036143c000b44194800703047c039008903503d42d288140290030940c800d5000a602240080d40c2c0810030f60300c40d0b100c00301800454070060900c2c9c0400e4002d20b07252400f0034503d011b00b22240c0b080200e500c02c460760707407500c9000e07a440b4014200014003403843ea02204601401104c0255801a0880307001800d1410a8002134280c621680f040c07203020400c000148503030081000201c0803000e542c0000c03d030700041680894001d00c030041010700320507610f040d00f0302000414070112584c0600c042d0209a1040541881d41c10300340d02d904100c0c003007040102040095405090b02005881150301503014030342d55a00c8003009401030040d10b008024a01c4401c0e07260b581c81d016800081c0880c08000944842d90f10000f0b021030700381400492207a482072100e120030000c00100180d20400524110488010b039150503009080000c84c02c0811085001280342c0201c0102d400310301c2a0701420081c0103481130000034840000d800c01e0030b150190001c20041c002c2c25503010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 206386214 1250 206384964 206384977
    0x1a0618062218060b010309030c1b031202030306030114040201210209040f02090405011a0a052203050d020705040e0d030b0a0f0b03010e1e0f0601031515030608010606090605 76
    0x916120845100d11010000c66911001008000b00c00145001c14000e09105008040a0a00741040f015499803400303060400c0300a001082c2d0030ba01120b06200300003014454000359400180c40c60b007001c00301c4000e910b13900304841c2d0b80d002e5860708aa048a14103074051150207142c06031500b4810030f200002203840c4402c031390204078035290200300041003a01c6a01c900c0c08001075500006031a1030200007007009450301039101c40601c00244008510001d00c4900f180c1d42c9008905040e6a0b4440e104c040455008038080200300301c44415a0020510002144040034940240c0c295170505445108000840740101d49650150313000c44800200640130b9804600b050380700400c4e00c0c800580d140c81e0f0b41030808581e000603d02840100041001c2c01141455079084a16000300c24960000e29801c0850340b407006010201c110003100c08180fa0740d01a505c18000c11541100c2030a116803960865a900c034002d1103a035000038034080d40091003c030184980300644942d0380d03610136054038001e800ca44507040709 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 206387464 1250 206386214 206386249
    0xb03010912020102181215150402070f260406140702030307060618020910080c091008070f090510050c070801020c010c1d0a0923041a061806 62
    0xc00303000012401540d101014101e00d9800566100454601d540c0c210141d600120300400c020392110700144404145204500c084c6507072050665070f050b100f0241d00a4200d1038982040c1300240d600280000c1c2d0100101050145112001e2044500884180c0d030f50140085100c0300018081031148034451050300e03040151280b40300341000c9042d00044e04507400b44008a5040380c2d0b0300010001840101d030301c400e1503108030b9000c60130035100a0224140340d5400700c410b0100003042000801b02703480b04080d902081d0010f000461889502200508001010744607040842c9441c840030f1000b91140301034400391070000e00548030821062405031596000416a150107001d00100071a621b8001d2003d410090080d0001180306281018058200d22409048001040900310700c0716054640c1c1040070200ca10304400028520070b0034482024418441c5002243e103100072050009110616103184241001c04103080503540f1030204000840b17186c0c1c4968050040160300240d206c0c90301081c42d510503c2c20 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 206388714 1250 206387464 206387471
    0x507050906190e2d060301051605040e060d0501020703020a0213020915180303031f0501050c190302030912060613020301030f03031503020a031a0a0203010f090f0905070e010e0a06030206030403030b0301 89
    0x1291440d6644d8004034224400c2c0000902c1001040c0c80d0900407903400035028050080640d41001c3c0c01007444c450360254504a81c02040842e80c0398940703200f81104580c00000854507034181d450005c1d20f410714200300b64403e0f03500810000708002e40d40708072220310744010501740044003400f00c90040b68101d1000055400c029a0841266031801d1000354419592480300b042c0c80c505a404002c0c00e030344290809070401105214800413564009884842e0600264030755124609900e4124918400d00d500c4c59009080d0800c003681c845c80010b00349001c0c101c101c0307001c0c1c40310070b80c00c2424049000034031001c3c1c01d01965140f0500440e020b54090003040074841a020b08081d1280c0200703c400c99940e00441d0207001c030805459507040c040040d00e4020b0030803c8254a10b5250446600d2521094041c1d45080c0303542c1c0c200b40c480900603504c0007040710f51103810b5902c3e8681e50140e1200c49031003403050b441d01c3c018010004100c000f0b284910401e03a68020425815a260364070110000d10121000769010340d038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 206389964 1250 206388714 206388751
    0x9050f0f0301090f051e0a020d020d11040c030e210f03070504120b06030f16060e030304090606050703020f0a05070303030f020c06090d020f070503100507090e01030507050906190e 79
    0x41444c0c0a00154051801851401e01e15090074007030f00c1010100e4000c5811084d084c40c01aa51952810b1249404482c0710380c142440e8200020803000800c5815805454608071140e4187c240c5c1243d06001c1c141c00a4406000b0800d108034103808a041c440c1f040118100880304507220144c006d035402c2061450a1828a42c80740c48030010003007410400d941c02d144100c10011a4501008409404500756001d030441c104c030807520180300803d5000303c2041c003a81070078044041e10104181d9008042c0c501007446882e5541c3c0018103181e00c42c91041c1e006000300d0342c07010400da0303001541518082c0d2010081041601d140c070200c008051098800113503a400b00840300c8070582c100012809007400c00054618401c3c0040040e00d80f5800101101c0c2d01e40162504210603503010682c00e4242d1000c40b001b09241d910600112541c04041e0081c000c0000034500100a001002800100383c907410342d001015916510100080c01c039119510390000c1408440c01d000f004854915250005406000840c0080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 206391214 1250 206389964 206389973
    0x306010b040308220801050f0a09120806030a0f23031e18041e0b10080411030307120c03030c031407030c020f1203040b0709120308042907090609050f0f030109 70
    0x5d030b025100e181e44440c20310514168400c109504108105020010080140d0710b04003da00c261409a00784081080082c0380f9031010f0004410540e0f00031408808820a80b81070f030740301c0c5107842d042d00c001410b03081e40780002c0e0310003c112407000c003107034081c100c200d60310380318032055035110f07000d031608847c0071068560803902c80d0701030428507641140c459107412905a900004440c200c5140900c2900c500c101d40100680000300a81c000b60000d914200302c24109001c40c2c40c40c482c03130300002c040e4030a1000b1000c0065003e1004010f562182d5001e2220003007989003101669241c0101424480320280424100c0707020380d000c0b1032880c00d03038015121044120702c501410245014100401d20000201308070030001403060301940070226080c030b802e0715802c107910755414041d2450010244090240404c09202a800501ca081c1c010b02c07803881c801640208460700c200308190b0b0000d0200f03030802c80215880b8080d810038020741d0b0340038098209444002c810400d0845810109982555a8414620114 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 206392464 1250 206391214 206391277
    0x902010c0209070203220f050904080c061911040f050d140304060e0406120c0302060f070b01090903030c020a08030c0f09090c1308070e0a0b01120504050106060e0306010b040308 78
    0x54002e50042c68403404510ba0a20400e007502900400c46c070001001485070603140e20381882521000e035800082c5544900e4682668496116144081d204210400c011080464000e42140744000010712814292440720007050045000e03801060700d0415080c4001c2c200481001c104902a441c107039604280c0344030050441d03202c1d4005800040540c040b50b8150305082c09100d00604400c4503460300612680c80d090f011126601000340305103400074031491401160340070380c1c18041d0440f80c41d981c103503034500d03541000f003043c1c60080b40440c0c1445240c90906c5c0c00420698066600103c0d02840d6540703400d00c070441640800c1071403404101c107110b0300700701c0c0c1c40714118075101d09442490310350b43d990611030342c0c1014001640440e08943c0b04a906018110104000303541048150601041301e01d0700c04010399110202a0000c01c402c0d10300f10402040c810150030070003c0b11401d8882d18001c60341c001c01e158640300240950300c04900200300400004a55200070706a40102c10707161035181c84012300b4504d01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 206393714 1250 206392464 206392471
    0x70314010303090519030b150d05070e1504050402010e13061d011a0a0914060c060a1409010207020603060d02040b120a0b0c0c1f1e02070c05010309080403060902010c0209 75
    0xc003d00024006401c101d800541903000300351046210900d11395914003100402844907090045281d45945991510035814241643c40790a94031510340745d401180050100702c462045001d0b2a641c522220700b844e2155500807501a5600710007020403c0500c027614038071a41410000c0e90301d15000a0000d0b90b541c0000c000d0302850240000d551400804204908000d102c500c6424400c0100e200e40c5900320040608403840b00a4180c003210403400081c4440c001c08001402c41d004c1c0508001c2c1c440e0350303540041d40685511440d02031a86506404074200d0081c4100250000c0781000412160310b0148440b2486074030080c0040b80070038050b00850002c0421006280303640e031000c2111402c02c1030a03540c00e90f01c0ba500f244500c1c00c06d0030300ba99041e030314030741101c1e0000b21810080a00140c1c848075006103092203c0041002e9030b4504a00e4404000c4d4004442540d00b0480368101043c02d40c0710b405140180d94004030420304150450300c80d0001010b1005c001c80c184001403200200607101e00100c00e21 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 206394964 1250 206393714 206393717
    0x61a03070e04140106060f0c0602040b0c0a030f0f0219020a0b0c0d0e0301110f0a0201060515070201021b011707020a051f050748060e070909020315070314010303 71
    0x41800d0901d07140018202d0f21001030314036410040c0510800c2e61000102d844c1150518001d40c209955042c580700912541e0482d841588000a11241c1e210780013514404403442a82c50002c00c40f01131204581e00c0100c034200c00c0068129050901004e00120200501140018501001d15540c0d030f03c410f1041d0b104401010f101d03040700000020840e0041e8144082410942c000c1c07100c0541d29075090704511039030b030503124000d030046032003c650362003588008094000688480d03400407a081400840d82c0092000f2401440f40d048400b40d035815244100310f1010041c0c440c0410440701100005098100030f08050851003000ba03c01c01240041003550200b4010781c00e600c642c4000d91f610b90040d070b030008020074184100110114603c08422429200c05050308000d4a090401c50b04a541303003c54004520701e607070081515100600c81780350300020528401c04110707840d45650b070b160030098842001c0003035450f4201c00f002d0520b5503940c90096a00c107105103400180f1340d6100401121125080c1c10580 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 206396214 1250 206394964 206394989
    0x30601180801092a0302030c13090203010e0c040f150303030905030712050904180f080a02120408060906010608010b0708070606031b080f01112d03010b0306031006050d061a0307 78
    0x3030b01c038816401c18400c84a031030f135104109800d540100c0c0c2e5030a007500c040f6029a818500b48400050741e81c0c041c0034866070090007800350005030207032903a4035100c0b4004a88143e2900e0863340c00f4131580e1150517000030b01c800c2d001c80300a145440c150300910b4007010a0301e007400200000c800082200caa025186c485070b4175200e0f11061120140070854807803600001100c070326040c500b40410303140303002181010340c0000583d58840114030200d041c07000c402c0c2000502c03000032401282c0d43c00c0228003c0d103e10a804100e80841c4e0b0390301c0080360035040a203d003004140040101401049401c1c0003020818055038010401c10343e280d840003100d00964201e0803d0692180b41481524014025600e80f88813190007442001300100d107a02d018407030b52150f002081d55a0750922a00702401c50816a0240c5500c02c4948039070b9584140c0080d07a1046600910900071540520303010b0010344250f00c19200081c10301000119030307554840003055502540300b1044180140c0c0b40103540c080014001400c00640c002c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 206397464 1250 206396214 206396243
    0x60c1c090e0103080d0f020c0106230f0d0f0812070c0302011103071710031a0403091508152209151407050313020916020d110303060118080109 63
    0x102591001d81004114150703680040010581c200700b690301da29a01c44c00010b070448002d2600c0000c0c0f140320740c00e000302d50803c03100294035880d0020070b11000568000401292480108101004c19407001380781c0d02c4410000d002c07001c652090b08220000e0320540c1d0291800040c0f40f11a03409040c101c030440b001071207850a401c105a4203000d02c00728005102d2250382581000c2d0005401041c0c1301d61100700c0e04138121b00007405001000da40c4002036401510301d074a0310510075007039215040d04a03403d4002c00c0340150005191881c1c0c01d10b05004e250b036a9101c0703c1c1078803003078409509a86910100390784001c201d05d0100c034012030030f610410f0641c02500300244c1e50079503213446102d10f666561030f1030f01240341424401c8214044101240e005002785040b554a03070328a500c80808900050000e074001166004111003a10b6602060070440340c03e400312040781c1c0c00701c001100c2d04900d030f01d6559220b41050010840d00d50180075501c50301280400304581c4c0b030303071074000407800c6604001c01a500200a4510ad = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 206398714 1250 206397464 206397467
    0x120b03070f0306150503100b0102160902030105100f020307060c0c0506070201020c120c0c0d02010c1a0a0b2205192a090e0c070327080105070e0102150402060c1c 71
    0x769050301c091008290b40545c90000003a40340c1c0c9604180201264484501607090303032003400551481e0301c1c014a07282060f525848958008e4000b405824000d40390342c00300000c580e0060740d00d101c0840c2a54001c500d81852540c0d00000717820704003108014010002040300001c0d100b07008280c8154055400181ca510b0386c0d865581c9441c000b01c01c451440202000580c40110f40800c0c400355201d005d40c1c107001e00034141c1c0300490b25070308081405808900040141121030084c80c854a019440d0003406110201c41d080800c007005445201a034007280541608980c0c40b031141d0003c5038018400c69903111205403929500050f649401040a80c4130a00c040e00207442410a18860400031245003003010141000d001040900025058034544000880e500040521820394140c2015081d00e10580396040c0c200864115441805101c005500f0640040c140c81d1003801c00000040c0c0503801003401403c00401015600c20203401641c0040080110031641c01c001c10201c04114548807001280100d030b10070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 206399964 1250 206398714 206398721
    0xb010504090201050415051207020c0f0a050d1b090f0b03011a0607060e0a0f030216060315060c1403040e04051203040314090109050a060c030e0301050106050a120b03070f0306 77
    0x10961095280864020142c2d0744581510155048103003580e000124004041e00d09008495542c10141e08038400c014080764042801c1e040c1c20825a64860880442d0b810828103003e68026150441180010280031813542d040d1081d4401d071044e64080e01c20b895140807029500000309030b10803d9151451524903080034800c42001042c0041040042c43c0b40c20002204c40c0b04030308000d095551203101c82c000016040c03003448a801d50001d28115003410514019407503051480384805208020880000c24a010b40502c100c0b2400303440e21202000c0c100041a02c108030080c07826506003400d030f0100040080b003003008001410600540107224945850010310f001441141d45506a40030320070700001940204581d020502200680380d2650744e81c800403242000c0c2c40d40060b078003140306a400584141c01021404040d400380c1d44115051452a06040c03d03980c01f0300c5544002501000120f816a10603420103080d10800d04003c10840080c10000303103854016080030008104010b82042041090310 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 206401214 1250 206399964 206399969
    0x30705040c0503161e03051905091e0304050d050601080706020c090105091e010311030f19020d1401090803060f040c020a030e0a0905101a13090902041b03090b01 71
    0x5505111044400c031000340b0030300020b441950007000c403c0c005043d0038041c445002c030149110204102c28000702d44024040c1800755000184000d4089980404980381c2c0581d40c864a00c40000741006c15800c0010381040041447c96480c5020500c404607265a40368103506d140e0b80200001c1c00c055040c04c03409402c00300c039540400295030283c0620388082e19000c000c281161800c82d200b100503900e07107094480c4841074850302542c21000d0b2001100304482855039080c400300550459400301c5074028044c0d500d440304000d02c0c0445402490810040c030b03182c0340c9821076501c9044001181c02144000d00e013035070155141240d081c80b0100420015081003049101c008004035018400441c0440010351141d41c1c0f0788000d420450b525006103003503240d050702d8000410380b20354100301030f242ca000c0d60503405119004051148002605a40742c41224501340c441d52240d029011103101d20300500c0e140240074214080383c1068071200184038022480407840d22030740d280d4501190300e0b00146130403001d03510140c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 206402464 1250 206401214 206401219
    0x905120a24060906081c090e040606030206030f090c0a18020a0c1e02040b0114030a0b010e06040f0e010b0418050915040602090f030609071a09030105161815030c0e06030a0b030705 79
    0x1032041c00906901c4038400c022110a07111404c1c1c249c8450402d0f030058030303258002035007090001084c0410b044924112511802e525015220661200400c10045a5451094100550381a0b81341d494803a007541c000c000122942c28015031001c1a992442d181003a9510350b4100e844060f1568405d40c2003034007030030789d00210919001c40103284c4004042454000039000443c0c8940d40c1074540c0459010340c0c0408402100241010b0326240d89140c00c03884100309000304d80c02c1840e80300000a0314194070082d2007d40708102c0ca2480b0100303e98045200800c0018800c0350648140c106401e14000040b030120302890080c04007581d9500710100784002088080500e40c040c1c0e101d0810480c0c600804100d86056480c0c05000c102210010000105540103015209515502e001c1c01e00146409418030b4000311400c0b0780f5103503c0c2800c502c0100030344641900c030f00c003d420280c021168480c0e00c29070004100e00220706102001591f0b502c0821503130703001110524040f664802000b040ca140801c101c00092104 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 206403714 1250 206402464 206402503
    0x6091c02060103020607080d0902060c0a020f03010e06070f02070e04031e140a05130306020f0c160f0b16060e01050921040519030807120905120a2406090608 69
    0x444d400300e4140d01c01d41d5005020074401089282c011300c050381024205a4000701620349030b040c6160303407503160481c80a0492161040d100c41e004607003018060021118a802c000c0c1020303070750342c0038155451003a4464501c21401802004a11300c42600c42c035a00546c002d990b020000c0d000c4041c62411002c040e01181d00b44030f10b05c2541e0341da02c51405d0803101100c12a28003030781c407845d07400110000350869400040c00280003244000f082c21150001d0000e1114540032109500200b24031004400c501c0d000342e6090460494050040020080003800b402001551042d10060300782c45110840e07602c100502c5e4965161000d02a0b102e40030032101d00c403c001001203000d00c920742402039509101d1441124050402c1c610342100e10110703030701000300458000c0e1040380c1e5401a440e108501c46840000480846d00d03541011070300707080c6444000508191103004128805480d00c2c1e4014150824014410140d02c0c801094028000e0b0f006001c010101c0007404505c85040803511400c082c0c00c04c081c01000c086 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 206404964 1250 206403714 206403719
    0x60c0807020f0a080c0a0203030d0c0f1103030c0702130c080402190609051e0603070207030b010e0108100b030102090a06092d12060b060f09040b01050f0f13030506091c020601 77
    0x1c011544040466101000f1075460031051245804d1000490004c2d48c14000411749482e003682c25001301d48480300d40c1d40c03a8440001d02d440143c41c400010dc41007080c0e54400c0c00020400398034035008041b21400205040030100685428130b0645080c4a04440001d0001c3c00f80811070030300d0035000c1c405c00c491107042081c460500310014141035503489403611403503520061603032009284500078401040680080e5407450704280c046e40c4e070f03015031100301d92068001c070001070060b540035000e505a40c2140c0c05480c2c00c2e40018200006482ea0304a260f900d95420041072066aa940907180021316548d11880729080c070308582c03000c5112440d1f0342c03125210301030a40b20340107254052501c000c2d0b40400c40d840217030716900c0c1000340042c400c404000d904004000b9030011a401250b0240c280c4060464043c404c0788600801107070300d8099501d503144001c806110402034081e00c10b01804100c12400c008150b200d0396503d8441c90100300381c400d2411030304220400a4070100410101682c00c040e40001c0400d0752 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 206406214 1250 206404964 206404993
    0x6050901050904111317070605070206091306090204080d08060409050a120201020c010501090501140a05010207140d050102030705070302060f061c03020c09090c100e0f06071707060c080702 83
    0x22602400c9486907954103c644130000c810003e43e02001000e92190000035158050352802075040d803802c1e03005200f031244c0050081d01c90341c103c0e944241d01034601030901c8009401e006111000c111019080d5844000c00f04143c00c092000d44001d11202004250280d00341c140500841c4014008074059414684500041500002c45594003a80306440d401031441414041b8024010f07000307401c0e038a500301000040c030b80600b03801450681d0702d40c45641c040340420705d08004518903107219813405078100c2c00041040d448440e140300590712005e0000f00403820300740c3d25079007203034003c85620012981c041819410705504200342d95101ca4580301407441d500307201c000166800d001403c000629640d800c000c07420140309114100e1386e1fa402802109a508103440071a44407170340481d19502482c14403060202492040c000c000c10700501401e0301d005140c0040500a4a500c40042500d03848140c0d100e100e86902c070070b0700415025014080005004d09264002406403070042c080c0000c66001007002100701 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 206407464 1250 206406214 206406217
    0xa05030c091e210d1b0f050a020907020109050618070b120a0516120f09061505010f210c11070f080d0c0510510617060102280302070605090105 63
    0x5070718606205100300c8001400729841c5d180300c400105150240042c1c207080160004008a1a910850301401d207a40c840c0412801c84201b20b001800703a60020303000c6000703400350300c81d1500c0a6032640c05803504141c88200d00d44070740c0d0040070440d210201190400c16203040922426401151100c0900006100c13040300428003d2580e1400c0f11140c1d98019404005516038042c50b500303684100305100e2940121550001458540b10307071400300c1c03440304904d071203103102c0e46084081107a08000c0000790f11560782c00100130203100300c40506129103940070041144007000300200a10401e5a144446402c1c00c202a007000000c50300b4500f03104000514500064001c038900f007070700d089207400041440004584c41c014120060301003c1503080903120b00304074040341002102400030b40c4d014001c8001880a10701c9000b900d4840d140026061503801808621400b906a80010052040b1105800414214403500581d4440050b80100840f201c10070143c0500a01d8001c3c081da041c0a42008840c10019115 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 206408714 1250 206407464 206407483
    0x15070203040e0c16060606120b03010b0d0f230d0f030902060a03051005040c05070618030203040e190204060906170601120903050c0607030b120303010b0a05030c091e21 74
    0x440700c000c00e420007080c41004510014542104045c02442d1342c1d800090640103d400c4623202c890306119000d14a42414021000151005880300380f03403a8107a00c80c030458406820040707508007840c08a0b032180d00c40c80f131038510f080448400078102c1c0d254800ca0140c41035520400030000c1c5414040b1220240e0358910540301000da06080110380c0da80e502c0d9000940c041250486d6038031628081000c0348143e03010016000451060508108207260b007071a2100741d600c92800200164403c00041c0001400d40c0307039454001c0030a803980802a42070f0001130003681c005400030000a01e0403a402c1003a603900c14205038444460000138846814001c000922403142c0c01445002e050b00c410280e01014841d804a07203038041c541e0261022070030446401005480c2c4207102d580300d03a002000701c04e4001400300841c0d0481c0c543c520b18518060740d603101034841d42c000410b00ea2460000388440360326030303c5503003d040b000c3c0c800710002d0000e44108800c220b0030580f26907403004017080e402405040b50900140d80c114 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 206409964 1250 206408714 206408731
    0x9060709050d05100f0225020f0f0105070f03050702040f0e0d140c010203010f080c0303030108061515070606060908030708040506090f0a181a0105030609060a05040e15070203040e 79
    0x2240304a06102d0300d05000c00328a504004d1601d0f10540c1e460b030142d4060320443c1e01900c0c80711800c4079a6420448100c0b5007c00c06036100c0308031103554542d80b8001e4494070120006041c69400c06001c2c0d00c48144100400e60f06070085440003075aa000c6282c83e00c2103400500440b02d04000003620081240c0d0b5900e01080319409211902080400c08840700e025107901f02040b900035980c3e0346e110f5000000d0000184540c0d22a803064503c14006807401100344c9058030484da00500e441c0c2e555504401c5c4000e4600113581c0c1100b048075010030500d491600811401d07003c0e2201007034452038404000e06466480e80002a990024400000012078034802c0f10304403401190301c03a0325100610300103481d102c000c0307500c294418810b0200044900e0000802020001001410052482100c4035a0b06400c0298480703800540c0800004d4428903012010740e40000d8040e1849034901e49403800300d02140d59180040c3c000c0c0c2c2c860100c885070800c0c02800964040788605c040d50801f403910b4420002002c1c054014031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 206411214 1250 206409964 206409979
    0x17070f0b060a1518050901060f05130f060806010807030e0a0201120b10200316021909020c2b080f13080f07060c1e0302091801080706080906070905 65
    0x4800395152190603000e0064010711482400f10458090301140c1604241d40c0c41004201001440340340020441d0304a90454980311007801e00c1c6842140c0c04e43c45800c014002000300c441c04076103500b4109604014040c039464116103420300c2400034194080040c0020109420103485c05034440000c510208003960a091030280c0c0c1b0400c6c031599000d400b1202d1155003114030b140070308144646c0580c03954170004a0700c1e01461008042c1c0b0b411130b124424240940d1311140c003c2070300d4005080841030710b0b10942c1c00c661480100b80c0c4401c5608142c0e44804245d989035440141d0f114001e00350544142510380510080b00b00242c0d0144014050b504000c00ca1a0300d40800390002d0707001400d1030440d91482d80c0c08003c05a5444a07806d62000300d800500041d52010715103140441b10134022000035200d203640d1240c00c1e01404550750304030080d6100c0721207503400c200c01c1c968940860100d01d56050103085458098102a070600c1c0004104105c0105200c0456011078140900c00350450318010645805076203d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 206412464 1250 206411214 206411221
    0x10c020d020312070209180a0312020c010c05043b0711030a080a0c020f0a0209070e0d06060503010509030315041d100c0e0d1a0703090b09030717070f0b 67
    0x12580d10388030314065014003a0a2101c52540e116100520015108641081090710b81d41c90940c180c008164000384103501c0342e0149000300c4d00a201c044141c40145001510349802d14038154250380d46074110310085107001c1020710071074440c0040d5214400c180840d0440d40000d1503182c01140a00342c074060080b103000c8001c83e008a10410003003100c1e0090030101d0b0340d81e420000005100c0401201e07840e240d907140c801100c8145102003210840f0749400320042c05108540c3e020070a0070310700680503070b080c404078a01d103000c25118003003000d04140c000c80c40059650b10b00000c1c1820f4800050811031190810810001c04d00c1142901c10b820440544000a50b00540c07101100580206011520340384190700c110040c99140d030700a0f03820a81c080d03454004080402c4180300c2e203031001400090459605a1001c100760841040c0e40358011030034a80854414865143c0c030324540025581d81015400c0044e44200b4400c0c0d0b4200f15070843c0c6104030a900e032840c9a207842c410b0580741d0b40c006110040701c0c1c010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 206413714 1250 206412464 206412469
    0x2130213080c0f0d0b041e08120f01261c020109060f290f131a100918020403060e060403080106050304120f030e010e0703031101110901050d06090615110604030905010c02 75
    0xb0101e0a0750034040d0347d1000d5440e003000308180d00210741c0c2149030f58a00c00081c03418694501400d0481b400c44140e2100c8118501d156081c0c40b005e02c084030510301c24640341030036003034262900c2c101050b0076400014101450781000016030b00b507080812803003800d141065003041190340701030f1810301200f05401480445100026030754101803000e95031103110031000003a001c0b95036000150000007404c250101407035040c18070107510400312034000411840c030404c10032001d4032019141e5004a4440041c03401b906d07503654204039007a110381da82c055803144080204058004044038003505042c1040340c1036180541c0d072131032103c080002c00310030040a815200f110310302135000f6568001c5210002c1c02003914a24040b0381d200d40500c0194002400826014070504041c4501651684222300c1e651510b070030a801968541c0c040c80c1080070160355041c0c000341d22425441403030090605410694000140104000c006090000c071442d52a0449030a00c00083e40080000d01210828285004981c805000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 206414964 1250 206413714 206413733
    0x1a0a0b0307021e2e05101a070519050a030206090601180207030203090a081c210509071502010b0f060a0903230303010e06090f09150402130213080c0f0d0b04 69
    0x11810b0328144840300840300b500d40d1010000304c080603014204481d988102d00010f041c0304a21858600301c000705121440720b04240014444107001d034080f0740c1780c4504c1c2104603500340e803841e80589040d049218070f44101541401440d81152294001f86001d5040c8030503078a82d00e22040c000c0c1011a0300264040415000780b050340c2c0201c40080c4103c40b025a654170709502c4402451421080040941035440b030107014007000e101845211042c1c0c030b04990662003003402000087c200944d035111b00030f0001000d46501042075a20b242a030b00206e420100541070042d0002d00510203441000d0a100c080016903006100d102160380003140031204418061540344070303511010840742c243c00700000119113900e41c0413584d0b00424040c8c3d40c01c221503440d100304450040c01642d4800c040c0d0881c00c400940120540c90a0707802078001000b0040080b1640c6407201260f0041000500d4888044801c10204106104100184906a95952008076054002071101204400050841d4a16030200342440310888 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 206416214 1250 206414964 206414983
    0x209010f034806080105060f0d0c0507050a150506010903050303240621010b090604060f032901090e070212030c0708070b1005040c0c030c060e011a0a0b0307021e 71
    0x40003956144070518854140a072140110004213400c08000186801c4c154210741e10717250f03000c880341c7c109915507c4131130140040685c5401004401e003d9080844e0040c4020032185100300341000071000c0120a25041e102c004140505000803603108201140c13010007100e901c5400c10030005032101114045c18401c01030f601c501a0808000b2034600002000c5c0c0c541c2d04140c03004a4031142c80c40c1c3e0303200d800c141c1c0d920600c80c45e250018414042007105600880ca41d51903a0402d04000c105076280b9000a0b004441404896411555207103540b6080e58000041d0400303411110099851860400c4010790745100c1d84c1000c0302030035000000075034001c00f10001c2c2d4480c1030f485880070390380740581d080c524040c04050764500707800603c21600085526051185082600280c1ca034000d44202a482c191050307101c1503015200641c030f071a4410402c040c20b10a814402e6003210124541c03860131400d002e4440c023103030000203940104000784441141c00280781c01c900702860301e1810b1170242c24607100782401c42c1d030b1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 206417464 1250 206416214 206416313
    0x1202070f14150115050f0c1219030f0b010206150a08070806061201020406080604240e16020f06010b0c030417030715140c09190902070209010f03 64
    0x101601500c1ca408580b0300c10502d842d810412040c1d8076075a1100a0807072085070100801c100f00a205090340868010f003541400714000e80b42004801015400d041d0f20400ba071065a08200016044081d054456a1444141034034100031304001c1d00d00103903441e600070f01030801391002000507501070303640c0616a03c0030703102c0b000907217000f5a0389050a50755620700f5101c0520541036048801d007040e10510a0700d04031505a03903034065503120340c07040c4001000c52a0641c1d1100d00365401e0500b0098401c0d4245004104071000c0403683e10303101001d1040c201d00300c1c110400f1900007800c48501380c800040c0c42e5065603014032501d6562418001c01c10316600c959880003030000056014445d0080f804406041d00074091200002500300c0051228104c03a02c652103c03208860702001f003000550450044d000280000e05100b5040040320b070300418400041d8030001c6032940004044086007000740005004088044030309a019007075603070320891580720510500d1880300740c074084d114080c001980e00b500e90b480b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 206418714 1250 206417464 206417483
    0x14030111070506090706020607080705181f021b06030402130b1009031505011d0c0d15090b06030108060a020310150206090106060e010c1b0306320103031202070f 71
    0x224507003580c540c0c3c02207951016a00803903000248081c00031a00c10f224081c0c50303030b42105540d1501400d486a4011242035019040d100c507604c8690b854000030800f00c3c929240000301c3d11101100003d1405180c00220404175078524102015070f100e6000b030380c0e0041c0e81150b541d00340c051518100c0005201c0c2582c5a640400840e1b00801400c1d0807003000d009881c0141d10805858001800c444162182849900d0794140140000110b050500c4446a001a18051881d24003407222550005586900103211034503107070188108090540d0703203d80750140d101518201d0845d85055100398a40a0041460101540000008107011750302035406c1e018041044000f85680d4020300e000350740b171400300c0c0e0140ca550f280800214989004104200f00468160740d00380b005540c2d50b5030709a484030300140c100c2c101c205610001c000115a4002c000d15080b16100b080c10841c50803040015100c12440340000080e00c03000180040390348050409806000001d000d66104810301d024802c00001001c0070304980d04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 206419964 1250 206418714 206418727
    0xe1009080d0212040c0b03060d03030e1501090f0518030a0c0809090a0204030605060103060305121e22061103031305150108011b030b0a0e07170703060e0f1014030111 73
    0x801c4505000b03a005217540000d5984546103500d0501c000d0721000e43c0a543c4490ba00c0002c0e02c240c00401681011106170f50b008120720454015090080c0c0080700d2081d1545e528202e245000d01c40c640c3d00c040030110290a0f03000380c03e0143c0e1a4803520110000300a06c1580c1103060010440c104d40d0010700151020206261082c160b4000f5002400100d50150400002c21510b6100c0d0181c142540d41080c0600340002d15151000e507940e00c01c500c045180c070070410000c0c44005d90200902852004581103614258001c0d40d8031410321550f40003c42413060308010a2000000001980e81c094800c04480455081504106107071051260505084c800d58600106d1040e4041d0061555421401c5150344001c000e090244c0030703214401c20711600240940420002d40b04280c00a54014810782082d140d051441700d407840c00240100d4004010030340b07c00c800c200f403420384001c980d84030000c04104c401e181030444c000200c541d07191040b509100c0440c000d0b003030b081c0c0e0298030114440f05090310300da9035080d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 206421214 1250 206419964 206419987
    0x31309060e06040b0a210c1707060c1101050f0c030705010f15050105090907030605370501121e0603210201060602100207110603070c11040e1009080d02 67
    0x100d03600556900724210380c08106103060500903007649480090070b1091180c00d098100030710a1042d1102c20088001000f86400300d202c4400040103030200e00444825031710303000b513103519080c0281d00110422800000c41004500540080140c049003480c040d651148080203213540c0c2e000e101c0e03074000b081c040003641404000056005511461041c2c4050140c0e107198003000801419520070507022030001c200d01401441d140b852298032034454140012401c0d2a0000308104801d0f1800210101124120710194481f01d10a0780c03210341c05c02c850243c00782d81010002404000c4d03002c038050384181c850148242c0191b47e1602200c002400203020403242c0e650f410444445c002980c06c18002010700e0400044040c0306000d20026154103800610365400e0504155009500003107003a02c2172025803039940019074a5000a500814466482d441500014241452291044140b241c800c42ca051010380c1c183d1404504e1107200041c810001a80c45414101030105208465084580500c00900e00d50b104 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 206422464 1250 206421214 206421221
    0x219032105070e01020705030a060504150903050406031a0a03020108041401050c0d0605060f0702090c09060a030c030e0d0f050c070e01090e0d050301030c0b070503070204050c040801150b030403030e031309 90
    0xe03009076480c90000300c0f12400680c0c4820180c0101601508800c0c140004a0790580000750403e200700d2000020224210302c040491345034143c110b00081c000902046910b44c18091010311310b071251441654445c0c00000104c0c0c52185120090510500030000b600344013070a1907030350503405010000e100030324100480310030940c0701c0b08002205601e09071002c5018200070096440032035801920724070b415015020010080c100501448045800700850b0309039071156006070840d210719441c0410441601480582070700d00700b03803100c5420350007880d240402c194040180c02440e4481d0808079940c101d101d03180d42c20428a500f02c0744003402500000191210785a2041400503210425529072010019044445100c20303c0040c0014900c103000b80400c0a8030001400c01c00d104204907450300d007071540418140d40c400c9452003807103a004a02003080032401c1c060784900a010301040c068a6040440e0080c0074000a003002e420182d0301c0408207134000c0201304961445452010303403a0090340d10341a55024 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 206423714 1250 206422464 206422471
    0x6030c01080a18030816020304150503100f1412010516030e03040f08030309010606080106081506040503160e092407090e13030f0e06120402031f0603140a030219032105 74
    0x30100c41c40d20380c15103d480402640c060f00c8241b8104104072b05135020440744c940000d0198130920b140070b200015400610900080180006e1102c045024101d42c100401c0210400400015034108001c00030681c4413132281e005074104c1c50600051488420b00300703515500950700003c010581d180c4010518620000c0954840c190400003070000b507071604411142c4e05402e220302c40114040d840401c1c5901d040c8010860801c901506050400ea910400680781c020001d0341103c100d003a5050504c84000f444106c1e50703100e11054000c0842209107034040c000c603210250005140390704103010034a1940314107440790060070089000d01060425501c2e24807000c2d4014011030100c0c02d03084020a50034082e040d151100700e4000e001078148802c0741a90088031100400032039041c000c021f03001585120a004030301c402c01c040d03000040c0650130340c0b60400000306407202804240d4003400c10b00d0000380d03000030f61014030b000000c008a007044192405468088408450401070000c280240044400551021f0310 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 206424964 1250 206423714 206423731
    0x1d0402040b0318030901091512060b03040302251703120903210705030103020402130506030109020c060f0f0103022b0609110132090303040303080412030506030c01080a180308 77
    0xa0f80020448580d524820300c00f000d4085035018004122104801803043c3ca10405401c000480c0200101d190782141d03400d40046a4103c0c010082c4401e050341009400c1820051454550903e584c8450540b818029481105400440241108443c00041c01683d06817501101c1801003410702031201604c0f038200716184110042d42401070780c9a0170705080100c1c0907086540381d95245900f19000d104c080e6200a55184c01d402c00c214002405440720401140288420400184c80e045031602c42030a1504c003800390801c900c400028800341480c5810007c0c1100e5040b14496050400c5111082c3e80e000c0d0b2558150922041482d040103102c455005086403074490052080c40490003001502d00c0d01910060700d01500400701c07800304501d62202c40010a40d40e04002a00704046000020b26550240e0412400600400113010070844841ba07a0384074481203040034403151030254082969800541c4036903040100c060701040741443c4607072000981c2d404c000c41400202000d0305028000000a84e2a002d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 206426214 1250 206424964 206424991
    0x20601141513030314070308011a070c0605090312040b16030207080a03031d030309100c0e0a1d010e070507060213030f06050f0604020a08041106040f0306060527071d0402040b03 78
    0x10026005c0211140c003641921a886240d08224144014a41d060004101180208141f0003c41c0c0460714240060030650f6485640d48000c0084c142080000c84000d0880d40007400140181e2484409031000f00030000058080304071103080403860200c9503071040009018883c0c468050541c10f81201241000d00340c0c1d5030f221035121000e00b95491100719000e0b0031541054600c102400c2103a0083d0f0b07aa9145840c050041902000c006155003038998400d003003641c48c0d010400c40507000f40c04072038010208682e0070041031801c4d9001416a00c02c001004005990000301c5050300080780c01944091900003c0d000500101481d291005180540d91038a00290f0000080d070186080d000b01c6000352213a684101c0d0302c1e212961561f09520510202d80d070b020101344804910000d110341070000842c059000402d503640b40c1003e100d100f86140741d07600448200c4040e0800007a00c4841501d400841c0391a09104070540d10301c101003003d41100e5001d80c401c1c000140007a10b180003001541c000c4010700c4003035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 206427464 1250 206426214 206426237
    0x606090501051b030d0e0a06060f061407051603060906111615060e0f1501020c060a0f021c02010c020105011202030d110f16140901060206011415130303 67
    0x589000065100c0d40e80041c0e41003040901480380311074030b215914620011641805a80303068030043d243c03204285109607001d14010401e020983c00b03408010202c190855401504040d401000d6036542e007165104030381c00140b80c2c01000010040074072040d00c00003450b030180d0344914060010b00b40a03a0300356892410800a03d001e20891412500046080c90050b010320555a0b0b4580c10f91850907810b413a140d070303114400a00c034020750460380e10810705045900500d01d48000c0c80b203406541c00445a04544c03020080740415200c520441e0440891810724646103111501c040749071804040d9403c1641486c00541c10946070150400009400150001d200d40da0b2a40e42800a00d0000c460195059221032602840c060080841c007000c43c05c0c072000c2c0c4141e944445200c900d0251702180c1d40a43ca500070740100a43c07070b0300700d145140484040b200c240165242000007035075100180962400e0521906100714144d4a40703500d003400140c24268117444e6248070304d44d80c614101500c825404181c8074000c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 206428714 1250 206427464 206427467
    0x1003050105100f060c02030a02090703020903060a0207020d020f041506110d02010b0a050636130513030e060c011104050a0803070327080f0d0f021501030f03170901020903010606 78
    0x9095a890f000d54451035498030308121020341131194140c0c0c0501461000001580720811000c0c800c0d40b450318050381c1e8040c460709151038404010030030214503206120070740041e6102ea802d100079030340450b940190340411238009002001003503403000303140c041c041c00052241c1d000358180c3c200072410030540c2c1902c400190141c0c00d80d00d141079000c1d441451030409100e1444e0a50140140c0c028030041561040d0541c40e991701900b45055a217100441e505542c0381041c50012407150f003c4070300e01824000744c1410042a10b02548582c0f0003002d01140580f030404c640c8400f02070794030380c034103e02c002e008880600403819100e030312500855025240c41140890b500c0400403c03614040d6141d0f0321100e40e0041c7c0105100c02040c5002507800c0808101400220703050304000d40c112414018010b001c1e0014942e00140ca0001c2d40907a060554201d40352180c41390002c51152411290882c0480405030b00310301c0c0c00c440801714110719060b0f0301c07180c400380f2074440c5c0154042c0c9800c1c082a030080004071b071103490 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 206429964 1250 206428714 206428741
    0x6090b060d09080c1b0915180603012007020901060c0f06050712020c1029060903010b100207080723012f0120040803120c0706051003050105 62
    0x48180d0014030410a0128200e1a54085818030380142ca28a00344298805080d0420401800d82e00f40f18510528032102d40ca00a44980d40082d0f5902d02c0c40d40c0031003640c01283d0780e03424191100509082000004210751020340100911500b07103d80300c20384e4012011404411340025005a01481e47c100021500381c0c0107680c00565290000701c502c15040980c0c2e902805050b004194204004009011103c488240d00140c4a02c404000141c1500c1800b801040c0458201c0a86050410100c0f4180480e240c4c10741e4400801c0082903401135611200c3c0c0010034003402c2a04215034002e0b107004804400311354003250103000c1d00c00d410183c0760400d0f030710038100c958140d500b010b03014260034140c00b200c62503000c1d101c24115003101100c90740748100c00c002c0c40c800808003031300e680045035122440320b0040c200c0d040c1a1716121016030521810320341070880444d502d014100740c0500f900000c0c0d01141e64585c15405907640340340d00410a10103450200c10f8005e2400185c44200c40d01e40c02c00010030080341522030b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 206431214 1250 206429964 206429981
    0xe010b151204030c0503030112060c0201110406050a020312090a030f0201020702011704020112050c03100501050403080304020f130524030d320c0307030216180b06040e041202010609 80
    0x582060034420074480d00340d00c0e0000680220188581d1140110000b2018005180213003c080c020602c4448030f401d1000a45075410b01580869241076100241c00e03c07880c003a034050b00c1d5035141054541e06050b90903031031031141c80b103913825403009001081088000001c0c100c124030712039950048956103000007030f03090780641040203010510324170703407094244c02006115902c00c2c0145803005000030200408400c658040c0c0b188003403100c4c00410814081070703603040e40005100038603000c0d20b00351854079807902a001c0944000c2c460081c0880da125240e542c40c2190240340b0b5030b01401c01032418240d0309010b94604e00c40300e00d0b034101c2042c00700c1e451904e0081401c4002180b9900c030900054040c8841c0714150000c2140d80d405c1d60a0780e91007600102d6060098021a0007403030085545404c281000707072600600c1e11300c00d02e03008103001e02444510003441c103c902d0010081c5011802810010008a0601442e040080c60801d220104014005550246a613042d0290020016603464142d400103607813640 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 206432464 1250 206431214 206431249
    0xc120e0102091c0525050603060a05040f050103021c020303041a1b03070c380c0d02010603150c050f0d14070503150a080307020904020d05060c0a0807020c010c030c02040f020301090e010b 82
    0x1174007041541003480003964402ea0051aa81146480b20002001c8480707031721a1001d0565244014021420444468645000d80c100796065880241d80001c0e030b28401c90041e2080300702800d00300607190000205443c84580391128500400c80409042c9035290800242600c0d5844e080314001031140d04040d408010084070100b042c1415000545a044000501d80c81d00c1c001f01d040009442001061101504802c000ea001042d41032450504100305040c100105005a28144480c003e1680080c21600c08414a1030083e4032035018100c03c8008200940300340c101c44074084104400c0e95401001035110780c02c940550303100c240303041d0284016521240103038a1190b20410845000d49000e20902d0b130b1140c401007262650040c3e6541ba00e04004060302c0100b0054400300b40e4503003142c2c1000390258000b505100a001d1102c085000901e542c070769082c00380c24040d2440001c0255100c0c1e40001c602025840070541d50b950750f45400c54010403030410980d0b515483c0c00d503c003c0300c0c038207010b400300c034000341 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 206433714 1250 206432464 206432533
    0xf020106210b060310021c0f0b030304030f0309050603070f1e02030301050d170d0507020d02060610140c0f06060111060f04030806120604050606130c120e0102091c05 73
    0x1e0380c50301c0d00d07400041c00c0203505200f00c2c000403004900a00042c01c040491f8000003c038214099081001c0d1200340c600790314030506000c4600f8081c0c80c0001500c0480c0d400203030343c4410082c03608058039508031582005030001400802c002c40d4503000400001440d0142d6540c1c510042c0101d26002c0101d1045081f500680042004014034581108914401c034062442c4a00c0c0100c81250650258480000e20b501507480340c04101d50035405108a190300e0700c190002e000075241c00301c000b41144001a588a00703101000c50040019428801a030356051010b000310350034030400c03d4055554502c00c8659a00041e10319951114142010580901035010402c2040712a15641d4090391b4480004200d00c0e002520004003000030380080080901460065001d401903042803403e01804c42c40c0841e0342003845040c00007580a069000c8000040c11152110009483c45641d251601a110700c0c00481c0d032007000e18004100020100014680c4544624203c481c60070301c102da80754608411002000d8400103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 206434964 1250 206433714 206433779
    0x120a02010f0e01020f0709090b0606041d0403170f01142709010e0703030e01030609050105010e1009050d0803012903070c060207061d120301180b030703120f020106 72
    0x502d800d0b92075424140140c9564845440d90980b0308040c41d84a03103a001c2e1200e002c1814820640203458200000365046880d082c24290340f07140e2040c1420740d00c42e4404450000030141031190700792150490302c400411229092090b00045165001e0040c0640e0022500340ca1010380741c0010306d503040c0803000d007503014450401c1080c0030442100502c040000d549407101d00b41104000c0c4504009980700e603c84c1e656a022080006003156180d03040b5000b1140b80500502c0260f0b080001d860500d40c085071144011111a04200e400300d50740c0d48029000b0032084070410800030b00c3d01c05035041e00c0c0348034800300030806620b0400d004000003250890500408001185a4070310400d203201e00d0a00840002d860005c155030b502d02110f507007561001c0d201283c0102c040302c280b41030050900540740e4145441c210b50500d22501c15200752042080000780e40e900c1049070300e4505000003001180c018040548100004101170540440488014010752130504085524880c44072110a9000da45182a40050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 206436214 1250 206434964 206434967
    0xf05271e1c080f040303090e0109090b01050d0f0209090714180415060b040f0305010e0c030c01030b03100509010509060a06080604080a02011e0e010b0a0b12060a080d050405120a02010f 81
    0xc4640d0182d520503010006880b20400060080000f0b42c82980c1b401600c52070461100101001030700080a90307818804034034040f0b501003140d207040d00c42c11284020381210510b4102070121600784000d400490040c200300900101080013011550f80c0554003405081c01010007441510110b0410a0700e12210082004221206d001d842d9800d1650b400203102a201c03911403066401075401326041c0407010005008010f4280192001075620100506d5440244000251207200700a24603040542d10250400c00381d804000c0004884030801d410049410321503a828041d010032202056a0710441002c2900060a031080310100c034142d6028180c07036241c3c5da8641241d0342c0400715281c11592510424003000c5141103c074422100007100000b5000042c035000e0b0b00355125024424420103a001003000085100d2003140c440e015421604c09032582e82d2000a200600b858100fa1118411038000107070080d0444001c08c1642c8003102c000c050498420807182d0303280d450741c1000b800240310100504103907 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 206437464 1250 206436214 206436259
    0x140613060806130f23040b01090c091809030801051206041101050c0d0f0f030c0918060305121c0207051b03011803080f0606090d030f05271e 62
    0xb540042544035200e1803207105005607044210a002c600396a042d090500312041007200b0404940d0024144c0b640c034194540401100c4144920b803c3e1580311a40801124490b042440c050034900c107000c078134002c1182c45003005048102049001c640c5010001c21a407134500440100c600000005001990710b6035a074400c0481e50703c5400d41800020b00580410f14002d012109403952141c1c3c0701e0707900503c5600b00500c102c00d0542080180b52424440d84020b5500420040a43d02e5448900849841500301c1000402544c0e00c00340442c007d02c00c040c03100200d030b08000c0c0302e10300400040c5012940744500701c500700d1040400091480d484200b52080d01501c1501d684482c20000380000744d03c0110049004949103039030300480001e04140101b08500d0b040242c000d40054065510700c0c24041c080c07000c80e1070501c01003000350900c00b044c5084201c542c49041264103844903c446036400c240c0d00c0a0000c055050110240c1c03040700f0010b50090204100c0c0000801c00a005181d0003c100d034000f41212071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 206438714 1250 206437464 206437471
    0xc0302190e060d09050f060726100e071d040203010e040209040c080d0e28060c15020a0c1401050606090415080f0313080a02030d0e03010b0315011406130608 69
    0x485814000302220342c3d40307403241009440c02640581882c4c04002c0c04c6505204004010500b8044900040003a8485940b85000a18056089040c1a072211b01644041c491240d012140701030710f200400120503444402c0308940c0241d00b02c000001c4c0c01c040f0811069000034001c0300004d03107a180018000d441c02455144c1c2090241e100c0480c078135100c07a842410589170036a14008a85003a04040d02400d003041d01124488403c103c20702d680b025402104841c560380e00c04d6001304002901228244001c00d2585d150350b00000703008542d10125040d0240c21181c6200058850354002c0c84a14110302041c010707188a188000c1c00c55181804141c1008024081c00d50032060882d0490000b107110032041010b651400e042038015a1164840d5854064003250f5030030042d03581c0c000500890050320006500c0d1880364041c00c2c880720611900002c80d004042d40c4121641c90b210320200705098104401c0c00c14161000c03010840c031040c00c04002e000c4540f1881c20202c4104021a40411400f880344444540 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 206439964 1250 206438714 206438719
    0x90f010608160c0f030810090207020d0b0709080a0506060a2304180b0a050f060a120206071a0703050103060b01090335030a050603060105101e02030d0c020f010c0302190e 75
    0xf410040707032101d400410300c0b002c1c203e003c1a0041c06000c1410009801400101103d210642c40c2c504280d011910108118400400314001c40001c622494000e502800c00b401202040304c00d00a442d0030025074500d070a8402d540914a406004141e01d0110b0b0300d9050211048090326400700d0402081c880108900020051201060600352000800c2d00d28103c0c05910565000304680c1002e40d01080c141350040e1007107100e00c030941020801c200b101c3c01d18628642d01242d04980b0f441301424802c40d00307101d00601e0a2842881e0302040291034140d84064181c2e8059141080640b420b41d0065401042a01000d425024030402100113007000120240c140c5a0a0418410f900c03100c5010300000e800c241d0380d0038985074998007089024142084070a0043c035003240c8103100b901030650040c03e4541344040320075981c00080c0381e06000354020411039041164a0508110310007810000940b07a5000c02c1420009500b00b0044001c3c051003402501c080d000200606200d260300d02c0c0007603812442880210741c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 206441214 1250 206439964 206439977
    0xb0a03032106080f010608070503190b0c0904020705030309010c0912022107080304030b0702010b090c09010c0209070f030605060a141606061512060b09040f020f0a020705090f01060816 81
    0x9072642c007030003284500404c06001084103410034083d64101500d50308842e0081c2d02c0f9202c0300200d002403148800075950003101d05a00c50310b60241c4d002c01d902c03500b8106034005c0d000007411010031400100540c807508510000f04841800010216640412481169031000080101002514001c002c6484c0d0700103c444003003034042c8143e111401d00076180c0c0442a0381d000440c0c100107010300600b1241d4400540d100810070441c00307200080ea40c0c2806041c0e607154170404120710900c1c0e40220005580b56800420088061030701c07040041c088d03403a044201000030304103c030005182c14040e003659507101040d152081c1d050000114034507542c00800324049000e4509803a240410468072a290241c60100c9400307a800e45000c5002d00f040710040070410015143c80c8007004092031403c00d642082c01e045134049403214101009038003a0242000d14901000700203140710100d0340010380c000031294262050342c1645c0c0c44c6d4811500080c0e09114079004a5000030000307640d81d4000803101c021048904012 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 206442464 1250 206441214 206441219
    0x120315120726010504050a0c09060b0a0509040e01050f0a110c030a0804020a030803070c0b060607170306042904180506060108180a03090509090a0203030706090f0f0501050601030b0a03032106 84
    0x182580e001752800e4500e5002100c404050003280d0303800d04043c0940b1071061100c1444c20007888070300e1058250460400c003002c40e80e4180d59403980c100d48404110340b0028802400c01d5482406038900554068420314070b010800342c40884014141c8000d103051201450800b50b05007000e88241100910880e40030100540100000c3c0c40703180614040c0480350740741d094503055440e08520340c11000d03028a05c1a1024007194000800445050142144035130040391139840d01d4012501400581051800c0841c00c60445d4222464801d0b103d07209141c00c54042c0090a0540c481c41c2512070024006002030308814001070307055018504464000094004802ca0f14801062072400d0a10342d110440c00102e460b84200705500c0c02d401800c1e04401d4110240a01c02c44983c0060394a10605c0c40c0100095180d000881c1402480c00c5207441d85034004040204030700b0781d85007c41c000c00f81121800e001c0b078174140c0300703901d41c1c104024840103403903140d01d64036800d182d61a48404d1f03080b01042b0501015481d031502 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 206443714 1250 206442464 206442539
    0xc0203150c0c03041203090f08060402040f1104080114010f0302090c1e0a080708163903090e0c07020f091b1908160509010f030e1203151207 62
    0x1813000f09000850040201307114907004041803070703030742c0500b02080081c03100380195040450181c1e04030740d0490307000580d000710300e4124000d40340902c0343c00400180400d0004482c1c8064002810b10311010003606103583e02d030821005050811b00010b504a00c28000241e403003020a8004c240c0800c814600c20b94141d150708218401d40d015a40030340010f0400014000d030182c00ca0000d40e086032400300e0b260500300100f2001420099400160f941c134580d005070780f00b141034621084d02d4007004c0030850b80040a9040c140035101600500c030f8003003420181c0000030171107400082074801c40365004040c81c43e40300403042041800701c00505030607491841d6030940c2e100c10324503030000c0050342842030041c481d0b0311082001070035030309005103050303101101d003940f0b043c0303c40d40241159014802400c01058045e4401d1040f0003c0078219104032462040864041480c1d0425000c3c40c8641d0714000b207400052440c90510108910b030084540c3e841c2e02104c0140702d4418142c40d01c0f858011103429101010440c00c04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 206444964 1250 206443714 206443717
    0x20301061412010b03060604090311030318060a0b030c01142109010c0806090109050424021201061b03051615060302040c1b030f0c0b0709050a060c0203150c0c03 71
    0x12111100380d507816808608040d07440c2210120280020002c0603134000c04252100750040c4800c0c404d9644840174002c05000790224000807800307070102d0381c684c941061015001c1c00c110804095a10440c0d0004441021038020051410b0016002c1d14000e10381a005403004042e02a6a41c0211014800b0043c44030303110328405840780c21044c08000314103000343c9060844180900c401c1c20420450308108140c8c072140800c0e41144d07011440005d156403141020803007c201401c40c1c02841840b600070f40e15859458000d02480c01881400e89400c0c1d23614001a986010704503e0421554218008400440e000e5805840d01034a04440080c0d6007126940d4088103108c40510301e10f425a84040600c15420244107900100082c0d090030f22080c4481009240d486002480003002c008102c00b80070110f170b00c07982500e22102e07404003400307145041030303400501000b89030702601d8080d2405400000d21107115044107501541c024003d881046000e410180da1800005c00550000d00c00b0022055502402c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 206446214 1250 206444964 206444969
    0x30f020a02010b010801090c0c080a051b06010f0b0301121506090e01270506041103011404030c0b0604111602060403081603091a0a030c0e04051602011b0807050f0702030106 76
    0x140009807402d56540050010030f0306030807c0300340034500074128400607009512504482c3d0002c086076103840f861201100d5030301c60084e8080d6056191145084c00d101b00280842c142c07201e0070440c070441d9031201d012040d140024405d035000e02401300000e01c0444c41c01078032040000c8401c007010601507280c6109070165500407010180c1a07540b10644041c1007100c0b400b061174144104a0700011724425224130395103c1000d8400343c018000700f07044002ca40c3e0f007548010b581b0302e07285402051520f01802c0150400d80c4d44038041c0c0d900042c00c00018038604d0188aaa042e00d464448214240000503c00400e04002c5400172070b00322000300030100c0440c1c00c1101a1422844403038045043c040c2c10f280040c60196a0b5000300035a640e402050301c54030000c2c505450780c50700301d031030000b4081c1c0c1005c00482d103447c41840400c1e001441e01d07081c42200f200d00040144034400c542c001784100b65441d40159462005174409400041000300440c00300c0744074400030031001e540c80040508002d220740010782141c1055 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 206447464 1250 206446214 206446217
    0x5070b04080f010501051518090a0b030c030f1c020c0a03061e09031d06070606080d030b010219020d05100507090321020d030b0d0b04050f0715090b0307030f020a 71
    0x1003030401039001c1c200a9209044640c0c4024000c039450400851200390444082000440000c103401e4203880050328207416242e0010300c407480c2400c000071070340010b1001d012042d0083c043c070400c0d9503040c1400a929215540705030011705501e081402d02490301d10402c0600c00444c011000f81c05040d64504082601450041e038000500d0025104105401c40a2816000e080d03400c0620000100c1c3c0c00424000c41410804141440d0341c1c042400106140b040405c02400c0d5807418801003071001002500405511a940381003203480500401680e4500b104a040110155001085401401d005460040483c814030440c0d4840003158003540998070200c03070300000105200300030000d00c052804a610113010094055810b0021084000d40301c2a102c4201c0007450b8940c0008100d81c0c03110b00c25182c0813500440682841d0030070f0300c0c0c815180c2c1c021248041c5d0500c00c003030300880c40c9640e07009540300400c4a6100c008006260a505075181d0700010010b50034103940b10440c0d071224145000030000c840d0303103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 206448714 1250 206447464 206447467
    0x803041203150602120a050d0e060406060f030803130f02280e040506060d02030f01180b090102040b030106030b0409020405090d03060e01060504032a0e041a040b04080306010c05070b 80
    0x4090050441d0140741141c1d040710160b0108020141e0040360303003201100790000071a1384807103489040c0c802d80318800080130501d1401e8030700c0710b40041c04162140503a20540301401b01366554001c07808035912601001d0314081080001c20b64841d10400840500c61080030801d82c084401c3d0000390880501141000d18203482000030403420511400c40300250a00d000f4443e11801e01e51145559490028107241c06104621041d200b59607040001220038181c0300001d200642061882c1d50b803030a0b0001d41141c00042c10030205859101c10300941e01942c0800364841d0031a0f28003442100a00090500142c00c00d50f80c2c141c920251b152405410b10850307020005009031400c1140080c1160300f9680004c001000300e0005000d40e035032003000c90302240c0d000003619004c048100028542c2240265441c016030524000014182078401f02c0c043c819401080c1030b5010080d203100c20510070408440041000200e0800600011202c0c0059900903506140001c8103044550311985050485d0304028040c010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 206449964 1250 206448714 206448743
    0x100509070e0702011e0b120321180c0105070602040906030303021c0506010f110f150601170601050702010c111005030603010b01020a020a0b0307050c07060c150b0f100903080304 78
    0x4020880c29000402c0748000c0044800600c2c11420032007030b90600c42606900c82e90140100da8600d400e1008400c0c5080a40e5903038261081c64843d0315580300c0c900740409906400040503501c402d140020340640c45c802034002080010011aa16070040e0011203489600b44000f00300c3e6040c601c00c400203944261801651660424800d00e80ba8070303a0f005071600c042c02d00007080200c2e40d000400404c0203c240c200000b00380448481c060401a802100100b14031841c00e0007940c003000e50b0043ea00a036004c2e25a01d030340c118003484e54408100211210750105500300308100c019489141300c0e16078240a190754540750020b400000d0403002555030341d0b000141c0c1c04420701ca55880c081c821980d2011090000b031581d1500c5a01003034000003180311301c049168003c070004150900030411203a01821070700a98550648829003d84806548081940c401c2c0307010003244003881036441000c16089000301410340c4200311204003d030020030485101c04104140d1000400540c2060103140154890001c101c40080c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 206451214 1250 206449964 206449979
    0x160c030c030c0e09070315020d02031f06053108030c06070318150203040206090316030c150507020f0402040f0f03021005031e1e16030b0f01020c010503040510050907 73
    0xc145402002983c002d100900c51400c038006041d5040325804110a00c179509002000c1c2c0c000e029100c0d030300076014000400c101801e0008148150601041050040900e4581c00e003150b450282c092b4040034403d41c0110100203151420a40c081c00020150341c3c040191a0f02a80d421608801440040d075804442132091854060055645034556552101d0b58042c4640380e5409111400212102c1543d0000c041420344d16044100e0741401c0000d0b013215000c600d0f20100340042c090b14401a11441c0380088041142030038a50502c46140300c82d5200c0d402c20811f9020860710703042e6001401d40c4150f08010001d45100c0740f0208900500c1303400d0031040d00c0c510314010b11403070029061000082107810010080d0155504084074500010583c24018940d984210066890700e002d501a91298408082094044110400c440c400010342d4052004003c001d0034401c11411050750940560040311f0045c1c8103520490146a02a00405c101c2e14034000703803000002191010b54001e40c59400c140000e00104 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 206452464 1250 206451214 206451233
    0x902060426121908040c08070b04030314030714031003140309040f020a020717010b31060f09150e0a06030b07050708070b190e0c010207050102060f0c160c030c03 71
    0x70386228041e5898a0b00f0080e89040c180100b0307002e14140480721020a06006007041e00401819118044420450b00c0d0420820140c00070310085001070456810304505840c0f590a89009150310f0f1039180401031003404c1d800454100401810604040300c00010204501000225003810144061913465064a0070300c419a03103689140c00300d0324010040780c0c00140d8005845401c503051140c21a9841702c0c1d1808180c050100c103665160b02803a4070f0202c1c89007022603940c0d000e001001041043d048100403400c5001d841c890b01c14110540300d026010850341900c0d0b00094181034080d0300074441180c40315051251100b0545d01030026581c3c4100038020040241d0b00a41c02100d1401d14030f003800040e41d1051a58401d40e00c0084c0400500004100e003910582121a104102d13600203101c08609480c020795125828003d40c2e00500c5402400170380d80d400414818050004410401440d542c0d082c5102020b0344070306a800010200c420840c0049100e180290002c0c44c421501c00d0030f0309103182409002c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 206453714 1250 206452464 206452483
    0x303060513060f050d020604090609020a03060909020102150603070905150a0807080303040602090103060803070b060a0b0a0203030a0c0c150e101a010c050c040e0c04110f0d0902060426 81
    0x80d07900e840010b00098054042600c216501190381c0c2e640380c4002d04c04203c150099500c010340303da0070030101240410880d005855a0742207990100541661428042c0980e00209400b90241c1c01c0007a150ad42071116141c0d40d90701040240c02c442909903076034100e4044403c101d0b4a0112804480285582ca2802ca030400d001000c5420003403d801c1d04104d111512484050001400c069000900d0400759000750424030040c40d114041d252034a9007070501a8141c0c9040340e48511940d40702d100850042803030030540d60b22080b1503004508590303a00340c64400a100381c0801505001d81c002072107000801e2060544100c0e4400400423480c046c000801510b0700780128076030484981410800103400000c092018003203e001d280c15054402e4030f041c11820300c0e00100e5190f42041c00c1005880c28100000b400b440200c1040d902045041c4810500841c913008980070526140420400799840300010f030030100006000508252419a075845101d40b010090106055013a08442441031340c80c00030b00c00d200c030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 206454964 1250 206453714 206453749
    0xc010315060e0a030c0608090114090d0509030c04050412110a030e0d14011b1106010509161e0801140a030309090c05041a030f130803040b04020609040903030605 71
    0x14181030310040c0800c0503008980030414184100c035016500d00003c1401035800c000c0c40e95481d5107aa5005000c2c10080300c1140c4990700306100000781c800002e029610510740307580900b003402c010003800c40341c5503c03244545906104000880409940d1071003400d00a5228241c0076480800c20500540305070b40180b00110385400046607800865044481c28503028401c4643c403001443c249400541e019045154803119843c08030440554100340c0040c4129410a840d60f0b5a54500c0144080d500c800174002c846c1c01c007001c10f000c101c445850342003d0701290300d00c0c1403450468483d40f58012035094118841d07000900b81303100400c400c480101e0703501c90214040da0703110314950a54401500030a02ca200313890b4625621103140d140c1510030420340f0007404800a02c42c2c035080300c10405e0940c44d0026216207034002c018202280b5819400d0038100301107a403000f031041c00c1d0380e100e407603010310444c0c01001603030404000c100d01201995071b03109104103580700340c0300001e00d1410b110034082c0e42e204400c2c0300700 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 206456214 1250 206454964 206454971
    0xd0c08100303021203180a05250f29070b0a05220305130e01080105010f080a11150403021306090506010c11040905071805010e070512060906010e0303070507080c0103 73
    0x1012983c0801c0c84081d4822601540360f99403103003049107202072046410080b03d402104649000c2007400f0030b884486090001c06000f540035040c6007040c06803001d110b0784000c2c00d00b14804001155880071160300d18088890072403109550180c0c1782c4100e0340440001c890054211342000544451440341a40100c00012035110086642441400c0100b1403840a0140b0001003050b00c0804007100400010f015070b1a4102c001d5692400c0b400d001c0c200c00e0064140450104001041c003150000301c40720441d0300444009200741c1d0031414418000355030000002c100108010200168940c0c26583e1050310351800009011454040c404c411544064082810460f42c4540d100110700c41c400c08141141d0700300c8002032a0026450305034038002043c1d00c480e44160b0003140145042175164001fa040301d400c02c91480781c81d5580d401c211268450805076944400100c0c01069080c24141c6529030700103411f044c00300316000418002840c640001e0380031509544001014041c2040900c0556104c050a003800d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 206457464 1250 206456214 206456219
    0x6040b1c081e04030317040f17160602030f09010b0604092c0a0209091908161a010303020d08010f0902090112022209110334030b030d080f07050d060302060d0c0810 72
    0x201601075403100600300b0f4549e905c60102d000c0584045811110044803450003024861410344065041281d61404000c2100002070a0711418042d0340304c2d03603600400641c6002c2c284414100107000703c12410040001d80c0c201e000d00344090021240d244280140141481d442a10411500040042500d4070390b410888214401c1c0703c000c0414003406034008600b503210391000880a43e42400d4290241c2043c071800c0940784a2003010f18414144d034040e900395640494414170a80c0c04000030b10412400b080030800c1001080990740c0900042a414500812010135900054044e604140808000b840200c8240c08120048141d10802001d14803402c1c80301c105140c22075241400000c00c4000c2c0a1501c42c0d82c0101c0c5484410107202c02c0c1038007007021000980f143c1f401001022803806442c02407160b048044842030251030b1507845900c8016960b00b465880d00d90448007500049800340c0700e551514004001a03681c3c8000e09800003500b840003500c204030740c078014524640a0540300040140c480c05 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 206458714 1250 206457464 206457473
    0x60a030201390309052e050d0e060a0e0d050c06070c110d03020106060e03011b0c17030a0b010e01052802070e0c0307030c05040e01090b270f06040b1c081e0403031704 73
    0x120307000441d1b60b007012500c0300303c0700380c00314040c00d030409030b041c1103000d42c00402030302009683c440414024240101c2c3d15940204c0c1c0c0aaa040c0300d408100c100e00da111000048400e44180040010b00f80b14105144154102c4404540c0c0d900040070100c016035140d89043c0140b40d40030a078100a040118000c2c442085d21541c2c0105404505131143c042101580a00b4207000c105256001720b036603070744010b03640c9141c6240303000000c041071034443d40010700310321104113958810015564143e1421004c0a242112040d1040c070300b101c1c25030208254010001d000508000c85968144502c561101c3e00342c1d28a061003004007190807044107441402410320007880344080380b0710361a040d10000d03500010051050b900042c0c0d602c0e200c0b168240c00110b01c0b080d00500e110351240960040c910000c400c80c85444003000c10058441d94643c054200c812289146032030300d194141107410600407043c080c42c00c4404101c0c00501ea41c03001f05101c01c0000001d0420815500600f41006125a80e101c0106400d0a959 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 206459964 1250 206458714 206458789
    0xd020118021c1407080c010306050a061e03061a0c010b060304081c06051002030a0810081018020d050a110301060608061002010f050a090605060a03020139030905 71
    0x162050802c40b420b400000300001c0703285040c54070b0034040848001d076a5610f040e541c1d030107140d90440c4c00a400d101c400a01414040320b00700c242d8215445d862075035000703444040c1d1440070050b080f908058903043c2c0041e42ea4a81ca40b07248034003e02903200c0f6621051750072000c1c20340d03104800c101d0007072004200300b00c080748501d002d480e40c0c80204926401640821501c40001d0181c0da00995071141c00b87ca80c0800c181e8001008058100c4180c4800040307035a6510228042d10143c4600883c6401c14100100401d80503400140e8082c0c031510141d41e442480c3c1c0100e50703c0e83c0e00810403111680145010014004180307040b40794080210001d104250901000a281c07650140c0118081e07241c841004074458000e4000c629900201081042940351000c26403000c0c240c20b07001079840a24000226142d0300304400c40c1c0d800c4c0c1c1c0e0182c494044d0848140d1000c4a012611400b50308880c2018000700d01801c00b509020a0190190b0b852a81c070605003410400d9500c4c3d01b0507411200c0e4502d41c05180900180d44 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 206461214 1250 206459964 206459989
    0xb0f0f010c0f03030b0a0e09101b0f05041703071e03020d0e0d020916230f09010507060908090906010305040b0708072003040816060512060f120d02011802 68
    0x41c1c01c02c12075803514041c1c01a109281c034042d409007046a0100b01142c00c0603101e8801c4a00030308031512400c0c2400305108036110320740307a01e0203000582c2d2146007050044240c3e1030b11500030711340146896941d091030b01c40341d581d00040341003580000403083e052058003c002002c80d041c1c0d500c41a0700281c6650080c0d174a24880e250791081c00105481400595180381e07010100a4026007089480d15040b050340480103010f602c0c0ca00802c040480c04070b40e140e252411400d040100b26030403031801003414403690654105100081c10804c081004000140a5000c0c11000c2c1744179860342034480c10071384100700c0c010900400700c60425240000f0440071501040c07007941c00150900b800304054441d0441203846024440840c1d1044100c0c40401400500000050044032000c00603110701c600070030610301ea050307141e01c034940020324240f200f103048440400d147c60300000000c01910075980f100022030884190300c1d20178200d0703802c41d00c14510344540a0007016161000c3c603101e41a003001c80e80c00030b0707941100321 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 206462464 1250 206461214 206461223
    0x3100e040807080c010903020d050c0703060b03010902030f0706030b18070e01050c070e0118020c12090d020d0812090c03071a040806010b0d11030f0103030522090b0f0f010c 76
    0x650105080c41645401c841019400c040c00c140c4e25040609030070701078082000c0c200c0c010710a44c0c05010549210724162461040c0f40c00c0a041414503545540014001c50000b65515550302c2e0014001a9030403c1040c05180e113160142030720030700e01040a800c44101e0324455001d484a0441d0440b1400034010300d5900c1401800c0904c071007110000102c51600981d01044198450343d0008580d510320130001314101c40030a0305420b1040140d0072084d0681c060b204010503d94855804666400072010240c035003a40040c2042d0002d443c550001040c01c052200e0035116404001020359180c2400d012080c2d1010820004002885440700440d03a11034440c480c45000700e02c1c1d05110074020440004450041c052101125010350316606104000e80c8203444005049180c004000e81080c413003419284569100b1a15100c05da1035901c040e039079030380802c00307421008030708003074110581d04024005000350040502c0003c240041c0000d0000c142503070030066110f0600410540341a0380d10400816456620 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 206463714 1250 206462464 206462489
    0x708030703110d0605040617030403120c0203030307030c030f0c0e04020a030221071e0905010f02030d061715011511100204090c123b010f06060201050c0310 69
    0x45a6045004082c0c0364045644850002000b84080880b0341000c070954004940800929030307240b45241c0354020240c02d4218a40080c402003010541818000310481c0460030074503504000750b400203085900449610380403aa503001c401e2840e0741d00d07105a8038440d41c1040100107203540341402412143e1300b031003402d2090343c00140b00030585200c0c1e0143c900d4803500c200d8400000c004181c2403d801c601c1194850000707a50b00100e4040010f240c8460000001540c403011441420640110380d11001c026003681035220811126070000d4083c0b0a8400410948440010380030325034440608041c61003600304420354120b40107000b03006001c3c8840d60a107800e810070f510400ca990200f18100440b600c6020820351020600064011190300140365030072440e07403240e18081c09591140110b416050305031000c0c18505408160b081d034402c00e8090301080400c0e003e08a001c04202d91030035600d00017a14044240c640c94200b0140780c090181e07917000b95542c004e060031440c00506011a002151050342445105e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 206464964 1250 206463714 206463721
    0xc050306180c07080708070204240e060103020c0f0706091e050402070c030c080a0b06060f030a0e1606021f0b03060403050904020f16020a080106050315420114070803 73
    0x12900212000c0d1588013211545403040d07400c102c2c010b40c0007042e0a03401142418142101c4800c2c0138000c5421040d03100b502078440d070802d05c4c4503403070308002003041e07040c140c0c00c205480c0411010007101c00324985003030003003103c2c1c0e041000003070020010b640a40e015040c18000b548074681e920490340256401980d0050700c1e202c0d1030030030072660042c84d803000e48514082603010078008004145040010702900c1c500d40191150000d0107032521405c940401800360a0002c219407030b403aa000380c800e43e186032003295030000010305040f0464401c0e90002e4050790010700700041502e40d4881c0548450f8011500300303c60380d08000400e0320f901c5e00920060401c070380000c805a00d07641e01c0d03040e03d145009a200442e190328126040c805d4002200d10300b60301c03030304104c900005c1100050066000fa680090040d20440c04404400c05541030054401c0700f0f00c000042030000500460000700c0c590320402e21004082105280349801800140003001d4100700711100c100d01008a1101100c2001c1d501407103d42c0c0d41d030b8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 206466214 1250 206464964 206464981
    0x406030905070302040203090d02010510051e0103110c0a050609010501080613060f1b030e071815031203050601081803030f0403020312010609141c02040e100e0601090c05030618 78
    0x18030343d801c001e40c0f091010040c880342440c00903031080340885c190002c0140c0d0f110324400d68a00113a601c602070340242c0c940300e60940580d6039040c0611166040c180828035400300d51203041280c03c00241841c203a03002540a80c140642081015000a04080200886d5050030a01038403144001e10103900b004800c55050104401c130b91080c8900000301030104034112005102e551580c44598070240040d0428020b00440700340814000d0440f0794031200c0d00c10b0919080080d401501c0d44101354002e9012143c0000003141001c6440e000f0f25689540000711031030480300140c440c10000c1d00c0c90401d82c0c0c100fa0b1800209000108481c0c100440c5600070405584500d0300724518861503010f030f04040c00c4140002621600703c200308056420300b108803401664220207101c1c070203000f04008504003c807071086e080542030a62000b8500f9610405842a046030100580140e902e4800c202890340d01000041002c0c0c4140e06c00c0c506a440c1500d400741c5103040c004002008007210300390010030a0482e2010500b0b40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 206467464 1250 206466214 206466223
    0x3031107091a12030f0c011b0f1710031b1a040b03070c06090203012a050f07021908060708060316031a070e030f030706060608130f03030204032f0f060406030905 71
    0x500c0102029a0f079006d0000545011b13001003111f0718060071124103d02c140d240211176802c24080a6510b25802c2003000864002d0000054075607850030348444004030101303502260350140040004103840100c1e19040d02c0b401014985c04802c2c40406050100b84590404503040300c1d00301e03142d4130307000c2303088074890502a00030440044020342c150700e4501c84030510031901d0311001d041e800f5104002410300790b0b0541074410784070300b459501c0321003000c2210740018a09402e524845840b9008001740058035401001d240010680350031000c00c6141c0d080005034541002600c008204188005200c94615071f254024450070140c103203008140034001650391840f8030258082d480c0028100e501011258180b9034a030752151b0b10070707198982041001f00d400e50050f4585405070440c02d1151071409210f4450048075800d003a0106d04050b001c0100102140320b99192019000c00c4468818a40750645001d42a182c40d4183c92070280803050450322066581d003083d64201c42e81401c0218040a083c40c0041c00c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 206468714 1250 206467464 206467477
    0x6020f040e0405010c030b012303090307061118100e01110a02031009020a0e090c0105030903042705060109050603061201090210090509010b040b0301170a0c03031107091a1203 77
    0x24601c10010007080c01415004407101d111a51001c00c200f0590900450303048000720320103e069a13030081255a040f020600440c0d100e031404055a080400c00d030b0b201d4080d0307142c20100c208241008030b40b807401603080500c02640008101c450030800c1d000520f001d018042030a0380e85040c080300010703201c070503001440b440f1031306a0300070180c60f4030302c1d000c4240f036000b0030f0014401d07801354801a0011030714400200b407050082c081c07c0c0083c141c1d0880030703004644540c4010112074490106000005040410070600c1c120b808070a140c0d46a410b404a0a2104a031b000034034403810040c900c04200710b6515450100e89e000311064403145050458980c1c464054a0340c50380082d00064290941064241e105000e80161441110410b1250360395041000c884d01482c0500c0da020300080004001c460016600e40f110141c0050a4a001f0b6046440c3c55400074590b80c0180c001c030355450710a01108500b400084041c00b04040d04000c10b0f40c40254609408140d004100c0c05081101951180302d6003c04c2500d09 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 206469964 1250 206468714 206468729
    0xb0102030d0626010b0306060607020307030c060906030507020102090a0915050607061d0a05030a0c0f151406040204060c0f02150301030507060e0603040515041506140a08031606020f04 81
    0x8096440101100300b080d1800c0c110008180d0003076284082c0743c103010707620303082c074000b40200001d8039070000708030091b03018a43c203c3c1c0c1841035480c0040002c5483c0380a10042441c1d40302c0b108281d00d025008dc0903120001d20190840e441040807014550300c01d1035100a0b5140c0c0400003903280861030010600b00c6094100c15800040400c030281040803c8e008644400c04040d1000040e00c5e002e0803403642c4171841607008001d60404d2000340c0c0154031070841e4006041c0076a4042400c90300c1f40e1946a20a680416481ca0003078544c40440c82d07260443c0449030f002101a24218540361404c10300500b050390100000345103070005c0c0c418005640d12110b10004420000481c55030702d503901e00d00507a8907041403068a000c80e100c0c41120b0142e16021066a03c9584c0080142c171007481041d07009030b0004402402110151441480c6004070070041c4950030141c00d200c1c15040781c800300c9508002e000d40d5140d10061140c2d008006034070a5540011009540b2940b0941c0540c076003100d8140c0310200d00954000c0c18 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 206471214 1250 206469964 206469971
    0xe01152609100f0207050f060405060c09040f0606030b0a1e09050c2a061003021c02010c0501020c031209161e0302150a18080304061b0209151f0807030b0102030d 71
    0x9415031011340c02002e8007881001120340328021032010784d4a41030100c0e4007420a03080000064088040c40c0000c1c840c058009000055050018030b00c04210f50480c0c21400000355100c0108085003044400000030709010314001c0f00d07040a00700200c02004403401500015500d607000301c0d01441042044d01c90040f0310301194440303a107840c0308880308000c0500000f1b1091140001040c00018400b45220690303801500c0341d1260180305190702c9000c1c18000b412410400003030900720104800780302400c2d0b4081034102541e540d05541164100645018100c48520b82280340c1d48a43c2da960404100b08460201045142c5440030002c013041100f6250700181d08051010300560b1035000d43c1008211021884e11036402500c00480708003a40442c0d401618101c0d07100700700500a0a0151260100d142011080c003000300900d907010500405c000d603a0800104145d1171381000926086d0324081e21450404204108a00000c000404440024080c0001d2540da1201d2a1a03640b00348102e810070880c4c2807051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 206472464 1250 206471214 206471231
    0x20102070b010e07090e13030c052410472b05040f060b27010501081308030604050411030d120c050717220e0115260910 53
    0x24103c0c85045030a01c00045480384041502d516940515004100341c1100d20700d22103003a0341c00d40700c400d0429005e0300c1c64810707000b14505002c074840746012000c001540e00b04c054100744403a03001e15001900282c0720010600e040e20000884044400303189810103c820303075001200030390b03403e660302d5120310050b40020018188000310420b5070515030340418298840c0c0707001c00301464031040710401c0d2030003012100c040700b2200100700c0980000d540d01e00000e0010000803190016824041190391100c0f03500207600c4010840b41d0380004050b54001c0c60341c0c001504040456807800710512004081c81e10903507548000c10140508060342c24110407002c1c08440044008607406000c1d08540d02c110701d941e9040442c40e505092107041682c1c05554801503442422446008075140ca4000011001034050740982d8044110707403c0014400810340310010000395410700c0182c248240740354203003109000103074103103200e15244420400e0800718122480501600c03000300207800c007407104009210480c1000c951 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 206473714 1250 206472464 206472479
    0x1211040f060b04081c030912120605060409090204060b0304030903080c0c2206050f010f110c030d0f020c0609090622020d0c2006070c030201110d0519090b070e01020102070b01 77
    0x1c0c05444001d9460304100c5d42e0181500320107940c1455001040c03560154100b4070094010010311441100003030000c01c000d078850f00400c0c2990000d5010406441c0c03502d00c424103506061040d01c003d05010303000c0390705d5860503031005071044009110041a150740000e512070802428414000013100050441602d2500460b00d90780d43e0b02014081d00307425260540009091400e000c0405800d8070603115003603420140841500e41400c030421400c80c60060407038010440c0e038144040d210b0300340c5d84d88460b6100c91142d54003d1401450001d002c4c000e420406ca801d0309a03482c880c0259014100b00c5980305002c1001c4500c800b03105181581041544c00420440e40d1000c00b5001400c8001881e580e580c501025211420345614220b040c40303104d42c04c0300c800314000e60311422541d07203c075000c2d0001040c1e001e00c00800d0f00c21540210b225109950ba28418012000e80040e804803003071402030000c1c054140c054030313407041c0303100003802d040c09001440030180584d034001c0d0141c0383c0542d007100248040d580d46101 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 206474820 1106 206473714 206473723
    0x110d02010e060918010305060103030f0f0509040c1b0804150513140312070c0f140114030a06120602030402190e01141f0c03091211040f060b0408 64
    0x40320302c0c21355500400c9030085204500901c002c0d803440c20010700b0698900e410004004944138604501c0f580181900d0364120b0071200000d207081001c900f6550040864440e80503c1d00702c10142c018080c18402602c12265901d02e625070303441d44410100c50501c502c43c0d013440b103050b000800f44020b0b015107807004617004000d000c0740d03058224090301a111340c001400848040700545400c1c0000d488200c2554020f00c000c80f8440010f8504100103040000f680c0602c82da8a04040300007540324031190000401402c1d007001c1002241114100003010b544211026800398081c00e0149156001960316a011904006800c0d101030742805011441114a03044169200c001c410420f042c02c0e01c100f0100c0340200e040d4441d01c011115605e009003043c2c149030b000000082ca06042034020684190030840100d0b82120005001c021111108006040a0308902685980802e010503103250018 = true := by decide +kernel

theorem cover : BRFrame.Cov 206294964 206474820 := by
  have h0 := BRFrame.cov_init 206294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 206294964 ≤ n) (h2 : n < 206474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
