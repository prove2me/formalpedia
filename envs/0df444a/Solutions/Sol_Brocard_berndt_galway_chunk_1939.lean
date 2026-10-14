-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1939
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:13:44.953686+00:00
-- url     : https://prove2.me/submissions/4090e559-8bbc-495d-b6e6-11d3c47a0cb5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 348561151 ≤ n < 348741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 348562401 1250 348561151 348561163
    0x1306080615070510051503061603150f05030c030f070501050318010504030807090f030206040e07171608060108130b1b0f0405040b0a051f0201150909150e07061103070204050117 78
    0x103280e840e410941c030301b0a15200000c0e8aa0040982e0741d01680c445600c240890050825505004051100d0a0001000440e903016241510011000d07102e00d0b9502408142d51150802030004194000721002c111941c05070020f55031103003d110354400c41503125003916085510495003100803a914030103100c1311542c001080b00241840f0250f41d0030690654001502e80d0080344207190111200500180c80c0030300c20900100b003000c0a020462090070000f400224803079440e03a0200024079103400089041d84034007503e6004032032100f490350301c140050310b0710816000001d04984003443c1d03907544c0780c0400310f00130b0040c03200f200d107404015160303030400c41080305a070b159480c03480c4a10401c100034041951040c40751040f0240400c514104501c0c2040d09a014240300407e00340c004007800d01c00948030304141c00200106119400c0c095416240c01255000c40f1440c5c500d0102592260f1000e00c04540150080200c12492004a034240b05c8940e000030281d64098200c00e14005a8a00ca0b1000351410410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 348563651 1250 348562401 348562411
    0x1090b090c010512180715030e06010f060507031103041409060a03030509010c0c032f0a0303020304050616140f060a050c0d0c050903150912130608061507051005 71
    0x28007207054007030300028000e0064018a01d0340c0556080442c0440003d170070a01e821103148400c0e00d580a603600c82c03070118598082400340100741098a48140f240010541c1c905882ca0101500046400c20204545030f41142004a05100300c1c44040c403400c2100300301400050680c4001d0111035250781091200d83d88015080901a00fa400801d10004e0380110903203403140000c2c82c00705d03c0e40b203650810002d0401a580060100c0d08085a1039141e9060003007802c006810700a0003820b0640384000384131032008681310240060700305220503c02840e00c0c9005101941c00c86238690310b03210454950380c00c00b0284400142d1a43d1055504800a0006014450703024100300020400c6280010240660340310300c50b10800c2040d0b9032000707580c540d400380c0140c9510944c05400c441403030359054050740c1000401c2d5046085407081009001800310180d048560000170f511100316124645801500d4907000600b0481c0d006010700100c14170f0018900240501502460041000142002c4005c04407000901 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 348564901 1250 348563651 348563653
    0x80c01110c0709200f070606092316050c01021e07050706050a090e06040f0e0c0307050f1f03061802030f010609050d031d19051002030c0d1b02040e01090b09 69
    0x1314014608448180c108002134034415907656922081600305071512a00400074682032405002098160055200d22030520b07011525400b01c0d50400d090041020044940031041c45000140755445840340001e001032200c4000090304100040c0000c11040001c200d01c01580c1e0400b061a0061001c200183c41c0240300c2414400d1030a82c07a140005e1072a480c0740150381d42d0150400210b80c15844507485800c103940b00103005c010794600e04400030785a848454043d4030a11403046e010440e0f141c0aa440300025100419001224411011030310392140c5449201c02416500e54000841d19482c0c2106060402114001641e0303150800c40313003600c2801a0080310410130b4a0f40d040c049a00e868084146050305410458181c501d0b000405404881c1c0b00791355070b00112007009004012031a400c112090703034030031540ca4180000c415000ca980307006161103100d05500c04441c0441450040c01d511070032118586010900540c245c020809640600c901443c81d695280070203814858400c074150342054880e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 348566151 1250 348564901 348564911
    0x180b090714030a03110703020607030c1a06130e01060b03040f12020a031b020307091a0f030d02191a0103030806040b0f011d0f03010c0801051504030c030f080c01110c0709 75
    0x100426600e03940c0440003805d1210505607421000c5c4d0801100c1d00850740240841c6c0e45a0703031890010070039205244110344070b160549020003010002d032101e070f203e4030001c0c01200c0d240184901d074034040e040310104170704655a52900400d01d002440002c511076800f44039070181400003443d14640015420307a040003150050b400200001ea480303045041281e503d140034410022150000904200b240c1c0d02400d802d502d000c2e9014901c50745089900a280406c541181d088081c0105040d100c4411080c00401030700035020034210b042a400e043e1410350701031055815007940c00717008403010103401c2e0000e0300810480701c10070a00d4503041c001d0103135079103007600d40302e001400800000c0d00d640c01c0190302c0304581640e10f04003910f42e1565180d054031154000c0090140140d01500078011207828000c042c05507041e40502e14000c0743c0c1c4422541100ea1102c0c035900c880d40b86499005604500d01801c0315503102c10410000c1c800000d000b00110b640c0c43c031704a5541c031100005628944491540701c0202a8106 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 348567401 1250 348566151 348566189
    0x7170114090103032d0f020106060207380a0c0c062609030c1902040c05030c1812060906010e0601020706140a090302100c030e060711040f180b0907 65
    0x5440c0c1d54112503050415144142800c000d82c072018a02c098040040002036040e50007050788081e681d840203400350002c10566854203000c90b2204041d020f201c10342440d04440e490784e100c8080e42228143da1303800c4100cad1809210030501420b940010f034603e000a030000690410700130340c070702c1c488010501414800e44003d00b0040128440c50b5040000f22a84626030005400d03003003e1044a40b43c40c021418cc90080070041c4005400f010b100d1002d030300030b1b850034200403021405801101d000f003070054a42414488100680c20035a240340c1602a041070140b402c0550300d400801900d8001c40c801d001400e040c5d0304000c0d160b00f071004010140750440d8404003080004d150032820076440c1800040310329039580300316041500ca1b01400d50009400800c20440020a103902c11502907480d40302e50b0b22041148441d10820000d401a1240940b83c02039540d601812403a00b640900c0304030306c4210010404050030710250030500c07046401610780800c000101f02c4207107802e1101002401042c201d030034981c226 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 348568651 1250 348567401 348567409
    0xa02040303120914100603050708010207080d0b0303070204060e0a05060616031b0f0c0609080d0f0e041409070302010806030604030e1537080c030a18050607170114 72
    0x7031070302c5601c0c0c41695070003520203000001c5041c28a00d243d0700221024810150030790401131000388000d0302c0600035050041204601030007103407182d47d0000034503400c083d102e0741c440c001040610803495052100304241c4005840c0c034003642009080c801d0034441c079443c0002e8204107039400200454440c8034100f01016540d02c7c04900315400c0d942619007580640412071842414440103070000e031800940b06c0e080003c10855055000668165036a1440c9141e650a90959114403e285842c041403011508400d918400c2101800c130600003000804c0600030082c44466020054171942a0703a04049818001e551300030883e541c1203001640104168076040d00c0c001c1c03d08601410f06403144e0300c0302e01140b5220f03c1000954025610030994100d45140540e400c0704604111300188120107003400c20003240502034a007a520800740e05002500d556112203a003401002070f01150681c03541e0b00e408a1011401c1040380794400d0b60700e5181c80007588150415080b503090140d0119007041c3c1e821201070500d0312 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 348569901 1250 348568651 348568667
    0x21f0b1306030b060a05011b030923010f090e04061a04060801020415050405030d03020a2105010f083403050319030e0303010803040501050f09031903030e160b0f0c0a0b010305060a02040303 83
    0x9107a40c10108d50f0301d168030701240c640da0306604c208480449502c0381c01c0340300140f1403182d42031035013600c640c0c3e2400340c0240103440488003031203240c24121526000a01050542d00000d0b51403601c020008841c41c5842d0001c0e0846d10160448020f680d030100301480000c0b044a2a031800300303003e003072141c18180303800d00095171a07101c20f10000c10150041042c40b641e50042061b88640780c880e6650204240d00307a0364200060009220b01384003003104a6000602d07102c0880d2003a01c095062042a0341c0d6018140b01081c02c2e00c2c2d4000b4040b070394100c100000702190051001e441820800e44d8a4112501080002800d030345031075a08600030340003040100801d038000411581242d10030700700075460722914540b01a150103031680740c1c1d40502500e041c0340c0f0302c040464003045a032132080c0c0b0100f002c07024076030255507101e141d04880c40e107001d44000180580e02a4101505103503101d600034a2801030859151030410391541030445450208000500410206000c92644480011011418030f072a40e02d000303045030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 348571151 1250 348569901 348569927
    0x45021e221202031c02070315020d1d37051e0708030d0c05040306020a030b010201110301060207060c080c0102160c051c03051b0708030a110d021f0b1306030b060a0501 73
    0x1213060208016050082c440c50b401160440100f100310b0300f100045001a6001801c2c1c54034003441e040d2100001c3c3d410503e03c05c0465046802454114034980c0312180440d141902c20307000e48045401800080c110000344450a07120b0400380a01001035100400e110710030020600d6241c0140805010111000045d500c0c1041581d202080ba02c000020a50b11841643c2002c4c00b07035400051140301003500350300b01d2000c143c4284c0c000c0100c01d107545003145860000303000b001c006800140c020084c03644100c0d100411513008180d12464640b100c121f040c22644007120740d0142c000600c107400103001010100700014203068503070203604507035158500750410b03504a00505001001c2174041a84035010f960303040f14509102214201c0ea00c3e1000284c0da030b00a0007802000900c10751f0b88842c480000b10300c80d004099030340c00520030400511130401e00160403004440d425640c85078085100d94030000095000c0c100d00300001501c0c0c0c01e41c18180c401440003003895000e021003002c100440e0340c4c00501d107d945 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 348572401 1250 348571151 348571183
    0xf010e0f0d050f07050a080703080a1a0d050f070801050103031704050606060705031605011a040b090f060d1b05010906170402060d060f45021e22120203 67
    0x2030303e0100c07528071070390280a402506038405c0b80c0e941403c00c00c4007001400c00f0340c00303034403820718940e605281c2c2c4080e00d00c401c8581d52185907260b8480d0071030501c0607030851458400d000307170740745c500c500131550b4a0b1a409500c0134540d03a44810040090541008040040d0308510b284107409142c5901d425503504d0029240314011172000404400303001013801507441c4003881d0960b00742902d40c24145680600b5141840c80480303801c51030302c0c1c0c8841c07030203106410074440c000c1d0240c007281da140400c2c035088803401030245400c60408148200061603407420714804800c3c0c4407152008074280740004081d13070001d400510030301000c1c0b0080541501ba420902d64041d40c11142d051b6a14440c0c4404000b1300841d500140c4421481200441e001020300318210256422804e402c0d5094103d110801841407483c10031741d2007020910100724051910b400078811850300c2c08880b03c2e02c90b0544400d1000d9484046001c04480c10f480a001e4900c4240304104024141180b1031440c000c611f40010b42c940c00000b05000078 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 348573651 1250 348572401 348572407
    0x161115070b1b0702040e0607020601090605090a090206040803030703020705010b0103060e37020405130b01050a0c111c051b0f220501030311070915140315090f010e0f0d05 75
    0x48102d5882c00c803200903501074414032020359906081990f800c8161403182c09401030a001040b032100620410381112001401c1c80180e49803100e0303203001408510f00590b04844108008100f44104000450242c8000d640059139032609007030042c02c4503c6e1150700f078105410100e0030030507540c6480800d90004540c4003640c021864001082d0054a40743c03d0761040c0400d152840c140300d0034694068401c8800c00d4602841da44010545442110300344030360f041c0455001d01070a20118418480d2840b0184101000c03c6e04070030303110010b414503401c11046c7d019040135038402001c0000078002d211003120458101900445501c0005198049100c4194041c4400e510005005901811440e1901c008200c0810080d40c4a0034010400b20b015490031303d01d4800c0c0f070400200c010b41842004129490041f0b003000c0503041000c2c80006010203104554944500c205040c030300c0e51072030a0540552401c500a0050744428041542522403011071099141c004900e141c1c1e01460200b20141000c6052412590b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 348574901 1250 348573651 348573691
    0x1121031909020307081b0603010b04180e030d05180a020907050c0c04050c0c0607141603030b0411030a0b09090d181e0f090c021b01020102161115070b 66
    0x400000c5800b940c1481482c40c001120b54000c82d0728910421481d402102032038125040c08040e202c00e20a00c445020308010030032100c80941142c00390700c034550030049a06c100d1014403502e950018030309480c900c0c0da00d8007070000120042c0d5006044003030800c09442c0304121074001600e6a80010800c3c0f090120004070780034070f41000c1c08604510034009000300210304185184201d503402c410f50300c0742c00d80708000120301444c0c010402c001c201c007821040c8524021030300c45208403000d24218110107258403010201050780d00c0e4006d10034590051003005403280b81c50401c1c001960740810249000390035401c1844004031010a8078820010182001003182a040611502d044544d030b000c242001d10548095840016000c560411242c10703c80020729141c503801c00104403041e5801280150b48400103e844100803c80d030340da06200c05000040c14103104000300300c40030501c400d088079000030403041780000d441c0c43d820340305c1804030080c0345906090360340d03903444c0d44044082c100640300380d41d001c9061 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 348576151 1250 348574901 348574951
    0xb0f0f01050904140402090603060112030c170a0e04240e090f0708060a0c090e0f2509050411030f13060b060c1005181002090409060606112103 63
    0x3010b261028008000d030216144002c0c95064042e101240306080000c089101482c1c00070321541682d564006450615101c1d0758241d4419098130022165030441d42c0c201106204902d0141404842c035455080c41221018200030849100ca031440a41c076054403840aa002d20f44101c0c04292035a490390304569480fa641c14030b1802004003600e109500c075040707001c10103030400300d00c0c240030307103e6041c041c00030004400045d42e00300e8460041c4000c0c8400b1100017484190851280f503004a900c080403000d0940911000d900d105412034004045294a00d04001c03c1c10688507000e0758104046280b4114108140d154044050203021003100b681821600d00c1484034940c88514111402089140d0720a151000240c0303581000c003c0c130f0100e07458000010408010007501d900100304040c043c10700801c2d840101c0d4025080804070940041e070f81c2c41c0120000b074a034800c540c094802c03a156440c000c140703140d46074034005903904540e07240156290717184112007810301900c0d0068002d401030020030845015103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 348577401 1250 348576151 348576157
    0x14060702191503060902040302060a0c0c050a0b04262d0a060914013b030c0a0c080c030a060b01020312150a060302130501030e070f091409010b0f0f0105 67
    0x3001c603902108100007601207940480c0100e01060f6103007406019a03c00d402c1080340602c0c40082e4119604115103052248960310301c52085106421303a040c810b442d14041154400250440b0019040000d1f090050803290410395070f01c00041105121400c6c000c581c0741e13440d0310401611814001802152020190f802d00c1c000611030001001c4824080d02030416070b0150056140940b0390b4202c9103001c0c0c0d0081c0c0c040c0502180c0c80d0b0154401404640f050700d030010030b1000841280c0300818440e03510712441d00d05000901058030000c0c001c014640c220704251038000079603802030001c0e922081c683e000a86010429450594204038002803101035030300142e00790712034a089003907031070500410002d2038900301c001d1500703030403040d80c4200303003103894060517070492007141400a43c02e1640c071420009903100c2e0b04500411002d502c103403800d940d605c2c40302440c004466040a000b031500c41700b484070031083d10310119501c510000000d002848040380030440945c880c0c4501401035071020352101081c0d02410031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 348578651 1250 348577401 348577429
    0xf060503071103120411010309120e0a030206040e091509150a0b0303130611010204060503041506030209040311060c030f0f22030c0c090b090c07030210060602061005040614060702 79
    0x43e2590f0708803050240325000030841d012210050391554038034065110b4030881d91002c0e1701014440b500940828242d600200550006601c0520f030400440140c9401029100914503076200070b0341403c10130142410040310000c00d1701030300039103420003030a8400080c0b90a03080580503041f9480d41c42d581081d034080d02034240b40c25090320000607020100f241e5001440c0413903445640340181d0342c14948243d401e07480344d4070034900040c0701400414017080d83d44141545038072004900240391603a03a03000c00c0b10002c2c00c99059000c18031107142061819000e0020a6020061485540c69031030724540d10040c140002e8079101c04060028001100700e0205500c0e0800b81441400d02c1901c03900a00c0c0050106c00c5015084420592100e0009a1300440d400f0700a802c1d034004050082c0c9030381d8486c28100e190070140050b021441900041000c00c0c801d4070405001e40382c207030b015220615100c2c01e80c200440c09603100c240281c0c607100c4100600003400103a5880c0401c00c031002c0d50b8a0846000092800d000c0c144 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 348579901 1250 348578651 348578653
    0x70612150315060b03060f120102120c04090c0f0c030f0212030a0905010608070302100507060609110403021c05060a180b100501021006081f09060e0c030f01060f0605030711 76
    0xc404424090640b4440c5292000356105110540c0c40d81100000da0000f5140355800c0b4250604250b0113182170550015040140b40005040c50302100800f84500400d079043d0b00307910f4001a061024050364028060100520309020841042c6041300414031250080068200a1600d000c50f000e61b109000d65000070801150407620ba09205a00c44003c0403901403c603030342c2d031a103000000d04100c0803400700b0850b900200495000c1100103015111075100250450742503a03903900118416460f4030512400102c100d60154807a030852052051500b000d40390040e40d0070080c0f07240c8000034000902030307074009101107001c600002500000c034003003040003000400d28581d04040000910390081d84c0c03001c0f11001d80c2240c2c03c41b52490140030440f00c0d2402005881d4100c4c07400a07440c07010000d00d400082d04601d40008100039036490b41b4088031708241800406400001e0b14440c1803400300b0209140300c1241008104040c03500f540c0c020240f22a100c0d6400303100700840082d080c180192941070300513030510 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 348581151 1250 348579901 348579941
    0x2060301260111090307080a08030c1b240903120c090105040801050906040318030f120e0301021201090c030b0a0e06030307020915030709110a031a030a030201140609040302070612 79
    0x1040401136000542c40d01d01901c2061400a11010001503110415402015492543d104d444a040c4180d118811117596600400c0ea0858100b008103c426100e0035583c03551148241240c0c1c0300091076401070f040301c41c83c1c6d00a12011a85030740c0a009590031158145102c1e955030381180040c2d51714050703548a01b0b019464a000c0081c01e40000c00c00c240320394860b43d00c62450b0351240e10700d40d200c1e103410b000190810b05500207807800501d801d017020f20038026604007140d40150180000e0b00f6644032050820b94101d51400420480005001e04141300c2013a0600384902d00100c40420350100441c071640e031810031403202048841c0c606108445102c0d40181c01080140781401d142140c44007840d400c94024407072207400150042442c4030700c401c46807015039028a41110018200c000e0448030520710380259240380752000d036607000c11001c1c00f0a4800e070008124103400c460800d109010060032540105190b10800000940c045250340613100d040c1040180b902d40e4000e1040184104c07900e0150400c010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 348582401 1250 348581151 348581171
    0x1380403080310060504030f0b0a200c0f190204090c050d050a110904020a050909120319060b0a020a080a030e01060311030d110c0d0f1205040f060507020603012601 72
    0x1c0c0d00443c42203030422000310f0001c0c0c1d100001c50300c5128a02c0042d184e0003409045000144d0500010364110100f141c001c60800031941c0008100510902007036048100020264194242030080c1052204a840602010741e848240c1203412030340540020b201e107603612803e80404c0003c482c08409000098040340d400c0ca210718241d0341e1641190015625054000c00900c0180742864100340321700e0f400303060210100d1804082c00404840502000c0c0180215120341c183e007050140910b1080c2d4680c0490300c42140d04000003001c44503140c008000c0c904007041400e00d81900020484806644056110340e141081c82040f40100404a402e001d42e50030002c001051003248180b003034441508400740d50743e8292850050365030035420a0328030442e82210b8a014000d1a0480c05091440d00640000d2000000b0b42d83e80400749034031117a6100800d00c0840c003445680903440c5010003030007050800c589402200d03000038440b404140302e1304e002e6403901c1010007405100503031610711b400079010003030040140f4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 348583651 1250 348582401 348582413
    0x9140a030e1c0f1520030105012a030e03030c030a0c0b070e03060c1c06030c38030a0207020d050c040b0d0c03120e0a0e01030209070801380403 63
    0x2421030410310070105140300c00200e680000542d01c082e07030f2040789010301011660714402c603000e0400d584940c0c20350340e442c8440d261591103140c2a0b2045101d540c50307641c0d0704080001d400740201e0304000d2180d1a10f80040085c0006108a1010f001c1d0141001807520070303a48006071461240324030b4001c4501000c224004941c0c3c11072a410503c0e0310030710b02e0324101d984001c0b080700c220082004d125030692026004c40e29408100008010000b01c507944505008207404982d000e40f00d850f8002c039108090444c2c10050fa414081d8100080b100780b100030400c0c85101c001348481110b10010b81100c80c0b00000c0030456031211641240c3d9900e6028015000d20240d609200ea1101c103181d415a014a0401003021950b00c1e14100c18102160b112400c80300c510b0442e100c103404120500b8580d0180b00005101c1c0140b42d03903461240000b01001000d807070256055105109081601801c3c420500ca1070400500400e280d065650401e06040116101d01003020a110741109130f0000035034588180006010040c050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 348584901 1250 348583651 348583667
    0x6040b120715030c0806220216050703061a030a062309102d0f0b09010b03160806090601080603100f0b03120f09130b09010605090103050a0b0a0909140a03 68
    0x51503c040224964481045e034000d001107401541c0001d00c07010003038203049410b450002c045407422006090450050054210240300c500540d010f5110450070030400c01c0900540489480240d565100c511660300401e5546400031401845c06481d10035001210380c191100d941601c040282441403401d0803440251500343c5000346080090070301035061905110300c5c400e204050400710000c240ca8858207016402080750f040e0341c0c0001074440076402d901c0da64080f0900c0c068032851501e40c1e40ea040036000e03251340395185460a0184401c2e42e080112035918800c079954080800e0130482d00c20b03600c40700041d0a01c0030406055444602d8200c5440200b4825400001d81c08000e0b412202c02c1c402089882145001d0441d1030445c1c0c0308100402100da003072035840800700408551012031401e8014002411440090700120002900803441c02c2c125039060192036040850200c0c1003209200000c04a451120320740210382449481d10994410001480c070740300e070409210000d0720807203c001d18000b41140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 348586151 1250 348584901 348584939
    0x3190c02120706080c16150506130b09010302040c05130e010f0501030e03030c0a0c050d021006090209010f030c17040b0601020d0f0507030e0a05090a0b040509010e0606040b1207 78
    0x1034008404003046240050800c05941a0341c45a204ca0740d504810102161b00c90b42c0701e8552206941e440300002500400c403130101c07a10f00d80b0081014a040810300080c5005041800300786401c10039444001e40b6411403590651f601500c1c08944445481c200307450904c44c00845045030940c06000240001c00340c0781c554182d41b01032000c1480d450707070b440044041d07460180c80c05050313400410110394400c03c0c050052445c3d181c42d0402c403081141e540c40b40ba041c41c1c0482440005608000b0519880d0002e520800020b481504003c500308102580000c0614004069070002e042d5a0800c114400340034165449a0001815205c3c0c11031604d454070003da0503003550b85a0240c4101c64491000e00e000381508420104203654260414005c0d440480e0502c21000750950054070555000c625521000c0090f807080c030310803001040b0310004505110494000920cc10b6442c1d02d0100c11550f10900807030700c6500304200f1a4082a180701100002d1f0f4018500c4201c0410351203840d000045404845000e000c0c85 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 348587401 1250 348586151 348586159
    0x4060b120705090604020918040f02420a0c02010905040f0b030d0f0c08030c040b0c2506092903010305060a1415060a0e060c07080705031506060c03190c02 68
    0x241c41300828041680500c51056510803603101100e620002c00307020030f550088c024130326144d80c41c0d05034010840e13140c6038480c10b010303522040c82d12500da445404046a004641e140c0f00c2d200a181d003d101208074054140c0c01c00030800c1315036007001960b1058000c1405041c00600c00c10103184210b00c41402403a101c0d0445001303020300040152003501038042c41507900e00545414006010350b81e82c0044941c030040541d5890b01c01400041420201e920160003128070200c010120141c44510f2061001c0f12a03003080310618402001b484015403101d010002c0302c4800e00340c141c03a000c0c6000d01801c0c0a20000000b41503d90200000040c4103000a40c01e018083c1d004041101d800001500000e401040f2614042030025520350215402c003a001414102c0c01881d165880f444141c1c006aa9540403180301c405680c400802170000030300a120100c0141821001400581c000000201461000a0505101d41c02c0030820001c011f005004a4641c42c003207845000c1040c24454014080100400301a13002e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 348588651 1250 348587401 348587419
    0x20d0b0114030c09060304062a4505030a0f0201090f060c0311030c0f1c090807050f0a08030f040e010602060f160e031002030a0b0603040c03060504060b120705 70
    0x7244660202c0380200034400c3c4a030b00e400d844009001c80e035400503100b19200c0c3c0d6900440c20540300c001680c014455050000c10241c4414404010200c1c0c80468151542c014032200401030403620306103140e400703d83e504803a03e42001d000c240210000c032686c0305075050700484c2d041004210b68001b80402d2240300740c0f21207029035241c2c0720000c100c40c0603000da9004940407a90200103e4001e503c030030401300040b801c0381d04d0300004910345824540f41c2c0140015903402031610011807055241c1030b5020340564078101307070b03014a4103140c203a0310f40103445042d00603c01c940d9061456213400005602400846084039554080c05918200035801807103a5921040c0410000c500301d88041561fa00485244240e200f5507159107040300200d01c0702036012000c0c403102011048140d10240241c655804050301d005840b0301c0c103104ea075015100035229940c07007841e04004010005071186038002c2a41e410500010b2136070340368a03000c0d008100b40d41b400ca5001a40fa02c26682d070b400001106000c0e03610684240207 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 348589901 1250 348588651 348588677
    0x50601020622020415150e04110c0a140106032103060b0703020c09060301060f1e0807050a0303050a140403051b040c0c11041103041406092419020d0b01 67
    0x10001400307410003030709590a00704a0015103080e82240e18595041d04245c000b142d074413010705032040c0ca010450008981c410742d030701001d8a030503c0b0710107480900b04d039a240b40c1958000056260451010300901904028401c480f00e60000d6000c80c014603802030500c4a0040c85805042c507809040c142100003908101d404101084640e003500c02566141c2c00600c0e1030140d40b4100000040002c06064041d0b41c0c07403d0014503030042e400c0038001171100380480c4044d603e03861501c6a1542c00c5402443c034903801030804022a45581c07071407908591305443c065031960b8401350110780000c00040c200b0401400802c005c800d2200106161120f2240c1880303030b85143d00d604040c4401e039404202034001080b6000042c001160603100260725480c80140b000808000d2400c110301030350020381e42500d04505c110106000c4c010304100791900054a14010601961030905c210f514800c014800440c41c40054085a80290327a4020883c0b00228400103644402900322100000e00b40c1180140c00501030031440300f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 348591151 1250 348589901 348589921
    0x80a080414011413030201090b010b04030209010512210c0d11010c0305070203091c0f060905100908090f01110d0203030a06060504030c090902190b070614100509060120010506010206 80
    0xf0308842e100d0340e0b01c10b2607601c45002c0d80c0103003603895054082d5525222003000241c515038290703010f88581c401c90740c1c0701c50550040c000b0440c416000f19016252610035002d25020000d10710240044028044a00f140700c0421050346005801413090107110b090361190109400445640c4d118021500030400304c19100c508405580007a00d00d0005600100170001085c204030726402856950640b510202c88026600e114201800b81c0060b03d000755211320040411109015030710a040841009020340d1400b500ea04049200e581c241c3c52003015412200c000d02d90082c0d03095000490100705a4044410400d0041d45a601c00c6403a44200d03881c02c1404911f1501540a9400b640e030000000301100e801c0c0310110b0020325400e00140d0384a01105080300c024442c1c440d103503000d07041d182101c0d0307240c12840c60400182c90717200b810911085040010052042c015040003412500c0441c1c00099a80360080181c070780c0c000070b125888650900c96644020202c05402130350140c9800c4c0d00312078060366956159 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 348592401 1250 348591151 348591161
    0x70506180a120806010224060a0e04030503060f040603083f0a02071a071716050304061a0301020d050f07050a090b0d020424020606010806030703140a080a08041401 72
    0x2040c2d00c0401c2081c095681c07040a500b0307030100c0103004030340c1c0a501002540c41034020007100319210702c04010401c803075030070205485d600401e251186401d440c241a41d0107042030000801050041d0b15403101840b0907691904510001e41d0030500507640d4506003401d000710024a200680910050500421140400c0003031240c0a40c0c0411a81451621601400c074043c2d40100f0007501c81d000700d0142410141d81c034648190107002d41b07803110072103442e5048240184800c01840d03403001400380d5400507245500301007140d40c41544508009405c40a540075818103c855185181d0950720206034a01e40c18100e502c414081c110030324006039181d40b4080c0480313080c400c2820300d0000170000c1e5010880903910340c028104203900c4000160606446a010340b0f0501c45a420a80f9103101003115419140e8040c0107290300501c081c80c107022107180c2480403d070303250a140b0004102300303202151013030030401c01c4c020308410310740c480c50541d90f444106100404490b026501580d989032a089842c240b030700d0512070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 348593651 1250 348592401 348592403
    0x60901080712150603230d03050f16020a0501050106091403012003042d11120d0e1503010803130905070215180d0809010c14181203070506180a 63
    0x10708a1240c10a80e1071040e0341c000c142c3d200e11a42c2d1039100c0800000c03096030031b80f814048242c0c0080280d03c041d40b0542d160540703070b103006414545400c01740100d41e0310f5140016031091514114901402441100301e01d031040f2410050105e51030600040341203980265094111105421180c0b80002c20504150894124009410501c20100c2542912030800c00203150b1140c00f6142d00c110300c16250482e02c0d00812059208075070171070030304804010098124920144100c003a10130310008032641842c142da0fa00040c04050038013056407880301980d82c4885407546101031032850301e0340300d5a4445560340c0d245c2140d11800b0640b0410200480e00f8003840c07090b18420503099005101e000c0c242c0390348005175030000d08940604012003003a00a842d500300701d0064004210703900d0070003d00d80700c41c000e802c54a0048106080110384040e445a510704031301a14454422207084001c486044000540e0001c2e9000c070766030f818040410b4940a00c0f17000714600b40705114003e00c1c00082d0140c5001181c603440402c030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 348594901 1250 348593651 348593669
    0x1051f0302101b121e031503020f030f010f051603090213050910020d0c080c0a050d0c030e031b060c07020303030c0a050c1203010f050f031c0e1201060302152106010216060203030609010807 83
    0x4810409481e001c0100142d500c00032f016a2000e00c08140090709661050001c201082d4880d424070111910400e44100a205a49000c1007800301503070021310f100d029000401c0c40c8a4030780011440401c0c0621a21581d10300342ca07021561030300d0000000010b42801800d0310302284030f9500185040c4910400c0b1008a503190f074480e86491400308842c4000d040869191081695504c002c1c000720900704001c180c03942a04001c0312402c8070101e842803611800034803241d05040305020310001a240003080d6600025100b244540340c0d00003907800c86036402440f00d25001449101b40040c0e00c900b405008605032030090b11509a001d44540038030801c0c41400c1c044607010791192400940080307005005d810340b41198545050502800400914048030524000f440e0365558002002145001d45181080484840d011030070401100d02c241c403d030400100002400040c40009000c9d40e2003402a8000ba20180c01100c07001d03511a40000d50b240c0084030000d014184e500004110100001030403000c5881800e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 348596151 1250 348594901 348594941
    0x31c0e0405102108130605030f010602010e0307080c010e06011e0519030f020f04020f250302060106140f030c040603150305030a0f14030901051f0302101b121e03 71
    0x110030300d03e0401e043c141038a421200313110121340010060310010081495640301c036143e04200c40000c94144041e0701c000c09582c03500c0501e600046011040c3c03a111500019082c1d20f401c0d42c0340405000d007400310001c044a009610012030800c800282250040d1380720703c55011102d4a4100380480c170342a10011040340c0b401d0010400005540b03890100d2418801380c081d20501189502003000da8100c601b944c07003a094049555082650010054010305003a22400015109140c80c0a912114107009503020003010702e15140d1445140400c40c0c0403404260086580c1c0c1ca0701e21800701e115002405404006410401125000b84080340901d06598201014615082c402401a10b01d15000c0300325505001c000ba8000c4021040840510301c5600c941d0008507241c607001800e4413504548000c00020a0805501031000d6101c59010341c0c01c909070303800d04420042c0350b00d2508040400391800249641103800078010b445510030845c0343c0d4030030380d20350b044060006c100381a42640c12600c0c08642000c400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 348597401 1250 348596151 348596189
    0x30c060207050c03120405120c211e1506062712120322080703030b21070806090111191106010e0709051e0f031c0e040510 54
    0xa034024080c0601c02c504480c035078425500801e0a11114407882109a40301007002c10503410880b10013a882d46902c4040c01c1c0394031314240040e40c0314000c00d620b04a00410741c64036058644080120202c2032880c01403e96041580300c12450b61501e89411a40d143c41200f0085030180c104034040d213a144604110642e1482c102042003032090030500d15842c0d121030400d06003002200d0500c90300030701c82e805a8034943daa00c1c0482106051401d50030940c1d4480720982284400708100e0b000b0b4801c075a0f40343c600030a40105060002c0c1514030304105102d807090756010000405507000480400b01c1b80c210094540aa07100110350307089907503a204102d22000d04120452a0340341070003507542c6040c0582414540620742d00d680502d0600d0981182d0b05440c20305043c80590380c1c00550031001400121404c00325103c048400038400705054002c54041d84a55030801d50660702030120b01b1411b003240c194090781001d1000c0007081910b6002d1101c0c0030f075142101050343d01d506501003070140d0304403090b002414200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 348598651 1250 348597401 348597413
    0xb03061507020d320a1407060f03230a05100812040e0c0d0501032a0f030305031008160614120106080705040f1203030b01020c032d0d030c0906020604030c 68
    0x84c0503140354807058103015901e080c8106402c041480320f42c00040c40900010f02c0c000000c1d1b481c204403080c00e41c0c030000303080101540c00940031020084904d030204220510300c0d544c1c180c241c411000002c0b031520303280810862032100c0c1c1c400d610400403803c1000c02d00d90754440362078541580081441e10950104024401c1851940c04160091800d840552404032120166012030343c080e00304a5503400d0341c40b4110440002869148901c21140c99501c0c601c51502c1d85600018175540300003030a0082c04800111241500d510001c000d00d40c810a0750764034120304895002241c854003810021038540c001c00b641120440003902c641d040c8056184241d0b908081013580c410200421100c1080001c0202164030380000c01d0000041948054001d035020311464043c050740c40d0081d50300d0447d84004501d28465a00064260f032154054000354883c01c00c810b02e0203650000084141c00c144070b00c0000002d1103030b04d0340c803000250485948540c241178a4010498a801003501c024002401030004500840c034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 348599901 1250 348598651 348598673
    0xc0506100f1e0302030307030e240a0305130203160920040509180d021605030604110609010e031f060e012d09090b190216200a0b03061507020d 63
    0xc5484882c00b0f42c1d982c0000c3c80d6621085088000403444103503daa507003081408030001c0c106183d000104251891000390060003170341081420507403910f003c00c184500500f01c018100380c002e000d80f80012030981581d11242d03500c3c4200d50034a86007503094200780b0140341000480d40c50041c4100c0c0f03054644010040c3c0781401030107625010748040c1145550704000c004101004550303030050310000c0240800c0c42280d010316440030313000741c0065082100240400148822000c0221030365521051070800403600701e0504495640c00d4442d040e265044840e40360802c00a61989400520a01d034858070000c40d0301f00284103691455003107400c880d80c1088000b400902c0043d80d40c001e0741703803582c0d00c242035400d50320034840540c0c1e00f50f5070340e003802400d40e403400e0801449040304500b50701e460034941d01203e021907a148041d116400c050380b848a00c10180085000224005282104c100d0711222040c240da481a100c0350b200d402008003402d00c3c45900801e441d4103c0d0010001c101c4a4400d4491040b1aa = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 348601151 1250 348599901 348599939
    0x11e0203060a1d060a15020c0d0305160501060f050301090b070c08070807080a0305070f140306030f06010f08101a120a02040c020a060e010b090711100c0c0506100f 72
    0x801280200e90220394481c1e2a8501220f5040084182007000c144402004290031884113600e0251405110640010b5503460003182500c07860007109450400b21143c0c0070700cad045071300140d0004e6a0f81050020540100b401d495400c9004a00260784500305401c80300f103914010b201d0307015035000407103241c01a060260494054201b042c0b0f031034195650520158040513003107030503002c08105485003a6044c4540c591080403401d000c00300d00d150f140c01a100300c0c659a414040f10500100140d4141c0301405035422914281046034002d50310380c0303440314140c000d601401d103e9200b5507000c1400180540904030f41138841c0000803d01e8860344052022007046c0ba000c0d011144580f1740a81e0050700c0364460381c0e0400c111980500450f0890380f40a809669800703c41c4440c1e82e052500c0c42a00c0c0da0741c4140640c001010b81000c0e211240e0001c41d460800c40300c21076151586240a0701c115076079820803402101d580c07103942941c015586030403d00215030540d02501e010100071800612120030a9490300c0980 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 348602401 1250 348601151 348601159
    0x206040311010b040609051f05031e0109080c011b0f0f0c030318050313050901051f091a0405040507050a21020708041d0c0a02100c0c080703080106080108011e020306 73
    0x3c6000c140200701030310703001d034801410302e0f80c0c541c00c1043c061050304000d40011092030500ba031003032030500029628501d0b45018138540150f00d40c0461404804d5100100c0181e01072103050300e554401c06014020708900074031400b41c540e4a03100010661003a991050040f4094035411700484004104480080c160365003103092544c0c3c1e004502200454101c50f49201c0d1041c0000c5650b620500e03000c289024060b80700c14016404070005000c0740d580c0b0035035a5071494061900321300403140d1003000c5500c0c0c0100d6004403010118042c9101001690744028410340e07100355800d011a0726240411111032084144101c0094800d001440c008100008024091140e0180c00340c141340f0242c072414015440b40d800302c0009200f89030700032400c002800085521800210510b4241304910b0800b079142c1f820714141040165030b40340741564141c02203401040b5250410403490f203400c11890080c045a1080c060032011851580c00011000f030305014416001140034481e10617000d0700080f26000c0d40015001c0c544c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 348603651 1250 348602401 348602411
    0x611061b0c0312180d020705040c05040b03101508040f0f0203070f0f05030d020708030f030406150308070b100b12190203070c060f0b2b05061005010e0d0201020604031101 75
    0x481d040030006402d66811111148440342001543e5003c1034020620112050f0400c41d902c203401900400e04a045030b00070364021801c0034002100b140d5070322480c1c10844003400c010040c400015045903c0c00191680391001d08246120a2404c1c1c81010040390b00800070001c04808000040b18440000700462025080fa401030b038488003c84e414081d140c00c0f0200303070340c3e45581c100020325007004006010b03107580c0044e04446041980064403031040b128494a00e50000002c40d04000046d8055025118404101e00352a42c80b854080b8095204d4503041d1034602c0800d0200d81009c0090040f01e04460445607141e1402100341080c0c120076100820b42e90340800303c0701c2c90481c440003500095126940079598401c4c100640c1c40d0810845e0451440041d4503458590f005032951114540075040034000403e1461802c1030704ea0700b042c0c0f030030302d540e00500703901410f03051000c10300d00c0510020542d00c007600c581c0f01e80d03032566051003401c07116110080e005a01c024003050200b0300031200980d109415500100b5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 348604901 1250 348603651 348603667
    0x9020705010b0907030c08010902070c060f09080d050a2601050d080d0e07030b010b0f0a0c05030d2408030708031303230703080601030c0c03180f1203020105010611061b 74
    0x26540e482101d4042c0480d80f901501c3c0031490344180c0488c0944060300c030442c10035086480c0c0100303001180c001d2209206480c2c420308800f13030245900384024900c00080b0380c1d0321508140020103542005040d00007050345000c2c02080c050411009203555104250b032076245a1034502000300c0c1c3d6040c89426903008a00700003c070b021803d03e00442c640405054001c0c840303d03155103440650450164419051002c040c40540302c0018600211101e0505500d0200c005207468204907082d485100c0010000600e81201540c6c0505040c0c044004100d041c418010419a40c0700300390b44a100b40d00e0020002c0c20108005125006181c0c0fc0c0703403225000c0d1501c00790b08802204090f00a12840241611407040072030340c1420994440d0350154411400c0c038003801060468280a4400079490074010103021828a800250b5550400c003c4020400d4600d200901c550341c03040c43c07441446105041d80154200000030880900800c100d03034040300c42100a100c196500303d601d000e000c401703a044041524003085280 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 348606151 1250 348604901 348604909
    0x20d0e10110a0b0402100815061e28030c0507080d020c030a020303240916120f020d0b0303030f0c0304020102012a0e0a0503121305061c050a1509020705010b 69
    0x260603a100f480d007119182081d00410100281c840039aa0803c8040c40c10000f03881c21324609601992002e41d484c0fa103403002d050107110a1480c1c03c3c801511f55602040c10304a02c1600300d070040c620303001005041072035405a0743c1141135a0f02140454003003030301004240000303441040140030402042c9401400c12188040781425540001c1007040168008000c0c407003030f80c81c0e0409203040d141d03000e0540101030300c0740301c081000c0203001092044c0405800010380e5141d8021001c9211700d154002d130412102003024242c00c003d4010003030502c4032901d42018140c02c0d00300041228046c3c0c8100300719100503074901d0b0b0460000d90004100f00c0c115500c1d40382d02901e941e010f1542c41c01c0904a01c0d02c460321a94681002402965085d500d680310301902041001140c07404540354145c070300e0141d12140c1d07840c200c14220040c0b88107903008a80020000448206545c6041c140082103810900140043e03142d01c440c101c29500125a221540c000e26a010880d12a0590042c001d2920440000c039800e047c0c14002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 348607401 1250 348606151 348606163
    0x3090a020916030609091203050601020f06010611070f08030913140c1213080f070c0305060117060702010501050a06120f0509010c0e180f04030908070303021606020d0e1011 76
    0x1580c604803000e02e10500329416016500240840310410040e411258403000b0b0060a47e508820916a0714070201e40264420b22102c64031141c18401c0f2001035075101c030024a400c44000310320146009600c80400d00007200d503001411038000354011401c02c03101c58200840010543c40c00e43c0e041c2d90326071030789880d1081d070082c031071080101100c40d90301c03034481c2500e0600040d0010641c44d105c509003610540042d00720002c1d503081c0f21491181c0c68560240e0b15140e001d8808681010f420340c400c450000a2001291744e8a07031581c00d010098034a16103640105900342da20a00036145e004012840901c807807032260b4944440b0301450000800d01940c41c16101e404c584068a11544903511118400042c5800c04070000c8440340969084032480c81d04141424407040140000e812100c2003808203083c9031052519038090480380c070954590030303682d00c0d0195982c180780501c0e41c02c0b00b6420000090450020602c01140710844e01d400c841c0d0039483c0201f040d200c030f03110003920034441015030b1544458420400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 348608651 1250 348607401 348607411
    0x1005061503101d1e040203060703150306020403120e150906030a06090509010f1802090406090212100903180e040b100911070605130807030806030a0f240204080c0603090a0209 77
    0x500c44050420640345035400c952400413010f042028800d000060714002402030744800b07e490001001d040ca8a4220301103401c691000d00402d00200f400f0051007801c001c005010300854484100b9101a00e040c4601035140e41000d41094405004190781804c060000b1a4030005c00f41000450b50307143d100301c600310345090300d403003030701d603546581c54151101e1a03c5507413a01170503003002c00603820381c1ea400034a40c0c0c0b0002380003c03c1141c4481c40d43d4115200c800082d228500c1c00c0c8155403441540c03000d264001c120501e41500003e08428402d0100300380c40891000343d40300d51201c2c12140e40e84d80c5603094681c40148c000c0001c0030700c1010015100f442441800256041d5800301a522050303070404206990000c4d02400019500c00070706030006403118200c428191341420489119507440300003e0400002400c0504218020700c400e6003040b0b04801c1601042075040c0c1c001c000001c40e400140204e0250f0b025400541d4090071440c40d4915258015540c0161040d0460350030000c0307070380440c0d1034803401d440c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 348609901 1250 348608651 348608699
    0x1902011716030f0b03030418060905010e15010801060509240d02120a0b0a3b09100509031803070b0c071a0903030412060b040e0708100506150310 64
    0x21444600c15031600078200b561800314001d104c26200e070000a80c4038403603031096141d5130040c2c009400070070809804c014001c00350b80c03000704010340e52001484800c01c022141e200b58125008000100c560080c030b0114143c4040390f40319402d044c141c0c41804000c4131120b01c50860300b250b002c2203100300700e101e1b0000c004416803400d0143e20f480c0440c164028010014151409032400c100c2507440544505100000b1107001c00700301e02c0e03a0202640c06a414004941c0344000c031401702001810141100d140e442e0261982d041251187d044240c41030703007141c4003030307559004680080010481d130022200c4c0c0003060040090999405541d1212403001a038480c80321100c050708922030030860301c1800d89405440c400c0585600e0b18042e01c040c006a100d00c190300803200780c0340c03104030b226052090f41c1e840100c1c07004014004101c0d444d1001102652410035200e16a900d10803050386030074a040c01c0c01924001e100281010880c9000031038001090303000240b050000300005140012440c0c07090410140c80e6203200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 348611151 1250 348609901 348609931
    0xa06030b03010b0405040b07080c040e0a02120a150312090b0c0c030f070b121819050d030e06011814040b011a0c03190908010e03090406050f0319020117 67
    0x100c00d060940315180112403090345085c003000041120a07030402d5001c00b4501d00206e5507036076242d18112501981d00002141c1751010104400040c8581c01852070b0085140c40000d15929002d810f000c0d9408903404201c144000c50081000403084d0030f607030003140e42034108204880e88078012841e864002d07182ca42629800009002c0321401c0510404482d036a1060141c1181401c00301103660500c2000840300400425030700060b0b001c6c01042c0701000445541060300c3c00064402c3c06020b00d8403a646081d00c19015219010210b58040d210300e810b038842c054003400390743e8030700100c0c01440e018090782240c0d8a034a074121560035070b4424800c07601c1144980e15000003941005010000300c05c2c4c082051518000411095502d038070000b083c0ca0011804545002d641c0c5810441110b030283c441e80802450740c00c010f401107081101001030046294140c0c0c0400100c1c1c0c1d520100001c01091090290f01600141c3e240341c607449812451503221030040c103104103050400c00306c0461400084841125a95403d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 348612401 1250 348611151 348611171
    0x120606090e01062102010c020a09050f06010816050d141305070503010504350309010b03061f0510110d030225030906051b0d030b120604081806090a0603 67
    0x1920032525181181e000800c682c40c149511802000e010781ca8100c0007101440107001107a100d11040d400303450b4081e1401c00010754901c1031202401c01500d620301e4445000000480d1544210780c02480f0f24101001f41d90550300600b01507035640d0044204d640340a881c0c203881000c104081e8517040c010078030014000c0c0d00410a040003410150103801040c483c0e41440103001c080303445d40001100c0b1102c400316031011525000d0032008607101d070100e100090310012040151600040d13019a081c0c0c1f42c02e400b40c03021a03446040c614040750180740c0d0302e4119031010805100e02e046c140d02000c0b0103d2030341404101c4103d0345400501d0950382404520010b600001c8110070707610b0350b4038034018048503c1032840203c3c11554010b050f560403800380004001d0085211503100d0400c1050348403800050341500c504101c0b1072001406003001601003800f9050f4203681e00c010003c00a0024400c41d040042a0f041050481800840a022240c41a44960188403010f0143d50f40d64410006003926100040c0008031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 348613651 1250 348612401 348612419
    0x3f070b0c0a0903171903060614072d0c120c0501110d0e060909100302180408030a0207020a09052703120f07090e070507061505130c0207120606 63
    0x802021040d039040c040c4020101140c014007080700740c0b903112550b1a4140c0d500d07188446180035115215000c51000702400080300d400da4046070070b94003039989102d90005c100c5036038881c502c2500c0f401030528845081f950720540d141c5c580d0300d50614605a12800002241e121000c0b80021034020303903e085035029245040000c07501080303004150a080070b03404600c0d440446600e0701001294030041c411902c5074410150f03550001c0358480130005013110b14504111140090806260204034000c5401c04080001d90240c0510f15124503440030b10349142d680c0c1d04040303402a4003e980b081f0b070840f00d400004a0200300500a452161207000da20782c1c2c21900b03503906490381c000e400c50104c4c46030300100b10f0000c0610030100d14952102c0100002d200075110020304441c02042030340709992030b2004006008042ea032000003040007a00640e01400841000040e00703202c000d075803058640c403627011400e00035041560307003000e0b60808460060318142c2c2e0343c84000c9030385c0c007030303103070b2040341c825640701028003d8481c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 348614901 1250 348613651 348613673
    0x18010e06070302060a05010f1508040c050d0503070b0603121b0712060b10181406120903041419030f0201030608011a03010f051005060304210809011802033f07 70
    0x51400005419031900500d0b0400022700c49a06c000c1025500c00601800315000d501d0b00100000f07450407940c0105400c020780c59401803402120041c44040100e030042c5000038002caa21601d0340c031128030f0030040260240c101180d400350007500d030040c010b001418401681071100c1c00d41c00303142d002c01c2071048002040580030300c0070464000d0020a02038000343c14014040502901c540d41032910240c45540d0001c1c1e581d00030b6106010607020000104103011b00003201030421108024085881c1321210810403000c80c030600940d8101704404c00341013010900b0b8620b12102a4018103002a125403907001503400e58ae0840c0042c4005244541c8481c20341c20300744121254403403034190400c40b03805d0200d81c0ba0b0fa1521984180ca20a59003c0302282c113204e0800050712111802040c01150710b541d80b203018105203000c442183c030551030842942c880f80389680b0328140890b4000d010302645c003100105c043c03148800c001100b041c111001c1c101d80d001c40c0601c1e6070b10b204094000d002500c9005600d01800404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 348616151 1250 348614901 348614909
    0xf0a0e19060533030c120102070507141302090d0f03030c020f030f03060d03052106010e0f030a02090901060e01080c03070b193f0f090818010e06070302060a0501 71
    0x501c001c841a4001e0039000700410b25181e101280048034540c03600003445c1882c90000250700800315144c9a0039050158002c0c01214810000d03150003a50702c03401034044105800c4010b030406c807080e0359094a030220758024070040d400106181464042500d441891500c12142140841d07078580d400b054143e01000810207003128100154a80b01140c84100c10350701000d44124001c0c00c0c451400001c02d405401a18001550f00c60040e4460401c503c145041000503201e10340400c4180c110132010742094180c1443c0c101c4050b00030240c00d4003680c00c0c0030081d00010081c1c0c1c029541c540c00401d64a4a2500890007000303d03800a007600f1040380105400c08450782d1203070134500ca0800c140c2020491501540444104030305109445881c04600348a2034403001d40c002000c2e20054041c5800302c1d00c42d0074416600c80d1211000c000ba800d10038601401c6941e900000341c81d411081c443d01049101d000d8410340c4800042c9862600380300507801040b001d8000e00030880151f0090401c00510601e64441c0d14010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 348617401 1250 348616151 348616171
    0x220507060815180411061c05150108040b07050904020f2109060106110312090a140309030a020402030604020f1c140124090f08030c240f0a0e190605 65
    0x55412200042407540490424010a0401c0001070140031020b900b030321180401415181d910856070392440ca14031f1604030a06071042c034202c08950104401e00d08402d00c42c0d410303140c03e47e103601c0d1903e40d6040800010800020041d003084102142e4075035001400051000c0e0807083d88034500c4080d0310b4010b032300a441c00141c00d00755008100e4190400200503046603401d00b410408500e1442080b03056109500c907684100300c0300f10070b02c8004170000030740700161806601a64a0a400c902e5196101d10450725490352641c0a0504d10002d413615038025600060300900c01890a0075000c40305c0c03240d40055600c81641001c0c924041780c480d403076001e14024020b140c20203004540c100000c51800e070340c8801003108280c1c07004070016004e134001d1048401805000c0d40090702c07150b5035802c05589902c0300c5d08640c001d000c1d101c0301e40c240354000c958001e0010202c0040b040349641e501c0070a2415100286810070345505e500c11068801d100344400000131160450341880d81d01d05e410600e0564501070b003c0c40c51 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 348618651 1250 348617401 348617431
    0x306010b0906070b1302030d0804021807050f0a12050a050f0c0406050d330f0b1614070b03100f050913020f03010e1608070b070804050402032205070608 67
    0x101c0c1d038a40c0111800d00d5401052110140c40d5074000c1c408900310900700940510900740080e210030341205169101310704c01c0350078580345491601e00ca9a040802e554240200e6010f0000c40d80741d802ca4009411140e03005d16040c03454001106202781562400d54200d00110f5641e070600c4a02c1c0031039441554094a81340840786440c0ca0b06400401602c9540e003200c1c0650380d11030f00f1660902c08400e108129180064160303403a03258080019a09101620849600004112000134001c406000740d03003620714100c034070740d40c48205512501c0001810000c2c400d050700400e1000f080122041010754080d4088040501000303080c840e489000e4403407604154898414001045603400b40d0080c2c031710110354143c0e252040030322100042070162409d942d00781e01c1809800f00022085814000700341c125046081210307182070b07560400c3c0c00301c0d1044c80805001040308000601150829400a40d0480100f46601c0f0014842112102c000030380c0346011181ca03000703850304000c056400b090781500721501c40b9178800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 348619901 1250 348618651 348618667
    0x51510170709050a0e0a03020d080a0614090606120a150501030204081015051c0b070e1c08040b0d0c08060306010b07060b0a05060310032d031110020d0b0306010b 71
    0x7a0316680351042854032502c600000d0ba005076a0342104020742c1400040707078069031441c42c0194488114410407800144000c0000300f0303000c103d002d080202d40c0741c00d00100c8a54415020303c040304800505040d080602000440c90f4220b04405040c8a01441c11002800c0540f40300c4248605115510450406006000a012402001c1090384003428902d00001b5a00340f00f80310340418081c690711255022081c400f1590321405030070b51900b2500d1042203100015500d01d202940c01a05d5010f440b9001181d000861860110035014003040c1c50040c81c00c1410982d07520030300545507100c01c0e4040d00e07180c2c071740b038400c8142500303d151281c00400c103d020341065814107000802c0e40c021420302a02e026124440000c66407208018070028143c09000c3d681d4a10b010f10307104601c00083d100840b00750008000180c0103100602c09005000245902d21000750855141101c0e4040000300c004034501400264200c4000c9900c000c05054007201801700e05000203900301800e181050748264009401082128 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 348621151 1250 348619901 348619903
    0x160c1a032401020703171209010905071203021615111f090212070e090d030902010806011d0d0c15020f031e041d04110f090403031805151017 62
    0x4141540d9008a2001040751a00101e18049099002814904441d01070740b007001c5800000f00300c600500704050002c0d4031441c000d42d0884512000280044e00304450034000510790703e019444140c002c0c4100e509800c0c9018518404c0c0c2079a50002c141c1700109160032100580002c043c0c8075007060903010b003a500603180c070031840d090501d17210402c0c42503644c03a1030030440d9294424541e03240b001c1008c44950076114104000203180603990368109204900f805c440c43c44c4240100880c00b81e040c0d40c1e800150b1200e9005603001e40744084d02c01c840c0f4900302401040c588500c02d400000e207001d40d00b07420302d02d4135005071020003030034490b1070038119001420521101c450000071116040725560100148040186c1d08020390301840d00400903440d032880019a50940f0014a00d000c1c50250920640d0304030f40c50308009540c40d58006480d000310a81d400503000c01d00a03880005a0301c0140001403030615a41e903464180189403100319801120039050010700000083c090000d443c00c0c0c440c0c000d0840000c100e003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 348622401 1250 348621151 348621181
    0x30b0d0f03120e010f020309010e070320040905010c0e040606140306090709052710050d0f0206040b120f070f02100f06030c030302011b1b0303020708160c1a03 70
    0x18080c041d00800e00b0640701040c1d0300c19003d80d54982c0c0204082c11110038518042e60060314815620f40c02d18400307883e40d55010030603c0413251f0200020f04484400c0c032003c0402400702078002da102d5695914800131071401c0c000c41c0c1c518061992095560007400382000100d50194003e85e04004096800d1010002204201c0c0c0d0010740c1103484850560325000121682401a0046900050031501004040750046443e803800032400d5280c14980c2c0d0303040d101003040301d8648aa01c0d0b00c042041000f20205603564911404540003030800c070f107044d0b101c60001000d6400303a071040d030241d1700c40d20030000c525a403a28002e03040060342c0340000c417208884034000d5880d4480300c102c21030309544482d0040102d1490f80100002c5502101a100003a92410040d0080c00b61401404910b641c0218a11000b4443d44421491040c41440181094000e403402c8000750006078003160090f400308031500c5112010700ca290851841b03480c460420504100745910000c00301f1180014140e07082c001e10604403003030703510 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 348623651 1250 348622401 348622403
    0x8151c021809101a030d02071802030f010501231c1a0919060f0605120604050c0a0c020a0e13050f01050f15030309040f0e0106120203030f0901140a020d030b0d0f 71
    0x1160003024252131600140d084105960f040c810030404104260300800c6050442d1070458241880c01104c20700b0304c1c00d0b440129410282a00da000050145600440c840801c00c041280c04c1070600303070045600d21080e0b200c00c0301d030b44041c0c4c80720080d425003007464001ca00c0840d1440c10b112214500d4500425a00700300504090810055500301a50b0183c0980c05507008040480661000300c7d5210130241990340508844012801d80d20001007882c00d05002e40d600421503c52050310300b00000600f01e49180204004030b038002e001e101e0010308100c0030650207006041041c180e0840e4651840c181d85000d88044100220b6410181002002c00010a1580d44592207250b80314a00c2d142c08006421032160301d501991091130700e0f00004111a40394841a20b1501140c001c225103504d42c0107140c5400a000402503059000b003000540c11a60300024002c0c850060520300e4902b01054004806900218003175001070b84180c1c0d51000455043c0500440084203841c0e120b1a012643c03940094544c00d000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 348624901 1250 348623651 348623683
    0x16030b0a0207050321060906040b030d03200c012703090b0a090302120c01080705270103021306020c0f0d11210312010e1006020d08151c021809 63
    0xa941c82c20b10005000303d66050700b40380100e18064003d941c4806040c0c60a481c041e020381404c600180341c0e400e01d403044002c060001001071030f01e0120244100c003c1c2c803081c1c50b4500d201e0001408400c03c441d1041c00b40c45c00041c01c40c0085440c103800d50215242d41f142040c0482060401407001003c40d0704040803400ba61a048902940c0d84c072003800aa600d40300c5540001c3d0401000c20b100c140e02a404110403562100c00d03070b50420640c0301c42500f21003d00803045a90160810300daa094041c0440601c0c2e03501c0401c040c1405070034004c00040c50000c1c001503510500240e008100054160b00c1e008901984910f02101c2d0000200442c1d29848030340070009850354000c45a142d82d84404009054160f018003068400700c80c0d599028241a585880081c81040d03560011071000c107a08000513041101590000c0d4000c08518521810403582e10201034845901d80c040d10310004115192882c0100742c00d2801806030603800041d01c144200403900701440c0c3c0c49000100309203c4810400300341120b02c264240 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 348626151 1250 348624901 348624907
    0x60c060209150307050304110906130207020f030f070303020c0901030c2108160309080d05121312030b030c0103060503060a091106070b01030302060a060e0c0a020a060f060816030b0a02 81
    0x40d02203844a56107002d4254801d401108200781540e00c0070065104910489401d02c08604141c14448050000e451496001c9020501c14054a00300d6001c1c00e400c1e40028100b402d94550078011030305005201c02c45600617004900c060017815010040010380240a0b5007480a0790704d5501c82819643c02c81c01020f44095454109030102c8500d101050817580e04001c1c1365517940440150b00c11140d102190071030204080c0c841c0090078034404116884203103442d840b086d01c1c1101c41c5c3c0d221040c04100811106180701410b071340101258040328201e1411889440008401401c081014903000c0712068541c10035050a0341440310b51130100b54950000d98189010900c007203e07160140740c140410075443d8100d20003090181c14000c040c0d103580c2c101e81c0a1b800703603481500c40da414801a580c3e0b500aa4055090300300210390600b4010005106411143c41951034000071550344001380c414a215034841070b41c45a100303000d10030041c04421014000784400c96440d9155607201c1c54400e43c001c2550349042d41c04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 348627401 1250 348626151 348626167
    0x3031817060403110c0306241c060e0a06140403081810050a110c03030106031d07120f020d0309051009061413050306040c0e06040b011d1f05070b0709060c0602 70
    0xc22501c41049802402d031000703448c00515410f001044050007a00014405411135010b00303085c1c21341d410140e04000142c95120311030301c4d6200034214161003c0e80c45c0c400c0909102c0810f8152003800c641020081103c07040381424107000b0a490800ba00d03560300380c1c84010015000d500d0000d1101d48c0c0c0c0c1e000ca41d01090705d41d110940d4000078001c60800805002c00050710428840740480114140c45268404101d80e080f5030202034082d80c2151840c1c109603000d040c080c005442c0007154202c04038810740c804010402c2660100d0b50f421003c541c102d01145014805104510345501200c2d9a50b00a160000100c0d241c008003d0aa2056540d8041017800015017100c00c0d14044203480c004c3c090140c100e805c503080615050039a0102c1d88282c4440c59880c10200d0554039007401603d041805c140e44050710800080300303e400c01c00342e05000640c01420341000c084a51007480c2c8895180c400ca031101526007406091a01d165a00144031104100035844240416604241c0500201d508402e0041e240c03041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 348628651 1250 348627401 348627403
    0x524030412031803030516140403170f0412060f0b060a03090203070f03080d0f29010c02030d050c06090d0215040c08030f0a0e0a030b060411070b010303181706040311 73
    0x20800103510f100071040041070516030107420541c0107051101548041d100b040800303d682c00f9403c455001003c80c20841000452640c509240020300540c000b00d00c1c0a082c805c802840d1b5026a0041302142025510441800304511800c1c09a0840f654144094240c0703074002141740c4251364141040c0750340ca00c02141551401c100c024050021407840300e0850b81c40e410007007035030303081400080c10441c01c02208501142c4079003d8071200002c0f9080181c400720f40c0d02e80101e445421403400f02d040000d0340700d10f840560342c20400024848460b80307915560707240350303417009080181c000e1a19009070f0080300c00c0040b050b40020702c0c040d018550b1103203444503100c82c54000c0c000241c1e50f016035028803010428040881c800d100074000241a51200f510046106082c8000c001c081e00c0090305a214043c001385442c00c2c150042e100e058816122a41f0342640d59440f045409002c0e00190300107481c4c1d0b4a0584130030407503110200984040d042c501580030301c84003229540c00300100001c040040c01d011044603120 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 348629901 1250 348628651 348628661
    0x31b0e0d060b031b0316031a062d040b0609030712080c0d0806010915090603051503010609021e0c03040b090105120f27030904020903160f052403041203 67
    0x1c0003c2c140c030803000e450003005103105114881c07641300340981ba451809410804400034100d07940001100288180044052084176000340141c0e00200c0340b03001290700030800314102402e454038001d00e40e40070040000b4001180c0924110f01d00512041060032095540055214101c4668803002c104502a62801c60901c0c0280c0914008078494440a4410207070805042c0b03201d81001e80c0c4408050703503501e030302410500d03440c000c00020036007140c41441550710a40116903ca111040402c5204400c41e02184c00c581030740c0e1004c00101d0780450074148030580100c041d422109100056410b02100ca15166100c0c4568401c40d0000c42e80000c081031b07140d01400950b5120100e542d0000103130f1a0802da05404908110341c144d0641104868201c0d030110011503040709000043c8c015810172a0380c00030300c00294050f180340daa15102c0e044490300c030100c4a00c1d101c000b4103044505410f17414030b40301c04c1c002035080e0b0100b5810440408000001400c07021400e07a640b01c1c3e04005000107002c412181030b03004103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 348631151 1250 348629901 348629921
    0x60b16050114090303240906150f0708041701111617040902030405010b03010204060c0b06210a050d0518090406060305030301120b0603160303050711130606031b0e0d06 74
    0x50402c0040003030600c0040003452066051034602401c151045050700790840c0b00321042507018500c400403401c00e0800300314802c0100003c80180b031501846140c0360b12150005101104d2091001400344500b1201e09521036080540c01d000f80700c02c8202c441c1405050140030080b40940340009003120a00c98030b406c00c030711080380461419640f181c440d04490041c0d442241c2c1942c0541c241590705006050510880d4100c030341603560000f8455465480c9105031101404a56000e80b986805884188800b00303841d04d0045818018110200146022400e001101c217980c005c0c00014080541c0c150036162150700400320842d2004003e5540f8038110001b400a80c001400900c000f100110b40704070014082241d032406120540b40d00e95450701010740d46c41246003082d034095118001000024060000340c04071910031103001e521541180c001c103415441c0040b00310501a00d440003000705507014070444d40d0602c510a0a440140a5170f034016065800c89140180100c00180303103403041c0f04680d84016514 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 348632401 1250 348631151 348631181
    0xf0c060403150f11030402030105060a0e0601210e0604021f05030604090201020f0a030923030d03021605060705040512010e0c1e1c0c0f03210309080a02010c0210060b160501 76
    0x40c80700c204913180035030011102217000c1d606c3c01021800301d1070f03e012103004840c1604071801c4155070348001100c844c5007000c0c00e081586103000014401d1049400b40b8400307008044020549845d050040100440ca204c0105c9255207a03c0400f61001e03030300c41c00722640728200359130200303048040f1f100407441e01d10349484c0f10303145004001e1000101036010381a003040700e03280804204100c01413402000c0240c0c441d900141e042e030001d041c403400c0b01c3c000e401400743c1102c0100368410284036600c0e81400c3c0340e4111803500001d81c00140c00e10040c6024480070018403410302c020480b4800c2601520354441c415491107100d8044000c50b1801000040c000e11a0308502410904c40400041c888010003101004100d03208a4ae105010403803901d0428241d007282e400c03000812502507245119401400074034069010142c0f00d00c520700100701020010030b142c0005500000300e0480c4101c2c02401c10001c09114400d45090040c100401c1c034101054540103456082d81c04400a01480d1080c01000100152054 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 348633651 1250 348632401 348632411
    0x1e0b03040b09010c020f030405090408040b0a030c0206150f010e041112220203070608130f030807180b0d1a0409050307060506090415090309080118050f0c060403150f 73
    0x4100341c58a01d01d0281100c00001e004140650303000340d07240c000380031500c44254800d01003042985001c80079542c00c030f030044600a00d400c4d191166191940e00c00c0764040c01094403000d86440c2603904000c0d5a5100c14144020303c90840703101d00140401548103070302c40c100120908004010b130385070b6000d4000410300741138090f502d24160640886210003112400d0708034aa012800e01c04079008211449020b41c000c01608500f0f00707003601038030703203000150400d01051a4110041c00160400c0240258103000c6c2d1101041880c2c84a0006c0c80201084016070846401503004c0248004000c00d03580346401210001c251103070482c64801c5151140c03540144d02c6401c0c994044103000d0080700800340640598010f1007290b031801c0c103200900c001920000c1064a00f400a281240c3e0305034801000759229207440b1089694071109a13094400304c0721900700289000c034040b4100702041211000f91044a0f015015600031180012854025484003500000c44402000c2c00c1c039400390b2003040c042c1c92800341001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 348634901 1250 348633651 348633653
    0x408031f060e011404060203040e040507091e0e1c110c090f16020c0d02011101020c070e10210620030405010606110102091e0d0f060906110a08011e0b0304 68
    0x30030519a10b4240703020620010a4000341e8114030229020388129030001d51809207030003004440000001d00684280c0150300c000b1404c040705005ea40e081d0400c094126070340d1980e01d10004100d841400144445e50b224076813803c5640700c2d0004040e4004428100800c2d4880314011035810031900300e1038198230424107010482444420f141142c003440da20402040d00301c114540c2640c0d10241454200c1d8081c0c58581e901c00150310036200000c00c07141c008005401c0480c01e1001a24280881e000107510580100c200100003101da001c0000814414209104480340c250600c0c0c03802c846800003810b43d5803a07507406406020b0242d8060b01c00000050b145a0740d18050400e14002c004034040c0400241e01c5900c52030300300d0414000e846c03940000402c4007909505003000c200c1070400c222903898001002000f02d81c04150301b540034600380ea0003000c010500040c640b0b015011100e46183c5504154001e005c0180065441000507064a00405800201c060f0300c580400c2c01d0040c950104243c13450010803c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 348636151 1250 348634901 348634907
    0x10b0f0303072d0605012310090b09130507021b0402040509040b100e13030905040b0f01030c030b040609020702040f060f0b030c04050d05030d0e060105060f130317031501090e0408031f06 82
    0xa0360b803011126008140c1f0f0a010070000300403504d0304c0010006a028100740030850210000f40841c8000074031640c00d500e00da00303610302525000c072101005a0415101500b482014000a60340410308803001c5181c141404000380702d018010f4005800d5581040002d004800582501c1c0003800c0e101c40a4599441c01c40205400f81e040d440b0210001000c240380081d060038075018001c0000030080000c0400f10305140110010800e414040003019121004d008203515075201c0e40f8041c05480d2400740c0c0c0d45c80c150040c0403d540c01c0034415000c1d5850144108001a4490391020135280021440b83e9641c079002c4404200d401130360052980260040300ba2410848000000c20b81568002c0050001601c10702c035064640c02c09101d61500100b0422410148030949070041407808102a0900b0100391651100002412407240c1d013965100000140051442c03411078001001c002441c00303428075410801568144400540010b02c0150040b01080c95000400003601114040d0b0300ac4486155440d8002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 348637401 1250 348636151 348636179
    0x7060909020a080109150e011e240507260c06060906061602040617061b07030c0b1302040504050d1103070b010e0612030705010b0f0303072d060501 65
    0x10004101064000114911039000362030351040320b42c45070105a031034129690064818062400a561841c01c000300709181d000b4080e5007c0d00400440721003901001c200480c910050f604102c1501400c0b80d150b402c6482c07002c400c0e45005081d03107080e070f4450260b460107102c1c1844904d895089020b0070b14942c0c1c0070300d008201521900074020101c0d4401c4d140c400a01c00310410941340c0c950042070802040c403420802208101d0303880c0c40684001009030ba10345210011480c89031304507031960480e0050010044c45c4030300360003203261141600762521200783c0c1c0152280e12111001415240c044001030310540100d6800c642298003d40148054078203032910075164004206680b02144030309650606132180042640d503007a40c0024a81c4860b424038600740e254601c000c203110340c00400d41404420004c0300740082c4c00858864800030411954003001c0016000c081301515020394024030400011aa01c0704207041280c601590b45a000c08041d010000e0361801600301920040c100800050041c0041580f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 348638651 1250 348637401 348637409
    0x6061608040801020711010f0207050616020603040b0601020f0607080a09030311190311090609040509010b0315012405031524041802040b0d0509151302010806010201020f04091e020c07 81
    0x11050841101b006545222600e802200107a0000740d00740a2070800c03400810790086e0901c142162190580d00040740d541c41180d00715030009400c002e00401d540c0400070100a0309004016120314031342840000c3c034814005000319062600d0341c43c49010b250290b401b810142c4040a900d9a4428016500206aa48000d61000040d1500605045264003882902d100c40002008940307404040401c01000e03000107025401595039544015040b03a80402c20100d40c06480015054207615240501c001c0e8890043c01202500c2c8015210400c150300400322540301490394040c040701801040447d40c1c0e0031640c440c1da09e4503000c0221103400c00031404007030400c50307a500400104c90360058064005a0140d48240a400b160038090040d6198064100d1640024800c0840d0ba4042c0c61344d40f0250390b94802e580e051040174041c240b00d825940c3c071074011a400740080c0000d61401e00720740140d880c188180e21031078074070b00d680b03402c102c04051198217001c4510160b0303403081d511186000c00a42e25030360036200e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 348639901 1250 348638651 348638663
    0x312060e100915030f02060c0d0c05010c050906071e0b070914060414010f1809090524060f0a0302060309030415090302090406090204020d05090f0114040b060616080408010207 77
    0xb548084030300800c010100b280040c44091891a550f24804d9140c0ea50200c0c0e00010a025210318040300700a1003a4819190341c0340c140c084420308101b801c50707001c80102000c01c08108492072150719401c0490350a554032012104a1105c0c0354045548041030060062503140e8120612100650103070700700041d603901d141085400603d840800001d40300c0c41c4201512030384c0c40070381038005600881c241d514844036400d010b10381e65854005440041030541210b02e40941e180380240501074200011b2003061000d181d252070441744861158603401005160920403180c4100c5254241c07240e034940002580d000c0e124940302d0401c00061600d94000d401030001a4001000e000708240c443d4000400710b0303402074080569501c46443e54006071a25803814ac2e080398080051a24409003885140e204030a0640900b00380c0800101050940e800030710403402c0b140445062001044600107e540c00003000c5540b10341c0d4455018003101c0c1c401a460003d00f503042c0125001030001c070190010501c42e03110300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 348641151 1250 348639901 348639931
    0xf0209010e0108040f0311070803070c0603110306010c1506050603040b1b070f06021312110310090c120212100b03060105060a170421050904060503060103020105030708040312060e 79
    0x5801100c03110000c513406441034036900e0160b00400d0140c0310030301541400c40140d9a401d5211091180b0390b0b03004006c102c2c4d420310031000030040c035607240c451101c14984441e20145181800b41c0003c000c02c11400c4080c01d41014058094281001640703c0402450090f007a6a00e0f0b01c0c1c00d060480d1214012180e03555240e41c03030b104000720760000b0012680380541c0001c08414402c007a4640500a4000300d070002c0442e81b0005000ca1480780380080b44c2c50701071080340c10b014050308020625041000c0410074000540c107000020002800150000050340c5503801c10400d401d1280c0001a0100c000f984030f040315005904076180c0d0301000c0d0f0070800614400342d040341c601c0e90741e51050141c544504c000101c000340260040b00b6540c3c0b04003035820340150090318014844a41007000701c034141168200c078000f044002500c22031501307150056100500c0c04601030100343d803543c0c00103440b41c07100810301c0c410030000c23000007420907000740c41c0b2080086012500f003002503220008581490420b40e20100001030b19 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 348642401 1250 348641151 348641177
    0x2706041103040503030411010e1f020705010503100302060f0f030907060306152c030607180f08061303030e01110301030209090c15130b13060909150303080c0903010f020901 76
    0x903800312401981c2c41401540b4540d04c46d15024191300140305502c0c1080400d05102c8990380e079000030302100d83c84200c0d9003401c80081c680040e1912245905c95810301809104000c500400f201c100011260181d60080e5500451280004070f0300c14101c10710380380500031080c0001403200096400c15a0040e0301c0c1080110b840d00c05034550740610903500800180440740c02d58151b41950b030503008003207002004c02c00c00b14035000000e0030200c044030360100080710400b14036103901c20450701900400e0003545000220381454a95138035018002c0c51078030b42d035905c40300c04000c052103940a03940d400303441c00080004240c1d401110005a100384401e0344070300091000305001c071401160000760990020403044c4031092221002080d0b03000800c0b084520340ba03100d03001580e149098014240000344170202d429007400c1c00341c054202c000d10340100c90424540560419000f1901e00340905076605801c04200580d541d101c1c801c0715201c3d0800301038040d420001891004c882c141c0291101c0a0241c07250741c1d0005078 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 348643651 1250 348642401 348642431
    0x1d0a1a0c04030b01090e010e0a03180f0b0717160507030b070305060915031e070302122e020f1204030e041503020f120604030e040c0923270604 63
    0x2642c0405401068030f5401045810403a5211808680c0c0c4040045405c0b030110100c24103043c5514070030b40220b0340081c0e80840190703105500002401d0321070001842c01d401c1601e43c080303d000b0342c3c0c001007044a00c1c0b4010944c0e102030100b0781f401c108802c01c1509044a4134036048e82c40d00420b110131600704040c0400308122601a00a00b44035800190903041d01e5a1400c00c000345028049940c107030140601d69400ca408941744070841d401e800813500902c41b040c82d51040c005d20742d00c0d03103a043e8400d8000100e900312502c04a9214418180f10741503c0b10b100d542d400d9032000038882d0201c04c9900040000e24100031b600d150f10360303a2080740a80c0361800c900d80e0350418070058407541d940141800c001d65205100514255100c0303525040054403445014801c1d0150524040302078406502040c01e00c86d40c01c0302481c00d405200000c2d03207680381001c403107460f20000448003401004102c042e42c48010145a003919040b8442c9091402901c20001c621030b1580e11106a070008d450690003281019204000008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 348644901 1250 348643651 348643657
    0x182f0c0c0901051f050d021b0d030e06132f1905013510140414010b0c160603020a0212092d10110d0809101d0a1a0c 51
    0x101800b20304850303030800f00140004c44510007142c14850240b141c800c4104644c4080c052084070841c0041800003118400d070701c0c00010103200d80426042c20940d4000c1c000214080da085101b405550b1030100c81490300c6a80303d500c0c4618000c400481c40c20080b90000174403101c121b5040180c032302c1c100c280c280c01040c9030700480900419001c40c0822014100c0c3c03040100020b0711079000700704680ca040d2401c0500240c050b0040c0c1e0802c5462440040c00e020114071090080c210702c104883c2008214036203254401c800905108040c0080008181c22102c5801403107404044412a00b0380d10703101d601c3d1507001c0c0003500700e004040014802d9210321041e8a42510440d0000c50000f085503004107003620203070b42442c3c4507801800000100b082862031640ba10034030002c4034810740d1100c4100c400105052464003900050400c00c008a500503c04108804900c1001c9501307601008030b41c080060074511030780800150541901e20646840c081808152524a030030004162a484082c1d1a0000d0030780281c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 348646151 1250 348644901 348644909
    0x912140f0a0203072109141507031224050405010b0301090b06071a010303110a150f06030512030703063c120c030b070207182f0c0c0901 60
    0x12004028412811061001500e0034035580d1040b03c2c07905455540e0f1050b64481d68400d08081d034031032144a4105034211192a01629240e090070010011120000710380c1e03c3c4180507030700c20071400500c0300700703140c492454160440181c81c020305c42c00d6003040481a85241e8411030205a000120b0301040c185400d000e000d0480710a9007045085900b03041c0400020b10090b40047da028004020381000910b4030300d40c1c3d142112041c1850707010756156080280141c42c3c10700480c0240d0300101c00290001d0743c214210b00f56112092000158a6092621900105161741001d405446001700c19010070081d140210311034200c580d0180700046d552034400c0e105801c0c15004e1078581c081c00650500c3d002c0040341c0c9500001c43d100300c0a1201d0f569101d4003040501c002000c3e144007107040320a01c2449041d00c211034010f4201d10042c4001c5182042468510842d0450748080720703180d0000c500a000d2542841d807075001500708a001208000c07022088680c800d0000b683d0a0081d080c0028403890311101c040d04803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 348647401 1250 348646151 348646187
    0x20c0c0a061107090c0507020312030106030b1c060f1d0c12010501061407020307090e0d0201110c0a03080903070c0e0910060302010e01030f110c2503081b0f010504060912 75
    0x214213008005025000c5080c15008005042c03040c90050b03a03003000720f600d1030149024460340d69418440010240e4010f030402c00d0140c0e1190604a142104085507251030613045140041d901c200b0781301800142030707441d05240240548a650000152001c21801940c4004450a4000d400324905017426500c0920480010800000d50a4818031108005003a910702c006c065030715103a110080302e011551948a411210380c84400c40c9100644c09208a00314180f15140703e42c00d20300c2c86249103507180c00c165002010006020041001d040042040e0303400385900c841243c07070b130903164104900c41d031004450300b0406110f24902c600300545c85101c2c104c10703680c06070b40d80540e614002006401078900009000c0307201d90b45440c410244684d0388003800d418414040640b0700031041000f505141401c20809140f0500080d4040000607196411581010070070307500b403161701894050640c1080441c940000c50395017000100810024180e0103030201e2803040700078200c0c42001a10450b50030307207c0d42c000044 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 348648651 1250 348647401 348647413
    0xa17040f02012003030a06031a04050715020a060f2012160516030e15040b0301090903111023060d021908190605160c060f020d020c0c0a0611 62
    0x5544507012140b101206035200350f03e0340e18500d0010b0700d590300440d1806902030781c400040c000c025800c000701580002c500d448007918240b646942f91219050310a1380f80310040f450381c0307415a5000b840007a000a4101c8810400c000401105202901020041080403004002d607041a4103402081e00e052840100841107031740e44d50701004003021695903600043c01420301c01c0d02001d8a2000c0750700d40042c441ea8503c1609c00146050081e9400198204c6c00c00100c00d00c800d2060040700400da0b4111880b00130302207619003850a0590314000f884c09103000902640f0061103000140d608a0700760035041000301c0d0030984525110140c4050180c54196200050041903409850002840000b0f003400180c200f00543d0769540d464904081100506103030806000341c0300600015100741c030313408020f140e07034440a0303c51108020a10301d141c2c00014900340d52181d02d01c0c1c0c3c0c25900d506542039010b003c401150368809600d2101d54031500e5503035640c4100d100000105035503106003141c04000401500a01b4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 348649901 1250 348648651 348648653
    0x6010905120606131107150b04060303020c1014130f0e070c1103190b1806010302031020180301060f0b0f03041103031908060924030c03010e01020a17040f 68
    0x6400240020542441512070f40d1900c005c42c0948000d100092280e00310b543d81d5600c801214069030344104c90507200d149002d82c20004260007090744000c0c41070031220004101c4c0100d0040e603c40c100c501c0e484807620340120700c0b50801c012107480702003a680c52110300760b18113640d8188110842d00c1150f45100103a880c81e40440045ca100489451640c0000d069446003298188200543d07000c1070015165501c035542440f20400703041c000403440198100140104e50306680110396a002e9800c014107200740da489040c003d401b46c241c060f0780d80038581009070b9500c1d0340a20581c02001c0071020741074445c0d4a4580d0014001981d04842d204580c110305060741012900b2045050355040180107a526024158000c041550140300070161200d41103a150140a41c541c0300420030040240710034040e05072507081c8a41c0301d190b50003e2241c41c04180c03101101041034004030381011000c049154041d800d0225055000c101034014200c0184e080d40c40f42002a20103150a42808080c0c0380034080c402c102640310 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 348651151 1250 348649901 348649909
    0xc09110409200d02180f0108070f050702040510030b0f1b0702040906020a080115030513060209011b0b2e0e060604170601030303110c060105190b040305010506010905120606 76
    0x801501c41c804214400030002e140340c20301e26403290400040d800c2e0f001a2104005002e01203c4110720302c16180b44041401c034400190104001800300d2091020b800e41c0040d05074031070001c4502c00e1f54060024407080c1040312014056452038001110410911000036460181c00741c201403096100007170001c1050005401c01355260300080060f85c129481c0c802c501d01041a50000340081e503201c0d03850905a601d80901144c0024492034460100340c144070034000500d251454940131142c03c6000140c1d100c02000050340c001c11442c2c02e507000c034a405002e8109010140300c4080c403950980303002a00126010f20040c40d040140009441c09042c4400103020403d82341311015400400034019624040c0c48010510b02200c008c1b0041c0304540c0088018003c0580c14083d1803821116298158140340c400da00141e120241400703120700408441100d03d02050410320b4600060201d01d00c0c0654443e205d040c0207000e40f40440c0d5160100d8480384e000551070412021000540e00414060580e90300e41c2c100304 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 348652401 1250 348651151 348651161
    0x302070317060a0803041202040b010c050304060e0a030b16020105150109090c0306080a060c020c0901050915030304050d0f061a03100b010309020604080c011d0609091b13030c09110409 81
    0xd40c10040c3e030040404d243c2010001070010304001603086a0030302c200e00c101f2003990480e40003241000049150f201c00103400105580964940d400c00001607248440440d00c1222a030744050f1001c0c86410a201c1c0f00655550303a082818100e07402800315a8400c01c00362003085d070440c202130004000340d000b0440c0b02c001d40c0c40a4080003d03460041100755540100c24900040740300103a403181d648142400c411501080301500003071040da44080b1070b40c074010008484050040808441d0300c589010391895540a00c100c0b40a80801848602e0803c0300f42810861003080310710840b415440c00600121380141a9a81542c4120040080503000c032003083c0b2001400c40d4032909418180ca5034010300042e680c03000a8005400d41c3c3c0001c0401034003030303000104000b55007250b4518040004180c0e215507240c1c0c1007280d0320418251151090750703c4006c07440e00d0f40c41007403855a20880340407030068425401c010072141140d0040800740482c43e10742c00d480c421192407000384004e0b207074100130810484041d074001d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 348653651 1250 348652401 348652411
    0x40f021e030a060f15240207050d06020d060306020f1321030f030902210d08040215090307050916020708030f030a1a040606031b02030903060f0408070c060509040c0302070317 77
    0x1c0440d403200600d00f034a6071740026130404404842e00240c1c8030891080c600c0341c82c40240e010320040118501d40400b00c0d501707202081d000b501e041d4000071108030000303407500150000e6610a0b0215650352006000d4030280d00003408004004020000020304050a05141c29030b1000300c001e1090400581d0740c090314101c000c90507010a15445540030300242c1d49488203021100082c00e4482d12400f80c55507550305041500003020248110442800056154611040c144415440006590b0000500002d26140255200039841014003003005541c5006802c0c601c94540d242e0211030606440350501d58484c015006a04500501072000a00d42c0d0159000000380000741c031240e404590700d40b008202590a15001035020a40780e400490304004c44409240140369244003940c02c1c5500b05c00080c1d00d45d0030150101d00039041c0d42d00498140074030081125000c40e400116510130381d54a00004d40150001c00e034191003145015025610b140c0a4000c0b01e00203a4581d0300e001c030f400d41041400b00c0041e0068a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 348654901 1250 348653651 348653681
    0xe01030e030f1615020a0306121a1924060f1d0409020301020d05010e090a021f030b060a03091a09030901361401020d080f1b03040f021e030a06 63
    0x100b40c0340401e5950240c40300744c1c99818000341c0d40d4008500f0180030307500a6400781c18012400e440d0070000c2682401d81c16543d80c02030110480d01c0e01d80148400441004042c85111300d49403291100d03030165a161039084818250010800543d036814041c5e814030903000003400400d070a01032414800740c10826522a0410003807002440d54070b5600070030308a0304001c0310941c0b1259180300501c20f207601c0141c5194000c031024010140103510f40c0c04079403401034001034412038071017500c3c955020724020f070050044004003800301510b40f4048100100903107403102082c1c81c9000100050001a84182141c0d03114a050600071440c0c041740500455901a50b5440c03400c0983c44031610b0682c88a9140c107501e00400031035000d604c3e43d4249100c1a088011700310040741550700c249800d08a440d044909942c3c0030300e04500c2100140d031480c448514512940d909407a4030f05000040000b080340b9070321044e0046000b0341f4020702156002e402c11190301c42a80c0019490760000d6104400541d40780c00c407041c0195011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 348656151 1250 348654901 348654937
    0xe1c0309120c060506040506060d05040f0f0503120603060c0405014a030604020a0509042a0603050a0b03190611030403030c0f020105060a0e090f0d020705010e01030e030f 75
    0x62151607000c054011094001041c2640b40c0302840540d0286540103102198100490b04002000410512a1030604074001d51114001028040c21031410080c25810021510145d01507280040e2a40d11201c9450710766408007004c100c0c0c0781400034000c2d1168950055451919042c0801540d40a03a0425a45c40c40d482d24043c00500d0b0001e800b002440f80309110007401001081d00020200c00d40c4210414007030340c0480700f04009640c40301c5813841100c030103072035240940d201c0c0c8c01d017038004800e1101541c14540004e462030003030182400203081110240d42c0c1c1001a616800703d42c80030b558013084d140364035602000c8244081c46d0305007049480588501000240c1d80c1600b0000c55242d0030440e01500402d03580c44040071030981265222080c0d005030b10003003007070b0b113000700000e0761100c62400744800c0020100002030020b203040001c0e01c1001038035000c85541599440001350748254a00801d400180c8004c160003095020780540c1048030512009542404200302d2007480c2900800da41c080e02014003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 348657401 1250 348656151 348656153
    0xe010b0a03030306050a080109020a0b031008061f0815070f0903060905100501051210020f090d06060503100c0905060d0b10050d0510030b040b06060d180c090e1c0309 73
    0x50240c24021846614003007112464281003100464407980001c0d01da03410f04401a0069440ac0a000c0985021090342510703603d58003c85280900e41f40c10035111b51080c0818031590b400c560400c0c98554a090302c801040546030111292155103040410400c0209080413482c800c0c0140591152113100c0c0c5000b0008d241d598403100d05072000034400352502d0300140c075176902c0040c07640035280c054981903030001c0e00d880038030344c200f940c03602444060107802d070340410303e0090103407900200c42e00703044010010044c0c1151814410010070903413045600c0703480351400780c1c50408118010400312000359190084001d00c1d04051200c5a84031400e02e0f2a115030301c01d808425991410b100740d0762002d0583ea0f06407108111807100d002c456001c0e110f1144141001c20401c0011895007079035a00036400314105101c0c1c2c0b100c90104105016031b068000c42103041220740141d5580c02681d400545016800f540e13a525070761030701541100d1034880400001d80104034101200210315040c00028459031400190721445 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 348658651 1250 348657401 348657409
    0x5010b1305040506010504020c070614070812150f18091203010b03070f09050d020d02150a0e0f09070f0c05120d09050d0915030e03040f060206090609060106020309040e010b 76
    0x4100c180034040c50752041840140b01c03080001d5405440180d804514103602e0300001607841310a481100104011010411446c0d1103200540d0031f5158001c107042d131546042070301110822001c0f600d501039079145562841302d42c50030f140c00041c0480301400800316449000791010071004001e103103469503c16024804a6000c10f84001d6009020100340300c1d03264107001c1001012600c1ca00450f40c10401d030100700344101c1c2d031010924007803964108e5000403800042c1c4042040c10044005d03204407140e001c66046000b6070002d0318030050301c0044034500308124005003005540d0806440d168001020458010152401000f90b42d944500410031150308040001440100e90b200381c0b080d18626444400d20410050104000d440c4040306003000e02c02141402002c0124070740301c5121004158483c1e207150701c0000140704550207850a16007016282c0e80360342d400f070341d648010b841122080c4542d40000c2e8002c0c17070100706036059680750350185203410381c1001040003a18402e00c101803070b0755940f00c1490480d0707a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 348659901 1250 348658651 348658669
    0x405090703020301050a0f030221160f050a1a0a03050402060c0a060c0f030218130e160e0105060f0a08042102060a05071b080c030405090a090203070f081905010b 71
    0x22640e005039030f030341c1040144400c1e00100c2e070200c2480c030104241800181c0c0c400300c01c040720000c5184544001075100d1081c5180034840401651640e03050300d00411081d0b5102c0c45c41050f96401c0d500040b15940d150344d41286880e200782a55141d5400f8001c1c10380760f0344240c20040e00240005d140c20f040c09645148281460495001141c0203a55010019096034100c0c1c0100b01c0c0401c0350404606003000c1c0845000790743c402c0c1398601d10400d180400c54442c0c1d0f401c2c1c1d101c4600241d1180844a807400782d4201c4e0070995260b8043c2490305c5048800001e00751415004440007202e002500303505104041c00c0a4980c180094411200c1c2120001d13000201c0c4101800c01c41c4420042d402042e042c1000b2078914110b0340050401d008102441000d81002030203281d4400d00583d20015003585d45c3c0a9450302c0d41107010307035000359a21140c010280300302d42a06030820351010340203c0550b24903036620301220340400340c9441030100c00e4001c842201841480c004004c0c01c0b49018800215a1051060005040071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 348661151 1250 348659901 348659911
    0x70c150603021e030607111c08010905130210050a03060b071a2413020f0301171501030f0303021821060a060501020316140604150f061802070602040509 67
    0x9a40e110308005529000110404404400408500c00200c0c5000309407116070043c0382c03405008040c0c4406203154410000800d0b6030f28000c0200301d440201082c0101440020303c950240207080102045100d080a11801d140700c0d130040c21180c0c140c2c4401c4007a00c040d0010340e0f08100341a511100050901790f007000400c0ca0301e1003981410501407558148480f6000041d00c0204001d080034204100c0c003400030040300404504452082c00d0312000c00c4560080c1c03140f14946038440c0f501200004541d908220701c034496150380403d0300c0380e045103050841c07000c010921020b80419291948440840d0080c2d000380710188048031600708004013040401e501c40b034100404401c02c3c2d02c50400149800f020701c050354000c82c14201c01d1000c5803500c80002e5584c015859060114030ba456400780c10803501460141803103034550280c90b850b260a05001001c0d040d82044010494100710750030107038500d18400c0764280c0c1c8a903032103c910006030300c405400035044100202d503025401c100104550340c031083d0b003d03c14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 348662401 1250 348661151 348661193
    0x203010213081006080318060c030703020a05060f19020f0702030714010e060301121217040b04031d10050c030d0203040b0604062715120c17031e03070c 67
    0x1c0c0d45080d080e60301d0050030704880b003595072900b00306200f8214044202e0711050704402c401030001d00a240001d40780d114807100080c00e440f001482d1010550007042011070240a21300b41c4102c0c0d0341d0141d9010310b00004503140014014035002c1002a4200d40d40500707a1175545031901ea0522145074042450501c003500000345900c20112341321310548e8010500c0c502e40c04192103003030840d450030b42e8800c4501c00101004000458200300030240070304c00d0109280c1c0002c020300e8113045080c20709105603400c4086c0c60a8001400300750b500302140c244140c5000324808050800b62008400d03580c1152160841801000355000400520070900d00fa800618041c5008640e956040c1c02e0100400084a00d03683c41401b107001d20a600d444503507451000081d04d1101d200c0046108062070141c2c108801c10ba4118200011680c0d5a0317030280800000e220050baa000c0448501f603e80170807091b03540b4011002c0b145810610070311743c00c503c00340c01006107800040b1070502540c04c5080d0307a11981c180d003850b4100441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 348663651 1250 348662401 348662437
    0xf15020a0e03100b030a06110906030a1a0103021813150806090c010212030a0510030204020d0c120b22110406180905010e0f1504150f0506310302030102 67
    0x62032405104025022034428802c010004c540c0f00403c0d01d83c180450041c0c035265948065030684250641241e2081c4001801e09540b03145c100440380c01081c09200b10260b4050303003c000d0b10305501078400c90385102212030450301c0100c464801c10400089140480b080161034011800f00b0f1500303041d0002c0a410b040740900800c0c680055414038101c0b042100c141198417070301d0702990030384005080361341001c1901e0300070500e99116100040e41042c00c0d407009400610026881c4525a602c4d40840c00120303c40e510116002c0d44a003529003590b000000c00c0340e1192aa50782034204001c1028100300400f221040420300032403002e038070220b5410551044c00811800421a03240102c05130400000e00f1440808200c0e55045c581300b4003500700001c1c02c021101d5601c4003c11503051107408880c104d541c0040c4103200155104501d40c4081b41244903415902c1c12105010ac0c02d0710780031081e5050f00d0501d01000c01084c0f81c0e95100e02d0400c1e070803515a01d807020900004400b6031001c3c002048280e04c050342e0468 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 348664901 1250 348663651 348663677
    0x90a02100c020906030318010f0224060f0f060a1d040908090102160e0601111623010e15070c0f0803130e10060e01020102040e090601061b0503070f15020a 68
    0x26003d0700c014911032098000f0005406030310400704400c40303091002e1070285002038421106a2508100c603a5100c1d40780415500d940d410b2420145c294894401522401d80c1c40058100703008001071100115684800f045c852104001d1058409080d0380350342040c00c08a034119030000c102190f841c540261218940000c1004940d41c04001c44501d141c19841081d0b0b00f103107000071410212902902d22410449c01203501420420200312484142016407416108039644d40e050440d441c1c0900410a03982d82540544060340d0b01403040c510344410702910482e0703041c006e102c1d6080990f02450301100e880c001813074045500c0180011410281400b040159507c40c2c5082422444902561116000210350001c20001380c515030301c500112003050030540c0d40883c50000507406400355421403d010100141004028040062020304903403180c2c8904580b400e4905043d00d0500c0ca920b400b4006034000c1006200007004080c000340500d00031900041200345e0780e102c04040e60b010314000400502d410020b80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 348666151 1250 348664901 348664909
    0x405030a0f0503100612090506090a03030f0204050a0e09010e06150301050f150111010f09081902031e03090316030305070806060a0914040b18040b0f06090a05090a02100c02 76
    0xa400c50342d080035821858422948114075440340992020414281515100b0340c4194202100d6254421f050314031030320b0407510495443d003840206400203070400b540f85d61140d919108031760903580040e0404044070b080112044001c48058400c40c81036580e220515181ea07018041a40070300c24504009000c00d160604241c01e40380c029041c000b1aa150700c081c824000e2140106880d06202070038003100c4101890301d07460040c800c20041c1aa550f0a10800320101b010030002000c0d55442c42c103410a000d00c2c42c81c0200c0e504d00138500000300f480d501c03054410f54400356002442c1e00000744021240362925402050340300681d100011004a0388510a0003400b0350081c0c482648070034240c0d5403d0900f00a003034003c20b03046076032041403020365240000c43c2080d100d64100701010100503221210044940000e80c00c14402110309540b40310022010079803002043d4603080c0212801050140f05031240c000c0c07000240310141c031040c500d01c12013042c0c0340180c8030780180880444507078551030803884440c0140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 348667401 1250 348666151 348666167
    0x50f07030516050702100c050706050702010215100308160203120d0c020a080a0c0309030219080f030304050a02010509011701090510090203190c050f0d0606030e0c030d260405030a 79
    0x5602101080b81e0340056a8420207640101350111201004001203900a6032000c001c800081c14034050741c080410140d4120001707269140c1300381d00320b45207002268141c400d2614155a205c4281504180400101e148103028080c050b0b0046058103c00015600107032501042a804000c600c03408903044041d00d50790b2181040404481c0080e208051039039840511901c51030f00c0076014000d4015041c82032511403038403030f005036a01424803c0301c21078400200010a4a91040c07480c1031051520305981103a0100569006a40c040b000f0480d1140f19030054806801c42e0039aa030401c600501402c40004c4e290754481d009001c101c2c40056075040049540480e041107403c00c110890040040c070002401c00500c0d1491296594000031700401c0c060b104440e01c1c454044e03a408202c2e40030070301d0030b2101519803081080780c80d1a281000744110300420b542d125000440240c0c2d040c0c02c410300d0202c01a000b0f020300300c0d60389032a40803d400d40c4a00070411300300c0e14003510151090743c80410384411030b981110708 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 348668651 1250 348667401 348667411
    0xf0a060f0209010e01050f0702030123090f0303062106160e030d1725121a01081501030204080106030506040b0f040b010b070f02040608160905070f030902030f01050f070305 76
    0xc250b107400820000a464009140c01141c10000c000070062100d074800003d50303200c1d541c02002840700380740140c05100010360204507020f0415114021403250315000a41f414942c0078a0b014501b15501c0404110303924800144142c5030362203684a8803065201481064481c0c0d180702502603c110a03914010f20f0b080310f510849001e648403032600d05240741c004030010480d60071040a4400d03961078a030102e40071914400b013010000100ca10041115401c4800842d00070503440041000c001c080f135044008038890b5055901094440700860b800c40e4040c5400401c0800c10304000d03140584d20303140d00e402c44605500c140c400707421080071b120811512590643c0c2002000140201904064944c45c0542406104200850030f000034240d00300040700c40351b00703e4103070014410040f40c0d82e9010b04d2500d0b00a24230401740c1c5c00c1401940850000c0040c8142d83c012030701f0356100d410740300002c41c080c0d0040180ca07000b627a1620030070040c0e4100325030034018039100d60802c4003c00854200480060705403440a48 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 348669901 1250 348668651 348668681
    0x1c1202010606120e0c04021209190803060d020a1e030c09020307090e090c060d05010513090309060309020303040905070302091c0312020714060c0c120705190302030c0f0a06 76
    0xc01000320b41c2e40514040544000c1c00b00000b002c0314004900340c60f051815500319009800440e90014810645c03840a208008070400e442c030240c28120044281d182c624401080f104050010807403500b06403000b10b080b588082d206600b115113070850040320320030f00318854544131003841d410300401039200b085e0b400a02a89005500714200131801400c0d584450203821004d00080c00060740c60001000032456000e0050b20a59454260b0b21084014203000d000780c9000d1003041302540310075100ea2060b001040d81681d20180160b050000031400741007113142c26640340c07005100206404031300c1d100d071500038007a98900503602d825141c10300c40c12942a24801c4c00401c50f0400c1c8030003190b04803420700310640b58444016a01c2d400c07480c00c00e038002031041000c192807144004115113107610100401403458220100c1c1d64190140c01c60054034401c00c213006003541c1246221903401c940f41072840d135800c1d00c40d005903030030059040090352815607800608442d40e4000760342c0c0030a0141612032200c404841360 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 348671151 1250 348669901 348669911
    0x3050c04060f080a06020a051b0106090e1902060d060306020309030304030807111b01030f0e16170c100e061303030e010311030f060102120c03030a1b0807030b01020a021c120201 78
    0xc0c140d482c4e5400050103008541c00181042d056881001150650000d4048506500720309410450080529001c0c206010345804c0d4007022031000091266050040400504a142c05a60900105812580300c2d26502610307076401000144583c0003031440361104400450b128546814010904c1102078a00c0b0148094281c9000c40b21002060150012000320902c0c42a114601c004a00828070b003001030800c44e14000303060104190200e0000aa021011284c3d08025112541a1551108584051752541c0484512401402c02622002d40c400050820311170b0403180b68085142a403240e0320440e40c0c40307164813041c0105504070048018040c001e01c1c00f049070410003001607159100c0130300204410058440041e0880c5e00c204662030080710307182080c646030743e5040d52107070fa40c7e0415103104c80c605041030180e001c1c01d000c0da400b00e448103099998106441d1603051301980200407070f0b480203045019136070740100540c407408a03000c45c4040700000200d000b12542009240120190512000c590401c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 348672401 1250 348671151 348671159
    0xb100c03051c090b2809030216090c1d010e010e0d0609080c0f15010608041410021804020a05030f0a0b1c0519021e06070c0e01051905060f2203050c04060f 68
    0x40c2c00c0b94178000035106000a08a0150300f4140d203086480710411229a49185022540040341e4000c0e5134a040c9503100d15402c0352034042004521603507400311030f0010f24004220381d10b540c801d4940e04d03000200900303070725030060180d101d00b801da400d03040d070503201c550000402240c2c1c020204039400d0040c0d0103c02525510146225046a601c01841030340104200c140124041c4020310103440b00850440301151410701d0314a4005011390800700b00208284110b641c00314840c20301e80203d44c2c4480f4917580da07500c1c559134040b154564180240113040900d5a0f0ba1106489458203140060103048040b2035408a6255180c0149070110b407003000107114009561610050b15910040b00c2500c903005002c003c0c508044c0041480d601903d00050040010350304005800e190060480c0d0596000317030f41d1500b012100450401c14010300d84146038100c072082168424000080d0054488004034420007002e080040801c0c0c0d25000544e081a1495085a40704d0280ca1030144074020041c822100614800c81c90 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 348673651 1250 348672401 348672451
    0x22a011e0c08060d0501020c010e1b1804140f01110301090507030b031b01020f06130201090e09070b1308030d140a0903020a0f0204060e0f0402130b100c03051c090b 72
    0xe440113002e00d61000c40c0e1810003030700790190381d17020890b90300800480b50420707039071039540c0c252804d4220102c05816848406051a1015507115540248034441a84843da10300718010101f4150714001d0107420720300b010f026400c3c040c400a06c807508031496140d50400001d4402c907540540b405d03084c986801c5022403e92004038800c9031b0003040780e411079007848070340d001070b410315000600410640c0502c0c07082001c2801000c0041e022035000b07989030400c1d1511201c15240f5120152400081603000280400c03502032003500400c0022441e484040f040c1e42e40e0103e8a00d035410402e01100d080f5201d55103c1294900030102c0b07540300324204d109109101807a00c1c043e413039612020001d4407245024440d41c0179902c40b501704000404556001c01c4d46840c000351460303c40c40042c0c074128415175850400b140300d00680e014610381d81500810140c10230780d103c141550044030000c0d00700c00780001030080c10032050a0400c5242141988180800e401205207000d66480c040284541100c1d61811211050081 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 348674901 1250 348673651 348673667
    0xe0f1309030302040b04080708010b04051003120509090405012004050109060810030c030b040611090913021305010603020d14010b031906050406060c02010f14030a022a011e0c 77
    0x1585200040800890070101c0182c800c5402c03100c60070100140000b0320200c0020301c142205c400c03000800000c02c03550300704800d0b520155080e0301c60a545500501c0403c8011444081d0400390b4101580fa00d4114000309000c05c000f1982a612a55526241b90302c2c50141c0741c0c0c07041d0710200390851901c0c01e4103007070010b44894100d0142d030041001c03002c0043d00700b002c0b0442c40c4002c0c2d9040b01880200d01d5807464015071405048604881e01410010b0140400e500d460640790000c6005000200c0f682d2040d01c14403032071301c62180903a0f00002400076014482440e108060113000c0994000d0386d0707410700780604800c2e0f030701140c21035104140d6900100300e100000c0d8240c980014002003a68124441800d02d400a40741e9a006075a12a10b440c130700051003500032903007402c104c3c400e0f2695510f06c02020390070f81d02e05402403160080090308000040256041f5030061000e0b800031810101800280e9117402280c0500440c00d0349a03a540b54a4001c80003081c40401880402d080c5c810311004c0c0449100410402c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 348676151 1250 348674901 348674929
    0xe030d0f03020f0405041404030f08060d031116080c0f0d12050f0705070602010903091e0522142a1e0f0d0b101b08090a03080f07030e0f 60
    0x1503001c02d6440181e0700a070b04441c01001d00500070320070307201042000ca540c620706032130480c040386502b01421120b500940205220b100300904d4820042c4e941d071001e44206040010780800e0740980d8000c503d0401c00406410090044c09005101c1582c501044c42410358044103d18441d107480d03c2d104001070103e0a12000642c04c5150881d2208002a40b1814500804400410390301030002c0202d00c00381e05510141d185400381c1d40300d80040d03640b08031104001021210790050b0201038501070189013803044541e4a00c41c90030803401c1c1030407910310740c0c40c00f2501404014050741501307400b4800e030079428465464100d03141e981d15880250542d07203819580c1c403418181c41001120440307100c800d03c7c8140103031417a59803612411580c82103d2044c2400401d200030780944a0f00c000c4603c0c01d2010b108800c0d002c900825408002c1c0071a00a8448925a40180317054550004180001000050300000a404481602d501c0181c0725111860013400504215000700d0146008003042e007440e0b900c0c1d1020380020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 348677401 1250 348676151 348676157
    0xd080313021c06020904060b0412020d170d0501030506060f0307170304030605070503190b060d0b0f0a0605070501050603060f04030c030e060307090306050c030c030402151611010e030d0f 82
    0x2040c0980702207607080b04003942141600b01140b01140034445541c0080c4840002110204400b9460341344402c502d0040f40106003211804000f02c0005080050300c456206000d074078841e80c0b1451500c00801e566000e901140c080d40d85407401001005800c0104a400c030008880c03a007030204106001c00e5030341445218807003142c015203d241e40700ca5424030444015541210301403105190080c2c000d85554025070310501c081d00b02141c42603510300544103008280c50020b081500e4400c800c0c060300c024080032000c6550240c01a0102c1f0210359034064000300619054a4041c1c0725905c504100c0e007124001171615000360070480c10450610712180006c0c0c3e1003030341420040459003090400b140c00c078400040d074907080301c0c00105001e4001e800014010490b40b180400780983da46552001100740000d544002240e10f040c00811b0040c5400152990086424408a030401c0c20202100001ca0600d01e0207031400e041d040c1001c4160350b0b0240b0176812030f500c26001040030107041c0c41d000707142080e80c240310010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 348678651 1250 348677401 348677431
    0x9010b0c030a050d2c0607030603050309061305130b13050903070f0f02090106081b0c0a080a0c0818151204080306010c0206070804240f03020a121505010e0d0803 71
    0x41303070207a200c85500715403581c544c01021041d19110a542613050303407015151003401c00103002c032840b0b8000e03982529801005142800112000d0080c1d0307030002030180705502d44040002c5020b480e043c0850130002039248020802034a10401d1001d415040140740785803c0c00d03d0100511a2000000c82c0c1e96a50f1100d00320a480035182460356544044010095020304182e000003400d075071105206010342442d40c0c0480403408844400061072144194a140a801220f444c001086c0d8080150820510b607040440da08007603035035110f0240e844612000c4010b000094040781c7d6091070f600b207400807054170741e82614101030b8402405d000f202c01840100039080000024106911580b0702c20401940602040e859107090307d800c8405400a0281c03d0480c64083c1410b0a200444c02c2400d9801c0309684403107840c841144001c9006c0c1d40425000c0d0144550582800b8216140d8461408144001100088014240300004209006005095104455449860010600c0c441c2182d0701310034901001c0f91 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 348679901 1250 348678651 348678667
    0x7090302181b1e031005090a050115050901140d06080d1d010e031515060703020a15060308040603020a140c0d030e070b0d0902030a050607080a050f1608130206040f0509010b0c030a05 80
    0xf90010051b0070242d0844510000e010544e5403d4203e41c1c140e13040301c8668200030700d4102d011035440c001d07107803410300103124403c2c00340d0141c208000070703c60790740e07120f00c0842c05a071603001c05480d1145004d42c09000851010b1034041070722820b0318070150f5400c01d181c00e01944941c4c80c000fa0780c48244038007400c00611240c000c500400081120008880c01c0a0711090316003201c4d0501a454101f80c61041d2107a1802402c0c0014003021489480309803988000194289401c0c80d008a00035046114030b101800740c4409844003050146024120141c0d81070300801200291a07001816108824259000b40d800840184581604482550a400700da01400503a2010b0b40c00000c2c0343c03c88200e005040c9004460034002c0140c4d03c0100d4038441e400006050003039440e06521a0b2500a084510013202c080d900881c03000a4402c001c80c81d001211003009c1851200240c0015029500503030019aa10002910400490425100b40b80c0140340f1b9a040c1c5003040072540c4c209842e8402c0982c44c50800c180060499 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 348681151 1250 348679901 348679921
    0xb09070801021c0f0f051611030a080408031e0103080403020414060901091a0901090203011a090904060c031b030e070605090d0f0503070c031104111c0507090302181b1e03 75
    0xc0c986400444140600d05140020407040d007020510900088e80c4200d010340306250001c211600d010040d502e11300e071a0380f2501d038910242c0016010220003a071420700d80d000303264401c4115000c1c502840701165201d00c0c41c4100230032a03905041c6020018000401c10800d0f82d41c0404442c112450080013003a18481e0644800b5070340b20310b41c2500d510241000c004101021141e002e141640c10351f41d04103014046010300708a09024122015034000c0f05032002400150f47c4e50011040f6403050708000c59000c411065504e41c41121484d0b02c40000e603140424040858100013007001024203040503032802c00780c100490340c4041402d4002d010f00ca4450380003001c01c007003081100d84c810740104e9120303082a140c2ca0410310021001c815039105da0b003030200a0070794001d403400311030400d02c0c0c0100300c00c00e0107150208640a40790003081202800f07103025001015880e03c25030b56030210a05022220305180200e142d0440003808100952440c1042c050700b410f5000d85400142c002c10885c40d419205d9895803250 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 348682401 1250 348681151 348681161
    0x80306130203180c1203030601030b040f0c0c0b070c02011403070e060c16090c05070b04050106080a0501061a0408070303230c060a050105040e190f020d0b09070801021c0f 75
    0x4504028400070400c004000b40c403080320f60300f980200c140d42c0c0800e05101000f0803460515a009040d81003000410a00d6000e41c0c07021000c0b440c050400318074010004215022200b03e41e100f0404903c81041c4101046444148254042160b0509440241075600002c004041420910304d0701031000000c12400c07400f424a154580000900300b95894a00025440e210303c0d0400460804424001d00465801d00a0044000c000f00c0d9648035420303d411901c0e445114140034001766001d5594600220307408030280004001180110004945542340041e030000c00c1c59080340e0346094000030301042c010b40001041c20811641c240c548011941d1007400d00c45800d4000002c0004a040700060300007840002007091071140c00b070751004111036030381da800740800d032204040454800c0e000317803003180301800c030010080f444a8020211060034014650204107114103254096400c076400d04200a11070742d003004818041e00814001391b0034404089200055114040300481007262900c803010b54401d580c1d484 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 348683651 1250 348682401 348682429
    0x406090b09070801061508070c060f1a090c0405031c02160e0a0e070f0504020c010f020c010203040c141e03030d06030c080705030114070c0206040f030827030703080306 74
    0x90904a0900102080d40d410302d0744640d201c41e50030028000f401680612280c280d40030305441c0d0110581c2c03130041c101c4056000340c0d400c440316030fa104d840c0c2d402000c140c414515072014420703000c18041006800c2050801004000d4000904208030512094801145242c103081d203e80040035140d00c80e610036804c4c58041c00000b60382c04103c80001840c0c1d08203d245e0390060008117420007054800408054170b401060103242c041c1404d88408010b42d05260b80109203400b04200001207201c89440400203990022008064980d008000c2c1701c1071250a00500c40200320184001061000880104040c80100044103da1940344a0b0500c80b84e02c0138001c407400d0340f0b004d1508004160716840c04887e02d960078041d500303062040640214207802e052048942007041a0100c10070341d642d0407005c4a610040001c101d030496000c0c0000512610341700002d00c0514030481600d078440026101405800c00c50343c09000310030700e094030044540d803004141d01003507a40003181181d0340e0303a804002c00d88903c8102d02d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 348684901 1250 348683651 348683663
    0x90908040306050408190302030421020c060a030f0e0a05010b0102031612030f1401060f050403021e0a031a0103030e0a0308120606390102070b0705070201031e09032007030605040609 80
    0x100c8080d020740d040d8002c5114512401d00c080c06080040c4444c5070012030210500e016904c0003e5404dc04e141c0703400075200388045483d020865205901030035095900e00d2440030000d0b405144240c0401c8000e0141c2440f50800b0320042d0300b00000c542c540702103135041100c090301d0286403891000066100e500140d94820090703c0501c100e9400d8001800e010509218001c001211078480300c45a40c4a8811901100e4004001200c2c100800411249010007203050550112060800000060203034124400080143c18004035940c5181000b60910380b0505465208010004060000030307540c0003520400c0c07039803c0010045036155404a09148101d89003000801c005412841c1c0038002e001c0004e13400c00340c026003500c9890008036904d090b8012032034010502040c040015400610035800b0b0301960780145404606144044031031300d9405580700d503a1a140362030302ca4680525411144001c07404050036910a1019546141c02d600d6101e540001021992618003080601c040ca0f04517500703440d0020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 348686151 1250 348684901 348684937
    0xa080406091b030f140309010f26090718020f0403120210020d06031a04021c0804090207080d05100503100b0a0b0d0203010608091908030910110d06090908040306050408 74
    0xc01d10800d55024000c040301c3d0745c0c1480d5688402e0b004088103507241c2e25410707182c07180c7c3c4141c4030b0010b9504500c404883d40726811010241c160201d101420709000d00c2844000d0107096041c44050308030f070101c40007800d65050040105101054580c402ca80c1100c0e00310107050011031400710b04904255043d11750320340482c00032991184010b02a8864402c032445086c0700c004900341c9032811140303104200c60103035000342010404c401c8090f1000005143c07503c40c0c4903c03482c041d160740010007281c001c9001581c41010108880d040c611480c0708050f08400d9220881042603e00f6001176038480825640400c182e481c0e030b42e5403c198070340c803404038040c2c000315030200c1d00d41207810043d0000303400c2441920300261412002c01d444030f0021070518880d40041400c12918030140d101c0074041d50019205d0340300c5100f02007441440d07000b184103905d29240f8a005030f543e18100420002c2c01d40d415070b0021200d070f0b0f2515403c0e500041442c8101c030100c1c2d91160003c1201c0d512802c0201c41e41c020500507100241c484 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 348687401 1250 348686151 348686153
    0xb0a0c17010902040f083f0313020f06030906011e050414090c0904110405280615020d0e090702120c240105010c020112060504090c15050a080406091b03 67
    0x9070050301c2900c01e5071710144012640c0f100469595041c0005010281c070344c1140c030074880c1e0726440081126904a1003000000111a0b1070316500d41d10484a2440320203910800b401146440000f01d542ca45040310f41c24150705005410300d4507410180b00d540c0c4000740d011928400d00c442d105240c001450010800c0060000f00c1140d2000c0501c04c0302c81c0c0c0c0d03150103803500c0e41c901882c00a05c0c0c103018030380015154101e224940c0c14000205000b90032500032a003640310040644100c3d21002d92506541c87d004101c2a2074000c0501c0c2c01e025000b584020f640181c482039420f1603100140344c0310700030101e41190003034907182d2040e4108182001013007006e0a000034130310041400065100007c1c400c1655004407140901c00318402c20000703018107400921018201c0d8090b600c210582c83d000384924000107911569071001030200c130b4061108440030117030a401041001d52010703a0211905050500b43d24144880c0c03c024080000240700030314095030380d1001d0043c414a04140ca00e0b0040f49501c03190203a4030303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 348688651 1250 348687401 348687419
    0xa08030a110c01020d0516061401030f0501060801020316200f030c06070201060605180109270e0c1c2918070f090e0c030a060c0f020a0b0a0c1701 64
    0x380796800954070541440d81465440066080f0003039132250348660411000085000b00d142e07840800360b420680382c2098403210419410814000d602c1600100c0c40ca01581c1381071420340d400e80d40300310610392050080084170885014210ba40300741504d4030607110494104e1140d8110780503031000d641d80c071550860703640a800c004000d0060340d95140c1102d500707640300b5504900f43c802a01648001071014040c5c0c241403c841200320789038110506050342d003a9210512981c01c0340c40500383c6070880312031940428130304078103210f0307422034950740310242a0f01c0d41e00740041100c0902d490a01000401000d501c41c0510004a9040f0340d03540502c0e034440d8203030804400700c60001c0e10030759420b81d840b185417180111a0000003001004c840c0d1700d0400005c3c0b0f901e4011010000c1903100105c05507806101d000202542e011302114210714444e40d000180e603d03601d01b008015005030302e42c410965200450030f01c003240c0c645005940c481e001d40400724070f9102400d02114450300440c1400c04084240d0b00100d07034201 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 348689901 1250 348688651 348688667
    0x9061b020c01021c021c120c0e01030b01090b03060d1e050a0320060105060a05040807081513030207030204021b0d080405160e130507080601030c09050f04020306060f0a08030a 77
    0x1c0907400c8a081c1010070600f208041202d90b003c0001d64440c61500040c004000005003904c1010b0510300c4842c0304c40c915020a0b5074903c10f11000158950084840d1517806100c0c136410f100303080c40c003411018242080d5540920015004a105d0800b8001c0c00007008080400b0740368000314102c10144640c0e80e450010760310a20b0010403404250f1030344221345200c082541044135504000024642c1c1c3c2d113014140300171580050808410098200400f250700241008000002c1903050010040c3d0182c560700d082511401400081c00740d00b0051000012075030003d800f07400d0302d0701228010780c0c40d65001c103502103921040282010380d0184c081c0070f1115540000c8500d00ca14056415500c0002c52078100c008800e015000700b55000d0208004250070584400d042c41010344a002144c030102c0d102e051440c5490001d03030046900804004040c46003050794061145c001e000350f070907031115003001d6001944941c0020122402045860407500b01135642494080051041c1c01c141c0b944d50002d2a40188501 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 348691151 1250 348689901 348689923
    0x80d021305010819090503090a080309040b100804110609090a0e0c01020d17040602070b0c0714030702011d0f060301080c030c0910121106030109061409071209061b02 73
    0x6030342008001580d5000d020002e02c41c0b04284c110b42890b003a8002c10070300501c04c0300410f946a21007407104902e60b46640d040f200113403200c03100558682c04444100400d4500c14911140030780031215034514002d07040712110f50007541c48a01403070b001c11f26401080745402148181680000f5001c14800102d0b130f160b008616841c901c109681501c0741c40b10042e44d0350034100ca0040c001500c0ca0070340030030340b40190305400e030800e1080700c01618144c001c1d2152552a4401c0d03807240d001c0b6000081c0101007002039201039504500010140d824a40b80360000f0b0a030303c170312010083c06101001c100c0c1d4401c0d038424507200c104100003807145489503140d04442c0e030b851111000d010f0081c80b5032400d0000c1d41c0383c40c2842d0f40c459101a0130102c802c2d41401b034100030480b12084c040b210740603080001034142c1d0fa004065400b07020b005000003200341c98016070501144000007814002c1940c0000d01c10316941c0a200c089900ba00a000450304101600d8048020a0449440500c224050341200301042c1d010a40b08500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 348692401 1250 348691151 348691177
    0x10f02040e0a1104060c0501090807050105070809011103060405040303021201090f1406060d0c05210403140315040b131806050106050414012d0c0b090c0303070f0f080d02 75
    0x107503850681c0041180c0f40b006100030086800c1c001081400d2082608000e002e2241002264082090361002034a810100c42101c8a0751a4000c0000b002d600a0f00640d200204100034810f48003a84000555480040d0015001c3c0d41c80d04001000d240c000c0c0c041758003840d80140003140641c2c3d661070809c0240a00712a120409040c00341c0c801b080311710100c08078000e00300101a98900520f0044100080140d44004018040140080d04517821540030440010f451041c42d0445d038905850028001c050a600400c14400180144620380d210003e46200d540c2e402d540000381d0b28584400150300f00c813006540411541071130b007d01e00184000c280100517074480c2d54280140d907251070003599280900e000c2d003031004950789140710b0f95622441201c08a40340d1000e069481003840a09242c6a4861400502c04265512590320400080100407a40012240013400e044001580061703144d108087c40507001202440c14141817002c40300c0000c1f2110347c05400c0503035030b20101140c000607420146500c054 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 348693651 1250 348692401 348692429
    0x402271005060f1903060f06112404020d03050c070f090f0504030f050d060b04030305120711070303050c0312100e010e0103082703030d060f05060a0c080f0903010f0204 74
    0x401d0420506036403002c100e4444050034103010b81813040074004286019010980c0b11400080c0800700450840c0240045503030303218182c80c1d100c040c5450034417a2065542d402124543d0b42e580d140040810f16003007035040b155048418120304044969000c1c5601186060180601c0000c2448560f0820702c110780100406000c000c90080e9a00c1c02c072401200c0c003401040502600341c0e90710b4402c0d0024008002d0b220800100b05855242e14a8603812642045020a4000410349284000a0f04c80c5502000c075140c01c441a02c5c00d14801e98841a403480010b0620501180f2004011814010384600d021440741c040c8507450504c4a0060410161007a00c1ca0450742c40d001040c55210008054160f9812000b440d1500b030203516407150f00c0c00348100380009400010300030503440d942030000700603e0701c01100c04a000d03810300017421540250b5038801072242600b000481440c40c0c0221072403105070780100f0001d172139007000122052148a0f000d0700662651a00e86000c042c090194081e0003607034001c50b600b0503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 348694901 1250 348693651 348693659
    0xe040c0f1101051611031c050f0f01080304150306120f0c06111c0309020901030b0a0b040b0d061d06070c1e051509030f190f020d080f04022710 63
    0x1c201c540c1554034504081054605184c4580101e0b001180311403400100c0b40b030405142c00c4010500100c001040d213260b150340c03e1203c60510ba22030a9004034014a204040b9458644c001e0366034481c600c5800d0b445545003800400d40782c000e501c044020000703003061102418a500e0300c4680c84001d5002140c440c0807644010800c3e0b0b01c07035451404186000c500614011004c0c0c0070806900443c4c0c03080c2810192100d0002340141c0b10f50829900035442501a503900e0b007001d0320100151190480c0c4240141e140036580d0000341c6c0d401d00c681300c666400c05400140c6407442c181c1000302c0c500d40e0400a055104840900103015488031030280000d0207140d41441200c402d0b400361604010f0800d001d40307290b10503014403081c20f0700084416001046001120310705035007a400c1030080e40050000400e44054524600810303900b04c4183c0845600c50b20190a01a0704114084c0c44600064207651450b082d81001a045441d07800c900700d02c1c1c80c07004004071980034804d1a4440905411100042030030b000c868009 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 348696151 1250 348694901 348694903
    0xf03010e130507050d0602071211070821090301060b0313030807030507050306150d0e070305070f0b1b0a060905060a0606050a023403050a12140306040b010e040c0f11 73
    0x4240c5940003014082583c91300013041540d83c01c0785e00955229a00b0850701e400501c60031050352281c101600d0b82c0c900010900c01d034904010399540329000c584c003d0a004c0b26410a00301c081c6215031402c0100e147c42d000181c010a005184940204a013420f0000c10311150014409241c1c06040c03280c1c2d6040d100360355607101181034a40640303400c00814001d102050700d5140420040d18001c04480b82c003800e007415806e51341c050720b014111404154002401c14401c0c40010302844c0050300942e034805c11184e14140c04265030303203d004c11075450600022101400782d0401d0280c50491a0031a10500046042d03041580d16a04113a4015000900c2e0000000c2c68500900c140c2e00c05000035000ba140700c400d2201d028a0410f02d0484c1948400a00001e1520750031a5400c2c1c400030f54080e0000b04419809850b140b0100304844500406005045803a41d2446071404112540044191801b0401c407205000503104180145202d0b035100307050170040c1e0300080c2e0003c0032543d000265555400d00184d070b02940d03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 348697401 1250 348696151 348696181
    0x6150303090509060d020301111c05010608041506030c170f070b0a0e030a02030604060606021218121615030f1503060b190e01180c0c0303051003080f03010e 69
    0x380410030809080026141031000503038040c8016240e29100d00382c43d8002803c40f004580c0122203410041b892220406040c446c0d11502e84000504010300d50414001900207403000b80010003101d1443c103400c0c01140260842001554441c0f245e2039916100e00c40510004000c016200c824030543d4100c20020704000b4016040300d4040303125a01e081c0941034201c0340c810700180700b150184136201400f00143c500708072032403003903000340c6002664a0510f20003c0c03d122180154841040003032002d201d14403400c501454036040100c030204508942500f07070b9130a000902606111482003654006034020301640d000e18000707081c0d0340030003400f03038080d54140480301c0d115003540d00c01d40401024800105164002c0341600c0d0028081241e151020410030800b0340140c0258602034101001000810001d400d01c803082d000c00642406281282e807801007003c040460013070200358880c40800c40602000c045100510b0308008000e43c0c54418421882c2150700038407451210217071400c0020140c40360f021003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 348698651 1250 348697401 348697403
    0x60b0a0e03060f06060f040b0408010e0705010207030c0501120e1b0f030a0807020603070e090c0a033c02090307080604051b0a060819180213061815080304060c061503 73
    0x1081a0354445400f032005c59040102c040d01403840412003c02d04c068510f010784000c007030120011400b44500755800c2c1c00e108599208a05550000c0d20910000d0160f044110a41d03d083c60600e203510f0340040c0002c01752040c501c0c4a07038580206141032444641802500c48940780030303200c40d52044401424540d0f190000d03540980b500806011190041ca07050000b10340000491401c840499500c00025006d080180d8901c0c20441c000616000d00d2034150003240c8540c5610070300c010308036500c03200300144400c00c05180d00c040d00e401c1000e18484002030b411303039205502c040c08469080380c44050043d920701042d2829100b07845440c65800305194400801c041a000207003200205500d0700f00103441080d000b07000c00010700b8102020450840d11803240704413850301c160112013130003c603005001c400000c1c0c1040c2d03120303e814400d0034800c140c402c4940c3e440d41d8600c001c1c002207140e1b440e0710000d0080260b03045403035a800006800070360300e5401341559000a009410421062070f036600310000c401c1003888 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 348699901 1250 348698651 348698671
    0x1081f030303110c0d0503010806071d010e030109050d120e010c0203042306031303081303020601150c02210d090f06050d1d07140d0203121309060b0a0e0306 69
    0x280520010744260060582c0b00256030210741000d0040c0c00c802e00302040e1007451000698003100400c1207520811a0325040030650400ba29080400071075a000401c0f42520941840302101003042c40c1d480943c0444101c41c0c2000981d01e55810300100146820b11a2000c40c591a0904601310307580070781846541da800728036400452a10f4903200c0d111b803044440c904400712190b002e01148221b920355400035441034408407a4003040c05111710b400740200c100500101d503c0c002c1881800d00094000a09606541c00101560b6070039103940c4003284d03007180200f00207400c00b00b6103040c00a24022400301760000c1d1088426501c0289841c10221803800303051040c3c00e900c1031281c1d02000824000c3d4001c0c01c40d80301e17040000c02c00240d004544040c10005021541d4203038003040703041010504600840900c1c0320b00301e030003542e140d682e5000695902e02c85030060700035400001d090550380d05104c0400d0000d00d0360010511110b552a800352445400487c0d00b031021804002901c10f00d072501042c0a0700c01c0074160 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 348701151 1250 348699901 348699961
    0x61e0618091d030403030e1c02011236060b15040311060f18030601091e02090607051b010215010803120901110409060302120109021e010302070c0608060108 69
    0x3920100603010303410200c80314030b80c0d41c0c00c614680ba80034001040a1800307521145142101071040c080b0b248235098015841c003000504060060b030340503229030b00002c2c0d919804201020f0610400880d61880315030f800d1110350401c207a001580101d544102d6036409601c04002c159500c500348400d0a81c10200c1c80500b03041001b0610006420b40040080654040d160070f0400c20410250003480c1e0007141e181d15006200d40d840c0001c0d2504200c06c5001d08041c46c07062020043c2c1c032424003810200c060400d024190082460b440c43e4070381c001524140750300300d0210792442441a00f001001e01c1c292204034014050010141c03c04607880900c0741c100d5032060300841c508007070700da484000c0e25000340400405548aa8055045111607005040501702400000030081e01d1481088a55105881c813010355904101034070025988003a408078400b805090141c002c01c1460340101d00a2064000042840d1000754010030a264020b00a5104800c00c2c2c80e110344640350250704091203c0d982800c405148048 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 348702401 1250 348701151 348701159
    0x90111030606120709051201050f07050c032502091807050603060f0d0507150306080106080705100c0c03080a09180e060c0703020307050d0e010f030203091915061e0618 74
    0x810718413540070071315161002c60540c660700010100f941c1d01c40c20504903034494007481465860202026042051400d1152626861440d21522030240400c080f41c100118542e0002c0350b189214000324490b07008002100620340800c00441300c40104100d051544100c0d040070441d030826604a03800340700c0040c110304001911100b044001600f840d41144d01703000d42c2000003240f1109006240f40388406d43c401180c0030f0300700143d040c2151401e07800b08482e80d1008108001c5d42d100d540c901981c03801c05107820743c1c6080c1d5505110441e40d040742d2009013504000142171000b241e128000c2e60949058002240e00d003020701c43c45c402503ea004c8081d081641003a004a10040780100003410118070900540c1c1c00c1803407944900d420144481c0300840803804600c1d01c4401c0c1e60340300400a60030b948904007141141840c02d1032640d1646904070b80d44c610324003203051100344200194841161403502006201041d150785418103040080212161840400d5002241c0039014200c00c401401d000d107903505e07050340340c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 348703651 1250 348702401 348702427
    0x120305030a0b1c05010b100e180705070c06020105010e0a05090c010f020f03210c0408060c091813140a02011205150a060903020114030c1603090801090308090111030606 74
    0x28100c00c2c50381c4621024040100d02c0c18141d089002103015000001710386204805000b910b12001ca00070040103a0200d100003d59220b070703079080411603ca590104980c0d9660780507640c0d48200c44010701401c9000d440094a1079054008030f042c2c41d03203565002070399200e51442e901901c0342500c0c0a00c107600603141c0f4202c07552040241c00015a414030481e0056842c504025081d58007084078600c0e062401040d10703116031b07481a94990003210711000645030514143e03d007611504050001c0e441e07070900242803017440c0d41c0c0800c3c00310040542a80140503007004007103d80d4920854504460700050401c001c40d003080081800300940340c06848902140c40d190940070020070700103099020410904c03c5000c00d54032040b150030080c0130541c655035000c1e41540009059004060703840703000c1c0c80341041001048541003040c6ea480c44400c501c0004050024501a0f4109903250080340140d0301c0d00e141d460602d54012011802280c5480080000e5100041e001c05180300c1141d003c1d0700700307004001884182c44 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 348704901 1250 348703651 348703661
    0x90a06050606041802030103050105090f0a0611040f0e270d080a090f03020f0f070f050f01020709020c010b01030f0603120c110d030f02010b010c0b010911040b0a02070609120305030a 80
    0x150042c001c41c5420344071070f801c1118505604c440c0700701903408001401003240900c43c20350008000742c010101190307400402c039511000944000c100980b20303110503214103844803e81e0054500015425038241d155900310452030740840d40c40c5500c424490743c040504082c0343e00c00d0401c1c01080d001c0c0ca105080714406440504010313004c10a403554454281012490101280c0d00c5580f00e98040e0007a11400503160740350650301880c114076504459404c0007010300c1d00809104441068034428200515000181e00385103095000000050002600100301c58041d409030822817000d807010082070f002070036900102c800d14080140008074000d03403400c2e2540128040c01115110300c3c0d0011140c0588070208072000320008007140404d12444804460503020f001d00e0320105020710b001d03d51940e140d19200885031041c0304810426a8920900e0540e041800480c1c015004050300140e6481d060745009584155521a440006000c0f0101091015000264444464055076094150340f41e0319407140c0209 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 348706151 1250 348704901 348704911
    0x1404050c01080624090604150807080c07030c080c06010821030c03070e03071502010203071205040507061809050411010306061107180204080d090503010b0105120f06010c0c120c0509090a0605 84
    0xb4014000340705c0c1552030740010405040d2025200b00c41172030040c7c0c003420540c0003622503414002403c003001b504210440a03500ca064040c1b4103581d024960741084101c911900f0030221040c01443e0000c80c50b1440010302a29808420360003542c2c0c201800340391000b40c04107a40c094101e10f0100045028940300300c0c40c10081900090035284190307950444802e0506060764880b001d41d401200f0803100e039400182041500c4091507080c4410314050350f43d9600c600c982c2c000c040502c603040c540c4044200d00e160100c405000020010407240c2402d062419200c2c0e010200c0900180c1880c81c0071a030b0713611a152441c032505020009201d0241403031110404002a20306075134086600f0b100c009102181004a48000300054480756151400c00e401c2c503003900c5010305e0a80c1030020412003504000031080c0002d0740410310000c0360896468490040301c0483d03410001030b0050001250100304110001400da03100b52083c001500c50550314014014003a00403242a40300d80c11607000c00003c0317070a68011560103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 348707401 1250 348706151 348706219
    0x603030a050318120301060f0306060e0d030f1809020306030f2103090a081b0d0e180603031201030510060f0b07021e03010524030a020d080f04091404050c010806 71
    0xd280d904507540c4c658109900140001d40b854044203d8180c1510840024100d18600341e0703400e03403840010030800110303044001c0403c012210704030314141c86030a05650300050111408000c0d036503040e00b04040e410545405100f4040d205140342c09000005070765003000b400b0401081d5000c010300040304150401448018580036201000c00054080340c01020003190500d0082c488038000482b551504800030f40c3d680501c200c01030031452903500c1101c18110b03004e20a002201a540340e00100381136004081c1d00e003103113091005c004000c009001c50b0b0b0000c8180044400c1013442d41e42c0c0614461038149125007040702c035080203d0009410001507071880860310041c0300725056410008a82190b00072a144011101a008500754004050484003100c91044004090490351600000c1c03c05507080001070124000107070745581d210070142a41d0081c10300e40000c00000701c03002c00c1c0b021110802c550403600303030003180c00145c240c0d03000b0403c150007494041c00c0e06048004880e1900340d00a1100c1122180c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 348708651 1250 348707401 348707413
    0x201140f011a0c06040609031b2013050403090509090106060c0f0809030604080a02011a10050703020a060f0b0f030102210a090f2603131b0e09150603030a050318 71
    0x603c100c10014680618405c8900140b4405213007001400c8801c51542c0100c0b80c08201c2609010500c007034807a000c0d8000031040006d020320030b64002000a802d500350002c0d01414a020001407640151a0317104441090380d0b2000c283d521340083c6404c98115004260100300c1050020021600348030410a61500c0b07021081c0c5808640030009281c14000c032011105000300141103202c00d0390a0141e400c1000c3d41c0301544000c0b0f00c80c0c1c00000c519400b600070160410801141c80028107108003c00000503400a0317042041000900001000d00078503c1c6090003842d82082c1e0103818101407003110240c002d40e1854240100711a550700f0b080141c01fa000c4803c0c00d885040c3c2c0310206240c800344d0082148104002c007928000080c0b03c1182a10141407410514418020030024200300825000c0030340e40050701c0f804400b4070904407401010903811083d12080a04204100043c0c0042e82140c600082c0040142943e00c04c82007583d60310400541d440094018004906c140150400480c4110961000e56507 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 348709901 1250 348708651 348708667
    0x1030207061802040e030909061c0803090610050a080303060103090204021b0604020a051c12120e0f10050709030f060b09040f17030609390a0201140f011a 68
    0xc25a440c9881c05003498080300440c0c0304510b00b41c820640e0041782c001c007440c01c0144010000d10701301c2d00184410f001e506100c040d51078a14165840023070541c0e1007482d00d91203091500100f65a4841210003400c004503410300071030b4038075040c071108084840030001145140d48800044002d4540f501003240c2041c1c003441528648207002c0103482a6419010080c100381ca0180100b015002056000f13600a126000002c01c40c007041e8a1030108243d00110032603206c0c40d40d802c0803a40c40010201a072012458901c2c6407244200c041510000c1d804104100d6280c0c017072801081e8110740040d1030860100d00d03001c1d0700f0000240460842d02016004080000b114442c501c04074009180c00c80302181e40300040804e220130007801d06040d080c00c1d2080100d050461a2000215802d2500a8912260191150400d80800001a1803002c00100c204a4070900c0112a140e60903540c020303806107000b40d400d00060903044040e000c50a4402d603880c00451240c3c7e484e001d6003418001d50441d94412012040117028 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 348711151 1250 348709901 348709913
    0x30b0108010f050a05100501112109010f0908061603060e07030b0306010e090d082802180d110f15070b0117010b0d0210090e04080a030e0307030507080901030207 71
    0x60003041003030004500e41c001150100704a550040480d0112840d15040c41b262503d07500607101a907034282003414105d5a0100101e20301f103540f100801039a07680d20111621fa05210300a420303940310a0b02c0b0b50f14241c03190366099a080d07400303016410469010100145442c1e20041240010440500b0005829925006050103010003100d26070042522004158484d09080107800d0050402040c062824200114415110251001440d04010007540800c0c1910310b548564000389020b4020480c900c0c050b928001c0194100011b003910b5400a6038450310581840000e03000c100e9400700420444800300c104211f800d0305a0a480c1c0e4010841001c81c0a008014078010a180c0303026070883d51143d0b1400c41c2000752035901494014069062041000d01c2d504e03109008540340364100d5801d040300400701c0086942c542c00d64842c0700380d5008a0240802e000c0804000d0401c00c0d800d9400b400228040000c480d0f0364407d400009000409c01c00c07441004c04d4424016090000c01494050301c0c04106460301 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 348712401 1250 348711151 348711173
    0x12030c04080f0106061707080a1d06090a0201030606020c130e010b030706030b030c04110904271b06050a080a0e030702040219122d0b0301180b1f05010c050703 70
    0x29290b1365442003484000d411144075282c40300c41c0c001c602214a00f051006240a0380a00f890504030b0300c51803000c48403a49002c845074018100422649646000400b003a9030714201e000c04d0380480e14001004c11071500c0070030b0160032050080e04a524807030003101590300414546c1042ca000b03540c1e0340c4014603584e0741805010000c1803150340c0410315074000c004040c1011068041c0a10840c50140e5171402148035038162070796450304840000d61140d12001c003e040c3c28003d9102422015681100d10402c140c00a401310b07203160420580d1400740d01d800b001e603028442e140b140000324003a00d00148a494180d00f01c02140300145041c2c1741000800c1c0c0c0401d013a60418115035005100580b00402e610303a200860b442042000384051003a400110302030194031100c24441c1680301491001d17141d2444940d0001050b03044064020059410502000ba1154a44060850700f001301903010906241d007040c6804035080c1c4451640381610320b17000049da0318420316281140c41d801045800404a1001c0b0b1030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 348713651 1250 348712401 348712423
    0xc0d140f0105180105100e01150306080304180f091a0702010b10050307080601020607120b030a021e091501050301150c0615140a0f03030c08040b0703020705040b04020c12030c0408 79
    0x880e00e01002c00f039501402e5501c010101d000740070400c40c081190303034940900d81e0b0440b02c04c071540003100c4141c02d20440c060101034101c0d500500c0000380000d50445000d82c4181941d040361401c124684415034002d017901c0c030080c00035142b903500780001841c04c2c600c11101c039000600340c000010810700d41008261015484406c54001c540c0c08420448078070703086030207540d00034400d1002d4001072400c0b90018022122201c03c40c19156a41d400440558408100d0345d0105500102064080b94085080c052848000101366004801c0c01000c02e05503015a645020410700585900341507a007032419284807107071080750f013400700310300c1c10f040a010584600c100308500d522112044d603c40d003003024141807040c0d16014130f03015a6007180700300b000d0241e2030b5144007584d6051406440c00c10450404040314013854100102008000641000b016000280c0347e0071070318203803028046a84020308000490088450081081c0c0012808072003210b00b00f40196441405072140300d00381521106600e181100e2480 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 348714901 1250 348713651 348713671
    0x10050403090504140718050d050309040e060f010b030c0d2c0a051507030603050f0a050c1c0303360b0f090d0809010912030f0e0c0d140f0105 62
    0x6110034554001500409440203032428455481c455500b5005980014616020410030303030148014664226540c03001850024981840710034103007080c649070381c042d8411511032440c103017500c1c0000300e0100d2881d204030030b0240200c00c182e00c0d0076144141c0e6400101941d00982003005104140d2400d03216201c0f0303030b2140d401071b5841d9580410000c0d10880f01c1444060140e03100708000d00001c2c1002542003581200002d4111803030b1a42d00060700640040d030030051242c0201c082805079002d0024140164500400c02c944016281c1c40034004040444080c2200d0030100c0c100d504040b03400b0340c02414030b0100032400040250385c101403126203a0203550744007140086410907035050041100c0310f683c10007003448200c002403c081c941c0c682d03100440c04550042c403003030500203082c050307082d80603403012900044c3c41810020000343c014010443c1050040301c440c0f602c002c00031030010000c1c0100d0400300c0a00031600b081c26684550007800c52a00c2904c80904c1002d0303407140d41520a0040c240503282903a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 348716151 1250 348714901 348714911
    0x1171b010203091c061104050f04020c010b150a090501080601140702030c0a080106032904170705010f0b0907030912030b060d060905061203130506030a140c1c0b1008130510 76
    0x71800406a6120208105a844e03041c0004e21240e035900d049e08441d4001140c005a440703080c2c3d00001e015000908989a00168042c0004216901000184111a01e0388d82c4c03006010388510054a414000359003982c009404000d2000394240104020010a4002021a1240c170907500001d000fa5000e0342000500d651141070030000c001e01000302c0780204808284450024000400b251180e00008201074500c600090680040050003411514416003100007480b18200030b000e44006481d081500c2c60203504014000340107988207100d000342e1554040d841d8010410740240444c003801040c0ca886602c01c03800c01130340700c24084c03912401008002001020807649400e40400c5828010054035a038140c00030040c0c450300d401601c070900140c0380700b00c1d1305a44030303112a00c2450091000e80090608509400c0c04e00400081a20240041d017110304140075280b81d50310014001c0e9050305100c0350b0020b52030340b04c660089000d003880380d0740b00030b0204900c0329006603a21000d150042d01c4004910403a610 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 348717401 1250 348716151 348716153
    0x5160312021002030c030f04022202030f060907120209040608151e040b28020a0801030b10030b1302030f0313050a140d12050903010e0303090601171b010203091c 71
    0x50010341c0d200d0342e101104506624040341c02c4522840010110802401c0f440e0000d411980c0349009030003000c564484800c0112040c0c4a014000c1d40191403031400e50400700f001074043d20381525000d22602c80703a0384c0c10014403426030144020350410124141c0c80303078031444045a900802c202d84400b4109030700045016041104001d45100c14481c601c0301e000c40c1d010701f0000481ca9054805402812929490140c036540040c24082ca0403c0642e83d0b142d42d000203900c803d03407540078144a0682e0f00503040300c200340e00d4050200800c0c001c680700042800903d03500103002a483d14800842c0580003500350f94100c02030010490550344080c80d42129000702940611203070401c2c10560000e443c203000991070308001d02c0001107141d0050000103000e58021007041d500d00e8499402e55411010140082c0302194031141250b803079400c1114800403910480000041d030141c00125042c1c20316159019007072050040c036010a0364410f072540503055100801200007640c6420b920501c080ba021f0b0304001c03005810f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 348718651 1250 348717401 348717403
    0xa03110c10051c270204060f03050102090307080d0e01080c04050901030312050606040501050f090409060f0c031a0a06110a0b010b0405031e0d0309020d0f0524070f0503040516031202 80
    0x60305104111586014102c00381c42c8000031400764508413030f9824940d449050301c0081d001d00165085450f5010030350400108020054016040200c02102034a504503103a00185d5640c52280307500703c1c00289200c8a21446501424036036421046a4422a1500d61254003203403800a081e4421000110350701802d2100090701d01c00c49810503412100c40380b91514120000b84180950701d5401c800c00000110501580c0d0340c0da100046036540308000f80b00d102e99071b1800380018241400f040c1c0103e070130041914002d00e0034044004010700d00810f8140828100030b0111907841c40e503e800541d41c81852818030101d0b01e00140319000304504030105d6515801d200034542031440420a00c1385c0d005403a220020380740380100316191103101e81d1400107610940c0340002240000e41d0f04015184041440d5420103005021031740c5030360306101c049581d00c00d00c010344480024142c100c0d0140c00040000a029000b5449503004640150086048480c0b00348400a5400d91100c1036008854215242001e907a240d60 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 348719901 1250 348718651 348718687
    0x405100c0c0803120a050c22060e0108010b0a0509030a0503040909120314071202091807030516020c0d08041d06040507020106120f03030e030301170105060a080a03110c1005 76
    0xe40c0030050f5060400c0007151000d8001d000c0c3c05451503544402c009040d51554074160340b115680108890812001821b22080242060142000007140e440922100d07501401c3e480e8100c5000d0381c0c4281c0b6000c00c49000711166042034030040e0b458025854001d010503070410103080504039401000540c2e844510b406032400c400c041d00c1c8006d05050000301911060406051540403081e810207070840e0b296180c040000340300f4241869404402e40d040c1680d440b200c500601e203d000107403000c02042d280d800c3c200c0078442000028100581c40078003000541d080151440c003200340300d46002c0303007020b8942280d0381044443e2422801d046007120100320322440c06000d413a4200d1101d000810415003040150800a85a80400313040c1d11010b0400704101480b0382e11203c4c0661a1000343c0b07440e561150642c01091301c101e001c0159541c00d080108060740f030008800c2085a036078500a16100c40b541e035003907600341000003810409000d8130a404031141c4520380502c40c50541030795626030300d200500225001f41 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 348721151 1250 348719901 348719909
    0x4090609050402031b031609050f0106020c060a05090d0f030e130b152d0d0f0219120905060c090a14150d0f1a100c030806060c030405100c0c 62
    0x207003400184805a1404141034440b40d907655018510901d007400480d2a000d04110b01c03221008544100140c403451551115014550703440701882c0c50b0741c1e82c0100b03c1ea0341101c100d207650700400410000b17041d1400b4200400102402401c02640a03160342c0310300640800e40d441c10b401064040040c004140b810408821240408607020445000b40030f000c030741c980304401c00f01140340a00140519813402d0110140a0402c0d4500f02440003040c1304d551458075410200d1010034450070011100307107034000e500903104940c0d900c0c0101901d03040062001c54175520048010110103580e10806000f10b80180700403445490051200d40d0381e079030403806018403081030f40e10035408440000581c1c0c81c9a0f9490800f82c07958070301c860a1071b4545c014403804000800707404d83d801240900d481112041d03404031102c031540110080364070082000d410340c0c06a4400002140060001c1c0030030b40044c0c0c0520b8408043c0000d07014550482e4101512040231444554a40c0502400b0400b00a0154100302240300284050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 348722401 1250 348721151 348721169
    0xf0b0415082403010e01020a020705011b12030c0e030a0305031e01030b040303050601090f030f020111030a02060106210504140d230a031b0c11010e030c040905120708040906 76
    0x346808008045481039024842c000c401c00359181ca0040d6400750000e42a0b0704504000b10b680741803c45010750b8446d51449042d0100d1260584039117044910740400d4410754002000d054000c60f8003d045004040029919040c054078801401c4c1c00d072400c021190690344640c4416641e8101244800600c1102035212004000b60500510000d80032501981c3c001d6454203002c6495107981c40140c0f6210748942001c00d54401e1034100109002c039042da007400c0b0b6030003030700d40058524511804617164440c15400300f016074800f80042081ca0712440301d12001c035991b6a0000c0a01304074040c1403058450644007178a2030001c18105000f12a0309001c1811051400e0501c000d1007203601442840c4c1070301c8145400305098000c0381c9103040030302a810004260380d1500d800310a01c071381e10202a0205200000c00d41d0a41d840700d124941e07550003180005903000d03004008245840002d01000043e1000090403525070050302c0d0140252224a000352805501c2805d1854940d410055040704403001070307001c25a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 348723651 1250 348722401 348722417
    0x203270a030210020904020903030a020d0807050304030c0b0414030a02030409140906010303030f062d05010306080a0807080909070f030b010e06030a0536070b030408040b130f0b0415 80
    0xb5000541500025450100541c0322040a0700040c001c2c0121a6255018003000172041102503001c00c131071010800a84441007540c494442c220f4041c00226401004615840344007008201c0e00d0f050380d54018415070030248503203150480117007550040300c005405a440810140038100311405120568a680300848900703141c0089551b075190018440039060559942200c0d00710101e58100c070707000c0e00c4484d5841c0d144024503840510b600b00f10681c4074140d02104880400c1c95807090003110210392001d402024529101e845022441d41f140108035025001005199800c0c1c80c1c60a4580c402c58075919040d4494a00f100083c040d02c202130103442c1017082c410500907042e034580050782c2d00301c0030107000000d0554841c003103400c010f81003c2074050300303400b4440340740012100c0200d0354801e2100d01e0f041e5995141e41d42c003002c80900041d40d0081c0300480c14407060140b11800f0f00500340002140840c102d106075a0f0b008012030045540082118600002d8144602842c6143c505a06889480c080d01c0d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 348724901 1250 348723651 348723653
    0x6060f0311040c1413030606032a03020a050618120609060108010e0d050d150b0d14010e0406150f03120e0609130e030904060e0403110d0e220203270a 66
    0x21000c83c3d0007030280c01013540451003410140980e42060050760340031400300001602c0b801d0902031803004100c60307400d40d0720340141d030900041001c0d10b2100b2640d0107824041290f04040c200140791700214803054001c1d50340c4510320f481e40d441e01c11a4a09000c0c100141265050084025043c650140c20800842c1c1c10300b040c00d95480000141d00d0398a100619040e42c0b03452402d40680d000c0d05030480701010141201c00c0100310100507a0040983c14841107041240f80b10010320010119824811492658480000600421340d1500300320002071110301503182498503000c2407100714099802c180d0f010b03414906104c103142e4200148841690f4120381c0513081129000025104200d10200d5803402500c0310600001d8400400c00d075001c2d031100420900440b40c40703114014a43d001180d050340020789601c10301e03010002c08241c04c8503040052355402e075648110b40c18000072031a019850004d40a0103041c540c42c0e9121440598050b81c1100180c002040100040a04421b01504aa000d507005201100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 348726151 1250 348724901 348724907
    0xa0c02090123121902131508010e1f021e071223090d0501060b0703031a04140a050c0d090b060108060609010207031b0f060906020d050403200d06060f0311040c 70
    0xd12001c0e81013076119501c000e18800300c1e04042c0110540c1144a040c00c003810401010201c1c8041556140d8000b00030341e510a2041e0755481d00081e8031103100007c2548008038140082e0014004404142c4016060500032204200ad603408068181e540d002c5001c0d00b80da040758041044070700c2c1c13140c2455107a010b4520910418091142c8d45c5250710447e00851140c040100c02c0d000f072001000c01003151501c1d48028200540644030b0b4010542088006046440c21840c1500c1400c402c1c414a40243d9081d990383e0390004002e11000d810152601404d124040418045015408001c3d2041c1c414000c58100b100c009418000d018051078400c080900c4071a229907070020b20a4216500480400340012440da990384401c8800d421190610061050203d6955005100582100c0040c3d08850480d803a8040456650150703010042801d15644400c0c040303983c1542c2d0390045007100500303610285149070b4900d0308446060b481b03450103000d558000c105100300580050010700c01902e003849245a004002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 348727401 1250 348726151 348726163
    0x60c03060103050a09140a020406081902130b030d050c0c01030515040f1d01050103031218060504111f090914040308090a0b040b06100c03020a06020a0c0209012312 72
    0x4541010b5480740010304c1c0ea901600070048143e04042046080c50080c1841901d9882c001001c1c2e0040d0304000000410260002d8136071200c2c1980410303a403034034409508129200e101c00506024094a42041e44540e036403e0091010801e013517250a9903070071040b0080303820440f4007a02c89051502d4981041030300b50070300c06190000c4070101c2d000900f1013403403041c0100901c0d420341000c424210380d821424512005620950589000f80c94840b0040c9021214009a40c41103e0343d4400c03140003803541300003404581082c4d821500c22411081e6080003400411254180e203049528440e5800386a0079189400140d441c019000710306050040b0340c50000310780c0351840c01902c0141082961400506103402c00c0c00031109450b402035180c00c2e14285414105000241601c0040c850541c0c02002e038403080c017480301c000f840da5041e0050500040c2580b903100094120a062605202c480c041c030800696a40050b40d01904a9289501004148040b0910511005c3e00360a001e18014040315440704400514 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 348728651 1250 348727401 348727411
    0xf06120312010b0c0304170105250504030206071109090a06150b04050f040b0d050102090102061320120109200105041d1302090720030a090b210709030308010503060c03 74
    0x3e565840741e620404515620403a03000010502d01504d442c0c00302c2c1d00640200d4010b494402031841007001c08208160000d03040c545413000b042c0208010001820302c1000b614000303020f11404d14200420302e0201c1c0182c1005c94101c603003a0041444181000000d201d91410408803d01c1d00082a003485c0240c03000d84182c0c0211031117103e40c0f120100c000e03a240e400c92041150302a005501c00c0d91646000d501075000100510701501800d0002483c84015406050b51181c100504100d00140c00f01194100780c01a41c6103504455103150240c031001c000d0040300413440c454a1282a42c2c018020007200001d0581c103840e0410404000820001c1ca2006d60b210345c903403240c07540340305940381c3e500c040c1c0001c0f6002100a4104c07428004100f1455042030700c1d0f5128014a403030f4029222240000c0544174800c4452200c04905d07084402c2c0b1801500f5070103000c90705840c110704030100c2e1701e0302c5074810b0501041392950001101a6001d204059006581c0340c0100410b4005016138100082d8002c068040241 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 348729901 1250 348728651 348728669
    0x2011a01121a04060605030103060e0606010c06050703060b031306060b0403020312221502060603010c0504090c0905060c0f0f030414040c0e090f0108120316180308030f0612031201 79
    0x1015a6100407501940d0b401d24001802041400e50351400603169400920094450030301d011207400c1078400204400b03224080c160f6450041c40d0030b45c0d8480d0b000b403d000d090001055550700d401b04242500800442c0503108480009584041e649031000640328150844035a00c141481308200603180010842c0280307410240d080c1e00d8000c1000d180801039200c281c0300034510101b003070001312485c0058210071742c00d04560179960302e0356036030341030500340c9001007035100019108100800c02804280d00c0010402c0d2280303040c40100c0d07528800140039403c40b417121411500705480411041104000383c8004804400286080520b42581d0310381c41503d582603280200d454a0000e4030480c4214000c51040380020315180b080e00304a642c9202100003402180981c0c803139050141094500340c4240c034401c07091814180551800110100d84d110180304035505014203060022001800c000e026510a891a0024503680d1611004001e8400c8840d0090714050300100031030101080811051815035040344 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 348731151 1250 348729901 348729911
    0x10603021507050f07030807060b0418141015090b030712030e040902120a03030507030e0616050c0607020a1a1e330915010207171c0f02011a0112 64
    0xc03c0c21414000e800481401c6801400d4001c001c100800d0043c04045002c0c40c0c041000b1840e10040c801150640c441c018000c0680340c404800040b800e00201103d03d88250699050348105c0c0f40c3c08060b0f071052918180c494819030300a10507045107208003542e100c070480003801a1403409442501d5601c001c0c1c000303820886e5104c20200c0a071500e4201c06a0340b0784c05028100a0585814119118000050200c00103800d110203d20032500c02e000300e445001000015006c95100c2d0940d10300848803c0859805001e0b090028581e12442032203014401c20a60700508141e42140c5002558468030314240c20043c1e8015003809440500c3c001360911446500b080c8030710a8546100d441031944280a16668101c80084080301d00c09250030300041d07820042c2c4005401d40c032a03008034505014040a03480c0168040181000f48500c5c010700904400c2c4c50000b41e5013141c00454818803007000984203103011449149124100550910681907a90740c032031014000103240200092106243c604080e43c5c0e9511a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 348732401 1250 348731151 348731153
    0x304031209060b0a0e0405060a0204060e0105090a0923060102011103161110141b07020910260609010c08060f1206180f03070503300103060f0608010603021507 70
    0x81c0e07200e00c1e40003c00a00201c040c558510011300c200c1c4013110111024042e07a00071071408141d9000362010350703045072100175906201c90011151908241c458940c00f108400d000102e404036489003480c0c1000d20a0683d00740d044a04001080e0780000d00420704580c075008500c2c18000d00c8609498205034020394440003808944001c43d94080c00c030300080c440c0d000300b86040190042130380c4000303062001600c041c1035507074958941039600354690110b00401c0c2010885200103180840c80158805411100416400d4032010107031007040ca00c005400740d80c017518182c41c2801030304000c0e6662140c0100000d12271142c09100050503410085c12043c0165007540c190492595006445514482104101c0c1d80920300080f0070903a15900841d61681d50213003095044413a14080b04903450365030440000d51412000303043c2200320304884903074503008200c001042d090b40c0941d400c0550080d801010082400004100c45c402194071030f501002c0346070b14007202000181c566801e600c240340e0f03001985a4448400d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 348733651 1250 348732401 348732413
    0x3070309020315060a0509060a06080916030c0608180a0605180a0b180f06070e0105190806010305150a030b0402030c0d120810080615030705210c04020304031209 71
    0x300c54001c1d81030140722118038010100089642c450724040f1180c2410035503070000e000d0006015a40582c00c00c008a0007440b140340520601500615a00100d46074080e00001d080484001900300302d0710155080e0082180580c4030080e035400c510440d090450040301c0c01c1800769180030150000304000e40310070000310300e2643c03080b0b451096201c500c1550026081403034014241d41d03088642040e08642e0400032002c82100103980058101000c000300b8590300c80c0801a02d01011840007581000010481c0c112403002e50811580502c3e810740310403102c0c0c10400005010740d04000c1101d050003600700380c181c55613a64030306000304590b00070083c14801d80f81c034000311b4140408280311640064401901034100042818000c01c2404c0603911a007490301da40e1a294082c150710b11895904c3e9101801203010100e6486449511080007001c680c00f966171600452402007940d078401c2c20500b403024501a0f4400140000e600702c41e800c440440c03446c58950b4010b4140700a00c114803070744943d201c110600f080a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 348734901 1250 348733651 348733661
    0x90b131104090f020301030c081f0e0a1a06010f030c0f050327150a0504120e0112060612180308040b04060b04050420031f020705011b030b10170c030703 67
    0x2032400c1c401e10540103003d61000c0a98000e200840f09000d0501c1d0004859402103a1030310915400d10318040811140b600c000060013422011890034001e40803000d00090b03980d1200224503460b00b0720900103182100005d85502210f24650080c503080c80300520780540d001c40c039002055403d007061030302c0761681c500c0c44104080050702000d0402940a4540300242c0002d04204115040b680c43d03a03040d83c8031f401c000241c40c4155401054000300501d51515075000e28800c407414001031504208808040c0d40b01070643c0e96540c40b01c2c010a605100c4810300c01480d000d074403540c3d9000f07522560036511541d80103107000d0b401017010300b43c0c1610001040400c08150008818008024030601c201d04250414101049015013560003084c29210121210b0030041031200e900c0c800b003145240c03282c1c00d0b6030034007000c3d40c0031060451f0796541c0c81c8081c6202140126036403c280189a90000b4105104000e002c4005444034021080c015040355030100740c15005032296210841b401c410f5200d845480d416000f0b84 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 348736151 1250 348734901 348734909
    0x110703050f010615050711010302180a140a060203040e010611031209060105130c0c020f0d0c030c0f0f1203120b03030307080f10050306130c170f07090b131104 70
    0x8000c403540181c03800c00542182050725500080210814014841035400d8400c00000505c290450b5429000b03541c00b9a0290000e106698a40c800e0ba00c0c100001800c50f04e155003164401c00c0b040309904070301c0d00302a48007078041c1c500750008514082c184000c0780b184100501c12034003040640180898a03900601c01d48001101c000c040c11124209074840b81c0e110a002d000b403034014080403800d20740301e42941c0140d15000c8002c4c0ca480c48816400d40038406a8080b80d0b92854024801c20000000144107070902c900541c010182510b4050600c00442e0019442d83c3c400489020f07002002d21030302c440c030b561a41c086903042c10403120314107034004044068204200c4943c0e05000210421181d5504112103521444071020890016600c044d4004c41c019090300913a82c140e8000300010300200003440203240c0c0c40f4001c4082e40d0b07006643d000d1982c0082520300c20b1400507080400201c0841c00700f04408006026212010312072a00c401c40032400b1000e102d84c81924245d181e000300840c000755802101c02074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 348737401 1250 348736151 348736153
    0x12050f0301030b06030f07033c0605040303152403050708070806010c120f030b1903030c050f120a1e0c03050a1e0f0905060a080c030c040b210f041211070305 69
    0x100743e0740d003043d2802c24080c6c14035101c0c180300c0d200c07900c41070301070a0030780800c01c146089c5458075102075494000081030010012410f03d0380e03505011120421803040f00004242265001980c00801d0350800c0410a0340c00f5000b00341410841884400307034205988650040ca24a8009120b42d1241d0040b07500c1401500f020b490b807180a1568a0000d40c4808010034840c4d058070103000301422030003403060030002c0f079040c1c00d1081c0115209000003803107003030440034803130141c022103580c042c441366178a00f0404041611045001c0001d201c00081c2c0d0094801c0105800681a4101003900c104014004603031143e001020824001a03c41681d400780d1000340c404039003040010421010510301904c038004441000c408114800710005041c030300201143c0d030140541d036030b0140c9074943d0119010303030341c002401c690f495440501012510004440c05000c44401c038003000041051000400101894090b0031249140c40300000c020110742d40348800954a4200d24040c03601c5200040e4860070710090307030001865 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 348738651 1250 348737401 348737413
    0x30a3c0309080d0b01020d020a050303010506070f1e020a091a060a1b0b0603010e01020c1002070f050a08040306050c09090403120e0601080d02010e16060e01120e010912050f0301030b06030f 83
    0x4003035400c3c1d00c8500000000c0e000c885200c1880c1000341d89c1c54002e50381c000e1840e4804c000500007030526074007500c801c0d482088445410403596481004401d404030300d0301e07145050740903064154907202e83d9130002000f00200c02c01440c0303c804600344e8840022488035008010001300b0300070091103684041c0c000c03004441100084001443c203122042015100c4030b10075070821650624452041c8221556031803508000c0150004042402c03001c1e400c45031042c2c1d01c0c11899020400421001d200307034031513035102d190410303034580c198580304044030030140c02209a0030050003a03024940381c4000540c1c00a4060918201403090070340020080c01304645040c20f10f02405c0c00019035141d00240009055403240c009000e040350044000f6990311400f05a0820048442e10030400070b4010486100e10f21018507240c480c9008010464003603906192140807540e64440841041c270060768142884000b0500e080f42c5048050300140a06000602000e000103410002041c05c40d0f604000703108808043c201603c0c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 348739901 1250 348738651 348738667
    0x60905010902040e070620031b0705030d0302030601170c0f070809030712080706051906060e010807020115260f06040507050607021305090a080408030a3c030908 71
    0x400381c54415812070040d802d00c0c614500c60714011030b48806485c404d40ea80341c58034542040e90f012240007807a0702840340c081000741c2c2c1d071005d0440120b64603402d6001300500d1811315100505141c554021001c07002c0520520511020343c0e07000211100080b2031559400b16912900b4a50045200b014454140c403c0b0011b500003c1101c0c2001404455004400391000280c0c2d40b00c013609040d0a81c440140711410070051440010056880150001100400803030aa03601844040c00c4401542103080840c02c0e40e44200003540e03220070303c180d014000344001d0010410840490a08442e01d0003000041380e0308882c0358503400039100503243c241030f115080f200340812000b0303199190a8141c5054070309000e104808915400c01c07804460090703078017030903940d8901c811604000043c000039180d40100e0088013000f10100f03e40030003400141443c035000d141e81c2c0d1181a0040d0039441420b174400304485007150a01d5080d0700d08402e138408481c0041c43c3c0e003020000c03003008030000c2006450052521b030b00410350007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 348741007 1106 348739901 348739903
    0x70302011107050324071806031d03040f050901080604020631180b03060c0f25050106030204060b03190c0e09010b03090115030803070e0d060905 64
    0x2d00100d8507840003908121440d90b00e1400340d005910043c06031180701c59641c0d0004001d04141040b1035242c0080d07440c1d0710701c5100b0f9005040e52428030f50140080841202100c24500080c0d0743c0c0c135516010089a01e003c58010a801104240d001141401e40050034500454000f403001d810b141c400d0400510910024a084e00d9518000306100003c3c0c0340e00100360041d003c8041215140f08004040e0800c95100d11071483c4643d2102d41446031102454003140c03440440704124a030341d80381020701003031903030f12925021400c0e840030910201401810351010003940d03c00c95003800392a135540455201c6020035940802e4101d07141e0b401101d0410250700c0051003505908246022400200008106a0b001d900544e0000707000010040c1c04039080c818103020254904201c40c20a00395214002c55000c0209404d0600c5103c4641d02c4007652440328032a40184d01a034148066945d5250a07 = true := by decide +kernel

theorem cover : BRFrame.Cov 348561151 348741007 := by
  have h0 := BRFrame.cov_init 348561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 348561151 ≤ n) (h2 : n < 348741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
