-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1773
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:37:35.015914+00:00
-- url     : https://prove2.me/submissions/778ffb72-6c3c-4acf-8b35-09ea1b046e98

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 318705035 ≤ n < 318884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 318706285 1250 318705035 318705047
    0xa0e180a0b0d080d0b0607021003021c090510240f05010207062a0525030b06030a021e06250302010c081b07020105040e0711011a06091c02060d0c 64
    0xc0c01c01d00a07224203000600040e0a00251940003580090200c0c50411140108a80c0d008503032020b5800a00100705001c000e8141c2d008200000c038044a5601c108817a114141c1a1599924010010f61000040100d4810641d0200c2c0090044c2041d50102410075401400c6034455034009181031403840780304010310f60b01000840c2c0240201e00f8210510752000c84a013044904d10080d00f00c0c8400d003102c07a201003140601005000300a00000c4400400c0e164142d8908442c6502040781e084100300d022904510700015030645040d8001c088054460b01c030b5034544c3c0e0b64841e0550302d40d0000410f202807100c0d407449030920102503004201005a04c0000d0038000d00755181c1006c510203002d444d009020254a04c0000b03200050203100c007060340e40030307030b0b01c0101c40c1d61085900a5120040f09002d100010f58014004421900b00c0070080c0824180140203d00c030046543c4150781c049420080007000f4200a00408242c4034589010341092480350040348850f440755000440f21031307840105042d901e8001e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 318707535 1250 318706285 318706301
    0xf0a05061201080d020c03100504031103040308040503010c0e09071d040603081e0307091509030804080a0510060506070312020705060c070b0108120304060509010b13060504050c09060f0a0e180a 85
    0x11009046c001d446801080e00c4510b00800700f0300043d20384000805042c041d1490b1030885000f001184e540701d5403070401c484190040d004041c07080d401c003035960184903c211440d80d40034030002c0c580510740d107030000140c0d80c000c0038880090f417401c0d5180481190303079102e20036100103601030802207540d6460550801d2140b030070003078035181602d01401404400c55001140d4010b03500e100682049112a044c0240da880f0503590000f4184000018003080c81e02000c9030100d08107200740c0480716102c10060b04a81a10a030703000f1150024414004c10b0007080c40782c01032214140300441c0040c600b1185072142818030070101c0d80790300e07250000074090b0104010400003030300400b828405048461119941d19040b031001400140c01540c5070800f0411080c000c1d03105010402000300000390101b07885004030017078070151180c0740c8118980320008980b00142c90841d0200790008024504e03103e8130380e00721420b54002d010a5801c01502c0f80c03501100780c4841c1c40c407d0785000809204c560714540244480d054a11035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 318708785 1250 318707535 318707537
    0x2040e010c1b2d060203040f030e04060b0f1c0615120501050f01050f2b0f020f0d020a0203070b0403050306090c0a020a1202010b060301030f060506030604030e0f0a05061201080d 78
    0xb02141d00040f0301070f1541d100d0003650078040390720544a4032042076149868400003826061001050104200407088401d500718400d4488140c003003a6101004101c403064450304554540400c0504448800d04000304124409144211f043c0c030040c04604080304d640382c101d503030194042ea0145540700d400a504100a2998440c18082581000c020468140c0311041711414054041018000007a440d0242d5070302e00560f40aca2180c0c241c20014a0406410490080c420a8541910304e14503840364000c4480c280e05d280030052030f00d01402c04250003075005110a40440c04140500e000003400c41c00500d0045000c2d5403190303282d0404008212544e030b00a481d456070200100b22600280b41c001c01e4a0b00029000b140820300255854810385c054155001e5282d8810400000481040441e002540200d4050380080210303075500b10516560310750585028002c280301c1c2400c1034103841c00542c22005204040c00d1a8507955072880401c285400c0300d405000300c004060014403402c142003081c2d5801203c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 318710035 1250 318708785 318708827
    0x20d05091c030c1403071706011b080304030512070e0406060509030a0201120209030f0615010801050319030e0604090c031a18150d0c0f1a0d0c090302040e010c 70
    0x509080580c00100e41154501410340b40e9200c203224600900b40091045540c280c10340d030b00d1400c0322004241d51107c03860846003030285000f1400075449802d0400340d032410368030901c006010a441e41c0c0e03060342005100300c0401804000455042ca0441e010f11301486194440d8500c44c00301d41d04100545620b40c100204000060015440594001591100c400d4083c07c01800e40c100d240c5007007020744600c001c0c698062084000c7c3c41080300d0300086031881150b20721646011400c4060045848002c20b00c250303585075000d4400a11024000c2100c4604503120707040640001803150041ba2003034000b54001006c0396602c1c00e034264910b0305401514402c903402c0480200c00241d003000a5100712103103240d00c0d071101c1182c0c0041c0c06180c0300d001148142200400e501d9881200e49000310302c8180900807051981507603000043d900d6004000003102010417040c440c2011000011302d001001421131040400c01da6020003c0903031140d100e45416088001c00220703030441101c40150004070080c6400700b12100f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 318711285 1250 318710035 318710053
    0xa0b0c1201050d060e06010605210408030105100201090204140105030d030c141305040f1d0d020a1e1407260c09270303010303030e0f0d0311040810020d0509 69
    0xd6000c40141916011030391010390b0b8143e41040001401c8003010b40a05209010010602d03030b0708080a040040704802011409480021440404407810f590042c41c080003800103000e146020007186e020001c07944000201038010f44c0000e001e4800c445181205084000300500c843d050910144001c5640c1c0d0405022040d403101d00200b0194285002e0541000085484413205c4d40d00c841072802880c2c020f0082c00b000701d840600e68000c01555040d0103104491441084001d2000306038806103e060350080c100a5907140c403981c031010420040d1007510410181c0c00400104100800240b11710782400820f050383c00c00b04d0440d81100b108402c44550300364515a40c01484002814103903515003500d80701c0d415100d00d8501e011504d4001c103d1036003008000407038070b094000040914100c0c1e00039034042c4004580c01d0b89041c1c407035610f55100540c0340c000016068401c0d01940000000f040100d07a1145000d65841e10035050403500244010f5058001172013490035103007409800d4009003540040c2440300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 318712535 1250 318711285 318711307
    0xa030b1020030c010e06060418110d1e0b060103050108161e081c1806050d0c0203040b070303020403060b090603060103030320070302151012030c020415080a0b0c 71
    0x116400107a0541901c20300c050721010409209503112888500300911031032540c184560703202d5904403a010702032440e05034000b54400c0d0038a050240395802031880e0010358110030034084010307180b00040d540d01c04034411107a00d0300b20420f200c20405000e0741d0b02602c9410400c000505640c0181c1c403c0b10554800e01c0001c40d40b1800174110070860302c5090701e01d071801000d40004881e440d039651101500e03018180c2d0381060111207083c080d03d560030980c1c80b03103012031a0049481d0030038410b003d5a00059030910010015103a41c0c1c1c44000a6400e41c0122400c06540e08121820b03070784460703001c5001a030082070801c00c000a0380954449400e003121494054502000030959039a0144009001c041c2c0b00c0c0031401480d549501120045030380c4202c55692101c0a06002e90742e40901003a9001c061801c10001c1c500d08419490142a91442d0140d0010001c00f40c404131032029180e08103990041d95041d4441c944110b09100c40000e02440c806021050110f05090310f90803c02440411690802c209038a041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 318713785 1250 318712535 318712547
    0x1170c060313170c01061a0f0a09080601120611120609040c050901090e1c020304050121060f0512060f0f150d081e211b0a050a030b10 59
    0x112809a035240e4907580c41c580d00000d10103040001030480001c045000d0042816200100341d280090300090140e242d40d90035081d0038281010000d108984241310b240c00c122840002041204541c7c0b4241c500300d42c40351440c80c14100c00b030380828020105041c03003c2c100030b01401062081e01e60744c0e00c258180603862980c806c1c2a40b0040000d07100f5000c0000180810180320307510f4014000c0034205100a40e1070345601d00081550b411140e0191160b584421030380c0b040d00c00110034400c600d502450400d80b030310b00191a82d10704040001700003010f05103031000400c0316100b510002d2281c582ca2429240c680801e00c0000800d04980310f41a41000007081b60f030310101020950842c9044801301441d0781c1340003944041d4003203040a02e41c095000c00d80c2c0350034418508007520048481002da8958000c03603100705175803031042c4040610a5807240e048500c003003401c2c1100c6544840e00c0c402d408001259076041403900c1e840030000201292003c514203800f0340e80b5100703a1040074016584400982e510a07800707086 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 318715035 1250 318713785 318713803
    0x30301050d0206070f06050703090c050906130f0b0301021303110a06170415051014010203120c0d020408070b070b01060e09180c031504110a06080708100b0703030906050117 76
    0x1412001407118100170ba0004644221034020204103c42e0600b200010b0242c003000109480a81441201040e6460003110040c05858014000c40640300030940d4a4007600000403010300701542d41c200200c0300c1c0c40070300080a07815000441c100c0900e06600e400e00c55a80300034861070041d114400e050044580201c034510b1083c40b1b25160300e020f5910343c600540701c0e0f1040c640304080d403400e141c1403001d601760303203c95103080c0c031424018032078008840c1004a036603005a0890010100f080310201d19050f01400080842c18844400503140c29240c4460070b03d00181544007034103c002c0001d0007014403000e014114013508481c41e20170301c140c418070700003540d0320405404c40714030b445040740758041c0765802c004950790311102500b0390350303200e0b2003900012524500f1a015140c254008850740d14a02d00800100305441072a03c0e044419114802c0881d00c04900074031904458a0003040411640c095602815009100303507004140100e60b440c000064450686c42a0201229203000007407503100402d849034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 318716285 1250 318715035 318715039
    0xb03010f140307030f0f050f0d0f03020912060f040b0a02090a05010e030c13020403050106120309150521180c0603010501030b0406030b0a05061f02070e040203031306051b030301050d02 81
    0xe005180350000a00f80005030340001d15448a142000c0c04010a26036461a103038040d0054403d2103510745401911056084084000240040c0c42c40c01940c1c0030391301404030848040d0000038081c840740c4101d81b0304142521000e24481d4030a003000100200044065808802c44c0b5041d07041601c08030102d09540242d00490b41408286028040b01d030301d0030041c5904c0800010003941400d600c000d5103800075409408251255400e02901060012491320010b800540c90b075202e009070307844e000702842d0049060140c2c0b02041402c1100134402d8944d642d05056500c903130400d00b117882c18840d07101c0800c000400340e0b403180c50f080030700501e0b0f030f6039980002d40e41151802c3c2004152400f401000070010b0500b034000a0002984c64107003e10140e0396400548955410358460600c0b41204c00101d00000e0811840001a0300040b02480081c840180702e50b0000d201038112030a01c401c001841c00402c2e81d039013000000070030100d200000d81c4149c05020034080c2c01d050196143d94108404180385005031900a4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 318717535 1250 318716285 318716309
    0x605060a030e0f0a3c0605060a090c0f110d0f05030a020412050c01020d080907180b03010218011209030512180f030d0b3c0406031a010b03010f 63
    0x19420606001011000d10303070000b0796140805620340704040702c0b508042020b2000c840c50b800c101088018054080b40f21808003c481d0066050795050047c20006103c2074014040c00f600181031b1000d8020003101d42d400c0d88030010032125425004121031340c1d007065590660700440756041200e40000e030700d040700c4805281c005e030303603980305005407000c0d2155a0101c151a555400c041d420b00c90082003d02401109034295a188801140200c0e201c0100307562202e01604541410440040740d4800002001c42000010030100c541100003802c90f08006581c44468085000c6d040d40f943e03020050b41e00c1503014a82c208989122030300c00030100c2c083c42c00030720044103032080400c448190307040c1c84c074038000705220071208040e03114010f1540b00c0d00001e07641c40c6000e00b007880e00086442d00c030b8518002c0c3c095001102032581c0454484004e00d004a2240b034442641c02e080314040c944540c010040070314080d210020701540da021404002d007405910110540300c042c00140301d00c20144800c00c0444241101c50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 318718785 1250 318717535 318717551
    0x103030818070b0a021005010e040201020715020c04141b03070e1e0a03050f0c010519030c030e0304080c030c0a050d02010809160906381c022802010605060a03 70
    0x810b107088195006002006030110b880300c038165001402c00e10498a0a000380720b103983c3d40143c0100020281ca0003070250b04240000c0c03041b0700c00c1e60400a00600c0324030444900003e0180410111411050110a0050fa9078104140311030139108013401e00181c40100ca14502e441407005000d034845030600c902c5100088055010061024611813040d10014150301d480d0795030707190540e42d801665442c4452401801000c030041d40c0070f04150340c40769290680d00340240c404450110700030b0800c00c0c10401450780e541a83c0e03020703c0b020030160024002c0c200c024811298020b003054900500417001f103200d05030812081c09180c071603400c0b0b001003640c28241203030030b900d85046841c00c08480d00c80e9540c0d6945442c00000340301049070892022121f4009900b01c4910035201d0f41002d40c541f11080030741c01c134054081d0074003441e1400b00412201030101e40f2060710f038030402045016a400441c010340011581c1148071040950301e00c87c03144500590008020301842d000206905002d0039040c0d8090503a0380e184 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 318720035 1250 318718785 318718831
    0xd1202070503071416120b07050901180905072007090b0619020a03081f06051e0c010209150715020901050d1d2404060e0a05030a030204150801030308 66
    0x1500c140590000c82004c9040000c103c81d540e842060700040c555007128000021404010048a58032603003040007a0311554070b601094070f0301e901c0301050380d0410510740a081c0c00300002e041024050b04d01304401061034141040002c0c407500700c000c00e035101c0704240b2072001001c01c0c000911004940c03200c0004511040714900103803c0d801890b08041d0ba43c0d0800018040b4182d001c240d41c2442d0303119171200451505d6504103501c160401181c45804410f0852042c0007441c002c1e40030b4521906820980b90f10902c800d5080b441039004441e8102a0743c2d00800c10303020030b103480015100300050b81d0015905003a01500c400d40d1000800c0c90f0000c1c02070b03000610a0840e44901304540c4d1585c1480c0341441560101140c200001888403078040d80d134010310000c04007410401c41006809030703421602c2c8029032900d40342e200081101040300217443c0304090220000a4052028082c00500b90f10010703100e0303207490544466079500d004c0308070400c07424500610000c0c0c0c004040da034105102c070120a0b4011030300b02d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 318721285 1250 318720035 318720037
    0xa08032806030303111356070b06040504080c010207050304090b030102090901090507030621030e0a0f0b0c0a0b0106090f12021c0501060504020f22060c0305130905070c02040c020d1202070503 84
    0x1540f15880741a0b01001c549110030301b59910031a0350039401a9a100341f00d008040900c1c01290b030000c2c214190680898103515103038010030303001401552001d151400080300142268010681180d80e0b4201090412448485105030901d840701070703009600d0b10030000000384000c04140504500365646001007040c640c829070000c00940745007644600340d016a004842c0b8044003940d01240010a0f005c003811041c01c181c0c00b080e048440382e00c0c103102180e00300b01e150300d003c3e0840f103001e9900f840ac40c50f00001281c694401d5500030030b982e4480d500c0c21802c211030600059095001900341b100e40d2038030800141c68860210310141007c4074074079405103161600038050902a4081a030081c0042140003040e80014001d01150441051b0340090005c0c01c0907110040c82c9520601000c0399a02a000000c02e020b18010300c00140d0100350107810a0721100003200321101600d1080014401c903a0070011414140320b1030b0300d007a6450000b00b0021403000c000800881d5098070084680d6000f107525010050100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 318722535 1250 318721285 318721349
    0xd08010323070b03040b06180105040f02160b0105100504080c06070f020901230a1202090c0d0e0a0c0617061c0203070b030a0c0c050a080328060303031113 68
    0x20041c2c07003030155203001210858205840684116010718085205440c1088c0121440302c0b4806c0307101c0c02a03280104000003061076a445c4190390b1b800b0840c4c1100001c94507002c1383e40b1481800c11102a50401d01407101c80b02407803c2110134030030b00300300c18841ca0034000b4000f1050a0700b240e546550352a0303883e0000303090481703810003904081c80340008a4483d80c5c40c094461620415020f00e047c4403500c00800080c40708078402d0304481b00048808c1701c0035041c801c0c1101c1c0c0c003507043da801034649110540c01804803413030600101d00c6504002048401c01c0780c1c02c0c5a810040c0708900e4400201d4182c020a0398003141d01500c0e081c46041c038680408191b5628907088408030360028103a0b5899907a6a107075146580c01120700315107481c034000b901010380f13000d100505e11b0300381c000001b0503494080f41c2d600b540d2984084d10050503040641e50b10a840007050282e1204c0c038010f41c1c00459503034514503001c0c0030342c1c102d9858a00a0072041c41441c80464080340900202c0780155568000c1195980300703c104041c0807 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 318723785 1250 318722535 318722603
    0x40b06091201050106021c0c08030c0702030d0201020703080a0c080708040c1a180a060f080c070204060b0c0d1b060504110604120b0a02040308030402240d090c080d080103 75
    0xc8506600706100650009040310f4040d02943c040003501e851038030028940f64400004140c201410b170300415029005580d02c500c440040902d00340041e0000b91400159518140042c3c1d0002419410198032081c01504032040007000e00c4805183d260240600e50010080410001208001028051304007048001485c0c00846030a800c442480d1004107030b4498581c2c40c2d013001914106811314106100c0c0001100c2c059541c5036020f0f68540c00445400740c0140074000c000209001c40c1000da5503d1043c2c0740141410701c0595a1110200c0201d402c00483c20880300a00060b94000d4100c021180b44445040703920203400107446c0d070f507460f08120301e89100d14644e8018102040c00b027040d0641c214100c10b049d009072b2684440740e40310150101684900e00009015410500115006080c41d907401e00004031095074150708003040880d90b03601c540014803480c2d0002d49500c0035405002c4403010503030181c40b41401620200d5010300d0040c00d8410184002000740804c03600d03294401180d40a414004c0c40d007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 318725035 1250 318723785 318723799
    0x6031618080c0a0f06020c130905030d091a01060813080c0a030e011418060913090606050a0608060907050c070333090224040e0a0f05130809040b0609 66
    0x8407031006540e69000079580b4016450150040b44592200c80711800311100d036801410081881d40a03c00740d82902e4490341c0b00c268881ca200390000350144060304442086d008002120300060030007416140c2280388011500320f035040144070103a4041e41680e48022941c055442221701031610b08280c1c400e8801201d500e000710090101015031098100d8008002640d551000d00a42c507000f01c4507109050000140607500641421141001c030040c14410310700901d1441c0c562400000e08041e106a050115410750365000140b00502d0030343ca007940a031500d403038a01c682d480d00c8804100c00f990045d04034001e1000228508201c0310003004024013442e48400c8016450014803040325003c6101d210000603060b00030702c0c1c2c640052091150030441c0c0d8004080c890100784c400301c0c0c2d54880070004110390b0001c41c200008102583c03102081da001d001c1c03001c0001548500c5446040c11179102400c0d004840d01c1d241d0080005c00c501c43c040e50842c41c801c171400102c030036800380014040e1042c0c951054111003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 318726285 1250 318725035 318725039
    0x1305130b0f040b25080c070b09010e010c0309020d0611070213050702072c04030908010c0509040c050307122d0b100206010501050a030203090703020d051b0f06031618 73
    0x40d50500d26000b18410800d00356540c0350100b2030707206401040c140440c2c100d04021046841482900f12a810090030807029152400a407940750030305204440c028416074481d0070f5a0a888002d12851000f4100c40c03808000082580d40001e800310080e10004e461107403154130752100f8a01100c22900250b038000c250706940b130013041c07030400a400110380050248c019031000080320a4118441c090000700d03810b940c5140080042d01c685e960740003a0094007044950607000c2803402d02441030410040307458407403a841e003da0608002c00e0703031070165440040010070b000b4082440d40202c10300c00008205440411030008001c0c10018040c980100810000311822919004080c2e036481446840301c2550038004204013004240c0c3d0341c42c4207100e9203000803810020650301e40e20035070145401041c80d00513a20001e17600d4000804101c8004400e6230242c02c42c1800e454900c034012001002c0c0f201c1a500e06401118420000395140402402d0b980d528841c895460000ca07c235500007802e1030144207000340c5540d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 318727535 1250 318726285 318726301
    0x515060f0d1517030301030812070e280b04060219081207030f1505011407030306050d050708071707030b0423030406030b120606010c150603080a120b1305130b 70
    0x12010700c54054542041c0d0601d103c40d07407011048a060760341003a803a03454a8540090091041c0c4c005088004101600020070390035a100400a40d0000d5401c11100c03c903c02191810701411241d806204103080c1000304002041e004625031003080350140a6141c00a181c2c01c00702114450103003608007000e0100200514950194004000a9080301003048400c081c4c4640124605a9000312804600d4403100883e55140f20001011854481e1401150f0b0030b60b500080f400e40300424000711902d0b044590140303c611800c0000d01c0c014071451449146031341c04c0601040e00c40f01e1901000e00303070f06094400102032041800246203c01c4403540312214039101c901060b80c40360094000c840000307060480a81080c40d25000c5418035041900241666407540070064800106c3e8190480c1e15200c491040c05004845100350070040d4080c0000ca5034810510200400e25040000044030703291607c1b9090782161075520004911040c480c100240544504400201c2c0c02c4150000429034089a4204400c0b4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 318728785 1250 318727535 318727571
    0x714120f160303091203022e020403050c0108070206010f1802041824030309150e100c060b0d0b04110f060412050c180a0b010e0d0303140702010515060f0d 68
    0x168084d540f060140ca8840c140403121740302030240900141d02c0a601325440700a49034101e004031030034040142c020510315440c1d400345d030402d90040d03800c0e4116a11400155811112195100708184050020b42d0b041c441c003004c545451b4003641203510701900d84008e580c1d0041d411030b030140072a481d0072801c644012101101406410a10b107c0050280c4203c0780c0d0b18041010041c2542d6050301c03184405400d00d41c440950038078200001c030070840c0a41d00207036182c4840c0b03625036100e402d5503603802c48000141000f009440e03441070030600a00701603a10101242e41440b8071508141d0041205500e0700e4503000160f1121180c04407180e0041340050002100b41007944141c502510900a5400c60754901042000f03014948071408902c0e0741000004a05490300c2d072040380704140504040781c0507800d11012525200700740c44110f0109a440c0194001503481298940d80f11100c0c0c0f000340550b00c0e00200e4100f03900c1c2081980740c05100c02069205010300800103641c400c9081080811200121f801c1407410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 318730035 1250 318728785 318728789
    0x102120c0309010c090b09060f0d0c0908070501020d0806240406090911030c0403030f0207030b04060e060f06010905011b080d1401080a0807020d2915030714120f16 72
    0x2c9619100310008001e01526003c400c07202d280318101e00b016090024403031b16030701051b018480c4c0c081c00c104524802c0f41500c01c0703041c10051640d80d01080341c01c0250035403400b4900d40085045d940301d00083e00706290300c6190303e68040c00a492007103220620440011000a80d9440625400c50200e4041115607000c03807010304490428005011146440719510f009200aa4880045d084e0400041c00070034003612900d0b0318200303544100c2c0e55181c2e4070303192903440c030f50141d60840e4050f4443c0103120b00d0351010030010f40c200521244140c0c450902c01c1c0080d00c08200b03440340e28140706443c4c6035241401c8280000c0d90740ea0ba000004c0a0381c540c0b80109810040c05441000040e004107080041002140083d02d40d0010740e00480d0549080455020030218203c44c048c00c5488a4072007000c10a641003000003035003444e0600c01e881080f4200749402041403038a1100e01741c0240d008400400c9016429001c81e0301d40c800950f0144204c00c06072030707040d041010b1036008214a10884038014580300c203c90126003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 318731285 1250 318730035 318730051
    0x30a230c0f1008040503131d010b0a09030b0a0204050411030106080711070e06040e0a030f120b0d020409020d08071109070906122a02031c09080414030102120c03 71
    0x19000304524100308654030011511a0002101e159a1103454041c285090300079000e4001c40b414a40c0c4000040d14066485e00314449003500480700031200401807661a0240c100701406500f800c00d0781c00c0c000d003c0602803001811580c4003a02040903228107504942c09400054002d11030728044128429081e4000e10170708000071003000004282c20301c2060251003c22404000e040000d1070501c04c15104a009810558003550311581110540300400c40403940701e2203901c0d04c412948041001600c4003410380c1000d48200d00b03144003100140d03203804109d03145550484000a042a460021420707600915000030221000002d2180c103201c4151500d5083c075008903442d0510343d40e600801c4840b000c803485200c010030340e0613100c102c0c1d415094000300f4500c43d103e4426a0030341e07400325025148140b44489100035801c00036a414600d200204c80300c0c0e4141d02440103100501c141d41d5a108a4407031841a40d44031000305c92506100d550030b40445400e01d250700d40d1070007142810f0380703a807946034801d80340c1007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 318732535 1250 318731285 318731293
    0x41e1103010807080303010501050f07110a0e09010c020106081e01060b03011d010501020d09090c210608060a02040f030f17031006020c010215010b070212030301090903020d020606030a060b030a23 86
    0x10300f00e400000300c6c0d060b00d0040c0d5881e42130640d03091030100f1079040f0030822109040200451303180340d207400301c58000400031900e6889050030140c800300d00715070740c105142003164180b44007403250541c0041e64103010150010000d140d82a4a051a40180900d07000000c0018001000180400002c0d90f070460702c002005100c0d01c40c0c0d0780e41c001aa80d91903210401008120340b5401000888903991041c003c1e9145810158105040b0a00c035108071520440308034105075984000b482191020045580d102510300130440c030b8203040910300c00c6164604c0c8401850380d1080804601003020360032450040f42440000143c0701d007415007104805000a00036800144100f41d4145101c0d880010140c840c07501640c01c0d52556420214071610581c4221810398201c00504014044548100021070080003203a0002560303030b65502d402030911000c0d003007171b40c21980010140011a0350203d00480d420b80d00210004512000c14082070600c484d0003800740008004a0700030000340ea080c0390b84100d08540030f0640b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 318733785 1250 318732535 318732539
    0x10f02030307080c030a02221a073306031a13110411250c05060f3a2c030910020715050a0305010e0114041e1103010807 53
    0x1240d590100700d0b503000005070114041070306040020300464222540b580050b00d008406005514035640d0100d86166100e015401000018103040304078038410182c076040b51078211a51a8109405145082c0448030080c0d1915011500440407000405546000003409a07035502d01305032a071044100094405004000300140b4455030b02402120002d03071000c0c0c4a00c903c4844d02c103100040070456400140b943c8208522421403d070365000c000511440740d40001094164540814807040740c1d806580501003e00c540740540483d04240d404944a11066800c0591024907c1d8007080d0001100809411a4603030f83c203600306581c020700c1c4c0006044006238030002540c9020600f10100e14110780303607608180012116841c0c210f10900c1d10082520450b8038454683c49004100b12001e015500490400074400f0b41441d0180552401451502e0307070010346600d88151021104100010248940da42c1c500d80920800c840307001b05050f400030007040112510b07525564200364001c0c05129031078840c180b80 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 318735035 1250 318733785 318733787
    0x50d0302040605070b06030c0d050c0a060507030203042106021c050603030a020307061d0610030b070f0f0f02011e0209010212031006230a051206030703050309060a0912050705010f 79
    0x2100d088a03810364a032032034000540c55000e0f03005d2002d0301c4e0f00c1d0b250003500760100c12a640c1d0030a0107031040c0128090040507500400f040f803104080d03400401445001e0019001080d000300940c0c0c11030ba81d051b03a454680074096500800e184000c03200621039880800d1341404043c0000031402001c1042c00200301940f120010542e89001d1200e655006a00401500c4001400b60b0000d03034641441003409440d100440d2805800c0510845c0c49600d0691000c0d41001401303070f04070103250005200e04000f01030110a80300280080303071740300010041c40403050120b03190503c01d6200b0070000d003074100200c108410303001012010351703c842030250061207003003041c060380c40c0f1107011207002d9403103010f03102c04207032400f00d041d5090040c00c21800030706040351400c007640b82400001800d4400450b40d445548160301c04105410f00f1014007511b001394410720b01400001c600000301d480c501003c450036501c03040117203011640c036103030360700450990481c60f08020300300680001d40d4419101c3c01d1303e40e5800b400c41100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 318736285 1250 318735035 318735037
    0x3051f140108071a0403120c0530160203060f101a03060409050717010209120307030e0136081507080601140c03070c050316050f0405070e0901080109050d0302 70
    0x890420f80c010510030400200902e9415400c80c0e0300303940e181d00f801d550f511140600340c207090f0f85e48041000401d281e001c116040c0b140c00a2031080b42a500c0481c100401c082e1440000e91200304800d01001070010700181c003849001340125030040481b0b54501d000c00d00140ca88030706581455040700100d10104440601c21010b0544440c03482c525400c5036140c0b0208005890508030641e080c1c000e01c4000308032503800020f20460b0450800025070364545a0f000c0c080400c0001c0801a120f410500c00000003a90015240d412500c0c2403a1840c1c103800911240c04540042c000300303019424094151003400c440c5141d02c0411541c9007410741c1c02c040c50301400d0b00c0800d00111380880c0020380c03620000f04698016080219040b030000a01400c0031078406a0a180d80d0044109031800840c8440421180c035003001400c0f40317071206111000089142002103003d036400c16a241384a203444000195846102e1070307894000990040c8903030744559684c2a401c0c02409016070950b9540214043c0e1000707280280 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 318737535 1250 318736285 318736289
    0x509030a020309040b0d0b04030801300308060a0b121b130612061518060905060a1223040c09050f070c0c080f070816050f0603070903051f1401 63
    0x1e00a5450010160100002000c41c0009503a0001003100040040b404000c1c50034851842a120070b012541890f01c2900c011410314030b0000c4c41c07200340001008042111120540c0c8985c0f508201e40c0310344450000900540c615005840382c24070105100302a942c104080c24021030388002c031800540701c0000892400c1c0700d40e0350540e0807032030100303c100b11892007840301001e05a4040e0000a066403144c40b50940303001c10b40d0003040029105844940c19081c0280510000c00c80e41c104070501601e0040811300601078030340c062081c48200c0c0203100031494a904241e0904411107080e4040d0200101c0700030900c042640d003030399215510480404c0542c054402e150040304011103410850741c56800441e4807001e042000c650391441034100003020700003009110a090146805407290605180d150303440d2a00c84031014025807441d41081200d83c840840c0146544010380d0003903500d1361681c0054810814590000380b9a10460340710740103a079007174100340c0c1102c2da400c41c081c01540c443c2800e2040c0346a080c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 318738785 1250 318737535 318737537
    0x13020309031204140102030a0905162601090c0602060f0a14130f020d0305191d10052214090603060c09030a0b04050d112b05071b05040509030a 63
    0x300002d41c420600c0e22482c03640b082c412800d102c2ca2012404280f030076a0020b56103508107580351100c0d00104842440201500103401c1810100e091410004240c07019000c2c009138005c42c81132141030740c1c03000c081d000004101d401004411800317603250002951800d0880e02c0d15030303280e05100410607000290240c00308100310400128800d4881070030008a0000c01441150180443c0c561080140c0301d20340f000c0f00160003601d90b1515040602180d50058040b440c14504000317910101c061058030018551a80050a4a041d4800079000005a41c2e030310036021807400c1120440d4000c1000d4585200b440143d41442030000150300f5005d0910411090503512540e040e0031950004c1c82c034a40360341c041d054040c0001c0845410207000d44035400c0e049415282074866402103803480c0740310354210702070300c000f60004001081d04451005c00503a18205054076806650304034203044106a1107030341550a0386030003048910300e50810500c904074544452046a004070300b0000090401078001c4143c0f1000c10032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 318740035 1250 318738785 318738787
    0x501080316110a051c0201110d020615060f030c0a0320030f040c090c02060f0f0415020d0f0513030306050109050a1206020c011803090e0c19031b0302091302030903 72
    0x41e40c0d9101ca02d1110002c4650308501c443c1000660303540c0302d403100c00f82018059070040400c03101d030000400300382c0308001722034550703005840c0780170707425400542c040e0f201e018030798224400c10115001403010300c03444440c0e000e480750100c140427030300411a0041508040e241c80030010101030044d022070741400c4d4092180c4900c024000070f04002034941c21194058480d00c0c9c100c800b240c50380200f10441d180c5000090040e80302404000100ea5128003444e00144500c0c4600034510317065a074000641c03043c0c0522140c980c2c012408812031420364000f2503051921720070500007494005a5940031401e000c2c0d06600107410001e001445500405000042c1d0700c02070461160241000c0e107200c240a1000001c8604e180d00f0041050005000e109016060f4620311020b201450300d0f081c01009050550024010455041c007800640280c000407524010124000d040448685000540040c00c1e4503074000000c0c4418800c1005090707159009201542049070300703685031030842010304100d0104940081c2c05030b00c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 318741285 1250 318740035 318740077
    0x1140105060c01110a02010903030e070806010302060a0507120f020d080603070902071509030302040e07050a1d03010e07350a0204150b0f0301090606080603150c07020a0f080105010803 81
    0x4001d0700411030000454000b050980900c0711103c60f652007500322000513590b40c5209001c01d40d142c01403080302c2112200521007035080c502d10644491044c440248504000200020000c2c0140300b522200b50700103c031224050120003029095480801071403005024000107030010a004540e014001c0801030018140d070b90070404150020741c000201a40c6100d07061803a06042c107a680a010b1540e80304c0e80d005601c0303501e000d42075010008041c04100502100344006981540e128105040c240c50240f000411181d141c0c02103401848a10f821a0b00c90280f0300003c60556007900514ad0b036a440f650340702e0042062800102010001d42589185680000310424050301d000c0c5c0003c6000103207120802d0490b55070380d0842e00c003070348004a1011504004401044107101c5842160002c1050341807000461034010000394a5001000c1c01d9200840b18101181e04034071420255916242d024124030006601e44105240304002d52003900150740c240390000c1001400402500e491030303d40001400050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 318742535 1250 318741285 318741289
    0x30a0f08090618010f0509031801080c0a1b0f1a0108191b0b0a020d020601090b09040204050901021c02030103050601061404330c0209060f15030a020714071701140105 73
    0x240390700325411a0b9034032602d000f5004070b03040c8995401f80c1c201364004c5542e001000f0b1411030002d0391983c410b040c020034608100381a4900f42c1210020842c5240002e11001040c2d40c1544011240030054030340408000b40c0002c0082c411058030840d560b04c140c40082c0e81e650242030381d0300c191346031440c002e030b08182560340c00150070051046400d0b60003080740454652140c0d00480c0c0c9800050181c5c0040c3d110380c006949030350b014862031303000d0062907100380a04c800340c6010461400c406480240074030b07511000955001d60a6068410300800840c030180018140e861000203500280416155401140f0000500c9801801403111584451611600300751800da56030314044044810094030103281c0103900c944100052130001249650303218265005003034010300c0704c010002003405d4003841e400310264403c0d42d2071003084464044c40003c07982c2d80395182d845880290160100081035549070380f201d280c0c6140089203100079a040c28100c0282807540340c0030b640c02ea803001c000021101c20b035000148068 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 318743785 1250 318742535 318742561
    0xa05040b0d150608011418120403080904060503010f0e06130f080304031803060606110a03091a04050d0b0402090703050606030609130b0c0a0e04020c030306012609030a0f080906 78
    0x2910040030300188082d0b8a44840b42503034141b40e481980340b8020381c200303c00b0101250340c1000f01e4113007000821002d042c14202d00868842e07804003905100010800005030350740c980140c0094007014000340b00300e03140c03012900d02034400360014044501a0100050840302c010b5440165182c001c1b503d2110f40340c0030b888628450384083c00980411500322050054042d05415000040d4030408000032107520b404802801c0c082c901c00c00e42c0664208542d10400700b039200d2810019280c8180420416840500489501740700d203600c40764118040104007428410340c010300c1c51040c1c0c002d8803082c0c66030b038600e00704904032103080325003540c030081c1400421002e0900304000744d03004602c2401d511010800b030b125506c420104403000d4111362000240410000d6200012481e01c071070507a0213500700111035030302039100d01004203d141040303901c1c003e95582070010088103124480c9654110324506188640030707100e034060b080c80c074003003241d88424400d0f0a01c907d80c06071140043c50301402d05078540c02850354103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 318745035 1250 318743785 318743813
    0x3030c02060f040605030402040f05060a05012016050108131e03050403050604140d051e090301020906040806010801060f290c0304090905160305070e09120f090a05040b0d 75
    0x14140700050b00d06032018010805021280c45454403850248100310a030b8030280422940581404d01744070751529840d5228003500c03400d00302140c1d2503a050345602d0032182c14100b4207045100d5145080011291000e843c1c007919420f0360b074043e0641c0d4600b00c207402580000e00042801e00c0c4908004d50b038a140b0a08000113503c00d00c0c00510f171656a886152a10b54151001d0300c1410018100c100b45200c10080b240d042111410450f0a0400700c21650b400054000e54028180000098100043e5020350441d20780c250010000c1d41c07902e403142620356440009000d03680442d0700e000d070049070f54000011010300302da04000d104603200544036905803c003140224080d691070000d1124080034030080c03000d00003500d60007000003400d0000c0d06201d483c2c00241002e9898214818000b8400b14a0114071201074a550351102031007511003030505468142182241002480c001c1041110031401c3c20040040103402c640e904001915a0300b08011107031140c01ea20f03808040c18294000217806031110340342d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 318746285 1250 318745035 318745039
    0x61b080717120f010510080411090702100c080103080708090a03060609020d060b0a020601031b030b07030e0f0c0627041b0f09050a06080402030319020d0e030c0a03030c02 75
    0x1040455560320420798503080c04941920410102d0740c0c40311089615031580d4010070800c05801154500740102e0f0380c0d0321102054008110740b50300001c01f808403803003192034040343c0540404264902560025200d041d080091340b8840d0510b610b030400389100c1c1202c14162600170112524100304caa82c0c0303044544c85509817030f8102026030000004200503104040080c01d0007400940e486141c0305011040718aa81c0101000c20303024410100071581c00035105044d240d02c500300c00800e0301c1e030100c414407800c50b5900c024510390000d42000640381e416017000d48003813814000c84040b0f08901030407980381c400803c44aa000035040c0100700c4000300380d40c0d40070092103030203001ca52084a603002103402d0340c820032403a4117654070007080c155056901c1302c0301d8200f480c00c1c0e2600c602545e05140004800303064921500701000740304070110781503607400d101701c2d070f006100e00c089512903400c4d404019442e021010080f5020a4a11400790440d090203c0c44059024005103c01e103c682180d4080c6e50070801e80300260707 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 318747535 1250 318746285 318746287
    0x6020a1110171503010606140f0f0d110d0e0a1208060f0d060506010806011b12110307050106050a06050c120304050307050f07032108060405040302010f110301051504061b08 76
    0x341c8100801c880203409000c0c10110b284200e103c2005160948029901400810500914601e46000c2240a071003040e01d8510303034165103c0c0fa000100c081ea004500b50301c0b48d481d00d03080e403151940f802c44000f031202c44200001032004060f0701c44070701d80f284aa0300028040059145800c21070521076990143e01c80f40080503200c0c04100200881c2c42004401d10858490b81d40d0000d101a540e0806882d681c030501c2480d20082d0340c01603003020011600e09400081100c020096940d00300342c05099042400708104c821a40c5801072410014042e00407440780502a800b20580891207074800c80854001c43d0300c2400030002d91281040101d041e42c070003041540e007404240003160005000b8000e010355480d0450003410701070b0a5060044c4000000041c181d040501650003800390b0f0341000803607600c200300f25000030301995507045c02e0340580300c400d4417a02d01c54039204c0000c1401d0304007000b5505032042621240004058a03450020702c4c41030b4040d0301f0116100d442422110b2040c00c0803130b00307601d20600b542 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 318748785 1250 318747535 318747557
    0x504022703070b0a1701140321160b04150203060109030209090c04060605040e0907060f030b0f03120406020c0a06021e0a0b0109020307030e01060f14030f06070201090c06020a1110 79
    0x1072031441e0084c4140d01d0002d0f1010790a0300100d82d00c042058090700c1090005410703000c0a600107541d5140c00224a002145a0281841000b9110050754951240c020303030354203401c1d281e2821407000401224216581e605511030305148000c40d10075203104a406840d80c00059045030208801920001c0c951000c0c2c2c459200e0000c15512a4007403400102070311707262261114100456502d2010b0000d04071a001e52107407104200a1f54400c54103401070076142000181011558007142c4801740309840c02d6014401c0b00042820b0600003401070045884d0350742501d01401242042002e46d003400d01c64400107038041d800d00c142c0107203180c14900c2001603c00031105c14252079a0b40c6110b0740c400768440442994044100100d840d018000c0c1007550183c20000c0003d80c5c201074130b603548400c0a010b12401c905046070522400d4030200074072000301c0c525004840291801e060028040c01c07a151084901c108420f50004d6107a0000400d1140701d42d00c0300c0074010000c8503c0900803010a40e07941e030b0041208038208 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 318750035 1250 318748785 318748799
    0x6210304031704060906080c07060e011523040216140a0506040b04020901060305040c0b0c0c09010f1d1b07060605100f022e0f0204050a140a050402270307 68
    0x190304840182d50400584551034000058120001c662081e01404000400c01810301424011501051ba110000150840201c42c400d4014a64180c1c0c0b02c0702c002101002190100f60b030140d4103803c5410140c0c4041c87e01c81c402c1440160300486a80c210700d038400e104004000750b920750110424003c080100ca0441d01d03144c0b0744900d00081030700c05a40c0101900180029410303da0081c6000d03050a0400b40001d04042c3d43d00602d02d040c91250001303645002c1800101c0c1c10041c03110390340b07100300100100020758443d4000c00b0980280c0c41260318080c450340710300c0310161098991a03c102d89204180e03421401e50348482c180c80d401110201d54a42d030356400451596201c00f0310004010f100d03a81c3c031f015803610480291500c02c14900c2d00b4020395680b480507801981401c2031110b840c8000b0f5006c41d1080c41031451001074000c9411041e030000170143c01042c0c11082c20130040401e00e04136266010b03281e4980030b11080f441802140d06000b8164024a40f01c05841500712501981c00340c21205566500c0f0f071 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 318751285 1250 318750035 318750053
    0x206070209060d15140105041415011206030303020c07060c0f03030f06050901060806090f01081207020a0e01080a060b2205131e031e0203091e030303010308040302180621030403 78
    0x13a110502d03a0f82c030380410108900001045001d40020b540410000550300108000790303c000700b401442c418000059030069229030044a03400300180760501185440e07144c0503001e5000359000305128460b081c0c4c000b446522400440c0206600030303103122064001500e00320090601808160710258031281c00041030340340c01d031809000702400c1c5d40306021814403a0030000341c004042c1c0418507454411005004800c40828803503028000e20001a980e0002c034400305400700285d07442200d60084603000084e00c1e0002003190012103204081c20407030702c07030520304102d039803001a04258203890024003402c945600c50340c420794006000b110860420303605540c92080c801c40020594415031070b0743d43d0310300405800c80b41c609c500104005a584074007070240d10003940c0340901941d103071040444845c0c1a201040082a1441c01c000c0a8150399880d170b12820549180c1d400303171104034002d0340d49c481d10700e0380c08031483c08660081c0c0008013000358500041092000c0300fa00e030b2418910500041000000190b1040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 318752535 1250 318751285 318751313
    0x30f0a06080d050c0c04200a030b0301060326130605030405010f0f0606110106030209070c0c03060c08071101020c06041b0f091b080f07050d090b040501060f080a0206070209060d 78
    0x10395659074030884000c00605056010000c5c3c1c0c019800d06202c0c1038111210541040c4522140814580740c0001080807400382811610a0742c1551a20201000b0b102104000c00081da90360310700380e204282e820034440700342d01c11083d140c40e43d00c2c000031040c0f100e14400c00045070010f004d8800418412003942d000b40c203da450566420580303950718003c101880d0000c81c1130001c03440110007044020310b0368004c208031100042003c1c003003142c540b07944020030007040c08100c041d5421180810076007494400140068001741d440c0c4c400310389160382c464114141402114030a00030440580643d0711641d5070516004c080b41c00e51a0f40085014002c030344400c2461540c1e006061aa0300403640f0400c540c2000e480c280307031000302d40400080104200328041a0300020390440c00300d00d0600d03030300c05100718860006c0c401c40f00d00400d1042018148418484150407030025600040314501c040c0d6070b140222540c1e1422048000c0d00414140400809031070940c05495008030090000c0c480c2d0304060341d803d00400c80741 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 318753785 1250 318752535 318752537
    0xc05120c090903180f01030204120606180207020d0320031215011b0b100512010e1e070308030a180305040303030c0504270605100306030611030408030f0a06080d 71
    0x140095a0a140402200b034010032084040c500e00780c1305183d03010018810008490098100092504080e40310380c0c100e500618100044a1382081c140c40c08102500d00340c07165086045140c19010401d00c1c07548200c50b8210350051160140c849036640c1520300180d606443c030220a542001021b403400c06000400154100d4100d0300764a10749001e5008003e681c031160681007001c078100c0401d101c5480c2d81e524524580004101c506951800c0c071100c294520f6412503500040300358a4000f0010054002400b0840440155901070085a031840d500620b0f9440d4044241d001500c1000442c00c11402036803c100c40040124a50b4120213076002c48030302404027200000d900003000c00900d6814800c9111a000501d00f50f40b4062a02446005c3e40403414410340c010b8840800503040c0c0000366000704018003002d0043d84810391644000381c001c203032070b01c0150b419505040c01c00c2d9082c00c00100b140e10459000e00120704507100c480c1041d0020703030001c06607440329a6440011034580c1c41040702c2441d040b21 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 318755035 1250 318753785 318753793
    0x60e0d120e1315170a0c030303090b06030604020f120a05160509010b12280f021b0604020603160c170d0c0203070f020618061b0f0d020606010c0c0512 66
    0x210301071010142c11840c403088001c1c40c0480d510702400c040d82d0790404441c20307500b218a0221a0b100214217011651000900310080b52100100701600340d001406100d000304c400d1900c1b41d50300740c141602c81c0e01c1220025804010603840340311030b00d025081300020f2042442243c400880340d81d1580c0c0b40a086100040398908030351002c10152601c500c100f805061181c43c070034104845600700d030154040c007804008070202148500d1040c00d50828202d0500103000740d003030006580512100d4020742c0140920a400c60200100c2c501031080003500500a0344e020381250f2840c0d41b000d08512017018000482010004420080c1c00815030350030500100100c104c2c200b540d282c20354080721040351030140210f001d4ad0030501c00c2402150900c4094a0740030f0701510620790719400310359a00e5900c0e11404005a001d00301081e02011001615250356401942808803401c0c50380c00c1094034ad83d0303024103080f600141d00180015409521524074400081e1180f01c00711600ca844000040e482401200708100c1980 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 318756285 1250 318755035 318755057
    0x50105030111070b06060904110a080403090b0906070b1509090c01170601021c020c13090209011a0304080702010e060a02030a09270e1e06010312090b0301060e0d12 72
    0x40d080c45807a015814000100340b4040065441004440000780601d1050b4000700b207140150b10740d41c1051201110700302143d542c610030b40b030000d01881401d1760242c0c000b0301140b01c00309280420700300300c0e140250001c2078141001829560b20708402c03030040100b85480e080d0920240c2c10703210050078134002d05034600034002d03820585000404020b441f40035265003080c7c01c030600c29141d80105000740d040142100e00440c3c40d980a0050b840c2c108045a5a03410043c089921881881c0035405032a04520032a601801a603848000f00c80d00c803080d00f04014442402c001140c0060004002803440174410b0402d505501c29140002d003294100295807400b58000003442c0780d07210f60004088024044c42c407403406402c00d942250710303503403109542c90f14080e95881113100321040c1b003040810751040e14039400c2640310b080001c40a860342d00a210403180305801100d00303c68140183c0e09901540c241420b12411a0b1a2400480b40c43d2030110440c0c0d0081b200f0000300f0f000c102c032618a20b034501447d8984003403100d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 318757535 1250 318756285 318756289
    0x6130b044e02070602190609080f03011a0a0e061602030d090e0a02040608061210060e041a1501030c020a120f02070803030601020d0f030f0f0213170303060409020a0806041110051201030611040810050105 89
    0x58dc04d1031042060000701b00802040e40c0140074540c02030000e5800329214040355565102a46038080080e5061240d0751050384032643c000004030564104406203d61038603400c4001084e03009a00855001c0384103000000c0c2a801d0000801140d52401c00403a42c000008240c0401143d28035004a8100c02c034220401041c81424005034405201d0300c0514842c5181100c0000d410350340d101d6241e0f04054460350400d030082d100304034a0110a40146004003010001580a40000403601100d8054014107000003040070010054070310816042e000390201c0888600c0841d0110486202041415030300e01c0e010854064a11410240b504a10310069640c080b0707102d110003048459010100044080e00c4685a454011003a02d4114209840102e907200580c4000b481c1d0b41840d40142e142403042c40100030500c28440f4002e40048400d40300f01c02c801400340f074201d40600c01d00082d00100208040104009030b0766500000c4a600f15408035801c19844070392181c1001092058018220340b40c2c80140b0941c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 318758785 1250 318757535 318757559
    0x1020610030f0f06060e06151801050c03040f08030c010b01180e0a1407020d0e03010c090506030403051c050a0c09050904030f200102030906130b044e02070602190609080f0301 77
    0x40140355090500609c0030749083c84050301001107042000100300e151105a00700191400b4200c0c15401c05440c9840d074150701c0e07907508500c202ca4039660810200341075a50251404406006448120604450504e403540d41508000341c40b5800d0705903a2941e081407458142d43c081c2c02011103071301410f42c6a40c00c85005192001c62003819200c0d914100c1d080348000d4001a83c14204c0d4000e84055031030340d60314242611036009401401b4942e411201d050500380300d6a510203403040560341030030400054820801c4414852500840350450480d102180200e8007030312800088030050b20b0602201855102c90005210707a000302c511b000c0c0c0d00441071140c00700007031005541c44000c45d00851140030305034071522044500604040c0c0102c10b0500c0d0910701c0301c2980c9c501440703080012404421076500c43c900c00303501004080da101107075144116404280384080f0314070041320382c2d55004150f40e10008a115a84d40c029120489a5540da490214000384108001d0403034802c92645c00380c2c072589042186000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 318760035 1250 318758785 318758809
    0x80d050a020930030301030f0b0109110a0c0228030c0806100308210f040519150c0c0c09060501021002040605030f1801060312030b01020610030f0f06060e06 69
    0x20349006100001d0151142014124004124034032002c0c841c1152020100d226014075015183d4000040040140050008030b0111148a4a00070000340c0e680d181000c11034441c605041041d20042183c99542c5128582d1070f80c1c001e000500070148084241c01d82d80c0f456030450802c18840e03406030002c205000d1100081c400a228100240403c1c0c07170312000182c071804031400000c0c290000454004a000041407a40b000c08140c41443c06080c1082c80c0a16040d12040720200e40c18800c580c80b0f51030329261603200007a8994410baa0030300201f150100c800141005a5480b42000b22080c1d60102141000e04940d00070b01c0c41020000e03116060200080c10100641d240c0c8100c1801000204601e03176120084030307400b15081e841c00b005501c9100300301d400e1900505407408658203110011061001400305035080c0315454804001c05000d480040e80c8039002140e072944568802c080c100b0210300048186554a40306010300c001c1d0f80300c42c3d61820100d0b095038024840c210090020003c0600703264401a50b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 318761285 1250 318760035 318760051
    0x608150904080f031f0915060c0308190b031c020d0f021f0b0d051b0a03051902030313150e06070503031b0409020a0e040f02070209040308060303070b04080d05 70
    0xa1140307840c0e1600b802e144680e000400702c003440080003070b810702c1d1000244000410f0039050030310184d50b2000564060700040000040410300880005030319070003220400c0c4c41c0f40d0305466114036665450800b19485900d43d072a428099124145030480d0358051080500101e0001e903510b002145035280280340c448270705010300a101850300740460007600000ca10050822203002c00290f81c00c9102e1aa02901d041000c03a234001840066100411801064800444103038030b0b01000b200b1200010055040054440074000d604040042070040c03d40d44440c194460010341103030710b048115400e8003220718450f8030134031101d0314482c0765101d610383c480e6000d12941c03c1103c7c80c9007003540355221030791a031202401c5154040034030140210680d010000790b90040510740c504546980480801400c0703003400380500e510403031415030f01d4800007810b8404c2d94031841d00076062006035600ca99080c2c403010700c06010340354107110a229007400140c926031071034461486140000e4680e400c0d04910015070301c001e04485 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 318762535 1250 318761285 318761299
    0x10b010c081204020f13050a0e0d0c080706090821340903051204080c030f1906060b03010b070501180314090402040f1e060306050a052206060815 64
    0x40204022009441d40102d40d80810389540c1c98130b03c000790180c00703030031116900102c0084103407a411440c1d602c19407241c400004113000c043d00000c1d440c6c0e21010640c1f500804602200b0069000ca482d2201401d04541300c1d0303000068034411038841c0303011504220040b40120112604482400800e51660b81d00b050b540b0900d001d00341c0c403140c030030a90f01d40101645181c4000c1c0040e05401d980c46419403000841d00441680c1d41140d0b44c800811099004d802029014840c1c2c20842c2e809040009901804a02a40c003130003440c0080200102c00580010080c1c600b640c0f40c250101c1e090401000540c003c0844c1ca031040d0b52441c0c0f17850443e0070342c0c40303c48066095030340742002003000c03907040b0b64130090014480a06503660358100300050024081c1c1d800c0701303280780301880c2c000c600c040502801e0480d05400c56007c034411540c4103c107c007508c1640c050503030440000941046242803400035091104c5014985114007801610100110b98035035001e0800691180b082c440c04614051240072061001d482034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 318763785 1250 318762535 318762557
    0x211113081b060a02031204120e03191115040602070303080a02030f070f02010906140907230103150e09010b01080c04030b060f0117040b060a0b1611040f110c010b01 72
    0x500c804812080758003030b030b00024400c181a4400d0040b200d100204903811500b505050030160a800030754950079000c10100300484c0e9a40c600000e60341c400d02e0342a0556000502c0903a81c814908415049041e0440b840b10000000100c03c90094400381185034000c0003ca481c5080090109101a0000b8502d903c10030038012081c9030799042c241e00050a05000d400d014442e24101d00600e01d4044c0a01080e1810080440c0000c0e0b64a0350781c0106100c8003211406034540a4108d121025080007601001c16a0304000c407035402130f000140c0e0312240b1814007407450342d100c200d0007500c0c80803585110319035550100c0c0091581c00640c2c0a801125202d4040c3c101811a9035205034840007910351131040403c9010391849030b101c1c2030205001d82d03000200600600707203490302c12081d80f826604680b0403030403050081110070308001a1003280343c05d030020021038901501d8050085040d035010076001615044941158115130050354501c1d1006003110b40c0d0750b8226100b01e42110400481241008524100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 318765035 1250 318763785 318763813
    0x160e06030c0118170606030c0102010c050d0b0a0302040e0606191503050a020705010903050403061b1b14070f0f0f0f0303050f04090c0305070e0307051021111308 71
    0x7102610340e00a00b005040c2800d483c10a5040f0080ca0b8480300784c140b540e100080201c1ea0100e10036018550031703030880e05105c1c0007800582c240ea618038a00c1d400128144020300d841020b07904102c18130365018002c08942616038000c54190b4075407000d4103007681d010000b0700190307081840d99007202c0444000c10507406414032a5514080345915002000c0645881c04a120040b4907412524070766030202c02004415454500174000c3d41043c0700641e4203914000074400b00d071142c203450315828207042d0786544900308a00040d106030780610700140c3d07141d40b8000741d83c6003141c0100500800b07029000414004e0b00c2c074000170306440c01e140d07802000801103d4901040504140070800094903498100300b61148241d80c1c8a020f1402140d10001c4610305011450f540560140c0c40a0700611450703540c02c00aa880301c0c1859651000d61140a80014036801c100982c01d2181d035405c1c500117144a030848001c50f00c035410b141a1a003024451402d0080060302444101d142c80f000c078000c00c60b500c06040c4260120709 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 318766285 1250 318765035 318765043
    0x204061d1003110c0304060801030b010b1207030c0c05010e010b030c0102011125080f070b01151707050c160e071404060e1f0801051c05120a090314160e0603 69
    0x5040c0c000d240e143c1c40a8600c1c58030810603a807903158404120707038940b0355079034006003860300030310040e58040018400842c00055110448808000e0030307004c0d03a11a01c030480704a00800a0010020800076008100c00001c0e1085c0070f8520748842c2030002140c4800804105403d01009903011030541e803400c020755117408001c07415206000003a13000010035001c2e20264250740c0346280c100605076031001130041010140400030b00b12040c0250b00300d070a030343e88441c1941c8540c42c103c503030320300400d8060340c031b55599043c1d0040450740200b252030041e08000da00d00200342b800503407000c00c5e8048074450406000300e002900d95a03600c030005140c01250300d00e88420741380b9030b4442c50043e0801c000240b1880e42c6c2d107456200f0020107000c210080040c0b4000c08900041680e403080c0035240c854441300e41e0f109080d60ba45a40c094605401c4000b51540306606503c0c8002039000030410000d104c424100000416241406444642c504502402d80c0619005034000c508203190001c20600a00c01c0a01c042510001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 318767535 1250 318766285 318766309
    0x106030b130b15030702030d0f0605090610050c0129061e070501091202011a040c0e040e190b1e070e0d060e0102040b281707110102030a0204061d 64
    0xc8001548440180104800c01c0000b102030f4980200001440010381d4000010071101c07058550810507508080c010205a44092040603401440a03010552529100d0086c044034059414298a803e402501e89401d6820f001d42001002143e1176103c00310300ea5484449006242c111a454905481c03950000011400003980c3c00801c0c40204601003008002d40c89400800d80141c0c1c010740048240d03a00074060000c40c02100d0540320712a112180e682053b024402c5502400d031200e130310008109040c80020945080c0c0da0790303244a42000d40e20b0349500707100d65580c013a0040050078440d1418120342200010580c0c1c0409518410800b0403c07000d502c0000003034021030444040140c450a410104d011340700c8044112015440010f0000702054550002c100b100404000005003400c1d00408100011480454801040d80224030900806200a499a0151443c240218000b104808035822600200c690145941d800035003400042d400074015400c00d280105103001802c10030021404900c9a4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 318768785 1250 318767535 318767569
    0x3030403050a0c051c17090303010605130902031611070302030a0f0f0515010503120c0c010309031b150e061e07140c010203010608060901030807030c0206210f0106030b 74
    0x4a0a8a9254841c0e4846007031244c00c0001c0720384004d004d01800c801c00c1080100c45000c00d81000309034124441006a0603c1050110b020394190ba18290060300e444e07020385e0510350407400b0642c0100e980035461002d18021007440c40d010080b950038007c06000c3c00b0800041030b00707a900c450000c00050343c0001e03401c1600307a8412260114054980f03000c1041450b652070040c21802012038080c044607410001c54100d80c0c0c00c038216488151203000310b1030144a0154030703942d503422041904060b075010b60040e0011501c01d10309201e50b0084525940c501c0c0c0c030141801c031982500100c500030352191900a81d140810624007501550500c2440b001c8006414130301c025541c1207800010b81024000c04600c2031500840d4422640c1d0382029003828002d5109002e031401048009011a1503410182d0000381a6035001d01104e01d8002d090f00c042c1c1d2401c803200822640000d00300205100301181303081e4104c1c204c501d101011b5003801c001c0c0c50542c404005030403141c10545010250003852b80c4070341c2082e115001c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 318770035 1250 318768785 318768787
    0x80a0905061615020702040c17101d1b0f090a06030501060509011404050d0b04050105070f020d12060f090c020c030313031b1e080601050904030815400e0303040305 72
    0x141d1a0f40d20068029058060760142c03810110b109210340042007050100460f2103030300b4055440554100345100980940b040e0709848054400310269603201482c8c00c4401d100d07a4031030528110b410072541d648680111458001c1c0403582a400c1d043c240e41d40c0001e0002802e0910481d81080c80c024268020642d501e4100300c030324100c2072170a41c002c0b02254003422018103001c02c89207250610102d80c2d0403c0d1400c40b89986812300040045125545c40302e00e01456601030441c0c508120b00450b0461141300114603510b654000c0000e04000b2040c3d00401002000d001041449048130f01074140003440e1050f41c0650410440080210303800c40c0800c0c241c0707034803010b110030001c404848415450480e03000300d0300e11108120b40c2041141465010301c1110300c10802c413991680c0344c2040c058484001d4800801240301080410040000d01c0161142400080d142407000381400e1480b036040361a80088038003000800710b01140c40d10201411580c1e08207000e009119201c44100780c1d40e0b480c0b00003400070b010040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 318771285 1250 318770035 318770063
    0x80306040209010e03030409060e011a03010e1e0711060a060f150507051002120703060b030f0411030a03090f0602030313020d030513030c060f0f09031209050607080a09050616 77
    0x8041d80c8000401c44d070280860b030301c40b601c8014000c0108243e00a10f1a00b050b06400002c040c4081211403000a200c60090de06507441c160503006d070008090700f414640c41c940034402076655010400c4520602c04c40e514403d80300e440c40502420060301518031020710741000c0043c4a00c1c441751500c5401c4510002e10385074230800e0083d045400d0700510800900c079004112204007a64465006401d1440340909801d1650700e130440b052702240c0c070300d01c00c03014400300c1800007540c11505500c400745d000d80108104014003901400103418501203100842c0891408a828000300007228034260292440d030000b9851401e01081e1070341b0851041034024420120302c20070608240c17090055a003c0031f00e11034002582d507101c0c5040d40002a960140320005450a00d00c00d4000d0f00c1280240017203005034803150040d504584070075081590902103a0b0500090500c00a21600c0e990010b08202e4012846140c0301d0800610050190700c8543c000c91081c0018019119644445001883c80300c9d030003840c0c80f070340070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 318772535 1250 318771285 318771287
    0x50f01020109050f0304091508190c05060a02010c020601090606021c0201060e04200f09041b180207050f060402031c090906151205150d06020f042702040308030604020901 75
    0x215803100003c143d0301482c0340305000343c20f0000141040c0c0d42c201405009224880e5000c1c1e40e90122482101c81c40da001c1c6010306e214219140a03201c20a02036a40c002d261511007022403240e50261810300e00503951480e101440c640e040c00b0ba81e02401c080b40c8180081850034100940c5c41c0c1a9900c4030301c0a80342030712242d920070b0003540681b000b4042c40400c10854507050809030b588900c601d40d9104200f02c00201a51585040004a02c80840c01001c0750320300d40303642d21a420001c0001c2401450401c550001054511119030441c01c1d64506120259603071001f46401e0381000039900c00c072003040c1e100806010041c2d60108100300d141698206202d200002c82c0811a14190741d58415105145085404a00d02d420b440f2080ca004825031222010038030036402401c1100d2040300e0002c08240400c603480ba01c0c0c176100507451152030141d000907041110442801d2100d0303000d41d124140c500c003030410101004030259441644099450401c601b0305141d030712100e0051100504d01c034070680c0c2c0007036009150307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 318773785 1250 318772535 318772541
    0x306030316080703030c08010f06110a06050a09110f101d0d03080103030806150f07030c061401080d020a02010c24061509050a0528030b0a09110108060307050f010201 73
    0x48400401e86a012000d0704118806500406080d4000307070401000810703041c080c1218504032040001400e0500b4038001c0c0445249034110311811140c0a04401c0717201094082c010a0b004240c51240004e824401d4a003108598500e8000707076000f42000c07141c0e80410394600d1001c9a814a02c0d003021415416085c0320b00c145010080407965125400c401d80c013003032580c4030842906891180d21040d44c6500d03407404105440386085202c0007881b000704010032900e040c0c44094010184203003401040c401466450f64240e554240c000003c52030061700400021808004640d0515101e0000e4840b92445400007401e110b809400030340b600d03100d600045000e10360f41519440c0b4442c180c10400082d030300e6a41c41d100c000c02c401056070016280d0100880e07107282c00890f41d03044074801841c516030b510a80c4240d107100d98a54442041c00d48005e00000301094040c40300d144070f0000c1c85400a14641da5142820501c0d000da0f2041d170400403181d0400a56481c0015444243c8000b22a003102003040000101e000d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 318775035 1250 318773785 318773797
    0x140f0c0304090e0d08070e0a03060c0306080712050c1804020405040809100c1b08030d110705030f040306060603020405181b070b010815091b041104060c0c230603060303 74
    0x10030b81ca40191625520404103c0342030164440ea03851010703440304007003110b01c1c0c0161200c1650140c0d001d1000c00c001455035014090b011329a040100e003881e603e0000c2d50820140754020185007000560000c1080024440c1e407000440c1150090202c003030b481d011200c5e40000420081c0115030340e00c045420310000e402075a030b001d1001041e0040802c901e4500600000740e44400b02c40e0420f114420041109482e01401c041c0d60941004500b000d900e00065806071014180d12a00711000704011004a20144020309910342c0c00c01c1c0c1c00e50348601d10b152010448920b6886a003c052040c0720600c415910b27418400c5815001c0301045c0c0c4a602e45001100301c080c030900c00b44402c94000581d941c00c0201c0407128604842d10181502c1d0300140120903418041c008541003c2250054255692107030a0300c5035403150148007800010300709080904080c8079a0250f0081710100b03c11550b0002000010007880c000382c408501c000c1007502810308070794880112203000701d105520120000700d072610f0030400c1e039403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 318776285 1250 318775035 318775049
    0xc0d15090b120d0f0c0204180b100b0a050d092a09060e0f130c050a231e1e0901030308060114070b01060f0507061a040c140f0c0304 58
    0x80040c0e9034580c400c00414a80710803502419101c14010000032000ca900c090320035041d10307112560006003504440040c0100e03800ca030301503a03511417403604801401d000000f10340306003103040390350803c42d02e210301c0214107a21054101d0010404d0030305040d400010340380400d4a024010a8410a80ca41581d543e060703a001c1c100c10b6440d040f100e84039112614852012a42e040d2005c00c0490788411110500c040b088828400d425612070110340d514510b03001c000032041c01200610503045e100c00000d1400c85031b80d802808081c050b0590b11004a010540018008404580ca041007004515445005064902445200d040321280c00d450703d601015030f070007204074020002040e941c1c5074a0040c00c03881c3d040d00c0490000e05540b103008440c40d01a02115000c2d81c120312102c00301d030f04e030140803a840b4800170a02e03070801105016440010f801c0c0e0240c021308050035503601076942d101301d06010441d28249421400c000412a03100d41c1400004100da40640706295015030350101003682c24514031555000e40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 318777535 1250 318776285 318776321
    0x30b0705091009050a090504020609060901020f0d020a030806030a150b0111010207080705010b09040b04080304060905030a03061403071a03091e1f0507120b04150b04030506070203040e0c0d 83
    0x81c542c1c992010160003910001c070341c08225142c9900c80035045030001c640094104208201800f41880c001000d8030b04544148110b8a603054103607e00d80c141f066155012015a000301e0610040503080151194131000c160028114201140c5030480c60b00020754020020b10350b035581040030b0781d20411f21800100740600081d03640b02c510b0314055400ba0b202c5030003500c4a51801c080c40001c2d192200c1c816000311b82107843e0f03141c80c0c1c0b101e4817040085c3c2c1c0040c000300c500550f103991305000128140301a22402005480008101d40b070205c00703040513402100514420340002c1000e0003c50181a0b903203100041c0d205030f01d074603a91040030362413800054542400384100907100d610482e100000c0d513070550940606001c0c0e484c403184120101980c100f502c144012890107807c0160200103584000410070000303202151603203c04c0c0f00301c1ca82a039150000d0141354400501881802810060140c218600744000c52502e071502203241e41c1c41d440900409a980c0d8006440040700030150490440544250404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 318778785 1250 318777535 318777559
    0xe0c0a03080c0d030917160605040f030e03030f07141002041514040f05010c030e150406142811030d021b06010e2d01090e060a0510030b070509 63
    0x8916150050850b0082601c20b40c8206611a4030901542410b580d000303000c40101548220011540d13003003006401c101d4a211088180032813028050240964040c035a00400e2140d2400c1c001c040800400500340207500c00c00048906214440c00c40f5400b640002d0404188440c4c04003003400c1403840b6004034403a03030021801041d14a1200c54040c0080e040f0b031a81e205c8a00d001c03003011958000c0e88200c00741d0f042d00840801c00755014000c8800424460300e845407401c081c01001803400104107105041821000c0f90601c002c0742c20014948204596161070f90070310304080c90340b2660078060102c1e01e05400105d024680e40d14080c0100e19241c0c0c1c640c030143d170344900e14043c0e03180094112210018003000c4c003408a0750301e80c001107034071410303142010300c07500c001c0da2440d203140114040c9424060380350242441015465000144260113004078081c04102002c9080c00540f801d034000d0440541c0d10300c2d00c818000d0180c501131140e01260303070103400e00940e80d83e00d5a060345d417405100078403a001290340c41c403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 318780035 1250 318778785 318778793
    0x914030c0d060606180b04090b060c070806010617060a0504020721020610050105180603070e0603041109010803030702030a0e010c140f072306130302031207050118080d0e0c0a03 78
    0x24100b500c03860795a4211400c0a285440c0801d0491b03c10801d641c9030420090051038125003214044c007002800041c54115034115080c940f00460380214075a402c5000140201503101c58040c0e501070b490410b5076060300380301d8002901d5030f94511444e4469580002c440003081510a00b200032032842d00c0b0009600c1040080c040e4884108a0301d0f80c084607032160b4003062540c01441a00c80051090000420710007000c014416036600141100040c0068034851464aa40e0840110700c668816075414403081841014401c00e11010703088158590024070030030260560000660300380741100e01d0042d02415075200140c5845c000020050003500e1070340d20401d100f007400100900c02c4400b54048910043c0d03190700000705240d583c1c4c0141600c1004220032000c610f440e074007400311100d904154101290382c0344d00081c5001031048407481036440108000741402428440c02c42d00d1810f0b60b111007881e0f40e80ba9511012407003801c01031000142d40303c049500c000010055079000100142031050110784a00b8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 318781285 1250 318780035 318780041
    0xb0f0a0c0f0f060507051204030f0e060a0512100302280902030108031e0313080309120a1110020f09120a24050a0c0801050d03020f0a030306090e0d0914030c0d06 71
    0x9020f44045050a01050105210351b0032141c02015040109180b5221a03030211580180e90b0342000400c203081c01c0407030706559000d004092116982e100c0e41d660315001a4102c20b4401e0090004d10b0100c0d18a1082015031100325401d4001004003144903d0401c0c14500114031035469048402600c0c40400003054031580007008182503030441240c0d42c044202e021600902e4071080f03a40c58032a21401c00c0798030001e00079002030b64100740307090169a05e811700b40a125165401500e409000540c0b001c9044013100b00601c54401c035010b80d21002e5282c9100a4402915440740201c00c034002d000e80080c480ea41101801031640d0940d010303022403803101601c005070b120204220511907500d4030304004151099410b2060505000560326440711070b82c43d01003040100c0100e0302c07041e4103502490448231ba0011060240d00101d91080d02c0010f030060034034941108071100201310000c25030118400f081d40d240c105d0307240812128904d85e50340225048401082c18020084600d6401c920545001c00c1004140d0b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 318782535 1250 318781285 318781313
    0x1a1c0c030204061d03030d0f02090d11180403170a0b03060a0203010f0509090604080c03120702101d1c0306030b040f121d060901030605100c0611040b0f0a0c0f 70
    0x25840160b42c11440030284002407202c1c4600750305600402c0501f171850780c82d07044142036600c0c041005050030440004540340300864201150741048100103520b051610002c110700f501a88102035a892409513006420007600c14100180c82d211080001e18001d899044128004400740546440303003080c801540280d0030a0003050b108410701c400106403800c2150311284544812070080481c2d0b00c5984400501d030b0321000c0d440181c0d000800144841c9603940310810301520b0705500603e0000c07400d400040841e203001c3c0c00300340450212050303019040c000007820008140c0d00030754000e400e61801402e5000f404550700c0100a00c902c17004100511090425503040307140940c900303004880400c00c045810011034142401c40c02c07581040c4000c80d04004010b011180018180007815903103d0001a100c100c0842c50400042c40210503081000914007c44040e1119007032002d08041c1044140703844d034054101314500b002800f25011001c80d2003651007140031a0010303800c81410081d41800c40402c1104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 318783785 1250 318782535 318782537
    0x8031311031c080a0b0901030615051903030f030e0a231e071509030809040b09040516090e030913201306050403020a05060c1f091b1a1c0c03020406 65
    0x120f00081e50300c0160b400380342d100880c010300e0300c1d8546c1e003075913542801003c0305a03002c207554658020118940c0c4400d017100e04100d104c50b220880d050700d03500d402040c501a000c0c1c40310070542000540f0800d0769000400c07080341541b10114807046520b80008d0602c49400310400300103481140d083d0700d402c03010348413140c0600c00190107883d041919181107200e0f0803502c801c00c4002031007014042020400001c064904940020300128910710342c43c0000b040c091041d20241c5164005003014021425041808001002c1d4064184100400d200c50b0b5a02ca01400007028020b2854400c02c5081004030741c0030362000135103900d1400485e0155626600c0c0ca8011610310440030016480114245004109a4080301e0b4003c1484500c941884144806034003c400541400d1050700d0780ca10a944c00c2d01c0603000f00e02d0a4507400941a1102d0900000c1d400000001d80c00d40c400c020010f2112010800c11302e100e075010310358a0360340d448502c0c048410418420440040360b0740b4080d018840f460340b5400600c102c40803 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 318785035 1250 318783785 318783797
    0x120f181203090506031b0304060207050a0629030c060c010605090f04050d0305010503030f07080d110c01110403050c040513050d0f090801051e0907180e06010b0708031311031c 77
    0x6503c01d11100384000c2d162402c00300c01c2480f611034132002510007141d00c284140800342c1040c034035980c0c2c01c1c50300c030b8070301030445e4641c1d00c0324803045804000c1d03c0100b03d6800322070600b0140c82c0c54000440d07141c1a0a01003076001e50740c00600c1d10300c480d81c03d4205030010b00340603080000503c5c04506d00000d041068404650901a03604c0c0396603100e101780141410ba40004024500d000044082c2c0f90310b6a00ca070707a0407102c9803428414148034003260f11409190601c404030803070342c42d1158000c0c10b00310780e0384030b100c1421524140014001b0880008120102d50300070b480019140e00ca101014442001580004205210320b04c00c40401ca9846407405c02002440c1e101c40030b890782c490360700e94203a0740112201c07000e00c0d221402e810910036001501c503400042d0741c419518015103908090351000c0b458a210400c5a407a201d0070805040c04002080c01455089540e0341000f0195a401c0c00512010705990002007400c000641400080b507070725070600000504881b0050010703401c460100c0d80228242000c210 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 318786285 1250 318785035 318785039
    0x18030f03040218010602070509040c1806080c010201090b060909280605070c082d04030f021005121603060510080a0b0f010906110f0d0207090b0d120f18120309 70
    0x2128140d0781d040c5d80c0300d5000703070112508210900c00c4000f4000c000f500c9000c410480026481100803c0100160400201003580340c20302400d10724003280d0b415800d0442e07150038034490108400a00154021600f1103069002d9210111540d02d0a00300901100d8842c91807540c2c220900c042d0b180018010f482500305209541e00c0d0f04c4288c40101500c4400f40080c0020421202d02000506004843c401c100c038442c000c594141c000e001d00c581250700102c130406850000e080c00d528040c61503079902d00d024a4118070b0641e00943ca28040a0060310b64842c2d240e42882c110315407402604402c0141c030b405400310f02d00c451071100007031808200355420b901300303440e00c10b44500d00e081502006c0c01c030188c1a16003c10f0985800e4003160541d50f9140c250b078440c000c4403505650394a0a01601d004850780d507000f401c0341d5080c26158011500030b020280d01c109450221240010403e2440c14048402c0782402c0581c4075030140300341c80b0204040e50b8403101c0c20303030301c0e02c0412901c01140c50140400c0c003d956944040da = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 318787535 1250 318786285 318786319
    0x4140114060f0301060804031e02070602012403080c030d0f1b0905010f0e03010e06010803070515040f060b030a0b0c041503090b0a150b04060201060509071b0b18030f030402 76
    0x122a000303114180b00000c2005000e0359000312107294100c2d20a2820001c140151079040c020b509640c01740f0801a0000701080209541c240110344202103c05040500780c0f00382d8200f00c0c10f030304032884010480030012541c010040b0091042d0b07050a14007a2050045036a80c80c0900c00800010214130002b040340d05201460a01c100086016a0010303101d00d0140a40508251204840c800126500d99202c0900c980344d420148401402450180021522030b0f4543c40d0890801c08800d00b055906103c0208000c045650f03078130315550064000400081304424000400e003042600c00d406081c002007102840016424007001f0300495090900e8080c0b0842005411000d03140360440191140700e1240100e801d51816601c000035021664a0300c00865640e0003c5000f507420035800140540d642d10010013141c10404241540000189400101900c0b03001d41e89400098801c0040c101d0705078180043d010840141070042605101d500b142d840d01c441c06043c05180d4421a0304034001c4001c201b0f594011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 318788785 1250 318787535 318787537
    0x114f030c080133050301091a010e07050301030305030414190506130804091503150b0f06090d0b07091d0103060b0a1206110d020a020c030f0313061d0414011406 70
    0x1918a4801c0c2410301484200200c80140c00c61000403503200c0d0600f40003032959024854200c1d080d228141c40c0009018512040b528640142d01c55108865800100f100540c2d2240c104d0f07056a41c58140280c5a072100c0c20004030084030340b507400100d403140d0310300c2a90000e001000001980d126104445d52503a44429410180c070469400074aa89000c1c041440302d00e02c00d400003003950700408a040c803400e0307494840e158424281070300d42010315a01c00204c0c1c0c10341054406581000303c1074404030b1920038160b0100f180e0b000c46102c080d04c0c41600002040096110720040b41c024400300e12a0340f200600201c20418440d820320044801529002c112800c905064050038100d0720904181ca0000205465000c05044200d0103803020302800c0208103c901d400c1e10203482140a10383c024200711006100b41440c01a16600850702a032040c8203080c540f948002800d01a20500c0c40d02d488440d01000403080c8600510760129805420b0032410f0a2500f00c3e03d091504036002e1700990b8120b12005014040381e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 318790035 1250 318788785 318788801
    0x20c030702010509030c06280f08060904021f020d0e0409170304050a0c140f010806060a0f11010203041115040b0304023001050a114f030c0801 63
    0x541040c8449405580580050004210080c0c15100303003c14802c0040d486901c070340741c01000030043c00c0c0b0150010060290b2480c0b044a10305280c44500c00c6981c01502c2031500070035192050740140c0001d4211744601e12200e0581c003880701c031804a8499220007a40300d140a0343c000300080e46040c448222842d0601400380c0a5821000030941404808002009070388010000d5506100b10051900020301443d2208004c0c25034140d00e15a015500d020000d04a1785031a40a041040300b00070b010350380da5450100d8401d609107040c035141155012206684c441429018000c00c0c6d4400700c2000144412401159030190046601c0c00070306801c05070101a50040c0c2c00360b0201c881051000400508107004012510014094000c01c801c04401c1c841c6044031807844801001e1351103109105840031180584514082c04442c400c2c01d2420800c0601d140303490b188664004410700d0481e00880f404c02010b401220742080e8440c0c0003e8118010503090b0b01c08034801103601c4201228001031429041c0b0403010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 318791285 1250 318790035 318790057
    0x60501090e250306110c070b07060c03020a0915020703050a0503030a0e1f11070212010b0901050a1a090d08070302070e0a060312080601120608060f15090414011508031c02 75
    0x1c440e42035884080c02000c10036070301d03a00b248042084486442c4100140380051036a1442c26548278124901081500e003148180300502d401840011200c54216103820107a4250790500820102c1ca4441240341c400303541d20151050007050060428800c011008500c12440c0c0c0c03a0521101600002240e901c00928200b91444882c1c0d0030300343d0b800c0c0c9040d002a0001e01540d0f1009043c500b107900022852003800c0c0601c08280e64412100849003000380c1c0c4180140030442d040701040e4980242c00d030104080140c00d614071030b00001d024000c0d65480944800035900b0100c41900c450035490040d5613041e450107032540c41040f031400600c130030541e40038034415603520902a20011140d8141902c00c24005002c5506011240266440102d080d108120007081440d000701018208041840c0c10080054020100300308140d2525459442d007094050304107510010b000301400d164101c45004200c10005ca960340c040d203050000d0b00d0900080540300300d00b002d49222110b0880064908100c0c0300ccc00400d10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 318792535 1250 318791285 318791353
    0x10f08030d050a110f030a05090313090b060708070c0e1f090507020a050d030606090503031908100f060905030c09060307141302030f010f0e1b0f07060501090e 70
    0x218446558202c603030410f524420125901842280301c000a4002c0c480402c1c001d440441000f0b510354041c00303020780004119001d07601d000b03274007081d0004001140c01036001c0e0a03219640f070301c45030f00d41d0822943d400d0782049c107454490400c0e1600c442019241e100303109225004a01080c80c202c142c0010701001d80d403180c0f5400e505490202d16402a003c010230280c19802521a154040b98080c0440580f140080d98005007040c1810800b800e400c00f5034114034003030360042c8481c0008541304030240c400000c9500340842c2030b43c0c940307001d12880d090030307007000305103240d04900040c00582103800c02c0c041c0c60044003030303851001d80720051000c0203804a452036410b61040c0e10400c070314003156510b800c03480005000d0070203070300c5280c0040381640e0042c1c400e030543c0c8106c2d600400801b143e45026202500400300d56141d581045503010b4210891111100381042c00004e42002d01d0728101c084551140e8400c1c1d041c0003d40c0d40e0114000202040a00d040f003501070344190940c024881950300115020075841e079 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 318793785 1250 318792535 318792547
    0xa18020907020c04050901020c010c0203040b07030503090a052b030902031f1d06220302030306130906150905060d02010c0609080412080d1409031804111c05010f0803 73
    0x1803038001800780419800703010105a4281c40e24056070b4807030304081d00003603a00d41205280c182160008201c000131504144000d2080c60400740880300741e9501490078a480381c03a44100c4d00c0c10300a1454006015120b04d014190a00e030030590740c5407075100e0800c18501601e8101400398241c2d040400c000354036410055030701c1240d05000303c03807120148050100140c0390042c801480284d85080c00447c0a980c000000c00401c0f403d0042044881729440c090740103c00c41c540c1c1c0c046e6a900001d00051b00c10f40421107402d18200b80f03a8884989140c2108041c030003d040c0138078400c40800c1601988000900348800140e140c02c01c00c0c40011200c1d8180e407a900e9104907034403000010020710504542040040000040e81550501c00501003406411559070700c1d030140c03e20404950b404450b0b203908204607010054a400c0200070343d1004100035000045003130508001400900340c0c0d0340100401d08001c0b400010600000768400c006000003641004581d88800449010449611920749554810001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 318795035 1250 318793785 318793789
    0x3030e010c021c0302010b04060305101803170c0d240603022104140a05030a02010510030f15090b01080327030606060d0608150403020c010905030303061203040509070e090a1802 78
    0x407010343c10f40a44000504081400005000c0c0da200760b00c182c566600c8a8220b0681c6141881040c10074204016840c0300f9802a54000d481c07014031007808072981d142100000e4114070001d044503400c249040003040301c1050400312181001d210b0300403050100c00c440c404500580240308588110940c11941d040b010f0a6a190249900c0c005104840350400c0c0c1408140c40c00c1c04112100c0b406101d2409136448016201e002400c540004100085807440210104040344203071115668540e00016940141411004641c1c081d08044038002c0c2410803e00001400d0b00d0040041d140900c0c14400c51801c498802d62140f02d00409a01c100e645900403402140c801d2400e03400800701d40c0c00c184004074075145e039005c90a0030403000d03082013040c2c0c401040c01c00007051f42c1401041c14004090821461483c10040880e41e40c0c0402002c8a020b0380324541e0300e40c1310380001c1050340c004101c0200380c42d540e407414560040401c1c2c01707000070300c0c022041c000c0810101c81503805414062040500c080008841d680c003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 318796285 1250 318795035 318795079
    0x10501050d150504020d051e01050d02040b01020c1e012d0f1803030c02010306080303070c11030705091009064a2509080c0f030705031603030e010c02 66
    0xc01c00041148041001480d519140091b00c00e00d8010300c000070315403421000b500598042050741883d202d918400601a598500b000c0c0082e05030155400038800b0348080c0141d01e81912200d1b40d43c0e11400b1403d0b00e0389019500c0035488048002a601c143d01ca9655094111000fa25151003100080c402c0e5140407005100d02c9405401c00d880b0310f0140004020900b0284001140350000e030000340010300424113550705401010024000a0002c600c6c505d40030500512078000c845000301115002c0c0a21501d554042003c000034090040002d007650500d5142107510355170610950b8481d0342050740000d0611036100e030340769505040800c0c17074012408402051040048820426281601e140b484171b181e40c805000e8030348030318004040100f0218038204a8400404816010010004400000e104000d008909060741030400d071403d51a141c14207000030b040080301c0d04919054440d8807100d080c207070400110704040f2406034641030203d030358100045440c0c104400c00a074201000c110304210319941c800d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 318797535 1250 318796285 318796301
    0x3190f03021908032715060609030d0801050301050a0b01080c070303110a0203070311061005040b0f090f100515030601050a110102030702030403060615210603062909010501050d 78
    0xc8180c1c1e08032219000c80100d8040042c0d801d4403008008000c0090003103600a002071031002400403034040c040100043c4e661100551012450001d103000450826100d0800b50b0ba088400141995a030320f907040301c014801882445035510070b42c00c040100388007444d1481950580e500603510103103907940b5914403190981c031900303045003050344d10046081150401030107030000121680c061036031004242030051162200441e000740c00e801400c184803224001380207a10884200751404105c200110380003d440400100890b50070440d80c07010041640d000c00c10040c0300301e040d0345203001496101c4051100003007482400c2504101d0030404502c666010b0700141404103c1450045100d0030314001c25403d9030019900000580e1000c1014402c10425000b100098407003504580080270a107007004041b0301803050b80030f4108454440d420140d0b0300a03000328010b15082481271050040040c040f40005500c2d89030928488901f040e43c1e062898650502c6040359016580d650404a10b0300c48000100341e0a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 318798785 1250 318797535 318797537
    0x1110703091e030f1e0309031b08070909050109050303010303022a010903020f060912062703041e030f230c030c0103022d07050c1221070b0906100503190f03 69
    0x5c0d40940000191810003400301c40c0c42640e0303240d0034500e140761038100008811080058400620350500c40c2e00800a100c1080f507002e1000400d00c6411800c14034014114000068040d010004c008401d240c3c00040c8030074190310180b052903400d80585504101c3e01c1c1e018030b1550015020390410000b41c03901108540e512040206070504d06900034000030107000c51551034091981224040042c41c03400000419000c8102e2000c1601c40000d01188a032240b14502500c00c101400d03011203040d000309594203030055688203840c9000c51f13010307082c40d00d004c079004500c1141051401024400010b1b000c50080749140e8090018048141c4013001540031750092070140c25000c01c208621103601034640050858100658840d83d0346400b1414014180381da0181c549014000b18012410041e42c0018440d5000303141e145a518012021407400401c1d2141100c040c01c4a081c02d01400070301c000100c0e03c1c40c003c0d0031505800318203e5550050503202d0f08024408100643d02124213004100702c40094a82c1c1442 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 318800035 1250 318798785 318798803
    0x806070305071110051801020717070503040f06050d15050f010309050102160b041208060a060309060f1a10181205010902030f0708010c02120d0e0a0501110703091e030f 74
    0x901e200f64074215200304101c03040c42c1c0b07510900000714004a0300c1500e00c11854000d500d0702d00951502c08000808014407a00c400c000a0f0300424840d05005440140580c010300924650303460703c000301250082070326050f0040c90315803605000480045410101c90015250366001c52018005500130981c9580a8505540810000308070b0610300003280c4031540700c0c819825a5007014142841900000d501d010f01303124076503040c8943c0e0b50300c0614041c12180646004501d200303140c0b41000c01b900e0107c1c0c1c60f00b509030820000807010000b083e03d8a03244803080e2045120001c250808407401c0074006298040c0d550100014012a040074814211050140002044c9806540c3c0400d180011241b43d01c00c2903001501c052200800a01a00d071188000784010001c206070380e60f800041d84103035030005110b50f9456611480c144070511040e50349031381000082100499800c8000c1c034581c8408811400503d07400f101150b03030541001c2012075243c00032820b8003428203696410185012180301506d201d20 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 318801285 1250 318800035 318800057
    0x1d0c13090b03150a09150903080103080315090103082106010e15120106082a0306010e210d030f0203100306110d05011806051e041e020f1b07080607030507 68
    0x3080a0105018013100c031000911101d071400e060321000c55842d11403695a0030002c0801c0400c1d40300b46003906603900480c0055580e01e0300009034030800d40e130105284d000070303202d0b00000a006074540600500e10010403100500b090b454400304d190a01101c900d030115020504841c128141400d15044003000c1c6118246001c031170f0f010358828050300764000d00000e4419000c1040c0204010f40009410307201b10f1281900c10b11030800308009000042c855410408504d0500900e550380c9954014a441100d00c40a03040840140d2151207c0c1c101042c0e0f000700341041c0103136184070528030843e8844c07458846400035040c00d660302c2e80c024050b0100702080c501020b1004045000107440f0f954020901003c0500c0b040b019404a50180c03101980310602c5581009940204402030002011540900312000201907407100d00000300c2903403074607180c0400d62003c00e0361103e003d44a00100651090b03030780801000707100144c1080d035070b001c03030302a1168a070084c202080b216400b9400c02c41e0045214200b506403c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 318802535 1250 318801285 318801313
    0x2060f0a110f0901140301211a0906060a060f020c040e1c0201090302010f051302040c030608030a020709051006050d0e0c0409050a0303050705030114011b08041d0c13090b03 76
    0x1411120900c40b2140c4000703410005981c00074107041a03c5407904043e070956150500c0141c0709078206c1d80c0a0048a95a0103c1c010844000060041103844541c0d004150414a0b20103075142011102d560082d0b554500c0800c080b801a011b8001001650b401000382041920510016107031003900c219240c86102c41283d013113801c0d81810390480380254000100d00205040c02800c0d12140c8034011007151a2030280401480c0d914400000d9030b405030340c0403451010400040300140140d901030080741c00045181120b560380800c03003904a564048061205441c0c42d150903803c081c080c818840458000c1001e50301156254124440b461480300a40b4441804240410180d91104000301d40c260014600351080642500c201d5411003038603e4424215030500b030301103a803130840d61106030500c00d0031010800c0c10000c0312003801840d540b122a40791a0f80d50744480c80c004048009800240f100c100300040c502c04441c0c0c094441c0131281840b5403210760f1070100844000d104a40303209400d4084d00d48011585 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 318803785 1250 318802535 318802537
    0x3101e0306050f040b0f0f0406020a0e19030c050f010c020d0f0206030f190501051c1e0b040c090b030c01140c0a0318060302040b030a05060a0e040f0b090102030702060f0a11 76
    0x203040c564002c007a0901d00342c54280c010000040c1b0300e12042d0000d0003400104541583e001e03600c20351005005a4494045c10305503403844058803919030200d2110b03001c200038159a000c19003201c0c411000c00b4565501d680c2000b00440416041c071740005c0fa4508404c0161414a50f082d8500c0d0190055005446082d0040f9000c0c0e0320445040d00c8400c6600f041c084d800a10740711010711482101d90130402541003c0001d5452a101045076107480326040410091081035802c038161034004290041c0691058580880b2040c42240c080d154042607441c00584d40009000390104520000e0141207200d5240e80113449800c1014442e408048060102c0c0d0540301003080090707041030180d02d841040440d01d10304115000001d401090405005000170026049048156604004c00c8000842d1303075034821010a0a00003ea80f00c800b151070b11006100a0140b80540e00082c00d0246981a00c5641c41d03102d01070907440142c440c0401a8400d100048581644040168011240d8100401c4244055400281c1c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 318805035 1250 318803785 318803791
    0x4080403170703092112120203040507050a1e120c0b131e051809010908120106021e03180f0a230102062206020904020409051b03101e030605 62
    0x1c8144005007035400e042d0009806002800020303480c4003015080d1202240341c548011000341518040e4180002d8036000345460150306220400442d00c034641418007980d07c1c0014481d641c0554254000450007030f049003002d82003411503004402c20709150200b00c0c0d0212a0942040d65180040000410301110041c010444540308000c01c1c0d0b04241440382e43c2500300d12110140103c1034445908201540f41c08007600d4104d141d0388940212550303490710090142c141040028103054002070080240d0002001c00d81c182c071465822a85035100102000d03078580c09100708804070313500500200b8020310740c80143e240d00090142155010003a5507021440407041900020681c000700d4032005182d624043c0d4024001c05e0903c01003061f0305100007141400c41204034051104510040c1e882c0611005404444078004090b000315a030750f58686407100203001c10344440d0101880380220306104480001601c0c000c03000742c450021030301d107840205003680307005a281d020309000c1e450340080810000c0c030520384 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 318806285 1250 318805035 318805073
    0x5031b280201030209180613020a02190611031303020105070503130b1009020f070209220311031201060e010e0301060e190f0e0102090306161e110d0e15120403030504080403 76
    0x705400e01f541004031014404100c0c16001d0320510803002400d82c00180c061800100d1380308000c0c8207040b41480005410010010703605494000207122a400000001d0f04043d8081e074001c01207a107032804116041d11080d507094071003071300402e49203012a400030f4046401c40000340b108060644d441004c401079801403c4101d02a0343c1c0403601c4815800c09403000c5901610501110100f083d02d803500200c01c600d00300000e810070060008201100700200101c0e0070110b9100d120200e1503a40310401800415904a01800036004d214002000e05050040100b6039445440403009035a0300d00c000d0800a40c41100c0042c020f03100c102ca00c012003060f00c42c4100b05c030108000036960310401c0041c1864104043d01c00d07102c4155050b404403c00d507100c40700d106c211941030114900c1c2440401c084910000001c015800c500920700e0280055800210128201400303903050300b03002815540480b203a000ba800c2c211440207807640041c1c006442544400d41c032070302c00c241040c10143c030703a11101811100419000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 318807535 1250 318806285 318806329
    0x16111b0618032a030a08040e100306020f0702100206040209070f0e0411070221030a031e05070c1203092103020c030d021201050a180509100905031b280201030209 71
    0xc0e010b081c01c100090841e000c4d40140705503011950f521603288118818003405800441c08a0304031541d104841c4000c680104040d034543c4e145408206035139002c0c0c4800c0b032080700c8202498109074008600280b0072a002482c601e803a554801040e101c4100303407980d010400c004100030001e40e96540c07080080b044540d2860945601c090300c1400282c0c0c14001c10710480e0043c1100c01d142c40c0e0f40000484008a0700bd103000b180f508120a000342d1300400d00c56001e0b460f241410100440e0690080045106500508402010f40b80d405800d808544030600d010b0030944102d140400c504480304440070b410b80307141c030700149803402001d0030904603041410800801500011f081c103040c40700c03803a900e0160804075008103007945400d040141d40c90454018603001c41d103070800603200d11401d105010010b40402014402d29805e481d00a850f90702c0b0700a111100345880c072052283e1240040c11480940e4842c20341710f12a240e200070b000707070259901000ca0400d40c0800caa150251107081368002803c3c0c3e035422003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 318808785 1250 318807535 318807583
    0x8010608011a0303040303110703080d090507051005090f12010203090d020709151202150406020f10020301030b06150d060b1c09050303010b07020a0306020316111b061803 75
    0x150070364030300c112407030101200e01d9846481580c010007110b0840e03905081c1500d542e41d044500e0349c1841a0713548090b10031040842c0702000c7c64080c0d04a0200d00b07208905881d81c43c1d80325001c101c17900b01e952109400289091010405070b043c81d00c52104440c03030042c00360b0b50f003481848070f541c05d81c1c0c0112882200d5820035800d505200c0d404100007800b0b00b000541c00e00c2404804a120380c048802032048002d0840300c0c01508040d51621045500c0c4043e0f0480e5142c0d569448a40207540c5141380228820795103e070402c0340c00d507c003407842564185e96101c07007412003d880d68010003842d9100111900514001005640400e0f8620302c949801003040c00c1c1c0c100d880e022000700140032501303000c034030354001420071041c41c0015002004403070640302200451034032180c0600204030781c103001d0f41008240620001c1440340c180401c650400e026501541c98208202281d0001e503181c61291035240341c2c168407501351040310700c0c00707501501c08001040a09807030b22015900292529000f0002c034842402c00b8841 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 318810035 1250 318808785 318808799
    0x2071a25050d020f06061e06070c090b0a0e0c09010e011b030801051c030e01111608030304170a120507030209040510030303200706020901020106030c0902131a030a0504020118080106 80
    0x1c0071442e0411031301500e41460290081543c400103815001c1e0b0a851140c1030800a0342d5100030b0f504225042071040000301c0e16800030400422100c01c085100f5001d40100062881c022422180b2a0a030b50340d40500b0040000b00648000b02a40d002d01e060040200950380755a910108078a0418041d0b902c1c151503500d00814000c001c00d060804880d212042d441003c00303e50400c0e4400191003080c41e10801a81201c1e86050030134a880100c4121810880000528050004041d41c0100c1c015505038855000f0f45903084224465205603c010880c4c80c80304611104950303000e00c0c0e0142907814007505c1d150204000400301c401c200c2da0f90803683c0c00528140240b40e890710800010700352000c0180000c3c1c0102c1044007181c00365000013425580c0000700c0e900c0692003904080000c1d82d10410548c40d15448143c800c002c2e4000c1c2010510f80003081c007000451400c0d42c10450100c00341c1d004200c0c551303180c4045240203000e00030403d9062012031298010514050204c000052401b800009403440c10840 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 318811285 1250 318810035 318810043
    0x15040c0b121b07051507090f0308030114040e1f180f05010b0a14090603030403050114070e0f06070303091a010605070c08010902400c0e0102071a25050d02 68
    0x1c01680b503400a2240e10001400002c04070203284103003010348100d6a5a02d002c40c2e83c41003642040758000382d41d207000801c0003a1a00a54142c030605034480f92546400e10600003102c8800da4a111a80c2c020906418810307100e0341d08090b0f601c0b07010b00214600032070860410b0003d01810044079840854250170040c01828132070940c0b41841124401c0c0054941500c02c150203810600e468810012000030650580c0c0800c02c840c000d6521100a02801c49030380300d014000001200c45001081c40420102c00c5032403d810581c9403079200a00c0710341000c1c46034030102c0080102c400220350900781301d20401d45075440361440314020560389c0c1d212560b03500c840c6040c0c2841705d1680d0003089642e05000c44840141d485000642050f1500c56400c1e00002d0f0b41d1210b14004034801103002034060662002d012040c1840d045201610103d4440c20300c0846131000490b6a00344922807484512550b007182c010360b5002000900395945c203038070f000d0420070703c0b42c07000c51030110f14110031901684003003681c0d504250140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 318812535 1250 318811285 318811321
    0x6040506010c0804090e1e071a03070203120c22090e010204030b061c06051f080606210307020a12020319050a02060a140a0221070515040c0b12 63
    0x2103010702c071000c103540e2010843d015600400310403d445a42030346981a041012295140e000d149640090403401e0560351100c6c2d00c4e000b180006d0384111040c98542401008a038002c40403640254508034584400c3c5007500405062885104400c110301103c082d8a0080303c40b400c4400005000038920b403d540ca82280c0048840301c1283e401031000700003160340c540105a02000a582407540c11600c1e449101400341d402c00c0082a0a02e414103111201e034081500080120b89103c0f41d40a082d00d52858076550b007021074019070f103c0c03000c81d09440d04010a403000040391521108990400304250300061464507030b90011680c0001c240e1503001549010030405082c445800c55401400605454180d2540d40f1440082d001d814001a034501051042482c4e25404000f280407e0302c0d03081102009441d6007441d03112911003095031580040b180881300031180c0c100c0d8860020218040002c0c54003451120091003a60500c03c0688009030f003020180c0188a4030351482c13442c03916860310302d221004124200c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 318813785 1250 318812535 318812537
    0xf180f06040b180a0f0209101101050601050c0a170f0a02060610030912030506030a0c030f03030f0e0c090c120709030501050709050109262a0306060a060503090a020303070b0604050601 81
    0x314102c4003100c1d4210b03c3d041080c842c00860201c0d43c5040217806803190103840342d000f900303003244048c41c02e42c00104c1000040e5070400a101d07076181c0c000111910b02484d416040560000300c45000000c01c51b124091050032911961030600103103580441c81a089500b4041c0560405410000e8a1510b8112500c84040904082101c802c040d11205c1d203070260000d1240a250780c40c00810b026903810003c40044542c401c4550b07051513103a01d060102d44c4081c40044021900380110100342200c0341c00760070401024000104000c081c1c4000308126a40b000d40080200401041000002901c400c00381e88140c2c1d9030b40f0703640900762442ca0510300b190700040c41c6a04001154400307104581e131020300c40f404c03903401c00c1ea4080761000564050042c100a40d00442d010300c1544e0400c003031004c0c007000e80c0780b002104040000040c01d11409150315542c00b1208958080c0d0902014400e80340110061500079408a044490003a000d50101c2d1440d4007000d8140c40219040003081181e181c240500c0d507010a003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 318815035 1250 318813785 318813799
    0x10e0601150f0f030b0d062a050d0902040e060c040317030c03010b0d0b0918120c060a09260d0e0a050d030230040605070c110f180f06040b 61
    0x4000014030741c445980d4402d04021516503190007a51080c0c02c5280800d2008080292034242454554010200700c000e145500b00001910a41014408a500d910210303507220ba614041ca0040c0e0400109509001240d02540d030b8400c801c06c00f40200400c0d80304040403901c6d40d50b13407421030416000048403800e1400d0000380c00c004020500da800002e4904680702006030b6034640034a0781e0074070701805924003140c0e0455418001c210f800302406071a501e070a0400800c0d2000440711400c040030724031501150030095440000032442d40c890541c09080d00d1401111418400600b1002c4c1d00d146a2280308090f040200c08030381001400c10710300c51100712030380200040c05030741810350790a601d8804500382c40003419404a0414070110110342d401c100b0703d103451030844101c5048500360f980340d8800e880a03691a40b1301000502654003480c0c04032035107030300f0842801c1c241030790004125005021065042e00714005a00844c1e00c88001d01c8000c3c010450b00780c18950071300d85842404200ca15400d692846452 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 318816285 1250 318815035 318815069
    0x60717010f030803061f020c040c02030423060903070b09010206070f1215090608030414030312150105250b0601080705070605060a030f0305120a050115051e0c010e0601 74
    0x100d450044102c03a4022180c039202d690780c4002888140b1a9a5072107600050404200440c56000ca500c48140d40200c60400030f400c00e10a04a81d203014900808006c400c1960030042d881a041850360343c40c0380010122850700308031390007103401c0990550080f100f00d4401326001d603117582c041c01f40542c0010360745059450920150401404c02d00302141003155241d41c0c0001e171681120350b60a00d8083c151540007031240c0b60f03451f4580c0750340390b2003071060840002c0080c070705080518000c0300310703a801d140c2035000d064640c42e00040c00f407020300703071212082c1441030070010402c3c00c080d04018ac2001d041030365401000701085003001e14650340010f02c031904100c50758080081d015040401d8503030407034014500060340ea03950b00100d841c1aa4507000075142d007482111510070568050b00400d0b900c281001c280c51503441381c6007504280c0f0400c0c042d4100c0d181c070703404d4102a8607120304060500d49040e64503080213215403080340c0600c2c0c0d100c040c0c070f0303000c0782d450312080c200880342005854014001d94916a4403c1c1c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 318817535 1250 318816285 318816299
    0x90c010e150a0c1e1a1302150909010b09030304150203040906030c170607080a0b01021603050a051b060d0203060301020706050f2e0e070207080f0c09130b0402100c08030906071701 79
    0x12001d00108641915100301249104198411b03a032540b507406840740f00c6c021100103605205810496010384140200f07000841c1800700003040e1340400d040540190300703060418441d004120300000960045100910002070402200d02819006502030369030901c0403403d001d050440b0142070103000d98550700c2a014004038540c00501e083d40000f062100258030343d40c0b10300407030038403124070554000f603031380c41e0008001e1240c0803426071790750f80c861011141c0c019419202c001048001c04900d03540160280300d840512101030700110750216000300014070340601592403808807038041d950f070390b5000444802c010884180d4a958081c1e0414004070000f0105600084031425070503000d4411840a80f2020031f00700c5000b0060540503200b4042943c2c1c50100f1820807a41d00c0c11400380c030620440900c4040342007040028041e0030801d4021080840300d079a15001e020b40070341030000c80403c000e900c0e024000400e104001440c080e103008800b0707001c1410702d02c20042c01c644540d4010a00d0b0070005004000e40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 318818785 1250 318817535 318817553
    0x180b0f0108010311030709061707150203030f180f1f1401210f0f0c1221050f040e04060f02040803071e06141e090c010e150a0c1e 57
    0x481c0d00c80c4409503048103004c00300c2e0074201241d10010080303042620200c0c004410792420111841e601044a284560b1910341c200c00804484034403000d6001080480c10102c0000100d0360b01480104260007030110760404149819401405000b0b070350450b8110465080101e1071240309040c40d44020b001010406948010100e0188030720b6560390000111001e20300304c510120103096800c5503080e0881c0034681041c0c094401d00890071282d4140741e150101c9d05400c45402003003260b03005001011101c1a54001c0c01d10400c0d0b070b42001c0c040c0700081c8a401a120001030042003c0c00c000c041c0c00a003803d05140101c00d40341400301c1c24041a005020501084c1c0b800020345103203e401c008100c189a90059141c040c08031084409081e072410301d071230b812065060f000f010b401241d8120100010032882e2465003101c4c04150f81e4655541c009100c1c0711a917600c038250900e40000010300382508500c2211a041e0a6889045400040340e815103100f02481001d104c2898020182401a00380b1007081d81c0e00450 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 318820035 1250 318818785 318818789
    0x130305031b0313091a0607030c0507050306011a03040f02060a09140607262a0f12090f130507031d03120403030c1101060305060603160f050603041b180b0f010801 71
    0x20941c1c03045180c40850205c501140c00b400d010300701568600e0341c2d0500908070301e0303524070640c1c032032040c0d41c80011907040000b00941210f101c00754110b0144001440140746d07070b00140007961840505002c4c00701580d640303001050761850940390603003214034004813041076024260344948079800c1800b00201084900081d8902d0300c1c0e20f07080f105c4400801141d011040e01544030152684105008604443d00080014080068902c4200c0d06030340d143d083c4055480381410740701001e800083c0310401e00c41c00c0440344541c1d10000180200000d030340401c041011594211009d20020781c4a00884400d0154629140200c020714400703180b0b000940e5030300c0b01d415400030740003c0070103030b1301ca60040e065449544450b45000c0c414000b03000060f0b44e420720641e14082511000e11074010010341c18444200c050845040360500c0c52054000d43c03034107081042a8100610135940e4550159081a20a007041d01890191200882004034102140c1030300c011030301e0f0256220300070f074068005030049170381100002e41 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 318821285 1250 318820035 318820049
    0x209090a1512112101060f0e2409060d0204110403110306010305060114012c01090501030b130515030307060504050709050f150303040812040905060603100911130305031b0313 77
    0x4e104465001c4021420044a4800d0500d5107030400c04500a00b841441034202d0b01d8441c0071005546502541140346548840c1403040c10180389030140361803c010210340d50040c2c0003401c1011283c656008103003512000f01084094143c00101401000110500042803075800e4008084941c110346d507072507880034103009480c1981d00100d2160070503071080ca0300c508035a402030310380c04c011070784521039260120303141e01c5040c082011603501080d2540f103031081c14020714008000500c000560313410f4800a2078013a00078442d42e480754100d013216450400c02400307083d20480380083d2524107801c05500344046500720311502402c00e81440107140f011307803010350810000c9090780d984403000d900082c41d40c40b40c0d5011140394054030900341201403008002e882254200c0100f844556510300810140348401c0315041180da175000c00600003840c541c0e00100f6260f030941d40c003d01e0080324050760003400007140e0080360070781d00002e400b01c0c4804400403c200c0d8410464019800c2200c41d1840300070040c06809124 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 318822535 1250 318821285 318821299
    0x6030c080a0e0c0607030314010b030603030406030504050c04050f0f1b0301060f090e0114130908040b07060b1504050f010c020906010c05071706010510050c0a03050304060209090a151211 82
    0xd245942d0034003050001e510000c1455540c3c5441d0300d0090054250900f6148201800c00300024030589600101c03481403d00601851409050036806c0c0d0040602510640300c5109260507142152507038401c260094500040101c050724028402405084c1c3c0103010508181107210710404440990041c1c0c5c1c159581d600f0513204c0210340510844043c2400d50014101c812104000100e240625501080d1041e00b0703100c0002400c80a145034059035001c19000b40080d00030441005050403100140100502c10200030505840c0400040d2481c58100c01401440000050030805480c2c07c079142c0c4142c4400303003001102901690001a82003000500490601890500260401c0700034421070010300321518440000000c05100f0540d599400d018a501649541c044000c5450041007920281031300d941c014403071040c040d130341152a50005001100e0f0b007502070124901c203507030b001b5000e48100880078000519100600c6442d0001116900c040d0b05150040f92900c00309800020504103408161140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 318823785 1250 318822535 318822551
    0x9130312021c0911041a030a06022d090a0519060311071509020901060203120a0207140604061a180604020f0702100e030d0e010507030f050c030406110706030c080a 72
    0x30303400c82560480007400c070b00c2c9010b6803002040202032162035001c1040e1401c02450f055505c5609004402642d19031b4568004980700700054500d400038401410814007456200b0b1909505400a1044502d2540c001d00d01040c6031003181400700a110080c0021901c12030700410002107801c0708840c2d0300031001019107031410558141c14010031110441d501c07002d201c4e128107007044000000e081d5820102e202c1e07481d8000000c0e0781c0e88004191424013002c91040e090680718082c221000354030200c070031502c0c1a2011000d0326a25001e100c00c602c44e07801804080389a1030a04190310111041941c41071003070131908a0004069000e0951684c010400d903001070b55404e00c1e60807000c0e21f00401c0c074000e501c40703c0200f241481507480316010004180586c1240d030306080c00601079400102134080c01b0b00088060000c0d402103403194400d4400300c1d900341055890900100006815a4040d40116011410f16482c4c84107200e07007001040020b0001d440c04000700c25100c10300908880b005800b01e161681c9560784 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 318825035 1250 318823785 318823807
    0x80a0c110607080706060b03060913030e090f180f250504150602010f1b0f0903050105072102041d0c091011010f140105060c03090607030e0913031202 66
    0x202038516002424180c0310311080c50015003503030100710100c4440f4248032002840c218140d0075240603180c01080022555034160400001481e0050f059080110746108020181c40740c0080314010000504480c400740350403000010303041c44900f5110100e9003d105040503100c4003041080150415650300823040c0f201e008807101415041d04103580c000d00c1c1103411114014000b100c5400c8644035002408417011045000f030454407058007c0181021044000c82060311606c1102c0000c456814488002c0303885c3c0d141d03907084800480d1500003140c07174505004410800c45800078412030b00342c9015031030b213800c1c00840c151481c7c890442486986032500494031800c1840c050790850100a0201d140115000038010203400308112a242c06511b0030100c481c0140c0c0b41d004004490f6030f41000d0045c83d928040c01c0c1702e403075400521408024041030200900030f9582c18000d10032a4000c0e0344400d181004502000022036010b448011100709086126001a0b00904104002caa5200d0016129100c50745 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 318826285 1250 318825035 318825053
    0xb030d021c0c1a0609070806090a020c0a0c0806011e0305150702100203070203032205120a02100608061b0310030f0f05100e0d031a13061d1501030504080a0c 69
    0x9000607800960019103948520080e41304080449900500340c41c1c5c1a82501c01083c01d13200650000e100f03400043c4085000d400400441c0310780300c1100d4880d54191255004400d55400460b101c0d08110010840c4401001150344c400c41140c481560312071541c1d42c0c0507603c3e00c82c8040c40b02d01514000018182c14001e1080d00441c41c109207040d5624070f0308448c02500c0c0d030300403101c4002d0342c0c500702c502c5140c0394100750b210b411003a808801070013409400800316038560420070b8203208510901445101004142c01540c00801000c0003c2003d8180004d092002c03c0c500108070451000502c10403c14031441152513080b40d07003002d000303400d0300c2d4079040c65101e4541745040601107110304222880f250105600031100d030b10f1401c040d45c030b44040318a070480603030b004184c0b1451402c6200d19410382500e05900544150030f080f00001981769601c1005000301141710320322210a81aa0040080841c0d4079a2084e401c00003d00e020031031b0389404d0b940c0f02d1203800348a10b81030404c40903140b032008001c0300d48 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 318827535 1250 318826285 318826307
    0x5031902031b2718151512070f03090f0201120209040906140c0a080403050c011103010b09040f0204060e1504080f03030f010f03031b03121803020f060103240f090609060b030d021c 79
    0x1e0300d91742e1a1a6821f03400c0c060700b030550f61200028100012104414407074030561a40c1540043c80c6c01c0c000b8042d400440d0000d100350901d424842d401c02000d2005e44c4c851141c522040d10a08012454010b1110014002000100444405001082940610f40e40214065030065140c00c10988646050304802d005200b02c41d0410541a800000403c00404040207810440300885e024000c1101b8510b641e0164000c0380b00d40804106a040440750500d8101c003803001f50140346241c0740c20a592a46040d1504821000310b031510341002060104000d00c03654039070b001d015400c0d0307500c542c2c03071556500500c40344020300341c1207482418416490401d4411203001100080b070140c00d000c000003a015205c100c03020140c3c118058803501c481d00e000c0c41e0022030140d040301d4200c1c030460200d0070940c0d110001d00079400803d01d10150340c2d201203003000c07150f44544100d8a000c0c180000305151a89003c1c400c88240920161213a403180000010300c640c00181600e09181d103043c02c04188040310000d541c146014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 318828785 1250 318827535 318827569
    0xb040e07050d2d0606140d110711090109020a0806042c0708010c14030115211505012c0f2d0105031902031b271815 51
    0x200e0303000500f652031000510a2004100250158945281000c00c941d0144905030204500c03000d51401210010b024045400004102160401451103030004503801403800f29110030000d103c603541b90410f441c801d0b001d404d584a08600d84180410007030300080313004103031a1060380c0714051024220040d007c41d03030340f03100d14400c220110707803400c3c1800b40c988400f030192480640ca0300400707401c00c1e0b2046449a0140981c401d20303c6c6140d0070014036010070641084c00c44d040c4444060124442c1c01068848404803082e144000355445124407040462442540301c14104100c100890708035008130b0480c22403c03070449201009880340507000c246451002c02c1d0659002415030a040054050040710031000c8110000036061003025100654040c0001e481312112061000210441c01c88268001c45e0065007016981c08403025034911426160710070204981c036280380251580088404402c11072180c40b040764000881c03e5007100d07404841d074008200a842e0360903580c0004442d11403880b00403a00c001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 318830035 1250 318828785 318828791
    0x18030d020d0204170a110604030c0b030601020a1a10050109030209070c05010b100e030606040903051615061403010c09141c05010509061506040522060f0906090b0603010b040e07050d 80
    0x40c01d000c01e841750282c0d1015101c240c200d9811a80900d000c1c000c44050300d41c000f10140b0010306000d280515504000c00d10303419442100705d0719001c51107822020f049801d94014031642440c0c40200717298001c0c51640301c241031002c1050244010780e1242c510781c0d40f01c0503500c0c24506010050030518090004000d0300c907003242a02104043c0554443e040d00702c8030701d0550490310a62580424081116030508001d0009501803001d061145108100d445006004a91443c940c10b80074411408644403940320026818190601c1180c40c1428040c1a01c5d0000300d00307010021900c1c01c10503651405101c22024441c00024045a84407170040307141c8482903811070700811252074100780ca20b81d0344206440d00003825010645c58001468504115400d58101a0190381072440ca111241c8825680d113601c0c042e010f0710b822002c9007403034a019903d4001d007400d0f0307000f01e02145481d40440448510103042401140c0800c01486030940080c100c1e0111004042d0702d0260f555818000c9401e401410a0282c1041c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 318831285 1250 318830035 318830069
    0xa03090201094406060105031f0b0715111602130609021e030402100804030c1401050709080604020a0b0309030403060f0c0305060102030304030f0e010e0409120818030d020d0204 78
    0x6506400f07000e46500343d880e80d01d10042c81c4a248003c90750040c40c40070342e12410028400c1e501c1200a103402c1200480000e072410310503903000030b0900c080d4115201100012503054144003201002849203402141d003044103080c07114007100940300d40c1840e0803a080c0100c00c81c904648410090b80001c0300620800c101840d150030158002c4e5021601401e00c45081c400519011031012046070b028030b03401028071500d90160308080c0d606160092080c0c0600c08581280c002082d44205a00c0e9111000000014180340114018060a40d1508000b61640c070000801006884207030400341941e041c1c102c0541c072035650301941071840c402d6802c02041a030501403240c00a40560304078003246c01540c2c4040c08280d8800e03004a959010858003d000180034001d01d814541c00740400300400304062608660784003001002c034043d40e42032017048030301c0c40801c0700c21030130700742d0002280c2c0c1c210048811020324a880601c41541c1d038000c150380b20052650009100d41911560750484008140b00c10b41c00500d01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 318832535 1250 318831285 318831329
    0x20f01170f09120f0405210a11040e0c090a02030a15150905090601080412090b0a080103050d050703020715021c05090415080a030c06020904061502210a0309020109 72
    0x201e080d14402400d00c0703010700c0c500f11140302009440032042070894541c2072614100821081c46001e40d00107407203400324280310088030030074030003800600d0081000348816103c4405020842c1c009001900481e00002060000395450080300c07030300400304c0200961203455202d195801400303403185111581d10301d1140010b0b00c2c049094403030920388843d220400140da13500300b8030103291400c95010340051148400140010300c10141e18000010074a4000d191580b1403804c44500d40c051032031030001c0b414200040041190401500c0030318103141c6071540c05c140c601ea40103980c8c0d1407580211100c40c41d16219602556108101c26100110305a40904c0c5420020f0306c054400d6206c110744034040c80c01c1801e840030410459480c3c004441181d8014060402036480480c0d48a505140c00c9540ea0303000c0040d02501d607618002c0724090480101078400807003605001925103540c3d0720340b921100d504003020000c0811a082583c0310a4460b01700030440300712034401241c12131981d42100c12507051205290b4070f00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 318833785 1250 318832535 318832561
    0x3060907030b1605030c18060406031d030f19020a080301120510060501020309060d0f1a0907170f0603030c060f010f06020307080708070f0609060b040c1704020f0117 73
    0x300c0c020b594104150310b5805402000c640d9800800d004964100081048080003600410035003503138440124102d01060b0006035a540a544003e001075149c2c40d0f40300b420950310302c8100301000c6440007035190200d045070065035401040400445440d580342940c0c80340e4001c0c41412400f543c0305400e40e81e20340c0c4856030307450308040c900700540d1144a12031f040d0803007000c541709802c240d400c1600118103081003d0300b009410b0b4805070701c510115480710b040200c0850580901d1007001152240700680884010a0002c00c50004100c1401c00c00340c452811000d03440c4080d031642084441e90a541c60382e903910082455845003016001071449950100200e10003504100f90584030864200c440942d5035480890380c034000d114010307103060010450b01c40058006c3c0010000203110f08000780681405840e08011a07840c100295005c549401610b00c5501d014450100c0c018100e0030092808440c1496400c00200000c0000703018100413902c04880e03a020303002c01c03030182101c000784e00000d142090202943d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 318835035 1250 318833785 318833789
    0xd050709050108011b110709020a030b09040609060b0d03121d0a1a090c060414030c030706030603051504050607030f0e0709090c0b031b0d02160506040309081911060903060907 77
    0x200340754006880d20810b206da0700d07a1011b0380040008011031401d0406007002580b1810001d02455510300d02c86506459510b0100e120714040c50002540815608115040e20240c03400a44101c0060045200207074001a0702c015001d0711180004a00b8803104d00e01042001c0c1c0e50340300700140318a071170309070811825468540010300e082001802c40d441c1d00382e10301d594140350741d034090780080244018440c20101c0c4030b40c02c038524030040803501c401c0040404a428107000d50480f030000380d00e410092084c010208803526594a01a0800c80c00b4905621007544941018016800b00b54840300550203400710707038010780c0d0946100c5c2d081e1505a552a4850307401080d5520040394034011076240020410b0ba01c4042e24130840800c6810749600752600c07580d48407580110700003403c0950900000e6944090341030f1580b1094414802009141090b040180c00d80111358480502603100540c240308414194604051030380d44069104c40346291180010000e019001c026505407065008100d42d0307040014508007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 318836285 1250 318835035 318835061
    0x5030f151818162d0b07050d09150f0309050a06110901031b200f030f0406110c060a03091115190f0804150e0d020105060112020301050f0d05070905010801 68
    0x495441d40030340c40288010361240c40b040c054032a41a005074484d0000861031226650b1501002644448402c1026000500700361030a60158100c1520250003102e9100501040c0f41c20003075606240800401614418680004040e242c1c015601044410028a04201c3c4d0080302846041d03d143d40011054200c01007040c002400c0984180c2a12580d9030300440350030403036860075202c891103080e14a84504082d26095280304151340090800c50501c06040d1503042a8409a0b0300c610304076009109038001e01741ca00300da40050450b0442961000222402d10b1000e0401084103ca1070030014003a014901070140c0080d19030880748080c441050050500e150880480c010103070108004071110f484c03800e41d070380210300c20b2130200d404907038488880390010402c00700c0031600e280b010340114104000d507101c17200076039102c4090118a40c0c000488281c0c022074a40114210741c0b400001400b480310300220180144042c801400a21105101e62030150608620038011560f481c4442c6009041c40f0007400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 318837535 1250 318836285 318836293
    0x1606050c07091104051c06050c0702040b1009140f370b030c0306040207050d0f1e051c0905060403050304110604140103050601110f1c05030f151818 65
    0x460300c104540301d0011000f902420b00c0342001d00740010b101542400c1e03052403200b0707980b103504c0a00180f0240240c0e8450111800075940303880f03440c0705000940b0300b521203062003130010714801d5451651040e8240d0844001018160380f0b18900d0021540500d11800030b141c01080500d00804840c0c11603021300030f612040e0071103150240d144030f100307200b1254900640c041608200301082e41d0881c05006581c22002c020001450311103159501464002c04280d1311010400c4c900b805245150004082c66040648070300103d10b03140038107402802c1744506040c942840308801d03038421081c0c440e5842101805d511008a40705400d00b0704000d002c41e0000c503011210801d400c640202e0301e0501c07400703880c00c50b00e11603501050140c01c1da00541c0a080000c00c804d04008420f030f1081c0d10760404022141c0380f40080c170081e06801c0b9481c0150765200c0340d04640303d01800010000d110701000d5040185902611106803809032642420006204511407040300220982d10300074440c1106070412500e4824010700c08035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 318838785 1250 318837535 318837539
    0x9081915060302060a0c0201120501080109050705010f090911130f0e070f17130c090c08060f0d080f040b0f091801030b130f0b0c0703080a1a010309051606050c07 71
    0x640685501d03000080d00a1402c0c400d10945034003944d605441c2c10310505150b00422005d01c09071040314000da10084e040e03915039403007070103200040c03082401600d001c1c68101e1502c54603001c040c041c00c0b000d10490701000c0e41c43c2200703085030b00b00405841400f9840c50b000300303020380c1e071320920140c1030303068007416007101d5081010443c050300400c094402152203458010740c056000242c580000c1004211aa010582d14600c07000943c0c2d031302c100c00241c030102c0c800107480090010020040c200052407540602e0700b90008115660381c208a21110550140e000c40e80d5042a802c0c808050140fa40b2040086c200422000000f6540c40c02410100d001034600c26040000c0115042c4040c00a10001c0c1c8000e15030808a2007010304500f50400d41c0707010f800101e246000c6560343d028a943c01301c6402000c100f0103d0301c0401c00da40f08034a0303500f04240000a1002400c010458804000001529414103940c0c4420f0307410808140240101200d00441c24000c444e56400003400e00d078044280c204050190000c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 318840035 1250 318838785 318838823
    0x1208010b0304051b0103231f0e011202060c030301080718140601120b0306040510050108060910020d18150516050301031104240e0c0a08130201090819 66
    0x5482c42150440300418841c0d104a102c07820090701e00b9502810182c40340c00031843c104002c1d040c01100301c481000303500c00b0300d0314030521618506005085941c04031b103c08101300940401e5039090640309a102010342d6102c0c58400a03081e03100300010013a040c0400b000008410401041390b4044840c08a51514904808428002110396403031540f4240b00140000c00c00c2540b03d281c04151021514000207240c5441000191a04500300c84c00c45284c2c2c001c0f040c001c0b00c441a401860f006206000080c06c09042c2003070b030592212102240e03103201d103901040c0362168407d02d4110210311200c0c038894951000c480e0911141ca49602c141c448121824000400d403280c140304c00d4a505c01c0c0c141d07a256811030b402e5070f998255a00464007400e03809500d13140300d07001601076500c1100c96031191007200d6004030324001400002410041014241e108140914400035801402035503002c1c200ca0703100203e103045440140c0c0e49031244d0b0400c055034402e000900502d0300010403a180f1450080f600f0b440d000e0700c0c00300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 318841285 1250 318840035 318840037
    0x3010504060e070c12050405061c15083f0a030b03071a0c0102130807090b040218120708030d0b01020715050a050a050c06040c031203091e0302010207020d1208010b 72
    0x1e002ca000030010001071300841c0d411344c40944400014680b4a1130280e9540000f983e81e0010307802e01b046e01c51004040031b8141c0141c428104a07020918424255510b0400110b403249400c0e401c0303429006510581c00c1e07080325407468032140025031038680c1009841e04051440340390480c145000100f46008082c02243c58005450001c484010800304541101c14954000642201c80801029902401040606406800040c005d040e054004210003403410300c0d0b840950301d0f0840007078082c920400c01e400c0e46403042c00d4240c2c1c200c0350942e05c410070307691107048491400f4000c1d030044443d40000300320360701e4003840750b0080c00c9494030076400c40780181e884132000408911a0321a90700803903010880038040601401c0605812402400c016042110107170645082c0f41d4221803c44400d40c607480180108086404200c001107410320341004000e0b500d955403010080000346151000310119040b004151003501224031195001d4000c014218041c40e00240b018100d40c1404003144013000040b07421300d1214 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 318842535 1250 318841285 318841291
    0x614131719230a060c020d021e1908091005040f0f180504051c0c0c090b0d020f0d08130306060515090402250c030b0c04030f0803270303010504060e 65
    0x40d14055140c8502c070800300c90000708041c4501e07140501119607001c102c4521850001031403540180c10403060689000f4106015101900006e00c1414000e002c3c881000031000c443d40345a032409004000349062581c0d00c2c0c06052003d075480b265460014800d1070b400800381041b1820b29000e1141c2a45031180d02c40d000b5920f000710310b510070805c2c00044c0800985d411054000e405030050b15012405e40c08500d601e00060000c80010400d1143e0355000c2004566400c00204092401000207111070b10015481300c2c04580064400d000082a00407180d036500c0c13003141c5d002c2d485683d26640342162030312070490b02220312082e2889840c0900014507400c0100c82c0078406150100c007d403a003a502402c2200a420440100002001101d039649184054034036002079a0300403180118541d01d10700d0710203140b040003032034250122428041040002e000041d064180755001032420344030750b1220f45250902d405031a0300750715958481540f032a401b41c040001d5060752402e40342030056607100c1000c00c40742c000075 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 318843785 1250 318842535 318842543
    0xc03080a050403050c030c2505030a030e0a2112020a0c0e0c0421060f0b101d030618060108010c0e0603060103060801050c181008010614131719 63
    0x1400051a000303956024560140c46410070b01e042450004485140d504200404101d580c4052030b800100c0e40082c00842140c0c04c0111800b10147c14a00469110b00c9070a0b002400d106c101014a412a55074500c0c000103810300d02c000c45400848103800581d9115221000c0d03d601403044021100d0f140302142e2044450341090048034000d103090051440b1410040000e81c00c5001444042411382d030800314448d2402c0004460348003c502c50800c04c1c101e03041c407445055518074080e00700d14152200900d0009007600c5050409044031000c2c510f0840441e1000019070500904042020300107032014140000c90002089412607a254410380782290110320b01140030940b0130300041020b00d4002c0085900c4041854040341c01d42e961000d090039104207441244185101150203420048031100004140c3c004888a0707251a80b8100040d00c41c0794180110303410001e11150354094009003c040b506540002c01c405840c1e01c0d80c8055003060340000c203510360501e0007602c0381c0035112820a5014404030703403c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 318845035 1250 318843785 318843797
    0x21806041e0c081e160309020315070305100302090c07050106080d320904020c0f1b1c1104091a0f0103140c030705040506010201060902040b09030606030d080609060607080d0b0906010c03 82
    0x24124000844003c85c245942c00c141e258540b88006841c00d00410740c4001a4684220683c00c0208028007a03a034020021644440c440004202580d111032a107500041e820000c103a907880241040ca0142110341c106080c00e202c1c1e100302840742d1354003c9076108400d0707401802080d002a910002405203401c2d008105000b4800e00c0403090526083e4020561500d81c041114004011034280d103042400505420040060300203007020282004ca0312103850004440c8000541d038015500d4450b84090500000c4c0980d550b04042000c02c1a41c1d00d8080d4101d1380c07000b0b800c1d141d1421581842e05540240822100000c25034071483d246000082d0300c1c80c100000401030b0506608107400d000061a00030031080c1150b40711300c00098030110718402072018020319100305517100c40d0b060070300d031906c90040c010a000b0b0b80310070003007118280d02c00300d40d030b80145080f950175245496040000711240654000a04080b20016856442041c658415a0318150a44411000da0381c1e40c40191f5400000e1a400703404509 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 318846285 1250 318845035 318845041
    0x4050f010804052e050f16050c062a0316020106050f030d1110020a02010e01060f050d0b07090e13030206090d1d040204030c0b04140402030103021806041e0c081e 71
    0x4580b400e4443d020100306003100340909032007001005c3d16401e03034200c6100e0120905000c20006865101c1d106660305003041c61030044064440d5596a500038801081400e200c1c14000030100e0180c021a007100341203590980300d06000d01d444120340340c0321401e00301540c6440c3d400034540c10100003a0049003401405007800ca150700358140c8403070242d01e004c4030142c01810064110b108061000d0100e00c4899030002940d0009419901d00b112110b4001e402000a090802c010540c1c0303800c0c140e00c02c0f6900c442051816161000252004186a00b088840006441c00c0100b51090b03900441c107824004e0f0308680843d01c80c0c90b24a034460706c0d52010b0500003000c24000c0c401c1c101c240c404410b0360002c080c1005150598988414586198079004101e81083c001001c00c8128160b01000c0443d81c002c8504500d1035146a001807180002e402426000ca80782c00c00040483d0b0701c0341c0c01b1009000e914400310041c407100b200d0303500091400d80910400f0500f214041a10068210800759542c480300d02c45070b0316a1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 318847535 1250 318846285 318846313
    0x801091107151401060c0b0a05090c011206080a150f06030305220f03140708070f0e0606090d1b060503040b0106031d0106030b01050f041406060d020d0e0304050f01080405 75
    0x62a41c0c8a481c0802c0d44444111102c01d03442002d044c002e15295075854504003140c82c00d1122001c01800545159007080d0074440c070200042041c1c4507900e005d0034681d0582d5185072182c000343c2401ea0041700b890046100c0ba02c2070041c0851403000e01c00c0701110420881410342c54803030890325503020180000d00e0501c403403859a450075504203854004007070324a40c0c2c0d0f0740d02c00746030441311420f4108849200300c60000e0000360303004010306006003010b64007500080b0b05000c5032145c0c2100500c90104041e2410010820a4541c202152421000079000b04481c0d126800c0402190000085201485040710800544644a00305880c0503e61050407040b680e464180c08034050055840326400c0c1640400326014040400d11460300110701c07520008003198541000c010b2401e60b1040d60500503801c01a10300d070704214841d91540e00810071a05680c5800040301494000d000300040a590a45802081940c5500000103801260412502d9091241350580115656030064030000d00700d0740300740d548031044 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 318848785 1250 318847535 318847553
    0xc0521090c040f0b06040305010903020106060914060315090a0605130209060403020415080a030c020405010e1e0705091002011b051606021c05070810050604150e13050403050301060801091107 84
    0x4501d840300415000000030005c0d003aa8815403040301d99a6403507140800301a02809441c0c01440c039814007803103e40c500640600060300100030107105010010001e014001d2958458890803000f801a94961510510f901c000307064038043d0798810111803e1403043d4502c180200c40c1d83c0c61000c0c2c00e180c1003501c1e5030f003800060004020203007460400e40e08003250303041c010401680c85900135691070418001d00d00600c022038406030000004c1c14541720170460034004031507500b5895619400d0b91002c40c3d88818044655000344400c03194000c031244042015030f03071f054001c07010300030300d242c400410349508803819242417003400482c0d01d030740540b4090348001c1307807060f409003968007980c2110b07911110480c0109000c03100100c4400c00420500380c2403000d107992800140001e00340950f849440c041c10104220141c80f0410036101c1040307482034502d006600c0c1c90109a9141c00005800c2c8401d0410f4a0040c0c080c2c0c10900420002994100002032040f802d0302030b1707000020b1040d005616002680d1585504 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 318850035 1250 318848785 318848801
    0x60f11071403040503031309050106021504080d090c08010e1612021201060e1303030e010e280501020a03021b031c0203060d050d090503010c03090c050d02030f010c0521090c04 77
    0x210b40402c0c840001d1a4a080c0010290104141101d4004504104810782128010f8120b00304560048003d4141e81c900c0004181c0c11030b0b04820701d50f44907006000004080d000380c540050960340222030000c0c424105400c84d06410481d80117403006c141514aa02070403154500c100498654040d460001600701000c042131000d9115001040c2a6191150840c445030305030b07480c0f480c602c101e48998091542c1407203540c4001d000400244045800041c0c850354507054034000c0301c1c811450b20707540c0701c0715000c20f00401300303107a4003034002d645070b035403100c030180c029003100460108140c452022444c0084022045070b4011040e181c804c3c21901080c0011002500024602e45d0002c9000c83e054012440401800d1101680c42c1d852145590609052500f562405040d2605041c28112014009003013040c204090302c03c143c84101d211121400000d1401501034180c01c015481c0c0041c4e00c1001c1c0c0d00c80c0040c49080507580942c003640c0c2e084103c0080204040710010110740114494a049217442d070000c4070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 318851285 1250 318850035 318850073
    0x1d1c0c02030d0f050d02030c0a0f08100308030a021e03010302030d0512010b0901030612050616050711060a0212040801090308060607110f0a050a0f051c02061905070f0b04060f1107 79
    0x4200175022500e04102d92041d0741400805c2c5010074030040309a40020103000386011031400b100d050401c0500902c85980c5e500000380320390b4011000580001807641610bd00608851300380e0104500042c802481360f0082c00141d010380201d58030000e0040c0508100d07007401d00d001040703801307507880d0500450700c40d00801c450504064a072180001d2088030100484030950044001d882d003402d010507402c100211911140051003424003145d40420a065140003071030006031103185d0785001540089081102005080e04011004100030465410550288815906c80d4540e030b095503c0d11401c00c442070056490081444403484a1042c3c0c60600c540c3c0840035032405000c480c0903039241d07000181102045d1300f240c505015014002c01240c948001008800402e0100c0301c0b05103402d640101d03005105526950f03005002007042c0d000c010f07120380704540b800c1d50031011428603540b0340d14108405a5094406031036042c20f201a00c0721801c424031402c292190f08840051414040ea40d0703001120001c03500440d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 318852535 1250 318851285 318851287
    0x20906030708090a1203020316030c0c0312020d050108060708090303100311030c120312010902070b06061312080304060e06071d01170a0c0215160509041d1c0c02030d0f05 75
    0x14001070032807490319220041e0b1b9100940ca03460300e014541110700000b1409010903003040c00741021250001c85103840301c0c0d01880c0000d1104146000f15000c2d1007408a003000543c900030000807035150100340c07071780229525510489039854241f50300365a4002136070300c0f2807450700c0302c10200009180b11180d03010440001e416a86140c10401c00200012511401191150070024100030030400c1a2501805060707094400c5050003426198040017400040c01c0c0e074011200000c030421980b2020040b540200810a0340c082000b081d0301d880d00046d0000c0c0d03011201c0398101164072030061800302c1c65500c038100c103a5a5603051503e13180140500c100d501061414060550390b68000d01c90640b000c184180d450510101d04a0400c0b88000d04d480c0c10705c402143c3d01c0e4040b0040c001400c9942c0f068010000305890700f9610b0b2122400044c2c024400e8000c1490000080d00d00404400c5001c43c2c080d00c80365003842c0b81419203441800c1562400004c2c00000e41c1038000c1c510fa400072034025001c11020488500d006 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 318853785 1250 318852535 318852553
    0x3010e13051608010c140f090a0b0c0106051005181003020f04080106080606031b0f0f0310050402011b0b061c051219050a23090613030c05010302090603070809 70
    0x2050401c0061007156a46040b00c1c0c4080c80b1181c824001d03151030011500d801c0080c0310f058401b0841c20f003d0820208820500042c1c1c044441e5507100c607000140842a444d1680e44d207500000354001d14652140900071080c410519804a0081040e43c40c51850b421400c190346c0c424408003c1040e59500084040c154240500d00c001c00300d407405400548841e9000044050804d005c280c902100102224425800a0000038070088111040c16890800341c1d081c0d90304a000ba000600f009038601c01a035003511602d40c0a501c000705a420541c0224001c5c1c80354005c2405e0304e00c1001044119520183c0303070100c44004981281441d10b503440c3d00450003485122101c640c1c0e52183d0420a15014200c1c0311140410f54100c1c0c0c2ca8080d0403910307846890b04103c0c0c41c0c400000000341c500344032140c0002441586410346e140188901c0d00b151507000004084a0759107042002403030714289280016181400c0e10000401c0342c1d4021300c2119060100100804d0031507940b4082200c0032900200803189500410b011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 318855035 1250 318853785 318853793
    0x4020f0c06100503011b0f0c060903030b1e01050901080604060302040501080a0b0703140609100e07020d03060f05060301210f0b0a0f0c050405060f040f06110f1203010e13 75
    0x2804501500d40302070500c5040000788403042007030390f03007140788264906910070440c9140c80c1051108200c46042680c02c110b10114182c0f05140b0b04800608910b0406003102c0802da8564407619000c0421645400e51451101708062029015900c89001c1101007010000a6006130506584280d004002141c0d0b5522507021a0580740280d000300e07c02d40c0a80100c800f0040c0c2a40304aa10524600e001c002c607002c0030f094403036120400f8182901070070340700001c03415001c41400c91802404016141d411282045030009540341c425003c42000a4a081c002081c500d0380a41c17540c2c01c646005111a04590074841c00d02441c0400600c2081490706012040000401680380461035900440100085141250b0342005880c4440c5c102ca40365450b00c50344010154024003030b2416554162225074554040204040b4517200301e82043c483c56804c02c80c0040d071164021084103500c4411815112810702400005d545d0381c040354039111075000b0910050190820364560306901069254200303820a4070740d15 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 318856285 1250 318855035 318855037
    0x703020d091b0510050304051005041b1e060504150e03031309150b13140607060e030304031404060f050a14070308040c1a030a0b010c0c15140408030904050604020f 72
    0x4181c042e00300e080d80c81000030345840402d41c03d0340011814007902d50300c0c080e075072141c40346e10401c00311f00d9183d60344010030140002c1c5102003401c2000216840c03801900e4265040c644004840c56110f00f860041020940300e10071816241211000c1c0044841100d00407000c0c2d6050861030020350b014841070110001941450000c40000c10084000140489841191080240c0103410641c00b4500400100743c20150b01c000000841e41d804064605840c0b400001034114408c81c01d0182507035052400c02e295900c0080025409180f098540681d600361302c0e4110140340c05244101e40100310000c1c49052a00d0041c40100b081071102e240049806c101800e600d404c40d0409401a00010301d1241041b041155480202028010301000c45000e114241140182d911004041c05c1003e515407607241c03016401214490511070b848003160050303d44038031007101c90b602c80860150001c7e0780b5041d0058541c2082c0211030a40340004091490860014107000c05000d010340003035000343d0b08101908031984410 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 318857535 1250 318856285 318856313
    0x3011406040c0e19140a14101404081b0306060d080306030109060204260304140607050c0907021b01170f09100f0c0201060e06061606060503011107030314070203030703020d09 77
    0x1d40d071034080342d04007000d0100401485d4003040c000d07944a8414029105010386a291040d41200c40030010b80303500c0b1007155041210340c0b030124000070100d004100710703501182041b903009000481d0035840d4009400c15940306815036880e904003c0000100f8041180c29000b541e002501900204241c1c5550b6910022a070040c0d2001c445005540a6440c020008440302100d08207034100450401c0d00745030b100d001c0600ca1110b20740c410140010040c0400105004280013448000e1445059181020019441c0c074681062705207100714160090b0415070084040c07920901d548100101035039038640310348551500140403042c3d04c0c4074101c41400060321030700801e940395442c4800410005040741004e429551290810403102c020070041002c0b41e01c2d40c8050b034440500184586508154a08082000704801d400658040d4203000991a0042c2d980317006254041c030a40d820003210b617a10804a140010903075a850058008001180c0031a1013034014002c00e02034114000b459140c1c03036031141003090f00b074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 318858785 1250 318857535 318857569
    0x51606080f07020105071416020d0503040f2106180c030c180e0c010f050d060f030215030402031509070b040f0815100302060d1103180c03011406040c0e 67
    0x328042260392000d42269540041c0240000d01a505100d200907100040d1400402d4680802060303010401003440214444540c010f8200e045c85907060900036244d50250007458000d94000100092010f000708142c5038524124010800c00d02c02559000e0141200e80c4402c06020200110080841c8034010311800940c451030040c08258030380002090001c50000e40441010316190304100403020108250302148800d180560100c0503140c0152600d0003010025100f46203031034404118441c0b01124841a40d0003200c100100940301c4240b017205110440d4001c1d01904200b02400107182c100b00e01c541c000144a0a640085460b000428410341003030744a40018004424104045842441070103000c1e08180c5054000f031a002c0f0028a410559100082c0a0740c3c00260050009503240d00000200142c40d40c00340e0340b030405441c41070780510106580303010b5002d2480003000d00e2405208102c0003486d000320700901e1340e542008001c020051300f4500b1080c801610340c01a032555600111403200504 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 318860035 1250 318858785 318858797
    0xa0510030b010e04020a0804120c05030301060f031a01020a0b251205010504061a0c01020f1b0606090615030a0b030a03080a051e160903020a09060303080c0f0f07051606 74
    0x80d400010b2440c3c159401403030055104101841b107950f48081c4440d4800d40210140d400d03c0764601040f2100844290042c0503404040000310f03085a0040a90449030b1290307409001c142c075011062034014912252050140c0d02c0380c82c0c42000101c5060388580d20202001b0190100c010b05010380310200c5068131114000380b810620740542c0d5440384189400740006950802c206410a000c1b075120249804001220030f9001c40c1012504c00c3c2501258101146c0580c0c1e00d85443c80d001c2d0302c3c0b0781c041c080c80010354240194070015040307042c188040d80c41003c0007807810a080c0802d0704030710030b154130140c4a02d49450711804489480c0d18100445171a42d482560347c18002d1604000d118100c50002e014101c0170710040417003c5800800101d126004140e540d070103440030440a41c2515400a140d000a40105a148ac0040c00c1495940107100701e031300035214a0150368883d5140310f02d0784200117a18650000c28841e0b900789601c2100607242c0e0324496421070310754201030703080180c40c0000350b4011000900 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 318861285 1250 318860035 318860051
    0xc1902070f0b2d120a06240f03050f0106030f09061d0d020601051f0201090b0c13050102010216290f0103060c0c03020717190515060604030804140a051003 68
    0x1820018030a0b079503c40c504100301c2c841404501000c0c0d48240700f01d121410910310045020810b40d036000f0402007040002081d14003400c3c01403400364034800018580071030340801e00501450300a00030380744a441e0f110790700d040f00da0030108240c0c0100507101211896580ea60071640001d0003a104001040b00d213050400c0c031103602c4031009031605498030a00e00454010310010015504c400500740c2c134102540340c1d03a103030008440b5802c1380103046089002d00002d13062028000125114002401e10540381068100c0854440006a0903449140510030070282051400d2020500c2c0c609075408400142c1d0003660b85404003804005980350a5426071890700c200c41c010010080944200d000d8110541040c200c26910b6442c040d4507081d05210300600c00d85a00100400300806200c4407402e0030000006442c011881d040995030b0f19800c520290540d203141c40030030402e1401405840450341d0080341d07903140904008000c0540c0390b526403000c1d0054440d00012035990703034407400c2c06400c0220b03543c0040c7c0b540c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 318862535 1250 318861285 318861307
    0x1b010e0f0706110303071b02090a090203010b040e030412300305060a05090f090f0a0c0816030b1801060906090504022407020d020d0c0303081e0c1902070f0b 69
    0x800c40d9002c1800c0c00002409141c203a007000c4141d0360b00a101b410f006100700c200700f0281807045d0090310300070b50241d07018003040503d01c016480b0034003950090340200a00510142440102d52100c0c554210540c400d120402c60f2110f40c0c80542d096230300c5845286803480500c1c940080d6294820b40391200e00b00c003a010300203865131500c940c0340d211400702e42d240300c1c0a14010118040c4c02e00500b400c02d0101c4110b00207070811808005091402002400320b840300002410308845a040300d0007800010b00850200319084504c094642040d80d801078882c1d5680e444000d580502000c6d0203560305169502c4000c001510001c40c4034400041c03400f80c03c04907151034244100000c1a03603d440c00820812006150300d40c0c42026030540b0f11155040d94061042107980c00010034000c01c10b500140900c101e00c04c044105035108250030f01510716000c1424000101d0b4809104405080701e07401c0c403403401441075881c810305450f8000f468003068010398240c0d1b41c5404501c4401e000c190000c44807048000b4a80c0740b05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 318863785 1250 318862535 318862543
    0x150503040311150c0a0c0209280b1c0c0806070f0f030903120c0c020a12050706020109020303070209150405150a0609050f01050304031b1a06060a0e061b010e0f 70
    0x41c420780c0703016124100880f1008240050054002402c00c1400314000740d18070b00890302c80f60095002400d1035031500d40421545040b40f2180340325081c40c62503020402d00b00c02c4038041c0f15180c1c107001b014041d40b948207891111075502206019100a183d00000040c03410003882100d005100c607945080400040c041c001e41180c901c900d1034001c040c031b082d400e000440c1d031003844100070381103144c0c010860790105541180c1c40b110704000a5402150345400240345e80704074440071480c034810405d440ba290750301c7c2e605900f00d40306244080d4068004000c428010300e40030003481c0d8042c0c10748064010003101c140108049407012920602c0e861003c01c01500107140c010064401001107103000310407e0b0824022a2102c1011110241440070220100b030405024890500c440060b60400071212401c6041904514494482444e0540748400200b401410b04604030350303900f01c441d11000000b00b103a0040c80703200da1010400040c01c0d540755031541c0104a00b0701400c00c0301c00202d001082500d1008644500b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 318865035 1250 318863785 318863807
    0x11100206060120070509130b0601050307050306040902040603050609010b040e16090e01060506070506041b030f14010e010e06010e070f021e03040b0c0102031e07091a041505030403 79
    0x150340c005400c11201e0b0ba800118801c0202c0d0540290b0109a6110062480c0c50b420b07401c01640880240d003081001c96601420b20362a6000c0c60780020075440302da00541b101e00c000d544210005404000150306d44c00c0641240000e07502c05400028101c0c1d0340e41b661800c0000965a251041e510b0300c0544100f4541070141c1d07812030000038007401e2445c4440b014040201d06a1049498a80d2204074040c4080002c2d48a0401031401400581e55018a850031076140c0b003084070201c0c1c148601103500209900d610090003b582e50007080625084403640f652641801901a140d15039903c1d2212001540030a02441006003a12001858076504222104406080041000c8100b1003000c0307030100100d500143c0081c07007280c00c80c0d21903c01d0803066021344c21171103140c00c00000301e072000401d689450301c1540194030a0b514160701d0004100705d4210703007114107020b131850340c00926602d00038486a860030181c5410701d14424581490030350f840c0094411000b4400b0040301080002c0104010703d5082100194 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 318866285 1250 318865035 318865037
    0x131e06091b0305040203010e03041d09010204140603041b0b041403030f090d152306040b032e1107150e1c051318060e01080706050f161110 61
    0x10940c0c0c070041211100c14402901d0405407902c011506544080d0f1082c80718000071401d03030b0703581c540b10402003a0500545d021004400300c44000103260302c8040c42134170f080da6240700500c002d0a002d2820081643c001400968000c1a00305105c946c614a04103d03000030b112042d00e498443d0b1a00f52101a03011122081741e02030b030820012010030703080307520807100b040400f01c818142c410b00608010651100d8500410b803002c1c5014400301212842440100031203000c03404442e11a65148184000e464a80d1410382e01640003400b00c01d411004a80e4440450000c8505070544d011282d40c1c50b815202d05542184035008001402c00600c085000c20050240841030b06014422072178440c0d0356131300b032003020800d50b005001c41d070f550415102f081200c1e222000c580003122540e4403241d4075400701640f0740c650100b5a142c400002150301d03003201304034101ca940a024003500380c60040241e0b246e9000307649200101c2c1c400c20188086143c0c0d2040e88034058092241130030703860090b02c18084500719541404d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 318867535 1250 318866285 318866291
    0x2010c090e040b1f0b0f09090105030313060e0d020d080a02070e0108030a050f0f0c0c0307080d09231302180f1c110301060303080f011d07050702131e0609 68
    0xc55075410006801c290f190344585104ea819401402440c541d035040300000083c00a00d5100051030140a04189442100d280c55143d81c0c41041654911420340b860148003e50401045910300036600e4035803681d0083e01d40d1042c8220756000401447c1f018130b0850300700501051002c02d540d4108035560203024500d51481e5954105180c9075030324054821701d0310401a0014900124002ea00245c0e00441ca00c9404140c582c0c0303480b101c841d107075000707006600d001f4490040006071105001400b074480200341d40707035000c2c00390520f032088000801110041e00300c0e91041d4011520b40c0c503010011800d0a181c19001a02e4407400da00002e40302400d40e038403d114000c00745686059603104a1800d110644e05e0601c50181005451301c810a4002490644d5265291271400014541c01103615842086088180003c1d6a00d407004a10500c0c030b2080342108150302040058883c0d405040100300b201d00061407583c00018941c8041c0580d03440300804c0c0c0030710181060001c3e800c482c6d0700464018141d24003080c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 318868785 1250 318867535 318867541
    0x801050f0103021e040b09043509010c050708060403050310060c33150501022a061b030415030b0321090607051002070312050906241002010c090e 64
    0x6000b031840c00601c802c4c04d903103190500310310340e180c0e48020102c10001c0c0001c42d03140b519050007030400c480c1480c00351504400e4170b0340c1c40c91400e001d076504510b403020002a60405d916940115122108060300715000e100d510008110703070808001a038840e80c82a43c5159880c80c1280c1d44031071541c1d690303004005026001400c0e400040441444682e07107403048600341080d10303042440240340c1a084901410301341c80d004901c0c2d8031660514000054030000c1c2c00f04d0381c10a800400580050034500e0501d10307001c6828070464001e01c6d20200804140031044024401441e0355031640e402c1d0341c000e91056015106c40c07055420910341500410030006811005820350010880b28825040d005030500d1810102c000f9480d121030b51580107884181c2e4001044580700008c11080724000c3d400003200f40c0c0440d80e11100860305034100e0046512800382d01000e00903030f445400c00ca045500c6c0c1d00841c41d103a0012154428581e4030342d07213140803902c0880d500210700c004100d2005441d201041d08542c011948007010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 318870035 1250 318868785 318868789
    0x4050303180c010c080f071203051506180f03160602060103110102011a0114070b0c030708090303010605040329040c030c06030c020c130204080a03030b030c011d21070608010801050f010302 83
    0x9141c404e500003014941c2d503283c0c1c18512440d445041c00007030901e11250802410198036034085489075040c10710440200c501181009024000c1c419401e800d01000d41c50040360342407082c0c20600c2c144000d8203d8001d900240c070300d403080e510940c02000060303000c1001001481b0f04411110307203844003070008200c040b90100c100c4041c04142c090450510035040200c580c00c5036a038045601140d0090b269840c1401d0002a1b241c0c035a0094424200048060300442e000c198040101d078121000e07500c80605d0a85587c2d14012410103420060383c12034800b1900d072000300b60668031980708910440710440c0207400c0d0b00e030140c0c4580355900814101840c081610b11026000203406030f9414044a26140c80e0840320b1021029104540041e0f44a004060410341056050b0704a002014001c405941c4400602c400445880e581c84620024601c0000300d0030341e181c18031052045011344901414490560301440d802e20744030603648940009508a070041110410030700c41c640c1c001240c220103012552460300 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 318871285 1250 318870035 318870047
    0x1030609050408071106040b0c15090102040b0a080a09080f030712020c0c0108040507090e1e0309060a031a060c0c030601090b01020c130608071202010f0c02010914040209060304050303180c01 84
    0x10040c440c01145c0001c424030360b41d40342528024025000c2080d45c442c20080c0550716860385e00006808191070340007050301c84006000341d4060b9443c5502ca141403140c1e80710111401c1001509008800c0e03921070610303000c1b0303810718020030b00c90300b516501e03030360300c0c10481c0c6e0007001410b0141d203c00c5050710500602c1582c07030022840c1c0d42c500d1400d10781038400361030b1805d00d1400d0481c91ba01c071404040c54111041e22484011600d20707100c80c808104440001001220301ea00c0f8414866200e40c011810002611014040d80c00014036800103899801110304000118505500407114403482d6031001c841d0868a00d400c000c1c89015211401047c0f00003000440040d6941d5007104195100d00c3c2403030414200b54072a548070f8002403592100304e8075500ea6490008005480443c01070b0b0004203e00103008140d4002c4580c0d0104940c103a40c0c06800918002d840c1d1481c00d080d15020382d205800b00000e0900b90361b080c1c091030081d4002c5014640d64100700d02a8140c07280360b01051203080d0491300c2c9541c5260307086a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 318872535 1250 318871285 318871297
    0x3050315010314131406131502040806010e04060e010c02100f0603020306040f020d050106060806040e0609070302060d0f05100f17030f1803240c0715020f120103080901030609050408 80
    0x11130541c1140815240c143c10f4420b070340300030101d18852802000341c407170014020002d0950080c1c0740c030282c9501e10707030800e016842580038841c095400000104030711094104041d40c00385c06000001000c84d51070500f5425074041c0400f510042e84032203100c000640a6215030052201c0c148070800c4441d00d5540400e03280d10004001801c4092441070b400b00b503440d050920203040794428000c2040540f40d01c000703421080141d40c0c1c0c0c0e0186181c9502c0181c4100f00203051401201c03140001d00d2418038603800c018080c0d22031800d84100980b41e03018003120503411301a29004900741d8801f03000940c1094444010040d440c2c0c41307035141034005c50a10855003004811155000c00502c40d1a985040300c00f004a510400140d0383c54141c400c4402d05041d0109280d000b40e80513040101100c1070780c8551402c40401d005811f030241c0210521811550140307860b90041031f22079015140b02d41002140c904410300c0301002d03802074452602c001004a020742c3d041c4a100e02401a05000300030701d081c1500c4099840c0200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 318873785 1250 318872535 318872551
    0xa0608071e090f0615090608150108040b0703021c0b12011104060c050a020d0f050d0f050f0c0705040507020f0d03051e040204060308030a0c2303040b0705070f03050315010314 77
    0x40710100f4215450b90400e001074a040d010a40c1803180344e03040280302c04841e00c40c80001512a07070101c0c00c0720010b4464a103071a10b05030755599140d10355890b0010f011802400c00c8003416030030443e00002480d40c1c02c00c00c00764220b2110004850300e0110502601240c01d2003940c50b16407402c2c07600c0506e503d08809a4040e66210318007203140002c24030305940f415041480180d841154a4000401c2006030081c121084d80708105480c4125604182034417054161807000f00031500134000806403d80394005000c0c0a080a011642c0c0c103036480700820304990058482000680210b025035000200800042040745a04e01c0c0402c11483e005606902081c0c6000e481003001d201c0d40007280c00d5568036040319009e90340250f0701070f907241003034800c42006050340e86202c0003081004418040034545100340c4441e030080a403485155548958810404410091038a018090705200f8200414610303044e00c058548280c40c1c0d9950303070034903000e101c40c00e4001000031410141010030855061004040c0c6641001030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 318875035 1250 318873785 318873791
    0x71d0408031609030f08030601110109080412022709070b18010f03091a010503070504060e040308090f07060306062a1203090b2706070915090e0a0608071e09 69
    0x1103210200c5440055610140141544407203000a011546c4025409210240c90702c0e007604046002040c280e42000744054600721040c0400c01c9201100d841c045001403000b03141c02c5001181c40915468804600011903c0b0004a010000f40000800440c8054072400b02c010f400c0a0303840c0c0804407100800b02c24103040004600c40c0c1c0301e18500980085044903071128050401846103202428230030424850607100e07124400d40028141024800c120070769441c101000030f41c0e0f94039102a5040403000d40054404e10592460840c61503052080350040e000c0307594089141c610307107100105560707110064014590740220040c003140350b0844400060b550300500303624400e0640f80081d00100032808014149808440030440b002540300034460100c2309019000d0590491154142d589440440741800800c40c078040910202d910618412100d8000d485c0c00a1110345901c2c9064400c017041d902510fa9076146c1000f0712481405110040244c012800c43d0004840841600b08046c109840b0744c03416240d03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 318876285 1250 318875035 318875071
    0x1b08060105060a0504080d020a12110304050f060903100203100f0501021c030e0a03090801050a27050705040207080a3b04110c070f0b19080a0e0f071d040803 69
    0x1014105441c006c0c04004142c64072507040f150065220700d0501400c41c5c45014036034403100210300980440c040d00240742c0080d8100360408060090381100e0a80d16580020240502403040c5d030100542c0f518811a900d0168680c1002c4010200d8422950003490810f49000710612544e680028455504000d240319550300061004090b002802d00242106142c0142038003c8141a08509610b0458190754001c2150f961444009800c0318103c0c0e040404244040005224840030721004100442c000e8043d40d1003c0e5413000040c0c200d070f008400442d40040045440030b11190050800a281c400000301204008400e030ba510b02c0e28855640c2c2d01c4c000710a08900b91003aa00c940d0712180b0310081c0d643c4c580e80c0e26040c00b1407030743c1e5400b003901c100102c0c0c00c0b0110000c00d608030240c0c01d030790b40241014000e58034581d40a0b41a10b04a200411806090f9915070201d403050008010055907003141c4005042080e0071720302d034404c4404104880714a088001001e00c0b000451100c200c0341d0002074200c40c80d2044e5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 318877535 1250 318876285 318876287
    0xf0318030c03050702012f150106020c010c14060403030506101e05162310020a0f0309030c150606090e0f01030f020d0f060203070e22050a110f03041b08060105060a 72
    0xca508059600020035801f10714034004090318084149203080c03044407004200340c1c0500401c0d0100b40158401a00401c914907960b501406140d105c0500c40c0c9100c040e400400e0703007140e260881c1200c081e40000d84801c10706c191030601d4614046000c5052505900006403821020707d8204c0040441007041030009040080c031510500409000754003442015140005005464080300402d0000c640340c003881042a0034518a0700c01c43d01c205501d078907000080d48101d00144d0090820450940520071146035400025001c1c1001c6040c1113420000000c1e1142000ca004141034483d03041040460b01d40c0c003e200144412030351850440c0e603c0801c0c44004111840450622061840c0007800e400208040c40104801e90300910711601c0305a80343d40b11004400c04010050202c031221b600d141e0114401c500c4909003a800c41944003080440c0072441d15848034404a02e41e000201c0042a200e0100c10301c4104400840107981c03150900f942e0720440ca041000143d195a410721400740b16220025862141b5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 318878785 1250 318877535 318877547
    0xa0b0d0207200108010e040b04060515090a0c080c040b0708090607052a090c07060c110a03080a05010605041a0a170103050a0209070504081905070b04060f0318030c0305070201 77
    0x40c5038807602c1607080c10440300142c0341100150301d1040c04102003d0010814056002c021032055400c038140310003c5d102c9490f090f00401014020600030b0a0048105600341c60381c40400b4002e1205410000c0c0301c41038803e008011810103440320185910401c0200500c2d00581d050310300b61900040d45694030004100040d0fa5445900070041160050411100d1a001c03890034100d1f03020706850345030851891590401c80014421640660004014804000407940c660b01c01c0d9407603045401c1c120440c44480c0000b40c034100c40203204600280030350341007064a904d14020740340106180e01b8207908040c14640803007141c082501d0041080d0401240a200c818403810444c0300340401151180ca072540c4a052064840d6034054050380510712800101d5050740c401c50480b82242c039010080c0c01c444091300a10b85012241c08026103107807150810105030800f403030008000030701160321742250410840601500351250030442203c1800380c0b001c000046500490030001c81545898050b980c1c5e1194401600c503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 318880035 1250 318878785 318878797
    0x1140c220f030b01090e030a0c030302030a0905070f0f170a0b0c070f08030a051501050409200a090807060302340501060602060601021203041106030c0f030f041509020a0b0d02 77
    0x1100011000050100004031039042e58480c179014880c00320b080640300c0c0c0d6442144001030004042274459000f0900c01c1d8040c5812a001e494040340e41d24031070b202c040c0782c036042c0e800c5030000d411019400c000440816440c0d40c01400d0303400a9140d04200114681d4441042a002804224181c40001c6103500184100c03070209501018880710718001d0704040781700c0e81003114800340003031420001c00d84b69010001c0d00101e001d0146c0d10140b51a04000406001d0800c5981002e12100700038184095154100c0180500001076611015064030700a8091715180c8954803600500d4030400ca081140c112a22946540380a24514440b07440d200e03402e041e03546003d17282c01510725480d040001c10410750100d60a409244264200c0d047c950586100004522040e10010030707001e0103002c8010982419400740d580034105054142c14419568a0544542e000b00d030212200414042000100b1100700780c1c036800200310300c0c81000242d0207a800301b030b044085400741219400300800c00c400c8451040d01100c1c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 318881285 1250 318880035 318880049
    0x11203181502010b0a080a020d15020d1803030c050309070b0a0905060c010507020105011d06101b03020609070b0a0f0305180f030409060902070807030302071a0c0c01140c22 76
    0x8944080c00080c000d1213021a91071142e101c02c00001145100040c03001840780d0003e141d4511642e0b0340e911100010814000041d22a40910200c5c40c2182c49100300c001170f003110145007d419000380303402001c44034182002800c1c00000e0040c403a50240014080080d546420710f030b1a0b5600e4100404d5030039000c503510060340241e00003000341410b1010342106001d006075800a21250340c030b500c042000e18a031010311003000a9181d0001d108c51910060340c643d100d02e0390500d0655010b1a03007651300c0030042d002c815400341c0e00c003500340b0a12480c200910402040c2c007025082c14042810002488090720007030707a42c20107486030003151710055501c1003d94403580140480d0300e00c020710b00110351240c200b8418030000038034092001411901a000f155032403540300032040d00c0d22449036415002908140019100307840c454443c2484840c80b000054043c007204000143c03a01c1c42d0281c105d0944010301c1440c02d020620030180000c2540c20030590328030803041d4000c8036160f041c40300e4441000a26500c801 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 318882535 1250 318881285 318881309
    0x40b0d03050c1c0e011d150403031704030503040b091006090f0608010b03250e070801080d020c0913031101150314011e1802040e010f0e010501120318 66
    0x10160000002d040c150807500907158040054000c1e5107148115042c00d0000c160519200c24556129001708408221402241d00041c408140400c41801c00d0b0b2802c0c8182c0703100010b0900c240350b0451140d10701403002031184d0840d4a03165070001c0031408050001080c108903a4089864200d0a1102140c1c048014804100c0c4c6903032034410304017030151740314501c4da058942000401c0c21981030040c65144003014004084d414802c0484180201d420144d820742128200d0020403001c50410405000b0903032942c8a40300365052174000c80c1010041c042000941d4007083c402032294880c0c406007580310040c180458448481400c1c02e940c00701860440700d9007946070101c40d040c00380f8101024001d03240520521304018814440080c201c131f03081518459004041e03152500100ea054100ea116613210480e2504c052203168041004d4941070514500140d450b400100c070320780a280301e403000e1800304000a2045500d0440c0c900740c1750845440182c01c01040f449148030700c2c080b02030288020200791102c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 318883785 1250 318882535 318882559
    0xc130510050702030a2f03031219020c0601030201030506040b0a03021225030c080d020c04021605010207050c091302130b040b0a140310020c03092806030f0b04022106040b 75
    0x942034609003c1095400854186c2c0c049107500303402c0300c800e61203a00c0900110b241501403c1e024944401c003e00c03165001d5100154412802803034001b61203103401c1c120091486504620000d8141c510040803a801a4505403054107a641d603d0414411a901a10001000e228115440f0f051840300f0030000920740e0020030003c1608140c4c440441164044d00180c1601130f12141c07415281d1000040c0304e0010ba0285220209901d0964010b08141c19040c03485006a0b0040e03031842c0c26a000b080702580d01c0d8021442010071820001300c00781d809098101d40d030381004540e50000d21000742076203035851419510a461070395901c480c3d10000040c0001015034050550769074a4408484205000307034064080c021410403002c015009441c9058031401c059800c00da210024810364440f000c1000c1c018425504266418501e0707071070280050012940e0102d0200001c0340e0700d9042d1585500205e0003030380f041002414481032441e185810454841e070b6940d0320740f20003000030080c00c00c1e41d01041d4498030b80080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 318884892 1107 318883785 318883793
    0x10b041e2421021003050f0601050901020a2303030408190207050f060904060b0a020724020706080414010218130603260c030403060e060c130510050702030a 69
    0xa0400115201d80c000a000641413409a000b0030358680070721460349401c1202c65402103081c00e010b0b10b00074201000030355801901e031000c2c00401d500c1400421041020314403614103020392003100d8490915003021001c2c0e6008182803c1c0440d40d21a181a0450000c00c81310700b1a103000b000180240c0d0010f06100311a4031a40a00d5402503880b0808104012600050514400d603540100a0300f4241580c101030a00c86040d090004448420010030b00c44c2d0002c5d44c001074500a2904100c00e40711441c00e840403104c00180d1600d1540081600d10041c800c454400c4403611044400210340311000c140c141c00c59020f03000290603c0003003c88a2011078241c0b0072010744040d800451403400214010860568100760021180c15895109010103580100701d255004400400300c80e141146c54102c00d056404203108480c001c032074803900c10b02414001c10644928070380240c1035410a51403460 = true := by decide +kernel

theorem cover : BRFrame.Cov 318705035 318884892 := by
  have h0 := BRFrame.cov_init 318705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 318705035 ≤ n) (h2 : n < 318884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
