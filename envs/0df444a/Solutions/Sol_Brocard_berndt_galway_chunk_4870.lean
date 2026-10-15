-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4870
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:00:40.662228+00:00
-- url     : https://prove2.me/submissions/b15df46d-5a1a-4bb3-ad88-f6535756835b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 875719424 ≤ n < 875899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 875720674 1250 875719424 875719433
    0xe06060306010212040e161d22060b0d0b37030f110906030304050d0605072312060d03020a020d031404060c17190c080d0e01020c0115140d 61
    0xa441d410707002c0394050703442d540c0303c0c4282035013402d04440d00c00c00a00c0030b4070503440e054043d9280402120b03081a080b003400210f84203002765105e04c8040003944046030321f140f8254030818000c030310142034048002600d641c080c000d99400c3d24070f0613500740c0c002c80040a0042414904643c0a41060911608080d5081c80400400c034a454a80d002030000e81200110314101306224450700414401114134941580340c060805460784603d00c6190f40c03142004402e14001282c61704150760000c3e8605001310810079828562400c01c90040710b190441c91700040c1d80141900024040303800210564410220f0302c51960702039551550400041d10881c4104000410503105220300c403000000320700e40e60b131669a554405020107460010498104810041e081e54040d2002d0a803500a500c0e228000545802a41c05a0718400d030300c003042c0d0b410202000002224555030107000485c0b501400010f03910600007c0701400c40d60020034181d484811403400b001181c102c40c0b1803403107421b401c96252001103103500c0c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 875721924 1250 875720674 875720683
    0xf131215090816030e04060b0c070324060308040816120209090a02130905060a020a0509190e070914030607231908040203070608070912111e0a09060e060603060102 72
    0x12414140d0494040f0b240030140e0051300613015100a54007402210380751074100c6401d0045525918803584424000c0020441d4080141e80d000003441c1e4001c07611003501450001c0e00c16941050310038020025082100500030000c0d0000305040701c001c540c0b080d0030000200c076403054015010f445280040049081003c0601c0600b8141d039000301003500e802824044c1c01c0160020540950350750240d00001602030003140201c900001140c2c0d58980313066942e104110312070f00e07001900144100c3e11000400c2e011088400103004010b01c0d110349101d0383c81c2051f920100d1105003030b050700a81250b4144207019410010304c680c20144c14004401401807042c408145002c1e0444c2c0c81801104c00001c0511160030150700c034051030090741618011911b40c0c6040e210428240c4080c0000382102c01304110340052050b0b680140b03032142700b40014442802c0c000403a076000030b0b28030312010030000e60410380f1444e04102d20002017050300d00500c0010325040e010000183c0003030072107004000010005003503a00c00e01c03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 875723174 1250 875721924 875721937
    0x3060303090510120504110a0b1207030908070b040503120705130e0c091e040507110703151e05060a06020a020f120f100209100801180914030f1312150908 68
    0x38402c00c2030345028204140304c1c52051040c41d0103288d4801010a129104004440d102e21070405003010546501d44200c0060840590640d4518400e1248038005015460b580f40110f008034003d60703c40103030100d0340c548110060b000200b4003404200500003139100068400c12900f03200407404c06135551244c400001e02c42d4005480d0320054100c0381006080307a0b80c1c4680c0c090f000a4808001641d2512404d6401c3c035803048103540254461181000014211408240000f15400001c80c0c00c1c166021804000307202c20707921031205a1280100f203103d0404440342d0004151510081041034129004900c0405034020480c0c0101c900c0d01150000080400903218049402001c8400d00c4807201d0310326000f0b4100000d41c0e44249646540440030501c5624a14140c0c0c044000f500c0d419103401668000402254904640d12662485034402070501400074181c0503000036007080d034038040d040f0750704145001608031643d544051b41022010460841e24121484075640c00000c8039403050038032100300e01907030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 875724424 1250 875723174 875723207
    0x902040602060906100305070308030415051e0a052a0c03041517360712021f020d050f04080a06141305030a1b02030709061503060303090510 62
    0x500203112540003519910450300e04082d12100d442c0d8422500352200d0610010340140d020b54010300214400400440d00b06104a003450801b411034000b00c1c007a0f40044500500310500d40d5031104506c48503031400c69004588410808c0140741c0b40329a0f400c1105402e1a036000310400d9800300c001c01d000c4a04403504a0014005c50b9100c0353360350f200303031003c0b4003000342800002c0050b032050608000c441481802000c0040364488801420301e03036105601e0302c000c0340d603220f0170b0848d6400071404014049503014051900c01003103540c0f9180140700402c0000145a40d07400303110040307841c0c42079000c03174081c0240816140142d5284407007074400403903004940003150207000d03103006041007021513130105d1100c00c2d03003400009995460314400081d0041e0020b0103442034004000c140c600c24411041d90440802560344602d000c04903801287c5042c52982211019554900303007840414420043c0282d041481d01e420310085056580040101d06107215480c0190007070000341d06034074052000c80107040e811 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 875725674 1250 875724424 875724427
    0x100917030705010501090b0307210803070c0c1401020c030307050c010c050a0618140a050a0305030c0706050103060e1606120518010e070f140a050d0309120c080118020d120201060902 80
    0x11030803007030f0003000441f10741d80c8644954040001c0780340d2001502c20100e4482c215000c01c080c0382c1e844032500381d40000e2000c410080410401c60000b41c1161821019101080610810702c400600292030944980d241521952092103214009440001c43c0d42140200b803038259811090f900d81203103001d0505000400c000e041c20590210700801e110f220001074000c010f00301e40310608076556601c52070450009000b542042d0861008240100021a0045200d00300d0700d2a2180c0d503241d507001c43d20280c104840c03458903448a00c0e070b148800c2010300707501403d8100b403010140ca4140040e00c3d245c0120ba039a01d0b00ea48a20004440c4480c010040790703507110800082c00034000003170099448050302e0186800c060f08000340400c1c004900a00ca0b41d18040140c05502c44ac0d00340420003801d07505a0704102c04007c0480c2001c210100d608408440c441d01c28950020410305085c0782c80d0a4511720702c098105c508841d1440300142c0e6a02d00b001c0781d40c0340c000c000c007202c0310030780d4008901425043d0000e107a000d00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 875726924 1250 875725674 875725679
    0x1c290f04110c030c010e0c010302120a0b13090501060e0a020301080604060b041b0c2114070f08070b090606030a02090402060c121c050105100507080c0705090a0515100917030705010501 81
    0x2810341000540c50401d5087d0354103c103400f40150300300d00032140510913070900e460004600c50440d500801100200500c62240c070418080c2410540780b030350208075003e03512044100130f540800030751590010715110081d8255810841c88650742c460080c8041c08058540c4109510307921140d21190b607481075001c0300482501000c0015003020b920110445030b42d507142007840d00408110760446050005a0fa03a81c0941e0b18078980c10b03081d0b03004000e0581d030300d0001440140c001a40c00b8010106640711305140ca4591800b0036001d820f002009000d00c0c003076040840141c0059a0b07181075240c0c024ad04641d1182c4801880710103030f00c0c100118490304d05858000402d2091000031000f0040c4400e07101c1d40c00c1c00503070b80310300c00d01c60700210300020354021400c28000c00d000a0b480401900124543c40c049030303c0c00341d079000001e04628040d02c180b0f08103983c0e0303414041080d500074007850a64005a03008001d44090080041c01e020462080300700c4030b01c6c094015064414184115610203030480001e10003540c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 875728174 1250 875726924 875726947
    0x10605030f1602071401050c010c0806010212040501140d0f06081c1b0f140303190c02150a11041706010801050105150d020f1c290f04110c03 62
    0x30300c15036401c03162400c10000600e00000b100b004402d160303120b50140020500c1e040c0b0b0760081c402030070201818450300b1f016040c1007601c03d10441c0c0308d160865070745c4511401c01e107001906108111206041503d4100400d00170303a40c0010080f44107010a144055642072011900b90007001e980c0f005030041c1c2d0900c4030014201c01c0c001034500c804168200d5203c0c0d01180c5010590786204000461240150003903c0440841c010100c420984d81c0071321407080700540418421400c540c0119420046000b88910020010764540304d210001c100d80d000808800104440030040030200a02d181c91403074a91b01c0c007000c0740c0b900c1c1c030580300284a8003e0044004240000701b80d2114001d0244004640c41c5c04000540c0f8500b00d13280c2400140521010b81c6028110061034001e0744c480140f2480c0f6840400401a5011842c038810421070307902080050030346856007245074900c144c908858840825291480003695512101c2072080b03004480010741c041c035005190701c00303014101032600c0310300001c24908041c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 875729424 1250 875728174 875728177
    0xe04080f0f09062d040305060c0304050a1e0302060c0a080a090302011e050103060c032a020a0f03030509061005011b060612080409060603110904150f0f050a120b0c130806010605 78
    0x3013900700740d8124444411403104840c044c1b0311010345164040f401250010340001c00854000380510b00343d414040407a26001d4003107040d10001c880400c90840c0100605506104107038112a0303c10b142440c22020f484000c00c540d00141c42c520f81160382d8040682014001d6001c101001501c001c210001c404190404004250074401650b0190400560036031640c0300340304e503d030480c411990152401c0c2c20028400c841c80308240540f001d40c46424441d0010820414094a0b030522035640410180f0b003c0c26881d00703060700500310211081e46c1c1078043c05160b8029903800a6a0081c3c02100305103845400c00c000904076940c030080075200200409400d0001000040c401e80c0c00c212018016255a0703a401c60840300101c0d600005c0c40c505215031400340c6429000a61401a85034402c107032241c85540d40710031503646901c02510303400400b070200541d05081481800511000c030000d428202292a2286a0003000f441260440300c0016200306040000d4130384c00152519504682b80c640c1c42d040c000e40103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 875730674 1250 875729424 875729467
    0x2240a270213020702030d1407051005160908030910091503060e090703080904020f0d0e010c0f020f0a030f05070c0e06040522020609010e18010e010e04080f0f0906 72
    0x1d02c6810030502030050540202c1d0815980030340200104a80130004a50072025030a6507030072400708005490100300208909145074201000000d21810031200c09801032048c1a200000d00c6090b58040054003030200540b0780e001d2040d40c501008105243c41128000055009252120b108201155040e64154840d0090300c4449101c2d06441d250002d00b15034401c407500c1b0042080c00200000f24032420f240cbc01a284808108003070b1070038003445030112003d40d1041c2400d41c20300d030b540b0603004155a61040001114450500240500c00180b02c0c42986a0104520207418000748180300d80e4070505c0f4200311651960030588035100310341c42d120b545000322029240345100318104070105030174400c210006400c0b0604484180c0e031004c03080e401e0002d10303007280c0443d81c107124207030044802c26140d280d00340030b2610f2410700240096040000445c0d0307864042c0c00810786980d0310030070040010b8108040320550007035003121540700c030803240c0507000381e22440440c17a410041c08100d0103401d04007082007031030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 875731924 1250 875730674 875730679
    0x6030803010503071d070e0f09150f12281203140106080606160510090503070203010608030a08280c110c03120a03090606030203150108060702240a2702 67
    0x103100e607614a20000385d030b81045e902488072040e002240314640254243c02030160003406130020700c2980e000003501c140d800c41d111080b02d4121015041ca5145c084030011940d001210704c5980050303242c2c04195541c10901858801c01c1c04484011740900340502a00030082e409000c030b0041801e80c4000501903d101140400c020403030b0070011407140d002f5440203200b04405043c1601b8080c0903c61800144030060068a060185c006c100740c3c0b85026009180c40c20340640011070b540ca100d44141401c440c80d6034443c840680051044000d0b080d0f120390a00e80166855649040c1501d0045100d100e2000d401486038966141c003002000403074109006038100020710050740c101d0100942407503254401c3c04079554444108200030350b6600d000fa4080c2200c075008250019944d038680d070100c0d15040c4101b0310146c10007003007001000106020000c040e400300451003d40401031400c0c4802030750700b606c10814910103480c4000100d590100ea80900d10080940400422a440b2445410342031103070940107a0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 875733174 1250 875731924 875731933
    0xc0319031505060702040c0306090c030c0e0907081303022a190b0d15210506010b161202160f06170912030907030c0b040f120b150d050106030803010503 67
    0x5600c407520501000442c1c0c8040c248500e0001c2035401c00006126107255041490794030305001c106082580b094100d1807003035403000500c0c0310400b44080d1213955613031038851142d5500e400b0854030551206009404c198558240030071100240b60907800d1519410340402c0c4400c611402a00043c00040720804080741030b290948105c0c42080c0d412104031290040074820710081149100c4040076502c21290590741000000b0b0141d203614150015410f8040c03040820f803c1c0041c03440500c00d06004103401003da01090a2808040b020020b60100e814040907004900a82c2802c0d440d0380240540109400180100c8035510b803104441076040605000d508009030b10404510b458039804e90080d40200c0344500140b103644803c200e010056030004000314032a000e00180080019001d06421010304581695661184d00b0609028481b480d02c1c1d110b21500c110080d440d10116144582854000f01e88480c950035003046440411828110090020441d41c40c4c08000002d0158981c0590b040e59011001c0e41c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 875734424 1250 875733174 875733191
    0x210a060c080604050606070302060f100b0d090317040c09090609020913030e0f0f090705090d2a03080a120b0d140c03070812030a110a0c110102030a0c03080c0c031903 73
    0x8581b60007221030081c0507a02007030100d2895881c00d0110390b03001c1c00900c07641c80c12a407940d00c58102e41e0080703c1010f1000351100d602c1400c041c1c1014212802e1440801d1075005450561510610310310309110f18030703107296146140d0302030042503042010403d8001d00200c00c5402c00e00e465040510402e0029000952024041b170040d1504100d803a1046034001d18070800d909844081081108000e441d050501c40e0801c151440d40d01c0e010800da4003540610315080001501d00350b00c405007007895039540c0d240700404400f840001c2c410005e5500ca22680e2900e0036080c03980038000d90041800710a219444012505d9000c02c02840e075a462a00e81d240c1015200f600840b4428903650303004500a00312145c010724118940b0b401100c000d1540300d140030300e022800001200040d000c580c0f111103900e0004048a07400802c2c800100c0c07000c1c403c140300b840114500a601000201500c01456004080140321030215800856070800c2d00c51041441007525511114000c0d90074216281c112440302180c01d00c50319 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 875735674 1250 875734424 875734429
    0x20c010206060f0a03020906120a1a011401120b0307080708031305040b03030a0f021c03140709230414130c1409040204020304060212010f1a0405210a060c0806040506 73
    0x31103801c0c201030800414242507900304100340c0f000500b030540194064034140030b27603101005500342c51400745001101c03904583d0900550b9102c143c0180031410036110140429136445603200c0d07852148100d00240c0007010b0300c00241401700a502a0019208005020810355000700040440105a90b1845500c03070b130350310a000960300a00e102551507013060240b0103140d0b002e0130407401d003040d05205440c40b605c041c04a0035003c1d83d0000d240d4002035aa0022104120103043d9030b250003000710309001189500c4d0080100102000380000f2502803800fa094820b29129600b24040e82c91134000041c200d0f103402850b10100e2040c060003501c01421340c4034001100030900c1000888654060200c03101a074035038003400065400980112348440d070030001c2d0401c8161507040d50340680304c00c01c401d0340d515103029607400300300c01054030072189030703104001c208200d5a40c0108103801103901c45200c92604c007140100350a2048041e070260400341014407001d02294001e01e650300c40e1900710340c20040798a64806 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 875736924 1250 875735674 875735689
    0x10614030307020d031407080a09141014120915060a0812070222060626010e0a02040b0f09010f09120615050a14090604090305041e15020c01020606 65
    0x16058140d0400c021400141c00c000d080288a54000e040418607580c0000c0c250b6455484180195480040030a9400c085039000c081d100c014114815900b900f52030290010781c0e140b03a014012070030b00c50503446410412458005440c0450003800801180f0310b006215203480789900c0c0301c603450060031100050344c5854415501803d17031f90f04400800b07001a225203d00c0081d4003450007a0390280005074214444c2c040e001c008001c8051000c400700e0316628102d0060013001c0508e186406d00a0700e1f00400e0b22071004169158110b40d1440c544010700e4072011b11a1000b44600d0f00160304500c40001c0300e2200304461f4005190300c035820b903505180520308050450b6035400d41e001e0001010300b01043e11011030569013100811040500000058039643c40000720300a50300da020740003488802400a45501d46505120f03400380003514140110003281d0b50003800d80c8501d01841090200394181d030b4849a0030b200100d03001d0308100301d51545540312840041d41d900102d801e85801813107050002003807400d1040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 875738174 1250 875736924 875736959
    0x1d180d18060212030c0a03020d020f0c06061210090f0c0f0e060a0303080712141920091302090301230a0b030705060d09060f02070c0806060d111804060c020106 70
    0x50043c1945c884441ca0308050b80010354440403d80c0a0042d550701858510007002c205c10b0803001503035902100f2242c00d04040008111500ca2850350458900194000c42c10600c0c240180b900020100460320300000b9102c50990003030020a580e031000b10706280703121180800e4407032a90419846039202d000700f01003950035002c010000b880000204a14074001c41c24010b000d4005803003c1038144508000d00541042268203c1903000d0360300c1080d126488a2150780500302e00620100c890780c001d05040603c921801d8507481c00f85010050107020400f280e0b041e0f034014040107000340203400c20204814105000842e0501e090074046000c02c2c400c100300d206140c0c04140240282001030310b88005c002e142d8100346ca800320b85540b61461440095000d01c82c0b10002a16010300589401c2c060400c012500410b0700660440d90004003441546e07591030844114a9500208a69048005802050a401e110003802850b0141c0c041440200300b41a0081d2000320350940c0200011aa585400700c905451b11 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 875739424 1250 875738174 875738203
    0x203060f04090f02040e01020a1803052107050a0305091804021e0411040902130618090f0e1b0907090e04022806030b01090e011d180d180602 62
    0x249811000c9041a0b00315804141c040c0f890b40d50781000b6600803070241e50082100d03003596540081d05035100d54100500c40c166590356541000c41c0d60960f9070b080d5440203112130040c44428900d2500300c001e800c0d40102c0d001c299021068580756101407401900130382100030401c1c8507440b03810303503082c2d1b074a00b03211002c0c86075400074001180401017001440c8210000441d154000352140071030710000ca00c460040005091041005a03030303168588401481d005c031038200c0e104001030424090303410000b030007500c0259422100c2c0020740c802c18003281c0380140034194601c2c015002e10941d074042d007100d80d2710000c4044010340d2260b4440e0f640c00300495401d0041e000301020040b45002060150800418242c00045c0e40d40003d11000919084902c4000040c0d11820000352034070105041564482d4425005040b1820a01215418030b12304070b160001119924041d035680900090400c02d80c21030a0084600303510a913400e400d000d100040c80b0f00c8400074200c40e00040d03c0c1e40040d94510000c2c000840d000e06 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 875740674 1250 875739424 875739439
    0xf040b0d0f080c030408060105120102030f0f0601020c0a06080f1602100905010209041401081506010f050a020a1b051f0f36060206061909110d1b12020306 68
    0x5a81d107640710041c810100756002a400e21074260004000c000800160110000502496150108002140882501c000c005034014402c2c000f400303180d502c1468201c007208040c48000d079101c400403494418010040c83d44001c0202c40003034030035000320615015490b9080484140c1d0f8a0000300500c40100f13072110001648820060030260040d60300071001d5620600c0050725000036100014240c2c0c07004000499142c41000040000ca00c00700b20820b07a80c405010b48080e1031070600f00291100f5141c103070840912070001107450000b07200744000404250b2000c42442401c29100030321403202c1040c0201030245400c4036016403401802c00b500b80800100ba602d200103080d005604440c2075810540402590601456030404042444c0d0030901c40214810300505c445e00d803843c000c0c42c088024240c0d0303000783c026084d0a68804a40425102600c1000c5001301d44213000d040703045540d2080014480d1090300d08012201e403000c11151102e41d20b01169100c0030b500302010401c000302d100640d07029600007103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 875741924 1250 875740674 875740699
    0xa051f05031f060b040f150201060e010608070210110c120c10020c030705060103060c03050f1b0a0921120503150409020604030203010c0e10090b0d020306041b09050f040b 75
    0x520b4015860034180516010400c9a5544042d00c1550015005642c6e0003038003501c00d2001803201e00401d18130040324070081c08850f05d03014181a04940602403c000c12000a00103503504e4020005180c90f0044a1810000444004580000c035000401c52509900848401400703165102050381d0b00d03040300d01e018200e03c2807402c1d0f4217402540001052009170000703205040c046881031101c10300a500904000c242c00800b404000c00b1a03000030280c0603840f0089040c0f0112800048190308948041684030f0303035945080009440159183c0c0c040304d450404c00c3c203021404012008a4240544140d4069512020307901d001e682c1404104d42400c96404464580b0f04d0901d00fa0f0000403103640081c2c60f2514181d16500070900307407189071404401041c21840d012002e410031000d41c144a100500d00444064103104071000c4912592424145580e000b10200700555103940c4040d201148682e030640f001086a440039007015400e200711807144070f83e00c51401c2182414010b101800e100104511032240 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 875743174 1250 875741924 875741953
    0x21010b0112112203020901080c1f170c040909050f210d18151e180b150d0f2d0f03020a0803010807051c21020f060a051f0503 55
    0x2c1409103c0441800101d030000268484560050103400d2a60282040040010900c500c0050503c00c044100562040020846610825212820b036000d0b5039100c01d07072905230081509c0d0165810400c100c0703182401c6181004400242c20a101211100350798a0308038007000407600c1078840300c1c020392185040044600b0004181e21150b41b419000005028008035600d60384078100003414210100c90f90746e11481100c0c4200d1804a80c0c681940805200c0f084e2030715079074a61b0391404074004110460740c1c00891003058620300742110001024001c40c480c841b003402c140700320502c1540155031541500d08408843e2034103066001c40c0e81d00c140f40032109445c3e40c2d0340d43e07240e009030031f00103908501503154a4800148018001c500030829a0300812006061004000d04480c0405508222168180300ea0002800e40400303250070903503501c04100428030001c0180e007405021407098010340500303010451061500d82c0020f00030810355440320504900c0c07400791880c0301020700441d981540940206140da4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 875744424 1250 875743174 875743207
    0x3150103111306030602040f081b0121020c06040f0b0a0c020d0c0813060306060306050a030c12021206040c0e0903130b0307050705070e04020135040221010b011211 72
    0x1c4850340c82c0041d4240d9280c81381ea0803038200f43c00004503010000c0d810000034a08100c500c00520542c2001d020715620500007803c449500b225480d0b81310181e800c5840340c00c06036030645000c60840002c5c0ca21510b858680b230712401c00401e0b4120342d1440601c010454110240c0318110075258503070014845c1440100064a42e541c0320714040b075000d8400c216140a5412418403000205a9030310049182410050090251881508268000c0c0310804041005c1480c0d620b08908507141d5080ca2203202c0c0386400440c90140d10394280c9481c0784190028001000340a0010307804480c0d280e0240c0c0c4003a207540c001c06480c3d221780301d119400104e081c0310901100c10a0001980c1111003400c0c500c3c9080300300c0d9030380e5040c001d15030311603200212960104800e650708034aa0301c4101a0030b03070144d0b0f0000f1f00500c42031255800b4103015500c2ca00315500103403c40d20380603151102d0115a14580f80e640000d202c0c041c0c0600351100700140000e0300b8042c24035043c1001d010b58001c0c0d4205100c404d003821024000300c1ba00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 875745674 1250 875744424 875744449
    0xf2417061003111c030e0907030e10020d150f031b030b060112060503190512250615151d0303184c05030402041d0d0504050315010311 59
    0x4205400c0a03c207083c13040c500424144607840d0860101e070f04100b0010035210040c00201810704044140e10140008207100220900c82140103881705103200d10540284100281c202d0011145800800d22418062140f02106d115000c41118103184031000300769040503100c0181014441008103000750b0233812070790066001d44000064150340c800000b443c0000460940450040d80440c1c0401c0c80300c14000d6600d90310404007a0361424a0440340c50706054200b10003424054601144501000035a0700103048180311403204103440c1d5140e44034010115048150703400411781c0c0c11014102d8100071904104510002801f6504040d00c11706048581c8207114442c2d544600001140300001c09154229003419011a50300b1840d588000c0b001084480b90707450520011109100704c1e4011907001044a40c003a038141d40224070640e04051024a90300b0b13158074158107014050701c090034158054003400850f101101143c2580c1003070b0301c482040e0b010a0101510303074003400420540d0760421000c403905 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 875746924 1250 875745674 875745679
    0x406060801061b0c060f09090608060f0408040503061005030f0c06180d0206070f0b010819062c061e1005040b060f160c15020606040f241706100311 65
    0x600031800c0d13076541104080c0d80c0003a408603031100c2090720301c0713a8003205071000360140344420882c2909080100740c1c0c44600800b5010202c603064005410844204142c41c02004064112100340c03d02004030580e5a480d80140c500034456030007858820703200050090340d0200040e01d0540b0740507107038428203440c1c044280d01130703081501c024000c001038a54000404201d400782c811001003c54519050b10350403010781c06120380f07600c09404482c52519542d01207622980c41b00001403580c1c00440d0300311808000b141c0c88504c041d502a160b8464150100d12503101d4032020700d001e219035560000000d0241c030207880c0700380e00ca03070078034028030460429900c1001c500c3e000030906801c00045070110340007544181507030301c1003000c1c0480c043c0c200800d1101032405010000c1074800b07040c4d0304400095030780c9801007081c1d02c1940c54024142c4203550590040c000c40d0f0b03000c0f40300e1904054129402d1001400c0d8031400710b0310303a00c0e08601c0324201408030f069802070084850030000341e4078541f12100710307c0320440b9080e07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 875748174 1250 875746924 875746967
    0x905040b010c080d05091e0303070302180306190501050a060519020304180b092d10080a030e030d0519050304170414010e0102070f06260702100b040606080106 70
    0x404920400060a101d401c0201d01040382d2800c1406c00307040c01c1d22100c2016241140160448840d5008019070350b022016103030050301c40c03100b01b51044000c00352030207040e00b501680f4140305882030840f0114059901c05403040c0f095990741c000380f040c102c0180c8104000900309115050007031908600310294900140b04483c20305403100c00d0405000324500c2c003003410551300c0900c10700504110801d558440707843d0002205008104c00c0c00d14221010140750541c540e60724002800070281c0f06e6141c00a0000741048407050b04040c600500141c08100b0824442d02c0340041c89401d80307204104960a403136802149654540403840140d0b81074102800072100c13a190524040300c08209400907000170040c001110000c00a51000036090180c0507056074119002804180a445070350714030071049804a00d0052003c0201240b0401200c0c0a64002e00e441207a110070300a90344d50014405460403e5114200502e1032081d04000c2200c00500c106408505004010407102d03001c0c04086403080d42c0b02e100d06 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 875749424 1250 875748174 875748197
    0x506070b0a1b021e0d0c11030718020c1203012709081206040b0414010b0a0201090b04030206040201170403020c0603070201090c0305030a0e120a060207030c050d02030417010c0905040b01 82
    0xb480311242d60301903001a0300502d08500e00c07000d0034025501e01d1000300042e00e003c0008a074002e0081ea08240054032a02040b10071651580f41000742100a00b074801911403008013108016010354405443c03602d1600c540f004105030480a141100d040f1400c0d0714510514000d40c103225001004103d04400c507095849144102281e816801058907050f00301909000307150000030003040311400c400e454000d9141c0f1700c40300c02070203800f0306540c1526100f00c485a00c4540d84135040f405070100040080c45440e0388030511040680000b80540214402d8907004404588903441e042602012030740500142d01c8502c2808032400c01100031500a01d0502c00070548034020740b00c0e580160113503881111294400107010503525403040300f48107408421100510401220760140d540c070b112185018214660020b903640400d402581c11851650f481170584c0c54602c070424000c0d4403600a440b407843c5080491a4402c0c1d80340c810302c03850102e407416460303070000c5c2070600003030100401c40840e0080c1407000702c1c100d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 875750674 1250 875749424 875749451
    0x914041d0d020703030306090b0a03200d080a03060e090c090717180d0207030b191409010e01152403020d0f021306020609061f050409060902090708010506070b0a 71
    0x14541c825520390020803100307143d8a0010201ca03101e85c4a43c00451a001c2120030380e03600e4208070800c5030341201c040c00420030400202c52100232000c0c00d40303520154040b100740801c940b94010f44050040c6850412170141c0d12245003110b141d046611000769001488054001d19103605201d810100310300c0c4c0851001820300c840c11400e041a41e42d80c0720540049054801b41c1305c00c204006040003144007505045203140c2c3c82c0c0d100c40d08042c00040348105003800b4000e4203c1c00c0c0d4020080d6032040c101c20021400c010740214000d104001d0404030310350034404130b0201042c034000382c0740c00c5480c0c040701070381d20141c910b84001c40c2000d070b65103410030547c00f0048501580d40e68003840300306403603030080180c4d0341840c00302981000e040d0794043c20654200008015007a100418950350090705040c0701d49411070b000c8440e241406154001da98400d24116640041c440390303501c40c6001381c1c403d0311000d00c5a1200641525481000d00ca003942c4003d0410a03000082c25251810f60042020140400c900080003032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 875751924 1250 875750674 875750683
    0xc0e09160e062205150a030b03010b0415030506013f0605090f0f0f030307080a11070f020f040b0f060a05040e0f041a0705040b0f12011e060914041d 65
    0x281c0c2c00c80f10032a07010380602c0403c07103829100a0101321442000c07400d28221881850140440300070506a45280d502c1883d2420740080c0c40d0000010401c004584091071414060a04c030b0000b9a95031054400104801e940081000301082010410048480301020500d2110404903680780b40c01d00b10881e680002a5540078013400b46000201a0031400c200b05001c03440c0c4501c03d00c95040d590301c269120100c0c82c00100c100c0b604500d9510b000e00720b0383c0c1c2d4289240301411407003c5060345090001070340c005118160241e10881882101e244134010b00140c200002c1c1c56540569942c4044000b005403054503003079008040801c01d90508034141643c40400e50400f84080303030420070745007004d001c01c42044103c480401c03d0f2184441542030509000314000c00703a010714007c505403004001505040784a401003506c10340070700300400601c1981c54400c08181d1074040d00e50030307806600a41010800034000c2c16040300380c03490902e039000c10b626030004100142c90440c0b0310001c2021840800540d0600500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 875753174 1250 875751924 875751937
    0x2030114010b0414010e100c050f061501090b090a0608060414150102060606180f0a0b03131e0b0a4206080103150905030d1802040c0e09160e06 63
    0x8041c0792520324240d401c8054420888440303040001b1112a0074032aa1100710082030300c1141e141c000050045481c0951402d51380c020004002e1080800b04007042541c00e0088012880030b82e90b0717030345e055a40d0145544900038118415840200f4010500416114140b041e034400401070020501e000d0b2071040240145082c3c1d000c1000d051101005015560100001d81c0c00c8070041d1400f81c03400155103070303164031680d02030003580c0304103020380192203295900540c2c0c20241015004003070380e900300b0100f0741d42c0c031a4503c1000c0394210760100040d0a40e005041390300c510b01c3e42009041c1a41d583d56542840108091300c158074016400d07104c1601240c403040036000c451102d0840f8a000180004010010100d107a400407080080c54001880018618401d0111003d902c6c01d002c109079047e0300d8028258001e822003501c9403032078802c0d0510014052004415014000d64080010f40601181260001d4032a59420b0b04440c00b000404c1500560001041c50090760b841c04010310390300d1400040c81c560110 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 875754424 1250 875753174 875753189
    0xb0607080d0b0109361e0c08040f142b022a01050304150c080403030b040501120807210e12030c120f0d09030806130b1f0c15050115020106050303040302040203040203011401 76
    0x41c4001280400c0034800e01c1c080b5107423420302140a20700f0760380382c070001900300308000e021590a02c10508107540402c00260748081031084003008042e440510305c042c90003003c1600040c4034503002c2e00075102c460f1003c2000d02044003041d2108100000042d1030f69807014000f12590b1031500e1200c844080c00d803088a0b0b400540351781e0791301c46042604008064a00406880b48203600d010300401040d00488810903401c0c2d8089103441e101e003902d060031034801d5210f11a5a034904041998a0741456002101c4002e407001164119003101e495060184d0702c2c09906c0c024012075002500007508900c41001a12400c0750003a4a24034194000141c0000d0364041d200440200707405d003003400400e140c50101c16030103c4009404010101064002030b034510490350034404625200f005404a1038850350f9072095182d00010845015001e15003038030010b040c00d10032001c901c6245c0210480940c4103000b600203ca400070010b608050641e001c00c4002d40c00584102da042d03503a0381921401c1e0300c85403009070080192 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 875755674 1250 875754424 875754461
    0x70b0a0809010c053f0702011112040b0402030703140106050f010203091302030c12041b06090f0b1809040c0e0601030902090f0a0b0607080d0b010936 66
    0x62a001600900c0c0c054840c0c5010b905148182c0c1d80a41c0c04419a114159000b40d02c504602d4080f107a03441d25221080340d2425525a80c855240c2449a200218011000d582c000c10002001c4a441d45c07850240e101c0c00e04039a06500c000c100481c0b0f4451800d07800c20300003000d0300d040603603d42c0e4040d441840e02c03200c1c03502a519454100a03c1c502021200c8e2484170030700181d0701c3c1041410004a0865001c100001815408000b0076451030301038050f2409030059007150015410541804540e802c0024110001a18003901c0407600c24841c2d80c01c4000c07100c42c9503c0d0140e0310700b441c00065081e080702450202c0e44954a500d10402d40d52100c856000f103020344907580c4190b0078404d11582c1494000c040310f05250509034008010b85070170650580c4024039020b03103070a0761649000390003d043c01920306903200701c000c07a5441c11301c54104000e161a0312900d104210000c0c408006507000d0f103451080e01800340307200f01c9410103803a000c0c01e00645c120380d0355020301407049030400348812152050b500090400b603 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 875756924 1250 875755674 875755687
    0x12c090708071a0d0c020f03070605040c05040b030706080a0f050106110f07120f050106050604031a070813120e130c020106080105101203181401031404080901030e0f070b 75
    0x10140b2059001c0d0146001e28040004585001c5641e4891003000102455072646003c5610b4424081e000318140c1d5a01566519131507420000701504094405a800b41005075002444e80781c98400c0048450707000e000b4045042c80c100c010741f603454005210011050703c48a0884a51040d4864140030b0700c002d45509615890b5445501d281804240552a99602401c0188030045440c5490f054056010014030381b201d20501d0414094000c0794440340d0030071008a404000c0000c8241082c900d1070170007409200b0b55964410488026005071041c0c00d041c200c4110f8400494008864142150b040b4242541180c41e40c03808075020711502e0388001145680c94a00010807603080c0981001041080000d01141c2010420440559030512450058111903800d4604050040e041d520031442e005400314405550b412a0003030b0403010107101c500007881c103103560103d60029203c1c40c0c0a0b98210100390304254002e030040d801810b0000e14442e0700d11400f0300c0d04800300390410603080541428001d8549810 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 875758174 1250 875756924 875756939
    0xe060d0302250f030c15080603071e080105010605041d04022b020904063e0c070f0303050711270903070b0a0e0d08010605070305183a0209012c0907 65
    0x781546e041000800d400303112503a0742c000b9002c0113454a00b41000b1502403090010045200203a001e181d1550030b04c2c00005e0b0b0250404041d00480360205030300142000d60f880203210f12130040318029440062070300f0500c50300b10801c403521000240110401040c5040f500010345c0c1c04400c81e400c0300d000340c544000355013400405802d24180d50224440c25140060903801c01c14800504081c8502c3d100e000c10380700241c1904000d0500200940b007a400406512418001c0c403540c850142a0381c83c590b104051055800c0803000c40185001d48103241294598038004032084420117410b01e0814401801044045403c0800c55809001440000519114902c0005080c440c100400e64107105080300100029134001c0d00300c0c1c00c1c1c60f5043c0f0b440c903661001d05002c4415122507207516074016540c42c0c1991107803104a0503006195420000f079034510b118440d90440fa8001005000b5044008180104100c00e4113501940440038103004100074034550503914541902c045900c614981e0001034100b1165 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 875759424 1250 875758174 875758199
    0x905070f230d020c160303121e0b030c1e04061a090f0f1302070b06062104210305070e03121c1113231e0f0310060e060d0302250f030c 59
    0x110b10074402400104402c3d0b501011270500020791078101501d41c802c1d40050354050000030317495070f0000d169800c07040240e40c0e92945440c1c02040140118607110002c9886000ca10316082c400e01c214841901d412103074401d001d22400180c48940d007001e840141d6821541d207140c5101100302102c5001611181141041e0810420150803180a50303000c1218003806254101485810160368011400c1501d41d4a856036000e04520000195140b0a0744076200ca140e25402003402001c09030340f6400065400302c10540c071200c400403050072030a003c1210210500c400e903903900e4484071000c00040c0240942010b10f9280d0b0050f0141c0c4080300780305209200c0b5160700b44004c00d40c210a807200d12030000507500490350710444a0314000582001805140c00ca07910b080c8040245000941030f0741440c964805000d01801643c028034010810240c002165410107000031841c480d055801001002400300401c4a91a40c2c0341c24411034640d0002c3c0800c00990100030503005602c505c8101002e54541590480403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 875760674 1250 875759424 875759447
    0x1a07050c100213062319180807180e0f160902070209011809150e190c0608071430090c06090414010905070f230d020c160303 55
    0xe188180001ca0003243c8000320341c002d44a260410705141d19056001c4500b41c40412030254445800041500035031211600880040d02a034845414210707210745507a0029061b40184c444a510085080146818410a644240e548d0510004c0c91404020800c0d0402581503400b00700c540c0492a4100c989011140e110001d002c00201113003050481d0f0300040c800c18043c46080f034078003840c80c5013940c6051282e100e2102154803c0000d062440007051244c0980040d03454014070340120000030700c81d94417400803241e0066104207200702e81c80c1015006d645090b0081c0c00d1800b0400824518202d00303101000620071031070a204000141c0c20315040d03000001442d404040841c103000030a10110403400940d40368031803000c13a00b2903110b0290201050040003030841c071840d80102c540000941003001d030301043c000d5185640b1101e82c020305400549071600210078840e250014101c0295031201c000d005031501459601000d8500051900e02d580740102d0021110603e03010aa81001003541202d0580c41 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 875761924 1250 875760674 875760703
    0x1209020316030c15020a020402090a2304050c040617041703010801050a060510020a060e030d060e19051e060319050607020106081c03020f041e1e0f121a07050c 70
    0x4410307031520300007506c0c2c906e0804000d0140c0c0c0c01240d404170359611540794102a0280d021300d0005c1d02d2040d40080200300807220801d01923032420300030035216036403041143e041d50b401e42c0361213001c00c81559041c41c0b013101c0288251104e9108512002010b44000c1c004c4d070007014044004601d40c103107106098119059030303104500c551180c0081510040e0045901840d568100a001980c030680c000380300c0c2548100e08001d102c2d240b030081c01044e000d0b80b840805016041544100620960107002d55044407003d03921665412103d01226141c2002802683e41c03000340501aa00e9150040301200f40c40c2c0e03445001211143c20003410880301e144c2c24450350307005000c10001403000c00d0707007040c00216642d2a5211102016000030300e9980031400b54080b540207005500708c8903151035984c004c54800d060103000388111148560b580da0ba02d049504003880a9403048864200c6452030072154101c03103003000342c080b20f9036504d079261460001204510340f88030320703e551649551100c06089a5050544480ca81070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 875763174 1250 875761924 875761949
    0xa030909060e160207080106120308011a03041e0204090f02011d0a09021308030c1c0503060a06080403020109050a0c050f011809050403020a0b0a0204050f03030306101209020316030c 80
    0x21100414002c15500402d400740fa0002160000344100c0c280301d40b40d00080159800d0100000341d2200110205864600968910540d42d80b14114411800d03540d0b45258141c0c0420f10110f408551412104a091550a011013004c00615070101e403e5620401c0262030b140c1140c5030307800555800c051122400807816499030044a041b0f4001740d00c9220711700812802e2540400c1c142006209100b405002d000c2140880791a019001c1d455a640c0b0708001c90218501003614501225a01030300a40c3d0150b03c0040c5000000d609080045401d400000d1051b8110743d01c4400a802082d81407180c0d1514138020050700b0b03001c81c244010b121410b0541e040441c100224050f242c480b40d460066100259140003401142d142c5850504a140441d841c0c00980402010414040d1a0300d080c1d004204440d03080c1d030601c024500c546c0806849000856125420040c10800107480600c00e0440b021681d03c2c0c00000500c2144540109103854000401340811034000241401402414880900200045803240 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 875764424 1250 875763174 875763179
    0xb1503010c02100e071212030b1c12050d051611190b0601020307080c010f060f05010503150a1208120c03060a060c0204060e0c090a0905010b0f03150306090a03090906 73
    0x25501e20080c0f0080f950035959030f419040e502e90911200e07000f0310300416018a0842241014551100d040002e0382c00701e454803150300380c9410003581010b9815040010709188550586454010056190100040200401c40f5102d82a86803052500410321149031110622031650301400b985454110500594460704580c803a24406210181c2c1c0c06a1040e8a020b094545c580180c0c554000d11078000c02d080b00105484071541e005511907003083c080c010040c003849980ea0f80700f0480095a004081c00140e0800c0041c08001c900086511404406045c0070071107a51121100d4014110250480d100704000501c1041c6144100303003603400040d80c0c4070171031550904800040c14548188101418845140207100c10742d5a44d901810041201031207009003890700000c05145a4450282c1c3d81c81000305203800315a03022b8601c11340707058902c1d494000c4d14140210010280a4000811421214000d45800b8080d0744061224600034070300d40d0000e20750041c00b0b1401800703c0c01c090300411005498000708 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 875765674 1250 875764424 875764427
    0x12d0f1e24030f0204092913080a030213051306050f120316170d050403111c05072109051201140a0207050c0d0507060207060302030c0403170d06030b1503010c 70
    0x850080b280e010129010703d900500c081800b510300000041c14080300852113100c282c0e40290050103078120407081035841e07a12904a01e24000200d42c01415040c0300740005e801c2c80b40207038024042e0070b4000814064231580c500c0000e00e01c0d84030081c80e0740d5280d2100010001c50501d40b43c189840310040340c40c528100d44c22040640c0c1c034018103000112002d0b5442c1a9824452502802091146200c010070f5461010b14004806007230250380c01c80000d484070124540040d0701242c5c00141130340f510100403006155801c200ca1903000150240c82001c441d056064489610030035001e030041c0303207403100d038911840c21082100c403017650100b1100590605a0410010402d005000c1c3d1080c80d80400503203032181d90403d035140244590b0900e400c9001641c3c90307403e00034000703a04003ca582943c220340199885810031170580c0815241664100d0044c4020300c001182100800400800520303140e01701807c01441c7c40c140c0e0f40c56071055034403203201c00901006c1450300c05000120003003a402800b5018001c01c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 875766924 1250 875765674 875765741
    0x603110d080403200109081f0e0c04090c080f0307210e03030304051b040c0801050d0f0b0c070302010c03020f0d1508030f030f09012d0f1e 61
    0x6500e1049012845050401400000365030145030002c8044107508110b6416204d0001c88546081c0805d011240c0002c1095002624690700d001e40e104120141e40204455000340030091400d440e075008448090802c1d45480c4550403003180a003c0d458200b034035050045081c50840b0751000d4264004001c940c000c110510080342400b40c510030405120f003120841207032403103061020320b54075020000c02c0c0000d0250018480020f11030083c0d481c030812070043c04110031140a41100c8010403031801c0104841e03d0300300400790344079000b1814241091005d544041e0120001c40780d480c00401e01091a00504d582445540400102c5081c03c62628200c5c1c00d04020500035006c586d14565252014030260000d000001c2c0d0042c42c010701140d49516200d00c0c0c0c41115001114146090303c1c1640c005824080140107203480f41540302c0820f035111841c0c03141030404000c17004082100c10f8031100d000c60708030024894101d040c02c4400c0840b4a01f807800340c030401642e480f200303005410300c0e22507210712004040b401c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 875768174 1250 875766924 875766953
    0xc0c041103011d060f22050705160605220b010303020709151404060e010b071e0803040b04031e08010e104502040f06090819020f0d140c0102010603 65
    0x146450744d550200003c0f5040244c5c041c1a4101d4520310b015012580207004a407804211880c043c0980d039120030f400c442a02841050000d03040042c2c12001c040b0f2925030200e074201d02900440d07003030107680c981108458425038008854007040d4500410a140e41440300c64041e2410342c0080c01010007002e0001c1401109010310130b4407074442000c11078940e8a07580036a0040040c0a8211010340e500c07090000d003504078560a84000c0c0d1800300d1500040001811407050170b0f0703c64591404c5880b02d40b030319100f03108000c101720107100aa02c030400000b00f4080b4880714600241d070f5101407940c105100381c1080b1f800030741a2482c0b03500f440003c7c007500820000c10180c4540b032240b5144881d01c40807220072855a203002124a000000c2554295030045400410980e10030961174000d141d651f00003100e54a1f00f501c0b610086410440004100680c0c0d0220000020300080260404081c0040028852038828030304403070040440300381c1d0040c070ba0107000e441c10081e8240000c011b03492540e22042592503450 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 875769424 1250 875768174 875768219
    0x15050408090f0613090b100e0904030503040206040e090601170309010c02060a02010603150504060e0d0203122805060a06090602120307030e16080114040f060f020f0c0c04110301 78
    0x2c0d210050503190304042e15402c1100a10440111380d031000180001c00000300c2d054090241d42100c141010300840c08028210f802074450007950340c50b500c085840b0781000c2e10880e4084410000010341180d02c4030210300540d03920740548581c3d49842c08a981101d41c00081c41d0b004c1c0c01c00e1284000980e00f00c00a00800703601030307c2c0c0a07622505080128014100e82c0c100903d2492480c8a80041c102c0e240e0002d4852840b42d27400b00072031424582c280340e07908041a0160016031041215030054034103042440d0b0881c402e4100000d10242150030709000000d84004800030560b150100710740d5140480702c1a00411290400440b00b6013007e00007910341c1039049503107412200000100d03150510a6000c1010b80c2c560f2410b6800c000c0101c00050b05100c1c8a200c3d400081d800c00c1300b00c50842400d42c0a8500640e402400c1d084088501d59450018121101120b1301c0113500780000c58001e54984001c05012030600702a01d041200c12080000315038001c4032440041c0002d10051002c4081d1010700c40304007460 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 875770674 1250 875769424 875769439
    0x1060e3601110703110d09030c1503020d09030210110306012c0d05030a0215010b0a0f030e060a06180603030f122703020f0d051c061d041505040809 65
    0x340314000e02511035030400a250700c02c000380000500d40d00c0b60020010140c40000d60741043d046c488103d0351080680030181c42055003000070414840909680700c0300054030700700076042c40f0107082481c003110515030059001da04171647c411541d54040c850b1006000c2504071325401c505240d00020a95042348090088c0401494856501c04600554030304078030f00018030407500b030b50241c50714580b00d81000381c05401510035002d003c00d4040304880c03494141c4096426545c100000040c0c119610043d10b0344c80310500d90344e02d51840d81002c0501c20a485500426000719405281519450440301c1850003104903900d4107505000203035201c0c469200522440c40c01242c90002e511a09005000d882002e07102450f4860070304000400b240500c2d200c82d4004c0d001e484141200d0500983c468090079074510000c0c40c100403e626040305400d04a200c0c0842500008035680c449540c0c88442c01042101c00e00d01b565903040008014601034030007060b2000400a00843c10140e85024990003401d4161b44140031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 875771924 1250 875770674 875770771
    0xe03060a112a030403030324080c0f0111061006020c2209150f09020913110402220308090f100905060f0903010504150b0105070201090b0c07050303040801060e 70
    0x5107038a0b5907210501109aa9485540345406001401c00c070803025142100100e05026200307020208500f19518040a004005009410030030f41c4119211800d0510008461000c0e00b50f40800400d4400d480c5000a02c0d42c06080220281c5403241d00607942e403080c400090b01440c4102202c2c200d12000b0304407580420f580c1c134070b0710781070788560300c0b0895032084030380b50030004550901d00d9040b620b207003070090b03642107141d0312400d103032401034035030103401800c00c213203041c0c000307000b41043e6000344013610045a43d00001c2c0300421008415028070391058905042c0421041410302e01003001d0040c1e01d10482d1500180d012103000074041c0d0b0301c1c0384241d43c454900400d80d40f824070008400c0f240041802030003003289142c103180a0180c5580e0291000d5003500d4000e981881d0350040045039084c94058460070791103440e24950000b00c0c1c0c00742d208500700c2d0048178000500394804201510140100c0c80021441504129000190000080c12854114203800f004041c00c4044651201d49000d90450040c0004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 875773174 1250 875771924 875771977
    0x516030201060302100f08392514062203020a0210080406060e07050d09020a0b040e0a0b01180e060a05060408010609060b132304020a0e03060a11 64
    0xa10b980f010350000d02d1080d0450342154494003078450b0032010344400080e034403000c0d00005441e4034003644210702e62558030034400202e424140020311724000c044842c1350403038035011a202c2c0b0a6009a07803121403c90440c1001700b1400c0d016180040030813800501c03041c58503a01101460705a1080088892001d51211081c54030901c103410340c01c1e40103004140320700c1e12144020036000c02213406031202e034500040412003180f003104180c0124515613500d82000d4201c0a1840100601242264003020030000041c050100801600003810509a007903c64a410a8200f00b9508881c0c070881c1040811a03900300c01c038050382c0841003a6250700d0805045956444007240752400550001640168081000601ea000541240040e290124818071156503514a0160305020300140c803000362000d00c00a000c0c4414960b0003113902d442456140c6040307908100440e0403a801600c0040020b4180b030b01118060404010103500b2010000c810400f80e042002c000c1d07541c2c0200c20929a106544940051215 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 875774424 1250 875773174 875773181
    0x70c06081b120a0c02010e030f0c0f07030311070608011d15190602010e060c090613120c090605100f0809010207080d14010b04030f020f0d0b10240516030201 69
    0x151040308010355840042c860221120b008480041c42a03090a80f050915841805100c401e411104000d6060400d50201d240445c0c100e07a00d11909445031520b0b5020b003c1003013184100460290b21031800180030950345d03034242081d91300545c041c04407600042180040300e9030910b01d42521075030074066a440c0c50355110642c205000b072040d0b0140511061046852901007084100c0f64190003c02041003040505501c4203070494410820f0a401c2c004110b960405100900f1050400700d049884641c407180202c641650840e41074481c80140c800c240003000303a9104000c06081c007201d1a00e842c102c401c1d002420000c80e06d0020040108030b8020031100002501580e189940c400034042d144c542d100800301c0140800c41581c014980010300002c1d100e032095048406880d040100701c1240b014540a00c4641251101440c0d00100c400e1032400c003140b80d20308114001e003094140301a60a1138411a140405040d180902c0007200c070f01c02108503070348c00004481070310704105002c141d1080305013400c0e07004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 875775674 1250 875774424 875774461
    0xf0f02010e100206060306011a0313061509050a140c03070e0316081c030c020d0315050a0803070c06020d050d150b030c0c190c050402090d0c09060e0c070c0608 70
    0x90728100e82d1906070082840380c454001641107401681e6186003003803590055801c1041e4901c0b0410100b00c01441c000407600350503000b550302281e49090714480e20011100e9038802d104207a952814020001c0c02c90088052040008030324034500d0409800070710443c800600500e05000300f041c0300100070b40b01844954112901d0300c03d04244940ea9194858507011a8888079042c4081e40b0098058640a4840ca011080d8550300800da29000700c08160000d15590911250f480a070310740025031641c0342c0c000500904460000f42d501c3e1851494021b5051010f03801607170940d084650900c00990380401620107a00c2c1c1201c02150300010404010054141c40d000301401090010030003954940080c014860204010100c900444c040b20094286503a08a07004125807201c0104115601d802d070044d02c00210014101e050200c075503940c0c0f0580788200e90011203000e44610b0200030000e00c5503007141e801020514171a01d02042659454448400c50007200b05015181c030204070140b40340883c1404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 875776924 1250 875775674 875775679
    0x6050903070b160c05030105090601120c050301051e060d0b1308040902030c0403020102070b0c0a0602030a02210a1805060103021012062411100c210f05060a030f0f02010e 75
    0x3c1da030703208070341c441c1001c02a0780c42518070124696001840e401c0500c1514499401071000c0e0005900340500e104a41644410031f442e80c1e03094035008103960341e00788581405080ea115001481310300c56101c010080800a2541e4031a0010024100114041c0e02d403495108030103075426002d24245150002140c0295000103e60610200030800c800303d00c4030090060343e000b6000c40d50341e01d5444c0b031892414070803980742d60a03980142c1b1460000031250780241d42c000c1b0710404050700308a06100e9107408118280802274034417089000703114455080d44511010340d040102a0750780d481143e1240c5545d4041071000a00880d051403242e103181d4813a15503030849050400d0309016079507070b5090600c00c0801d03074000c40200c0455420444862409100c51806841c50080500411280710f403100c030003406d102c600c90301405000c00c4520515404140620310100c04030100081d4400c01386081412074800030120341c000e9a5000c3c0c2072000c80d4911402c3c540d035660109642400f00d00c90b100498044600000c0740c0d8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 875778174 1250 875776924 875776927
    0x21b030d0603110603041e0320010f06060f05090d0219090903021c0e100504090903110d0c0804090218060c0c0405070f0e090a06031b0906050102030306060406050903070b 75
    0x21090000d50841001c40307000303005200c01001e010003009101d01c01135800403e440081600d1200c802c629420100d9000e000b400c2c5007a620034100e00081c03c484400c414a0426551950b03064402c40c440d1080d28050701592400002d180715103400030b0010b201d010415846202c86039085411956152005c01012101d10060204141d94000c0b403405006450021009401054000703800075249004021584045994242c103132800700d02800300b00b40344000b540741005000c01002c20b403a4598000c01504500ca40d6a034284071242aa649003026200e01d10881086401980c42000c1420541501c2c280c481d84003005a481c41070502028100b0540b8081f95004000441d81800105010406144143c0142d4060103183c0d9501c10440e8142e240e01006130206864110310307880313401c0c816900c3c0d502c0309420b44009591074036a103440746040404441c3c0441c00ca503440090040c40185c6c01100c0080400b80011410350909030005940c40c040c03801500100b040c0411031811a680c01c01c6008003e015000046 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 875779424 1250 875778174 875778187
    0x90606060904020f04050d0821060114161b0302011b0812190c0503070825030c18030501090318060509010c080d0c020102090114040b030604051f0b07030906110c04021b03 75
    0x2d40c8e900070800f81d404e9119401c44408105481c840200d2240304140c0d2900d04100040c05880d00541051000d0b504c2050381d40d060b240080c4d2540c0c10a081c00f03c20081c0e0441c000d1075440018000b004005242c401040c1c1e600d181d9000600c0c1c0400c1c0c40e41901600d0007140707217540c0c3c042e05026510004556002d0350b0308204240004a4100000398003854007a65403281a031380b005030400420040b01c22060980107054154900c55100780d001c0700c0d025078145800036004c031112102c285a0b0f86241c1064030240d5440c4124401c041d08144840c54010305c02c0d0711026414a0400007414600074070a40c24140030303400d5136500810104808507910040010b004204415611200038000e40001142601143c4042006400c0c049c8507030984044070081c0c0c601a10716a945414040508005000c0322807001c01d803820340c0810f101c1c802c40f0030017400c182c50b5034035202c54035800c0007407508840342d03ca81700f13010036180c007000d001c400803800204080003610b016a4451141281420380399039040800203e00000c20103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 875780674 1250 875779424 875779433
    0xb0c2406090615120f060d0c1503061a1206090f010918050109060b0f040b0306010b130e1812040509070807110f010b0a05091006110102160605060405090606060904020f04050d 77
    0x9881c0031740320708200e2415a80d2140e003880785841d4101c1015151282841007000805502c0003070226480c0e40d4a0301181e0107544080c40b43c243d1381001c4c66282c0080f00403030401d8248000302d8040e07501200c100c68458181c2420001c8030b2480754180184a0000c3d101d6070121008081200f420804507480b4000300300300000707070030908020031050400703a2242030300d4410310380503103002d0041c0c2c181d0050080203030090f03900e00401401c00e83c0c001c482020000f90240710010340c0c2c0030b009130309030308c03895041e40c40040141209481e0f600306910700e4060301c000c540c1400148400d850351090980d1204030781c10101801e80b204001a150120382031851481403246000f4510149010b401c0688000c60541d500e00c1c0c15034485041105c11001290030800c00b510b080010000c09115a414003a9903c7c000d00040c50000108040c001c201c00c0240151102c07521041800701e24101441416401441d0001415450414a00081b810310800c4811840707140c01054a10360a0240c8049a005020050000001d086140340 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 875781924 1250 875780674 875780707
    0x20705150307021e0615030c10080603070915150903080403030f02010f06260d14030703060b04062c1c0c120507060f090503030f160b010b0c2406090615 67
    0x3d5200c901d40c4211b106074040e04001400d008c07040802440c842205e560641e003101c1115009012551610445c440014000304904c43c20743d0003045505031115203801c084060400d504c1200310403003003101c0309c8007c2001c18030600a9400340e9034903207001c403d070a0010104a01501908413031803206440c00d580050745980309100111011018401c00030f1030188101c1080d1642c4075000e100300032506692030450101c9100300103560200d0b40342070002d00f003034695482c05e200f0703041900034002046038a03100c060041c03804180032001030490400b000407895540c011980b0030340801702d102004180040744000700f10f04140300030054405244420641340d01e07404d1260b6542c005201d4031021030030060070f030000a4400c80c2010141d40c0041c4c01180b40c140c0110313403080c0b42ea020078141c48032010700e80c000000044038030900c18000c0c103040354110786801c40c500303e0300d003848010155007034041c4001080d040302100704600c0c0b592014048550101c19034030680407402d80c1c103201a244040400c0040e03140d43c501084003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 875783174 1250 875781924 875781931
    0xc151a0301060503030c15060315010602010203060f0618010f14030406141e070813050d0e15161707021002030307080604141807050a03030201060510020705150307021e06 75
    0xc00a1100556500500d81c907489032044903100b41c0c00420052801c0c0707542260781600f00070081e080f24682d000360601025250002e070403000051350000705002d910f02e0280314150345150102c0310249040c0d05822032415100c1a80041ca040c0a410118404141d02400c11200e6844c204084595030b40f401d07282250003425800c15404500d484000411b60049000790090890000701540c05000e4845580950319000020f02c084a001d00714450700002480512407060703510310784d031901008412144100003642e000780b840c00b100d0080c144140002c002a072002d17001915008070380801c214021a102004912929001075004840c440f0604034032603000004510900d41e60307943e840580c40381d00410090303400200700098500340500c0030404468507007007555080710301c07102102e15003079175540800c001000c15481a40583d41d50b5200f0800d9081401252100c0102c0b84007405402d82410001103104400445a0102080100c001800310b4000c0125444d210760f183c1000700d504185840da1030343c540c001c5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 875784424 1250 875783174 875783179
    0x1707051e071a0118020306060d0f0507090506031b070606031205270109140f040e10110306060712020c0303070f230607050d060b0301080601030b0c03070905010c151a 73
    0x90030b40684401e007102c081d042e1501c0700035640c9083d806202d004040d4101515080d1301039400c02c03c3d2018064542b080c590480d86045010880c3d14245030301034021150742d0300c02c601500040040150114010148040c0c022441c1d130382c2d035200c05290400c0d00007010320343c00040104480d9107100c0d4100d9004405412940c03000405403030603a255035103001c00c49054040040c04914194018403130080301a1141e42200405440c15862100d01000501500e26028501e07000c0e8105142031042c80b0258012400e5003070403160141d04d54185800400e42a01c00c00c18054807216168a100c2d0b50700c5e2080c8082680241c3c01002c99403911181d041020b9110072008007141d90202200c07204540010880d0450920310003500944a141d0703e031241928654081001054055a01c510101c0e00c85083d0000d103010300600740051803503604600d40309180c482e01901d64402500244100600c19500144040940c0d03400c0c07030301c501c2c040210301e000d1540012001c0d608407030504098400c11640e4582d400c103110031104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 875785674 1250 875784424 875784443
    0x5010b040503100e03120a021e030105032826120124090506090a0b030412111b101b050c13020405010e190305030703110c01050a1707051e07 62
    0x903040c00c6011550200b01c1030004d07820a010b001c20010a85450940c0815445405860b00d10304900e20908070a00010b847c07800c60003c4010b110a040411641503100708004203111940081e1245d07228070507040c100146001000c2e030070b0001c525103908080b04e0249400e02e003544c90707521b00408068400d000b4041c1c1100c24858005201000c52114620090010340703031a401d20003403c10040c8002680090992904440076460001d0445440c0e00214071840c004c00a550000980742070042c00ca01100071060000d510046950b0081602101984009081100c0405210244540580e60030b64407100758407040170708a85801c240203000c110004c846804036900a10101660410001ca0245000b8180081c4031108440040d090086081e0b20400174001d0f2821100c4d629580d481c074607444104100c000076400c056101030202c04210304400781c0024201103060040700d21005007440d030050032454000c030343c02c00441c89141c0101d088851860604055070540d40c140c1d0300f90010b030390050703e080301c0d2400d8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 875786924 1250 875785674 875785693
    0x504051c05090904060204050d03030603020a091e020315150a080702030a1b0f06051e06040b13020714160f0e2208041e090b03060609071d0405010b040503 68
    0x900c6915100099403901810300712900b00740800c581004001312481a402c200104403070f500d071241c040105200740d501140c2603046105010710300040742d210341105401e203050040410540c1203a12003266005200603200d544e10301c48002e030610040342c0a034002264402c0c14050b1140c1400904024240392140030361501e455400700c2e6284641d40c02180000c5180c64408038251003104076a050300d0007140c810305050303810345501c01140c40c01e4a814021082c0c5a41742030403117868038003a80e40030380215030400032000701300003007a000725070206d03161001c03940010a00c0402260903c920140754001d02168011a0b000304c401e03040b1281030213a2004104202d800040075029106034611906449495051040021b00b40c3c903e042e130700e08000c55500000388004184c0407181c2c60a6089101c0030301c03000d81d03c1840c1400721411a182d94204500903005102042856101d96420b41d822084902d40a1a031840e04030001c072a01e06099011903215003414000034509414101400c10b0b180c045055130f034030b01e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 875788174 1250 875786924 875786953
    0xd110f030d08070507050307080f07031202040602031204051f1d070521150c190302070c0e060402210601090f08150a02040305010e010903020d030e030f0705010915050405 75
    0x2004481c200c0c0051900000901030500c59005440305c24861b0301240e040824596444d8155045128103000d8540003060340414035500190700d62804001c41021031802e4201300340291640b040d1050044080020310100e000c0217400c00c039000b1000801d00c410175000e1903004260740034210308035011102800581c0800d11042001c2110402c0ba00300610101c0210b030521104110746030207032160f00460140e40d42074502001071420300ca10400010040360340d0f0f142450105c1c004082004803110030144103100721300c0010940d070202030a4500a003c0142c442d620000010b0191003035069100600b1988a41002c540443c024060b0203030340240c03140c401c400d0f02c038821030044840300d118101703841d401140e55402a1800006454225646807000b524103a181e07280d090075511002003040b40c1d60340d110f0800d000d169051200100280261a052000d04900001940c3e170380a1281006528000040c640007089400d601126600f0303805058825440913044e100300c001d15045405482c04d00803651501703100e1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 875789424 1250 875788174 875788183
    0x3090e04062c0a11061312051006141207082b0c0b16020106050a0305031801050a2a0b040507060f0c0b010e10092c030405030c060313020d110f03 64
    0x4100e6500802060040e500d590282004c404d03d41a0002c400b006240a01b169100290001c3c241d003151012505a040c61700300c0c0342401c00c83c41075210500e084e00600050a030b00405040b911707002c4a200b00942d0385050070508106190f4004881c901c103080a024680c15404840d040b10792009481c10b080c06581101900c0306200c0400003000c4102d40e0000a80c400100300d15910b2540c2c0a2000007829070720394000c54103d000303d400683d5035610204201800c180c912020b00351b403080070f10b416403d108170041c016161000d2000610b10a004000340d5044c0c141d1002c40b211101e58004501e1210350401741450341c0c40302441c1c0500700c00038694146081c14280140c8094880355403003c54040c0c0d5a180400000265002070032640301400a8200050907040902a0b08414080c1e41440e100740703625941010041042d51061003d5500240810020381c0e0700801c18403103841043d00c240b666950b40192581c2c400e20200002580503404e101c00f241888502d20221000c2075003518003d2201281d0410150b58 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 875790674 1250 875789424 875789501
    0x32715150a0b04081228170a0b060901110f01020a09051201110403021020010c02010b0108090d0e0303130f21110609010302070f0f0507060c0b1303090e0406 69
    0x466000a1700c00303050144410041440b8401c5022400c0b01c8255048960034855a0f82c1d204000140700d8507600c41d40c080e4042c207031900440e1030941048110403d002194140c09102e403620306100350107a101c800642c044c00540c6410003500700840d620141044040c1c901913441c0a460301500642000400b43c120511031042180c2c1b5050065007400e155500700f01480445091020400002035868101d54100c0d540718404080d800002140c0614420070082c2119000c5240d50304101c1c80d60309001c4142000300301504103002d80d1626182c1142c450005ca4503501c940d802510040802c0c0d20f0005e1801b80c0c210582c002c0c0d41c42641c0e241c580300d00d0030140c030900e441c4102001c0d05240c000e680c008a1403414100400751800e040c10054104801600d600404141d00b6500ba02c0203a848407202c0e08106050100101410140c02c00d42214502900e4011301038600038246400b010600e4080014035001d621010010011410802d007a4501841c20b040500400c207481d102c001e500c100b00c0044041d219510a10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 875791924 1250 875790674 875790689
    0x17070b0c07120c031a0a0b062809120305040303020c01140d242402121b10021c0501060201060b0901121808190203032715150a0b04 58
    0x140c1414240c00c0c14101404800c2101c0c402c0412030000001800950040801042e4821148040c90032030441b501752418415058402c843c00c0011030500c210003200b0180d401001408490103c05146059a42c405e1540222010744038142d840030070113901100a1040e40d20035400d403584181e000c00152204180701000400003442030003002c8048860380d00076000c0c0507081e03120001c80d103544003102204202641201c1c0c00f40700c42e03a03441d202c40c400c0d131000302804040c184002c054084001d8500323003040c01060b4040c11449031340c10001c0800351082183c8012221200703400c40d0307030b03240c0074580e101c0b04c92a0016003a17519013000300016804d0300610a1104aa44d013191251a00180000441d44c031101000042038132030b0350740c032030350020340580c190200d503d8071031100075941d501648042101c1080034100700007154010400c204040e9200c200703403070b01c074050000c000c0c54403000001003030f007440f2060030f140700120081010040b841300790b000c2c0d00f280703008140c4000d001943c07100c1420034144230701d005084 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 875793174 1250 875791924 875791933
    0xd050f340e07021606020d080c03010605070b28020c0c01020f0607030c1115040c0e010b190234050111190309080a0302030a140304200a05030717070b0c 67
    0x301d041100349168890320502c192400300304001580b400d480c455401c80801680401c84014074960011000c1d508030524040e51411903162020081141c85032210003444152101d0205051112220142000100c601070f002114510301007548006e4200d4600d2000511441c858000c0031750000c40c800c00c0a03132021700500440d58980e10140c01900d03008036070b20108110b030040b800090a050040c0d4040c09804a10643c0758142390030b2004082080d0b41140b00c00031454001004105100130031110419082c034ac0c401c03184070441c2000da003008451100c4500403c550303010070300014030440001d8460606180209140b80e290300c0112040405038040c840c1070fa1000c1400e800a400704150102d00300e00c00d20b000f0071800d44414149040c1a8030110403005a0b001007211101c00f42c20801a11015000100c43c0c0e0031840c00741c50300442100b0030380202c1c0c00e00e109510b00c134480d0384030038a105024040140855512554840d101c8209100c2c3c201c4140e858020320b6004681c0501d980102d07000d41c0354020050 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 875794424 1250 875793174 875793179
    0x105240d0b040b151203190807020d1803150e100915090809190602191208040201030617071d040b0411041e020304022806030b0d050f34 60
    0x603c02490041c001c4000341800400c140c0043d612510401e0300c104101000d162210400c88101c4000300b4150060018410040100060b80354001003a00034100140740c0b5a41c6d0b02815000d04181055075040a04009200007104001101540102001a8002c400c0320b1100c2d816035511412517900c0d040040404a240c1c488016040641c6c009803000e5000360034292818a0f078000188541d80c00300c0780c0740001e110f00c903800c201c4e09030103003e200d85e04408101e030105101e80594800754001c10402d4284c00b400344280103e025640f0990007500540180c0c8880c02008040600d0301c1d584000b0341c450760562519501440300208a6502d845001d01e41c001c1241c120b0f41c859039956005c02100c03156241d0802e543c1c00311104440301c03566510300300311020310006035241402e00520095594002000080c1980340400040038206852401c00b02c580741e00d4000355541021001401d103030070001025000b440740c88101c0800200c007103500d4904400fa480400e20a512104910448441502420f045600c00e10f008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 875795674 1250 875794424 875794433
    0x11010c0903080d0e150403030c140f0d0b03030f042c01180902030106140906150906071104060806190903090306020901050904060b03010f06030213051c050105240d0b04 74
    0x58800f0800900c0049160007811041a140910650100c1c001030010424841416050706c1074800703001c814504241c2d007100c40340134004503101c0c91012520800c0d0001d8800c0c010409940419034030701c4000d0070f030b980d1440740c10040c200e2034202c1d003c2e140d060030450000b9070704181401061960307443c61069042c1d050f0300e4614110000803220103985002500c030f650031401680d0038400d43c400381c808000400c00790860710040c0729035240014a001d020301c800301e80c411500400001601c4c0c100340e00700c0d0240c0d5941442d1401c450f1410b114041690001e0400c01c01282c00d01020034110f01c2031f0101c080b1121000784003003000c0180c0340300c800080c0205881ca141800400c1685d0001c141c00d0206040c22031501c040800442c00300e40c0fa9600549001307001100500030f010b0000006801401c2b1850150b090481c0075408110200840c803480d44500069140c10702c000b144440e072850b07840d405c10001c008529150800d0441404c0415240e0400c24220300040540e1900e24a1518415004400c0c0f801903591f03a82d9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 875796924 1250 875795674 875795677
    0x6030b0d0224040b04080109060b062106010e040f060e060d0812040206221403010b0f06030a11121918030e04111605010b0a0b0a03020304081204030e0111010c090308 73
    0x101e00da0b03040401c00442c201c0c000c1c2c0002c1c001440e515000144004080c2000c208a0b20f005044030310601e010000381d800c00d140b82050691000d40030a8140d015100d000040c1d4100d0140340c1c4480c0c01500f092000d40d901c07540ea900006c112440850701501390303552401040050210070100030400b00007032028207550706071101000e90051000c0c2c41c00d172a207c0c1c143c0344404d020080d10a403146c56145080e040c40b0540c40b0046406411405030001d106480c90803000a200000b02007640d400756001200044500c8081c1e0003a80b00ba1440045990792058980c0068030f160204940e0100011500c00c1c0c103071100c080c540314070002c0c603a80a4081045603441da60031031345410010382c0190702c5519141d0304110a000c1000800002100e8082480010b8180c5829400e640ea5103000350303c0b4003080d0301e0402002c9004003c40e003c1c0e02c450701c3c2c0166a80d80c1d0b0700c1e14813180c0c01000e0bd82e20710019140200010560090407003108024240c0783d0640c0201c526070440c0c00d80d00c20007004000540075120400c0040c05100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 875798174 1250 875796924 875796979
    0xb030c01020304091a061b070920071104020a020d0206060108071d010201061502011a090411101106010e0405161511031908011e2411070801020406030b0d02 69
    0x790502d05e060702c0c1c10002041904003100141d2000b40d10020440318001c00c104200003003080c00010311824008503910005600310b080c880820003c000340180070005036080f8401c140200401c11034481346070a10007507a0710141d16601c0c01521604006c524690b0140b00020301c110131590300c042e40201c0c3c0c5c4070030f01c2d091003014801c5810341d9251200486d00f695808403854161603140d00000e044039003009000d40d0110301420081c041c185020601001c2034118107500c0d00f03000207452007401203210038012207600100d1b220300d00d400d0041e030f0004a00584000551802035000d0300803159000c0c00041a203507402d2580c414600e0f0782d245690741000e49400380c14842955440380c4c0599007001d080142581458480030042c00000782038100601c10b44409451821041031642c81010210713082404000890801400302255250615400c03402c9030b204400303c40e4051849800d44d0043d96441d68840d010750028003902c40803a040ca0000c0c201810480300394034180750004d082526000c55074901403104c2600c4c9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 875799424 1250 875798174 875798201
    0x41203090212070602010f0f06120b0709080321060f010e150403230d0819090f0204020a0e030706020d0e1e0d241418030d0c080a0b030c0102030409 65
    0x20b85251001100500030040207240c01c2c0c0021400c1a54030203044216070440d03040304005454600c0500014403448144440310360300417491f07407013a2101902600c400e002c036400481103200004240e1411f8101c40c041420b0441a045400102d441c0c9504021b06d00134250720450002c0d5450203644600e10b4109811450840101252494140c0380d44500701052409000c100c0c5411110151084c0c40c6020421413180103c2450094400d06103003904021900c5520700032800151184501000d0020344204035141a500030421980d0b1504100302404206020642900c24002c001b800100e060002c10b0710880c0761006c1e0744d81102481110100300d100f00011546d018042c081c410703d00d01c1c80e214044a140018040c041400385201c40244484103590050b00200f4405d04006107221440c4a401116410000241c10f481c1401d4076010024514003c080d42c10101606011161000e40d810812203405101c009406010074010708080c9960303124182a440d005a00410003000000d52035409080c6c5000b80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 875800674 1250 875799424 875799439
    0x5030603193206100f06080604060f0303020a0b01090203070212030405070f080303090d0e090a090204090c06110f070608160233090a0c06030908160809090a050412030902 75
    0x198084000d0042c0c0c10100040703100711991000a90904109240d4892002c00f800c4000c00e0800c40385540c102d0292280780705111100300030806a503a607810040140442074444200e40c1c0c0e480c00d00958410400d902038905556580010904009500840740304141c20740040c12203581001c01c100c1e1a500042043d202da018002000c01d10070040101d00340101903080c000c2d6200c4c18510b5003d410006510019802d022008140030401c0d20b4018034140c1c1300844410003c1d0782245400803a001d4403c1c40001001c0424000b4003080007034000c9040181c1c5401c503c122881d0324a85800709507190850700400020440d240001940c9072045520540366080c00e04c1900c00d6100c2d50f0b10040c0059450340c0c142002021851040007040820054103940b200b103001c0203000d04001610b50484007900c0e1f02514042507205c26400c024881d070042200d0f0b81502100308195800600c0c144100d0507003125890600c01e2142c0c0c00882c0060007507014040c0900d802c06250750740c0c40e511600aa004003422601203070810b00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 875801924 1250 875800674 875800703
    0x50613030b010905180c0904030f02152406031e060a09020c100b1f030c110715143906100801060503030418020a02210405030c010503060319 62
    0x541e82080c0c000c1c81c0c540e101007054104040c10741c00d28001100340404a81c094080300c2c205030f4816480c0342d045501400c0500d22054030f0b080c101c5c20000c41d2131560312800050424403140013440182c040c5402e014021810100002e0350130005d00f4481030711845445000d003071410850040382e89038582c00c02401001120800c0e074a4500700117a801c00181301d28903801202c402a488500c0d4010286c0e12001102c42c036140e86002c3c512260001c079a0343c010700800d83e80e01803428081d0b000b90940b4618052440c125101c2e10354908001031606188950000000d0100e00400c0043d0100030540c2c0c190a883c83c1c98000c0c541400d902000700c060f420b040f0146803d5840702410940c10b0a01c0043d00a003400790340c109455041000a5080d5402c83e80414080d41c003c200801200390140844440c1e03c4050038090b988440c3c40b0707000c80ca410821043da442c69502c00d001c107402c80c00554010310480d1001e0302030f5078040d5041401544c42d40400c075500c68050300400301c03020090891070a03800c040c61160105141206 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 875803174 1250 875801924 875801933
    0x61b030109180203122203021003090302190b0a0e0c1509010c0b130c0e011446060801050a05040509101a040f05251403151c02030705061303 62
    0x8442000030b6545d504000352415800c82c2141c5500c9040d078290708441703101882d40d40403410a00342007120004142d550b46484003010300c2405400c020040c0307407000c2054103805050407a080b1000b502c01100091402c1c03449503442e0404110315001c0c0c0d80c01804c41084050750880815607512003240503040041d850040400286140c207600e001d5024100e1461f0113038103a10b0001d0301b0107156040708003143d200b9401001130b151000c400b40003000080e45d00b00040c141c04030a401d00040307000c000190354150719001da141c3d101a03c80705030304406408413100c0070301c2d92808140c0303220a080c001c580d01710071100c40500c440d0030319402ca0b94100d048041100d18950080c403811040b903441034902c080440c11483e092103245024043e02c030f40002400c2d0100302508280c81d146203003c900540f01508804642c0318004400d003d84011448110031580320b03940c0e45404200c024004500c40d1103144940b00b8020440e01c007600b00d0030b80e14a041d502034001c003222400e00003045140e170000d102c141c6540b0758210002c40002d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 875804424 1250 875803174 875803183
    0x16030f0803100801060b0a0e01090503061306110f251203050c1932030a1d0d020703033b0f040e010b030c011e0f170711061b030109180203 61
    0x200001040b82c0e8580c0361f0448000c02c20030300c4064030b0b030410515000900c00c5507008070300d07280c200d0071840c10909040101c0c13610318058072586003050250380c0f000c18500360b4607880b54010260a40782190034044040c00e284071000103652401c0c06070065000c00c1c0f0040e5041d01030b40c0996042010300307e2440c1004449641c0b44407010000c040f10707000030201381c2c403002244c0b001c032002981481d55842c014268105c10100d441c65000062940d16050744400d140403c04c1d040d504404a4050440182e90344146407a1010b035507401144000c500003101000c0080c50035402c06d043c0c4003040707050188811035101400e06030301c00c50121651981e21000180100400d5a1540719010380c6210341000031030380300181000c2500389100c2a041906104650a0324404001185800c00f02021142801d24403a01e984d5411551140084141542001080c0c24041101c1d00b24000c0445c0c40055421500030342c1d541007100042d048185072045a0900600050042100f55003151580c0f00181c034424100b40000d4001070b181 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 875805674 1250 875804424 875804429
    0x7022107030215040e0408070309081204080705040501030f020907020c062a0303010b19030902120109230a06090503071a010801062301030c2d0216030f080310080106 73
    0x803a804035400704110300342004034480c509402c03003c3c2da04151500501c80c2480300000d100810f0000c00003002e42c101802486690007419074802241c00c0e03200b503000030241503070150190300404c0c480c003400000c0e01d2a09000b42410f84c0d0307100e461044030702425401d0003030f800c5000d06060154007416050140079114180504a07500d07100842d440c02d040d00c41d1102c442d12480032011079482c0c004200500c24200020121110071400d14102181441019401c80c020f1200800007580000d070540040481c0c0415080420200d000352a5100d42e00300040941a40000c0300250b01070b19000340e400c0d140460301c2580440601e0340501c00b9645801c5a554680c04007c142400d11a40641c83d2401480b845400b480341c03c002c1d0078044c407483d446048200100b08030701c8480315142d04241d00d45c00384080c840e100f040301e55158000c10b02d48135202500307075460004100707010860314018401c40241d078102d4071000c28040101c90700801800c05114664a0b040181d0744018004c84150015150000b01c0e4042407082000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 875806924 1250 875805674 875805739
    0x10e010e0d12050403080601051e0703110c0108060a0b0c030903011b1404031a0a090f050309010f17040f03200d1101022b09060e07050909120304080702 67
    0x1e60503601c102030480295190315068080ca071904110020f50440829900440242006901c481e400768080c2c0030164004512428600085800030400d0740015103080200034010645040001e054011075448a0455900b68042c0c9450360820180103042d0061400d0210102564a8803e903e40841d09403244c0c1c82c01c1540c8450158925800d02d40d1000c025102d009180380360510b017a1071521b8800165000c13064140016042e0408524001c01c50b921188100f46c0c0400e01c01c0401059062064680e007100d0350040c049110224110340d000e00c5120031408218400c80301c52001c0d2540d07150100c092a444100f1000e0140c030003d10f0f032004006040000747d80f04079000600b4404c08140004004da50700d10040c0601c0d0b801071104410300410b1102c41c20841080d0000d0442e400b812844620203010420409403105290000d02e40c004180030820300183c88080d01c5500f42038444984055444000410410616605101080004a04100074000c20f03000600b210b5100b07201d01d6503000200100c41f080e20 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 875808174 1250 875806924 875806933
    0x30106030f140d050403030f033603030e0703050a1e17030613020f0a1d040212010509090d050412020105070b0c0702010305090d14070c0b1603030b06040f050f03010e010e 75
    0xb0902074108000300b040390ba24600242007a20b542e5010349490030340d1446c1c500f4181c0310341c0007513802503040340d103141d108001651210509003889080501c21504400c140c00203810400d6581160000041d44402c82e64002c3c000c1a400706640c8440342e03800010b4042ca0b40c1d42205903142ca000c190340a86200701c5242040c00a07669091100030400b00500d40c0f1521071540d4018040039100d011b0760000d0b02c1151104d804d2400c400141c0c0b404400c21442d02c2e4010a0f072140c80810107445429800403c28140c1d14240d07480030340c0c0c0d222115015940c1c03480b00d1031074000a00400041c01001c02c0007011000507803041c180342d030501c9a29680d03070000107000c5829032a10940881c07041c041d0340c0d240c01855044281e9002070141048140401069499006003114602800182c00810810402e9118004041061a007a294a50100400380030b1025800c15400641000160780f0780d890300d00300721000c44a00c0340c64100c0f0140f91106022602040000c0180d05558801e05075403109001c0c020611160051000752 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 875809424 1250 875808174 875808203
    0x2122030327031a07030e030c071409040b18010e010609020c0606010c020a050d03200d020d03020f04150c0b161412132f10050c0c0f030106030f 63
    0x22006004600900000100c1d4034810004260141e200d58501e00045449031003a59600c1e1081d0040c2c42c02c4450407100e0301c00042e8440c02c000010802000b0f60b031810070b040483d036460904006080c0004e039009806441010045000700b108103000010743d0b45404004101030f0103a1b0345160840b43e00c0d40c41401a03540018840c46071040a010196001c01c1c242491307644001d43e1f8010601c10a81e40c00344900420700b580c02c010038103000e00e8140c481e210f8040c998141502003d12190740350203003121050090b21401d0094003405009000307440c591091680914100b03460300340e8088404c0307400a03402c0140040d01c0c0702180072030102e10b04148a038504842000c8411502c40d0000c0200c03450700203440c1080000d01104204000411100350084003441030039020a01500300712016a407030b83c41c403803d0110070003105400306060341921610050708540000019100c507900341c4207031082c4829000340b9042f00141d00350618110550807011034002d0000180b451b01c82d83da0074488600b0b4102034a940c003c041f4034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 875810674 1250 875809424 875809457
    0xc090d210f020109050a0b09011503050102280512040f0614060a14030604080708040f03110102010c0305060d030807090810020c0d0c260f0406031d21220303 69
    0x40512801c014402007109010b2610b55a40312808208018000c504113404110320807400d4201c2c1821207a40f00c01070050b195240703007d5000798061002180b10302d03622800d0318030502d0100708039001c0b002c0940302e440c604100820050b90b6100014801ca5075181200b000f4008100c140c8691042000707604200020b40c1094400c01020314001d0303000e03507890b00310845540070359100890802e8000d40e000c030065031905075602d049085800b45800c58956401200380000c00d0000704c072951020032400381c0007000a01c40c140303400c40c217944c1c007151280d40103150010801c0001e03104030034465100c821031030017800c0c01e907c440d4900d060081d940455200700e41c0100d001d2410311824030002114461900b0302121202d143d0399008007104803d800c81c40404e8070030941c10382c42140031085a00a1a43e4410151303115100c80700a07000340380040c816480703c2446001d0007d170b0480011038230961019240180c03c0060403071001c00c040c2c2d201075113002820319901e450140000340500c0c80c0014500c651209444100c5030480d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 875811924 1250 875810674 875810687
    0x3060b03030f03042306060a030303020309120f030a29010c0510060611060108060702070b210f0103031d0108010b0c01291002030a0906030b0102150a0509011406090c090d21 76
    0xa0706510354202106000c210384d102c0501c4c8c4200e940c0f500303000d41c92f503a50000311814007400e0501c1d1300c84100c000039185440b41d08000114826152002c003041030f010700e00e000400741c0e030b1401c00c0566190308880440c0259801141c40c030301c03550720810480d46100c125010400903240158040d50100e042003550440041092002c030340900f040d42c00a101c02e1900c80c00080d9100401d2080c01c210704d04c006048038a122100a24800c03101c1a0b00c2202224100103c1249d030078902480300303800003035141120000c2a1303001a442a01d1040580d40c0c21450707400c0c003112190315807051031030440300c0d035031283c4101d81c00d00b0b01c80d42c59006100d641e101b5800070f6140e0341400402602c41d0b61560464000b00000f107401034020107000c06a03a0fa40c503001500c0c0000301d005074641303101c509410030808000e00170050201300640001e403250719044001d001e50310380e010100b0000042a25016844820000020f031040c4011015068100300180002d9910071540c8070300088150310481380c500340505c114081e0a5542140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 875813174 1250 875811924 875811983
    0x607121a1201050118050426040806040b0703050c0703080402010e0a03050115141c110a0801140a0b0103020a0203030a200a08060405071103030a09110a060207080c03031303060b03030f0304 83
    0x88051256103056a50301023040703580ca00d01101c0b050a845d0381d80340c108081c41036401401f10002103a42d41e0410342408940d05a0445032000028200400103003480340802c01da03280c032503144d1504c0e4800d40f290b60040d1804003c0145454110035100e400002044090103410001c021300108108540c0c00d280060402c00c04410600d405441201001050002124a440701158120710f40c9041000b500000030090140756205107200d60801c0580038005406030380c0140a0070f241e940070818803241e68010b4040e40144503070040503800c10b100141310390b002d0383c01020a00c604030103215140c8030314180001403a042035079210000f44280e002c002e030710300701846226040300280c180100c054410f00c8800e6940e100041190002c3c41c0c940b4250803c110095801d400404001031a902003030b0f4507004000e503140f2451080b04480e00c0381c002006064100030084586018010084960050450b00d0312405020420074660301440100001c800c2000e40c4405540103a100c7c0c01569881002041101991140301 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 875814424 1250 875813174 875813219
    0x61710020921010b04020307020c1003060803340f26040302040b010306080d0203071b0510140906070c0e070f200a0f030305090706020607121a12010501 67
    0x1000902080d58426a0034440000205000b2118040c0345880074098110f07940d0640d0480d00100511007029004105480450001d548207a0111085c020840036584544988481d41e00200100181d100001640b140c1c00414140650642c40481170100446000e030f890940c0c50420a9049100304481088031072485175920a0a80e00096400c19003030041c4580e00c0001e104550b03071094070840741d01a410890042c036100e000da80d80741e0700100000e901c990289070201e40d06941c0e05980551203944c00d414405480e8094084034005c0d8041c1010340d000e03041e8094543c5400702c14401c041c0707030f540c41000811466100e405d88101d0649406403412214030054600821f000004802204265001d4580441440720301840d028800c13402d06000d04007d0b0000b4003900e004d21121606040c950103410490080c4104c0f41120342569a8420481c0c07145d1041da580720020702950607081d040d080c3d6411504e018004028240e2129087c0c1d40003c1440c1d01c642c08911060351182c00411040d1a0503501c90018185c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 875815674 1250 875814424 875814427
    0x20c09090c010203180f0a141305091207030507050d090303092909060f0409050f1e01090507030e1b010e0303041a0c0c0607030801030b390d06171002 66
    0x80d413a40959500c030a00c28071911040141c0ba51044501e40d43d1280240004265039240c04004c40b010020180e140e00400300c0441844506070b051003980c1c4512105409411202d00301c900c808200c2d88110425402c0100070320103000800c1083c8102e403031807085626099029481c616010700302c003046030300050b001c16110040c5a840e043c000141a038004d025000aa0380c2c11a001c0000c240b0300862000c103816213000f040c01b040802c4190702181c0508800101840d00e0ba4170600300d141703100c15450340c00c00c0c500541c000400442d061501f023550041090700703011402418440700a1b2925002d1048400950705044070240c0035600400203103000503058020b10300c0c00f4140030319400c40344403020201c0c0c2100310001d034148114400f44202503801d10000c00107540e440c02c2d0f06004160300d00a0100359071801d0b14102188a000d80c00010f244101822840042c1c21030110191100d908211114101868070801120766404624820b0030060300c00d42d407a51501c1407984280601d0a800316421025240c070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 875816924 1250 875815674 875815693
    0xf0d02061b0c031606021b07091a0604060c0c0e07020309130203060303071e06090c0e0105040c2a081b01180c05130609020d060302030c150d0b06040b030106020c0909 73
    0xb000c800ca403800c440c680700d6014040f8251034144001d20800c03e00200c8820442c111490201d0049030000441d50500c8052094065104c00d542d0606006003042d03500030001c1204010b00ca0190038032080042c010b500079101c1c0c0395550209141c01d5001c44a610050300300081c10002072a0240740c400f1140030f4400218118035010021a98074407410b400034003145180001d450014040015102c1c640d60300c40d0003401004070918004c0020641c42c0138251815590000110741e60401d03200b00c043c83c0a8580e20154914200004d40d15003408281e034007001a01106064000f060384200100030341e401144071400300c0f8190310b4501d409c540240007810303040d10b041100000030681003452102a03071070031120241510854a0100e00802599024800d050b0010540c0050124141e0140c021240280d050762601d4080104009a404c10a0001c07003140800384421a00103005600812543c000900113034501034440e2a80380c41504244d02140041c5e0003400d0802c0f00d800e1541507aa00031503100007d0207050b0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 875818174 1250 875816924 875816947
    0x1050106143103170f0711040213060e011b08031b130f05010f1701030b07020705060309010f060509071218020414160c08040e090f0d02061b 62
    0x71060040c54070324010120700c1c602c0e00c40b080c0724507459240b00b195a0000c8034040c802c408a8001c01484107a80410700e008200000b404a0000c507a1044200824980380c80c0c01d665482c080360a031442d00c250825400d120f02e20440c2c003035414020291900ea1214500b85241100051a0f48c1d841c0500807425000c448152001980040550b5000261020480e006640080646031140038204488040760b250440000d140c0d401e84102500b07403682030b41c45c040b1700d008894064810b40c42d445c2114850213858001080407807018145d50f43c021b00588142e0341200d0795080003d4030340d0000c2c0c60b001307003996544500700007107071042c0f151100038030703080d0b846002525000102818040d10301d03208041c21600c0700040c10f0010201111100d00d10350041c010420915a0b0040221501c03044900c4000c052828030946113260140c103240c1e020b180e120000d06d25207410140308004420010b009060340340324440c46030089282c22f0102030410b89a41c1d0044c01c2c10700c0e08034014400350f07002070405c01c0b03100d130100048a00d82 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 875819424 1250 875818174 875818187
    0xf02120c0a090f180f0c090225050304051e0f010f02030a050d39020613080f09040207081806190c020d02030607091e24030f0c0504150201050106 64
    0x76110070350005203c1e030b0100540e0700070342001c0050f00404605a1600c1c0308009040160f020514041d0403500e104a03150079000c4100d1080c607185010200c02072642d100f8142270340d402500c0091103401500d080c95520008070724000c51005004043c0d290f44114508541881600d0000000d000d10f0030011883c54040b019450744180c03569038080080010300015600180c0d003044807009200c0013040c0040c90b001501e0191413001d00001800c000145402e030116910001300240150411140700f41c2c590310503a40d000d01a403140081a0800c1001d0190300c4007690b40e44040e000742030145005aa40d4004082682c80012030585203901c40e0800703210b80898035071128900c40d41a09503041a14001d400b40c0001840c2e0342d0bc881c0c0003941031190004001d0080d5105540e078084a40d41060f452103141d51000e06182c80c281c5d03000d044180301d51030400c2896124034103504502080682800150310660840000654600010b00000700303000003000c0201918000200380b0340b12061000304841d50520790b00400a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 875820674 1250 875819424 875819429
    0x102120405060f0304050106210b0f071e1704141519050903091e0a060207121218090b01120504021011100f06080f0307050c1302040b070f02120c0a 65
    0xf5101200280811009502c0800502503030030101d0180b002c401203200d01c0080c2c02c041142c40f80c00c0c1001081401442c10205c0740140515100d00c81020341c90302000c3c14141d070010b110400c101042040d000c0c101c01c019011401a40a40c00503110300e8884611680742040051500040c016020200886e10a110b202c02c560072600302d5021031683c07250754007203245000380c01c081603001c070884103c034580c1d0b482c0d04070503400040240e40550406a9401040e80ca4140e07a03c589010754521104880c00103004980902d4036021600745500e40882c0011903003d51641a04503026407a80d54202007003642c0c0110342900407004018051146141039408a90202c403a40c01c51000e0200743d55410a01203001d1140350000c0301000410485215a03800d0540500a90310800d0220b004400141003015000320072200119008801081d042401009210b0040e1f107107256150310702d40c00d02000c1030902c9040001c085c064042c1d00b03a40c85984281c0101310f150751070000520b05542c011500501c81c0d4840c048450704 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 875821924 1250 875820674 875820697
    0x120d0212190c02060702101205010906060203070b250305010317040b16060f0f0f0509012901020304180507020c01020c03120f0d0204060210050c04030c0e0405151005010212040506 79
    0x20b10b1502c00314845010307022000798028009845110755541c0401101012441c1c820240581c1c0d0340d51110104403882402150010381040100101040070031400310741089550400d910550545ca001091007413800d0302d4400002c0d1240010014850050740301180380b228142c00c689094036102103104507104040d65081e000c0d0300d001c80c0c0000e02045030701c4210481c09694003804150382d903000150051540010408005217414003013200c848052045a0000510451450665030340c85041088041c1c6507000a04502c01040041150311f500c01c500b03e0140c0e0032110104035414140d070042d00389400b07102001e0440d4002c0d0440f80c015940010070720510301e81c04a0003a80c84c02c0e62070b0250160310030864264082c40c000100002d44950000700b400b00c514854508010781d46a003040f800703441c4100e00c806041000544004d00c10303a050000c40c00e4006105400f100c3c1000d00e21401c10244513030482c0c0b00c200c1e60903500c204208a5070184690111804170707100c0e10b4a0542010b001a0b40c0e80265459144d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 875823174 1250 875821924 875821937
    0xc151003030c0309210303151d09030904091211150115030612030c050607031e0519060323070f060f0522050f120601060f020309120d021219 62
    0xb001d1600520710300c1302030441d40c0d031034a07403001002c660000340d0080e110003140001d1802d16031040b0040d0f0348881c00700b950b000c55a00030800ca84008050300080000d00581c0240c00708005030b04596943e0310500e40d03124450704501799851030492000d03007510505064844590000f00480708201e03d8048028150f48079000c40094400c5e00134411001010150090715620294084100600d50056225140b1601c03070f4044a1142d960520103c041d5800000600d1201c1040d500552441c0c50b00e80000e07512141d428044114500b40e08416400d840940e4000c0e2500c0aa00071101d00424074001190000007094004160309071401d40c4500c840c03100f5101d103c0c03c000765000707d018810b201d402103445240c03960204600064004114000361551481507522502200c0712080c40d60034904100403019581c04060002c503840c00d4015504001101400303011030104100004541d59001121103400207000f0082080e6071048402916103080034455241400c418049031500c507208221542c041c161510b0801e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 875824424 1250 875823174 875823197
    0x6030c170a140c0309120703090b1806071b0b090307120c08030403030815100206070f09080118110603010510050d11030f04031715010c0c03020909030c15100303 71
    0x18001c0c4100c0b61a11202c490107000c1c407401085031405140034610000c10744450584841e003007140d038410024024007040d100300c003c001c804031402c068a96200c0010f80b10b001038030381c100014400c1e4000d231000c46aa495080d4100340c4445e16848410241402d2060245820b41c0c080020740d40b48140d1290701441102452980f04102010600c203004014440c101c90b16a62030f49030142c5841c10032501050008900c440400709454805500c030481ca13241c1d0040d18440e1100b140c220703211480b524004081c818482000580380c4000d102d40705d1103009518a00c42e10780501e19040d90b50300c4c07044090b41d100740b0040c401400240e80302404102094400c0c1011a07681c1d1210305240e020344060154401500c0f004410840c141c0100003ca921840c0f00c2ea4448540c4203041030f0618141c070301603448640002002e92114000c1d4050811420740da801140c00e4400c0990700c1d8002403444174100c40c0d428064201180819400d807041194560020500301240300038a0149a0441003c0080c031000d4104030500036003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 875825674 1250 875824424 875824441
    0x10e0601063c02240403050a0e0301060305030c0f0705041b0f180e0108150f010b1c0501080d081302010c0209070c0b0c0301080f0606090412021009061506030c17 71
    0x4aa2414034028a0641200540c0c0020b52182a04c00071a180c42550b591400741401095002130310496041c1c80c1c040c00c003c4402170450b2031614042105805669910000c0b01041082015000d00580b002c010401c051082e403030181004a144c4c05240954104851166007442c1032410701640101454544c00d032552014040314903800c1d805a640d00b010207440c1c0480c04481100c0d90505175200b21044914001200160500d8107804980d0300303c1c903040480041c0f048030045001007210b283c0c0c2052840920a003400041708903002a407040d115a803040c91541c1010360041030180d403112000c0e03400480918030342c0029040741504840240f2170405d84000551140c0076403423411038160040e05400541c03074103c08640d0554030070701860a5600c607603410701080e4240020020b00c1040040c103001140e0b00ca643d03031010000543c00c4440e080d805612620100072a10340b0a000c5154060500411009107100c00c2880d1a003007a000300c0205401d00e1070035810703641c1200d0624807003410018114220b646610b803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 875826924 1250 875825674 875825747
    0x80304151818050603030702090a150305030310052b06090606080d0c020102060603010c09170a120815040506182512060608061302030405150a090302010e060106 71
    0x5424a8070051158007107804000c1031250609481918001c01054407907400301a039034050310034025400741e10400019640032540d00242203113624100c45540c002d4484d9140c0742036410458400c225054513550410051600100382c450280e61030301c0115280b101144400982444480e01070034694844110301c0400c141d55021400803e81c10f000d0f21840380d00d0400040031030308003120603030041c800c81001c81c15501d018821903035460741549450340200d1412584180c840104020f0080901a1990034000f01d007402c14400d404030940c0e5603500c114540402d1041402e0013140c2114040c0745410104100345c0c44070010f20035801c920a42060440e84c030f480d0400381c81800d1801043c3c0e4035826240352015a074206140e04d80c0211b010340244900e5856100456003004111520781e409450145038500040c12603000350b400034007030002d80710b1b011403e413407040ca030000c103440c500f250300e0780c0309003260a245e03080c445d45a00350f240f0340c0944465454094001c2c00008200000034500640040f850a0b0810080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 875828174 1250 875826924 875826947
    0x1510141c05060603120306031f090203060124080103082203080a0e010806030606060301031704050301112701210902090103031106090304051807030b0a090f060b0408030415 76
    0x69840900054034003161200420b0b40c3c01e5000b4481d10460f01000010041a6449908060002e00e40040c16001140c101e9a46e250321030b0f03003180d40d01d1800c2d015071000c0c0601c078040c001a2004108004102407800d40100240c915002040300c81c2006000252404049032180c18800d081c0700c000c2c04104c1620703400c11307100303501c02001000c0001e069418150400c0c6d490151407026292017000b41c0d50301c020300d0784900c030440340942e01a40400060000480c0f07074030294100f000e1000142e0609881e43c01090031200301103588410300102060b860845641d6456012080c0d01014400c8000c401240003e4140d00c8400705070301ca4130141d00d88044445d4036543c0400b1340150002e0000c0c59659590a0183c1068100340e0500710303501400000410b06d01c400070480e81100c9014042000074407038100d180d40006809403000d020162225080495551040050b0300508000f0000042006e030540008003200d20301d50000322420020700c420040750340040280c6042754074401142d01c000c400244103c1d000c03140c18 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 875829424 1250 875828174 875828209
    0xa170c01060f05030f0a1a0c0c0729070c060f0210021c06080d02060f0c0c010504030e0103270b0a06050603040305040306050144150603151014 63
    0x1003000252040742906140443d10140d09483d004030200d841d40e030721025880b4011f4004201425802580d02e41120300320307407103c280d40401e414003c4010056043c441c0503403240c6410b44081191a027520b4150040032540e0103d100102c2c90302002d5550240200c4851284a0030300030203854110205000707004285020f698988115541e050741100301450845480e10344119074a031103004550000000f900703085202c030903001007806549414000d8490b1034001d144410200080c400c20200744000d016040c082c0b803080d241d41884103011000101103079144085908d540e000101c3e1144440d005059000c0441c1e0000c21511081d50713088180b501030005540420381045000040006056000000c1c000b905e11905040c03000c2d9a139038203d580c1d03003210b462098904000616500448420030030644581c00d80028101c100141069855424000c92410002045081c20108031540c81e0030f0040500405c000207a00c616030070704000c04070320701440c0d000f52200078145005000e17490f559112460410750781d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 875830674 1250 875829424 875829431
    0x110102030f0d1a0102010e1b240a08100b1c270b010e06060d0f112b0203010b030c030a0603050304090e010c08040512090103270c060807020a170c01 65
    0x1582c02c054000d105040441a4480748001406030355071060042203c004035020040c0b010303080c094203110220b0380311a0903951080e07001114000340e00005c41031b901e460030400300082d140c400c012009000c00c1d00040c10807204a590700424400442180b00f66414039900b0580f003949141c030349000b2802800c0988602d12007450050251441c1c503201d500c01c250882c421003164019990b142c4407111048000e07201c0c554095400e000302c09590300300c4e07071002d8600c095417130005c00c882c02c8006c280f40b41980203101d500e013081d40c402c14032410900364000140b0300304d2481904519540c034001d108000c501003d0300c100c00c070010010200e0070440031608900080d68120083d26521962040d00c0401403848900303200d019401d1138004e132a641d0203056007500c0395800c013003e0640e0400f030b0200d80489500c10302d5031606059403110005212110341140c00500307000100c03020703001000da00f84180301030100d03400300040040c0001001049a804100c04e801207501c181d880048250005040705140038400807201c25618 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 875831924 1250 875830674 875830687
    0x1006092601110c0d02060103051c0c060608030d1a060406030207020333130b0103081c020c03090312040303140d0204170109030e060a170a020405150901090e060d110102030f 76
    0x404440d150f14040300c18034203050000b80d03100e840920001c0c0584c0c100c030414011b40b2505008402081040e03250075440e1403415030350740782203034a10b400c415990762003c200ca0b184404240f00d02c11080f29900440303442c2d4071049001480c18411400f0b51010103802049150444d00d08000030456481c0c280004e4207003040302201e20400708013400341381960100a401291141107110b804072200f5801280c040c801d80e003142c80d00111644030440c54100d0701c500704075045074000c552002d4201022944061903803518000105407038510f040c940314101c420100802c000103038000c4071f203203452400c406699840b02c0030044010000d00440d80040040651201224a4108198080404107100382c4400913080b8900781880207038014141601e010070a81c00c02c91040b001c565500742e90269021502601e0320340c80303c0115400442945161542e0b020104040d001076030081ca0017406446c1207c0c1c0000146404000180b45c9181c0460280c500e01c10514204070b84e9100b8011214242c101c0c0740c0b11303a6941c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 875833174 1250 875831924 875831951
    0x1b040e120313150c1205040201090f06050403050105010f06080a11160b040c090b0d08090d02030313031a130303020703170117011b1725171006092601 66
    0x180c1d255011200e0302d40d805482c0c0c000185078412044c044203103542c2d400300500f0586441004010207001a418088802000034540401c0e02c80070001d080c00741d59407501c2d54a946803050075143c040e00103e042138440001402078982c8129855400b00d00d945010490a400c28101c0d0700911820101c0060140240000300501c1a03031111035015521030354441d05001d03510f074a8642141d100f0648a40c0c400d02e00b0314150082200c40000c1d15810310300400001c000701583c0e000078a075502072003451405900100d400c000740314004106200901c0503200c040117610300155a0a10b4031680344000b000d055000c107000c0240340c4159803000e0300c600040d80c071031020358440d0f04524500c00744079007040086d802c3c680020303140c4c51341681e60000601151107200380d2000780c00190704070740c05c0200385c2c642c1c01070704101500c44007504c001614076003034194607241c0c080c0900d90704d070b1400b6850040020b103142e070151404210040d4040d400e081111081442a03652500340600300010f00f0b50031620040660034000c40341c4811 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 875834424 1250 875833174 875833201
    0xf04140714010f0e010206060d14011a01090e0103030e2806031b020a08090f06120a0501061d030a06020a020709061701230c0306010e0d0f050c031b040e1203 69
    0x1c0980707600c0b814503080141114031010703624226005030045400316015042010743d000c1071510a00482800001d50031030300703007118900c1903e40154240c00d01092142c2d60400004400f40299181c3c00303005605640300600380d41e03040800c00b401819a8420481040d0380b200c0100c04111684000b849055510f140040240c41c220420303003d483780d1443d04d01941400081c1c5070300d40c503610982850820881c4410491b042d03032400a40c40d0011010480d0009003079001c0b0301c03140700705040a070008070395041200c02003075400c41c060003d04402c915490b022171941e00081c0074110543c4428003580d038145440040f800d110176548810030a134207006000c510303043c007c4442c074110580310000300300c0251004030b6441c4030300c2c080504c05110f010642c04241c80824580055a1081060406014048da0a80440d00200e403c5106591082e0415014070800600748203034500000700304c00030000385488001280800c0c6001080e00e02c107556403d201041124103010f002030188402e14825180e10b00344540f140310 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 875835674 1250 875834424 875834459
    0xf0403171009141807050d061d03030a02040f06031a090709080708030712140a030b0612090c0306092a0d1a0a0516080103020f01030b060a0906120e060f041407 70
    0x81c4c40a15103009403200020003804480c8010201d07500c0146d03d440e0007009094510400201e001c0c00c5803003070044602000158050340c1911001640ca0303141070111007244080fa00160201414882841519400013408103c031170411501c6401c90340b070b0f4020039903c07400b450b840700c4824010610001503407400400900358086c0540441aa05400d44200322200100c1e07078400e0700b1110060107184145032103580012901580540618604010034108404019003160b45c6029a8843e520001180c14280115038003c41d041c1c00910201d0040c030b05d21040700e00180400c0408148103465441a82d86042c2c03070790000d50f00207503070f15000700100200281800c1c08849400f03a80b0700b00000f1a9054514418801100140340e4400d4078990850342000b14003c10000070718101901e4000001c010340c2c82500072306005029480b5410f15074503004024000c1d5481c0702654078860f29295950198507404075110b64412480300d4807888555a52418661004c2ea900c0c92400074400c004002c2030144182640d043d8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 875836924 1250 875835674 875835691
    0x140109050d11070e04030206040f0512071202010c090f1403010b090a0207030f0c0314031815010602100228050c030d15080307050d0e06040306091101080f040317100914 74
    0xd9152012007452544c20f840080042c5d00c000005404204695419001c0c10700c40c1040d15814411064145620b400107441601c1228940d543c030710116030244104801490700f03052030a0841d2030900c1d09003d00e41c1501c1000ca880481c0d2941c410150f0f0300317510060710040d00406902c400c0c103007030030b0180003500203d10480c04a032844030380002c1c007400380ca500c8000341d40c0355588404080756003090001a410180080841d0603070703454031546446c03003840055004801071540303009542c50601c000385050343c904609003002e0f1042080260000d883c040d49030180004809907100d0020b0510111514450300c3c43c0789005002c0030a4030418905184c00c07507a070744110128440046130301c50070125100c0c820490000c2c0b03203510801c0341048490060b0b000310038400d4000e040038200740d504e80b5080291001a00704580414481208004540e0090310003a000b07844001c0398042d41c40c0a076006019084009081c082d50160000042d80154400107080094414800300340031041c0c02014801c1002010362b612324 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 875838174 1250 875836924 875836933
    0x7090f0b0a1404200a0c11030d1206090911041112010b03100603050c030604200a030213080d020a150209040c050705010f021602060d02280f05090a03140109050d11 72
    0xc0310400c02c0409005521030300c4c0180c0b40350a180400035600319412a0003200c9046002810070169681031018242d0802c03261240025445032240d010200d842540200440d98034040310a004680c2d103a00c0c0310b413181021355002510864414415079580034078125007086038020ba0010401010301409540680b059000300c2c50840d49600040d42525030448485054040900c00034109150030342003450096010051250365000020b01c07891240c0c03140c800a8003103078000420041c03040d01a0800c4000b009244040c2408024400d402522815071035400b402c40295001c03400380010056044800c0c61900030300800c15050150b001800c03d4201c8d400079075040d4070304081c6440550860003103032a00501080284000100345c2d00304040f81e04842d8103601655400d005070403407500850030000104240b00c3c101304081041d820004c00e0380d0803500d514000c0001c00e0111406d21b407a001741050035254402c00c1482020036038041343d401401c0d030601c00740091180c1d0360740c01100758100303102d00fa0803824942170302c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 875839424 1250 875838174 875838191
    0x50606010e0f061305060307090f1a070b071214010509060a0e0112210206060a06170601030509150a02032202031b131b080106080907090f0b0a1404 65
    0x19a2505000d01c00c0070340001c07050400c2d1080d49080700040c090a00c1a100e0541210b440e200460115001104c44e10702207a14800103100b03040440c40701c14002c240c04101080360011000410070b940c004c81400502c100b00c480d020074180fa024005880e008089044100003a0b0743c6800c200681100031300c1200d0103082d160f40450b5031030800074607000954040c10088102c42c0d18143d07a10f6100441d00303005a65241019443d0b4145201c510b80c0310111007c141d008014a0400404000076400650b024000780a0844d00c00d003000555181c5156002009080010345a5540c071805800c2111800c0d180d02e90442c40020824950b0040c1d02560140d0948090700ca1444071040c1c03081c4590455075400303076260788030101b0b80c040103000c03444a009071400584007a6801a201419005451811031040f010396040707005c1a80c000c1e4844040c03401084607103010710303050034003091050311250540a501c06240d2034440d101200c525940104051800140c45424865540c450303a1108104458030144a2410b01d5a80c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 875840674 1250 875839424 875839427
    0x8070618050d2c0a0303080615070c060806010f0e2b0b1602070f0902180a0f050405250f050f04090e0c0307050a0e040f0606030f0309170706050f040503010c0c05060601 74
    0x640f8420440909800c840c541075840642d000c8400406066000c2449846c00700070b215000041c001c49803286903149101400c010000c0d10841005164034104000c40f601980c9481d40040d00c070320f0b0b0000079070f900c0500608962680c50b10f00741c8400742084041b50400c0440c100040c005482e0321409820b4032884c2608103042c4101d07210101c9100c1c140410307180300c8050000d03c106a00401d0b218403032132401d50b252014200400c881600f030b030340100c1000c2d2030910100081e00b881e0054652000c2040941c201c0720015046a003080c8645a01540800c0040760160200901410483c1d400702c3e4016400d0b03449a9480c00540041c1c08500d0301c54000e0302511070200e00c0ea0600286176410b60394000c1a0580250804080a808241c000c0c420740b40d580b42c0019003008241c180c81010b001e10700030450350800126900f030280980c04e0b143d0000004001c01c40100c0c2444202088030402d460080c500940e03160200160b0015030700071a08510384c10351031b0490f01d081c2c10740c1064076009203510480c11ba40007036490303800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 875841924 1250 875840674 875840747
    0x240b0604120618050d122a081302040e0f100c020c0616020a141804022d09130b0702060c070212190b011e0308070618050d 54
    0x401c603001411400a50000d812030b00039541d0607261104000310082d10b80c03999072810b1580032940b004076400180309030346801540241c80f5842d000f000807001c1500f00391400944031422100b80b004000c2e40d031002c100348854407140000400e030010004d00031502e583d10625203800441c00000380358800c440c0074000c035490074020118a180160007600c09441120103000440d84103003000907403040f000c84110b00503a584881ca0010f440500350406600540105000310075405003000c104c0a14500100001a601c200e003240c003950310703108034500e550121640c400b143c5a1780101142d0220080f000c00c44a11010000c00b0784050241e0030100450710f84003010781e140c000035201c01c40c8031001000120058213040e1001101126064100e4501c16a441c600c402140710300310007100c170006a50010070541c00d40581c03822000000d050102c44003450740d911504a4401c06500800e12502e4040e07520048005105419405410074240c9030400c03141d0800a000302d00500c21210805011075001c41140b08071030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 875843174 1250 875841924 875841929
    0x80706021603140708010e06070f0512070e0609040e150c040303090515041502010911270406060515071a04080d09050c0604030302151f120c03240b0604 67
    0x8600c0d040d200e0450f140d04252540300980200c181c41405400641c000e0244202205120a8006070000303040000006010003900724071a01040700c2402190300c99110b0340741c82c0c1d41166007820911068100600440d209001c0c4103800c6510a180540e64071003d00d01141004101c4521903442c0040c0d80c07901c4000c503440c0218000a40050b040c1c49081c4000d003000caa800740d880c00c2c00c1c006a418036982d440006942075114801a005035180c900000030000301c3c1c1c540c0903111400f140c4024070000c1080110000e420000c0840b104203035100085018071030b590348484003030140508103030f0141c1107030340140806034468002120f10465001c407940300e6109042d0060301a5038022040d5103044e0308120140041e112038a01910f03180224107821260743e444c400100025403094003e070203d443c00c002201c808400051010f80100c603082d20000709030188000d0401580d048041001e41c21000e810312052f0081d040c2c2008044028465000c114050001c421501e00d8503807031424004403040c4d00605c0130602552 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 875844424 1250 875843174 875843203
    0x60f080a03030903031b020a030e01030203190203100b2205062b0b100f080901020f0403031107051806030c0307060206190b0901030b0405061609050607030318050708070602 76
    0x100c02200c00203101e07401409039030f8020b140100b058580c0b0b4030715841d043d01707840d641e10141c0d00c21a0307948101a0480040410480c007400d046056180078503010f4035022045182c1c2c882158000000b030303401c80c942900f8030003400710201c2041e10740f8801c2141c425942c15407149a4064200008000f03001c0c5045000c581c21139051180d1811100f424100f01c00041502d252900503064550034043d5041c0c85443c465103400c0c1856031091100005050302520b5800e001d000103a03c0e90041022903079400345513044500312641480c0c6180147e1440c00d500e401d06a45801c4507900c02d00320264500d5880e240034207140a208120140c90780d4174440803c2555400c8a8400c0a001d84c0101c0001040c611400c502d450888081000214032103c802c2c0000d0f4840704240c00440c2c3e40e00810081c0020300030108865a404040d0600042040f423040c1c0c00546000b2040c4203043c455640010301c03504040c425000021495610454029015118a00345486130941c3c000c004c3c49100f8150700288591001590305130506a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 875845674 1250 875844424 875844433
    0xa08010f03050c0108040f020907030f0e0f060c0f13080a02100804030e06031506072d111005120907031101020d2a050d020307030f090b12060f1203040801060f08 71
    0x8043c01501d03003410040c4142d6889100c5035840c00580c403040c4189110b84055540012010b0010b00c5040850346451030f50015a4001520f00e0220b000003e030060304070b00c00b41207194590a19115000541c421130401c000110321408000442034000944401400e00c202ca51100c1c2010204040303446003c1298050000f4100902d60181820718800441d0402000c0801c1c0c681810303250085045540141e10481704000840403e40607840130130002c090070809080340400c814502d489588030740011490703c0d4070424060509292440c019021281c1103d0496007201144ca4100390103034039070800e444281c4100e40d04221550980d88041848055110542c48110310208880d601140520b10322809817085200584420003042040041070419103030f945c02940d40303160328640107045d01014958241031140e0703d841804407903400d00c269810000b00142e07440d0183d44200018a40181140000382c0288011481403400a4040000d000750342c0e030000203100c819550b80d02c541149200c0c0c4500c1e80076420 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 875846924 1250 875845674 875845693
    0xb1b030a090201180b300f07020703140c1f02030406051815130b042402011b031d0d17071413051c12032c030a08010f0305 54
    0x255200c0d2079500d0062406501d45150042d10607035812480d00040c0446501086242500c624411300380861010900c40c400310342400380c107040388150054956030100444000040c10184204a60f40c01181c0008401c0c00d20642403080c40c0d11801c1b2a51042d024840344180e40000220014550300203030b11940c01945041d291500454103134022006824070700b4015400d4144594030f614494040a46110304581d85800405107203510340c41560050100700c03c00d001c200242c0d0b0400081c4020315032808122020444506c80484c01401b01c1c2030b08000402520025050707059055000e80440c40a040c0a607052801162031566105101110000000c820030200440120b12618007a0003070302508248451034a042681890380c2c001e00442c10002407200010041b510b8081017464130003180100c078200c1b202e4144c0f14030006030400f144640501d5140c40364244c030b00801c90120600742005007000f038641d0f440c07070300050b8881c7c1c00300006200251011001007030700c015904101d4212075104005100011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 875848174 1250 875846924 875846941
    0x10e13060b0c06071206081216060501171509030a2607021f0504030905060a02240106030c0212040303080604020c0f010b010f0507020a0b030c0c070f030b1b03 70
    0x190524004005840d50000551184464080c0c540440c000c8040c00b9030b4a00741200034880c001d4084502c0840c1c0c200b12040005034004a600d5100c41c00c072a400c9959000c9500c1a00b0909980d050004c00661600000094001c800c618181000d0f40d00c40644000c5001c0305124068590181c4441c511a0010081d01500d02e01560000b00c2d500403501e419100400401c3d0010840f840495035640076801c650361030b48803c0b4103641c8042c007845501d407040225050680340148010454000e0a008542c0041c07020403e50081000054000c0c0d404004a4000f00000400c400c3d01c10a2041c0300119040000340c054540c00405c0514040c582c03200d0190405243d901c089484400180c030036508186d00300b00301078029009218444c0c600140c900041548000b24000501d050740c0303806114204607080c0502001a40c0d4140ca801c1250070035090507440b9180d40d00e08040900c42c1c805004140d1149400001d14030510440d440c0440340a89810300300c3d540d03100d202c880e11f8901c6000030910301c0401c00020f41a80c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 875849424 1250 875848174 875848189
    0x30c0304060b03150a0c050301080a110f040911040c03051308090109120503130501020c061c02120f010303120c0818120c0309041503111302130605030103030e0d02010e 74
    0xc0d0040201044281e60b5a010034180310750016451143c4000500304001d905480c01002c1c0b50b24103601d00580303950b01d0102c0c080e07105c0c02c2e04100103000d1000124186142d540c0e001c0d010740c1d0144010420000a0a949071000cd43c10080840501942c141288510038502034030a62b840b1342c400212000025026965a0b403269001400b580d050013012503001c00c0f8100d1054415a0407449107000318ac0d48c0c00c0140c50034031711703000d02e90250b81158021404010b00d9140d40d8140c0e481c0d19429422110300103500769810019014040d140342c01f1400312030400403d192070824aa048038005d4075205040c0e1442c0c0480b03c1070b03480142141010520040110716000024811155104111001d82d000c01d800d00404038101c2d4003d0604400e00ea00c0820044000d1410b031048010008602c003220101030f10315a11504941820002d184c403907031010540d51b14002c40d58040b16488407000f10762036096500d03460040c00f650020f000c250b0003d14050100d80c1c0c98101000c50040c02c5405850300004220300c2c40420001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 875850674 1250 875849424 875849431
    0xf0d0c0206160803040b06030c03010c050a0c050106080a03020705120111031329070f231608040e0a0507050c0c100507082125050f040b070308100b040803030c03 71
    0x100074030042d200105500402070341c021403183c1c81341074481c2414010540307030004000c0210b210f64035051611083c141c010046070748030700381410b0420008509003402401005c003035000701c030f003401003070740d01d200f0590301092602c1507c1044406050306030401c0c181a0881d48030410486000c00c04102190300c03442510044001c2c0c0e44a1402c1d10b07550a0080310b502548004040c0c40305d503500c01ea80c1803000841d0030461703051b9400018941054840ca03110550140803c0500c0c803241064030000d4480c072540d0312203400b1428140c000c0d04150740c8035520103240040210484186100030326200129010b076108801b1900380d158010010b1414118010030058511013020b040340911804121303990020f580da1024104003049003502c1826203040c104940d000b03c0c0002c012034501d402da03405900290035421101c82e0740e0501e514010351214442c20101c0301d2031045402001d88250301003084010964001039081c810b0b220040003800c83e9983d100045c8aa0045000305a5682c201b0710004240742c0390039019550 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 875851924 1250 875850674 875850697
    0x901030e0727091b090b061c050601090806041412070819031508010e010b03060601020a0605100b07060e10360803010b19020d14071b060e01020f0d0c0206 68
    0x100f0300c0d043e985011101c000200c032840704911010082107208101d10440e5014541a03d00d2403806035100030044480d1081c40c1010400e80d40e80c8049000c59204028000203081080d00b2201c0c24101802c1c8600282e0362007642c20304d14840e07800341041d036411f070300c0944003116440001c880c00d1818400203115004031950f224020582d941c2c800d8a06a00e1a0041c08001c0c40108000118004016845820345025102260082c0d00503030610400b030740c0c00540d001084c2c0e006070001a054482e4694604800d12561200c0407450000c208002071201c1903203d4089003125100710303500c00d0854a124400e03105015a4810390803150382c05601c804040244c5640e00302c12400010102014640c0c400741160000e07084990841c00200701c1518181064803208504085400281040c030315a000041c074020785488401089500032810303108000e0b4074990a02c0d6070310f021103030307140702d50300c8100013080e64202002c80c40c0103105258994000d6140422105203405440d900c85800f508140c0074032000385c3c003446001c403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 875853174 1250 875851924 875851931
    0x50d020d0e0105010f1e050f0607030509100306060201051f14010e0a1707090608030306061614010c0e01030e070b0c07080715030b09090c09070201020d0603080901030e0727 76
    0x110800000c1c8500390207050100c5c2101c0819080c40031192814200b1510040000c2c04624180859558801888241d820807228903980d0011071508941e04c1c007400e00d407950480081441d851096806802c880203983c5550300070070030f40d5030b0000382100340041454441c0041d09407250a0007009183d1070300407800740041c1030900c1048080b5006c11103c0d01e50398030209118a1006a5554405041c49000024070131002c06108203410301242503120710014001510800002841054007505020484041c3e42c000c0101040320900d108124003820b042d0004030000380790642c2514540d03000344540e0001c0d070341d80d2001702042420203015441c180d000c4900d83c0d005100d903800c002a088400c014190183c2056504204510914600a0306032280b240358207100788100f500304032403400f0002c0c4032501d61804030344140c1c0b65110404180c0c024801e802c20408028202140032051050b1403008094426003039804201c180101c0103603607159040c5010300400c00d410980307405080c180503000d120384010b0048000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 875854424 1250 875853174 875853191
    0xc070201200114091c0906120f110c010603020123031f1a04060e0114070b060a08011a03060a05010e0f0912040602010e0d0306080a0305030901110a180603060303050d020d 75
    0x1e803c885030407645044160b10491083d6060680b00c440721959030883d0a001c1d800a04190004c0c15440c41040481885641ca0a40010075220341d0000545240110710755651a03c41e0744c1c2c840d01800c0f00b40030603408500c2150141c298943d481c0403072400c1480f080546410364440680007400d03c002c2c90940000b40f40c81d044007140e881800802c42e02440361800480da0307918a00080604050368145c0c1e642e060040c07440d00312043c41085011159529807104210940780d40304c000140e40c010030360304910036642c40d0043d00c03441880b030003108200003d8110100c8000381e49680c950001c2d6442409604600d141100c040340d01c21540c8030105d80c0000481d4140c4450380c003000448030403608a540b00c1c2005079103824000428a42c20310408038901e40d145010320005050000d103076903903800e40710300808200000000030b40840080d403080f10003d0807903e1060b40c07a600b00c007004116175030f00e11443c0c851420300c5400050480c064441c1c403003142d85c1138440d01e0603d001c0d41d00700c000940007401c1d0305d0500c0b901c81410303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 875855674 1250 875854424 875854451
    0x50c0402030f010e010f030b010311040e0f030d05010e060a030209070c120e090a11030c1605070b12010b09090a0506010e0a06180b13030219030b0c0306090c0702012001 74
    0x1d14403a8200c1401c0c52415890401e451200c3e400c1079212191164044505001190f80409210305603500698064881020715001c200180308070102074800307004100100009802c040300807d0100c4180300140b1160340c0303401090780c802c48145c071078541c0300c55205c0042005040103100c450340002c460901450481841e220020050340383c1000e800002c031031038044038203858403d40b2103403c000710b110200a100d000d01c1d034041c070901c8060007102c180c64021403c0c5459600101c1c914842d41d1307218040d078690030794445500405401c40381400281d89640300c0003003035030910301d01030325496140104210b80c00e44818207c603005140c0038003010304104000314000c1e010745460480308001c24082c0e8078000c820b449080c01c516104940d400c505000441003012000761001c0c0660b500c00e89070111003a00840300c2c2102c4d40c0d6101445640001c092030342082c20480d00b4003801014510501054825000941c3d62003403e21175403040d020000d021524604042c2410031078001602850702c000c3c030001492101112a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 875856924 1250 875855674 875855677
    0x1806200408151303023f13150503161103130504110703140c0f0f060603010b0409150f02091206090d080405070b0d151d0c04120f050c0402 61
    0x1d4071903005100003114288410103040d8820301201d6101001600b80e50020f4440c100c140c210b2209124051901c0a8100d15413225541400200744800c07610203113005090382a0440c1e40784080e5640755000006040328010a8980702d0704c941d036106444c507a540020141c1800400380144100440d0f100700b1010602d0400003081700050500404034014603100801c0180c0c0c08003126441c41c10703414001400040d070042a0b00340418420001c80382c8940b44031218a20f003910310850402a4480c49181d5440c80c200840c00700d010300010750092016001900520040e01c5100400030014401000e00c1c94a1440307981c0a09981c25212801501d4859540000743c030241d42100007500603044981402140031007040000010820350420040c01e02d0251107191312161f4900c94061100800100806071a10365406031203a000400340c0a4407054031084030240c8110030f10300d280880707a200c002007220110341c0c206860888d4601080c2c03040c203064658583c1c908000602d401c682a00c04c46103a03008950f034030b00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 875858174 1250 875856924 875856929
    0x30a08090c132913021e0301062307120c03110102030109140108010c0e0d030504050a03030905040e0f03030105010e0a0e0f061806010e0f18090706030e0118062004 72
    0x510104940030210844190b40116452503580620310b102e10f054079846500e681195000700e0300c0e0043c3c0350480c241c41c5000110000700840c03041c0c0000000856560382041480064000031500b0020680401040b0721440c07140803009400e40541102102d2a03a10501c41c141a640c481c0c505071040da2880c1e2100c5007139800030781040741e4031515000d404814111740070b00c071801058850000d010810300400060f101e80325081c4894084c10315011000e040c14003940031a80145000b928030420140d5074140240808103501840d4896401d201551410620020319106804506006180745929060041d12030003044000b0f16080ba0245400052030346400c80110300c180001c41080e000c0345441010000e461059a22080c0340c2d0180005002b826680140d58048101c0143c0d030248034200d0f2440040e91035100041101e20701203105040100340f04011622800b00c0341c158a0a110400100520600740d0f180d1003613050900070461144030100d00301d070300281e0303400700c410241401d009032051301401c865100b40c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 875859424 1250 875858174 875858209
    0x1b090910150201090b040320070e0402040e0307030905190806010e1f2d05030a030f1206030f0b07050903030307050c1506131518061508040302030a08090c 68
    0x1940200098025a507030424100258402005a141c2c195100c5807410070191000e8200403800b96800d06185061150f40b40031071000b0112000c10f40e8484044e0312044080310100c2c000ea0a04200901c1d45400106641d802641916008200ca003440144840001c0e0200c1c07645440018a1000400110501c00303540030b0401320b8045181403070020076030489071504142202081791300000401410502c0c11050300c8191140c400801403107104081071b040c201c00e035000258140501c90080d0105600091040300810854541140403845400e0f44000c40d09584000340c00807998080000018100880c110f80c80216070511500f8883c0d00f03804a40365410032985440841c400041c030184040040081080100d51120940094034214002c5034050700d807106643c00c12030b10380d0f00c1d000c4000491490000030f050340180a19000b2060725000016000c503200e10300b4412654280d2040c024402c3e4020381c8500d8040e0015803810480c0c41f0111444800141309016034003402c41200d10076070307540080c0090600d01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 875860674 1250 875859424 875859451
    0x4020c0a051c090b030603010f0e06150f030a06020702190e04060f0c0e060901030b040f06240206042603012403150b0a0c1b030c14091b0909 62
    0x610345203141c0420803515080b02401c00100184082c0d018683ca4241d4200040050300d03074450801107400b5114a0145a21007424086120b011580000e40d481c81418410724a0b900d0040030b00500010300080c640103500750300309178440e20108100d50001c103c99880030741020781d41c045107400e5003d01149034118080d80c00b580800c0c0010b00c0b1240c09001c109446040c001c0003e440700c0d58000d0050f400d8110909e0080c031000c100030a041e8040c4e03003c00f80b455000b40003401401c2100c3c1c0c01000600b0b1a0099141d0310206c1c4100a03181c01003241108090308083d002440c035500e0b0380c0c4900400301840c0c0d070100000002d004414054000c420080c1d0b00a108a29030320012003582c420600b104001d103c007100070145806c0d01400c4200e80f50140740201c80300320080f42d944030942c18084500280398000503118072101c08281d0110490800804110b074002d87c1c3c0e52404a0319854801c0c0b040100000081e404440100802c0144c600c940508a440c01d0308016580f900880d5401304405080481d0700402c000f22 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 875861924 1250 875860674 875860693
    0x1406190b0f040e0a09170c0a03081801140613050903090603250203120105031b13020d2405031f0c05041806051504032019150e15030403080a0b04020c 66
    0xb8405c010711940040c000d009041041c80303901203075103042d0230401900708082c0d01e020a01c026034451444d1282803009000b8419696019044d06c00c0640c151601400344201580080c0791036190f10619000b100c900020f0b40c0342c4200c040c01c001a91300050a00c100d032020303600040300240d904c0c24000c3c480300c0c4150059912014600c250704581641640708031300982048070100000c842c0070b0100c6079002c3e02100c4400381d401d00c000140d0300030b02a101c3d000c0c1c0920300d400d00182c80100b80c0301e00402e80c07415811030611a682c030b600502d505c40c0c04091450360f80142400380c103da1003250b60840039014034103181c00f80c1050b035920056800011401e10b0300304296950310050207a81442e0351145e520449418039545414a503981c0c0031b944000720050390200c081490290300313941d550003c1c50000320b035148040c5400a034a8800201c805414500c4880104250704942615030604482d100607200103030302002d00b10380c0d83ea2425101000018441d81304181c1c0c030f0403c40303080c1d621840a03200111000008025468 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 875863174 1250 875861924 875861933
    0xc0f0a090614030c030703090309120b010905090c010210020715050a0516140904090c05090709140103050c04030209042a0f170303180c090a1406190b0f040e0a09 71
    0x1000740040c260740b40000c00030003050400d40000c0300d0b0401521300e000562951582002c4440d101d098201001c0400040882d40c20f00c80b110841c1d9060300e0b215003041103152a9448042d6903001d030394013001d0258001c1c18601c0303100e6413594003905003039005980041044041c00203c80442d070040342c0e02645c41d07980d101844510941c0d00e002d044c2408003400c2611030100082c91542550051071507461185440d400c1c06400c020003003200704000c01c006003d0005038100004080e0071001e280c040e881021200c0652940c5541c480d000e114080c40969a100d45040c0c115002e004254034003c01c10707a2140c0c5d0390402d0041070510514212a102c4a45031002c013524140303000070000142c21f07071001c400c41d64500955114001c0c04400c070390304110004011030703039a01034480140c14102c100c5850341d40020114100311030750811390040c82c1c2c2144070320b500c4021566541c0410030041ca0034030046210b440380080500c480c46459005000140c0704060306402d081e50b58032070014103030044400e6a034040c0c503402035500b01b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 875864424 1250 875863174 875863187
    0xe10031101111f060b030f0601180e06060a021603060605130b0a090915021c0b0105070f03030b0609030307050102040905010b2713022106061804050c0f0a0906 70
    0x2801d1804101c0b200000c01859500c802c6904040b03451580d481040d41c101c201c9510010080448494140d100d240400158402000032190a070100b044c41e5184100b500d640301160003580c02551170204551540402d00545030400e1007404158031801b044420000e2103904418015441001c01013403072814101445140e02c06040c103421200d04010521980c1e41d104441c8400b0344600c00c400080c86c0541d420714400700000490b603089610710009002c01003180c0c06481954000c070b07911080c0100130400004442c1440b0b5000d000c1d042d060383c80c4801c0c0c0020f111b904401040703800140290700b090303112000241140e108443c2102c01307a5002504000f050000e006c1c01d070042c00c2070403049050403401c0b0388080c5500f102c400e4001101d0200c2d1128002a680c80b9018001d81c07000b074100319110304a54107290391442040c3c000992101c1310700001000d0780f5040c403c031041070070607000c441c2d400750b49001171002400303000c0c150b035440e460140250059200908050304240c0c50035694409490300d84403024250f07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 875865674 1250 875864424 875864453
    0x9071502070509130f120e0f060c031801110d03150e0112060f060f030605180309030d030b030a051606030e030f03040803100503030f07050f01060608060105030405070e1003 76
    0x35500070a204100369680c000c0710691140a01540e40c1020310300f880d2414480c400030341d00400c150103442402580d541d12007181c1e000458141ea0003e15201c600003003051a01034002001c0b044d600070060051400b500c2400d200000e001810404c05181a001e2802c0c10280c840780550006640c41d44d61700d40501080340120002d1071400100c00f0039504040c0900400c802210024024070f889000450350013900b90300500092502110303c0b42c1c03054a904d840f00240005640560305480e110b00041034035140402181c0e4400401002013604408244e002d802a040014000c0e60500810b0b50490101e00180400d400b241e0202001c0a01c2d2030a00102600301d601c0707a0b207986421361041c05030003a07040400c41126001034002c118540c40f0350341d6001c1d2022402c89908481e8050101050007943e6000f000050400240714100f680c0000944c07903a150b08940407481741c8000102408080303503055009100554009004205580d40e0580f261103050800ca001e8034000f1b40400d44400c00c04c14403801d0040e5800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 875866924 1250 875865674 875865677
    0x240f02072001140a05090a1205010c090b03160201110f0c0f0307020d03030b030309040603052d0303060103180b27030316031802030f0307060b1c0807021305090715 72
    0x103144841c140024490780c00c4402d4040c00500010fa540110340c024029120050303001015030066544a410030b0044184640080720203600b005180400e0034024000b800680340000d4000b420341d07950001c03800a00100e08210b0055540c1c800b074030007030410444000c010014000d604150380e01c0d00d81105500d820141843d04143d40c00a10a000041e5120f001c030300f8180d83c040c5004290503800340006400c2d841006416a8080d1400d4000410803001051484145480d81e80700000b031007417030301d405401d0603422204c1d514640040000980540c000d502c40c800120305401c21010801c59991000c00000702941c26410340c44140c603000d40798000703080d00c9560883d543d002035401c6080c10010041e003400402d00c4501459220040207a02010b00781084410a40003001c40710044c1d554040c0b151207912400054843d00e080101440b1b0070704203444200c04059800560034914411510341800f203401101040783e1281c40c4941d4a00ca94074580905401220030b04050102503140c40240d503519003031450082d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 875868174 1250 875866924 875866973
    0x10e070c03020604022e020f060a02040f0506030a06030b010b030a110a120e031c0e0606030c1f03110c0f060a0b0d020613030b0705030108070801050c0403240f0207 72
    0x300081d80031800540050703059460b201c2842044500085a0080c042c86112888110190603415a40000e18095000c1d4801c00d42c1e240da00c696820005a02c600c0c0550703000e00300032141c03c11060030304900956200540f01800513540f91203541f500f030405801c1c0d10200c0903401c04410300204014030f1080070382c04000d40101d80d1410004050242042108284003141d095480c2200740c0500b4061045520946070006440398505100744440c00034840040c0002d00b6115604c0000e4144c2000a429500c01c00000c03d011084044190301034208078403110f10200700354940f101c4ca8851032102d4060541200d0a05c050b000c0c00800152981c0303840f8005091800c0c66040900161a540b1044c84200c44141c0680e00c2c00d55a9500c1c1008843c9081594001840d10880f04200035038a0390200203113048e0b4a07654203070307504190396603840b0b0b00380d40d000e444160480504100c01c10028200d140001c10343c1450700c81082084000c0d12000c0c0450b8044d56640c004540c00140290402525010f1001c102c3d0b422004036 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 875869424 1250 875868174 875868197
    0xc05040905010803121807090e03070606050306090322120b042609061809040303090302061807050607052b110f0c0108041a070504031502030f06010513030812010e07 73
    0xd0180c40b0040c2030b118401507841b407400c185040078032540e000b80941040a1080321541c1c21815a40c1c0d00c6041c040e90b002e442c01c0d40200e101d140104070f07180601c4402005504100c040c0044103425500302c8a4a00070200702c010028110313541200501c1c1d41d03401104000c0c0549010308018401c5030324039180340c1d0190781d440030001c10540450203403120f104e429260709845090300702e52460392070091103420740d000d44030900300030401d40c1c03540100703a50a1083c2e0070348860b91286407010b5a422004014640a0b800110051000c3d080c05409880c0301d600038802c40700c8148082c0600c0d00e182e0010344e0003016900d2a01102c03070f80d0300d401c50f490101400400005003a2803a141b4415610340040d0102203040003020000302b024001002d101d0348100000c220340c3c80d4142040071016180c0d61003448200e400d10102030320b40020203e24401d41c0d1080300b030121085002d9459100450b010303800100a4000741038441000b00c003081609010301002204141084015410701104404101c00240060100418407986 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 875870674 1250 875869424 875869447
    0x20d1d0a030308060f04050103060b0a05011107030f08090402070302010b0a05060f160f050f0604030f0915121e29030a0305090609060c0312160c0308190c05040905010803 75
    0xa480880b905460070702401c0c3c480000040342410150801c0341d0080c00c2000100c1803107290f6001505c18001240c41c0c10750301340d07510015644520000d8124100350080f8600301301144c0c070101c64008a91203003020600e01041c2e1000202241c206a4082d00140e41d0343c4501d07455410084240710181004450f19403c3c10703560a81307c61a440b407043e01d840303003d20b488039680401c10081e5039080010b9000d01900c04482400105507034070300088130103030001116407e00707030b29840c003502d000d4081d940b40c0103000d88414030101c03059952048a0020704074039039440790040103405114082e80d007a04000400821140491841c5550600103038800950b070304820074030400307155400600c290a03554541000390f00c40b0000000a403c44c000d02c0c2c0c003150000380000c0e92603080c0202000030442d10107410188016030300d900e40c100081d03480e9102e00c000800c05c0e1200c0d030404203005996080c0e1203404083c140c58003039010000103094900c5500348601240000c50140002041c60090030b0141c03000b40000c0d4104035542c0c40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 875871924 1250 875870674 875870689
    0xa1d091009021e0a0507060c09121128080c03031312050705041401051c0c0603151502060403091a07060b010201020d110306130b03062d07020d1d 64
    0x9062550b54001450104400c00d04001aa00003040ca60642c5542e490031018050340d01111048445a00d400da400c0c044500a07401d0b01c094583d2130700340002031007240e40c892280c0e84840d0b2016034051014116040800d0780d52110329040c64600d50700200c11454029064030b400c0340050b449220340c20a0094144015050604008458001d00800c0d1900710509015013004000c1d00700c10f421a0a0615000e075103490124001c0c100c91068034040103003110342e0450003814040c2c240c002c5c03c0b0f120302c203020420282702e40c1088030f4082d245000d1944140d651240c620320001c500c81d0400151b0492401c100505070011050002880003841021903165041002e8400e44644680140111ba450b00701e003c95900c00d5054600e034800100d02004040314580b82c5c45855007044a10a116807075000403252514890b004482c940040640100005c0e00e92500c15006948200501c06110b049451001411403101c50306500031402900501607071908090010080700c81c00449103402c400d0250111415110041c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 875873174 1250 875871924 875871929
    0x70807081906110712090e06030c0a14060d0204032a061718031204020a0501030b090606090d05030a0c0302010614030d030906200d061d04170f0a1d0910 67
    0xb8009034000300180c0840503401609409001420743c0d25907402c1c2590054981c00554484215403c01e81d0390300401c05980b2210b0604039030704260314003070070007150315504180000c0100080405041124180c15001240c0050b44265032030b501c0511240250048460b0301c00ca00c1c90400000c00d40301d4180310000e400202005201002480500e0004030507110420390701e009a0b81d5903050b250354441da42c6012143c060280c0b0168811034030380e85e0000b0150301078400c0d840404030107403869200365925003c0120701d410141400c0e82109a040002d000110140010800451a07483d0810540321030b04000382100c81039040459200b00c01491004665000604500000c6030303407501003058102c03885c00001900700c0301c0703100222040f00c1d00b00307220711003c1d80c024240d00401c002d0708001c607560310401c0e80400c00100f0411280074210b0f42c0480c02180d403138500300040804a10005140024455241c2c1d0f80340c2c024107040c80003c00801003102c2c4030326002c00103030340d440c1c0456820140c0d092604541f84100320030b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 875874424 1250 875873174 875873183
    0xf01050a151d091815070e0d05010e030406020a0b06040603030e04020a0e1e190b1902122b090201050904021602090a09170c0d05070218090708070819 66
    0x200803040701c410b204641c0391100901070490403990601d5414400203601d0291010b03e540540c4d03040107210b8000013011885038180b40e03640d4116156880a10280d5011135505403629500c2d203001e10443d5004100401c000c01d00c9900a004500b1319060240c2c1102000e043d040c42f450038800700b000880c6d40001c4080000108a400582c0c41d88442001c0c0c42c030034100200150040a01100c1c0c0c1750030148100e800781c14034800e0761000007016849050310000041801020780307140c01031240340180c4900c11080112070780203004403440e800050052000300c1c1c0080000d030b04c16041220300300041c0245041448520350500a0500080c11182c3c00030348580284800c441c0034076408941200f20001c00601c1462107038001d00400030508008034840b000c0e040110044c0d5140d03040582d100d640f01a944100c1c2e500204500c041c1820446021040350140e1000b841070345c0c01400307400c0c51840500203983c00c42c01407031800700411440b440c1c0000d4038180303605540b1411058005050322a0820452080510b000781e10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 875875674 1250 875874424 875874437
    0x30403030804080918010f060215100b0903120d0b0f0103020310033e04141b13052d0301090308150103090f0503070201180302130e1c05030f01050a15 66
    0x480c804101044c1c5242405c003c00602c0c8000002d1224100410b5010f4540590a0b00e203c215007d10002c1c03050780c1a0b072200c4000c00240e404000203204107000d45141e100c0201030741c0071040ca10108014942000d80c1c01485d060365400510480c0c40e0050b90b0340c000700c8003800e0540c2907181420295180414511010704010001030914241d0b014090f21850740314a402c40c004126685407216004a00c0f000343d5017030046241c12801c45103d54241c420502c1440c0e03810192441d240384400203010390300690b62654112809450105007640c403406004540020314052441585107078000316002060000054041c3e454204100c0201e030b03000c10002e511139100c840c41900c41c0d0004004900038000c408010744502107100851042083c0400204141f40c000d9880d83d0051000ea0103400c42e0076003610000b5440107030300410f43e185642c071343c010320b9244a03001c013600d143e500041e07100d07020310260f10358500000b10700004100805007080c00325400740000b41c0344125100e0421900d075050300d0308114548284141b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 875876924 1250 875875674 875875687
    0x521060a0b060418050a110304021c030507120c032c0f240c060f0c070b090a350f040308031909060507020f0a0c050d050705040c081803040303080408 66
    0x407410100c400420003040e0403601c11050ba04c012008010903640d071040c0d241010b011071441c05048050b079000359001082141000200441505403061450f01142445020300008010549d00103610001d8091a240c1d01d0f50f00983d403030000d191180c60703003524001034081815800c01100e50b002d03d1101813425034501001504c90400a20103c051800e1603501040842c0c600c600d0403c503c02500c00310243e1012a241600c40701c10703254410208492501501c1e400b4408440860910b4058070780103041d5405551200710305881d001c910b603035280301c020342e00740340c030079060400c901c4a9181d100400b48800c1c00d1414a40c54180400700e40c4100c1c40098004e4901101159001c3e10700c0189a04441142104002401851078808050142120031031302500841007150b20ac0480400c0c0000d40c01d9101108000840c20041003084800540c1c40590313071480780060100742d41d00c880c07146110003803040d1140407861820101d008441403003000e98107101d0300b0912007000042e400982c61900076a0104101e92900c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 875878174 1250 875876924 875876929
    0x108061302060d1a19031205070f0c080d020d0908030405060703120e100f0504030c12120515190321030b0303120108190f17070203030408070521060a0b 67
    0x30300f0500d01d62541c80c200c4441c0280d0303010b80610540d581d041e02d6819402e020350140d2031001050b0320001e002110400310300302020780b298005002c114414000a100340c0e1040d11001035007035070b070f030000301403544003a0707002c114079404000050910f51107240020706603080c096010303241d0146100d03090082c900804c01c00d0800d402124000e241d1112441c08104080e141c0c0440340e039440000a45603503aa1400c07900c90700e0100e4600555102d10b03056154191510280d95510f404004400300040420128070b00040c841034035401414000d10100052101a4001108015241074516010011101c01400402c0020344203055030440024184003c00da20300f42103408d0303000d07000101040790f06020003e01405001c0c0c40800340d0341070318040b00480302180c113040b010426929a01340094a4501d584800000007039500c41000d01c50b4100050040c10034905a002c01e1654116400644464020302024031040c10711100c0514004140b0401d500c40400301c420250711044042c011050f8a51141a5400c00741c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 875879424 1250 875878174 875878177
    0x50a0605010c080f0c1203011508160c14120304021806090a0b040902060d1506020714040e0c1c050f01090305090909070515090906030d02030405090a06090603061a0306010806130206 80
    0x124030000b5181003002040c5a06c0c481d03402405007100c102401d0580c4000c01d0f07c101d0310325102d071490003412450108480d409490b42c52a8810450b1a5a050740700e2024411701070080948801203010815201d0400d407040110440f01c003c0e25a078100703042000c02c0045d0761101d00d0590040020704000034445440800704000e80248400039400020010342c884068175140c0c031003a45c099129048014107900c424003240ca80603603102d0080ca000c6001c1d00044103242947c0a8040c4c1d40400c400c481503003415201003003900d07030010056001205e1410090007031041c00c1c450a02802030f000b0080243e03640076500500a800b4051100e4001e01140000500340c0404000800107004018201c02001414000b1041d0345d500140600c4d0203101c18078049582e500700042c181408031266009141054100810b010003901c004050603602078807404002070100c1d06100f008003443c0982c401141c094420b54444088451459150340030391b000000400c10a14013083c0241c200b44910750305101007600303000141e0107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 875880674 1250 875879424 875879437
    0x90c0403020406180b010e030c01030c1205090703030906080f0103150f110901090816210629090613050a1e0905070602030307020601060f050706021204020103050a0605010c080f 78
    0x103150420118202c01c0c5102c814004102003201407100210302001114260011f41981e5090ba2010700700350303aa903000350030038150040640350020176401c1103a055001c1d07076030548199165800c1020184185540068000090695070500e24040d040880b60034010039014440078003019118241c807441496590043c22500b903003494103022803500c03c1041c142960000c00355a01003500504005520480401c0408201101e1080290311034589034803910203030000400350041c100410581d800040a500c24201403243d40710700c888100c26094509030065001001c020300c140700c12410040f44d42d0341d00b0701091a4488181020406484a46801c0090400701781940031412a00364803402c4102203502c8866000d0103041121801641d5520680e12484143e43c0b03640103030042401070098500032014505a140f40345841c40c50961940c41d6101240c0140d50200078a03160201448155a0306000e83d64024121440401c02e503454240007801d905000d880040409002040300d49840c090941515030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 875881924 1250 875880674 875880679
    0x712230a0b150a0308071103070e0106080a0c09180f060f1d0a0c0f0813020904050f0606060c0c130e060f0405011b1b06150b0711030c0906090c040302 66
    0x29640c91070031200d241c40440300026032101050740ca1080d0b19102c0741c0e20080f40e80088111b442e041c055240e5101c00c102c085c0809805200c0c03084001200c61011030221700030001941c07907982074140611304409540d00c0680c2c2208011000030240700301000000d141c446c44540da040094041a000d0303ca2014001c0359010100165400b01c0c00107001e141c0310401b00d1100c6c0c0855a83c41983d4400c40800e0407262404c0303000000556002c131103401d03280510746181d08611001c540c0c40098016600054008100316411151174020700024884010f04018413600550100c88803804c01040408030765540740c03030104052044017102032000c0394100c01d5114149140c3d11000781c81c0e162401e000d800d801d0381410f5408807540d40c0b0f48251760b1145a046800314040b4041691141040366662003180740c508030504080d600c00340e4510750b120829800445c040001c0140f0500662a12540c1c241486040070034021503000390044600c10b0800e42da600f0f601c03540b01104a44860317a54a030b01142c06294099030300000d4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 875883174 1250 875881924 875881933
    0x409021c11060a051c020a050f0a03020405030303040609030201151505340b0109060e01050d051e0105010503070602060f01060c0807121d06091819111b071223 70
    0x80a942c45030043c608503440c1c80180300205845517001080303120740c0a07041c002401c1809000d00f442e085000400340480300345005410319445074000381c02e6920581d000c60305560b031129080704054080c0110400c1c20301450309044001e240c1400d16810038011501c48041000000c0c050740381c138402d14040c0ac2c01c0703002c0c8400000c401c40c08009011600c030486000781d800001010001584086900801c4299000100761000713a034600380600070212494401200e5074040d40c02d8010ba07444101c041002d0701c06130000082401e5140c0070606007410175903005001103403c00c408200d40c41486403a01c0b4116001454002150080e50a000300940030b4020010010b2404282116819034400d0019241520844142050590031005c1203007920407800c4032600b102070700040654030ba00003020715501c2400324050000c00c0202e25082801c4a600040600c1011000b05100580e040140d0500c0c020b80c0300f484c0205070041c148a904446407604580c010b0a0b803132000400a0143c4001c46082c030038200207021207 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 875884424 1250 875883174 875883187
    0xc020c0120012a020106050901061b0201090902070516080f030301030f0201140d050f0a020408061b1c02070b151509130e1b0301110d0b060c06010e10050409021c1106 73
    0x80c0103c1d180140b49500540c00c1400200d800e290039400d00b07048581a442c2c030850362100c2c585c1c900b40b04105103000da0602003100000a2041c4260000340341240c8a01c0242c12514091b64001e100e9064581000c50079500c00699050000400800c0f41c0c1526000382e1401940205e030b10048480b4a03d401840d1030b180004918819001102c0d00094000c1208124050301580c40700c080104a00030791044104590044001c1440401d0294049450b001c1c2c14401e10700d0079103044030109000100f5820b0600041c1d00103081024001114403058010381319985080c0f0010071100001e8802001c220441c0d4001800505108240da4414500044c10500c1800344400c5d02c00c1c01c0c01e2a2154042d41c00030203000107680381e00d6580c1c60f061080006805000c400c40d420400c00c030558000409501e205a9008001000122444101001850300901252190750b00e1868440007030041d541940d80b104c2d01031030900415000694940310907410f003800403005031740c40320107900f00414070f4160242d0ba48d4200d0780004d0744 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 875885674 1250 875884424 875884481
    0x513020f04170610061412070c0c060e13060e010e130203011811011806030e070302030703061d010c020c2701031506080312011406040807060504090c020c012001 71
    0x50384c0c0308503000380019042a648142c25a031030b22810412201c01c480c02c200307040c404002e240c03c00e908842c0c40e1904c040012402e0703444442840340c580040021842454041645180807030703c56a00601848043c84000c0ca4503500384c0c0400018040c400c0c0c0a142d440024900e84002c2d5043d914164000b402802400080c03c040040c0c1d016608007a5030014042101010550280d0000007112600c9449070010034a00b10044009120a40054401c0d006034100000540d6041040305c0c0034500480d0005034031031116032040d116190f0724110b00301e00e90515403200f54854010501004804042e21000b100d07201854045e44854900011403101405000c008400c0c001c0c0c00c4200030382c44969440c100310b0f075034440003007558038029031900c5141d03d07034a140103010280c004800200c2c0c000707016100c1414030381c0312410b031810020705800200000e000070070200000380690061008000013800a042c41007202c0307000034072181001c9040c91451103240081b120749903003507000c110030440446044c41c1040c00382c0d01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 875886924 1250 875885674 875885683
    0x5061504090f05070201090203150c070501060b0307020f07031509020406091b080c27121f0b0d02010e0d110402040b0306041506020d080c13080f0f03040513020f0417 73
    0x151140c1842c043c0041c104a00500c40c94020680081c000c1500018040a840e1038110003801003802d01c40900100300080d0003400b404002d08114107405407603242502009280030403010740d0601c50342c840c140c2000882d20061224660500e00c200220340c0030103d00218002d0700480e4416648185002100c800300310720202c0c00f1000c0540da94444215860b8101c0e890034070302541065807100b5448a00d46001c1001540800f00c400e4005443d401d4002c0100b241e072818103281000c01c1c594241a07500ba251158690300c84c220302071008940e0681650320a40009003410700c0c040b034050288042800c1da1050112031107220042c080f000b0415540c49803988500700c060741080c0c0d000c3e030003103040c040c0300401c0911049403581900e681c3e5006000c01c100b01441191458405801500c0900f0208200c07181200d01e4503514024181c01001081c18201c5164140c1c03034442e81440540301e40d0401d22044c422a40e400445900d1901c4660003da26000208030000c0a4890b50344040150b251403100c05440400108 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 875888174 1250 875886924 875886941
    0x5090f06030c12130812070311041a0c010b03072402030703080c0304020a05040f0902010305010e0702030f160b1816050f0d03110d08040b0901090222141915180506150409 75
    0x981c10b000f240861010b00c04580110f0044034a40e401c1e40b00c18bc001c08402e40c0142002804040011030301c450418080780c00c2080d55040311032111a952401000b228040c481030352105402d100035441c002c11520010140c0d14050142e00070824000081803e40d610034410b40003410000b0001c0121000082000b8001e0a43c15406c0380440c1c10b00b00001100780203150400c0c0704140d07a801461400301c04140689840d403010028100c01c82d6030b0034990020445202140388500b1190028440240960510a150035140245507200b4001c003071060006840b564408071300540d00f56a0b40b03c0354011403400390f402d41c903149041d480f544201c400c01d41e03a43c1d0f40081c09a009a014100c410320f10340382c503805542aa1141e0401a4100c01340010400321000103100c0f00480025402d0006404071200e40c1d403642224003a181e903015803041d45038403105101203104900e8444a400b011980c40d82c07420051a104182907407000910319910000242242c5800b9250303107c2020a40807256a25103030350f0128018007440c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 875889424 1250 875888174 875888177
    0x10c0606090e160b04060c150905010204170c01021f0f020310051207030f080706180302011a190509070e21010f020f16170a05090f06030c1213081207 66
    0x80c0c640d055061052181a0203071136000a0740c40c5000d084c5401610940d03c1d600c0102c41803010707015010380584d01da11424400a1103000050b940b1440d00400d80c900c1c03d00b282c1074812940012403c40d10a80e0001000241c2c0011055458100c04c01d040c1c2850082a00e5051100514000410000000e42307298a02c6c0a803001115000c0120540000c0f02c4d40d00c5803036010040052100c100200e002c281c1c54005089c50a100e01c00128101c0c0c07001800004111400b41d003180581e446456030450310b014204407001c10317001510603030704500740409801d02a140718400c1c94040c03810030011940191050f4415100100b005c0c29404039482065900040d00c16090b80e040c450b94a080040c00520803075000304c51131840e100310300904005940c0030380c20845840040842d015140d150304d102f84034201901401c110100b9456064965602c0000d2244080c00184e0041c441d807010810030645000c0c42051701e01c4211404d00700d04841e80e803104c2c130f00742204070314101800c034040210302c1c0c28810003801840c91007140a03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 875890674 1250 875889424 875889433
    0x516230102030118090c03150c081506070f0203031219060902040609050127060e09010e0124111c020f0109110609030c0a090e0d140304030e010c0606090e 68
    0x21060080c200e000a010f08100044025420240c1d42d0311600042404c40c020400c100302556a566180704482c3c89100d0000c01c0c03502c8a43e21405140c01c103011544c070424001c070414a4050b00000580d0f28440d590f401888003120301d42d914203540b0200b00303171480c000350124603510500301150350400480307100d81050161800d00c0404240081c490090750111031440d02c60500312424400191003611407555501c030085410302c0802d0100d05500c804000401541c1c89401d00f100c41c0c0310074007400990507004003207140b11100040080e01c500c202c003400742c2001c815486100380315a040c111241e04544c0758069480c42261401c41564590820b4490b000c44250215042081941d8505081e00c0e2018406004800070301664149828800001c28100c003005054070128500340e40020703040d482d5034112000c4141c0c1d031184900001d201f044040004a6541003200003d082079400618502c00203000604000c8086500c1c07249034020340400b06260740c031005c00d000302a120800d21008104006012901c3e124 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 875891924 1250 875890674 875890733
    0x1207020102070c031509060507110705012a080409020403030503074d0303010902070b06030a0b0a1505090a0c0305011202010c1101020c03120a030606090803190516 72
    0x510032640803540c440303e80c000007450364072034410b1880381008503502540c0700c6072504002002c500c907443c4512032a0300c40e140414480e120b01c516181c802c2d04414144480c160480071900e04084620840207102c120b1100d10448900d060310702401581d015100803800440c01004054224010314807589107a03680c1c0803141820682000500e06c0d0308400810095400440e01c00004103000b40c802e1440501c0100903008015420145154402d0f80180c081607408682c1301d04000007501c1894200b1011070050482d4803207525a4000098050018103680d07560b0b4040066a41e03a03140d041000b000f006200c14400e24000a501018101148003900007034503080c0045100d07640c40d444402166010b9461402040c02c6517200c4201c00a0459094158400d0342610030b801d0b5002c10035212140341c120440741e201c50030300c18041d060b1286a0071400600c181146d090002c807030000b00307886e41c9020048405401c0c8070024000d981d2071141000602030510101229401d115200c2c682c4040c81044652041c40d8a0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 875893174 1250 875891924 875891927
    0x803031923090304080d020c1005040e07030e0c040c030504060c0f0509121905031c1b030f1d030c10020c0a23070e16030e0304050d0c030203030409021207 68
    0x2040208811000400300750441c000341c0900803a00c1d80004004100c07407805441c0c0c0344a500e00141c0041c0180103070301c484000942803c010034107002e2a1020300341a414513003032210b41e01c0217400052400e001c045c2e4942c40b81006900800440d190468060020000c0d89001035000b009000201c50544040b030420580d80291845a451a030750201c55650722410899940100000c650341d482044805114142d4007840740c4003845101880f0520030b500650f941e11038000b0701d030041c0183c81e14480712245040d11100230301003080000c00c1050004d28001901d881926200f10080954a03000900c0083c5e00c80090311451000004042200044049400d10010300540c0016889240c1102680d030700065664000076a1000c401c02c5c0080858030140710050344001e00300e282950940c000352203007104a0902101b0340500511110341c0e586841c01b8802c00e02c01b44107903907480c403803841400d01a8405102c16002d0020040300d240185900509480e661079484107a40040d4100031005c6a10003010b00102d60348a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 875894424 1250 875893174 875893181
    0x306090708191d0f060408090409260703020706030c0206070c1a101a070804120c0308030403081005030a33020f03010801050609091b040f0e0a11032e02040f08030319 73
    0x3290b0084210382307040c6543e000d0001900000b081111101c0310980b084c180d0340c0c1140590500c018160b01c025032030b80340b2030600078680003669100d1400e15180519008116a000c2615507000c0c0c05401c041045400c1442c00f07a03000203905a002100c01191010710507805c54071041e10040b5070441000c2d0303200c410040100da2940c40f0740e11006140c00001c0200300070302a00003000c2944d83d40500c4591115587d2a180d0b0052648202c40450000321503030100059500200389110290070168002c050729005561880d80004491210350f03003490303860b070840800c90a481c1c194a004e40c03403200309645510034000c9035009900300303000f6882c2c20b500340380018003a820032842c118407509000000f0004e200c00042c0c00440440707014103054005440300040001207087c0d0181c1a100501c000c020b1401101c0e500302100c085180407031107803107034002100707a65401100810304070b040101829071280d00311003200014028451a07025824200c0010000540d40c4404800755105505080094410310320508105007203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 875895674 1250 875894424 875894431
    0x80c0105071b0e010e0f0a0506010834020f0f030a050a0c0305090d050c03010f0c0507060e03070b01081005130206160309090e1b0301020306090708191d0f06 69
    0x148040c07003108003045008544024015080034603442c000e803102084094418240c110074191155201805104200d150121b540020f20540420a0f402d020000a061260150035250740f103020710f8103010344c82e40c1810b103105442c50b1000020500b10341e00d04007a40b5031880341c4c5070240f1801010003e5445510100031146020299980c2c1850715040343c0382564000301301c00341036040000610050095440303401c2c4403800ca034010801885100511070416003035400d00443c1d102e074981003481c000381e005c0e000010340700f070303942e00000209202d4544c1002520b03600a2000151502005500010f41601d0104111509032840c0c0c2c1c080c4010743e5001ca0251408030600d900070740001040200741d83c0c82d042c820103848054400e00d89000f22664034299003090701d0001d11809416041400c2001c50b4200c0c1c1c803040d241c5032034294001d41c11403410000081c42500001c280c142801b066000040b60759940001030082641416420080c840c90003901d146022051910061584100f4040c1b0702030400001c3c0c211b10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 875896924 1250 875895674 875895677
    0x50c0f06070807050309030a14010e0d05090d050c040903030516081303120906090302060a15030809040c0c1a010e071d040209030118060b0f1e06160204090c0e01080c01 74
    0x3401c074407940c1d46607180c0d000f020280c0d228001400b030610305c0d9800740140880f103401030715280380e076007503601845085500000300351480794000007001d400c150300141a40c1415804039043e030b4503a5106d00740241841900d0703104550051520440d030301010b406600c214010031001041601d03168140d54195240201a642c0d600115101c500800000b032040c5c8120000310810400070a0544099407031740155030751410100c0150304100e007080f003114090704c10000c40100c0588503494061840d12420628031540c2c01050080f521100400380c405c0c0103405c0d00ca2000c1d4082484103440c2c400007001c07a0403940c203006140c0144034640c0406e000c2845504007184800c41340125400c01c0203181304100082d4003200c0c000e505552074024488a6049070208148614040c1401044000666041081d54941e400103d4490003002e05003845040380c641e4004000e807000e54441c0d66603d0181104482c40e00c1c1640003d41c007038140307061181048480386541c0f04485940004c0c050341c0e40ca50034200d4880c1c801c0c2c502c0300d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 875898174 1250 875896924 875896927
    0x3030c0618020603040506160c0809040c0e090c040e06220905070513060f17060a0506010306050a0b19020d271d041a04030e011d0406080a050c0f06 65
    0x10804035400340740d0000312600c0707142003144564042409a0022641a43c0c160040820001da6000481e80e103030500c002460710b041c49038901d0381e44081c10300582c0c00880c061542e0b07900300342c012030085c891148441d000030701154951038140d10746e90300c80d403041c01401a4401210049856401c01c0e9100014282800000c200c00154080b61035006141008041d1558480c81c0000907003070b00c80e0340c0617105a034550340300031072850305100d80001421010741c0704910b40c50340110300000501c0045000f58101080400105090700c1d2480101d000e000325400c8503500803070000000441072205802441c0364042000c0305912840580e0050703071124848110703d40031690b040542103800404074014143e008840c070016640940f82d0044081904c04240c03440016001d4005020510180120480d010406403c2d98425894140c1e4010b10007078012840c41d061160301c81e904d2048604880d425103007400003a10411500c0d6407030321503980e10310782c0780c1c0700383c0c1d050280403090310f007500703105ca2044402c500142445 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 875899280 1106 875898174 875898197
    0x2100203191b0206240a06050702040507090b03010b07020409050a2402280203093a080a050a180b04180507080402120c03240106090303 60
    0x301018240b081d0005a142d0001d500c0d40c0c011150790012486161501590f050100c02c4003105900c07003131014020502d01c0c0c1c09000703000d05900840d018800c40e16441c0056941c143c00d4015480c880100f00018010b01141340c00a08801d03101500019200f08261144c60410101c240c00316160003180e040300c400c4c20185502801c42c420030550446c90b00410540311240801c407400445080e8401403950902c05000b84191030280c1805803a0b02000c24042c541c03148a0101e4100042650200314410a0403240340c001c101103d50348043d00c2440c1034210081034800d0740100d00b080c0d0420044031900541c0105002c00000240403446806071500d0502c1a40c014204080392540c621a140c401004038550b48270300c9243d080364044c0e41092145980840090a149500042980600c14800504030f0741c403035500700c0004001c803052000c5ca5170362262011142400d003440702500040140051 = true := by decide +kernel

theorem cover : BRFrame.Cov 875719424 875899280 := by
  have h0 := BRFrame.cov_init 875719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 875719424 ≤ n) (h2 : n < 875899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
