-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1922
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:09:55.78991+00:00
-- url     : https://prove2.me/submissions/a03788ea-4d1b-4e58-9818-4a23b0e32e63

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 345503597 ≤ n < 345683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 345504847 1250 345503597 345503603
    0xd0803010608100b0a0e0f04091e170a09090c0c05190c05060301081e01050405030a05031905010305010b0a050307050901090b011101090b0402010306060507021f02160807051011030703031116 84
    0x600c00d80030400c1000320350340c032420380107210b1443c103d080c50004460150042c1c2140258a04c02081e00ac0d6040201000e400e00851400001001900b41c10803500489410241c840e00b8904205140840c141030b2010640c04402a03c3c50b41b280c6061503424030002d00c520f0032036100702100320106550740041100d5402c02e80000e400c50b040b21662140e085000c002020144a000000344081e0600c1d0726031b01c4d00e91003000d0f005001c2000000c00100d1400c4071418486504680c071000300040d6a4a003825402015080781152060301c00d9440041c05107000038814083d81d0303006100020030303480c1c801e03010000d010958101e030611003440c5580e03a82c03036003e1040002d820b00850b05040c3c98030305480010201d41d40c6802030810721205211141c0507841d0035800d031564410400b40001d540b0f00400e07083c2e24181c1d00b00041c0c00303c6007848101056660001c82c0c0300c0202d40041d94484980e81c0f0070300040d582e00400380d15410340f07503000b40302c08070220b8400e030130110080160b00e12403890301d0409101e00010800702c900907 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 345506097 1250 345504847 345504857
    0x1804020f180a06050d0903030b1f0201112a0109050307030306050307050a060c02131803050c010507030225030c021509090c0306010207030b10151d0d0803010608100b0a 74
    0x446908604000d85400e03486044986010590602c10f000e4032070300a010001d0240c0740c1e40d4080f44c0402d4080d1313100e074030081002041441c0484803404041410740d218211700b00194240800301c201818054241c841c0c1d88a5000a91011014158200040e099500d20080f45640301c0c070038440450010300c000c10741d13240299804503285042805061a0030401c1e4001d0303000c1c2040480420100344c0c00f8a03d2841550b0448440500012035407088000d0009a14400604615040314108254101d4010121448041c0081c44641d4404400760128091348040101001074420022104000c40c003451003200c1c443e0130040c007201d40540208817a403007040d599240c4120f0004000c4191318104094503800308070f400782c883c514034203080001e45540581c84018113250302e80020030400c020747c882c0c48000d0b0007a0380d07201100e0f51803200010901000c41d011480d10055010743d085150400110b0a40b4180e008540c5a19692030120102c0f08030a00a05030200d0710b1214101007003030442c0ca80286199101c564078 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 345507347 1250 345506097 345506107
    0x20303070905092e0e1f0503060408030601200601090c111f150506030403020a0201170408040b0a02030d240e01080a1e0c060906170403020c061804020f 67
    0xe42281c00700d81010348508400d02c10008100c0d04440c074003a20300070740310042d10400702041e252000b00391245c0103400100791410400129050280841c2c1c5c00c180101124407800307503604281501d5580c182c1d80a840010108002034495020305074519140b240400c0307800e10180c4610302282052001e0704138482841d160884d41281652001c0905601c480020242c2040c00307403401424031101d1024075540916031116100e01030000740029840041c0000f4000703e96904c0c03d43740094641c941c0700e00481c00310b400901000c503808030703240340c00f0301c520340c415000e5103024182078400d803503900034240d46821840100320718602c5101e60f00907004004044011150940180789080b0880019a006a10541075000042004100c0001e6815140350400d40d20700b43c484410390503220b00e4654600c080d101000074030000030902c1e0302c4505042180c5580e070360b1803c0c58043e042071302c00b1000203071006030040c0d00030100e6407010311300300c03009040050b50710441301c0c1c2000c440d8020800303076041074844040f0303404045a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 345508597 1250 345507347 345507361
    0x150801030309091e3201030c080607080c090a1805040b0c090319050703020a0b0a0906030b0d141608160605041217091c02040f050106200a080a020303 66
    0x7036406020720403014000c061081884000d4049052088900c45031a045080100c05c09103075481c00ca28003100341e420260a410044507000d10081c44100c400055800c400611000d000c41c0c12402820a80ea03202c010b526a03440540140e002034001640c07000001c2c4c8000350b56189801c0c0303000b0b060012070b0080391910b05801c2000b007c90004000c0c2445540030011030909545c0401c1050441807040b030345044001581c21702c1071034414103400003500403101703c00105e4240d04003c0130348011030060703966020054441104a090b41d003681003207500008c61030b0364400003585060500c0a100ca0060488450200368a001059504545d010180c182c008403000c1c3c04185042000e00054a09420101c0c80d00d442d01e0b000c41a20b20850001810341c00e100511a000b01c0301100484007039420042480c4a0b1304c509501d800e0a190a03480704903c203d1400312060720b05d18187c01054101c800d65210f034001d221143c003032501242a94461a5060b0244450540015040c0800ba207241c00303c2d42e005640301d00d0085 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 345509847 1250 345508597 345508607
    0x10080708040804050d0f0323090103020318011104080705010903020d02040905010e16030201020f03030601020a080f1c0c031515030218030304060c020111121b0f1f0b0f0303040b0903071508010303 86
    0xc2100310912300002180030910000804540c6400000e190040e41c80da900e01106030307900a030050302e0850b03500f042c03e0405030800c504050f20949002500740d071191507a410042d50100c5903448020b4000d41ca2030746441c090b01d031550140c5103441c0240d001180d04203514105070704000c0c01c2400002c40c40d001c1541801503590410004100c14018401145541800d0f03001035514402d03880014460140000c22030607502c08001a141c540c07021042c0020909941800d0101801c0b82071f0700440060b1400060040e030341c0090b441c05080394100c4280806101319003804901a44c85500310690804e84e801041303006440800c0104010f000f207545601c050380c658800103140743d0360f20304072255546c000542c4603046088141101c1d0140b041030100c0400264000140b81404e12511040b0f4060040c404a2541495130150001d4a59825901049525080b034100703d40c0c0f0000241c0c068059105020620082c80e04000070090304030001d048824050360f40008000c2d50409103400c1c000213070000010800c1503000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 345511097 1250 345509847 345509867
    0xf0712120b0406031104090317091c0305060f0103020c011503050a06060806040302060105190e1e0106050705070302040c0908060a06090f02091c0c0f2310080708040804050d0f03 78
    0x1160300380f0207a46142c55144882403500c1000388100d41d6007200e541018062000b500c0341c645c5002c0000010b06d0464180c0b40c560014562a607074144013084403105c118400d201d954800d000040c280749925030028011002500280c201d036006641e10911401d2580c61640c6160003544030340c0041c159203c403440c2003400e45149601450040d400f0500340b100098011482c141521019508054841c61110402e82071b801c0544c0128550034603182840700e4660846080300c841b49012000001903680c0701070456491068080240c000d402240c814001840c01c2c0d004031600959510340740c401151035040640c1003000589107001c40b00e070344501c10410720140340603c3c0300044c2c10072400c605228405004c03400017923000000c01c1d40d69410322403003400c00c100d540c80c00d009405012034414042d030b180ca4048410116840f1103c10000b0704460f8030109242c61078484080d00310170303640c900c090f4031103c1c42603401c084050021206800d040c03002083d40e40b01d144454046030b0080c150911103070f0315420058002101 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 345512347 1250 345511097 345511099
    0x40b151c1707200d02060309100605010504061d040204090c180609030206030109090501110d090b130503040b070c03051204060315080606101101060b1c200f0712120b 73
    0x410701110300490003524002c0800158214500d0003d118180002e800c1404d851009601181c04814815030f94000522a4040b110050003040312a80350401034509024511494002441c0e44004c906104d0000041400c00f0714040d001509054513100a10180d07400080307064005030030800e054403480d00200c0031400822681c24030740702031811034001c507605100500a00c0c0c074560301c40c0985d400300b2100754040d016140242001603100c10401881c200038124003801075070305a18410202e00540c03200c034640180706034850300a514283c900944508503070001c280c15640c450b4108000404940140200c5406103521092540d403076052180150494424240b084182c1062090174040d41d00c0c002062500308800322440c289003802207204880802a120b80030020703509000700010000c10002c094074081e800200c401441c61300ca45a1081200d00d00780e03c4988030310060900d503415a04071402031107141081c1c0f28a40c40c1035410f8564113000aa40105100014041010200c0c001c2070b5105400140d03074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 345513597 1250 345512347 345512393
    0x5070c09020c1c0203160b0a060e131112160f0b07020109180f06030b0402010206090f06010b031e070206060109080d1d061911010501090504050303040b151c 69
    0x140b541d102c01e0b40d40c1c600440300810f04020542c0645150b00030015200c224030490540103210f070b03042c40c00c00302c06041540c40100b040d040c004081950a20881d1603481101c1681041062001a44602c0141c9ca60714a24a401409900829005110500140440b0444c0100c442d00382e6150408105943e0b0865000505400c41031000c0c1b8010303a4000c04c2241200c070290721400c011714801c1c4900c0000c200e4030910084080c5802000410804042c803040e2042d4002d070243da0f0b8550307441600300c0e100c14403640256010f80241006114480c1480007854100c0c1c4203041d010007107400308482c031044500a8031500d01503800300e0b04022403586d0202e030520107020541301030b00e00e0385440030001d020790021082d0400501c0310703412030040e00d071210415210710101c8880e07902c2104420150241000c501100520b41c15401c0c00c0000c15509100d000700d500035680039000318036545d91f54503046c0c0f07561809441406002440051a02d0030f41d20742d6409a01010101440914070606141c4038010408203103000034144 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 345514847 1250 345513597 345513607
    0x10051005090408120a0f060306090203010b0405010b040b030705190815041e0b152d0306010801090f2a0206150a030215070204020a050415021c05090d0b0705070c0902 73
    0xd10340000e80d0070424011302d0701c80704d03502c1c0d680b07001001c1c4c042ca00c1c101d4203071443c028000050080c25000164081c0c001c0d0300801c0b03068041d60500003510024050f06150400801003049103501c4100110b511240e51300d0040d007032113040c5504a204104a9100744005040741c0c00348529070800100c03e1103410004c4074208402401c0c0007911031082050340c0c2010840c0c3d07440030b030001d007501ca0030418080e180840d01c0060381e07a40002c64a20005d40d4082500f001003c41c10300b0713191a01e011108807406042c0585400c06a80c0ca0117020740c015107004070100ca06551601c155001c40003207410050004000c041c612483d03540310100091421400030403c885000c000e0040e83e01e80d84684001c2c405581d01138031000030b170042c614540d5400d84071b0068000c5d0840e2000464400e416404000350050380e21940d403200c814406600200da0324110f80c680700101c0351750074507a10121401000204829030000c0e141c001101d01c1034403100342c2401e04a42d224082600040c0700c0e020000e550b021080684840f03c0b00318104 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 345516097 1250 345514847 345514853
    0xd060c1209050c0111100501030b160203040302130b0d020d031d0f09011406070c060201090221070603050603010e0f0a02100c030207090515030a03030e0708071d0711100510050904 79
    0x15403501c10009060049556803822400d0082c0800e07085006c1800007401203507502c3c07070010040c1004480172588201016a404185407000c07040303070b04803500180103d19803c900c180040c0103052900d180e95003c5124031191005031109500d40c01404c0c0a51904c0c045030040310035012803000401c003900d11a010002e020303010b940c1c410103000c6c10b44500404000c0c0c80c0142c80041580c5108004002e002211501d100260241c0d05410440c0f80d50320070307a4444185802d04612205202280c00740c003120390407110090003001c0c42031340a60340c0180c00600220344032050000040c1414201b61010711f2a4019140040030b40c1000c000c07460600c03010380303000303803852415844c02500c0b4086406054032654880011464a40d0562000300001030010140e40801c880d41ca000b40c0200442c41030501b0368024030b480055182000f007a80c8003103038a650100a030703125003040300101e05e440040207102031180c011462804c00d8404c222092002e600070340001000d00704800703c5410180c056011a20400c1b81100304000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 345517347 1250 345516097 345516103
    0x122406040608030f0a0c05030d1509050915091906051b03060303040b0702030a0c06260702030901120f0204170c0913060f1b020d121808030403030b0d060c120905 71
    0x79069605a0051702c6009188040700c40d0890000050013521012a0500041c4900e038001c03844a1000c0c1c20f42100386a84100b608181e44003100d06090a8201d400c106006d0501d00b040154400319540650300081d086414001d02c49030120402d50b0025560400c00a17825040b81c0e641080c2e565244155046180050010380d8034400c500403941310b07650204844c411500d08001420707065500400103c8030585804008000074075514010305080d0356a00d03c0100c04c4030040301d007405810303242e000c0c0d03140c100c1103030040d206055a4010350082a59400703200001070654030241000e000e604001528003100c01d101c0500c2c0024200045104941100c284450400041d0180100607484540458a580c2c403074404c0d8003c081c6070400b500c2140084e007604486c030b5804603e046000720551108000484000301e801c0445900106140104061040d0040030a004801444d8440e2003450701280d00210a004a54103030f541c01d40c100ca1a9468050044d00742d90000c0944010034903c0703400300509185a1075080c0e0b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 345518597 1250 345517347 345517357
    0x1120204080d1206050303070f1e05070b0f04080d2003130e04052e060e0c030c1e0f0d0c03051003061d01050f01031e03020601031112240604060803 65
    0x1885540d80b0f5500780c10a550700900002c00d0003d0583c0d0300c1b107800d41010013404550b640c0403200c00c440070000311980d11964000b0302466801400800307a40d400d1490003d620b9100400810a15005100c0014a020200814038541001d03640d007030701e120f80c40301ca084080030b14105080c915130424480401c0d41300702d4030782000c121420030040d4142c2c0d841d207080032800c140120f01c1c00422458030303142d10b440c041d0300b08840c102265150602008119610001c441e92030100f0340c1c1c1c0501d0880c040011034510407440002c0c08a150b403001a414070031070500310700310741640035101038400c0110100d406504440640301d14018586181002e10883c6040c8000e0303605103400c0d01005000c5651084007034000301c80c600d140c03000840d1180c020002810b00780410107143c0c0d030901c412070741c240841441c1074180c95008400718120764190000c042c0b607403d5980d4035800421001d2000c0d00420803424000308807608001c4030a0007000c5801030b19185640c10207040c1d6078000141021701541c18120100248640002140c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 345519847 1250 345518597 345518623
    0x1b2103070e0f04021b0a0c050a031502090a05090702210301060503190b0a1d070504030b0703180b0a02120108011b0507080d06080f0c041107030e0a091104050112020408 74
    0xa50b002c1102d0002074000d010b0941e07034071035501814010411001c00022032400690040c0e0700c1d511050781d40d200b041620900781c00010a40d05001d11220f071031200d25000f401311039034028008003080742c441c00425184807007101c41c40c00581c403803102d1a0a001c81c4e520a03010884200380801c1c0746604114025245100117000d00d4080c0707023503825040d4860a075500049040d01c0003050400070b259650038580e0100d0030966030a4501d01c40d5400b107000c480c003410032201207a40c00750310f00701d8503941d400c0d0070340c02000e4008041884507803280d01500000d22208029114200c0c0040041c0c454005001c8802d0488058000783e105a142860005d649005084045442d824501d4110ba60700c5d01841c0c098858010300308841c81c0c03241000e00200303403408041585240c01c2c80e9582122071100c040420881039030514001d00300220b808116a8022a00c91000002a00c0000e06400441c503521400c42c0d00710303201c0d400c02014031040030409000030b681c401194420a154130f01c06509042c24140850b840320741904c810 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 345521097 1250 345519847 345519859
    0x6170616021911121f060518012102040f090312050f0c0a20070305121e07020d0209040309050102010629030615040b36151b2103070e 59
    0x248400c0e40e12003641604112803801030f0388040d10705d140408240b6403240c40000a2500348080400c4506200f5819000c82941e124100b4141e46451850141508109003030f103000102c140114015072664000c0e1110800040800038488410341002003804289001c159005420f1134140809400c0000d00340341c1080d1504445680c40700c0d4020191019024030b04082105040141da09203101ea000c40c860003128040c5058624060900c1d1b80100300b48100aa41c00f0711201070b24103001c20200708000b9021403440a4803a64040d01306400082503441c2c02c60301200001c07a81c04040c41296030a0080c40000d21540c500c0420f50200340d00100b1250000c1c00c8080230031140400001d2241d03031800c03001c00d0042d591f06684d5582d00e4440c0401200383c0d0201c03a20301d008003107203942e9002c0d1a62017000f40620180c04900300381d0b400d85690420171116522150220514014800150f03202c0540842041c00341551001301020700081e0104500e8002e100344003103910303000380104020560054080002180300b1030341 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 345522347 1250 345521097 345521123
    0x10207030611071a060102060711060103030f030b03062a0711040b010c0c06030e070f060e0d06060b0c031305041107030804021309080d0515030a060f061706160219 72
    0x107a0501401a1030700038000e0700c65540d44c0285091124107585c0102002c1c3d0030b8490982e901c1100381c40302a10054000d41c941d100310010804280b040c01c000c45001d140389000304400010b600001d1600d0380a0344d0344c400310b088103c00300c1a00104c02c0480e24001c0038a0303910908141198466010603501088907601650b00c41440181c03683c0302d003011031007150780070800c040b00341d4030358000800030a400c0440c1d07902807041e5840030540349844520007040f580195a0218550600320500c0388014041d1800c0b50032a85803030011030b0b201c2c0c020016140c214421802180c842d20000314003544041c640e03000c9401145010b00e0000003010080454031459010302f41480c07075444a00c0400c1e8421169031350210b550340b50079000b60230030050000625404c01440c1c824059912900781d031002d0702c490f002c42140d141c1c0c001c0c500d41c4009100741d000341c024114100e50015020381c0da520040003a5050a00d0f280c1e09800078400c011162808407204403031080310344001e285080f90710080170418810301202909219031444 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 345523597 1250 345522347 345522371
    0xe0601121a03010518010f090f0f03030b03030408010c090b040609052106070905190f090b0a0f0e090d0314060f030a06060905060a0603090b01050d050f07030b060a090b0102070306 79
    0x71240c0300001c0540204440d18010256009100c0e110100c01542e50a104102c0b03031244860140e40a00e035007020084000ca891036071241c40f5443c110304e0440515445041490f110356083c07000d031000700340100022a008103016402000e08450350040e00d62924244001c2c80410360040d500c1c0181c400035545d4058452511805c01c02c0b8414641c054019880f40c04204501c16500a004a0072114141c0d04000d00c40c01c1220640032080c0385000f00107441004490030000443d05411181c50b007400502102d9a144d1984080d4020301c509400c5000f030b40b0b4001041c8001c0840401c0350612110741381c5010042d81044c0041494503800240c001480341400e181d4500403660140880e442c1c640d4071239000c001a903a0b803686000581000c985203031041441840c00130702d0f42c1c00390291a0011354071030f0203180e207a030810082080a59400c0002e1740c407849000c1152001d00c2b810044003000d07600992040406141c101d0070400035004a80009200343d081c078170071035200d9030005613050a60303500480204110071850 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 345524847 1250 345523597 345523631
    0x20090102030d1e0509060727120b09061f030308060a1806050325030f0804080304080c1512070c020103150b2212122003090a0e060112 59
    0x2c08604165203440011210301036104100c0000c10100401882030f5924010b0b42c81e1252000c84822022840c21006c0b20b010042145c105480e900f11150310b2110203444488000da03554240700704940e1141c202d0140005064200801035024031034a00050480701074040c90000f48880d488001d0502c0380c0800812010b0351260310745070242c84911801400c8890740c0002d01c0141240384201402400341e0400b031a080307a06190010344014880612410f05495981c4040140800c10010340740200309100201c1d01c054144014401070107041e000780040e41d070b03201c01c000b00000810252585440200701d0312100c402542c000d07992025507401c5c81e44003500107000503030151059002c040000000c401d404200c9403480d001601151103c081c601410080d03a445400600045000f500e0303a024018040400150f8482c00113080704a041c0f41c240662080105081000c1209509591894102003400100c0b800c0c1182c980005151909a0305081d003042000a007507001801410700e641c0b0b0702d4400c0303403155070f481d5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 345526097 1250 345524847 345524857
    0xa080a11030408070c1e03080c0a0506090607090e010e04080a11100f050a0b092a0313110d030e0d05250612020711010f0e0d0b060a06032009010203 65
    0x200e1091640c80c03915142c003c555a01071403080b01d10440070500444d01280000d03c110100c114903044d00c01c06800c41d111042aa0440c400c04121842410214000218188202070240c24108001c0c103250504050251182a0030341106400a142100400404100303582850304030741c01c001d0461350b030711090344119100380301c01c0c61a07a9940b140c00110240d014107a031120b002030504500400c60364880c400c40405a60030062002d92045141e40071030600c00240d2410000706820400e0039903400500c1c00000c031541c10440d6580c603010301c40c0312481c082c4912261580300c0010100d4550b0301180d8213641c0502550031150405000303c10016480d001c0000c108080e8001740216118035403001060400c00d03048003024041d00d800240b0700c9840d00801c05182c02910403890703000d048484401c0401c801155440034148000003001511420140551520750140c46024095031302c007000c0b0b140450070301c000305156070f000c50b040502e411800c1004840300c10300e81c04d210350804691541e540100700100e1440c028 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 345527347 1250 345526097 345526121
    0x20a020c0f01020c09010f06030606021c141615050a02091e0d0503040f090b01020a11040207110d0501090201030e0a0b06061303150506030c06041203121104030f0b0a0509030a080a 79
    0x91700e0004a00307400034600d00707001c840c00c80c2d8040c0310140d200c42c0c040741c0b503100c10380c8145540c543e030049419105010394085020f044440c9001410451007200d20ba10705200701d501942c0b00e00c038072a4000c12221090040b2940000724000c290f01c0e001042c0007180c0d203602c000c1a442c10407046180384400c1c0395501481014400d410000300e03511551500321168101d000d910450746001d25040d8101203079400400ca00031010b0308203210705111280369003480069407094508460590381410072803a0380da2003010060795a8091000058031441a1002504885109000500c240e10003860140010108200c00354804025a00240c5811150800e542980c800d40c2000348108920130045a0304000c680c01588246822000c56080c0e080c6402408100e01c194040c9455100000e00000080390044024414020b4005000119012100b464100d55002500b003282d8040071180c03942c00b8041030621454101448540c100311a0500d07400f820764034072072140f0117810712031381030000755100c0300b10380c465454012 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 345528597 1250 345527347 345527359
    0x12040f0c1a040f120203061504020d0617120405031906090602030f040b0105010302120c18030607050a11061e040c03050a32030405130f060b0715020a020c0f01020c 72
    0xc0070940c1100250083d019501c456682c100c0002010424088042411500900944a95100d902207024105042c021481d04107030208000c40b500066445488006c0005000450005070102d440600300014011018a1403038184818400790342c0114038400c20f40d003840001007010301c46207040d02c0070f405aa0f01c00f030400c82c800300c100800c452400c001c50f840b0328800c0c0384202c0e060b85c80d032005508130f0103501c00742542e4030461000141003440c200c00800710f50314540980d40031204500002854130b0002c4a110001490200c0d081008640101c120b001c40704102019100703d107411001c130440d168401c40c100c1c60341c040480114041c020b46450301c070040c1d41c0082c1038810026590400c004d401e103100001c1804403400c0d40d100500c0352560b800106604403c7d901551030245048204000803c0005004c51008d0f61061110048035262007a48002c1461450389625030065050881e00420082124401036004020302c1200544c0071031003a844407401c071a4403112244480040389003584007000c50350000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 345529847 1250 345528597 345528629
    0x150c150f0103020112050906010306051e09071415030a05040f0c030b01170a030e0f01030f1a010e030303010f03081602090f09010c030b060f031b03011503060b12040f0c 74
    0x203051900c10341600e0007030302c1e401d0032180d40050500484108660101c110f030000401803000031010b4118540200c20340b091000e11104203036002551000030f440c1b564259000e5501003081c0280b40409008448044800d980d4111113082140003c0c840205000102036807280041c04002072003000b08845a000400041182e440c0d04c0d1064030100280510a401d0854032401c80350808000303030006c180d9a1580e141d42c0102040020f00910404640600e4141601c40d0780d01040c680003480380781d9040300c00000005541c04d83c1c10024150342c48040c0054000e400410040c01401078851008003100d0b4003048950b0f482c00d68800384070701036480c5507000f0351000840342400a003d6480d1103141c00b5a80e810020407001c2071108082e030880c0d606010054201109104a583c809012406944d101d0026003072002c3c1000c0d00da40511650340b00743c001c2c00600e240c001d02c0d18152036151056101801801c4200703450001ca031300c41901b401c80d00a100401a400c055050070030008030240020003000380c4803842c2070517 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 345531097 1250 345529847 345529861
    0x60e03190504050301110f1801020f030a020c10020a0b0c0315060703020313080d1d0a03050f060108070e0c0702041a03060a1406030a02010f120b0d0c060815150c15 72
    0x1580c040d103e03051107582041d80d4450000d2410040721140c0c0345ca0f02c24945024694000068208201c500032030641c0564070601c00c0c40e80c0148020300000209901910725400c420041001200341214410115448007490394009041620034940040d080303118185c4a50300c20360130300781d0406c03461080c5810400200f520400c05400001400ca064020050f440d0619210101d4595807002c1610020006105103070b403981c43c000007058104142005480c1c90301168690700d40034544130307404812110360350081004204488051054801820881344000100d0804000740f901e14020810081d20807503480e03410044100d091924100c140c0000303170076038206152480d0408010072002c1001818031009000240340e9240c0407440203003455050710b600c001000c0c1d80800300e03504800960a0110966295101c04080da41c509100700464401c0d00b0602081d410020003c2010384080c02501c4450402c28040c80c0c0c5540f040360300c0d4a080700d1245507540300c515410f010307843c090f8101c41c0c2400b9002c0e60340078400c070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 345532347 1250 345531097 345531107
    0x5121b010825050a03050a1a010c0311060915090109030e060a030f06080f0f0721050304080109080304021809060402150d09050a03080105010504120f02010e220e0309060304060e0319 80
    0x1c3d441174030100304580d58201101c09842c0c0c0c0110a4620381c1d0007900d02c40c8558007580000806c680a440d2004180380d00314005803a00c901650032901070b40c005000303c0f040800c0100c03000c1d8050340e00390080c0400c2c2c0c41a64098464040070901501c1004c0100d15041c1c0301c1e11a41c41f0241d20009100144000b65540b031400e9192200c503c200642c40c0600003001844c40000200d480c01c807050189641314296100d10b929a440303484900460700c60004003c00600b0b41002d0080405090040c4031899880c24140f04104810780b078180345645c2d81c2a400c0130000443c0011800550040c3c05072900804451689000e100345c1c401c103024418043e2400d1245030601c680011340703800042c825152a2050390300c410054805004911500c0b007460000e030449070000348500d540c0385e0000e02c18140f0324000d140c034500180a902da502c09200c0001c2d001c0030f858003640107034041d01d05214240400740d481c000d089004150310b4400104050401500c405030028150301c10001c0780c0607013800350881400180802c6000b48 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 345533597 1250 345532347 345532357
    0x2070b040506060d031d01050c07081b1816031805030306041a030a060906060504060605120c09150c0a050d0203070302070b13051003060b030a0605121b01082505 71
    0x2082c1c0304560018800b424842829540c494154403000d01d00c411100e49100d907900e24224040c1008018403280715001390421280d0042e100780350113403240002180311003019241018a41d442038850401115205000c0c0072900d400601401030b141100c1204001540603000f031420340c075840e044a00c592014003001002850103078404441c01d010201d80c00c0f1600d200314001d03000c4258140c02c514459000902130380e01c0800d040e0702c255000300e5010b40c0c0b80009400c682960b800030b004a000050901c511302c0199034400d500641040030a800c0042000c00f188400501104984c0025400181c12400e0341003040b100101e10740c408112032125920400080d12604000c03000c4002d88603900011070416260016620389191481c41048200c1c9414100040c144030112843e013410307030b55a0040707107412404c1f0003188200e01115000c904146803078144584c04400031070b200c83c5500840402d84002c60349000d690308411091a0460850f1518070688044d28541c00d5007024170300341c90034008801e23500000500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 345534847 1250 345533597 345533603
    0x11040311041e1a1807080718092c120f1309090b01060903171c0e1b030c130b03031606270302152706010312090803070308130602070b04 60
    0x42c204484103030501c59140c5002000b0400d4a0a04001850840c0305114030350384101f01e07203884815175441425015020074107400190078152030318140c207661b118121455044001c2800d0700469858419a04c60b100c03812000b90790340d02d510000d481d450350121002511081d107400000007080310f568610810003030a20240403292050440000a4180d018000301700450f0b801070410080504150280f054507803000c00d00d04d08400c0ca1000c0c07802800740900c612030801103032000920416000c4002c4100512074400414813075800072101d41d6072600d0703044240b80d059800344004540c0302d141c100000c3c203500921349000c1510700d402201c202440090b030010f03440141010444411001e02142d1101e10005810b00a000b41c4c0c4020101130011044480342a0b01070b41c0403003c1040c14a070611043c15140481c070a10645500c0070005105100d6290b041020071540350600308002850082120b40f2801803020103428800120300080da200b402c8000d41040c29400f4000315a9003009107020312280c1c0341a1016 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 345536097 1250 345534847 345534881
    0xe060c0a03091d060105030709230103050a110d09030905060706060f050a0305060415152301030e07060c03020109021302070c0b03061315031209170111040311041e 72
    0xe100f485907900d2402c1e101250704124641d921440107440590000d803800d010054003060000302102114402903c0030b610458000458608030001401c0d100c0140110038000c1c600802ca0320400d51040442d840102c07080c8011503200c402c0e08003605d11001c02e600c101c3d00110002440300c1001295800075040d01d249180802601d900d4200f886840300d868000107003039a2004001c9404140440f40c1c10380f2501e414039000c140c0b404400c180c180041c0d110741c40311000031001d1051410350a09031202d50344414080c681006940400003100c0d0741d5121078480c11080c401d41010038802d242c404c1d0440044250054990560310543c01100c3d03000b54040c6c801903a01802c02c90300881d00e02d90301d508490107413a0027811b42e602d41041c07542ca800105810007015484d81e2a4000001c0000d01d151810702c80b00c0c000d40c860000842c50600d2807054610310264480a40e4074100c444401035032403c0070b80c0c050380d8100c0010000d220054010500601000e04844d00342020000702c0340d50f4200c5504401042c0d03e4980da0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 345537347 1250 345536097 345536099
    0x31a0a0f0203010302090c18100e01030506040c020a1212020a051902010c1e12050a0902090c040302060409110d090b0105040c0c080414011e08041406070914010e060c0a0309 76
    0xd25040b80001c0c080254440502d10200e6401803688000e00341080c5600041b01c0b0b22800c41c0300180320241982c0c003207404281c41d0040301c8110345c2c03d0720500d5444001039605010104c14207200030f445d05034130f00c1c00a00400c00103404540302480390300801c07178400b40c042c01195203824072840036200e600448080f40645599070b0b000d9400501c18040c12013840b036540c440d01c0c1050610148415002d000d00600c1007082030410948180c10f90f40c1c0920383c000c070009440082c11160500510420300340040c0b1220706020108030030401611040304550840f0416100024040c3d031070115003c4030311940740401903007820182003405100141103901d0482d4011503041000181109059130000c20300100035001d8002840104407140548241720f07071600d01450180048007821000c0d0324a0103000c040440010148400c100801002c0c041110110f99480002d008030300e017082d80144401907d0081520700c800504401031140d000d03000d40408100018189500c0c6c1e40740802c21a40c1e14825442540004c9070450 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 345538597 1250 345537347 345537371
    0x903040314010e060c0a030b03060f0406140403120b15030a0f0c0e241b0304090513051e0f0f0102090a09021201030308040309051c02010f08011508060604031a0a 71
    0x2040000703d0b840c0c600036112555030300c0151001034104000b59000e05494212031041d580d82441b50a03c120360340b016000e41d50525042c0841100c0000c0680d00d1850800c0c0240310200741c0200019010f244150004200e42501d0004298a00d02c1040c0f0840003280100a21280802540005c2030b500c40000c000c000c0000c0441c800c40d116401003d805800046243d5007246500c414410289080869000c442c540500301e4110228070200d483d044003642c00200c1c1c24060004c1d41d0003490f070000b8a00e40c44840b2071030103849041c1c8554042c00d074031010f84030101c5460804101071004a152560100c20b6582030402c00380b50034003075800103032030901c100303030b206d4010504000b94030984203d840e084203c19441c0e801e569003503c812002900940a101300d8520021302603032003c00000581080500c120303c586c619200141c540c1c40d40c13030702e01d00900c20980010312455140c0400c2c1003d120562a110703650341c982d03070041142e07442a500007401002c1c50b0a6550442e1450745042c42c0520b0010400b0003400c80d040c2e03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 345539847 1250 345538597 345538601
    0xe1e0103060c1101061404020d020f0301060f181d1003080a050c06060a08031c150f0e370b060309160b03010806010e04060b090a0501061704021c08070605090304031401 74
    0x101070403c150322201342c41c03881810262301810112210707140040c83d040901410200d550000d90051000408403450203080950040003c1d4088081500003503940e400d25801d00d402e4001101c1c81011001604002004044020141401960424000d503581c0310411002082c5600800e4180b40510540010030200e040082401081303460440285040014072030200d600341200c0c103401c0030b0280d2242e041d4151903859214520081207140780044100340340c40d07850207078824002c00302c03ea01004440d20040035030810107004254490701c0241e0f00340003803400c115002081c201d02d0300c17504801b010041202d0040000390031725000c500c003489490603d41e244102130ba84d110034002c2413600d8014030010000c0e10701c2c40301e01681162040d100801ca81c088140071485801003128408a1240c0722401000743c10341180340b002c3c02c1c1e10a036040c081c09180c20303004580d144104084200c98501c50410045c01d1001d43d0094410b9030303910150074421400c100103065901d030403502040d07030042150440e0b102024014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 345541097 1250 345539847 345539849
    0xa0b030a0512030723030f0919030503090a0b040b0f130305070210120f0b01080109140105060a031e050118050103050607080705040803041710020703090e1e0103060c110106 76
    0x1c040142a441151403200059030409803080003070201c02d820f42c07011406485075517103038020b61a01490b200d103060700310350114500250607441e00c0d0300400310409035a501ca5510b0980c55415082035641d07901c2d00c0205600e40344000002800c21942c180503c010440d50124990140c9403030b492003041070702c0304e100c8641015100b42000f0042441044060018100743c599004ca0598904004d43c0c84000a00180107640511420014055582042405940e08130391b202e409800301402c1081013241030711070207244d4039040c01228810030000c5401d00b0340910903000a49103107513603a48540115901e000440140100380a8840c0e8130030221032119044044ac030072241283c1d0850000e00705074840000075500d000020308460104002000041040c0c0c800300002c00040c4400960101070200d4032000c1c0d400c011780340d101e00070b07640e0040188801203a8440e2000d425248102c200c20360f941c603116040c54803143e0107180210305050721000003042c0901076105410000c060f403240410f46082d40381c02ca007200e0407 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 345542347 1250 345541097 345541103
    0x2121b0403060e0a0807300c031103130e0106030c05030f01090b12160302030f03130b0307110a0b01060e0f01021b060c16051504060516030302210a0b030a 68
    0x10500c020404160079030004104101c0d0801a100c2a0016456142e038561008606882c3d188035a128580690090011b4010689140e50000e04042040303a008000418840c0003900b000180c070184c0016010900c12102980c40d01c680250045a6407140e007405003000f489030b40d0119181c03814400e02c560151b02282d108200c404004c0c0c9140e8200320341e002c000d1859048060708100d454880c3c06130107100b0000070b8003551000340c1001c400c51452041600d00000103101d00c2e00c03908184030007030072034010b00f0010007903448440e01c681e101da444c9442107451441c130a0a01403075115a80c41c00c418084400103140c1600c40507507d000d5600100802e015040f000d041c2e016005030b1000085401012144904407085840201810b00d42140140100d1030020746c1c044600140285507420040740c64035444010300c1848803e031075401c003454184050014094000900e101c24200c494410400d4402d5044803519843c25420810841c060317940500300f41801c68034035a805207030041e84c020340e26000890b00710081d4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 345543597 1250 345542347 345542401
    0x61b0706050906041215050108030903010e010902031b150706060f091b030c030207050a050304050102011415130e030c0c010f020703050c1507121d0a0608070819020a030212 76
    0x460a00d07848416032880304103035581b91030318298800c4180305010f880e00900440c0d0085440b040c62100309400c4400c04441c1d816141c2c98082c0c0e020042c0c03404918164040409560703124094042404900030303c5840d00d0142c0342240010b0800f08020b02c43c0e0040060720b010600200041c1c0c0c42e090b072041122003808410b00d0340c40616889080b21031098120140348503c9240c05070421071640d94061501200240480e0035820100c0c0c10700c01c550f130910564810065000300d031102410022004403100514401e09401802c9043d40704484044541165101014a80072256100180316200b502d0700300a05d81140001d41080200702014800a100d406481c0c0140181200700450000c10502882a44020711107070018000000401c400000c242e1414503103840b209103150300c510103100303040315110f0103620407600b001040c002281c0c4a92182d601800504000f081c2c0c0d1551201031881e441c02482c040c0c1120300006015101c1541a000381551183c00b00c0928820389070301205403c0745190a0040761850 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 345544847 1250 345543597 345543599
    0x915030f06090c18220902090609160c030e090414120a0207050105130b070f030306080a030503010303031814032701021f1404080309150115031a061b070605090604 72
    0x805180c0990000c4000c107640c03400030700a40207161400703c0260120705e17295180205410341c02c00000b0554090f1044400d05068138180e241c52410080d95880703007080015000081c0c04042c0034400e149620a4010f10ba00820301c1d0628003010340d10400035070010580551381400c139459458101755000e02080f03402404a581c186401160301c0d8101140c514402031654500050043d65100209402030054100508582290070050103580180d40084a541d000804080203e07600c01c0030f49054a0307141c03802040d010300c014400840c804140b0005400308041d19090f06130b1860000090401d0340000410780c0a031801903068001150801c8803050158120070300c540d4070b07a41441c80c2c2861081241000051540d021403100f40c0d003410494040707803906800070600204010401c08200143c05400558407036604050b0b000c81800e0407000010709260700c03140c459500001d09440380d10740e42009000e41340c40d2446640381c903101d00c030055020301150003040c80c0401c04034440c070119503032003d0142a5034642 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 345546097 1250 345544847 345544867
    0xe07020c0411090d0c0b030702030a11070e0402040504020f090a0209040b2710031401290312090409210e030604080423100216080a030806150915030f06090c 69
    0x14130034524219129284000c02044002c003000145001d8820307a4002d40e210703682e0040103402440780c908500c03400e41c0500e508101c441c004014440e40140e0540e00800d040d1241e202040d2100640d441c0300350b00400c06010080720482d50b502404a1200803a41032124a95130400e0003805014146001034654004081d0748400d998031491542001c0c0c0200440c1c4031a5590f250241240c0d121400b002e03041e511035910300c002c04c295001030842142581030503002c84540400180d44c0300038202034031519a0b404200c002143e6510340c070407217480b50001840e00000c07003400d2040241021002c2004041907105140100c58140003c002c0e20850f4480c6c0c040d0f24090030400e420002c0c2500d9840031054280d2240ca80c089a207520f20b40b420311a2464004100100180000c60900b44c4190410b41182e0322031520000031a90054420f5044081601d8040300840c40131091f410074481c440803d900000031501280c1d82d038250400852142c2c9003102c02c3c80342500c480c02004885c0740c050320364803e00351003400390300c1d20 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 345547347 1250 345546097 345546109
    0xd02090606070c030321050106081311060406020a0c08010509030d1104051c0c2907051908030a0501060203041202010806010c0b0c040e0906060a0b0a05070602040e07020c041109 78
    0x4010300414039401c0c500b840c1e8841d8202040da4104400081c1c50320940311086003005848004505d010500340065030401c40c0080120500a00c10410405195203a80603c10410401800d00b1405041d15a85e20b8660f00003039540c0484200c01c0f65051559040003c880006114071030051740300c400603500c0e0200707184022b00a003007005001041681c041000182c00d0b80c0c0c000e04034200e80102c56005802007014113000c0f000542650002c484215800280b4110800c0c80b81e8851044100710401626080d65040c110703c3d108512001180c1c010034103e40800b4401014082c612541c0500000d029a13a21000226141d00a41c13065002c140b0020340c80350300542c05150160750094040c03401c1c8021245a0b203132035144a1040d21f0044840d90005010300150f401103515650000603600109030600704100401c0b00503265124083d20301c640420402400391042040303884854000c0c0044d911a07032541a0303003003403000556200b40544074220070400700e402e150080603404030075401010f003050124024408 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 345548597 1250 345547347 345547351
    0x102120907062f0709060602060609040b0105060d09050d0507051905070302010e0d0b0a0e01150315091e03020c09061815060c01050901021305011103030403050f07150e010c0504050d0209 82
    0x110f61000da40c9104404100f002d903000307000404020465134a4000060304147c4086c01260240c40d0300d80c1004082099aa10305c1d0454009540b56a03407240200b00c6036005180303411005080f4010003810140c0190711001404151f0301a0041e02c3c0504044081641d42c1681c41301c004050b90000c01e410409076000741e43c00489018040c02008130700c0f0043d52140b81d00c88044501c180c0455030b034888401028000d105150440300824141c4840c0307411038503410054903a14540f00c1e400d03a11140c0b600100401002c0207110700400444081c405041450082d49032700c40715041d03d00900100002904a2400c00c032842c80310031015200002c00d444039003850a240903a02c400c5600a9003c00402d15980000d20540b44107003c0b174000141c8490701640480384a4220754000c40c10400303480e62844d200796011003140d8102c0d074107040955030f0b5000d6884107030380b0b4000c6000103413030b2100501c20f141407508103400024010701d200000700b202c1483c408060b115402507020307032504403400c010b9560040c02e1402c441a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 345549847 1250 345548597 345548657
    0x1080705041d010c030911100e0f040608120304030f0311090d021c0c09060f0503100c0311070308070201050a020c0709020705011503080a03050705070228080609010212090706 77
    0xb880c80014500260070340d05240d840c500000d03610003860040c0724080380d5940c10484100c43c45030141500305001458000c0d480b17101841341a02c1103e90545036510b502910040180a003514159a041180210950000c030b1341507001c9020030784c1c25184a4030910511904048012030710b0b051421100902c89040e0183c80200c0c1c000e602c400c0c0b619802c0301e00503000c400c0346114440e900492400c0401c00c40550f6801d5000807840304481400340030590300403885070030520001800081c8180c141104802510400c1196006c13207a000a800003450361190401d8030488098000b40703d1070b12007048000c201e108a501840c0517400428090092900f107070001d00074980500e00116100401d003458040d05d150a034021209000c000440380380765505406003913031203521800c28a0030b01d281500400d20410f4401c2c2404001c020001d006480c0604a0b403440e40500001e0003200c1c00c600d00044800d0003903100c1800980c0c2d9001c01c10015050500008070300056810740d560300748043c05801d9580004058440ca05 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 345551097 1250 345549847 345549881
    0x5070303060806011e0506070b0402060c0c0a1701051501021c02120307020c01080708040b010b070212161e030203150705040312170604020c06041e140d090e0108070504 74
    0xb00d0b52020000340d8042c0001000c22108400190141c0341107944d282e0045000e62010301000300450741c0c104286a0040d01642c0c0d1590304d448042199090a45524096900c50b0f42c03008040303200b0340e03800c24500d2001c8045008018a840e12031000070505800001c250040c0d00032042070302d0781400102d14040d10030a0340111901503203a09940ca116401c00c0b0780d92001640304500c201000d46e4044002ea401c2036107418104510304203501d49503500c406c14094510f858000003503000c21521100d02840800004c2810f403802180c0d4400090507280b5144a1003c00e0840151070022520000280c0c10031241d008000b0310320f0a484040b040b01c00e0070003d000000303000c001c0c400040491100240b4000c80b140d03c2d5980c403591410345010101c0800003070460760180348140308681c40e15400040450b0080d40000c02010308000c00e1740150310449007280300900c400c5c3c0c61182c001140030001a0040c81212039100e2008864581504c0450300e8002d201d00d003c5644001420407150030300d42c3c050b060301c541032089 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 345552347 1250 345551097 345551099
    0x20a090f1205070b0a120929010e1501080f090a050a2405070c02040b0a120b090f28110603192a03050c0d0504120e19060507030306 58
    0xd4240800c2841d80720214200000d4985410080700340100d002501e0369051040c24a500c22500501c210503034032252040ca40d4649600301800004480d402c10350101211a130052031034403514407810802803003203081c074020310f07008203c0c00d00f09a41854908001a0740301481d031754400707030700f11090003015003501d030b06029214800d40484c0080c0818407815006030166520b0342081c040c0c96200710b004c100c8051381a440d1900380020140d00582e60300e0034640440b0085451662100014000c2d0700d140d0102070040d079008140c0c420056404111480340c01d034142500c00490300c5900d107a84441300002002000030342e014801c120051680700e0001c801c0c1c02200303d0b03001e144180300400c0e0b0607441501e00017000601c02d0700e1560000d60a0082c6160b40008500c00b030f1010702c2c1c500e05446540170039906101810340b0b410000310410b0900040c0e44040b09a00410301040c14141001440d40301800c52000001d0740b5662440a1410090481c06a001640d400c0d14100d40ca0f2000844164202800840030541c507044 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 345553597 1250 345552347 345552359
    0x60b090616060203091b010c02060d1508010216030e0301020304020105071b0b1308010515090106140c1b19120f111206100503010e190201050c03040308030406060801051504020a09 79
    0xc06144174500c282c2c02082c0d0450420842d5002c04040c2c40d510741003000302c1b03058100603180c04082d644010309940c1c0205043c0407464405051078441d40103101c042d071004c900d40c03004845c5c816410042034000d84880d403007a502c103001d0500b070b44401c40b0040d0118500300440700009a41182d0050706020300f000c5002003c1e00c40c214070300c240d4000c1d50031540208130b0610600c030414081c46055001001c10344181103c1400d40007041c070345007052240380180301c070b103000c407e005000c01e2080352032440b000000d0315084e90071556450768803c409000c1500030500d40700081c007031002e0a40701c2400d640240c1000103c13003642d569040314004201c041202c00c888a01001d06e481d4607a4444001c103020a000a4a1945001080c0c00c80c1e90100e03030b014070b02c05da040c0940b00d0200f81c2d0200f51300c800c6190513000300402100c01c3c0016500d5100e103c0c88900d443c400040c000061010b02d20140d4000d62140509003c960f54501070942610b60039250903041c00a004010200e900d41507000f48240000b41c00e10400081d511a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 345554847 1250 345553597 345553601
    0x408071e030506010b04050a0602150609070e0a08031914090922050c030f240702070f03060c08100e15122a0306101e090507120e01060b09061606 64
    0xe88a20324a0801046c140118a000312804001e0222440240000c166000c42c0c00d070781c441c010300100d005042800c04200740f548503107020f071541040542082d4400c1d90312103031550349500c0210700b074440c3c4130951012881584240848420f40081c0c2800904103074034401000600c800107030501c02d80c200b080b0007100c2e400900d04400c0d8465405000034121166540062500b0f0981055602c04590840102104c0200160720340b0100c94072055415040c3d5a03551505900d02074890b0009003c021940c50000100302081e00001000e480315920342c203281e02d5104008605125a000301002e130ba000000003814440700e00d0300715551260043c815001400752606160822002c5901120392180070040c0c040d41004c10444034a00800540007805585400c0e002030000e0310241c08cc81500314042c140007a1030018ac0c1844002825000f2020400307820b0940000d08076903000c00002401c0b03800c0c03100b4503002c41d4043c81020304403464425500c0c0b9050071001080800e50007540d00a882450101c010790100744c0074 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 345556097 1250 345554847 345554849
    0xc0b07020709050103240204061704020402041a0315010503040b04030f0309021207030b01120b010b031816080c0306090705100516260c0709050a0b091f0602030408071e03050601 78
    0x140e80101e000700e80b020000c0c40c1c6c0144544040807000e00401040125552098841100c2e620354000400d04d42c4513880010003a105d20342c04a2010b000d00b411b075045800c103890085001e2f0280315008221081c000e0015646400100e50240a0f01c2c0c40200007070109008a213112800c52041c80d001680074042c1d40000c0d16911800b000c0145035015100500410006124080c098001d613905015901001e60b40c51000d003505004070621008040041b42c0c1e8004c41c0f55108021040840c180c03940c0842d171610741508181c0e03a120b20303082ea00c600010188a0700b00412810301840c070b41005000c40c2d90400c3c0a2004031540d000f2440c081000803c042001900c80929055445100b2080f0bc1070141041c8484c4152241107490101413103420070401c00112000a41e180c0ac440410b83c01248643e600b01c2420020401c969011b03800000d480b0401000690084100e01c1000040034003a124a4850394100d0b500c0c055030040c41016403010308240300f8403e90606c2e0321300c240c0040c8021010309807170380c0c0e03800e00742102 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 345557347 1250 345556097 345556103
    0x815010507062c0c0f13020c0712110a05040902030715020a0503030a1401240309020a030203060f01030204051806063010141608150607050c030d0f0c0b07020709050103 74
    0x29400f1981c4180c10f012401c0300312003c80720000c0d820300040010341104443c1d403000040b140d00140e080300e2060103000c2c0b6001484040b0019644d1080e80c2081820040c00e5190035109a03404a4042290718107849034003216900580108550b81c2440c403101404003d03000c1900941c414a580d140000314100000d610480811801080b203001400b081c4003480c0043e0060300345004a82407900301c1783c40c950f83c40b00e81d600700c5240105104031030340042103100c8030a41000c1d405005580c00c018405a010b14528100c910175507003046965501c4050312111540b408a102c92500081d01041c502d2800c00300001c2078200002014007205840c070000015045c1c04d13401c800301a004015036003203048252242c900e186d21303840e0042c00141303450483d1001090150394510f042c404400041159000b091141c0c50762480b02810705541d4036180e0030304582e24120785010300e10a03c40c0e40c0115605600c214907080300350505850701ea244407400d998a4450280003003844007140700c0c0b6000055400a54024a4000c41c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 345558597 1250 345557347 345557411
    0x17060f04020d06050f0102071a090d080409020306130e0307020f12030a021f15090f060b0a03201e0304050c0307171624030905030307030204050a06081501050706 71
    0x1c0313040706008009882c40201c07419504000800c0080c44034000800002413540b5084a43d200d0340700d400140c0c0e040e4400c0014085039000300340800d45c0700c02c0d035004600034171007280c030100550903540608062300d4200d080320805410a003d00c00050034400102d9800040041c90558041000780b0603c0c07840d0403554001e0016440a82000700a41512406046003115002e0602822081183c88001070b4010300c00d5110080da01c0c2d402004c24052507000b0800b400800182c199141000324000380a00050b0951000710090103162110400c00c1314215441e0b8105551400784100284031019800d400c014420f452600400c0c1000780700e42e4052011902a2400a410100405141d85410700e000c0b00c400d1640010100c80300d040c0030325400e80000d850405407243c00404c400321004812000307000d603030174020710500c008814000b180d41c154001c0c0050b0341050303400d1559140d03140001c4075600c2090f10200c101c607100e101c0d0011207511420007401c40500948002c14000c204c900402d010000c0103420202000f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 345559847 1250 345558597 345558599
    0x6070b0f07080901020901081501020a06050c090312090a290307030c08090d020c1002160e0106030b03030708030c0d0e0307060902010315350607051804060617060f04020d06 76
    0x2e030002480c58009003094021801d0200303c00c000307005c40c0409800125079500c0c0341e486040340e0f8030030081031004d180d00903818010340c2804481d014103030700000700083c40b0340102071801491078818001d40b0783e40c04000301084017142c605010004c0c0f83c00d6401c4450f0010f07041041c821407040281004600907541d03560005892101048018000c0740041c0c0040d1080d005540d10001c40d690010302901d441d4001c071016040c440b4030300c0e82a4500300503980380310103401440344006035005074403841a04031100b40e2028800001120101500c0340b04082c0300610246083c00816114000c900c003620251260000008580001c08246450758200100c01c6421a4456900300e046503414050003074035000400b07202030b84a040c0b01390880d4008610910240340d00f5581c0d8072415412902d1103581c1d129003148181c42c40f600300704a00800541c000d54101001030000c52a901c0103040520a40040700c003540c1d20f00b00d044032504008492304001501c107503031090181c1c0702044180c0d584d1005080b6080c440c0d01c00201c003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 345561097 1250 345559847 345559861
    0x2190215090406050a060e4e01060608060a06030603030f23030108030a14040b0a110312011206050f13030309030c0501051e09011103040209040c08060112060b0a05060a05070206070b0f 81
    0x40034040703034232042d07200c5882060320f6904c014088110000500c140c808101e00c800808840f10301000c03200703690035507092480009141d5089500076001d140292355080c84240c680d00c1c15400d4544d0342c8001400102c13100c643c4400c00f48a141080e40ba00c0b881c54221f00e20750051a5004001d81007138000c103c00780c0000843c011a29000405991902c1d01d02551908041c540100b81c0c91501800c0000c00520400e42e0490301018820710448075030b038080c48079103a039a5031194400d40e000038420104645603481c00011407450003c01504510418010816481304580c42d81d08030050a101c050072018807101ea001a80021000c1c09420701c25021030814030054295260300110000f0054040c80d6640d240030ba4000000034800c08032540907406031280055521145001c81303040b5115400b5829501440b030011420168040780b40850a0280e40f044c4407140d038500070131078800007a00c51154070010401c8400313103072402403001c2c25100d40020841420700b007035030b12034803c2903604035059034441540400300405 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 345562347 1250 345561097 345561109
    0x6060519020d050f160f03210603110f04020c07061d1503010302010302090307120b06040f050f0105041505040f0c080708011a07022b020102190215090406050a060e 72
    0x85900369200401805021110291080c4202c25850076100320000b01501000300b00c0007290400d540c000120004d21003d410000d00c51524500000b0100003002c0c28005024824001e0343d007940c0d04a405c640625141c00c04000c0903d28440700690019001d04c4410030341042400804000c2217140c1354581c507640708080343c07400c034282080514400c0a0b882c07421410810403c0c141ca0550740c0c203080043e52410443c0019107000e1082d44024500c10107078914400f04201d0f04400c80c0500002c2e00d0034407c04d9150308880b41034520446901a1803590100104664603194114069000c1070440d5030030551307141c0c40400c0c251040440701460158540360000c052139407142a07a903002100e0b240100041d4100004c0050200110725a0300661101042081c2550759a07114803801c0c69044d80c0094044155224420a030848800c040c0e02600801d080c0c0468100404c04003481240d00414070075031020803041d803e14070303045401e00680050ba100004101d5407600b0314040d01030078964842000c00c07413504042282c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 345563597 1250 345562347 345562387
    0xc0b0a03240303230f070204110d0605090105040225030e0d080304140105070519020313120606050105031b0d0b030607180510050f0307030b0a09060e0a0203072a0501060605 76
    0x803060021340e0310f80003140f6500a444024202d00b088550b2590240005000341641018005ca000b01c0014040840c48040e4015412a8070036215440786a0761b41d81004224010b51034001043e48024244000341c1c1c08405403054024400e040c5030b1a403400c0a80800c4100e14507440469800c40004284030602110460b00041c2d5010715000b8410f52074550030042c80c9000d4a03c45040c41c80b54003600c1041c26000340150b510302d2122002018020340d88280c50a0b000c290b000007a200300d4504400410175500c617204030f80c8582c3e2580041c4558040811004943e6444840a00b0402c0d548035000d04c00c5e80d0303041c004d541c01071039148e6543c0e400d0124042074040c2c2411a40c05144074000e2118010390a50700002994541c1a43c0c19100b600c135658038900743c7c050440040c4240d030050132910007003180500d40d4405000c1d14100d0002c07044070394440450f2800c03444142d0711980030810a160101707000a0008075501504221200247c15100c01d035201d030300b555001d8100c9404602c0c0800d0141c101c00ca4600f40d40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 345564847 1250 345563597 345563627
    0xe030f0a02060916150504180207020103150302030601380a020717060f0a02220915050a0302060901020708010f020406030b030a02130507030603050f0102130509040c0b0a03240303 79
    0x11410003040700c03018184130054818003008810000700d260a0600403820b8500401420352039150105103507001a009611a100803408130789421003620500c52180700c550141c0754003030014460f45c0d00308007003540301d9502121490107030421000d1040c00101d045503030780d04d4101c481e00c0300c64a030b8080503400b83c103151145d046651b0901c2741704081500e1603000541d10350080c0e0244400d40d0703251290440240a445001c403592219401100d035185800710b41c0000d5070866030800004c11008024002c0101241c2c150312810b640034150090620140c0b0b4941d009025191050045644e50303641c42d0010303400c2d02e060001010b4419030103d000c00c40e039501400342204c000740890107000243c11640c009221075107500c030040074070b690350000100d0315070082c3d101401850b003220446000300e01e059502c0b4081d6010001940d15411080c000048078113000d05858000c07540304001e40e601500380ba5058405422000101741059180d0300e506607649048004500e4a03d0b8611007605000e007107080107400408540713806 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 345566097 1250 345564847 345564853
    0x11091b0708030402010c06091218050a03060b0301060e0406020c100209180a1d06100501030501060c0f0501020d1d0c0f0a0302191502030301170a1e03030e030f0a020609 74
    0x90414901240466485951000000342c4036151400101c03016102a1401010f039071802217080e051046141e03054080d550b03c0d550315110003524821341c112429092080c6508a00040350910025501d9042240d00c50009000000e200d075540040c60b80c00c0000340d42c107544a0b035001512280c040740500c100c1503c080103980c01e528103410240130401390380c810b40d24440d01000d9080490a513600036003000d405110607a0865552040c1000d02030f4a603942550000c07400c0031408400138443d4000d0140303a0403100103856084195a40d034172840d0108508043c100c440e5542007040c07064404039449400c154190318244900440c080b910618a071904c1031006d00e200d10403080c03003210944d0310a2600c10580c0d5050b13a20041e080d00d4a40f0b140c000c1c607544c1e0411004c0400d0040b500c403003158004041c41c100d40c10b012030080d1a0940700c1d0600d807039941c840000b4201d00e010808030b072204448188100c568501c20b10340061a905103500d42811600301d81100d04003490009480c18009a04100c52a0001402806 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 345567347 1250 345566097 345566131
    0x18050d020105061806030c0603072c030607111204141c0b22060c030e0601060c05030a050901020c04061502011103220f0c06021e01150b090f0d1109 65
    0x2c113180104001d01c41c00c0107004001448644051155190010016203a00e483e4101030301d000c0d210300e00ca02901d80e03405200d8090b482c84035071004800701c2d80003006000b07001252034011088500f0200115512900d00c5500060500200b00d10001d00c01000d81d01001d5011028010070030000041c0c464110003130110500365400400c0182c000b058000c01c0621a100350b1406030200a00c1c04001644060081403800512080032601504460400400c0318103841c42a82c86160039688030040c4130025100b68010312044c00000d000320300030712604105004582001a282001500341e58254000340f024840700680681c80344e8090250412031414200da0340c0c00d610b04820801c05808540445101070708030382004500340648880c900f801740350802038000074140c035010065900d030221b600c442990001da40810b50103400601c9004c107261210485180ba4a142070341c91446500304411840d44142200f961031030380da072441040360144c1c1c0316040c803400c035210200400654a80040614030308000c0c0c1c0236 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 345568597 1250 345567347 345567349
    0x1c120908030324010905061c05090a080304060c030b061b010f0b0619051303050d020d031e241d090c0108041502040b0c030309060a06050f0d05010e0118050d02010506 73
    0x500040b0000690304280c4240c0324040102e07404202c46c0c0c842a0861000210ba480c140c0c490000040392641c61801400030762030fa035040f290780d100d41e000c028041400500c013240010f03115800500340c06d521481c0215056038440000b40d41c682c00300e10000071503130310500c1e1009075400070b004907010150350100401a1038940c202140326481910507007009030003001840c5000d84e006200341c800760400101502d065039281c7c5403c55940176000524000b51041105011445200e406032500d1110341144004240c5401d14a03240581401c910f1001c818819004c1184140d602c400000024010880d08007840d84031040d040100080190003c801508900d00111260b41c00c859a203400c6a40300a0150210168124580007405140c001c00c03a0550b0000b044080c10304000090741c000c20200e0296046034031000c02450854401e446200d8100400207c602001c1c50f01410040402d0300400001c00c80d20f9580c51114210f51120762025682c9501004140c20300404100c02e442c0b224503400204011300b000301c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 345569847 1250 345568597 345568621
    0x15010b040509040825060e060c070b060a0810020901031406062b020a080103030e010c0b0a0b040207050a0308090601080721020f0907050405040b0f06040b03061c1209080303 76
    0xc01090700400b05807010a003045100400c403103c00c6410f0420703201040941911a18610691106646c0103080068110b11403801040c0c403401560205e80c02da00e0503910390399000100400800e1241c0c0807200c0324001036081d4041c0200c0101040b900d200507910750070b4100140407500041201641e00310704004000395030310b81800301c07800424107030220003e560411803100c21352007440700c9000e120b038000b0494284103500000c565040c0d0b8401e0301c5e190280c0e81da42d8011181c2c4540f402c00940782d000c1110102d01003084940c000311402c000a4400b510b0804123451b141d24080e403485084000031013205c00c000c88900244035680c050300c0508040c104030752900044020000d0030b1101110010b181d0f460400c01c5548444a42d601e5400113003a403122803810000180260b0001d200b2180690b09182150005280203540c1480d06007008000c1c9060909290200d843e03500000d00c0b40e50007003d2110524420041a010a035440b44140400c0e40080184800201021440d03401069107600034014003030001100c0b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 345571097 1250 345569847 345569849
    0x11104090608061302191a0315030109110f04060504150e060916180e25030c050304080a0314040c0942091d0d0804020d080904020d0c050c15010b04 65
    0x1240d52a821164001c01185400040e61007d4110420851244001e14100c40698490058444820103070203d50040c1402c2ea10780c2c50004100c0302818441169514040310403069598000c1d01c005a0b03280c0b10008601241c90003040a003d1a10040742009240490700784140e202c6000c0c1e82007256030901a655412503a642000101409150110644c1a041e803040090007491400419040c41c180104407030f07200403140764900500383c5140b40c0114214041d01502c0c044001940d1051710b1503465484030100c0f500003a6101040546411a200310b00341e031048128052409100d506194525020b81c01d4111020202c0c0079101e54441521143c0f482d0084c650b41035400d00703562201b20425480310341c0c41c030200e000d80c0040141e1450711128048011014950b1813100c00721504458144003a004150707040502140c00039840302d498102e4400052024020f0100800c0181c0003600f00080c1505c128103490800c80d01c0c200242003c1248440e00d0b40400c84a89004c08cc51004481541043c841c120300f4411 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 345572347 1250 345571097 345571099
    0x901120201050702060f090114040501200703050a0803090105010f0b0f071103100c020c0a320409110910050306061c0605010803041a030f04060c0e03011104090608061302 75
    0x644044015a40190225078219500403c041d940e100303048108100e0f6000950320600180d424414190180443c2080390107407403050316806000c1c0c149440b0340001c8000200f45039118014140300000081c410041d04c0b0b08180320315203494070303450941e45481c00c61300168004603514403490307820000440c507441103490b501040c90510342e44400d02d00381280d00300c2c2034a03507260b0944074001803444005095884034a030b4503d19400d45000c0c4a5880401c0380704c0c4072600030300b1000c04500402505d0340d0011840d01c0e440c08841203071a82c582d5401400502205c105000c1640c480c501329600700301920b001010750f640003c04000500b240c50030000800d41e02c080c018403c0c2e01550710709858558203c54030800c43d240b26032210040c4110360f1030300b9082e501d030380080c49800020740040c00388260311410b1030240e074403595400b0400c078000d035201d885a001504060b0301c5401030180c0303200300b210aa202800b9031001d480c2c8041020356220701d4602c46004840346a4020002a0030450078001c0d042006554214200d0b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 345573597 1250 345572347 345572369
    0x6010305150118020d1806020a02120f0a08090a120519020d080f10030212010f05060603010e04020105070204110313030e060a080c030912040303020a05190305030420040e0a0605070309020901 84
    0x1240701040c40007020764518044106c10b00803080c004202c844e030000c0079135000940c20365401c00d0745140305401a014100f01c03900c0c050000c1c880140041e01c0b4076a500c4c0d00c10034440c221902c40020b034554417400c0310501e14420001d140021840c03516001c19050711090707003480c8010000000303a10b20003031009070003800c00049982444041351220410360080c80c003854000300b00e0503864241220443c000c2400385801c9241a00f8540080c49614000055034100d90800a060704242e68a9004441c66800740c4400c9a01940d1410031000f04110750700a180300d400202103502c00945141000341200000c40c0d920751080b03100f040900c2c01c2c15401005c1a800807089244581c0b241c885c3c2a44ca810914042c400a44150010500009140d4005140b07070026000d82c00f69a90818a244040b500c0d01d08a100500460350402c0400d0014104400b80c07140440c891550801c03110b00c0340c000906940f00c095a11a0703990280132003805110441c400e150300040a42004c0001c10040d60104100e40070511130401c01e08 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 345574847 1250 345573597 345573607
    0xf260f0703181e090605150a030c0c06050a3912270605010503010c170601020a0c06090512030a09060c0f0204180519030225050a03050601030515011802 67
    0x410076000e800740070b03c03100140390201c0150714801d00c005248500d0450904200d0001010709010001112200c0b00103d5103150010032103080c0c4c060b1041f15032900400c0031010804000c50510b02c1841d008811043c000b0940c011078080010f141c101400401141c180040f0f600a0f010900203c2d0040314251420400c132041d21000e4030320000c0c0041c2c204094190484858103015581d20b40080001310b2040f40200503503600c40c0c041c98202c03882400c6403400304140341270001da03140011a0603076200c00b05204079040e02e045aa01c5040380d01c11030f88003a0100302070341030a000c01d2070800c540e00d001240c6c1c0802941050b240d03c80007842500d25124080600045c285103405003d601041049120b03009001480341c01d100c0003c51104685004c016030302c6000340c45d81200c4814090401454254255001b42078802c0a4144140e0300a0b00e4101c010780a802c400c0c000419407644501c070030055010f4805403146601d141000b9040c4142c241c402500c28458a00501c6094800d04049a5882412900603207031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 345576097 1250 345574847 345574877
    0xa050409080c030c06010513061401050f09150a0314040f0809130e031309020903060a02090a17010218120d0309060212160e04021c050901090f260f0703 67
    0x2502c035909819560b4000010643d2142c01c0c00103065049480607070344031124100e03802402040392194020080d9001c80b60803021025032160b4003a190a0000c05002e6240503050030004031001d01e01c450781000e451380071414440c3d107a014420115050104000f4481d186829683c1110081203103000500c1d416000c503d21750079031500e2400303d0050010300780402c00b820000040316541e4000f404c80c2c8140c003030144401f05502c5228002d41c0d000c20000b030002c01d41c3e80c8a034035890f0b01a4009451241c1c10910001c400101d994141c41003d5208404100040c1d95608800000c000d4004106030310f80120501c416014142d00d0000d0b18a50360919840d002130305540034a402d402034424242c4082d200d1030804140810204209521403041c40d443e02c0340c845908130030003404142e0003680514000200c036111000f140c0c0e40303942c100c6035210041d00000100c030185aa1604c406104500e801d03100140e1240404246103074400c4101c2c800c3c1034003041d0904201c2d5403480d084282c1300b40b200c010100b0046007070001ca9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 345577347 1250 345576097 345576113
    0x10c0903050a082101061e050a081302030c03030d05100b040501090918020a03030f03050f07023301030f060b041e0e01140109020706051803041e031b08060708060a050409 75
    0x340104d003030303401080d69221002068032400d034040c204d102d50061000c407903041c011000c4030802c0380700e51103100f882e03510a43c03840607540c009072050b41c241c01400c05140803a1f0b010700c014220001c1254000804d0b00300518451010075031904000d8030a10100401d00050b078000c450041112414600401c1e20440c20340e09420500142c24001d40159101001004260300a200384044040360f0b03a04105658402002301e80a800594210000d41c00c070300d0240c98180c460842503114054192031103801000c914291841d551000d034410b076a070340c200e020410208030700d500584400e544c08881c00d200f07100340084812440e41440c411032401e942e40d00d4200d11425001c0d0491600048400c042002541e501e103000c0019601c220002c8400070724050004800186040b8070114105400c00154107050511b680d4400481c5015a0f0496040c1307803a07030000004558110024078554610b40500c42c10b1310384031249240c414080d1042081c0032001c4100025a183d85200c0c0048410807100071031500e01034241110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 345578597 1250 345577347 345577387
    0x9020303070822090606110601060f050d02130801060807090b0604090b030109061a0f0d0f02101103030907091a0d170c031303030f0503101509051903020102010c0903050a08 76
    0x144241c07843c500000d04c0340a03513104400b1680070b030b00d904a050b504420b080342c41e45000d02400e000f02e01004190450346110390050075500804040062422480e00c814071a5421540d10610460391111424010588144000313001018207513020b0016210785c06c0014080d018500980b1035445e9680301c90010b95071300350020429280c00c41e80c2001a060410304d2205c02100400d05a4010b980c004804ca80504111200400d245c0e04078036140900c0c1042e508212145180661110400c009421801c510310301c00e0000b14003401449001303000040c0b80c0006001640c102006682d0480320f0010002d8203030f140d0801e22031041d6408550f14002007821081180540a1209070400354840424403542c03107404180010306803402503c410005560a00e0200c07000e00c0100c545e0002c1c03a002120421241281c80030840d000794070790410001c03498582300825608404981e003203003007025003e030070415540c0a1041307a802803401d107403100760b16046031100c07540c45001050040000700c0014416180810780e64001c8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 345579847 1250 345578597 345578647
    0xa0602030705060604050a06091803110703020f10030e070605090901090c0503070315150e03070b03040f0b090c06030703020d050a050c270a12060e0604022b020307080709060504090203030708 84
    0x4800c45000e22b5011001e0003a03401180440d02c00b922115284800042490449a0041000705c0708407c00702401032021100c4e140c0c40c281600d6652080c1d81410900000014001940c0d4554654a410042040310301040e4440710001d0b02d480301d60389080c4d5000c021a54041514100402e00c1e00d030740b0440311a8600a64440e0300614848910268000d40c401c4a50440c413004030300300c0320155203c08483c40c5501c41602c1c01010300b0303040d131f124030006402c0c04411039010074031406481d20b58181c1c00c0441d070b080c4d10444944001030760010f00368420018a2040c143c208000030801c101c1d614118104611038820440c5400e852403101240e80e216810407643c8001504015000f11000ca640300c5050000302c0c03000700704981490900d030000134064000142103100355001085c120b8041d4500c2805104149003020300c10194502a00e0381700541ca041281d0300007040f615005241152400c0d03060300444285030821440baa081000e1000980d900000b0360300d02d26000a841c503924a5003801c4c080074603049410003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 345581097 1250 345579847 345579851
    0xa03021909060b0901090e01150c06060506072d12050f090a03030302040806150105031b190807030b090426070f032115142d0a0602030705060604050a0609 68
    0x40f071186900400762018000070b894189100780c4400824074694000d001c1e20f885040740002902400e44200f56013031031580519000220035807204007203004d80c0e00050055451040f940c0c03404402e614801d0086280019041507810000300c40d989036403240140302803030340c00c100000c075410b0784580d810360481d03000c400010320701d1240b165039180c00780c003a4100b4407441c8858000c110005d0389030559005100f5603030005030340c0c0074510350b5403103501191021a203c2040400c2014050701f140b8003a180c51402c0840001e469590f1246480d00c4001c040d40c00c00c0030075a020b001d0000600002490007a003865058180f0000c0340641c1880850114485c021001c1c040c00416511483d04181504a064881c4410008038000f03400607041d4550300a0340c0c0c0300301d541110700d21b841800300300b40c1c5042000c10342c0411009180840b40c50889107680000e80e40205c010f000c0e14000d14030300d0400e140645800f0014903650000d5401d01086484860f122079000700b0b4213000d01c6e183c000081201000b60b0050f4040d140d40700003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 345582347 1250 345581097 345581099
    0xc0e120f01090c05042a0f0c02030102030a050f070903150e010b190e070503040302030a030509031614011416180b0a0f0e01030e19080c030304050f010c0e0a0302190906 74
    0x9a8410001d22410380168075241001142c2da400283c00640a41134115000000c44100c404444d1207541e4041c450400c201b00c2510700c01032b502800150f002d103102c01e00220742810050014051044007610741001d00c281e19004000003103247c1d440040500030070100040b8030080180481c05000140d0b10603900411444010101c1c903080c40414007a600600d180441943da200420b440920040e200680036901c140118804c4034440c5d00b00e03c0d4071071800019217050108196a41d88508a516402c550544024a8401c00e09800f4442c1804a0360780804d4480c450801018026032240710380c3d10441042104024220314007400d88824004250b0f4030360f041d90352404200c0c01003894142000c80b900141483c0d01c10f049a41c400d020381084c0750380d10400f0786544951081c1c04048600100c0c2c08613014038040c030840c40070500602c0a5881207004802a0180c1d6001c219110308554201d02820244820300c0000f4002c1e44801c007809003940e0381611224181da48160345d03002085450380c889071110381003680c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 345583597 1250 345582347 345582353
    0x90604060b04271a061308060702010e0f01090804030224070605040b1302010503010603150312081e010e060904030e0306150316030803060d030507170304030e040c0e120f0109 77
    0xc09641610512a100540c580320445640a4410502c0800c1840001404a08140c0785c504020808035020550340d900c41030b0b448440c0790800d0310840b04940542d44d507400c00c1444890600403012085c50680003001008032960f1071944a00503404064003c0801a000d9070600c0c20400144810250300e0300120f444100519080c8003a01048070b084070180941d2000c90039850031500c0c1d00040960523100d5a0031682400e400320300605000034525440e146901000001c11900f44284100c6043c03550389c6a00c0c0d00d020054804082027958002d00035504900041080030541140e05401a90454400d00c0540302c9040c1200c8010b0320b00b86603036060240400b445000007541c0303400400d01405405444512103640c81c404210000c2d44406441c040c41080016103e10b4405200c0074864401d08025042c0b50b03440d20f90369580e0f50284201a498040001407000781604201e10584469080b1018001c4045404d801440703500403209442c01400c1002000301e210700140250b082c20382d0103030020000703040141 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 345584847 1250 345583597 345583619
    0x92003150a0902070f0602210103061a1504231207030512070201090920030c090a120f060b010e03030f03041e0b010605090a030c06020f010c0e0f090604060b04 70
    0x603040d644540c0d040940050105650b009458200c1d411100d66a1170315215100c07030019500100410002064800000b110f082566040030302030760149100088104400001c112a000c0104020744200d80b20300840030440d11a070202ca0030369000500b0103031895514414034250200b408045503001c00c40c100b081030501380004012040303d01032401c0b588031456000c2c02d0703032040c41001c0c00a400a03500c0c400910566002c1c0c2c100164050306104030750540d58035580ba0f143c05810070340381c8408560002406840f103251540030400a446032660124984609640d0080030802d0502c0082840340c640c0340c3d00842d0780c081c0c00c00340c507101c8001e802e890792008944000300c1c0561044a0498030264880300041080f202041510301c0d40d030703003c244c1c81d9450b403d2482c252181e411610138194020300f507040100004445002007002444560010106d0b607114150650030b43e010809050300700074544400c49855031700c1c4c00c8440072022040d500800e8030317100c035004603003c1e2450f0b8103c1300300010001800281003c3c60 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 345586097 1250 345584847 345584881
    0xc2809020c0d02010f0203010612020c030912030301031101080705070b0601021609230f041e0204021b06130506010909030309080703181d0609090327010909060e01092003 75
    0x2c1e078000c00c2500b80602603001280002c0c0522000100c03240490276042685a000b4500c0c24484407c490402c103000c8000b6501c10301100070740130326030000f0004108010100038446008a030908090b0203a15000f00c005005000307107000540008292000700c0d8199009010b400c00050650403510540344c0c03103422400181654a588480422450141e41000102e00c03c9817406007501c071005144c1d80d01c03191140d800828109280305000c1d0440744496006940e5440208049490412803500c030b10000031f000c50504400038002030307490014074900000070f400460710606588086a0018181485080880061811403c028031400c8002260002e054000c1028103800c7c2040c0221255070b9254101480d21015004180460400030400700f81c0398500304941036072101c03505c411a801c0c01c0c030610714880c1c09220026803031790101c1101c551118959210503035002608820038148803141c60000d111071031600500c24003150783c0c0e0b69401290399941a41104010040f01c150442d1a4200b95503d0b034601c201e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 345587347 1250 345586097 345586123
    0xe0303070c1e051c020105090c090615031302100528020a0f05060f1806010e0a020712391502130e09010c0c030f0c150603060e0d020c2809020c 63
    0x1302501c0401824414010780740b1400800000c3c2100c1c01d10312050101050b806007a0320342c4802021a001d91095140010714811071400250f183c492445006201000240408090800808010085901180f00c03444403541c800c80700c11040f0800c1030300c2c0c05c07401e00d0000c020003450040c0c840800300600c900080c01174001c0040c03001e4002240c80d800c01c41c0c401c170214a43e0b02d1541d03070004001044980040038060754003050500c000b510b022f0580d41c4800b0380c0121004d00e040802d0707079030108844590407030124100c0d0454540030b94200343d4464010640640320030320f00174001d0920350800048640d840d0103841174884240c001500e0561569541c4502c01e1003140c00203500e6207400d590140c00d51044003550003a81d01629060022140301030202d503114400c2c841640c0c00d10010911444400ba1441424000d50051400191200203154880d061160f80c12002d401c6600120109406589030240c1204850030f0241188452a0a0200c4c10072801103910004c03000d80b003c1050300c1c8051004c9003c02c40c60381 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 345588597 1250 345587347 345587383
    0x120706090b0117060c180a03030c030e040509070b03060f030a0f03080f010605090d0203250303030b030d0f050c0f07031421040b0c0111160c090e0303070c1e05 70
    0x70b2a040f20300b141d00c840c0b288807440340e4040400702d0510020040202001e1700d40c514440d0300050400085000c081099008500150b400103000040c55403105000c0c0350030508803414001800c101c84482d07903903200d6000e0404034882c0000441d00b2075803404105440030001600f961000050b40c03e15405540c00c90800f50003041741400052103441e00780007403030306076106502d03a14186011a402c0c03000782c0380703001c004a8051080c100d10b0340d0403411000c0c00b480d80d218041d141c90009400e601e0020700f6038040c12615802a40310303008034048542c111180c04003c50700361409a03121951103154501d01302c1100e4611155000d43c0d8000703c24170101804600700700c2000c100300d03104a600182d01c0c403c1d1602210740c021410b00c00340018440750802c0d00043c0590b8200000210384410f016902d0b500035846281c44207103c18400703205100f0800028402c2c0000c141401c0d04000c1c80e503540810640b20720009240d0310410a420700020300b00501c0d00c2001504e840003003030041c000242403910960304c0080b0404250184 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 345589847 1250 345588597 345588599
    0x423040f09031403100e04110d0b0603070f08060a090f0605040812071e050307030207060203010b07171327020a080711010911040504080c0a150506010827120706090b01 74
    0x3070f99810480c1c0c002c0f0307088031200101c2844d100300b001d035000d400b030b101f1650660b00071340c0e07050140c1d5115a0940500d002c3e041c02c85032824200304240c540041c5d540503902d40115100304000701e40000c901f55902003c00c80000c224500c03185440e0b0700300d6180082c014400e40c43c10301400144001030001d03158104a9030201121500e4400301525145507500140100e14216040e050f4001d1052003e581c12103003034200035040000c103545220a0760426003149003140b40100703000c41070002500340b05400b489035481952400c0b2282c840048826640d000b41c6d2030401c1701c2821325015443e014619124104444021904c50003c070b00d00626149068808200060340303203080802010f010310515042035844842e0001241701d640501022300300c02481507481c50405c0c004002055424000004e0b1144544a402c500c0203200c4003a404490b07016110720b040111550402103100007882c1040070303080d21004c0c80c020401e81501c26a190030201545060003443c081a40f00030895290082d4070441d210303540810717041e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 345591097 1250 345589847 345589877
    0x10b060414090c04080c040e0f30040e01060c02061207020303070806030d020c04050c040905070903030809060f01060507171c1103070e060c070b0703091502060c0423040f0903 77
    0x16004e5405808000e4014a038260501c0c94141d1240d61500f030a0320907900076200d8841034604004818080030000040801d4901400f60440340c5a4413880000210303900b0142044410040c2d040b050041505100b0818182025542c0d18400e80e07248100400c0c6481551074286c60082d241d070815584500030403004c0c004110b1a01d00840c00031180c00c0d6a900420701c51480900f0800034110290149480c84410400031564815500505204240a440301d0380814510302d030042c024540181000c910340c02c0403003400740600b2141e00e85811a0b083d031030a01d072507140342d04001910215041c034100e44440000707000341400d25207490314039400c44800e004004000d10110309005034401100c04000285000d51018518603280f8080d00c034a40b03c120446000036119421a0b10a41c001c42050700400c854440c2004540da1142216405490520141960341003050b0050340d00d018500551009201004581c01c000c1040c03080c0940d00c00008105219548000c030444000f000a1003054000030391000844c182 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 345592347 1250 345591097 345591121
    0x81e0c0606010c0215130f03050304031506061d2d01020c030c03030a031104230a05101403072708160e01090902040b040e0f06100f03060b03010b06041409 68
    0x1850300030f0140c502105078405d100400c1d40c005400242410308500012880442c210a000081c0d803043d80116507131411030808150510031b00d007100c04e0090034100c0030b00c02c2c180d01100d0294914011410039403048414030001d048422440c200305401c04000140c0000c0c2010202d036500641420380030785003403000c10400e0680350300000b000f01d034140d4002c201102c0c0c0c90340b00b680f102ca55208144c240c141869115400c1103045901c45840f044134a02c020041d0195203850252280101800c4804011141450001402c56180d038066524944c401100048000b400342050103083c41014440d040071441c29180c0139410600340c0034032160f0388038041081e644007016860390410349500b00c030b2040c4983e1030300308064003805d6000d40c120b03040740c0c49080e203a0464681d40111012044100040c01540d02d80c07030310052230000c00034000201c0c030a60358820008400c1448000080d0380d00010040b50904103040821701400b450b905d0680c118400140c0003e100500c0c08070741c82100c400710f800c17800036100e140907644 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 345593597 1250 345592347 345592367
    0x18100206010f170309060c070317070201170105090a111626030903030c070c030602040b030f0f13020108060f030a08040608070503010b0a030902031f0e1c0e0d081e0c060601 76
    0x2e241e0040005030414134060f8060a41c64880c8002c0b501c5203603d90f40c0300c1d141c0070b06002c03810030ac110010071884115030b001801c10305000f001c0c3d03854055a6140c240001e43c0100d0103851504040d546081c0c0352082e007440012030b0030158500030031103400b045074a40710f0314095081c0e001810516141e160061007034580b8045078080c2070013000541c06d64641e107510803026030008404580035001c2c004004000340f09400680300a000c40c1400540742e1410080c0b40c000c040c1c00034440c80c0500460f00401040617100c45000c5440c980a203000d190a036120404904014003511203903a0600c14074007018104160400108152070036952428400d89401506450601081c0200894640d0034801281d14900c260300c02d65486000908881441c0201000700c0044280c408881c641c05440303101c180481d100801620009010307030300a0603455104110020a11019201c50b039110b000303d2a41c40d400c0c4000c400c2581c010001000000e4040e2100c1d082c00e000b03075403080c0c004401c04d0050000080c00d960007078a9002c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 345594847 1250 345593597 345593639
    0x1a10061409091b07061a0f04140a09052109010210050702190816030914010c02061207020a080c010c20060a0203060406030503040b0d180c060518100206010f 69
    0x40454850000c0c542c40c400f80000d03400c81e000024054003021032800d00130718172054045084203a10b0000407091212600c407140000e80031300d0610783d199558020301000c1d00e40c08460013400154184071894118200408580c1140f03465003405503e44d00310402c04010024031400360200c0310590f5200d414882039a000b12150409a00700d1a01c2e19440303181505440c0440e0311512411740307400b40b0189160003056002005400054248200744100c4604170711207440c101013420b006098101d03035800121140b160400d00700e03503084c0d16004038103280d00801200c0100d69010030002d07124403401001500034448080c41d05c000581003034511840001038030512401c0500b000c00b4180e580c1d5101600c01c041e600241015400c9079842e00e0000205030b090018001400d42045034030781d00c0c16011041020f0361380840203201c03510b40e440d402c0c00001e004000c8803400c40700c0030b040203511448a0300074a070b12483c1d1581250f0300507041441000a00da80854460b060350325240003c008a81c96103901341d45a604c1000075 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 345596097 1250 345594847 345594859
    0x10e07080a020426010e0c030304051e1509030c0603010e07031a03030d0e0601090b0d170702091602010c0e06070b1f2405090a03020405041a10061409 66
    0x4208924418000340741d0148100d48050318255444101c442240c0c111400403c904019811088500c0002e014003803030410b5020042c40780c1d03550030002a84038861031144520601c3e03041481c69882c40b03485172040300c1c0303107000700003940d0103541070300e17140c980e038043c1800f2403083c0511240c000d0a07140a07016030341640d04a0071811120382d82c01000380c001708546443c903501d05070100110b507119641000200703510340313241c41d000c20707a0010010490b1420034103800c400d0b18a810103403000040e448403200107800c503030002542e04000c40682104020391181c600301a40006400081220243d40101d110814070748a900030003114400c100c0880d0200c0c904086164003540820083e0040380072500c44503003180b20040c5070524bd6031b60710290600040c40c1e602a80781c101034546003d141448601c891140140c060900600c0e1405050000c3c10100840c00000d00c03c90742c40000c030781030002c1e000c43e0481c039007080c0b10b0104140c10200114440d14400e8440c041c0011031082c0c03003040100e1081c6c25a0859103003d810 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 345597347 1250 345596097 345596101
    0x60308030106030213030501020f130801050714030a0f0f021809100506090f04091b1502060732041e18021b01020301030c051003090c0501050913050a0501061106010e 73
    0x2c124040d41c0074241960071a4400c50011001c148288010181840943c200b590388203000ea8100c3d1421083da881007000c0c2e45403004101c0d081e90010f01449103030301104503459403983c680a441e002081c649041803212440c1240c4082401d03603640c000c1c0f4404140f0b40c5900e40f04514001004156001200e2030041c000f10407404020351b0500c480a440c4800c1c005101d44005142100410111194810207031191454010072502180140150070050440d084800d11601c0d4401070180d41c0b090701a0401d03040114604402030381d038404020744100b070034858030400448040343c40001032a400c580500251821b8400d0b900290440d000800d0040701c2a84081d080390300c0000400c44000d400c614040e03e024504a0b80d2880c8090085c030095019510403410881158244001d10601c0942040001d0505280200380c00220380c2c00f1928008030b070002d10307066a03a2900d10002c02c05003200754007400107903400c0006104203840680c014038183d41c02a40d6005004010200c0155186828803540d00d22900c4140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 345598597 1250 345597347 345597359
    0xd0201030e0c130203180a030e0105070606080a0c030501060b041a0c0c13050403080a020a0503130804090c110f0a0804061b080a02030a020f0606030c010528020601180603080301 78
    0x541c0380682810181d03011400800042402c65a1803030003421950340c00810400b000401d011911503440940c4024003400302c80c1d0340c001c0c08511518844a040c40300102d05202041959048a0f01602c09401070754640241442d084d6005142e6000480c2c107035007481804151a460f000a64044450f4080c501d00c20000b03050542c2440e500941e0351000e980144e80011345541c40345001080e042d50302c1400000c0070b00e007a0034010305070030015004854060040002d00441c5a0002c10340340c00c03024400420418681c189852503280c82103900070102d050078400c107036003a55000501d258800d401030b011f8070211426011030544551000320001c0940e031b001d000500480f0b110305202c100c00d0003200751074960490946c989142d02e07002030703061000582c0001800c22000740c1c140700915010000900910440c10700f070000075180d509111826041241c081403039020012150344811a15581400d0300c110130035403c80c02511282c1c240110031041504808521042c500ca1044408407a00f03e003000d41180d080031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 345599847 1250 345598597 345598601
    0x20a05100912080d0507020a110102031303120c020907111b03070e100504060f0510080610030c0318300207060503250e0f0604080d0302030403050c060106090f140d020103 75
    0xc4400d543c002e9090140088082662044901685543d0020461841e040c500050000c0d0a540f5080c1150000e0001c6c49141e07000e01c00071000d61780d1010921300c5981d03214034120b90184400c907000c0e50080b103c600b40b0600c0360300401c01310204010282035859841714007000b42050192100c02d0354041e40b20010070040074003911000c0b600042c40401601555613500005802c0d100c55401c980c400451384e030410403061030000d0b410301058116040040c0700703190550003d191748090344045810b1607101d944081d81d881c0b096002580c0310b514131f4030483c01d00215007403641e500e0302c49200c00d40000b030500003040d9080d210034680000382c22665009051607410400100c078580c0010740000d2050075201581a00401407603800603210213155100041070311076804010107041c504080700d000740000c20083c080e007e004900502d4078016810302507666255454126080e208500f4100c460b0300030740c800400d0f1950300c250020304071a45c1c1c4042c0540240c542707030078286007a0500b034000e038000020f0344098010b5000e9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 345601097 1250 345599847 345599879
    0x90b090f0601050f0d21031b032309030d0906020c07081c0f090503030705060a0f0b06090d1a0108070501023d0e070e0105041803022e18020a051009 65
    0x8004100422011500c1c090303c6c00d40c1c1064178004291100c500708425506900e46844031185490144880b1843c80c44030101c42e00c041800240101d0030300c3c0043c8407a5010001c450a00000180c200b002003840e0802d02c0081d0003210b1103030680e0052200000e201e031070000745091114801082456402c10406046d90142603001400b010310003006c0c00010035a80034405401414043c10103000b940c503100002004a0355170090140500b0b280560540746a12800300340c034481c45060303541000002c80313401c021613181c5034200c20114520f07022001165803072002c501d28003212801c5e0211107079205140001e800c0540e50254585014503a9401c000c0c0601d8a0001d04604208000c40002c203c03403081c1ca080e051010136004441d0b1208100010806420b2a115407501c144200034540e4440790150740003501c0b28040031100d01003004000c2507429240d04250000380300e0321020402c1080702c1800180400d800f50200b01a0701ca001030810000360382c01c000301d00060041407603803402e4010382132484001020f015 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 345602347 1250 345601097 345601103
    0xb070201140703020309030705102c040603030207060212040312120b0a06030608070b0f0405090907090c200705090109180f03020303191406010509010203070501090b090f0601050f0d 80
    0x280802500c0255080d07000b0060355029030701035503498140d002070524100f074550016000d000b00c01101c03040c80380d000c00d40c0003d000c000d456000c40300c1d0011603d88200700305451880c1d4002e25200c0b0001c101900000d1220842d4403603000e8900d9000c0ba06026120b03400b0b42c5c03101611580d8401c40c0304950920940c81c00100e4002c40f2000075003816104041410300c202e503000f8902080d540c02051003003420400c40c00d0000c15003100c2e04ea1400c000c0c10a8588140500d2140b41e00910000c0003040d20b51406005120141441752001c104448210030000c01000c505114486d0307034902991040024100441c10200f550005031080d2000d0f4600001d410040250080b03600030404500d80500c00242c0c014001450f4a01a038000e5403241001c60a2034000f001d11000b440b401403600072503012191a4440c0964440c40908000f5100c030b2102006038214444d8034401007031540303000092030401040e1825240584058421030300b07e6902da2801a80d1142d0a000341a80640b01d0042c02500c6d01e0702d941707401d10140c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 345603597 1250 345602347 345602357
    0xc0a0c0209190e07050a0e09030703031d0f0706090902070308062101020c0102120717162d0906142d0409050f16080f04083a050106090b070201 63
    0x2081120b500841c1c1e541205405942c1003024100b10500c5d100c0e62000142000d00011541402c1081c107045d9030b481940ca00800303168885100d00340343c0c0424104008180041c00940c0e60500030300c80b00725143d480500403107002c1100e034100490b8400080c82a41c42d040d40c19150680c0640320002040490711015074944c2540d0401288404030300404c1c0040c2968410000001da2a03222000740110b900300000c00000422561403003008080c10f0b060085c41e080f810401c1e042c030400c5d040c410103c0b0650800940068509880310600345807841c2500c0d00640d4404958946a00507280d80040f500002050341e00c44024505118414221200d010f10200f40d000e52420421050140922082c254000360320541c2460795a0b070070400116410006a540010138820000d4040e00103400502607040180400b22040d000c500010200044802100d084084030400280300025410070510006032220300c3c240441c000e0300c0c410361211214024681a1001900c1e041031943c28403001c0042c031341040308240c2c1006 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 345604847 1250 345603597 345603631
    0x6042301090807020a0e04150504030c020a0621020a050a11010608071508092802010e0a08160902030105010828020409091214031f030b07050309060c0a0c0209 70
    0x4082442100c1e8154460596291200c105004103c194507180d445581c41c0c0c0304800c01c02c4000303845282040c5c0c806104803070001d450b803a941030481c1c0441015134000c0d04600c00440204076150880704200100001c2d46060204d4114102800141d0040701440c03c041032041c8400c03841140900d641c11901d81001d000040e01f1650341445504c0c041c0341e5444808984500b1852090b000d5211082c07a501404041c02410580440130700c000840302007203031408107041e8490181045a2241e024103000210041042e040551104405525002c085201244c1e0a84203280018002814006e5904950341611440b28a40d22040505d01c03090843c0341c105456444c448203078041500610141c000380002c08000140d1984601d403021011610501d102d060144210032110500707000c504036640700802e00c0d00d00c02800c2c0690a800280c40aa8000400d0940d9600403c861150b000300036510411410048071440e4480c0109a00d46204001418002511b007400000141c184800e50541006031080394201c04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 345606097 1250 345604847 345604913
    0xf061a03100b030f0a03030608061602030915130b04060314040c260303010b0d1410260319021501060203040e071101050403170606090603150a03080c010501050901060f020604 77
    0x705420507804c40c0072941d208424080f00e602004407685c0b200c94081cbc48000d200e1000c40c040c1d52402041d804900c100803030101c2c48400f24020b429203024190030b482d41e02000da03c810409109802c00e0080c3c000003490003074241400d4607080e0301c036406a60000701038800d0710308000e48202d1481a0229074450a4101c980c0401d00d0002000294000c010280f44251120b44495450080ea10202c40b0000d003443c20f10184298552000c808000301d071141c0c42d880361680400d840b01042880303203084030202c40c00042580d00b014041200d258408040560030f50325800440010807030542d10a004a8005a00600060083d28840f400310354200904c2d052001c8410302c010309140c25140c04540481c0022401f1200c80c003100d200307054003500040104c0b1201c2c2880d85090200c3e00c540001040302d4080d480d8004034042c02d40718400307250041c40c1c104600e01d59400b00210901d011381000c2c45460301516141000040d0303c1e100d025640501d009a50280c00d0b84d0b00e030307038591482d00c078071001040340ea1148403007103070b280 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 345607347 1250 345606097 345606103
    0x210303010609060207050105030702060f070219110a05180115052a010507030e1f02120c032a161a091e0d090605030406180f061a03100b030f 62
    0x1d005981d41d0084103414900000d0500302540d10041c103025042c030502c103001350007244032039010b5000551212960341300b40f8124030b440443c4d108020382d28a10070b60603050108130300b040310b6803030000d4035144121503035017050282c0d001f00303a449510260a0400140401c0701050f41001d001d183c941f4000d8209030100080102c99158910345c0515242c0f01051559544020b020b00d95005c51281070030400c500c0151901510342c0c140052108040c103540b20078180511055041e625031851740360040013a0318150341c6003c25039005550700404034001100b44841e20b680c8000d00ca2401404154183c2058007200e511a102002d240f4212220750088050301084601090300c01d100d00080c1d80140f1f0700100007680c42000881d180c0096a09400000c0810b1000c0c0e04a241441211282d10702a50780e40e0307031820800020000010f454500c0c5140c40010014003900c0e0b030301d51807294010a002c00c40d250b490781c80c00350b03881042182c8a806800031150003c9890943c3d01c004d010980190540d403009100d0540903003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 345608597 1250 345607347 345607349
    0xf061b060f0f05060a05150a030e03030702031b0a03020a030813021806100311070206031b03010305070504050903090f09070e0913050d0f090306181a04021e0f21030301 74
    0x607502e0707481d00000440704a5015031500600c068810f4080c9070306140100b000c040c0c00300380c9120030306000210311a915109512060030300380340e02c2c1580e403a814072400c02900c2c1c1c0c4c40b400b07454111800c070502c4100c14101c0803886140d003035410740050918184a94040c2c40111000705401459801c0c0501c01025803a6222851003070b00003800d0002c0f0f9440c1070010010407005540c4000c0425140c045210009010201203a00c070940444005840e41e881e046400c105020118605000e0303840400008100000094032000703448080320700b0b200554a0200d00c03903890044040311a800f2000d000b01e040b40c0e0505000880e044441443d00e00e8040710403401080500354241c4215500a03110b019110a100e001e2000d001000c1482ca405e681800d04180000c1c80302e221800b0240505544002880c107080113105141c6400d680480c10f034680307088c1b0801c040e9207120100c5081c3d0045a0440c82d0312141c0280401b00b1803251001010001203000e08000c0c4009400205090900c510b01200030305503107101040994 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 345609847 1250 345608597 345608621
    0xc0c08060a060e1506040b0c0304030f0308092109010c0302070b13030204180b0a02090d0f03170907120611220f05011b0204240f06030509070f061b06 66
    0xc07907401e140424449408a0060841380340084d1031005000301c0d43e914044400b11169020040c0d01c5070f0321542408e0039841940c0c0b0003000c0d003034855001c004068100d11071070b12491001013554800742c0c041105040c12017005030352042240b8108050106903004034001502c244c082d104441002c6c4d00c1e4400040d80c0c0e13118503141d81c2110340091080046160038040da591080302c4a4000c1103445142c5d48400d41c045014104464190b00403c03403003003d80301e40d00c4280940b0381280400da04100c07603040c0a002c40140c0495034013011180e40c005610210006104001c482502d09900e4100060340c036498010300400e100c00007814001c20000b5412400403d07101d41d512941091807111920303024242c00d0320381699101a0500000e460300c0d01014420306600540590182d4002c5540c991a0f4020745e40015074021100011418001c00305840e001c1c03004c60000c0c4d4416403020407043c0c91303030508070340c1d203180c60310502107408859441405480c3c46483c8a128a020800308003084100c42e603100b906540800741d502c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 345611097 1250 345609847 345609851
    0x3090a1103010c0206060d080f0f0a11010501080303180c061330020d0204090204110c072111010504170c040b0415170f0a050a140706020303070c0c08060a 68
    0x1a81400a000161859824118000c2045020069000c0d449220080049119904038030000d010711a8410032944001103a0b031450359100048200807100350031043c0340784005000e40c540e0603201e0005101301c0741602d6003200118116035680780940641000c540c0d01c000240a200b8940a903911468045c2c035800e500c81a89400e403904000a4900c0c44100820540d4840c42c0c60b14000740c5900c8401100a40580580e42c038120454a070001c0383c058011840001d410030720b80044031501d50426005030032050447c030250303082070345c0d10100c08140301030004003140d203180c0805501c000201030001c01105014181820360406599014080040b24441c0303150506070011104419207250520a6020341c0204840402c05001c00c0001481160518010100301404d140c01601d07210f2020070500d100070b0010400c843c00c0006500c0c2207501c40043d404201c0b803810f00000300c1801c0c0080843d0f014140e07165540110b046279180001121241c11040c015100c2054030240410b44141c1071089510500580c040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 345612347 1250 345611097 345611113
    0x7080414160b04030227060409081213020301061d0a0b03121315111b06090d1406070c030f080408120702160603150612060b031305160e0402130f020309 67
    0x1800030510790710200000941c958511101541c802d91b0840ea0481010344c5c000132055231514000039035200d40e643d040f1800d54031a0800200040d001c0310840c40030302c240c00a1004580e11705609002c0d041840fa10130520700100d0008203e003a40354411100c1030001400c0302e01741c00340c0841610007a0300030902c6411200c652101403158240e006451141d101941c0b50141001d0b2400101c2d035118541c500101d51000d200941445041e0307510001c0d1884510000c1150620540c10f1414030b800b506610b420b48403901508001070060303405129046545070305500c5a01036030700207004c200c0b12840300a2003156105402c0c0039140c0e4851903030381c0c070b05d01c642201d4006001d0725480542040840e161544042c00f010709040c3c0ea242c1082c4146c071b00008131601801d10703040c542c4203000f804014000c075801008801a011080080b103541007030026060310b0252080d104480031030b15109821200c5402084c9410b101c1c1000719006040643c04040766455070380c000030714520600c841205a0b40103403055440c0d6405180 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 345613597 1250 345612347 345612349
    0x1104052d030d0c0305071403130801050a050618040804030501090305030403020f0703030203040b0903010e01020c03040f0b030618280c14071a090f01110304110907080414160b040302 80
    0xd611040010101d004000d4140340d0030004001070000b4500504004000c41c14008010150f5403501701c0804820540e9125443c00d10a1020300d510b44c4a41c032103941c01d101c0072840c008041d20450b030090780c010f00001c104803d56000141d091402a1045489000402000000c03950030301c9440c1c1c2081c03107503443d00d549040c0341c01c0007858000055080389032030300b1008040000a80000460342100c1400039526110001a00003a005000080d01076201c1e50001401da0b52018001c030082068810006800c1b040300d0300c404042c9030318001124000e81000e504071984102140f02c811042d44000a01078030040c0c070308104189e9034304501040d1603082c0b89484c0c100c0400d403503401c1107007085402d4481d507200f403c004180e150381040164495039121400c1615001c10f08182042c0700d0400c0c80d8880341d000740807106030b50006070142e13030080318255403007c40094020101d140c408006409400782e543c1d066a540c070340c0c4d2680030400c10841c4031032800f481950368070304000c0d0b203281d01280206404944188c4543c1307980 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 345614847 1250 345613597 345613669
    0x31b1b0801140a051f15021c21060308070c1404091e2a140a03111513080f06070504030b010e04050307140616091206110405 55
    0x504a2442a414070b00307003101408400002d1035100e81c0d041804580ba40f00c0c0c1d0544000c030f04421a0041011110820208129181e035400a09800c031350340c01c031011002d003920020b102c0000c1043c640000307200c49640c01c6000700d94200c680d00c2000c9001c00000d98554a44d21742c032017548040b5080710f02c2458900200604040074140021040c800c0d034051040f01110782c0d03003880c0800654181c00e036414000e11050b09100010034606501010004111580c44280007425188031540c8500703101c01c65681981800d03030031b11458241c12079038013011b07032038108209204210303c0710741c50007031599846c400f8050004424695070303903c8000e1184402030850000c8041a89007400c800404600610400f00020000200d103069654112400c001840d041902c0358580710381140700e05003024010b00411042059110b2001c900035001d000007820320003009603550b10544017030b0200c0c80340d070388811741201d50400825400c0e0000d481008180c0e0200340b600d6166000900c10300f0300074540c03080742c505811988415248178 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 345616097 1250 345614847 345614849
    0x312110403030221130902070c0503060907090b060a080a0e10110904060b160201050a12050f0114040903050a0e040902030105040809180906070f0509180709170a0f031b1b 75
    0x301041600c0e011240e0803031010103000344203191406e80c2c001065002d0000c1400d40d0006080000c0a070348450401c82240c59460b8094003d58400500d00075491240d850701404465004099850340600350383d4254008004041d042014a280d02031260701501800082c86200c802c1941c00b40300a40341c4007a0b900740012944690460018014100140d504011042140b0407a2030350928007a0796602d81c040c022902c41440c0300100c000340381003005102c201c4581100c9907050380c0c0c0d4810000040040309041209a40c80c881c40980403403020849031030510711881151006a102500110703030aa41940400c0c01c442040b642550450408220040c1c07910745007040d22841c21100c041208542015a5420f445040144c08001800325142d54880d1590042d0207684841000a01046009090443c85881d842d0100e5028000400401d000300d2540b204440a2004080c2440141041d0040340d455100a2110480c25000c2c4041100c0202c400b24410813902d020502c03c090307684000110901e0312402c12031b5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 345617347 1250 345616097 345616153
    0x308090a02220f020c15060310020c03270d12090807140406080a0b0601030c0c02040507031a1912080f0c0a02150c06040f06020f0a02031215060703121104030302 71
    0x1017004401d0418001440c03c089041c00055250302d03168a8002898002e031003081c56003d600100302d080c8107110100c00f602481c41d542d108041c250305000b418200703807800c0e43c5c2030b50f40c0007402280e80e90224142505590080c46a804d0248801e80c8900c041860940c180c0c0c03000721061f50300603001503503003484d000b420018020380c0c0080480e00790503078440241800040a942c10140e03104c00e82620141324800d41c10341c00b500070740304200d2410001c40c010007400c1e560000f144801c0b0001380b00c0206040a2000070b45e1001110045001682404803124401040c00c000781ca01c4d0324240f004c00b10001600c4014602c28680c50b00510f1288850b2043c0001c110070000300000040003482006025000403a840c0d50050b402180701082c04040d00d00703074000780074244501003c114046180070010340c0002c000e00c210342035252004055070390742c0500c940013111442d00680010081c000309001a001c0d400d0104070790014036001c40c9055000d00a51120b400ca50310540040e8420340c044441e200c1860504001107030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 345618597 1250 345617347 345617351
    0xb06121807060212030a060b1c05010512191106031807150504060f27051807050715090203011814210c01020706020a11070f080a0308090a02220f 64
    0x320b002d001a40700c0743c00e109040700300400040046d0a48210b40e000748081d003940c001c41c1d034480c010003c00c100701c90700c1445c0d05e98480e4540000480d40c1e1403d00f00c00710b601000d11000f425503050a00f00c5e92070302984184d04554030b0b4071114204c0c0c46952800040c5100714003040000c1d070381c0e0342e40d032045a02c0d1071076a60018240f99080d80000001b10344c010101c80546080d03040c4200e100c00e0041e81100d12003074011611124001450701040440030303081400d01183c808039103205500ca4104500d030306641050f9180e0011880030001180050b0070751f481441d1646400d140011070140036000f00c0e00303444c0200a02c80c0d1101908004004101920120603a0b02d86280020204034804c04064404050300000800548801090314600072000350100d070400c13680a03a0035501c0b850801005040c42a88030b109400c18001d4000c0820364161921940e411658184002c1c81c0300d100540b82a642c104c00500f5040c05405984408400750316481d4064003031000c502a141c0b041a043c0002100304c44000711800d403664 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 345619847 1250 345618597 345618599
    0x70201092c04050c04060312030b01031404060510170601030b070206060906011107031b0311030f0304030b0a0f020313030e100e13060f14030c090606120405010b06121807 75
    0x201c0110016420001c420403202903500c1e5414081d1038003c1080000f41c0c0542403080200c1000440080a0484801514184000b0032018015030640d04640250f040103400c00c400100421000d4000c142c0094124421103070310760702c0703014500c0500c08107400c5071225032042004200b000700c0d9040c400da11020034405404282810000928031401c0603002c0e1b81004800400410309020030b00c070a0000b503600032245203419404111f00f0302603060a10094070400078a0452a1403414045014a0341c108801e024504d003500b59995400c0c3c000b0b01408034100c241ea6034070700c840481814070041d401203000c1d402c54124003415140090000041c40ba085002e203140b108054481a0030004005094004540c400d4901d070301110178800403c000e82c400c0700d8201400034009501100740f04103ca4600080d01502c8003c14964140701d1001e4065a245400c108104409001c581c404001e442d00188240e0000c1940c104a034001842038200310100c00b40d802d480e05c03d01034003103142001c0105005996000d40106 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 345621097 1250 345619847 345619889
    0x30315040e16062c090c0913060e090102071203090507090f1e020405060d0509190b09100b011b0203010605060a030b031c020c060307090f030605090d090311060c01021c0207020109 79
    0x103800d02d04e200d003e0b80320007011071101d00208050300d01c070440181c58042280c201990400142119100b90101c130b000c1980490740940040c0205d803d40d54000c0c00303035885d80b03203403c20071402882120802c0d02c150240020100e408141c0d4040d12020000044000c9805e40d21280c0c050304ca0508682c0b074142d004d10403c4208495110001614510408000001641e607640f40582d41041d5644000610301546440c0260400032544005030156030050210341844400c1d00c2c2c04e0341100c112990740e07408030360f5860044010354000e00408801d14030250011540e2a950004101c1a800040c00c0001090b100d0400015a06081020000b5504450f00c9003007148210200a03407610105078000340941000400280202c0c000d44004000b40b40c519204d180c400d0703482c100000109015501070308240602107130350b481d06110300c1e0340303000f5030341c00685103001d42505130704104403640522201d81d00c0355024041c41e1401c00400585220010400700b015170343d00380390320004010405680001c48040114610600c0f6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 345622347 1250 345621097 345621167
    0x50d05181b0607060906021207020c030c101808340905040c0f060c0c17060601030f0e01051003020301060503060c12041e0c09060b070302030315040e1606 68
    0x40c1c410a0008100c90254150118110748105080500114248185207080140c1b42c1e00400d204400f08559078407985514000302e85401c41c40c0c0c02607502d94031a001840c2c003860680d91048000100e8203040e003403500204803145440c01154401509900302d1016918048140c54114814101d00d948005041c2ca001640d0444280d0900880d2410390f81ca100145c10000e4004054019000e50b00c4a000c4040d038500004082c80f001d00d00c1102c004e00f9218002400c40c0400ca0a00e690001d000060840e680d034450044006200400700107000340d842d001c2c2050081002c1c850180100303d05400080040d00354018142504c909130300603802548280100401c10604009803000000c40c00da02ea4815162800c0c800401020300402c034824400c08103150b01000311800e8210100c42d0115024815550746030680d0010f4054000043d015810400008181c3c010170780c000501c0e807800030800265030543c0b092861a210114419090aa90800d428000c2c2038100f51038000d042143d6241003010b40c1c4032003803144 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 345623597 1250 345622347 345622363
    0x325060806060d050921071e030c0c080303010f050a03030c1403040504090804030b0708010b03160e15071101030606020a0b0430090906030c0308090301090b150108011a07030f0e0d03050d0518 84
    0x410280030052100c201032041004cad50840da044041c2008858541d40c90a49941c42849040c480c900d0281c40041e1a081c450b032104100c82e01501c4586092400340c84088595a5a0144030320f103003c1000081801d07a40d512480380401d002d10b000c140c0320b03415481d065059a0000e44040c1c18849040c1c0100700520030042241d0b40201240e20400c0000348107102036456111036606503034880e40c00000ca050125000b0003400c01c050290503120070014230000190111800d078082c81005030020b41d40c1c100411288541d0940003032181152100741055103c0340d00074040f0481c0c8c801c0d002005a03081c44000341c1c1c01200d030800307880e48000400c81645542ea80d00c000015074030006007007040114026105a5080d4451194580c00c21105201c1d441e02c40c0702544000805008680405c034010000301d1805140c199076403600c42c400c40600e02d005d002d83ca0582e1030482d40d482141c01c2001b00c544862040e1603514426080e01c0c82a2601c60b11b859041e6590000c0d240001c05502c044542503100c0300c00e0307200c000b03082c80c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 345624847 1250 345623597 345623633
    0x2030610050f07151a040504021e0a0b0a030c090e010e010315020c0d0e040608012702062803050f060306180c0a12020325060806060d05092107 63
    0x3a50710300312491600c00b240900361020f4041004034905200c45840d0b90010108000d03500307410401041408200030444034103880181d08a0180f110780404464400004949068000c103107030b00480e510400201558007514660740080d80f80e030b0100040b2600540d0b282d0241c4504c03508900300350306260400c11600014400908011140000141d210b907035981115007088040741034400b015900d403005014843c4215130385004074036008000602d00010710a03400e48100320803a100d2002d00d024032160a0141102043c1d80c09070b001c1004000d00000d11108403001e18005403a101084180e40002e000c4a030001c103281456a103000400c1403550340850b0481c0d0041e201d00c94650182c500240b007500d000098603219410091601c400b20320060002c000340ca03000d10850460f031101c0003414111141e400b00d2810920003095842081c0b1520340a0b81081e50300401c0a8400303401c05d41850b414500782d0b034041d501c030f039501e80041e402d2140d02110180b20115454010300114034002c42540c8007200409058903034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 345626097 1250 345624847 345624857
    0x6120d080a06030f2105040602031603050f0301031406180a0201080a0608070905040c080f151e04110f010302180904140d08090105090d0813150609060e090102030610 73
    0x10010709281d84000080c6030013400d0001410614602192840c60120480804a001c100503e8040d40306404480c1500c081c0e901a504185299142e0788030080408030880074040d0501140749071504200c040d50007913003d80300440100800c02c4199080c041c001c2d02d08040709181f20100c45000c100000c0f05182d45074286000b403030580d9588145801001d654114460720f014030382e00020440e103140c00c6103000c0c5001e01c07042c2140039035984865076100c60038000c00e40340e5001103200a41c0540030381e65590f400f103d040c03404000c2e1552208120484581101e0440b9003140e032513001d401ca400c1c044c50070104140203003800c600c1c02440c81000140b0001b104003551083c1d0390a0002001c024850112162100007581240e04220700000040c14520088500c02483e610b0131001884c07002d00001d045954821b40d0715041000e0f25442051443c403190100244d900040341c0c250348000120500c0780c1c40003000890740001c0c2d018249403c81e03101040180c15800242e00610a01c4040d594403810038650b40164148 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 345627347 1250 345626097 345626101
    0xf03070f0e01030b01270806150a050306070c1203020c2a0f06030c0711190614031b0c240702100504110103020309150f07110a030f0e0d0b0406060e06120d08 69
    0x88800701b4082e60800d070b42c175005480c1440307400c601d020888148510212400c02c046074581c4103241c0c0d1104101e4000d000100c1c01d551000100d1081541c0c400c01200a280152500b801c08511516203919080d55804450103104264202052300b1107074200100d044030700e000d02100383c0e0001800d9010261501410710702c0081c048041200002d14260010001740401c00300c40a40d2031221070342d140c14403030303007000c80c88540540b82800c408070116489540c90103014001c0d00846940344189401003070300c882c2c05124900c0512019000c0d03415561501c80c07420004403051900510081c107040c8009128148581014240300c0025017821110051107028600180c681c0c0c0c560540c1c0b841c003031204041e41d00090303a04085c060903944180e80a80315400544a000400c481c100c1065a10b600740310000c0d00007503c01900c0c2c8561032190f03003208004a80148495480c20040c0c0762913000300c100383c4040f14403940c0d4110412465081c10313803507580620111414025125600c40b0944c07540308072303400a0104502440 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 345628597 1250 345627347 345627407
    0xc0d050c0709050f1b040b0f093007080a050705100309170706142710110910090810181a07030f15050f04020f03070f0e01030b01 57
    0x2200a00510401c20144904d080070580c101068200395a01044008011080140980313a0400c450480b09005011450080190303079082d01c0344c0142c0c94095100840000105045003400790300140940085110041e80070400082450105617510101403500f07d8861500860000b04642003200c0040d2161141451101c0c4118000d10130464014100d00d88010310b00342d0040004080d203a128490041044032040c00c18071020103030707021243d018003000d421004945c500031051606402884101c2183c40d26140e90601c80f060711801c0700d6541500c200881c03403807168a04404111405501c0d42018041c982c108096143c5480c0001c1040c520740740c4a6800c05a01001601c0700c0c41c074190000c8500c1c1091407407204842084400b95513003800203083c240b003011034032001e102d2445290b904804407084c240c68107043c0061442d030300244aa0080e0309228007010300c02004000c511413485036503504c418201c2c0f040c0140040c0d031b2514039907041610781000e0f0398460360400040800d1b007460f100341c448142c070440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 345629847 1250 345628597 345628603
    0x10061505130b03090f0706081014030708010e2b0512090a02030a0311010c09080303071b080a0806010207080312010905040809040606031a040506090109020708040e010b0a030f020c0d050c 82
    0x548408070050703001041151904e404988010786841c1001622042aa0352a0844205600341c0d01250403205404082164024080740100c68400c080d05076101c2680d01d0319a64211102000c40031440d40010120550041c80000002264400c0151180340d0b141601d000929a01070041c0c82101ca1a0008c08207044480410000a800f50700070100c9908034030503d07000701221200341c4206410340c04d1800c512103a17801001c00f08240da100703600031421a078401808840c0700214403a61400c0500103440c1d0008907a00a000b0105c0d1076403a100c1300c1d050308000000900d442256400080c1580042c000008201d15200c0103a04494150901107940c0e152420048014861038a4541c3d010307140c01000211550583c002100f54500303000d03048414203a200a05c426242d04440065000181c14014007074000741e50701406400c0e000da42d00c9030805880e034003840358400c2e082e0000c08031008041540f5070301a40c180100740100049140c2503080c000591480ea980304a801107810600c1008540e80074420010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 345631097 1250 345629847 345629849
    0x2120a030914030d0c030b03010c02340b0403030f08040b0708060f090709061e05120a02040320150a0f0806060d060909050c030c0105071e080315031006150513 70
    0x3041540c1e1345810441d203401c010102c00d000c00020034101200d5000310328043c4141d5401e100243c02a01401901028540c10741d1131420780c40046240050306035040d00c080e080e003130029000c1a400c16130707100d05604000c0c2401c5030611005007040340e448100000203081d50540c0383c001e01e99081c0043c490b12645c00040307900b4408100e05070001060010000c41070742c040c2c00442229410b480d00d1841018107070b1107031859580020072070085901000740988811110410300c1c0c4c000114440142010f440303580305825206c1e80d11112124840d000790b803640c140f80880307071426900c069004c2d0703504d41b200342c89020340805440c180c81028041030b40c0c0001e4103606d454040300c0306906401e2080120030b4072003c41000500742800256094410501006136604001590307040b403072416101d41d420960150781d000761500280054500d0360400d0101b00c4000350001d005580181c900354885071501c5892428145008403141d200c04031507082174001c000c08200200405020001403400e690b6440e030307402c2c1c140f0383e131202 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 345632347 1250 345631097 345631133
    0x30e090403050315011b1e06060b03010303091212050c0109020423060d0515090a210e03070b0a140405030d05040602060714040902070f230d02120a0309 67
    0x400c0101503016004600c90b03082003400501c01920140110f90303070801184e68400e00c940181d00c0001140804a0341250f10f400092030103030f5420b481d5200b0b026160294004201450003000510400d0b030010340c02406042000840421202191286442140a52002d0080c840c0015017004004030a4000c00310883d0054018080c0314594600c1d078584134030300400191550381041c0441c0c500d25048400c1c9060540040042400d03a002014815580c04041c0031049984900c401480003e01c00076000b50301c5100d41e419481c88952410f2000d080340e102e002415201e41c100042c140701c1105400150b508414492608113501c040341112100d2034441c0e50411981440340c14000325860703a0250007401a070310b003582512440d4a401c0801d4898280310b0b1641c407140c4000340014884250184d01411050707001300154445d5042e262211503550100ca660301aa059003401c078107031006d1080024100600311803000300700724111495420014055046540304150f1507984420500009070308448130380203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 345633597 1250 345632347 345632359
    0x50703110c0a080705011d0307090510090c18090912030203070504030b090c0415060206010b0304080f0c060106020706090501020a080c071a0a0f1b06050403090f030606031b0302011b030e 82
    0x41c0f910011a580e030400d1240350300040035140000b2080d01002014418200d0250087c000300341040030340030240800500b030031007540180500280480c042d01818560100715103a1481c003492030780e04440c4131304080d00103001707480c10010b101d00000c0381a80f0700b208a00d698038005880e503c501c40100d5051140758400f030105140c05003805200b00c0c0104608020702c000f158200031508441e400c9080607061481620050f81008004001c1880401c00459001f481503c4851030b0440400d484c102d107402c04000040300e5448440103121007501000340300040c00560410440c0c692030280000d5552004800c0113026074400f190720001c43d00f042105002418982400c48910403080c045100e41d1340103a015800025070310803e60b0710b21030281c40d04c541480324031a84541110040d8581e84060a4042d000302c2c10820079402c002422581d10801074040c43c030130040442c1503855810441140d4940904504149840d1442000140e03002890040d600356021000400c00c1400d08083d114400ba00e001c043d0400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 345634847 1250 345633597 345633599
    0x6150b090d170c03120105280905040203030d0f0b010806010206192012040309050a0e06091510051201081912030e0109031e0c0b0601110a050d0206010602190201050703110c0a 77
    0x503160301c5c54141c1c0c10540303241c0461401d90380c3c81c1c01c192109949140d000c00314014180320a500d680c0025910030300240c100e0b807406400c1c00e0b00101715103604007d40d80d42c5944521101003981d2044560760005400d200402c01d500f0002044000342480702030340321280da90340701b85108604420451044520182600c684c42da446007064400e05807044030101c00051508101049524040900c40191007a6101c4000720f907640f10248543c0d00c0d030107000c4d0f862a2005070030540695444c64000c440741c280301ea81d66074998001546041d06604113030030280181d0030003900c0781001d007038084041c106181c00c40c00c010703855406400103030010080030a07541095402d2140040615801503e07010009070075102c00c0880340c01c0d425080b5091100b00d5002000b00c05400c003c503503c6e41c4a43e80c03a044000356182503500118007a95040e01d403840000403a40980c00103c010000640c06102e840d0b880d10001c2880a05250b0030390000b0498428454000c0c14022071501401c841c4000704209021410301420000c442c0d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 345636097 1250 345634847 345634867
    0x120705300606010f0201060f260105040c0501120605030c0d020a03050124081506010e043914120c04080a03020a0507050402071a0402150706150b090d170c03 69
    0x40c0c0340841c2c0d1203002c1242c4955550704944140701d210202c1d10088000c1a00c2401c0c2024030869500794502280c6041300d2185224855400f0300c14640614230400f110441d141c5888005000345092000000c4003e02c1c0c09400c01041d1000318500c1000d071021107070f00d40701c4412440040c0c40c0440f01e410184c000d40c82c1ca00c10042000d6104401d010b005a16032180c0c00b684e0391020410b5039070445c03404108a181c8080e0201e020795005000000c00040020008292030140b6040a00400700320101000135402c2d000d680c012141c031050004002600358505048080c1c00094065540d10441012a0f080c0d00108001906010500c09640c050603400080c3c40e01c00b03040341030095031444410400d40344d41c0a803503000103041c82d041c421a801c2c00d5102140313920b8034003034003018a404070300140166001400745200122443c0c0c0358004041c1103102d650b0020f0310301003400078070b2101d50064012040b041c20400c0401c3c69507407110203c030480b41e401004958000781c1800b080c0414011460320034541d1101207808015 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 345637347 1250 345636097 345636103
    0x20f0a0b01060e100e0409050709021809100501140d0f0c0f1d0d03030908090a2304060e0a02070c0b040801290a060c060b090f04060b12070530 63
    0x121210b50303030740c003c000c0d141d40c0400c00d40180810382c2001180c4000c0c040b4640341840d410140f4014010000e450a9596684408082c0d9025110b620110714212050445c0c4c0e00c0d0130044107030014110070710011980c1c02c090020300b480c5480c80c011070070039801003203061065085400c0181108541601400b103940302d001c000d00044900c022000206a410605119003901d0300c88810f8185d00080080c0074140c80da890a41c01010180c4040e52020703010041039220740c0311450340320020310319002d195000021f0807004810341011000090303c01c41c00c1c20010842d040c0e000403801e401103a08480182d49645914108215601d968014005040301142c0040c580006600c200314851055035104042607810b145140c2d640032005540b0b80c4040503040c1408410f1094050b240c10a104940014404100c1c1d030008d6080242199442d0074079070f92504120400c1726130302640c050001f00759001c1c140036401c540c2154a0344141e010301070090b80c42003a01c1c42d0110140800444041040d1703640000510304e02c100c0380e2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 345638597 1250 345637347 345637349
    0x3120603150606020114061011070e070e15070807140a06050106050306100c050a0b0709091e0b010e01091701021e03041e0803011a0408031803101a040b01020f0a0b01 73
    0xf0140d40303040c070f45400c00b585410132207124140c000c200b03107a82120b06c0411b50355a074112008240310302c14250f0200740103c442102e40c2c01820300d1381700c00655140203010001c03142624054581405410b000802c00200400d00f038450a9078050441405010308000080c03510b0903120000e010700f800c0c540000344654020b0011400b07134070117031005000814a4070041c0c9007a403075000001e045a00015401000c20441017685070040764602d040405503907524429001d071110040c642c81105034030448410b41e140d151140680e030740710a0130481100c03102500040c1c54107116110361038265100c03c0039003000120a40c101c0e405450340480028101c52043c8039100150401c4608543c1c107070005540c1c42c1e008907251003810f0026800301c0c2540c13660f0300f0322860201d50800801c00d000c1821080c4400720f0819802c1c03000e840704041c441d5140b15001d911000b01341c90040304220b58560305151001d0844007041d08003801071090001d440104143e405070004074038100d180b0030344148900464492900300025280c10368 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 345639847 1250 345638597 345638609
    0x5150405090a03020303010b1b06011715060f19080d09030c0504020309060403230c03070606090621050c0a0b040603050109051e040c03080c0106090f02070807031206031506 76
    0xc503941e860790003a9240c100000181c09a40280010480c03003004c1070061450840071510401c031024046500351608600382c0024040a6600c604803080038030401c002441070303100c085e91601e10b0404101051401001412941c026603543e00301d08098a52500c10780020304460044415804481d40e000300b007030141d4081254065005c0a0002d4540741600980b4001c10a4134054012600d580d5030980321860301c0700c5131038003110f50b2a400b000398844030000f52400c0c1503d207001d1542c03030034180b0340001196140e81000060b1440d114090041e00e003107041d00c0c0c0c03000c600c0c1501d1030240c1445090aa10f026003202009910040c010f20229030529480c0150040303541c4ea44062000d43d03200c0003140292082140c0304060080c03103180001544694400454000340a00c00c1e0036031b150744070303241e00d10709620401d02c5642582d1200002c002e14002d1307108051244448520450800000307580302c2c0e90300c1c400c1d100c0160811405840c0421280e84940c0018019035014102d611015030303130b41d031010140c01c0304c1c440c40c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 345641097 1250 345639847 345639851
    0x151d070c051b15072f150a02060a0608060105010302130509070e03120909270a0b1e0103020d080913150e0105061216050d0603260a08060f010c0501051504 68
    0x10000085412044d101e00341c0d40f05008800740110050703601445501070900340804039442c51440b40c15203421002041700c00b40c00c49500d68407507600c60302030310f08140070f4491880c80d0b18041d001c02c0f50300000b0989a041d5182442c026a44901c8585290704c1140c243d00204d9010710b1707000900c041c564014030755a01d009825802d49000460400703001d41c0701d002d0034000780e8000c0005400a125025450b00d880b809048119000700c0544144044914042504200b256030088400c144610341070140401701d1a81d000f5018038500e5030540d400320300c2400825400034001d03000030808d0240307035440741007400c0d400620032410480c003203200f40010041084e074890310801050a200108280c103141c0100c0380315026a20100c207942d26410301d6902e8089591403403800f000014030044011800c10300030301004500505004401c0500700542011050798490385400da08070402044074060340010740c641e0f100c41e0403941c8944035030104006803a903c5201d03070300030a42e500c0c040c1048450509054595880300040d039007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 345642347 1250 345641097 345641119
    0x30b0d1a0f010b0c0319050f0d090b010503010b15030709030819030c050c0307030e190905101202030d140409020c0610050a050310090f080708030a151d070c051b 71
    0xd4607504c2a0018241c1c070781c04c2002980b211444000120140311520314109244c004411102034403500316401c01d100840e00e40c0f50401c2440200114540903050032002004449551000196400a40d0f903505000c4440070000511007802200d0030001550440065580e0f4407034501d40c020140265040344011900d010071a449a500c5042500d012038040c0c4011850180c090301d050703840311030203641a80e00c1807040140148089031011104000d080380a4081181e052520921003041400d81043da4540d00071080ca00c056600016011002801820029903079107180c4144465407285070408041d2500019000112146c000b909600c030b9110310b030300c005100d5200d070204030064281c1c1c8600c40e4580d11494420940c0300d019441016450b21400b4020f01c20030450385c45074140e402c114010786200c480441004032640c1e0702d004400446030046030745c4001e01d0800044002d5a0f4001c01d0f07212548030070000040e02ea90154414030001500300d001c4508081d41c7d603c2c0903251b00e04110101f8081c81d0301d40c403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 345643597 1250 345642347 345642359
    0x80307020d030506060f0d110c0a02030705060a05030105090c040909080414010206040819181202090f04020310110c1c0905150a0311040b130306060806040b0601030b0d1a0f01 77
    0x120f860702400d0010191071504070081ea010b91135070003000f41540d9142d41c2d088200b4818040e10000c10454200c04041c000c01072050040600b02200303644628020181000600b16040e8002c0c210303410348404035864442a114800003201d036014681111003c00e1401141c80180084140580b003200e013030403880303414030032240012600c0301030580c0c0040c0355880521402036401251440344940c843d140c40c0202d02c901d41804188181405a44116100d140010301e203000c1d420300d901d42ca64440701d1601907111500786a408a6614241440e00c0c1e07907001d40c2e58080c160501c4059040350031030340784441128050300003005034045d00e031541c0c51400c1c081400765600242c10309003189512500849101d00c6428080d56230400e40242500400301101004200310101c1c4101b41c01c0d000e01030b5800c0300b00103c20080d046103420012540b9030b40003600b1641c850810440083d9040000d1580000d0a03e40441c0d0f00b0290302c041540c0d043c852000820b851058034030944010742401d000c030b2081c00800d2a120300b50760398034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 345644847 1250 345643597 345643601
    0xc0a0602032202010c152309010c0c0c030b07050d05091e0a0804032607060e0712120f0908030403030e030607030603051902061215030106050a140d020f0d080307020d03 74
    0x224000d000c204a20300740380c0800c4600c80500f210300300003040410071f844070b80844114807181c105107140c07455400c5d0034000616024400c00d46501d070142080d18044015440f50301c014085031000034103003190000011305407440765060b1481c00c030561105100c0c5090074481035803202c1c00070708800c0300c41c0c000c4030728148030102c001030b040301c0c80d0340002a0f1883c0c141113413204022001c4046490070240c4100789982008502d00004220540c000c60b00012100c000840980c103001c5298400c40c1d0350f00141503080081071241180300110100e6042210009401d0a01078503040c00b00c3d84035050500000c60008149a00841a603d240307908800b03070380c50350303682e01c9060f02220054003014115501881d11400c60360300030240080c1141c0001c01c01410205050810a20824200d4030300024500ca01c404050a04003401070030b002d8003080766025900303800c09205e82c0640780c05240c038900c94450b515401c020340d22078203c0684502c03070243c2103800418030f41c1000781c050b41c020750721100184607000030080603e00c07034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 345646097 1250 345644847 345644911
    0x506030303010b0714031b100b0d1505070c06020415030501050a08030f070303140106031a12060c0703030618141308040303030b0102160e0106030e03090a05040207080c0a060203 78
    0x1a03c03440d05005143d04c5242103640400c2d03600845100801060031318403e450b4034422800090ba00410204200f480044262003400201034054090b00070b03c2030000d0545c88824a50301c401c6040041c55a80d0084100c800038070340c100c09400c0c01d100080100c1c1c0000780700c0040580c41c0f40d0751000d100c183d98500a2243c029543d2283c2e001c6074005108000f4001507000042107017030700070318001c94940f9420a498017406800e03030042022954072001851203104035481c0e041c840c5002c5441c1940000c0fa201544e44505008240d400d4100b000284041018020340c4000d024141d428140340030886010560001050301a08101201080800081e2000304514894103060b030b0143c1c0450501c0d00e95a0250041d0500c1c140c06410b42c020300e0b14001010710498200402407003080c65401c02175140040c040c00301c807640c2c610560945c004001d032418588402200e41d048860030740340180e81d10183d00348041c0b2402a160300011038003c00c80c49000340030b01c607009540503001341186003004100c40350f1612510006 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 345647347 1250 345646097 345646109
    0x90f070e1603240801020405010f0c031e1209081b0d0903020907030e030a031a010e030705120106030503040605030103031806120905100f02030f011d040f0501060b0c10050603030301 80
    0xc21420a60640329811907003040512505070301c03803000c01990410920f851034220390360b26035022170100080d680c81880040c8101c13540c01c00314800308060301c000340624061091940301c0c60705004200301d0fa62180000c0030322101d111504005440451804a410b0340c4035076084030281081180e0703418042d1000c15442c00a41141d2a2600c106107558240a40c03450020981e0f0700745540d854010035145010302c02003000c003000b41e03400a8041102c0032022000b42410407124104407000c007554600344c400280a01c25684200c40000180c2540205c0a01400c2d590300010068000404d00044080d0048003440c140d038402c1c0ca0703460780c1c254400f04429603008503104a10008914254144900312140e000c144001e001d081503d10344d28020600741705542d0300003c0c401341c0c10381c000100545c0389180ca461502410110141e440c40d46d0b050640c00d44010400b0b0000303000c1000040303090302004000d522420041c0f108118540d10350b91150405a1144001d2102804160408000038518540401140c0c16901 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 345648597 1250 345647347 345647371
    0xd26070212071d0c09041a0405010e27030c0106060f090602010903090501031e0c0509090c030714030a0f05040b160306050603190906060905090d02011a060706090b090f070e 76
    0x6081200c003c4855000352201d456500200141c2c40c2c5503d13680030703011180082060300e28000d11045c0502c412104168000d218644448003881450304101c200008001d490310700300200c140310701584504512070108110072641c40c00c0fa0002c0c0d8260441e0030180903210341e440d00c0002a9980c4401d81c04d0f2441c10304c0042c0000d032500410300056000341c0c480308110142c038556004220207004598121200040c1e84004103802145118107850008403503540302c80680700407400d5040045005c0d040041c280340722582d20034040005040680c43d075101c005046040da0043c001ca051a090000c00ca200a44080c00c002e510090640c650f24064000c080c11100c001d4070043c41e42d43d40b54003194406044a0710050200e846d240040c010800c2802400b02628120000081c142010602145885452039809083d03906010b2204290400042164030b8454180c0303280c5d5a5076454500580101120b0b20000c1501140106101e46508000b034080074500c441800c5521003030700c0b06220013540604941d6402806 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 345649847 1250 345648597 345648629
    0xb0a09020102071a220f0807030c030b280b040b1e06090d060e240c0708030408120702100b19030213060503070605090a0f03020f0d2607021207 63
    0xc103900f0040d11200c55050300c4c28100f009013010780000444410b11005032003580c60050000001c681200001803400c80018101140b546c0d465040181c100c2c44040c00148051001580d52401d4140118208150447c0507200305100d9950000802d151100c1a01940c54218001c1e0b81d82800511441d42c807210b100d24600c0320320042c0411090354441010300790032100f101d803071100061650103107002003403940c1e01404840010384003008100b10541c01e1402440d00c0b5809020003550310108680c038054101403081c0d0b0300d50310360400400b42d21481e240030008102c210100300540d5804240c0c3d00c5008042c034020b200c041401e104203d4004004285800c600540200c20001450182150516819003e10100746e082e542c00010742014150b80c84200402d000080011003460041050800380410f0030b1040b032002d007160003146205651010280c02071090181d040306100d45000b21925203605c444038041008107418514000e500440c1c070403401200003000070710b403001e000704580e0161030001a40100d45 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 345651097 1250 345649847 345649859
    0x2208221202130902132918010902160b01091e0515091504060b0304050105071704080a032c0c03010504052d0303042406080309010e01050f0409090b0a0902010207 71
    0x1c2155080407a408003146000382c2c59550b441c000c028101010741c0c945506e840c4c8071400c2e41c1c80e04956154840c03240701d05402e00400303c400d001002e81501d125a00c0185c13100000031610070200b00c0c0000107014994001c0c000a8020a950040d44030b2a8005444080403000c0f43e00700000d0714002d03510044d01c14455400b844c468202000001c0c0c0c0081c1e0121100e904003005008034040300c110f500070601125000041000b441402d004240d0040440c0c90003242c07458401d400131025000c06080181103640000b00f07411400d20940042602603408401c4070012908031140301c1d103c44c2ca0809040c801c0c010101014210724042c0300d528440c42d08140074200c0c0038111000e20003d1b101c45000b803d090712820801204215042024610a500c40d0b0010003c4a080303550048900344d4410380000303001d0410038140810807021041c1c5041c4d0300203080c28141c0002d91401a0b9440c0990038521a90300e80124002442d200c06811449049002d403c4255254560144920940300311200103409030b8411003040084c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 345652347 1250 345651097 345651101
    0x60103060f3c02040f09060503190b0403080421050a02100603020f010509060c0a0609060e010e0705010815090a0c03050606030c1204080706151a070b220822120213 72
    0x2440b1442d039401032400740c44907004000b03400c045c1c01425440e99101c2081c85a0b00b4104007105c40303007100c01006041c504195903180456080100000d041000c02d40100d41080180c108200f0400c00210f4103060345052002c001b400303504200035410051242c0728800c2100100c51054406503900540000c0c640000100152016800402d41c650011002c00c030201c550002070180ca41118032801012440328140c0c1895016a03040010741d8984d07174500b09684160304800a04042103c50a003801d02c41982c480b00f1505c1442080321410380c0001146042089191056105440340c500545007000143c99220034442c0f2400102d0b005824030400300301c03e09142e1403c24a20781c0c1b16114901c01881c12580e82c1d5140d099070b18841440711640300c1e10105010850102c0e0010400f401408089402d01e000d0782c40ba40c2003c0c402a01c041d00140c2030f4000d82d9440900540000710540d0050121650345041e0301d0b0039400c01c02d016584a01c0090007190101d0b040385200e411203c0383d0340040601d1a40c49a0b021b4030b00c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 345653597 1250 345652347 345652451
    0x27050a050d09140603150306090c040f0509031902010b041401030b0c09100e03010204030f110405070302030c070803061c08040801050f06102714010305060f01050403030f0e03060103060f 82
    0x3031b8041148480d180d056404200b140e00c511490000f40040841c0201400141e0705a60038522000e42030000700119921b002081c0e41c0c010014968030011441d03110400c0c1d004104800480345c003c1d0510108003000089e02608078100c80c070444d102a150b5407002c42c40b5880d80542c0102030361088e074202c1e605a05a12940024154003402000145026a650340350385c044d107a070f04011140c104950203c9091071502d4481c95900c007243d030900390f18514145100c1c4281d03100d4400300500f030000210105006844500c81c0501c1003000803506695a852801e00036800d401030302c140642e035800e08000440356400e0546c00d0b80200030117055075011062210741542c0201e051094088003042181016068041a84e00c41e8010400c3c0d4201d50400024100010140c8500520b05c0d07000d07040d0030303c2c141c0d403a0340c3c44012a8210383d0107207054110940c4030f00040301c44001c04c100351589441100000b00c240443ca90140c0e08a2100311400c000c008844486c001041c030301c0300e4a95070260715001ca001240078400c84d07050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 345654847 1250 345653597 345653611
    0x703170a08060603282301050616051002030108032a100c0e041b0f030212010e0709081f0c0c03020709050604020c010e010e010c0504031527050a050d09140603 70
    0x174a2149118142c0406a003440c1c1c03044c5103603403905001c080c0da00c054031500d038044031508181001581450003084030743c41140c51075050049880040c03024418180039032103100102f40d8066580e075a4511817182d40e50040c80035003c9040030940c415001e0020300c03521540b800007040c09400f272000b182c203048005120860144040c0b041e040c03484041540c0d14402c019500c200f0282581c0154a00e1000500594011100b541814030405c465038491001904103030450f6050846501750781e0790310a04a4000c202030b400310740c80b031250b103141c0200ca8100d04e2094084c9441440308024007640c1c1c8500325900791240034080c1c0583c200031802d0010602541000342d102038003401c05841c2000a010550845404001d00000d6035500c1d0314400a4810038000c40c90300100b03030300d40300d03047c18207544603404c194598102032480c1943d24441c41940052011190751818414026201c03280c100d414019140d060f215000c65071801385841c07051685000d10303808016201e0321558104404008401d0000c581d101801d88 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 345656097 1250 345654847 345654871
    0x80d0909020306120105180f030405030309060714030304080304060c0509011205040201180b0d06050907090b09031908030402030607050a0203040302120a0b042301060e150d12020703170a08060603 86
    0x8603031307200d03402d0017450300648040c042a03e00c1c2501852050402031001790b641210340041004001c00e903000010313283c10a41c2255591790700e070301a2034511590144010b8441241c0070100811080c4000840918440c901802040c00003159501c021259407003000c03409030103d101c01d501c0010240d4580d01881d4005e00c18109900e000480300c1b903402060b480e9601100d51020300007808245600d15008110003401c06849038000c5090090014100084500812008000c041a010b80c81c1c0c2d01040884035150b44580c0003014810181800241d540c01150180d01a105540100b51400e1082049960b446080d50145051609544c01c00c41c215a48100800302e03172241c101f0900c0410b00505009008500c1401290100781c042c04240d0416156019450b41c6a450300304100a05858901d52036404030110f030000700000131010008880151404002d42203580c00a6514205d5400041d41c07410b0702d0040944a40d41d43c52035042803001d105220007140001d60719004103281d030034403401561708440a84c81c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 345657347 1250 345656097 345656119
    0x6020f01150b0a111e0f011407050313081608040617010b03060409030504170f1203060d110301090f06050106020705040e0304030f031101020a020c12060f010b0a03110705060709080d0909020306 85
    0x17105210726040c00140400c0d800c141440784003110244141400182c803a205540d09181c40c90b000b41141c00000c043c107141d4003080d5000d1040000c1d140440300d010b102070444441d0006203080104440c1c015000f03103800318100300f42c1d070408406030108041c100c0715040c802502c0d42d50f9101c00e0101801e140c803070440a00400744008118414984400030050405000a02014104819181c54400305442c074110410007042485690b8543c0411500c80036004007407040100d01150200c2c0c01403400e000050255522113540390108260b903001281250110303400c032411180c0350401c00044038010424005282d104000410020b03000101452806019040040c40e01c1c003850740c51405d9a216410302c00058105400b11942d07407506541101d0000c41d000001c08282c580750402d41c03000681030042e400f07011804100b4091480c0300c0e42060046180c0700c58881d4840490346026030307072020123071200000b2401d1400c02280c10b42e070018800c1c03002e200c01e85e10044c0745807400e06800000e60010b401c864021001c460 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 345658597 1250 345657347 345657373
    0x602130308030a0b030c0a031205030615070c080606011416020102030405090f1e070e2e171302031c0c17031608060a05090a0608060106020f01150b0a11 67
    0x20280d403045840c0d079004102004c1034000c16082c5007042d001c09100e072045203414400700314a190403d86100407414115a00c1d210b82001813981c03420b808500c851a800000d50341d0801000b49401422101000c0c00c440c09a00ca000c0151001c107041c131031010400c2001e100b82034107041c0041c00408182c1c01801500d01e002d0b103481c0842c24145049a209000291140900a0300041c44865400c0c20460040441d45030401d000f00400050071890707400d2090032500c0e9a502c9990150b00f580807141c00743d11404d04000d107117460240c0000321031214426407034003c0c000124280701514025500300d5009015103a900c0d1095115009001c000721140204901131480900150080910106c24003200110390346914133010101010a4031000c00c8082240e1641404543d4840b101500c0030744500b1100240c6a540f8a4664001440142e0050721a803141c000005941900402c00c58541c02d10b41d00240b00f5401866200e54140105108030f0082c80410890707161950b209904000c0f645c540841902d42e00c001c5a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 345659847 1250 345658597 345658613
    0xf030f031f080a050d0c03080a0209031c1d0603040c1509080a0303050f1f05120102090904141006060906080a24060908010915020304050313030f150212010306021303 73
    0x2d000390302194000c98803031051040800a20300c0503201894101c180d010b80f564020940800604403252203a004075021030107940912800700300810081e203181f80c409a072000141620f410408840d04080c10502a0445041020450380b282e500300c02859030183c50301c0b80c00c1d100c07d59900c800904001d291140824140b80a0000701c0c40d86000760b4021507142460303006400501c0024142008040360505050303141c44001061138200d4100711444c0d0b1912080c1032021740039208400d034203035009001408020420488a860718000181c42c01215070b0120b040d0244c0d01283e80c20300950010801100b000c11441d403040460700d5001030120404104803d03501c2d1591150790720b5155204142201a005010095000e15800001d0440500038000b5000c5522480b5030004002a010344c5660008001001d22174108120307108214034128052000d40d80e4244101c4101403030400b150b80c01c210144031000076002e0300a860001e02c4041981c2c40592031565a100203600204200c01c4070001200b001011035404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 345661097 1250 345659847 345659849
    0x60611030702190e0f012301090b0f04091407030506010c110d020a180b040b190902090d02030316051b09070e01030f0c09150318060203060604030209070c0b01080f030f031f 76
    0xd1040d85000e50404500711140f01f03c40229204109001c003c05445030380c00842c078400c484584a090390380e41c1100442c000343d4800d642140b040d841c2400d000c07002e441050700c0c074030f0310800107681c0400003074450b0401100c998640103405002102d00320014004c0d49403013209108103520040c5410b6825a4846a41810403014034854402c65914682451070b802c080c0540300010000700c915514071483c05034101403107152805168030a90b804075000085440c0c10f9001c048103a001821652644001e62002c031641035040303c02c071918000d60610011220440f40a02c0c141d2000a00e2201c640ea40d141c4102d031010240300f140c134101919a02c1c0c0c0c054084a9200d650b003a0040c3d541c480b4091406c281c0d80b021446001a1514100b61428510070029070421412880c001d070301c6480965241c031002c0000e500e43c000c6800c00396116002c681408180e40e084424000c00310f120310046242e580c3c0c0c6031800368540180ca5010445034108200b40d1a1410900c8015503204205513900d0035030500d192141c45042c525 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 345662347 1250 345661097 345661111
    0x30913050402041104080729040b0c160b2b020a170f0103050303160c06020a0c111504140406031202030901120b030d0f12050a020904060611030702190e 67
    0xd100c040c0419800e0501540b22103080d8030803203d00e054076101259540e02c00d54410a08490f00c682501405400012000401c552140208070744840e182d403140130640e4809000b0f01518880c0615039081c10390401c034114100e032010742425051211404002028103180c02d0042140bd407915000f0700c05a1480c0b01030b2030a00383c1c560b036100d0070054019811003007103805004903c0ba018607000400025800004699200ea01c00c51804001ca29600081d180e04040c00d900424203400824200c400310b510004501c0700354050580d098400481e40d00740003201004a100b00c0c408601004140300e2403044102c5441c070a075010340005012907036629070b1400429280304000040c1c100165110456074464005115600e044c1010803201c01d080c00026680c02e01070360014144181800a032040c90300450044058491000c0280801d141c0182d00701c00a5000c1040d051103140b40000101c0c0f241d200b18005d146401c1000e008501d00a1503400f08001026034403240500c0c40700c0c01c4808210030881c2c851460180007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 345663597 1250 345662347 345662351
    0x306011b11040e010b0d06150f060305060f0d0201080c0f07020418060c0912030f030f050a0b190302011709010b060a0201050603190b04030c0507090e030409140c07080903030913 78
    0x6030070704200a0b100c04016012803a070500c140c1c041683d1721a41c1e440312007a4003c000007110f0140141c1c003449000d2962204600441d42c0300005a0300d034154014520810049507801d500c505600d0801c064030100c2ca40190004011400042ca810702d41c8004117042d6400141840c1048100e500203004d440c584003040a0000745988440d007048914002c00030101c00c0703400d1050240d41000394114001c800742c0d0f00034080003003111240844a000307030301c0100300341c0d84203509000910303083c07a03258003070203042140701c0c003405069000c240148600140d010650740d050751211501740c0c13982460301c500200900080155584d0b00c0e85c2c0102075403194001c0c1351000c0303d80c0000c40d8601c0c0544c101810b2900040b4841c0c5400c001c03c1584c8001500c0e03806581d407140c1d050030035a0340c105960410600d0440e160300402011442c007103200002d15000401391048881161041c01044545101400b189105a480c031210b2501402040d00190f00100901103920707001d002c503824025024005002c201071658144851a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 345664847 1250 345663597 345663623
    0x10207050d03021605010903020d060f0908030106080402030f03040b040905090c0a0807030b0c0412030c0614010b09040614060304030f050c01051003140f03180a03021801290a050306011b 82
    0xd440c101c0e0a0005d00c42400c1c2a0122071541e00887c14200c501c8200900342951030f40090340c0050310b64044210103800c940340c030744c4070346c0c42d50b6010b801840c003503030160711a20030084070302c42d01c1c40c0000c200c5e4151190b0009030b504003454080c04e20080c210180081e02d19024101800e845a21b40700d81d00002030141300000c3c48a10310b181000e09105001424120010700f081000b4004403803003074172070a0340079131510700740d54041907504200c4020b28038503101640d0f40c1940e000010350703882c81c00d020300f90015003150100700842c1e0340d541c4026003003400c0300401d41008041c4005030104e8000e0302e00d81b0703c5400a091051400203080403841c08c489007141d64407410880030300180144408a0b00498900040600508509080b1035480d41d03a80200d0700781200c458003448000c0055150341c0020700c000c0d54090020752968404407007080c041c0809001d524a40303510300140e882e2030070320038145546103130010071010710707080641c501110141d2000346514180042c0c641042c000b01e00805020391018040c407c41d03480c407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 345666097 1250 345664847 345664873
    0x19150917150a020a1409120d0905030111040e06190306020c03070c060c03020a11030102040e040506061002070f0312031107060603050d0e060f03040501180308070906090b0315010207050d0302 84
    0x1c01d0000e0040c507000c83c03040c00103050341e80d040542c070035400182c00301440e21000c851000841041c0e02c4c02410259008400e403c81405810020080c10f80744118000e2202081400c107880490183e449188084030408021848034101001024042d14003010b9860f08642c17030f82c031020140e07402006060021b0b440000c40b1024810303425083d2000c0c2840f46840b800c00c41c202e480081d078480d441000600003000000485046550035070446005007104880400c0f146001c3c00d24035107500040304c1481c003a021402c44010604c1c4080b07803880503a43c1082d041c980d841e00310f0311458680e110b4800c0c031409155a41007a60626824403001d0007044c1e10580d404224a811494443e00303150b10b4500132018840c0011581ca51943c94805850408940e501d5035622503440e810082d014103440901c4484400031100702105040e4000203180c494889c0b62900d502c6545e80314001c50303248826100e560a442c0d010300100358070303c064074281d030300241c03052048507441615003000800d1410030000450260340082d100d5804 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 345667347 1250 345666097 345666133
    0xc0f180a1d0c03241906120501021308030301320901081609110d020c0115060503010906080a020d110f1005040906050d1a040602160f060b19150917 65
    0x800300b04d07114040c1d032044010100360300241020b8218545c9200020b0300c11010a900d6001e20f0090091098559140d841c9091803130003540036141c80c82010201000119004070000220380c12107040340240402104810740010500f50391a1040c05d8028201054181a9880d401030602900f8910051b00d45086031082c51400d01c1541c1e032000704441d06180003408003056400648445000503400940d0701c040030a5050300400c0460140004c01080c10000304209174048080c50580c0c144100401c5019126900c480d60b0b50a010002944009041d0651002804040300170b0451140540381c1d0089110300303000a025000041c00c0e0400048000c0f604101e82855405900b00801040e03c250515a0080d107546507407400f00410074450844400c0440c08104855048030104500c007184801607100620341120703044002c01d0152101410400081c00d2450000351020311000280c41c2440340b80c0c6004c441010080303142e03010720184100d15800180c51020681004c3d403d052546c050034084058144001c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 345668597 1250 345667347 345667363
    0x3050f0a11010e0703120c0c09050106051c09050703110402120108010c02010c14040603021b010203010f030b01080318131d0106030308071404062114090c0f180a1d0c03 74
    0x43e040e8400c1c0030410110303102e1180b010303c90a035807038404030100b0b0302d09060f1380d40007055002d114050f02d0711000040711035001000d0b04440c080580b0540307010003581c1512058440d5640050030503040144100001900c020b0030320042d040c00703403015003040180b4143e8403010f242640004000c0e510b030359a100d0b02e15420f01c9405a00100f40c217011082909400d00e1420074016070040360b0607d6400141c040c01c4614104030f6207583d10f0351500941d07503580c50703d00703230140500584021910301c440600085114500401980c1a031140d203006440c055000c0d10412070225986040f0000150741d400e2680807014084902144e881034010000c101b0618618000f080920010702010421007030f0002698005002401c8504843e03640ca442804003824200b04a400c01c0e5040c4040c40040c074000725a0758042c000c48907903209881c00c000796040340c481d100070b02c05401b1011140d00c0e400750400031407040c82400140c0454008004920000d8503002105205c8101d4002402e2200144d006001c0b41d0700520f41004550 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 345669847 1250 345668597 345668621
    0x9060b0118060c150b190e011d0703090201120c050903120a02060f091c080403090f050a030803130602211303050304140c04110408011d070b030403050f0a1101 70
    0x207400c052500600030101100303c400100144003a003000d6403a81c910350015410260000d081142c4041d02d4031a04141d400c0b00d11407905c0c030070342040000451600c0c1d0040c0c600c1e84050080700c04090341d20352808400804034040101d05000c4000742e07550b840d030040d20070b00100005a4481694440130107003014503007207068001000620007007110200e026404a07000ba006413450030080c055403909201d90303091100c1070100f1404042ea401c0070f00e11a079400752880380580d01a4540000003030f00c820520032002d42c80d0040c1508500c10a10801c0020031039001182d001000407001c0005401c5a07030742e401a07a015542d00e115960341d20402201d112116a800d9801000102d4030944d445c13034559015000e404000c20103404c0e0a002d41500042810520009407015070040003002142180110710015030014013900425618110085200d052144244140c4030b40e6100188170f00d44c5041c008562070780c001841103003000014008501002c0728840904410718940c4c84200d42c00c094206458210b4482003144 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 345671097 1250 345669847 345669887
    0xa0207140f03070f1118040204050901150b1e040303020a0c0617160201021902010e070512030f16080a03140f041205180d110a05031614010c0609060b01 67
    0x1410705288000200c400701503200f20a08581d400b141002e003103101c0e00011164026000032a80c60030303094000482445076108032001c0010341c036400c41c07041c22a0049009084a1600c00030705002003140400500032100051103074540e00e580d004034120180d086603104501591154180720104041c4000c82e0300070700110f1401011302d100700f000c090a4400f015100c001140d900901c41e8241c82c0c401e40444610100d122b4040d00203c0c51004000e0003031150404811040c090a01c001c241494215a400b04c041c1c06140114240750f08922030200035400408815111240f0005420000340440050314440301192000141500c00c1c42d508025010000c016521040e83c0b0802c210014020800195020403249022a2202c2c84411101e05081601070071a50004c54030100c0c02c200010480e2580c10840b06403140c1500320f9640e0181030f51303034010720031802c00c0704141d51092142c010460086040100149480380080c005074031003d08680c04468140c07121521f44428824950b000044103031008a0241d070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 345672347 1250 345671097 345671113
    0x50309090c030c07020d0303020904140a06090e060606180d0803071218060504080409090c030c06020f100c020c0409050c0306070e0f060d0f050f040b0a0218060d060e0a020714 77
    0x20f0030f480d44110003009202d040c0c400c07086421300d8030903810f51701041006071080102245041038045007030811503005a01a00b81400481c071500c181c0104030b02a502100140111340703410b420022942c00002c910180d40000c44000740b040d942c0c004103458042c0c010140181d0b00d080001e0028044180b0391a02985542488202c0d4516808603180410700c680080000806440314038054111303200ba50b0000701030301e00b031541c8035040c400f0003804181228880c07503e01c00b010341d64103c26a10340044880005980e001003a0b01d61f40518140c10009a0403154816113000048000025003203540c1c0007029034956000d401036603540e040c104503140e006a00b6003000b000c103c010600280100c00559411030040401044032840e196003900080700241c842941031119142402c01c0300d102d10000c4405035402088203011941e1100140f003103900c900c000c02e180c4490112140d052180e9039104c0b200812900342d40d01d000007010303c12156203a0050200800142ea6807440b41444d054001d240030351808140c1241e41 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 345673597 1250 345672347 345672361
    0xa0521100603021b0d050a0210050f0c0c0a020d11010813151d0d0806010f0809060604050402030c0a53030706020703030902130e060a0b060d09050309090c03 69
    0x4032000c5565528026039100c3d6411041030104600341034030125803164442c0c4c2d5000ca03411001400d00d6150950864400c43c0c1c0c0c541c0401e041c3c83c0c0079260040c10101d040e000c200c030035103a0001803840c150369108442e0300d41003a50104464003640c7e4426503024005e01e07050401907a01c06c034541d0b0001f0708003400c0d0500407031546030b41c00300710065003448242540d110750b00369809181604614040004000b600c90400150b600503140c00b004444603800100d01400304400c043c0038960150048108000414035540c0d0362050200500c0050000c1c5c0e810f20990301c20710443ea070703040c0c8ac2501808001070310b0304c1c91340c000030220724481a10002c06003550840c6103410b203079000c01d6240c060042200c000c403040c84900810743c1d94114482c2420141c09180001200000c3c141c02d40c000201e1184203440c2400ca081d65030034000215aa16100c00c2c003607800007000300f185e403c107c0d0005680454002d01091600011300d9900048512101048503240c0003c18204440d02d482c401380b0b1b610100f4080d0a91941c64000c0d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 345674847 1250 345673597 345673621
    0xb0d050f042f0603090a170403201302030a0e0d1407110f0a0b0c06060105040803071101091206060503011407090b130905012301030b0109180b060a0521 67
    0x4103600c0d506180246038500c0b5030007540d0680c2c00e070721409440b20f03540e42800c00c0d9081d00c466501c00c055541102d10500d1601440d41c001c120b80461b0b0700000000210301200f1204800a040c1d0b64425501904101c640d00d6032004c00e200441c0941e8034610300080040785501d1560820150100440500085d40b64042904029408603071003140e00c03040c85200301c2d030000c0000d0102101d4659803600110308140114088140ba030007419000c204804940d41556844011961031040c3d00a0700c65941090044c0c40008220242c401c0301c1120504018070302c41c4d200d100d04241141a59007d85441e03840b0132041101c1e0800b0321800c0000740707020308642601e25044c007000d0302e007030043e100e0003030800d030001484128000d8040340c07a4007400d40c84000744902d507502c2109100c4592407070301e4410b4901d0200c0b0380004035070203845808007000c010384030295040e1410202c0804070404078902100280c4407203807100305644120003000c04847c00d803645a1200c80188805086003010040c3c06580031006041c040f14603a80e03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 345676097 1250 345674847 345674873
    0x1205092a1c0204020408010903050304051207030f0509131a130b060a0c1505010617060103060f0b0906070501020706200405030705041d0a150e031206280b0d050f04 72
    0x200703901d01d0341032403010074000c1c0304580c0201d03955480c102d9000101035001c4011800b443c040c0d81101c12000d46640170003102d105450000300410202d01c00580214044c4000d0000c5400c010282150342001281c20800d031000c0120b100b03031900c1c4040409072a4034050744030101d040c140520030825403003103a001c03c0e028481c00c0940003d010300710712500c04000d0030002e210031b01e00d0300000a0005503520040900b980c0e1004910b160b030b421000d000074607107500c2440b07403030226111002c120b410f451070401000e8055000304191504060b0800803040864002d00040c941e251248000140c2c241d2042c5400c40d14407402c200402c1c18207404c000c100300071b40c3c0008103072058420071140029000703030140002c00d5400088074803c01600030411030b01e081c000900903182040070302c45810300803050320030304c80c7d903d074414000b0282e1030040d20340208295050144c40074001005c81d2402d9103603444106042c0b619008594400c100d26500001d00441c612070a000b51900003400c80f850311507908007581e170020030b200c0d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 345677347 1250 345676097 345676129
    0x30c0108060a0b0c01091101170103030807050705011a030105090d08150f0d030f110a030804080a0504030c0b03090c040504050a060510090c02011a0a241205092a 71
    0x400c8085091940d032a00e0200080c404028281d50782c0310150401c03406440200b205035102a000980c00c13490794020005030000d00071b461608011607003140c1e42a1107c06000e0545010400c05010080c0019802d2054626034280d28100b0f0400c0e0940c1810142903820090800c0c481c0d41100c00d1400c0300d643c10003c00c9401c210014a8903820b03130b0340600403408103c041c464840e070104c1c8070b00c80341040c0354000d9070004842d841651075600d40509145c0c41640e03a584045d0044c0064089000200402e0488024040301140c514016251a0b40c2c5e48951414000c0c03a00042e9040c0c42c00030901501c00000c0048400e443c8080d9030600440c81c003038175001d0320f403462400040c10302622a40010704c0501c19603500e00281550f44030400840d288504028000d0468175174612213620300368a0b0010624009444034110740300d0480140324000c801045001c0740440b0042d140c140080445050301e810194080c1c1d03441080c100c0001d100030b81e075142d0f480e80f0350506210445407481540740e8011650311002c030f2051000d00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 345678597 1250 345677347 345677357
    0x30203060303070206040b0307090e01050f01050d090803010e01080708122a1605040509010207080a121517100e030a0e01140a03090b1608070e040e06250905030c01 72
    0x9180d901082c214816500025488080001c0220307044040308003840c02158603a03035041089803100011021813901780100750744403180ca000d1707a91641c801d200805140c1c904103400300302060039503a2448150801c0e00a0910807a00800500c0350034402c01c4483e000b45000c000405403c20864a40b0100d4401c404801422289100035031010200e500715542268100104480b86410000c101004055075030291b24400c030b06001c00701d036010b0414002c3c1c58a030754015660900c0d1103150792060b160107000c0040e04003c1c0d0740310300c1c24440b0001c040c4049001041001c4c8070f0f00c0b03421101c0040e2810401d1120050302294039101c410b1090300d00c0042070f03807540141810b11f50188442e01d40141d64102000d5030840e0310003800900804059810740000c0d14031481426001160f481e00700004284905003040c60000440c0c8500040d540b0303106817501c40d003500c0007900016015907030152503801c0201c22a10610560028690744405072a180080041281c1074600b141c0003900300000240c4542c007068003581041 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 345679847 1250 345678597 345678601
    0x1203090a14030313090507020f010b030304090c0c0b0703050604052d070314090d1403040b070815060a030b010e0a0b03060d170c010b040609020906030612010204120503090a120b07030203 82
    0x902c0820440ba000c00e4030414600c1d0880d80c2c0c015040240500b03c46440050145039410b400e604014041d26502d22802006141030031b00b03000c6082d000382100c544801c2046150802c650100d01c1c800c030403500401003640c02042d10304d00081440b0036100b0141540006001c1c40d58410b24010b41d4456200480d1240070a01e5074640383d901d012805401c03a00a41c040000c0c00c2c009001d2000000980000c428074607880e0360007440030b100c0510000e800225400303031503140b82c075000071010f910545241d94848641180364030361802041c040754075900030401ca040843e5403005840700750342c3c111101d901c0e5844210340c040403581c10000c101c0040d010290025001d00c0304a400d2500300030840c405203034071f80004514141c44401803001c0ca40a0000078800300e00452404401003940541402102d42c12100500500d01e142c0302c010500c4005584562000300380e5509100200341c2d11540d107161000e043c0070364000c41e1a544141c0c00c010030084154400c401046091240c030002508000701e8503403000141c2001a01ca03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 345681097 1250 345679847 345679849
    0x80d1b030c15021303020f0102030309030d020d11212d04020d050a08120109020f0a18050303040b0417060112030c0302070f0306020d1a0f040b06070f050105061203090a14 75
    0x4220b42621118040d40082460b1150442c0c5481c1d02046a00803600c007464459680010380e260b12040d00c0c07284903a0400c0159030b141c056942c0081c103896140d1200080c2410100c940c840041e0050155403080070b803070702d9020391683e0140b000c650304841454401c03103840b4003244541000b2800001810040c4440720000340c255590401c00e004065040816910f0151103072034200010b07480103100640c0c001500e4008503190741548217940491102540c013524100403404259185a07034803024840805d0b03003040c0413985460034000380008080749454941c880c3d0400001c1e032860310748401840303040e600200041040d80c2680503100031040e018201142041c81c0307424105e0030700f00660400311610000030800000c002d050303030041402c8002c2400030008004a00085c2d0050990308900729400321441c8900360191800e5405140c850500034074141c50468280e88000186155203c1038440c0c0c2d42d104100092418042003101c00d60310410082d40c900300c00d80f00002c0c5182001e010340e50321041899245c1d082 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 345682347 1250 345681097 345681113
    0x302180f031c030b04021612050c0d11250510080c0a030b0a0801050f0403080906061f0e1203040e070c0f0f06020f030411030d0509210c0d0c080d1b030c 67
    0x1948024000390360729500112500483d0314012030440e80e007030740d41c008c000500c1d200c0c2c41903590348803494029140c0000e05050803600303003007424620031007130107460011604480000d0545140d07807243c030f8510046ea0303e0882001034080703841034000c042c01400d80810594203050802c55903614064180010181400c201052003912140c111154075031030441440110b4802104003403040d8880e0b55403214030303950042515100c50041e51407130f4000317801040034100034032806210b0144881d41e10b0300e003002c01419800110b220307159100728680c9400c000340c1401205414201c0c2a40f00e1041c7c100710031908a00c0d910342070300141002010b0b0071064903d081400b08103203a0121501c2040d0341080540324101070428803560402d80340a14403a10880c02090b8140307000d803050328044040180100c020182d0341d006107a405a45e11700c0003401c0d0282c481070348805c1d0744140c14015083e02900c91076410380e0034108614548440302c030071320041c00fa010040c0780c1c404070040f1341510190ba1501d002c1c07503230a40602e000743c9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 345683453 1106 345682347 345682361
    0x3a0c05031602280203101509110d1136011d03031c0608060c0a050705120c030705120f030103021005040504020301060302180f031c03 59
    0x4070505050307101c1c002600075401035aa521002600ea442c9440c007051030260702d50058007540d801d43c1002c0000c514012001d140c108605a294408020b04410610618841d60b80761181c01c51042000016529003001e52030007444040c0400e8400700701030b0004403090061002044a403030545c40e040f01c045d07410006c040310202412480350011900c1d020004203042c8940402c42d45c2001a4400b00020320388400395070b800780316000c02d04200700156102c1e07511444141d48080e06015061102404507040913045090071a560340240c50041d081c0f80092180d210b8401021400e00308560000c4001d001d024824810b40303200740303c0101d103115035001e50f100e0202031010600041c001800d01030500020340e5501e040c07040c20315541e240014141e9000f6000100003e4011800d00f00360713940c002500203000001c07503140d40b002c0050300109503200803515010404000084007000f841c3d00a030310001c = true := by decide +kernel

theorem cover : BRFrame.Cov 345503597 345683453 := by
  have h0 := BRFrame.cov_init 345503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 345503597 ≤ n) (h2 : n < 345683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
