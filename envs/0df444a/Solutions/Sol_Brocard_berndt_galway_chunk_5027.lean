-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5027
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:30:20.289499+00:00
-- url     : https://prove2.me/submissions/fa28a46c-13fe-4927-be64-e680d3db0ed5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 903956834 ≤ n < 904136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 903958084 1250 903956834 903956843
    0x111030711040b041b08090a050a0c030203070602030c031c060305160609090c09120c051f0305010611100c05190305010302040b030a241d010516030c0e1903 69
    0x56400e00d03454000390186115607010302540c00d10390110500d140500459064085c040718410a0f03009200040310300d1000908003040c240141c44c3c042000c40c106103c0045e04034002c2d083d0865035451441031514204140c2e00623030854105110300c501511000c012111141030003203092036403180703c82124000304038a5000600b03c2c4181001c1c6411500480180f0049504945401050940e502d11080654640d901c070140054110b040078004100200144082c0c940200e90740d504003034461000c240180d6980300c500d143e641c01040d5100c42c05a060240c0c4e800740c402d03841c02114002c00400780c07640d01c0c22500091152107440d00000303a070040c465021b0310300904a41c1d1410245601900c00074008010a02050340900e0a1010503143c0d4200000c0da0584241d02c01c89002003400c404540350082d4062600044101b0b883c0e44424401101c0305c10003982601c00c0324000205402d055080009514019003403005040c1082c0840c0c001c5a00305244646007001600d01001d0703400500000c2e21500380300c1c1c00042 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 903959334 1250 903958084 903958087
    0x3120619080f07050f060715180f1e1e03030f0606050408070b07080702130216110907020a020609040f0b09070507030216030206031909020907030509011a1e011103 72
    0x15103844000b449106058603101a40d040c1a01c074001d008000da02c0326000c60300030300100310810000b00100e189090300880200c0c0000c58001103010b0b50f000c850080d20070744130300c3c0040e042c0b00e051102450381244000c0000001c044540c0b004c2c0c0d9200c00310030703100b504035a400d0b4200c04002c5c14036006e50440300f800a10780d6010807915454600142254005019000070341c0304000012800b044d024003120000754001c80c40c0d6040208036800c004141003050304402185400380300011b0480303140c4110307120151003035909180481142c41402003c250062120701190701c04614030000d41c0f244021510310400580e000304908944116007000f80c51141816030f00444e03620104540c1940c040b0251009074403a80c00c0e50305201a01615860085090001030341c801403c00224441d0843d400c41c4a14a03c10f17114040b81c0314000d500082c0c0c4101045840d1000700f41c4900c1000804e41081c0300b070401c0c59010344805190140411701242d030a0703022240040264006590080d5503a006029135204100c0c11003c6a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 903960584 1250 903959334 903959339
    0x40b0301060e18010e030d0b0102100e0c13090b180c0d050c0102060c040b04050f181323060a0b04110a0203041806321203091c0503120619 61
    0x40300803481c200c03400e041d8402d01c202c540f126150107000300d0503081a00c00055062500c40503031040240000710504d41503110301c1c00c2c3c540ca0300140380201090052084d01810418148805000082e849010000f2081e460001204005003d042081c0e8028000810070b840d03240c55105407030328110f482d40aa82c3c0c090f00074000941007250028038420703044021381c02d8640e16100d00004079414040c6000b030b940b181400f80001d0200c1d041c82080400041b0004005621807069100498008801660301190551044c001c00c010b00640322a0f801070801088c600702010005400c1d0191580805080c040d00940c40f140100841e640702d421103881a0074100b5020358560044202a50f03a6202e032080e545609100101d0001c0740400b846400215050451411a0100b000e00c411002880b201d5164000c030300c440c02c10700644d0f1101c00c0c2d000c0d0301201c0b010046599070760380b80c01c01c81d01c1c201034055400204030b00c440c0c107000140c011050b641488100024020383e03849540000d61010002e00b440020411440e800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 903961834 1250 903960584 903960599
    0x1050d0b0406120506061e09130f0606080d03060b031902070c081504060b010e010c080c070b1903060909020f130b030102121611060c160204020f0a12050f01090b040b030106 76
    0x100d0203180200c40c050b0140130011f0314030100210b0000c1040d808048400010842e852601c014048184070b1421000104060f507101800c4840b0713a004050f00d540075502d002042d54240c4511005454105080c0d811460300140c1c0d012007031411410b20301c01d660003155000c10000c00001d10000b0b00082820358841c01c4807030482001420003160241e404d0342c04e00c1f41d440700c030354010740b00340e0030030031043c1d490115510568031031650745ea00c036642c8801c0074031500000041001e542030144c0096a2642c446840443d41d2501c010195201c642081400d503142500640050342c40c1c0640c00700d1214203880c0400e5184404080c0701c010310ba802ca000c2d801d54000540d500280019000c0c41c0e12440807940701c0c02617048155000c9414052540c0d1501d0203602000204601755003030006429400b02c00d5146e4000300d403241c0d0118060f42c000c00c00208d50b00202007500d0301c680350407400c03000c1c40c588441401c00c020302e03090046030381c4901c0612035039503035690306c100101042c5c945411400b2004e41c040c0003408203a94500d80c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 903963084 1250 903961834 903961843
    0xc030503130915030209040213051f0603060f2603030a09120201020711040f060f1502010c05160305070c0b13170d05071b0503100e07050f01050d0b04061205 69
    0x1d550342607124030701003504061881940100d0080580b540c14143c01c5a081c000384080250060341e011440c1300101c18030403014000e00e4441c0f088400800d984a6084400303000c511019004002414201003052000c0d1004601c07078000c0382c110071050301e60700e0302c0c044242441a100c2582d0700803902001040046a10540c1c01c0101c82c0c900c205429140341d500320f00100c0c02c038000d031034004140d404070041c0010f10f85000d40100c00911540c420004149544141c0004421900e0f03021403a5100901743c100d41094080c13045038607c04160604528240d800766070581c0e80501c41c00c00070705018010a0020a00440000c540c02130203004511035591580c001c1c0300410342189204032111020480c115002c01c09000c01c9090f803d1800b0349549041451307507910000e03040340031506140d400003e000000740c15580ac114040d100b074150307000001c000308030100e1141003c889421042c096022641805000d076404402c40d00035152006001030b82509000005000e040701d940f0504030b65404204c9001400f2001c034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 903964334 1250 903963084 903963097
    0x90b06071121120901091505070b060a0902040311090703090b0a112b0c020714150f2d0703050301031b03081b15060604060c03020a0602161520160c030503 68
    0x6c0b2001040c60b035501342000d02d001c9014840002800901103000002d1120070240d802c440d00401700e0810710749602c404400c0341c00541c41600c1e8038090301c20203066800c00d0300f1102e40002e0340d442e040c00756611036112442c1201001c4d200980d103e5031041c6001c0101070000954450b8190000002d4190280715201c0480b28071003c0b0341707801c40785031104080304603000040070400c0740e60720120302d040259071394108962030000080029280e40c0400507500d1805032034004000c840004010130820f02103418095011041d061030200c501c8000b0000000403980002c15241113076806407540510b121103a01c601165203a0350300c010011100451a140e0100010031407185c50b043c2c903030449504400c050a00007400b0000e640080d04410300300020721825200340e00b40110070380039004503255a55150341d9102240d0044c0c50008500e0301c8218844200030081042450307000c1030100601100500d0805054030b645524242400020005002046142c041d841c1038003050700404280300e0659a4100326489602c101d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 903965584 1250 903964334 903964337
    0x140f070510023d050f0a0c030e0a0c1502030301030203060c0c2d0c09010f060f05120108060703050105010201142802030c0a091712090105120a06090b06071121120901 73
    0x420008120074404d00c210351207404201e20010807a00c401d11450020007aa00c0340c0001c264a03510254480807040000b000303014030424881c80403a242c80044528410841001001c54104000400140e5400a000c2c0e400c440103120030307551100e000c1800c0c3c0c80c00108038070095000b0609004140c13407107a410701001b00088540142e94807603868030304202521400b40580d09110111050a0061911600184040b580c080c10120300d440c0c00706541d0340003c1da00f64001401c0741c2c45442040000d40d0315000e210300603d0280001d000e03e083c1c091135402c05d07a0300180304070004811510104642640c100e0100221000c40f1401c66407824403100d00b51059201c8a030301c90110303000001c0040c482d204e9480810039840b103031000e45690301001c2030105966111210990410106000d03441c0c0600341ea0026500444520100240c4949841102c100342ca00c503491861040e6401d0280c4070204110b41c442c11245a401c54440007082c40c0c5040c0b20078902c2d5055640708851160000c03881c41c1c0180c0c40c004100c441001d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 903966834 1250 903965584 903965683
    0x30e0a05120a1101090501020703261b010c050405010e120111070807060c05090d062a0507021302040f0e0a0f0e0a17182713140f07051002 61
    0xf001c00650345045a846a140164061001000801c45280a0510585541040b20250240c14280e496282c2018038540219407160440e8506003409210717003001ca0a56003840307070070036150000217401c408652040c60f006901c22042c0c075807180303401e5010411800410300d4450312440c0c58200030001d500110821070310300d031502c44440d141501460030f880405400500c036468102c0c3c0c0d65150406005045071101ca4814071182c0c209040780101c00340003818460342d450640300c0e449401008680b94420b1900c01c2494030404c0280310005881103030030280c81c1c60740340102c010388035070701c0050003003642d50746404809191582c0d210b0a020701080c86007045010b000c000d4034000440ca00860341d403090b00705100c105880140f9000030f50403c1180841003060081240305800701040980001c00421152441c6e1107001c22a80010004004e0300700808a14400040074141603240e00a65500f42901540c1d2087c0011140c22402c94800c0000c514059100b5a40c21b104005040185528074540c00e0681c00d84400c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 903968084 1250 903966834 903966863
    0x20f13023c1b0307030c03030b0d081e0d02040b19140301060c1a0108030307031109130b19060e10031b0503070314010806011d01060c030e0a05120a 65
    0xa5092014006003050a204039103203002815511141c0c0c0288940341500000c102c40342c007800c0c01480a011910f02039261004540d80c82d1400a04036900c141446100300340441c0303104042010841a1190252402604040c0c2d02c1c214420140324003541b0713444140c4a00000300810f200c0954000b0b0902d51500b40c44038201c140c407550040d21150310305d440e264000744050004002551160080c1d104060080f1407049190701e040400c2803203500d098101614a500c0003091080c5941d06100355401c1a0390070041508005024000440b242d034030201078110540c41d01a110380c09d5a80140840034014050701d9200b42940d9807038050300892294003403900c601204c242d504200740c060701030aaa52681815180c0a00341c10240984464002030100403c0580c1c60200c50400d14802c2801400707172107100c004189a61403ca444201443d941a01c0c04c0c040039501d004220403508140364000e615810709004000f40741c440d012a0080e10554001d952051910b9502c3d141600d010900e1101d49000c0c0140820713524 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 903969334 1250 903968084 903968137
    0x510052410111b04180b0a0b060702090a0515030724110a0b010305010f0504050a121206030309030c06020f06010905060415150e270907080109030831020607020f1302 73
    0x200c925001401b021405000034540401c2c81c0e10a44008000038482c3d41071030b070036802180615400701d9201c500c160340d5906000c141a40e040344209145000c40040031035a00b00440840c038032440080350030b640321034400c100100c24012240703942c0450110003194114909030801415410302032000b951603510740440000588454000c00c0e21840e08a0000c20010710135a0303509410100700e550b01401c201d007405810b00c80c0c1c20b090094400842c040d40c0d034050850b04509004640b003550303912500644d402601e0001e00c001012404c0d604643c025130000071190303200303400700780908a40c85540c10300c00b0030030710045410010005110002c2d05555105404d042304041441060b200301600e076100c400008d01c88071001c41840c2401540104100203440c2e10704c0d80e54800d07600717440e480c200031070224850700104071129560041c4050421107003507000b040395600040800041c2041031019000e118000303100c1d001d41d11640d2041014440140c40c03900320340c14191094000350010f003006209090101d051000c040d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 903970584 1250 903969334 903969371
    0x8090601060e0108070309020405013005210706021306020f1203010b1303210212090117130b24010302070b0c030916030510052410111b04 61
    0x8078025100c2100301c403485001034030369400050000741015150103203480103840c3d07409001d0007032a1004c0055425008005a4200780310020700303403204001c2c034043e50030104100080e240380d0300d0003403a21404500c503000244c4105115015025251500006102e00d542c0c0f00d06485e8400c66030503600392102042c10840c429262111501004405102800140710b210300b4403004100141a84041400140c4d40e569200d208260380410506580d85d400d4801e80e0f441e0b014498598030600103200d051038504042d002901c64040b071101002c1d052550800240024816408228059080040003825141c030103184a400c0c141002d4090000920295000c103e5002e4002d6450107a413103812005669540c408050480d08010f1041116204015510b9460703000c1d19000c0300514028400340446101c0c02c01901d0664001405c003c046c521701c64040061042d00040072400402d0032030f8000144a241c2804859840b074074404a402c501076071064002c0c0000d03200c0050b808041c240d0782800741d6030000c80c090000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 903971834 1250 903970584 903970589
    0x13050901150f030507050c0709050a110c0a08071416080c030a11040b0f1206060a0e04030507060903051b0a121b031b0f0305070204110f07022b05070608090601 70
    0x2c5440180300041150098000c1e6901002602d492424801040c500754601a419440040c0540e82c0b0402d201559240d07000340601100041d42032480c10240c00c0aa42d90f50130300e0403000d88004004130700c0004005001c0b01404407001ea10044501c180381020007049611801d01c9420030500c907140310a4110700b0045460039907075130410b8020788082d68a9050101a09101c000c0035030104e00103c10304400d640b03100d1204c244c005103600400301403904005101102032180c1280c00d850000300c0400c000298840126080c981e804180420000751529081c1d1b4140036000c1440080383e0a2052201c1d500303000119600a94010040c4160109040d00c0139228101040c0309950a0f564003011000881c1c01a002080d1003040031019810704031454030707040301c1030310f8010040b40042d03000a0b2071420361030503000c0c0c0c030b030300da0a0910028640b0b8260f80486955209101000380100d40081c03000e07641184606850142000e00e801d02101c1c0c98a038a0907a0b181d0040d07004a401040d240c0c4003241c2d8481000411505 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 903973084 1250 903971834 903971837
    0x103050f100b0640092a0e010e0418170c0604020d080c0102271905010c05070302030604030c03020607030605060406080414100b1c0b01052101021305090115 69
    0x141140d00b5042c6469401e40078001041280c400120041102c8680103030313400540c0c0800c203103041a0074904c040701a505868018a420501c02c40c0c0701c0c4a40340c0b6540d10f841441c80a050100c0c49107007c03170061710444801c031501580a45800c50010301c0c041c1407d0703c1c03401544680c56031a80006541409086030080720010a2141d0100340010f0040c20242c100400540c00792600324100b61149403d80c7c203aa00801c0452406034481c0c480e0450a5400c0303140310b070b9011046030b0301103060b0b0882d403400d45508800d100f90342c104284440715009200040c020a0047c68001d820f0b51f1030741c502810064503031179110004500610880000801861081c41400143c840080010345440e141c002c00715031054001e4016200f040042424403102c80040005a01da104441c8000c503012198070101703c850004281d201400e001030110780e1000618070401541595002c5400390050400e0350803840300d44910014409146d807000680c03980c85020500440120f5904031505040d580e2150710390f01000a030207a1550 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 903974334 1250 903973084 903973087
    0x102a0804150203130602071523030a09050f0106140a080a060f060e10050a060e01210b13050a060909110d061130011503090f06050103050f100b06 64
    0x300544400d020044028507500c11203041002d99a502d80419503144d003d203015a21410b0104030011442e4002c800c00415401c141c00e144d1020054810307228040d02c4d2100034600000000703032800c1400e902c11460241c005084884c2e00c034400030094024226401200740440c0048604201407070f0010008003528400350107401c5803e03481c0e40b040c000d45242d0006007541600c994010030a0301d8584142c80c8208071308040c450000c1d2508050108001042d0858410050f8a00807483e02e82d81050400780a40e44d1200341340910b01501190788000e0080c0711207281e0140003550103c921221030340010340200d07203042c0b0802020740d40300309103c1191818030b401080d110340340c0e401b64102c0c5450003e44405600803000860109000d0190006030392000000d07480040206104062400b910541d85580e110030324098511541481212000d0111055501c010142c45141030020003003120814440c040d4054020720055031a403400035142c2564001018036445a103281c110054403e0150b0681c42e40f018144a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 903975584 1250 903974334 903974339
    0x602010f111e0703030204030b07030c080c040f12060f14150102070e0f13120203120603070b040e041401020403031e02070623190c050607020303010501080f0a0b102a0804 75
    0x96402e40c000c1c0340d041d424941c1c01d00000000c1120b10b41841c1c4039810036075000401f800400c001420025019081401c440018030082c40325a0036104404150f4000008014048001d40f61201c0500424425122141d0030100714800d1480d82d440c0e414021243c5410100c07400c0010303001242e9914462180e00c004602c91004503880e041440300c1c03142c1000c00d800200080449580b200c503401b020304419a40141d000064185405500c5815650060f03401c50240090600e0108100d42c00c0c01540160402c4480d401c001c201040628920030001d81c001000039525250749040c0603004010122807008084901c00582c90600d102145210559226846d4008400d10000d00c00d50004a100e808082c0d0b80800c120146500b00c0b608098540804030b5500d030043c0c52110700e042410101c002e8004000c0d540284014003941c2c2c0c0200c000c0c1e0b131218503001d48228079600c80b80702c2030103014200405500402030003180c0d04030680c01051035481c10440c04014400c41440108801e148044907005040007000b807206 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 903976834 1250 903975584 903975637
    0xc1b0a06140a030906090c030b1807050d12090e15090c09010207090c020705092502070303050306090a092a08070503190c1e050405010603020a080f040314040602010f11 74
    0x41d4010318007802d80006c4180884e0f40350305040b4802d0b00292203030740d1008100421420081034000c5101254005800d013980b502c80400d0260407400310040c07241740350402c8500c00d24440c544040042011004501480c14202d00421400c80701c880b203c0e0041c3d5800300003a580d0907403002107640410040e4000c000283c07030015604000e0450030142d0007103010303a903c005a10307518910020f002c2e03070000302d000340c003c0410315080c002049114220829500401c030200007082d044403c0c1c0c1d501c10f0f0305070785186055491081030300c01441e58810041142e50101d030b08086d81c00d40714091155030003181c0341e000300303c0d510f4202035992000d007482460b5142d03101c0d0a00700c4401107842e428260781032050003660343e5503481d0502c6032500b064100d400b542101c07000710100b01c43d01d003e000e180d00500080c107086252030f4801d03000a02d00d1400914002034200d0210200702010700c5449604889806000b4068a454417000001c0c040e0401204041c02c483c240f4800c8440104040100c0303c0e144410010800001d040615 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 903978084 1250 903976834 903976841
    0x50d05031302090a061d0a15030312110f040605070c090b03120c121b07230f01020708011a0a0e09070e090c150d0f060806010909080c1b0a06140a03 65
    0x34005106448000008040101b0000e03031454108100340c0301010b00d016104a0201c980c0904110710f520340000702000400d811080010a0001c0024013040d05070664400051074400d0041301e04000f40b001800146166000d8040c1c0007243c0320784e01030780c070103559100003905455029076a00d504d5000074000d040c4103240c0c0c600410a0344000c400b0394111070040c280c070700c01c41e0b04111400340c00d02400300f01b00c580e003110904c02031020300300c0c5200c64034031054001c4084a5030f211440d29540683c519601010301c80e8000c002e00c0b401028050003d00000450003413018a030078400482170302807948902d010801c04883c0b001c9920640c06600204000b034501103540c0b54041c00604006e40600500240c0303055a1140d0189203820808000580ea0b0303120301d1a5071a0032200243d074814103161800c8801d01c0600e802203042411100d481c10042030581c4d041c00c104c0403501c034686520300c80c3d00c0303114484a01442100080c1d60b0b00003045802c00802a5030b00740c140c3c0c0d00d2910848561175503508000444415000381d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 903979334 1250 903978084 903978091
    0x130902090a0605030714040b030d02150a051b0f0d1d010c0306030f080a090b0c010515010507171c05010f0305061e040b070c050d0206010806070f09141c0609050d0503130209 76
    0x804c003241c1e021a0384040ac0c14082080031346401a044004200d040c0c528920700d058100700c1c41817080045103030240616607500310011200e200302c0030005204040036401804d0f112410444901045200030900200403a40072200c0e40c2ca41c0c950a002400c008107001340b1841003204d42091180d4850881076039601120742c4903411004c1446107440b00410030010702005000e003103074801700008407424140890b139804408062641c5c10804100240e01c0080c0d052a4291a00038400c0595a00c8040000125100b20402e800d000030180c500800021a0070714030401c04110f03401042615104d8460f242d11442c4101000044400c50b803261010800203006a191590300001c03e180035000640740e039448908081110010b080140e2288005101386402480304641000c2c036030034200000c003000c003c045c3c18080d440c40744030080b0001d001c05a2140e200e4045401e03c0b1607880ca100c5440000a2809000500740300d10150798a00c940034450840900070030482e8020208006045880034480d804c2204203c0d004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 903980584 1250 903979334 903979339
    0x30b01091d0f0615070602030603010b0409120c06061205100b040c21060e0a050f0115091806030c081c09030c15030905010e011a0405270c130902090a0605030714 71
    0xf281d101a0322981901170300600788104070250781c1e424036004060940340c01c0e0034002e00c110701c2c00090a00023500a000c0c41203082c550700300f240c641e14003400c5c583c0c0113100592001000e025404042e204111b000320300060714011558082011070044001d22040321103031004040032031440c0e04070328040c43c1559000c03030302c0107082000841c000340c035810740c1c165514041d00c2105100d81c80b0014001e507031402140d0540544542003455a0711400e501d0001d1401c080d92140052072480040140d040344900d40142015580094090918035540e0070190707a01e5454106429240c1c07144440d1342c09a6114070840c0040b203800002907000fa508080400c0c03c0c24110700009001c2c540d07254100c000107503003030146480440180f4000590702c0804140304046000070b428892187d0f01d4070f0b082042c000310001d003002800400002e61455100119005481d03d00c034006410b60060109110050100c0c1c950060300c002442030340d00c07c1107070300c0300c1d0908402c0d204540034050b81600314400600c40780c9907007440d0f0642100e00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 903981834 1250 903980584 903980599
    0x9050c030c130909081206010806060d0e0a020a1d0726060409060906020a020d03090210080601111b1c050604060b0a0f0b030915070801031101120507030b01091d0f06 73
    0x143e004000403520b180781e048401d054040313260140b03828216451079200f6001e0800001074503220700000c0081c8100181104515510942e600c80c900040146851b000d5002d007401140c6521000070010301403150390030204900e456000107100030703c6048034981303a0100b242128103034408140c01c5802c01400410180d00b00f582d8550060100d0701342d014400b40706000b00001690f40d82540c400a06002404a8440c241800c0108000040c2c841217103003581e880c0c2915007408646c407444012100b503c0407110710308061042c0130ba01428904042c0781c050101d0380490740c0035606035002007004182404410301810b81d03001000080c0c046101c40c0c00141d1034000041122620607100e0100c17007040c0b600c541120000c0400841003150100d0b040210024803055034084c100c2519004900070403000c41404000c0c030507003100f16044032a9004030705503115590099010700c502d01d0300c0e060040042c0054401c460002d104807c001815407034002240e92444640920030380b495032007054000c00201c02820040c0c11074007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 903983084 1250 903981834 903981839
    0xa0207110910050a06020102121602390904050d0f050f04030c1d160c06021317060105060c070b070206070f0506011a130e0a06091e0609050c030c13 65
    0x1107540405100302201c1000900c0c1038141000d01c8a80c810640194081da0310421034111502c40e0b03010059031100c180c0c0e07541e05c0001c0549030120300342040d820f00d0f03038003001c06410210210f054804c4000403580c0c40083d200030344498902000002441503501900a802020320724008a108080c80c5502d01c0035400e03c00d280542581440d19140d20a81c4143d85c0320844407418854200384ccd4142903040c004100025503c0d0411004200c214424282d000050003144030702c480c10485240c06a80e001d81c00141c03030440166075000b42c5261040f81e91714206d510701400001041c5454002c0c10741d4080740025009052107401c00400085961142c00c00ba070f4003138014403402c1c00080350042e180c01c88622890140000394500558100700d04045035038010004c005000e02024490040c2c1c40d5000c8a024022422007519003044100060000d504900c400c01d0400700c03050840c00314044900300104159200308040c541d00c8500e10100c44080da040300907041e0400100c0c170300012560140440c0c0320754050741403400350b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 903984334 1250 903983084 903983089
    0x120402030f10021e130b030a0b04050a06031112030919080109030e0a140915190306060611030301030c0b0f0c100f06060302070c06081b0d05060f03070305060a020711 73
    0x115104074440115400041030ba100000383d0240246000c0c004091500340801510761784d034200041d0040c040c8061003c80060480301058100b00d06441019008124030b05141800b2005401c16001c00c3d1b95107039040c044110141800d05050320350700c1021001e1800d00c2c49200070001807070b400f04030401c00c840d181c0d100806c416400384641070358244692181400e001800302030020f20756199200e00003540d00c8003010440390b1521040b9980c403174038422030712000e0030300c0d81c0014070741842c520001c0c5900035001c040801003001940c441e9007601d10300d440b40901c0302404a0f0895480c03009010060a030048550200008400400506010765035121224200b092400140c0d18048000c128103403810380f640d5402001103400e00c1036201600c00f51800f075150900985a081455000e417050801304a048800218100725503002100029008030f82d1030340c0d501c4032410003c003030700c02035940d00c2c450015406005070394a00060003608480c5e014002c1d003100e40c2e640350680029040031200f6650f10703861080141196 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 903985584 1250 903984334 903984343
    0x10207061b0e0d0c03080f04080d0905010e1507060902031507020115052d060f0a02071403060402030a111f0c120302092407062a0311120402030f 64
    0x1035019507001400359080c5500030954644048524014080c116468010030089140041504d0700915101e42d1400c03003261004062040e90b1115001d8002ca5110540310390317014003500215042640c440c1c3c5901206020480326003001c4600b948442806c010500009080d50040300034940000c0a440280418402c80c2c00350031001caa2000050751b460803245403c06070320841350042e0006444551440c945424282c030403848040103100304042543c01c0280e0350761014116070300306004003506a03c81022002c0a903442d0034030b000d52107140300c41b0441c3e040b4504000a01912035074005000384050b2145441d050411203480b40c400d82c00c00e098880161000000c21901d854454066549612074412410310b60101d0014040b04c504146c010010100c4030b0741c648820322456505201212014030b100d15045520384100c00c8018251420700074003000e204441c0050100d00341070186107483c4030784c00c030408034221890414501d60105040c45050303030081d00c098016610610140464100042d842d03e881d00c0c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 903986834 1250 903985584 903985601
    0xd0b04050609071e090e0c120c130209010207030312270b0f1005061b06070915140a050715050a051f030b01050409080f040f0306050c0a08011701020706 67
    0x159449078050007542801003210b10020300d4013006070040e2207204900507503c118180720384500603845012010f6015014424200311000c002c02c0300f5034448120f000a5111510300c4402e61040103101d40c0c02c0c0400b01107000301c0310841d0701640500080d50455406503042030740301d81000c010681e138140b039485070303e20344076011341021541400514507050b5142c80c0701e070010001c00c40c00c0c80c030207050284403818403120152000d450088031600c0c0c54003015040112030038132069803020503114030000e0040c0c2d2500502868180c8608680ca84840031311400300b41da00100707000711210290000c01034107640c14410302c042d0105500c61010313100450000d20b052000d40e5402d8555042450f903a009001c1451311482c942d106070a04013410241e042d1540d02c4035181c1103014801c00b801240c4031006902084860b408036200f0300f88030001e15440d592509410400080d041c0000c40d0750350301c0c2c100850040601070003500d0a030b0140c2d41d5612401da0810140b160701c1c541d000c0580b216590284141000a007842c0500c1a2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 903988084 1250 903986834 903986843
    0x709080f060609072613080409140606120109110706020a0305060423010b03070306030221101e0e030f0f030f010e010b0a032d0c030b010503090c09060d0b04 69
    0x7000d080c29020022249006401202030007030b501c031441803074207000c10400c283c41c0000c140c400d1155104040c0b081d00503d071203401030407804002400319544030151b100c500140100911000a0385e11030080c45694450340110307251b283c0300c03c001000b009105030480c520000c01019094188841c554610003a600440110310100380c07501c0420925007424401c030780090230b030300c40015001300340318600c0b0002103c1806600701c0080008001903289019810590045038058611082512860200c000c184810100d0000342e000c0d4052642c12041e0500a211031b0103521642d1481c0001020003046c01810240407414140c00107200082c00c50707503030750003403c0d40c0321008074400c3d034a140c4071030b0001c150341e01604190b000c850303441c0050101030030440650b01000540c2c00c0c000303100c118280da011810740240b507090107443c0351101e80e2030383d22049400544031150300ba06c09100711582c180064999000031601b1503481e5104032808246450f00e5510345801040241913400c03074032400c1e06d42001c1107408440558 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 903989334 1250 903988084 903988093
    0x1205120f09040e0d09030303020714030403140625050a0908120702010e061e1608040303050a030f09050303160512040c0f060c0b01050907111005220c0e0709080f 71
    0x100d801c00f4025200a0502c000103480b2501c0c003070340054034011032400054100341d400700f1168208008042e420381c01c100c150302241e031240d50300c0c58203190504003800b408403030340550700c08220302e00405180001400490f412030a1a940010b034222400d420080780a801c004041e00000352024050043c000000004400641d0740c1c0c800b800054010070986901d0380c02150200611004e0180095400c030014200d403100302d07600d41c02c0d5040c0c1e40541c80d103408040c02d1080b00180000400d81c116000f003440b161140c80620050860603c075904a0340e260030064119041000001e4041c0a080301c0e8a500e081e4074200241440c007040c011071010b110440e000c4600802110051041e10300c020380500080c02c0034940140111882d42c0c59108864043c4210340c000c5018002060103503014000c03880b00460440d040312a031040d5a1103240141005607455005150300c07659010441c5441c203051182c4580000044040c24541820300c103c001c00205044200140f050000c00d10b0b4405202d005400c00d40c110090 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 903990584 1250 903989334 903989347
    0x30e0415090c14031e101a0a1b112107080313080d090b071e03030506041a09130303060f0e0403030b0604140904030216030b0f07020312011205120f 65
    0xe0b00b250524010203c4600090080020024444094007500c80c84d00c400c0a000c1c1d11161151001c0341526003281c0e860061000c424002030b020b92000d010f820380c0594809c1018101200c105910445854001c0c12201940600c406e0b641888025001d4030380c0031840e800d070170191100c482d9043c0152a0480455500001401207419008040e0030011700008006000c6141c90410f001d0b00400030b038402c54540603404140082070203000001031903180215528081d01900c0751800500405048842522443c581000340110702d4803107480740c0712190701400d214001d480b00d01000c04402e50484d022820162038940210342400544510030003020300d100c82800c00e0800d460060103440c04100803138004d00c000c0c4805c201250f400151404010815550100b5603103031030404a0519420702041110030148000000402c1030200d42a4440d59845046510b10307250040d089860744242414002e0090781c1074010312864040205242d00c0074447c2c03044803000d41ca00b5001228607008006146518103010400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 903991834 1250 903990584 903990587
    0x302041409132a08160e06030d0c140a12030c170c1b1906060503010c1418040510031202060702031e0405040e0303060a090501050d030e0415090c 64
    0x1101000d40d411100c07401c032440c0158040c900800d05150282c9048826514480c48840f41600301414070b0140c192501c40e140c441110325520407a5801801c400401c40400281e98102c000545004480060107026480c5050070202c0c0c039a49400300c103641002e550029103e0389103080006481c0036110381c040c640c08a20100b006002c695030a03a41030107204d1454451182031b0141120703503a000514025564443d00303000b00c0701e4403080545901031518424105000c6540039000406c4403072922455082c00070f6602e4000381403c0e50242c2c0c080350003040c0c4400b64031071303501802c030050920b41170315000d003509003c4688001419960103440c0c10f8140c0d0b401d214248140134400055003030018a43c002010306040880c0d00a40d20b114407200e6071381019040015a0034451202c00326402420001d00c11701441d801a80300540341e50040d103500c3c0c414909941c0020303000d00a0700955048840081c1006900100b58a0036103420103030304185544103139074800743c54402049240300f4002d04520f600000c0c441c0f00f400c80 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 903993084 1250 903991834 903991859
    0x203070c14030702010e132405120c0f01052d07060c0309030f1107080f1507020f100b040b12010504030e01050f031b0f0307050307091406160c090903030204 69
    0x2181e20550300100040c4015076000701310140001d02c1070b51304007a20361016052800400c4640f00b07115500f500044643c20b1541c0c0c000c0641d0a45200f194000300401803a244945c0c0d4460f41400d4580210003025003540c3c540c00b980103030080715407107080c00c0b00030741040b00e03070180b5030140c3c2031010344810780411880240003003031248928000c52410100522045510701030040882200410100b0040302010514001c041c4030000c010711200040b645a41c02d00000c0c251940c03008540044600c0c00c10380092000c52001901e0703c2040e900034041e00109100042c60740203082d40c200255001703503c07408507024035180d0480d130440c00c011440c0002000c0c107191500400c0c840c280082281006824040c40c041800d01e4000c07170750015592691500380164030000c542080c02180d6008000b0341c80070007006030307258210004500c101000e544807d50192200b404901025945032450f40009050044a111200301401e1451042c0a54221094190794240410594040f4181240002c0d0042000c00c200301e00000c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 903994334 1250 903993084 903993113
    0x609010c0b0a020d110901020303060d06110d05090f0607270b0307170c1309020c070306020310030c0f0e040b06150408010c02011a030606061e16050c400203070c 71
    0x3045c0514201621000039601c1c000078100500c545042d1b03440104000c4140d0003002c0340540c1c001059250700004080070001c2c44100c401901500070100c25039500070f404129140b05070700301d494034104032907842c800510042001d80c0c02c61442c0c040d034101180c1007074100080c0d0300c10001652000f0f00c3d0f00d151004100700040242c48407400013024408501810610107a403010b84410420040c1c60300300214401d864148203500140850b4400401d0104c441021840c40c800d80740201190700c40a951080c1c0504500307228421074254040484c0400c002480c0545020b0700b14000a00d8030304601c5600e100c1402542c0700b5400390b06a80e55842010907072540a000d117800c11040c80e040310409132843c0700071a45404c0000d010303510644000a0204102c203200d00181d41d070602a45a20b0784070010728442c1c04103851414170075541e07846452888100351419003681c040144080021030310400c60b01c07440046a540310810140518002c82d4000310640b9240b014610802869455014050031803e242407200040d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 903995584 1250 903994334 903994361
    0x120c21130507030f12210207050a080307030506150403050a0f0303140a06091d0d26040b220c150e090a05010f0510140307051207080105090c0c0c0609010c0b0a020d 72
    0x1030031001646c0503c00c486580c2d100021300241e07959040e4649a81095441c030002468600044180031842d58140e01c464401c4000355100305100310005440311a9028030310004040d9805107845d5400034400c19902400103100741004242e0310034014480407516001c90f8084401a40c4800030406001d86010b002140e441302051307a031112091541d410f03211030360f054040d07050010711a0844400030a07440d40d05084200c4208a02d81c6041520f072038109130b03009807408600742c50940821200b100d510510801d4181e8004900716410b464100c00e119400b0101482c81c0501040c2e44143c1720740e03100c01080b00d11404075012b001038258104000380005c00c047e9001240102e02482c1b40304017441d00a80c98080701280a8009612079541510031a45480b031002007001208240d030601554075004039116042c0c1c0c00403070702540c06594400745200c0c1801168980d1585501c1404031810a050090081051480600d4001c8044610351030b01c010554040e100d84031419400950514621070510402c0d0200044 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 903996834 1250 903995584 903995597
    0x1103070c021c08070204050414160e0f060d0609030e1206041403120711010f0911040f15050f030a061b0206060306010b310803120c21130507030f12 65
    0xc2d4880c0206030003420130003802141e07140c001c10b0503c5880c41141455241080c100d41903c00760460503030b00654240705a40040607014041b0380c1c00610f00d29014407404c006800d10400010316200c10f1702801010b001503003030249200c035251a80d200e211580f641c0d080700000a04890400d868055090641c50403002c04980003401007050252072241d1142d000b007454640158414407288100d8010300d42003840c240602c2c40e00e880c0e802007011010010031031420488080040407120910700e415580d00300e60740354402a4a450500c1189000c0d039624240c0c0001408840b6101a240d031600c0454030312500d01004403a110503181003056040100551003a000c1d00606001d501d080d04c15501d9000c2d20000300703402a221188070a000c424040480e9950900030b10b8085806e990300c0030039450394880c424103180c0318048400110b044211208641400d28200092080000c1e80c1503142054000036040d11a00210b508903100030540c2042810061800b440d54114203200c14540140e24010402c42c840a1024 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 903998084 1250 903996834 903996889
    0x16112808010209223213020102030d0c092d0909021806060c160501140711010c020d0c06030c030f05060a0b09030f030d0b04230601030f1103070c02 65
    0x564610004101038441d030030001d882c0000c2a04070145c8000f091110161100c00e4924030402d000b0038136200302c003150000d02c080c10744803085403c14050b8940341c081d016910802c1151750741c0b840c3d94001100c003480e80c9046440f8035290711040990110461402100d250300900c1c1d20030300e440c02a01c0e000140310f014010811800c50354041090398a5440d0707015801004000014240c0c1c40308402c69100802e52020740f048903503540701441c0e080b031250041e240050310803a602050b100040d0201d408180d0001d1080b0150305038070b40111507607104c0300c5080360010316140460000075002c0e500040580361688011480114918005003180c1c0100d83c0c4601260400f400d00840b9101c03400050f007550755804659030b5603c0e9002c040780c541204244010054400060340400280301503102004144045070305001503807207080d0302520403205d01c480300401c003114000309820750701990210003099103031a808240c0000104003190107410483d40d40000c252070341502801c518110b16202c0350390f442d6945a049014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 903999334 1250 903998084 903998089
    0x21005071a06010c051005070801050f060d0f1b0203030109050705160b06040227120105010b1c09020d030e040506090c12060a0f180e1216112808010209 67
    0x507003003400c444089200001041080c2d11564003001041d40100c00c07609090380050b0384000510f0116400320010303032410b0001c80c0ca032070014203914040e20011714032070524190415031070003804111440802240d070340318180c80c1c081480071080900c042d1500907584a41c54501d58100b6070b8802442d0300100801001003545400c3c814440a0025401c588003680941d50301c0c000c50001d1240062860320000303121440610907810700c212655103101a5880c410205c0400415030980341700703020311140214240b003078800c0c0b11602503c83d464030496070340111b0440210780114291013000403040e4005000d074a143c1b8128203003409281e801c034101352000940c520781410228002c0c017070710b80361501d40b540d1000468100d642d64554040030381305103d040e071030869840c0d180f000804080921802a1030801728030038008180030074850002542402c1285c5040c11034598020034440041f001c4502008951110302583c403040c00000302d038000280c440b240d505105910001e0f1421a82c8044940d80c010405602244c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 904000584 1250 903999334 903999353
    0x20a05040608040c03081614162c042d171e0a02030912062701020c07090609110c030703140706090b072607080a06180902100507 57
    0x15609440e02c4040e0340c84500e0000b8080600d035101800035013010407509804600c550900900750b219000c03a003a070700b402a4056448038030780c01100e60000302541040041c0c4042886d01200a0007000d041200c0c441d01d0341040e20707000e000f43d90542d441c801d0340d2900f1100408141540e0510300021891030045800341d99050740c0d4008010000001c01c101103000f0942100e03c43d10015040c00c2d171b0750500e45030174072810000e50702d812540d5107501c2200c0c1407614503030f20729010449034040c1203079a00480100b42c0c5090103010750b0f140565881c3c081d44d820400e4a168520610121029010f030348004107c003480c0648480c26180300885818071940e040190740651a8000111030400f0782c9414051400521b44070403007c0384c0500d843c00b8201134101041c1c00200210b00b40c40ae03100d17405039203a0118a81b88600c140380c0380c0080f1803550020000361408039261342e014005103a4845a0030710041041500c80c041f901034640c500f42c080c402540c0b251300314001c40c6024401010307160000c2c588181040010344480c040c2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 904001834 1250 904000584 904000589
    0x110315190203040c1a0310171002130f031b050111061614190f0302040f12030225091109011b02030709090309030c080613060902060d05130b060306091f0b030601060807030e01020a0504 81
    0x9c0c10350008a000c0c004442ca1410801000011807625100381d0703c0c10a400341d422400d40c811450041c1c600040380c03640c0610b40701c00c034400d10314001340669a942190b0792100f0006554580a000040760032800c5480e40400815100d2100c45104107604006000640a5117416107a14141801444248040d0880013007a00484107420b140990b160340b541400d03410700410254210f041c41414452001040020420000301e0700c0210040007aa001d50301c50f680d10b0300401c1407084c0064102d10304c95400c410030307c903094a44c600050669610035a10190300040b212a9003044001c01c01652040041c0910000180700421490014098a24202070041514003540f5401044503940e40070001c195142d0030183c40c46848c0e860020022400d003001202ca00641400c42140d00c0414040068540d0801041e81c902403041d11000b0003800040751203620041445404200180395212441c0700155010032020b07000b007406460b1056030341402003000f4161052400d02c0085a801080b2035014240d0081c1141c04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 904003084 1250 904001834 904001863
    0x50a0b07031106070509090627010f05010c12300911040b010e060d09081b0d030c0f051b120c07080f060105120f0703110315190203040c1a031017 64
    0x5540c0d10b00d0001500261279010800d0064180b8a680802700106401c2605072031008080090940d42c50004603269450420001c01c042c1504e0842c04c0a580a00d000c0300c0403d11180940d090303880400803011144000c2c002603400551107000440622010003403d611800c419103040c407426000200180c84252034040342401040c001911402e4005154003413083e281d4013501c0d0584d500c4896040340000b98000c000d02c440c41c041c1545000005003c1c0c890b000c4140c2458030f0f0503014210141042c2c4164000340e051030520f1610499030002c5d000700313109118501d50484803a507180d43c0340010035890300a907500085190f5014150200078150002000d0741114001c58540070743c80c81107002141000900d0105408a1003040307000f100704243c44451420304001a802c035020049018941c5c009000c003520818810b07480c400710382002c11125002103030f0007800303074000c01030159039209049094800242a43e004403404001e0041d480300818030100144403554080c280001010590380d1103400a41c0000e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 904004334 1250 904003084 904003099
    0xa08180f030615061201121106030412031104091b0809161a0415170c0a09210803040c0306060b03040b061e0d0c1503090f1b050a0b07031106070509 65
    0x500c5940c2c944c11aa2441a00721810400b0350391100c56038801002c44108481488500c05004642e04240094a11941c4c2051119005040707441064008244118030302407418402c10020400c445107000c0c046d000d90780280c664080d02c02810005019040142c49101030790050001c49207100c4490100300700741d502c0b601a200c0b41e80703604101c925681c440c40d842410b4103074503002c141c40035640000110012601110740c202c200d68500c030000006101e040304070404265200c00600035003105451149281c04110850040510152603610042c0c000311001c40b040c6000b040180204081400395000800421003101e0460900380c3e03942c04030342d00041240d409100c180c1c61152080c240c0340c1d800114040d000d88071680185070b50919502c203030078900800a078001d0840c0040103d0740b00f0b20072485459002260000c401c052a59425580301c90141016003004a411020415545860381e080c01022803800c01d40d81c0711580e227030203000713908006200c0e12250400010082556044011100d020310b0455445 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 904005584 1250 904004334 904004371
    0x2010603080403111f0302030a0e06070f18090204151206030305071e0605011203090f050108010302191a040905160e0f040e0616090e091005060f030a08180f0306 71
    0xc2c03002078090255141718500310000105e8150194019070203003012a60074090034940e1001c1903a104c0083d100100040c0e540d4040b0081c40c1d11441311070a800c910503511018842e41d80b65040e040c0d80181d00070751850300783da0f802d0f50b903895003116515601440d0004140480d62940d100507000740901400075002d4038448503d0a11000340b81403001d24640d001004102d507507180c6180780c441c3e40d4054000ca001c04c0341128040f4586031103169410481c0d10503500c0032101d030308542c24003140c441e94010030a115040c2880c0841c3c402042c2299502d210101110581c950780b401491206440d0003908061140180e0341346070fa5540c0d030240302c1c080313103c1c8207540410070070482e140410b00500030b40003c2c002c1401800c1c10300c0348040b42121034100c0880295912104181c451000400d40e0740c0503030302191960300c821504600b00344140c00843e0700c458020800c01803a105400828205840b1281c125114900082c0d100c161603040d18000300300240645203001c0c002c9030f040c0400d95402c0040d1180b07a502d080501c10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 904006834 1250 904005584 904005589
    0x20011e2d08011505070f0804090f050402061b03120f161e0e180a050103050d02070e130309051801090617030403020904260301051302180d021f021c0201060308040311 73
    0xc071707100290f12802140c02c0c840c0714188030020b50000d0280413540ca06114030420000e080d0b016480c00707240c00030103291034500c89600889400c1040d030307039110301d5000901c50500058100d40c62280716150340d074170498403403420310040e4004854030560300d800d0003c0200c03c444c410601c02d6a0302c42da01c0c1d0600f051f000c0002403a0004800c2c600c0d94142940c07100070070003040b41c1441c40341c00150480b445001103d102e08491407069881e08890300921003008199400184450030900c0441d00307081c0039003420052243c0320701c04220204240040225001c040100400101216204440040410500440480d81c038801c503d0b40722710840c030005c0d100b01e0074a0302080600c4501d007003540300002c41c40712100b807000c800d454211041e0805d22551780708041000d101c801c01c00b024004c40d43c020381c01f82018100503056004006840005040030390b0451007114440c806144030140d4515941030940041550014940307240c0140d840703009a079800c5904000e020000140c40e90280e8003500e1748808103410041c0500007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 904008084 1250 904006834 904006837
    0x2701020f0102220611060403030902040b0915100206070507020409060e0601060906080106050403030504031401110a05180a120b0a20070b06090420011e2d08011505 72
    0x41206510000e881d01254005120700c1c01121102568405004d07a41c907025204030071400060022600030341c0000d40024030030350107118007501c000d2001030040154400301d000c04400b1a51b40603c044c170b001c40296141380c8001350042c04000c0e44000e204500c3d04210080040c050b5181c024003c0313869035100400c1280b0303034000f5100f410041044030025139440380010008221446040040341c490400031441510403400c94041d2a015100c0c2844c16103150340700100017005403203003429135587d10104003040c1c80040040c804d148580c0d42d9562200c42c80c01c0c071a55610001114148100074010003041109011203050000380d03000440c1070340b20b03650000b410b4054800c0c80501104d024404104048907000d21002c0c2501a00880880d4480d5440105102000304145c070040e0140d40c11841680204c14403008000d0882c01c10f140007148684c821100c40750b40700031384000e100454011040c0501d141c0c41004028164002c001c44e030610303810703940700250148406024010904c3d00f15044000d003e40240f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 904009334 1250 904008084 904008103
    0x7061209050a121709031e0d06030c081b0f010c030225140603041505060402090607050102030a1b080103110a081606030b010905030312060109080a0501020c0d05270102 74
    0x20303210240310360314000c02c0312250300d800030000c9801404c0300c00803c9200c002852084403444001c515096981941d041e58440a041d8a80c0a82c000c000e0040f00707096134012070b0300a610070b54004c420f50307060010941c2041402d1500299604460040304610343e43c0300317000c0e241e4140a080000803446182003ca00703086c0740c110040004800b841c00e5000c004401c031107410898003010303941040340c898442040043e1109442c080d0540d10b800803940390700c036140d44c0100e4104400520040c40c03c0c0e000008940715800016054556940c080b040100c09901d60081d207241d8642c90004500c221408200649640e07410701024010301a020001845a19138460000140982104607a050a516a69800b07035900703d00911000a00302a2a40840e501601083c002d0703d00c010041c50500c1184e101030443c419005200074100544c00c6400144800c0900c0807540a80c040c200140c0d580f1410800d83e45060000211201002400c01c41d907d600c1c0c1200c4030041c540c0e8500001c004920041c0d0004038944481c1c0c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 904010584 1250 904009334 904009343
    0xf060f020c0a11041404080307270f09240b090312030903030402100e0d14120f040303092705040302010905240a0501031a04060e1507031b0207061209 66
    0xc2c04400300f440885000140500011601407203689a42152108008000c0e58010300d280010700c00702e011036010f1500c03080c103800340101d00038858245a0301c190030103000350f008441015540d002405481c07583e001c1e10700040204404c0c205281d01c50302805a058015128258080340f010410080d01c1d0b9044c040b0380d20411020100d1612810319840340c03922513009403401c9106154500e011180d940c0244060b05c900d8034000c0c0101100c2c0f9540c0c4500e50040c00342a420760150240121000105050b040a0043c0601595803192190300f1450041d1810005801503541259002000c14080c03000c001c07042a503145100d000709840d2164603040c4e000d480d0503032004206028030702c004203120b507101000c1c50b0902c1c20000400c40c5601e5010f60031003111000c0c00081c1203240d46180498040400703824441d0440d100c4d40c00041c3c2420503902c01030502c0b41d00040403c5401100e81403002036540f50040d08004054030301000606005240081d41d241c079148074120501445081d0790b41e40000e070b903000300002c0703422 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 904011834 1250 904010584 904010593
    0x20d050a0209030d030608030a2a06021c06081e1f0507030c1b0605100305071d06010e0112330801110408070b0f07080a09030c05030a0f060f020c 64
    0x40e0403004041d40056040d40d02a1055610b043c028902c60300504080391410300c0510b20700416070f04216407101014668034240c40e0162803001c02e1144071603241150324040c200042e11031440b00204210008002961415a0306084092100901c0490790480780b6903e0b030540c1400020000d0000e09100784004006091a0007a2000ca030260750303500628422400c1f07580401050651200584a811071800785101021480031907030300007800c503800b00342c01540480c012100540d50740d4502d840c0c44010b40040c1d5010710394a40d030401c0c1d081c180102c940c06c040b00b400c08500303451611000800c42c0b032402c0c0355100050307100d001610f182c03500f880081102c2c130000e00ca84441d008001007001805420f41c800e4158940c40c044125918500f14000e0f5030a03240020080e18074146080003007101a00440100e0700d011104000389030000b4515001071040c00d0301c0b80c4402920500e1400c211130b405401e581310500030b400c200f148900060351000040015030f4040c600045070100d071004400240141c02030389149100303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 904013084 1250 904011834 904011841
    0xc05070b130806091608030f161e050309010e010527011e05071a01240219210320071a01081005010f050a030303020a020a02040528150612020d05 64
    0x10102c0d03c840d05d44049644044d01585c3c40701016568032510300c00d840340d10424060310780e001c1c00501441e407041d40100500303015610070108c40c98800180280465440e8000518901e00d944c22280503140e4643c02d00f401070804481ea0004201c4002c0d0b41d9400d002552462403010003603001e100b516140721803e942c171040d00881d008014180d580500c0003500d00147c004070683d18034034845851810313100b641982d4100c0c840417000002e04140f45126050a5005d0131603030460f40f40c000e181c41c11920340100d203014241000f00d070a240255403200703900010141000a51745d22600c0084a07040050344034034490b955861a4145003050a0586106241e400c80310b100000b441e034400103090000000044007041280d0b41e42c5000c8030b5540281c4116500240596010400300340280e020344049107850040d2082200c0b540d00280444000300da804019000c0d040e5403540e880c036502c02c1180c5002400600300f00f050500380320184045080d10580b8104080c0e0308070103403450b0703141c2c05694844d10014410b000e1401c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 904014334 1250 904013084 904013101
    0x306150409060f080606010504031202071a040510020d0525050f01020c06180c010e240a02010b0117010308030601111b011e17060f030604080c010c0c05070b130806 72
    0x20b854400d000c40c0d040000000b00301c004012500c24010007058661070325252940d91070410a445000c00702c0c1c190f0166410000d201d4180a00b80301201850204181e6121301b041d0400c00324150302d412000840d0300941c0ba03541c0d1035400c101165168000c100e80e0001e1000140c818002c480c0c0c501c4c10040071409010356010310241d05402400e60300000c0e03000d035001591030460800c00d00c0504a840c04942e48140e940d41040d50103682a4590300b00c0c003034009101c09064005d40307542c80b85038001e81d403640d1100141b1000035650a10804584074424070704501c441500b07040c0c061442138103010141690303c00101140d010380c02040103440800386107007a01d50800030b04580020b80020000d40383d002c210602c4055103400e214034410403800c102919a40401150380344d469103003040042c140c507001000c110b183d0381c1c1d80d81d0410031148038902c281e8880c0d0b500c24504034064203550040640c00144a10190005c001620100f000030a40f140c4a000686820002c00fa403507101869a11a24541c040e84040c0310700103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 904015584 1250 904014334 904014341
    0x1b26190e030f1b030a0c0b0703060308180418151a0306130b0601110d0e040b3102250c1d0402092401140918041403070f03050306150409 60
    0x1c030f160003d0706400341203001507124411168401c0004241c1c108000c0010140c8180c0c0760080345510340002c0507900e039a200e40c19903010110104000300d003581a85007a00e054007691440d040c0c003940100c11000d083e950030440c4cca00765801c0c8011520b80010034525a50000400c015040090450b90740d81001c0032440f80c1003c015209845c4540c2d544c000030a01d50241c0c0806040a072040c005002811030300f00c1c104c1c4c0c0e2500c2c0c40d541d2036000c0d0b15008a40c0141da60042944d030001e0f0104156110114003100c07401d00341b00000030205503540144250b0702406041106c1254142c3e5a1520a080d440686010200801c0c00d40112240301150300c8981c0e0400d0040020b175120707510a41d521801900d1b48c00300e80c040e90710950308002c140103600701200c4c0c96510a08604a0b401d07050f0b074003e0708040680c400210b10100d88000c801d9800480c2e41000280424114a0031110b00240055440c1071082d841c0c4011000643e2805000e02c90000046001a162041100b030500580b4248503122a21010803a014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 904016834 1250 904015584 904015597
    0xb04020301030c14101b020f28080a020108010513060812030702011a2202122a1206010311070f031d032d101b26190e030f 54
    0x1c40b100018011070500309003080c4580c0000c652541b0400c044522225190035254400c1203810064840c07881850b07031508800260980e11070200c08040303980304100c5182e004c0b03c03540302e45032a078003120750400540d07000b2030140e06480301903d01c1003071032502e450f8580c050005540807800b148201c82c50326504081000145000e04140c3e4000d00080c1c56900e00e0b81c950800b070380d0009074001d00c1580c0040104c03070580500c884480110070007600780842d0001c58200d2940480340c04042d0032510340d046801ca103604680203609110002c0850030f01c0c00f800170162215400420b080c6c1496900c84089401c20000710a03141c500303034440f18116031120945802019102d0743d030401010100c0d101980d400c6444d0200e0400410203c82480e80e12072912070f43c40203100d04034544042c009028840540d03040789000d0140251440d40c0008086403481c0035a0010102e00310814140ca60070b20007003210f8072030610105440d030424040000306e80c03610000c46210700101003008200800b80b10001d81c120007007038241c1c0500300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 904018084 1250 904016834 904016849
    0x70b180117100b0a030902040e0a02090115051c020d15050f061e03070521010602060a052404060b04091a060a020a0605100b03040b040b1f05130b04020301030c 70
    0x2112188041c0d4010101025940180084850b040c140400c0e4507080150441c2e0850346008145556140c0110b03045a01c100c42015080d04112005000d50400300c41d014010042d83c07a4407030303134100b1090b0014036a010305402c04200404514148601c12600d4054423b2907645090400c420081014003584c5200c10303210f20b0b0b01031180c80c0018101e51400805031890072000320240703060800c40c50741464107075000401c8d840902000b40082180c1030010440700444013036840c2086d6255051400192400070014403009040f4106070030404580380b05251a0240f845940b2910111802d1a0005002d0b0807140c00000b403125010030300054001141e00900b040400240c82c403a45001590107100d640e00c0b540d0600d802507070001c1c002c8000140b03542e1084d54843c00240e41311500035114264042c45500070345080e2a4840880d081c04103002c2a8006950440c2049072112200c803049040c0280c0890144a1a440340c00070045e0104c415030181c02914400d50010001c564030740e1a403a202101d11768501135403d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 904019334 1250 904018084 904018097
    0x80a051f0b09040c090803040b0708040f0b070b10051c06090b07050a11011109010507050a0b0a0207050f06070f0f030e0d020708060903130312051e0c0d02160b0c070b1801 75
    0x1132070382c02844032100f038840701030207103182c1800c02810350400e9115400469001004000000d0242c0d48004104060401140500c0c2c1d00c03041070805a109410103868104140c0450780208065aa10000d800c032a400c10b8240384c0b040c00060074003400915142c080504061094001c01c195254800020401ca01c1141c44500702d1308400b1551034202c402140340410721000810810402d036001c0e40103000d1191041044405540c05075640300140c610640c0d01103107494000c03420408029051003250501da6015004141d545000d10f00146174021409600051000b0140b01140042c8241c224141032804241107980e50540d00340000e42d120140d200d00d401c50700400000c20081030011003110303040741001418091460464403444c08000c02c1d41d05030014030100300715219500054803d04503421841590181c9c40c0c401c241081420800d92078031700ca0441d009080011035481c0507400e09016a5020a091600c44074034808083c907248481c0c00c00320700303000c010070105e810019503a030140e0300b90020382e0380c00e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 904020584 1250 904019334 904019351
    0x81f0608070f030908090135240a0513140c030a05010e0f0403210507170603011e0510030b160e01030e0309151b0724080a051f0b0904 59
    0xf2412034048004c001e141c4001041001d215600c504043ca04c035001882c845549603030390102d030000800c0300104811f15003104a00308105034040d048500b450103420449020303500201400202c014071276025640c42541d80e007804403c0d01c460b82d030142e100f000700340600d40020304142c1daa12041d500225880d40748181000000310b0a2170410103900d00643c9001c2850a2a0311590740030b84000c0b81401c41c030f4030400b4070301e02c9511490026002d494011101030310742100d40400c08100b400f00003002019940641c1c1091048607202850711880040410180b0340050179886082006106110030b500c00782082100c1c600784404000446031007910014261102c80750320341010300550503209046100e0000350018800c483c424100081c1c1100800704c040c00341132070706541c00c401c100440142441c0c07461590198500b40007000c000703940c03a21006042e451065200541c0903005191110050940c0c40180d15113010030304c0d602007002c41c5407a01c8510071003400019100e00b60400b49811030b102c007a11070b83c00d10030305 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 904021834 1250 904020584 904020587
    0x20f01030c02070314030f12041406010f14060903010e060a05100e04030c030908011d01050a0501031e0f05010c05030f1e012d1502120910081f0608070f 67
    0x4903607980c20305070050400e540c915107800700040c07101c504041c083c0c00200302e00304030303060008010004055203080040e4541010300748062100d01e10404c202c4564800c000500020b6090030112040390102c0d4409038040009501140e1680214420150590308003040145500f6010480a100b80302d600401c10840c0d41e065450101c4510342e101c1c1c5168114442c0125000c2440b031646985c40310302908116000c2a81c0c1d02e50781d421079001c140607003001ea100c0c448a152007007080c065280c002c0d1100c04140155411a2581004045940031a401c0010041c101604000c0805406002c91750000d000300700002c50144058865071040300d8002030f00580c2400030b82141d40c05132015131945642019103440d603091107170540905022050a41150b045c50009910003044d00401401410051407044402c864084010b480c041403996042c1840c0400d00c140b52280e00c3e01491805042c0c2180b9140400351501500b68075001e8080440480c50a602c96000c1015a0031201079030040d001075550a040341d120450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 904023084 1250 904021834 904021841
    0x9020c01090c1d100312080606070f08030a060905010f140a0812070605010819020108100b07051b06210604020d0f0903020d11030711060405030a03080702120a02060406200f07020f0103 81
    0x4010682c1002c214a8915240700e887d0031640640083c0001e450b11000340c444c41148a8501d0084421890010411440048a000b100020312268405000550405d40382d26050400d90103040c00240303140d041200c2071350b0354458490081c4070b88400d9400301140442010020781c05164242e580328141000080c845000283d20603c6034140d92000d035440b4042c2c0d00441d40007501902600c000c5250074030200e00307031000380001c00c02c40b84640c2c02404280805d1002a0a503648510002d10605061010701c3c02c602004005240444000500144a03919030f030021b00207001c0c2010b180442440c1101c01080061180e01c0074130f02034020740071121201c600030030440340e4407050300407100c903070b002400030038006008038030008012000280303076030f0800e81c8a1000c071380f5014269005600160454042c01041d9030140703d086a0032452640d620304d8030002c0b510195a907038000d0300003812603945041e0760070810000684413021540b03030703102c00da41c808460802c401316800640c4c0907072152622030b140007400d600130310 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 904024334 1250 904023084 904023089
    0x70f080705031b06091219080a021b0312070201050f0112050709020d0b190b0909060d05031c0615090e060f100f08010b030127110a03050103111909020c01090c1d10 72
    0x1f000e40c6c01100c00401e040f180c0510151036485e98503024001c1b0a4060032141c0c001104c40400d50003141c44130325170b0481c8401504064521001d691600f01801481c208035800d140c1940c00b03900700442c500d60a49011843c202c043d0380540409480131071030b44c6035444590080403a194040f6100d0190031044881c3d0051035400f8444c4615080c0304101900c030b82d052a002081d4080b500605000c25450951625801c641c82140704110303600c092010003030700100b030f07200b45405000c4801600540c520526000f602102d564080d0a046250500018000380e40b070b009034443c6040040c0101d90500100c440191210001c40d00c001c010640c4d1800100d065404501564101d41102ca4091070064101d941450040c00c510102149940c9404104c200101208000c2c4049040c60394001a6503156092001d03500c0100e6081e144560005100c098100c000200341600391100c85000598400c40b04076081d00618054100400f04140b0800c0050300441041040040b0b06159141445581d02e051009030031302c1490 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 904025584 1250 904024334 904024357
    0x10c0806040b04150308030906090109053d050a060b0313082d0d060b0a1e050405041b020c03150114060d0509070812070f080705031b060912 62
    0x44000481500d0941c024051201d0041c0001070213100e040c00c26880500c03141c100f80d6003004000240030b0301a0b402c201e003613400041c40008001c6500c05603206c640b600e0701c91800750b507030380b403a0301c140049048448a0b83e42c15000041c030007041540c08800b1900900b00c00c50b20400311615210001034070040c07180880384a5499070000707913190700da140d60350017454101c1110741c26a46c1240b5848500095503041d0a0384035508005015120300e04082c0c0d5909070f031081d0b00040007100d000d100380180c0503000351048008a20b00349446035900610300046540e400340b40c0c481680a81402070b241004051103408090640040c0d003961465190381c018181d48000c2112411a55142c1030010080340c24811001940110001c0c10146802082d4403914192007056603101d806401800c010001d030a81009803882c020400c2c0d01d0181407071429141c0000720003d60300060224080042d0f400c0030464103101320796900704004094601c0700100315100b617668a00b12205030092240b181c891241041c044103640054909 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 904026834 1250 904025584 904025597
    0x4020a060c0804230a140301052d0c0906070f06050906040f03051806220e0603100b0f0405071d06120a09061d030a090b030c460809010c 60
    0x800038240003030b904e00c040c4828021811320300d10700309665600d0003100501c00411b450003503d5a20040500b12100607062110700c50040d0811421158024800c038038100d001446609555110b0005020360700c210079620b98440d00000e2410101701040d500750001c42d001d10400c1200382d4a1980190340d0340d00a41c1e000e080c504450542c140002d03c03c4008149028080c290060100200404102c2680010000001c405500302602e0030707007030300e014041004101128517103819041605c003080c3c03291000038001200548884c00b00840e41c50300d000da440c40d200c0c0a001042186007001c00100098150351002e503864034200c0d142422464014140c0380408403801ca003030b07119112800260002d100c5480300b203d0041e2100d41f44181c06d20451300d19640c00742e880000d107646512218008140042da604103000050090041c816400040f000b0390707001d10100c1442c0041d044000c1c0c0c019030800008012005038681c0d174542040005c00d00d04929041c04100d0300c03960700685405c5003e40c00e8620044111000960 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 904028084 1250 904026834 904026839
    0x11100332060d05120a0915031109121504140f010504210e180a0f060803031303050c1f0e0303040b0f101a07030f0c0f080904020d02030f04020a060c0804 67
    0x1040b01000080034400c1d0102c2c1e21940204141c0c141e650400703820b06001c40c05008081181c0c4840c0030080441c542640740c104069000c003512441240190319106001c0e12410310005200082000018150722120f80414144d141600d0840074049600400314810700980054052001c414091140555445001c0d01c5014047c0701000403401c0c47d280c00c0204010b0306c601b4072802915804600344503910382c8000ca400c0c62409803c0c3c40c043c1c1d110070085100380392134103004000c00c1c2404000d6942281c0c0c0210f05503c0c81c074007030a04070385500030001c0f850800d004074034150896011044822615585194081c050344041440207502c1c2d01040b540600591100c0c8009041100e80d8140300754040d070b010310352060050703d40c0d1301418035001007182061061030000c1e1f034000b4142c0100321551a50010302c0c3c1aa101341c000e5855a0903480c0307240005043d0080421a00030b1651183c0540300c4e00ca49a41046442e881c0032100400c0084095409038090440303000c021560304d00c1080e40350a03032034108019a18162 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 904029334 1250 904028084 904028089
    0x110c0708031201151b0b0109110c0304030b0c130608040b0609040f060905012304170307120203040807080c0606040e010b0a060804140f0f070915050105071110033206 73
    0xe40041c4000e0800c40700c50421503c4500170810400c0341e41c01074000b07008540c10300015004a0b8800109600ea1910603c40384040550000445060700e912031601510b90b12110144c00450180c0392010f44103138151200456243d9204010521840c0503501c84c200d20340b646000c0c4206200281d0700070341107000140018010480e581c000255540c4075400010360028810034024898800c080000e501c00f81c21001c2c442404400c02d160010a0cc100071a0382c42c1d810004005045090780c2504560b100c4d40100024060026000503100056040140c0b40d9503007448000c480e46864003102c40c14400c03440c02c008000041d40503c905206810040c241142160a04800b074800c1d44000300b00b110360042403030300007083c50401e00001c16800303c1c1c0c0f0010001200c1000400d41002d01507004030030142d01e80350b0702021044420300050200e40c405e08040796078401d81d090400940d04045c5a04c2d0300450440e4202a9450b8554021003000c1c2101c040c1028602a50b2034440405044262443c00c0c1c042c5d08020868070b2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 904030584 1250 904029334 904029359
    0xd02010e061305060d0b030c030c031903020708030a050d0c090303050306060702060c01110a27120f060507052101030c060809210702040b0301140115020709110c0708031201 76
    0x1003840b00101009581c0d680002852a480001000801c9032164160003080c00c0030410400c0ca58411400340040c0c40d80383d00884e0760354144501104207801c1d181d510380d01307060003480440c026000250076070360786108000000e049a480020441d00340c03441c0c0881c00104a129503050001c7d01d9050f0340711442d5448642c10081c07287c00080050b81d10410400081c005088240302e0701e1901c52540c030b4034a0300c8449050002c1e1041119580c0d400021441620720008044003120030401d5131220b02e079100c41c44202d4100140e007a0b80012000701031a1805042c04400b40c5c200014140f0020340c2800d64502d488040f4414440c610207200c01420a00c18a405010160188903901c0e844854230044035140d56140d4030200440c104d44580013001200081e0005c03d50619020746082400290001e10821110281c0000460070510410700556a1840c2061440344248074050081149201c140316201d00d003095000325a2061400c0d510520526400051a40b80401910004030900c8031403005603182200142e5030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 904031834 1250 904030584 904030597
    0x11090f0d1a091615020c0105031005010c0819020a150212191401030f0b0f0c0304031d043222080906030c03090d0201020c0d0c06060f0618050d02010e06 67
    0x25004948034000d40d03c21641c002802490480300c0d100207040c0c44000030f410004000e006a040000800c1044070400f03182032014100c80007842c0c03400588d099420055030700d00030106003d052001003019011165800200707041064090390310454841d42148003c41241b00c2c0550b1180749640583c000780301c604035a1a000f400100c034200210f5120300c14403140500e01c0007600102c07041c44610203440188000f0f0580d040d07000369148154207803424100d6441001d8080100003c04012411400714503440800b09074422858014009001020350450400d00142400150900142607901f1100390ba40c10001160f00a038003003040809600c540c51104c1d10007121130742e000c0d200c1a030104000c401d070f86c6a04000b940310703851082585889040c2012000c0c141000c00026a045a00604ca01d10340e0b05408a1075811228a40c200107603100c0740b030700d007a06c0601410b6129100319009001c0005216030070103c00c5100490106106040c80d8440c1c08200d1405d140c808043d0004da010b80b041000d60a11074010000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 904033084 1250 904031834 904031851
    0x906020c0d0b1008030c150903040605030c09011716030f0c14030403050c100605030f0c150d0b0a1409070f090b030a1803032f030a09020109030611090f0d1a 69
    0x2548130a60145181d20102e5940e620b41d0160b910130300715003c030105080c0c0003044200510714081ca442002412400041e006518100c800185040035a005880b40c021002c44c0e255030707841510344001c1d901030f4140362180440c08a401c14006042c0381d0300701d1003883d0a4103030f01c0e01c4a48000d8034440809130715810003070044080c401d0420040d00c134005d0800c185454468440c5001c109181454145410b00404003060501540048114041595119030314160581c1032854240c441480c9511030300078003282c8942541022020b81c012600c03054001051103a00030688600e5200d0326100130865105c030003210070000003580082d0034001c014110340256046441245d000c905e50311441c268200d0b03008031880880201e0780d509085e110394000da00318010702c0c41500c4810800102d1000840c8110b100081502c0d908656440405045a011b41d5010f00916040f020400c804500c0140540d501d0b0302401860344140301c0c221440190386032034480596110380c000c5c0d49040065140c9081e50800d00c0180c0780c101c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 904034334 1250 904033084 904033111
    0xd030b03032d030f18030310150306030c0b0406301505031603051608031c140f011806080a0615080f1b030715180308190906020c0d0b 59
    0x25103260b500c4000e540074000c3d40d84900e5807030600300c1c518031203402504500f4000d41c00510070840503c8001034003400b1107000200702c00ea03500075203000314000e000d1500018114185420041880cd1907800a030064601944030460031001c40121035025030660101130307014802c41540d003001c0c0141c5801c44100c3c511951004908079455000180c00c1501000300d02c03442d8070101d101007007480f10410050303552240c507608a0ba081e0303040212147c3c807803050716400b00c802a030002203081c212a40758009003540341c07a01c68950483c1003400406d46509401e2240781400e00e001c000d002c055080702c0c460001262014002000300d0341c0300e550b902000d0011048a540c84405038180003803c080280002e81003036015401401211002d14502c801711100410854000e0303014071020b0210b1807000c9010540001c00d800c014054021400e41c050b02c0c0a51034000400c0c1290105445c402c038800702c0301c1408290b00a0311a4500c1350340350391040340e1301c11074a02070550112040a54101003456204101d400041c2812140b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 904035584 1250 904034334 904034407
    0x1d0a08041a0d1a040c0305100509180f1c180611010902040f0f15080606060d27020f040c1407020a03050d09050a06052701020102190201050106020d030b0303 69
    0x1100f02c44040441010107110035420300842d2500384191100714141c1d0404000d141451810b006006d2003601906008003203050101d01c42d04140f01903000f1a059a02c100c0f8200c0b08000f4640c2d407285c66200c05258000e0020002c5034100d8080c1d6000802e050075801c009112030300c0c0c00400c5449200f0542480d82075540c8221900c00360b1203900507143c0f6800250707008110322040508134002c40c1c41a81c90080b0f04506a4424440b60101050705034118204a607229120700000700c1900003841c15507074003101100380700202c0b070341a8440c1006054550003215039034124880380c002d0006030ba140c11540c4d400100840f4410a4a86184010f0188140054a15052140c680d40c421f4682807210244002184040204001c503140c00810b40d0050800c40c9006820503500c112404105401010060000d07030300d01c3c0b800301d0301c1d074403d505a0300c604104400d0b1038045036460750040e000300400c2c007401005010300b07880c4940c107034001d0052106441000d00214506210412601d00002c0200c0204504a0132070540 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 904036834 1250 904035584 904035607
    0x80c010e01110d180801110301051005040e0112151b03110426010e1c050a0c1e03030506010f0504030b0a021605151503100e031306031d0a08041a 64
    0x240c040c0303821151109812200c00000e013410a41040c1d2108065a06140300710001001210542e41118403c0e50b40445c403c0d00c0d200b0540311405036401c401418800394000041e10001d0565041d03100740211a001a1300f5a00c650f05015564114808041c150140081042c414401c1d0300400c400e11a04010904064480340d1000070300744c0f0400b11a820032440d07501211070350000e1254604030040f0400030519220000e03034480c51039640c00e049401780580410f99103005c42c0108030018aa40d440883d0460002840349031001c42c0d100c1c007800703900280c40c0800007141035018101c901c0041c10a034492030b042901d50390340c20039034060044c182140d040c0c0070700004101c0b1105940410f03103a4815005040c80f280c0c00d01d500750311042d00130080340c100d03c580a00081c06440c0032070f81550301d001c1040081810f900c40d8020034a50b20840000c0a00700ba0503000003d1032135410351100c9040a20704120090541c2e0b82c0800640c0d500c14114003400f00c51042000300400020341c6291140346880c10083c50402400022 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 904038084 1250 904036834 904036843
    0x12050309061602120d0b19150c06110a120c0f02070b03040c150923180a0e030c070f0806040201080f0a0921080f10140d080c0706090f080c010e0111 65
    0x1130300e42c600751a40c1001d240303403426028101c2903692485e01c400c4800e180032301c000b4000b105a00c83d038007817000c110521f40c20f10403140c00002c000e0a5401c401580e42e140035200030108182c141c446c0551601d00318024040e14441d0040c9416811194001d008141c280020a600e0340d002034422140041f1103d00096483c040d9041224001d8a98540010807850801414441c980903080034801190040e2046080d58450348226205841c41c0580c5000d41e4400110800030182d81840390350610020038a0007101c080010322406964246e020b503c802035481c007146543e65401e6034024080340b03200000514400f05006160340c01010304101042000d0941c07a010300300346041585122784941c0301c42c1894441e82180401c2e402015440300c0c20f03160310340602c4020074100c86000344070304103910780d80300a0f00d40d440100184000f50802c050695544882500507a94031007407084801241c40e0903400580c00074068022000c40f90110044c1002c0e00c008401103480c039091a491a0500010303840a0600c0e01c010030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 904039334 1250 904038084 904038097
    0x2d110f070803040e090105010e0114010e0a0b04090c0201050903070f1b090614011107170102130e0901111827040605060f030c0a090213180204031205030906160212 72
    0x1030295540d107060a13100040400001d00c1d5410316818500100200ea0000610504482c0c0e001942d010640104004807100702540000300d0303000400010105842a4070401403045402e80c007000c03c8441c18001042e0309880c402c0320b03019010303003051040f17002040311400416055031003078008a02c000451050203013110300d243c02030310240d0b94580c0140300c01e51030440c0905000100342031401c3c40e2150282e08641e030303908600401e0000351400c812620041c809406448034002c40d01d880080da29264500d000d8414803c98018809600707082d142514201e80c072044581c0720410307045a0501d08014401d0205000c101c00d1000c0c444001c84e000e110301202c203989040d0140d4800c800114003403c0c00c6017040060b11a0315481880380d0410703600030405507100601201154a42440542c45d0101a0401d05882900d44e1000c0d03a07810075503c603080710403100d45c010030036a4441e02075a00f050000c441c0c11281804100c410404030f900c5600800e070b20801c54001d040280d100ca1040381c24030259040000e8540d080034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 904040584 1250 904039334 904039349
    0xc08030d0c030902030303130c0902070609020a050105040e0c07030e0d050a02030d0807050a0315050a0602060405190b0103020609030a060f0b1206071707030f15062d110f07 76
    0x214454184190354000d0500110003450144154590360300003031303124440035081307410300c03080192a0300070030010140b00c5001780200300e0704549070b45260038070310080c020b080804c0740300301e56000c000303d0b107580100c0036102922500c2c0d0626600d035480d11000c46036944058410b605001d01c507090002159584401c1e01c0c2c840d440761018241c034100600c141403422040070400c005000c50201041001c5500405564031081d06280124050910340145411020700ea08410781010110f00c02003012500092001c1c040e034450011120004010b0b41c0f100c1e04a683c0c0c2a000b07003c2c1c8200e500410246c9401e40c090320f0750280041c19180c2001265942c0011600d40b800f200301e8550703cbd0044040603140800001010b5150307400604614901028010260143d0728158080702440e00302054140303110350303c0300c0c4d00c0c914080820408000d03848408015a4080d114201c00038600d1000100c500703645800001070755080360000750304031010b202d003130b1112030126080302081d100d100083d290340581000f8980c01080701 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 904041834 1250 904040584 904040587
    0x1a01060f050a12090f060b0405010503060a090309080601060216080102030903191b11010f0305040f0b04081204030801050a080d1416080412170a0e130f02030f06010e0f03060a0f090c0803 82
    0x441c41e01c00151f400388000c840c030581c6820010032040e1170102d402503009a0140000414604918060760f82e404e198000f00c18500c42c01e000071810035000a5a01003048402d40c0340002c0f00d03980c0c411907090b440700312400c455940040c090035644540c105030450b100101414000d5100e05291240701003018080c0041e208001000e060700345558000c500d01c032411006c0c0c90180124036081c0c403006044040584001c010030840000901032082100945805560203d00d40310030b800d2500300200082000e00596105200e40040010441000a041104840356440380603001c0c0540500c0342e07003600309003400380d2101c1c50349200c2c000040105001b84041d00148103aa440241582070204191440c009a40d80445003002000f01c015040b40b20a80c071198115900c0c1502d0240201c0c50020f003180c6e08031507035001d0010080c05041c001c888141441400d00b0398400f075062a008040107140c1940400c440e8058014001080b06191984c1149403449409a000305400d02c0c5a030755100001c00690015115800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 904043084 1250 904041834 904041863
    0xe010e07030c050d03080609090a020607050f16061706060906120412261504050702010509060a06140f150301031b0b04060503060405090a0507121a01060f050a1209 72
    0x60340c2e007414060002514400454551076a020b4104200901024440c120000c00a01ca1000800500445690150000d501c91005240090303032034039252120002400303038051240100b0701c85032401040340c5881e9034902c42500e0050080720341c004042c1c0025004101000308500b60384506000b0b06600c4c0780c003020301c0c01038030740b50070300000200030f0000340407c0040590500030700c00e580065aa40c01120030280c00c00c281c40c0c2c8484031404260818030250810b082c40100840742e9019800b45204223400d506889880d43c03135088000495089000340500300e220506001701c54241300c201c80500c2034014102090b020003040d00c020701d50300241d00481d1004c1e5949903404585a0101410380242000d40b0060305060a10340040c1042c0401084a80600e83d00e10000391918402c01c10303d40301c02e401c24292091700e51a01101c4a00085d141000d41e10401c04c028800b0340709010900c401d049501a944085c4803961038001150160320441c07100003044106040020303070302d0f82841103080b400e1080403020144038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 904044334 1250 904043084 904043093
    0x738071d090417130e0109060b0901050d060e010b0706050604050c03130f061506090b07020f090a0f0501170d05091c17040f03020f030d0c0602031803071103160305120a030e010e0703 80
    0x5c05801c0100b039030781443d07804c0155540c003006490320440242045034039541d509108100520071036004411155102000013030300d503500b030010680e50340100b509100e0b503560320007440141d50040d5448041b1081c2040090310070840d03140e4061b0160b00c51a480d54000702c036502d408003a00d4018440e000780e50221101044001e4011115034020300c0781c59111820312929800051000d040307100c0e182c0c0200c0881c1d0002d030382044c56a02110441c414110204a03550711122180740000e059001c46204e4800c1c1c1d0030759014140104240e0303030764010061040d50b814440c6400710722000d51050702240c034004000303203040c1014208005007018107109200c542607e85103004021110a40302c60045c040d80090002030001644818400d0095401c1980503a403030b03c50701c070508000e00091958041c0c40c000030807007101b080b09180c00e1101d444412012203020164450840f03120100394400200780c0e0388a2040e007440e101814015042808440c10006094658058200d094a0304075000d100309030000007041c020071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 904045584 1250 904044334 904044359
    0x308190e0f0f0c01020a03050d150b130e0a0b210a0b010311010210110a080613240911033114070602010e120738071d09041713 56
    0x20f03082440186020186910041d185115050100141d1902d680101401c00402ca802034020865540e500da80d03940c544000f0380010340503000f03075600759403041c010540803481c40c000ca0894041c024128455118142100d400d400c21880c11007105001d10006200441c00c50310540c0c2c021809980d0244a582c0e400000908000c2102d481000461422440000e0050a181514240c1485081c454819110400004d016060343d40e42d0f050380d80c0c00c01d182d009040340d40080c001c41d03e001994100c1c0c00d40362105048010765400b00c6652013044402d20010701010000d152058512150f00f440303045001c100e03e60101c0c51030303600000b0303034503454103a104c86c40740c4108010040003000144000c0003a151a18046034032103d00320007021501002050503420302c00340300800c0e0300c104000f05540a0034034540542c410f5410007036200418408800c40000c010714010f4401d0102c0f40c1700780880f4245441100208031920704040c1080c2c03085052102882500d0304400c0c0100b98101a014100c0c204d00d00d00710011030071 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 904046834 1250 904045584 904045603
    0xf03120f050f0a1d0301050a0b0307051c260706050601080f040209060d0219060c0c0e07140f1603080a0b010e1011100507050702040b0103090308190e0f0f 68
    0x410800704003107800b00e606007064680443c202e02c2d00781450361824242540350307200315190580c15480d20003480b10603102540084850a0140d007516600d655a80800044064207507848005c50f0481000c440081c2843e0341120085111580c5500c080c00328040c5048590010030381101c501d551407060207a40d607040b4509d254042c0c50b08003400d00900d0030358041111140b000e0000760103004080c5924003103558139483c190080100420103201150b403946c2c014100c020307020058800000031170010074242100c1e01031500c200c00b9515442400042c008401d0303c01d5026460241c00c036042881082c403801406560b0035030365402503440740c0d07c0e400c1030242c002c11500c200c0c003150706015a0451741e210507216540303001c1c1645110300348964428a080c1040e810b080104090a0b6450320f410200800550414094400c007402501c00308522020000103400f21041c5d1480a001714031480300088003001d80e10881a07000401400c0801d00041241ca914500019420500c00681040280c404d00180030407400c1034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 904048084 1250 904046834 904046837
    0x5031806160303110f0d0911011d15042103030e190f020105070b251b0212071e0302030c0405010506180103090c06080a06080c1c0c0f03120f 62
    0x40c040c00301d51200c1a40072030030401402e16841d01c8001d002249000f0640388402c401512407950346420f08002c0008115054046a40000d910844460755114000c2a40540e0001100b900c9003455042002840208105030428a500030400410600c0c8944c101c41c8485d0f18584107010000014a0040c00340c0b4840c1c0081c0200d640042421304042c0d00c1481450b10700340d04070400003035410f80780c00102c480f4881c0010142201e00785405218a842c580e1000b0701030060003102140409407000030848a42c5860443c48200400090000c0d015140001d000840700da4000100c40e12140c0d00d18001d0101201c06030fa061005141060410039400d0900110510403002c550800240d810480000c986019200c4040700e0840c66141802090f400381c0e2111640c217410041c0503d0300780ea550802840b6480464000c4122414000d00085c81000015841010100203100f0502d103c21503081d1400721052003411355001d088140001784848031047d00d41c001c0d50240244000c0c2c030b0741c0f40b04060081c149445e01c600 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 904049334 1250 904048084 904048087
    0x17070803130501080604020c0a0b1905071d03150702070503070b040b0f0c070e0c0a12050c0a050d110301141207030b0606030403030905010f0506101809180f05031806 73
    0x220102001c1944805a8009090001c02ea40711800810024004c42c070180340345100300040703c014001c4108035544034503c00103507000a0510b0b8528078050361403e95004002c1001241c032100021003640d40b4001142014003168824428405250705201c0c1c140c5195001d604039090a00903410244030f00000381407414081131070145031150035240c038410215080a00c200100790782c20a1002030011070010304125486d1010f034140201c0800143d0b100400c464003190f203000c00071140103480c0c0120307413090030800c103100d040a130000d0058500340c0c48007014900007a500c9020b43c403503040348006035018010003500b1103544a82d0005002d800b1000d40800b400580c449402003000940240d081c07540440261140354490310386e0700d000d501400f4070702c2000f091542060607503d05038459522192040004803080c0070a40d18228054528213900c011814070308510030814030034403a042d00074003c40044124000340030744580c0c9584541c140c4170a412200c030b0300000b0719a02043c0010a1341100c040044403200d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 904050584 1250 904049334 904049347
    0x1d0a0e070905270d1407080403061d010507020c0105030c04050306010803040303030501061704060b0409060207031107050604060804080306030703150f050f24060d0e0303061e011b02130617070803 86
    0x210384d2030802500c200c08100c505211180b25020200c29180c0c4140d12201d61500c4545a207004005000c2c2e000034144044500340000500200c14041c0600612040d00600401c2650314011211540014002009124104000603240d181005658000d000c0d03040070b151642e00310710b0002c042e41c0303060703000e0010000d0001c00c0d500e66055000b06a60800da02000000702882d8803000328014100782c00c80070341040c2c408203c2c1c2043c55044040c0303080da40748920680d200562100c0030403140f07014900a120005910310005030025421200458000e040201110304155899446407000000424480d00040c0c680300980c035800c00d980030300c603005001c803030105440f0f251841495540f5000400301030841c0341002600002a122281140e405400100b0240306e40021054501e40c2c07a401512494083d4156a03004109402149443c1101190582d10b840250408078000c103141d11681d1000c0ea84001c4000300014440b415100e403000405046002d260001c02c04140d01d4206150751344904034070340042209 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 904051834 1250 904050584 904050661
    0x306060306072f16050a080c04180c1509120b043c0b0109091e05030405040f0902010e010c080a03020a05160c08060a061d0a0e070905 59
    0x300e82d445586840c020203220128092507514501c4800314014500400c150204030850105003a9009a0000024000c0c25903800510503d90700341d105248440e041030130000e12520f03042c0c00030000081c4583c5c004031003542d9921591404030307541c1d00140350b441c0d07030759410010160405441c900401140304140c00c1c210f0307192034040c0460001080103260310707075400f41e20101e00e80d08045800400f5908200350a904d21030807007102c0046681d441903a0340605000001082041030203040140303580b10441c0c035480d0380c0790560f07050003491400040300c403800140008a1640c44600c5002c0d2184070035036011415a00c50b000141149003d80311990400c04100c21540129421000b00c5040c042c851a0040c0d0340c00c2110b40407102809400075914890819611020920130010214015654a007096030a1a1542070100080b1142ca104034103160780c4000b600380400c1d0005611a07401102000042620300c8901c14017030408106400420030103540b201030011400340382c00002c14844503511500200c4601d6040c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 904053084 1250 904051834 904051843
    0x110d090303030203131a18030903030d1e0c080f0a0506151b03040308070605010e01031115040302090421032a0e12010e0c180415060815011403060603 66
    0xc0501810780000100704001c05032080c0d0904c080d000b1500d01d20440301056420601d103030540c0d002003000500c1c01c12265001c40442254503d04000300207501c1c07e200414208054081000c003240e00c904514003d001005450050540c3c1200c0c5a940304c0b07480c5000141c2c5911240050b007000007a40c42e02d42008941c2d1562110611150550a607598440c2d0310707081e400751384503180c602c0c08a15003c0413500008201c5c4442c0900603091140e9010f001356070300c03003c0c6402e510800b44800b515007468000110894248040c01d1500c40700310007071191074191a5000f091007820140c0b404c603404011414078040682c1e456540040030300007482c007840581008a00303d031000c2291620800420704410110600c18002c1103c0b0402c10303c0600046821060f02d01c00500820710281003d055001c0c89070048010319011076050340624030710700f590307020343ca454a5100181400c0d104403003110395502c82c0840c0340396003000300075140c4098250000d065810418078803407180341c209402c1c4c040e9020900f0f003c140d590104 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 904054334 1250 904053084 904053089
    0x210140f0411030a03170f0402011e0e0603070c0309150509041d010509060405010501060801060f110a170406030b0d020a030b07020a060c0807081819050c100c03110d09 74
    0x80c1020198441d401c14105100c4180802541031041900107004c15400070f80404402c40c42118144543d078030890104828001103d0007030010b40000400700c3c807a9201c01c1000d00c66441442c2c81132300d60068002140303ca500c26a4083d01156903142588100b5a0100450014103940b01e14803502081100000d0503074040e6262403813140d40c84240c0b1400c61a0101000150914810020b002d035041541c800340c1c031454256419182542068000304030503000386c60850494010380ea0b000000030300400c080b500000c0804416045002d0005400041003c04030100071140314122116a902c8c0b5102020341100c0c1c04251150244045c120380d034015954882d0b24200302c0f500080c0c099038550796007504908008100d81d0081003e0324107a160009143e100c501d891260311540c5900d4001d4171400c411462136170034a45042100c0d40700c541c0c900c0c0d000381e40131612404103204034215148181c03400b00140b03000740004107030400075811214400c1810f43c009141d0610318030301e002600d131440034550002d0001d4801d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 904055584 1250 904054334 904054351
    0x106050102100f1b180b0901021207140a030f0906020106080a021507060204081b2e0c1a07140408030304020904031101020310090e0102041215060305100b01021014 72
    0x401440b8850300300c903003100f410720350b0b00ea00d881210800e1300300190450405421401c1d0800394020085000507449045903d000e0701600104900380b15503d00b04256840303d0000c54400042c50aa80c104600400c41c0c1454944072341c4403090b00315095403004249009640c0024116030514408012112010807110500b58050700c0b05a6001079a16030360221b44a2044001c260510029000a6060340412040d0200126003102d2440c2402001001010060000c140802840d45240b40040c00d00e000e903001c641000310b042410980010740c6406c078180501442400003d406581004180c581c414a2455549610010300c2c0c00d090614607256a40e001c0100000e0040c0c10b03c00100c0c00f8035000c0c0c102c0300c41e500c403030b18000d41d46e82c0750541b1a030982c03900702d229080c9031134240401c1081860040c001e94007581c2c40903c10304c0c0d9910300d80d22100144021b804620740c80340c1d500c60340840480c0052044640f011160040464015410b000081c42d10001d00c41d8664030038a848030414142c41030340c4c107068009040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 904056834 1250 904055584 904055591
    0x130c0b160b1f05100e100309120e0f04090204060b0f07020a120c211401090209010f0b09012708161d0a05060102160801060620150406090b180f010605010210 69
    0x4c141c0700741c072418030321000c503035120040c01001444180d240e04074807199481088922044c000302c0c1c000361002c2514a04155112401c000d00340d090b402c06501041c2014002800424051381e16410861198030101001c60043c0c00004c000e8198249002980000d002003c551000d981440d11102501d0707580c2d000306d41c810780c0e40032000594481450603000c44a80c1110203204000b4030ac42450b4000c3c001440120b02035500a0000568541440218002c90340452241490f180d48200110784c90b0703400800500c9120b601186500264072480041e030040e0000c0070062403455441d81310034240031015440160f04000b10100141c5040030080910b800c07242240022420352a0400180c2c01d086008200c8001698030a50010355048150401002c403002519242c4c1c85030303000c010a20a018001c1c210071042d1f0b000b20702d00200c4201d003d50303070380d03005d4001c49000850020f20360710042e0841c000c2e6040c11462001031980d01b5991024410106c00c07000c803000030003181d442c0c1000030b900d0b40b440c0007015405c50368 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 904058084 1250 904056834 904056859
    0xc01110c06061915050c1605060a230c01050402091f032d0c06120908160305040f0332070e090f030318150c03130c0b160b1f05 56
    0x3d18220040151060203071074040c4680d0400e008129130804040c00c00c45116210103440400c20910004080c1c90000c2c00c21403811003a02821356800400300d0542d10b0813021420100f00c695a91800343c03a46510741400442c0c0790805004004080b07201400150f031034a401d20000b45669001441d0004072940314074509000304400380200b0030018030140000a904103208143c08101e0011480c10a03940302d5140c40704154030200c040f1044070011035000306401020080c0c1103512840405541103540300b031812601e016114815a02e0f0501c06070300071a202d080e40035842188003089455100c0c6202c0c0040c24101c450145890150f42e0381d071600c0760140c8691f014000c260010418080d07000060b4020040300d640b41017650700082e501d843c80300100494010305168005004101c58003502565128002c2819601c0b46440d036040d0810f070150032541d40c0c4007180001006010749003d0410b40081c0c8d2040c1c84000400d007050030025030000e1000c117005003401c142d051030008903010b540913144143c5d000c451860 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 904059334 1250 904058084 904058119
    0x40623090709080f010510060905032805070605090a05010c02330c0c0f03010905030a0509030a330c021b0d1a0103060f15050d0312050703020c01110c0606 68
    0x30380b68002d01d0f82d9004041c1c19001480b0705401c0b650003520410089605241d6810040b142252540038150341500b10440304844040502007240e042c00303951103d070a0f8001c05940e00c500d420515405040400c601068020b4a864200d030b800c0018102800c21500c0c48019a00080b02805600344101c040508a180c5103103a560214250340c1007003030003441d141d0314800348000669400780c00402e14894010014200450305040c01002001d83d031020040d0f0a02135000c2c0160303410b40144803015090310a4010100216003900c01109030485a10b86000010f82c40b00d0b4809403603c481380007100e0441c00c117860541040d80c00034400c1d90b100300c01c4001300b01000c522800101842c61798100038000c185d4500154184a140115242c1241c1c400c8601b003007001c0811501c0c801355441c0f07070010410340d000103108000b182080111340c80010701c00d250900b01d041d0540b0a00f800c03100c056901000181d40401e98190001c0300344907881844000c3d1811030b04040d12000030315900c20b00108940d00885e1030900000000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 904060584 1250 904059334 904059347
    0x606050402160203060108031306140d050103080d0c0905011202071a010b12100302090114030102120a05061207050a090b130e010209090a0902030715051201030602090406230907 78
    0x2000020025591020498180c0c42e66074a401401d038481d000e0031000140c22200041110b1711000780741034820301c2c1443c20000380c40c084500111015034280401094103024018490b09020718400e01d445078580f80160880c000316018003000c0d10501c10baa1200340076681c1c10078212054026540c0016075910198500076000c801c2c840014610f0848100002c119041004050150100720024144460362030110040e105d170103611029400000000040c0300341d17203800d00100c590040c0035002504d005e02c03803810011a01e0701121451500b035901d00502150b0300e030544002580349101001824000d01b09000903240c410240300380708010381da940781480320352500d4020390007031201580104004000e00361014042c0d4420002c01d0701c2603580500185040a0903c01c05014a4019004041150a01301007000e0866a5181c8505020301840b09a03604000b45100601947c415880980c58161450900c815200541c001c50032144842d800245c40180a03110024006400c4400c03440607200c0c1e16058078203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 904061834 1250 904060584 904060589
    0x15060f040e0106090b0904080f09011106070906020f03040e010b090a03050a38070809011b20070b0f0f0d020f031806061011011b0c0303050105030c0d0b040606 70
    0x80e0811101d2507009038107521400445450807001e00034070380c20720300f045401002290020031090b0180b04040c107004665020b88002041070514080030488034505c03a2502e08100d41c05400540440f1060000035414440341c40103c08030303c0110305103802c3c4079980d405014140564609498040390303541d40da596100c442c6000b10b402100f52880841d0500f0040754800c520740703501151034045807008107101c9480007142c1088108001419076a158450100d07266034001d44000129900c407221454150300449942c031030304805440f05452284103c10b070b00b044c0308031801508680e800c80b0804002040b480b800b1100e07589032303c540c000e945600011081d03080e4045d81001e11040d91022401c00b0000701000025400f40b04007044038540f4601c44042c0950300e0750301310364898104440b0008890800e0040d081c0c42e0500d141c140c0042010300c5a0016801904002590400054850140601855018440c0c2d07405030005074080d00129000780040b030340c0c6881c0c0300401005101d48a001a091140a5020a01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 904063084 1250 904061834 904061839
    0x9020d080c0303220305030403050d060b03070e0f03030412080a090e07050d15030507050118050603091f0614060c030c0f1b030c09060f01050c30030915060f 69
    0x11108a00040d00340d50f500111107101e402e240342e8000c10400c0b4401c1c00741c1d4014690590f640c034910303541c9030340c00c5840360031050802843c0c0c3c1d01d460b004200d148403400510710941041e500c04142c2c408030f404001890355408403440c025042040f00303200d016801c0c00c20200382504640600d40e03030328060780304546211990b070005000b00b004030706008400354400002d01c2c000c0b41c14802403001510074036043c58810000d200041080d405600200155405104120303240ca0080c5a82151107548001040c00342d441140d090400b80c0000ea1134201000419100410b04800c48104100c0f80e8103040c054510100c0e00030100d071103040041528503a480041084400e4114040142c0351500480a4441e41e12156a0224070345500c0590141c2030b00e0800241c80c1061040080955805450306001e20120b0312011a030f039810024100003c200c610f0040000345084450b81902c03083c404000f80341540a415080c46803000b401040050003422034000488502e21001c500c0021941d449140000710002034041b512034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 904064334 1250 904063084 904063087
    0x5091801140d02132301080d0e1002030d0905030706060815070302070213140f09030c07030204110403080403032a030804020909330703060b1e310b030c090409020d08 73
    0x10a440e00c178115100c4070046a82800c4100e0340c0311029252103001d0014210001070307103105050803a143c500c0581d840b5001ca40180d030310b01a50b0300350f14000d0354017810064580703600c00035490081128900c10107008011680282414002e603d202903130b480d801500c008101a00851034000350340c1c481082c95541c2d95501010015080280348035040c038003044400b910100c941c0e00000d85003e0340441100c101440103400380041c6421a420070008100583c03403080d0b19101804040700051840b0000d002440c040d0300d50000b03141083c80039042e86120700407940820000c034508400000e801603000d54015504440804041d542c11041524045d4007ca03098940252030300d025500c1c040c03c0c68280400c040c000c0c0e40c0c00060340e8000040e0142c40d510300c203680312544c08101450004503044801207100b0746100c0c074140b4040c031140001c240c40191041070b103110f130605214501e141d0302c139444810082015074820390840ca04907a1028480c0185480c590007951a0840c40b800c641e21448200d28440c0e201301c020303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 904065584 1250 904064334 904064351
    0x120106080405010e010b0d0b091c05340602070204090206030112150c1403070504080a061a03010b09010b0703090506070b10170d03020f090d0305091801140d0213 71
    0x140304440c1618141c0b000e504c0e0984a920704007040c007608100c18805040859070130b150b130751524403480d00145031a400c1c3c001c003061008403030620302072200034480b241c0d112a22061100400140d012440811b901500c0e03000e903001c00020b030007002d040c9819820820050321115a400424003510700400025170200740003002080c0c0703000710b640705540f4901500c005990419400d00b00000c80c0c3e92440740001180801840f200280c06c540011540420321f0f140803801c01796181e0303c4030310740001c0e82e0f4112081c90321280b44100d490480f0b20310001984040b4000d1001c000b105012a0200c8418007490b009104001469000c0c54007400d01d150003001d01030030300755880b451800c1512060070142d44610b9020200c4100298246c180c0003680445c0c0040380180c202c91580c0c803000c0e4000d60020701d110b03940c0c5c50b06004080707040d520942c140329414004c1d180c640e83c5020240c100180d1820200c00118400c1069006100c1592141448550a201070300c0c400022000c03400003422030f040c044161009942082d801 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 904066834 1250 904065584 904065587
    0x2011509020d060b18101206270b0f0f01020a081204050d0801030503031f0302031006090e070308160501090c140a090e0606012f030301050f0a0308070303020a05120106 74
    0x1072900c804102c00c200507007030320381c04200382a20030b0200f041483c4070340043c07041152528400c0c11070321001c0384c1000c1c140a402107801100381d40d07099200035180e08444040c00c0e412501c0702041c085a60240004210f820140d10025802c03c640c0501a40595807001181050703900030050108183c3d0820100c079200c0c81003284031194981c00b214110b8160055660322030300716015450560583e54001c1c00380d42199940c0000b100007240114540032500c50f03810f00007001d43c406110218035001140300128070b480c1480440c205481500c216804a5401010208081804c102c2a50321540900c803602c401003c050801c81d000d046414009080c4008a202c001240c1c4690508601d517032409407201a050359451000008a50010064040035089600050202e40c46403040da80c198501124021048100700550358040e1760701c03d02c64600b45d00000061010b4030f04402c6500300d0310030854a8004442c1503503910302150003002401428550080759052000340a40181c0340400f0b10040542304941c0d44940 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 904068084 1250 904066834 904066837
    0x60213081606170403121803020303040b0f060120070504060b0d0621020d24020406030e0609030403030503090102041509030308060a0305071a070b09010e0607020f19030201150902 79
    0x7a500c0e100c100310310000c1e1441c0a118070921a801425500c902941e0b07540b41507a1041025241d0158a5515845e1401c13201d0024504807006000741c0c0110307140e2400c0d241040c0901070240c400b0b07002049042c1001000d130391100c581d00c02c00684c81c0e50800b00340c900301410382c0303080702c20381000390302c60b051280101d102070b0703c00082c0031a100401814001035070348681c1d2800301510b080508401c9200c0e008140003608240011030b003402d10030034034621480721040500a4024008401d1110343d41c000a04010055040c02004414034000303002c0d1072181003964449940c2d100360b110040603c074000c0005803a499003941614020080c05030203144e5001c200d1401080c3c1d0b4120701044010841c090086440e80c20400122010380b0f43c00760040140c81c1c01c1c60030b603ca0301c81c008a41d6040c010400c0120344c0020b401140c210740599020130012900c10f807a10442802c0c00002084201190311588180b01d0302580010f41c440164400e1030500400c01d2942012400341251a60541d400e2852070400100041e20b9030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 904069334 1250 904068084 904068103
    0xf060a0201061a13170c01030908070501141504020306100c021503040303060609081603030e03191505090303100e0c2118010209181302150403170702100c06021308 72
    0x14130b03520080e10750000c0e696030364100c40c10305241d0b805481c80540304d500a90011010364042c1d800181464180c4e07854a00b906d000c1c1a80c42c5402c41d000e41404a8500120480da40040d8210383c254210700d05000420100400c1c00024410886850840310a640b600448840c510350840101aa24545424081c0c0a42862b00c0340e40000b5948040019000e0b2002c00c020180302c3d040d60a004000f447d60320201e43c5a10048811b6600d40220082e90742d04d0060403030060125849200c019100a0001100d2011220020010b0300d170340c2c204208000c1004004034a40c400d9401c81c1c4110f5003180c454100100030360241c1d40c002440e4a0070044030001180c080c00b506071244000420301036552448103601c5080c0c5c001c03030320001d030488aa904000801890401d400754484480003902c030048c6c0581d00085c04090205c02c0ca0b5080080014080c0b00340302401d2207648072101010700462802503658042410800c90040c0340040000480c4400108078158040325400010480f0540501303458502498541c036065 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 904070584 1250 904069334 904069357
    0x1605032a04092a150e0405190606030e160e0c0c031e2205010f1d0a380301350f190c0b030702010905030403150510050f060a0201061a 59
    0x84800180c0084c5001e000b111290481d81d8030b005094140b03041c00094180900443c075119445154003005400300c0c8942c00040c000c565012481c3e81064a18504140c030180400c5140d070f03001c1c2c03818850051002031407504858442441542c0c3c0701e0380e4601c10b0640c0034515010134000000c61040b812480202c003d4807400b00200654202c011b500341b48588817a94500c0b42d140816401c1e4551144030340608a0301000035160811140720800308800a110100c15410110b55010207451600710000642904455400030500002c13174245050054611400144640002c26000e17000e0105030824065981e0f003204a214110303500f41c40c03502109521411b0347c00340c8200c01d11a0081c807540d01001c002d0307818451504400d010390801e080601c40860b581c0300825081c250741d00e844082000a2041004200075030007007601940c00b1107940140c0060f6078010303211100c2280149010f10103035031500640504c1000854a1550321100444264003500043e07002c640c51250b080000c40411032120001c01120300207 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 904071834 1250 904070584 904070663
    0x80105090a05090d0509041b0f020d0e0f0432060f19030f050a0c0b030105040b12071509170328020a111f021605032a0409 54
    0x151001c4800301c4108960f550f000b540b12404100586000c0c00003462003400141000c1280010002d403543c032580514400c030700150b070307150000071f01c95814462010301d94800d18004500d0100d0600280d0b8002140131058410350b52101c144585d03104c40c222050402c8140d21340307580403510150745c0c3c7d0180842103071000d00412400385001c07900d160140c1d4900c00180c48407001244c080c115181e0448020003858201d5003031140020050200c1c00c4007a403680100765194601d03a0720340c141402d0109441d240440303903020701d004045499000754003051520960b02d5102c0c00412186c8004002c80d9159015407004410b11020444403840800210082034445142d07a407000401041c03840414404242101c0d0a0041c0c00c00c0c15524001184a02d2100d200e9200a212856900001c4a41d02014240400306005030b848070130324800e0740341d550015600074202180035020034110b00e1416558104d102c0541100200c1c05c202c0500036640320b0707100c4080950404004849041201c03244c05042c003c4d0855401c00002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 904073084 1250 904071834 904071841
    0xa0f0c09080d090b030a05222901182c0f0105010501051c110f1602030601060809030a0c050709050c04030b0901023906090a1a0f07110c1008010509 65
    0x440fa948100e0351105107041c695500c140303161001b0803010341211b03c9082c490598005c041e0050700c04441080c040c00407a655440c009060714800fa28454105100c014840c00400c100c51158502102c401380805010419220540d1610074401d0000f104250002c4070107046080c01c1e00001c2d140303820790000c030020040390341c0755401034406014030003c854100b4050207548480f030304d003038000d941401002807040b4180845070101c010b02d5005216802e1100012001c50419454100600780c010440344c149a5160b06040160035100c0c41500b40003000c2c1b061504144003082410803142d00180403000d0100440d086c00d4040401c1e942c098030084d903121803400d002c1a400c402c184201d40c000c94181540f80389640d11114000307074500c01c05003d1b81c455480a800031074411014004a4032400c0071401502181d00302d46062540c0320102004402d4500d40c43c01041058055000ca0980110281c10f21f0070070b04451224251604803089040d64014101c480014282600166203e0607190221034100c2c241c1da = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 904074334 1250 904073084 904073087
    0x60903031b02150a0903060504060c0206182512050304050a09020901020712060e0f010618021201120c0801110d0605010c051b06090402042312060c030a0f0c09080d 72
    0xc06040280d0f000000c0070a25500c2c4241c2c40003441c035240c060425844c0d0981c0c0c1c1d1942d80855100321000d40e851500c1d0855505040ea06004450303001d003100310501140c80035103065a075602031040071100c0b400ca48401004004000300b9200300100004985004c20245900c1c16940380d8020348103180c06110305070f01c08a00c10840e402130710501c54040e0300620080740303040708402d903d5005d07481c29521a69a8071a250102c00140144c0c04040b01d10800820002d240002652813804d04d81403010310140b041c05041c05c001602c4040a044070301c0404441440740d0542400341002196070300a488640c6802c04039403484e14244003402880d02d20b00400c01c41c2642d900d00540d040c0c40c5814005196800c000140e800541807201700403030554011301158286100700002c00c0403a4096000200c0301054009400d100101126028052550596041c00901042e0045c2956130b0700c0503040000c0343c0d401000246104542c1e0340721101515613110184404000301e480540038900300d02a1803010301480c4880540107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 904075584 1250 904074334 904074377
    0x20f0c0c24120a0e030d0b090a0b030a0210020f030703020706090506030124030e010c030b041a1e03010b100509190f0b07050a02031f0c030506060a0305091606090303 73
    0x55644600740362520b281c100050030100100415052559040350014601040010340420045540b0001c3d0310300c1c8030b00421090b0700f4000d200c1031043e810301400108503140829030740345c3c16505664101030031890301c000b80d003460b080000b0700c078141c4404200c104c1030650000b1302c0c01c1255100e03240c0302c01550b1584e0138001b0510003402110381d99a5079070f0a941030f0074803205d20102070780c0041c900000c801c5900c1c051039083d650f0146100001035214040d0405038902032242d8004100f480808103001030340394000c54029508042c40010348082442c00c2c0b00c01e80c800b07402c06260098010140300c250100d008024040b9001150003a00035032801c040e41da4061b004ca484d110a59000d00029000d06180c00414061a071103140200d645000d115080d80040e2030803c1604010240c8280c3e0709200c100844449003101ea007440210708060a00082c01003546031a01260200891450041425601c0d200480d14001c031000503d1b00018031501c1c0003ea099010282d1003c0e244244c0d1510200b465410b0181c3d4075 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 904076834 1250 904075584 904075639
    0x2006071203060e390f0a0e040911100302071e0303140f18070801061512020901050a031d0d080a060609030209010e040c0905130b010e07090b0d020f0c0c 67
    0x4803940004011480c007000f0000102101013850b0041ca80e00000a003c20181c2200f501075850300404110428465005005501c80200564042001c00a640c480001580307602e4070a6001d2a40c440c054080c05100741c040350240b51308411400c2040f4800c02c5079265a541c482d0050300020710303182944a015901c120a180a444000410307241a16a0040034842d82d141d00300000303061003144400540e0311002e0041c1e200610500108041d440702c15400540490042113480d107140e84100080005a1707000810381c0e000d5001407074006241d00e00390a860002210070f14184807079100b051410340d8403d41c84106e062244c2100f840034000d003607031410262044641030000a500216440043c0b02002003005207951140c0a030012815030741d591031300c41044880c15a8100c20040c0d2920040062120422610380145071680d0740c428640b901079002054010f50340201c0d00c1007030300004e00d001d9031500340d0140c03400455114200c65503501c170300a070580c0d034a2881180600441c0c8a4510b8200511240421000d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 904078084 1250 904076834 904076851
    0x3070b0919050d030b061e030c07200f060408100b15030a0506011b020306060424080606180601020c190801020f030105090703050403080c0a031e09050705030606030a2006071203060e 80
    0x101f05000c100070056604006c00c0c09c8c1038103000b4081c4e40c0201d010508640700c6061620b40300340e8120b0005060110071540c45041c103026243c10070007040f4803100041c4141c40e00c1821180010010603410020b600452072607110301800714040103000c1100c16030360010740071341400d032150740ca824440380358604180e000410295243d08010000b0398241815000803c01301001b0304130b80c001940000c41c14082d0540c503007091410b0b0b03000f14100802c03400c000100313840c154107404400c6103a140242c0000d640c0c1c80890f040a026a50101501401181003070080018003089002551600090110440103810910070141f048051001041445019125681c0101d0b0940e458120950301c40207410020342c4801003460406646411112004546400c5858410b20118007c1281691800c04516080542d0411072003500800103000300c40e44c1c0004d0b1010802e50155401c0c2a660704204c641904a6064603680d8110310001242401c01186403861000920349450800c0a5501c0d00c1109206200440b45044c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 904079334 1250 904078084 904078117
    0x519021c0c09050d0b0a020909161d0d1e0602030c0c01140103050d0c0503090a0e06031c08070c1103030d020418050403140912010914010c080903070b0919050d030b06 73
    0x4c000c241c85c074901990144080318054541101c050104401500490b047c802540c804c0c03c1c9041456400304442e00040405035911112401640002c1c00c2c050350418010801794001480c1400603138002c04504469400c170f101107480303141008505803c0d9105c04403420455181102c003214240004c082541078a41120040c1485003101e0f20035200740d004560290b42a00c02401740c01010358603d40500e0240c0fa07009000c00043c101107081c985844c030070309840c0340a1000c5d0115032811550200d1003a80c40011450300120214a900703007040c2520001039110b8050000241c844441042070b0020b10854914900d9010481c010400c600101c0d402990000d000500c031a08142102868601600c4003040041c0b1141d0798a00e01c20b83c050071645071031000c070382c2c02030f84040e0814140802e01c2500c51a800c1820121100d25101c0f00160701ca00c00d890000f0030340a0325402080c0385000c01c01c10300c80808d9664180108500312800c016035103400540c58240000d040544034507403418000c090341c0f021000030340c264 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 904080584 1250 904079334 904079359
    0x7020d2705060717160311010b131a0d08040509090d020d030902120129030a1e03020a05121201120210230f0d0e0a0b07030519021c0c0905 61
    0x41560350141c0029109060b26519101240c3c01081c020310b91101e501156004950352442c02034015000c1521f40822645082d009030565201c040040040e012804000520350302058662228110102016500113298008450812000c00d00601c10f4030303000c07194a226950341d2820555204040080705c00141c1210361641403540c025007050701c1c00c520003040d000f030920800102c1801c450840911b43d0b01a942c1400304106142081c8070066030210980140c05940015103034080309024100d01955510b204103501c0042c0741c42802460341041d40314041e500c1c9403c491100f252250824400c405e080340e041c50002420081c0783c10000744c02a4043e08050b510140701c0808e413030300c0c2c920394640340000300ca08030488440c1d603009000f45030001d8820043d64403103800c030800c8802c881c83c0f0040c0c44281d501c4400c2060101d00341c1c02016601400c00e24021500e6955003c84900580701d000b400c0c5080780c000b043e80300e1102e6182880705000b0300c0c080003c00001d603001c5022240420944242c6404c000c600d00350 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 904081834 1250 904080584 904080589
    0x3020a110901061d013f0c0905190f08060a060602070303140a020f070803120a090b0424051302042004090e1606051e07050705060903010b030607020d2705 68
    0x400001041410041c5240d0211400c01d400d0801041d4120f003650000520301b1102d0720b4103107090040403011003082240c5418500050000e41c0c132801454071a0301c1030510307540e103600c0010b0f590014040b01040003c5042c1e031107006a584050a03038a40035402d08140d00491050310003d60304c801c594141e500e0124400d0508150899039000c2c40d10380045004041c03503a4a645010841d10008241000084d99288006c0e118098039450141071189501c0c100311052001c2880c40719019005500001c4811001c4160110102c03c04d61000e420400141031104020300d01f00603e085040701c170300917141071102125400800172410220024014410000d1100344500c08003540000d14591070582107030014035070038a043c001441c00da803000d0006480040c810701c0c0700c0801c0806000c0e0305a451200b038284500c641e2038079202c0b1324500a580c00381c000490354104556094014a00c400d00180c190340d41d600704600000d403074590700c00410700403824000c0b40ca100361480c9003038401154010703ca05e40006040008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 904083084 1250 904081834 904081877
    0x20105070503071b061713080c03160c090506102f1515010503010602120d140f06040506010c0203152a0c01060b0f1206061603020a11090106 62
    0x1000c0d5040c0c801481810000385403c025002c81e82d26903800d00520919000f40101055024013481c1e005003019802d00c10612081280c4085407070f80314100d161903050041c1607a10354041c03280e1a012f841301030005041840f0510070a44103a036007040c41403003203544100c2070101c0000444402000144c1030341a0802d032030313002407940c00c07002c0c07110384154400301e070030b10140c0d14010a98030440505400c1805000d0a10041e000a80c070300c41d001e003002d0703007150314100001c0e440729500c0c00c60955031440013841d602000c2c02540a0401440019011039460400144000941c041190818003540c5440c02060311903004020941703000350b000300100041402100e07507a00c42c81003d0407044221440341c06807107258104035500c040320000000310740e071540c001c01c1e0071074290b4260382d10150080300c01b080f0750311980704010100da0810500041101c2030b502c82d900424850b2107401e142d035046d0191116840308041e40032402c90030b2107010303168107100c9840480800610035801e12424000c64820004d00c000080e501c2c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 904084334 1250 904083084 904083097
    0x6030c050702190b0403060b03010506042d0209040c0c1406151c05010509060f010f05131505060f090f060f040320091617040803010920130509010e090703020105 71
    0x88030740b80c1207644c601804c1c0b6a60029042129400d0b111101040c0d181001d105030340d8400c00859091180200d60107441c90740701e0700c000c8003106030300300a8401192841c2c2a0100c0d6004d00000c0d2040240381c1d110b0200510a843c86001180c0801c403d40601c056011700142c082e000e1494130401c4614020710b0000c0040582d0a40c0030005d0801b040c4030a500812402c2c4a010b101d484103501400152800503018070303050505030013040c5c801141141c1072000303403a07610050401d8628030070001a11442407807164509401740d440250700440001ea005068051032000d0301441000b65098a0140225801c00004e07004820459026810510082001c82e2445421500d00703551071310521200e01001d07011490240b412a40b20b01c4481151004400e51640091300d045444c07640c071030345d04d03040c209503503240740d1407006216541c1e0799034884844c083c00094030445140300c41444440290b0718402000b1080d0120003908c01c0034803420080000180d10315400051511810180c0301070041e460071540152616000340 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 904085584 1250 904084334 904084369
    0x15060501051b24100e07020a020d0219060207080d020304290d0906270309030b07090e0115090f0305030d090c0e04061a04022712060114040606030c050702 68
    0x111031038902c03030804402525035065424009012441c0c8800304d15201c8405500481c0200014000c20500683c0420b0b2441780320703812680303d00350001d5400020b03040082c408006001a224a100203a62a00080d406d41215540c8003541c4040490100c01d0340c5900442c810000360060041540506200f0195044003103092110018281050070a00d0740444a0322413007115000c1d0f42c2c481052640001d01c2c031105085001465422020100b035a0003010640e06100c02000100040d0114018a0041c0c0780c4202070030b02c0d000b48008070b42e5a40c0e28603001481e400c9134840841d00300c050214020004e40e4046c400e4a0b040b03c025031a01c1801d14906000f407036a0407058a0b00c002d9800045070b0400f00010b07490045006541c003160040e4451560000c800004461610a501c100310034880c1403802420000390300720b48005035400900740300100e028085008807101a500482c030003c59a0312107901482040b01e41580e08101c42d03616001d0690440c2d0b4035000b120007241c0c0c00e2005000501e030880144c0c0203100b07103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 904086834 1250 904085584 904085593
    0x14070609031e0905092d090c0d0f0c050f013608010c02010c0e0310051816031109101509050303030a0606030e0c0a0b030919080715060501051b 63
    0x7581480c0e0700c1c0c0c2d44842d41c503800094000408014a00d40040c2d03168001401304c0c101031801020420964074414402450b24000c654100040c10b2014141310a1100304405407070660500c1c03840c5000c048202440204940300c025040c0c0105590900c0d50300b410200c401a156074100d0b07082e5101e46c404140089103011811041140c21023464140d11056400400c0c1c081c0020038201c40d5148040c0c255109130302980200000d01000301c1c003580e4002114107045a0325180040d50f5114a095525500c0140b480714066110764a0a0900004c4084030b05040764041d0b10389091545481040140951060320f90030003620051605000111a114154490160b1030030320741c01e620758690102e811904102d40345005545d440074100051034042c09130640d2001d1b1140984044a01170000071544000ca01840030b500f200480080c0c40c0b80800c00c2024003c66024900c2d0b0f660140501d001c1c07015610041c402c96220024181c41907500901c0e00850f41a10070585880c0d04046c1d9034500c10b0b11424461400e6200c5105 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 904088084 1250 904086834 904086857
    0x901020c01081f062a0305040b090301060504050c090a060e0f150912010b030708010605090a0504080c0106080307140109020904030f021204240206101206110d0504121407060903 78
    0x500b052140700800480d265149821581501c0e002c017640303810107401492040062400c0000d038030100315026641c2441d001c40e214500c17040402d005110503002650414034160900c05c84155090140000240c02c54542030b25a4841e003086480c400c40b0200c1540140ca48140c4900da482c7c000e0b07410a182c11803030980790804420000041d020089001910a03a135554540c0420703500741400301c1005400f240c0005c0c08018900800b1075a1110028801d005040e03031a0007140070072003c40708980c0c074031500c43c0007844030076220624035840342d0014004803034195a00c1814000075006000d560300301500144203184994807034600791031180c141c1c0c55403002c50142c031103503041d0007101c00090405014561202e01c0b4200d4010005602c5150804a00007075600450801c01100c4c100541401910703101801e00314000183d00e804800740c80c1d000c0d4030b01c6086002203182d42c200d0b110360744006d1040d80521301c0310f643c04110a00994050881c0300c072003041044100705101c04070b01e0030b4012801d001d1080c58091000d50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 904089334 1250 904088084 904088131
    0x1030906020d0606020f031e09040902130f0b18040303050702030c0d0801080c0a150e0402120c030a061a040e0c040306140f090106180e01141503070b0901020c0108 72
    0x28410b240d01a241669400203000681c0e0400c440007000b00f646008601d030102038450205c45000d040070350161020001121085612950401c868859020b46207524010040d0340c0d41010b0b0561080d10308440d85090028401850061148442020490b00b044041c0e12942c408901a00b401070581b01948000c21515180b14030400c05c481681000e0f03a900f40f0386505090300c55040c00d50080000303200da002031000f0300a0054400a8500d81103403410712144c190391580129000c0e005101030030164101c608104002c0f09000350065200b07404220b42081610744400c3c000003040d482a02c00100c0c000148000c0c0914214000441d8100d580320121600b010b5607a83d620b016211081c08030812441198284a402041440070326040f2456800a008440c204019640c00d13011501200a9480e1514980102d120080d44140b0003070182c40d28020283c6090b4050003070303210340000018082c0c03080e0403000504441e03040035070380601d005074041c090603404000111034411000d4034117030881d41064020702481 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 904090584 1250 904089334 904089337
    0xa030f11030a0b100f05040203040218101e05040507110c060708071514070f0c030e18151008090d051e120403080a05090a140f030304080c0c010203270103090602 71
    0x1400c0c10312019041c0c4d810281c0001e4030003010f80c0100d000314010700503c00140d461443e8051540443c96500000740d6800c0d0107040000d10580c0400080c00899a4039040c11255581400c10740d4010b4800b841691222842143d080d00302201400091700018902c03100c903c1d09000030610700d8081c12906003004401d0312540440c450b42030b0380d58001070b83d404901480000903054550b00407110704001940040c0c2c50006401c0c5000440000d0400900389114065aa204001d0007404100390011050758600310a000c4004604011114030070081007044038001441101c03410320032100f040c00303881002c40c60031040e201504240c180c03c000700f01c2c00d10501d10a407010000382c41c103100b0f804ae8524560901c0c0c20302500e55100600440e040a0400d810441c501000003410120958022070141203200001079071800d140c05820048042d000003c1800148079090002e80110082d5400f40e40d2840801001a43da03881090b9900042c2440e180c0e074005c0314a031200441c5541c0c6010b0401150540040d9100008c9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 904091834 1250 904090584 904090591
    0x7110f0102090a0b120a0f09081b071e140102240a1406061c0b0a0b0d0c02010e10020c0312011706150310050406200a0e0a030f11030a0b 60
    0x181e5010038008514070f02040404014202250003528010551900c24584040205021031258403641c48030400340e05a030104481c2a00450501d8960000d07016440c3c2580703107041c6444040c4607646000c20910145504600e0149042080c000c16078944100b07000550f90903041c0740d05501030001144400c40e0080000a0303550021403a541662800042a201701ca581e00070980030041800d0810000781c40310821101a08248002c2820b80440300250078041e080e500c07a241c4e00049002400511140c070340000d089003020040e418428000c2d0710300300701e0880b0507080091410f0303807000c80d8042a1904640c024148401c030b59007500d284c01e0743d107802440c20020a9100a06042c0d40d0707020000c400400b07000702500300110f100b1400e180005080042c1d5110708519008400a5a640c003007010000503901249070900c495154812840d903c0d10b800400740c000d45040c2c40400c0c4080010210f034134181d849082030341d602070150010302e031080d16aa40029000803031031303403d84140b40720000802c944d212203d10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 904093084 1250 904091834 904091863
    0x9090504082a2e0207020d02060a030209010e030d0905060a0201021e19020604050622050a0b0f1506030c0d0b130213050607020a0905090a1a10080a0308070302030711 73
    0x6550311011083d00e4202e0141c0b0103410340807518021400600c0501000d4105245030310003689a021600024501c00301284000354001c0e00091010803154054010307001100090300c0d016090400c6806060300d4403e800ba1400000360341c0b0301c0a00461408002404226945100050030116107006400c12400d01c0040d2090140002c01c680c25030341d001070401c12130808640301810250405030b60b010740c1e03141c02030106201007138640704007607100740c1154400c1e82964101003110a0800b180c144142c480c0c0782600d007031000c00c00e00d038001500840600c410f81c0c2000b4010305858a19580d02071560281d800114400050940b520252042592110317400c04148140f40c4005a4403034503080240c1c02c1d0040c030380c842d500410301070144d400940d89200010084655654021495645107581a820b2001740319008200042c456400c200540c3c0703881d52140b09000104200c8400c175110304180b07546410100000340002c1004002030f00702c600c250041e50300b0103480d050480c09040d1181b1f101d030500c000c081e011700c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 904094334 1250 904093084 904093147
    0x21c02040306050f090f061602010e010f05070e030604030f120612111e060d09020f220f060e16090b04030f0c14031507091a090a05060a0909050408 65
    0x441500c1e0010140c0d080440717800200881d01c1002d075180d40f00c0300d00418045940c0045070321a42064000c0d000a05100c0e0b803200208618507000070f01c58020070303055542c080040e05443c41c44520303081c0002c41b540560b4158580000d07500002344200c8210b5145009030001c25190440081c0b90700e481e1004c070034441d100700e40351003540740345800703001701c3d007800f8403440303180c501046015456515650200d4610740c00c54071000c140a4101e0001c90460325640c0300b45600203824403140510218464241400c40c18940c0d418000301c424080840142c81c55801a0480030442c103002c0359a080d07100d441441941c40c0c50505803209955003005001503005a8402d540c0f001c11000490f04001c44614104054042c140014001c19140342c04a90f4800001d040303155104030741800304445034010490b5800400d02c0c0c00040220050181040e0303225080305e1281c6004076007000e0b0104842c40e00c0e0381500c0780c200c0c550350398080d450314210b240030281034050b2081d03407074000c20001c5076290103d0601481a042d401e08220 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 904095584 1250 904094334 904094341
    0x1603050702010e011e120917030415050705040b070f020a17010e0a11010804032c01030b1005090402070303020d090627050303010608220c05030d21021c0204030605 72
    0x3d48903100c201012410070041000040003129180c2c0e000820120b2890060038411103e40c2103401031940150281c0b0b98908a05003802c4000d01400451140b40304103150561141c24245010668005a07041008598148000e01600160202601c3c046020701c00c404c03da44050b8022400004982d0429038882280b06a1070a20481c2401801300f2101200000c081d800d00b25146c0341c000e15190740401e41006003850115040c140f15103000000c865020200c8403014540024240d00d04010800050200341000c410b04c00c18901803120358218200750f141c030f0f8a440c02d21400c00009600c900300403010300d035092000c03000c0032900748207111003244203e100040e504c1098000364a0940d07880708480f030040595004d1000128040281c0781100c0d07440c103040040741c4034084512a5141e02404100100000c2010703d03083c4a014170410301103a0040e400d0b1408010f40a00031942001c103521000c02e172a040c3d442a00083c482640146031003040c2006000b561501c1480890a81c1d0080c0d209643c2e0513100d1091 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 904096834 1250 904095584 904095587
    0x305090a170a0f210504032009040809040e01060902120f1504020d0b0d0b01060336020307050913050105070c02010e0111070b0f120a022d160305070201 67
    0x303034014081c407008034280a1072280d0900e5440002d014014542e804050100c0c040012811150013400d05500410b61000d186141c000e00b01d4200d440243c50f028500d08103402c83c0048251440d5800c44007524100c1c1950700d64582c1115275210810682d00943c0e190650040e100081c410000034050303681000d41c0e00e241820880e0030704000500140180011202401802d500c464803031144031b10243d0b40940c40e80c014110301c0000b04500c0e1200c0d600141c240b0200000c022104003441e040e82c03001d4800f0403968141c0881002500915070100c2400074100181040c144120110303411554801012562015180d9003c10102041035a20140100a50616008000c428080e055004100b407600303034030404513900000e0440760812085818803040d2480c4507d442814030010020b41000c625450362010940045415580145e082106281a64021881c2161540216803884c20b16000042511704190012406020702c0f1522504800d800c021800f480110341c4001002c40707001e5140d49440c4c00d1203000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 904098084 1250 904096834 904096849
    0x1225080d020328051b030702041103191e1505060a0c110f09130f170d150e011503020d06090b0f09010515071106030117070b120c03090a020409030509 66
    0x103d40703c10070004807071a900c1d4410280e41400e1402185030200b010448075060a42c45801c41c040d4026040005241000b4400301c0198002d400c01c0c2c00c550f002e50040500e4404462260b942070300c005060340300060300c1e142550010401410012403481019603690700140c1a0362107020400c02061510128105010701e0303000701405114103076440c0000d03c0c112800218003540003070a0440a05808403142c0a01642c102c48044096008a0304002c40ae000755003404140c0180f59520941402e101c2d801d5074800c0e0700304070441103a003200800c1c0326036402c0040340b00c403940c1d080541108155081c480605050036501807034008185a20f00042c00c041d0741410300080d04c5041d09001c0c01188940c0c01009540c550100d909034111389140920b88400c03c82c64007185041032030002684c410008000032440740400440103c0c00d000c2101181c6810f592004010f07010301036418014a8402d1010008078803101d4a00110b6100e0349441c280e600381200d035400282115400c2a00782c0010b500030404042c1810601e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 904099334 1250 904098084 904098127
    0x1c020a0b070e0f01030c110d0801080c0409051b0d0b070302070b0112050a0204020a020a02040f0e01060602160e06121b031e0a0809010507050f06040302010b1225080d0203 75
    0xe080b429440818002c0381240d070944070040d04240d41c4900394445c1902c104820100004040c0a0380e00106c0c8403207000780107039400c0c021400c2c540140003100c0d0301c5181c00e01c0713548141f6502801802d035000f01360030090a841540400a50800411031988000903647c280702c5201340880e071001a1a000300c2d042001140d401604008114027034400c0c2c12010a0001450180709a030443e405650b803058220101e06182001400a41260414401c00d8040555400c44a0301004120080007420780d1030500301daa884c03c42030041e41011000809005000707156850f10342c86000074051922091145d460a0328061f04018000400b00b00921010350390703d010b0108415482c50000d18290307a0a0010105d0f455880d190001400184001180709559004405541da007a0301300301902e10b2046406a115100e003422a07089006510b040f03103508043c13501c0e8529002011030000201420300b140c005552039070f8481001024000d4000da0002610b80c0d0404c03d0321030340340990f03000d151140644c030380e41c10903c0c15a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 904100584 1250 904099334 904099337
    0x405120a03260a0f02040b07060204051801030c030b040c0e090c0109050f010f03050916031a0a05010b0d090212160f0503010204081203040f050d0f2601090e1c020a0b07 74
    0x10a41008541c0c001e1100c0c0e800410183c2d000074241c036200210002031044d54000701640e000801c9441c00e000151b80a1300407900140d86c080c0760f408586641c110031510901000700a00500c01003400071903503054040754000d214516040701c003601c0341c010707100050040381c2090700c83e4814089541c1c03d580c44035948004010507203e400d0f059044c3c10000c2c10181004001404150380c81000a020003801c01c00c418480e104021800d8a0325141c4c100740300b521101e002c01000310440303080401c1035403285204003812142801d15403401e01803032044d240c01a060343c142c1645c0c89040c40380d40080382c4000f40180d10f000c5008014040c0440d16107c014500b10155070701881c03103a403050000300400000460400030001354105801e0342c0303554030715268100c0300300c0000281c21403080c8c07008044066001802c404940710581c8030b40a41404001c2081d44040308146100101000580104103069068100b040c14805c040203440101046402825103422420070190050340304102110a0180c0504401c0d04030703046 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 904101834 1250 904100584 904100627
    0x1801050601050307051e0a090303140414090c0d05100501090e04020d06110706021c06090e0a020f0a0b030c07021924120c020106090e0c0102060a0e030405120a03 71
    0x80300081d1082c0001000c203801c1c010005820355a1140081c0720340c01003040711151070b4948844080c01040008540001c5010032451042800d14250075026101282e441e00031942802000c1c105110704a54090000ca40b00c800500c0a410032180ca40505441b80c446075100351007103480c01e0001000c4021980c8442d000c007000c00140000368880958a038103d9411203004103039069082440c804501c54050007504152002c00c440d51401784101c0c6850b00a000c0c100d060100c107846071141000c03100221821001584901901c01c0142000011051002130051946403001c0d0307101c5004009910840b9034800b01c03140002c0c07840442c500010300001c0707104500c0103414001d003070460703840e0300c0d080c640582d0101c2110329007580394180c410b0b90805002900840240018a400318020f400307403c80340242010346003400188824004005a0505541383c164002d1010303440782c1350b0074002400b83c1091900e0a0004003c0400c4a40369141c540000d82c03240c0c0014400103105080040c41c800c044a07956985846 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 904103084 1250 904101834 904101841
    0x9010b09070c080304080c21180a2d0f1403070e090a0822030311070e07021b0d0f05151b040e07030603120203070c080f0303010b1b070e180105 63
    0x1043d015241d000f84c0c0300e0b950564892141d2001403408a06040592408510740003007e00c00706030002070100880758040d10840000d00008200c2d0088690280621075040d1000b151030400d03005904c038800310003405861201c00c1d16000790449a40540d00410100508108081c0aa04080108000038014041c040c00c40e801c1a000464581e001140080c200c09400315081030b2030a090007142141d08120038040720080d83d05e2401501102c084044182c4600840c580020a000c00c560301502c68200750b40030f00f00320302082c1414a1118400001103402003100d001600c00210b104500001e442c0c06040281a07900600380221407100c00240000042011081c00310000140d410030384050719100000311a85039148202200180a9648098070071105c4075443e81010b9004001000c8160140900040a5480b602c3c5203641d201080c602045640c8100010449001d003031001d092000351440d07100041002c08883c05203019019048131112034105406e1204080481118034170b0a95610000d000c10715 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 904104334 1250 904103084 904103093
    0x608060a0605180a1509050105030c011d010f0504080d032a090501080403030f06150e06190e0d080a09050a0819150f0905010203060a1a0a14040e09010b09070c 70
    0x43e1001e4000740603440d00004a00d1318019a001905d0600c40302503000551a40c03080100d019042c00c1c840c240c001e0280301c824100e00e5100f5504820542c188054032000307400008011505812000e00e401c0030003400340030109e4900020300032a003904819640100d2020155004c10301c0c40b012100e01c80051000041111000f0390300b10513450708446090900070607a644605098000d80710304403125429510307102005c1185040c88103a030002c0318265031426081920b1388180b14440c400c41307402e91005402e09440341440f40c450000040848805401d079881e000c402d5880da00a60011076088002c12040f0005008a04100c1000c900400c8600000c00060310340010f182c0c40d03007540c140c0242401024103240d95080030310303400c88046141440400c1054008600303010713000750020344100344a030845000004030744407a1070305c84004000c4401403600e8940700751410360750b4900818802c0040c803030074000040c80c1054098050300c1404164000700304031064004010700040018811400d00552200c41404031303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 904105584 1250 904104334 904104349
    0x11805071e031e0302012004150302160b091501141203090a1202090f010e07051804050711120c0304031401020c01050705070b01060e0f010302180a090608060a0605 72
    0x1184032401d24141032040c0c801160150300d407070300064a1816a1100f00c0107800540480c0e0101c640654000c0084505030494030b1100d41c001589910102c0c0180000e100c11004031420001002050400610b0070010760155410034510320300980f464425001040321108081c040b4001d000030140301501c2c03940c10001046118000e0508046c040c8110248100e6000300c02c004031a00a1001404040c42d2544ca108062010000075000ca000b0700780e5801040300010b0300303800503040e5100303840d01d80000da4418008a0706a00b00721070b455004d100016441520344c60314440c0502030a415a11044081e1000b0350052424826000d90410380b01e04000e0a0400c0d940481610181c80d0322104070101a005d0484007400390245a08021503546403000f405100c42c0c00a0042081c1841410f240c08241ea840c841518030740300121661b900101d81301c5040803158400c1c1d004058070110348208030f00c500b0054001c00d01c4e1503507541248001c29550641070049880400c091648406550401d002e071604103c04075844 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 904106834 1250 904105584 904105589
    0x80d081303030b180a0c0e030d020c01120b040204090e0c0a03050d1b0c06080403110c0f09091e010509011811010f11010207030e040c0509150901030621030201180507 73
    0x802d0ba460441d08141d9598000085204440740244410f0341840b040074001807003440807003001309060085075031150401040043c24141c031a00034181d070092003001510807030b03c82c3c2c4ca022002c581d40c04144140760340f1440508081c0035a0900001e441c010b100b4402d2500c1703010003d051003070143d068200700068000645031850511803420502c0d451514440011511810600401b402c072000307004501e0741c0e481802e4510940c041c0c0c3e41c180703001c03244040c0d40c1e40307a0a4080368650403490101c0c4450340c501b40b40b510fa64002040c07004503043c070310503141c100d1590880209888103076511a030030711010300001d01460240c0a040039010844030190ba580310200c5104000650500010008510381d07140203c065100ca1008003000307540e503c11314603008084a19505c082c600c10752070141145003d0b44600281c88485902914030300a40060480f4158103400c0b606c64581007586072080801c10098102c070a03040044080c0c803014090041d03240180c259007107003d0440042200304030f44804118009040c404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 904108084 1250 904106834 904106837
    0x909150b030a0212010b1503010f090218130c11010b031e01090b010617150102100e0102130303180611150403020c1206091006050a0506181801080d081303 68
    0x40641402000c03a05086100c0d8029600c03c003e002d41c5219460190406045030404641c0c040c8036001f41044081c15000030700502d0007004120106005003e05940140003aa4181c240c81054a0486001560603508141402c0b8215110152680c4098114070500d4441000c00b00912a031030418002c00e0f40c0d0081520b8152426601c40103c5d03c000c902984000b0010b07401c64012422984c50b110043c20121000304410702c103583d400c000400c0c000c1e60525510010805a002e04400089d1040d40c1c1e0190044a10121540d58200414000051058401002540309072159442800d034911015440f010607071004050020301d46100600204c08aa000c1a22549034485000c035100d078142246814065109940c1120081045d40f079109030020705180b02d2004003044440d0b07101112a12420f8550314402d007a00204128020300c050301e4a00082e102d080440380c001d49204559000041e6410340c501c064840f070134404030040c0000c0e20700384911320003540e003800d001001e07040c00c418807000920100006030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 904109334 1250 904108084 904108091
    0x1a010801060b070b1b07200d170a1404060e040f0b280909231203130303020c03040906031419150905120c1b0d11010c1a01060306090915 60
    0x511090aa806082031454070b0300b0703217541b40d80306417400c44000b031060103d82903425913815100c0d425140400d104008507901150012140c1e034070000c02c0403a50408210003040c450f021800808841080c00504000d1490f5034a400300c0000c071200780801c454110514071038082c01c0c240c9201d2140c407010f40d2041c3e034548045d0700c0518240301c0d1810101130001c3d508503011642c00d020320344052100c09400c1c035030320440d03c03005501e910190002466440c03104581c0562048000d00c002400c0056041541114600a05001d031414021042850a42d80310b5004480116628241030003030042c0307903145101c1d0300f840d0b02c01060082c04401c42e0115002da100c00003828242303d00030000f110394558004030202c1e54064122080b52400c13400849954210841c440201e10900c1c3c080c2180c200d1103c4c0002d0301140241450001502e283c4480c806640e810300d1060602a10800140020380c2d6249445010103220360003e540354105000101078504c10f52080c00e590707040812440200b0504540075240604500000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 904110584 1250 904109334 904109341
    0x50306041a0402150a08010905010b21090703051518060702070902070602090904140d0905010e1315080d0207090e03091909020c0a02090c030405030406030c0207121a010801060b070b 80
    0x24513010322201240318103250100305a429103800c44040b6050342e143c201c081c8410303a202c102c4080d150064004c1d11482c004485421600c400782102c0650304407608000f43e500164482e1100c41c0780010410715a0b90180c1c80034100720440e08514500c00000071754070040c00a906100400969504080c00f54807800b0f07034005144001c005981c0c0c1118103100029021000c10701e0a42401c2c8049070342007810741a40d024540d40901d245209986070025140141c41d1031240c201a41c4c14002e84185003046041807a948103000c820b808581003880d4010088003000b81003103003581000a00744511603002d13075002030070602d14030582440031080d036100e070704184c0e0918100035600000590141c43c6600209103035200103290320461001103910451076000340d03207260705521000c41ea00f00c144011100540a9001400240309580c03080d0031000c20b2900301e02c11100200d4444c988495000e060300d804858482c803440c484840003001041903801800003d00803c021440c1c80400d814a2281e5007008000c00303a0000023 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 904111834 1250 904110584 904110589
    0x30c03120309140303090f06012711030c0a020c090c04090515060a1d0d080715200a02010506030606151c181a010315020d0902040c18050306041a0402 66
    0x3140b0b400e0342007084024042d044803401616a0b01c1039600a0341c5010344d400c5611003d10018486040360781011311000110a6494441c1c8491240f4402a031031031b4844600848500c000d0024500544c0c2203a41e20303540318a4198080d10b008010a106405502030104220b800d182800940b0102e92201a010449681d14059240c91920034500d031580010003080760300146130300062032600440c0d0380c03184054218282c01000824902c0f906c0080000f842048004001205c00550120801d0f2540b00482d000107034111060151210101c002c07110200464819503e0358240941030300300718168040d10040c00d14078081903042200100c00a442c100018101810f0700403e00c105164013990481002a0305550708182b01c009000c40307043d601c40b8003a508c034844000554860b54126980400070300242103508010a01079000141e0b00d441003075440365014003689603401001c0c40354145d0303515203990403000c0d2003c400c0114241c000e0b60103a4461810000054800c4145044030980442c0c081030039a10b0340300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 904113084 1250 904111834 904111841
    0xb0a020d06030b01080f010b28120303020702040614010e10091a03070e151603032403020a120209061e0a08010606120b0913020a050a0b0c0c0901030c031203 69
    0x80d9141686001c1d4004240048201550305a90f00310b029a40e00908a41e881c0d42a01c0a8003281507124440002586500b08180011510070a2041007808a42c0c0c1d04c000305807a03400b405030141c1c00b081e00080c03c80d0440c6424071500c0003030940d000f420602040b03004002020150b100e80642c0c00342ea400315901c55400c0c01520010000e04655010f03507000c01c0c0c201d9807180280c0064400340d002c14003c204800341442c1036504100e00c040c55856050500001c288100c00e02c10b10b600701a801e065403500a565103030180440200c402c541100e808408502e9031062081e107a10301d6001001c140d00d243c00390001640d0345880c081e0016811030303a49640b00e00041d99580026007020800e07904c006074600000d041c1506422034011102a40c03902c800400181e008002540c410141c00382d0720609000014a41c0000c5407030304a00107001500041801c0d0300d52003c10010b20650f004000340030404102d400028004004251500d00141d0710a0300552440e6561182e070825400001d0213445c1e2a414850080c0c400d50 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 904114334 1250 904113084 904113097
    0x190c2303190c0203061003030c030302130b04090c0f08070c141005101715071b060c0306090501051c02060c01020d090f03022a130209191809050601030b0a02 69
    0x1003032007840a4440054698000844128040d01035140003840c130b2600c08075028202da03015242d5680361309150340c0450081d130202004c856047d22215011443c07980740005007024156180000852012055028100c40444400301041010100810036096800341c01544200c0d48201c429004c0510300b034100d410b02c00b200810f000101c0c030f42030401445981c0b40d0303d2001103c14494443c0c0e00003d9019002e034641900ea011850207850000c042241a417203040d00916000b561140291480c3c03560b9a1102a105e084040300006611681c0a1018429912480e401008102d0350b0002201c00c0c0040862100c10f0002d02900c84c0f00c022903015000e030303001c1d0101c0705400401542081491410310b042394007003c0150003075005104800c030340615440c00740a842d80c0d01210906a800780101c2c1c004000340da0521107105901181c081c007031101e81d911041609000c210b844d021490145081c4500c17015540e0460024507505070030700c011000172400100740e45055903040001c0704195681c085e040b0010780b103542e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 904115584 1250 904114334 904114357
    0x180b0a051b0111120108010209060a0c0201171906060c23070b030408120601080603060a0b0303041e0e1627031a07030509160e0714030c190c2303 64
    0x40c108809880d03c00100b0f40c2416001079880f45903255030005080f03010b012011034103d501007200300e01c9940102000301d075441c030516103508071200d01d50003200000c2007960345801c400c0201201103981866401008003820301c7c0d141c80100100c10362a030b1050050b07050707110070020404400e403c1400900f80300304000740050030000e0366a800e191a00d4050740d0b0041034480c110514400200d149503204016007400b4801c0200240b12719210400c902d0000e011041c07480794144410000002c1d07620b0801c40440c4403400c1d030303030205080c02c0c80e02c441074000480c01040c0600006800d40800c04560f0080c2c4107445150454504111504000c0045400304105803c0a0095440304118600e01f0381c0740000503204040942d418002529261038141da101e580288054441040310001e000342c0142c1e211456100c1c00c20301d04040c1d422034a01d04e94281d940141c885c1d03081e12800182401c81d15150010724040f15906185c250100011916500130907000c0807807090900c05528040349082c10100103888081d8040f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 904116834 1250 904115584 904115591
    0x1602070515070b0a06050906040b010306090903020c030f0c28031a07090b04141302070206130602071215020a03141617130b0405101407180b0a051b01 66
    0x492003078601c070ba04202c0d001c0381c040b030701c074400100e0001c680d02610b002c40301c000e420b000c140d0f03d4160421014200140195040665078a80090000c1090158400e02400780d0050706201009505050601502a0003800709501c0030801d00c09948640504c0da042900c100c443c80c4503508030782c0e15901080301ea0760001d03004400d800c920000d10400246000d0141042d511944840c07035580c01d902200707018034480e00c0e100001150203403d6500380040b1043c0e04e4400320400501e8008640d001501640064400030300c0050490000c0c4185c0703804002120103401482900700b6480010f685803120340040b103126026454020498180d4103001e41c11040f800d60541400c0d1100b07152030032400303103145d0551b0541c4000030203503180c00310003550b4003100900070300941001c40c0040006480c6d04134040000780080700d07103219050308500000010b00c2040d61304501039002581905101000821840401408550704180401d08000c000c01407021190720341d25a003412601c61000f413845100e080c40c1d03040080415400c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 904118084 1250 904116834 904116859
    0x1d04060e12180d02010906030b030a06060e060112020306060a0f1e050a1b0803040b0c070609050703060b03060f04140709020c010e0d090e0402010e0d05190c0501020d0816020705 78
    0x120010b42141c4000d51060140d81c840d04040192100d90700c40007038041060540148605482034000b206070240140881d40c0426407580c031181180c1203944015401d800507400c1c4207003503a226549109100d124102036066040050024030b45210358444c0ca003d0007001d610011000740950304204041d04407203007282c03440c84017280160032903101c0780041000034444442030354030480c0900c145405582000c0c5032815940ea075683c488031540050601003c042c81800442c0001d19075005584070a8482c10103003450350f207107141402c00d07241c20b50940c5100ba00070508001340442400070081c0e00a030030243d03c03034001c1c02c0101d132941000165080319110600014030b95071250015086285049503940482e090342102e944112050003041c01054070011902c00403070003541c42015148040140180358030540081c580d240c40c585411456984040c0c40d00c4d0042c10180140b1196100c010f241c280040d000101402800a201d04001011010303101300148050709011300c20010308002d4803014040042484 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 904119334 1250 904118084 904118113
    0x10e06070c0303090b04030b0406150b04080109060f02040e07031e0e1c08010308031b0906070510050c03092505032508030a051c0b031b0405101d04060e 67
    0x5070a000580100e018280c0004071070920000b11800c90b604451001184c0c3c0303441d61740a003c2d005609140c4640064204041441c0300380200800c01000c8650002902d403146146c6402034134070400741003d9407841880104900c1500420f11548084c0d10318001030b1480c0b406480300070301d25843d0042ea1190380341c120b072114400340000d4911040780d100b003c2c1400c002036000f130480f12003409000081c0302030400d1001c0350140080e1665102c1a0042c04c5001d0300b00b401d9800800c895030405901034070140d201032211085055503124054001d090403032644d107180f0388018072507620000016580820084014160305024051080c840500b90080c00c0d9901d0818031001d805041452601488248040b82c0d00000d00c410000f045038600091521824101410f00c0996000c950400180920103900e4031a00071856070240410b445a2030184085810002000140001c48a00500f81540f00507804818440700d58041395003c0141300c6080030a000750380d10703e8240081d00c041c0c00c0d120741c03a1084404607004034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 904120584 1250 904119334 904119353
    0x501090e100b01020715091d220506190e030c0106180e060711100c02060a0c0302130902030606040306020403081b0615011215030c0306060501020a0b15010e0607 71
    0x10184401100d81158000c00c0701d0040720721039040540980d01003c810014420f0540460310414810b0600c25116660351030780c0e21494a510301c00184205440080064049290314603581d4458502c007040201122641e0b400d50700c0308050098101d05000f4522003c003114541c00c043c484071041c40c29240c4a00050501e24060400c50064501b12000840e0036503a0f061540304003410350450078003c0c241601c4460098440601c690b10450700c900a1201201d2080d20078004c01c88a010264000c10261818808000c121a40f000881e0304142c0104218643c99510b943d590050b070b8a0210010381e20740702c0c4000120244240d80c4001d03d001d002140004c00e0000503800342c480d50078400d441700d40c81340e000e404064039170314215803000c603141c112924020f01d54450140d00031850003003c000078801810588200110381c403503008460100d203051040c41081f8490160100070a003c0c00201504062940c42c0c8020380e40042a08125009418081c0d4641e0312864003540f5500010303103d03541d118410300304403010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 904121834 1250 904120584 904120601
    0x80604061e06090b0f0f18040e070f0b120610022a0a05060f1c0f140108010c020d09092703031a060f0d18080a11010509012009010909050109 62
    0xc40d030103100010301314040500b12a01d0031009016680703410080108407103282c212420b545843c9042c071601031683e40b038030703c5030b240340b0070070a0000c000e0300e0300e4010902454860398002004880e01406518844142c3c500c006404c42e2080711a900b444040010885c60702c1c10f0b106841601c0c00c40c101c400c00703201000c40e4402103822800d440301060642c55000703009c0a84203808820ba40964200a21010f8800c42c8100c01c01c111140c250108180740381403225002d5501240c8200194001c480c010003200c0c000f403042d59204a43d600140051a000d45005885040b40344190310304d09440354942d4044026a000030301007001e0702040c840600000303040040081c86454540b8807400701c0d28003028414580302c415100585c40e02c0090b5850041140450005003040d50031404511125000071800103030894041c0c48141d80c169610040c07205100045400d441020705031101d140d05d0080009a060750000b88a06881c074080c40a9039289410001214803048990014080e1441c05001203100c11450704031481 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 904123084 1250 904121834 904121837
    0x405190c180605060a05070303090b090c0108090616120603060f02071b030804120c0902030702030c06070c082b09061a010810170f06101a0a020a03080604061e06 71
    0x505a5000200845407036010303040e88003030305005c00000070748180000d1144503c2850041b90283c4580d41360311ba4a18180d5201d211a0800d0306142d80a5038040760265201d4060300060005003400500c0d000c000c507580800b4400c11402036071107016443c940c2c000500459100307100b0020a403404500700e00a4100d49400c40d5090003003800b0003410500c00f02c1080c07d0f40d4010079054030b002c2c54110f0214141c550041c00b15a00c002004001880310150300c0918854030140e0040c66440e400e039040d4908200e0010008010300c107130207001d88082010741c41a01c0c41070662183e00b40541002c00303812200c0c2540009410b1040e410084484100300180d00000815514900c250003240c00400c0195031010f800c40302940d00300d19070030007041000707010300081d6041000901922501404a01d500d030a01104950440041d81c054004210301c41c031141e400c42120403110441403c00e00788050080d15801d04181c05010030002e00c0100310355030354940c0417200512014046500302c9407000f00c002d0401c9850701c40d460 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 904124334 1250 904123084 904123109
    0x204330510170a020a110f060f2401030506010c060c0c020a09110702130603020306010303030501150e0105030f04170c10050705130e04030509090a09150b010210050405190c 76
    0x10940d800303204290107411030142c01500e2640c54403010002900402554010400c2410041c031040c003083c03002400505a000182a0710300c0c2942d10301300701325800340803400c616641010701030080c4041d66030010951000d10f4082403584070b617001202d503411740d1a40504264502910600f84070b0f0069040c0c005503100395642152113507102d8185084841d40c2c44000804c2d40e003048107200614000c20b80e81c98604110b40c00080c00c50302d03500172034980b1800340c00890103e5603c400500110700140b400080d6142c0342d140440c0d03c01c01e4400002e2042c0400762121041b035000e0008241000064030f0195841280f5890785038541050441440d43ca0344442414841d1515190106800602c40c0044400343c20056962000c0a45404040e80320240000c009070100a410b204000340d6507204c4610a025540341440415060014102200c4601d03a07802140d456519092055007a640c011507542a04e840103100000c45a8507801d1942c1484070040300c240398044102c8071041044281e040b0041500c12604010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 904125584 1250 904124334 904124359
    0x40203100b0a42030f0b130504060e030c1b0a0f03080a18090c020606092a09120304060810030506180f011419051302043305 55
    0x14001c4501620720745030001d040c0407090080315101d2441d00b1030018240c1c0c0115541854100c0c0743c0740b82840000303400100f11030b840f20598156260081400860708140104041400030002074060040c0d200300110581d1900001130600445511410001503550107032a030784c1044a08407500c0b403c41d90700c003482e00c140b2031908070060f08120f8440703c1640e901c0b0021342030150131364407020001d401c480c590b0020800020fa166100040b00d041200050141c00c13400708541848080c040d04004006201600664240041000700c401000d00c85100312861208902121a20402d0120320310a0301d0341c540e04480c800442082c81107000000340201c62a50391990b00c01c3d240d80d6140d1030500c2030380c070000d0410f0380310001090b1001c4075400100b80c2500f00d20b0407140320344d412280c0749007036911140044820a00d0b05081081010001440302e000c2014600e003000b15140001101035104400500640200e550340814030701c92081080c0506c190b181101502682e200c808085003a104150050901604600360388 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 904126834 1250 904125584 904125613
    0xe0c192c1e060a05070c090c0e04050a0e0a1704050402160b0603060702102a020d0f11190c1a03150607020906040504020307180b032401060e0a030b0906040203 70
    0x31810281c0040145160501c0c00e002150150841c0000342d0740d1903801e00b000070301c5d0701d00c0380f14008000c030725504c588403100441001c0004403000148031031480d42c2002512200700c00301165030040c02e644060303500c2542082d44102006405035400c42034100c0c0c80001c400b0f03003158080100e0500944030f0103506244e0741d2408207054880030181c9034000941c2c407000c1c60601000c0c00d41c003d4216021040380006008031640d00079401c3e00703c0c0c40300310005a00640910b4034240c0d40a030010070600f00d103040c00700e0001070106000e83d8407103480001c03144c0d645201803c00c0800c002801010010404050a5080c8849401084000798415980c00101ca4941c0115003071504017401642c4070290001c260103070b80d507141001c0c000076000060080742d06000d01074011480d00c14001030b0340240e0584000c0090681d1280e8140741c40c000300781f40c00c9080340d9441c8402c498081c0078150000d0545130f0a151903840e10350a100856819190382d000100280300240c1000100a00000c3e170a00c60750007101240c3c414100d8000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 904128084 1250 904126834 904126879
    0xf010e010209031e010f06320d0204021b0a050708060106020a031b021f180b0f1e0c030a081603090c0b0c161401090e0c192c 55
    0x1031030360160011114107490340712010b051500c19040304000f04050500b50488821504e003500400040207000503d4255442c4240f0804002c5e580310344e20a09a42e800000592709030700010009210700c2d00011490000000c01400340da18207091001c48410b00d800e071034240d440b404070b801091000d10810f4000150705100081d0b81c101250152200480d800b21440c41c40201c031015101039810505017495020448480c1c2d001603040f51305503a030003520011103801740c201d500050340400f510711400d001e00b901c42510f0717a0446641024080c0301148600200e01201c819001e540000c10300307804041a0044030f1078020000a100e17044000c0024100f098100056044a00d0440003600d410f00c0d411092042c1038916000700704250812044031810803a00d0104d0103901d8044d04882d80030800383d500300c942075130032013a40c40c0038100300c000c03041251800000c66105405a0800071020b03c94448840c48418010351100901800708444c208102d213000c110640004000490a800b9080c221703808418844c1880c1d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 904129334 1250 904128084 904128097
    0xd0905010f031509020c0f100e010e0303040b0c03060a1a19111b0f0a090605010e0909061303140309010501080f010c09120201050c0f0a030318050c100207170f010e0102 74
    0x43c0c2001d64281002c4040c03009402c83c8000c90300c82c1c402c155408004140c10011511104444140410010480c030f0300a13003500c1c0340e41d19140d1180e100b030051000081e4a0004c69610041c020360031500d0707540d50030000b04548003a030f120500d0230603145e25401d0056411030051070310800311003010580315204101142d040f484400a01c071583c0007540c8450065803510040c20700000020054810324ac1c1c200300003007800380158005150165a85400c200075600080c00c33900c401c4040341d804c2007a1030540d9041d600d4500050002c07840215400f4207408142c01111880010041c912079540c03289401d50040e80245802e0041c44524404c029030040c1c0154140603441145425940f90501d45190070100200211100e030700b00e06002c000c2c081080080d000f00f014286144e4103070010000c902d87d506010382116400c00052a00d8103a03007040f1f0000c91030024101500032416a03000000d08180c0400700c0c1071030195001550030000b0000400d085210008000c1918569200208521400f07507414a01301e10481 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 904130584 1250 904129334 904129361
    0x50a1403190c32120405031903140a031103151806010c081c02120f010e010509010b0d091202010e0c0901060215072102071109090c0607020a03050d0905010f03 70
    0x4007542e81e40c02220444a440f15002958035a403002072810800e052a4075034030880340d03034a40420200130514042100322a500e05a000110440d40941c400405450b44a0a10340c04088000307450036085203c3c4d80034207600c0c0d4440c0e081035240c1c207089203c101d00032381005295100b40c2041116902000d000308005000b41c2c2c051716110105403003a41c0d203444542000b034008030322004c07028031030b002501d00d80020310a1450301045c0c0c0917680303027074020b075661900103030410240400c40301c005100c80e4980c00c501506550810088584644030414582701510a61038003c0c031302c0d2218007000703921a40541010700512507903000e580c5040000720a01100c2c402c24803a050060b4040f054022150300d940a11315080745c100d1a1034101e2802c1e081007651010f20852441c1e03040b82c1d000a0000c24408881e1010a08810031154083ca0381449440c2c556240c043c5110b20703218200c005009011075582c18920001540c0c40400c0e0f078110880480c01600c001558030400c0d01040500c1c2003000303024801d12811200080c1c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 904131834 1250 904130584 904130603
    0xd0503060f0d0209090303071b020d0206090607061d210a2a0305190e091611120d0b06161506031a07110a0f0b04050a1403190c 56
    0x445040000d0307209250516070300107101a0103040561510048180f00b541044002c6079a03081c244d400804920400060380d0300070011584682c0113a42c4d1200061809070100d42c03d94032000782d40c00040301c2e0720903d00014031580c5017082003080d1415030740c85c1052122400e41690200b0514980c41c215900300303c01c140c89022002c0292942c0c0c28003504004011070001c2000aa0f0075022002406050012200c280c000c18004070340300528001d03111541e5806105072404600c0c00c5450004150114070180c410100d40b4001d070220302b14548201c10a400c082090021140d00c203400822014195214041c90800107080424070f201c4c5003000e01c216541c094581c3c850b911031140c55190541e100c0c4101d1510761070103803079090000202d218030633082074807404882d4000881c2400308020380440081c091a0300a500702c480404085041e0030300007940c06801c0f170008003071590781c2d1612504290b007054008000c041000c4413802c0505001024004405c00441024000c0b45040802e60748690b080600501c45003c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 904133084 1250 904131834 904131841
    0x219080a150b041a060703090b0a0905030639130f140603250203280f0f02072c0106080f0f01030f0609052802041a0a05120a05101b020d0503 62
    0x411741c00401241d8028546840c0941c1c403800e17000d407168000c1d10400b002030443d000500c0b0030719051190796002400b8061504581000c0c00c046044a50f40c40c42062010541501c08000d09a4803c2211074480d40e0341c601c0344949464580c0c0c07040450a0340243c11a003101180d4824130340c20b005084038021440c20503402e000d00c102e400001c1885000140d0318045000c24040382038a00c0901c008010820480607405c0e442254400f0028440050052500100140c6810101c40240c01140c0002541c074440f0012017008400f18034160390040d00c44401c40e40008650000501640c03102e003481c0903140c01d90003a00c0540301c68031081002c4000f8000900011041440400040c2141e845a8045442002500c401c941d00184442e6510410f44500b450581e5402c4100214a042d11130102c0740c0369410411580c1400360b00200d1085400f40c050580116004004052401000c11543d0712a560200441d0f42c51034a904031700000c1d14001611020001c000708411030315038000720301201e8616040c2ea52508503a07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 904134334 1250 904133084 904133089
    0x1a0418020c0a121b1110020d0e191701051812040b030a09020301061746060e0d0f111f23040b0709030503070219080a150b041a 56
    0x40301c3c610307400140704c49103104d94020002c080c8031403140f03400f4158041344c0000000a01103603818000b400c504540180001c0017440390814092521608182c0d000d218400440c0c0411400061541162a1a0355011603201c24140150840c03445054410035943e1098096085582e81e00020030544c0f0801c1f0003480306228224544010310350008400501140e181c4458010a0071a82e15410500b080000409030b00007420082240c204d11411703904920340d00700b03080440030142170211816a085091011590b2206410b907a050210180d00042d00b00100075211680c0c0d40c2d01e00c0b500303030880c0c0421100400080032038021014100304101d0350010f072041c0550075a0b0100400c5840c4112007186550704070b041440200900f40c1c0c0e600d040103403807080d074606141c10503542d0580014504003c118071110203000041003c019620200d50580d508000120380c01c000100b40442c9412900b460f104880510b81400040b00c1007446412601c5820000b416010050200351201684131400c07410a90715102c02c40d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 904135584 1250 904134334 904134353
    0x120f100e0c0a120b13060806010b0c0309040921020a021c0b06010c0804120b0406060803090a140a150e0a0e16111c050c1c08040212071a0418020c0a 65
    0x3c07440340000245002401e000038405100c55681a40d010ba60f244180001d00007008400d000d003005086040c180001c2180d120f0b0f6a108241c04103001da612040b149040150308012510034410401801600903c03440c0025070f2409680d40c16446480d01d030001010059480414204403078000c64441c40326070790310005546428400d40700321040002004001910403c402d0706000c994407070114180716050508001040d22595001280d641c0c104010282d1696903046150b81118041c84074000c2c81c001c1c0b600001c03103000d040c1e0310036004a0322002c11001125841117020321a00300440e06040850380301d03902c0d020742d8030f01141c1d407000012107034068601450040995000d0a06002c085032244c2d0341508038558058103d24500c8049000414503c02d052814030602c403010311034003c00400b80d000d4080041440340d000c0d0010740070f01100c080024142c1000d10440d806880200040300c0090350159064095a01078884e0314010900782401ca42c02c1c1d20113008449080c0913000042408015075124080b14 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 904136690 1106 904135584 904135607
    0x40c0f1d0d2d0f020405150a0b070212030a02240403080402040504022707020c0a15080709080714010305010e1b0f120f100e0c0a 57
    0x440d00c03100319550206811010b0a180c1c1c202c200840034210b4210600b00480c003035842000d1003488950300401500d18420381e030801c034a0307441589200680d0b100d10100355010416030000c20640f400640031342100c500080002041048000940c0d2541e80210300d0304000d030b00042d503031503480c980742002c031100e072a5941a041c1182c03a2a0f5002002c01900800080c0700307aa982001c50706645030244403249092007103030100d50f80c00d60149002040c07031045072050010301c29210170702444d06182003810b046581220b0008403810940c00280c84c8608018091010404608000034424034108081e40c01010b04406075244414114001004e4840580206804030315101c107003d020780d503811519290f0f004444410740c40305410071103403800c0e2103000300d2502c0b407031092014018118503041d0100e004001203441051491381d54414039905400071514041000e109101c007100990003040300301d41 = true := by decide +kernel

theorem cover : BRFrame.Cov 903956834 904136690 := by
  have h0 := BRFrame.cov_init 903956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 903956834 ≤ n) (h2 : n < 904136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
