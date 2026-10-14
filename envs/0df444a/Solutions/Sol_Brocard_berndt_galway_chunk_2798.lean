-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2798
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:46:25.470079+00:00
-- url     : https://prove2.me/submissions/822ba41d-a8ee-44aa-af72-d7741415d615

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 503057553 ≤ n < 503237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 503058803 1250 503057553 503057567
    0x3112050904060902190309060f020406021f020909040222021c1a0102070303180509070305090d02070e011a04050411130b090901050f030f0f030901020705010e0d03050901110d 77
    0x40d01c55400c09400003145100f074001d0303400341114406000c0e910f07880c014054004240b00c8004444254940004c41010042840035100802041e00680b4126401c40204401d40105c19941c005c46441404100000e85600d421541c0c0716506455540c2603c22800f100c055107000c402c1100c488600001b511465240005c2c056400e20352041001d02c590039424141840441200c0d1a05005034852001040820301c1352111403100ca1403400710482d45034036103000c20003194007101d040c2c001c00d450300e0911000a6003000300c207014000c50f00c0035021680c200441906c1509042c0300d00108155a03000c103c0c0b604400d03000703d80080c07030005d108102441d0040e00300e0015800090613001a50b5018400007550402d100451305070901c000d1441e00c00760308007020049070450250304207400d8464030b11a400e4050080082d0107803440c0d1207005540395031403100020318042c4190445c904002c101c5a00b10240c0e124409901c000903494203200c2d031100c41d800c0040300c0500300342c1d10848040c4524602c603c482c58000791 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 503060053 1250 503058803 503058817
    0xc0b0a0c201206091207210c020f0d030e10030e0a0c0503160605041a0f0a080a0b0a031730090d050309030a080a152606311205 56
    0x81d040302c00c8128010300949901089a4860882c1c20204030625400708a000800c2447e2040300a442540011840f80040c1d4000c0d901d010702103031a0a00810541c0b8103030605414080c0119140701e049035060368024401e800036110341e4010360000c00e1442002d0b010360441102c110010003101c2c0b5040c001e040c0b80710034800380d1140710700034020742c04600107500e43d0204103000c0c2c0d0b840b5103800380380c58036182c0400f03045c000c00c0d40c11080521091282000c444039000c001e04811803d5a5611914108074070790401304c4101d014220711803c4410030400001e40c00e0721010340d601c00260080364070f51904499600b900004001900403a414002e0111201c0707000103c1140101d50780d0084030004114100140d81c14801a25410041e41c000e1042520244c82504419880921013801040a51131414800120701464100003201c4201c82094403144080c4401615003031000300051003503041500c00f203a9410340c1e600d841d85c00c00003d1403031141d00c80c115003088a50154450444107103100a440001e0150b00003903 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 503061303 1250 503060053 503060059
    0xa11090f0a05041e111306050f12070206040c05030102030601090306020d0b0301091202151009020d0e030301090b0108060d020d0b0a020c060a1d0a03120e0f070902071208040c0b0a0c20 81
    0xa502450a000118241d941b000005003905242608042047d00c140e041100c0184600e0780c1002a42580c001e0f0302c490a000710455001041c0343d09051410710054001900203600076031060041000c43d07a4048104002c0326044000180d0741c0110320382000140041c0c2c0b5880c0c1c1c1540c00c043c07501080024407615504a040c103039081d2004083e031800c18030540c00e0143e5511040310342c0801c0c244140c841c968010a5081d441100010701520000141170031904241e20070600640d0360f148100081d6002034031a5401542191404040300e401d07070000c0d90b040e03000b882c00352001094100140707400d02264100e82d1050001002ca030014500010204041c100820f400710290406500e2540820000103140109544c161038120141e01d0f10b500003801000c012040c0c04091003060094044201d040c00040060b1440d400056960341040c1407001207030101841080030803040104102c0444c4980c2082001d440e4203641c101c1d6100c0b18648116000190f40c0805041d1146544182118001c1506c0c0303542d10150079 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 503062553 1250 503061303 503061311
    0xc0b0c0312010b040302091506070203010608030d2a0f0221030a0b010305060d0305090114070506010e090d0f0c03050906120129070b07090308070303020309060a11090f0a05041e 78
    0x8000107903c80c016484000c0d0881100f0300894614a01c04406003d1018007400a6003003080f40d800107400e460107030303010342025000000c808061441901070b100044070b00f1041c01c1d01402400410107440c104099040702040080481d071050b0038402d1104404242d080c414242c0c401c000240c000740142d00540f81c11282502d090498951540a402024070446000340400005400ca84069426a06c01c0b9411810000502240120740c04554050300200e4014001048070350706012000b411580043d044207890703480000c0385a241c44e4008851034004043c0c1c50013840403038040c90103a440e8000c556880e03500440c00f080c0c0301c08401d80d070f601c1c0e00d0481d11140300390580310b01d10b4038865003d41402c0540f110089000c03c103060106210240068000c5400d00d040e0b0400d5a680c0c40d07901e01c0c0d81042c0c0040b00040c5d00001880f20440c0200441e0b81c110080960070403021035002c0250403684940040d550040d9042131b40010395543c0d14107030384e00414002d0802c1c03220240200d12800a11000014114500d180c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 503063803 1250 503062553 503062559
    0xd060503010c030c080619090908070501050615041703040e0103030c060c26180609070e01080d081f0503010c0c0c1403071701110a2f070b070c0b0c031201 68
    0x10134002d0f44007114042d20307400440c0c1c69900621150b070820703082c901c90194400c10001403681c020b21030480c440b0f020703c000307030b8031921503152070342c2034480241405208403045540400d071444d40a044604a4180b24280c0342d4405215402500794001c0d54421a600840b030f0000006040d0001c1c0850a010720a050800030071201700300546a2500092035188a0a01c1804003107400c5210302d0250b800503026a0385c85501e00c0c000b14514a000402c80342010f02c3e41100c182000740c075034004040d501404281d006040c41012030003004214800041428140002501500da464503607090400041d1801030b000f400406080500034020b42c080720802c541e4446d40c01d03000118011a01211009141c0040103082d041c1e2402c1201201d001000d58030f4182951394049110021000c0e04c0201511011512408000b070780341901655080b20031001c0d07450098000c1e417404203000020541d0301c107491080c076070f0907103907280d0382002520a10103801414045c2400209100390000010282034180c4d41c0c801f000a050f0380f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 503065053 1250 503063803 503063807
    0x20a060810030b16110610060c03030b060409140a020313060f0e0703031d09040f0222180309060338060d050108060c041503050408072102011b0804080304170d060503010c 75
    0x407c54905101c11180b060a2041c9031140609107440e074080d10300415985a4800007604d254000e07880742c81d0300d50751007064901c0c45146003102644580710705001c6003103142c420300380181000d01c95002000642c0da07030b2a6940040143e03000c03105085a54044600c000d440c2c0c50301401350741075083e401034000421103251005161056110f88030300c2d8414442c45111400d6400e00148844800f541d403000e0003000c04030b02d52a00c9070701c20041ca944a0001d8111303826220304010300700d04121b4101070105400c02040040c0c084058800e018100305007000e080600081e00c07a0301c10744080e00c4c44031690041000030b10340342c00300481e0401ea0503103c040007a603041d078031505203404091007a403091024200c84c0140180c160790095010310350040c02500754a1a003103140e9282020301c04800152120000c2c22404201e81c1642446510822560f0310f10300f4140000884001d0041c44d0300410040c40404001300003010010b0540f1503494036240c103885507840b4002c140543c0003900d141d0140f076009618000098500038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 503066303 1250 503065053 503065063
    0xa09051005090f0106050307180b060304120e0913170405030109030e03010b060403021f0318030503100b0c100b490b0606070606081006091503020a060810030b1611 72
    0x81000b401459003c1c49c1450040041c501d8290103810581c0c0c0b08818100f40d04c810005501c00c40c49050405017580c040d42c0d0160880d990040054040c0c9c20b4402009440440220f0346081c00fa003040e803148400100600032100d52003540c1003950554280100300e410150400060305444104400030702068540c2c0d070500600340602c2c84080c0d4080d01e00c6034102200040c1001d81240f020007450045000c3c008080c0e4034840c00002d0f502100024000010803108146844140000d8044525024680984800a1035851511401d41d40c05182d460440e40000c0d81d5101c034600c040b401024284003410030300101000030701400800c40b0341d4603a031000d6103080005c55217805581740c1d84c803d00100300e0303480d09000e010250304244401c48015548880c045080b00040189904000503000081401070403c5102001d440445020110903280b108007400160381e800c0150061322000d150940c12951000c8900021072044e41c0060168100101070249083c070541c040d255408554884018088031450410358407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 503067553 1250 503066303 503066309
    0x90302030f0a0f0201050c010605220c110c041509060e0103120512011211040f0606020708011514180703060311010c03080408030901060e18010b0a060503040b0a09051005090f0106 79
    0x400c8104814100546c0201c0140032903289070800016601e884038003042e8000726502c041580070b0001100001c00088500071103a00f101f0f1490482c000c2003903450050390302c0c440000500d01c502d4540741c54685d0119054405001400890014804981c0e24101c640c01c0c40b05c20300080d104119000c0030305400301d004504840392480c1ca0078180395941e1810000105810f01d42c04120350205562090090955032402080140d2601d86800200e2915003400685083c000b41e001c3c034001c0e4140503000840555511140c0201c40307800c2003105031100e816000810000c0c00c82e07480303a4a080c4040c1448011540740d404901039034400d40541c030100f00c010005659a030b00700f003401000200308500060010300c204000d0358200c109000003013000c94507500040c030081012a03a00b20304044040080500c0c0a09010300307210300c0b4054800402c1c3d03909103a4020701a11008001401000b88100410040086035100060b8550440c0954800110402009016080540c0e40000c240b0500d0302f4482c54031410b101780030071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 503068803 1250 503067553 503067563
    0x90506011a030a111207090f050a0e150303130f09111216140c01051b0c030d02210703021c111605190302031e03010609260d090302030f0a 61
    0x10b5a84420f002405088210010341001d013003030001120101081e29203d01a0300d40d5103802c6000360038400192050301700c2e544114840c0780104c008001c5942084000c5401c511200b42d261050300f45500800d00e584038000050740c0012041c800042c0c511300515980b400d84103454024425408200c140000d240641100030404896503130228040d103814844400092002e030624030300310907030408984178541201194014a035190010420488665000d42030300c034032040c40050521252441c80d9a584c060342d282081025030000d594405520228151442111076801d10300d00c0c0d2412000080103900a10390240039400365150744503000e1200e005198030100d000b1660390800a03050f403c80e00d00d041002007582e440c021241c0d8441c0002051013420199400381c1c0045640c1c3c2c005110100100656a0140506440904c010b01044e0362280030f0700c044403130103842d20080c40302c0c2203144448981c82540700c400c940310356460709904039000075502049900031800d0b681e13501403040d1169200d818410000300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 503070053 1250 503068803 503068807
    0x105010305060a0e07140d02090301050c03090601230924030a0206090d111503060111060906163c0e15130807080a02090a1406040c050d0f090506011a 66
    0x403044001134000d41d400500c9142c500740108100200003040d91007070b280b4580030b030b0b000600f940142c18240030305504245000b207020b00d03524006103081c3e1074a00c103010304120710701c00f036050864080204601ca040350380010203e0101d800d142e000030b0458280d8280203000c5010b600d800040c0751901144021a4940107418946040501c00030400c0030301d00701e0303012126030742c1e07072808160642c461031134032102d03508481942680d034103041c0005000d41d4192001c00006600c80c80800c200c0c004049a0103400c00300d481041041d144600d0416551940041c180f95800420a07032040300d0760302c8180f804030059503030800c65210170914040c1100d416040d00c038040e0704808900007098840032120020300180d5070f032003d20030300f09841d030150030304040c0306900480da180d005031024010340c50090555900701c450514100700d0b442001c2822035980c640102000e200301d9a4086120380c0c240140c04a80050360481001c1103110703c04040e2000400340110240d82901c111000800c10b0f141c90440114141d4442113458 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 503071303 1250 503070053 503070059
    0x3092a12030a0c140316050709050105150909040f08070b011401090806010b0c070e090607120212040303050406062715060203030103080c01020409020a051c0b0f1c020d0b010e0105010305060a 84
    0x200d4200c1a00130070b0742251004014001a11680403544613a05104501600d040c0d490092a441070315410f8000a10865040300c600d82e000b50441c0403610080d074150340780b07032041d9203030b00300000c0c59071060002401c0e46000081e8401000400400141a54107401c5a004041103a000446080056001d02c01959002500500800c2005000340c00b010407024200c500305500c50800d1441c2e401c060750035400c180e1111050004043d04210034011601011100310b041503520464807215410240014040c5960bc10108041c01400d030850390180400b20b4001465800c425420304040001c20180d05043d07103002d0090030a00c40e104084130440300c086d030003107007580d0940d01d4644407a480301070851b41c0380d03608110006000000b8009800515000e440307280e1a2400305040c80340000003164603000d401d14000702d0525541d2881903807000c6410944031313647c2c0c0f20000c24404402c0d045840d40070303500121258206040142a0b501107041c0c0b42d4000301c0b42c1481c1d9035080198199502a50819446940c03c8014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 503072553 1250 503071303 503071313
    0x30609050c1f030e16030b070e0603091e03040f0302131514030f2806060b0301081608010c0206071d0d03030b0315010b070803092a12030a0c 62
    0x164010600400940d40071a98200001c1c080710200a503080359503070001c0d00d003039100e80c2512903452201309901c0900b4806012040e0407030807940f41e000042149002c400400c4045100c2d8440219100010b00156030f0307420500c14460303540344207402003000c5c852030440a01d0913403030120a84040381c001d6404c1603065801e66082000b111210015501c03560345c2e0b910019000f0076112030480c020032900340c07842e020300d00350000e040c1005e40c4001d003e01c0581c402e1030b4807141080b1000312850000b880e0f21020408020514046002d0700701c3e0303441012980404000400c01c0d000200303180309040f402104c0d02041554509400d400d8404000c440400b40c0c05c01400146030b203000703060071929442c0700e200d90590000b0000c0058072031101c01e441a00001e603182030200d175a04081000d8064a8100307248803c0b50b602d1308400000d2480b40c41002000c60f1000f2010403034000041094010700490000c1e048084111250302ca0300d004920a2118461840081c1404014201100300d4400c0d020690b9204003034a031946032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 503073803 1250 503072553 503072561
    0x80916140f041806110f0730080f150402070503090405090a0503040b0d061212080c0f16020f03070b0306040b060304030f03270305180102030901050a0804080f160b0106020f03040306 80
    0x400c917440036040021b8003640c8465001040511310071039000302906400941500210100c81d811080310070515105049280c00002082d40000480c01c0341003683e4803c201c00100005201480e500301d400031680104000021001d011104000e5078104130540d5188995039032500c1c034041c0a0607940081200f032022181800080c44904600f03600856159a0303042100c6245c0380703110303080d2444103002c000c01015a40c80003505421048946006007481040101c143c0d041c458030103162075141d5080070120454907541d2040c00401c4004060750200c90391005442850b61048500791300c12407510304040c400e40b80c85800d40b405650955a2414080190307201a40140703118940c2c00700c00d00e0902690071141c3c0b181002d4181d0703944031390354486d25203044c014001991124103c1150640d001440211000d0b4bc2c00410389040402500e00245943c0b02c9040103640351113640d03940070905000160030082c2c2280c6500003100380741302d1441e640d0b046c2c2c2d0310413040343c40c0c800c0321190340b42e55013040008101090060708 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 503075053 1250 503073803 503073821
    0x141501050a1b020a240e030c01092705190605040203070909090c15020f07050d0302060f04030e2106150f0f0a0b0d1407020a0203030703080916140f041806 68
    0x2104d000e10b140c54001212482d600240303015010036103440002001540300345c003040c44607016030003850010304200001c0d00c568810f008100c4032410b034422000600c0802500d140742e007e40c9030f8007000036060460403641c4c2030600319404445607041910010340d9080920882e07200e42055644c0c840b02609104450b0007500700c0030000c3d203460008200101d44040751940e00039114000d600100740c41a0b03020702c681d041c50350f2903111612030200c0540d94030101350003242c0642d01c5158100c2c48040340d9110300d8251210402c0c1c030100ad810000102d00c18400c4080c15043c811245250012515a5580c401c400c980c40e4800c4072805401190941101d001410300000403102c081f4024240d040c282c1c0c6401d0030101039001072002c640c20340d454100c400d41d000c0c0b02c1400c890b0000035030b1014083c80202500841d40c3ea215281008080095840018011340c4041c400c10042c01c50700090f81506a986207003440c90350100c40d0752140b01d810b80051514480c603081c4a00c81c01740c2c548205000c0f003040281c58410007000742c58 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 503076303 1250 503075053 503075059
    0x2030d09030c021504230904170c1c0327020f0112021201050f060c120702010c0f050a0501060603060f0e100e01030b0403120515041e141501050a1b02 66
    0x7000b02401a50b809122180082102d4042c54445140075085000c0501441d00000b680011444c01411500c42c403204991254000107a070891014405000c0d003148900d1a00f00945c0c01030380130072140c8180001040c4c445051660b42400000391100c1c8480803400b100000ea201010030187c40d6005080c030f000341c901c403110141084441c501c4001000c909a0f0300500400389000d0240c0018015440c0c0308114043c02d91040d2041d504005172181865514800001d00300c0c252140441da91013160b11812405043eaa4021505042c0b51941c0c0383c103903034440140d44116a15400e000001c54114400e100b8070080f610380b0a1807410882c501301000d01c1721040070b4210191400c40040c04184080c240540900861050740d60b0340c243d00d41418000e101804a10b03041080a00b80010300035002d54140e00d40c441d80c00101e40005510040d8080342c080401c2e0340001204d8a0b041c8070505022030403e00b210380c49032001e21140340c4d010b4450801103d141c80380d00158000f24084550074401d0345114081074010f27500c09 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 503077553 1250 503076303 503076317
    0x1081e0f07032003011e0e04030e0a0308040e0405060105040e1203040804090615020d0903020a03080a0c02040e0102070308010f08150a0b0301110a12090c060309050c0603040b10060203040602030d0903 88
    0x1040c4000399041000410103000f540040100000d07000f00005404400b001040242c840382400c11800081c48081d2011341081701c0d50108140070b0765890000300c000c6602000c15035a403581c91120495010048030161100d000310000000c290805000710380c11810350348003400c90529000072040043d00b01820984107136a041c44041903d010600c14100500703081c1c40c070070006c1004004028689901c02c40c502040000b4030500704016180c42e0140010b4075444500c558998184850884070311101e141c020354070a08000c1101c0078030038103500412140380130ba0b58446098be00c078030240304030701964860310503030b0340c400c5024400410030140104d8000e00c40301404070f40000394500017400c0d641c03004445113007150001030048080e83c01c084c1089070b2042c440001e00c001020747e1036000784480c0300c1c4240018103845514810805c0300034041e00f80d134000c00400a0b61a4149400d166001c104100c07004011000049004100c0b01d0001068a048802c5a8000d5207014403a80500c030103080310b1a0704506101031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 503078803 1250 503077553 503077571
    0xf0d111504030504030c0b2805130f0504060b091509010c080a02030d0b030c0d150207020d0b010501091703180d0212010c020c04020c121812030901081e0f0703 70
    0x1a0030a005500a42ea65903c650850520040e07000780ca07449410459820000f14102010004c1c040e0001140c00c290210b41c151582c20507142d91213040c0b00c220400d4520040030030340301d040f03e0007038081c1c0d04296010025203480d140c03600024411040f0640c0d00080840325036500c4e1500500a0500c80c1040c50080b101141e16035a40c1e601d6006194200b003d0382011407142001e604602c01e003d4500004ca004251403500c1d040819600444000302404401c68601c80c504081410340459420a42c00741983d80c540351a410203031104c000c20301a01e0700058504000080d07036015400452090715003503000c0c40c60144c0c5824854403442403940d0007501b014035200c258000d643d0700b01d240240111000d00124410086540081c18042c0c0c91030031510551042c08180f08180002540c2607605200c4080f07559900e0210216005500c001408190701c038640d5950603050780c001202a0418640070380b25442e440d02c480702480702151401d1050015450040002105010711115181e00114181070004280310 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 503080053 1250 503078803 503078833
    0x150306010b0703080a0c080417090604230d03050f0a170f040506250e03010204121a0f15101806020d09080d1b0519150e0f0d11 56
    0x60903440115600340c0400e9842c103050b04440e8840d40007a07010020410a088840302400c02c40000d04041c0200750909915250340d24282c040b114154170040255490395031750039414400480031310b11503101d01d0003201d03890101d08141a60b0041140d05403a00c80c100342100c0302c0c102d81c9800c00806201040340b12004c0c1400d40001d0b0701101d0081ca0000300780002d030b180c1400c003d46040303009412004509a1024000c0c0042c021017001001d0200717a2901c0c201c2805240c00084c003901440d041090200107140d0309508100140d95003407880500d10071881c1c00c2c1d9440302c180b6105c0140885000100d40b44005d4400e43c5c1d80781882c1c20b502e0703014035420310303501d101c048a03084d950202c100d40241008da485512082c01864004006600030001c1000400001c80c002c44000c004101d1840c0c4000c0c124924106441040380a01890000403024481d1284c408110b0510f00841101c0d0214161014138206100c54101800315550342840c0c04800180703800c01200794121003583c0c009024a03040e010340300c11080118 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 503081303 1250 503080053 503080063
    0x15070206040b18032b0207170604050601240e0319080306030c060304120c0c090c020c150c06072010020a0f081e100b031003050106050d1106031503 65
    0x10410440d180c2d00c60520034403655a008511410500c60fa1010700d0f001c0f45c40208551404616665012906905401071740a9140900030380025013921078030400031030750090026003035108500490448400d80d17a10414403d070307581c1111062880d4490070701d4100300c1900415100b8036050014003181d03004811410f04c075484646100003124110800820700c0194941009071a1030b4160440e03c2c0d0707246041ca6a5580ca0310f00184544800340008480c000f018004502e821800528491f5811711003000202c0c402901c45001c8001d403482102200701217101c1200d00d04c1a6540001c4c040000c010548840405588122840c1c004032104030860000c021300d40c0c424040113444030500100562944003480001d805000055050420001820100001048003030009405605008180c85040d1200400201c540a190b008440300f290000b0034021084a0408103400b281e0080000300042c41d250310800c00b5450452502506040c02540e10403002e01d0540015900060a024030307201c0f880c42007012078202 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 503082553 1250 503081303 503081309
    0x2c090c0102060a0c170c1e041505030702150603031c02070203012a0305041a07020a210f030b03010e01090f0303060503150a02090a050a080d110303090c1507020604 72
    0x560800461020156010064507070070240c1003806002542d5044002807130005801528003841c04400d0204036001200021602240a514005125a202003407042e01070392140c4501c42d10030030240760042505100d0313410750f8021606a4050701d2051044011101980009801c0903414002005240784074865441004500405200050b031160070a00403d404c460180203a140c2c00c140007607540f07004500d181200c9142030060300380001c4e1929103040c130740d440c54044c0c04001446c02d02ca405110700c20750006001c442c101c0c403c0e8640340205440340e1454201502060f696030200b1070200040070740742c2c000d41000f00b80ca03801a00000e0350040640041d400d40c1c1c0e181c1d409403080c3c1000c1080c4001e255250144070098041030b4004d0180f00004003000410700360040800101d25400b1641104030780d80d8000e188021b2200a01c0b4054503034a80c1104c0380c8070341003416448045900b1b0050b950790003001000340c03403003007001d00084c005890049060281051458403200d480400411010006941c0c4e0009480a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 503083803 1250 503082553 503082571
    0x10c0b06150408010c090503011a090c09040213140409020102031b120d06150c02031b061201080105150108131e120905011d030c06090a0e090c010f17012c 68
    0x185c1c2c15200d40241c102e000a4004d24003990501e110110441440348207007210210948000c50140e5500300300b00e40c0c50250405c0b0503802800010311180c6841304d10007403000e644d54401c1c0d0290300034541c41008103c4019000090240c0c0050114000b03a8000b0a01424a40e487d0030603505d0359030901c1e0300341c0780380d6000240080100d1382c0c510003400300c05035140d01a00c015110b0305086042e5400e5800103903540c88424804002c005000247c49041c0d2108016104a5107000d4120080313561030340202400f802088039a44581081400001015031041002900500d180d0342005c10101440c1c86078040c3c1c501801107050b94011516590000503546203119200b100f40f0b5a8400516050030001001c07400c00d58403030251281400340000c0d0541e4049943e00c001c010480e02c0d03958424642000c07604094141e4401990510b48800b0050340b0788000c43d405c51321030303800d9a8101e85e00707042e44001d440040304980a01800d14610006201c020b49158035500041c0209102c0030f0301c60803810706120881022114144 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 503085053 1250 503083803 503083811
    0x3060a05090d1b1e080a230f0336150a0603111210020406020a02090f07050f0c0703020d030f0f0302030c09011d04050c2205010c0b0615040801 63
    0x41107040c0b200e01c0080c81940303820150301d091400940c42c00122044040c12031524030b0503858403000c20b01881c00c011a801a952030300d07401151000390800300f041c16210380054680d40030300d00c040303629822031b9400302d5000d10080c11078a521964070030656540f096800589100d0720150a030380d213104504466138200702c00030308800c8030700303d00700010712009080d1241440c20714030f00740001680309810701e125010543e1410400b41ca0102e031280b602c080c26202100243c03002130003150340b59005c00c0c80d0792098001d55140700709407200c014124010104680340d60020343c05000c9008000c48241c0207000141c0d44000300c1d203085860b42c00084440b9221070045000c0758a102d0080d4145402070315049403a103a40c1001c50940c64180342180980c0b10b441203140c100b0020150005c0a04003040a540741500c010b80b00308800c0c90140d510304085d921030506c2c0f011562220301c28104075041442e03040c05891040e2354800700a40c103a61000c00400c0040c04140d8040d5603801c450003143c0100d0040c00003410747c580045 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 503086303 1250 503085053 503085061
    0x31b040b04061412040609030c120905120c01020304060f05071a01081b010f0c1a0f0912031501030504060b030607031d0c151c02040801020a08060301150b090a030203060a05 76
    0x5054003c45080010070340500748840007104480c60802a0710503001540400c1100e11450109c980011200340102720342800906840b1450380303c19160241c80d42501c0001452910b41603155640300c0225900307006034020401070081038801d400f80003030410390382401d80c20040c40755070380007010320020950070410903202c00400c410741041283c3c480c040d810700108155464090002003451040d180c020083c040700c2c81543e0200404103031410103a100008015480d400d0240c2d1201c0c8038031041d100348009120b420481c445140000c01102e0240c4909110305a6003060100150043d100003403042e200700e40c0d56440c440300c944051001031f110708220741c0c0c0000c3c0b01021400110301d000c542001e400082c1e01c120301042c0c0540307898112840c0070f1150f074051a00c2c0c018107041d455802e4100002c0602050000c030300020010b0054015220040d00d13034940b0309070b59907001c081c90308032000101d014801c038101c40b6003000118002d20042c0241940904079a80140c0c8a8000c82c2ca40b034015114492038940d254108 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 503087553 1250 503086303 503086307
    0xf080627120a17010501180506090f04020705070503120c0705010c03050405220501171f1d0309012607031a041d0c040504081801022b02010e190602031b040b0406 71
    0x280340540000d003092495000c20302c00701c020390300c894014180541c2700001c001c022960303241a404010f10b8010010f40d520b28451806a803126014402d4500070320480803249500103140c0150754103d960940205440e0f0718200045940e505200d5081d02404810000031410340c8039240401201c080c2e01c0089603004221228035002c0b1141603201c241c0d2075212030070000c00c48201003188100002081c0c0010050780100c1c407031400070040104120440300f2050340b99910004084041c0030f1528098880400940810382c2201c2084008032900c190340081a00081030f05002e0b5204103400d03032290800314880011040850116604030600b00120000016070321182e800801040807000400c2d00c3c18041402c0c184c0d01c2a000e4011420203011303100306400c2702c035483e07442008022400b40c01d810b080000780013900e50b51803011020308004401542096045c6542100c0040d001240d2501c0c001c20940680c0c6a4659100942028103014907241c182e20030b402c8080c0300307c1d01a00141190168040d070b01c3d80303040c0e40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 503088803 1250 503087553 503087597
    0x603070801060803160c05031903020c0303040302011b0f0c18061d041401091e020f0909030d0e01020c0706020c100305011202040e010b0d0c0f080627120a 68
    0x112040c1681000018810218044260354503c030a03584060b49172104c51074140740040140d0801d94042c811407c40c0510404101c8940c010207003c0d40907030f01c03000704107400d060b02c9110f035000285c0400c40e82e1420000c000307802d0072810506030040001d00ae115501e6502d26038030145940c0700910105901c00b00311b1580f54607100e4000204030740c07008501001b031654040e05000c0d000a2000c0d00e601002214000344420039001940f032558060903400045016014104409034003180990240c1320724400c2081c3e9081c05540c1c5401018140002d5040c130440708408000350075600310485095400740a11700b5012400c214000107042c1580180407080201400c1c0840d080c00c1c01c06040806003040010891001da640c100c0c0c40d1b5a40545021854850301410180503000504507160441900c0c0211014040c00d4288201982c01c0340103840001951260702a5a07401d043d18040c000316001410a4100828944816500d80d041c60958020f03031004020441260064000c00c070101e03454400700804000f8000c0703 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 503090053 1250 503088803 503088809
    0x7060c061b1d060c06011205030d0c02010c11010e1b01032c01200a0c080f13090509030a1b1b080a03022a040507020c0a090207050c04050c0706090213020406020303060307 75
    0xa40f5400c0603a40503c482d40c070705061240c081208042e103221000d01100788121501100001004e2001d8203200e01c00034000c104000800b4000f44c07222188540c501d206005410070360180741e00801007003100035118072400074052003a506155841e80710107481c5d4100d005821400c0c2e1525130717641030801140081425102c0c0204195241c00c820345030000b06000c40000c1d600c8171001407030091045403191030701c24000e104d00d0450348a44c1c0404600c480f881c2c00000c80181c15156861020700098a0303003443e46a0742d00580c8105c2c00402d4141d4580610541041ca122040501a503c445580c000503120104412001e400c0007060ba041141c4440a01d50100a0408200c0c0d02e595107110b00041c02c0048400c008440d05418803540e140d20105201034170030001141003e0000340307800e100981c1c40c03007807200a50083d00100c0740740c09201d414203028070b081d10446208881a1031014a001959034070742780100b0500404a0380000001c007101c2d00e0040380d00c0600701401080d0010b40c0c1d00d041c50b8080604e44103c0e98 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 503091303 1250 503090053 503090059
    0x1418101509051c050715021005090a05010e0d0905041e0603080304121d060a0e1e1503060f06030c0c03030c0403110906061902010b12010c080109090507060c061b1d 72
    0x4201c81000913400990082107880c0070040c029080711020040341480d0310a5041c918440c10003007809444013012400c030360070300c1c860030080041583c464071080d1606080541700001c541c0c910707410001307800c050304008400c1030040f40010301020f00014010031610640c005980708035001c01000100000c01c0e40c1c010aa0465041208a0b02e54081e41600a80c4c031089410340a41004600414a0380c040d04494884c51b000408802d0f42401c800c2c0d60990081000702424440c4031b4a010440b07202c0c00840849002e207002920036400900785d2010310941e680042c0c0f08850300c07d010420444d44c218280060360003030031005803080e5124594200000e65650700c1c5d111b40d10548045050182070b990b1324085580801158000400090342510240d004110b100c843c66007055004504000340d04040d40244c401d40d0300d9484490031399880315001002c581c82000001d0550707014290902003c1e02070001000c0c6548189000b2850b4007404040075084070400d1409808101080d8080c440b445106c6d0034591b03400e07415 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 503092553 1250 503091303 503091349
    0x3050a1b020d03030b010c0609080306130608060604090813030b0115110a060506030115090c0f02070b090105091513050108073e0a0c0f141810150905 66
    0x50300024030340702c074402d0020103265440300020301d16402021000c101a40281c000c008500c164100026a580100d41642c40b034104001c01440c81d03003032841260282d039a150b000f000b0b0755035180e0511004050703e0100703a40802052103002c2030800840d407400090f6101c1c182104580d45842d20104040d90048035043c1480280c2000000c00c0e500007070910485600302d00085640d44404000c01e004100c0780545200710b408500c0d0208001d42180c00a4118a0b6941d60701800a4000101281c5461550050580e0440c0401000e910f40d8403802c040e03c0100d8000f80805100840c180340c0007980c1d1b10042058501c030112910800840d0303084800c0582c0070f0340b1401e2103071051488403041d00303895400d0008e980c008900d8002d00c8140c01081e2181c006801040c0b4100c0e558988541080d08030318200e4030622240b00c0d0021008100d100c1c55050103507554902403e4020085070201040e01418402848101d81400130300c000200c980d0140e044c8203001070781d41c0303800c21428100300904c0340000c01c0340ca80d40109155 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 503093803 1250 503092553 503092607
    0x20a180303020615120307050309180c1e0f0d0f05100b0f25050f070b070b0106050c2d010b09040f030507150203041419030207050103020d1103010303050a 68
    0x4651503074080301314201c410030b151400000074110340240300c009000e44030220780c0c10104440007004040c0008102c8900d0240c0f07a200410035445c50040b0342d40a80c0c0e20060080c907104420703420074421410046031085040200008d148286500324450140009d5110280015016054801c060b040f11a0003070401a140c240315107410350348038030700d05200c01c5600014010341d4015107440d80321040704001460721603a540c6081c92540c568030310320900524015003800241d103c1540c4116200da950202c034110b80ca07031030f10005071640e4000004404030341c0180c02c080d41d60607020003504400300c042840b00540c1d19074175894142c210740070b0391b0f2901d01804100301800701052800700e4242d040f070361601d015070ba240741c07a15154070140380c6d45c908003c100d030000c000e21042018072584130b2100c0004008486032800c0c20218078044841078000a40035811000041c480c9501c41d4000341451000000003083c2040380c0602808241c1c0241e0040d0300061000c5410045258010b41010700070302417031824451140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 503095053 1250 503093803 503093807
    0xc0f0f0403020910330e01050c060a0506130b180a0b03060408180a03020312030c071704141e190308070b06010908030a080708072a030e010f1e0903050d03020a180303 73
    0xe94128000303200b034106c0c124a65a00c24400c850350410050140d49840c2002b04004024110540b0214407400440b0311f14501028103200d103140408005008035210743c40502c50f000c5499000d4440f00301c0d2601c0c0c41c4600c00f01d403410809ca07800b45212314060340c0d941c0105801070b03170740303c01d290300d20b611800c4003a004001685d8006050340c100328002d10034580d60741702c0d000d440001e0320586200400761800300c00140c818020190103007044840c11030307521500b11088020401c2c50403440d030304510070542411003441e40b81000800000c0401b0380030b0021109607165280c410340354110490031911500170004003c0c09584c880d00300002805080002d6003401c4140d40c0c080d0034803000603d40c40c108150325000901182c0b19040c10080e9640b803004040c01c108030b406824209003c100e10680104c1c0306a1510781055100d85101c1c03026119564070ba80b000600640070201e28910f42030704500700254005c000c4080f80080c0001850304000340c4005030356241005018100f03072600161032038902544802040429 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 503096303 1250 503095053 503095139
    0x20306010b0f09120d03150b0706090311010f06090b0d0f080313060911030d1b110d080c1b0a0308090907020709051e09060c0f0f0403020910 62
    0xe1030503203101d44810710301c152040c05000720b41c1c1075075009982000c000086280170034101d090b0b0300503603010b0200340c0012003081c15240051164000e00c00040101c94041400c0e81c1c405440b05210303103000c412101c070001c10305007503a00c141160030016503140390800280e0a140308211042c001074420060003880b6840da07aa418440c090050036946001000800500c02c1000c1da905207607004100300900a99410038604218100b036180340644100e03001e0001d100c1c099403419171400c0c00d02c00c042510180170741d124880c0c0d421210f4225000791000d10b1100025110704090051a075408008002505090700361411032a49082c04a000b0140c03100d084c4017140d0418111840c1810507248003440361200c6900b00d16110b01540305061980c0703844144460a80d011007a4080713107000d051084c141c4c0c2c640120036511020191003420304004200300a03c145600c3c800689408640740f001e0700e003401e59a401158002000300e4510026080c0c802c0c0601101909141c880340071170000a6240022854034078607201c00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 503097553 1250 503096303 503096309
    0x506030613030c0f020a0603060315050103050c040906060e0f060109140f152a0c1801031205071203060315140f18011b0207061107030b06040221060901060c02030601 73
    0x3c00011040144075801400034403255000d005500f0880c0d65110003170007020386000480700c04007016410f0407203aa1600926050b40d80050140c1b02e88160502088010913400d04100e40d03068580900180030f500070b5101c1882000841010f207254509000010140c04a64118520082c00c102e0905800d841c0c02440f0180040306076662404803290f440080351a02402d090f072450b4410040d0380d4104040059150f100340d00d102070485000b07160312010004641c484850200000f44400010008a038601d80079415140c0c081c20510710b811025100e480441d80074010310070101c0c0e150300301002000b4643c14113080c41e1620507403c0041e00a000490782500030701030040f2100003106800305aa491141d0000301e12864008020000c600302108209498801501204054008d50300001903190081c3c0d291000b102d000f13406000c0c2c3c00d081d039507110250f00016180d1074000d0f0b82401180d80340d40b02c11301688000d03404400c0010003071400c4000c00c604140141c01c202c0400c8414400300005881c001802815 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 503098803 1250 503097553 503097557
    0xc1e02120a02071e1e1d040309120311011802180604020408070e1626040318090e1006290d09030309150618090f0c0b0307140306010804060b0406050a18050603061303 73
    0x1487d00c3c3c40c04c046811001c0e98000c050000041c0c81400105600600c02c81e620f031070105d00900c1103410300e10103246a5202d0700c502035008802990b01d00c1c050003c0c0480603600034001000141000e85075001946000780710340001102011110601c00000326000e0982e011405601e013031038041d034017490000203a000c00c0b200760256101c4440403034101800b603a00b82801a5194000441a80d59040f100020b00301000d05500c480c01108500f1006108074007034041a140300c449503511214640001d0b031000d40f4800262200321900b4824003441301038034003079250414020360b4082840c0b40c4900b028040803502001d104ca000e403810004008860307402080f007a5107505014001424040c2d82072904074010704001c018aa807a00403070121b014550540954080c10b0199a1101080303100b10308000340e88803d6402c0c0d400f0601400005000a200390000c05134420050b00100362560b58401044034411142c01c080034100030745c1d85060f8a5401d6104099000c00f003200203000760b08105c4400d180c194202180541 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 503100053 1250 503098803 503098859
    0x412030507091e0306060e090606120316060501090b240d0b0301020705030309120a02211b100c05070b04020103021312060c1e02120a02071e1e 63
    0x861a405602c0341c5005182d04921540c0ca0388000c0b240c01e00761000360008480503858682d01040b400d0346c07588480d01c2030044c03130700a003000d8607120100101015080060205440104000b02c042c20020b242198014880c100108083d41001d40383e205451b20058024001c1613262008842c1e980407907100315140b2408074100f81e58058121600c3d019000120f2203036010b41c000115282002000001940720705003074000d81d01035110340f0140e55020b2061030101d00050b8044894840e000d081154005001c03074001c0d91003403500b1400c501e48528000307c10901c2c202a00018012039518819008410703102c4110300c1c242c0d14000c181c0d6a00c1c89999000b51020341050303070101c1c041100e19a03110515018101b140780c0ba004640062410b44040c3c4100b01d004d0000414105c03207900307810381112910841c0000c503000b805520341c181c51440c10a4102c0c081903011403154100010358210505100c0130108c00400f20301c90f103e402c1c004402030040900310051500e84843c04108605070717800a41540e1340003507480d292 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 503101303 1250 503100053 503100061
    0x1b02031e0f011406041508061b0c060f0f0a151701060e0f0709090621021c14060106020c0d1104110a1d01030203060f010318170a030f0504120305 64
    0x140c41c02110040c01215580307050280380c41d651020703c07010b210f5031084406001000c00305160503807440c3c2c24440d0f406140e00c000d020482c80603031100d03100c0300d10112003c0340d03040c5000c45400e240340c2582902e41d07140e018004828010007181800e086030b8400e00d400401d2144040081130100c031128180700300782040408104c012290803007900400d0041c4114012000141886480d40120b10f005580d55800700e00003e9002401a2160140500320703002e1401c2016040022000301d0759070455080100c0e80002c009101e054110295000c2145042c0200c03445d07600009251382451a108041e0400c0056600480050940c1d0f036500000344c0079030b075000e1861003003002d1070300101d009800346c848a600b41e0341e030100e410070140398801070030742029860120040c80f1380d0145c80150201d01c810303130356903800c6034503074030106541c0d40a6044400792080044580c02c440820340c50b0341c50704410080e042201b044000542d0940305502d402400304080c3c1c2c0a108000701c0c28039640d1032342013003c1ca4083e0014151120000303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 503102553 1250 503101303 503101363
    0xa03020f0a03050706090609050d08040308090d060608010b090a02130303051b1506041401050907200f0a1a01060504090f1506030c14090603060603100b0a08071b0203 73
    0x1c2d070340941291002601c400c13000c1d002c4d481c5805140b0000d03020100000c1e081c94054180480e42e034210382140c0c034044c110784807a0156881044d4480e00501c0d03e00c12040028a03070710500c001054000c000090b002e0960b000c004c801c6201600e40d012050060140610f11500e80501030110790780741c241203075100d03c203020354822014540c031004114061007035105840368418441c9442040c040b6420811521040d01045240750207024145d000f41e400c200041c1d0080c060305810700d541c20380228070038031a42d01d1122070b0701d00305000403a142250001c22840d0b0400c05184c08501c1600e25003040e01d0180e60401c6d2004045010390302c00d8003403841e1205680c07002003d42c0c1d4060040da2020000000000e40c03a0306000e0f02a00001a1100c0019600d14190442600010969103900b0b40140068a1502d920301000071a07000648035440c8a222000c0c0003d00340e4201d00100410b2625403112182454070240241c055413494801d100668101b21522006a8000c9206a00000d80100034003100c4611186 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 503103803 1250 503102553 503102569
    0xb0a030f2322020312091302070b1602030304050705060f040504020705010b0a0806041104231303021606090902130803070308040506070914010807020f07090504060c02010b18222f0a03020f 83
    0x11034100e00c006012740038040b50420f443d102d55a1550204034050760000126900c0c403044602801c541c01c410414407091400c040100848043c2802c44c0b420729445000042c102c0c0d004040444041c0e642e003140000320305101c00c200d0000e00d00320300a040d082c50143c40d04400121050001440340740d031401441304031110881d1049603401741a4424550f03150002e01c49141e4010001d0940151141c000c2e100f5070b1491003041c840544016a461361070491410f10100040c0d0868003026031036111407100800c80c02e00801c09014498080c4d940c14900c1c0c20607050040c00c02801602c14810051100c0b814010103e145c1d5000c00500000c2c640001d1696401100302d0a010b200d0104250b18010808002080d0009400c458056030041c0030800c98141c40d04016822038143d41c04180d0413609000c0c0b81c510710348200d06415441040c0d030722001080c10050441d1400400034075411525109100039071602011201c10035110110050078400aa05610002580700003040c44002d10802c4e04084010a5840e9210 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 503105053 1250 503103803 503103829
    0x1806040513180f050d020c0405061c062a0909021206190302040c17010f060818030c06130605060102070e01170705030a0f1205040b0a030f232202031209 67
    0x5030b00e424125441c0c116118502e43c402c400051050950f441c0c7d043c601840340741e0185c0b030000c001802001c2e1b2400070303100d203611002081d520179940d1a40d80e4070741e0309a80040100b2203107888400d030103120703191000740200d010750f0025402c0b0b52045c404160681d220815a54003d4012074050307400610250a40203800b81981000390414184800403441542086814441e031011400c0720b40240c3c0c030360a029070360000e40d1003000005644200424a201841c1450760055180c09040e20f1a00d10402c2a00b450280155115005080c0b2003950f00b040c45003034407800703400c044248050003001d803a00e03507440100c07207060250aa05541b4a030006400c2030040120200425014090f02d85800f480e04180a000c0b0282d182560105680352400303801c1e0740b00300b08540c00e4850007180b25060540e8244118002c0c1001c050741c00e100340d0744d0104000e01d54040941100b840365846180c42c810703d40564628030b450201100c404815440c02c1170030005940108000184001c002c08507030700c915490b000900e0040480c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 503106303 1250 503105053 503105063
    0x1060e061309021f0311090d0b0601110a12120b0a031205070c0f1d0403022a0306090601170109020a0b0d1104090902100c08160212030f180604051318 66
    0x44c00c00314040280d0540100c0400380b624108001040100030184612800040035840800510b100c0d0002e482550480c2c1c01690600d8445c1e05c41d420010b040746002180301d000c2d2600c410910b41603d900c1c1e0f102142400301d5954035410301c410402e030404100055500d000090041800030507046235a4422010341d69000e8002c1403009081d9500c56542d407064805005010428030701902c6a0f6202000d100920300075079061f03008200c0240c61120600c0c013030b0b080c9003000803140c02102e17101da9141d40800100e40151980c0c0042d0840e03524040c1c0c0c01a03802c1400c80580000e0341450072460150f0340d00001c410845079440c4842e0703911090220700200510301540a000109008100481e19181c180e01c903004107032081e0303003054221a502c1800d98500008142c0100042020854420032501d003c5d44080d046d480a02109000d2035a4003010303041d40c2240c0d40c001c641401c007003028907000e07821900004c405007054582915003400c0002045540c0c0d000d520800d8016152030441903040194007007000c1c0c4603003003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 503107553 1250 503106303 503106319
    0x90924311b030905010e0f031b010612060b120f07120c090504200d2001020c09091615080115090b0a030e010f05240127030b0901060e06130902 63
    0x2801d0090010040541c00380c0340740d80f070000c00134040c1c030001551014040440000b10308000c40044a081c4e10004901d54910302d5484002c005145211141c041d45424032407500460a141c9003818410f0440c150f2003c0c01d800e41c80701003040c0d10254081038402c00c0d07502072064020740071554200100c10102942c800001c0d9890030b0100020b1180071081a4214090300710010f144042c000208680c85600d600c015005008081e010503010624070708100d80c403001070054440d82002800080e0341c0302c0d800c60b4184034a4005000030402c0892030221400a886046090310b500c102102008001900500468030403d040301c0d80c00d400c403030045404000038440c201d61b559403101a0307e0018050b0141c526445415800d2000a01d240d241c6800360714802c0a410403150210054410350302805880d07105031506220042241045880004051400901d09000e0350194949140f42c88055440002c181740c900740d02d011028040c080c258480c403074001d002158031003840d0500d010303180c00801445000a501c0f540f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 503108803 1250 503107553 503107601
    0xf070f020a0b040501090605030709090e0118140d03050c03060904030c0512040317070f15060506120f060612040f0206041706090c0a030203100c0509092431 69
    0x44000f07105452003a82c038a1801640c0348025512408169441400715481240c1030007462580da0010744e05400d400c002050b88203144145001035940c0d1761040ea440013030034400c4452401c013002440c04007002860704019a217002c0c40001c2d090301018003042d204225a6000c6000d00d445842c4000515030040c06903110030208180642e46a40544000c594400d2030780c0103408540381c0701083d16501c0703030004c81e1440f111090340d507000b145801c00c00326140c00543d07821b070209141c1c5401c0054400303514000c000e01041e003014201e0146801c1c0c0109000d11482c010071803045803c85000030907401c298881e240c600c48100034800a520f0380550703009a0501030509000380070000c00025010b00945c011340c29140c250a540f000e01044075014007010f5096404000c2c0804103014907401140c07441500d1034510700b071180460010b095141c0682e1280348030800714800403203000b45c0200c4500c2041301201c188074400c9903032401008000c4002010f1604003004098121000840e0300308a81c1e0020312180480300b0b0103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 503110053 1250 503108803 503108819
    0x9080702091801050a0c0f080408130618120f060c0306170a030801060f0203040e1506040803040305070e010302130902010c0203012309010204030503031306063f03050f070f020a 78
    0x2940c0b0001c0081d9608150100300f04001c2031043c1d09020142d41c0e162940c0880b00c0c4426a10389501a00c11214210100410803803a900907180202408560752948443c8001c40d2607486207010f0307900070600d03006505100d04005210180010300310340d804200480d40c0001c84c3c0307095000340f502e82d2045411007000401e0340b03501240030800401f00e40c8283c603849126602c0e1070085651090301c0c1da070400580d204000a00400038280b2466500c80703d40e01c40080440c440342c0200c3c809802c95405a401a88049824000c1000a0003554058134840003850003a40c5103400040703002c03c50000d1080c03207139914a204825640300d01081d041c21600a03000f4402d616460b5000c0300c004000360048200700d030342c240126070005010f0007200e00b280c0e04000190700710b895140100042000d004000c0710038582c2c603400080c140200758a90307848402c07140044803803007080400500c00200700c0d0141c1c01982d04202680c60000341c03c03c003503880c33810000d07081e141c84644a142c500300300d445401010f5404114500c00140441c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 503111303 1250 503110053 503110081
    0x10060f020f06070e040c0801081e07030c060801030309140a1802070f240b0a06110f0604030f0305070c0b040803190e060411060301030b0f04020d081201060f0906080402040908070209 80
    0xf03031044c1e40401c000600c1321b60840c0c0c0840c081c01901c9a0703800c000c50302c601160b640307000440d043c142c481c107480c1050382e20394868240ca441e0381d20030360100b42608010001d02d60052801d82c02468200c442103500c290000010f000540d09009242010f0712186000d4039280072941504c039190f500c012601c0603581075080107944400600c0500416504190540d402541540140540c0f158040c1c2481d16490074094162960040b0008080041c4609410458030401c10008503000d0b43c02520b03520141d4002d401c004054a200a21450078003414201007000034100c482c0c03090b03100782c009406e070780c0300d803a10b0f0385450f1035072111005048a50705020011b402c1e9540812030390b01a0b407159440450203100802484407501091101030001011017000600b01100d42c2c9055500a100801000311210141d80d501001e0300183c40c400c02050340c58005007c901d801c0410710581c1000c1e8240009103500e050710050404600510090290361150034250400402c6005e17100c0007075008052078814504101441506 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 503112553 1250 503111303 503111327
    0x1306062102032406090a0905060c2107120507031118090609010803030f0622050402130e030a030b0402070c0e0403090e040818010e090c0705011410060f020f0607 71
    0x40e01408001c10900003405403103044226203400b064903d81d036440d081146a1a005201d0f200380e0745c440302404002002071040c103205403036002040e6156100c0d520041d40071340e81c50b00120361080c00c400038084c445800080d0800d408600310b40118107507850000460180056111102d5603810115418400142d402000111400c050714820401d50ba010100403400e4000e208029050b00100082032140e58202021a4450313000313001146190250491100110081030450403410360358002d0104500c0c095000da1140c041c0c072041440092031000903151603124400804091590b05e0348201216190b640645514a4020844140b290740e1000400d0191804a40440000d03403506ca021800b06081203099000b03a4000310181e045c20942c0b013819030a4034a1140c000d05220814003040c5032036580142c3d0500c105901801a515200a1b02d0500d007074a10030300405500000b4078081190000100d10108200d8609140004000c0c44c0c000d0b05a05181ca0f410b014203490041c5020014240e80203000c4000c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 503113803 1250 503112553 503112559
    0x130320010c0201110a20160e01060e041b1809150f0603060e0a020901050c010e0309011b0506060d021206010b180d0b06040e0304090603210906081306062102 69
    0xc01c2c40700c0c00f03044c00c1846500741a002052583d105424804603010030220480c425a04440c0b8644540350082c1c119003003a402000b4082c910001880718540c8a0400e10b0100b10642d010300c600b07014182141d2046041490110400401000e49825040804069402001442c00800010003400010301015a090044d000490404800003034007901c04d10801e01241c2d0400b52100c02034582848110182d0b20a405150401100b40a82a1169000e214101c1c0d0a05040001c0d0707581d0584070005004204200140088540c507840210003107072000c0f400c1544a501201d900343c480c01e20b440080d00e44034100c2001e6000d413103400004208181d400e40140f041c0300e08070b44001141801c00003004a800c0c40920300801701092078000c40c50703a0529410000b2240d0300d49094a043c140c49030104000c0354202e51007601d210900901c031a40030164480311020b042c0d05440c1c800e40e034904184001c0d10201000d000d0100c0002180c01e14010702426910402c054240390828096200d40d85040410300d009190060384 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 503115053 1250 503113803 503113811
    0x110301230403030b01170a0b060c160302270c0a1b03081b0f0924161506050a0b1c0e0d030e0607120e0a05030a0801140604060503130320010c0201 64
    0x40303540c0a2004028400004946c0c07105541e00c402d1441d01820a500110790046018050042e0f04902800090141e1740c240311000c445500c1e5004004c04980301d100c5018075080742c00020505a011818540d60022405812a644aa00709411a40c1d01451140c40182c0d240d40700806080540c440d5801d0301030290070003110403050712000160080d210f10306142490300010025446107080600c07070b074a4103031815540a03450302015100d60680303030b2080c2400700b500c4000c0c82c138810801c1004111211200c0c42e080c810030100d41040c01241318025180580c000300030b408200a0702003c0d02040403400020341c94070600014401c200c0701e50313540b00d03c41180c2c004070b800c1034042c54064100041c5544200081d9130b501d086140c00d01d0b0070030001d203090081d06082d4014844100049102000101071603141c1d0ba50758149907140824405810b40340040042c0700d00380420007000920390040560b9040400c1104200b1060402e1034150b950303101c1c50f180002442e81c25040f00740c036158190322404080b851380d0000c2c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 503116303 1250 503115053 503115071
    0xc020108040f080f1b010b09131403030a020901110102040e011a0409020d0605010201180209190204030c060207031403030f22020d060209040c020c10140d0501121703070c11030123040303 82
    0x250a07252800340b01c903000702c0c04400242742d078160808c0703045a40c3d0080041030f000340751584841c5c0c2140d00071a5504040350b000603c1051a50748102e892810341d001300001c50030f1030706000450340d2201062107044207462012601005a8941204482c020401c4a0b42150754030840c1b58124044d2082e8401d20b0b015519002d800d5141044001d0502c0810b07900030107204a507039a046519408107030305015503d42603401d000100003d0314000310b010103000a80c00034050545985051011a2440d82d004e289541003031080c0b006110781e4210b0190468a1800380c1b404000700c80f03114182d00d000104010754422201d8242030180b160607030003001c1c881410341e0f00f80000d1016440503a900c5550641068010180e01d01444005100307440c1c040e07544844594540c40c0c2100303220480140d8100780c10214072903100081030300400c082a2110010220b40062030350546c689104081e1007110800b00c060119004000032000b5541c00b9400b8601080044070b86400a81654640c03080b513890485e81140031030b140141b01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 503117553 1250 503116303 503116357
    0x90c03050f2a090310200406020c041a0910050108100e180c150a02010c03060e07030c14040e010f1706041b0b0309010e1209010c020108040f080f 64
    0x11482000201e10250981070300c0601c14040c11002c480c1508507500c03c1c81034195540d410300421040c5a100c601c0410301d40f00c03800400041101282040c106c9000400081007501c0d0046603900b0a520102d5001518042c00201414654450000709d0b500c100303000100b1041a01010713400302510003e03038030000e0035a58003040788075222040c0110350102000500059040c54000304500010781120280d4094000c56008607642208841fa015a880004500245440d40c24401d1205404161605111507844e00c05a2001d00300041c02034801c054848440350f0b03840307002c3c460301540c550310140616078450380c804241d840100280200f0140c06440d200005103a029054143c083c140003101a086603107403561170000805d6000418003044e502e12100180c07420008015522401301c2030004078114002000481c2004102f80201503120828006131b000760344d009054500e099828200407800307032110305080c901702c2211400100310700c400107601c00c01c1002c800c000e130449110309840b241d40c5866030000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 503118803 1250 503117553 503117581
    0x60a0f02071a0409090f0503070309060f05190809011506050d0e010c090b070c032102101a010c060b0a240302160f110414011703030405120a050d06090c0305 69
    0x112078074060b082c0000d000b00c034180c0d0f10126485203c0c800401651020395107640c15900008426802701c0c404007000c001c51501710a00c0485022140350642c40e1000c090f0b61031060b07001c85824001004540e600180343c11509500c12240900d010300480d00c603e40d961801401a40100c0c0d4034680f40e03040a42411a4410500400251000303640b921140c1ca814250440e8983d000008240c8005032030354800004144d8054482d0420707012481508182180020003034545100c0038980c481d0140f070201c4c00340c0091404501d50403000000d2034124030755009801c084000c1e0107030907071459205000000000b04218554100c100b5450650f203007505105500038103500b00d000d004480c00500078992540c5e400901051419030301c03203200c2d0218000074008030303010804440104e8115940c03044007074010310124812802d14240c022214000350301d1481c00d0b60f21140c0310449901011119280455144141c078000c0c4156522391081000c100841540e503070350311010300101142680442e203080003043c02d05640c540c1c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 503120053 1250 503118803 503118839
    0xc0d1412040f050904020310060e011706091c02010f050c0d0e1207080d020c100518070602121b03070f0b0705090607030f0315090603330903090302060a0f0207 70
    0x106500e03092074001840150503004001700c7c1e05000e20000581d50000600c10503010740a079801100a075818102603d11084c60204034400d90351002c010007418113000515601e0300021940745004081041009a026211b00d02591440c0c5060500b089020f01c9040080c01140c17880b44030601010401000c25a110b803070303007080805080d104100c0c1d42c000c50160001401182e000380e5005292419401485051020440721b4603082902d61060005000710900031010503100710001e8542c1600d003003006540c4009000c0100c00c01900424600340390380c1085c09000803c81208103072a680c007484d107004021702d0850482100e040c0940c4002c00c10f583c0c4a0b20942d8030811000d480705240078034503103041d0b036400c501e48000d5007007584908640c040056240e91403001000075010104403141940b41058003044004050340b140944030b0050588100c1000903010001411040050ba0220138281190f0050072074102a40001000400264859209170160040c01040d8282d915254846500340307031429042d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 503121303 1250 503120053 503120069
    0x228050325051b06040c0801061d090f0d12060905130219090c0302070212010b010e1909021603031505090106031815052710020c0c0d141204 62
    0x4041c080003040990800c28200d40781009420400b214100b0300140505218460310b5400443c140810804e610ba8203e01070701d1035000038082d9904021700303442118000c1004c2e542c050204030106810743c80900c800300019441d0420340e1040c24941d5009480000d0750300c2411142031910000240252943c401c00c0d01602c1d90b460007400c4800310381c00700080c1403200c1c1011a441303001640c001502071920310881d0281215610b01503180c07101401080743d28144c031038040009904000310a00305a91002980042460459003208a0401501000107030242c64000004651000034040a900c4042a8654505105c4d95090202c3c11415a80c0405a0b040340305064200c000348006021040c029042160a1342550364041d00c00e1440351601e04004c0c4039031104070502941e40080c802c429403000100c00703642c5500040c2c8103a0000200c0c40e640c0d50240000c0c00e1000d141d0101c0d00c150284414460031004003001013000340540c20b28108800c5040008440c10254454004160610700c075681c05e03102125001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 503122553 1250 503121303 503121331
    0x30803060d0203031201240207051f05040305101b0302091e030f070f080c01091a0906040314010b010e030a0b04110a0e0406020307020d050f09040f0f02280503 70
    0x112050011075039008004030303410b010600c84054200c4410300c0050003410b0f80200032000f104548074264008910003041c60464100c00700a12203602d401d142030003000002ca0303401101801207074040318240101d800080250003103900481a20b0444d801903440030420310381090041b081d8500c2a4101d1040080d081d0300303e260740500070b611050804070382c0201c1c40050242c440f0b55031598417040c146802c03608071142036030103100180450b540c1042899055403082c20054140360500d900c451110f0030f410341180000500040b03021942d02c40c07030191030040d0b620900800140482a0308103020f040a0850759001418200300030005190014600301001d40100c0c7c0c4900341e0311580c440c1c9410140d5000700320b8101509400010302c1d400c044062902c01c2e0700031140140c490801ca90001c0c100008524017808002c02445050462564042104ca0302d900c00c41d070004007010350042040282548007a0701807610310108040111000ea0701c000c02a80c0d07460b0780e214403550351188003941e090105440800011050b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 503123803 1250 503122553 503122561
    0x90f03110d0c0906060815101e020106090207060b120c0f090907030b0915061519090302120706020c12060c0c0f0303040f23100b0103090209090304060801090204030803 74
    0x410407498580208012481c0d20384400d030000a4520a03070000002440c4001005266a296030b010100e44e802151030304040380a007640140804801e61004140d040560403071000c4034001d610031401096481003d5450f07001a050840080c250030343d6240c051215021112035100c00454901c1c14203600400e24051a480700c002e100d011400100108054070074404044085481100058070a002000081001802c2860b00c1d081002020b010310b0b0060484000d48031441a1001c25034662030180704c0c008003844080c04d000c66410b144c1d030744082d4109480c05810400c20f5400b107082c0c020303515183c0072102480400004d1002440d044400340819800400104041015030030090458203d41c208442120205000050640d402505d040b00d258201036110000c1006005440d0700511101488d0890390441c0d0390b1450b114540301d100c00b240665581d03841441680648e021910325500a810311495240c2024010795960250180401148441c0c00020b540c00351402268141d0b0b074090b0313403a030075500c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 503125053 1250 503123803 503123809
    0x507020d021b12100209030d020604170a0c0b04050706180b090d0219090902040507030510030b1306050a0b0f0a06020d12060e0901060501030507180b0306060f0309010507090f0311 79
    0x80340401e030b076900c003400403140e4000c200f040180c0c00c0c580780d29040040e5a108103104044c40c0c50715400d686005d42d04000708020100c1c0c100780703c42c4504002c015aa03950b03507460942c01c070380d02200128001c0546051401b88011b00200003402c10a58590b074948495003e44a13108000c00d42041c0318000c2c40381c81c20450416507040810071701d614140b0260250714040b0440c2c1005100d0904e036084544042c0e41e0b200140e00358900b60150940000d000d017000c0040f41000c240d841c07403c4e1001e01001e043c1a004001141000495500704082690000410046c0342010010034019000048007288039800f00e00030700300315151408500c402c441c0a9001481c100100ca042076909000c00e8580320041980e907140020710b443c0713a0450500c94980c4000014515041900140468801901240400036110660700f40c103000740346240140c580444c4441d4a95540b6000074038244500850800011008014030814402c1500507034003480e11a01c400300219243c480482d0329480d103110107084504d140daa0820541 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 503126303 1250 503125053 503125093
    0xf0e01090e0c071106180406050405040b04020f1f030501090b01090815060d12021005010f2108090a120302060601170703091110020c0126061e04050411040507020d02 73
    0xd01c220800c040110313500e00001e4a5400c90208816596803040d03003c40603140038070400010b4503044500300980d08040d203c40a01da000180002c0c0200c5103030030036846580c0c1e090810440e07a20721100c0348dc90500c0e0000000e000c0c080a100e100e1b0850304081143c0076660099480d07100b6940711800410201d600c1e508d62280540c0040d20242d00031591000c1c41c008542c01c00d40f0071341041d803c1d030018050b622000d0b954078210358050344000d809001c1c1200910a2104d01840c4a181c0b10715442c04005800a0703042801891080c4007840303038030603055000011040c08135015541690b01075001c0d14103a5440c8001504c105190310380884091702e040d0b00040609000354007020b203e42c0510120395401002e10041001400c00e80500307009a48125428407056074446041e40713160000100307003038034031640c50b050300007250014043ea07110b60080500c01024036045148241c0360704000b8001c0c811414107090256a00d0043c0107114091820200003601c2940001515444d070b03269680200203100c9a00c8080c1104 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 503127553 1250 503126303 503126317
    0xc050d050c071a100e0103030503042114090102030f0c0601080d050304030c0f080c0604062906030708061c0602070201030b1206061c2f0904170313060203070f0e01090e0c 75
    0x1440b00f1040443c80d541700200c0719028608c40c1d03e40035500c2c10035050100360171666030400c03a03c00700c1c0c0041102c840396100720014011180100b146031075407240130050f400c0d800340103845403041e03101141ca1540c080740051040d040350303001c80668612a005a000320788900c000c460240c00320322404070300400260324410310030388580a01d60b86414440381c480840c0c28070001761030655a86444541820b2801c0d6980503031488400d6002090031030380340e50700105442c0d0000800c45c1090002041c00201207840e160000380d0004000c001d0303117449048510b481c1d0002e4105060683c00240f50211761041ca0030030328a00c1808001030030007080f003595900c041044411080c1c500c40301100c9a0b2aa0390000385050400d0081c208001d103002022080641880c07503003c2c1c201c58513511510fa440140000700c0c0210440241e00d00e81c1303c1358640d85c0c0d510b115803804a4900c86500130314047c40003080003103090b400702d001600c107800350f514090140000d41c01120202414080c2ca91a150200080742c2c6600071034000b00f500c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 503128803 1250 503127553 503127571
    0x10f08160909090303091209051e150a050c0610030b040f020103020d230c0f0a050a03020f0703020a1a010b0d090c08010e10140106080c0d0f0c050d050c071a 69
    0x801c1d44680d800750541d41030a4085004c44e40700d640c9802044000243d11200303c003185801082c01e031030180014280079001c4540c805500c401801c000864271350a4400004412228420340d840c41e54140003042c41e03000d111101c45600400c40030901c80c424101e0204210703a0011801d043c692180d031209104c041c4052130407030515500300607488600c0000d006000e403c866141c510704000400522500203101d006050014ad00c104101c1280c2911090058402c00a440e18001e6150728908909900034030800041464030400424481c0801d0b50004003031030101d2080702000344100c4207110a4068202c00c0c0039881a28400744903242d441c2c0001c4c1d118114543c0666000081180d0703482082d42143ca0030707050220550081e41403403c125115001d0040300b85181200e0f02c1c1d83c3d43c036200d03004000c0113000e4a860f400c1d20b4001042c0c61541c0b11604000c1d10408100c0041103100030134040034000d98022400c0b0301e07115091500050014200c6000d90ba222a040781d062000385600d05000b501242c2c00a2103200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 503130053 1250 503128803 503128817
    0x70905040e10060f0501110105040209220206130501030f110406031e050c0a020607020a0201090e0403110d0f0314010f030b04021306230f0a060302030901020c060405011a010f0816 79
    0xb004a02c81e01a200081c51160507a081c07545c03e182c0014084003804904a180740c3c10602800016150300003a03d6100340501800d80310307184c00c40ba0300b00900007892070196000b203003c1009000c1145810861040303850903202000301d4400911140103580e9a06a060b400f540140800c110640c0030342c104140b000400c1c9680011500c0050a403011501c003510340e04c002c948e020800f8410301d0340401c9955001020b41c00142100d65080e4002003c4200d00c7c0201d0b002543d07200d01103402c141c0210383c510799100241094844240d5040d40080048002e40c86402c0003a0800b410790711b04408501031503051300c40701881d00240c141152610421800090000c236000000e0515050040346184900d001505030400d0949964501c030b500e0050300c54500712058415030b586442c111301540d0f80540e601c100d44c03a070b00307016131603694a1200b42d0090107007550010386030285008100c02c100044d4031034040d01c0c0e1001c4102c0003500c201001180c0c200c3c807126040340071a11100221701e164906200f9510030103171519000c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 503131303 1250 503130053 503130073
    0x406090204080705042004031101051c05040b0105010c1a0606070b01320f01030b03191115030123030a0c0b03040b0906090a02091308041e05010206070905040e 70
    0x400c99205501489807604084410300691070309001e00001d404801c000b8000955640e08010031502c603500c00142100407084485411340d0040b01544c0509a0510000f042c0c6105c8100072800341c00221822544040414004601d80d03000340040fa44954001161105d6007200044012144801a107401d030311080074000b240c00100c100548034040c0590306100c002c100719504e034032540203202c0c001c50072103840b1040c54842151a000081c002c550130034a0f010400219580c0402c0c00c0400042c81e126070b10a41146050034440790005a00355200b007942c2e082c200c5840788100428030700081c040c0380c034602400229120684100c0001c1c0c07a0407040101034502c4043d50b035664410552003580480c8000d01e001c4104024444038080c102e81c003080b948003900c150b19100c8401500d41100d400000e10449904020a420203100403080d1402503108e985076990710344450064066040d01101030705400899240803495510225040e4002c2e401911031004407401c100c2080b0251806c540c1c4c450036071103880d4003c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 503132553 1250 503131303 503131319
    0x61409060703020706080601140306130f112101120b0a020c0601091a03371205250209040b0c19051305090f040b04050a0f0605181603030e0406 63
    0x1005020b200c3c1d00100581494000d0141002c3c400810b0380d4140814907500d4156601c01c3d10480c0d61204080750010b0383c05040140381001402d078401c122281c1843e0000c03000c0120044002800085d010f10701d200303000d0082c1856240c000d0b10074001c0c1c40b540c0100352103010000e1400f04006030001e02c2e400c0090b0502d240303440703da403502c9402d91050a400d501d4540c24900b020490303044e8a000f503000e4000d1b0802d01c804505481200645003000072400707a0300900e68012040342901c607065942c0c8071481c00c0c225204903200030201e0304018140018001000b80151000e0801180600c11590182501046035202c2e125080c003d20014500b40d14070340100140c942c3c9031020240101920485c0d11040d40740c4185600c4107a000049402250046812005107d4007909020b40240d00c941c1c4030114081c0c6603541c0c07818500700054440018600c50512402c04108904c1ea00094451040022284060484401010742e103142c61440e070b1907100210142031010a102d0528402c20960151000c03c03c25565030075 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 503133803 1250 503132553 503132557
    0x40b1e0a020105040c0e07020d050d0e030f04030c080f060a18060e061f080c040209010309021306080d0f120902030106080f010218010201020304080a03022109030c0f03030c0406140906 81
    0x480c00050350341e40e080100b0020781000d28000703002421030031600307807a05520280d61450040c0203d0244080411903212054442d005055055003d42c260b81d02d0b40400381c80c1d02c40941103400b084a80d06c100100201c0c1203c000503c1c2c2c0c0b80300c2080801418151540003150004007079034210071580a18280701c032000710b06207002d003d40c1c800080d801000107203420540508111140784c500350542407051000c00111070006100030744800200d400580c0c47d005400180d00034110302c5c200940007400e145c001c0071041000c1c0d0050040382c9507901658400c0340c100300215a002070294010700070504200c01160500041d034003424038948050000a805611205618504490070310a5401a0740004543c800e001c4e07002008840444280002d5045003015a1500142d00504075514101a804a020f03005000107507034401c00c208000b00c0c45521400d02d054030540f0795128640c240c0a070300c101c9015894007680041168460485140704900b464201041100c1c030540861501201e0001800750043c20b41d50100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 503135053 1250 503133803 503133817
    0x327060c110307050114030604200c0c0f060d0b030703062d05010506070213150b070501050f010605041502070b0a030608060c07022b23010f0e03040b1e 67
    0x100c0c410380e09034614001c0000c801202005000e6004410308210300d907000600c0030341504215850340d0b102d81d101c102160041913070035050140717900102c44110f0221041c6c0014014164001c0980760002038200c1400f2000c0111964180c204800304847c03441e90400e62300c04d011001009054806403680c030f45415042c0e0b140000003a0882d02c80104070f6203d00c0c07055a0080c0b002d00e401105226540c07400000511901401c14007034043c4044071010b10140d0002e50101c6046501c01c4142464151640ca900350940c0010318202c0b076039842c040104800b0181604070a0485065594061a00781030044940300324401c1802d0310103520640d070020491001c1e0b500031708020700e01a80d00003080d600c1c20414134078007070002c0c1400d02c105c0401c20100001d601c034850716001410281104108010031081e0800703030700060503009003100c0b02c1540c00f2078417090b15110484259114000034000c5000c01c0c4480302c120340c04040d8a620f50b6004000c204110090b50700a000c140c101c00740c0348140d81281c054200d2003640070403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 503136303 1250 503135053 503135057
    0x10c05010b0a0b0a0e040513171201080a0b010b120105040209060c15041e052a0d06060807061812030c0f080304051504030e0103050c0405040e0105010e0601020a0807032706 76
    0x82030b00b10fa002c0d1702180400c00080308441c140242d003000200240c801504001c058240411090b0307072029046100110303071011245070381141d12981d544ea1080c0d00c0d9020300900301e0300108110300000d24250840b0580c0c10f0a442d24807070070b0031640b8001c204030095121500054002d01c050051850300390060008401c01840072000402510700ba02d41040c0300310304c0c1103004641d01d0103001e60002050002034001c001d180c2a40c601200c00f825003c14011840103400c00981c0044146518020440036812080440e154070701282c1d1081e489201c251111230200c050344124407090303502080a150a41e0300200701a0003402d20706004400c686a407a602e511260302512840c1d00003092004010003000903454280d075100a8510320305190354010660450401d06904058807103000c200048004400c03a00100b400500400c00349403c00b032414080d01007407007880048011031000401075400407a00c00f4a040c0d000b01c0040c07808284d680d00b0386d0785800080e04400c41c5000c2010382c12400d542c140310031018003065 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 503137553 1250 503136303 503136307
    0x10e01020c100b01030c05070b0a09020a0909021305090d03050c090d12110706050315120613030905192706061e0e030304091d0d090303081311010c05010b0a0b 70
    0x551242e0180d4042c10f11050416203019072a1814a038070109599007140e21155840c03041e220000c40138068218540040d5209415000005074285554013402c4814402c2c0d4019000491402884040359001c0728031002c5600401114130109100380e120070741c060080000141030054850109501d012000c1b01210000e448080140d203030b0350000e0820580c141000f0040c0b02681c00e03c01c00901d23a00000d4421234041c0c4803840d0454017950b030214000d03402e086880c221281442c1c841d01c64500d9554a0005030081079003100041a11f0402005040001e41d040044084d0385180980720207a1008022062410307070180b10074152450414011140140450f03030780d0406d412800300b00c802c1940a945220410701801c5603481070301e92408015a0100e0328100d03400104001c90b02001500c407030f6038810760300050140d06024078841d500032510300b00342e038003941d6814002d80c0c2d20004400e107a4a80301003c2d08800d07420701d205449611420b202c1c64031511075800403410b0f151200110700e035641103406c010300103400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 503138803 1250 503137553 503137573
    0x10c0509130203010f1401020a05011401180b0d0206030402030a080c0a03090501020d020c0609040f0f0c0f021b090c1c05011a040506031f0806040b0109050c0a0e12010e01020c 77
    0x184215040c94001140f0715454003010381c8021605201d240d210300d10180c50501039a0090045440460b00403009200da80541540354010a0090150102d01a9000c0c4101d80c5102c1174882c8001e13660000d0300480c510240791302004100c0c0c100600890340b52003001e0200c2d0001e9120409480102d6201c4010300c2160440d2402509154158108504640c000d103184140242d00290141c0c0e075040036140c0d41da90b40b0b80e185c0410b0103490041d0350f8038481420004800e40003100b95001a0024015682e02024083c403001c0498540c00042041000da07c18544030b241300345403421540741c006d00c0c0040300034075108a140080300c06e0350006440f0303400160381d42e004020000c603142c1c94116074910011078501c0c0a0070000043d405000103272402180b2425001d142d41103e45900504c0040c1c01c00404580309850700c1c1c903108680c41c0003405181c40035402c280c0820903114010050b25082c080c2600c0311000000b0820034030645c6504c0c0e018200c0a0341d2140d8402d9500c050a10007010900103000c00b6102d42d486c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 503140053 1250 503138803 503138809
    0x7021c02121605011e11070504020a050705011a09150102010603020d030201051b0310030308090106051819090809060a030f0507020f15010e01052806050301090b0a030305090f04020c010c0509 84
    0x1420f540607078103000c140503030440c042da821600e00c4106055418000490110700d030b01549411440c0c0c0085400520000e44681c240d078211024200d02d5115000038824024982d030350705c0c0c04085c2c1807240d036080b095050114070b83d14002140e85002d404107200029107141c1e00e07000110b103100604002e0340540d54134000d01110030250f80b020fa02d061401c0c02c1e400c1ca103081442600f54114800c2c40f001e0200459000406e241180a42264009000080803005400701a01110042950644000c032141d8254081100c1c0348419024010013140c02001c400e040002a000b4400300d50b02c041d041004040d40c480840c2c0002c030716441594013807605a8010010038000b01003042c41d01441130280101c01da690001040240b600c1c0844074103488080e02c09200400c1c0e40845c00540c03480c1c441d242d07601981540004582c40741c2c401c0145040320b24007801444180c1044040c80b00d042030341c1c04041c000540420041240e81020200151090009480140b5180500b42d105003124010000600040c2d00010950080c0c6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 503141303 1250 503140053 503140093
    0x603051906060e06090a0305060412020f07180c03020d0501080607020c032803020f010c050a0e0402090f060306060c0303090123090601050d080c030313031101020c0307021c0212 78
    0x38559150400c045414803401511031030607052494803030200054083c000e81c0303030008240011980201214070030f06080c6041901104003094040051041000900c0c1c1c9050000341d041c101c41401014025008840264002801010314a40d0500da005c114800840003103101f5140244281c0000d404181010007001781420240c0c20814840c1e4000744082401940e44407140d00b0035001069800b1900e0300c145020703800d010702c103041c1c0080c0794a40000c00d404c040c0c0047c0181a504a96600c1e50403000c1c0b002d080200300e018200d4402c1c0c0081c18280900901e052000007036800940062009062000001020b0b107154011100c1040c281d441c0e403c2600a56056401c03401c003010080710100701850b11000e4180e4600741445014031030320292400c1c4081c4442602159107495004095999a04d086d400b44652031011210450000d140d0108019243c00188240e64039030b90710360055407424500e9000c100c2020b42d14280390807102d050252820060742c0301c0001460015900000c0d220010070816404880 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 503142553 1250 503141303 503141341
    0x171606050a1e020a110a210521060307050307080f010f020715020d1407030b12010c0f030213090212100f0e040f060e0106060909050117120a05090901060305 69
    0x705041404442e5003445003441c20070900707508040107071100403c1d40300312201e003043c0d0820300c40307402003405003020312005034038016244200c120078000e04104002d0840b80c900c00d9504400800d18040c406807203001d00c52a017290040d070011300322080c01d620b45000a0610b0300c80d902ca007106a0002440c80700f6040e080c0101e05810000803011410441c1a4460030305038000300380d1000a9a50005959264854a60100d18840b00703001d0a280f207494100d502600408030310b141140320710f0010518800043c014018484103801c0d40e6071714008542d0821060300650048198080600602600440c01603042e1000e002d01d06c002e41045011810014464004c41c0303043e8000041c8488102d40612403290303440c20f566040369204142602a10305800c3c4a0018409055286215420440009a400e43c007500603003ea4003c80001c01c103c0e682c41c440c4841300c548080381340005400404400178400d010501800400e04281840c80ca0650301400140004000360000e0010a0751035081c480c450440355503890724 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 503143803 1250 503142553 503142571
    0x10323120f120112050d080c07061404140f25030609050705090703061d06010507050a12020f0307021e123003130b060301020405030102030a02090f090114060717160605 74
    0x1013522940b14141c170707103042c0020b2805011580340400c004500782ca04903081039800031810006081c006000d082441c000390340030b454420900000408008000c200502d541c1c441c240101040da10802c050706102081c44a01085610222000008a4560b0069452403482400500740040c104010084441009070040703007050302d840e000780107110000364119000800c3c4804081c80750f6500004990300d1007004401032050040298103401c02c5604800c1c1c80300c03208640c0075525200044c090a56407806100c1000e0740c001079000c4c1c10800a4500030317010040301e801401800040440308449883c04180c030b0810404040070800a01960b03400b05d10b2042c9640307003122154690300780800c0312200142000d1001d4105596003021807501c1d0b03800d5044030000c042c042c0003175489140c500c141a00035040008801d000300100d1007003210510701455414183e490204034101202c2000040c0020b5030400c010443c1d20009040c0c4611041d8100740103001c1c1800c201919051540a614000b0f00303980b805052621 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 503145053 1250 503143803 503143829
    0x20307060c03080c16021e0301180b04080306040902060a0215070903050c0f1c1104060b0309060a050c0d05090a0c0e0601020a0311160b041d010323120f1201 69
    0x2070352000f4200e0304078883c0d8410030780b038441c6222840c84101411070700075800042d9186504c69803654003000c04903490700f100200070411440c50103510b1fa550818009000b5014030001400046804c0c01543c0c10000c05000000c80b90010380c00b00310203a200045000c0560700c500c1d0006004000040c410303034446414941111010318596515940c0c0c0003d03141d2a00c01c840422001030322703407940610080034070321a0040700c1c050441170038008050742138410b4442c061424408041661300040003180d0081034888004d02c496501d54080d40010400544492010f2504101c41c01d400543c900400d40292007940191224610500d09040011030a41c0424070365004041007000903038021550b1074046415040049800800321411400d04144000b00c0c400c122401e41d0100301000390b8000740058a141c0d417036441142c07810030006003c207442484010f00e00d90b00f203540707080c1080d0f034140c2e901c6589108208441a40403189500412074102100c00a01c021011a403562803041e943c01d06801020080710040d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 503146303 1250 503145053 503145077
    0x110f120f220204091b150e03010c0c08030712020406080105180f16020307120903170319020c1e06060a12050a082a0a0210030b0127080f01060302030706 67
    0x400c066507000000c0e208654500d003480c244542549881411240092041c000300d485042943c040400f004c0084005000300d100741506040502c00c00400c00a551900080c0c0155541c0c0d150243e400140100c040110701c014004410304d00b400544090403854481d0038182d8144000c0c080240c814900c685484c2c2050b105100000b400910116003100c3e911410005202003004140e14500c039803240100303422484a8001030ba56070101e51041542c0c8160900c1144481c1c400851041d03000c15612000d004a030391944d00e0b00b1855940c02080406500015540d580c2d4100c0302d0f1a05070050b456016400743c1209082141e14509004100040c1034845401120220241c46040e9504000c0c0c6c002441c0b2140043e0040c2000c900d0f144182100314500703114030002400c08841790b215600c8000480c080c4000038000c0e02c05500a002d600c54454043c0c0d2006200001122417078002880703102e10904142f04110003185c180e40502130100365101030000410742034990b00c103252030030519500440420a04c50120703 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 503147553 1250 503146303 503146351
    0x91908090405060d120f0201110d05090601050603010312080a06050d03090e0c0f0d02030717130303140c0d09060e030403030e0f1f03020304060b091603060b03060d0303110f120f 78
    0x48012603880e0100e0b909021b110141d0040c481c03201ea8003445800402c00306604401c40d003240740308801d000f054919a03681c48060044501084c0002041c05041c100c003403204501c1984542d620101c0e45a01141c0c1e995510040b039005402c0d84407d900040d8826010300189032026038140d0080103040d9a186041040c030b1541440f80911500286002e07000004a00854840e070140364001c184044009003c2c00c141041c00441022003a0440c0800d041c130070042002c49059090900c1001c000702d00728648001000280014000407a08603103280e46c4001107020541c2c01c00141c00510f10940f503107a00d00d280c450801401084034103000d481070701c03a02e0690360b0030320b001c0449422680d0b40c1c1c00d0140c0c880d15540341c00d201800c0281549500300380002e04001c58403124920800c02004030340c404000094a4000c09803d42c030040700c4280c1c102080c60407480001e44260300020101e404401103a0401d040790410240d0755000d61605008044900140060000b090305080d4028482c0d5004880341c1c0310107502 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 503148803 1250 503147553 503147573
    0x12011d060a0f05060f0415080f06011d01050309070b0f1e0304050c0d170703030504031701050901150509130e0706020309091605070b1008191505091908090405060d 72
    0x141c2401381c031001c41c142417050700c1c0e0401d41e0050144200800e403461940d401c01031445008445c090307880c82800011074015401801c0200c65500740f2440c044801c4040030044da21988080c064074842d1166813000100c03004880d01030110080c0300b00510741d554050801400780e50380b4140c06c2c401c0710b0b0410018070000500020303080180c05815a9500c0c40c900b87c81c100fa0718000c2d16580188135a0b0400070300c0108040d81980040d1181e4070a448500c0d52080c2002400c02c101000d000e03503500050390000610482c501442541025692490861b06c3d0100207400304110607102151068001e445500884103a04203001c2a4041d100b103100442c2850904400220f07201c1016010244003984100c8001c4000d200360210340e04c5603041031070708011b4245042c1540038124540b24890240c000c0c810040105115880700401c926040002c2607208280460307004000c4c20050320358681c034407500086035004121300041800140c061008c05481d880003805000c00d9030001015507104101e07444803600001c0060700 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 503150053 1250 503148803 503148809
    0x2515050906421002031c091a0f0403030515030601140d0c030b040c0b251509030806030607020f0303150d02030703060608100605180a020d09080702040c0e010207090b0612011d060a0f 80
    0x40200d50004142411540c41410304074105115220000700700b0b140c200789d05501c0c02a4481d41e0200300907a608041b02003074008200c0340d0b6605800000c01001901c03520500601091070082540207110310a13070720b258010703a00c0c1d441118546480382c01c00c014002d0b840600c000400e00105803624210001140c0100b81d00e4811000a0340d40381c0c00ca0070414032503a140f00c1030541545010800000f4100e0802030113005084941901c0f0b48039410018500501c0481c0050340c00000030011401d40e01c0388000e108803c10741280703c0b030300400764801c0300000d6602005004003d5000d44400281581006d410134144088828003001c2c960420b042000075444074410104607040741c81440b80c40c0e803644840d00000c4d2040700400c42c00141030107600002d100381031008002c0c1c2c03803013141e04000c244950710f03003a1614a83e2034203150158202900800462049400814060340000d044903d8502640c04641900030f007030300900d0507903e0585100101ca0000b541c80c2d50004000c580001c0507601e000840080c8a150740 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 503151303 1250 503150053 503150107
    0x1d03030304031e0201021b0615040204150c060e030406080a050f06010c1506090e0304170c0609100c0203010c0302090103240614251505090642100203 66
    0x901c2c843e410350710030741c19a06140301108050a43c1d0000b0b501940d940c2a0540e200c80c88000c040c18411010b283c01c3c401c54048452f005d0403c0424041e80b07100392902d03d6240e1080d1100d5455401c0311400010500091000d4040c079150868a410900030000441740e0090186131210034502c2800703014ae03006014010001c2d032100003042000d60741041c03030020f420b103940301000b00c90610844000400000c000390040c0c6041c00801c20f111000200f1103555040c41e0a0040e410901c09c1003004614203203c0e603e1240100c8608140c412000141d0210b803c4881e42141c0c1c0000a9001c206040d0303943c2c0c1406080041300300051007554141590004100140d0144145424000c020859401d0a05160181c41d960180c0c5400c82502841d008120011411060421605d21002082650380c4a840f489080d01881d030072001840075546094500d1340c01c882910700300f0240400c9035541400740350740e42051054485054840b00000605100f481542182001582c081d13400612402c0c40001c800382480c28462020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 503152553 1250 503151303 503151347
    0xc0305070e090a1a2a2710031d152202090708100e09030a030501060c0f030e0406051e040c1130180f0618010c0813061d0303030403 58
    0x6200481c922007040000b0528410701c803032840c05d907480140003034000c3c49911446c00005900c2014040e074854048040168801710000500301c0300c5203e607000f00000d402d22a4a6101003800030101841c21904410840121140c00e0810079140c91f024085056442e5111080e00300080c3c07980002c0c1c02d0310005005400304035011000032000084021000e00070100b09036003080c2814022800b9440e5482140c036507002c24200000041e1044c450841c4980258000d1281d804846a40c0da04035451080001800c1d449a120704020401c4c0d0b585a05051440c040b80c0d0407403a540114006110075180840549410b0145140c481440b0100115070494000d2014105e0301010b0700510306001c0007040c041e1703e14200100403401020416044810b80b00e030006c22203013100002d9000042004a103e108032040d102c400c01d00c040b0380f007540135800e41c00324584524401810f1003440c01c00180703510aa0780c06a030004501c81d0018118401000504210500590145280d8034248d100035100042016410420440e4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 503153803 1250 503152553 503152561
    0xe0405060403210c05031e070f050a0509060318070819081c0912140708071b030203010f091104060803121518040201020c0904120e030a0c0305070e090a1a 68
    0x10581c440340580d00c94803c00c00056000c0308004109400481d003003480941d030008144114881c91070b02c84d110b28234070740d00c44401c0c4d40075100c22122600080003013010b0003010300c0014165950000594800c2c48400f0346609541d078200d002c2032810304607500180c0d0503008804010a080041100700c84847d4004200690740c84d019604010f05000413180e000c80145051390030010000410386002024040343e50f141c582640d561460b4aa46c414190003c1640c003003080030b50006130303066031180190181d81c141d0541084c1d8a0300801d094542e2402e89400d5295200c03100300c100030b6403060040b441b40090310704100207804c01c0c4078503030b5910400641c41102000800001c81c2e900c84403c0000600e200900034440d540040019803d00b80800d6604901601070081043c8079803c0c0a1201d5105607001f03034072104610b074050340c103a441110300741c00143c240c000c007050740e00414054160a401548a030b8014006c0520304a40c0f00c100341d20260803044103401020400f008102101c0744400192151a130007003213616 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 503155053 1250 503153803 503153837
    0x3020705070308040617180c0d0f0c030b18010501050609040b030a081210050607032f060907090501080304030b0f0a1e0b12031303080a020a0506010906030204060e0405060403 77
    0x2440b640018034402e000240821855442129044640c0740685140d505031201e1001006608800410041a03400428000400d1808103012643d59008030400030380c080903510317a0a0400c4940d0025140003402405001030401c507100d284640501c0c24000300b182d94105000900f8612075801c2c03003448ac9407560561707840b0b40d805100c1d4a07032860784000c6859403105444155001000b0413a040002140c03003c4000070b0606083c0110b603900c5038144d4071440740258231074083c00594801c82480c1c0e03100ca129002c91a90800410905005006a60090080c2440c1c0700d44da1702642c40503005100c058009005c1000020440718015402c107070946007900041d62031100b071100801c440100080184112403240c10088100d92101c1d98820040e2400303594281e1051401d41c0d64804c0c000e0680821840140800100b001d5074082d210030300552043d80c08a1141e61610f07442c080003a0000100d61307a0b2054204114a8a4401e0700e0061841e0910308069141a072105904c50000a00140034410000c1c2088100c403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 503156303 1250 503155053 503155063
    0x904051903020c01080112020d021302160506040506090c0604061b02060a080f070e0d150b0603040b0f0115080601050c0a02220b040209030703080d060801051527010603020705 77
    0x3080000350521501180c00c1c0255901c00180503d4041900c2500210341c0b0f80481d50211100c0380c000c0e02100340c02e1400d5003445190642003095440c031640c00c0c0086c4400f4079440c0c0180ca94140148020700180c149030910300d040040182c100030f00ca81c024001d0881c903803640025a01143c149080c07882e0002c182c1c4075081d00c1100101740c002d6201000003111840103810078041030007681050741026a030b41e079020064030390f4603060004035803141d249274645000031078004414603048000174010030120445000309905030810b9408070751108590082100b401d030110003150050400d120b200030803180100f03000d00201c10140199040010003e00004e43e0340c420880301c01c0e1260301415a840448202801c2c0f171b403044e5803c003464090750900080c08501d01e0140265100d0110040180c503001d880e60fa43c000c20b982c048408a0405925070700c002031a50300a20540384a9072200c0d1003945115481070421201e00c2060100e042501ca04808842119500b005001d040d1022411b00607903510850410910f00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 503157553 1250 503156303 503156323
    0x31104020901021905010e06040606080d0c050c0409031701030803160e01170705130e01052821050105010306050601031107330f02090102070b030408030a11040305010905150603010b0906090405 85
    0x10b4030403d4140300412070309074000d2f82142e81501c10743d014000c1c84182241c82100c80d0501412540c06045a0b0358180382c1035124481035807103418050800c0700d21b009000314003d03090740151002c03035010003080156540701803030401d00001403070030340d039000342240002e042020a008442d02c0818401c00090b02103000c1c1c0d08030781710303044e2900040c82119030f16110030760410000d00886008500f4a10148000d00d562400d02c20888001c07904650040d08020461007070300f040100c18001c1a19811800b0f002c02e0084c0301c1d040c0a14014140403071280741c100300140079203030784a9010340c11750b000b041807002062500070316041400c2d4100310701071080301401c01c20130720b18208102017860358a458803a5a240c0069030083c41200801c3e0261446650b40d4180080b00340400c4501900086080000409005480d0302c410003804603501c42c2802c003a1aa04e83e40d084030943c02c42241d582d400281000f00500b180c110f20765211400324001e0101c0b880d602c1c0440c108000250040d80a03415600100301044820f00103603400c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 503158803 1250 503157553 503157581
    0x907050313021503090d031b0503010b030a1803020a060501060518010c020301020f0c070510050703080c070c1a120c0a0f0806041404080403060e031e07030210050c0403110402090102190501 83
    0x40e41400504c603502c408071ba244c400f01003454000902e14801c010741440031069920b46500e803c60380b90060644c1103034001003010841640d160b00c101a292034000403140304c04d01a41c001c103040600c5280030801c840c41138002805005040c40380e00300003101d64003414980c460a02e001c440100c05403004c68068007c2d45524455420b01103074001c419003001506a080700c0e01203640d100c403002d607481c054500d8480c3e804090005136001f80011038000f0044010f10b069031183e15441d151640e1605480381e4400c00c01500441040c000409540450b007a102c100d4018510710b84c3c81e0f00e060101c80001e0011100500328809110103600000c41c240d403903910000c000d80c901e81c0c1d51080c42c54107140450555203d0b0004880052402402c5500d440c000415a140700e20f040784140c0ca070891702e868980d581c0d0482c0b2401c400b1032082100c2d03108600c1e454001c06004012050825484504610300311525601664009028074410b04c8583c41c16a400074141d0213000301110762000000d414182a80035014809440708 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 503160053 1250 503158803 503158807
    0x611070f17010b0414011a1201150f030e06061504030c060201020a020f0105010f0b030604201c092a030803013201020705010f110708031809070503130215 68
    0x180078400c18014903440909070008010520400702000120f0740d110381000b10700c001c07140c0140880c18510382171420300e004064000c0d0800c40c0800c80038190f501d090f0440c01c400b9444000c10101c003034100d481c4000b449040e00b070a2128405040c429503440c840249980e105461111a9400644aa0003154042c50300b04135007884454580718040d02035801103452600500c14110031101414061017032a06950540800444040c80c00b450030510b038101406069000360354803442580d841c81d0304440820041e01c90307080e0351030300100039040d0080014000c4200d0010706080030840008c075550081c0440d40384105d10001034440031604480c0c40d140540000740b40800010002c40c80001308401e0044400503002580742810518121b00700441c440d252030750241c1e01410303042c0300a40c01881e40c1400c55030107181222800b681c0b40344080c98426540e00c010000d4100162006e282c0f40c03240d078030205100f130075a142c10150414003c000c03ca440000d0400c030742c0c024203801900455450b8403100201445102800ea = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 503161303 1250 503160053 503160059
    0xc15250602041a030f01030602090103140f0402091303140a0306030f060f06050f010e09060103021e07140309090408070f0b071716050a112803030c180611070f 70
    0x3034025809400390505003140d07200180d10780c8520404407480385800c1c00d1000016440c550741c1602035007041203c5810305881749043c0840360b01c221003d81c403840c2c03004240c00321414140140306088002501f4141554507498041c004250024a08038003049600b2440e5640d940c0080704074004c1c030041d08020546104200b4103820300009800c04d480056120101300710447d518000c00c01c2c00100341034a98007041106000800070304c2c1414440e82c3c0302206060252800c49030340d01c2450418080a54005040c902084035000c0c4041e00700f0124040d800c0310010740c0303070002203070010b80b04120050000f030901c00f00060700c000304804da2405141066100c88c110380c103405e00641c041d11058071480000d0001d0b1103440024116261038007a2a4a110551038080c600500e480d0112034810340b0807408900e6104506110896441008840c904418002040010b03800c6601d40141600c028403640400c111040780b40d103d40c00741c0042e1100450380326040c01104128002c0b003060408100703500c082c400c0d0310044000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 503162553 1250 503161303 503161313
    0x12101409010b06040f12021f020706030b0d0b010b0d0e1203010602011a010806060f070b010311090109060501020d030c1205070201060807080a11100908060a09140c1525 74
    0x38003031446100240301c00200c200901109000c0c0e84155440c00e038403483d080006003810b91803982050f0001c4d01226051190000c40003043c2c400548140050b030242d04100b081ca907144c0300b180c0e00500c1c11521090000040c0d12607440000d030600580d100600001a42c0b500a01280c0c480b0b900781d082007050741c0005a0701e106914241d00240324840141d401e203c20100d030944a03200804c850071058444144544032941800041d400126a07941940303000c2000001041900b01482c0c021803054215021080008052010f841e006a00078200075040c40f8052045a030049203070340080390203150000380124840021510100c07061b03200b40b001c5182109000040d603040d040070301030711800c0046404090360341212913a2001845009060005103007071220b00c038900070820303602a03515440d02d40003664807401c115050103c140c07210152a95502190820041c00d904031b242100d80302405416002001c0340882c0c0e1620740344c840304030340c0c500005901d29101011300007040111011481400ca0412034030300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 503163803 1250 503162553 503162591
    0x1207060e09130b0a0507020a0209151207060e0f1315030c0b040f05060d240503150105011e14070501052e09050c0931020f07021210 58
    0x15034041d10100c0006114400d0490a0810855008440120036681c20740403000500c006486001180100101d4030b003d6075400c0850342c0180c041061241212802008010392050621050352300c5030010030007004416007007803e034001c000307056030a404100d03680000100f131100041d4802012034503000300e403d109401c0103c2c40d42520710480c0c50740f00e4541c59000208560050b4801c00c041108111028459030610001912101c00c0d546000704240d8000c2128210343e01e4001790a03425071880d0101046241350070040c40b0b44001c0d5a80c1104025410040002c1040c00da10450110b03005800000c510745610802c0c0d5a0807022011904031f0b1550002e10f441c502a0000707407407032081159030071171100b01b901015100000180011030a440030381c3c50403004101400c4020204285082c00b4408441c2a0b222189098042203007802900b96100c42051405031140d0040c02103c1c04510601c1604540d201100c2210103a0b40c04580c1d6010807100e140b01503140240c0c800840e84050b05000c00300d524203c0b0306072 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 503165053 1250 503163803 503163827
    0xa1a060c150603160b070c031403071704050607030c1103030c0a02010806030d08040b04050f0307060b1305070e0f04110a020a29040312020c15010503010b041107030509120706 77
    0x1c007402079849080070140d542c50440c0103100501103901013008070030800c038000c4c4002842070034000c103550b03a00e4684d44404030703d07030b5481074207500006042c00c100641c88583c07903050005001c10700d0030581440e02042c12801620001000d00440c00c005c0014024481c0d070801c0d13a00c000404581d942c00c1d0464010b52901401d11040b400701c0e0406000c0760b0306160204249280c24075945d00d1384503d030380d25110f600c103444020700140c420740a03051340095200700a02c02400f100340503110120714850000d042c0300b00c41c1d603004421881a881e18043c026083d50064015500110071900072a5410103240050000d210f00100300d5220040011000c084603000300700704030041d0040300c2a41c0d1075900c00700c03018448500d481611a49494480c00600024040c0203c00380a0711142001170610400508442c50700742211201c805658030302004201514090081d101da4180c02d90b405d021010281ca0540d07403600543d1001002d12a0218504d010741e01e40510480144580900b1a0f0926550340005403045180c65 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 503166303 1250 503165053 503165083
    0x40302100e011404020d02010917060720060a0b060c0102070f1a041502181018050604032f060f190804050d0c020111010e0114090703020102060a1a060c 67
    0x803034016980320041c4a004280190f240d0b038600d41d036840368200907042490010890500401103401303d030743d02da941301000c48602c44d4801003070203040880c00903001c0c2c0442d492070390f0003044900c148601000c02280e500c0d0003040b007a030007045414450000880902494a03405c026610101d403440911443d80c9a040402c0e0007081084c520020494100365072680c100e40292000810301d84000c015110303030b80100510300c80701320201103203000c000c0000c2c0480400c40d42d600000e4a00c00190031501003501d8080001d00c001c440252500d807a650f03905050400349007075415200c0110b041402c0b18a01d44242c001ca03c0c10013800d42d99185000c00480119810802d90403000021021110003618000d480740d03805660010010a060010741030100c82655030360408a040101303034045856032800900540da45210f0000011840506104a24003481c0b03000740f00d0b98555000c00810005030341c000c1340061b0000d000c114003040106215040410064584240ba608454000b810b2040c0007070204080c00e0805041d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 503167553 1250 503166303 503166311
    0x4200315072a1b0e1f0f1205011b020a0206030903040f1508070903020a090207020d080c030705010b19030b090a050a200a0e01330309050601060801060e060901120504030210 76
    0x2840c80f00c3e8071401d00d004040100705000c000c11803510851401d403003013842c001110300001d61244440700c02e286c820741c0000c80507080c144140d02080001c1c01001c207800003109800c1c030400343da070300300964654442102a00a490000108401c650103004031006410307120010041181d843c0c1c244030303485114045a00000d0b0711040880c449038400c40100003266002800c0119460074070301104001d502154040b0390248902d0007604c0024000009010725982c5400a03540712002c90522500355210a105680306880700381c3d0f0a03480009201807501901e400121404081c7c0c0c03055481031410048040241039803181c492103104001f400700059481c0303c140342201c041c100c03080c001d103c4d21500320b0041840010700d20340140300d1070001d038051200403942c40744600b0885503886280c401510035500328100280d242e903855001e118041041f140140217600d440d00c069858040000c06080c034204e0b2580c450440021080d195070b108a406840d04166600d00f0007403410180b4005e0b40d144c0e210000c4111181c10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 503168803 1250 503167553 503167583
    0x30c070603020f04051e0d060501050a0e0408070803060a031b1409130b270a03230909040335011413051008120304200315072a 56
    0x21900030f440280c90b801d2040c5003000c0c102420490355802d400f10350003a41c24a0310f011189540c404454180700da010f0707000091154100340c00e11240c2c08280d049516000100c03c14040000c4910f000c5070051900700c49040d881c0c0c0c030381b280002d1601400b5800940030882d41162070400503825103804c000c43d0b40112100030404540c81c244040a0f1b070441d5a40c000382e0154528030045505445520b500c01141d201d210303003504200c00c90b211141c00742441284035034046c040900070560042034107030501d00c429210441c0180e0441c0e6030034091084008450086180101107410180143c0c3c5a0040d41c1c47c040c0e25041d9100c104040e511940c1150401800d0080100700000e40030841050101000102501032050a0b29108400014000280041103003a10190300028404002d000e183e01c031800d07200a459aa08080c18042d00d6601ea0740300380081c004c102c40a1a40660f8002500301d058441d00260340d200d84e40d40c09058400c50300c51f401d0040e040d0041c00e01c4064071032840d003144203402c2c8150010046419 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 503170053 1250 503168803 503168807
    0x309040b0409050d030509030904060f05030d0302040e0c09010e0d1406010b0301080a170405040908030106121401090c03110c15010e01031a090307020a0b03220201021c020309030d02030c0706 84
    0xca0a00940190802514004d100d0701c2900706a60000380c00044a10f09100c0101081c120703076580d0b0001c0c45c0501c110100303210390b1a00b4042c0c448a003211349030941c101070405107078501540e4054807220b42d21400040c9080d2690140800e040409001414031001700c0c20f1b1300340441a4811030060b85070310b008550010421b1101c200540e41610000ba0013890010155a107626401c900801113440145013803000080a41e1103010f01d420407480394500342c0c0c0b29494000c001d40002041001020500c1c100480c5e0b6070b00d0301d60b540380103044403a05500894459807124041d0000c06a800410b2072008000840c082060303800240f07030700d13549681c2c0103a003940d03a41e40c4000218070340c0c28000203000d402c0385545030072087d150a003119000b00381d02d401e0b82e140802c507074000b4100d0003441c0e20050f901e100100401001110409541c01c4441080148a0b1122442c1e80001d4581511b04c5508640100b098441000f4038030800c1603522401c006821034000319401800a0758a40200741d82840b144607100022413018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 503171303 1250 503170053 503170061
    0x80d110c0a062f0307050a14060c0d0f0207021306260d0305100e09070501030b030f12030a060b0d02070b180a02011b060c111605010909090809120309040b04 69
    0x2d007040c3d54040740d01c01480b10701c0070f0040e20070300d03021070040c4054480800c044043c0010840300c0c0c4100000e000342030092401c1080403054020681c0d043c1c200408101c8100c42c0c107c12514043d400c0c010000c0d030360303207645e08440080c0150000a5044100902c0030740d02d0500340c0c0d0102d03040d20b51f10f1310309480c1100c80890542c2c44070581c5220038401d4000000a06c0514000e810043d0440345110030f880c0c009403603000e40c56075035008072a01c1c1c00320343c4812020403a5503054402d000c01d0803020390280521802001c03045964009c0c542c42d03105610710000000b24070000d00e030f2220000c0e010b000718580d901c80c481c03945c481c06500031f085c0590b001c00080c00456244081e000c1c2c4044400c0c00c40010300150030aa800543d024004000d1848060f14486002c1d0001146440340c07a900b41865150124101c502c2c01e402c07840c01c0d00e1565409116140010244810703a0001084c0080f180c24036004118000b5a20702268035010701800642c0040c0d00004600d01c4210100240406c000300396010410365583c1c10402c0199 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 503172553 1250 503171303 503171309
    0x51f050a0609090e030c0303090102300417090d05070e0c19110a0c15120203220c050303160b06041808181903020103110c0309011107080d110c0a 64
    0x880c8034640200064002078004041c4c080008017585d0070096400505402c540c4203c41d0056142d500040d00c9800c0c80c2d00c00303001450031070780c4c443d0104140c000d20b420b00301c4154044c0c07001c0d0220b0300010440c81c81607684401c49101d00c9000d0481880208140340c1307182c0d106441d002e90b1415209060003c0c00141d4401c080e0b500c0541280a140110626032505484010440300b10403024040c100e0003001040c1104c003050010a00708021096079403041038010181803290a500729628010400d00c8010948603005450320411002c0c03849c01c45419140c242c00c1c40c3c2c02603000303980601020441030582003602d6641c036440ea0141c000807050369140400c1200711001480042c15506003451120040b50710600504000c05100709a0002c038112607000490200c441c2001914800f100e1606004550f03060085008010f5007103102070030540c03040360440e22070141e01c071054108002100321034041c0004204240c0240044415900a07001d072560003043e08503c510003035428410441000c4080c24800045011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 503173803 1250 503172553 503172557
    0x3020a08160504030f050a020a0b0d051e060f0a080105180f1504030804060f0e010507020d180311131406040606020c01021e070509151002070303050f0d060801051f050a06 75
    0x20b03141c1107a075218170706404548140c986114440d0329100580303560700a80e0250100303646c4a41c44000c41800715068800040480d4120504070000b180300220f1240100e4004808640c0c0405050480000c42c0d24900c2a13404100150b0a04c814800c0c4c0921000c0154101e150303020659600d0381060b52555035500d402404041c2110308000020007207849003102a802c18130480000c9400d0201400300000c1c0c035038000003c03c003650368106021140c3e030108400365000300f06d0f040081141404007046d0081c40690700c4090041070140725982400c0d55042c140e11007800700b6a10400030314150042090030a50100d03030302c90050f85000d40200d81c1c5030000a48004054050b4000c20801c01041d003030701002c9021040e10030b9280300e120f4001c2550340d101200c544c483c0c0d03054031140288110703210800240c2511218010300395000300d1001d0001c2540b00341100c0d403d20000d50195a203070302070403c2074010002a402104654030308800d20080d0766a000809030852001601c0058054481080040300c006520131500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 503175053 1250 503173803 503173807
    0x3061a21190f05180d020d0f050405060712030b010c0209040602030403050c0a0609020310020f0328020c01050f0f010b120405030412050d0305071107090b0406030f03050c16140609190603020a081605 87
    0x447c151003000c92503c4103c1c10b00c0c0c0b203401c0c90fa4a50105050360012403003125803110100011206542c14882e11780e2142007442c08038072039910364010414029001d00090301c0f07150004009001d150040c02218050150b050451b00c4110702807c0100090000342c408a01c40e0180d10400c03d42d0f07690703500a40d11106040380c4a18903680301c0c0714901d01e09099860300000300c140341581c010b0282890b40702410484095500215003850056086448075070014030315076801070f01c20b0052298a50715015030300c81c1c01c644124441d164956040c85485d41c096503011100c40c070707052000e0300c00700708012403141e090341f02c50340301802203031224a02501e00105c1c00707079614041e0b03022000803c04038005030445c54030241d01420010b48a40c6944444141603a114025008910b001602c28103001c0c0402c103406c500c0c1c0c1880040425103040410300352910307030180c0307500c0e10400001c42c1080d038641d05c0144040b1003d0103c00190201940d1b1000a40650040c0450901190760040042d10702585801c144100800740e42c1c03824 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 503176303 1250 503175053 503175073
    0x7050d05071404080102090a0b1e0f09031c0e0d0b060f040908031512060415091112011b02120f031e010603061a21190f05180d02 57
    0xa8000c19004000c0010054800c91641d08034003038000400c040c0903403500160761180c0510904c11319440643c00003105c002c1c10040c42410b403403003003514800c86101d150001e40e1407214440c910a6030007200d031107507454000e10441c00c1032240541180005809551280a07000050b081049100010300b040540700650f40c13000950745241052204a00180c002d00000c2e4848194541800907041142d41000f410319035607a188103840c0c820701c1c00e0b1000c504400104502e16007961502ca002c1c91a14505a00944561400c0100641d1103d08075026801410f40d140c06040c0b0749502c1e010b0544200c20034508458421024146880405c5070420840c100740120324180e1603405240c0194401886a00300709461100b00d03d9030103c0041240c001c18403580e01140f2a400c000c1110144181c8080c2e20813040001c100450300741444c2d41d0503031280140d483c940c011950319620b0302e0104024040d81c03038000c0c1d0b20380455151403002c80d80c000d50041410304190301c14003000e05227581d5a690402002009640310132142 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 503177553 1250 503176303 503176327
    0x38070b06040c021005010f061e0203041203050f0304030306050a1a0f0306011b0b06040501061e0f0e0d0b100e01030b0f0604090c060c14010b06040b070512031603060e0705 75
    0xa102c1c900051044400c00c82c8808205011600280c000c0d14a120000000f00301d00d0f41d010348000350404100e000d6980c6030221100180d0381c1c0c812441900d5900e1080c40404092500510940c1d036000c0c0310000791903513450585001401444070f070044501c60328001d40c010030f2289003134104090903400c3c00341e0b861616014440c0180303950030040182c2c0c104410000581e9180b1401e05505d00b1592180c40c46640e0360816800304816140c05802480030400e81001414145088007000c4c00081050f0411135541c0c2604001110f02080c10701070982c000c4a07030703100c0000300400102902e20455060b642d03100d440f51501c0d84820f40e01d40038807001d00010085404100301070036030861982c0080c4010800540c004107507075404400200e50740b05101040c07240d41210103001c400c060a01e50903c0b148020070402d1b00ca40000390741e0380518012584242c5000c904c070030070450108440c07058404080c0400d9101d14110307164514040e20350f10150002401c0910014080d111034071281d0180303010b07840b218104090b180c0c2e9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 503178803 1250 503177553 503177561
    0x3020708160c14240702030111030c0a020c090615250308040b0901090b13030e19060212040e0406050c0915031e0f0c090a38070b0604 59
    0x64904440400c41c0401100030740703116507185881110740c2242d251a004060440762401d02009001e0140b01078407160806540310012208036946000c5031300e460190021074010591500d0080c15141d0001c280300000d4420030240402d007200c0e07802c40b4000c001100c1408205607080e01d90070342086502980350340c07034881c500180681d05030b00010707008590190005046841c0d2015402d4000c11b1920b002c0c881031105a0784000e902104080083c0900ca0305503030303801c070b4204008003200b029402c442c119804051290700b00040303000b00144a12520750b42840c0d070300d0485d001482044098451f19030100b180603400300955003190050b051000f001e50303c0780c0740c10001d0300300140700300310b051010482012203035107600300c80140300d0f045c04c0160749a1a00d0032028040a5100d0310040a20b8682c2040014144c004000d441c0e0014a05244544074a603903c042280204c07960800c18551070280c5840710112042181c07150407203007100c4443c501c03035002058884184142da1018081350308140c0012454181600 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 503180053 1250 503178803 503178817
    0x10091401050f0f030106051804181b080105010e1e0f04080a090b130806100b0304020d0c0e0405030309010b0f101d120c03010c0e030703030c020d0836010509010302 72
    0x20142c2c3c90b0500c41c0e10310001c694000d8000202007180071410301541c5130210000d001d11301f01a203040110b0010303c0607130500b031111007000038108205000140216590072181a0042821900034889540c6451000250580456001102900740a0136044210030b8080482c050184084d103914542c541d902c509100ba403200c0b0400703062001c1440c0000780c030301c01a001045804403d10880b8500c034205030420341000b8005d080d00c05000d41c40c5e0701c140704113072070301d0102d030f0700540e0454681c0600c0101d4500300c013500c1100d900840c841001e4001300020700c6000320045200e002c01c003008200e0030f4030178004c020000066100c0f268200a603c280400300c01d015410450304000608600000c0398520030015022043ca26080c00b4941c02440340161581400d0044c910300068509140b03901014000c08a90344800b280310181c10092900d6680041d07454000d0801c91464028003041e903100c050b0048050365407035151a40100401d5004c00e4136030081d002d00f50106002c4140d60b50b0340b415190f013004501030b4111305 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 503181303 1250 503180053 503180077
    0x509160b0f0f030c090a061e120908030c03040c08010c0e090405010b0a08010e06060a0b09090a060e04031e0908031b1912140304021318020a03050105061009140105 72
    0x2d410500d8440c0040c42c0b00341c24108840341c0d180c2c40d48081c8148290b90398001014401740314441000e640158584614082407450580351881c5120744140291041d01c0e0054030800c2c0c00000d00c81c001000304001c6129501620540c01c42c81d03a42e541d51400c031010743d40396500080036146212901d25090580a17007080c0505c0001c00c10112a200060385003403658400c0301b80c1d030b540381c1804407040818040c603540020221380ba15643e034030b02080c03550a0310070241d80c00e1241110070002034031418160f00c0b44003d0602c02841345020310f003900d0b019094420301d040d84040c0c5601d08440d83c030042c0c8913807003900556801c00095410701c403078540d04010400e074080204801380208441d00f0038125071100c281510074080c00507094034081141014144048040d020f80c0110010410040561102d0a1101038400342c4607000074410440300e02c448410303c3c4844000d42c04001c0039400401d11805403c804e0281c1c004440038000a5905032041e00c2c40e82042c8190b014162210600120541c05a000b4118407101e103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 503182553 1250 503181303 503181307
    0x9020a0e0916091e0306150b04030308060f04090f06050702010e03120a0e0304031101050918041401110a0909050903041a04061821031e03060503010509160b0f 70
    0x80300040c0400100700c80c5030303000d0b0010b000860002544100d03804002c00714110745010782e00207890a070000781c0103070101412054a40c40040040c45201144000070030390a400340da2581d032645802000f0080680d42a0b1084021180d02e968500c1c192003500d13101a070107071803250414001d070790b94005050000c10036015075603030b500030000c2810305200a0000344902c0305540b00c0d03850190040c508640b215000080f29a005110510006a40c42c01340c0d0000070007400e140e500c0b040c0901c00240000c2c5ca03c416818070403400c0d01030000300719031900990304040b4444000d000c1c1750640716aa0703016004031061900001c104480801c000c04823903000641004641c4181e9185c5621280c1c1c0b510200301c807080c0811001c2c80060100401c5501035a034821322800e200e03c411010f4506002d503290403440c1000c0c0c04454074180701160405021740d408420401c0d0b140c807034107000b11901202400603c3d5512501d4029420300001400c070030030106406e80c2c42d03001603100c242806d0602c1c92003900b0b070700301e40c00c404040041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 503183803 1250 503182553 503182577
    0x140f150a06110106080706050f1c09050309030609280804030209091b0105040f14010e0406080a1a160c05011416180e070509010e0d0f2a09020a 63
    0x52000210280249441c0c603100c01080c1490070b804c4a103685d0244455402002c028000d05134081d0845900580ca05036007a19206282c9642d4a4000c6130212074400910b0700500c6003c11101001400b08000c0c1103080d0b800558550302e007240c65100030085040c0c0140c49081c41e404164425803c400e80b207014044550500d0344a9012401041003071361884103075445003e95014215030001a0a406502031034401d0910f85440d070501c201942c18002c1c2c4d82c4c6040c01c60304613030407a40b041f000340301c80c40c5006000b44003039590381440c1c03600c0b0103981d01c0581d00e001c18103059110940e02d109000c0d0143e03000c1e482114440204035021541d0342c002d54400c60300380d5203030b138520010380850081d4140200f204181d161003581080704041d000c007041955806009940d00801c00038500b0880c83e00341c0c001c1080c2042580c0e041c4140c01214402a288042d0f0303800300340d0050a0045c0707c641840f940d2128030031950601d285040301e09480444443c0c000b0301c20340d22a019401c1c08540503d030058a0105001d00b440304640403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 503185053 1250 503183803 503183809
    0xf1504021303051b09100501020c010309051c031505031c0305100b04090204050a12050c151209101532060a2d080402101103030702010c0210140f15 65
    0x20841d044d21410390311003600b91805182c99a1030a4001d49080034030001d5500d4480080d49178003054a020f814140d9400d109014000140710343c042d042c040200e40601040340c84405030041c05884c16404039102202000320b03150400103600b0480040381c0380390f008502d400ca00100c01414004045401611074032500042200d83c40021380060900801c0158907542884144401d41c006a0301400c00ca100d80d8000d034001c50350100308140c041030144e0b801055880c038007100491620507444100c1120f64480b041004c83d10f0301140c9291000c01d010b4040c0900720100d4403002030032105000341d14a1402510304200403003054100c502104005223201c5468600880c00185030750400c0300d080010a07030180b8100c1d0b0a62004100070440c050591010360380c240c8000c0010300c001d070300520080c051490340d503004160340c0c09010341030300310785605007201e03a20f2030003140c000e000e041240300d21f40152240410750420045d40303004003240a100f40700d9100f1581d44800180c010064054101409589012008921a1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 503186303 1250 503185053 503185063
    0xe060103080c060a140a0b12030c1b0315070f09050d0305070203010c1418060d0207030c05060c0a1e1206060c03140f0f03041e0c0e0f150402130305 65
    0x54041c0081684480401c10b4660408800070b000011607881c0c400d50b02019401094926000031585c000050b80003010f0005c10362405242c481c440075440049090042c140000802c2d01c15903c03d1035240d031390130050905140e81c503c15000e000300c0f4801000005100b06115031110124640c051500160242c2d8500104040002c0802c050f000508001a420154202400303010818045407900383c1900011014401d954000c01038420200200039450b003103107990f0801540c04402c1c1d109011540d8403002c0c68050400c001c0100700311824000c100006211100c0b49060301c0180c102c0c1e8882d10360034004842149424561100308005204d0020850000740341c2a11503003000d00004e499000d0082c25030b0801070400c0d0f0000c807038581500f03c104607103920320702c1d25030544040001009156499458600c2c0c00c050414100b000c0c1d0404268240040060180980801c0d0032100c81c0080d0b81a25141c0d04251a0f01100c01c8032000121390101c41c40c05011b0038030794000d104119019844022040d2070b81d07101410300c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 503187553 1250 503186303 503186309
    0x1d150402010c0c0e070807020115081207020103060504050c03010f06081e070c0f1223070f0c03050a060623100e041508030316090807030308130827011407060e010e0601 74
    0x5001d00003002031f4250248181100202c041040105403860110707020b649000408400400c01c80c0850328000b164080d4000c50007408005209210b031345030400b035079011500b091003203071a078024030280010003500581500380500c7c41283d600072401040e86c40c098081c540076000d40100414600503002060665100c03054151242c80c0315041c003c080800100300d014035000701c001601000c000b98030190220004c540c40f0540c8203010304052102d03410310000445030703540042d000b4014a0161300070020164010015141001850b4016480c4525040a100f40308580749400000c50a1a284118020001d0040355070000f8004190301141500c0d43c40c6042d0541d1040b40c903640088240240d142d600d03907107035691354100d140201105d440c0024269035100513200c060103226012022942415024420400b1142c1168810b5500d15591369858030000300d07640c0b030003041c0007a20312070400c3c2d41c464514464044c91040c195428840f40e03890703c1009004000040fa60340d0342c0c4000281c4040c1050055a0003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 503188803 1250 503187553 503187557
    0x90a29041511040e01090b0f2107050315180f161e030b07080c0f0409150504020705150916080313050f0f060d091e05010606170c07020406050a091d150402010c0c0e07 73
    0xd48520900c4034502b081d240c100c1480f0750802450741c07401c15812060360354069400318500700c15603003a401d01e90074840104001100e44c01404034040405108203000402c40380c90302c01e0800980e000480541c06a401c5000080030503010002050a036880f441805400c606840f00d01480c2209402c0d00e9072869003d588078449907500c4280f15040d02007100c410f4001000c0956080d0710b4440140c0c2e0740c83e1140700307880080c80c503001c1d210302080300e58404001c0c107018280586c2d42035085603118107103541c0d00d030400107219000141404011070203081c40790b4052700000000c0c00d01d42c280d18022080040a4120803e40702106a4a44441e004140140f201858a200514800b580407110b82012800e6403483e401c8907041c040c22001c0c00700c400e070003441610b5003c0310705c9076800d48408042c80010042c081c142d01190b880220420b02045400c000d40c002400d001821801c400907001060085854841d800e520401c8c410038000000d016500400c011090f030751203280d41d50401da80300d02803445140d10503100400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 503190053 1250 503188803 503188849
    0x20112020d0e0f010b030a020918070308090915031902060702030709050708220f0516090203061008060f04152403060e090a29041511040e01090b0f 65
    0x540e080a102418100f801a00240440a0283c1c0801d6484072004402402201c03501c00081c445100044161346854400f0141d501c00d550301c0c180500c00307400145c12a403003598142c011540c5090024102e08803014050302818581c005e181070300a44611a440030707600b0441c200b00d00d00041e030b0f047c0070081c0506410781c000141800c1c90070f0002c00518006004c2c40701e94200c006508154094506048550b540c000e40080d2070714407d2904508050340841c4100085200c85804140f04105402441c0715000c00d4551099003011f507482103403800c00c1036845942191b02810740c1802030400b5000074041060001c05480031a90f00da40356010b20b88910408801d0141280103007020070f91601621b0004d080000c0f10310202d0800144071919041c00010040010054200c1010a07042c6448402c0125040b01d0404000b071906007030500003440c1c0d21000080d40740c80d08419030701d03030b07450002550b0940740d50218003503050f8204100c1e08020001400421340c080c8a00c042006190781c2e18110400c030180c0001c0c829 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 503191303 1250 503190053 503190071
    0x170a111e010c08250e090a14070302040b0d021602090103030507031b0203061611150103260f09031011070c091e0209150406021b0406050105090409020112020d 70
    0x41c21215032840b20400c000304581440b0700d0a402a420034110310000c4030b10f203c00b0502c88415140e402c240d84040e80c02891031400c001005070958007012100807000e00303000b071a0380c0b4048100c040740b14078010101d41100c20310280805c44000d0f405494040718118902e14200c54a800061040200741c2c4110f001400014014013010b5101d043d5400018a08070403c0703485403d5400a03490303a000904007111186e00040c000d041a02c24180001d01598580689002940c40c81d640003400300240070948680c040c02074800142903803000f103c940c42c03050034182c42c03c00400074103919a0780d100481d202e07030501c1204403400090445104210900c0e03084080c451b0784601601c0c01d1007900445a01001140c2c1c642a0301d00e400600d00d80c800c05e091742c0100d40050f56460f0380d40c0001c0100c088118802510140410040b03002c90b0005501d030040e17040c000ca000d40c071400c5e00c030800c02a00c5c0305019560028070305000314000750400e03412170001c0d5031050401c8100e055061a034441281c010a055204443d00c0b81e80203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 503192553 1250 503191303 503191363
    0x301081b0409030507020904243810051c091406060105031f0f0608060109090603020a090509031b1f1406060304020102100504050c0f0d170a11 63
    0x10381810310191020710885800da10040c2482c0901900a80551503c800180401c015403520b50500c1007104800381010513409100401060040e040605440d107140ba08004c20704013070501100404001108588544074506000903038002010325014041b044c0140c400280c45c00d0551406082c240000090420150400d191030094a100010361034100c0e5007401030990b405000c032580080713a40c140040030000302c02c1140303030696642c1c81281d04d0203a16001048490740807114070b00800e02603071003099854852203148200c4480e48002940001042c104000f412344a070013859003c50050162402c00b01042882444500342c841e00302450b821070388400c40300c3c0300740c80d400007020980d0b08801c010300340c0c43e0015000f076820080c0c182f5200300303804400101168420006c000410304d002c8000e010034282460155035951074110100e119845034414404103083c85041001c005030821401c0151200c010305210700b1340d01c8004c6c41c5c01004803d604030228503504104481c040b50384a039400060040707000e40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 503193803 1250 503192553 503192593
    0x2031918090e070608130602030a02030714030f0112020609280b0f1e0708280f05030a09020a050612040507060e1f02070504050c090102010b0f10080c0c03030108 71
    0x1c1840c540b80280301001280300285401c20b441444c2011985502c0f0b40500051110300400010401c500000030020391004a4000d14003401150711281c034504020912000d041c001112050740090000c40104000b007600c0307481982450002d043e2a05c0c0c5800d000224070307114035400d444034650145611080590b40420389601c000e00300c2e00080d41c14103491340c01042c128805d0007992400c1100d110105c44240f12003800b2920150390042d40c0a50b502c0ba411040a501200000e000383c80c10115031020700154041e00036114450340700d070740e410b1841d5030701500c40009240c8120140c0c1c01480e494404a038079180c40004000740410612039011034034051410302c0ca050000e400c1082040010201c0c884176031640507950f215103034901e11007050700c1c4038124224a080400e500165205081005002c60071000348014601d1010a0380280b0042c4080c0b0180101c0c000203c0300d060f048462410007517101807041d0400c81d005003230303606010b14001152000c5850340e0400e0300a20481d0f0000303080000e0074804025 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 503195053 1250 503193803 503193809
    0x180605091002031e0a02190f090b09100813150b0a0f27140408070219031e0609082107140d02090f04090c180501030506011502031918 59
    0xe525504c1e00a0492416142000800c10805980c5001c20202c00c2150141ca41220b070036a0381500c0032407000001030110380500612008541c020001140b43d08116086511480014010404449407010115032000e0010008031070718045400f80000a1b0540e07061440b030182d21400070070414000b10030880e101c4d0445c0c1c011802040500410001109039001818881000c654640e41242d640460440a41000d00d00c500c1ca16180710304001c00c000720000035100d103078000c3da8120020b441e40c401c42d00e191280350001505c180440802c4207004600080f01c4032507a40700e04000300700c640e190354070030341c0c00d42080c11205aa4620781000100491050b0345442e4040c280d89442032910882000d0040b59118056481d520190001040d00321a10303107034441d1001440260041040175400d00b4400303460070040c0074401c6140c00c036440c1d148983d0b02c03e000e082c1c141e940003c0036259a92a050211000704480000842580014000482c0f100040210003603614101e0b00d898042c0c0d160081c4e6002040140c0e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 503196303 1250 503195053 503195083
    0x40b1009050a0e061c140d02100f0b01140a030b030a150b090c03040602090f12060108010515030c0f2d090c070f0b07140c011401090603030215060418060509 69
    0x1104010503a610390038020103800200090300c0401405040a001381c6e01848141c0c0b0041c42540b8603000e18660000c0c2200f0442c0c0498030410107010712041c8442500c980c103541600086401d4000e000b081412001880029880d060014100e002880441d00b0101c9981c2d05481c0c408203082850400d520500a102c0caa802c12a540310482c504541096450300001d8000340c440c540c04252644030307464640e0750004407403000b822408240008032070159214400d000341c403025400c000c0840d03d88804403010403031b08040200a040d00c14820800c0c0001601100c10301a401041907824501c40c040c5001000d03180101d0342591001110384a041c040c9908014010b050306000403c00500802c0343c06104802003039201d215200b09403074400049881040c1c066511107507000000d0600b200d400154801c0100062030305094455a903200300301e1003112110320015000d41c108100b086541600b000304558491401400002c500da1044500414040302c040c04481c026030796024491015010001c0d154210248 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 503197553 1250 503196303 503196329
    0x302130501060f03020f0d050a020c01060905070c0f0c0b0c03070309080c0f1e0301050c0702041b080711011812020105060f060405010309080c01150312110d0e040b1009050a 76
    0x2ca603000307001940100c69a003c0560104e0350800c4014494111402503c1c112014426030070a0300800d0025070000d5806040da43c600703200000d1004241c01901d10540d01a1034480700b16407070303407110341d40c15400d0b150441c0c005d0010701001c80c0303608641d406042124410801162903a20340c1c03801911031a0070350020030895200000c00310541c2d86151012000500070342c1c409400c0c1050303a00c03095035076848165032035140d403c0400700050181c07014040c0c007810b802124280480d4280512020782100600e50030710004410000203003200780240903042c0e440b0b030004000642c5003002d4001d4108140b404600301c0e210840c1101a241d0710394240241ca030400d100b00d4181c410258038000140407489270303126031410301d5140d0000b04240940d001c283d40c0308041c5240240419a0b20029501804442c1c0c0030071242d03c1c11502d0850500380c4076107c8030000a408034001c1051000080065070340a002c0a0400da10980b10300103280380c0d4039040da507110440181c2c0c81e0340701401d007414108032802210790022400c1c0212 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 503198803 1250 503197553 503197559
    0x512070818072709020301050a0e01061706040f050f0f03120a020c1c120603051608060c030f1306020d0b0f12370f170405010f080702160e010302130501 67
    0x18000c54400b9403041c00f50310801502d95a00311015180c500c0780030354154a001c0411404501ca034110748c501e46400c40007004100c0d11000c000341c80c0810b2208040031940f000000074006003842290350440340c002c0b412141c4506001010b103241454400c882c000c560400b20f000100800001d5029400074480d55041d810110001003103955414810340c0b06181c00082203002d0405070040301084005440e40c0018000280c40f828070940ea1391040010b001d0108400800007111100070072007600074455840201c1c80c40c1c5501110502c0c3d044041c1c510071000c51500300700d0000500602c000c148920343c009000c10340710b10f5038080045a080c0d50f10814040c1d0703120040c0e281000ea006c9030780b002c4000c201c1031100100980da50000c00e03250007034403a0181d42032010f04240622400079400c2500e0351158003405203803201030328011040d000e503101e094045015241d07203010a50003030f540c40307610943c036104a4146a1000c2d2200d212035072141d01206010f590b000c014819070800491310000900d40680511442d49 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 503200053 1250 503198803 503198819
    0x5010f0509090705090a08030c07060c152c1b0a0b0a030f060f0b0d0b0103021905090f10031d03070809012303070801180c0905060901051207081807 65
    0x1181d6058030b8071880240001030440f50084065800410300079200502203510340c6191a9254440c480129061007007510003e540c901ca02e840b1900c240d80990b69446481c1039518940103404c90041c0d42080914046031805500c0700c582092032a40d420708002d100c0d10100760003c2c0192610100b4040c0124204101407241d15444000ca503400c0c43d05240010700208620040e81c002d00654000d003a48083c41e000018660b54460041c0020a505407010060a02c0c1303903005404a1086066030011100c5210303460711070a000f10064020b007039010700340c0510480c01400190f100a0304080a501085d9540c03080c0c1044529080f0150000d040000194500b4071203455030b52540c01410051410041d02400d211140c600c0c41110522011000d00801e442c0c0c24000c40242c019802400342c210400f0021071320780b940100358040c515506c18580c0341c0402641c1000b09001d020340c811303031449050000810070000c60790440b0040b00d01c210000e9652000d079050041814442c181000450100c59104840510400c3c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 503201303 1250 503200053 503200057
    0x50f061c03080c130807080a1505060a060c030c1b06030b040e0601121401050702010b010806011818020708030c091f142a01091101031404060902040e0607030b010905010f05 76
    0x21103103030340113500c0301c942d80c0031800100201e8009040b5401506000200203000041e80b41d00903101d030941d002002e12500440040ba1f200b20b603001c1d0700c84641c98080118a01403100c2405150083c5003503000b0030310310f0300c2d42468044074035803d242e0200c0c40d4208100c025454868110b50700b4045800744150025100c43c96a60f41c81809035466100d41000c80380c0c100140444030000f9024000001d1020f0f117002e0401a000b4a00405d00c40d01181c04100020015840784c003002015850107071900460608000c2c240c1581319007c0e410401941d402c01a01010814200156100d00742024209503101303228014403d06092203003242c20240700c0c241759910843e4100201c0d007407000035042c03010340318080c02c818580f07407440009411420441426083d44028010f400c601119801400301c444a41802e5004500315030300e00a04060102116020a001a00c0c071b810218205000820100d0f00000610003907003880707000c4d108113010035030b601e00f05810355800991580050409080c00060a001924080d02d24 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 503202553 1250 503201303 503201311
    0xb1605160f15110f0703020906101d0111010e0303160509060301090e0a0c0905060a080601060e010507050f010501151101020304030804110a2103111617010f050f061c0308 75
    0x42407602d450b90702203110300c0f140050f055880d81210749003180900ba1948400050000341c4c003881c60781000904504040410100e1228075555200a03040c5444040c9000c980700d651882c1041042c0d1800b443d010000d02440203091b00b540061940d0f42801058203608000b42c400c21000d002d4140050000381d0f544505503030454400b000e001c265000c80c01c4159017000301c00c52000f45030b400c0c030702c501040200c40c507400b4612070b12054820204964a510241c2e070390305001d224240000e50001c2c10007103e548100081c0116500c504100c1d440e0118464526003903403026004a12103091502419441d148d2102e046000d580008008502c0c0d400c158400034051140200080e12040050f507200703015440d100c1c0c8031001024420601c214861101401d4a600c401020054000948850000c0030b001e0020075100700c0002480590611180b5101036440b4005500e0800c4245560ba1010b11310b1002c5140161441001810000e05c0c49140441c1000708a078a8071002e14001c15002e0f6032500001c2d08101d5080d04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 503203803 1250 503202553 503202569
    0xe0f06120406090611040306050a09050316110405010303030b0a15080103021e03070308041a160b060d050f0715051809100909050f060f04050c01180b1605160f 70
    0x4550780d03030905a000d0480260000c10061501c02c0d045110201d8801800070340340702d8034040c00a9141c0420a0003a9540c20102030320b07682040048041300751a00c0006904948070300303044191105650002401c0310000d900941c04070342c440680300c80515091040c40060001d1240903c850950340070010140b920500001b0300450a1031890104c1e108107208054450a00504542083d900c03460a105541c015100c0c010381000b8009144501c100ca820075100140d01d4a4030b00060205180c0364105000006040b403030b005080c1e60350702000310703600b0300450b02650300440052449504c0c2280140384116002c2c4080704100040c0949020001c0001c005540e0030411940c4000a0302d43c0203408543c0300c041e42c00441c00c1850300107100704100c3c010803400f103400440c20545080741e0b81c02c1584c1d03034a40000c03640185984c00040c0e203040c4960041c42344550482d4080e010568098613140806000d6000307080c085502e40f00c03080c2841c1000780400c06144103104614064a04519080304c440d0105098002c0c3d2807 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 503205053 1250 503203803 503203837
    0x7140f0415050708070c05090c040b0909070309020a0915051f0c0c08071e08030408030412080403060914100204050f0d110301060f17070e0a05090109080c07060e0f06 73
    0x80814401c8054950303c54100c8110b503580c07115480c0150a001551180c140109210000192500f0302402650100c13101c1c1d41d6018a030105c06c40820403844801807500040c19954000000580c84000742e00001e40801d810024030182052110740b821801540014481e50028558040c2400f03030042080c55007486007400340c1c41079410728080c2040307401604a51228031600b5000110342d4402c0300d600f10032440c20396100684d180c40d4200180c070b80c402d0b806040c0c2940c0c02008200700d2840c40a07081020740380525481400c0903102c3e80c8100a81d5041103003910403034600003603489032210030700000e245081c001c0781c114030f81480c01010802c801040001c49106070700c184172500a1140c00c0b0800c0e154030700010000c00126465400d2505801d00700c0c0211100d0f100801d00300600c0200c0014050300f544d00c0201500200e545510b0b031003015000040c007070340301c1e55207400e500000980e45401605540c400e10010b010094180032000340fa05509244092081c0c804135080301c8c80e5103a0a00300c030803800340b92400c10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 503206303 1250 503205053 503205089
    0x1b0e0607150e0a0b15040605060a0c15150617090a02030d05070c08100e2503080708130611011413021009080d030f0c0c02010e21060f07140f04 63
    0x1900704181c04902524150f6004104901c2040700c40c04170042440c02c136400c0200c543c0342c1091181d240140b48550001c90740343d007400404a6041c00100070081000c0c10301040700900d9024201506581d5070042000c14800070443c07070600113944034141c0c001e040a004084180325600001c0d0b440d482e194040b03003480030010f014014400501d000724040d015002c1100c0844503020101c4005001d0244400b0b13103400740c445441758030400c580c070044c9822691400c2c40622821904d031741c0030990010300212075444040240141c03401c82051500000c003a02c0d03c441c40c4a05c0c2040f11103080d0f41012100f4005003d040c0d08010201e0340c9110000d0141d41c060755418444005050243e0351500b4580020b19580328281818200603490303003084000c103c000109002d012a09801902d03410305402000340410107000e0a02c85a041803026055500c204d0749038440341000f6505007a080290a54034007031101d50304002c0202e800e0308015020818000450007516005880503c03c0103401103009103001c1001e082400c0c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 503207553 1250 503206303 503206331
    0x303050702030906120105101112130e041a160917192f130915020a05030f0112120f09031e0c0f0609030f0203101b0e060715 55
    0xaa0b40f00207001e025569150b210205018184009100c2e1511800c0d400c000403441e1b80c07040c000902d0b908900e1005101043c103428000b00640c011031300c06403c41c050b00000040f143c1c01c41c1c905500882c0035281c035030900403e00042e80580301c00100240d04c04030710a944d8101985d4003203c100111000c00011b9014048150442400c1c0030980c4d006510401c11030001005210002c1d001c0703044d031040c181700c4072112031145030011a000c15180344d1035442089141a401001072503006150801d124190300e0114141002d072500403600641d5084001400200070441a0028045541d001d00960241c550681b4043d40d20307540c50b0708030030380d80c50200401a095415401e0060b034111000e16400300795443ca83c20b01c86051503070010104800d5070f1111624500184504d0f00641c164144e48060b0380e810521811a02c0d40c0340c0888030004202d03018826840255804201403044085407038081c10088802e0841c240c00408101c000306100344151000c01c00c0c0c1c0c3c00100740c014078656004040c80c0108030000c41c1c1c941 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 503208803 1250 503207553 503207557
    0x1f050930091f2706170405070803030115090f120f06380108010807051519090303080a050c0d090812040303150605030f010e0c130b04151704030305070203 68
    0x400081a0380c1c0d80741e440312640d00b00d0060104039a00f011074400b03480910003541d003200c181d0302c0360402180320031072000790f40000c82c1481544580144d0458541c1991280310303924642c002d81c0616008076a60742c8042c5100c1c0e01146440052a01c01640b4644a060419060031800300140041004e811154100c0410005030410b03201081984007801040314a409405c001d91000c25a03c0c00340c03150080710300d03405d41c006c04016042e21b942000a040b02402e103400c0c4820406042c022121010082c081c1c1180e01d4018120316030240c06958810180502d1460042c00042001d8600000c01d4104800c00c07029103104819500c4800754948040703481202820284c00620803040c0c0030152080711070400007499099044100d03c00717559100685203590b140000c0355103001c140d070010a0ba90041c001040b01001d880712140e08280381e141e8542c545041a0344500710f400d51548010030700440801c0401074400f4055540349090b01c603040c080010500302d114050007040080009003810359520200d1320711442001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 503210053 1250 503208803 503208829
    0xf0702010216030818061606021809010f030212030408100b220506090108010c08041b05060705070e0c030903070b10090e010b030d0f1b051f05093009 66
    0x102c81c1d030316251242040d4155078490030146a590030307081e10f4012075040410481e07450701480100c046400082c1d5440ca40a54000c0c0303a008003220f401c0d00c09800b113558031b0030083d001700030f082d5030b404d000c80c070b94130601140d4200c00e070380b40c1c1c0e06070800c0c0810001080c02180014500110080015400000c500041c2c3e5400119041b036000c04880c00c218081082154410f42c000c1c282180d0b40c4015a03a5100602e00b84e400f00d000d00800111900081000201710307030701d221603000c00c44005040303484d02e038004103100b50072084041d07c81d9403080740300704440188120000d070004c04109141c1e00d585030040303241d9928810800000c0c0f5040031803000030700003051003c102d4007030541403d040c461044041d608034081c0400700c003464400d000e420141001706000700ca04031281d1500c0e80f40e600010b4100d000308022810820401d031024058403050102c0c1c0c070f01a003102d92030602d05090000c0d80303084c1248140c1c50700c044d81001c1c4540703a1030041d4100650340c07511000609019040382d0a82c0e600c1d01c03140030441c070214bd20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 503211303 1250 503210053 503210083
    0x4030507060222080d020a030e04090b16030b0102010908070f05070803030a0207050105010e15060d060b070b04030f11070b090d12020d140f04060f020a120917120f07020102 76
    0x410a141c1070420b280540034816070320403030307402e1150f1a003613140c1e2034068000b40c0c1c40160780704548100019000e016032800c01d0400400028200000d515400d412a1701140c40c6192070340381d41584d60815400d481801201d490a10080004000554442505118981c4090544080e03900810108001000100701503c0350100b926201c0c00d00007030900194003c414212415424040085402c00c0300306c86041c0b0800c040809003161020103000e2206a9101c1040a0789840d11144003240200c860002031034001d1081002c882989018280105a00800755480007001044080c0c42c80f400b000055030000e0302d0012400540c2c03441c0c07100c000784402c000a00c3c020801c0001041e000700d465004120504011704a07140c0204c1c0c034250700c1898110f4414051441d0024106100902030742f44282111482084907004031030a1200603103d443d002c3e45a81404c1c400161042010711018009030100d2498003400d00c0200b011881107050400360340104041ca504206003c2460425a8402c0141c001480404 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 503212553 1250 503211303 503211307
    0x1023c0919150207060503090303010918060c0e040b0d0b0708180f15092b14030916080a02060d1a09070302131d0f0604060512100f0e070e040305070602 67
    0x199500a588882d01400b5805070245140c00141d02d4020400c0301e1003448414041d41c5142c0c24003a01000418002ca05020a00403c5030300600088c2c041c81800a400d160f605c0e2407510240c08000c100a8800880740c550140c2c80035241d92002400594007250005050305000d13140d07644041d8400c4c0c1e81e003c034044103d85442140f80c00d159182c00442c82580c20003d5003e1001d050b5601c01485550780c214041c425000014844011900c00d502c904114120f210f91503c00c6808401802400f42d640080d5540c0c0800d400500d28115840700990141c401040c0000203046900c0a980006505001c0e0001501c0d01c540c9a1080da0416900080c2c6c1d0100000c0040c600412401c101700018000d410007000443c2d4500c0504001c10b0115a1031038041c034410641c00880351a036100d58200716410806000c0a030400e41b900c2000c03a45e50390303400b00c000f01e07541034030020300340e105482005c002540c0e40703016080c0400e85040340c10845a000030a0a0301a20f10400e880075050700d070f6190403203c922840c03902070801e40c40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 503213803 1250 503212553 503212559
    0x311010c05030c0d05030609060d030906030903090504050406020901031505011d041107050703050d140415120c03091b0b031303270806060a060503011e120501023c0919 74
    0x4400954064507080c3c4170100d0350358410051102b41c89011002502207600c4400c104400c034483e800907842203220f858561410340c0d582010406549042d20103c03203070742d004502c001441d41d151150001300d0f80040c0320101143e103088006811760329040c87c0104003118100740784c681c54581d500000302d00c14041072225940c2c0e51a04029403654421b0000300c4e410b02446031056801c0e44603603088a41c000218501c07514082ca4640140c1d1001f00121801d0b09002c00300c588650724099502c691041c1034655117000c07400f0301e203520b4000410056414803034121407508505000043c0c2d440190f07903001a085054010040c228102a0381038506140e82e9030751510010144400c0702e9040b88004101c914003400c1300c0f80385d11480208020b446260084c0d80010718144010083c55040c408040a51041324103240c001a03101c1c20820265400c003182580c07582c0d000070b810310040c801c225030108411210101091200e1006840c002c070003005040260000c1c0c40801c02d50b11590b1a06d81c0408a01061000c201c00301d99 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 503215053 1250 503213803 503213807
    0xb030304330c1104090f0f060606030c020313060302031b07050706140c15100902031006020705060703090303081b03090a1407060c0209070c05030c01051b040311010c05030c0d 77
    0x500c04040090406841c0030400c8450b00514400801c258040000c4810808000034000102001c81d019629035072982d14640100350070300051002c40f03008660100380642044009016650600214001c40d40204443d2a0012065000720155103a81c0b070051303a41d40710204484008281e62071110360815000405000f0003400090840481b0f2503901d401103000c4d621200000c4502401100d070785160806561807480090201455900540d0400d122000c0c90b1207218040498004031500003804204081c00d1000e540c04005250080104591082ca0119241d80080c10310609110040900c0002001718800c2903011400c640d43d0110071820948034944842c03181e91321800303000b06840710050383c1e105050f07044004c6003000c15290789494115040841c3d6003031002c035010041c6644100b108611502c1d00090040c8000c1100d600041300118203410305c2d8a03c0e201041400898100e0302303404110420014141d0090700c03014241c2400c183d6400d2601703090260031441000c02510f0680200d0301c03644001a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 503216303 1250 503215053 503215109
    0x50607050f1b03061006051602040f020703081005030d0c12090b0a020604060b01090506250b010608010815010612020a140c1e1504080f04081603060e0714040b030304 73
    0x40031011207030180c0710105e100b40d824146000e2100000e80810000c2c0c807400020b0070b144184e42c40030704002242c07521120b81d80f04907000901c040300000c401c4000d1240d420b040303100305000303410110081d151022490394050b0450b00300450080c2008480129152100d020f01c15000042c07a0f4000d0303140c7c1d0303a100840000c0d1a580203c5086840601d80805040d195108006070015190054415484c00c10f00d122110002c0310010103031204c003414440c5220000e5180c00c1e00764020400360716408555410120a02d040500309141c805956981030010080150f0002245400d030032820360050fa1032056101c02c40d15a100c444101d041e0300c03000100d04000c80700002da1040104400720900e1035140325051169201e051600c6816003020388a8041070126a81c000180703814201c1c07082d594a803590351618582404250701d0880c40c036007100ca1081040c46082d000c4c052131030300640042d103c4241031010b040040c01c2003209150042c2c1d0f58101108441c4c0b0100100c802404580d11100b6042d0304c1018941040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 503217553 1250 503216303 503216353
    0x61e070c1a07110d0912150f140a05070503040b0601120504140d02030705150c070f0605040210050c0601060e040603150c021908030601030506060d24060e010207050607050f 76
    0x1440443c0d000d40900000c42d040a01c60744070341d03c00480c40d00d880040c2030f91904001050b50640c1c052903209002509074425011102012040400c10401000304081d040f0740003001c00c0c440358141030800062a900400b201d41c015400954810a034032050012036110300790710f207803550440c42d190500c01402100b0f4075070080000c100d401c0361505403a84404036242d00402c540100300754800c43d4031450250000028a601820004690b401d0110076101c031200e442e01e4500995150790750b44180801c0d810b010418540440c0e43d414250701c1c004415000c0d50780c81c0c405210744020004441440c1d4129621500800000c41d007040c100305001030040f07400001170810310b00c95809441200154400d03511640b203100401c0ea00540024215640d00005601070f281c010101399001004020a165403e003034419042582da4000c11704132140394403020009c002e4010780004040c0074401440179100d07a40003400005407103055403425200c082915169180c2131440020000e9800340380a00c1d07044681503101c200034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 503218803 1250 503217553 503217557
    0x809061605070605070b041103031c0b01020106050a18050601031d1b04060602060a0b041404050c040506030f1f09050a080319150b0901120203010b0405030f061e070c1a07 75
    0xb80c0c0c0d900026111407084c440001e000360080d07070004021442140d80e400002c0c001a0544e4075010205807450005120000450000e0b9681c01006249503424464580586015600301060310b04080e514664111b11480d041201c940703440008a150f403280d0801025440080c2802c14003000201c161070f140c900300f0100520211400041d1002c5203014014141190400c0d00903000d29100c2d8901140a00880844c00e9002901d84041c1ea03038185c0100c014070700c501d01590103401c0c1d00b0344240800c800c0d84c0e00602118403c1d44900b00103c002c01001c142e6020714400305800c8644140c1400100c409450a000040c0c601d014040712501407083e5200107610456a0000401007980090300764401c45010801d03041c4d00302d0f021081031001c5031003000101840c0c4014107003400d40b1241130710a03d00380c2e8400d07005011500c4c00072808001078181044400c4420070500b02070005813030302040010340f20071284015180f030a45400400d0300e0074094145642c205802010070341175807054050390001c45109403483d0b00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 503220053 1250 503218803 503218813
    0x507110315100513110405010c0c03080a051903061a07020f031009020907081e06040f060b091008010308030609040c0906030f1a06030d03021305041802040509160b070809061605 78
    0x4d207940940c4250221211a0306680707040c1410305004581280c807420b01290045014000840402e0020001e40b09030511907a8090341d070301400751003003c448401144a018542802c5c0240320381794200c0350b5060081e5121103125240e10b280d0002940d89a8011030f89605401141280c0d24503240a4200c125000e00a448145d810345a051041707909607011a0f0450100c440c9a00810080011042184d0407070801400415084180c0e0120000c59001d0740c00000c01c100c2c0001e00c1c0ca058140020821400b11550401c01120740c03460700c410601e840020049441340380710000107000c000c80c01c506030020300900c3e141046803540300e141a90144142d44002d6944150301c600c1540c10355200c80c002c51250201a001e001c0c034400030081500650003100c3d469001c04400c00011603151910320079204a601060704062000e00c013401400201c50010344081745540000500c0c00c503110301003080d10120b0f007071142c09942d80c0c082820a0b154a0090403002039000310300007440000740c1002100c41d112a800740094070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 503221303 1250 503220053 503220079
    0x109030905062b0e010c0206092a10030603140105010f0b0a0f03091103300a08041103010603020603010306020711060a0c030503060406030503070c0f140105071103151005 75
    0xc0740303014106440ca41c800365040b0700808440c00c800d0058180b00480c034041340d07100b2601c40c3d260030740340561440001070303012904015038440200034080f0010520b2a4400044051880c07003072018078540341d458095000c8110581c1074074400e922030002140c001c402b45401d00303034481c0d100e40645028428181c04441114010800026242c101c80c20a401c903200c80c0b210540000c8190040d100301d41003904d0b005081c0b1001031094a0602100310001000c00300e096000715101c000c00013820703944104240c0c204041c00f6021060350003181701900f090b007102168184410040c002400742c2200d420003074110342c000c0000000c110f1300307070050040d440c80346404801a104c40d0b414000c40703000e03c1c3c42d20800500c020f2100c0c1c0c0030074050700003160098000b0f030003c01c04030344a8403000c0c510752025504403914560b94804000480d01840240007a02ca501a410200030030480000c0c074500a40001a002d4009940c0011865908000300d00035890340d203103010100d00d05000d040e04d04840038440c45001d10b254409071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 503222553 1250 503221303 503221309
    0x2011b0c032109051f1205070504080111090a030b0408071704090f050903160602090d1a070f09090509010213060306050414040f060905190c03020a05090402010903061a0d050109030905 81
    0x50007034130406052040700c040941995000c5125011400e001e110a40c500c03012181c8a80c003403988141c403a51502555149440c09090844546000e0240401b005008075029030359514264011244c025005040507140e03402e10031042c0c0701c0c00c04005c044003002d070804108045204064803c603000e50b141080701c10350500d100401d642c002c82d600ea0307454008000c0491040344550020000074056440141400400c2000c0b83d10001032520990352450002407121680303c100700b52641c0311031545031841d5081350610020704007080328050301c441d403512000081c82d1404250305498080c046110146440e660351036010300200043d000c3c640c0114100452105000303c0c081c1100d01076039105058010000451b240c0714020b18000f88120b40030300a20198a001d0828007061440c0310b07014008038400d2a03d5841000066240750380145d004000350010000940e030031180342d02c112500031402052034983c004945080f80c140726001c0754000100200c0b2824071205600c002480f40c46034403607002c001c0c1c0354410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 503223803 1250 503222553 503222567
    0x601080106021506010503070908030d05010306060f0e0703050c07120f021c0c080904110a03050f070e0d0b100f0f1502010e0709020c0c040e030c010507050a050702011b0c0321 77
    0x718480c04141102046136540f00d0402582d202c0345600c1e012080c10344074204241103902042c0d4220300c4584590050040c06028411f010092422210300c400051501d051b5079040d920082050042c16030300d40c0001c1c80c85000740c003101c0d2100d03400301380c00e120341c02d80d01000fa040800760701e000300051080341400180e02001d8221100741c034640391144031504140341e035140081d80c041007103150055200e00301246d5074020900a007000b018240c501148501d801c0c0000b94171303280020004c000b005214103403500c40342c441e540d117025416004078210341c540c0ea0707403130342d1070751044196015408500000000241d014410001c0f64180d62041880620129000c00101d00365085042100c07056000f0210030410090241e00500c1c504075401e040c2d0381c10410307500001d01102c81960036030b15a078100040102c08008203215159012509003455810059894401052401455002810311541c150355150049540c101001000d40c41002c030724455490746898012501c00c45002c60040b407000405404182c01014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 503225053 1250 503223803 503223823
    0x6050103032c150c101d190b060f040b0907200c090622020a0c1b0b040b160b10051203030601050d05130c1e0f050604170f0604030305060108010602 65
    0x122810f40d5034819a0040550002840c150584140301c80c03200104028010340c2c4141d440c000a04100200141c00142065042d50b00d89100c00e07069840031000031640c5142503000641698984d2a1041070390100300201081020158814000700400c6405c0c0d40c401240420210078142d103011288900c400d865442a2120445522810703031000078285090860140e0100c00050b48080d0840011204041c00c80e0b00010359080000c0c05c1002450a204640c919086002055425005154605104000103008500030043c0390840020108040100f1600740718019402480c460340505040e410090207120340c2c410070740520b074244131008041d10003101f030f01d220b584180c60382403800c0c85d0406107a00400303000348610903011207003071480d012504502907403011780b5070b50310300180b1460029088880c7c041070f07502c1610406640340c0144240d0321070074150ec04541c21000240c0c2141c8400d140030b81003501e83c80303c804452146208000c1815070580141d4081d0000380c070360340b820341d0320782804076241d0480794 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 503226303 1250 503225053 503225059
    0x519060b0421020102241e06010903110d0c0f0e0f010e0402010c0201110616090b07051011120c1305040b0303030711070521010606170708040c0306050103032c 70
    0x200003042150b52518855480c1841481a148281e066654603c6640c00c1724904050740d04240040180341c0021880702c02c4d1100070000c181042d0304e00007000030004101800018146552420a6003c58031501c0c0420512944001c401003110380702d080313000c141303400c40c0301e004241c8500101041c42d0615540c80b080c103030b40d00c2c110485416522500159440165980124100a01c2d906031920707001040c000c13a401a0300c0340c0340d81c402e148404200104070403400e0f000040d186c0c0f0308000c41d00015200040c9041d51890303181d008120b29001c4000700b102409076076401c070440912a800c0140c400d0460008101040c509100e201d04c051b21030f018001143c4250707000c15050707801003001c102440c1c002c0c0850104150032804481e107050301c50700410024074002c142281030541001d69100c1c2e00c2001c3c019000078210364985081c920403150741011141d80040c02d114203016030100810180099140341c030001d190401014081c95940e131400074842e10000007034048069299140081c080c504000c8038164080003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 503227553 1250 503226303 503226329
    0xf0c0210020903070b0a02011b030608031b01020c070305100f201305061809130302060f100306090b070e010e06040504110702090702060907092d090203010519060b04 73
    0x4820118000c2d0700008809602d4440c0c1c49000508501502c001c20003c0070981c0042203140141300b0f0700c10a03031b1400d40c550090508022003844031450000650b00449240700b0458805150011304600921542d07600801901034110040b040c441c00144000e140c8245010401a4103003002504088602400340c800300c484000090b0440a0011800782200d00d40d011440d10100e59500c00041c003da1011086500d03948410010002c185040d45415610034a200065500c1c4001541d0007516080b0051040c0560507032100070425164031091090051a03029400700412a00d90a1980840904807142030005203505c203003401e00e500c03803603041c50007100182c4141d060a080c02d0401003d46072900065028071800c0c4084000340c0e4694801c240501c02c00e40241c5031504002c050f00b41424040c1d006a0b450303500344042c8541c2c0030204207280385142888298030051b120010300c0c500140c06103110180d8198201801d001000d40142003c144074060144200032281c0d841000183c140030718400c0002e64521 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 503228803 1250 503227553 503227573
    0x2090603072006041b09090f021215010b1207021f020309100501092a0518270612010e030d0903110703030309110f0319081308030d0f0c02 61
    0x511000d0446814602807042c1c440198400e1403034448101c03401d49082c40d203050101100c1c42e0480040002c1c1184035000d01c1040ca807a1950b6040240030720b0001d004100100000c402803005000034601880400c00040d01565948083d6205800412108049a180fa400b2804a500025140d08100d041e0000c108450800e500000020740001344160501e004041d0301041201e25882058041d1180500000f62071010600001604240c41d90b0102418401c1c015500c2e6540c2100c2a9003030041c045410069501d01e030700210314440d260a400d450700301407240340200300c0030741c41c3e622030700c99174054841500000619454500380d8007080101d80103a0810010451040303000e811038000c0328041e06000c51000268a5014584107042d8015000240d803040b4000400081e4940d01c02c2c103c4003150400065000c400000303444440328004000c1940d14400070004100542003600c002910780c000d41c2001c40e40d18519035881b64442a01c1703040301c9103083c052000c0d0460300e20811108143d40e50041500b021 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 503230053 1250 503228803 503228807
    0x150103150f0b030a03090816120803040201020a0602030a0b1807121d030c07030302070e0c0307110114090c01120e030307050f0c0303010b09090a050115050f070c03050a150209060307 80
    0xa070040710480e005860310a80030036502c042100025451003683c0e5140e03000d1500c00418141003481c040c02030704a8000400700240100d80d00c5101d50560030400351540da80321440142c5c40c0011600004200074008401c00c880c0040503030103034929000503038002c1390040e059680f040544408540c0034003caa400f051400c1b03c10420b9204c402401070513000d810f064a91a0890f51035500400070500256001000c24000c1581c18009000100041e2400c0c444a0600768070340507190100610300c1080040110648031b08dc1c00035000144840283c03910003841d420000c0e01d42d074071112449859404158440b50503601c94200f4415100703400c0609020714107549030a501229564854000c64110340c000b400041e80d800f90500013140200380460f0040d544411840c241300c04400014690650300349000c0040120b500717501c030100c030306e0001d500e811551407030790b804083e07840d0159090180c0160441c0c100030007007103000620140140e01a031640080e0791038141d00d14042c1c0c8624100395401420070700c040392032a8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 503231303 1250 503230053 503230061
    0x30c06140c180f0d0606030c0f061e020a061d1e0604110d060f14060d030e100c0503031005031c0e2101141006030c0806060d0e061815010315 62
    0x24030042007507003c640c01000260080841000a84000d0b590b0700c400c004211301000c44c0001000c6c3c000640a00a14102c0c0103043c4007207007001022415100808444d149200b4402c151400e1351040c400c008032880c0e4410120123203800007030b4031500e114140b8003e9810340d00c00010205074500500429680d5075a950300f0241608581406400084e000c0e0f0060000300540201000182c2e0402c00040046c07404840801e18180602000d000e030b40c0c446404800710b42d003c442c51050f01402d50707400b03071030700213202d01220065043c00c8003400501011092102c0401040700751821640304074100e880c40c4081c40c4420350b41c2e0305c2c050350400209040340c1c9280d40505040c0654000c440d4030305070f09030403d41500002401c0d22070900600c001601c1d020208000344620001c1400038000c585001c001908001b14043d0502c038002e84194490903001c80e10300342c0c0756510f401042c20807c054054581c90f00f0a80200d40804080403c159100c3c003458101d0080450b807101c40d10304807604460407500d4a142d0b500d92000070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 503232553 1250 503231303 503231347
    0x1903020f161701062102010f0503070c0b06150a0c020f040e0703061e021210060207180f09080408070303080901150308030402030705030118030810080c2b030c06140c 73
    0x1954841a00041d030417950b140c1032010008210000c80e9000b614030004002e03003030030940c032003c0c80411300c207202102d80c0c01441d02102d2680242c42c54019141c40700002c468250480700e07250310640004005010307581c40302c12207090078402e075404541708210300200420f98102e80014400d40c5c1c0804010004504103800a00708003100c2c00560201041401c000b0050703902c000481c2410708001c800740300d000442d1403d032400038007440c8043d1610900f42004a440215001d032460481034403041d9001400301c1e10307440748483d9903102480d00d0750389554402a80d01d610b03480c0b00660220303440d800041c072403800600840c9404940700382150744803400c40d0b8440f409a00040c0090381c0602c1400400b08054400344103024854114880d10040710216160081c00320703a00034011141c000141008205000002482e94403004007155642e9004494100e1420032950200ca0000b44802070a2048249500040034000d01030103500d0078000160415068244aa0250fa40a072154400c0102124001a41491001e5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 503233803 1250 503232553 503232599
    0x6170609010812030a06050d0605070e03010b100c110303130611010b03060703020d0209150d0b06090901062d050406110109030e0f13110a02070f0b0409050a0b031903020f16 76
    0x2058440d0f01089090623036000c11519203035180103022050340c000d40d00050030442100240202f22803140030940c40c500d1492040309001d103221811003005184985041101d8002d4100d075207424a01c05040002d50342842550041100e0346940c003042071040c003800c04000ba000e0000c1642361103800e012030003940b1044600d42c409500380602c1d0940e81c2d44600d15814007411a01c4141c880744d01d106074008942140b07072018032460080042c0f00403900c0c0c1082f00b904541e0281021070000305403400400302c1e000c103500c070b03d0709204001ea04c1300c01c4540c002d005842504c40d0b50381d91f40483c4000c0c0140600700c440c8480c2c0900071070320603005404c480c0341103407041509007406010501c54507595030050044d20011101c02c0311000c00402c16030b0b205076040003038100501080341d4441c401c0780750448103031503441a801820412601c40d8005225640244c0101d482d850b006011581c1c2d8664128a04040ba14180c00480050048007450580680d00003160704901290086500d00145010342c1d50400e84440599106 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 503235053 1250 503233803 503233811
    0xf0717060609130902010e0414040b0603190f0c0b0c060f07091203270b07060209030106120506060a0b2521090e0c031510021606170609010812030a 65
    0x1c143d0303c54010003084002290b4002c91502280e2002520b481c2d144410980a01d2038161504410303860f00d44044e41140e0803001c0b8a05c0c50b1a80e0011a080024500c600c4001004441c0700000b005800500b011031980203101840c806616108080754038818480f401645078413160218441c058031400d050b40000c52403e0000005582e070004581c4100340b4101503002c203000c0348803840c250644041d003949000b000080e00d8080c5041c09407000b1540131700310020740b80590104000d609610254002000b900c083c10b40300c0031040341c43c03130141c3e0340e402e046900c03a000300301c1080000343c402c85000c1a02c0c150354840da001e8650420b1840900d40500c502941940c0340c01c503c29980d007030310340c12552007580070600d0380d20070951505042183c84020390140407200707500300c200208005c91124612010320244201e480c0803034900813840c101e140200c01c1c0c54003003420604080c0041d890f90041110380140c064060224807550f1030008020409030709114055858006102c00664004400025507201c2c0d41144001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 503236303 1250 503235053 503235067
    0x708151009060221040303140909101d100501050a090b0d0b0102071202063a0e010c0905030606090c0f131716030b0c0403020310090b0f07170606 64
    0x24410301904580e260200d401c900c014020140e052103407001c0400220031181080804c000540102c1c41244406010068002c41c0301500d180004111001c999000b0215103090038401d29000000305544983c0302c0410100060054403082d0100d1140314107038001d0030a0072203151000540340740d48401d440300e0801280b06008142905198082c200e03a030519140002d11518420019140000301e40041480c0c0a46003070110041c0c0d00c0e00100e41b01d01c002d240e05144141c0d03140d42c04800c5800c0b0650880c1d04003442e10541142030446610440c419140407000b4081c602d0107400a0b01c151100b800781c203070540c0061f000240c0c3e5081000d010760b0400120710900d450036086000c6c0d0001500030007140004000c0351a030070807214104003401581c140c611400b0308060030102030040001a00d07444020502120000004c103050111010b03a0002c40e0090b013a60b18900c10754403680d00a00402c4803c44003010040c0202d6900c0802101d20f9100364980d84446105104100d50880c01501c0204000e031300c0700c400c101079 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 503237410 1107 503236303 503236309
    0x305060a09020f04290d051203070e030d080103020406150206150604050402181e0120160801090b09030a050409151d010614030f070815 60
    0xc1c400d0100c0c40400c0c0803402d48a00e060b40186881c0300070b400e0300700c0504058031888000741c661604a04400c104903480c20000009030165100f51003a040c141061802503810482d2402d1103c12500d43c800000c1c5807035222100140002e80e802c2c01041181400d000b048042c20007100075500712841d20341e009503034184c010903424808940000700301403070300e034036049401800028200303540d2188000e8060b07010341481c40741c950042501180b14091202051014030007211b0503598204141c1a1712003100c140200e5035003401084c02151024001110301032050801401901c002241107c03803800c200d40c030020004c0048800c0c0e00104445040d10b50b0213412107090b91280c00c80020a042c0d403460312681d034940c9370032800c070704003982240b124491811484031b412194648d481c40718882960300e00381c0ca00d01007a80e06100d074010441c003152201d4001d10a16030b1040318009a00c060180d4a400 = true := by decide +kernel

theorem cover : BRFrame.Cov 503057553 503237410 := by
  have h0 := BRFrame.cov_init 503057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 503057553 ≤ n) (h2 : n < 503237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
