-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5056
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:35:56.606008+00:00
-- url     : https://prove2.me/submissions/1129668b-e267-416c-acdb-c08de9324185

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 909172661 ≤ n < 909352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 909173911 1250 909172661 909172669
    0x718090c031e081b0c090910180506070e0411160b0a061214120403050c010f030609111801180e0402130203090303041a0106090603050c0c07080a0c08030304030e 71
    0x9900c01c00070302e44152119103903590042076600120b01c108180603403000b030300b54034802000100000310041d0340c0070110741400a40995512000d0908015007a20b4182d95940404841d042035129034104080712078034140100003402c000c0528100900940c100311144142180c404121851074900b5094602c01540f55298191608009050800600d8848500090548600d041074039414098450a0b4040981320b0195183c4841820b609001e580c040c07000700302240d004201110000001c3c02c02c3d6a1010310140124008d1106410689c042480e00c00052140e04030729001d001d81002c09641c8a00c0c6020100c011344071034613109130800201407042c0d01444040080c45906400a10103041e0a04003000300e180c040503078200b241c1c284820361001c4100001e1240007006c00c8003c0c5481007001c601c80d410050001c1c504005d600a0380c09044e15007010511a8251b0701c00c5820041c04001034031400c03921004c2c65501c69000c0c0380b050f100440c1d90700e400320300440c3c0801200d0040e035054640b2601031400320148 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 909175161 1250 909173911 909173933
    0x9150c180b0c1002072a030b2e260f19051c0f03150503060a0c050c150103030f030b030d120b100908150405060a0e1e0718090c03 57
    0x180c0c2c0101043d104200020340081c082c050720800b504144110840028010b03015a5401100035070500c2d10208041100c50b030f102c9030000c00c054850842004055640c0c01040d003582201c1c07200c1d4010403800121501c85900c44070854075160401340c25901680b100d10b9648604540001e0b07a50000700a110079841c0072052510054859401d544001d0078400b110002c400c0e408914901158035002d10312002a0b1610512120303c12064042008a003440f010139a0352710020b00340307620035a4038a030300300e1824060720588000c0342c214021665120402d148410180900b8401100414032400d00c5000c628020302444c0d8038088003070000c01e0018400342c0100c070340003070001005d24010b50304d6085150689404044020554075a2100f2a0b5945000c20389890140b04144080c0740618030001e0100040c4041005030704040345400105c0e030b119510050508045401110031380c2007202d000c140804040c003242c28000c54006018141402d41502d401805464414a0092901588001c1400011818825 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 909176411 1250 909175161 909175177
    0x60b03042d060f0506090601031514060912010b01020f03070f030e0402040b0d05010302010e1008010302060310081506030d1b0b0403110a0c03171c020304080d09150c180b 75
    0x960201c440541d12040c046601e41800c0d15421a1520104051410104c03242c1d50031070384c00e10302002829030074051f01070120028042c10407241c3c120031003c21a503454200b528071100e00141011703060f01c8600c02c018001c02c41c82e484140035004801d00b00355100d8001c410b40706400d4000b0110f241d02c0c405d96500311100e9440300e0319079600550030700001ca011540d44000d003003123000c00000040c455041d800050034001ca84034800b4800c41861003552a0a40c0c0203196a044a6040c3e8015807251103160858000586c82d80104500c0d2044056514220740d0070905c0500540c0154142d030075842d041c1e801203911015a00800303050f00d100644c0c0100080844110b103500502a26094400001000985081602c1c004040d102494210810700c01e00c250716846a42e8000f020040b945401060410840c4c0d0041c0c40d03110042095020002800f8000690f088454494035a0346c10400749030545848240c0310043d240c0b21214600c1c140c0c05410160080c906882e242c6403006880301828a084444801075100c00a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 909177661 1250 909176411 909176483
    0xa15090c0302190215090708102003160801050a05060703050a020a1b09060b2b060503032b05010b0d0e0106080616020d050301060e09040201180e0a060b0304 69
    0x1010302000c2c20a2006030b101e102459000c0c01c070b0440031744008000110041c102400942008204100844002600883c111780c1001c001c6441154000d150141065030442002014000800c000300207001e00d4840c2caa6000381e4940380103076600e074014818480c0e840c1c0502030704a4030400002c1c0c0468010805011602141e03c11101190201d40d01d84d20014404040c0100c2140b00420502140d90300d03005643c003900060411a050988100c84d420f102c95240c040701200401c141c040158248440c1c1107030001c0c3c400a0100ca0384c03a04507202c201041d2005c5401111807040011003261001c50a0140d00d04032a0904101820316000c40c1c1c4550051100c4a403040e07441d07681c0c00d03000581d80b0040c01218450415601d29884480e41c580c0044d00300882841c8060800100f00f0043c0100354104c1070621047c0300a41d0551a20707039481c03005803255014003c486c0c29140b034289000502c130036103c841c60301c00c40f0b00c1c10702404255604d25100145000c25640104407000b8070b841c419241b41003400c006c10041e05aa = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 909178911 1250 909177661 909177667
    0x607050a050d02092103190c02031b0111010c050310060c02220b0a0806040615150c08220305012702060708041d0105090610051e0d060b070b0a15090c0302 68
    0x2680150314000322521445c3c150408030b20b091411410802c0301e8100305041c104540240c900d98000303911500d100b0019030400d0605d440041103a44501072104140240300020010310081c0c0901801c81d4004035041682001a00b001046403403083c11034500c5154081c058601d400282c0130362102c9010140144042580d0310042018542c4c3e500181100500515026054600b03182c1442c030159081c1a480d103d4401004808009503403c0150040c0a1106840e21514188440c5030080552081104070700d881409181d80b02000d41d220b031a500c1c200c9200d40c000b00002d80203801e0401e025444041c40b9080f000c0e0540198001d800d1060090003800c0c81070b54030f9440c064840c1c0003c141c0d01044140b807600d003a00c1c6070041c01a82000b51031103030008000c542d008501c0314180c60042c45482500d181100200003c824811051040c60135641c80b0f5909072400c1c403400c0c0c1c4070000401c440d004403c2c140c61801e80c84001c5070507000076200c9c811581d020031030b600c0300340c034100130001c07024003001c0381e03480e080550070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 909180161 1250 909178911 909178939
    0xc2111030406090315050606030c0a02101d21250b01030b01080f0303010e0402060904062606150a0e2a070201020c011e030b12070905090607050a050d0209 68
    0x180000c002408690f11001d40707050850525925000c0c1c0c62001950161808050040c2a5150003d903540042e00c002c255645150b002412414180d001c003d00c48000d0400340b909a0801502000342c083c240651b0480c0c551084841741d660201c101d100800108550030412031540b890324a942c0b40c0c00c802c100702c0e20510850147e0b604800c100c402d0b0710546004040e0801401802c0051180c0c14a08032104002c50865043c40c07041031440c030000d88003d1040100080c400785a0301c5940250b00180041403001c240c0c40000f41d41c281c070f8074001802d10110783c011a00050581e803008440c0c0e0040301c9024000c00758003170500c4124880c885002c0d0046c18a018180303014445046051581d030380240310304c08036030381b070310428400a440e020400107014144186070540d0007640800302c11011504540e40f901240420007000407079060b103101c3c2d482450705d0007480c0020030381c404c05400460203101100704684071a601e01e401180d1502a029240002801c02c00100001a00a401801103030500a000c010f0660700 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 909181411 1250 909180161 909180163
    0x50106091e030c060c1a04080a0809011e0507020c0102160329130c140108150604081b0a080d0203041a0d0f0c02010506040b030a0210030213090603020a060c2111 71
    0x3e5078080c00005409044034410044030070a203003601e00700d41454035000d0030070350b4503a01d090051040d03001c00c00810340000b0f003c85030250403424120b000101711350880c1c0701c9058600003503c0115803072005441103801c00302c919480060041d070701c00e01440005403154211368401501588507012040300b100d080b101d10740a1015401a58054a91410028140c2c11745180101380500745a00594004601100135400341e40c2110b01c1c56400141e07219004410100c000000d41c035070107542c0002205100f44500c1d0500040d0002d0081d401030800c440969103160345100c0d1039a180034030040180160000d0104010329004d1038003540e06060003c40382410b00c2d1191155200303c0d66001200700d0303003076100d110100880381c0a1041d01d401440640b410301c80b40e81c03102d0200765221001c02c0001d00903400356402c9601c003403003941511600001c07001c0c80c051140c2d5801d12800601110302003640303d068100d000165040c06490070001d0154048040540f181c080c100403005840d05444c0300c1d080c88940c211100e48180c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 909182661 1250 909181411 909181433
    0x1f0e090f0615040b03130606080a0b09060112020d030c111002010c080a0605030307020f0a030b0414070b190c0314030106050d15060c080a051201030c0509060301050106091e03 77
    0x5815410022841c14030100a030291501d49a001c0b000750070001031180c0703201d00044030fa0010a40107220300c410580d1502000030041c513845040304e8043c50101d0f1040241005060740a007681e101182c1059886041c540844250f0150007035121200c0102100004c0c0191300755008140a81d0b0010b00520866002c40c400900b903001c00310060b5901c145902480343c111076132a0f0458503081080003110b060a01003952032041480c0a48140c3d1106401300c8150b54003488000559030200d82c81285043c40e140000a5184618025039a40940300e004248141000c042c2e400c031240c10295040b56000070203080d162540e039640190304001c0000c81d444004000031008500902d05540c070150303990450f550390740481e400d41020026a261a8100308403007640008409500c41c2c00c2600e0b0341da5904d2843c0169980c1c070a4610840c100e403600c900000901005801c807804072101a51488011f0b6640800c040c2203031401d001d2207000c502031a000b480ba8141d00220381aa20b41c004c07080950203601c984404100d04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 909183911 1250 909182661 909182671
    0x3091f1506050a0f1706010c06020d090821280f141b0c100c02030c0106060f0e0603060a060509032b0207050a06090e0a0f02031e090a021f0e09 63
    0x7880010f080096550f000c00c8007081111a85002070361582c440040001c00d460150505041200d400400c000f0301030190304071010141c01040403c9101c805152405880e00200001585000504140004801c407881c000d80700341c1081c0c401103422141c80d148d910300d078a940341c2030341b5510350741d085400d10030702040c455400440508002c0c4096480d040003000d003052041403e02d54400400c0c419205031110004110381040407842c00800c1d201c00c0c106040740b542c05500c0704021150700b4150300080d003e800044600101465945450000f600202401024442a244c464120069074410010329104902502200e540141600c074010103c0702d488042c9040c007400e2060b1200d903d40d001004a80401003040148800d50320205040c1c47c269002d04158002c3c4a51402c058041c00010100ba800340c0c080c0c48100d890f60030442d224280b405840da07000310044c201050f0326066502088800c0d00010b0a694026802410102154800c000d401442801002c0600c140030380d03100c24040035624985514411 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 909185161 1250 909183911 909183917
    0x306060f0f130f08010b010c020f18130b06060702240f0c0f0606010305040b043302090108090309101211031e0604050403080114010c051204050109080303091f1506 72
    0x200d030401000c07080f02580c6500001260380350010030101039810504541e0712980466040c91300700186801300d040c80541280300c0303240a5a584c05c00005080c4104800c40150103600d91002c50340e901e000b845a90310a102c03020794002500058800044502410a21007051082d034071401c00a042801c500140c10500049105030046100c03035119140c02c0000c1a80040240b03402d2001e8200f503107a55500c034901a20151032810a48508904210107558000d500030710601046051030b10141490001e410644030359000828107400724203a80f00000654034590b400401c07806000201c6001078404041c03a00d05000025101c454452050102c440030354031a100200141403c4030340b60b004500c4009004100902c254540300c140000300342d00602c0c280c1511a000001140003000f071006a07441c800d1503000030b14500c100036010425400500c0500200e40c000e0b03c2d034040722605d8240aa449000841780c3d6110f030381c040c50f2060013680495410400d100e004600c0002d224252600d5010012500e42240003c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 909186411 1250 909185161 909185197
    0x220e060c0711190b070f0b0705041e05130c0c02060a050c16080318030a12021b0105071a1806010303090311030604020916020f0601030b0405061b0306060f0f 69
    0x14046a0b4010b0318400c44116040d60502c03050301500200140c0314024414001008240780f401c002c0641a020310450b003011036503a851500c2900108940c1c0540a0412040c1e1081c1e9088a5104400c15800540d10f000301140c06501e05204110000c0c5041c509410070070905400314400340e11850001c1c601184d00d90f469075991118450365603e000c0940c000800781c0050b001040180c80c03400300503200200c021240840e02660310000080c500881100d02a06141c0c1c1d9201100308260002400c1003081031442c10050f10b01203200065801c3e02604102070010100c808091081d0245d0f07001f829404140c2890110700300003242c8110b841c1410980085000c1240300303005009008504c1c40e0300101400450003094a031405a0210f54241c80c050b248070b42c80c001c48001c01c00510b000b8420b00103924402d03401c44503290781d6420031640d020780c1650705485500920001c161114009861038450450342030446146480c1c95051000c5a8850000045040c10030b005075450b417000d09004250241c0c0c03660400b80 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 909187661 1250 909186411 909186413
    0x230406090b0702030406020d0e0109172b170601050c070e0a36080c2e0204120f1b080d030b0405060f090405010209040203070f03050114220e060c07 65
    0x14914400b0340000c0656206001c1042043e44c0001c0c040070303500311440c00501540803200160740d0341d02c2c60f400c41d40b480340d030f80021010941e9000801c100e51642644506400800350843e030f05850514002c910000349001d1020034440c0401800141c20400c180740040c68030041da1882400c19005030000741113000d041043c4058145140190300c440544a9034005108440e0303c0c4021002d96141c0c1d040c0307940188201004180320000090325481002281658846030009640d00c1f21649240301d40708070b440160390340c802000998400d5900740c4074410101d0004030301035101c0003003036806100200c414031020101b10300c00d40d0354038403c08010006180203080d2250704c100081c041d1864290114002d500e0a0b0410550f5580c5182000701044d0075200448982c46504000703000e0310541c0216074100d80004140410715520410520303040d161641c08006ca030340c0781c5100070781d840d00c100590f07a4059920006010141801003064441e0f00d207100c000202c4d5180f403440715040100c211048031019101040801c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 909188911 1250 909187661 909187673
    0x140c0a051f060b03060904030f0210020415170f010515090307060f120e2107050a1a0108070e04030f050702040507021f060f030807023d02061923040609 67
    0x2c0c1443c00c0c40d403400c5180000210701d0307400d0014409810402241c002d208140e0085c072818500c10010201999601d80701c490211408074195900000a007450a00b580d02100300b03c100780c0905044002c010b01c0344d107443c003044440c040700d4030200315810007080150742980d000c21230702000340015254200c2c584596800a03240039000f202d10f02c0700904181101d0781417040480c0c02640c82ca42030341507994112281039000281c2c0a4554018001e2050850a03403d01042d40d001402510494403413817000da0326128015154001c6118a86882000305e012400081c0500d0681040340551324000741801020340005003a80c006990a0000d03800028403d240c7e0100e07402c21b010089915001071000a16080e0b0742403105405100160460401040b00380455884412841c4412085034807507032404051b080c24290b9817030040c000982c160b2001c8503003400714000f140707d034070a411140400d500401c0043c440c1c009400e100c40d43c507030050741d00856208a0303001d01c02c80d1070180f802042d0000d52500146880 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 909190161 1250 909188911 909188921
    0xf05040507020d0e090c0d021b07081606080705090d0308093a09031506230108070c06150b0d0506150d02180405070e030c0103050106140c0a051f 64
    0x1150003540e01001c105802103003a81003c07000b0798034250b00c1d0791406e03000c018500a442c074144c2c05034000030780800040b90200700d9591425109064900803136036003030165542c448131138035070b091f00c06142c004109040c052000e184e4403290342d0804034503000070700c80052404d0383c2454080340440c00034000c1c8840020200030100f0030702d94011401400e04501c00401d0030b8450302d098084019000c19014600340c0d80b01c1d80c0c80d100103546c004481c451b20b00054030070340058415402002070b00c50441820308000380d0410803100b02d426041c1c441c41060380b03800108442203403e08100b510050384420340c8000300ca0f22204032500402109407126107550146050f1002d5660144c01544070306800b2504030f190440600c1116586400c15100503030320445041030903001c0d4426412294414074140400c10762642100750404811002c0f02603491035420702d0015000c880082c02140005500c003030744580e009803148006c2c60312180980485d080c5a099075038461900c4200d01c4001013800c0d0400102c01300c50814002c03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 909191411 1250 909190161 909190171
    0x90507020705041e02160c120515011401050a090509090706110c090609040609050a1202010516050a1d0d0c030b01081b010518030601030819020313030f0213060f050405 74
    0x84c04005018400e00c01038600c60030840c1d00c4503078000349400b83e4094050708903165542c08641804403980e035010000580d07841250070b0b102d80c011900480c409a0391404094142c0da006280a0400d031035000c01162150440329620b004e000340002c010500f50740d030b203010b00d1041ea006030003050040e050410017441d144420059100c15071001c0e0001d6603036596940c0d1030b6480b660a0350720000c55502c50500340003910700c600d0081c1583c000c0480e854248403124480340c0117060560024800c58403403000200440080480400014109102c0c0110952180c18015a0056a03540841000c3c211030000f4130f00f115000d000b21134558601c2c0003001005281e040990040015401620f402c10b22000c2d880003a02c0c1240c1c40703504008001502c0c5280d49091108007101c040f029044035990341e10307840e0041075a444518840701e600080ca0280503514400012030315280e9140031900300a92543e51118030401d41910b0480c0c0c4460541d44c00b4864602d14440c1030002c18004a100c0c2d030403403614042c0b200b21000540 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 909192661 1250 909191411 909191419
    0x414060c100c090308040e06010e100804030f0903061e0b0a15030b1305091f0b21010617030715180b060402040512030702120312190b0604090507020705 67
    0x210020800c0c1000c154091241290310011900b03000c02881120051140c1e0001400304101040220701c0c005850f0f40c13107102e641d0070f03243d00403002e007100c00704030404403a040c80d0400160003400190003e0311420300441405000e013442c2c12110740b6030b039420058404907081928190508107580007000e1460141c020010010740788030580b903042c01405500c1a18054101c01416168041d444041d01c50340390012541003101e204110a0074070340c00594803180914104145012440310b1101140c030b01d4460b5540c080700003420540c401c031079403040700c088000800042880d550b0700c803400600e8501da4440d107888064010003039543ca1580d840c00c52011621020071703081c054645941c2116a400860805000355007003c100c10b1150b5501000501034852134201540094202140313000c0c0c0c060000107495045d1003140e03840022552001201c0e03503800351040e00703950911041c1c04568021050100c100d0440409079021030300303507000400300c0e40e9944103034004c94a46954504001117a9410301c15030f405414219 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 909193911 1250 909192661 909192667
    0x1b0b04110103020304172209140105040e030703030b0a081501080607081501120b0301060909110f03190c050307061e0e030d1101140405150c0901091a1e041406 70
    0x2496810045198004580c1d02e03610018046950302005819202c03460031003004551030907110307000000074080274030340d40d10840c4818001140c1351401e401000d1100c603201000b981040d81039141240079200701c0c042c50f034118032018804103641c1000e1201000d541c2d0f015840c088554500181c5c9841c0800003011001000319010510801001d4a01d40c400c1d030385d40900c1c0c00541040c400c00340c0401005c4181c880780c0d040d860b10f040081c40f520903030494500d032800703050b8081c2c0980181d024000d145404c2820268503030011070900740306120100f0b454298a0003071280c0c0308255114004070b0710307003059508031801040d15011041118482d070701e5107010703450300341c94040c90000401e004240d403402032546180502090001c1251810b90035440a102903030400801c142908080c1071654550f90050100c0d43c0254010002407010503400048840011069580c40002751811300800303001080005c2c2580403200c1084030344003096010300044802d11038440c6d995030729854030b40449c100d1040f002e1018000d490034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 909195161 1250 909193911 909193913
    0x412110d1d122a010e09040b0c070f1a010602010b100f02010e060a14010e010f030204050a1b0314010816090506040e03040e07080a0524011b0b04110103020304 70
    0x40d21001000c02910049820701c000504071154600d05100d1034414900300750f00100088041c900758800151040c002d09000c030300116020301c408500036803c00340400201c4c0001708407a40d9aa0303c8088200080c0c205000e555610460510420007a105811140892000c04030410503003401045140001c02045030540f004c81c54614101e071422040c440701c2c2141c407058900070340044002a80800583d030881ca0b101041b0740013483c07102d80740c602074034075500040b80301100080c500d03040c0c0b00031400c0c40c00058615805c10002d0000280b403960b1003522160303a105110b20084a114a00b602d035140401c1d8205140c21a91008005902c022400d61002c80c0551001c201540c0070010f48a000b0030126203540c1d5400454090050340490511307510000a000070004580403401c0c0c003458040d600c84400c2d03203500e41000c0c29694250741d1441c0e00004110340320b4030710b9201c4140280e07110043c1400980c10100c2e40b41480c440300b07090f0090b194006601e0801c020045a450012281042424110f00f54201 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 909196411 1250 909195161 909195167
    0x606070b130309050a0f03050120031308120c07150b210c09010305100e010218010c0204060308030a140f070c0f080c01050a02040503061311010c0212060412110d 71
    0x740030701d006075812070380000034584a040c01c80090130000d0b02c0701d0b4209030380e00105960718049200650302c6501e80320311030102c44900d510550b040c00d9000d00c03040c00c680f1101d0401b0b80070100108102c5d8845000c1203a90081d000040400f0312a56106c80384685450326402c02e46038070840e244820340c3c000e103446130801c5140c0d0380c056080a482c818441e241840803d0b00d00784d61034407140c0c444903648500144000410000c0c002084500c0c0e42680030244060115003407440e0a138018091600c0c0a140701405864182d403150b180d09441d64001040445d84a9407501c4426480d8015220007070361a0300c650440c100b9100d0080056003005240196245d68900a00000c12440340780c64002d081c0e649000c0044180213080c01610440c4107408001c0202d0704044600710020f6125104050003401144001140c0d0401d481d010078640340c000304807078558150000110b03000012494101d038003440e144200b051130705003046a14851071248000c010702c0d03030b882440500401840746024601ba0b020502d1a540a54 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 909197661 1250 909196411 909196433
    0x140109081806070b0103060b10030908070f0515042607020906091b03091c30061707050f24070f06020304030801050111070e011206110d050f060607 65
    0x35010101c6401224080005030b16109030000500140000400441840311591056220540407a60790508a0b48440c0543c162030084901038483d000c00c4c07009502180c10842e41d01c007594415800d4030f1050702c420380c103002035440542c0e0950f090280d810080d031146180c0079180c0306002010312170300d00f4484030344d000035109c01008003c40c0c01104903c0124000c102400801c485510f11281001d8880ca4800c28081d80c82440004074000d8141a00c01d16110500540a0144142601100109281c00440482048004a01d883d40c039236986a90000d0b03011810007a194803a04890050710103030b8075190401c13514012410001d4495000b600c141210b10402c0c0110302008a03240004c66100c0c21a0b0514004d2005426030140c02c81c0c0c00002088101a8050011816280e007620b5208080c01280320141d5681200d01803076103800b003140d0062125001045001d000d01740302d824007107070001103114056025002031b990919820f48802c00c0c071107406c1402c003e141d80988140c607082d09201d041d86441c60101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 909198911 1250 909197661 909197677
    0x21002040803090f0301020f180307090c05070303200409060f08030306010f110a0816060507050f073005041403150a0c03091e021813021908010c090314010908 70
    0x511060074013800c1d40302901036403c80260400380c241c07906007950090030700030702040741c02d13120380640c580c045400d601c1485031103407045050b07907038904000941d40d081c0c004007c0603840301d80b0301d5020f90b42000c1c074170040e400500c0942554500415900d181001280c094040c5400c203c840350002c2c410005144d81c0013480c0b0001d44400d1800d41288080004450308088080801403e842c000092029008215a420410140c800c41d001c1107a55140201194503000355004100c00b041d00b080b006000c24103541624015440500131b0f811503034450001c0c24060807140c4c032048003148003c101000040c2504280c82d03006181034003e401c1d050059250480450001000d045841c0d030b0350f220986183e88240d00c000204c3e0303407101e10aa04185524003c0100c0c0954050403031207a403005d460300e1225201c2548190003180150305840c13500c0b2081d4208600c001e15180391814038100100c00042a0009000d10801800309032071310602c507815801d041c8240c5840c010881c2003030b0b051401c80e030006004201194100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 909200161 1250 909198911 909198919
    0xe060a1e05091218040606050a0e0406050105030c091201020a030e0d02030f03010b03070e10020304151103071106280e030109150c03380d0308060103110706051602100204080309 78
    0x700384c044088600d1103440c50f9410b8100c0c1c0b034910045480c680000040c810202d007502c441c0f004a100d401040260b13005070146070300180e803e00200d600485150081d18160000524001c800301600204a0890b084150303c0d8000a031a0310524403040d44c2801410301405140c409103107807060103020b1110902c4180300f40c98103044000300181c150b070b100e00c6000504071001003011880342c02400c03009540b500300b4040c0b030205041840002a61a006031100cac2c070030310a02d001950030a48242c0301d005040ba0643c0071181c11143c10460a110f40600ca11005010b9034000c049000881d0311501c014464030116560383c3c081c0c1c0c5488101d00c01f1402d440c014004c002005003010402c2400c241c001c0f800b44c00d072500d10144030821652149803036a4161740c09400200d107441c003d50080100010400f0180090038041c012500314400329809510a07040800c5144d070307100da4646020311968403941201d204840d00c60120480303070b00042280760305010701502200052001c2d03007007600300840b0640340d100d521481881 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 909201411 1250 909200161 909200167
    0x501140105191d061c050d0917120c0c1206010303021212040f05191a070509060d20211503120717270105070b15040e060a1e050912 58
    0x40c9a1755006201401d000949095281c110246465a580c119900c000c030081640042c0104591642841c0d40c00601240b100030a40b006a4003842c10301c9070b2005903c1c0d2114050b602441c42141c41c0d2100d21840c0c080b405004185945c51420000d082038500140c1040346e036010054006a4903843c0389154015030086003d003e10403651038140d280120800c01b0815000444030030400744008144a4904940308010518003540d8200c0b00b01c0b03203032041c1c0311050b0340042c0910401c6000b9115a00800101d2076910720340300404440901043d10743c01600907050115400e507224091151504110f0390011000f2600c00384408414000a84515690748200c071010400700f403000c10700002c0d01c0c1140842c0410315185590b2031030070489040400700d94900d0407a072600c5500e5428254461000c80300140d80084003042d071030f150040946042d01e0004a4154080d03101e8043d8060b04509200180c080c0316001c0d000600c24011440070010007140f0200440428584802c0000f200310103d00b500401d03c240031281c1c0e03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 909202661 1250 909201411 909201421
    0x14070509042a0201230c1209030c030409020a030b240a05070803070c03020715120c030b15040609080105041a0c12010e01050901141509030a0501140105191d 69
    0x401c244446000746141240d0529019180d5011762119014610070385038100240300c0f16400003100c0909440c2d06440a03410020300192a41da0111107401c2100282a03d1403e2403007030b41c2601c0e54102d034000c4850b5a90008461010b541c042c812a9010301058500d4901c40561b4401004010320f40e0803d9154280e000880e600c25502c55070403174031103940c800300d82502e0303050070708001303084120f1a8001c41c0944103c0001054100c0b540210b032490010a50ba800d8681d40745400c0d69000e004402d200000341515629180410342da500004180c0c0072a54520a454a1034204010120113503980184040d915000521022440811600c0c070308121900801d289070b15041c0442165100350340f00c0c0c0340a051204008540024044802c0e412200126141d061690700c3d942410030080f0003020072540003400c1000c04d100f1050403805001409d10060540e84ca00300241c0321142500c0b1212603801206a508005001501d85112140100c1d601c030051500258180107103541f0b03200a031081d9094015010002603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 909203911 1250 909202661 909202691
    0x4050412030f02040f15020706020a0506130f05030a110712020d320309010315050f0d051c080a15061d040207140d081f030818030d09091407050904 65
    0x74004200c13008944110f669104050b90b0806e1040c0c81c0c2d4401405a1f240024440f4800200340b0401904400901010344690260b42e0040500c00f10071540d000315021054080303042800035216180d8280c4030502d03458078512104c7c0c00c0011903000011141c00f204d003c080940c50303407aa071030304007680b00f04818202e401c2c1eaa034000740c1c400c0010400c0300750b107056003140000100100140ca4017083c01c1c1c0741440069150510b20400c04002d0150b03a07088690362141174210720f07000c480c424015018005942c510b00030203011070380c41400c00c0b410801054401c0d042c000c190150788034209400440c4078100c0300076800d0010080c04a910240241032203d5214600c5d69542c0d01c0385c2c101c0d186241d1082a0800c990440c0b1110b603100d1250716650310106020703000060440c50308107043c03001000280405003015042d0741c0c40c0c0c0b00c260001c04201a61014500c4041003a460070072010740b0070006070726038030030b8545002c0880041c0c1e0f4010707540000012520042c0580550803909682030082c044a001c00c2000c4040004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 909205161 1250 909203911 909203917
    0xa060b1504080a111e0105160206130e0c07050c0d03020f01090f03080a0504031b080d0c0806100e030714120706031a0307080d11070e09150604050412030f02 69
    0x600c2101000034000581407000581094114890760041d107281c0160f004200500915010001802c1d91045c545081d81d072242004000c44656840c2108118040b41c02050407604a0071001103005070b03e0030248008060035201952245100c0c100902d0b04685a881c0c680b20141500d805000d400a182403108160090018064048c08400208048a194100754a80b1515a901900880c00220220b00850028001c29202d690503031130312101011100d103280b141d000d09032402e450081c0305019403c440c041c40c0c054040c1102c916a1340780c07802d081440c104003118503170600d40014003141503208071180e00e01042c10310072110310242000c2010f0301440410085031050000b0700c0c49000d10760010402036050352064040d12403070455190213584050505a45094602800400d44e0041000700030040c401c7c03401c50118400341c029110750989c0c4110841108800365000c000d80e401c6802e00d8420a01d04040566000300110703414856030420380c850182444d4628180b408050f152a4441c6007050300d0740403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 909206411 1250 909205161 909205189
    0xb1e0123030c040e07030e0a030e0111032113050c060307090312120605040c091412060711060a0504112806090e09060106053007030203040c080706020a060b 69
    0x3a60300c2c506072140401d01d030b20a000b5409841c0d019008031364018420300c210920f4a40c018001e002d212840d8038151503240000d55518108031280040410b4800280081c100780741d6000c5040c0e0a091b041d6a84004408000308500d440b80c56800380c48000c5500000c41410032242901c10740d0380c80e180e0001c2100c0003560b44c1c2000c0e001c2d00c2400941c0403400d0380290140170312054103000308811a140c00801c42540d41c82c0d81c40e900050a40e000911040001e075422014040b80200458660314446030402c0c1046001c691361004126001602808200705104c40c90340110000c07010821458950f81e00102c1e210129846400342c025500c8442540c8500c0c040d0b6845860008007550465545107002041c4480c02d00a13000d441c2a4080840c01c1030b040042c449060b5405030310b038641401c5040c4e881ca8201c4442000e400c0c180008a559000c918001945860083c00715690140e90b030b02c3c00742015003281089a100c20440c1d03021030010000f00754082060729000d5803000c40800c501c000340e0006401700000c201 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 909207661 1250 909206411 909206477
    0x30b0d020a1d0a0c0905060d090b0408130801060605030112020429010324120618061d1203190e030316081605090909160e0a0b1e01 58
    0x4004076040c00d10248000d80102d8540018126954811156041c0c80f074000d400741c04070300500e500380054030304a4054424050361550014003100f1546610301a414151804d84902c0000149204201030090813a0058211303180203205407840e08400a009120510034801440b0b1000070580466491307403c010078004281680d1200c851100b014031000e00c08150362680402d241c03180c114504444c5040c061461408030302e02841e140d2414864607036040509400b142c1c07182c0d6610341c40074907180401c0e6544c6598010040040c005190000700e44910000d1403400015500c80c84120041035180c00489500c0f0440e003040320b1365205c011058034050b000c120750362035681c000401009900c0100041c0342900240990f02c120f0f80d130300c4240b0901010010025403c000038002c1010b64005c0c100f10060039041a503000403142d0796203408180900401594202d085c0c08000c1074240010700c821400343c1c42051a040700c4903a606102550206840c03200240036505008400082c44982a083d1300b01c5101198100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 909208911 1250 909207661 909207679
    0x3020307120e0c030d0914010507030212030f061507150f02040506041d0f0f0f07110d110c010f080a0e03040302190321080714190302090f040e0a03030b0d02 69
    0x5002c2980b03d2a048a81034020711882ca5110742103485040c680d0308407a0011041c3c61035400c160011290765000150590a511440041d0f003002d0039400000e52041c19111110f000c02d05102080000c04004140740f6050180140802404149011400c52420014810001d18030040c004d20300060b010715401294000c00101d8000341508903005029107088071034505000695070080f10004019041c0e4803214508030540000c0c500e90380140040c6e8000200c0d080103c11815119205454040c140c8844000190b06000700c0d284000100041215107a090800c590a5045401c000349101030050016603081d407294042204010f042c01283c000d10380182004820044607901c00803100c420348000c4034001d04000350a0360300c40000d48802c0101106035100711103611010402c032034103c48003030000c0f6030341c0c41040b5028407030f400403c14001c002d609840140c0c07154101c604001451040c100c80502440c284480034803151030100d090f80c00190b060a001400205602c040340300503480c0e080084d004240c00d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 909210161 1250 909208911 909208931
    0x610260708030c0a1e0b0a09020307052707141c0608160305060106030207110105210108070e0c030907060804030302040b070609061b0f0311091503060a0b0c0304060302030712 77
    0x103c3d01314406801a085207041c114038410680740d21440c41c50180500303441c0e2004c5150040c41e44c1110031820700080846404585400010b9120070a040a020041001001001c1040d1403506070030b601a4003800c048000300100e0f026100742d8460b07809404258a11840307c20040b001c254002c40103408480c0444640100759102d101c000c003903174002501c0728400e00000007402842070088402c0181e03c01d200b440c608010b880191303074903004016134201c1c4803001140e01c4c0385490800134143c002d001c4e4500401e5a41c5c500540070514100240c407150403040c0420400c240c000b0005444012281145010852a80c0e5410220000d004580020700144000504170040c0440c0341c2041c140c55010b00d001304401a17541200c80791945d0880c0000000c6401c00803070410302400780d84080301300c101d804040380c40c0541c820001914403115100444614201005000c1c0710305003051003001802101001a19024000c9401c80c0d490007288030308804c15030004001003149106480c0c0ca8010107010b5414845450b030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 909211411 1250 909210161 909210163
    0xc010e030a0b010e042a0e1909050c1305010e011203120c0e130911120f0109230610030b0c0706020a0e010f03020909010909050c061b0610260708030c 66
    0x7540c09558100d4251004246c441c070803101c050500210000c3c01e82011318205d81c0c0d40080310010030b40304601c1c4840b0035505100e0058020782100501c1800908a05d4240b80c04021a0410300200c8110b4545000014810b44121200c0c07681990700c84126044803054a240c01c0b030708140300d02501603440f820581d106508540100c400d0032411011144032007200e180f152440203d031298a0040d0070303101a101c1d42c14140c01c01c200e21182160386507040d2040005103035505400d540041800b103600d072031b4817400b4030785d0343c801c16002041140c0807202401c4941040b42c1c580004500328000078001f4803525001c1a00034640710112405554040c5066446030301950018110301d03150300da001d0114044800f00c4141c0b43c844d108507140c0c41001402c2550a909040d008001024400012201d5101e21014015142e90302400360890300e90b030035420421680d181194909140d0007508a0030308408420781488594007954444120000c030707181e1801050b00288146162000720b502281071030000140001113014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 909212661 1250 909211411 909211439
    0x120804182007060614030307120302130f05041406010804080c150705030901151805060d0c0e101a04060f0e1e091b041229090d020d020c010e030a0b01 66
    0x3004031800c0200d01c5e540e0307144948454548030420343c540c01c1082208000785402221070402c1305145401404c00017407405440b5510b0f40f07a04010210280240d0030055441e05005041c95841e520000c000c1c1818070b000041c00400020303000400c030020100b110740403200c0401006480c4c600b1085c09241c1c0d0b05080e02e020303140b0762065508148550030110740e01c10700a1070b030551030110780d0311040722444070405400c10781c020075000d040c10758030048880e502000f00b90500d603848080c21280c0c00354015803c201d80c4c40040304055900108964607202d00c3c0310390031680c200c2600c040340e0282c140115650b12400c4116056213028441d1a403040070150107001a004101040e00245402e503004640d0f91581c02000c5801000440944101c5000b00018040f00c0e010102c101c0441d840380305a200e05400b00844c1c1c1040309408125540c0c034800240c2001402081001440c801c510a80044e1401c170914060094030750184aa0103810300c4a108900c981503141001040445601301d00340a8095031120035040f0152 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 909213911 1250 909212661 909212663
    0x1403190c080f060901270e0303040c051e010e0f03030714010e150c03012601020d0c08011205070608091608010902012006010620030c0601060801120804182007 70
    0x410142c005001c50814181c0780b4103844880d14030642c91481c0d81099900400405c03078034040581c5403110144072040401c00345004600c1002c03901c203038608100c00d0001c80c02813070007500e0145003030300a03c958590708031416015821042d1010070840442d000030a28600c03540030014001e02400c80c2080c1c22010651041c0c554074080400d1300c074205d08459415201d0700e025512100c0c103247c00c00040081059000b0204181040c05155041600e01115944d0880e04080202100f440c0c640100c0d101030b990001100e809004140703d1501c0900440d191683d482c1040d014142c2800301100c0880c50f4074404000b420020b42d1018104500c6c0d40d00e40b90f03058040c000f1420201c0c041440c440022968400a941c0112106029802040700f40c5c80c2410071140c0b9507810481304800c60302c0c83d641004900051000302a2210400300030015545406002001d5642c140e002c6001e0302d07480700ca244005000e40049408a8145070302d405040815000c14800402900480e0700a000d0401811b0384142c2c01c860162480c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 909215161 1250 909213911 909213931
    0xf0e0a15030914070302090a2004030c0312080403053c040e0112120f050706020c010b010f03020415050714030408100e060f0103240606020a05100605011403190c08 72
    0xc180c2403c441c1c2d0f4100c5800b000313501104500000e520b52009903c90382d10202004680c1c8545246c5203021503480d1b00c039030010b0325055807220060040c80305036075202c40e00d442585440c00c451705e00754400038100d02805102403c044000c518141d460900c410f41c1c4d070582e500c1c18029440402031035205c240580d0143c40707a81c0846150400009030690720300145041c10f50450a01c003090913450b84201c64203c02c25603d001800002d001d4a004907400388054460000c01400000344940c00c003001404400e0401d039400c0030180108400d100c800380307a07845000c00f04028241180c9401492418201000d410709000c8414440803400182015002a41e2014182203a4080112076070000510b5180d080482e8200941c04c8641c00400000f103501c14000803280819a0043c0c5004600c500d41003a03c3e11503102d5401a405030b0390036001d000f01030204800701420004200541860440042c100c0c00c00004c030b00300c0022000c80011078061500f043e42c0e1340c51100030340070012010740610140200703105807100119 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 909216411 1250 909215161 909215183
    0x70e06030a0b0c0a03060803030a09020f0906011e090b0703082e1202060c010f0b0a080a11013915020a020c060333040e07060f0e0a150309 61
    0x6982000700314007901a4019100301410380d240d41c082e0741d10354015009001003680d28000014060350034005540150b000300382c04581c0b0821801080509001102c40ca8400c1c1010004e0042503a003100c400d8042c10031098103205841e004400c26950448503a02c42c004003000000c00310101984041220305c0380c2103800760181c6401710074010507038182006040c01404800400d00f030017100f80b00a00c15000520042009142035000d0100d6400d40b030004806825070340d190039180781c00c0d00d812100440035100764030040002690302c0e100e012641252014050601105049268009240109091141d00b030101c40e488424104c00340e4034503810f803103030040e566090b84111078081129540222400e0b418641d0040140c1241c020800c24542c0c00a0712100c0c803090014544070100e12440080200b003c2c02086048015905606000903543d0440c01810a5044914180000717034000c48030710124085450001041d084510100d8080981c6030054008440041803111000d68590030070410107100382c0c1400d407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 909217661 1250 909216411 909216421
    0x3080d0e0706020705040f18110f0103020f160507050307030c060f05040803031611011104090f0b010801180609020c0313050103061404050a140c0a0e09060109030b0a0b060c070e 78
    0x24070380006014480058100c0b01d4104503500e09a0040b91600950280000d0381d049100c0003e05c07118840941207400d40000341384203020703280480300e441002c1d00a0a0a5180c121214070b089420b200d00a12940e117007058500c141d081c030004004c080040c0c03001408941d1407544a04092049100c140320b80c400054064561398100752246043e1402c6485001c010341c03e51321000110312141001c00259420070240038511007107a2400d0058052071009803001c1c51380c0d28108070105055030110400d801c0d81d5410031291800c0c90342c0c016100d83c11a14484001600b100b00008110090104c1da401b01499500106501240010120082c03802a514403c19a402660784c07005406a81c0e192152521000f00c600d44004c1ca810240c002603445141500c0c001100340748a5141075442009490b4021080d00204000c140c1e10b0300900407541000c0220b801d0542460310000080c60007503140001444044040003142110140d070300298040c00d030080800c0d40b900c00c0d81050f65500e03c0a44070b00142c201d4060013041d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 909218911 1250 909217661 909217663
    0xc120705070506100303080103111f0309060b0d02031f180c0608060a08030d090309080601090902090a11090d0203030d0c050c0d03060e0402060a090e01030f12081510030608060103080d0e 82
    0x1c0c1121341c50b441f4452580e00e0f6440d031511034640d91005130703084031001308418031402c1040d070300c40308080035500c0001e110030150410104840550041d2405400c1800d03001d030141c0c0c1c2c002003038208807070207984181c51001d0918080d0094000c08120071743d1403461041c1c0e00100031550309084203481b00c030f50f68054207995a004110018001e40b00b40344a0360401c01c00a24803440c03c0c1c100c0c0c4812802401c01401e0155034a0b522440c00b030f0264400d8041c1c070781c1d41d0014021403030501801a00110001801e00080111102d140020320484440034403550004241e9001c40d02d0500660318901d42809040242c442c3c2d9184c05400c90b809002c40320014010400a950424080c2c881e010969184042c160700c075a5680d401d204ea9a800800340c0000d01c0500100024a12034005a1a0195100317445000a5001d40d19007820a18401403042d8140607000707007001405403000500888a03503044550032031a001c0705105600808280e080703803005000c1c483c004414050030100410704091404410007000201040c42 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 909220161 1250 909218911 909218941
    0x11130203060a141c050c040b060703050d0f111803010e0a1e0c0b03090a02010f080403020d0e0f0418050f0106060801150302160614010b1c050c120705070506 69
    0x1940c00800c1403070501600180040000c84800d002d0201c40490380c605046040c000400802112070342d02c11b01290049080c907000d640c2013481c040e2405070401d07510f81d90281c103a004104400e11110341c0c0d03544a110542e8140c204034650411284842d9640b070601c8011400e091a103507d80d8040e40c02c000002c1102000000e9250390346412a1010801d212110029809500703501801d03504440c0c0104081108100d1000079030223074800c240107268144280c4005041c0240c0340c01d03a241844407140800c804260082030030b0401ca103451600406001410000a40b8684c007003606036001460800d40301c0c403003101183d0882815000d032048a07442d4002c04020f5090700c94a00407000003903d100b004105070200b100a208002445040241c1024501603c01100108040c4251100c90300e804042c95101010400c0d6809045650701d520f1030904c4003410310348610f05002d502001d003640e400004100d1202c607401c2d1200301e10305c022004214140142d004005400c8032209070703114050031010800345030f070f0a194 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 909221411 1250 909220161 909220171
    0x18050a0302120f0f070f0c06020618070315050702010905030a050a0e0306070c03080a061e0504050a0507080c0a0207080d05031f0e0604050402010e1914010206040c030803061c11130203 81
    0x2850311301c6001c0d00d0140f58015000440e82090060000400624451000c8000d801d1603401024545401c485481808130b940d40080101d070810030090020038140c01301c01c5207450140c1c81c08181603e83c884102e00401e4102d902034414040440c0d042510303580306004001a81c3e6594030821412521002c140d280c0d0002d403003035004155085607040020f4002e0303801ca9131090414030700199140d6180c8a50607142005040c0c03058245004600b40140d107441d104542d040309907d00704000925083e40042c140e1344020b8400c1d044170030081401501c4174030070083d80b0041d01818040d50100001d24001805071313007040d24580b0341205d07240c03018801146d803411000111500b07284440c000b40c4031207041c08003c0401030003c2c0d04205003003403140f0640d1a400310b21040130b100141c144001c1e070f1403c00348941213444455004e04640181d001c0c000801c0c06400802e09032034000c5151590381e140c12000440e443c2c40136801d44090240b25100d0703018004680741c0074440c3c40041c0d03588031011482c0c1131034108a21007115 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 909222661 1250 909221411 909221437
    0xb040615030908070501060305010903080f060f1203071505040204061a030408031003050105160216060c3309020901050103050c070b070e03030d2405030a1101020118050a030212 78
    0x101030030051190704440415402812814544111515024203488184c2c10a0710269180c1c500d80040590103402980d2200c1a400d15154900700348001500c41807005c54024440e201d04450700140e00790900c2101e00c0e03254800d941030b0015920030401b4014003412181a4802d038945080000d04640760b0070302e904c0c0410351000141c40c0d40d5440e559401c8a03080588600d44660740240048009507091040e0342c095100e0101a440c51410500c4c001d141c0402903a10b1020f241d80440c04010181c1c1200c0040c841e694841e404507400b41012440c800380480030700070503070807406045004940000c00e900c505070050003940c00700301c1c90f03072240c00542c29100140e80c200040f8000304601e0012072070100416400c5200c9180020703410002400080c03030354114103081408030344c0e1414904400c2d0a0f0300603d0802005800392002101d06d0300380041c1e16054403140190850010b0441031a0705d80c401e52003800a000c0401103141944080d040c680c1e92034400311001c50262007072110103442c080c10001500d8483c0413040e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 909223911 1250 909222661 909222689
    0x405060a1e0e030409020d0f0515030307030e12160609061b0f110915031b06091908150a0b091911120a0b09131e0230010b0406 56
    0x8031980000b0440740b4441c1c24a030005000200b1719020a00090504010304800859607401c001c80c0c0b0812500081c21a504a01000003a240c0c1c03a01c0c007105a410300382e05410485150489000414841d03030f01080c900e0018041c4a100c41c280042030b42004040d1140759980c48842078480e01d040e201c08030580700f140c0210403400d11000020b8480e80319194958803d8404640c0d1590071000308555003419241070700480700c070760306420380e6042c02c01442c0101c91006114a60b8001500041941441010710075402041603020f10b80700850b841004500408801003107c16503200c004081014400a440c0052580d0034400103081d0f41c5030008009026907030140600515001e6031040360000e21280104182c070030801d0050002c044000c40c0c09502c00c00300600f012984000143c1001001040200303500151000c0194030800f14a180c1140c050004100011b02a107035036900004062110038118030500d60401c40d80d0103e82107041207a07070003d981f690024010f40c1500c00400080d20500c3c017461848020700 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 909225161 1250 909223911 909223961
    0x702071d040c21050708250b03130c0e0408131509090f0e01020f0d050115050702091513060f06020d140904020f0f0301030b0604020f030403030515100201050405060a 73
    0x40200d80c1d282d060b2499003096000f85983c0c4182c2000c00c0c9520035001c5170020110070f111500c4164560142d00e00b014a1100c2550a0504980090001030b2200b0b90108200300d1140c01c00408141d2071001d8100c00c05143c22070300d800c0ca002000f650042c841e10510a00c4000c1c002104141c0075000001c00c40f954030340b55600d60401074900e00810313200d10340002054580c100309010080038401071400c11590480310350b881c03038414400c100303840c1c040e031151303202c021001c20181049a100c0180c0e8012507048603106c0c1c80d900c0b0410800c221101c00040301da4024850740054074000c0542e8071080880d2480c00e0100ca12a03030300c0f002a41c446200031928404a0502c0a0128683c0203810003403c2d61038009100508020103200484d00c940c12100100c0d40c02c010000c01030090100e102c400303950000e4211030651804940080304010f81c00080d00090605854801203480103d03030380c00030444500302a203d00000600404020302034641514140c90030300559020407000d503110302031056481d041d400700f000c9803000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 909226411 1250 909225161 909225179
    0x6040605190302090a080c030f060f0a02070f0b190b040507141315021b06040320010903080c0304030c090c0203220915050301050a0606020c060901050706050702071d040c 75
    0x100c080003004060f82000103050039038445100c800905121402490300368000b030141850b000106c0640c5d400ba600800400031920349071017005500406800c07000d0f8507401686040000f415000600a02c04400749c402c01c0140b45240c9014042850109014003204143c0c4050104841c0c041d64854000f840d1425409401e41280004001c000b40d003001344103405c0c1d40c0d100c80c00308080451400000503004001d000300c90200014040c0348040084480c07500d01451503455000c110301250100040c0c00646400c090f040c1c1c01a070802c0011a0050300d5550b854002c000301070340340da000d404112043d9514560205141401d4803e14451101c281c005500e4041081644030165107600b400300c4840e0210301c00810010f00600a402c1140b1201188020310380c03d00e8201800d585005040e09a100e20300740381003042e2640011110441d072410745d07155980d00b44440c0102ea080c411850050016410242400400350703000820804481580040365850002e00d0034000c2e4205090328090043c8065010034482014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 909227661 1250 909226411 909226447
    0x7260d1b0927050a050405100e0309010f03020c0a0c0513060b0d052503050403030e030702150a0504030804120b010605071203020d1e0b030706020f1e0307020306040f03090506040605 80
    0x80103030b481200c0c200c1000384070007a02c800303c0715004c0d403d4460b0140000c0044c1007001c0541e940e000e040034040c00e5090a00b40f1350724045c900302641000716101181070507e0090381101d45c943c079244240ca00c499901d0401242d605024400c00c2c1c01482680403901c4240020b108190640303000300720440c03806603800c3c003d201030000501440750025401030142c06055141d1070200b483d000d582c502040520301810090200e030307025400c441c0f00384c10411030140103950f800384042c0c4400200600030b40f034070b01c4414100c6041c0200d40000740310320300000340482c60554503000840b10320302c10100800b00d43e803101d03c1200c2a001714100241103894010413185060301a8001c3c18180c0000c907400500051070042071400908401585c81b0044d40e54601d0706020706041c45040c0151166000400c00c0c84254506036544490714101214400d2618642d911241000d1040b182029002022140c0c20f00b46810001c820840c1070318100c01141c5040b6002610303003000c0056608440c0e094850500780412890301c90b400074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 909228911 1250 909227661 909227699
    0x10f14090414070e100f0f14010f2303090601050f01021005070c0804170d0e010e0d0f050115090b0f01050a200601260a1707260d1b09 59
    0x80511040860404840100075205e181c0300800c2c0c04000d458801108400c2480382c2060024804406040c07201348030010203610100420728000301d4011207244110303400d0340c030581d0500c00c00a40300503d20700d000c00c49000e18059000702c1c0c00c0d95200d0740d0b500200160410091001070260b0001d00c1c0d82c2d1010003480e4042e952100c0107003440307101d40f03800d41e480c406240d105400120380b02d09241d1a8801d007503010400c0d41c00005950400c84007070f011032800130b445c940e00c40400746d01c20002600010704100400e030f10480c0140d4060020310007400d90002a003101c0505001d450b00076440c6c00c11040c400c1c980f0001c5010803100c10b845140c0350142180d030843e040703544524811b10003904185003441c024000c1021074002e00b040304081b80103007000e034108001d03c1030110242e00541c2c01502c502012801c24a001d1000e902c9030441036507200c1251405013001907001903c03040030303086d480001502a007194010824a01d04160400c8003500c03001c0d98403003507000d00c80c021001460250040c440080740c500e542c0310301 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 909230161 1250 909228911 909228913
    0x9061206060d081306051b010b150a031d07060f020601120803060f0a06031a010504080c01080912030108010b40020408030f040f0e0421031d06010f14090414 69
    0x2c856140c5103503944e503499005800113031000859480342d214004940c0c0c3d030070484000038404600100d002610301c0e00000c1e01d0b40300d4904005185400c450080e800a00d048580d05900e2000205944e42c50b9102c211501c52040800ca8062800708a24030110f100c1d070584905040e003101c46071241d182c032031480d040241200c0e00400ca20b440300c9001c0e0f8889113440001c00031503a012800110a0056032906031031554414144001408123101010f000b042c40b0440d02c800303290440721580c418400d40e140c01c294204442140c1000000400c8d0b00300190480103aa4905030780c1c2031344944411540c101c580c41a0301c00e0b0400109080c01d0450b09140340c090074111007200c080c01500b080c0d2260416411a0301c00410f408000800150400c00c08250080c05002004000d40908083c600f54a4004105001c80b00e2800030040703400d0000b0002e40258402c0b0b4011a000c1c942440141d13405024680d2003c007805421500ca40c03140f80040d10f0064180403480c0110003812055442c0c441356506190101c3c104480340e01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 909231411 1250 909230161 909230167
    0x1c0503160201140c0105070908010b0a170114090a02010906050f03060f0102100c030e060106031808030402060f0a0c0308150a0512100507090618051c140304080a0209061206060d08 79
    0xc0746103400541398a07401500006043c1c28424406494800c540d80120500d0741001c144040a64514105104950315001a00030304000c80354510f00424008010803c840160414001c80500c00681c00c41e01e14400e88808113070a80f2060103542c0350003030f607425802c54801000025140e040c200d054010500341801100d02d032401008810090352862000f2000190780d401409032351030020840d032401010203050800a600d001c10543c4074221008001030400c040c000003017000c6440b140122890300d07560700e4080c3d480308a2480010401d0071901410780004400002007441c02c0e511105e0700c1d00134217000301410328291509043c001c1044442c04003860394040d407401c00120382414024a403280000d5036441001e00c1c10408060b0111402c618803090140d4130b03c8060050780c035804440d03400702e0710000a08034480385a1800c054080c1d1090004103240c0000710f4001012000000c906801520807240340c60265030307403010b2002f600b000301d40c081502d41c841004100c0c941880d05a0303400381805480b9281ca = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 909232661 1250 909231411 909231437
    0x321011d060d1511091c0c0e190c050913053112030c08090f1002070206091210061710020f1b1c020c010f0e040905011a1c0503160201 59
    0x10840d5a0f016050039004000501e648052412028100d403100ea521040b1546d85180e4481e404001224014000c0c039a2522000c503031440c8002c10701c0b070805c401c2c8032428048510320344001403454018a83c0c0350700404200720304054988160180d148124045a09a00c80800005010411000241800303140c098904110f0000c5620004880c281400e6600c0c00316105400303100083c55440c0081c202d00035600b1160405411210110f041a03540454a50160703c50b10742c0c2c000100544030380402c0320b41c0091007003e04240c16501090314000d00502d040c0030001c0e00c0e41ca0544c203155110b901130f0286180c0180c102521358117035a0b405048040f0b4101041360805150200d8880f1780380c800442c0d52526405000c01c11003142034104441072924142c4060500317012288006408001070071210000d1000100d60107030240c0715607204085440d000002405504040420103016045100d0f02900a07100c4455201c00c0084a10940b4200c030781c414021454a541010008030444822508a0400c0580c0500396 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 909233911 1250 909232661 909232703
    0x2d110a05090c07030207080313051011010c0306090509010b0a0306052e030516140f240309010c0c1e02030715030e010e0f070b03090106080321011d060d 67
    0x40c4a00040c0494a650790181c1c24061b1030301c0c03130580c01000ba80e0300c100090300700510044540d000319101074500c208420001d21080d0750560305450307200007940c80d05252541c2c09905800440840780000030400454032110b409900740c5044401e060341140c2d5800081001a285910a5901021211064241c880707400c44915a900c0e4074596464402500c0400707109004041c0003151500c03da900c001c4040a10701140501780c206408030f030503c10388010b0041d40c01030b10740c07000c03402161058284626030324025460614030b581059880351241d602c0c00d4800303c4683c1c050300048803600d800c14a40c0b207403036241700030040c012807100744104e0305801254000518200005007200300142aa100829240301109030182180d4143d611080703164403034801c0c50614100840c150080e586001034240d80c80d59844402c0d4054441640b029169110001d45003220b50100d800010000c05801c2c4024100e90b03850100c0110b140c1d41080f00c9542d480110003080e25444d040007400c078110300c1268000ca080c03c0c02c150328 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 909235161 1250 909233911 909233929
    0x1f11010b03010e0d2c04090212030c0f21121902130e0a0510090b1206130308071e1d0901030b060324040b060a0b0a0c2d110a05 56
    0x210300103a2003c1204d072a955008203221043c0800d04050751084500c404050000b0304540c00003a000b6503407594620155103c508404040704989030840340d8448a0524007991105c2c2c4001c800e84074000e26809040c002041003131203628105558515040c01c1c00080e0010b074260340603080d110814001c448107181c0c00c4140c0042c0c90b0208501003c0d44450303140072501135000b070005003141c800c0c500e03090030410801c0d20030900900b0344498910001d030b42003030b03517001c101102d1810f003000c50717079210f070000f0441034500d5550071021b02d47c81b940e208406034468050550f0010000142e00d0307002c0210880c4818020b00c9500c202c220107103841080e0040f0103083c008034184c0c440c00c1e0070549000c107030042003000310308040001261a614062002c50030040810500c90351410213000248141300341c03400309445d40d072a10360b0040178043c0315040c60781c1c42170164800b4003002d0a4034400c441c2026407040c0c506e03880441d403100c0500b400750b400240490400301c3d035940c030108100f10764084e403010710345001081a40b18a080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 909236411 1250 909235161 909235181
    0x6020f12092116170d0207030803060a0e010e0103170a09060509060d02180316030305090d111206060103050114061204060f020d090501061e090c03061a070309051f11010b0301 77
    0x42121a05104c1e0310500d8840890300807813141d00204803031035500c1d4005005401c6a8000c0d10725070700d94840e14000b03103005441c0d60114066129010002c02d50101c45005603040740d10a000c10900c2c00d03107100001c0b0040c000d00c6040c8004c038441201c1000f030180a02c00801d13003400c000700030b41c1c035003600c3d030b42010101c0c0c00a9515000e900400c0c0084030080c201000800a644138500c2d071050f13100d282da0f500030401d100310038441d03004520203c4103c04019800c08588080c610080070160366001c2c62110700c1c0e84a0003141e030203000134140400004c0b2407040745440300d4039080140482e0302d005069a03a84034100c5001e0f0084071500da07280d802000000c107500c0030300058803040e032011510740403d091281c29602c00e90060100300004a42d42ca5014002c000c94804855040c40d0100f60f44d040f041c2c081d40203015a600c2003024000001800046d1391200004003c0d8038469101d10705150f490b6030a0014108421507004405082c0848040205001d050401c0305911150004501c01d0b00c1035012900b90360720b4800e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 909237661 1250 909236411 909236443
    0x80a0b04230c21060a053001020f041d241c05010507020304060315060806120313030605060310140c090a030f060e0607050f04050108040515010308030106020f120921 73
    0x41801000e00d41614184c1c0141b2013162403414000700c00302c41080d00404241c034903000100405072030500303040a405460145402170801074072a5a241003c07070b400b5100c0090300003400c04000018003000b04503099126120f016088514200390690300b8032488106070b29640410813100503070440000d07424055644074049540c055521245000005004d48064081401030070440724000d10810354000d0126500c004c007140c0c01c9041031200d180007401e620801d4841100094441004000d00c1940e0b004140140360076130856920b00c02211034041168060b403c6c2040d00750301c19012480740d55105014080881005054244150390381d070f6480c0d01000701e404211201034860340b013050b41c00c0e014009030380d100e259400c041d4034018021000c1000380c400ca0040c18140f04081c0e000c04c0a00404021055400800030344105a03540c40341020f104c02d4000348144001842003074017641c2001c402040c42c901c3c3e031400407409414003004404100454503a40354980411a44a0688590b044104410340c1c496003124 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 909238911 1250 909237661 909237727
    0x1e07050105160f050304020904030e0d05030d0209010e0f010801051e030106080d0e1905040f180501060905060301060b0f09010e060f0c06011508190b10080a0b04230c 73
    0x1000a82a43c40307800e10041401002d008000150711141d00c50340d40240e06181101000b680d800c0000c4105007480300142241c070002c203600a05419507401006001002d0300d800080030300440c02c0104404000d03240c54009140c0500400903410110100c00e0240c0d03e9215680c01c20854001190131a8910b501a85440d484124046100c82d0807080810a044064a869280031a018905031342c43d150380c8203071405180e40301440700240211350300143d0f41c0501d0070145070070789540e8100180a4403550103941c9181d4030b402c021a405240c14400c5a0489600c001100d041101d80107580b1129000320a00d00e040c088030406942c4240e44a1004010340c243e500c0150340c407110f020040901e42041600130084200041f02d01d1418160460703003843d48030300d08000c01c0201c100c0900d400c0c40a0120081c401d0780000640922108454001e030f203007446114040000c01031440301004000c26204420119101070b285132400800042c10f038074030b407070340b0411401240d4a02a10648510380c0d0859440d101d0804481c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 909240161 1250 909238911 909238951
    0x709060509391e0414030a0c030b07050d0608060f01150c030c02151308070902071e030e030d0f0305090307030c08180d06050405011b09050418150e160303051e07050105 74
    0x440c041000400d019001040304036402c8d516070f5a801d66500000d8036619880d400144c0d0544100105c80d45010700c10000e00001d6550485555180010345031230401445520020403440c0071081e4400040740c0a5440e02c4030800181c405461128003104d0590700584403032a922010300450009206108050b40360085013444e01e540709080c120030341c000c1e0304881d004100000102d0055410a501d05610800000712075010b0b16007902c0c0500c40d441569018040c000d00001c4554020020341344500864505000903a9402100758a1380700f03498008000ca80c003003107801c010402c00409803107900c1c400004046000ca034080041c15508440104841050300d40b410002008000c0c0901e20b514203100c00d401494508aa902404401e40e03802224090f65980400a0700710700280812050690488484030035011030944507006000d03000320401041c4902901448090072402103007044a4041d0303500740c1002c80c0081c4102605640060b0b900c2000400d021520200c0d01c04c1c03258501803c14006124403010320 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 909241411 1250 909240161 909240179
    0x50714091504080c01120e03040603020d09150507030606020705100809070b0c0d170f0604020c0a0b04080d150605192a0303150e06120f0709060509391e04 68
    0x106c0d0200700100c600707000e05503194140001c04d4500ba6081c5060240e224030000c0e006000034003c030321000c6d204400191400040c080306600c524018841583c051007100e4482400341d9403606c591240c1c6030840301c541c100c001c4035031040c0d0016401050b4141950481d90b42c0307080c82c0300c1c41d4000340c229907005e80007400346d2400c4941080320100030b00e01d4040c0341401890f200c460803442080040146028580014105032525402d00c820703d260350344044603030418103060a1084040c0c114400c0c054070076241400c480d0707242e8035083c440002c49078a5036800340f514030000030044000400826030402d100491a90024200c5900400d2030040c0d8883d012080d00c840e0b6080c0181921400b0013020705400301001d00307209910b0240103e030791040c000d4440c401c9880c103a8282c980740ca802100c580c091800b410740c000c01c01401c00c0c0c220a013210b5084403049002c1c0c64041820585280c2000801c100b4035074410320044d01c14040c0007021a00743c0410045040c40800c0d000150b03c8880100042c0c1c624030300243c14419459 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 909242661 1250 909241411 909241427
    0x15020322081c0c021c051e0403060b0102010209030d05130f03050307060b0a0515070f0b0c030f060f0d02011b1b0501080c040f030b0c040f12020405060301050714091504080c01 77
    0x81414240b1910030450383c007039103070049910020610b0b0014840d00034190b001d1030841c3c0e124510311310301601c40c107a0b0680b207030010b400501086881b41c0c01c05503a00740c558414001d440148034010003a028030f244101041d59540e000c0d640c19030051011000000e08110345c12615001140140050740e52980b151030501c00710762140400d1032242403108001d00c086e4550b856040540000d4100d2259180344905205946904c800b000810326948042042400e15080d0099400f980080c078595810361100d1080044040c166801650051202401c0e00055803017145010718040c00742c4200b00d010400c645450803c100c111002241000c03819100300501d513405240c0035800448481c1c05e07800c0608010005107207070300fa03200c050144080100032459a14005003258000d0141c0080f80110b02e80c1c0300c816808003611550164859442c09000070818201030184501c264403983c2c4000311180b1000420b1500d800c100162a000940c2014415026503558000c20260a0640090000c02c49110006104013 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 909243911 1250 909242661 909242707
    0xc0f0319020c03160618360903081311040504050c010807020102070f02060a032310080609030304030302030709080a050a120c022b0212060f090d080f13050105042d1502032208 77
    0x140c982086940480c2d8004510758210240d03441041c0030790be0600f00f03011440011014103602c41d2074a0180800c2000004060306002c100380c80348441c0f0741d2103480503401c0340600350000c0c200910300711600300140b404400030b019051050070001003460740454000c08000201140250208058040c804d0b25040f140c1078034020501040142080d140102c0d1481d00c1e03010183c8000c041c10f8010010414550141c003020024020107400c90304514a28141075650b54103040003a100350791a4294034040d180b040382580042c80d000b03440c01158508d1b000306090000109040c90409452040c20000141c0d0750703004d41400c0d404d6080092486007465142c02d0081c0401410714403041e441540c50050041d00030346001d03402120300c0104625a80c5c2c2c18402c81107480c200400600551a1404000030051100c0f4050070f0300c84080d004404209062010360a006101100600100c1c2ca0340c000c024241c940780c0065900c034008031078a003414a844024024403842d154011141c408001c20150254040214144070304 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 909245161 1250 909243911 909244019
    0x30905010b060c030f090d02030f060a0605010305150f13180203010605060a120c090e0711010c020d020c0d0213060f08190c06050c0f0319020c03160618 67
    0x100100c3d01c01180d4034425543c000d90f800e10003241c10710300c43d035620171360403001900501070301c0724502c200403c5a2504412600710030103500d41440816070794443d100d40b42c030454114111105100c40e00040040b44808595a581e200b0f110401005c18202c450207039084ca030300d01e04210390b10000a88101400e644d2039801c03184c061042404601140e07a4441c0d00c03020901d0301124002103407040c1e03840071191950306411001c48012014140a503007644646541c4041d0b1585000304407030030b245030040340c40344800749061006a0140100300a00c0c50004441d9142d144010b181c0821202c41c2d90003482510f5040c0d1202070300c00c00100d020800000141b02c11900080490002803010b07000c0d0f40da00127040018040e190070080301060318000c84904002010340d55901c0011030b0b8407210308212080b1a005070070028001030003403014200f06400d000609030344000301c0940c041400390400701c04854070003120301030407075800c02084001a46142c85416208142c24404820004a2648044061101a00c20700c07102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 909246411 1250 909245161 909245167
    0x916060e0906030d0e19051005030103020316030b07050c070306150815011a0901021e0601061202030411010509031c0801030b01051f0810030614090d1106040305070c03060c030905010b06 82
    0x4201c1d804184c00e401004206e8404181d129481e540c400215820342050b90842540002045c0d0345802c01c01860489101714100c1d050340f83c440d000240b000e4100d2000034124200c94020070341c058000c0d4050510071802c00c00301d0f8a41507690b1150400d441030b100610550300910042480002c80c01c2c45000101c40e22101189815407400350144058a606036190a5004002c144500d150b8800d008880700003440c00d9248140f1000007118a80f911028070800004ca9205a03020070995824020780b84215048407000c000d29204c070740190344030740c40002220b81c0740c01b409050107502c0032061002d01481d2115030ba9404290b041d80303000020810103810540c4901a00364004041802130a10500451200d20b00740503140c03124480e1140302400c540009140170305002e6070302c40e075560000710588691000412600c0507804540c050b46c1d0700718090410901c50300305070000350100780520000c050052107059044100780d42c98442c0e03421992200b51103000aa107658410703003803280034010f480000204a81042c0703 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 909247661 1250 909246411 909246433
    0xf06020d0807140315120606090a0b0901050409020a0e0a020903011514040c051605030306030c011b0f03050d02160c0608100501080a1803120e0c090601080916060e090603 75
    0x80002018090340c6074100c0040020301117100c50b0070080702424080d2001d214202d41c00c1c0c406484400403500240a510f04000048810100d406011403505014091504507420102480040d0415640c180e03040b01a0f9800090317440c4d00d00d0030583c8580d41045005898001c6030302010b082d80c20404400715000081d02c81400b0041070302a060144400c201d0f00064007401111055500d401446c01c034229414914160206000010000350321a0808406440039000b00340015103a840120280d1900302e182048450001904100403c40244c080e040036803c0110120840c4107170f900112045150445190f5203104108445940c032018044609143c200d504c0c1c50390032039a11800c5440740904002000c00491042c0c0c10f15032000403003a08804901c0c18078896420082e14903001c00b04003440f11445c3c00240356103c1d001250a4500c140c000740991000c0c2c8800004650440c0c000e0005844e80c092805400ba602c01401c083d03000500403a100c0d004582c14940401c10303038010040035039029401c20100c8072 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 909248911 1250 909247661 909247667
    0x206070e010e060301090e0705030d09050102010b04050919060908160302060601080c190504050a0b04210510020a050c07030309080115081e0a0f0303140115360f06020d0807 76
    0xa41034a050000000d0000495924072307150008036030106806001e009500d19545a000811005071002a002800b03490b01c1d000900c000c0b40c008954074a406d401c62220f000e180b18012104181e118015030011030102e02c140c403402810790040a08840c50340501035640b00301601480780c01e50040703003400c20702060324001214103210f01c00d6a007070070001082d2809080c0308a00460543c2e020b448080c066500761a110003e40c01d60b40c0c41401341c40f440554019081e82c0320541038520b144500d5011000e0600e15230266940c40117504500c1940090080031b100c02034810f6400c114500095010f40d0b01c00410501d002886c85c00c4944120040c519403400a4091040160008488103d20004e905500350304031000300007070401080001c0104003501c480c1c0c55005050780354100c801142808410036005036070741c50141c69426041c049040100c0e5080c2c0300106440302400c800002ca2800d04045400c6803011050701e660000c241d00141e080038051103040c0000359041000d201507040d2800d06501d00e050034075003d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 909250161 1250 909248911 909248917
    0x270a120f0b06010c060e280f08030403120e0a020f01110616090b040b0405040606091203030509030c011e050702060402090406020a0915020109050f0c0d060f09050d0206070e010e06 79
    0x900400200c0340070070700991046408039251358120380208180128a10441d490f40004030082940900c4071070b0110b5006050210394108541c0814440c44030700310380daa4070303006805c02001903050043c001410030010b001030142c102d403100940090074060410b407040041d61404800460304014103910f41900c80c00b40050b0300d5070443c018449030044400d604000302d444000540200d0641ca00c0420001764080050300500282e80007218140101611260225020344c071500c940b02c501d082c042c0c0715001180c001d902058008200030190382c0b0b021000490542901d40c400650007a243c85184a00781481c040d1090b59003081c4d0503c090166401c1640009001850151020304180d44c0010f130084414000c403c200c00404007520f5104902c0c4000f81c000c1e00820100d4420b0310140580020314040c0800441e44c448d40040c000e10301c44a800c3c09440e101c005001d03250b2031804044e5542d01030000320700100240b903014021a40100002c0ca89a00c00910300c8410300c403248c4c1407001d01010242695988015 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 909251411 1250 909250161 909250163
    0x51504141b1e160c0e01151707030b0d020a080d140304020d02090910110408100b150c01200c070806010305060a0f18030203210103080d11270a120f 65
    0xa060f16a00a64a802c1d40d20400180003040800480030010b0b4507180504114121182080440d00c0340f501c515058501007982d804941c0151020300c00542414000e9120048990001c0e04040c1650fa80c2c0d80400d030402400c0c1c012080a5001c4000798101607030002e1140ea01c200c1c000d04c07503420341c10154082280c0c6620303004000c0c4228001e1000401c0c8000402a0311000c0c1200003051202c200c00c0350154400e0741c46405040b006000c0c80050520448003805080100c00c8050043d8503a1944024410b0b030a4000c01c41004017175413502d010001c00a105070350204480750344000d07a65070316050400303140b130807034258800c089a4200600400201c0e00c0422019401002680007040d440d4640182e6801091a102e001d10309080c40b40003c0c01307041e8000040e006507082c40c456458402060002c0800c460401d1000404200c030800c050000a200c6400805040b550f680c080da0801442a000b007107074041a81d21100c3c41381400482c5159840c10001d402d00512460103400110140e41d16072000031840c51030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 909252661 1250 909251411 909251467
    0x12190903120309080f18040e0a051507050c0f010c020f0d0c060b04060e0a05160e060403080f1606020702010201050c03061e061905070b06010206070f03051504141b 72
    0x340c040c080c405400d04940c01c0002c08007038160744c0c0483c44070f1604c52032040c48002e401585042c00c0482007031000681143c9c6281c03ca401060307100070800460203e004010009410054140806015a4420048602c0450404002107009000020002c0c509070281849035004d0f481054040a4140c2080340c071900704d0b03082900031480300c480d50089406858903074000743c00503480e40d04000d00c45165611841c0180e1003001040f0807048158400c480020000d100541c2c03211003000204001003008000b05041520036401e00d0a10020035240f2419050a080655516800042e80011982d082c81407a40c1321820004d000e045080c0040480c803040000c81503a85403603e0b110010546030f8449003602e4072504007040b1400010300c000d03030003001508500c0080360001e01050204140758008102c0c0351050700c847c0d40300c003509462080100c01810002d400c00006080d070161242c1241c0303d502400b41516806a0010f00c5414104071009c3d059904c050900d441a200b4130078200d98290882040e42d031401040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 909253911 1250 909252661 909252671
    0x901152403060605030c07110618010809060705090d020409050f0609070905241207061101111216110303010f14220902030115030b0412021501210203121909031203 72
    0x703e00544140120723143c403a808600821080c816288a042c3d0800c1e0040c2a03950b0003540e01c0740c1c0005030307550704e0940c0c00101003401404182c1a0342400d5425002071030004001159842c026220142084407040a00a064001808002034204100700803801400301070020071540c60940304100710316194514191140030802200380803992010032901c2d800c485002980e8100340e035004060412120b440002c02c587d420b0955442e4107071500d0741940c51440a5541800032035648100c01103140d0800c0840fa42800741c4a1845210201e0802c09075000c4c0003640a0881c000e4148080d40c9001404840a1403003112030f0390403e240c1941d5a40c100151011940c2c0100c6c00c1c40c61840000d02405c0031554581c130501e03006000005000804405500550040c3c0f034107400346010410403030722441845a005038200380c80c0b0041144e08070888140034041d0001e40e400005820300c0e40000e040c40800d020082d45400003240d00c50700200c440c40f1904050020342420002d46142d0707600d8a00b00160743c0c01550a05a80d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 909255161 1250 909253911 909253913
    0x21b090105012723040b0f010804050307060f09021206040330090c05090c0a0c021309020904030e011d22060330080118050901152403060605030c07 65
    0x3420102c00310020000f440070b40310307100d5105611040255101070503c3e41d591103090300710b0801d48548180194094882c1d241e404180d00159400c0501610403039080c4001c0014002040301449080c0c7c1003240b420001c0b0701e24125004210302c0c2c0103d454a4200380d001581070000181e0807800e2a401601c80500a52040381030120581d100c20880140c01c8409041000f4034040180940b411000d44008550076101da488258071644240202000700d8007007a1501c0e58078000d4500b10100c0342140e254003102241d0881150301045080f50309417030880105d11800040103566030807125803069040500d0300e00030304000507400903074550101c4884000001c504039850542c0b422a41001014542001c29100c070300031405a038030410554640d019014a28011071140f44612030350340181200c0030341042d48000d031700303000b82c24006041c003030090080c56584a96405034010b414141c840104104540303d001200550002c040790051038000300c2c10145003410900113150414103583d00a14400315030b070303154481 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 909256411 1250 909255161 909255197
    0x10051203031302190803030108060c03071b050102071523090a031803081306020106050a0506040605090414160207050d0c030b0c0705100b2e050901030b090a050403021b09010501 78
    0x910024192134000800d0003050300c440000055049920000c00c849103a07035107203003084441c082074902000041402041d038007101e00b0310010401c500d003c0c02c0014a0164265075030101164014038101c02d09032039001c50551148000c07005684d84000f1081090319140030440d40703445d00308600c0d0081c1030080d0450a02818170b4407030380040c05141e010003950398640c0070207401c12020949100da07000660a180c40410a8141151801d041b900041d00003410942031000640c2c2582000b40c4480c0c001e9919000e018080000c1c1039407030702401c91500380d910a00e100c0403000741050843e4021078000c101203005100059205000d110440c0c8d00100d4410340f544850229001911520318050807510941d40718035000d81c0345502200c00300c00b007152410711481e00a606a1010440260504881800c44c030003000d005001c1c100a00560b2014580010365800180020b20480e5041d580c0d00e080543d02c00c100020540c0400000800c440c1020492912010100008860311014001c2c141041501080408080d031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 909257661 1250 909256411 909256429
    0x9070b070c080d0206060901060f050d0c02160315180c050d052b11061326040801020406031d1002180d0f0c12051506210610051203031302 61
    0x10450b0261003083d001e0300750003591842e06480c0e03584642051000004c80ca4000d2200c0313170a0310225291039090014020544000f450038600745400d42c014400a6a8066008614a030103184910401c140000780441000204ea918612800d00340b480c0d0105000400d100710301c4d8504903041140c8140303c0414a14103d41061002080d084010400c0e0145513900302e44d10721202100b42c1180da0342c0e0141c11000c40340035501c08060300c4404602806400380310119002410407030303028030320205c810308040000380d040c07440da40283c2c04525079941c04541404004d42c10b015400e00203000914504c80071002c0084e080d242d02050326a1850158000f40e40c1d00c500300b02c00f0003243c0d500070080900d02d0070b403071034184007480c00d1700f0032401c50b443c021171840031420004079590420402d41000c0180456207182000c3c000000000d400d495100c03a50380000480148001d0004003201c0b0300d000a4440e90416000351040c0c04404c5e0400751042c4e624014200d10804000700790303a404801c003011440b8130b00700c50000c61600d070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 909258911 1250 909257661 909257669
    0x81b0f07200901030c1d04032f0d02010906060905070519021002070503090f040c05041a040f1503050705190c0215030108010204030b361c030b030f0609070b070c 71
    0x20302d40000800d00001005400c122068015040424141010f01e040c00150854005021800d911010320120f030507180c910301c07503144801c3c1507401c10b10b003120301a20f4900120350000060303449031825000c00005000f008024083d180007032020381800d100c0900f440c0150a24100300081c81030380b48a09900c2003000d03100002c104642195510250f04015480307a20408483e8080e07922100400998289446030300280903103551024245820888d01ca501d0028212540c4c8081c0e9091201165000c80080d044005160800220302050f4146c2006404d40d40b0040441d401d010091040448424218a40e250451814545010007402620001c0c202050107140396080780408000442c0792441503000703105490084400304402d650398102e88070020031101c0c920f6106076002c4021451001d600380071600c800c1d80c120680341d00d0120001d0517401c2a020310062400641c03950003403049400d09001003030301003443d00064031141c40e0094809980d200036116003018038000103000424003000b806c0300c0001d4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 909260161 1250 909258911 909258919
    0xc080c0712080901030c080c0f07080702060f1332010201020c0a06050105030c09100504110d1815150b0a1407050601030308160e0409020a15081b0f0720 67
    0x80020b0600c40c46a0f0094900f581c0440d00c0c0440c42c0e00d00c54050f0400d00e109034681090140b403d100d4021501964101c03039011105501c051003102c00580d01c0b14050026030154585860701c80c080c0165001e540845d940c012602080c5000704070660741c003005024040b554007401c080aa401c026030040340240b240903d5120b050065060100411002e90803444c121041141116001400c40e800c0260000f81500c404410381c0001404101d982000e400c02655070503201150350412512088602c01e59540041000f86110b0340c0e1085002c102c02503101c01c070141d0b0580c0741002079054501e00d040040845000381c2c1c012000c0410305035161407094240240380b068140f055030300c0305000c1c680260340360000c5c00228007003001c0400044030200401c9a821400301c2e15640e89060003c2201800021b00d001c1005030382010074060085155460082c040220b0341182d0b680d10010701e030680c0c10010f00252042d011404400c10004820106001c80a807103185800400c0c1c20b110a2020b165590300100d00d85200d900 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 909261411 1250 909260161 909260189
    0xa080a26120403020c030c030705040902040207140a121704020409050304050d110a080c010206040b190c02060619050d150204090509030a0e0102031c2f090a090501060c080c07 77
    0x914086030070001c0c007a41c4207800b111350f9001d28000700b588410000001c160560702080007040755207002d40101801c0b6001500062500340707036465650365400e004003144181d0344808100000c000120140ea0401211403a09803510000c4a100d03d801c1000a04080d208030307201c895036000e110050045400810000340701070241c07111031411410600840792028402e0f02c12850020315060045010401018168058902c0c0e80d1103035243c1e90041d40c0507111001140744d00c1081070f20030540d44240d1002421580041c41640703004400c0002141e80c43c80010103403841030400308400d844500104000725403011418008201246a51000303010b00d5001454450801041c0150103102000a14403804180c1d10706415403107010040e6900d02c00c142c0c41c0802c2c3da400c4c54407a00841141d50000742080c2c820814100211404911014a502e5028184021401c0090044010718251803588000c3c82100c00501042d854008003420b2002c016402504214001030250380c108004e00c006806810321b440c08500c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 909262661 1250 909261411 909261427
    0xc06051803030a0c0206010b070c0303110c0301090602030a0b01090f060c240c02120711090405010b03070602010501051908150709090e060f18120c0a080d0f0b0a080a26 74
    0x103841c03a8913400000d8081c060003c14031016401c1120449071f081003500c00c045103190780480d805900c0e03c07810b004500810103001301c1650280251110b081c001c0b4401368803810104808022102e90340074040c18000315030000c1051030390035144079003121480e090000d60a1801c0c148218032000c0b40c1070070704411302d24113020042042184d220765940304003036080300c83c800241d600d031908600c2105009001d00b41c09160064003850540ca025074044d200c1c000206203000b80f000072919140041e000600540d442e00010300c20b82c10443c3c001402c07100c4c1500c02d00303405031904019580740c82021030340d00c0910441d64005962940a29022802054405000c214403480c0a128988a003401d4404140144100e008a410580324110346403441000102030070031224486402189079106c1c0c0d0f6014442c0c043c0105940104003028050030303050780c0070303000071501e01c09100c403031801ca820041d1a03600c1500411000d100d01c03900001d1485c021a0301a80080d80300307540044800c40c69400b00d6044030200c40010740c0d60 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 909263911 1250 909262661 909262681
    0x30206070c03030806220b0f190509060f090103150605150415260612030d020415050c07090e0309100f02010f18151803020d1407030c0605180303 64
    0x240449001c4e0b6901503580d03c50504111800c211034000400e4003141c01c056008201584d8400f40039040010100403400f010070011a1403010340400c40c10102d500c00d0001c000314101001c045502000031102840c16510b03540c000f82d0644d070107002c09004c03a200300e07801c3c502c1101907921800150800030801b0011403140c01d9180c000e64001d0003070001c0326100d4a1801c81c00760003120346542c8038111120410850552841006040e03c006085c2d55120040364030303521103141c1c148000d0032941680f110241e502c0d420042c030582c1003012142203e007086003c1240c18a00c0001080c110f0030707150340e0781001c10030600420360180345001c1e68000360345c003030320007030a02032960341150f9241e900c000190000d20440040d1506d050455901240000b0010311560340d1800290031000700c00c41c0e40b000c00f1000210303a45400942803005130501c1045000d41c1c00015007252240d0030003058040348107400a060700d0045103540003071014551071401010b580d110000303d0141440d500c0b001c40010b00c62011a501c07407508201c0b071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 909265161 1250 909263911 909263933
    0x31e0e07031101050f03010e06012a0302071a0f070303060b0f071505040c05010e04060f030804060206010b030c1b0a0530120c03041e0f1101020c2803020607 69
    0x40b546400c02e070b86038958550040742a1034070120b5004000e030842e841c0c00204108003030001c0c016030402c44032441c414424071315030082504400c00d60181c40030007041464040d140104a400c6000312848000f4131000d01d0800104542c0719100c403444003502d03052145019005010b070342e0001c42d100303607001c20300d2600140d656000e4070406019040c4250710083c86540c81086030070030b45029100c205c503039070103000b02d50089591060010300036100258495484411ba0015071f80c0f600111400000050108035007a410400c0c0307409020100c180a1031800c0940b1001c02038401c8032405200003480810900c503440c1d003400b45903107071034000050365034250042d00c1e02010203461108200c180a00c842882020702407030026a12001e1610200c0000c980320000900c2194000401c22120344031a4801031036641480c4800c201c5951154281e407041d40c4c103901e8042d00f1000d9490b502411548203e0140e4130507640c0722800304103181d500000c0d51900964076418600040c003504069045100091403c0410100c0000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 909266411 1250 909265161 909265163
    0xf070f0203030f040905071d030604020402180d0c030201031428020f0c06160c0b18011e0509010b2b05010e0a08070b01050402031902030603030d0c020a0615060906031e0e0703 77
    0x107030450720101d525404805940b091445402d6404ac0300010b0040c02c259000340a82e02641c0d0908054001020025506090041c42290904050070040086503007502540003110b0099100d80c540d803401c1c8042c6950003180d04080d130940780f42510f002518400750750449540310010200903655030341502440750f55501c141e82c1c0240302825030342800c10161182c00c4048a04e03078011084c4486890704421400558841c48814a0555031440480312901c240313129108184100c01021030741d481c0038280c00d03085803c100c03103080c026a055035040c0c00c1c1c003450011605050100300e4042e44e942c7c0441c10500d0040600b00141100b901c507100f402414409040050144280310f071003800c4440c0c1c2c90388140310981c002500e4110f08001c2c04030040f1000800354020390740c024806021241888003002c900b034140c0b01000b10500260700807403031100c184656401800d0707000945030700d2024407a150010080c41c000c8984030308001c00d07a0341c401608440b04010443c0c09060040d50707060140200ca1969140c03181310901c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 909267661 1250 909266411 909266417
    0x1e0602130e09151605030c04050907180906120303050411120c0a09150b0c0f0105070c0b0702070b0d0902033406082802130b040503120f070f0203030f04090507 70
    0x108040d11400751540b5184601c0f50040d551000350005001905c0f03c2e000030f021240c18150030f10000c2680d840741c9003205d2203800c0030799941010070594003020100c45010780002510301d00300036051200c10015400c0700c0005606103070008150341e49040a17440c40c141c0d0001240c0c00302d40c001c003a040c4030b0400201c14810034400c43d40303c2070540ea03400b40c0a040301c6600d410070108241c1808200030305680e1b070020307081a00c0300506440c444000000c101c1c1c00c540c030841d081c0d004515080940800d0054255101c1d510803440e0000b00003140c102228038845000e10b0710a000415140d4103003008540303050289414580507204130b41b1161b0312401e4034012a06000380390300d00c0d480e152070000840300d10841040d4004c00300e00d010b0315003078154011030429602c03941d5510300300382d502042010b298130003500401c401080021441500c0300d00b410100f40c240b04440c0001b90802e807060008141d140b8001040790001980448120036400891002c40d045008070459022130043c0494000348030000b6400540c0718405503a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 909268911 1250 909267661 909267673
    0x606061106010510081308030a1a060a02060a052a03060f010903151a10030f0f021206040e011407030606091a03400b10031e0602130e09 60
    0xc28003540e640091040c03581c88a03880388a48a03a40c003400d1400c0e000000c211100e10031440355190780c3c4d03181d03009403001e21141d551144c100740e00118210b212501100112800ca11300b010300d0000139980c05010302100d904944d59400b180500000c0c4040e050580c2c044100c0f0710030f0303d61809d4250f0540c0c20845583c0e01a00307000c00071545540c4949000c03415282d0000c0940023102c00b108110004048069182e0607070038110744404100e5603602e91020b111038903550b01080d40f5900d05080015901c1130b1050b0015a801403040010860840e603200d0f5214105941c005064684102d4145c003400c004a0054008151403040c460a10307819004075003680c2c0d0036110f40852564818540c207000f420084010381110060000c039040d041d4091b400d02030071030f510090940d00502c81c480d02c1e00c60f281c0324007400c180070f15040c480d6003009100460194000541915200220300c0d42d10b58801103a00f400386200001491104d8200300002603054440d448542802c40050b151108030301c01055005940c0c40740d1501c541c1d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 909270161 1250 909268911 909268937
    0x81b060405060403080c010b1f020d020606010203180310140f01150512060a15111c020a122a02030f0c0a060c1e3008060108071b060606 60
    0x6142110100c40740508503a240516540355038002c0c1d0031503c42c12005548603880c2a4680e6609010b13040602d4004507142001480300d8000303031504d41d06084020030344d08000700b0818076070380201c15648800c49030080c984e0200c08190000c0d060000307402036280c0382440e02c105081c101c400d98000074071401c101404800240d0300c03284601090f803d1088070710f0004100304060740004005042c06508078001034291512262a400b50601c40c6071000344101c001076490343d0400403441c080108194041e4003558040884030701110094481990f160007400090303510544202c40b03803054505080c0d09100d039118009035000d8141d0140f03d40d01d00c50b4241d10078031070285008181e410105110600c0b01c4001d115403801440c0100540f801c4a01010603512100348101035059081800319030640a4410202c106d1040f40d000340c8549240c0c110280c2510603041074113010342c49a041022641c00c00c8090801030001c3d6140340d402c48502d80d400704c00050035a8a1481030040040783e40000c420f403582038441c490403280c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 909271411 1250 909270161 909270169
    0x170a0c0f05090c1c05011e120503030a020c030d090f03030b270703020d0213031b0803070618231002090a14010c020d242a0302090a081b 60
    0x1500900b580704003894003081c0c011040a00504034803c04001c1d038000002402c00e200125402607200b94126820320706201070024541100304041c00e400080d04640400e04e4680a40d640002488090000e500103841d0380001c80800964a402c10312020500c403410790f910b85120355003030746101100447c1c10f0078540002890880049900d151007038440c0b50300a0301c0700c1c00d40342c0d03086806404242459402c22a03c401c55086000910000f212100144226840d500d40507076204440710101103048814030051100700c01c003004650380c1903008180400e40314541c0ca50003d9900a1003001050980340d09040b11220349003c4440d050410390f00c003a6007825107150604407d91041004090380100a442c0611040c50308103100000b014044c5070403030718010540e011441405007080242e0321012142d4001c1902e428241c49090101c02d0711300140b042412071140000c0250f140546140c00707940b44804001450b2003a4184c40451100505084d003496640361620307100d0310002d00d0401030303000c1402d10221301d0078 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 909272661 1250 909271411 909271439
    0x30e1021020a022e06030f050f060108030f03150d050d0905030d09031e06020310030b150a06030504031202030109020d050109020c1222030b0703050f0610050a09170a0c 74
    0x14580260500c0504040c110b08103031a44120200034500440d01514854000e01c11352010311f11031580d186040d0f005080c458501040f0b40e85180300e650160005002c0c1102c0802603a901040988510380c6030b07141c0003200c1144101d031121981d0400b211400d150b0a1290005046124110a44582c500c454840c01070544941408003940c01049896204000090031040000c0c44a50619446003410320540d035244180e03031040c2c1c0c00789403104a8060034000c1c4071b01c0140740350b00015802281180d2142c464049400d0b40c505102d400141a510030003d414940640004000306a90420840d81e941e10390000000035040300c4014840a4501000811489102d20071030720b5a80c102001040320b0405114280e05a034080100710711040307101125149010391a10603400914840c0020f03282c02d20740008018101c4000034000340c600600c003000d02002e616014003060740903d41d450100d0f5102084602581c9401440c5d0204004400284680a030000042180c094070f6203d80c0d400d1204958810340c41c00540 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 909273911 1250 909272661 909272677
    0x20604020906010c03180b0703020d0201020406081302060c0a060e0106270c02030c010c121404020a063005010314030301060e04020d0f050403020a06062709030e102102 74
    0x7203100c00459401c0d070081c640440898402e1408440b560f00380e03002c0d040b541e08a41d1043d00d42e590041242010140c040c00403914102139407000b1400d00b4034005000300010b2020b070251198000d66921032041d03444071400c0b9011070103603c0440d0038015079440c05900804003504c44a501c0d520b03001c404540c141101c881c4000031620034000c046454282c49882d0000d0030111380140a41c0300400050400003004e01810307405100d140c482100c8009514000d500352040141c40c01120b801820802005995083303401064807040e1030720b05c94203403000c200e642c0f01420320a07922615280c29203900b1800e0b14240c01c1a4140ca00c135011702c20070354418440d0166240030038022480425851100c2038240d0a0941c050074080190036008581d00c02e141c0e10034011030707005407026001604484444024481c0b103004100041841490215003202c00050100100d1400841c1c09e600c152940760217000c4c10711031180c4500e0b100004110103a44100502c01504040d440c8014030390007004450280c851034428401d498080c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 909275161 1250 909273911 909273919
    0x114090303031008070909210c050a05030a030f021c0504020f040207050a11040b0a0918020603010617070912061a06190e031501050d03020a0b0a0f061e030209040501090b070e010f02060402 83
    0x7800b08c001c0104075495154038202040f200510324404034004111155000e40140080c6035991540e41c0010701b62400043c001c2c200d0313401000390707131042c20025249a00c5001c2041c400142500c45100141d411011211015445800891000f0600c00c0218030140c1c01881282c40c10720916202041c0415031707050001466025590388810443d05403542c00410340400c00c030b201c12507402995400542240c1081c0c100800040c00841c604068403001032030035400890328144044a41d1a140035194030502180000381100d80703841001c5c0342d4281c00000068032000082c50719465018005002c03c0900c80c6408000020341595411b5201c0c0c10701280310b40c4130403040e8002d2003440c0e090509000c40d00e030780c00104504501c18209802c020651f10445240911501107020a03103030840d030f9003001520b9440d00f040810b00d09240300703071442d4000c0c01040000c413581a11208807581c1d8074206a801400a118050720308a6142e0403c00c45039880038040c0a41c84090300c2e01c040812600a089036142c01c210707002504 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 909276411 1250 909275161 909275183
    0x1b0327070f0b030702030c010212010603051305100e0705030109030f0f08010b030f0916030b060f03120405191e170604110103020f0d1802031c0207050114090303031008070909 77
    0x41900c0d400c003d5030311001c03d00440c1c1c6000307100d020031800ca9012040045a040c42c9000511017264103002d120b4000f10041011840c040903602d40c01d8030303a90b01d400341410b4203035110243c0e00c2c1072009103c03040041c44000d000f080100840e040292a40755144140000030700030220704485035000300c80450594001828850035542d0f03d98410342a603130040d114581c00d00c10043c040c4503507903104001c1d9019600c2003410345450b003005805d12680c400d6400d451440794010030403140c4c0e103031061415a401c9890884802296400e4481e041e1041d81090704903070000400d001040c103200c0c2411345007008489581c00070f007110b0b14495004a480e400166001400003071100c40009441d886078018010181d522a9224038000300c2c06010002c0b910000724000c08154450781c201c05519042c031141007070050240d0303103103040740c2c1c7d50500035211500ca00131181488091242c0c40c190074041019501c003040003404a941c0e900300300c940311040d81700384e01c180c04a91140c0100441c608050340200e03492164882d0344982 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 909277661 1250 909276411 909276419
    0xc0f020c0d020f0405041a07050705100b0114070c140a05060d1a0613090513021008070c170304050c030102160209061206070f0f09030c0506031b0327070f 68
    0x18107803210100907a0b00c104191910040c0d5602c6219490240e0310610a0215000c518001d10300d165500401c0401441424042031022440c0450b1100780c5e1074260100142c001c0241005030344003440842e0740320714044013056500400c812680e10300f0580b440804191004901c05040041c0c5a0050080300d070000418090078100300c0c03854121102400548840486001070725000c91003940041c203541550815140b010010000107201c0d0b01d03000100d0b03c654003070200341900401c0000c041000d00720101305840c800200c0d2036101d5036903060314a030300c0300c0c00401c500d501c0d511000081e00252400c0c2ca0300e001d0300745c0ca6001d500c0c0c14030880d00403445041c0340318034040712502001041003000b0001604502c1050800d2100003040c0540e5125420f540c4405030704002c0000b000b404c02e11300455100c00d000c80444140046449107401d40d040700c0040b51801c1c0e80e030f40e0f081c5004e090415a9044c10007544004002d0140d4941c00c0081001318812080e45522450b411810041d81c42c850b501c5080700a04190b00240 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 909278911 1250 909277661 909277669
    0x50409020c01060503030a0504061418060d270308090a03020c0f010e0a0303020a1703041a040f0b070f02011a060f0703051c050103060b01030506150c0114010f090c0f020c 75
    0x20700a0725140005042ca54400200781558040801200000c00009040c0309881c1c100b0105e29082040884c1c150a10751a076150403141880710000602c50350001c64000d04240b030302d42107290440b0800241e0700081540c00101000081c8003141200400e00c500d000610221000988210715a0540e0003000300c1c11034042031109a0310401c880c58100910a0f400c81d0710340c0c8540c400a801540f00760b00420084404e4180450b0503c08071280c16403040c010030920020807640c40c058400303d00f400c0d46c0c4205070384651814042c0c41c45116001010014482d08016016400c00f00000305003c043d0002c2c01521441c118180014030400301142d80007800b4003001c000408050003505040e4840e0500350b24020340702c2049000f010302820720511803500d81c001442000700b40d000e016801402030805001d103040c4107002403000744940c41c5000070b0301c501040b60360f041202504980310110348a448403060396143c0d021030346078036054020001d05506000629404520403106c071900741500354042c0c002e45100b10100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 909280161 1250 909278911 909278917
    0x30d0618050c1306350f010b040b0406031508010903120f0c02060112080c100e100c0509090c1c0e061005030604060c14030a0b0a090b0609040905070323071505040902 73
    0x4c00c041d0421030005100110174504000d14030800c2090300c402c51030b20b41d240003490b210507040345411103400d000400c05500c0300d400740c1301940c040741004122010000610030140609a1000d0810b600306801c0f0000d240d000103038014241e061007030501040108629400980381e107005001c0c0141e00c40720040184440b09841c07618868402e0034680e140090340c00826107002c42c20a540340c0c070941e0f60795610304103080c1000300c5e60079500640e4041c4181008080c014109000b0520090302a18150380002e01c811000d41c00c8500b0421101c00e12000e440101c0d00701c01c000c01003259404468400c00d40410011058605801c1c22114010014011955190348440143c40c3c102216018009421089013030346c0c2d42031740034506c0340803400d10001d0040322201c00c0000b105015030040c0d00003031401d8501440750701c61000302c641c550402d440c0032552a40d24039060745041419400500441f40300c441001038980f05107021403681da0131401322504030707031900294129046041c0c01c07800420030810007000340701c02a03005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 909281411 1250 909280161 909280187
    0x6051023060c0610082505011b050f0d03110301050603010b0f0702100c1a06030d030b0307030210032901080f07020114161b0203030405060903030d0618050c1306 71
    0x40c0794244150a50741c2c078600602075038034800e081c08003e41440140020490100d20b00c3c8200b000f120715210394513400610700890302135581042900407184440c10034104942807038641c00000ca4400e1a42c5c40300103a12041610f41d1000000c2c20980c40d1001840c0c02001c0c1c0e410f0f2035004008510b507034a00404001c032170340100400196960306004102c0545c2e11080081903a8005403034011580c0c996241c9465581c1c2d501540b0b08186462509000044d14001501d075141c156504001440442c00340c000785c03901d0500d40c40207510604140010107003603495009501407100c90702c54601c9603191509a03030820100381503558001811800041d00c0d4102821400b40c0162450000107095000c18a0f0094030364000c9402c0201d1480c212100700103642d128520991022040c0641c4110b00340320383c0000d81340d108a1003400d100d50b40208001d00d003a81c080c01254107801c08503208000e603c0e0365040c0080c00c5000c1b404001000c07494500080c4402a00380d04840710b540341641c0315000d040c20900103944d12602d02e00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 909282661 1250 909281411 909281419
    0xa0b01180305160801060f26101e02070c051011030c010c180803031f050d03020c010f030e0304050405040c0803031603150501120510260607050a0f050f0d020d020706051023 76
    0x100c070301007084127100c82d204e4400f250001241e601c070800c0101c90704141c2106000200351040000e00081b03451031038004161030044410108059170070b04101c3c0c80c0c024021001c1024000094034076240b8505602c1140402615210180740b50803c40c045000ca0007144161941c0c2d030000c00025050f082c8001400700b1004280d640450001d881c2e902140b0003407019041100503901407803194510f5a00084511400c0c1890300d018801c1c040700380365203610390069110320350089865002149c00c200074010844040c1c4542001c5984a140213804a000360301c206905001080c5025503180c9074007180590b1038240c50b0103869401c000500740600800600c40245005d0003054800804907900514503511000700404003018550601c1107424641000009842d803020702c60204124010270350007201e020040e45440c10010f403a20728000c813400361403181d010400412480010714200500c40395000d00440c9014200c200442da448041400390050540500401e450440c4101c1080390051813040d80f0903040030b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 909283911 1250 909282661 909282719
    0x20307031b0c180b0a21030e0f0d0804030c0e0f060d1122050f070e06031f0f060f030b01121a040509030316050f030a0b01180305160801060f 62
    0x240303e500d10b12035443c2c01e00d82041d00c56104803200d00e408400c20001d00b2034034916032104101c040c01c042400c0100034006091001c90700d5000c03038540c3d03a060410108240640303401c444103c1440c0010090f4894001240c0580b20007001145119541c24558411900282c0411841e10351404003c400b802000c01100c4451110203814556110800c50700c0040600400607242c0c5265110f55030140c03240108050340000303000003080300f0789a00500d8690f02c2c04064070030319944e4407403130440c1c0c800c1865102c10400b00c041d1001c0000d4046000c100d00000c803485030380c4002445240780c00440a4400c0668454001480030440d11103d080a0340b08008507031490719002441c040040105050700d000b2181c959450b080401081460180c58850961441003490704030b1603c10580c1040d9458080070b0000300c0c040765146041101640500560380c201c910824862046554900d809995131a82d059180307840150f80a000965036814041c0106540c0114450172142c2e007400018803414141c0086968404805 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 909285161 1250 909283911 909283919
    0x70308220501240b03091902060d1404140f071e05040f0c0201150e0415020c06090c040c02030c070e0a0b060a0f1403090d030c031b030e070501020307031b0c 69
    0x740310329001d00105403032143e90040e002940044100080d4040b0001100410400c00d2032900418017600758801c000000300c20781c1c598008112207005280c3c80c0244280b40908003031092a41040c00f034856072003440c00c2c2d102c20410500d942d4581ea000c042902c03144e40400e0060010210341e0880d801c841c00c052010303010380c0740d81e800000c0c2a07501001b02c0a60702951400d5041c2c800c0d90a0040c504481040380480a00e2031038007a440310300c050000c0c40600501050050000d04404a8048442448641e01100c04609000b040c030341d156a5200400b030700c5546403480403400f00c0d0011007139a00c200d80c1103000d0300703120f46480410f041c034080003044003006543e91040540a80d40e031030007030200000715541d184510407255001402d0750602d107141c110089824010040c50007000268000321502c945000328044000d004281d002c0d200d0310300d41302102404200e0341009254558400c10f0601450001c40e00d64a075902c2c01661030b807281032070142c00a15011000c01842204100d400151071040300200c0c2d080c0d43e6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 909286411 1250 909285161 909285163
    0x6040c020f0a0c0320010504060f020102090907033e13030206030702070f060e150d0f05010810060504140f0c160c080f07180c0c02031e120703082205 66
    0xa54110f40b800c2c4039940038420300450303040740f0000c1600083d400c40010440c00c00039105002d43d1140800304002c0760001502c06100390181e41c0c10000251940321a4101003a000d0041c011440c041c84200c28808900750004031440e10a00b0301170140c100744c003074032a1881a02d1744e09038131900250508200c5042c00000588542c0000c520504c0c81e40d0150010f9400c1060031440c00c00d040d8880c4007086414030440c1040da50301e00d001e40207145918080790381c80078240920005000b50080074400180b5060002a4425011400d06d1009602c41800c005182d190307020001120a00e80d8210b02c3d061621000942078080d048034a50000d03122464036050032003c0b108201c00c144810011034441c40344034002c00441e84108150f45032034400d04060f100715424040381e58490b141c220209102c03d622012048c6181d40180001409960003a09484c1d40343c005441a2001601201c03240610384202c044100104c01d422007520704055055544003160b850b0143e108010f2000b1490820b01c80c40128484400910 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 909287661 1250 909286411 909286423
    0x160e19110406121b0c120e0f100e0301060303030b15040e060907050c01110403020f0d2a03020d050f07120f1709040e0f06070201110d020d06050603150a09060302010806040c020f 78
    0x80c1d9541d10240701c845d4036040480385100840780e000c1c00030605e6205219039400f0307040144100705540321150704102e69011984120f41381660741c3c05d5482c200004c0285603058100201c000c10a607840c0010407040b41d01c3c1c0b1414030461081c1580140100003007408d51074180038241d00444140351940c1000403504c1000e084a4030107030b004401d00070000b41002103081000f0780740303440d0404842404001c2c580c0d440b0942803180d00030030a03111052080c0b0a840c00c03818002900041d58000e8143c0c3c50032861458150351750103448a4400c0702d4410b03040d0020302c0300318007004298030580c01898540b00728561f907600b0710003030b03100381810000c1c4405004800c1d0070b4440d88203042c904808600101116944004621b040a901a24074004c590414040c11030ba801560700b2100e0b064140032005135034080a24010009102d10340140b540a1000801d010288800d40401010380008681080d440c80c0c1c0c54050104961712880024040703030800d000100709141c2a8080032104a2600585005408601005007010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 909288911 1250 909287661 909287711
    0x90f1602032b1b050c160e06010e120a0c0e0112020303040902070503041a121b180a0b13090b0105071a060f1009031716080309160e1911040612 63
    0x141020a100c50781590800c2060301c00b0720415488440e450501c0003418403224001c22070b0341442811208ad80240e1110748082c01512001c0054440b0107500703103031480707a000d054410100c85c1e0309a000040340a0610407107000915500400551078240b4085003a00650450f0000f039509000c18000000d000c07081441000281c908074403541d80c1e500005116060902e0080c0c066040d00d00f144041400f0070740d401040b01d000c07000a0b044000c0810035240080d00d6080c2680000c0c02d4050049110084600c00e440303401d00745d070303d00402405000940e00044400d800744030400b40800a9003066016400c00030f01006421a00141c90a40042102c00c081621040207503548400107071508e90802c14001d003298800c10902106110515100780480740715444800d001e0081c05013a0300201184ea0324104222106010182030140000c4555850302c0d844000705c01c8581000304e1600407a0169000400d100d0f4040301e00c1c0084045060074181541140d25a400e0091010059aa500d0a441552107070307030203120704 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 909290161 1250 909288911 909288917
    0x9021815040614040b030c1c0b130e0304031403210601020a0b06030102091002060a1410060806030307050a031e111b0114030a050a0e0f0613020609090f1602032b1b 72
    0x9007282c12500000740c2580d823282007824600003607841303581e48421003102c5030b408022001c60504c00b140c01d00e50840c4242e074002402011811103007141450040064900c0381c8082030401502462186040030700d02d401c407080341c01600842c0e0200c00042d080c1008030740000c4090300041c1002004c0001c195a0000c42201102603405481000120005401410a0303500500e1042c1d0311820219462000340c115406440103001c11031000880a4608200355080c1d079411400710b440300c0820b4100030700540061000380c51100d20414800e00d409000b0f002c45c0030483c0410004101181101d4915480e4000180e04513040140e9407244400d41040c600c050740c0290f82440001034541003511210003103d21441c11216183c1003c42466109500814001d911542484003100844e40501c005090b501c1041d41c2d503944041070b07409214008001040441c801d020840416031040b100c0322069949014400d08183e02c2004002411103440c0ca940c0305003c284c0034200c02050205500c5601940e102040c1800000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 909291411 1250 909290161 909290167
    0xc030705072a03170f0909040515010e0105101d1002190501020c0c01020706090306022b021206091302010e031606051306050a0806210709021815040614040b030c 71
    0x1480002507100c804e0201c0c1e0910607280c0041e00e50800490b005461015204140078030002e014814140700c442d030b050300100032a03000ca40e103508040303d00700000e00880b40905010644980d003a40500d0441c440840305907950b0b569800b0190400001c4849580c001c2e086002e03400c54003800b00300110003c0d07221441440050f031102c000004440c80d20003c00c44450444d40092010440150010a10b405413608401c01582e2501440103071320501070000d00080c50ba001e0b030f44104100c0b62382d6501400c20b01c1c2c100460211292151020410380e20320585140ca1001405040e010041d8041c02007156459006400e84007410301c0c002e403150b0410159801640171410005405545c018103076503000251045040c0382e410805219801031000070300501c01c5014850381d520071400180b1225030034006603d644211181c07151240b04200103904441e00c80a02c01c0900c030030302c0f0907a1400394440300101040450300d41c102464a442200d00d001c000411420102e03041102145202510005600c1501d501e840d8640e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 909292661 1250 909291411 909291413
    0x1609090e03040617062101020720011709030306060d110c06190204180e03070b010f06120216030c020a0801090807031d0f040c02030421020909060c030705072a03 71
    0xf03a101000c144113058541c02d0420003185e60318040700318140c0f080809060000c3d040c144540c024032401102404400c1c0c03004c1d00e043c0c0f08003987c070300954512003a41d03000489003010500000407031045c0c500e42c2c0d454000380006400b03418107a014045000c200c50300454840c041c030151410300d43c8024480c0c100f40d0064410844000b0221040510042c46104210318003494441030b040c11100391040b000580d0340ba60034840b030400081050341c4c82e00e9045490104103581d03540302403034402080c0c401c80d000300f032a030545414964040c0c400c1d41c14907004000310b1503aa02c942c1d907003101c2c0f03400d1480080ba8849071f90000810810000d200d4200043d11407507415a50b840e0320b0601804608040800d0f0401300c48c80e65511906480740c0c5a1440159803d4401081540780400d06a003580030384d80000d4101a40280640101c022035120340300307418020344a0074101c0d112800015155031003120b0809c1e0300b500c2040422402d5109000500c8070902442020126114100112004440714280c4140104084034280 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 909293911 1250 909292661 909292667
    0x10906030210020615010c1a0906061201060e012c01081f0c3e061b030412050d0b0a060305091b0a0605390c030607081609090e030406 59
    0x81508030540018500751920842c4c004080b140da9050350704100c1c3e10741d40030701000b440e507044880031a0b4230301059030b003850081d00a5580703000440300240300e12000191941c10741d206104050070717a24001568001d981c240050781c03811420b80f100f4101c4c002201002d0f60002103000c00e000e4042c003810800b40134009640c0b10b02605606440e01c960700f50030301e030005820700c01d40c111401c80d003490000b03280500d08003170341c2d101240c40e85200d41d0b200c0001304451614044054010071030354413070300c090740c4204085520b681c403404d00c80c0000c80b001440c1c091410102a02d0f80d0084005e00110005c114011688032402d901281081083d40e111300b0100703894109003c0081e81c2404190012141c0301c402c0c00709100b021b0000380700e08043d84513102c02d0100c00550704580c1d001884500703c86c200c4908582000111380d140401d0300005e41a407641007030140034144041c0b03103004101b10b40902c3c015511021562603a443d09041c90003500c000d0300500400403000180326015000c0c210300116584065038440e0700d818409 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 909295161 1250 909293911 909293929
    0x120d030b06040b250c080a0218070e0d11030a0609020108090a020a140a0e041109010b1c2a08061305160c2907090803031603020315090109060302 64
    0x1080c0708481c103200a2140d1640d50007a2003036400c489007140381000320400400f409a600f61809400d03000254404503060a0015559000714030a440d502d0490b220b031f85464030840c3d800d0790190b00041940c0b81100a07458804460b425513400b8454a03803002d0340190000740341150202049800985601c000700a66800140181d84403507224090320403142c0580c00241d15146034051200c4440e13040004c41a0750316224140005000103a45521407800c0030b06125507400d902500c00c40c45145404000b19a80d0313110740c00d4a811098201d01801103d28240382540a0b00890203610400c01104541091420302c4000c0c1100302e40b48d68480c6000d80c1402400d120000120301501e1503901d05010500c2501c209950b080040c20004d4600b81da940107842c504a0781401031418103e01002c2c0f110718030440c8018540e450350003480141c485070b499544d658609a2203000480f081c20180c0c00c02c20b000310016004e41c0065131310420891a0715a140740541c0081c0f903d403400e03001400d12950b00c07007085c82142000b01d04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 909296411 1250 909295161 909295181
    0x103292401020a0309090216020d061b18051512130c14180405030405030601030503180a0308070f05010f0f0608010b0904081c06050618010215010815060f120d03 71
    0x34006a06036514060881da82501c06d8a450f84ea0000f0101004070006140e140d05d51341c01002204840802d00b00b40c4090000092100e00030f2508100b0303440c12901481c406c003110b51101003100c00d410301c0c0104111a5850440172440d42d580100101d4581c03905540040c0c0c41254002c0301e00010b0007a600340842000d01c940c004605d00c10842c0714540c419922583c801c59403038641c0014000584d9517203811411401943d008542520889002204005002c809401c890221742c4155200703060050400c0700c0d104880c0310240005000b00700805c0424540e444044d40345003c0c074004100001c10400313800c02c859085510354009541c0f40707010b00c9080c0e800e0140d1217501000702c170084401d08080d26140c40c5d0b0301c80d2603500d52020900b03103420400c41c0000d402c600010040200056100c0c10301c001c00c41c03078070030828608600502030f08403550742c0a41c07034a20840c10f07220142e00503c600700c081d1010750689a00038041c9588820038000e103600c0c1c1e50300c4484001c00d00c0c01c440060300c915410714001900351088010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 909297661 1250 909296411 909296413
    0xf051e09071707050901061205060402070305040302060c0a120207081b010806060a090b04030f1202120a030f0603050d0504080d0e100c03170f06010f05070b010329240102 75
    0x205109502100081480507a294644500031078500c960b04540703002080c0c0e22a54024800000000c0d80940020502031007100b880024040b079906c6500f00000ca00c62040c000340450418071061000d0b00b0100d010740400216842101d10020003a152101e080195110810045e401440103000300b0605005445606080c0803c1030140007908001034035031100100300b14003036140070440700900c921814410004050251505650b59100d0601c4e00500c2002c107804d907800d107140c20601600d5880054052018050000c185040410845084014000c40150001c50a480d0703680403000c54024410b00074140041d84031159268501148241085080380c4a0414414008a084980d4540f41251181c040c3c5034589940c015805117020f40e035039805100414442c10100c4100078481c0d0807501c00c80d000340c5090b2070300c0300e4964101008855501c00ea140003880180b08600410000380c3d684031000c82022808240c141e80c01001d01740b220202c60485d411591042030075000c040d1461030403502011450288 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 909298911 1250 909297661 909297721
    0x14090d08010e0115091505130e090601180b12010b09010614030f04031b03030903080108070b09040903110604050105070905060702100e01120f0b030601090615080a09060f05 76
    0x6440d00e550810502c10000ba10b881d024016138400c3c419000d5a000e05079903003201d00c0480100d01c00034142d8100d8490001c0035207040340082603641007014901d114072803080080881341c0c20701d0a491a000300701d86c11210107a4441180310b40350b50b51281c0c0d0421034015000002644100141003181c40141a1708c540b091004d1104607148481d0a10b0071240d201c401585c0c40702558441d0316085a040d0800410050b044a1100d2000d04051745074200e80400d45c06aa41d02c03a45907250360f10182c0f0b0380698030600ca030003642001460702504094011200150007800d000c0651074400002074280041220700301e84a940d0b480400c10055080316140c0c0150100b40d503e98104103190b4045801c030070640c2014000d01c2111031500100780c0c85503104502c0003200c42e905015030a001038020000d030203881d14840c03082c0106000402c8001c820321520342210001c0b1007407254002c00400a403031269000d08036030815078032001c1c8400440d815010b04100400c001c44001420318000546000784000000c000028507041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 909300161 1250 909298911 909298919
    0xb0406030620040509041b1a030a150807031b03050102040608240939070b2d0403121802040c080c030a2f1e120a1a0414090d0801 57
    0x104405c5512a40c440e40c400100e401980341000c03500d001e85c2c00b405090603500c107140044030035074001d1402902c441000780501c08548a60500c0f42c20340e80202c40035580f00100c100045004444800842d1300c2e5940d4211105884e9150182664881c1d0441d1000c5006041072107110140d00c00e501d8418922041441002164100040c00c210b40c0503044101807046800c4154a03c9108140381c100d9403c45155000c407860090082c035090b42004500303a545020345400500c00004082e07068103110140d100140b501d40d07810034500c40d43e182c040c0081e0308000e61040c034140711880714071911114945000c4004046d4100d4030400040c2c44c00c0b00288070400480d0028046442c18910507240c101d850502c011581c40c001d140c0d900c01c01055529207020611255101d00f941ca44110008c095088031013140c00b11603080e400380c024040c450310b01030b01106080c0400250745062a68050004c0c1920101088e100020400019050b1900300d001c10840392452010301101d044104070944001000782092049036242c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 909301411 1250 909300161 909300169
    0x1081c140903011d0c01020c0307030f03080c0d051014100804060221040b0601090b0a021213080307050f060a0908030c090402070f030c111516060b04060306200405 72
    0x2038035502109100458124003958084d04908400140707196508200c40810b0070280c1d81c3c5030a810181d016014040c103000c0e4500303012846405498120784900b20804160703404642c2d40f440108400d810341c50611400c1d0402046000d401d01603030382103000c400d05504100d5110301d000c001303007000e40c411101c0312820b0340001c1d040940da6a00c0f27600f2030302c010b8503803991560b60403407030843e9040244403d003120104401c00c800e94040c14042e003400c0c0d81d6891615141c0140c00c103d031043c800c4a00150b0f02007021900c0700c1d41090000c1152039105011442c0d550340e1090340528580012030b084455420820b26501d42020400c0080d60000170f017141400010415156003c036484003910200312400c0006401da515140c68048504041c0d014603003042500c05410014000441d15104482c4400f50140c904114640390888010b500009803416240c468a41c25400707100135084802c0314440d403034000141165450788100030055000350000f00340303c1c07101c0f0010044400251199500904144800e101a4031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 909302661 1250 909301411 909301427
    0x105010c150e0d05040305010609141306090c0306090b0f0c0f0d022208070b0712030e0f0111090108060a080d0f030b0a030c0905090a032a150501081c 66
    0x20300040c0032920500340000040251201d02c110720050710070340c07031500e0803a5030004c000d0044a0291008102c4030342c551aa136415685291454005400308501007000801a48120800c030343c4908800102e160b001e6a403180c407011070382d106071201656802d04070240140010a02d510500020b00e200092411082c08149805000b4030500101000314214101c10b1607541282c82d4554104070760300b85107003161000080c4220f240220340282c055080c00242c843d21400642c0c0300b96a00020205000c00a210300314014249407034614003030b2007101180091020284181d48802070000441941c07182410005042a40c0140046005950035a001c01c40c1ca500840d400f140c202c002d1911103007101d0800c0c0f00320007404088240960051041400200308201c2c40b0f080e9046428810b428021584c0b1810095103408000c000900810a80703229841e0000030803003400d0302c4004880070081000025207074800e060880401400ea09652070b8014040b49004000003040700c00c0c60709503010703035419990b0005c00c2d400f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 909303911 1250 909302661 909302663
    0x213020c0c040f020c0f060606070807110d140d020303060303251a390d0905071401080c0a0e010305060f09130311010603170a0c05060108150a02030105010c 69
    0x2580810184000e400912a0a8503510002c00c03e100040c41424840000c0d40300039a140e0040c414600300441404011911501c588002020103090001a481d680001c1c0c0c402c02044408450581c1c8070501036641000c040038403401070406e60740c008008010540b800c065040d200040d507200703200704031140e034000044642c200d1002040e04501d0902460351324191a03824002010841d40240701c0422070f04104600e48034a81c101203071a541101e280c055040c003040c0d00504581980401c00081c07050041da8000c00c040640207000084243c003549640e4104180390700480030340754a146030b0107025a070081200741c00c044403010017480d06119180c05003441401c45004d038185601d84c000076000d40c4c1c0b51140907924400240000060b8a0a50001001c01840e41d0045011510301c80036802c1108052003150180c0307500c203040003080c0e000010000410741000b6100320070080012460800201c0a100060007810310307400030185243c00c620034950014005001e4000c80d031042c00100b103180c0e481030b030440c845 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 909305161 1250 909303911 909303949
    0x40e0c030a0816021002210f0a080424020309010f050702071e0e09010f0c09050609011413081e032b1d070503100e120f04030501060608150a0302 64
    0x48141400120241e145218069441001060b5070b0780583d40210f044010b14012124030b00b01c01c000c0c039803184060302840d88100d200c1034049c0a00323104c9e00c2c02000c0c1c5076000303401801076031420200301841180038000c01089840568012090000d007003801d01400000505402c401d006920780004004c0d5122914403c3c100201501c8103918025240f0f400c407000a0183d0321408122841c1c041d240714040c20070140c481014030703e4400143c116622515140d4280c03440100243e150800c1e40d401110303600c0721140c4040d07403040c00b0022440020f100c855254020841c020140805400b0010400320060603124400c185030000c10020043c0b04003502400c80d0011480740303100d100240050050010b000d00010703400d10310310078400c21101c48400528401243c03800c8040300c074000d1762070243c141901c481d01c01d080d002e0741c0300346039884c0102ca110000c0d04105051440c91380c1800d613a51601030a45160b580301902058503142030018040c0c1900c00da0641c001c056174190740041c555404210000d8a404c004030707903 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 909306411 1250 909305161 909305167
    0x901031404111c060c030c0f0e0102100c02190b060a091e020a0e030f0715140a030c1403070f172e120803011d070207060f05091e040e0c030a08 63
    0xc1ca00303640801c10107250404005c002d0f054215001034000e100b001610341c042100560700c102e2213807241c10b400340d80d01c80690207880500100d51580020304103030758005055004003420b0783c4187c80700d81007032701460740030361030f003040d00e06080b4140110100c058100515a82c00c0045c46017030300004990130010344400460059890213041c40894400707020704481a41805030001e00e1042000c001164026507480c3c039005690000d11010541380040c1ca0035130b081c00c85506024540c0e2050282e40f100d4801c201500b03101407070748518022074410380d004030349500c0400c6001c1000c071060b81d40320300c1030414080c01284601450a182c0310411034140080c150300700c4020340000f141502128418144002c01e02010180c010030303220300e42004960024010f12038121614984010f58025100429010b42d8890f00940301e283c0c14038600302c9a170a21240a8410b0000c104162034454840c9800c000d80e00a0240351400c07000101c8040205492000615024a900c42d511040f2140d9011805256495100140540d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 909307661 1250 909306411 909306439
    0x9010509120f1209090a1107050703120207090b030c0f0a08010906291c0219090903091a0d02031f0308030f010603090b0a0906060504020c0102090103140411 69
    0x14040c4215038000e900180e18030148a80070500244109041d0b01201c2a00c90b01c0c1d0b201005401c66014844020f03510021a80105010307140799801001e444c1148030420f03150008a0b16400d00c3c020340303035100310f443c4001400740f048100d6060101d24090224a58103101800310340c00007a03a46da05111005100d00c025103040d810540d181e0300440d00405604e002032241030b683d41000402070840c005000d420400c0001c1e2050000030040303071488607140051050411519800c0c006a1400214004a80160074030007101e45034500211040e00910095401040c0000580b034002c058400325030002410008062054080f0911001a030342800e543c1940181c0faa074560020a0210211001070790f00c05110340804401d0081400003584074580308510034601e640e031500201c046804c40203020781303070045e0701c000301700130450030b802c511403841c012400815010b4807200020202d0748500d10030310490f9400640303040d10f940c142c041c541050071a14032220242c9000e4998404500301d00b840301c2e10405441d0300350a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 909308911 1250 909307661 909307667
    0x5041a1303051c0605031009031d0307061d030307140c10080c0c03041a040512150c070201050d0e070611011503020d0f0c0b03010311040902010c1415160e03071a0901 73
    0x2001004003c04840c6544450007c3c40002c00e5030b00d00940001d181030300003080f481c501085c94550720101900500206103046011030301c1070412810300c045807854140d03141360b0303070303400c10282850b00d028503a82c0c600b490b486101c17149810a0100158003d07490f01d1a94012150405800c41c1d0210b811590180d59230340c40c118441c114880d0780c011a41e070312100c1400240da4110680588140d81095030400c00c1d03054003442c480e95136a8104035544405050384c00080d00e1000000280402c11301c181000c03814a184600c904050394189c0f803a02026034049001080340b1070340305d1040030207400c0f144020004210000750032112102039020203401008840303482020488442c58490304075400400d43c03030b00c840d00c460200310740d40e01c00c0c0b00540382d9902041c00007000349054402e68060f03030713030507140c00100a500b5501c00266116a0009520501442101e05d41d00300301015246d10481c20100059900080711101401250307192134154003079400501300303001c0d546d0035401104101c0c40084002d9182d00e5000012 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 909310161 1250 909308911 909308921
    0x30a0302100513080c0d0306061106060f01121d010c0c0b040b1b0f091302030c1e04080a080705060106030501051011010b0d0f03080604020f04051903050105041a1303051c 75
    0x80c441e94000400078445e03000070942e04040d07459660140314240d5150030489540090b603001d042640c010401040f10392510582c1e00c5c54042043c100303200a512098114000c80b05480071030414801e00d040b4507003440d0004c2c42038000ea1203d5081c101c1c003c40300e43d150050030b8030f802040200380c84000c50119a032608030890f900c00017820880396642d101000c412201003604424201c40c090001880813984014139402034920422030aa109414000c0c81e00c0384c00310708121036030318482101e405c000c0411250010301c065410302d4020f0f12402d90b65030a52605a1070401d0503400395040510780300041c040c0703a44d4440b40910311601c41c81d0081c00201c10000c03640c01400360f03203031641e484404521000200401a00540c80d418080d45901d8030f655909411700060b441003801c0c00d2084042044240401c3c900300319136203440d00c407418a10032255200d554140c2143e009071025141440290f0011103544400000301d40d1081d416500910600e0083d035010381540034a070300e17074140c1402c61800416610a150300c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 909311411 1250 909310161 909310163
    0x24080618100602061e0c2b0218060408120c19030806010f02070e0c0d0b040603240207080f07020d022d0103090210270b0405010e030a0302100513 64
    0x4120041c1410414030120184511544015009510000740204040441c40c000f003e065900c134101950b810001c0c800b650b01100036041c00005c000d0310080040b00b02c4800d506207204540e001603440d10f40030220349044000042407442048208028000444046200d140320000d29107403507203900b440c180c070b2803e0a4240d091126201260150a41490380c03010600f8024035080e25940045a50410102d8840c0807034044d840072076043d0b101141181c0300c8140244810b40d039260f00058a5201c82001038107441d100c0e8025a260360444441440440000c4c048103114645240218a4503402e5a00c280e8240a0040c1c04040183c0104040c0190b40700c20132080f00160707006041070040080c00742914104010800380410565a408031418194020710400080b140c00410480c2c0c46a14200d080302c0d908031142d4042e42c10b0030703000598186441c80e90240c0014051203200d258a41f401c050006202080700316a95100b9805410200d000c26008a41d14031450b54500c0c01103601c8c0c1d5004c4a0401032411840 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 909312661 1250 909311411 909311449
    0x1207031b09020a08040611031e100902130906080a050601050405190207060e07050d110d03020c2d011704062a02010b09060303031b0d0605130b0a240806 67
    0x800c500c031554084d10192096108144c100248480c4040003c11070100721800e00140b8000c040151180590648040e0300405004100707046075190f01c008020303a080018812400c0e0f103001824040c061440c0202b0015010800040490741d445885a80d0745600600c02c4c2070095070b5450114495808020f542c0d107020080c0c08047d950f50003245402c100500d09241581154000c401c0d011985180c0a94080780d2943c0066400c03520450310310400007c14880c1100301c0a521403c0000201503c500c3d40c8040d0314640403001290b60b11845000300f81e2030426180c1c4a04000503008100d14060035290803a40290304104002859042c0c25006a010303814a6201d42840d1036100f50300303030b02c6070381500010007050059883c0c5415454480c141642c0703010550350740d0742ca150110111a0429450030180c810a2129000800c802d0b645401041e51321988044101010b6120040440740d81002d141410040103610b40300340400342c138040f2100300c41d0981450030007042103100c0856810759640941442d50024030b5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 909313911 1250 909312661 909312667
    0x1509100507050307090f15030b0414010b0301030b071e120f02130f14060a08090718050708060f0a060f0306051c03021e0a0f0201171609051207031b0902 67
    0x11002030030b241c01c1100c880c800502c03e020b000c18a0110001da080450713003458050460100c0d040000d4014082c40b400d0385400a81c1c0391952038144040e80c7c9140c1c005c10f0105078003562941907081518003808020858400d2103c09100220340907401403c00d031088c49a46000802c003020040d40d00090010040c00032802800450003a40e400c09280d100c40440d499a9580740702d1940e25825403200341041148582d00c01030910074241054011019180e001e401041600e820305e40708c0039000029aa9007800e540c4882d030b64410458488e0b080400703c0d0f04042c044914400c06083c0c1c0d000903003081f000b8000c580810100350450788441d80a9000000030f400003c0401d601c42c121502012001760b43c2c2481503005110304952010280c5a18101c990044902805002105800e44a8000c1c07402551030490400c03030380460b841d46c179a401c01c1220b80141508074601c0c0c0450001080105950b1158006034443d9145501c004030b00785001542d4011260706c0301996000250310301110883c580c440e80888820342c000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 909315161 1250 909313911 909313921
    0x17040807140f010f0b060409151a0a0e041b120608010e010209031203010627180f0c0f09170a14011401090911150c1e1e15091005 57
    0xc985400d220030640e0080000304c0030600c060060b107102c1d03c080c90700034004101c00d101c038141316001003400b070100e0860061001e030b845003140c11200a4004c402a9448041030f8184000e0340203212040340c200072030381030019020342c0058500501d0480c0010b000d111480000b8182503150760040d40090103460020081001070705c0c102d901075480301005910a000c0c038540e000c1d1426140c1d0699040e02d909546031044590001c04154921441030100740100c03196000c001400b52855914041001e070400700491203100b06808041a51600e40142090103400d032110403502c0e43c455410f2046540410111544808110300349060103145030004d406c0710b07401465903007200c60541100f95004141c03080740d030903030ba1703140c030030404894403001c004101185001c0b0130f01c050300e0207402c1c8040917000603100c245000512410b503403811101031015803000e8100d20a40c40702c00800c6c13202039007003904c0d6880740e500b21001494003502c0f4142017840c2100400c1d8100031070728502042210308040c03502c3c003504102900b86 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 909316411 1250 909315161 909315163
    0x100c0501061511010c05120a020904090c060e03060603010606022a0d0c030b07022407270503010614010503061203040b040b09030d020d0816050d09120f0207061704080714 75
    0x3c1e010640d441d41d03080814038510288600e084940501c240c0311122100e440300d04c116000780d802100c10760361094843d9072041c041641041308000810160311611590481d180c140350400d10000d05243c4241d15009040044540201da1221103400002501140e080d0103840d0040a01c14045500d400421043c1688204140c40c2d030700c10252402424920b0003590350b00740c00c0780d480803541d8400e078031400d500c007610000c1300d142110540c0000c1c45003402d006900002c50011b0f064a900c40001604420813070040085060030700c42e40002d05526242d00040b51181800a03103140703c094600c5000d80d111884020050344280161005030240c4441c4aa4495890038800d4181d04441c0107940300740106101752a2644c000200c103e0750381c1254540004030354650110b0401d14504021880500400708522210b811603845840c0c0c80301e21981151216061024005050b414020101d0082d5444104140310321500049010441c280f072000c2616165200e25203170095015809000745440900120f500100c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 909317661 1250 909316411 909316427
    0x708040203160609050d030e09091f022703070803120105150307080115050903030c030c07060903051c0c0503190e15031f1205010209010e0f100c05010615 68
    0x3008a08a0700d8a0802c0c0c104490702c00840d00c202008140380346020429400c00310414140c80b03029003400405540f100c0046594410122070303100d0941c00c162071559134041c12880c4082140580c403011030418021514401c2c41c0b10340000d21400c1000d00c0c8502d1401560f08101800c043c0c02d1482c1520b0320b0710795015110500308800c2c004e0318410f00c240d5035204000074a0304181c0788110096a075242107a4a04188450380d0b2100700d40d01070810404000200c0c0c00c0d03c00700002c206d01981e0100070341d13880c08142052420040150403510402a0441d01000802d030f000034000e60f812940d04031010045105a8291400c83d4103080040940c0808540c95907a511200c04c00c01d861000780c2c50f61520481c000c0100001150643c02941da14642440450442845602104034481c80d841d504a0087d45030144101d041c4080c4034102c0312030b90001350b0b5102c1541c1c40010340301110415190b50707640c0a00c40e000641602040e091044c10040380c800c1003414420250001001421070f0b18050b0070b0043e1418006000711 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 909318911 1250 909317661 909317663
    0x16060218040504081209010b06040f0f080102090117060a1a09092203080903131e0b0403030806060307031d01022a071809080d1b0c081818070804 64
    0x5510120364585801c00e03019440c401d650080781c06103041a503074036280507060098041c1c00a07643c1c6140c00c210355200c1100a04c080d00c500c20140b1140d0389401c91035a5140c210380c121302240d034014000d05136181d800482041040a00c030407001a0b83ea1b411011a00b1403203668043c522004500c0d84d401d81c240d20050003800a2401500d00348460791b01c1c4640c4040e9482c250f840103411100240410011a10411307000303400152401c1580e14010075160a201240c56032b402502c1c030400000f84c0030f503910f00000c00c800001c15a5011941c10070f0302d10780340509030401c028140c030f002e00000400113005c0c80c844d50001d2502379000207403280d00000020a28000d401c00d03d842115412500b1580804a422180103001035008800400d403070707810101903010421410055107155a10385581d240050582c13405070040b0b01c0c600d0b10008031143c104058032009040861548103110360810100040b40000080780c02604009180c160070140c800c020070f00c401c5551543c904205000b50034403c80b140c1c090149800b44d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 909320161 1250 909318911 909318937
    0xb041104091a150901021f0510150f0813020d0c050f04050c070807031106150f0d050606010e010c06050115080c030c180607020301180303150b040b070503160602 71
    0x241c21801c80c011800385011030b070254005a0b0283c542540d200f440c008206070740c0f042c41603405100020b2210890b000b10030100304078260b290700030403843c0b50a440011300208030920417038004075040d06014121a40300c24050080080d08000501c0b240445400c1a00c81303039025200030b4a0102c5814441c01e00482e9000362846444040d041c0040d603e064010a40201110000240740516603603e0442681c40280128140318820840b24000c81c008d0090522400350761180d41c41181c403c4081014880904a000d0f118036030007000030021840002d420f9034440d00070300303000c03101035940001620746070404000280100d04100c0003142110b42c0400d03515016542e034481003d0380d140c5200800707107804200e480d16810354003881001c90b64a0319040c0403041d0440603103550301e04046034010a00756051046040c5401111040d51410036615201d0707591504081700035034005034100740d1498a940314038850568400c0c004200c0358180030041c402c0b1811506904100c08081c4110701d00310b00a900712030191022 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 909321411 1250 909320161 909320171
    0x50405010b030a03020c040203070905130605012d03050c040b040b040915030f11060403171b03180f04110c06070207050607020d0312090519050f0a05120703030b04110409 75
    0x2d0400080d003120302d950517006440c401e000581030000075040181060100b042c2138400003a251111443c002052a2200300441c45030708000c000341c140c0038007040d507415030b2a042e103200c00303564249025040ca41d00140790220b55601c800c16000d0040c00349421803a00000c1c001400190800d82800603c101c0b80700079001d00000806451558116403284009030200c4142d0440400090210050000b08000140103d0a250320b0780c4540744c102540d9a04d00d8168030000801c920b0b441150380ca10603c401d80749004620f81100310f40c0244c8400380c1c0030b0704180204280440b508403580c440c2c04c00d8005501421205440b88841002243c1d900f1094401c0405406014004141800c00d80100e801654020700803450441c1d4940e401c54105159110080382d15940300b181c800024001e004c0100300c2030601c0400b4664803c075040a605010251542d1304440c2c1c080b0050000140001c1103281018224030705040d2102c6c8507086c164043e00c0000c0f001c41c1d100c0d207411162401010004094400d80b4414001082 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 909322661 1250 909321411 909321431
    0x30908030301082d100f0f15050d02060d050718081501052806090f080f0c061b150a05070f02060c0f070f060605040c02030406050a081302060a0305040501 68
    0x92244000c1c0030f142c0258000c2c80030130040b03011311020150301c16900c5000c00501d40c0624550390611090340d00c00300c1d02d01e4581600f002e184989001e080c00f508a0711104100018101408541080040c410f450141081c074032100203660300c0c03800f0340340f00211b0a0b20500031444e0200000f02803131801a40100c2c1c080000700042608000015442d0040d80c988050707809503402c1c4002c120700d08460303051109020020703943d4611030400e402480c400078107a50311000802c03401c0111f686d0310031a5035003080758180e012200400021000150502521800340c400690300c05a80503240b50502a8409213100d034884c10301001c104200a54002e4032a040203441003110307440d20541290104803200d100340c0180d00917400b240301e104040c0c00030031101c2103051843d441e00a15944468400b908604207961041e40c400d020400c0d8107150080000c80d11a44c400703186440d05007640940345000b0711150008003c81000090402c4040d12803516060b90000c01c00d0f51603007400d0318002d01a001c220b40c01c4429500389000d11b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 909323911 1250 909322661 909322663
    0x130201320a0f020f0a110d120234180612140c060901020d20010c030b03010e010207030f0302030406020405090901051602070f050d051c020f060c04030309050904030e1c030908 77
    0x2080a0101c80506010700302e41e11150040c06249161b698010b000840b030000180b0400707210034551000340c015010080b110042c5102c0318050290741c0c4280c0114607003407d485203038511b0b50b00545111040c3c203118041d4000c1d580e0000e1070b1381d40281c06003034814038113003060140c2841d6002e4002e200300c00715103014229005012050150800580c090380c0083d1000c903a1034003c80140150390346801e04580142c16582c211400e40d19800449008650355195204250a080c029000400310f460001c1d0702d440c1d010f540041c103d01305060f1341b50415a01102240c104200307901210020308000b89036412508144116600820003a02c015040c04074a101c0083d42e6030000c10b00b102256014010041120b281105010b14502130807002c64141c0105040c0485403180105460120079a5500520350511603d800303d03e824405400d030410b1000c20300082002070360111402e02942d0003510704400c0b64540e80380a0b1400b141c0c84c1900e0764040b070240c0404004410005c0d110f100e07140259100215036036598541 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 909325161 1250 909323911 909323923
    0xd0213081227040e0d0c03090f1a030c09060d05011d010503030a03180b100501140319021c1a0406060504030503070f38070305130201320a0f02 63
    0x4511155040b100d25441140440b140b004400141c80803d150020f4801c003400c18500c03d04070400b15994040a0043c994002e580c100900711130041c1442240c20b141342500140952200b22010000c00000200c03211858000d59807800c40241100d80c50700751070360103540540804d006121944140c091560074070722140321039a04a41c4090041c52412041c4003085014000e5250350345409117000d043c1c00001407e001d9680c1c400c410a180c04150f40c0d0504000410354115540007494950061042c8160781e9201d050100002c8108034006944051010301001030041901070044021702c0c2444400a48044010341050710a00b240d0030407209403103003070a65840c0202c1c0006001a8801c1c050b2800107010300c048404054010311ba95800803540603d800010007181908408100300d240048004590254010f504528141828091032502c10341c140021111214064104082240c03141c0e80907400564110183c0e00016000300c003941e01004d0030000360301040c0300c41e00080c61501503c01c030a09c0841c0d9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 909326411 1250 909325161 909325177
    0x218100807030507051b0601030210050301030b070c030c21020d032009040b090a0207030207063617010204050a0501020a080414030c0402120f070801180f020d02130812 74
    0x6010480e1500c01d411001410020950414084208459041c814040114400c119607110041000d50306520501c483c40c05000000300511000f0700041c0000b54040013829030101503440c0424110030170341000c0300d80c01c1ca1030701d01070020403095584c00040b08035640004050f4550760220340040d0b0407c0b40450859100b6104120b800111442a0350308101c1d01004002c4110000c001060096a500c0012004401600c03914286540013410310200f54040c840200180b41a0500c201a9208110a12000d0041c0c18032005c021106c0c0c1c4e50b4841c90404101f25001811100b0444000c0c1002e5a0103207000398024000c0b18416030618900060545c400105980b4080d48400d07810309051800315014000e810710107200da07140c0100d50842e0307029262403001d0314601550035480c90981c141410344140c280c0000e80b5800421844800500c403031100e900280000340d120410000b600d0400111100c0280180d20203c0541400000e89855070400c0054401c2950102c0c03003a0340c40c51600022400040c421480 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 909327661 1250 909326411 909326417
    0x306010602033f1b13030b13140f06011401140a020307050a060504060506040c050a0c0c08190c0e01050a0501110115150f0203120117120301030303021810 68
    0x101800454000303001180c3c090403510303501c014007040749540351a40d852000c0d00030040501040b900c0429031542107400c03540d9649042c60143c00f11501e4804024a0101601c450400e9000c11115007411014041c840e4200602e0032170f42901c00940c90312030704020754150844c802c5e800041192103016038115903c00058441d135080ac291001d031000141c0114142c3c0041d07003c10310282d8003282c0b040c0300c1e50728524071600c40003519150a02d070420446401505c41e5006e503282801e4202d4003500030044842140d0756040c8004201828540b640a1400680100c4064081c95221003d00213074205104201445a2500002c4688074030441d03034141c400344125584a030951504200ea5406030880d09801c10545001044460120101301c441c07810075804940754034148103990301d48941c01030850b000c170720240c4041c521701020742c08000300208060080030310302038901014021114040051030418210790702c0d6182c9941c0e480c14090025002070441c0059840d02e41a000580d00c1d1420682604032443c0d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 909328911 1250 909327661 909327667
    0x12040813180b42030f190b09040219051201090309060c03020303010e0c0c0316060c020a08091306080f060901060b0405011d030f070e1b040323030f031e0105030601060203 75
    0x514070369583c50000c01404000c42e40700e03204080001c2d1540c01544600409041c0c1c40c50f50401c0340d601c4480b1100500441003261400e540707009903a45450440c2d80003a01103c4008501d218941c00d20096201540704c0c9910031000d261a48503c50190880c0051034004d03141e4001c0c0b45e41d00d040a031450100d085008006800400043c41200040b5600e02d40201001d03400904050300b582c0c5603480c65010034130301c030000240c1d042c0c0042007001702d010b59020b10600344090000076849a662913058050308021900c101042c2141d00c42814050340114010040c00c4202c0c0c1b00b01507402d10070340d103c0106880450b820750078580041804080b11044608955040c1e403918004100c060541c010606072800303859041c02061001076031a41c0c10800d0002a00100e11180b601c1d040207e00050801c4110f030b0100340030007050004202282d1081410a00303034401c0c1c555100d030700490900c0e4508511820407207041d002e4021060200310542c4052404200c0d03a13442880b8203690301e40d010982d403143c09100d4400164010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 909330161 1250 909328911 909328969
    0x82d1605040b2b06201c1a060c1015090f0c080a15050927010504170705120d020309010507030b0f10120c020606130c0512040813180b 59
    0xf4a209103080d07070203000d001480c240080e001c81d880400c10540d540b00000e0101b032002219003003035540c00c072100c0202c00030898042d050301d030000240540303c02180318040120390001c0c405c205020744054040003030020019101e01c0300308540c66568034010f0f251041e241030320140710001035110b0b0844a01d4991200c880540d24280000e0140c0b0f000a01c060b4205401c00c3c0000321602c0d405480c40c014000204580c070000741e0049000080200c00d0007840c8030340c2c1000280404688500183c108182280a8141c2e882986040880c0380c001c54000000c4c6100c0c000980f2800580c080e4055401284864000c0c0450346403080c045041d5014400b0140d03221044100d440c9a41c80c116210b885513520360704107000620325441200701200ca5001070600960080710070040c091a245040a40144c40c140b01080b031075005c03450043c910300528130744160090741400454288000c04003940e031a2585824060900d90300c445e81c1c6106100b203580160001d80c01e12003000da103440c16000b00516030041400c0340180c0050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 909331411 1250 909330161 909330229
    0x1403060d060207020d020a0e07120b0d0311150408040302090114210106091d07050a06050a0e0f03030d060305120c060c180307061706010801082d1605040b 68
    0x43c5002c0340e02c0a002c801030720041e182c9912040040109518140302c1b854902c00140501c1080c550820680e49459240007240c6d0710401240f010035014500101141c40ba0340b0454075024121400901040003982004108402c0500030300681e0b100b610300c010356903a628041410690340c8240950310290642d00201040c1030762802d44641840a070010600b542c0d02c51a0a08075035041d80301d1140030a0014518080b0981008040e006101c255040040c3e2450040020030500803055460200701c0d4800000c3c189030385100107100760710b5000707054a90303070342d20300600600030016884100c4150040c3c200984284000d5000c2c2d03040d1415007000f43c415540c81440c00d203104d500c4078210708008503039120008510386003001b0007405010152201441c01300b50140b901e4118900410306030401c0324020040c06000f00108042402e1444c0f1030240503903040148403410040a1203500350180d200e1482c48410f00b010a1580070112101034808006495000040c4400c4ca640c00040e047d010030f68501d070040c4044 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 909332661 1250 909331411 909331417
    0x70f03030b130f0606081b090103110c2b09030f050a171b0115051009091a0406091b08040c05041103010503190b06010c05070f0f061403060d0602 64
    0x442031400103514200d6400040310050000560b42d4050740e940c0b5000c0c201c552510602010308003e00301041c084c60300b0700082e13801d02d552030200c1106100200d034038811a40281c020700442e081d041036442d110000c11180310f9443c3c5244448010b0b0178608448061030b82140e4002d030b10410f02035558814020b0441c1c0301c40d0301e1a241d001e412038691203120142004030750b45078070b0b120104464400c00784c0c0e200c04a0402c910002c2c1561313021010b83c0d1404072040c2001c08810141000c0703a005503080440090003200541d2911840d07032148030346c41c1c00c00c4c524462106072030756028607084007101c2c10483c007500c3d21448000c690204160743c0401c2c2c0780d8520a1085405900c045911a01c9640d1189400ea241c0d0042016203801d04421041c265000c401400030380390511100d081c000100501c02c903081000d4031403a8030114040c0480741403103d01e45d16002404814810000038118111b2032440311582c40103949441812845080700142c05542c00390128110402224060100207040d0310500504d80c50320130080d8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 909333911 1250 909332661 909332663
    0xa0506090d05210c1c170c1902030307030e160e1f0303020601050f0d110609060909013507090f060513050f130201090e270601031511070f 61
    0x221808010701e001c51582082c4010640c0c01c0102c1c0c03070304d401c806141a4500400a0510b03a550f000004c40c0071122544960059103145c245d400d0314203944c4654411040302d2103200015460880c0900f95468110b4000004601800700c581c1e04000710014a10b0003605e541120a0342d405142c0b00c803208000000030801b2032a04041c803840c1403510109202040000741d00658030450160300980010400c0e480c0c41000e003041140c0c291840c10a40c1500d5441d0700d40d001418500c40d1181c3c80205062801d5112082642c0da1603001806c028010351b1502d45400074a40595840d1042c00051782c2d1071a00d903082c40920300c45000c410801071513030301d082c00029000fa008658013858066503030200000c0580d2040008503010041c3c060000321414151010011303e40d0080920030641c104581142c011b0340d01c0b800510032140b504001d140c91b502c82c99804160400e604a91041508124a00b00c080b05000b01d4107034100d80c0710341607000b4800c080d41d05e8601554201c2d140e14412040070701c40e010109401548000c0b5031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 909335161 1250 909333911 909333913
    0x2130b060304020613080703060c080709032103060f181109061603021005070e0a05120d0c020409141b101b0f08030106121805060105240f0d05060a0506090d05 70
    0x6183c9801950b8581f050560044d42c4a0342c58600340c40d111a0000681500031615240ca442c2070360842d104ca04140503228071084c07003200c40103c03030b004480c400d51040018010310400c240d48240c1d02c84130701d86400000d0346600c0e2041d00d088016500b500060049170401d03d80a0009400c0100300d203031245401802c1d1000ba820740c000c480601080f24218400c152013040e041d104e115049140c0340500c440c500f619044030740101c500841843c038000e00028010490011894280311200c1d8074030210b80a0617410328010311030242280d120750203130300c040343d9082d00005075010228101000b204120b0750401551407100032685100301a5010045000c010f107007240110140c2c010003405036211001c0d540240e00c0f040c00544190740c0c101c0c040b10180035800745100510425520300f002c076280d10303840703071418481d561141842545440303c0c00c517501c07260413401e6840a480b5441f102202d40050b403ea001d00600c2c020103241000003503840c601840047c0541e00094480c504050404050081007442c0c0201503440e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 909336411 1250 909335161 909335197
    0xa051002070b01052710060806121c2003310302010302030402180f090d03140c0304030c0602040e0f060612011a0c0109050c01030c02211b06100302130b0603040206 72
    0x1505c4c41c801090042045980304400709281050040005d00017134189031080310045c2480c842080001907034030f41059100d00d02001100700a00940c0d03905681c01200c80c0c0c5490080c42d0205e10384012014220b0401a440c0c0e44072034100350f03042c41c1002000c1ea4182038a11114020600155100e5800b0b164490310182540f11030000124600e40400d10031552070343d40e4040d10341080f40c240c0707003800020a000c0309403c0a0240c030076241c04540c803004004000760441c0d280800001e00313140c400d0f0540c10406070001401c540e2241c9070b0603000c10302c032400c851096041d034207580490206d00305001180e000015617001c0b181503900b0600aa402024046020444a0000d0201400540c4284584000c251041c1c0040418121850000d4291045c40512009641051309405a00031001d5041010651032003071269a0b00540705441c41205c103801e130701506034482c0000700a03012024a07116000e90780211900e40c131015981a003c4103407000101601d40044050012030010b05001d0007078081120020a6003003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 909337661 1250 909336411 909336469
    0x31c0b04022803110712140c0609060c16060b01110f0604050606060304120e190b0d1d0c01031814240c0f03090c060c0a051002070b0105 60
    0xc280d0300031054542d890b92080074400800c05640345003220070580d904041c0901810109000c2d007501030712001034140700c11840304181d610301c120001c03020400d8610440341c44801c071111456641c0001c81d030740c121910400c0007040c0903c0405040e036000b01030140914561030030941c0e0344c2015200b030030509414040d4170000c5030070800f42070141007214407512006110368609820040c5c03504402501c424080c040c1001071102040c0e220007001160030b010708011484050400108566140440101c0303880028403c000c03428030350000003041d00e030704400c1e028009881c401507200303c0c0c41041040162664840d90030403105501942040414034110960a80340d4402034031074180b4082c1c141c3c2c0181864120b800c0048801809100500c0c025a903202c0402691408240d030100d2840b604aa450b0307408030220015594040030401c600790303414080c2600da1100c104c0400544d40e074641000c120342a01802808014000302d902c241d81c0ca55410106060042c1d180209000310351580300b013410300140d50701e00216 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 909338911 1250 909337661 909337669
    0x9010b0a0309021f08010509040b04030c031202040e0f1e0a18020901120c0905010e062b1506061407060c1b0c030204140f0a02030907031e03170405031c0b 68
    0x41404c40d000c1c01000c50110074102c0042000350160000c600c00e110a00510010455014180d54000e45c94100340c1c1c4000c22500b02a01c5c0c01900c05a20034049000042c003140096859030103d024400083c041c440c2138841d03980a1250318a01c120b20340d0320011240020340741001e9034101c5961401000d01a4146803115000b144180b50260001c22886104004c04000c1140701840c1030300a00005000b08119410400c24103600b8034040c1655100e046064412900d09010b000d00941c10843c407200b90b956103460b4504150035841e400d903c0700ca0117180c01000140369000340e030b56407020018030b41207504d000007659440340181800340c03002c0c0821000814180c1148005108002d034907001f000f1001d80701e4910b00c104420768021240c2968140446420300000b00c2c550103010303030002d880d000c000d83c913582d544201518025180d4005040d50814642201e0b45081303920004d11114040d03655203d00084240400e19100404e4600902551081003140d0b1070180d1190305803c40c241c2c0c5440810440c00b0030b0001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 909340161 1250 909338911 909338929
    0xa03050c030402131e091101080c04080c04152103020c010314010b0c0a051e011d0307150e010609140106020c10052107050912061302060904230a0b0604030209010b0a030902 76
    0xc68410780c0c0300d060311102350f80010900d40d20118a00415240500784030f0442e8a40d01e1080324203024540307030044d002c16648480118000741004e80341305416500078201202202c0318602d8154050300500d10020341c65403181c001c484401c1d0b08101051103d0346814441d00c1194401e0b4402c0d0a0740c020080041d0001d4801d10134920f1074a43d11101020071849465440d00312032411505410070b091110b03000100c00c80c04415615403d420980d0040f0741e060410320040035002c1c0c11001080c43d441e00b40081074207042a07008840519030071a01c0000340c0c0e264401030b83c4d034072101a48107178000000003e401e41c5a1003100103012440134003402c856445010340080300b0805042d1100e81c081400412000840d0600804581231840d4440c0109440c1c10808040d207030b0400d0f13540002c0e004040000720f290340c903103c2e07401c041c80300c4019207840305400c400c1c45c402060103101038440d02282414807482c41c02e6840d0040546043c0c03a00281941038503407a080c0004072607031140c1c950340d06040d251040900980d80d00709030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 909341411 1250 909340161 909340163
    0x3101a0f070507030c060323060301060302100320180d0507090c05040305010c1d040906330e01050609062d0c010b0a080c0f01020a0f080a03050c030402131e09 70
    0x20000c06013185801d01c42242035400c4501094034250700e00f540c0f58011030031508000d002c882086081c1d02e030040401d015101681020b03410004200c4120020365040d40f01c0d0040030070200f900014418202025461485007004161110410084158013440c00c02d581c0c0c1c040a1040c4101c40d0700641d10000d4405540a412504011400100c2d0800c280042030283c0e08600e40203107800380d40000d149000070312220128030054021561800c4a104006e042d6002242c800000010502001d0250a5a60022001e8a058003a030104a80c00090301000340d100c107416a0300c02000320b410690703d003051001c0f0340c00241c1201d60060203884482e40201040c40c0210380d030404c041c2c0c171503658000d5041d10350a43c0c42c15000076010340e020020400180c2400b2891035445402103600030550b20302c0d240100d14040e001c010150403196070a4103d4100440280104407a0032561000d0103c3c0d42c8080080015020445020750010302c011000403031490554031004944120740000800d0032003001d1194210f40070b01e24 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 909342661 1250 909341411 909341413
    0x7030803270d050c010603140a060c0819050c0708031e0106020a02010c02040f0608120415031a040b040e010c02030310050f1f0302190e1503101a0f0705 67
    0x500004410800d025102000c0e90580941e880400303100d803598422940310382c1420000d001c14200400c6000390000c10085030032402915440220505050700c0d403003000021520f080c07501144c1e200302c07802100c41c5c0c0d20804600582900c0c105a00e00a0401341a0040c503110a6407010003605002986d6030307026601030054550000052114642407610004041e080a4150f5001d04000381c010703030b03100b0b00e0b5405444d0706540c00b04c0c0c0300c1d21400280015050b42e03041088a40224040790b81d1120318040500101c699140b44c1c104a02c980101c00d40450b207002113071003110742c03840c0345034107460406821035000e03030324081c00004541e01a1504103003100c0d080c5144100580000052055001e0b48200c503c01a010443da150306990781000060b40d0201032a0000340300032201101c0c014800d0207681650071580c40440c0c4242d10100c0c1c0200200101040202d440c8220300d94103100040c04807a00551340705800d80a02d11903068140449092041c442d0640a4105a01004400610010f050107080c1040c4104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 909343911 1250 909342661 909342667
    0x150c0703030e06010b07030311071a09071d0601050912102307020607080a140c0c010c0e150c030702180907080a0803180a050111181905060f0408070308 67
    0x31400070181e038200d200c200d00300d42c400c600501402e000f2000b00c43c0d94540c14140000d024882c09003140701c60048500c00780481201f46400485512545603c5102d07080c5441501c44203070722024203903081d0b2031059264000c0e005080004049502400003030100e0080203205c1000e20090b08a15442c10380707070740c1c1102c0300c00d0344881d00c1034281080a030b05101c48400444010b42c0500c0c0016001790380f140000c040c030040100319030110703103000e045501c0901c41c503000c01c90354a4149860304c1460480ea010400c070300410741c03802071007210b0a4400e041d421800c0c40010040c200b080e442c9904204160040301c004100c500041003044010b036100300802c0351058004951060900e40f8a0046013404801c2c0e0101c000ca4000d43c12500000e010407040740e0748144a25084200700d49405071071850501c801400401075031900700c0000d22203052101a04032019a060340006c00c441106c14800c07035448100600ca400a541c5800344040d00e860000f1385900d141a507209410195241c030783c07503e000d48a50096079910740c00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 909345161 1250 909343911 909343913
    0x70207060f0504180504210201090b07020d0e130b0306100f0b0a1b171206040b060a02100f090f0804060305060405060d0b06040b040c020c0f01030501030b0c0a02150c07 74
    0x1001120070022102c0c1016800e02e0329200c0e102c4940304105070f04e2139055075550009020051000d00111400110b071030580b420f0150300401a0003040342860981c0d581c461500014201d034030000340d8090708001c942e2402e00411002c800d00407007901040410401944401010009840410200d4410104100300e4204a442c041400b11140d50342c0e009041030075400c01c0130504403504200f44c035003441d0080c050301c40c041d030f19410000300141d00c5207415602c40c0c1c000a2030a44000401c0b5941c2d0240f1802c0b1010440c03c400320003009484d2052080e0300002d6000407042e01c41c0200f640c3e00801e803032400004080381b00529940d03226601c40344403108075026a03010a0511010b607245c4240e0b980501e080d0b4082150341803141c00120700c0c00c2d401600418001008000a40c56211604403124181d40508140724041c141c200181d00d070b03404800c25034001c2108401300ca0680d2b00c20700880303040ba42c10901004003525804d110700707015440401c00000b580326464400114850103164148034100348200c080c1c0b40c0800f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 909346411 1250 909345161 909345167
    0xd05010f230709080303240a060503040c06210203040c0b040e0a0c0509130510051302040501030b0f010c021002120307031e0e0712020a030b07020105180a0c0303080c070b07020706 79
    0x1c058403403010400403c10038828024000102c035000500340040c05200511f9507100c000c00720a118100ea08040b2070280051003907002009180901e1181a85200042c2c031490200c9a981d01074620000140140851001e080a554011600140501124140b040d2584d0101056074426804480d07003908003020401c0d5011140716031000a1045e1030954589000b0300e0004440e403042e5142194a240e031440800c500709006015140184000b03003a0313200040300c901c50300c0001c0d00940314850209040c01e440340083c3c42d040341d4055030800305840e049541c1c2c1d915024848100144000c1070150307c141a00100020f120401451080c0e6050790041040c21041c074a4032506010180010011410000503181c22240852420181d5060b454483c140707113021300004410000542c00640030705101c0007030119140d0b06400c000e11500e1016034030520000ea0300b0b011991001420b4024044036403510051001074450541c590b00100e05218144c140700a6803240001203006440c0340c001359000490070810190 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 909347661 1250 909346411 909346481
    0x606030f0d0903030f1b0c050310020f030a02250b061c0f031209080c0a02030d18050d061b08100510090b0c0102160501052203020c0d05010f 62
    0x890300501091001140003402000d0180001024000b41e841c2030000144590100072206515100c580007107011801d10500c5061030340991350190140d0000300c05601c04c280221050103164101e100e01d16a510100c2c00d00030340085020301c02e415174225006d51124131070f50a01107001d000d09000041800c04004010100c40f4441900c81521070f464051070220740e43d81100000d05800d4101444d4403c3c00c025444000c007003003c40207041200c0420400461080083d000d1211803080e0100e401c1781d41982c009545107901d120b900102511005c0e030a100c50300b0080501c48035203125000205408644000c40040006104540000603c00340c040198500089142100805050740c8ca5003030806032110041240420740640801c1d00c50014030807010744000d504950f681904689841450545898028042d040a8400b0540b20b242001002250f10464003041149a41a002841013401100901c2240601d64100b86c0d0603550390301000280300440d0268484150300084035492040c561a06904010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 909348911 1250 909347661 909347683
    0x3050c010c0c050c0d140d02030c0d080910090623060f04022502120a0312060602011e2a091707120807061104090504061404080f0c030f070302060603 66
    0x3082c403035050740c04640003284000030b40409403143c0782e100001d410124000140241031030464811003151000b8580d0200141075032030410011344500318a07003207003214505415140118650004a16540b1801055110200442c0306500100d4070382e01e40d410200d20384e00c031100c52480c00740d0054100b1809240101c0c2c00d031a0840b0840d4210f041c8072501c241c661011401504880d0510400c0c100c000540d500e58031303542103041d003050480d40f03c44480d140081010344d08031107900030076091044c00b15810303006004003000c910320f1410741d4004895600640d4013410200d2100b4032400e900703003d080d8050b002c4032000075041c4940d49a260200f071402c00c0d049041050803520280a4002c1c01044c0304401110804542c59500803038156103405650070034400500c800e141c0100c894100080010b0090210303003215110b80d010f0700081091504071410001e0b41482150700401440c000c2180b0718805103110081e0140300e59130b400300ca040060301c0d415030846e0361102000ba405a40213000300f0507985820007460440c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 909350161 1250 909348911 909348917
    0x201050408031801140a090c0e1306111c02090a090908030723031f060c031e050f04090621120302180418060f06081f061203050c010c 59
    0x1034a0a03440d00c0c44980409040307940201400f45500000302002d401ca07011444002000060b0f40c2400c60f5060001c000600b030440740d0030191440001c1b083c03181c040c20351046a000355901e4001c01c0070b54a0000505000c0c04900c1580c90a01000010402c1003860081c1e00fa40c0da100107a0368040d101c1009107046290f4000180d141c00c00d807409001421120542e6041089400c0c00c0c0c0f50340c1007030847c0c802c1d808982e00d45a01800800300400801d6580f002c50102e0031240d55860b10f2000d600c80c48104d40c400d40740d14001d404074900c0740c00c50101440c24080110301111610b0141c0c1441403140b81000700e0b40c81544618521030f00c3d05820f0029846114001813005c59900c0880107003405a45d5900e00402121011010b050307000c51103030482e0a01d1140701c5031700c82005100300800340c5035031a03440c82d6141d1104141d030704900d0402035540faa00a0710030041900c00b41001440a12000d07142008000ca011291111742c070f03110030000564454500844044a10a40307850703444081c8410040c2c21502c07072111510070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 909351411 1250 909350161 909350171
    0x260703020a030908012003100512030d0c0309030512100f080c0f010513060302090607020405010b0705060a150302060306150310080d080c030106030b0d0203060711010f0b090610023a0201 82
    0x20305000e0041c41030b0200c0e595811622a92a08d0340c1446171100c5902850700f082c40c0c60000031040c400030000b403500b214440300c20015000114800c80407144034481c000c0106400b000551072015003016215880a031490f00c05007201e44442d1607100d41000d07640003000b10f6001440418440ca40404035246841080c41c0060400304906900c06c2464454070035201415800140d41c0d00d2900c80c8030480700746039001303442031101d942c3d00c526000c0c1a50048100342c0701400380ca004901c1da801039008525440c048803010860546c10b41d02001005d9001400030760b8030000070380480f4000e0105030041e6208000b46103c0b070300050310700707008070b424064500280c000b08041c18007045080003424080ea41590a28600040c0c0c0b070462001080021440842c0a50f2503c28502040001c0e507021148500c9062400d0003440710360000c02c008400d44002d0500503910407541400643c072424509254501001c1c03a00c100e44002c06c00a18603000683c4940c1a024000341d28800348407941952038912190410520003004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 909352517 1106 909351411 909351431
    0x813050307030804030f48210201060b120606130312030b0603090c090601090e16140c0d030b0102030f030c030609060306070c260703020a03090801 65
    0x800030740f01c401c6c01700c5458403500100054554400c11007280b42c000d00003013054200700c0c01c01d1117503001d008070100d200e013074001c03000d4130740ca0340220600141c2e81c01d00724590320b20480100b0308905581c1070000400040c0700840881e403070002c0300181c1800c59190040001ca8500c1445e400b800c03225040315001c0244507038041103643c0c405103614208980e03950141405014003040f50b0240a580007059000312a041c2040c1017503003c101450312a03155502d40140c0b00455a06541c0d1003190b4558030002ca041503040112100e400100001340d03414000c1429036a0340d64403200101804154541c0340c01080d80e4001c00c2a030f50a200302c1c440c01030702d03880c1610b042c051a40040301c031140704000ca0b0001c40d240d400c0104943c0d02650243d078036156104007503245c0d803045548800f0507014141c207182000b100da1703001c2c0d0042c0001d144a68054000c56156040c01401e8600c1900941102d900d0700007000 = true := by decide +kernel

theorem cover : BRFrame.Cov 909172661 909352517 := by
  have h0 := BRFrame.cov_init 909172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 909172661 ≤ n) (h2 : n < 909352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
