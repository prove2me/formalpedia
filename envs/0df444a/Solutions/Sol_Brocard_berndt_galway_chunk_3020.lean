-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3020
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:25:12.364082+00:00
-- url     : https://prove2.me/submissions/92dbf929-bc07-4d47-b7e9-efd45ee9be27

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 542985611 ≤ n < 543165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 542986861 1250 542985611 542985617
    0x30c120726030a020306040f0e0a11060703020d050c1002130e062d040e01060801050907090e0d0509010203070605040602040603060b0309060c09010909061203091707050f04020c1f0e0607 82
    0x10000300e0301d501580056602c1503001f400020b100001e07950300343c01c0710a03403111101594071410885040003038114004003001c0c0121199410040d6554000b999030041d41c0741c1d1420404042102d80715030314100a614684604041c0079910381c83d502903040e00600482c031440515036103080114080b41840020140c06403165001e600709010829040c000d00c40701a0303c0385404c071b42d5a0b081500184403e101c0c01c00504001030000c9090b0a068290328584420741e0000d60803540740c441c012041c0e281c00202c0266102e21810119264440180141c2c150300a00f00f0140482d420282080200005a80207100b55110b60b28100542902c802d10340340d05010882e04c048203644400041101210302c036000d4038044505252100d5116210b91500003500c034107070303c11010080c160000d1010550005166030190286180118407410344461032030343c0d807085119003070152116414410007900c480c0c045a680c403d04508a90400440442280d003c0200d640910401450f2081200a04101007011030160507199 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 542988111 1250 542986861 542986867
    0x160b01090b0d030e010215090703051e0307030f050f0703080a051b04030b0606041205010207170304110f0114040f08120a080c031909061505010f020a14030c120726 72
    0x143d0240e900c403001c1c46050b03044d849446560041d00c030310f2001d20b5202e182064041c104040c40c40c41c00500e04240a04031f89000584940c40d1007420f00300109071070700650940340030301e20b5451900d429215845242281ea014090010f1041d0a040e000090700340500500a41003041c0d5072408001c5510201d071658035007800c4130400041000c1024030f0061500010001d020310b1416a446034604c850501c4002c1c02c90345650049101c030280410207048114844003208100d01c0c6142036a1400c02c01c0c264102540d1003528903c80180144e4801c1c1e116860189030708803429036aa44550040115255074440c0900b00d100d6465200c0c232051003402503514a49103070310b500b0010b4444131138801d000d410042c6134200708580f0043d1041500300170302841d0409800349400241c2c03c401d01c0c8040d0074041e1140c2007103042c402507401510382158001000c00d881d81d081094013440e5041c802546003107104416800c5031900c101c031000d40012192000038000140302c0ca0719140c3c00f82028107101c02502d0071403035040c041c001c24 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 542989361 1250 542988111 542988113
    0xb13050d08010b040e1b04030c150c0c05011b05010e0c090a020f0307050a1b0f0b06030c0a060c11040501170f06190e0307051f11190302160503160b01090b0d 69
    0x148180350400101d40c98800c6240c002c0c0c00c00146c581080c0e10036100d08101c20380822041ca1520000494910b541c039103102e2028080c1c40d0800c0007245441601d041001c00c200504c02283e0132000c0d80e031001c0d070040c002d1155034814400c15a58142540c0710724850713208000414041c80c080e10895811000041c201c2d8299174a804095030150000208a82401902588058810240c80810b241031388030300b094050405281c140364002c401d00600d41d502a510010340302c5e80c56500c88a1100c1152181e2516503407059071403603d90f00745491142900d412a04040002c114464031524800301030b400101240c0051141d560000e030b8074602500c0054800001c44068603400d01160001c59a0141ea001102d182c0b40d200c0e510f00b4544104043c0c0680340014145034290946458040c098801c4003950503241020041000201c108070062254028182d0001c0c1803103660180d103085000c000d0300314090303a881d81d44a102e440040b00c00308904075010707140c2c84000305140c3c401d4880c8454001000e06201c41030707411 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 542990611 1250 542989361 542989379
    0x40b01031416050d0c050a030b030102070201170a0f110c0c03031617040b0a0c031b03021506121f060510020d120b030a03090503010e24130b13050d08010b04 69
    0x20b0b403440c07a020030070100100b052401c101d015500c4440038640d80e0755660755807844001c04644003510f22500c282d004020075005070fa8401d03031030881119403a0187c01d80392a011a44002026109401c0c1207940c200908116001d1949000e4441004c12009071780700c1030660700416480e4840d00e0741100011a0b100300e040b000c51090180c541c0303010601640390785420744414081d803840d0043d101e4903001403010383c0c501d0100b585c0031200071000d21010b010026808010ba80107505d4034010020310700c50030014000200c585e962a841e207480c01a41d0030a5a10303203244608042000314588900840003414104000303583e0800101c0c02c038001081364090814034840700700403108210740c0c84440c0c01713003074440710b0303220f131a550501610007020701c2919070000c020f24080a250a4510000410006800c0365000e010700203000c4807454815000030026a00071b56580c1c1c2440d8268141c000c0252515803448100040900560781002d0042c1c002e80844a50000c0141c046503048424040e080510a09200801c03402032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 542991861 1250 542990611 542990641
    0x71e080408090d1b0806070f110c060309101415131b090501120c09051201020d050f1f0302011d0301091a0435160f050705040b010314 59
    0x4407031481c26280811040005410070f01d503a106841c2031101d002541c020403000080b4800030010040a0301072485c2c1894058900e490542d104800d001d107021206095010902c502c40403d070000305229243d00704a00d00b10343c0c55820f02e15158485250042c0d03c0b120211a5010610803030b500080b402d041c030305c40350500c402c1d86880710110b51000d071070b2042c002e4511100a660240c94851b41d440003049440c0c42c00040c4800c0d1800d0745c5800d11803804501440d9942d00008004c10f0b900c0544200c1c3c0b0040c10001c40034024402c903100c4c15100d9140200348414441c460348100c0c090300041c24041600619458a13a020005510000b804107006800403400d0381255a4075024152000f0000200125551250f61581208102e689034010014040004103d041c4000126503005000c541020a1a40184035240214250700314198030300814100c040203075007900120441d902a540c0705d2200501d280035981c489040c0a400c3c412410080186400d501c20301c5080303058064001d00c22203941b900c0198150b41c0c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 542993111 1250 542991861 542991863
    0x803062812060b030a06021908010509061c0c080102030709050f0f01230c0f01180b04170f0c011401050607032f030c1c0507080a030f2d05071e0804 65
    0xb039280c8039588500c0d41c0070301160707000501503e00507036900d0341c10241c4c03416100d010400d0310034804d4250041c44261155001c3d5644144159010104004034808a40d80942d080500601c0c001082c6804150030700113402641c0901c140d521005c42c01915002001403c2e030b4041c60341a008240503006898a42c8906000d00c1c034451043c0c641010400e1664000c80103509c1106480a96032210544a03d0401c00f4840c401c1484440d00201a422a01359514941504054400703490400e0802001800045400490b1058045421040e0b0350700c204102d4030380a490320f03d0701003d000c1c1c50b03100006800c2c01c010b001c445000364190703074061040015540032005031044101ea0403a1a1610a081c1407880c000c04c002c00c002041080244405d41d1807800d8001c00811003401c001c1004814000500002c030703040152000c03490113083c007041075100d01c401c501c010800400d0302e01c001c4420292000c0c100c5a032007880046401543c00030301907940c81d0030098401c0744540000c0c0391502000340380c0007507903403107035810716001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 542994361 1250 542993111 542993123
    0x103030c15050c030a0b0f0a0602030315060a020601090c0e091915060c080705030f0307051c09080901030c030e24060f010e061c0207061407030e06060d0203030d05040803062812 78
    0x80100023040c4c9645894105401503800002848488600e82c00d41082a02007240c419140040584009480c0c41041c425160400e4582d84000081405200070780c229040c00752100c030003440d040761200300380320582c01820310031890700344640c8040f44000c0c00380066540300e8503426103600440d600c0d1441c030703070101005565600040c0090706403080d000b80114001e01d1140e80341900c1e500c0002d101c0381e5610a00c401880e4081c41d001c0a48005800300066581031b003030909002a15a803400401d0b400303030040301c02d4214280074881c1360070314003881d071203110703c1c840c510080034681030340c807403083c40304040b098000140890810003208005142c01401099880080c03e040d00c076080441c1040070a076045914201c0b07015464030321842c0200c0c5180f545a40c003980620b4180b02d80140d148100e0f8813040c0141490780164042c40c0f911040d91010401c132641c201601104003c2c2d032a02e424040c05c190416240c25100718410418006102c0303003100c1c0c071041c5a550003a2100007601d040107003a034481c0c1c0a02c1c200c0d84 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 542995611 1250 542994361 542994379
    0xb090d020d0c030221030412081005060d0b120d0e010e090109090c1707030b090303040c0b09030a0b16020f16060302090f03010f0b0306070c0b010e060d08030103030c15050c030a0b 79
    0x5d007031800c2e203c10056440f11300c1c0b464503400d082c032346401340c840c0c81800c04003080044410000e0002c0214080800c80390256446c07551210109841c101a00f13050403004d80240d002c90040240040009401820021507690001c1c0e11244034011a0461240561568010341000051060071010f034004c0312039034030a88c03510240555508003c03c910304800348840e002e03044410708009000e01301c8043d50b0720141c94005185903107850f68072400130903854010210b1a610205031620b00ea14108400c207c4a50040c250424602d000c0c0349902d1541401900e101c018001d0020005007200000f40d0f80105220090074005210b003410f0b81100250865120700740d12000112041d4040e071428032030b51604409082000ca040d1191209048c1740c680702034810001c00030302c1c08000002c40c0c9254401c60644150040c7e007800e03500e440002a00c1e05001c06805040c0d018000000420190040c00c801d040d0351080b112000c240030b81070316a20403200c0c01c8481009038201000052000003841c0c0c018406c28a004080b410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 542996861 1250 542995611 542995633
    0x3d12170c03160503030f0709061b06060f0b1909030f0b1506120a111804020c0307020a0e010e060103111204020a0803030c0a09080705030a02100e060f03040b090d020d0c0302 76
    0x10079090b03881094909400002c18410388400402c1010b900c030b2118103080418a01d040c0b0000c0071709860f071100c1d44c1d21140401da403034104900380d00058001c103001e103400000c15490b04007c42c1154004a11510341c5c01c41c100c0382c4c0800a002e45102c0b4101ca4000a2000e821107540d01e030841c03200d6004056540d0031000d101090310a039103107009080012a104414002d42c6400ca440b84100e820070111146864000e0001562a000010213900c0800c0705880c00360300c40c10740014040c55800b44a02c000c0d40032840c081c021980501040300c03035040300c01c0010407141c00e03200c94005400325603030503115203580380081000e0240a4543e2106680080c4058807109003503a850450508540003502c400c3c2003024001240304400d41e11034100e00c06030203800c0182034100e1820000135510003a00d83c00034017584040d420019828040c0d509030080f4000504440d13510140d0644500295004440848807003c03000c0201b400c8401c0090342485142c0c168001f00290041ea4605452032000c40320200e08507c10944002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 542998111 1250 542996861 542996887
    0xc05180a03111c050a111201140a200409020703090b0a1209031707030b101e081003060f0903140702031b0607060e060402030606010f0e06033d12170c03 67
    0xb0851602540d0307418506c441501c10004000118190f6210903814088007442880d0059030300c3c1d0304001355035400110017030b09141d80c195104102e40002d10200c07002c28006000c1d01c103170f00180b0565119617a000341e52512440d040ca028010041d242001481085041c0350b4900150312422026001c1c0c100103c9801218801103015502200c40600094451003284028100440c11251140407403c020b440204030603050b0750b45040b1400204c003080025000324111500d0f0030341403000740d6003011050210402480404002e0080321804078001030032100361403013000c100d00542c0c01e043e038014050011401c20345d801100010344007015650117402000003600107075043c8100010419240c0c0942a0ba00c1c090041501b030400090003d81400f48000e030302165075601030035a90f5807190071580782d900e946074803652112020149100300d1507281055402038120340d412101c46000182500500180b588034002845400c0308410010041d40b108240380d40c0104048028146a4856078102e90400090b80522 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 542999361 1250 542998111 542998123
    0x8161a0a230a1e030e060a050a09050d02030a1709030702130f06090b040c020f06040b100e090f06071e0516170c0d0e010c020918010c05180a03111c05 66
    0xc80810481d0501c40e011094207000f4050b100345a060822255031111017040d01d4883c003e00c1014a690703030380d000030040304450b0301050805410104035100c0798000c28003c0c1d560f91180201c10301107500200b00845401260007190300c0340501c4809103003803040c5542884a001902000a0f112944a03400d1002191007071080300e0040c01100d00100b40040000c090004070741a20701c10f40119001801c00210002c0005449608641c1c404821841607403140c03001c801a100b85e8115030010360300d0b281404001c107000502518001581e07001e0f10450b4440400070390304030009590030649a40c098512524141c002c4018140320842a25284403c4c4010f0b80c40901c2a00b41c0e9100c01d034062004986607000035010440394002d4181810600703900a0f5843c00681290302504000f07200300074950016a50044801220794155038900c000d20459900180240c65500031400a0b0070803e242403080003145000501e87c81125001703100301008040351820301c11100c002d000800c5d90500d03445500c0002400c20000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 543000611 1250 542999361 542999377
    0xf03020c0f03220b070b1306020906030c03160806030601060f030b061b0709020c2e0c030515010201060b0a081b030c1c05150f0a030c08161a0a23 64
    0x1415010f08084180c051091071030b400510078443c00384a12800941320086031500b002510f024010107004071710300000648548000d10340c00880100620004000f05400f840c02040685490345205540080440788984111101079043d800040108400c5004d0009004000d40300d14002c20b90b0b8007610041003099105251102184401008200d0000310511620001e06220501946000700340341c80c26503500342811125909142403042500290012a031101400c04040403e1108122808018008141c22075100c000303402d021060140542c410701c0382006036000c403c4c21034140b240da103c0848180340c009001d43d4080801220304105003408070055442030ac0782c0e80c20340b03a6400505405420240780301c201000305504000c1884040c40c0c00f2207421846210648600e1602d0381d42500003107102800e6440276042000c031100118441c2000b144d102c200750341c071840d001038559803401c43c1285281400d0340c4401c41c4800f4004208158850000c0644411140da10301c50308802540020509030300c400d031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 543001861 1250 543000611 543000637
    0x30c0912050f0105060a0f0b09061c05040303050109090308010e06061b010c03150308070615051201020909090a050d08040521091219060b0a0e01060f08060901060f03020c0f03 77
    0xc42c0d01c1e01e0000900840380d20071410b99903260020f144c282502811303070043c090755040c03480c0854a210662118002e5901c50141c0030704c0003805140c422200002020305a406030f0010b8140000402c030113056014444040d685940c40c40c820340e190010041c28044081d0400798001803c21100b075030040781d01c030072a0222000c8800015021108030300501211104030001046100c0742c042040411f0950b402e446407107402c0003001c582550717810b0282c244a040350300507641c04086201005550001540900400d50307060f21400002c2d00c1b03004c08290380e0b031013044005110360300400f2070798442485900340c40c0d00b0504c44d00880b00b45050384442c101098440c0010590b12010101d2010003a1800c580b50300403070f44800015148803032411412402817441c00e14041c080e25161070a002c1c0a45484d00c0b510001d24100304030740591750b1210b400801440000c0c00c00c800254840001c00c0861510007240c1d4100c0701c598480f0109004250015406034111801442d01030143c410213021200d420f00c010420035280d0300c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 543003111 1250 543001861 543001873
    0x170919050607080f01050907050a02070305010c0302130b0c03030103120e040203131236090603080406120e07033f140c0a0807020a0306090b010510031b030c091205 72
    0x54014035021008040806041440004201c0f07910f414a1f0305812201e549405551b441002c002a0302e071040c19400204998a0030485080c01641903000e80b0b0891000d01020383c04903600c07508081c2c240035203542c443c869002040100300240400080c115900a10b05280a001c01c101d00040c04a0704100c9048440ca004801ca410400004000000401116007003a0300c041410800c80d0110216160b1102845154074903180b200c18aa001d00000400c141c80043c0412038407850007807215001071181c180030820f080301f520030b032080700e00170307841200002030050103401d03d50744400300914180a402c914000200c0641c4c0141d07099420300e15074200301d401c107404009640c0c03140144811440000ba4003108001e0140c80140400850410b000781d801c106c14981b02e0701d0b035000041c40315410303a00040440b494851000100803585c84e406048603070032140000741903030081c01901903030701101e504e00482c0240c0c0350580d0058065030020328140f060b890005045d170740304d0340152416000d68005460981c428 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 543004361 1250 543003111 543003121
    0x30c06030c020a060f1b020a050705120a14070515070f06020a030b061219200a03060b040e090114010e060d1103010e01020903010617030406030e0102270f04020a1709190506 76
    0x1410015001d041a1f200400052516441d8241c8902c41c0c0c0c06041c0c071640390800340320042e00080104811131504950300300c02c0c80c85001d1026a88030030078854140100b8145990213021206a4145d030f1017541c000e0904040200280d40b80c000a610a840c03000c24599510389240f0503840300c2000e0012450175201e0b03818282030041c400c115040d481c440d10140c40741001c081d594441030356001d44501f1a03100d145541c407801c0d1039070250081c1a5a400000c001100401e002802806840700075000d0075030340000300b007800203803040000344020900904540762000004a08030f030401000c3c000c00b10303014158940f512480c2c40c00007400c1d650f0071100402d8682d00803648160783d103020b2040c1d0000301003407040c1c0c60b005001d1582d2a0b490b402240f00b03980c1810340d603002101e0380c4c820a40440384080300001060303510035840303410f0529002c0341800080c051a509800f00d1058100340c800c03a03040551a45981050480d103191100c1805002040300c1c005000382c480094600c25040b00341c2d41c0d15441840900300034900 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 543005611 1250 543004361 543004391
    0x150912080c011d07030201030515040c020a301220040302280509041e03050c0f0610171504060501031703070c060b19080d020c030106030c06030c020a060f 68
    0x1c0d42c0010240f54081c40050700c0d02200040c0e000300b00c80c0d080c00c0201d415070321950b10904880b4400c84880d041405d1019021841c0e030f01040c24801284100d902e41c100040c0710300340c01542c892030382c1d002059500d04008640b03030038010100d00080807101400402d410407000001070701980352020240c02c5641c04070f414030441c6002a2402c1101d80d1a40c030464256240001e40840b9001500c1158010300c0f980000c00c0500c000c080c40200030000c80304402e2451615071400800c240e104165500260080341080c0e00c0034100400c3c141e0042c1c610f9015003e0b601d05007500c90420480d2045481d8079803181e0364042e00314252070310040c0d02c0343d07004030400500b662440c1015401c1d0115244120000d6404001f00005150004040c0d0708a5400800010320013043c0008107212a45020507561240e0240c0d000081101c800109819001e00e95070a03500d859440340c0a04d402d9400c03d02009002d0300d12030302e0900200d4840d42c0130700f0b61000c00d40704841701ea81568a52000f00e944560211304411707240c00c000103060003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 543006861 1250 543005611 543005621
    0x1401060e061603030203060a0909150b01030e070302011103040825050102160306150b12060a0f031502030408091003091a24030708031b2104150912080c01 68
    0x416240c1c6031500082c40b00d5441c032032491200041c00d15601202191071a2140301800004c1c09145104010401113414a4490031303803103000302009581481408a40d03035100b4094112140b51000080c80114210741c0150b850402840381070b07810748424800003907140c008010342d0014039840494150703040c1d2144284620007000b600100d040d075014080661200c0c00508240741165000031000801c03440d0901d18101007040d0703500c6204440c402041e100707420480c642c84036014110845200300c041d9900d8100c45800806440041e11480760305000781c0301040c07250020355105110380460380c601507841000400681c00100b407140002c3e40c0752540c504103d0130096440801850101c1a503182c507100380e021701c03044001d502001e4200c40c00003082d1003c1c2c50410001e0080c0841d1002e03079803200a5003118603076181010540000a1045507080001183c0d411148080c040c0207040700d80c0303024201050f030710012010f145420104010101d000030405046104900f01c548a102c4881d50798214644a5094030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 543008111 1250 543006861 543006887
    0x31f08060a3b0f120d020903010f0609050f0a050105013e030705062202010e014a01140c070803040621060f1202040902120703030215090606040915140106 68
    0x507200c1030010728612642c0050302e502410417003000d80d403296051b02190240000005500c9400d0034660080b8201e501c1d50000c1e0310460601d42c4041141c1d0303402403658182c482c284203103408503a03001c010b040c00d01100484056414402c2c500103080030541c640c05451200c0040c581402e9800126045c0200704040c066030350085100102d06a0035010034040900d102d03008100281480000d00f00544035074066444420007580f08078030700c1c5c0031540081080e01801e0454110244007001400200e104a40300c1c0701c01010722034180e64040c40019540c092490710b90140c1581201d51003000400140c0740400c10040c000340005a0700d000b405218040640c10031280e07500a2071090b81098401c1c080520301442840880c2c1c0e681d0052241c40e031503400814001d0540c41c0000e50091407844181c04500070001d070f508102c1e0700c21f07400c586941044100f0108507031001c3c1da201c4041e41042010803443d141c00c2d044402890301812080400740e007444418400c5032154101c003880c1038241401001050b42004442c03641c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 543009361 1250 543008111 543008113
    0x30c03140c070b03040303151820120408040906030f03030b180606031801021602010801050a030b010b0304060f180203070506070c03060e0a17031f08060a3b0f 70
    0x8050030615850b151419406485540140480000e041c14802d0300000c80700e070300102840c0e0405c1c0d19000020343c07200340701e08070940f0301d41000070f5188000c0c01d40c018441d860b101014a80d0901211404020307007003d003c2c1c003da4850b80184800318030342da220b2040b60002c6115042c80100310500b4078002d001d513112031810520422030b1610100e65803c0000d00e440c2e100c0d0007101c1040d502c0d581c8111401c1001c0460101145561000c103044e82901c10108403403450078000d0725902b1690380c1e21420010210941d000041200100c00c0040094079004d00c0a181c11511a0b00701141400706c941d40c2e0411100c80030111001c1e5001000b00b0415400c05210000207800142c549d50300d02465034490f4200058180300040c40359941c0c00000009010a00045484a9201da41030321885481341c030326405a04140d424012080e0000003200d000034140403a08119221100034113410754880d54000024070307000040080000340d1048040780c023018a00030f040c0500000d04101ca04641010303c5514040c040d203000041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 543010611 1250 543009361 543009367
    0x3091b05010813050f011e0f0e1b013b0a050d29190509011b08100302041b02060a1116110d030509120d1b030e0904030c0314 55
    0x8503903400000140d100f40300b458a0844141d040c40c04501d0010765014481c1c85520341204070b00070000c0c4c0050520b42d03482c03500c0c060102c005540c90b8982214101c4040c074540c1d612221000d2081800421501900342c014100015208040c2e002041901c48500382d942074010300c42c1c40b218804080c0f06c1c201006080955500c81c1d52420180030610b48442102c1c081d1207078048480c990300c00e2200801c0c481c540e0380c0c111b50707085190401007196088001c0e03542e000105141401c2c00950852814440e20302000300720209400b0240402105507158038000d05807242d000100d010200158880d401030b80354000b644046140b925a07010402420a40050042a9050304054007820400e0381d01c01603941414900810401c030050381e180180840b0000c1034904d8000c66520768103814103400801a119952066a001205240d0500d6154503682e008a0040c0411125510900c0c042070710740100e20b0b010b100f42000c00d94510b0b05c0000590141045500b00c0000e2030741c00e1010708040c0d0200400081808028410342 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 543011861 1250 543010611 543010619
    0x60509030f0d081b0d0204031b08010c091503020d0e0c12010501031a060604150801050f19140d0f060e161a090f0d050105040203160f090c09031203091b 67
    0x3c0070b020041d01034402ca040050b044244526028100c4540c2c0c00b41950031995039070780e1301e00000b640ca10400540108440a140010342040c10302a20310482400e41c0d510300c4403401d2a00c2d40805010b001c50540415a09118220300c0318003034072440e840340312031000400201d0399143c104207000012600c20b801036410407004000041c4032a54210403480c80300c3c1c0310030841c2c2c1c0e100c01241880c01960710294500c244901c0c060301d029000f02800c0e05807a010f0310302064a40f035040c248030050702c2c484900c0c07000070304c08801000910944180002048802001811551950f844040c0c140d4207070002502c01d0740e5900d42001d981d01c010000840021192505000407034541000c0ca1084421132406c070865190024500c003560340ca001c0c065602c0314000b8020740c459038080c00c201c0d000340404c403400c9029100c1c028007003028480c964125000c07142a00c2108080074241940d040142c012030f41c0340800e01c01242c001100003520a000302400310142c0d580002c441c1c18a0074901c040082c0c1c10406121005900c4040c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 543013111 1250 543011861 543011867
    0x3200a06030c0504141f03050405062202090402150a080f060d0f060b0609041d01060e090c010e0d05030301032616081602060c0a02010201141509070504030b01060509030f0d 76
    0x1005c4170b40300c0c0b000c00e0924122001003080c08107034090452440e2110a10646441d0b0958045c0c1e00403402401180c01e182d0b50109000c00000f281101c0d4103941d5461000346005240c10860315074428806090300070f44e088613119480c000d4000175500404210300404000f02241549003032907024004680c4041081680d4861202560511f43c0c003a00300d5403100007401c42034503150b04a400b140c60190080043d48036200c201902c80907894080340302075080000000b070088120030400e01511503007003d0070b008042c48005440c45031950f1203017a0041c080070054400b00308180065802580101000c8845907403980f80f041c0c01d0408859440071810062040342034100ca10582800d6040e445030540c0d584200109600003e5080158003d40c007031000640d0095501c00070411000b81807003038000340158243c6c011038450003c1c00f11610035000e42810050205881c0c600c098179041071035800c065203041e440352110110004260050300c041400024442802c3c181000600603031002600a0300034240c40250003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 543014361 1250 543013111 543013117
    0x1501180e010b01050316051911100b1f0903050613170304031d01050d0f0b010e04050f07030b060f04080601031104050709180b0603040506011a030903040e1003200a06030c05 76
    0x3440014046c1c250b0600d1030703805201143c4c29a10b141400d42d03641040080d0052261303603564511020b5000d0000c644014840b94080d000e11040003c1505444819444d8082c034200303040003440e010400024800400f040d801d11002d0701411025141c42d030484c0361824480d140f11111950040e039020704000300f002088d4032171000d03900c550a44001c42503a101d00c0004840c0d90040032002c500140c90507101c066800c0480d40114040502a00e940b0b914120380e4041008940048544515102050300000e81c024465800103a03016801009107050084041683c00c01d0740140c1c2014030268071101c0103000b405040480b11250b1541110140214035105070001c00194080c4a5510004110400f075092203a440d00095042c91019010365101e01e03050402030340c0e5500c28852406040c41d0034503a140112541001c40788109c550390000c515142c0351461002c4002401054190a500c200c00003000080d0148070030340f4116601020001940002c0c010071000710301980c81402814504014801e05076013010075 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 543015611 1250 543014361 543014371
    0x10f0e0108100519080d05070f080903191203050c0708070b090709093203040e0402040f021204021e03120c07080111030702070e070503181501180e010b010503 70
    0x9551180c4554811800d050010707080f030f55008401c500b44207400220102d51030300b00c5031008100c400004a01209994501c14420080c0c030300850030301c1e8100400c0c2034074024020030303c000d0700302da814a1894401c040380048041080f201000d00650134041258140202c0e5000850f410307903a4500500b507038a043c543d204c1c0301001040c000304500020003210050090000a01ca016420b0140d44010702d822280305240071029071340095648030306180403e80445220101503084015446d090428943c6582524001c0c001c07030340b00d5191a65042003810354000752020640d070101c80201410548100301440740c0c14805941c40181c200d95102c610396000030304941d5084030444480c0d80e192004903403400d044094121502c035600301036001049031201b0000f5446012280d0a40e402c1a40f074058907003000200351001d10004e41c092010407481c0f0380d0b0000c860342d030a0891046461500e0001d800e280407001c264043c84c0c0d02c22500011f9008003002d0f0040c21003118014000300f04d82c44840e00041d04900014003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 543016861 1250 543015611 543015617
    0x801060e0a1515020c1503070f05030a0e2e1a01030f020c1b01080901020c10022503200a02030d050c100e030a1d010804080904060308120105040605010f0e01 69
    0x41038a8000e9052904001420015010302c03120f504031400039644010b58401a030007840003062114940c0c0c50341040e40c1c05007403140c0c2da066022001e0407040f2959000134200e02402940e84294644503078041111011005c41c07a8402c42a490390032044440001d01280c0d0303008490b08141c5400083c001d00e0b203804207200c0d82400d0010f2000c00a50401009005501c0081030a100e4010822044c1012000800c003250099a81c2c6800d50380b441e200314207074004e040bd0404140d006807202c51400e10030742c0161603546000224954240100103116801c0b0861300815004103071030034040b040d89800590010030481001006207078a04c0240d011903600d210200da04400c0145c0031500000004040c444041403000c80d00043c42040c0c0c42e0720070191654442c59003000810364840499960b0103440810484009050711054140d9480c1d8035851000d42c422403500e548540ea444005c030001f821702c005050700c010800c81c1d251307666040c4401d000442e061900a1810700604850808002d40c1c400300b41c2050740303003c3c6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 543018111 1250 543016861 543016871
    0x41407360911100309020418111507060c11011401170c0f060a0314040b06040c03140613021b01230c18130501080303041b060f11070923010801060e0a 66
    0x4013240144401c0308025840b606040151500f11404103180c2101c50003011250000c0201301d0030010064405c030050b0a04079014082c21010a64a62084003410b0603414030a4401701201001030841b0080200c0d8102c881902006004d80e0b01d09680030215203140d08018410f8201c00750001c1e0414803480500c03445500005420b5481c14030a4200b0143d00040c1d031070114a03030a01c1c2c503241c2103140040b03602900880c03400c01c010242a01ca8003684038001d8000380a00202d445884c240b00c900c410740b20b507051410390200040b9040240a20954070f41c0c4d8143ca00000d080e0710a40c1085c80c45240540d1090240c92004092040d402c0121049404414081c0602d9001c036180c1302c0807803180000301740c42610700d03840c250000441c000048003d620030b9205010345040c41e10540c03a2600f041034517014440025030440c5450440c0f500510881281e2460501103504040c1e0340c0d080041036403203e0b102140c070890101c0180302c10b00c85041605001d8442c0d18000e00126041100c076101409000301000100c41d110 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 543019361 1250 543018111 543018139
    0x130b030c0904060312020c0d0c09020702190611060f010e061c060204060906120606022e05070504030b0a051501030b010c050714030d050f03041407360911 68
    0xc03000315200e44070081c0c0709000240d902d080642d001c0d041a507441d805405840c0a1030b50628001c000c0850031648030400d040c072141403019580080d040520200d07080070048004940508181c204500103200a88d13070380c8985001e200003d400c4c80c201070700c10444454060014000c0d00812888164070100c25106004002880074441d242480907610140038240300003804101183d018512105070303005500c4030900c6001c0c40c08081d00b00c800600c21140141c000c3c8680f80b0400b240c50b840d034800350048000e80d1801654100000c0103d5a00391180d101144c0700080800c06c0020002032a54400ca89400400251070856071101d021400021807a041507a83c094020072a8090318186013165040011145c50a8031004550030030421240c0f0700c1d00c2840f030502a64889440780f01120807010032907440d5030854890341d450400e0741c0c2d64a29030102c24080d407000401c0701042d446c040058114981611010405110541400200350700310807980182051001c50108942d2400010407030800d0760030000b1001c0d6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 543020611 1250 543019361 543019381
    0x150c0b0a0b0307030b0c0915210c0d0501120204110a020a080307030212190b030325060603080a0e09010e010308070f05120c0c041803090330081b130b03 67
    0x1040c2c0005008214070b45c1882031041c0e121001d00780182060305c4c1c0c016080401400d94901d070092180000106944014038400f018100743c0071504201e0000c0c8060801e2800c0e21050250b4009801c030400d103200d0b2040c0401985054050030030b240541c0b10040386000090040251542000c0101a0000c0000000b10380c0b0320780f01e64100c40c1c02003110750300d00680713042c6807803000e0740002c01206030304821b4140150341805103804400c458030000c084442507007050f01702c1c01360b040c1a01c1005094030600d135251000400f041c803110041180c1a00340e513a41113940100c0c0204040d40e20180c005040030301507000107100140350b14040302d402a4020310001c42402d040d1600038030f0000b068840e1550030304085250548441c0000c3d2410b010307601158248265104101e200340c8c003140014000c0c00107801d9450030404501d100c40301981c001c680d091603900765108009504104561803134800c0001d00510100404080030041901890000095040c07800032200c4102c1c10085080c051070340d103402c0004c042201110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 543021861 1250 543020611 543020623
    0x10203070609110a08120a1d03151b1809151507021e0306011503150b09030d1106180f2d01090f110f130501150c0b0a0b03 54
    0x648030710180110520361810018001c91000400c0c0601e102c48408181c100010030040b4001018101040c20101e070b45004071601981000d5039980c0c003000203480002c540702071010203000b0000e00c06603d2181050b5140c100c07043c04840010704010021312801400780420340240c940311604503100c14507a1900d582103034010235010307012584255040022440400181c0241402034000c449500d035048402e110300c25458400350080d9031607040200140030750003401d22080300010b594030b400104a03c100d090300c00ca48015802c2110b4030311001c604159546030070880101860f111b03160485203440f4a0241c2642c52101a1862410b820701c29040d21480d40100820b040700410381e400c481d8150300c2440c0244503010413207120301c03001103445094038040700e050040c1500ca50b0b004281c4040243e60b601c4204820a90300c0040d0760003418100100c4590740e4007000507544005184001825524040120041e41c06105c1a10203006041000b032001c02d02d00360302c05620458825000c40d00c0b04101c000242421 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 543023111 1250 543021861 543021863
    0xd0212010905071e03170705160b2a0d0302180904080c06060d0c12061b0923090a050601030608100203012c1503120406032c10090201020307 62
    0x241c601940e100a02800241100480700c86a4846008002a00c4481ca01d000b281c0405008030b002a00000000c2c1c902ca4010288180138030b045e07810007200742e1030a400300c1740103600c00240200049962441e94a50324400c1d1501c4c2c4070011240a07080d4515040c0f51101680c00b00081032540c081000e42c4803c041c50142d42400400030f01c01c45081c40c051401e800940c002c00215513840c41602c0001d602401d1a20a1078102d540001012000c41e282041c100b240c9541ca0a0071104a6216290503040c10254000f80600b803220b600c44146450400030381003207603081c030748010840302030321580c20401d40c4940b494aa0402c0000001003415030b9900c006034060f042c03030f6100d4103a611a0407036100005460340d0246040e02c1c0010900d1800c611207001e280e01b040503680e4814a2514000082a46400403032144000039070050141e89558041c50080c5179290001e030f1120380403d850781001641d60740c44040d40c1c3c210b142e550307440001d007000315079055580702000c0c10070a001980d21203140c025a0b0081060721a0030b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 543024361 1250 543023111 543023113
    0x8070c03180f090501050427061d0609060703021801030b0a03170c07080c090c0a2d080612030a050706110d06030b070305070210240602010e1b030c0d0212 68
    0x203a0382c05002e502d41ea858031070248482d24000003c611440c09024400d480340e00d4000002c2c0d2107081ca50f41340c14080310204d00b100d074155210b00d00c505504141e10b0010800d1501009407190b032600d800034030309010004004508240c41045620841a44500c0000c611030b420f00e40050324405107008118009030075000584008101c604518104004030010207650f01107074107817010320ba601c00c00d84d81e480003070341c0c50551701c04003045c0001c280200000107400085030034501210058400b15450b410401e140e00c8802282410341d07007580f00740b504044410307080f0340d080d0b41e920303841c042c42001d454903030007681401c4081110004040d801c4c00825041113240320561074031643d4a4000401800080c07425110488000000d0700010b0700c00c0380a80308040c481e40c044d401500307004074030240041c0209503130f0a0040304c20250720001c40c00310000100090180055400001d41000c0e04070180f4504203582c0c4036210020307900581c100007510049003800b40a8015183d2120301c1c4100d00c0001c600044400584941d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 543025611 1250 543024361 543024407
    0xe250e09030c0706080702030301050913060504060c0f0c0210051b030309150106050901080105090709030b16090509190f180506100501031103060906040e0703051b010c0308070c03 79
    0x28104080001c0104414003400c890403980d8132582584ca404c001c03200280035030030500040040707044c880310644e40240e0107032020480041a03503414013201d509030340c2590300641c1d842040c0103042d049070326a68000e6a9003020240046140c1c0000e2000f40d442200700108540881c40000840140d0300c0b0b02c007142c03403890560740caa29000c40ca4545d0342c805945c41105840e904000000c20a0181302119a181b00682d65500c5582c20b00c0140000c0b02c202520503c20440d5020001010840ea0b1b01c0c91401412041000a1440348000004008003031603000144103005090502ca52115182c10f459000300b00d0b00804550319581102c107800410340812282c6946e4a51880c080410401244451003040103040500078161520011411101042150500060100080307459468104010b42d0301100080001c202d40f91026500e5003041d99a50044a00c1d5000c410000d4004400760350034600040e087c41e1817108c10701c103900c0c000c1202c17601030408024045401c01c10400d061041458540d1802503081e1505 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 543026861 1250 543025611 543025621
    0x2040b041d0a1a070e0409031101021c23160c1a070f03020310030f05070f0308030711160303110a0b070e0a170304150504150302090111010e250e 64
    0x51507042c0c02d034080b100d0b01c0340d20141d0b0710344485290400c0e01a0010340d94002410a4000610004103000301c01541400002c5550041e4080240020000d00704844400326a142841d4108000d40e8017810542d002c0c540e0040741d00560680000b0700c5036011528032900d082c0e030b202d440c9003034034106162080036010704002e43e030301ea5620b050064650700404a0782d52f40e424440b1101c004400b00d000544207801d00703008003601000803c600140001503d4011003e0300c2c241035403211fa03065500e003982d204071410b120100c10000640e40003c40d60014001c00c1c00a8802c000b03440c0303034200c01142c0e540001001c2c001421b080307804e102070070006000c0850f80140100054100300707070042e002e4450541904d00c13036030303040c4c0300840d1403015036940030313008200c05004600b060704114592a9440060340c0503810440207000004500d1607654031030410343c1d183d4400680c1c0e0f2010000040000300d442d150220b03241e0500f18225a1a200021a60001500340d402181d9901003d0080880b00c04660b00c220700080b54501401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 543028111 1250 543026861 543026863
    0x1a030406150e070e040e0c011112030a0e0708010618050a0f1401050a060c0c152304051305161b140c0f0907090501051c140a0b0f060702040b041d 64
    0x25003d100e00f5141c0500c0050070104200a60b80e64080c040a039400c0015054607a50050040820222181c425aa65a40c10700c062420300c0e00221021a04151541d0022455640a00c1030a015060b040001d02034103081c25035410102c404800103011a5075070354001350505c041d0740d1298000d030540882c01d01843c0c01044209540a00c2070107102d119920304000040d03d18040e0101100e860f074007068880c0028a481c4004a10040f80c01100c42804802d801420f4515000020000001c0006000c03d494070f0904043c852140c1c1005a9000014544020b12070000d1003115000e44182d0a85810401625511203250541c9a203170340007031201e0017809050041c1d1a0201790104881c00966559800b05500020002c03450f00954038400400c4d43e2402c1407000e944030300d0080620b90116a00311035031000c45200001110410300c500d111a00c400014040d20b5240ea004510316140101c50280000b042c03840012450720404400a00c1190340d80340790368003511941c00c0340323940013000780b071080188054440403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 543029361 1250 543028111 543028139
    0x1b060510030b01080f0606090703060503070b030907090204080c0d020a05041a132a020c0d0602090a09062d030501050907090f140609040f060203010626011a03040615 73
    0x444646203440b002242414002070a000840301c608001c1c03c0c070743c0390002400361103c400b4003094209901c038407010640342c82c100a5100148a454800390b980c0c80c0202c00c1d1410a409600700c6000c241c01000200200440018503619548080b5003944034143e60380300003460042142d10403034200703042440502c00c0c1034584501c1425001c0503514400c0e4203085900d038804481c014a03039200c0b0f000903034005140c07a20b110041d050003100f5a004880c1910010b40002e0f243d84030303440301141c1058000400552a0900c4903c0300002d041c2014244000e03820452074810440081c01011a480e261a203401c0e550700e03103902403800564004008000c0ca0501e440d030143c481001d030085c940e5050404401c190104e69a204010f040140c5801400c2e0300d481d28820030000003009441541c170007040007090404103110b840118001c0c240c9460300d1841001c51001d00040080410704058444544030040158003e03481450100f202c0c0040b80d5966030361103241000c0141051100d9018501c000700001c50b60168080437 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 543030611 1250 543029361 543029363
    0x70507060f200405150a051902030d05100602011d101a061207090b190c020628020d08040b07050307020304090905010b1807021b03010f0915061a09011b06051003 71
    0xc54841034104855541c0e0f00c242a5080b0001d00204a546151032200750f123a0200440d030310550f450034810309180300656078240c07850303400080040300400c42e141d024071544448071040d80061150401031074646480d5a41d222540c01c0064540d00220400b4040b1462100490070044c00385403510000c0c2e032900a40320088038a0350116407604004581d0310114020b850004041920f0b010380800992011914943d491904a8011605020b4544148038640e0400310041c1c2084180120f41300c50729009141c1002840000207020880d01808081609100d09079801241d0703080c560340d41c2e19132030001ca00c0d510503a0302070074100b8602080c1e2420018190481e5004c10001c95540488000400d801e91840e00300741e421030096440305220550301503035440da0303000800d0014000100c800840400b001038881e070034020bc8120b0350600440799a00110310405002e080c1c3c0511446003101c07003030040c3c1031904c24143c45505018040070f0b01c82440c10440038400001e60300000900c0a8101a00501410b00075408 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 543031861 1250 543030611 543030619
    0x3030510030f08250f02010e180123030d1e051c0c090801021303050f060103020919060f080a11011110180f030206090c0108070507060f200405 63
    0x214011540c80da4240060300c1d0003039540e840281e007a90360b001e034030b07880500f031040405801c650400216112942400c1c601c1c1c00380402d08100d1003d072000400404104030a244100211241ea080b10400c10131070505441c0540c0440c1494020f68184140702c0c040b4400250741032240f8911015842d40c056404030020807000410b011070008010203550600945440f200240c20400c2c41d0840d02543c1d8100c1001c0403c00d0030000c104075100d40c003441c03d80e48007948664100c80d40c060208100001001611600c00c110702c094005541151300094440d00c020340901c40c6807a07488500700c980031180e4000c2008116415840724015a100c0c0300a0726810140d00a0742d8180000c000c1010310350068414040310034600c00942000c0b000c025000d001001c0c1d040c001c00303c440002021600090b1315042c101207031406900106628980340842925201c02d00200c0341c100159a4288100c580d006000d0b550055485000491201c04e0312003007400805500303182e100314090260142802e50380701d800030400d40358261 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 543033111 1250 543031861 543031871
    0x7030201060b07021806041d01020a0e1504030f050f010c2a0309050409060906020c011e0b01020c0d020f1e010f140708130b03010b030a0b0d050c10021e0a0303 70
    0x30b000100074092a44040d40104902c0443c1a40c1c0e0b104811050703004e200100009601c0004190520070385032840c00fa03420740d80d40098050755641c0c000300c1c8002122411100c2c2d68181c415002c42c0920b80c081e910000b021242c3c0ca01c00358003003100600c0a6005401240b00070001100c0c0614000c050071022000d0a0401100101c1c5c48400c4040e100c01741040c0ea0580ca42c8108185417405000040c46640002d0320402e0b0f4a510980004140303000411a0300c58800001c9204e40e240400f44c60503840350320300210818030700b010001c42e0b641c0104006c018070500301c1c1c4480c3c2c008214004210400d402425450b880070b20340b603003501640c01d0490078400004083e0b0f505000c0b258030090546040751003104541b5008001d00144000543c500004c11902c00c0100e800d1102c1c41e40d40590100070382013a0031105001c0b00110070040002294400c24058010480c3c03001d00080f02501c0341a103440c6041d61150050b01c002d4060310b6103500800222104130780520348180204405100f05886014100c0d040703001030300f09 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 543034361 1250 543033111 543033119
    0xb0c0c0a0509130b060a0302040f02090f030d0903060207021503040606060f05070c03081b1605030c18040f210c060e0a1205070c0e09010207060c03020301060c0605090316080703020106 81
    0x10b0301c1c00d070301c9201e03050b15442e07244036561281002130400500345a03015443d40700c0800140c407640500f007003500e4804400b41e103e84042e010004642d080a840c68000d5012081281c1c1260f8803141000450760070890041e914086030001c111120b2030401e1070140900000180300030030103540d01100c111203140d642c4541101c0d282c8400c803403d2127030802c007801880090350103001080120004000340d54003490072404011403074408030b0800a80314101c508003441c80b4400c0020381030034000900280320440350340d40c14010b182040d06c2c5504d0094005840b03850300d00c04080802c04111215041d80c98101e4a200d0300c100ea04000a082100e80d1b10125113003400d0414007640d0b00d0f0005840103125502c002d101c6120000710300c04841c0c503040581d0075504a076001f03400244011540d10024020701d0904000b40c2e55603184d050010544a10500142c1050b10420040000380c1e804110765032066440000411540c807410361003840c43c0203440c0f00c2c10ad0300700e01c00300a800700545403000f055020b1103a0000c1c0415656 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 543035611 1250 543034361 543034369
    0xc0303040203071e062001150f15050a1107090e0a14070b031303020304030b0f0702010515030309040c03110a030e0f0c0906010e210708070b1e0708040b0c0c0a05 71
    0xf500440c3c102c10340c0d00c4d0302c1480182d02414050705401d5138405c010860111401c0860309641d41d030070095603039215000041c0004400790100001510b8569400505003104510003081881800f10310001c00022500c0c0d0801d1040910540d001003035190800d2022140c0c0c000015144c2194610858606560f5014218024000300380c044c2250300d0304101c00e042d540c2300511009046600c00e8110110f0104000c040001102c43c4961400340462800640007807501e0303100682101e6018221074103100780e0303900b14611641c0001c100d400b80c000503900480d82c0c051240c406d501405441848103201c000100f81031985e039a155101200ca4400e41c2d0440c0c0d00517203000c4000381ca920381051566001038078500015011b50207002100c0d00704202130314990510f21128586110608900e450304d07040e810040741004040c03802c1040c800038140400690340f40000504800c8010751012101807040710000c282c00c010700c81d00405030f60090801c591840c0e030344c0b026840c545440e07004105942d842160851000310761420 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 543036861 1250 543035611 543035639
    0x20a03180c05040b060d0509031209031617130801091a0f0109110c0109050c240403140f0a0c0e0a0203040b040b09010e01141e0405030d02090d080c030304020307 71
    0x1401c8554201c6040c10081400094403035080056003005c002c004401c032006480c454148a1403112000d55154400d22546059149014009a50f19881840380d440344018581c494880c4642c00b1600506140b142c44c4590003600a4648400150013484000a80d0f8401074001c0e5003d20301c40e5035038103030010707a1000d08031340d4a0044d500d4010132118000107100f07981c080ea02c50300c00c0c183c540c0142c80c00c0c200715941c41d03030940d9a45c407022100303500400c039a10401e082c0910001c0d0602c910b55045004a805018641032030701031031002610380f82542c41e0000000f1003d000d4510702400300c2e41592400d020a0428041c40c6d6854803070400d10f8160b05002807002c0d9054800e590050b50300c501484000d4071141c580c5843c00c10042c0c5822101e55840e0300c1c1000c00c02c0300344112420f8203010500e8101324601290905105420301d0780245100e44c0d04010040041c170040200e036166101d140b40142c941d9030020116010903c5000010101070000a424001e0324001002d544501e1003202200d090301e44030121070707940349 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 543038111 1250 543036861 543036863
    0x715020f0d03090303180f060e010b0d030c140109030504030510020f040b0d06050406180522120e09040f1b0f06030b01140f132408060d0f06020a0318 66
    0x504500503040d20584250882d00101340203190218030b8072010750f01000040c52888041340c0300384020310034130200000d900035500c4d4802d40b40000c00c010000d40c008600ca0003005a0014100280f15201030200f1842d130351601000050310380204540b088030300e806001079100d800151001c0c826662a0100c00c601c5000300c40d400d8055822441c2001d182ca11801d801c1d82040c0c0070740107401e854501c0030410351281d1080400030065070401a800014014032502110b6000d005044079050b8144240140b104040203819490307440b2007034118281c0c0d481c5003280c44007003010a56a2242c80c4a05000500aa013040c0c0305441c0c0c080d0884500c408560b260a01a0807810310500018400d5088100704050190f40980d80c0b004041c1040303804818000350a807050b6126051070b1070301900200c0d0b1070207541008045003010300311480400360802d0391410b048400c1a02110200100070000c0000303a2103031900101078000c10f9205554400d9001c2c1072a004005c0d4200447e41000030313142c810b000c2c01c00005040b0307041c2c4807 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 543039361 1250 543038111 543038113
    0x60901020307021c112b03021218030f03041505011d0c03100b0301030f060b10050904150b0318010c090b071103030714030c191104050702010b040e0715020f 69
    0xd15180c80316080101d08100341c0c02c0500481003401c0302891011b010000b0070901100403081514801c0300022807296800d0320b98010544180403400c400c2d005041250b400a400f060300c10440b6414800c964030b184156007029075252408010300c0f040103c0c1c031048035036000103414140040d80e2202c403201e9981c403512280c07810310084040030500c4808038000464020003481003502c000c5403200078804541e0b1080c2c0c01103544000c480c4034001440003030b02c82c0714a144002c40e100c540780c2e0b801510040c214014404a648070790380c1c50459a4940d0440c0c0c41260080142041c038540342e1030400b503000b0300c2400380940c02da6194200200b010003184a0300c0b10380141c940310a0441d050a015441c0c1e8120040c3c1908000c0c0c15100400c40340001c10f0885074640c1806400740002c56032446d420448508101c500020401c865a0000c1c1c2c1038000343c03001d00d603030500f41e6043c0e40c0080c460391611422405003d19101181c0c0103458200d568800c0b0401080203800d8505202c42d018840c03204a5040fa551140400c0c031440c9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 543040611 1250 543039361 543039373
    0xf1d06090c0a0c0219180f060506072405010b1215030307030302251407090615030e07090f14060f0108060118050603010b120901140105010f0306121406090102030702 73
    0x142c03038054024190550f0001d0300f40814903134104048103002c016a000310464030a0710f0150703005d0f02e0160048445140c170480080c40301c0d52404022071803602908000a01d4684400003076049100b04034141650403029150a0000b56903442003c8403d50048808450100000c00041c0f61314a03e5040c0c440078800c041c008510f040c0d00c1d40c07821030080d04910803122460354241c0c4141c5070303120442807800350387d17006008501d1010203a84003503203840510341c841d21916003080030411000c14038103010030110846040100b03001180541040c02c00b161608049102880c00e400e4030000e1285d5440b25800702400d486003103080e220700b41008040008100244d0020b840c00d00060b16035445181c90030a100780c1055411401e40cbc9810006007690000d8000483e1f1000c04140025405010b40e401c81c1c000490074000c0081a05882e110550748a0500549060003201509082264441d600c104028000c20902400d404000d1425081540800341ca07500036119a402040800c0b1040c07003143c2c01594a60003c00d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 543041861 1250 543040611 543040627
    0x603020a090b06090d140616052a0a120306080a021507030507050d1701170d0e060c0106090203070e0a0e150d0212010c09120b0a0203040c0f1d06090c 66
    0x20142042002c460742020041c80102c11079194100700c40c00c802d00c070300d03209042d03a01030004040c03801da8000c014000c441d0004860481032a04442125030190040c0c030101000403082ca08600c1c0102d01d05e9854070144500d1b2808024450541c20110744840740342e406006071540c03007400c0d581c1e500000d28041c0d804608141c50b1441c0b03504100c01018010320900300030b800d040198a42e41e050260f2000781c03c0200b6007910206c1c82e40d000005a4601401c1038840303020102101448840d83c0781c600800d99010300c130850500c2c0100759101010b5034200e100a40092251503254159800603401c141e400030081401020002041e01d0701c0b52000c8181e504409070303550742d69901840081c4281c1103050540e04074082c0300c941c40250316a003d034900e02842890000c1000380391000c2c014900d00c02e543c4080b6015015440c004005402081c000750000d08001c0f02584030f4032103003002401e80d41c05a01000c92111000c400250f00c20700c80c00c0500600f41412044134441d0381d82e82c01e000c120340044034071681090082200fa0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 543043111 1250 543041861 543041879
    0xc180608031602030c0604060309170a17060111030f042303030a0507150905031c0506010f08040503040f031a010501030b060301151827090b130302012a0e0102010603020a 75
    0xb12a0340020202da89241c505804200580d001d50480c070002174a500000050141005104001d82c17280004280350114080d0700501104244e8407000e000c41e010004110141e1182c41c01081140c0c92101703490b6a01c45071062041c05e5807051140c0144101e465028850500d418118150f17555800740145251940c043c000301c5480e407101108032142c07000e040c81c400c401c0100e8400c40082c907201e42c0081d5074644001c0000d901050010f81c0c0210100e0a01c0e08200080e6449111001000c1c000d082900f0140c1301c920380b180c1503000301c0d040324a081c0340c8041c000051141401e20000390f120f401540041e2030741c03034000440030744103108100798101e9401c0004015041080c422801409020300e8007008411a0400381c045211240d0b202210b407028501148a4000b100041d900b03a4a040e520300b001317964910f50710f02c1001030707005203402c1c9103a020001035000d2500070b420034146604212181a55800c48186004800408480620015000d08000a0039500512030700c4190380e0028801c40c1030305d141200c1c079 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 543044361 1250 543043111 543043147
    0x703021006050a030f05010e010c050d0b040c05041e08060c19090f171e0c0406060c11060309100c09060f080405330901090611070c03060507030902030a0c18060803 72
    0x80745c2c1590b9506c0c23011451402803041062006080d13540c01e640e210030700541e0060b50f0100308050300c61480d040b640207440345c00030110b43c119142c10412208503001031a648101d00c00e00d51283e0b1840c06034008002d140b40400300102458541d4442104604e40b18000440e42c20107280500c00c403042254501303008940005d061101640c0b50081200d442c0080c1c0c4200c0420300b84011501c001030341c400e03d040c00c0280f900b0b01030f52024002600d00211031036155291980070382d82d0902010700400000006c140900300c20700c1300c61010a0300031018407210f50300700001001d42c2c615105050000d0014013043c851107200d110818000c9401900920a0742c0e01e06100000010b5105001d0b1840f40c0d65048070400d4451008686100b81c000da00001103034600d0303040480030303541c9021446054110410140000810001d03450095a4100340006840d5a4100c021340040c40403110181d418421608090704201c2c0504402c1c09a07016038000400c04c402204da00c10980302c4c540a0980740350002d04c504201040b140840c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 543045611 1250 543044361 543044363
    0x1a0103110d060612030917030f0906070303022a0138030309031b03010c050c0303070e1305010909020f0319080d0609060f06090e06090402060d140a020703021006050a030f 75
    0xc3c0d80e640c1d01d05404490410510450109640480800c40014421400440c10134114017a51034980300c2540305503507100d81c3c6d880511841d000b050301d1050500c41d5060b1540314440e42003800c185040c04601c041c00300b540038181d1000d5030a04011001b4054146000703018200743c2d0000041c0704000300707405442113030700b54986501403000384003c5456640800c007114014034400b182c000a820382c030040c5425117141d031040209001082000d0720b40234000000701c0354001c05a10300001d04003200e8001600c8003055040e20050241070400210f0750110350742c07000709168801ca03440403100d80d40400b8142c5800518101c0c0404500361800c1d640800e1014004254400a00d41c1c001b851a8450b10303030a0841d5403035080f0075078080b03413041d00b481005d40004501d0041e08034a0a20502890003c1c00115102801007009002e480d01056030325441c291034020060141408541c189945040542d42d0002e4004420550040c8100c0c0c0d601010b001945c810801602c0c0f02401074010141162942103c545c91550 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 543046861 1250 543045611 543045623
    0xd05070c03120c121b2a030513081e1006051e0d06060e0115050f030112060b040c050a0905040203040b150307030b040b04020108070e210c1306031a0103110d 69
    0x10a00341d044120348130710407001e04203d505254000d0304a0008024106040344a1005d1b40418a008403454200050b17040a81e4180b030056aa03d03203c07200411008156402602107210710b0b001da000c5c403650a1070110364524030b6400c0310b05000074000340300309071072507845000e400c200400103181c2d040e9502c0c1030760442c1c0800644000030030301a50307480d00211540e80d030040d851101d1450040c0400c903c141c1c40151000751374544039051004142400d101c07440188208808180007417140020040700d904958958a40100304000502480c075002c0d0403035001c5c00c4600c00140e000400803400c1d2400b0310a50703002d690000000c081d103690b500444803619580c0c166141d490f201301140000011116201c0c0c3c1d1003140f08d00c1d59042c0500745031002400f0b0120251103882031216201e0328003101e8a03000480c900b1792195103d1080c1c0c010600c51030701c0c18450151005504001c00004145081c00e071508180b08591040f0500b40c5014800c8031503c401c46428000200108420440c1e455145841c40d0f80c2cac0b10703450041c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 543048111 1250 543046861 543046877
    0xa091a120f0406051e061e0301020a090806010f0303020a0f020d0b090a02010f08040b0402090621010509070515180303040b0309060f060108270c030609030d05070c03120c 75
    0x30015502005044456038681020707681000708028590152030b070004800c4400c85e0b03c45103000e200c0c456009006101601450000c1454000c26410368038030001e20802600071035807051510300013001d40c41540603040d200c0c42000000202441f030f60750f03120126034255000d00000c2d1020713580c0d400718090121069030b20000c0b4542c014046150042080e0186440c200148402c403464030001d40a413220030319450501582100300000710312951285c5902039412104602540d9449000500f49000e07a1002102603c0c0150708003030782c000c1540214000c01000301100e07003483c0d880c0100714005281e01b000408120007404010a00c030002c500741c1c842c41c800101540e0905032150414a03032508110395a041580c4904144140200d51202198101400b071a044220b0b15101da45402c1e204030144040c144954a41c0a003800c0c40e505006100c10224020142c8a45041c0a00c4895803500000455003446140c4004106c0044c01401c0741e0101690540320b003001c82040d100400028060300400005200c400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 543049361 1250 543048111 543048127
    0x1303020402040e0a050f150907030e031b0c0d0515092107060e1507050702040b18100e091b0315010306020c0c011b0f02011119170a091a 60
    0xc1e0016002405080f4101070f01464a040d041e405c0c0d030005030a86801903242c3c030601c00e03151581c0314940e80400342a80c0d48905600e88040440080403c0301011055000106404400100b00d510b01c81e0082180c10490360070001400402c2508200ca03900141030358407940f002d4581c0c50a059030740d540500214251110311001854001400c82d8802181d030035000d0006440c4c040108500c01c04a20011507001440e01c10404400d040171060f014018006002c0046921070855445802000307514401924540f1a00c20316007078040840002e4602103155142c0a03008114a2148402103100d044403000130322914102e050100f1485608000d02038250103541541c4901140c812059402907110355401640d44c24056141800c0500484d146030408c5495014500985041c0950720728994100c140c6486030f0140d440140c480600c01e00c4502d60a00030945900144c6160010061f400c0d801600d110700b503a000610420205d00c500b001c500b0225410200c280300c0040049003101b041c04100300b20034600154 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 543050611 1250 543049361 543049369
    0x4020d02120f03030f13030e04050a0906020403122a0809010309080a080a0f021303020411160b04020a12050303180705040603110f04020901050d0f0b09090105060f03160308130302 79
    0xb1009681e450340008213100020341e560a0f5103510400780e017001c9483c002681d41c000d040c0700d450702440748542d0b02d407004a40300e80c490358410200315500141c1156115528036000c03000c044010700f0580454115107031004585139003540c2c00b07040c0074a40e003c05c07100c03020f940d0f610300190030050b080790425540d007184a0004900500070310002c82a1b031a8002c140c5065103405007654416102c0e444054018428058404200310080381a2070341201d0100c0c24415942e13100003d8040c1183e40458120b514026800340410203917020b0080d802a01e107011440d840b6418129a040b00d010010801d0344100001500c0360040000d1a10640c202015190384a6650000a09617101c5810a81d41c401c1034100300c0c901132800007144181c40d4420b50301503003410458000a0142c2c0100180054141c2d03c419216400d0b140e07943c440001550014600c0c4018100301c880c4900070081107034698000c842c00098100a8130f80004d90004d03060030000403035060390450360340010369049401e030900071304039042e40800141d071 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 543051861 1250 543050611 543050623
    0xe130803070203210907050a140405090c090c04090b0901030f0308040303090c08030c0f01061202121c0c050c15160c0b0d02130b070203070306050720010b0a05030c0904020d0212 78
    0x61060b21a13806428140c54003410034071030750b01640c85180042800c10a541d0403050024415100f00d8000640c1e689411030a4184001010580e0340030450310100a4000c02890142c810b441120004200c000512414072154035028040503003c25511101000024492002c2d11b86c40740c403918001c40c4000d0a81c3e2000a89001a003114441e5000480c01400d2018104140c1d401c10302404024000d9624241d40184008411075019000f984180300074910b06000b000f12480c04101d00120382c060344030414004052845145044869000d010704140d42881e086004c0d072103085152228614140420010b880b482c00c181408032a00a12154000f665004030800b80405c20911000940d0352407408520f041c00030542c2e001304414480a009990141e107002440005496020708001019102d43c48280c503103940120b0540803002400303031140444207040d040010710750340c10f840000c42907481394201501c4039a02c1d9841c5803c2881500000c01501d0802c03980d101c40d40c000340019100046002855040c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 543053111 1250 543051861 543051907
    0x5060d0c0906051009051c0203030417010207030905010203091e1302071a1b03040312060b031510050a0c060f1103090105060a06050712180b0a090503070e130803070203 74
    0x29940b510304100c030342407003001400c10810382e05c0c0c0307481c2c03440c20400002c02c058401410520a081e50380d80f00811500c040080302d001d00244070031603162030401c80410b03000c2d602c5000b0440000e0360300100051154000400ea4401a20081116004017181e854400c0d5000c00000b50652100c540411107628010900c01400c1041c06503400001d6000c19020084110f0700150001e0318900361a500f4070460300360803045d00d81042c0c0c1494500780021a01c4800d802402d1705410a10180100109021500e5035003041d004a004040d0f4180b10b01b0070400800b6100c0d8050b166480d0301003601c4012050003d407090f0b00c00c884803c54040c0006040b000d042048225800494500101e607660b1028802c8030700d400d484042c020105031405610b415172964444140b10442c42881041c820310741749445030482e1419000b00984050602c160315060700100003041409a0702c42c81d030090140c0d0030042100d9404a141c0d43c440c0410910741c1c02c81304220ba441948070b41c030003024201103000a22030380800c854030300c02444401c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 543054361 1250 543053111 543053129
    0x1091413021e03010e0f04022d0a060806040f1802010509030a060908030f010f030305070f02010e06160303050c030c04030f03032702031005071b0f050724020f0c0405060d0c 76
    0x2e60402c3c0b0031038200c400146c1142040d200600812005a503008811507040c41043c5151501c80c0524031032540114000005a601c04045000031038030703d9001c007030329110340d01c22582407040c070309068000b40480b5001d50010b80c01c0520481c2080c095401480180807420003d41103940c400507070b45840023100d44001080760f01400010900014050350303d0501c0c050211640d175840341354950354014140d4403591100503c6402046421015a80103040203001e0344405414135a41da9410810b02900c245005412000301c1d103400c011600b4080c1d8002074903c95076007580040e16090035503d680c9000d0240c040114201512194480c0b840002c0c0320355003d5080c0156820580c83d56030f40704040c00c0001003101154002c1c540010002200d50013485090501214118031441c9109030504803804040c1500141140c4210000000c2d404204c2d030b80304e00c64801e40b0440031a451010780049072a01c1003121400e00c1076201100d18504c42c136190380030305d402000003803004460500d107948070b03054803000782d00c4007042c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 543055611 1250 543054361 543054367
    0x1b030a08030a02091002013804050103142505240403030c0b13111e06160308070c050604030503071e08070f09230d0209100f0501091413021e 62
    0x594100245c1414581000c2c0c0004d10405480c5e50b50302c41c400d0b9941c0480101000c90220032244403461102e1305010b400041d100380700d10768480c2450030340b014405001200070302c510707008600c0b000106a02d081000b03030200e28069006282c0400c110711050122010701854203e0015440d10010034001000298400d4690041070302c0b6900f000c2100a00041c900d02695254480b40e1000901e44c0c0d0601c82c58a0301100c6020f01402d00c4038004001d0090700301269001307600005d50445459900d02149220340c46507890f8070895940d21000c4036151101c40e0010483d521400114000078000c80c091540119146441e001c010241d0002d1744510709200d01e008046048c040074085c40c5070380104c023a8107844042c10704202032441c10740b200119464050070655050b20140c01c84407641d07550000c5022098004000840300e0074030000101403845240308940d809404100001029406600c0358401c80c6c04204e0341d01074040c4030700c0511888009040da100305455003001602c0ca0b4401c500c11200b0074021250496031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 543056861 1250 543055611 543055627
    0x19090e092a131a0301021204140c15090f0901060f020601090b0307050d050a0b0c030a060603110307110c101d1206012d15030b040b01021b030a08030a02 67
    0x1c101e400c040e5000490200915650380a8840107980c550004089070009845081d030108180c0110003d281c0941c1075000160340158a4888400a40900c0c081d0f084821400072450300d0b55910281c1c211511f4100110490458030003000e40060709032424040c0c42004070074010300004000c4a801d070400c1010641201400026640c10041d0a0141050400402101a0356000a03544114a01c0b819216000c0307030420000700a421301105141c5c81e0301402d01078680c100584900f185800407504500c801c1e26120300041c03082d11030700440000d00d0808010038556200c150007149c00c2800c41c107110340d045c45500110703c1546c0707410344041c0d103074003440e6229400340124500d491407003003409030f51502c00c145c400d400030104000450107038111101086a202c0d807020b501800d030140498811070440a00003034900041100c100b51490307484000968080190032500c0301040b0403100200c5a0900503445100da0301014040548000c40c0c108c0000c044405a03502130751060100d52040360203003105130f00822044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 543058111 1250 543056861 543056893
    0x1140f0a0f020d0546061809020907211d0a03050408070e0f070e0a1212091e05011b050a11030d020a030806060a0c1a060109150519090e09 61
    0x4044001a20b400702c4941c07485d0340f0001e0645011000820104030302200c01e0340010020b41c49030004190800300509040c0030806d0701340090040340b400382d02540b1f07000002104540706c0d03022861112802948160450018080b0364020030603d040d01c0350a994101284498030010020040800d01c00d0b917400741c2e554146034007141005e9045c0c0c062060601d400c014051a5818600f08079402100c520b05010b04880d12000980c000415074400c1c00b4071a03450400005000d15003210341d0b1482401d84035500101da4503040414141d0100305814210120340109100310341c4a40c0110b01c0f10b00e1407031140d00b2084001d03200c5900b001100745d81101d802c002918241418101400403001d4003c50340050081e0141a88021341300f600000d00b0315224110005038031070514054510880d190781c0054000c070200507988039014100744159805402700d4000800024602010074507071078048981e83e01d2604090a002d0407070580c44082d4400310030300c81d02103000710340400b104806510440d0303200020801c0d19065a840 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 543059361 1250 543058111 543058141
    0xa0509060d0f20070206030a1806090302150c0901080c0405040f0608070b07021309020d080304060c0e0f010c11040b030f1b0901030c060f022503031101140f0a0f020d05 74
    0x146a03110180b000c10f180d00f144080680e8485a0141c80c45503a80d41c0350a0984010124241c031840000d10b0407070000184283c1da4001381d007880c469005c841e1031010468400c03c01d2882100d420030305d900d003000346440300c0d481100310315084110407562606140e1101c0000c3c0580704e5905490085a030385440810070104104200c80c0180042628207261200301d13000300d14102948501042d48035280c1501004548414408018254103c00fa00f912802c00b40707001005015044203100004030755114041907440d118242c00c0c0c0b0302c2030585410070b040900e641c4905c0380c20310385202140d01590350200300d6060744081c4901c03800b803242c40c000f4003e182c1c0540d00368600c076190342410a010b8210031005000240301c4485100641300d40b401c101030000c0603940300324a0080b040510804004040c10080c200c421040707813000650384240c60354507002d1910303d04c4a08840321480040c80507a80c26000c9440340560441c02900302c420b120001c5032808000240e5800e0b6423046905102c201c1d075900820034403090b20001c2c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 543060611 1250 543059361 543059381
    0x50a08010c021504081b030c0a0f0308070801150f050d020408010c0f080103050703140a151b0c080301060c03120507021506120d0806030106120c08300a0509060d0f 72
    0x41c52143d41869142c814240c0209550402540b0700c0d0742c11a4096402002a90304080a85003220a1403825160940066010303a40480100d91407001095440c0d005220060680f1545035504000c541022412500c80c0d11903800c03071080c0441049200ca0044107070004002912403500007085104410030010110b01801802c44100800c01300117100003100441c1c22822685c20605011451350414241e80c01e2070310400000b0501590040398807050b5025410003c0380c10344001c0c0d5031020480740b00f01a5030550040ca0300400000041005120700c0c1d0090700e4120860303001345070200394070320803050b11000c856043d070f43c4801692003c003888000c0007184000301e900000503205407520300c00e5003011650382c0180101c00d6082c040c11100090290324254083c800800ea1948019050704a5090000e41c00f070b564010a40a4019880c81c200e08503074040c0301c00b20b0211259031641141d521000089000e811a0340043c003040f00030080308841d9503481c0d001d04603d10034130000040c0107201300310643c11200701c650 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 543061861 1250 543060611 543060643
    0xc0507091d0a1502181f02060a020a09050411040b03090601080d0c0b06010e040b03030d090b0f010503070b0a020106030803091e07150815040c0815092806050a08010c02 74
    0x14040000d00c1d81d50000c10044020f18096121890402030443c0b108402074415048070740d80d103140700c00442c011014540c4039241d03002c1c1c495540701c2c80740c48010ba101d0740030710002245d00c0a0003000503081a6100101c80602c18903e035041c281c8540720101d0541c0140c504100d81e91120005000c04c000c2441600301c44002424040c01601d5035586014035500024003280c1802815610b005180c0c8942e0044681c90342d00500792940c1e4201c0549100041422080a580e08061640041e600c8081095660305a541c01802403020600d00003510700035500c40c1d0f20840455480315000030008491038055070045540c04007034200d400c60040c01041801e00e8407014003455010031010880301e100c409007841480083c0c500320b483c980e13038140045404040e80c010640c1003841c20042c0580d40c2d600c042c0c16805000c10020741c0c42c0c6c1e0310100080011040d0700303490448450a842d981d00300581a4600b0741c840c0c0384038103000422040c0c0ea075400a9011002e544c8100100d0751500318024480e581880882a41c0700440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 543063111 1250 543061861 543061873
    0x3020f13321312020708033006091918110f01020105240102010e0a0501090b10030201020601060e1c0b1e10030807080f0409150e04050c100c0507091d 66
    0x1020740d101e01100c0400036240359901c0c00d01401c3c9a1080c400c030b00241010400301c80c3d90740500000225200c3c01e802d10208c4440507000081c9080d1a2020118000c1400030841c1030710744c0341d0740c95001780002a0081814041d966200142c1c0d0940d034806140a044d004604030030082154806003c0b50300f000c101503078110f900d00010040c61614580c1004030440041240d04201c00704800186e004100c0148100000c0c812500035000300901500071600c3e1500c501154100f0b9111100141c5080c8014003009000d40c1000c801070101d84e202d40181c40b02c40f41c00804048151105030001d40ba500e40c050700559a40c0248400c1004a02100081c040c00f9424660068002d14011209100c00190360200520f0300c100020000b0500910342e0a440d2119034580c0c14a644d165168801801880c404102002c00d840d03400001038420450b40e007651040d50040050051114110208030114100003822028018400800c4010450801468002d010500f50000b0029051101410b0707001115078021600d90090b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 543064361 1250 543063111 543063121
    0x6090a090f231003110d0606090f0605030a0b010b0a090b07050607030e0703020f1201110f04090f060e070c08130e1009060f03140304090e0c0405100b0403020f1332 72
    0x900c01c43c1007180c1c0c10105014044200c580043e00001042c0c40117050344c0d092100220b500c000580c0230070280c000140c02084090b03660350a00da102d900c101d0000d48210a25001040120b00d08001010030106520301003070f403251505100c0400da0040740040e00d01d54090010050295018400c0c0e205c40310201004010151541d80081c0d1303d541040710050040701121001044c040c003d41117040d000304103800140e02c8075106004c8a1450b0000d1054040c0181402ca00c10b440400c2445410181c0340c0781503280b2803da950001c00d8404402040041303901020810421403045485c0e10240c01400c8101c4950b0620b041c0b40100c0703c0c84882ca50001000ca0380760600070422111019148003c9070f42c852160648401090003450440c000c940c4404515410724040000030a07002c50303040d46c212403c4600b0001ca4607400c1d000c0000c440d9070b0281c1c1c045220f04104c18030140c944402e243d50b81e0000140100b140081c0e0706a06000c0d81d0795071504200c0c2008544000007074400134135400945050b2254500e09034504 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 543065611 1250 543064361 543064381
    0x1104020f0d23090a03021c050409180b0a0209041a01021c11010911120c0310020702061306050309070b030403050a0528050c0706180506090a090f23 65
    0x24440020721070582e148244842075129020812014a00307102d204a0b41c0342c81400c280c2c607114801021001070103403042014504200040702d9495203459130320a41003500341100100245130040000d205441700740071040014101c0707401944502c81d06580545c5400c500000c0c0002c0e2003008600280e0460b034420310704030f2039a0001c1d410a807000a000e0400010020240548414040d41c40c2100d682d42810800700600c00d041d030100901d144151020f0a4600e1689045500c0d21140c100e01307a496080000c558001c0c101c0354020304403190005100038900407001078109881c640c15805807007c500007000308040c0c204144100030081069958a030b195140c07664008065109010305032052050103e41450446104404c081a1180e0100c5002402c50118805411a000700c214440079108900b0042a0030303100c1c0c900b010200301005000c5601c2030a00003000702c15004114159001340200e440090038001601031910340385052a00000e011010440c0302030008801492002c01483ca035080c05100d01d5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 543066861 1250 543065611 543065617
    0x1614010e030403150b01050f0309011a100903030807020f030309070603060b030c1204080c0123011403070506030c2b1103070e0405061c03030209090906060a091509060603091104020f 80
    0x9102800017516003281001079445025420107540201004000c001c0f030520151303c10940c003107080c194410b4140c8250104502591558510b5000401e25142040064080e420130754104405005a03103041c00300760207803480c640085404000750380c0306030802c020058140c4201c0002c1c01c00c1040390343c40e40c03506090003881341c4110000f04c80700300e0028000a003846000c400742c6181901440003445281c2048992040c41c42c031003407840f252010101d00006a2641d861103c0c580c1c40c00c041c000c0c000d1a46008104400383e00001d00190040d88100310043c0b100c1c50085150094001c020070406040302c61111007000c4940004506001e04000c2041c00340040d00603050504c01c41d001c590210385c0e9034601e400310f0030ba40007040d2220884502d6441090070141c043e0090f001480007500da098540d55054000340d0364140941b0001e030802c1400c10188094050307500040c2c00804620b8201e001243d485025030104d0302d0035401031001998601240041002075108500600005c40d02941444445003001801c0d02c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 543068111 1250 543066861 543066893
    0x5012405120703050d08040c030c090b040b041e15050301060f080114012412061206050604090b061003060515070b091204050103240807030b07050313060903051614010e030403 77
    0x6d43c10009020040c1d0809124040c503030021000801d01c0d45c130240f1201070140d0141a6110f9828400d540d40c850403e48103800f10100c0d2072101c0a12001102c014200409482000c0407207105080e43c00701d00da440c00d00460008110030400c1e403018525050310b0608540368000c1c5150074204540041062444032911000d050000c0519640201003030b0314165180050300c441d2443c510f081c040c0c002a242c900b600360135582030150f18140866990b80003040700300e03605070350300800400540000c206142001400c0d100d444266081c0001c103152900c0c002101d1000d104503141345002c00140400410180003c00d03500035800400814000650344400c078894026805154100340c0e86046c0803001c00303e20b9500903540e19021020015090b01c800d60301c0d455810500052702d480840c40b000c00c1e1041e22a4046921406200740700e9507c0410784e6030351101901d00c0503400d800f005824044d01c0032910f0b050000d25415031158072142e6000320340188860a60b10010a48941c41c4c00600c020004140e24502d0110b4074 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 543069361 1250 543068111 543068117
    0x120607081b190306050112050c03010b031306060e06011e02102d09031e140306060403050f010501080f150a0f02070f05280510050405012405120703050d 67
    0x241d4000e4140c8402070065100106441d0301c0c1079807200c0415055441001601d00030390720781e40320541203101102528010382d54041c40160400c01049a904d2500c0a1504444d40391107030558142d464480f14151110b80d01700c0c620240c00c0710b051001568000b03403030ba0070070a5100c810740300300540c0013000381d180c1c1400d03840302c4000c3c1d032503540f08244002116041d244002802401701c414a0400e8224030003841100002c07408a602d80c1c6503d0040109032040c0c20f40021030b0f0703881918007251254440b600ea000070301144e07045581440003000003101486880241c480312400028950b00d00a092807600e082039051507016003201541000c02020145a02d80c8142001c2d0003140180c0c080c103000000340f01d40d80e800b420414502e440710041100104003206441c060a81c41020b004901061480d429400c0f00002e106a10450383e2000d044000d0f001194418082c2000061b041d900c01c820324070b182c00306100c01407105088203040c8038a00d01721480c10010113420f00200328060139545c405a079014110921818 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 543070611 1250 543069361 543069391
    0x20a060f061203050c010f050910020c032b050a0b011b020a030218090d0302090a21020901090f1139010f05150d0302060106050f12070203070212060708 67
    0x106441604001c00400d48105000140861810014400d030050341015040d54200508807402c0346181c00303102d0140d9800f1014000a4940300e1000d0005c1d4004d040e100b5480c0824004196401106601405c0c18001210840c0084406150035070448000410186141c2d00d002c40280c101d076444400490701c541d040801403000845400020b04188150748000e50014400fa0b000b8204040411141d0080624100f240c0c009510b00714207a050b030084100c0b4503080020082c00304205159821080d011140b4840344032142c45032600401c80f0044242c001c85807150b115111003160501620640450620203030080341044c00852101030810310a8149181407080750000b0100703200c244500401103407401d4000c008501d50044820041d19003200c4441300b0a00d500c3e0420340f181451001c4003d041d52650251070983e0a04d40260380a8010302e01400410708140441d40d41400100e480031300802d12a0015500c4859910401101c0811b081c812180c907004881031042d040d030000036070358000d006040c3c20341c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 543071861 1250 543070611 543070631
    0x115080f010909020d060c02030919080604120e090a020a0e0103050c090d0317091605010c030f050313050f0703021908031606091b061404030c0b0703030e030c2b020a06 74
    0x84617101040003411035442c1c1201e190003d0b4000000300115070060b2991110304940041c5002810546c1c07180e42499040b1100182c00180749018180041d0ba890034941c442541280105d01c0302e1008407a0b821035141e000031140c004a8001004090250302440c0903c99071a0111212003180203d610160242d01d0340c2054208143c0079080146400112256454403483c00d480344a40d9150324550601d2104150080130035254464601000c0c180e80540301c283d0302c480e1440e41194258001441201000035440d920710000b4818490380c220344250000a002203030550040120004026040900b46080710408000c0c4d05408401e48072588485040003031260200d041c2900905085c00000300142c0c07208400001c1940f9080c0c41005580c0c0715581d510580c0070302c880c6078126101d1800041d2400a1608080058080741002454031520a01d0b0100345855668180c40c0385070803548000620f5040400003220031010b000c40c500e00c3d51100e02030301c008441005800b03921007c010b0130141c0410f442d01d80d521 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 543073111 1250 543071861 543071869
    0x1030b10180c030e060f0105041107020f01111e011a0121020724020c1b0f1203160305040608100b040303121b020706080a05090c0d0c030c0b030115080f01090902 71
    0x780b00441c0e40d00c2917840310703c0c104048040c100c100b40655841280340509407011045000140c03212603901802856121500500665500c080c03028090380d0380c803070110841e0091140c80038400260012100200d8030a03404d00ea0118910080c020170b50400c8000400785026504c2d800210700c0c0201140c20060380c80c06030f8248402000d0140610448034900c046a96010410301c0c2d00420000c05c020090b590011442c943c54417040c40040465940711700d00c004e070315800307280c0256450541c0098400302c92a140b070074010360b600404c001070150045000410f04106141d048144554089101303004204201d04182381000d0501460102800300140c2c0707081c414043c2c0c0b0380e40c054400c5416450127054441c4810341d000359140b0890140c0d10026903a00c0c040f8041085601480340110041005040c01c820848240310360142e40348415201440c182c100040450021902c1202810f490b0380309a40d41c0d0304000140b01d00382c0c40300e0012800c0090a070304018074415414006130645410101c0801c030400b40340009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 543074361 1250 543073111 543073121
    0xb130c051c021201170d02010b06030a0c03060510030606111504060e16030c0501020c0118060309020105120f0f1806010b09030708060a020d050609090307110a1d01030b10180c03 78
    0xf100f81c1c815401d001051400b04d00104820801100d01200c180031940c1c6812030076207a00781071090b0408410700c0410001c0680f03401464403a00c840c900014169600c2c00090142a90300b4218030110759500f009010702a03000460325880310800c001060200062aa0052066001130010b84400d5a582008004c1001441298000c012084541d4039040d100e003070210840391184203860240c491280601000d500416036a1484d0021014185580345402004d501800121318220b0404c0001c1200035a0742815041490250640030203001c01440e040100000248005d002151856080c41088041c4d01c00000c9007415a80c403c02040e488481c4d140109142c480707a90014200350051508108481c1925405000004403955040c8010b803030ba0001d1151110082e144014550800c212440104a18202c400d651020181881c071480307543d807450120401840c403d2001c10701147c00100148054400c07000d4201e500e06510f0384a00f854903402d0056044100d03219a10035455910b0168610300940c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 543075611 1250 543074361 543074377
    0x3060a030b0403090e01062a0816080309100504020d110109080d0e090601030c320f0705010b011d01141306021e0c010e010503040501110c010b130c051c02 68
    0x80103070310381428940603100030130502840300d0384640100000342e280d11820641ca01c62656481d0300b00300545601440741806090581075901060030001d0440072800704201d1010315000303209054032420300094841c240103411044a1585042c401400f016035600e01001c07041350740c80041c0a03150440d41c00107a4290b80f21340d00400c0140103541200a0350754100d00140b06107002126035482550301c10740190300715114041c0e20000900c2d0318418031405407098078035600300424980c4032158415101d041c00da165200340702502c0010030103e101c400304042409950f181a800342440010200404a213002d1084848541e60402c12910500095401020220b440210200505103200d51302c1d0000a560307100e030402c21640c0542258407050464901003440c03030310020146d45101c81190200c00444403500003400a079119560351861808200804c40201282c0c0043c40000c50712107072401c2040003001c40801604529811300404001c0c4a900408507400f9511890701006d0781c440304640702c1c0080c024104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 543076861 1250 543075611 543075623
    0x90f11070f0512040605181f110c030a2d0203011a0f040605101b05010c030905390f040c0e011107030c060503090a0b040c030c270f0f051302100c080f03060a03 70
    0x1071152202940004001004003030034084510213445001030603a2056a10005403000c1c2d011401e00c125a1484010f28107005110640c42c581e400dc50b40010307084a8000c100000c10a9a05492840e141440341c01440c54480c1101c0401c0010300c0e00011034810700200039107000300b041c0d612100e00d00d842d59680c504880b40d0420000c01942480c590060010700c4c102000303030346a1141c5000d070000c12441d0f07940400d26851901a2107019001c6003c2e21251040d5213072202c0c0e010454490611003903d65106510a909060740c0324180a42c400e030000d00b08600240c0c914a1b0f03a00402414804202c510a9450840c3e401e03240066690b5150b908640c10056909030080c8000d20030010f03c0709005099541e0010b8a00a50050b0300c40e0781d0305e048124440078078455440c109618084d450511004940c0180c54040d80c1c500c020031403001c2c000001c81224403c0f00d204903103c140c01104c2c0b007036040062144092964605286580b510179848001840c010ba00d58412080f10006c0046d010b6202e00300e4a000541d8441 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 543078111 1250 543076861 543076909
    0x1302060c070b0c0c1f0f0c0c3507060c0f0c030b10030506130230160f0b1c0b0f13091416090f11070f051204060518 51
    0x801e01130380303500c4103600c1244a015800c444401107401031208010503081070b11441000001c000d01075032034060f040c900781d0314404580300004041c2a80b504230038010f42d588904d54040d8694074644550703010100c3c09030000d5404480148402d540000305000101e42100f03424150908926142e05007020a40009142140450610400851410030b480c281c1e40309000303892940d40c62030102c051a0b0b9500c4806035014129412312581c248400103140002d090b41e040303120107561b04c218800d1421442340349440740807142e11010042d409121135803d000d4464128950301c0c00ac00c1c0c44060041c0e003000c690b24542d00341d41d04004402540c940d80142c0800102402d02044655840101d000500b2001720030783e46046d80b00c5240485040c0443d402c01908100b441403c0b001d41440082002061445611040a655080d02410302030b0540e020b841c0080c418540e1038454511450064100f0030390f058040811a0180000d000e400d030000700b030350f072613a40c160f2000300342c0300901001411503c4500350490100441d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 543079361 1250 543078111 543078127
    0x20703020a0b0109050415020307030b06161b03080a1101020c06010303031d06010e0c07050a021c05070b0c0613030314070504050a0b040b0a030203040c0b0f040303030509061302060c070b 82
    0x82070100da4103000d25a08a4981c0c0c0c4d80c0504010b4800c101c0d17001b0264104c0c0d103005c6070001c8031680030719080005443d0000d0340c4450000443e1160f4480c204a9404a02a44603901040301d20b0301d0191500390030280103030300d45103550390f0151517006181885c1d05000c18070380d41403202c0400754142c1c0d964281c4802125010350350b030709000d00101002d441c0308881c401e808500d00206500098447d0403100d558540020599a403401c03500680c101d03050481d01c5000b10515113001d40d441d030b036600301d80b0381000c1202031001030945420791501c07910b6032001c4840700040c01400d04034040030800b0f90b8007108c03e8841e85041600e80c501280141980c07148525010f8121080c030030960b40c00b07000713042501c40c1a2000040030382c5035203103011b01e030055104642e9412010028442c100784650091034020380700d040031a08860f22502298072541108075800110000031904001f4590f26000d07940d0003562040240c003842c200300004044003201d0b424003074002c05c0c0008a40c0b840e000100480300c003c201c40712443d501c480c14 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 543080611 1250 543079361 543079363
    0x50f03010b13080313050f04060506040b19111c2007091a09011809050d0201021201090e0a060504032708060a060b1b0a020907080f070f0f050c07030602070302 70
    0x312141c040c000c00802d008514540004100c40010042408941c40c2e0b918050402800b25446606180c01a40341e100000da1510b03040302400103004984002038550300c101078010605030001c4880c0c0e00300003004812100b40303000490301c00d4a1409d9100d260146900804054030398200581c810b8803035a0405094401240c1c0200d109010f8901c040b400b8000c041508204d0581c900707010050302c1c1e01900400041003100c20b11400d100a2842c1ca41b4040323071020383d9880e82400c02240e003503480c002d070f500000d02071000e0709a1114180076140500082000d00840548142e0b10264201c00920b0307142d68901040c00c0c03501410078580e81020b010041000703541042040314000c5d4140c490100d1621481003c129107103d20300070344095460b281040c5051000b0350390780800e01141c83c41504803d002d581024000f684845200d2445001680c4444440c1e061450f42c800540200411800030440900050443c09502c004146000f084030302e059a21624044126414510349900c010304c0288002000c40070960 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 543081861 1250 543080611 543080617
    0xb010611120a08250f0804020d050304080303071803080306100e151309022d160c081605090610030e0a0614180316231c020c0a0608040201050f03010b 66
    0x78103118420942d0310b00300c0052046002600380b04011850400740d001226100d110147e5016000503c15031042c0400c1d100d443c2140d10540144006800005c10024416040cc08144000290345003c9080614644861a0b5070001821282c8140000c100f07112402c3c2c41448000c005820090070300100203100d0840c000640d0010b100910610000e0344c00007403005243c4207441d0318130446040c1c0810b11600b144a86500c075441443c0700b9401c5402d0041e590582d8004000d0080c7c0d92084000f840700c04e003806038003480e1060102d02d40501d040c40c460180300c180c4800d0400c5401c0030041d42e8038407001c0e03401c040580240030791441408552046209580511906411060041da2401500012a10389110b91400d110b5001c2c0c000500f40e00400400c004d0b403a202000d070b1038050098041c1c00a03100380d16000d000c29030b2400702803441d030350120041e00394500c0c8008444e000101c0d180014024015202c010540921084c41108180440c04001070705590040d0201d98051950610b184e64a41e12000a02c246030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 543083111 1250 543081861 543081871
    0xa080601051201090b15060c1006170a0f11060c150618010b07230102030702070603051005010912030915050703030b010c0203060f07050c0f01051609030b010611120a08 74
    0x41c654000001c9031010310601840a400c01440121a940c00d07046c01c41307540c050131b000e54000c2400c000304010a101800b0704640007180c04c0c0089481440e00c5414210316100c0041910309800c80240d0710300095103d00940079480d80105506107151440d00002d040b4015092080c800380500598036681111840000780f04030070854100440c040150249032401800340541e05408400f00603135404241020301d0741a424020072007005401e40c24550203403e9030802d8600f0000b603070241c1000c4c84010f07054065554411184a005035440b89005c00080a85903544140c41c1169200042401414800e0b90f04401800d821020302c0c07151000b070440285a070740441c809500003440c04062000641c440c601c031000f40e070b40080040409481d441011142d040740a000034062000400c4107040d4600300b404481021810f40c0000129480c01244000c803001302c0000700410060540400d000281d40035800700e042d2251454035182d2111481c03007140c9890300c15000840c9240c1c0c08140c01d56800e034842d092034422 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 543084361 1250 543083111 543083119
    0x31306120e0303070203030103140109020406060c0b07080903091e060307080f071b1e02090702011d01051b030a0b040609020903010f050c0301120f0b0f01050312090d06020f090a08060105 82
    0x311a0100700c1c0e41c0c80740429900304c00160001c000400c0410204c500320b6214903141800000c010300c45600203001c460072940304e600420302949140c424003500442c51a4020a0760508652510b0b182041a03101d00c20501c0d610b100e507200d140300040000f006d803510030520601800243e07803800e080c40068071008044442242d0340001780c000030480c2d03209226010401d0034040074020b43e5400395654500e181d0610801520709804001e01d40d01594984070614003e00e425000000c2c80e440c0c8502d40c00840b00e42c91480c80c4140c0c100000d0242500001400404109011500c81d840351903036090070740a0070071000804e500034140a0041001d10301c40e80249040308040b070081144030264403a500a681045070302d1128602c0c1400104032060503841900b031b1444c4641e1515601e0b41203907030f80104040003500c04110a882c0f0100501450804200d10102310501400c0300d03091190850003c0c030b000201f040010000382d0081226100b40d40b001c0180c840f8204010f00744603440740c0350f000c2680d0b00e443c248a030500c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 543085611 1250 543084361 543084371
    0x504030503040806041502040e181c050307090905090a06150b030405030901031a2202070b18070605040b0406181809060c05041202060a02280b01090e1e03130612 71
    0x120340688211006ca500324a0f650711240c1c0e0703001030341e070759a4480c0300300ac119402a1100205803e40c0e5080c882c084e800c094072001d8072420300301c00040ca08100c03608420000352408003402594200056100d40581d40050041200c0c003000e084236040ca511a03002c4180b0360408414001000004000740010b00002ea9080001c0d00e6055410300b038412500000a80244105c9400d204041101e1949074008460711b401502d0031803a9519200040422240c407180308103801e202000e50b00c41440024014801d03441c0c554103180c02e240d8540301394840c80c42030405004969002100341040d036080d03103008003120412101009914a00800508038080382111030714074003142c41c11000d004400383c0d400d440c02c4129142c400e110039800d00401e680102864001d503c0340031482202900c407540e45e609034054030101c000c0c140100d440c02c01300c0403006030042a4040d04114580b662100000f600c0440c002c4020001c0700c03030381d450102c2c441c20752059001e10f950341c81803010701240a9400841c0b0815180064804200c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 543086861 1250 543085611 543085643
    0x3090a0e16090e06010c05070f0620010c02060a0203133018090f150f0810020f2205030f0d09120c050910090516030c0806150703050403050304080604 66
    0xd6880c20364001c030012600f003035001c201103501c140310508100e0b104500321060310781c40384d0080071205180e034890b5002852600d0020300300c800c4560b0038825006004020b10402e54118000703502d954008094000495001c40010014001545030784495504009412866980408031903142280102e244d5a041c0022580880003842a01ca000707400110050042e0003505004a0340042c00050468802e4652100283c00030607944045c0b080007030a002000c280300a151a04040c10004d100021940c8244184940380020251004031140c80c9004c0c42d94040c842800713044400c44644c160003640c0c142c42425254001c0c40c4000405130754070845600c81186a5649280f2030140405100008044203500d00c0300b0406424912641c1c0d4101414a0740604401d0b12005440300b1600200c880e100e440100301004180613030103105400505045140c44415032070944045070424041881c15800702c000015400c003810f00c80c2099130b024540c000241c81e99241e0740c0308500e60781d000a03030703080e16103001d0010301c40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 543088111 1250 543086861 543086867
    0xd020a0e03120301060c050f07090e07080c090a0f0915020406030e0f0a06050903160309060e0105071109060114040f14031b010807030f020a02060a052a0a0203090a0e16 74
    0x2403140b600c81c602d620f03503801d000c0101d07103507000c1890443d2207103c0c0e420071005006080c855a000351107600000240d04940312440c0c0d240c200d8030b500a200a130001140c001064982d60700c80741d403100c0c04080c00b0840d000c40406040061031000c8015182e69070304404014040e5180e0001c20848609a070240001569041d01c107131a2210070b03001c0d20066000f00c0d00c04c40014043c1c0c112a6200300c038042a01d0402d0141c14405ca0074840c5407008500182c0020401e01090790460240e640405081c40e000d4104101c0e55030b0890740202c01c00656214061807400a0b09a82c45040000c10151040a0980d107407503458140c00c05404d4a80595a03502034000180b203000c0c2000140e181e00100b10015070300e106c4810070015a4107410141480b002c0549032241103501c1d00150004040c200365550040480c0d10b0210985411900c0203089407103e14010340b0900c6403070421200110a141010020554881d8038104c02ea10314482d8840058000c0305482001076040d8181104038071800320403c110b5040b2001c1c020032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 543089361 1250 543088111 543088123
    0x1905031b040606030b180a2a120c02101e0e16060c03200307060e1c0e100e040209030115140405041208191a0103290d170d020a0e03 58
    0x3c640000c0d14050101401001c0c940080c0c00c11646c403000512014510b19000030380007000840180d83c4d00101c4030000c0785c0c1d40446100c155003049e210401c4610356088000b0b444001c414080340319252107084501c0543c0c038500440710714601046003004001408a08607848000f01e842840454844c1e200c00954207010b01c50b0040d850b80c2c195100607102490b60901412690800103800d403a110500c120000200c55114040c4840c11450003040c045c40080d4084031038400800103c0100805c1846440c0c0300e8889011601d8000440c0c10801525080394020800034043c2240c207a078158201001e10640f2203d1010038400d82c0c603024000c0c80650300e00f6080c00151041950000d02e103041d540301210865116410f915080141030790611750305080207a15800b41c404184004180d245109040f41030b568061281503444864586c0320301000c1c0b00c2e0f1065400c0d03416414000da000b450f0030102c02c1d0801c041d00c00c42d00561048004551746070443c10b01d0f000000d4000c2e480c0380c40410a411100d0780301345800112 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 543090611 1250 543089361 543089381
    0x60908010f0c1403040309090f0f05060a030305030114030a08040b0a09141e0402360301050906010b09010207090f06030204050f090a1205070506010b0c01060b03090601051905031b04060603 83
    0x1d1100305210020f0400000ea01c01001036040003800240400c41c8815401100d166004000001c1032100d41c0840d560121140a802144180e20204040000940000070b40c0d04503000f89128190031095803020078200a100707080107010a500280200306140410003802102c1187e40e2501c402c030740c031040c603212400d450640c0941d00505a58000c4108028100d04060320180540058200160780351040ca17a105520010301044015030f01b110441c2c2c0000c900c3c1c50111a04070700a125900740b040ba841c0e214007041c014000107039030005410100c3e900802030b510007005142400c101c941c2c102d4031140000d0905010803442581480045003000c0901240030340128142009131083c0b08940c0d440d050020428118101030081c240990380c0440c00a00903980203010540780c450355400c400200508490894100950714117090040c450a44c0c1b001404d581520400c1e540c4e0751860401c4003508214890b154429549072003070100c2d5007041340700000742c001d155000751000d10202d43c5821040d4140e440c01d600d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 543091861 1250 543090611 543090617
    0x10303081b07060207030c020621090c0607061104180c3902040f09030e122a060415020d17011401050d020904090f0506160c14070807060908010f0c 65
    0x2c925004205554002c0c40c0c094441e040140d01c0c051720f070b404107c01e50058002c031b40c5e220044680003d0f400c1e10010306c0343e500c01026030150140c404010f001890034028508040d104030740d201e24500003004088100c1d0b024102ca80d03501c0c2c2c80c5c0c61850f01070340060b04c80104500d0010700c2c48040d240740707140180c001c2c4030100d441d0344d08500d029015061007800380300c0424060348d001d502d407200410000014400c80d02c0c0c150090350340c00c103401e60180034450740450015640300a0b60014007803003500005180300c0d00010150b02200c54060000000091080c000d80c1c000e02ca00355140714250850a80000d403420315040c9586854104020080d500c501d03103a000d00c9491100400c0300c543d000d00d58030036030090404203200b5400600f001402070206040b110210002c0f034844c00c2086011061010401540d42c2c032002080c400310210b40d05407001840113a80200083c074609000700d2403101040c0500810018200071000c0721003142c5c0c2c81100400300c600d0b07031088420381e504e4500590f081803c0b0380101304890b01551 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 543093111 1250 543091861 543091867
    0x12031f030f030807021e0c03190b01051c050d0c1203140a090618030203040e09060c0f0c0a050109080a091406090d031e03020414040504030c02040e070b030f010303081b 74
    0x20b02c040e40c0c2208010900803c41c018815216151701c110328003d070f03107552400c00500d16000251705140c5003030703d41d10f1400040d0400c110300c01c0001d03900c0101c0e5419036405942d032030341c07030403141d80c20045141764200c0c0241140075010703540800d66800207044074414055107034440c620340c1e00d4400350300315101d1000220890100d600014505440303070300600089807003010f000507401c0b080294010000d04412080700141c0000408000390a41c4120f600c0e04460060003a0403030381403010100302684541c1017060282c00000c2124035100c6020312013800c140da085002800030541c5071503c49810743c48200727a140820358491020072113140400c0c01c032445903405406d031840c0115280c10442d415032181e03c210100a5001422040b060b40c00030580c041144948000d40c403103042c44003403880084070301d0f60b4034080c919100801c400b20f40c0c08020071440c140c06a40c0000c1e180c050001e009d0a00180c0e8100004048001003440580007064121504990107661801419100e00494640c002ca0034150549041c8040c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 543094361 1250 543093111 543093113
    0xb03040c0312020304080304080d11031309090206090d14010f142e060302090f04110d051009090b040507080a080301090e150420010f14070c0812031f030f 68
    0x768840008591050040345d00701a5900c00751850355100d508030042540003440024142908500074808110b2900d0103582804507021003400104528414000510344414007402076449030f500700c0381c5c480d0380508448a000d206041c81c204001050207810641d40c40c00f04188280b80346440703050603400c1c000f0140380681d00d807207030451126000c081d4502030300c600c0201100681140c180072500200a80e44000d0b84640d2100c0c00c00072580072008140d4011400d081b010111035140d041114070700c0c111031f00e00096075107803c10502c41d10701940e00703c8100c861911450a06109000c1c2e1920300c10344c819000c841c4c0700c0e41c585e4402522490240760080940d0b0040c0010b00210403150054001d4800c5d100403503a54600070000100d01c90410344d0181ca000f40c800d00701600d00c09881400342c003940c2081c00c0c024100072085000030001c0c0d004400300c014440e00880e2000c00c2140301e1380c0440090107803408a8a15103680c10204819074000c0c1c4180003056820f003421003a030208244404212032700003176003403820489 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 543095611 1250 543094361 543094373
    0xc050d0e0a0c051e040e1518070b040b030613090512180f01090e0a2c0d030b0102120906070503070308090d0e010c230604050709060609140d170309030304020103060b03040c03 77
    0x2020380f00b40000e02a0200c04082147c03060100340c8105001c5601d00042102c4050140c10a41c40380c02c41d840c0030b4000c010904c04400070804072604a03c0c00d58960b8070490407110010002e001081c030080c1a03010b2142d8480c40d0880d5a0003808030b00000c3c414101c040a6883c04000b4001c5460f4681404203a00120800031a020b4408090f84201903203800305035903498100c2210710030310046000191409880c001c4d45140010030580c8030241140c2410018481a1030010355107007080c2000d41040200000c0340300107511480d05441030207a00c8411a520b071500b91802402d1140215080c118511510054028880c460040c0013003890040e100c8140b000b11580701c0c4040700c0d248800061401d0710b05006100c0e10302d000c02900c1e11a5002e640074014150410000c90182d0340254071040030058103403000d01a1220320460706000c081e00301d0f50710800b20614600106010508078060000040101c2084140c60002c001544194400d980c200302e0503403501c1031103051b40000c1d140a05001c544060030f0001420f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 543096861 1250 543095611 543095621
    0xe07090e06070f09080703060f0e0c090c0307030e01060e07020c03030304030e0402160b071d01020705030705040f0b0d05031908040f02040e01270606080a150c050d0e0a0c051e04 78
    0x84a4980304e408251108441c61030440e01d50b0080301d0003556041d0010301d0701d01900c6149030102c090000b801c207042d84c1c24005844141d025252204403180000801c5001d80294003802d4a038140c44000c1c130680340c0e02c640721120003004464100140c010b05000d403c1518022003100d2041c1c2d030684071586404000c50a00000750002862241d1510900700ca070f802040300300d54003511445a40da80c00031b0403000d203608008102042e40002d810b65009403002c0c409903070081014000e42d00d00344c0e00010002842044074029180400502c0d4100d00c0b0802c2d10001c0c003202100800707180c007140740414070000031034604848400040718003410600c180030120b00149420740040b030381600d0a00000c2000214500f080003071982120b1080507541c021360040c0d0401449004400050815001801184c006604d58450004c072038090700e03404c01c1e581d1250307055a81c01242500d00d19441c19a00f007180f200b8080041303542c3e00e100c85064682c083e103c840080c9918000141000c1c004091301a40c44104001e410b01000d01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 543098111 1250 543096861 543096887
    0x6090f0c03040f020d111e0a060e040603020d0c06020106060504060926010c0504051302251a10080f122b0218090f040816030e0409060e07090e0607 65
    0x103101c0c0880003595039402c1780f4640a0080410801d8825902c04000e64250a0441c103801c4111080d0600c60b2a40d40a08240031a0402d081c020303000c001c0200080d000b08441d4100030361040380c1151010a0004480002040d00d103550000c00c0b895481d580150345602a5100d1200059280300040c0a105421002c0c220612544010501c1d000300d042c00c1039082d00e4000010100140010408000f189400c2c007502210700b050707140c00c6140130b601003040c20810711006091402010f40d10052020000b00100300c86030301d040c1400c5004241400b8410000c440c20511030f40c2004d00c2440a1045803a00100b890b46101404c13801e681d00c2c060f1540440d48102c0800c05070442142030f1015103070720350348a070b0000301506c0c810040c43c01c0d9407030b04c01c2c0100880914090040c0710000703030040411001400c1d0b0821600d0b011100599404108040d00d402c0310040f01c601c0e0f0450b00141403000003400c0090a401c00c00e04401301d0021748403050b0721000e02004840c0380c0f01d081c1101d41d00500105000314003d507d20184c1c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 543099361 1250 543098111 543098123
    0x1080f0f0c07020d14010f0b040e2116050109030f082a091203070303150f18110a030504060e2d010612080a122a020313030b04020906090f0c0304 64
    0x2040c116200c3c17042801044241c50b805944a00b000e4400d0340701882240c02c1340100312810040300c0c1403034283c65550712a85040c8428002141d110400310701074001a100000442d041038498400e4030701e4458080c2c4107041d001c401040c081c2c0c4406180901880200744100300c161205404c0c80d0842e01176074444100813114901e00401041907400030340350280800c091200704402580e030303013400b454004c1c11505d40884000500010301018009404211401e00c1215040b80c81040c06010710313090000181049031981007800c03400149a400c00c0d8061700000e00c12401030313008200d480140c03000103440c0c02030005490400c801290000d151035801c602c44035601e00c1030130000110140c9440c401c1c030f45544460020785844c1c00c080303001c0070050303800701141d4542046030f41c041c009481a040303420b510741d000102d20350a1548a031100d88083d40300300142c1e480090401c074944252a13480c00c01e891000020344081e80201200f0000503980d003400e0070090300504142500d05101d58a41ba005103940d0009401141c00d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 543100611 1250 543099361 543099379
    0x81506090409050703050717060c0d06260609010605180912070302031309061a07060b090a0c020f06060f1005090a0f050102010e2803050f03010b0901080f0f0c0702 72
    0x81c1c1c60700d20903004654807a600500c00a030940c203141d46407130a81c0c2d0003c409182c1c0d08000c00300100010468580015007210410780329010441e900010b0112500000d0b24079400c42e464004001101c494842400d00102c242e03605030711280342180c00c1e54058014103030407910003a03001403584203c3d880380b984209644280d8500304042c2c90000341a5004081c00c0d40164004206004000018040c800060005503001c01480d441d24000010004500261481464000c41e141046c40740303d401800d510720000b00011445e103800c8459200902c1d500450000521440301a039032010380005401e806500020001030070140c1000030052000d4000c00d0002c10810103104070b40305a00c0d41e111507000340006900b080300e031505101c002804c503104c218904041d54050b10300d00c0b028034071800da05110300400100880507203201c1d080c1550284503584600c010030070000b0000840c00b6482002c0e14056009a130759900c65110390041400014095401d00b101c08208000300340240168402000224405458080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 543101861 1250 543100611 543100627
    0x10f0e010e121c030b0a060e010c12170103030f0905030114011a040b07030201060302090903070308160c050f0f01140c030105011d0d05160b0a02030415020a05240115081506 76
    0x2280310b5030080140046512110781700181d1074540035443c09062507162401c803000200700000c2c09151070764009841c1e0040480d95840b024440c2000040200c030000b0080110b5940303107030003020030501000c100c2c0001c41c1d030f45001c80c5620303040c001c05070311507440045031445134200311140201980e4000030f04c1000380e040000258000c0d815028005481c000e8000095040c51401400070003c0d000f4403150700c0383c004020030300c0040e0f046a05243c1005081c41142c209509108089c4c030703800c2171004094860700c0780c3c0404045005000600407401084078000344558040d1080ea14150041600c100c0c2c591441070006001c1c5501c2900e040e0001801c042290100208402c00314190000a8a066415401451100744590800c005220040181458541c609013280000079201c0c02140100c1c203c8503298110b48824070f1007004042d5486803c1010303501c014440940c503100180c0803c0c0703c40c2400c0d140c1400081c48400c3d108150303c0c500e16070b4480c0202075481100320306200c2e40d080e580c240d2040061100b90 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 543103111 1250 543101861 543101893
    0xd091a09060f0a180f150801210c21050706020f0a0b0406020f070813050f060403031d060309030c011104060531080a0203010f05130b091c03020405010f0e010e12 71
    0x4c001020964541ca07200d40c244132407152006e051841d01d10030f01c52030340010010004807171002c407503d070204d80d82a0b014514500d84118400a03990241e104c401a0301000c044542c5200f0754992214450411100c849548510590303c43d500300000e08400e400000021021400100140f54400c0c03040c44010300c3e0995040c2d54640580010344150340100000c01c24030030000c203944114000d40000c03203005d4040800e5000184091085000c0101004007c540e480b05801142ea910081201d00074101600c0303280000e801d907070ba504051907005c1d540d0308150b0b03443c0a40390741e8022a4182c4a460f03948502d0220340b07803094040a00912060303884a441515100c2c1c2041401131080d01038060311000e03084c115803600415081d2000c3d1040d080c207092600f814800765000d072000d2034848030b0740540c00d040e6503038604c0340c40b074146031076a120800038001c185900750215604d64010800d441e03090f01c4082c0c008086080c00c0303c030b0181d102c0b1650702049001000106518001d9000d204005100e0122903040f20418025 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 543104361 1250 543103111 543103157
    0x815071107080d09080f070e0604090212250608060102060c0f09030f2d030301031e08040e060108180615060f0408011d1209011d030d091a09060f0a 65
    0x10f034000407203a140502259009004070407240d030840c0d0013001d441b0b040c25684e80c5090009080240b00c1c0741e8910b901021501c5865081c0c60102c01002a111501d0303401c086501c600440e02c9101403243d1400230081040ea0040c05041c0c0a00340680c01801a580ca00848070620380c000c0d5000d4222a03030038400c07001240d404000d00d400d010400c001030005405207512606604403564440e00080b00300400544540b280081682c5c1142d410403034444001c004074072820711209124401600f001c00c0000c2c081001c1020710000c0340108020390f00d80d0015030b94441c2c201d8580680c10012003081c2c01910225034000003021880150030700090615140014074141aa0258003a901502469440f1207076844203a9640a180f5900030295000c0c203e100c2e80060904030034412003c1c0c2a041c0b0980003004550003126071642084c1440117030441d44d100303c590748041e0024a1034485c00040341e60340c184125401074400c0139210380c424081c01290401c68000c104d080103400202c0e84604000a1a02d90032080c0650080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 543105611 1250 543104361 543104383
    0x90305030a0903060e0c012c1c030206070e100c02060c01020a02010b12120304030804030c240509030a0905060913052701020901090504090213050718081507110708 72
    0x40155442c61403410a0a0722040e40b201c1e031058211a40e030350741e41d9810060f4080c80400600d10400c812010b00c1d0200b403803c101d5401d85800c0001003131249c01d00c2c00c1000d2a03150340c0e170181c0c00329160340eaa107070004c4898224a90865400c100b41011400409000e20300502c2083d200804150070801109405422a00712024510040c2c1d10740c1100707021405d0803007036042003080400207440440c0013003a031850300e8880540010100041e55000405262281c841c00120350751259106207070036110030400004541e0002c801c044d1030318203004506207500001c1159400010b588421041618003400c21226400100c05103400103200038030800032207150b12850303100b40c0c60110500889809043c414204110150300075a5685c030400c4980d6030750f0b0f007045a8108807442101c1c003107038803e8284040f032500000c1c08004038080e0300f0007080c0101c06807c80e040380c410341081000a00070f6075aa9014564848091140042c07040740f030300105862520850f151801103204c0800c460025590f90407091a145640070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 543106861 1250 543105611 543105617
    0x4021612020a0c1202241303060203042a05011101230f10030b0f07031409030a120204050603060f120d051b0d0f0f020c28081f0903090305030a 63
    0x41c96604006058203944068201c4110344116109198041124103007081a502004403081b01880c40c584904000c803800c88410640d00070407681c0d68034060000c1c2d0420f640865610010320714040c01e10301002051001c580310362044035180362404005441c5019080c0382c0d09442e5484204030484c0285150400c1c84489284e021050b0601e400740e40c02d0b2030342d00c000d44180c0201c40c05200070004503960603401e54000140e030307503074031015154800c0c1036000b00901007000e254014810308000018501001424000b2155190b500c4100d411f26421012403045004142e1301800520101e001400c140340d40b0720314658040d25105128201c0303081c080c500840c0d41012800280000f41c01e0040c049007c0074080280401001414a0902e440c009040076186403840c0c410494a030700100d00e075500c2080645154900504102840600c98050031840300c0703250300341d424104d00d030480002c6c5070400080e6440d1000c1c0806a2900c41518012980050030701e85030240d0420002c01d00101c08244180010710855607180c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 543108111 1250 543106861 543106873
    0x60d050108210c0303060907050c2e090203210909010b1908040302190c1d270a0f17030106031505030705030a0206030a0f02070f1b0b090402161202 65
    0xa07400c07020b1420b22502e050318040040c0000600d1050000a50750000740071500f01c0300a5981c41d10484182c007860010000d50310810b80020301c2d40c000e4000766482c1890000e440c8240c113003108810001e0701c40000d40250998400765005141e0382080100c4c80380c1c21100000240380c0310320000021103640080e0072220b02075000050009500d0584010310708035010a08011140c1c0c03070f040e14003030b44801850301115540c040e00c04140c0304210b079085680d0007815502c3e0001e20300341110301c2ca880c4191021204802402091441464211000c3c2818129090108000c2042c03c0055596045c0030060750302c121808031460035a840110504005907000c1c041654002540b07540c1041164600c0c00c050b070101d07000c1c0e0040c41e0f0a1100d620003080c0640001d405135035850760f0b0b8480c404528010546c030910022100d202281e0340003004032100c0000a05401002c10302403d0702d0b181091000303030005114403564a00e0400400303540303081c04d03005000e20704030860700300b804400c290710785580c1c140c1c0710101c0b0300041c1c10030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 543109361 1250 543108111 543108133
    0x51c020415090e1302060d0209151803070f0f0510090b040905061914040207050313140108011509031e060603061b0203040b030402040b0a1701021c0c0906030b060d050108 75
    0x1001003141d1160300f81450300c132004810b4010a000d44949840515419000241d031004c40d110020760090058641580030f6035103002e00b19007503503005072120f018031a0003140d0380040d408075803407440f2083e90303e50766034038910b645014204401003000781915024480743e04000510306e162280a00004e040988020a242c5013980800401e1901d42110a0012400006c1400750201101804001c20002d540050391171195042c9a8a14052501c501d40b2642c040076000c198001c018095031304032002a215415070b070744c03141142024000180312640004c2c00380d507000c10108849500c1c0001c0881607441460401500382c96000554200d0381080d1800c60b128154813151107280308a0045010840c4007440c11310781040704080c1c8511004c1c3c00070380700e6a2110944062940c502c1030741002003000101c40f030b840c01003881c0514080e4012090394425603c03800340005840280f1b0040c526514402d83d14000d00c103080c414103800820352400d219802400030702803008140e00b83d00c0707000e02030003900009004003800 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 543110611 1250 543109361 543109379
    0xd02030616091e06260105060a09090509070302180403020c0d151b090504060303020604020f031f0509160602250503190203060601030902150304050c040c0e0a0503070501051c02041509 81
    0x94170b1031080002136804101d03000d004088140a05440c2d0451700e2651741e030b0b0348040840d2103841503002103511902c0c040620208500000319107045174802d441c80400c0c55008850114842c008440c094050703005100690300310701c1e00350740085040c1d10a009804001e40301d014040d084401e508040c4020140344614241c41c3c035005000240100f1003100c0070302c0101c0c11607030001e440300000f510080c0944000d0045c0c25442e80c051103001124100c3c2d40010041701140040f80700601410340d424559802006c0f92031180c1304804100409071100c54000385000241e03c41c01c10b015606001001c2c60844000300046110342d82405202070840d80e0148803114050640101070034424054061414075240c00d40c4c0100603140c024006003c1c8902541c11a100e58440c1085410a582070244070351141c0740850010306990402102c20941c1c60541d41200f0f4282c403001803580d2003920740107060129402384a102c2034107060256189041009030000350405648180e0300020030029034a802c045292004140131204c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 543111861 1250 543110611 543110627
    0x110406142115041a0f280f1409070528090302120105100315020403020603040f0501151a0a03110712080a02070807030c0203190b10050d02030616091e06 67
    0x18040f98104540356021400031144041040240e004080c59140411030303544d80f00d2800c1c820304640041451000c11001a0300320b44001c0e0007001241002d008001c50000c0085182480000001d45001072544403501d0079140c40d00031103414460450401120700b51360348086400104140c4540b40c1086103030551040000250f6100b8030701310140c0c50101044a07001001040b03c0c1100d4001b4812104001070103c08030181c407464002a40100b400428003040101c01c1074440c00e428000c4000b0841030388000c040d8103c1d0700c1d20f84183c01d102c10a4039408134203040128000e0141c00b8881c100056100d1540d400100140c06c00700f001d403000d4022000380781c06150005a00e80d03000540482c114035103090b9a9544c0c000b401038580c09420002003529180071510300b004000c3c21002d0314144904424018904083c02c02d00071282c0d180103181071040040c0c0e5003800c0c1e003c484c0301d0358000c025190359a540d07070842c0b00000c0c0542c108010044134100026a482009040c501e801585030002018142481e00140040c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 543113111 1250 543111861 543111901
    0x7051204090f02160f08070c410609040b09150f0108251b05010e07060504120b09010b06031503120f0a030c0201020c10060306060501031104061421 65
    0x40d00400490340740c20f41c008007001c00d13164040312a405d00c480604103d040740c0111207006020380070541d0049416001c0d4060038030260300900d00000181c0700b1000b000090188030001c00840780300750624000500d004409402015000340000502d281c0c280c0024201380419030f12541412140c002c140d0150511031007051f0440402e0900c00f009040944c0c94080b4405002241e250104c41103011400140c41807244100800b0f030313a00d564040c85101d0510300e000b021410303a0b95031a0700c2250400103102e8015400c1d181161284650b42c07030709440c07546603680b140a00824030b001e155a10080824079035981c0e0007940c05098016400d101000042046c0b52502c0c1e00715503281071044040c8105a003100103017080700d40111091401284000300c0002c00d9001e8000d4807810102ea01401929215083c510b40c801c0d0111b030302619041c8407140d0b40d0001901103601080e4a01d1030604100801d02106005800503113082d03071801003951404c0180c018004900c1d5032035010070012100c003024014001642400170b5018 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 543114361 1250 543113111 543113141
    0xd02120f010303090e060d06110a0207080c030c1c050106031505070e150702030f120d0501050a030c1a12010f0602061b161401020d0519110409020f0705120409 70
    0x41d411034401038030400140c81480490342d80d00d070008415448503681414000d82c0800b080c80441854000e6141c940c0140e20008010f12444070300080c80140007681c480300c420f0240c090110101404c0034403403001142c0400c1c00c840d2004a48040c001007003489610021400380e0185034070030045001760019954050182020070400c091039143c4c9644802c00782000800b55500749503500001d1000c2403d0450620300c0324424022007000400c1010060010080003102d00000c101170783c0c950707041045c24101400087c04c0c2100041c001d010b0064104960003610503026581c1e0708105200703c2e40184007000b60400c0300048005d030801c010558040095980011003491015214914000e0362015030040f4030420010600901d03802c030a102c8040b60340841642c41100955841c85103000c140d0240206680030380031428200084075110f0a41e100754030900e03c880240c64030781454940d280000e0b4000d84004040804108118000104104a0009505000c8030103d44903843c0c0309004040b644080800c43c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 543115611 1250 543114361 543114391
    0x80712050405011206060f03180209090c010f140405280906150203160b06040f0213060f020d020604060b040209040207061a0604141c02090f090706170f04170d0212 72
    0xa03801c0700c5800c01e02211f901e0700048051180314520f4981c00c1c2002c000e500400c2074018040c0c00b04020606404000003030302c445114051141c0219074101014460103900c05081c08140550315008689041280d1800410761b500740154150030b080c1c0440340d00c11030b00c0c0c584d115010041149402c00f1504000030900146080400c440c000c81007240d6a03900c02000128070900050003984d8552110325040c4070050110f4803961100301d4440c1604081c02054041046035045110300742c4001b400b103036600800d1f8044c0040e51507541da110b02810200c406503038050f070240465140360f100c0d44003822040340200384c0400c442070042072241440c1d007804071250003188104000d1001a0416484000c440408c0d40e10280100b2220608842071100c69030003035000e40140b0a00c0301c0a000300e40001e00a04a6a050765502c90f40d4510540d00e091001d030358600811800c80004030010b1840264641c003900541e505030001035015000241c0341d105501500b4900e074007113264041000380c0d01d05c66520074105620151 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 543116861 1250 543115611 543115619
    0x1d0709110414130e0a06020d0f2c0106031a16030b0a0e10121209090b0f0906011107060203041a0403050c0603070c0804060c06050a0b1c080712050405011206 69
    0x40070221407540a110900109a201010340d03000d080748113901e00565840280515000e4007a40c40b05076502410f600300306460800f800a44680d960074402940d6242c480101d070114498841c2c030100d0b900d107481d50307900700000c080383e214094400401c80c3c071540c08040c1c0c504001c0c0140385041c109960020035140c07040d0405252140b0180d64155020709400c0e440365581d07141d020b9501c1c02590042e001c1000b401400e101004040c521a0340214620384072802641c1d00c425841080310311085450341e200150f144041101d04100e18541c0c7c0040d410f1602c421200c00c94032007030b807911a040d0700581c0140e000040c100824251808911040203e04425034a051301e03546802d031fa2492524009485000300102260f46140200701210b803556014405035140c40c0e035a100500503840c40b080584441d81407000180b840c0d42d8902c00c0c2403103004000d10701c165001d110520304110140750788003110221010407240d80401c1c54041841600861035603400d80c1d5505002c001440302c81040c0c51051107a047c100c041c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 543118111 1250 543116861 543116879
    0xa0f050906180c04020a03291507140a0308070905031c05130f0305070e0c16150e010e0d0e0d080307030b2101061712041403011d07091104 61
    0x140e004950381c199400b00c100d41000660512100002d1154403910020b94840c4450309070b00b04190000d140e0385880c2045001d950300c69100c428800005501801e04011680740c08044400381c031030b55001d14851219507030300400c2686012740d1504203134042000c200c1086103017640003d007c000b51100343d001e0408d800100405548111101d04141d0500c0303004504840c03e400942600b00052511035110902c0aa490500300d44415a034010100e5107400c5000148807400ca8008890320f68580ca14004c81e141c0780c6440c2d003c1c104051b8401010704549074001e0900c01d801c24011304100fa0b1441000c0d1440340008840544213103040100a409030080d905c022012500d00310907a6030150381400e011039500c1c8050005130103641c0c5010444500807058100d031441c0241548100240c4e404203580d20a0905407800030341e6515042c080200c034003d003c000c18000b02000c0e441294946402a0002c6288140da0250181e16000c200414540c4e0f441003908101d01d5495008040c1824038000c0360501c1e042c2030a240c0303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 543119361 1250 543118111 543118123
    0x903120609070c052e05150f0609041e0b011103070f0c050604060203130501140706110409060303020607020c011d010c0201141b0705041b0c0507030503030403080a0f0509 75
    0x1441914101c000509040c010042d0b51034840d4840c00303490040700f40c2008514030b102c08400f400880964242e03170301c400744031134400c090094074020300a440301481c0c0b10800c040303540081d007580d4005030241b113a0328030340e141c42c010b00840d44c0c80e00c005c0b5500c440c6490741348000c489050035042d040003081e41c4403220034180841118001500b0010144041089044c21040340c48958002504203000050010300940e010002e00901540d851034402116a0707440110707400c444c840880241010200185000a481c55110405d074007200d0f4100c43c1055a0340c102d10045030301c9030b4002c3d00503800420811500c103074180090a00070400b404d20000c0c4004000c1d003140c048550301d07016418882403000260a5a0080c0c2c0183d459040750f088641e0760300b0810000000e4103010070684005480385a0300455940780c1402460040c0360030060300f5481801c1300c201140e80e111500310990740c1d40680040400071600a0000b94443d80c06510742400f50705001002d5404c1b00d01d001e11550700c6510f02010b22140b50030225032 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 543120611 1250 543119361 543119371
    0x18110304031e030e1b030c03070305060705090d02120a02030d0503091c020c0d05071a0c03030a02210c03040b13020a09020a05040905010e041406011809060b0d030e0405090312 77
    0x10b00103039030301c100c080e401002e0300c01c14466584600c1c0c1c205c02e50360b4084028865158030607010744600c8041ca1060690b20b0400b4080200280c00001c0003c4d42389210314050842c110004100c507507244410b802003640306000e00c03100c01094100e40342c55004c0d070a0402c00001102d2203407500038a10302c3d004d03850646404004040d444820811080455020300c20060902d1106008016454088482c90066a20a000c0c420a11481501c0501800303a280c0c0c0c0c01525408840100035518640c1e42d1203144000390b2254640965070b049041c0040032080410160510450190752055904c1c106424407240612005048030f06006411850200589900101c0c02c00c8900092015880f0380b035102e8191143d01440c0c000d11803492a00000240d011180701e51180240d0103981c10518044170905460f440760001d008005030180c250580d01941c0540da0310020019002c0c000004200791400c00044036071000a0307090700050b0540d107064900d850944241034201560340005d40c0740c080328007540340c156071300100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 543121861 1250 543120611 543120647
    0x5070c03020a0b060126070201060b070f12090b030108010b150a0c110103020d11031806102702160c08010b0102100203060a0f0b0d0b10080a0c030b03071811030403 72
    0x8106264080e004058003401c01c8900c004620180c0d60a06c2100c586c11240303c4010360074000001403040e0a80f080345c0c0559001040400350709a0303a101c403030583d541c613030307101c4e0402001000000e02c480110020b18080c06010002141d9050803204101100c0604842c0d80c00d40c2504200f800400c82d0800c045814160b84046107031000c82c01c890040c0e000380285c61101034528100322f40700e4002d100c2040110301c80c07800c41808424004400d5400c40d81c802088881e00000942000180224a8031500500503c0e507000b402072854419010f1a4080e600030300e10900341d0300e50000e0031000700481030480310081d2825034020408007242400003541d9007801e03808201b040d075001004c1952911103a080a024210205c440040995959000c20142c0c2c060000521304501d41240c800703461030301003105078850f45980d03290f400503160034408200501110201d1402d0680d81c03050384015450602034000145607000841045210110001040c0e407849004421048010401c000000e0781140d214004c043d000d074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 543123111 1250 543121861 543121883
    0x1406010f08061f020c1519050d02090310060e09120f1305030a0305040612020412020906031504080c12040509011401180308031e061e0103110408060a05070c03020a 72
    0x640820f90901c0c01800080590700d081e02030070001500025412808281a900f4030f84020440f802d01703e050040c2c00c044860564110045980144140080c3c54281c1c0b40420040ca05030182c40028030f0003049040d212115526458104100500900303400e6010b1400760180c07032400c03801c030b456010a2068038081d40000ca008101c450000d90090101c0740607003005001c43d620b620a07400d003d40139801501c607240c001041509450b004646034000e44e011981120002c4480403402d41c01c002d8a04002041c19130144950036003d0034020402d4030403405180100d012503513603094082218105031002503007600740c507000c0008110b80d031590301020703044030801080c000b06c00b52100e0040341d2440c03000c2c22002510002040101c14401c4440c000c42c00b56103206007100500c0190018602c100d00102e400641c0b1468240504506601c00c070000c40c0041014500010080d48800e450310442d08107030006a8250700c070204101410f4a248103050b0031034400c0c10004100032256400035521240000000c20f035a61030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 543124361 1250 543123111 543123121
    0xd17160b1503070501110717160b040305191106030709060806040e07030206130e0702010e070501030e1b0402091002150f04150c021207110a0f0617060a050907080a1406010f08 77
    0x10320070347c4003908280640c003071034030b030140c0c0802c1d41c0d100c01c1075560034091403141d4009000150b1004643c100c3e54002c01410050075442060022000201001e0f60306042001800ca0240d8400c4002c511880183d12440c0c1d0407420010001c05000c0001d0020b4051441c04903c183c0e000c00000c7c44900702ca80c11101300740c0c0c9105032009000816420f03440b00000c15040d03020301c103103e5019000008170b564418200c0350f41c03035a210b004406885421f0109180c0d07070080b01c2245d014100a02540406c244c001e04050b14055524001c00c0c40300500d007001d072006800415003103101c03032007c2011a4001d508104a0151424603440e0400c40d00c4090f010f5031581c4d65102f501c01110780c02031142c0e502c8011656800c80d203802a41c00e24034107902641c02098800c00c039401e0041009210340e0300d21829100c9643c8c4100c1c24164106540c1807c81d00501f441d40d00c4107141500291740d540e6128401e1082e03c155032200d40c1410a60b0000003a100e0040c101e241c010456410013055903407001c3c440c4042200303854846650b842d8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 543125611 1250 543124361 543124363
    0x308060a080a0f17040e0f0a1401050d020a0e1911280909061202041b1b020f06030a060f060c11040504060e0d1806050313020d17160b150307050111 65
    0x214000c10141d001260001b2205c410f0302540c1c1c450207204444030010f079900190b40080381c20303e0214003000c022400050080d8180002411000740c8082c00e40044030380c46807104460f010b411501c5000003038001c0c07101000c0040c24052441410300c201c2c0c1007800e0200241d440e64440800314103850f00200c0d038041c03124903180300704100e5009049000d01005001e4403501800c240ca51520416801a4100030180248500c07100310307810311826039500d0480e403804809020341d9030300e0300850680c1c5c400c08100001125a45a000550060f810180300081043c0f91207e80400c152840c1e0080c401c1c058541400f5010a8080ca21951049400c80340001e05a486103460801480303070200050084c07041c1d510081403540c10040f07070600b40d060901131000e1036580e41001c45262008541c1c03114007581d034078410001030074401e24001c20940f058408201d4440320101c184200c1c2c002c41107090014109080050a000e510b800254000329038018580c0f0208444000c03031741c1d80b60b0701e1140d5030400c0b05089070b109040350 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 543126861 1250 543125611 543125633
    0x120c190201090e07030c080f040b0105060c030f0c0106080c030d09090504150218090109090c0b0f0c0a03020a0303150302060711030309150c07050d02010c060507031b0c0308060a080a0f 81
    0xd0700e483c009401e0800082c002c000301344440705007010412180200d4628500004110b02c00d50f40001444210f070f0804c414070038150451333080050b0310700c4140411a001010b110240c24060400c80000a0003464100d0307061030b05840c3c600c928042d030400364100c40c5140d030050780b00e400d07160102008201d44e00ca502e030942055003101c41641090f1b10114420a007545e10640100c095001124030040a90303da040c41022144640c000130645440f80c2420841c0d6005240070309907a61040c05d2150500581c0309030103041080b200303821401a0004014102090f4041c4503904407040c00540d0302d0100340c207603030101300c0b0352192070702c00303404081c20310340814080d50108122803000801800300b4120205080c0008102d400019035416180240c00b40420b030750810a245c01001c64050b59540035201003a01e07020028480502000d0405454140e0f50f058007082a40350b604041d070590700c40c0d07950045810001c10324680130702114401d850102c410010702e072001403107040349a04240c0d40800100c2a16105440075 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 543128111 1250 543126861 543126869
    0x5070e040504050d0908010b0d1401091b03170310030f060608032208150c032208071b0b0f0a030b1305011d0408040e071107030605060102120c19020109 67
    0x1410700c81000100580400c80780c080d55400c1c2c80b1514410f032202c020900360b4240244131a00103a004d07103203001050884642d1400d61001d14000104081035880d161070040340d024100200b490500030802c1040210034a01030380ca0419442e00e419800e0000c10100c20b20014400030740b82c001c2e030201f000240001d9500400041280804890b56280c20001c110b108034814807600b103000300302880c002604d00001c40c00701c01d5540043c003480c0d01640c89807940e20040e007016140d6034802141e80c0000c039004024651683d082c1e40212103184d110304161405000c851003004000074206004241005010708a4042d5080344000b004051f889151540c001c4000348134902200d980710507888068004603046600540c10f840317002c90408088502c0981583e10210309031401803103031004010411442d9060030403190007071814609900c60500c048035071843c2019640095440c6941c50701070110544e010808104000645140d290804d0f040400054031424007107842410f41052501c0c0c8400c5a11480b41c02c4054 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 543129361 1250 543128111 543128119
    0x2060a11070f21082a0a06050a0c030c0e040c0212030a0e01060803340210200d120f0209060406021b010801140d0602160302150f0f0a05070e 62
    0x456031441242e4059006102d90b8641c0001d1440c040c5841500c084501c100030b4001e80381a140c00424078000c4880852040322036500034641d44085030001d024066207003600d00900000c14542808400f03803007140d040c00080c40c00e052600b01001c00d0f9507085101c15203401811200014502ca00200603401e0441c00f4001b01c6a10400004012007698258004006056108000c0084549840310147d5030f101e41c489001001100c21180c41002541c04100d20f111350120f0240c000ca40d026a000c00c800d003540d00180f1380480d242000310700310038200039030700364028401c400200310018100f400508540a44072140e6541c6071202d0a1150060301501141c4401501070051aa80e0343d942c6002515941c68030320300107081d514625801c03020341c07007220a181624000030041121000c00000c1040070b6111100c200c0b02c0c244c080c032030300781100c85c0d4554003480d0034002c0d0003409101c0da1a014980d0764000007460381c1d8502c240350082c00340403001011025401040090001520b403104134056410481f5010507a40c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 543130611 1250 543129361 543129373
    0x150e010929090a02251209080703060e12030a0203060f060a0e0f18040c03060e01020307090e040c0b1b060f0f040b1e0a0b01020616051e070204020a0201020703080a0608070302060a11 80
    0x8050b170a0408541900c1c05000001022641d0a10460f01d04071b5920412400b5400f030741c42800407c44541c04601d43d0849081121100504150480c1c0c041c0c104650440450b5404001c02000741044000c0c0d015507441250348034038000300c3c030901900980351410100c0c0100c90088204000341c50300c4038060781e031a40ca90040310091409180c03080105003a80001c0b1800c0d410000391410406050003036901465164232428002d60a044c0915034010b00144191010f0000200004480c004a0010051000e103801280c3c406180f900311a46007031400b5103e141101c080707100b003003000c07982c00c0d02c1150010b50054102c161601d4184018140c05200110410500a410140045802143e00c009400d050a0302500c00e5682c4560304080b420140350384500100318204840300704d0385182810000b0300d212140c0014202019600810f003280c00c0440c504016030b500060a400745a007080c1110b5010415501c02c0c0002400c0c0510141c0701c5000d4131000b40100e101146c42d400d80e9000b4103908620044000817600d03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 543131861 1250 543130611 543130657
    0x706061a0a17010b030c0d0b12031b070513021c15090e0a230109050a0501050103020a05090c070b13080310140111060f0a150e010929090a02 62
    0x82030744070300c003001c0100b1080c2000c2e86200241c5541541250004110681981c0e2207511840495210700030285e4100e40c0c483c1040440e64a0010714085131b4441c030000c58440040d14801215210181c120107000d070301c55801045550788031206551000160680586c0300e00042d202d03555801035512051403c18100380d11002c0c01030403880007100b00c9816a006001001001810584074180b208014050000b051aa02090f0642e120741010340480500006900086600c87c3c5080641e0f080007181c0716519403004100f0b40c90204055009802c0031a040d1502e800c0504d080080b612038120002c1400384d902c0001005040c81140c80344030941c02c4004966a0714110540358034007142c40c09a01c803654221200541076500c100181071030026036030003c100a448a041a218841008003240c240701d807110f5500f100424100315020081249030040e68055041c01891401d41c2c9110018914694198404401c16562008200b0059009403600d880e19200d48808a01920550b18103001c074202d4400ba031a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 543133111 1250 543131861 543131909
    0x105060904110d0b19051003051f090e07050f030d030c2010060902130504050402060403120503010e09120421050f03090909060103240905010c0309110108010e070302070606 76
    0x760490704c2226541000c80b002060209500703481d000302030300b0082603458105414001c0c0d20241d001070918200c0b040c3c0f01450881944035007210340206007560340b2407080040600082003000040c003c111000d000300d807440804296120301ca0318400c03041603101e4081c11000f034041c0308219000c1c00c105000c2810105039080242d60340310510991599140392a030300041c001130920989240003140c2d0a2800b09602d8030301080f02078000580141da00140c00c20001000400003901400343c00da050700d901e81c8941c07514441e148c40040003401d40c02030340c11080c010b0781004101d40840d400e450f0340505240c2d910010582542c120300203008001c049109040012071950000001b81c40802c00c121140074995a03040080d40c0c8444003880010a88120031000700042c0b0031a00e900c5c441901c0d24000010044640d0b200e0500307440c0031000c5100070075903070311a0006200b020300801714000030a0900380200d501d0180c00500000d0020162020550301013640307c200151504a4001030481d0704c0c0102074011707610800c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 543134361 1250 543133111 543133121
    0xe0c1c061e060f080c0301150207080d0c020102070e190c02031303050304151d220f1a10090603020c070302030a05030409060f030c05010302180d0308040210050c060105060904110d 79
    0x1408541500f4002da4568403901c289071080f1110014241564038203030700103107405041c121007030030760080c5100812504410001c058407100380d9583c8941d065964000a42030005541010f09040c030020201311603050b0740c0d14011180c1c20209000194403032030b440304a0450241054541220305012000820b21000001500980e00c0d0700445410003030300003c09584c04541d9145140c07007040c014800c1480c0d403030004c2100300712842c400039900408c02c1f1000c1b26000c032410102c16500751982c5050940c1c002c0a00014184031072004d503202455034100c3ca20286c1000c030f091041004158000500c01182032040c042e201c000c1da130203000c0f66240c02d26441c01623103a41240c040c4e40c2d150b6240a00c0000c2442a00e0500c0f0200d0790842c920250345410800110b019601012980350300810720880d000d0161514414021842c0c080d9480c45114289441000300b503802e050300480c2041b0085c00030615602011030b003581101c0d0101d4145270345120f00004240030340210480303541d100c5004030700c0c424080015084 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 543135611 1250 543134361 543134369
    0x11409100c05030d1505100e0d06090f0f0605060607031d24030f0714180a1503050f0601020c030c0f030a081204060e0307110f0a2304060e0c1c061e 65
    0x1721008098030742091150700321503910701c440000e0803031611140e607041100445c4907180c05460f0208100303000d502d4032400c0441d034000440d095080d1004040031f220452060540001c01103c004e40f500003d920004e19020000641202c414072130115400a43d444503032515405800d01c01100112805100550390ba410444840790341003d0b001c00200406d1003010341074408a07650b40000e0605110910807040c40c42801815604034000c6100030480c03440ca4941001010b120b0380d008540c3d423034940b01c1c000c2d002d100901041c2c10b56020103100d84881e500480c281604175420b582406091b42c0f01230010349044c0c0001c2e806000440b0014406141e1001c04002c50b119a010b00300500680007031000c00c9540b0321400c1805032003240c5440c40660b080ca86071a840440702001840c880c03500341c66114040d81c080102020345c21502c1d000f21010307118145401000f00400079003e010f401840c1228080005214000e1804242c03d0b40d290031060441c8281d106101a0002541165010311041214006e600f41c03806 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 543136861 1250 543135611 543135641
    0xc0307230a0e03030705420403120b090114040213060903051911010e060d1104050a0506040f050f0111060903090901170a150603080f09040b011409100c05030d 70
    0x20109003030800104841503941d0020041410204840000b020744241f0100c82c1c0070310442028903040600500421480c109541c003144805040c030346400340c41003030580c142115080c1840d02c10195a620400c409044410340c2001d0255011481e001500074841c4600d50252407005000114038282e026100c0350035641304108a84406c0b0100028415000201100600c030030105840700c00c05502c1440181110200901582d040048102d180b0064514031040e0000e00035000c13404000700d00d1b1800c0b6400c01040c0907151300c1d10741402c003c551450040e8034022903000d0041c0715252280340e48561101488454217a080d180380b800d00c02070b11610f035800101801d02c9904004004110540c00d040b41c00d0104000700028441140659610042103c0d141c1080f40310350b80d1040004045a0100000c042d2442002e905541d140388040800003111050440d960400146010341810210144111110300b1821158610072410081c000c880032450800000c2982c040840c400e44080c84d1600030300d0b484800c0380 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 543138111 1250 543136861 543136877
    0x80a02130f0f0614030a090f02030d0f1e080a05041a28020c0d300204030203071d0703020f09060a170f07050406081f08150a090b0c0307230a 62
    0x1013204c0c80080011380310fa8512042000c5001d40e2000e60108014a00c60401c400744229649c000900f03140605440303601040c40b111491a00340d912030200700340808d110020301f14904002c040145049402814102c4413566100030400740440c02d0041d00c42c840742c8075116001480c1c16105000500202c8001d010039074011010350312100303641d00a6546000040d002050605108142101e90304045064880910020920340100c0c894030b81035521080340c0c41d00e001d603680d461071040c14500402e42c1d00042e05011004450860041401d841e16000001d903d40582c8840b840011a8881d202d904071403944214006540307900d69401c013075010040b50644e1050109aa0740d548180c100f00b02c21a540f50005504000038040c1b00d0140d00030300e4004480b030140072505000e0740424402c04c078640d004034040d139100300d441c40180440a482c6a41c030080303059050040c11926a5007030084600603004400d00c02d40800001c0e54140b040e1401c110f000d229041e000c3c0c18012007600c05103d9400280300d074001449070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 543139361 1250 543138111 543138119
    0x30f0b0604060b0f0d09080406110f0f030f0a18140f0d0b0c0d0204030c1d0711030304061a22060806060306041e1b090c0c050706080a02130f0f 63
    0xa84a0241100c0f4801d01d803a02c0d094450a1000ca103600032107800d11055510180703400402d07180000b8102400458a5000d00d01c40d01d42c0b10306141c014008140005540321458480d450b0307201106030f902c100c401030201030319013040b2041a14005c030143c6c0091841300010710300285034148000c000424400c1034078014101c0c81d84034240089281c24080242459030342c2d8012038016a40800100611807902c07100500302078503130340c40565003003059102c20b03610307030b040030141940741e44600712203801c07043c1ca042c55400014440da486445e0f0100030800345c101030756001c1d03202c00928049080032400000514130740814405100250003922440e02c2c20300c1e498607007000818079107000200d0305d01a8a0080040c0138681d2265106903d040c4220600006040504003150000b0520b61503080c4a13168402c1d09c4c121941003818403404c81d50010340c10010407400200c0c0d00c0118001244076429242149001c1e110740c0e4404001c0030280c807036141c1021700b000d103072000020265040c207265000e4429182c00c0004450751 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 543140611 1250 543139361 543139369
    0x717061603140115111203070e01090f0b090d06050a0608010605040204030f0215070804090b0f040506090708070504080a05010605090709050a0e0604060b1207080108071a030916030f0b06 82
    0x111084000d064140c1e80040c00107411200c1c0c01c401c48504c6213081c0d4420400c505c0f502d0f08248203132007191002c0c2804014014015000141c1d07081c1c0541c2880c243c0040c628104c1100b001c008944205018801c0000340d4003203070380b1044031010342d450b00010180000d007030503984070740100302c10b10949500e0351810202240614090007150f00b225000410b403485401d50b03400300403140301014200048000c0420680300040c151070090320040c560140001100f005200900a086080c0e10409102f503243c00100b0040d55108a80300b071700303c0150700d004551030f901c0110030340d039600c1190080c815500c14642c1c5481002030540000096840a450141d81e54403051400d0715110900d00034194490035a5034180800306a1081c0d03503030701500040c00822216035810350302c211540050b4040c40e483c2d0164040001d182d40000c00c0c140113020000041c080785103015040844c5900c03801118582c00070000106034268020030448540b1054001c1c00002c07155646080c1c5030040c80b4850031a028140800050f4441c94 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 543141861 1250 543140611 543140621
    0xf1103100509120319180308060418030c0f02031c03140705160809040c05092d06090f10020604030207210f02130e01020a11011b0e030717061603 64
    0x1500e10082007003c3d0201c00400300c40e08010028260a00c8207240d00d00625080d00541c0c000b2401c00c0301d690014101810300404190000345514007c40c1004c264415001c02d0100d4051041e1f0103203040c0e034107041a40740c04003400080d00c4003e54144100d010903001000005500c280c1000315072810010b0303c044100f40500844201d6086c07000c285c046c000c5401c482400100007a0192107101c030f01e4906104900050200d409950b511130000e01e01054019190905070721140e444d401d03684203030b01d82c100c1f02100114000c0c40c00640354003814011130400080e48a1980320340360340d032000701808030600e880701c0000d64032041250280c00603c60380704000b030100c95000650010481d0b5018048002c444c90f01c13020180c14520700c00300e800499a050b40d008142c5540f10f1005150702c00000543c0d6104903800080040c3c002d01600e0b441a4542a01c0d2204440050300f04c000c0d10306c45060403141c0c0d040200019050114690008542040405440c116682c004c0307001441411807062080d450b0f443b5400c200e040352 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 543143111 1250 543141861 543141871
    0x10f030f1505100219030f11070e06040f0e0601051e030105011502070f0806010b13050409120e03030906030a50090a060e030c0111040e06090f010905130f11031005 72
    0x507170000720750020904c242030b60407c004142c10000354140c00070180038500142548040c0c0801c1001081c40b081c1e01c0c050103003032115144403805201026003a540e15440344410310a0138494180b0a602811890444002b0003034000014000c0110390307903031410700711080d101040740801401642030210300e1444201103841074078a82e10003003103d81c0c01c249494030300b944120f8000043d803922840006050390303075004100b14948155000d400702070790401d006d4405528620258485d4006100c0c080050702c82805690b4030000601c4041810407180441d4441600a011410100300700d80c81c18058070301c40800240005101c00400d2920041d4801c0f1800300014295024803481d00003d02c98408030f0303002d0b044911204c2001003540c3c0ba245d4101303141800c503518150414035821000c6002c001d511780307001c2a103510500c19079507c0c0071890803070f06030142d0354014001e03031070880d50301e00200c0e0b11801a0108104030300c0e44451402e04c0c0310001d00300200c2d19410206094481e03c1942102540103540c0e0142d01c2c021 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 543144361 1250 543143111 543143143
    0x7020909071503020d09020d1211010c1d0d0507120b0a060501080c07170c07060305010b0702030c01081b1204021314070323010f0810020705070302010f030f15051002 73
    0x2d003414a0440c007951010040c04a401c2d2528840c1015980c0c042d025445248240c1c6000c812410301c91018004401c2e10b10344010a902d0000070a440941184500741729850100348107001c010b8600018450401f41500900f561150560220340d4403045a03a0000c964002c0c9009680307a614103008005130b40751f0740181400a49403401081101d21458068540740340300c0d1031100c01180b00d10780b4007031164000d40019510f6a00200f0200115505486001d014001110440d46800b09035004aa900c0040008a504004402d00000c142c01d88400b11b402d4101c50400038cc1d1707038a800070032007002c0c6114181c90503442071140001c845034103d000e200b545c1000c580c2070441210350351400410386c0249100910114803040400562019a40d20342400c1c2c0030702040041c104071503007003805162411100031002c001c400e20410071380000c80c17400280542141d5091070001c405402c0b001d802c0300030301000d0101e0585207003002d9a40d40a402c681052500ba2801940c50100c050070b00c807001c0784d4400050309202c4030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 543145611 1250 543144361 543144389
    0x114030f04050f0102040b27090a0c030e06060609060a11070b071a07090e270a030215040b01030602031302031506100903080f0f09031b090112110906011809020702090907 75
    0x1a04142d07884113903c51040c1c44e00c1c0c500c1404100c00b241d03107203c0c201c84c80ac1416030780e031184000749a094801d03100c441c00208006c25541c5801000305401e03129110103940706200200306031070100d20516401c00c03071208200c1640c003815625104a0110b41258000b2141942407103019100200301c2a0f0300c0740301c1c203429a82ca011447c0307802c1c001804068042c004420070142d83c000c8280680181d08010700728105a130003000201e0719410000c0c00d050041c1200c0188001840c140804070310502403031415079822100050790380e01ca40302c00b00a421a4000c00079010f00a0181c9803602d05c0318130075000c0c410325081e121801d1036100c60404540c45031480c000100161024000b144030214907001401c50a44401040d41c6004038540c0081c1ca002c41b4040b182e640914400c1c0f003000a800c014054600505c40c22034643c01180c2c16580320b00700e020054002d01e00580e00c00d400528203030310031200010425007000c0c0f0701c2525600c40240e500a58401142a80910303103820200d094140700003034500c11191000e10110f9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 543146861 1250 543145611 543145627
    0x6040510020c19020616150501120305030c0310030c0821040503120d14040b04060b0108061c05070314030901090b0708070f030306030507260705090c090114030f04050f0102040b 78
    0x2150007080d40f0140d80001c400d10140781d01c00201301010800f40d018100401001c000ea55040e001d90310160401d40c000c040c0c82d000312000039000010340b41c10031203054000e512942c68000c000c003501e0144d032010b06422400c10380061040c1022072851009070950900011202050000c4d003540d10691080b140c1540c404540010358070100405400124246034000c1001c102c9159005004030781503a098481203a400103200800070f0070f120750340300300300e0a00f0446214948000065985203e400100c80441e81c0c3c003032040b0401c0420b004007005158021507170049100b20a04543d9290072403000d060101c0c030180301c04906080001e050f12085ca030700c200028078100341c940d206840301c080b2000490606480e404080009801805040d000c0c1200c9201b000d000b0010000b004050b0900d41000b03281500a41000d00440d114001c2041d40440145625582ca11000e001281e0061010f1141c00d545200801401001a03104004a00030303401441100c088501e18801c15080344901d2103130312055001005210 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 543148111 1250 543146861 543146893
    0xc032006060d0303140a0605280506070519050706030612050a0303021317010207020405130f08031504020d0501050906120c010807051204052811041802100206040510020c 75
    0x905280309207404182113004410749116020207a851540d16a2100014041428400000d0440042501056012710348d0b0300140f9601170000d0052501030703500040d851043c410b0170000c040382e0205240040c0c250f107009041c1152500705c24001c2100090078580001051840c2c005900b64580c1c02030094010f81c41203a8042c0d00030b500c20b0705c035846104e260803000601c50354150782003509074194030005642da0341e42d03104100032218024000300044024a04070000701d0712601c0041c1480c0d900049031540d07603d030300700c41001c2c1210040c40d039a4858000a0201e00f200c00c1500040c0c101c0b001035a441d603658494004001c51340080c000b0328009079018150070710305580304800007a04030940703081192030590740b10b05180346071100f00e400b0346455112401001c00c925000079049200b400d04000d00130600704640d6000070300000346511500c565211042c0c0103500100102c1403100a600030051001d400e441d0601a403a80740481d42551036010b454002212490035000301d4101030845070141c55902140c0d5406 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 543149361 1250 543148111 543148129
    0x105040513050613021504150806041b080403141803010507020c03030d0504020a05130b0909030f0a05031012030f0219020a05012001060b04030c0b0702060405091e01060c03200606 79
    0x40c1e9000c11010641140c0f640303508001c002808d002c13a0005907801c14940041c0c501c1c02c1c094001400f89143c028505061341070144440d400001324074013890540c6032420225112010042800042000020314400410341c051084403c0b09050340280181d0392000d40aa071a004c200b0b9100340c0603042009041d041d441d09600c59a03100340b00812810711241c0b12404515000d00301d42c0c2166042c2c2d502c4030006510718000302603a0b40240110015454403c201e4038801c414080e81c0000d60a000f80400440e11414000d043c1c1e0300500509400e4004104036814024500c1c07a41030100805030190804100d2440e0803d10800701442d0094044810b003851704004480222186a550903800d0b40d580703603040039400c00c2c00381300001c1920840342501e40f400c50403c0e80400010780d020a00207181001400d00680300c0000f503904903001211141c42541d64407260b281c00448820900010040143c0007045c03082d08100e840f240d0a00903601c40880c0011440114101b40b6a0140d0314036542c008000200c251801e5401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 543150611 1250 543149361 543149363
    0x50910061511073006020304030306030203150106120b120109030822020f01081e090c01020f060f0c1c09050607030609090c05040e03070516051f080c0711030a06050105040513050613 80
    0xc2614031358400e07100c140807038006070b40c07c1f000603880d108108150320b4200501440003641d0000020654036241000c0c000208580d06100f07015250341d013101003070703803034940c1104114003260090004502c6c500d40103100c1501280c00c0207082d00300d8003005400c01c201c05072807958554013805c01e40c2c50038450310041d1144e600062888004800741070800340c50340d4024011500518620004000801d480c01c000b908005503c00941426400541000320070140c40040c01e030060400c55080359603c3c0d007081d4841c13045171f41c0c485506049040c810200208080001c0c014451715003641c0c1002800d440d10808001e95030280030140400c0ca425a00b480649400d03440002018031940480e031a008a03a03039901d0800c1c10350380041c010100018400c000e10b08100f00032200076804001412050045000081c4c00d401d40944180c4d10828017190301030400c020303131001d45660b45d00113040b6600384140d403a080340644024007c0030f01641c10900883c6840d010a0303201c504041e03000c00036004903078480c0c010010300902c1c0340d8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 543151861 1250 543150611 543150689
    0xf0c030c0f062301030b070e0a03060903020328021006030b040201030b0103060f060e09090102030f011710050a021b0d140906070602120411030d0504060305091006151107 75
    0x543d020340401401d0b0010400001a000e006841d8950304040b040050b00031f0040b42440b0500203c0440e5039a90040003041c0d0360f00210004120000381001ca24600884601100d80503e80310300c07006110020492412412130b55081310419081c1e481910709803802c40c03000804615000c1c0c041401980260450b041081d03040c03400284c11962a801003c8280d95a40a0300105981920204907814884402a440860007000354518280302e46e900d6260a014800c841c2c0b0860641000c400d1000e041c41a0075803545000700500c80760424403040c078002d40c41a0406540c045458084001400740461084529581c3e92250401e0140031500d10344c89074001204075500210810a074000076040b0f2010306800781c40d6104000c4c0c0c5141070300e0140d40c54055140034070b22a07400b42e80c80103038242d0300c02c00301c0b000d6481c58170380071611340c4030040104e162064141400080e035040450101d2504e0342080030f088010455900d06a00c0e00c03c1400d042e482d10039600030b00381c017071020450003103d0401046c840d1070383e030100c91 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 543153111 1250 543151861 543151871
    0x6020d0906020d0204060306170c060a030207230d030e101d0a03080f100b0301060e030307060911010f080c0a0e060403050604060615022a01170103120f0c030c0f06 72
    0x99a01000c03684046662070f10240d01080601c11281d2600c580320281455000100c2e400c41e03840304480d52a03900e034121504c103031000100d440c41144690152500701b90700819041d02081d00c62402c5100d000348510703200861103a15100c500b010b01c42e0064080482484000c3c0c940c2068401c5c406025000114100099030704009081c0c0c41ca280802914030701501940e5050070608204500054220b0042c0c100c0d21000d2814000b401240c4164003140d04494507402c1c5203003000c2c883c202181c1980101c3c080070b05501d150400c828240f1a4040b40400544800d9079a0f0f40d034402c40c0d140990f070704242a914000148001e11254084d54003d04480e1000080180031905099583c0c1e01d55140c00402c035000c484154655074100100250b6020400c800005800034040961100d1001c040d210f460308403150041e082c00c08900c4460740580d01e00c240301d0351442d0000c080740d03840707082004210303d68072481d00014500c7c1149406561203080303043c00195050751240d0850955840d00d030f009040301007040d1042d40e42c034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 543154361 1250 543153111 543153113
    0x5070c0f05060f06120c1c0b040c0e0c0c1c0923010909060302010c032a030e0909070305101104090c030c03150501140706060e09062d0406020d09 64
    0x15000301146910900c0100260b141c510740c080103a00c805080503014070020300390951241404190029013403020744006260702a00d4640c0c0c450b41c154054042c11403000c1800340001d201c4010ba05106440801e00e03420625198071143c8081446a200386001c036400c98031003e06240c4007041205481615403410245168941c1c0c01649410b0f032588240908403030500c00d0003200d507002207000c00144a06001000703180e256400282142a09100040400c01070440c5807a4454051406040311429211045840543c0f8135010b03298108102407144900328620024100f00d2001901005481c0d0040140901c6500340303101401501c8400c10050310500c1c14400454500d030103210340303900c0d00c5c815580801e08894000e4083e0031511044640d400c4615080c501380718690700705909550f030314032a814260781c6001c10305000f0000c0c1040c2e0010031481e044c41f070034021144000203106000e10100d01c4036086032030000c0700d2408a2855614640500c040510008000c01c065901914800101e0300d40403a140c441707 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 543155611 1250 543154361 543154373
    0xc030312010f050405070519170a020706060e040507060c1415191b0e0103020f16050d1106040206070f0f081803070305031204050a15020702130b0a0905070c 69
    0x1008448803029035800108446030708800320400404007510b080103e41001d1100034624841d400c0181d40b5809544d4182214901c034492010075400180044181400c0c0410040c01941c000c0c0415192141400b001007540b1840f44003c1c0d00885d806001440d00c40d00e0440240da50380c21010040c2e914400b44404800c0c40a401d0101040b02015504d0f41c0e401c03481c04034429200b80032400343d40d05a00d0b28000c2040d250708400a6131109c24005410075940030354000d130048020340b0403030a082144100210b4031038154418034011402e054441e00070764800300394002089445c21151180c80d2401e40c400d8010a01600300700009141b183e014441d0541c0c480c109403030b292810002c0c000101c440380d80001d4520500107000d081c0b95102a42100030389112403658170340c290b4074043c20b801d0110716180ca4012408005042001c8888503a100341c1c0083c036a8203903a1030100940114409074058081d00c4440415007174144500b60305504010840d500c0203040c00008401024002c2007003007030100300605400400d034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 543156861 1250 543155611 543155617
    0xc040c121103060405090102191b17070c08030a05070201050d090b070c030e0d05070317040e0703020406080a06030818041107081803120f13120f02011d0609120c0303 73
    0x901884081c2d0b41d007803240a0004491000b080b6200507407050000440d50600d0075180221100540382c01c519042d141c2c0310903d425100c8401c000c007034000303c1c030782c075503270012000090201e01f0b010300c0400c601940c0d07484001d80c40c0e20824002800141c420050500150b019401501c1e150101d00030002e1035451642d0ba0701d421030030680300e200115900706115001c241d0711a1400b00b0203a410b848810740107038281d0302c4565030701c0036020041030555030301085403030b141d14802680c00429a904691845041c0540c000c0c0003903006009040003c0c1c1100005515900340b401183c0407a60304c5052180340480700381200007243e40104c0d1071544142c41e040e030025444046000303445064040d41c032169450f80000264040b08610a00581c003c0c6c201e16120201c103900b0500707485068081c00c940580d034500b600310140c0000c1e4143c100c070308600c00080e0b000d414450466200041903200ba200d00e10341038441881c070200f2444913402d15600010800441506040c0640b5800004044908450131301038403a0029040d50 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 543158111 1250 543156861 543156881
    0x1a04090612021509010507081c060f0e0a06050d110f030607050408070f06080c160507030311010e061005010c0201090b0309010506031207020607110d0209010902040503070b04080c040c12 82
    0x10700800c5403425032a003059401e60840d50015854600100000040c10034002c1c50f2012302143c4012800c0d1311107154074a98086075100100381000000c0d10b401c0e21800f040703168098021880c40103400501c0a210394402e21081d1b0310b00412400000f240b0b0354441906070b111140040c0c00c810381ea1350000c031a4800300500c074051056621865201d508140e0947c6c94040203038040d64481c440c01c2001c0015642000c011038211401d550040e903034002400500741004075801c40200607101c1c2c000000103041e0300c880780258a8606000a018026580007116030790a000d03550800d00001d80c81040040d036020315003101030944181450b41c1c00550716111001e09400c01c84181e4041c0c0d44031402c0214a140c00e0040818100c41d0300f550712f0405200e500030504901800b04024a00706040d91900141e9070340c100760803101d81c3e00510b80300182da141d01d0120040c0d0030511840d4042e00c0341794004680300703c03881c09590698541c1001080c0c503c82c01820400500050b81d80c01d400c0c040d0b41a00100740c0c01c2c46001c2c00d06d00c2c1c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 543159361 1250 543158111 543158129
    0xe0f0606120702062d011208120103031d0d0c060809010b04181b030b13080c030d0c031116171903020c070b0f03240d060501080d080108071a040906 65
    0x9181155100b1548442c20000c61917020b0529100e120307940510201030b040d00c06854811001c2c1c5070514080c0968402c91383c071840141c50a100010030513a0010fa2601d9441811541061b075602c04000d03c000082800001000308041840512040d4400c10000f179010031203030004645131600102080c00c0314112040445248062003202051107140b411000107821100c00008525107035448cd8801014003401a00b1190401181001071103044010313035000c1c0350540c0c1520ba82d9841100500014216000b80c1008a41060a0500303803022003000c0c1c1e915800c10102c0148001455074070041c013440e00100b41c0c0c1c0c4034002803080c1100401143c0380c242d0030480c10b4a0060b61162050f00796860440701e81d01c0f03410203034001c109201c009494802900e4005a04900b074182606280111440f420680f000c03464100c0048000c3da4180b1a4a8008a0407280144182e5000e00030b140400c482280090247c0c07699030b80a03160401251580d52092800c00f50380349071041c00c298983c2c54080540321158800b42e40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 543160611 1250 543159361 543159373
    0x40c23040510320f1e030c09090907061209050a21030516050910030b042c010e03030112050c0d0b010e0601030b09190f020f071a010e0f0606120702 65
    0x402c206078003085070355512000c0c8034100660850060302c2144541241c0300016071001c5000f10001c5e411840203601450301c000400d80340d180072601601260402d131250744c8038070543d40108005401c00301d402410b5514558421210071002a0b85a000d40009030003240e070342c070440c21500081042c0001541480e950310708030a403080c01c100c0d00102666809008846500080442500b02c203030010111481c2c003109480305040524400010f900400c11040100c0c0c00038180038205448038035590081c0740c1844440c0d21404203152260b00c507800c0322081007800c505944200014052081a101c050340d819104130201c801d20319454000c20b03a04000024120382d1640c880006000102d0b10381d450315070000c000e20b4200b028841500015007007a41c09001f95403440c03022035280c981e000064000d119a100c5480c0250341c0c0300070014109809900071501581d445280017400303807080722355003c3c9a0486850303d100410b661102030420134900405040d0302c4d0301101c03c00c0b0b003c41c200e0f45486071a101e00240d0700075010f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 543161861 1250 543160611 543160637
    0x9030a11030f1902120c0d03090503010e0a0206031f03140c1e03060403031521050c0d08040e0711150f01090908040b160203060c030402010905040c23040510 69
    0x1c42c141c03000040381c1e590380000290703102c5088258a035207070940d0101e5121103640b02280301c0904041c884480d99420850f611885810306400000d09070417540180e00801c483e0186450064540340c0d60417000f2340c44142040802d68109031320386c140000b6200c00c004107038010380d0382d80e944070340419000032100030390084060941e4520b000180402004080c841a80081150400107911884014001400c0c99070780c041d01032500740c032201e50034068110072109031449001e00003442c50b0b4104c07036201200c85104848d415400303410058480d400955000310f03850705240c1000c0c2800c6190000800e0902003103a8103142141c00038080140036905081014042e07441d080c1018000c0c140303803050700134100302c90410850000003064402240d088817100320059480703140c090f11801140c0481c03e40691b140c42440180103001010000441c09203100f40c81c0d00141d1070740d400501c13003550b64030551030340412111541c00b905d4400280282e2000d02d030381141c0c1403406840c0e50001d1400801403a10381c00150000c01107403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 543163111 1250 543161861 543161863
    0x5070506220501210507141b01050903090109290d0e0c011d0904080d0c020601080c01021501060318050f030918060904080a03061d07031401060203030a0e0309030a1103 74
    0x30300903000a01e4880101480c07140b1403481500940480013940f42e40c0d0780000e80d5607100d4820f0680804500409a0340d410014455100e00c040e10480030407035500c5c05000c2f030344400f000001c80c1e01203201a12151501c43c1351404030b0fa50b0100c00302042c04500045001880541e0440004140240020000003a2450104101498445107540c00ca05111307020f0345644100c050600a11103004c401c4810340507541e40c61803d5000c50042c8802d8507003890030001009645a00403030541e0503100007104641ccd800111030b00490350f0f56400c242c0c5c1d41900c01c0751001403110510940140b401c0054171089400d0700e00080d0b480c3c2d0314098031112104500d03000419203880f507160482d52804501c0668140381c0740742c1442000038268140140c030082c821940007580d40c1d046030003500110010b090405494201c0c42c00c82003d2014200112070140001e450301a06001d4100e0400c030300c80c1038038140e6000b1404c5540766100b940003040000c008000c43c0c80f041c07028800560702000254003542c4a01380710041c03e50140181 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 543164361 1250 543163111 543163177
    0x5150a0e0306190911030a0c0302011b020a1502160f1509050f01050a0212032406120714040503011517121c0f0e0a2306040f05070506 59
    0x1d00c650020300901c0a6000d02c560312500c1801d0480c8006180021842c100e0342ca01061070245405029809422060007013080c114011a8001e0b04d0b030041620340445401c0310700c001c07041c009601c00c26140007403000c1d5010052800c014100d0380115506580601c62404083d40c882e4040340c0f680d03480d2101444600b809220545400049d0f0800c101110b041c0000940c1c510302045a2a040100103e0062000c61003042000420700030400380d155030b820a08901d00d0000c0010300c1c0e16034001c086c110340c40741c58108101203c00c204800c0d0f01d90382d86a210000c0498150060070010b0170b852009001c0464a59004e1140f0240400a909400d42503031800c2c41700541c0103262401806181c109940806201004000316401020b41c54005042d20701c1d070348032010080132124444850b00e841e000002007080ba0014403031041d5402a9452132801d5034001124504402c40100340d0340641008002c02c00041204845051452050054490302911003001c510550000810400076004418010000854507003103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 543165467 1106 543164361 543164387
    0x3090328021c08070e061c050117012a05070b15011d1509061b03033408060d020301050108010b030f0a0201080403050705010605150a 59
    0x111406042400030314401511a0348000710480c0c0807640840700480e881d40d24848181c1d035840d0203d4800c600d10030440e40091090001403201e04104080b203084c80002100000d0b03940c582414aa4000ea41200491141e49001d9120b0b010403803a01c40010700ca4442220849500d00c5410100c96901c41e958015080c4d501d560180036007403050394000418100d090341c8401101070022900921086a120340680c04a40f070300070303000c13900540740103080400b034014202070900d1803005103041c3e58029078420b50303070f19040001042040d48034076502c0e8042d04504402921101400c1e03440c4c0c820110b030380100740d0a0003940e20000e01507580c0c0e0001c0c8241260f010f1f00070300841d41e44031044c1d40604541c4038031a00c01e014000105407040310000301c2040c0d25030142e607400880e88640d10280c60550001b40103031000e5403610000b2445484142c0208603d6200000a564450b80500014201000055 = true := by decide +kernel

theorem cover : BRFrame.Cov 542985611 543165467 := by
  have h0 := BRFrame.cov_init 542985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 542985611 ≤ n) (h2 : n < 543165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
