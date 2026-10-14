-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1171
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:35:11.968727+00:00
-- url     : https://prove2.me/submissions/8d041bf3-68fc-489f-84b9-5c8d3103c236

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 210431654 ≤ n < 210611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 210432904 1250 210431654 210431659
    0xf0f05040521161d0402060405060408010c03110306031902040e0712050f031903090f02150703120509060105061c0603030e0916081f031b050315100303030506 70
    0x1404001015030b07418044140c00418903500e00801e40c1440d00c580d161100c1c008000d10310040450052110b008407241201040806080c4e600540d1202d001203802441039410a81c0c10200024000c600355505420102c44183c030741d581006041508480e07040f1034041558000e40c150010901d0300c007001500e501c0755201500043c40011114807044a5601e480350329440b408064588160b12814000140049011a1010300c00346103400c000150840079440a81c000200785555074108505002c0c420203134010300c07a4042c02c0400002d01003001610190070510044000903241c8032510900125405414052022003005110356401c200400c00c5540001c000d0141c600200300030b00ca4907500a00031000110700075102d0160702914241400400c42c40100030090030304d0341c03100d02c0240030f43c8004819404003880640b40304075003e101100450f031174240c1c405840381c1d814004c8584440d0800e17405000312181141112100441310301e069600700300450b0342c54030340000f800c410004213000303400260381312400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 210434154 1250 210432904 210432907
    0x3031c0213090902100c03020c0405190f1a0d02060f0c030c070b0d05070e030c21010501090212010614031501031803020a0c0503012a090e01082a010f0f05 68
    0x40341004401d0312180d07002c40c0100c0d032912414415414800301d00602c10301989003000030601c0c6620043c0d504c0e410031010f14007590b5100d00040c3c070f0b0815104101c000d03250303400701444100c402c07100328000b40c44c2014600003c5420242c1d0311341d4030711b06004c044072242e42c003501d21411300ca80605546c4032600189102682c0b40010401c00d00c00c50814002c4c00c0c098940f009c0c601b92641e00801c0c1507801c44d500100400c09020100c94442d0040c0c1c5c00013218151303e03134200e0b406240c8014152180340000e51241c580c200a40c2040e001080040741d9030080e001c940520821200940ea030303440221050700f1080480c10301c4020410118212200403c030600707005206040105403404072804801000c2c401101c180c0040e08006c91350707010418041c200d1401080100c000780034513003d1400c2c00d17228003190030341e4059121030700c803070303944458050800f00001700501045240c0540e512500117850383c2100707030703001e8000224010300f0320103522150282d140e080041e595089903d00c1c0c001d080d21b00c0040c81c0014014040c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 210435404 1250 210434154 210434167
    0x2280302160b2205010e060a02030f04020f01090801020a0e0f03030306102f0c03060708100b0d14040807030311120114030a021c0303060e0f16051c051f0503031c02 72
    0x190300c010101d83d40c0315800020b0940800c220640c2815005855030642e2030040060200003a103039250076801c242c048400c00600150140140d645540310b6004044a50020400c0200250084126504000159814810756604100b0162241700859100380e210b00c00b4480c441c00a442a0301038200c5448440c1e0001d040c0122026450500f4845003018080d54400a4140c0172070900f448001c0e00480f180c145441c2505100300381c5401c41070709000b003154440c00460349030f036a110b0a400544003100003c504811904150501d1140c56100b01e0090300030a040c020520b0901d10b0300c1c4111039000508541c4036480342d007407181c8600902c070411002541031003005162800759540501e205503240401410032448111072901800f541c245a014902c013a0100d002c0180300102c102410b0352051380070400764015010f10100382e0f0107005005262036a5400300c1c0300d1803581070f51a403203503002e001030f0034100000b04d0380760900640f500310310b00074940c068000344480c0514142458030f130044104804000f6007000d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 210436654 1250 210435404 210435451
    0x60207180609050c04091a010210022d09190e0601031e111e070803060607051c21090c050439080106020f07030b040305070602280302160b 61
    0x1401a224400c0d131241c002010040e120749480740c80392803c002c44220401400700340020b511110185010740303840d500000e00702c40c480001c91134819000ca40340d00966a059800e100381a8580260307900c1805281482c54400c031500082c0d016004641d030100744208a42d50f000e004401915950068660390070142400f010541942e01591040001804089440d18144115071070811510550312040e51001c00081010692000844e60300c6802510310035940d08080c68005d03d0700c0600c511000301206401120700c103039644941507880d0000c591804408005407003003450111054104001c1c81030401c0d00081140781000d802441102c0150f055000c7d00701103903684402c9112038003840f480c0c405a10b802d812030322a0001350140c09040140f006015110301c05c1540c030754842d510300001d0082c444880008007054410400c80f1340541d0300510964582e4880d05820950380070744043c01004a0100c2181e160691191090b100e01001c4140c0090035080580c5946801030800b0b0700c1001d0841d5180700105a60 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 210437904 1250 210436654 210436661
    0x20601030c330c1b030b040605100f030f050c01030b130f0608010c0203040f080114040605040507050d0303020904060b16031202091908071208070803061801081f06060207180609 78
    0x861440d02d800e9142070861801301d40d50448200605003000c45040c00740081946080041e52041c2d01c210000b409860b03031035400307a296000d42c1c443c00d9181210a0080200015a88107401191244044600e0134480710015015145800300240d0812003d41c90314a1441054010301113200c0c242500151140d00d5061544c29078901a64510140e4400a030412100c035642c4840c0c0c000b0100000200080d01e40d002c010a030310100a0409460243c607140401d05000041c440c800c001e100082008040311b46074940600030350030296180d88034524055001404044240488681803100007080f0101c0c81a0780d4199100d04600c001a0b03443c5070b092104d0400c6495500b10007107440b00c04080700305030324035205209140c80c08603002080c0d41030811501c2d10001e8030032015102c03040d60128003e62039981c4c1c100807803100d10b0000d2501d154030b02036200000e00850049000c6036070709982c141c00f00348086488624001e695440c0304250040e4451102003000c2074001107151103080311903a0105049980d1080841078 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 210439154 1250 210437904 210437999
    0x40b090f04060e100314030c0703030c0303061206090210210c030b090a021c1104090b040b040f1a010203070b01060311070c080105190b0907140c01020408010b10020601030c 76
    0x41202e107400317006004006445032180280e400085182ca80c5141610707844142a1000034103210a19141d0b00402d402608080060705000203da0070010b82400c0c2100940001ca60580c0155412654500018455a1403601d041500c10801035210070407070107540100110152031003096901e10080c000c1d07640e48554140178024205d03001d6221560181301048510458981140315440c0c01c08038000450403a0a4808440d075183c1d0004a2401c40d0010030003400c440030020358403c4c544000742150010f5648a0f10303001c0c10221401c88030210303480041e6a644550301c0003400c000c10030f0004009451180d00051078010020049500303010260380d56600c1c80c03840780c0110005944a004210354a089440103070403411040000388010b00d68900450756042c40035021108001c0485104280b4400300701c1104c000d030030444000c6513503503501c4003032034001c051040c0494032800d0100c1c11100014400101c682c143d9030031142440b00a0b180030180104200c0b81c00301c40d0960100e4503203a990307000035103884103107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 210440404 1250 210439154 210439171
    0x3020a0b03090c03160e0a0f09050d0207060509010516080f0c0d14040506070b0705090a030506010509060901080616170106030e06070f050d0e0304090c0906090803040b090f04060e 79
    0x4032400e0030041541807040981015000e5845100307505e90b03d45c152818003003100c46d812011001c640700d50281a0250803031400c0d4841541c03c0494900401c00002003000600794190b09480c001502c07403008503010b110b2803000c54001142480800300c20303810250043d103018400c00400c1e1404984400d0003119400c2000c004400f90840c20000a420b9000f2114294a29840103031601c0c080c240301c0080ca2a0282d13110203800185288000f07021540118103e40e07240e0f000500000031140c1e28940695140400d00401e0301441103040456a1414070881c12070513122010064005031741d682d698100d0f81030070144120f0030012403242a4540d00c5812001038041d04e4240d40203d201100030244518080e0050417410030460b1307624401425650040c00e403000c1d41850000411040c5540441d6451400f030386e040342d0034041c5480a02000f0700e810032002c0b41211311302d0301c41901099461099580368003442c8108410984100000c00c2146020741110388905002840095110f0721031441c44100107045807640e2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 210441654 1250 210440404 210440407
    0xb22060c0b0708010b070b090c130e160302060906031909060209040506100531090b12010e0a02040c1209031d040e070303111509010615020c0102070512010603020a0b 73
    0x300344800300d02400d50080450a20507295490708203c00388a104580001e00b02411900105481c01c9080c44900f100360300091420003003a00c100e07210b10050410417000040d91148a4a101125402400074000c80e50000c2809080005d0041404515400246503a5014542110180b06030360144100001680500700040e203402c040700a02007100c0c070107040c1c039114282d00d803007440810380c1c400200c841c910645240c0c6110313181403c90b241c950085900c401c038003c401100003c51400183e43c490180e0040407105100c086901c102c04600303c07280942142413136003104012101504050b0032002c200311407071810515440407551058100c404c00402100040e00d03604c5100d4843c00c8011045140c010220340c20000c94440031038441d92007002e40b20083c20310100c0600e50444c2e40c0c0074401581164060210810a880d01404850080000d03005000c0c441c80c00c44101d10f00103100107445251164107800814140e8100410024540c007803200d010711a6480341c50101c01030b241d205080005080034141079 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 210442904 1250 210441654 210441677
    0x309170d030612110f03070503010219080c0a021506010c050d1106010501030212062b0323031504110408030703020717030307170601360e010605040b2206 68
    0xc00782c070b4959101d20f84507040715101c0750106802010414080c82d044a0303400041d03c924021a05040b02e95004507815440841d654100d500c0c070b01140c2032050b40c280c0d03c41080b6aa1880c09104034090340e442c400c01a88003014042902c1203015200b504150141055101e4429940c1c4040c0741c400242d1503100003841401c442103203c14100a2140500000d0800707500300362446070400c603c01390040c0b000c0e101d04204170002130001818041d0b40300320709140e580c1d40a00c0c0b8403402c001e8548040c1008039400c2d846640c0c40a030b4900d0381101583d0240346994903044074003003810108805007650b0f10409012070000c00000a880c0030070001844064443e03000340a06034a003441d1081580048a00c040c2203400070810003031410b40c4001c5921075441c00d8061000070380c9849004840c0468032007600300c46404080039a0018405000800c00040e80c2150342402081d101e80ea031101029082c424400441c030203000a10a0005140c09030a0f0301c12502105012844403201e44091800741e5440400414000c4441 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 210444154 1250 210442904 210442907
    0x7030c0b04120314061005071a0103081216050706090c0503010e071404020903120a0c0804030803040b07090e16140f0301051f050301050f03031c05100e0f0406090309170d 75
    0x58054442c4c05148507912490800702060074041d0305e5420404010001420408000041c017207102003402d241c40c04900d42d03071a03140c01d00003035014050b5128403001688c0002c0d4840c00f603805503008034100343d441d01e050841380c0c2d80b554041c0030b504804503280c101b807820200712030318240b081c100c6019104000301092031501118100703002c10403014501981c010040d80c2c001e611f00096103141c14095804441d0355040c0759000f1a014103e510303004200c0f540015002040c000750704c02850040307008241e00042d90310f030200207546101003445042820540b0400160b110104000001610349480c00c0582c49404101140c4010b6413041e04c841da051000840144a2420807031041655030108080c8040d803552001784c0034029000501c5030f01c0c030402e40090001030588052040d240844031442d00c46020000d90300b040f1014080c1258100448008003400040c840d0707084035294081c507440880c0420a40b00da8440c2c00141100442c00d9050155042e000910040c982c50541c4101d40060047c190300a0000030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 210445404 1250 210444154 210444161
    0x271e0b0109080c1005250308160c0f02090601020c0409060504050d090602070506090a0b0a080106030e010c050403140a05060106050304200906041a0d0b01090f140a0207030c0b041203 80
    0xc105a16448046881034649480c41034680038804c60901a0b1a0072201410351100100e03603d40c809407041e016070450801d6080182c0c9400b07110315160400b084000840300f128419400c0034040d10952146031080050b040c0718161a0308601c040c4103644001d041c20002c50160340103a50108c2d5880d540d10104400d100f010f01c40c0021050b000d01e04003084614080c4020364401050140c28400c0e080013030901816a61410154014080242c19545403241c526018101e81024810800464100740d00714650a0040c8170b04683c20007189c032010300381811621344a080c00051520b612203446074220381004240100203082c02001c0c1e80e40c5079035491501b031500040342c0b00811a800c4042c14102e0303102030281c2d10f85200315070010040d24000354803050b9500d0156010f41d19140f242d003040c1c00590020502c0104030109050f0f40c116601409103504880c95070044402c007045101091420001281013648150001c0080500038600515040034a40390401603100565080355807a081000e80348d01543c0500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 210446654 1250 210445404 210445409
    0x20a0f15140109061212081003020d1b05030c1005070c0e0c19020105070f0e03011b0210110a0e0904080c060a1b02010911060c030f03160810271e0b0109 67
    0x11490078540d18642e141612010038040301824410f01d07c00040440c250b07d03042500440c4c0090001515403543e051020550006014142001b0001180400c082c24001864100c94201500c04013100d600c40800702d0740c03504100b10441d40061007000005540042a44060180f05103030641c82d0b13034488000380c035000c182e43c075500001503905080800ca802900a0182218005581400c50032609000c00080c0100000701e201220003a12001c0e90000079070010f200480b10391428004c00c000c000c0f413074144455000e40507082e000070383e0380c46e8000002d007040003826400a00c201041400d00e089104404d0030000d080b113101941d0759489180d00d070f40b11242c40e50b8540b210151b000030021000a52200c05000c0000c0c1c03010340c02001c1c001030f00c00380710f0010405c46681605284903142c40382080101550100c03003004ac10b400240d040300101720800e000481c443c2c21203c4001034060b0030885181000036134a01801440c001c283e41d91820100742c030048080069242d08064002400010380002411104041c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 210447904 1250 210446654 210446669
    0x30f1201060804110f010507021011151005060a020f06041a0c0a09030605060612090a0201031d0607200105040b0603060114031b121207120e01020a0f1514010906 71
    0x901480b000c82c800c1c1035400ca4100066844c0030b017030004e40c00186c1c1c26108042c0003e41050703d03000316030b94240d0312142e01c080061700c070401c1c1c5156015803a08840c3c00a42039030218813501081c01c08000c1840c0000040640c0c1c0c5403801520802144502481d0800d041102c080d030780600c1106c10940d012406808441d03000b42517a104500b07210000800070324420346400014202c3d0b039a900071800c83d507102d405444443c580a00302d034009160240c04580c849a008038200d01013030401b9100a961480d041100c503400240b04000e05030741c0d8400c10304503004440100b00c44001c50000c2d0809160310300078080c1504c91170042300f003040c15061003c241440d00005911424900c03c01000c82546a507010400a200001100c001813400e01c48030300241526500801200710361007405004a00602a0409040c0d8107008640f00c900d0b610480d482540c0c070300040300709540180c00010404c1e00049142c045280300d1b40c01003280c680a10032040d04481216003c10101140d89519801000705020034010302000e05201e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 210449154 1250 210447904 210447917
    0x90115050a12030e13060b120a061a0d021306020c03120a0c0201081017100c09030b010e04051e010b150901050924030c04150f120e03040305030f120106 67
    0x10100052281c04402c880201040f0610350118913994801626403200180e01c44d00b00440ca50340e150350241c9504c0805004e01002c1c284000480700352103442480220703242c22020100f05080c0c6021005294080946030451642c00d10502c08940d04200148002d402503400425010450604051818106e841d145070303022410800c498075160b006034080c030855420300b0900d10340e40783c4102034005911241c01c44400112540100800e034400000e202c1248680c3d003400300014860400e088403103840302e001c0a040a0081001002480c03c1b43e241c06602c280580203491079034810a05408602a1100c0c2000c160380d102c0da002c5015290004240e4192005d00d4221344c94011158000b8005000b000300c042c0c85a10f83c82d004001d202c2010344e6500400b00b004081640d240b070b0100c415602c40e0020301540c521961009540d07000030340a010007601c10380150b200e503080c2c4000482807002030504610b4621880c041800000b00140e000c1015210900c070340c0c00025100d8071981c0e01c444103007005901c04401c100c0d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 210450404 1250 210449154 210449159
    0x1091409060c04060c1514040c080f06060904150504030f0f03050f0a090312111306031e0c02070302060316030e03030c07020402070201210e010f0938090115050a 71
    0x2d600102c030f0849207030303040143d050680c1e42000100c00008100c407100c02c905020001a01c0c40f6440c2d48103201c0c40c07241c07040040c0d040e00c4030980345e6030b40c4c402c020310045640040042111460903091813640548644000b030044e0300018840305c1900d100755030480110780c00c840d42e03d035880d400c442400081207085c03808000c07610b000e9100e040310780c001078035050405a80c0d605030028540b01d050141070715484900103009100702400b000100d940711064103150400d206901081540c4607005001d1030303510581c0c4202d01010301e6242c283c0200501041401584a030b0400040182c65920155115004c424a45c98440c882d16501601340c44400c2500750080c1c00820070000101c031101c2c25a00b0080d01940c0040c0c54444602c01a0b411018134048504003440305d1140e48080411a0800c034034181c40d170002440503102c42d24000c41a00c610160080400c200c0e07000e8507012480283c001020041031010042e400040c0d500d524002c40b000b0b440220482e5150304140e5005648400400002c04017601e2034660340380f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 210451654 1250 210450404 210450421
    0x70515071209021804022706041a0108040b06130c050306030609060106020d0507050709020304050d0e1e0609060f07081b0606100302031005060f071506080c0603090a0b0109140906 79
    0x4100d0403a41d42821340c40c000c58259190711702c91650300540807520300d9042200400000c0922000c54049200e1420012810019441c1c0c542e86c103446075040e10340c04010b1721030381e58001d807442d8000c02c8142c200b0b02e8101502d050110501880d0001c15503521003941c1e0342410424942800f034021b01c010f8880d4844401008a00c0c0d002030f00e00c0102589292803500c0340c10700d25059080034150740c402420f4a00100c140710031302c00302045100d0314070055251112400c0428084c400e9044055681b002c0c048031a40d40850903082ca03600814165034014509850018140303801a80e503088014140c81900c0c02140440e0050400004119a000c2400040c41e00d40360260000c0c001a00c55080384003015000302c0442c281c4801211074a025050061030313030352101140880310060b5008840705480140741030328078040324a210711919065640380e030b020b0030800d0450000d1118592021b8503042c524484ca0341036402180380e40c0c0c0254003030812902d0204c1d400c240c0146501d0a0710b4040c0c0003e45603040541030144e00c030b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 210452904 1250 210451654 210451669
    0xc1b010204060c0b0a020c0607110d0e0108130201020114010e011e0b0a030c031d06090705040213090b0d15050703050a0b0a050411160c0501030c0914090c07051507120902 75
    0x2031360041e1410202e80c0c84201c84006405500c00180345845468144080150040c00c1c140401055404403098490245811274006482a01060128600e9008102951690021011418018000444c00d2100c94145542e40802640f00d150103040000040c00311211323041c2542c0500b0480c2960210403810580041c40f5440703581c084030705141c1d03241142900c003400fa812042c1002c13500044001c08141000c109520b0314021910a105c5001352040810545454400d44144400310450105202e082140000044c110055800d612500102080c400641e007042500090b000b10900172034142040368004d4183d0718050141810b65060260b07880c20750301c0d0345408004540c000c840c0410050303100260041244510001c10303680408451807007040c000e19004800c00c8400a03a000c004640d000074080b01e894580e4020060100713505418200b5600e8a5414030341c0007034580c14014a03200d0a0360b5518500341041c2d0020170300d500980d0400c074031170f5080001e101e01416041014051303104180c0c00110f0342c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 210454154 1250 210452904 210452927
    0x20a0f140105090f03100c09120f060c05090312040e010905190c0e1009080c09040503040b0a0905040e100f0501050d0f05011103010e0933130b0c1b01020406 69
    0x40110105052001e5951000d61a040c0300b03024003681c007107a40001148001e0f20b602480c040108400c1440002c1640c800006134032114ac11010b80c0d140c0e0b8900c3e94400c000360076603041500030864140b11058561350300f4041c1000c04d000c0f03564203541d518500520800d4400050b4003035180e0340e00d01800c1240302d6a07010031140c4840c11202c07000030590030320481552420f01c0f6804564000b0502007141c41d015401088100913103030f1003001c4400c103114500400a001c0c1d811a0000c02c43d8006101c20491100d051024000c4003625080900110b510fa40c00301d82152076813a540c0750540d1280c54404039400252040303800030f016882d8140038940c18403001c100c200745030b0300000381801104440c65040c043d0a520a204050708217140d2662565100c0200e00d0000c1c0c10b8070780c1c2055004801012554004d582c0b0380030701e070781c48404508940300c904079018090410000e000c24508040b1034080d80006101e020910320480c88514442c2d00c03644000c0c0410103030990700400760011713072041000b44459908070780d00b03d21 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 210455404 1250 210454154 210454157
    0x40821090d02030f180a080d03060305060105030c06070318120f060c0804081c15031b0603020a08012d1502071d0f040f0b0406090614100528080703020a0f1401 70
    0x8a002800042a03101c04d46c1c1c0d000952501511080f480c2044e4540c020004481c016811510315980300c40400d92140401e501d100d41c0703c0e89c01c20a007400603003d0f02002c800136000d500c9420803c2c2e690191030040b00d200746000c07100004d1681c0000f081001c1403103448048032842c138108145142541e544012841102540000d1090984003100d416829800141042c0c4845001e50903083e074a02d001a907054032808000050f034903070300b00841c45610a10907920070100540d03842d4041e92030306201a4a000940052040d00403c00005901079151400c4000040030200c0100500d8121540300a0804a1641160008061055144840160024140d90001d04d9002c0c1d010b4951102c0c174103c6101e0302d002c5401005001c10b8400c11044c045150f20901c00c0500419080c804000c03000750702c440d170f071a003141c1200544124580c107010390304050008151900352038401c400d20807484504013203aa459548807408991200d1010b008604140c1008801060394941c0d50701d1b9941449070318401000f180c00910b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 210456654 1250 210455404 210455437
    0x11150601050c0111070c0f121502131d01030203070b1c020901020c100801080106050402030c0d0c032301030c0b0309060c130504141509011409040821090d02030f 71
    0x1015a00031340c0100e9920307866807400c640c0c0d00c1c00d0f0f14085560a0701403103030400d0f00340703c902d000a0045900c050241e500d6801040d26820310fa030220404001e4000a01d03521001c2c500340c10200c3c0e19150541d04900c2c480c0c1448484c0d9103076246104141c40e100c403940180d0541c1071705000d02108101d0b010000c0380c2c4140201d1300035840c2c01004004038546520b034007049502044210720514415000944941a9620140280000d5480d901070000783d21084d43c009003401310400c228585000380c3d912100d0800c21a01d00402c0c5800030022000c41001c08651191340268040700400421000300c406200900c03403c840d450651818440c030307a4980381d009040c05809400015640c245200c00031000c0c002e810002d00411040080790080c914a6904482d01c04481d08040c215610b00c0c42e0071059241228681c2410399142641c6c03509111b00560b0150003150b44020500440180c000c404814201c0407080c000340c8045860081862403401d41030403494019074004000c92015203901c001103900b2540c0c1d00320b458 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 210457904 1250 210456654 210456667
    0x70515160f050607080f060307030f06050a090b0c13080c1f05070c0905070f020f031602040b1804030f03060e0609060102150901021806031620030301030605071115060105 75
    0xa1941d003000e00e0001d0240c0a040308100801e070300131214034001c540d2080e0300c80d41c640e40c1205169540003940009040c04400100c00000121240c0060358488680c2c0404507010b092a42c0d034038400c80c41a030f000e0404003008216270000e40851001007008048a1008144441e682c1000c100c00515982440d000320001c1c2c1001091031380980115400a40d2140500c40055954001e02d802004155220b80c00aa900141c1c0d481280c030014514880c907035180b001d149042c2076003100c14049a0303940c00c00c9800070346803051042255201115924419002204445a071619150051990300038407456400d05103445800e0141c1110348082a070301900c2640c4145444c3c40d8240140e1421b4110034a1032603401a8a040189800041d000741031021208204a804001030300200001800200d41802c0c00440d80d041259581d0301c41c50003441c400583c03109054814050394045410355001360015128103854405100074640d01c1030310b2603101000c1b00c01408902d8204200c45458080140c00581049004030b5031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 210459154 1250 210457904 210457913
    0x1608071a0403021c02030c060c161b031a010f05010e01030f0905010905071d06100e090408031015051204110d050c031e060420040207080c07051516 65
    0x303440051a00905608a103801d250081d41d03403038402e001c02c103034040c10614512103500000030384980325507002c081d03c990760318501000c03020741001040c580700ca00e060102e41e01050202c142c413807c0d950f4014020040604505240003803c4000c0003843c64011010010841d1440c80d03014507003514000d103404001c40065400480c09003601580c5004083d00c2e02d103004040200c1544a41055071007081514a015600c0307602208144604500749185400c4d140090543c0c81c010071310113000302090600f0307490407403042e000c01c4011034112030884141c240041405940a84013144000030002212000c010210082c0c008219010b0889003c210503800f4010074100850311500c1500400041e006443c503000c642401542c9100402c0300718003c0c013400c9040100b403070312603040b8480303494940000d08650315643c0c0c43c02201455183c1d2041907009a40305103100c0c0d0f40302c0c002841c0140c01000c0036503c64400142c030b981880801d07400b00c0e11032075102203c5c01c072411200080d240b42c41c000d010810040c3c1040c2c00d2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 210460404 1250 210459154 210459173
    0x50702070e010810060e090307140f0d0809100204060507030f032a030b100206010b0d09051b030c041a04021602042301120503040e041a0a02090114160807 68
    0x2040600c0185000003040f042000516071482020b0f10790280a5640e4980e0303c3c00e1912400e40b0a80b506801c00c1000c0804203c26443c1411140b10310821502e0a0724040806410030080d148003d0018400000380841418104120851210031100451402d80381250180003480f62007030080501c80e404828040340c03402a4002d040344000a040f0b044444140c040d82c407100034003e00703400c003c09d10301350031906a4100380b028454000155001403106908202c2d03141900e03040809076110a0386c580344401c0010b20280b0006680b40c400100e0f034000300ba00761042608001060941a02a80c03a10040c892000201d072724466118105a50040c0d0301c1c0c8200070703002034545202c20041e4001e0b0521040c001e10061400c6c0400000c403021064012590300c0b420502c48065074440041e000e40d0007400140402400c800e00c01b40c0141c8034500d0580c20030400c2503035132101c10040b1820340c8425404941c15645507040f0f10340a100c0b555048200385014814001200349c03c05840d400740480300e011610f40204046a00c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 210461654 1250 210460404 210460409
    0xf19090c06021011040b04051519080609010509040b0606030601030f020f070303050f090303061003020912060a050c090604140301020f070c05040c080c031504110403030203040e09160905070207 85
    0x10015a04691101d1000e07542e021542503642d86603240a0001c4071082014003910280e0750341015803413419281c0010001119141018000c2000c2d04010048040044100c1040008420345640d540b51038007208002003010140d1049020340440420000002c1001d030308907602090132100992651a40001240200481124015210301c0040c0c0304038038400040180c0003c0d4400e640c140b000f03583e4000c840e43c0c1c02c1c1090301c0c44000c0343c2c07060000c0b90283c41c0800c1c100746507001c0b82c03500605007081c003000504c1c403100e02901e44c00d2641002c801d11034840c1907401a00d902c20b01156240345840b0000c000b003082c41c4141d118103455480a003159100741c0c2c0e020b404640d5001c0d2400c01b01d0703841d4001c0b810b0941186111740310f0240b0a87c60982d581e4940d6001e120903a01c05c170005000c950070340e034030403225404042c44840c0c00c1d5840713507640000ea002c43d840c0c840940040c50080e1300035602c55003055140c2252040c06410b0401e2507000c101c0041c660f4502000110558010420114294882800680c40c0480302e8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 210462904 1250 210461654 210461663
    0xb070b01050a060813020d23030910030204030b07032d09030e060901230d0608030307021c0801090b0a08010c0c1a040c060c141f050a05240d020411071a0f1909 70
    0x1050010295400000ad800038001c100c0e5001800e41500300103808900c200c0c440200280380134000030321814001c0c1d01c09080b104141400d0400403603035001003900f1000740c0c54080440d581e04c45502d800d15510030319041e0014003e94072145400141c00001c0c00812148005805030325907407400352081d81ea1102521115285c4c0101804880d459003900340c0c598008440c24401841185140344050b80030303c1d5101e0030050152900a216400c08040e88058251815401e800604040380010801c00912070090040c005070b50702c9028141070f1402c81d48500343d80c07088010040c104c509100114400c004154202ea20a08004d8641a000d142484141c0901d262600150141c00b05081181d4204404d5001761802da1000304001c3da1a40c007401d084440076200ca4500350000103005095002401c6034808110005000107514102d960000f0152212482c900200c014045222410059070002100c191084c2c11420038076490003e480c060031080041c00343c0181c0c100301000d00f0b40c982443d8411140c05030003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 210464154 1250 210462904 210462953
    0xb040b0d0e0d02011b0302040b04140319200306090303060f010c051f1d1b18010b070506060604230d020d05010e06090703030c060f060b070b01050a060813020d 70
    0xb160182c021311803040c0c0c1c4001720b4004044500024800d05c200c60076904181d010ba400c00b41071204500e061401518556003600c5212071130050a15162400410940714078a01403089070500c620600e91151962a240a40c0c080000d20041036008800e92340e1242080e00c010320701c1e60b043d00040301d41500d0b50901500d80c0c050328070840c1c000d14924041402c0b9094075402400400f16014000003641c181181c0440560845072017000d1b0300799600113245d200003004094015118100d04184842d00c8282d00c4007403803a10008640d8100b040500a96512080442c0e501c0e0500c2e1500000c4a100030841400c80c070f10411030b441810442c0d662040c1080403940181094409204a103842c50081000c030141314014460000041c0003030000088400c10780354150784641050303400c0d0740c5400252106880c403007009a203922002c07550f5584200a030040030300480300342c040365241c00140000044035401c8030f010800701c9001c1049001c005061340c0800c42e03064906440146182c02c103c40750540418240f04007181 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 210465404 1250 210464154 210464173
    0xc0c0602030306031b3f0601080f010509030406080c040b120402030c0f010f081012051b01020115030221060901020d0b0603040b1b07060f020d0c090b040b0d0e 70
    0x24000042d5120f040c058080b1100d0020790360803017940b68410910190310a00328039102000060002d200c031b00340080b081a075480600341403255851000260050b660075808080100314800342000042070703d009400081115060602d4007603124031650181d0418044e002022801000d1035904990041024140d43e90300c645181407420031010382910160300c44e124034002c051042c5040400c01c04031041c141c689200c0704800078003e40d00d1481c000c10190319540d4044000030401070954a182c0424031440281003120740e5400780c001e0000e01c5070034150441e89411149241c4a00d2040000250380e011074050181d00d00c195640180401d2120304040c50780108410301c090040e054000d018400fa910b513041c08401d0b00641400450f0108032005030019400d00041891141003000107089110040c6500d4034000640d104c1d8000d07204c407503a0498289a0000c0ea000d0202107a10401c0e840c01124a400a081403400b105c010050003503000c3e41510110006007010002e103140c1c800f5140d1002c003015140140c9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 210466654 1250 210465404 210465407
    0x206040e040308061509010318050703050312100b16080702040f0209031207150e0f1c08010503010b01090302040e0a0b090318060705060403180506030901150828030c0c06 75
    0x2002a1002c602241e00c04000c60018580010a104518a42c0351030b20b060001500046020700f0780d94540ea840d162200c104800855004c2c807695010f58043e80045640c4c1100008168009e10000c00743c1460009040d824422104402d0850310f8260f5005448004201541001d004520503080001d5201d840e140c40c941d241c1145401501081500328166101100e804006085500c42c1080042141486424841070f0320303c0c0d940300b84515448a0212180340c401a003106203008000071400030912030703001101203104c2c0d0090381980542070a40c000d01c0135510000018015405a000c007e124503243d000700d0401a01c104400410143c2000d5144005c3c2040e000054881e80402220241090003000b13004403410203408584140e684100148216915500d080380c2c100c458401d842003d07014032000150594561003c0c5000d80c01c14800011078002c0414594005049607000105540100d845468400ba40080307001010051540c4074401c0c8000d403030102c0d880350469000a000b615114004650075 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 210467904 1250 210466654 210466679
    0x40b0c06090106140d0f0c03050a05030d060f060c1203020c0a1a0106022b02030909040602030f0906070203041415040605030f1f050d02010c0507060e09011a090d030c020604 76
    0x11070290000300010360300c50b1000c980011000e56901c0c4c000e2032110920002450420740792171060300810002055980740d50f555414070380c5d01b0f030007555580d10105606449817040c5c4101401042168045400d0714600780c000f425038960500081c008251900d980021580250110750034008480300f600d41e02499440d00342410384044038840400041c0384000318030b541c00080c0002c88214000105c034180080c9a00003000011710150960860105000300d640381c2d1508088280614841e031409030700e920380108040752007440181541c00591005051061294020049400380c4120400901c40c1d08204004a4600c3d03030440c0004090880000e8002161640500514000c11005c007000c1300d15281c150712003400c00c01c0801c480d546400401c40070015460026410b00c24184181812a10000c150312054245806a849040443c0c0c0020b1081079070b1911040160140402a403480021240c85180d0314150083d10102030094104840e0078043c10f0040390400808e0b0743c02082295526200da600074400c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 210469154 1250 210467904 210467911
    0x11041515170109050112081e0304030c15052e0302120105091c02070501110a020405090d020106060c12030504020a033512040201030b040b040e060103050606120a02010e06040b0c06 79
    0xd41c41094008200a4841d0240a048560960101c1401c164584400c00e80e907019000104034405c0044480d00c0000f080b101461059011f40c5805143c000d880c20440c100e1808294141c006919040c00c003c400307104011601c03a200030002500c0440c42d084481c0700c0e0080c110f5040658001c0c51421680980b610540080b071044032002d058605101401603a082c1c03035550100c4d0800960010b103028006940318001c1001600321680464015800980104049610030740302c0350002d07040a5183e0b86213076024000c041c014030542c98065050303119074561045007541180d62400b01500d9030081015591034000e284051908480130300d403a000240c000880f2104014801c002e0048644004201d07004138070300b5500a840c01c0900f02589545039401180142503040c0c420382e003e561010301c02141e86403485030003050240e1100401d1507506506020785080002411548124000bd210300031800b80443c00301007035039081c200b22480c2020500020491700854001420b8040f000c08c40f40e80c0141c000403010b00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 210470404 1250 210469154 210469187
    0x50102030a061203090315061e08070f03030c0605090c0907051806031315020d0c021f0e1e150a1b0305090304060c0609050601181811041515 62
    0x3843d07910108a00200e40b03828014010840b0140104041150300d0700c8030582011000002501c203851340d074040001151035170803005011120006001d40322003084044068044410b014050034503540d0700802d041003810004003150b880710086076119000f0080084032880c020903c182d60b2401510003081e68200c0340121205a00f2170243c3e00032030404600b268019804a5040c41041101d0b4681100e00c685144d1b1500a19900b00710b4500b03040400c0c0328034090041164003078815034194030700d036024400c5071944034030b41c3e245444c9000031101800a0f110207801004800020703000c04280d08c1e241003000100ca8822000041c41c20000301113610f51005120518404c8111020201c00704120201c0300111208442c5500c1080b09020b1a40160030101c84148181030210f114100c0d0356850b4188035083e801a021038100390038007408030800e0700540a4129002d250b418442c446078179582e0703010450000301401250356600501c2e002c6202030302c0700050b0003c90701c192442d40000340000d000030108504540c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 210471654 1250 210470404 210470411
    0x1060e0901060909120806011e1d0a08030406080702070e040807020102010e0105101e080a0303050f07050901050405060306190e090f030403170a050c1903030b0f0a0e150409050102030a 81
    0x2043c0ea03640c80380203441508084409600140d4001c280c0d140d11001d410b444c180854100001c200d5000305001d060b81c16210750301c07548142a040d1194062005000703415200790101c50b81449004c0e400000d81c5c007280c1c118500b298090315261416801c0c4281030b0010009140c2c483e0402c4180154040140281c030b04c02c0e40208054040c1c11075080c201c1700c2c10303101c2403d61181d400003003149108804048440c012416281494079548904243ca8400341e003c040780401d4941d000c00c10321940e08419658404001e09041d132501c060304000034910f00c900d000d018451071012001c05c041d61a900c54003111b00381404219010b0a44605130a14038010465003a511817080700d0000d102081e000c4280c41c112580300c00c0f0844081d80d03e1035103038091f402040c90f15040190a0066101c1241d003000007030300e5841d00c900b4040102132141801030503510610f5085000728040103120f001511180d981d50110307080324010750099101c03408941000502d080740e0030740c03050511040a003440010350086009000d1544200b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 210472904 1250 210471654 210471659
    0xc031b04030602040e070e0a0504020a0207180606170103050304030b07090504020d0905060618060d02010e1e1f08060103050a0e0d020304051309020d080f070f051005010b0306030316020a0801060e090106 89
    0x101c1d203079030013112a079801000030b988c20000b50403c4d4024015040541c0141c403002512240b00d4559001180c0c2c00405541d100c4804009060300700383d80300307441c441030460403440c0e606680702c0c1343d5030b0720a0b8480208010382400c001030b1054401c81045020b018020815596942c03841e900c180682a000300c20f6425000710000b1501c03501c4d042110313081d0086403d6a8501507580d6508000005000030410381c14070450030700ca21202d944006d02c00c03038603c205444181e0040814003c0c044c10010404e65508c0b40c00c81d52045103007850300f0458203640000d00741b03070200382555908001c01c040d1200380b004101c984100f9209000940d000700280040e2101a23501c1034201020100b02c0c003e4502d03c038400307504100c42d01c3e19000411440e900401c140c0384c40c0e0507114a032992654484005900294044e40c23141c0007450254622821402140d00504141c02075600f07500300080041d07103a224141c601440ca0128100740821034489440d681c0050081070000c00c5203942d034080b0000d004000703c4600c2040d51920201 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 210474154 1250 210472904 210472907
    0x311070302061b0a09180f0e030a02070b09012a02192907120c1a01080607030504021513031a0118140f09010216030e0a0603060b030c031b04030602040e07 68
    0x1a84d8070340c0e034240e4829114500c0d004401d403442c1101c98a0410054850340000410444d070b015400c101d011890056550381a04d0700c0003410208940c000300030341c4004000020b030681e480031625070b42401d480302d1505054082080d06040c459642e0009400098004080c1b10741040150180300b15042d0100090403004c0c1c880712035003058941a08428000420700c040307400705681c40c2d0582000070650030700000b00c1c845504c3d200010718008540180056051005204501042c0134a07500400c19045c14071860500da03000498180c4c0a0f43c1890001d00c002c1041000c018000240342c00441c0c020302090362102004050110f050801d015180c40d4815005410003680d409110340a9016a090000d4556403608181582d1102019040c041d1640d001c0c043c801c404501c940590b0210340c82501d507280a081e4500900c051109a507201c0800c1c0351425500304a41e410080c100e962000455012596a130388103504490481d1310b0000300110b00c5000f00d804410005194001c00a807148100e9298255032072910 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 210475404 1250 210474154 210474157
    0x1802041a0906160b0a0e07080615120708010f060e0603060414030d1506080f040506191e0b12030c10020f070506090f100b1012022b05070504050d120311070302061b 72
    0x34151231940403400141840c00302d03041081d802c0000800780004a03940c20000f82ca05a4203030059a0540d644016100705081c540c891180200085c0c0c400030350520384240040c0d2620302c020806090380f490f501203030403803503c2841224007802000204005c01419490b8205d4003d229004800200b041c100c04106090105107045210b641e1020043c4461307a81c000e0600c4001204022004066417a05d12a84165815810480c1d261900c0a000242e84c0100020070003502401c00104215400c00c010032148520007192940328a00c5a00000da40c035401d4000354040b078030a00c2c1020f030450144009000780b448010a0840304203912804861981020312180c000b2550390a2a542c1e108140c840400704583c01801c01e502003950302c090050802c3307001c031052402d50304880500b0120240340e00100d40300300e2103440746507004219807a150f41402d040c10007090740c802c0c0c19030000c0e00c00300c425640094800c2c400e40112852550b041000c6448030780c20315029580da801502d4020b00701400405403144018042c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 210476654 1250 210475404 210475409
    0x4091b080903031513020301090e060709050a0e100302030102030705041707060c0f030909020f07150c020c221404060b010f080606070303021b03041802041a0906160b0a0e07 76
    0x20b0b40c596100d045400d5000740080050b0740d081410601c501d10340752401e10180d4000d0450a4011035091010340c1c81500708400104034009024088005219944940300c20400f9107880440005c40b90b1243c0682c0304500400382c0c0000c0d810740c0000200a0040ea101d009482100c0410b0800c10450000e1101d1b1903d944150050400003807241258401250907241102d0006029040c9040c5040d100c6006c54140d900002c00c40008020001c1c0450420840c443c403a108840003400800000521810080d142c1b0a130714003591080041c5070903440c03103241251540340078102480c0d0400540c00703000400908800e040303c0c02c1e54031030314000850089500407000c500701c0681c140d5552035541c0d01c1c10304020858000145c280c00300340d801e1100701003001c5a034042c2c0b900310a102000b151203514003070031507104500b414070302c4201074014403003000440880d03145402e0307181c0c26000300f030b490302202c1000c507065000d084030303580c2112f007240103120502c2a0115228000c00c44204140301d8240d04250391581c03242c052 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 210477904 1250 210476654 210476671
    0x3090b070503060315041514010f0b0715051e0403120e19080a030f1508010c11030f090d0204051305060717060f0a0308070b090106090614220204091b08 67
    0x241303d60818012204045940710f4403d61140b01a026a040d501c011950001c0323242004003c030800501c00a4251000d01005040305244503140c08000c1c4d403a50310502200c51201b00d03242c5c0baa40801d003100181c1300c01441d960038850707101e011880c083c01c0c0184141c07000c89080406070310301513008000c00001318400c0340d507507410801c000b286481c03940c411440d03034001142141010355884c41c0498203905400381c200320080c6003000c0001903003005003032421220390404202c14030010b1040a5644400402610701d14100d441b0503036180c0d02004c0110f04031200484000b5401840c0a0800600d80ac2c9070900c1c0103da130182e02221031560311400c0698181c8451008100c2401d4035070000b801d135282014004100002c05007030141c401c0c0c0c3e070356586035260b0000300049811820b22000c0081160342441032070010326445009200751031a103480301c5280e40e440407115009109410343e00000210900c0303100007690041030111b541d03d546210f600020403246840001e085072010f078030086a845590101e0041c0100c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 210479154 1250 210477904 210477913
    0x120207020d022101060308070204050606030402011b0201090314030c120313020909030c030c0a0b100e0703050901141603050603070e0f070314041a0601021c03020f09040c03090b0705030603 83
    0x9540070009a4907020030452620b001d03060b1541d003c0602030050f84000c0d840341c4040c5032120254810002501c130001c060a004000038010000540c0c0d002c006201d008a0002601c0924003107030004880706407540c0c0015004450040c0540080e0300e000009013180868a0b0a403006010044080c40340c0744000e85100c0350340b510f680500300c0940740c0100130035041110b076011613141c03a40f070039081d03801c540050301c4d4401c480c0c00c04102c1c00c0c1482420101654412040800b0202c5642450910b208010000d420705041681e0b4900084d01c0c44800d600c10501c0724003954295103903113040b59450003032140728028040040d040001040ca907040000358841624658100e10401d0313641c0480310a86104014051000c05407503800081103520306125107801f50340a10764101e50b01fa840b00f015004420003038000c07411980481da070000d440d41040c03824003028125141c05a40c451105243c1c040c54003414074265480307840c00c54018078140d0550312682301203114a150740aa80c0d5102d2007034415020844146806800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 210480404 1250 210479154 210479179
    0x80417060619050f03030c070e190605030706050a12090b0105040606090b31030b060406080609150901090c0e09070602161512021201050112021317030c0d020303010612020702 77
    0x4004c0d69800148a02030b040742d040a600f141114640101a400440341c6807803641032025501c5162650445500b11280a0284521f400c002c84e03035920052181504001c1c0108006a05611940300b0030340d0008009414401d80d066402e049402c0c080a102c1c55100d1445d020001581600680c1d400341128907100203503090441c1e207681d0822a07000800b8607107030088101038040340550f102e2100c0d07010b140554102c0d489490315200b1300040342c1c1c50303800440845e446a400c215003032000003880a00e140d1402c849182d0360310703060310072405880005002862400c01800c0803441c1384682048a21448083d0100c81e11a5900c8000781d0300c0702c0e000c000e0303100c00d1806030009218038a585250000100654500080c2c120440034443d0101e030000400f00325072096050040000d980e000418070003281d460b410851802580c03107602c0740005102c0c0302d4090704c0c5035007243c000700c40701c0c080c0182d42240354204203070342408118810094890380709001d0503002c90001030072408440401c1c4240d402d0541d001e03214103106003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 210481654 1250 210480404 210480409
    0xb010e0a0b070303022503030f05060f040902040605060f13050f10080c160305090a0e010605090904080409090c170613060b12010e0f060f0411091308041706061905 72
    0x81c031200c0c00f5402d01d5020000c5404842d10b2840d09290040f001d5181d60300c04010b841c0c01070548481c02c014a403030700c2c10401403051550b2100e4180b0601101144c00003800c0c01c20b407011801620740d642c401e9500000108203007480320b031104020421800d000c90005040c58807030b4100414030800d039004035001590840d00f00d1045020fa8107140c0c000051a502034140300254800c448003415502d42140010780106110245041c0044ea580142805903e0103005604140c0000c1c02400b0f11140c46104820410201e424008100120760180c0341140c001c3c080042c40c1e003001c280c1a041c07403161225802100c203105465444c00f20303299028010f035009800f558012074881001078620004070700d038025600d19001583d40e109104003056282444003401d09000201c03034560510b03000400c0300c00c0c407054000c1000005030100d03018441c008011940b405494942c80743d4140d00303131403010700101220b100007004540e8910032428100e141441c40100c882d260384020038002200000365070302061109080080c1320b540f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 210482904 1250 210481654 210481657
    0x31b011412011805160503070e0415091b0c0201020d0f031d0d0207050a03020d02010f0c060f0209150c210d02070c060305100f03031202120702100b010e0a0b 69
    0x382098000c941c10070151000c1444444020790001c10701564040140c002031601c0e00030319512500b0300300c200301c00c6086620081c00e5880020415420050002c0001d80d8955031644604034220001501300c41680e110803a0300010400c41c000da850400e0342c041030350720962180103020310044c1c0c103078041d1120820021059800f40040c14500043c161628040303c0c4c40c04640c501c52008034041e9000b040e45000b140c2004c3d0034102e0b15004640a142c120310f085c005602e80d015401001c036421b01c6c181c0d200c02e5402904a0321186c86d003030002d164500b0040103492081cdc070360300a0301654408031020b0700c10594941814040740301c0e00c20f2820507508070603401004140281111056460602c500c0c520b0f048448a070841264451481102d602c03000c4001030111990602c142540200580200c40a072410b2140c410124a050f01c402000c00080401b40c109007401901a1000d80f02019030400481c1045d00010b03449000440891810501e0411640d04961050325909051000981480b01050419052a030603 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 210484154 1250 210482904 210482927
    0xf060a0f030b0d0b0412030f0e0c21060c07020316450509010b0d0f0b06030c0d0303020306030138030f0319140304030e06130512030405040605031b01 66
    0xd0b02600300394012580d0f01c802c940c4514880c651541c540c001c100d40c00b9045443e560440d01400342717070079541c01200c140054100b0b0030040485811044204240b42034070384145004040c21180510400e001c48038001e0005040708901c00c505580305445001c00d51b0098400f94402c20300c10780c00d541861101d402c042e140e140031185042c03607156036900080404100304000a010b01a259680b030042101e058000e108806440e2400c03603082040b4030a940b9001d61940751040c000e030140c41100003190340c8d80d4082103102291000a815000c03501110706000d40203400441300c0c3c50207942030008200c08200c5000e070140c045404614180780b14000b15109141c82c1405107040c039058810105000e040d01c03010000340c61840c00c040c81c00c01c501c1c8039101e8010130205c10682e0241c1000300c10700a100c006078001e14041581982034588a803030f0200c4e08a00d45842c0724503801160815031707848618085520100c018810754400762024000503a0320720506a413103e94502c080c042c11a80c3c0d00038000343d84182d805084 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 210485404 1250 210484154 210484159
    0xa060c0302070503030a0903021806210106030f120f0c0309180b090f04170304051c1806080a0b06040b030105150c031204060c0c0b070f27050f060a0f030b 68
    0x18003d0325807011a2940d44180f0040c004030b00000410811480c0c038210b403003c4a0b074a20a1980503080070008154a0700d005d4900705c886030032813032514001c92400d51180d0019504107107000084129030401802d52520075000f200018001c1d010040110300941c400410154143e544080a82c9030000076501003004400217218039444240c02d068680c0c48002c81c1d80142c00e910b40340f04090909140c640c2c2c90100c0c951500b05004814020013002c90004180c884145025402c1c4180d040d0080101b2601c50349220008510a5100c1d50045211340d030040c90903101c3d20052004015150f42070042141600943c8140c9018190404c0140402c0c204030101403007005803414400c1c05c281e14101e0050640c1c0040220300861101d0741c2c100400d10400b4007074405404821708040d040c01815031102c640d00c2c03c000700b065061104403c1200704403882900707400c0b0f2140c01903000c03034800c183c0c03c001940e12848922416200342d50b01d0341401c059240280450384ca860b040d8442e9419a99070306801c1c1c000e407074814040f65 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 210486654 1250 210485404 210485413
    0x80103060213050307030510200418020c060915060f060d02090d0507030516240c02030c0a0f031a0717090c1003020306010908061303080c160804031202010203060a060c0302 76
    0x100351324104a0400039600c10406403002c00f9001c803e00c0c0498014548180c410320911944002c85400b00c011901a41e41c01146418121108200d20f400b91141034502010391141c0410806440340c08104a845150710b154500400c0e180d8904000070106404030855010004000350034620301c4d00d600801c41110090200304108002c3d0b07d5542c1881c480d40d00c00c2c0d8568204000ca03c03405516001d03550003401500c0030301110075051031b400980000846500300140300514010506554080060207003840f4005e12030704c01107480702c94202c031624081c0b004560140030700040b14012101101c41c030b440792249990308a0a100c980d00c4508650101408210080c02920039403003003078850035a80298400030381c501503030720305011000410718603181c0d0103c03441c1c0c0c014006000c0d088003492426080c051b01803610b0303602c545500b911100b0ba0312581c000d2400071007054054504005800000c1c200302c9025a41200030465094400d034242d120451341a58405400803050029170701403001d4450a80c020310448 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 210487904 1250 210486654 210486659
    0x1090c021203040c03140a12080c0708030402030a06020f0d0b100c0b0709030503030106080105190b0a03090218100302090a02070b270f0106081e0c0d1b06080a1407080103060213 78
    0x6030151200300c032603086c15048001c2c03010501c95040c0c89a5103032559071803c00380d203242401004525010b003807001042c400000001c075082d95000c1081c10307005508200c08555441e101c40b51401ca03503200c1001e034230401e800d103822a5a507141082080d1000c5004d03440d81401c0c2c05036560754811103c8005c014806104111034003001040c0c1c2000a140070b00525117070710b000c9504060400030142801d0303c0480e0310440301c680034400b841c407800c152548410309040100350b80e1034510002d8808444150301c42140001072040081801c078076521034007102e00035503012181c0c0d100c0700d014906038030039060003400f00b000d05e201140300e2890b86c074850740015008050403620401a401940c1c10800c1000c0f1184841e07440700001d00a0034018440e0078910900c05408007454460008843e49985002200038071642c8801c0150342030080803289001411000190454519143c00c8042d1040406032000460985003000b5400100703003000c9500e0246045844882a50386540d0f01d2001960003494035607048010782400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 210489154 1250 210487904 210487913
    0x30c030709090e0106050109080609070e0a0b060c010b09061e06090103090b040f03110106081002130f0f0614120a0504050c150d200403080c0703080703050702040501090c021203040c03 81
    0x10020742075443e00c000b003000352510380010140c1e180d17904081c400360815424414000c0380004d2500c222094101c0c0b08030320340d4416407407000a00c0c5100c8d000f41c104c00d001442e80b0030150117500560350640102c50051181e1101c1c030600c0800c400007030b011004080d00c1d100c170115038a0b042000d40301c0380805160206400320140d03200010140156802c43c0d101004001e19401c06401007604800040c980000f0800c1900e0304101035621404100c92203e0380b50b0010382c05c040101c41500442c003078002c3c1003d40b61840c2d964a003000b0300c80028840c100014080c411841c4804006e00e0031140d1003c051030b80d28502e5150003010300e0050070050b000f00c9045c0f043c480f1106454075400703803c40724011500d03c899200d215040544007038400025240001e581005440c0c0c040c01058002d079810f480d08440d405845010001d101486c0c40d2640d080500340800200b522400c066110008280f0703184217481c14801e50342e840c00b040041d9602c020114015801201800c20101c0301e00001d554071500070344a411903555070303464 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 210490404 1250 210489154 210489161
    0xe0c18280218011b0b040816050f0d0e2809060b0c060907031208070201020c1506011701140d0804030b0a1b020601080c0d08091f090e010b030c03070909 67
    0x50048190086016040d16658201c4000c20790b800303003003440028044412900d420102c51000420b0180e200d408036061010300400c2e00c0400182d10030200b4040e156051455880070b49044041052003a8860324403640d204d240c0b800807020015040c40341404881156a5554200c20b060900362526000f00181140881c02058003c1030103102ca280c1e0703460900f0702642046002400d410484c2c0c0120002c100050188044160a005501c2c01015a480d49031701207029224180c8030003035511908038000e140b00c0c0099a4a8061760302600e0301800421170009a0b0485902403080611500300c0000000345424481d006020852165601a2138543c40369140d25000074155031283d58165160342e440a481400d0414000042483c00107090035032402080b00d42e600c42c0c0aa0f5240100060a807010800113460f00380d17141000c1c010700c022104881100c90403900c41075500d0390400034911540c005040c00c9401103240c16a41a0380d042451a61402c80782010b43e40050306800070841440c200080e824224807 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 210491654 1250 210490404 210490471
    0x180e07090204180905070302010309031107061e0201050f22020d0501050a0605060f0403020103020d141f1a0301050d0201051e03010905160c02040c090b0c100e0c18 72
    0x1000142c5480c1041e00014140b4441a100b80e0380d40e10b0201648081040001d801044950902c0c1c00b040074003980c50100d49030030513800003842c10301c07640c40c01140c01c1e600010b28a03031702044141c000040355010101242612419203812040020031004034803025400105800351031244956010a00d40700d601094018103107640c151816590b038000c0c09841c0e1514000c0c10001c00c804c480840c00c1040c00403660005215510000b4140340d40010400542d042c50307084001121040000030500d40307400403c207191a0701c58000300320002e55614011400d00c070442122800d000c0319000450450782002d0900c40e41d05120303001079040c0441404452082480254034003041c548411003140c07a5490103550005450000e0710b50960140082da0902c90300b41d009010707101540c5c0444000c25040d15943c0166031a503426002043d00d41000941658200c00c001681d101c07a1030000002c1012000c121852600c8454240d18113601c801c50078004510004202501c1d40c00c80c0001c58020203134500342d800c9051300c3d41c8a1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 210492904 1250 210491654 210491669
    0x210140c010f051815071b050c03060f09190c08190512030c0319060f0b0a0e0f010c03050c010624020d0f21020712050c1213180e07 58
    0x300442e811905080c01015000760f05146040a09488580083d494403002010502640544000500030622600406800544144105900b0110303402d18540350140464054003070310a0502140b504211164100e01c211078000c0944400e15030302204c0d80c480030182c03005a83e90545c2a90204900c04140b00b8040b2460024507408a00d00f154603115080c404452480802c0040070b104000460200000301c0e64001e4000c0000c08401040211920081c9080d03004802c803130b16842e5010a40c00107582c0245942c42aa440e0403120300c4088040000680f01c1d00c240c140000d11400a05000034001c002510045683c4000810700517122900403c1440c42d401842c0d19019402d542c0706005601401305440704440c42c80c007070000800441c4d001e0104140003e0440c403241e4171a05210306099668150340001d64400c0e000101d0780e21000d4001c03d035802640d032002c6603021b10b030f10680740569124110b4a407001c0d0750340b103209031510300100003000940b203450012881d40c841ca00d079100c0150030300010f030260049 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 210494154 1250 210492904 210492911
    0x1005060f0c060f1b0a08010b160f052802240d090804030c06020d02071503020c03160209060607050a0201030f090503030a0609050a09031e02031e04060f1b0210140c01 73
    0x107001035003804d031509528035400d0a010041d07018002e0b440800700741551a246041c9598052010b070800f4405192003014240f4000c8510340d02c100500459035114071080d808601d507101e01007803800c003498403031558000e600c40420b1220000c0340f601401030707120b900b84861046040541c07105a11048da020309801726035903c000076007070080220040c0004041c280c07520041c844034000c0440130355181128020442140302604180e1030309486501191160724076a4190b80d00e422041d03500f10075408040300c04030310a90680c400a01365041900550ba20350345c10100420790104035400640040413482d42280d2040d48591012003c603504100a5000d8240d9a00011f0200d240001c91400c80754080c0181010394141601e480110358800c4041a507201c02c000c0425200f603030003000b03130304d54405d10a012440d40d1820b00c15044c5c202141c000b80c4200e4000e51a01401c1c03584405085883e100d002002140440c00c83d80700b0b0016051040c004402003c42d800c0c0f0340107160140e081d41c50719410000d0412142d070345 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 210495404 1250 210494154 210494161
    0x30a12090303290102060a0522020a09020c07050f030105040b0a0207150c020d080a1107061a09011707090b06070b0901060b0c070501020c1005030c18040603060207050c01081005060f0c060f 83
    0x28100b04647c1d000103031001c02c01c940d080003840284240340310703041c1d0300102d1504044c850641d690104000020085031030111354600e00074030310580740d40b0f05118191042284000301e0442e0300f03041c05003c0c80355900100d6511a0340d58400800001d401c4075105692601e0b1b00503c0498098051050030350500780d6400800c050424410006c0c17098000800d640071903400d0020032050000c0030303015542a59805880070032881200000007290f003920f4a5a2030340b12035990300008149040e07203c8e1245c104032100c25100306980398091201a03c0d4008500c50b00504100201c0010031806034081d03410585020003c21050f640c0d034091040380c0c0211034028203c3c1c00c1402d08109541c0c040020740002e55003a036000c06181403110001d040c82c08014948c6001100000d40c20051001c00c4040a03c4508014030400c0101c2e01ca040442c0250070480017141c507031146612030003c542c004c81c40244100d52004106c03448074100024031800307401c148a00700b05100140300307d000100c02881214460000000310421614 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 210496654 1250 210495404 210495407
    0x30f051017070608131110050c1e100209031501260601051302070f08070c06171003150f060e090c0d0305040504330512030a120903032901 61
    0x702a41a454642d0007102c00300b1260350800c44480d032015424030a00c3c98000300341040c0320504040350781c055118480b81d01d00e000c210382040150000784071110881e0b505000c0100300c00e041c04981003001c081940070410710000344c22550010f090800300601a144003c1800300e00c0c90820b1800c0c0c1044400a42e800c2805104805080c00c4020f0031010800034016941b400d8080b41160541080c24280c017500002d400d018440d0201c1d0f00c0003c1c9520482240e070350511402c0203140568103000b0400003981c0b40c1c2034180e40300c11154480d03000f14030303609600c0001491a0b4400701c3c0c0b150100d05d8995810b880c0c8a02c0d03141841284030719802003000080d409103a180012026062008481e00342d4070130b0070303000c0080c40440d90240964041e50800c0e02e00142c288110700c1d01e880e98080c07001c40b6030b8050301c421a503800c3c4202c0f545040c2044600503038000e100d000448441580300e00409807100c0000d03405031426a8a066542c00c8800454024100000d81103800711600b9607072200d90b2141c0034008404000500c555 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 210497904 1250 210496654 210496679
    0x30605090a021c030806041116061e0b0609012307060f05010509040b01030b040f02040e0a020f01090b0a03240618061407020f0102010b121f050702030415030f0510 72
    0x101c480c8004800c020f65640600801000742586d40a40c1c1e0701e2040c4850206441d0403100594400d5207002e44400b22480c080001c0c143e14a80e000b60002002c02401580e1020f0042d840d183c4402094170f406d004110b001113440302c0251034240c80258225070005e0b80e40c0f4010000300b404a02600d804645001e000785810f0039500c040e40800d004607031000411020411107010981035940c07101d5001800d131250705144000c24a043c0010350701c030385003d006030341d0305a0001e1000c01a6100f51000c1d0200300f01d010041d11000b000c0d12a01304c5120041000709c030b0340b0303100e40c0c48080205142800de2007021808240d2450411054006001080d042e4034041d030350141c0450900700600003498452041103000107414158010700100030301401c2d00301c03041d90a5a0003034120f407200503c046d040300c01140769035130855a1156182c680c1800880b00320605c003032907602d6025861080e0503507002146403038a4104945003000e10f07080071508043d41d501c02004a0703030560103014081c03402e080703030000540e09051103050403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 210499154 1250 210497904 210497929
    0x51501080108060601020a0311030c0d120b030a0b130201110f07081207050309100c021207060f0302090901061103120c0909010902120402060901111203070e120a110406030605090a02 80
    0x99030701c80404c012984c0e81c00180c2001459041c901151214030313562019145d806520030758a41401003410081d5810b030301c0681c00d010400c20450600410f40321130309140e203510800c0005800d00c2c01c46000a0340719015030341c621020340d1040c50447e03001840f40300d0440c00c01c200c00d00744813903a40100d601008045010851300034a0303100e4207010f601c0c050540d070b1644d50342d2003a010024007501c00da030080c140c0a070054881078074268026190220070506840101c1d1a030401c2d0040c0f10104143e205000342c0c45200b4406d4400307c0001406c101056400c2a4040c0c0d1940603580c81566184401c201c01c01c0c0314010b401c1000e02030381240c00e407207850300c043c48200141c0301030503003209410504c14020580d990f015044044d030001e405480a0b40c0c0c99260000403502150300d459903550320701c69070b03000f40b10841c007480045205001c241e590304247d100403002c200702d0b4106030300c00140b5584034a9489001c00c900c010b000c00f8481000b880040c1c03055580da50f05094039000c540a80017500101e150744254180040703032112 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 210500404 1250 210499154 210499169
    0x102030103080d0501061d13020d051602010c090b16051c020a2607030f11010c110601140307030b250f0908030a021905070b041503060801020304031b03020705040515010801 76
    0x41e03215030340070141c00e070103c0782006482400c5144100100c0800c0c2d40c1125903d490850051015140501d4100c60030000e01c0414001503280003f0841104d215482c0742c000e403009900130f10300e080442d081c1d4030981c01103841c0c141d8081c0103100c41618100712210715404981910b4000c1c048040131030800c04a40c0b59988140518946107114841030040240112880d260341401c0a800040101c40129130050282c0f621003859844d00000b4032080d84c20400c0040300d810804103d58040c2e884150115450985200854150380208000d100051703202c1d01040d4071121055010b6403507510134100d0700112508110391404580c0c00581800d641e903008891170b0152020b580114500440d55400a55410181000c04d1201054105120030000d081c4400cc0040250441d03003a211905c030709100710b8880320500b8410100b80742443c0000d01c04010700990b40b00d10303010b4841d00384e40c2c0320720350708068240d56141c821404c6001c0c1c048046520758462043c58044c50320450354441c4610140b00242c034501c81a0890f02c0d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 210501654 1250 210500404 210500417
    0x10311010306060e0603040309080601080708070b0403170c0a0b0a0204091404020303090d030e0409060b0111161a0714011b020c1f0c080a0c030314160305180102030103080d050106 79
    0x140f2500a0905030030b44a0544405590b55194181103a03203d20a400440325401441e000242d910000220001500c801106540482d9694050103195108902c00105105401c0c080c0d501000414000b0b01454001e41059942da0180c2356a400e0700c2d05402c4858030b000c0c590100341480701d407080d4440e48400e4040b9505039a410b04103a00025942d0280c40001403040d0860020f0504240c46604000840c40c0301038020300c0040454a07080018042c54000c00f400111400940402444002801100c05c3d0b04280c4c1041c02174180060601d41041d080c410b505141810031180002410060941e0300395145100005041c3c02d124064141100a8820180031944030380d558510076590002110020180c601144006038075202d000c0e540c4010341d5a0290085e5404620710898540280030799441c1482a602080702c14200c00c4003c46038074082c0e035012140c0355a03e40c44405d882c041da0100c0e0f084403401501c50f8420b68001030b020f00303a9009030011129034501041c00b801c451298041c85024000ca0308248 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 210502904 1250 210501654 210501659
    0x12050105030604170306060c0f0105010602011503150c1110090c09060e0109020307020a12080403120218010c0c050a08010915090b150d0606140907030605010507150e03030f010311010306 82
    0x800740884c10315290055400c008003192041e543d05c0c04840f515003c480588010900d0003a14900a26091150344050f50a00740b0204018008035000c4017035941c4411580f8400340c0d410b11b081c0082c07003042404010701012101c420000c03601000308505030800b100b0302051581035841c0c50b00b0b146260b5031040da01d9034100711042c054000724500150540d030a2000068990391010710484c64608001d80107485c0703002480c2031a950076071010903e44124001e460314405603034881644001c911078903a80000d40742054520341410742c440c0700c402490038000c02e0f00b42c85164948000400c184460307408040140c0d91015500104240c04519202500740100d08024040c1c071511100404c0c030005008000104005034040515550303040a02da0060b0010b204216140c2c41d00b0f900d104180148440038400d52940000030360f558843c0c0110700c103440c01a0b445605000701036854032401090382d1503c020842e10742001110288040004c0d40c4104c03160100c003030155240d41005000d5041d1040401d04141c14441c05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 210504154 1250 210502904 210502913
    0x31c0b0d02040b24041a0906030703230c0a02210403020925030507031401050f100212160c0602060c0a0806120607110106140a060302070510050712050105030604 71
    0x10115015540894801d0f92080000c02000c20301c90f42030640444070340386050031803401010f0400e1394824046076640b0300030305019582d28090f0040c01a03200e40104002080b941c482d40140b82c41494010308510041b03500204000300788400c8a44141c1003c001c03400190075030b030401c28040458940185c0c1d940e01e010304040d04181d80310f94000a4028000500071404004605900101c0d0819080828a0340e90010000801406007901d4007400281458171502a0b0070001c0c0c032150403a080284040340300b050f514103102c12018100c0546042d80210004d0005500c800d0000f880d01c01480ca44920500d180380c902500040066006007085601c51800c100000b440c0504841d10001182807041082e5182070008007410f02101000030350f40520401d024000350064000302c10709070942d009010442c1c4031000007003141034962035694855583c0c6810040280207a004002181c01502a034840066030552003050350416103004000400b88800d00201c00703011700c20140036202c220017510072800c1540b507 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 210505404 1250 210504154 210504169
    0xe190305090f1801090b030703060c020309012006160c0f05011506050403030f05090a1203080a1a0307050603090106030203070602060412030b09340309140607050d020706060b0c031c0b 81
    0xca80750300b40e4a41d08446c081c0d5040028a0065612200521001c41d6116009403a034014031083c03404203240445c42c403541e03203100c840030500d880700d040103049940d00c1e10100320724a404400081c4c2805462034146000c01c0520402c03403180307801100041034500d403d1400c010b0000c810b51204040100278401440000c0c0e04c080402070301c450380c2c90b14580f90060040060020040c3c0d600100d00020001500800c00d40c02020f100e02c643c07202882048004103132803007580b182e400d0b920f016905802c008020b010a107803080156030012004000012a580c696001c41e103040b03800d800c80070240c3d0009081008000020340132101020a42c40c080c003590000002181700900050031540190780386d1401c4000d00d500300800006060003174444400e070480d13840e201070001c01008800352421035494103210615100014094001d02d8503030348080c980402404c10340d00a41081d40c044131142d441e110002280114140609940d2038110007556407410b1614036007a501540080d9410010b05106000b1f410342d55a14 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 210506654 1250 210505404 210505409
    0xb19020306060a0c050c091905010602030901022d0a1a0603030909040b0a0e01020f1c0908071410020403150b0d030504060f1707030615020106050a03060e190305090f1801 75
    0x14040000030240c1703400350801c040c0101858100200c2c0082100104031608500ea03400350b000802c0040d070362a508102d1702c03440341c04109130144c1c1c015038070101c012000503c03203a00003400152015503840c9400c0c80908200300031005803403036168040504031040ba11b83c0010340103c401c500a502c1c2c10080700202d0703140540240050036010501002802c1c080f00c0e504406401001c0038021552902240d040b510503800c641d2420810110180200b80b01d125a846424011034024410710300b8120190396103a006180203084c004c0d03d009054480482d03601030700141015610800c4951074040d10b00e0740100454800007040c40c448c0c1e01002ca06000301c0e802c90210b40075039213546040582c684c0b03141d4041e40c0d00859045074401f580300794000c01001950581c4003200f5500c003085081c1214002001c102d090311030b1401441e600c80c2c40400c042002945541c00324078281203a5040d10034500b5403181400e1451402a401d501207000020b01600c0c918151003401c003158411101040384070b0001c1d008403002c10050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 210507904 1250 210506654 210506657
    0x70b070c050109050d020d090f0305120c0f0304030c090b100801050f04140c0c010c1403070c03091d010e0a02120c090a0f180506060901171f030b19020306060a 70
    0x1100d0110a00c142900300d88032043d0414100d0702d6008003400c00075560b007055030040c0001090014081000030313800400345c0072030741c110000b080581c1c50f03030364450025070010b00301480e140300e00405103914910500c00b50001718041d82d80400400d02d060f0300302058540010400c1c0c0b090188c0c2c0803811096030440b441034192202524804ca07450581c4011a000701104440749400c090104104480b02c0302d10b900400048000100030302510301c1a6034292048103031801081500102800000ca84500c5038580100e100d01074541115615900c03402e1401400200105540d03204d0f4440062011000d40340440e50000c8114108502d030a070010402c242071710300034241c02c1c0d0245000500707a4940d5100d48840020341100300600420301d9440000810316080000402401410507000540d5440c00b83c082c2c0e60300c8070040e12154040001c050500d01031080003030a4030030f0084d6401400d4038100700039076000080e41c031074100c1000e142803905286030465030015000a4881c010001c024041d281c2409480000304075 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 210509154 1250 210507904 210507917
    0x20a0f091d0d030519090503030402030c03030a021b06070c06030209030f0c0109140f04020c1b1804030507051c03020a2309060a090503030307030c110d02031801200706090605070b07 80
    0x1510703803099175075124000c4090384505211030401030207000702c01103020b0343c401c90403074070700081c40410b15131031380504144840540c101c0f014000d041c2081c5a0b4802c2d403100000d00711854040165294000c0c0c020580044002070380c04189101e03070b030600300080c4107450301700307802407100c41080e4000902d0141e0501442d285101c040b00d040a4a40700c0c020580e050610041c0255190380c0d6440025650706050380b55420071b2a100c242e032644600b04042e05111840d01c0c4009850360b9600c0352001d403060b81c884001194030f40b09103078101900c044a551400107040c00c4da030380540e0b00d68038500001e154041980000501e42103034009003002c40c02c0c40040f00c03003414096520326203410360150290340f4180030740e0203150940800030820802c241e040c1d220082e251030701d488012800648640c1d141e91000001e9013140964010061030a03812900000c0300340c0da081c1490f002c480311480744080c9055200c001c116440d1940100020300540340c00c496408050000341c60f1150504079181c0f504c074841e8a000d003100c42030106 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 210510404 1250 210509154 210509161
    0x31b081e010617061e070903020409051501030305030709091503030e06040906090207060608030a0c03080a0b0604030528030c0f0326010e06040e0303060f010c020a0f091d0d0305 78
    0x2000c2d0048030040800d480421403864040c1a010b880f0242161031050400f2521190043d05150440da5402410746540e900100703400c65003800002c0121318416542ea12501c1d14504010411034003143c080d502ca6550349407a03040203507001d00024410b40101d0300c11400e040350920500f4020300309100301da800d407900795010500c2030040358a0b032180d46c02111070340e42000004241400d0a800410406101c0c0104218003a0b03501ca403180c0340d001d151400780004038115070440c0070910503e10f6540225546d44002070710303500c0b5000030781c81d43d200b0390080710035400900840723400801010301c0301c5a0b0081b41802e613282c1500e503070f8010080700c28000010712652100d84903000340f41c0f180900c100308421a041945140080c0030b151401a00b0034811036a40d40846000101da6040600070390b1b100a81900013582582c944004019141d41ca04281c1410805082c100101694640e4103500c018102c0b0f004401c0c103642481811020342c0c00c007880518250303190b002200c1314418001078540741046145400100c070748 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 210511654 1250 210510404 210510463
    0xc0903110d06060b0c0c100903023d11010c0c03020d0513050616060f02090f06070822090b010804031e0c0203031308161a030714040906031b08 63
    0x81130781082102c0304000c540201d044c1d000003250000b44c0000c503241041d01020700001c49060700540002074110041c402d070345048041103e281901030059010043c40c01d0403400c5002001600060320000050002301214a02038080c4540e182503440751070661040f90f22620044d5654402e80b26400800400148104800904440020140c1001007c2c660303241c0e0f02030500018298640004d1b60154604900106040c1451084480c511405000f6541e01002c2404004cc00e0b00960016100c6000c01c202c0351955003001100043c0118400f0500903141d418000350a04841e00c0e01c0322035040c13190403001d21001ca80c000780100e14444d01c10a11200440d00c9034021150707140b08400c000d40520011410030320001c888502070381540c41034811918400c0c019400580051464410311410404c8219516503140175230000f180e0000b5203043c0952808400301011046900c980e00c100e0140d40c0e125010f008209183c07a120150520055000c0041b0b420b040809445940480407c2012148003207092601d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 210512904 1250 210511654 210511661
    0x240f020312010608010503010c08010f090b0f18040b0a02040b0306060a170702010203070f0819050603030f0301030b190506130c2106091b020604020607031e120c0903110d06 76
    0x1e10104000c6005940d445401924402082c090b440c071950030003509030b004500c5140901d049815958840790640e103466950802410f804c003603190480b070702d44840c002686a403110454000c0000700c4402e010300c2e060500420038103001e0440f01840b40100000c12050f20080c041d6600f00c81d007100c0040c0e9400608109458001c81c4026468102c3d0400c801c0100040d010f43c0070398405d1080d034031441d4400035258001c80340141c0445295180c40d83c40f50140701329416503441a90b1140d00613046924040b482e4030b2400403a0001d9000710b03881d6244100301b01842c04042c205412540285c10184034500741000083e0840c55408030302650150b451a51000461203880142d010303880760b0364105c1c03400c0c142c0b05079207005e40098010444120308100310040c1300c4403960516100e140c2c0503400b600140c3c80d15420007507140e1181034140d08006008840102c0945c3c00d01500f02c1c0c3d035029807200e800c4441c0320760b900d4003514403443d401014008100c0007040030615041c8080f011080417210008000340b18078000008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 210514154 1250 210512904 210512917
    0x6040302040905010e07090e0304030b090c030307051c050f030a1a040f1406060328062315031003150908030702061e010b0d0b0a0302060c0c0901240f0203 68
    0x49800c0915070400d000f01903000450380800d1100351030f001900c0300659402c2e030303144202c0004181e008210030004182925035440d042100c170020384480f9100e00c2e001900d9038010b82c205039001c2d000624040010f82d04a007050074584201d04201c0d0400e034100d0b0200380e1a0100610503000741d600c0c0c1d20054024a04140c07804030070342c3c0082003003042900e401c0e00e0340d00502090540420500084010803070515188080c1c5e031103103101440f008040724155540345420646940010307056610f403500400d07002d141141016800807007403c1c55603125111820009510780550800d50000010401c2c0410380000000413016260460a0a1030700601c00c84a00300810320404050f10040c008000d104082d5808070300f1a004040d8022000000d061040e503c03880c500c0700b80b262901e03429080006074035512068100d03e00d041002062a040595a1b4005c1803444d0b02c40d9090b030203981c00c00c00340c000e0580341c511030312800b4226907181c02d82e101e488804030904503040c09032104148240c100a0a070310610030000c40d0b05 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 210515404 1250 210514154 210514159
    0x815010f030b030d03020c0106080705090c070c120f15050c0904020a17010b0405090a0e0c0d0305090904050102091201060b0306040902060408070f0303110115061206031a041b030803070e06040302 86
    0x2158000d800c0e0017402134104200301d4106500702000002e84c1d00e03002400f182039643c020141d040e69110380c0001400c0750f010101c00c440c50034181c5000503501ca1811a204071140c0240340d150410b5050b807424070341c902c9039510394241c420315210070f1100c600103243c1aa1a00302080e82e0069482028000c16030702c6417203880121010036000ea00125843d81e5120141c0700b02d4200340c07003005103901c4000200003038a00c4070906180d40da1100808001616000030102c45140c0242019843c0414450124a080c2e6085505544d203a40020342244503042107894100c20407a10402003010303504008e544541ca1201508251295449103003000c00d6541d8801218001c100340d101300c422095130f6807141d010b680d055103c00c0d00420710503c0903054508044c000d452940a0000741001440e0808a0a4401c84c2a41b01c95150943da901d02c040001810000c4083d5400896150790001d40f41c28035200381d00000c00c403a01c944c18900c900040000a1419003500e0f0000840c0c01c0400325013158501103403c070700482e40040e5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 210516654 1250 210515404 210515413
    0x405070e0a18110a05030a02280c030e0d1a09190507030c060302120f180a060510120b010603090501021e090f06030615070501090c061206060815010f030b03 69
    0x1d05088800b2007515540d005a000380b02140c8680e0410900307000300c20960b0041502000065420701066004011a1019030556000303110a0801c06140c0c02040ca10100401c42c02e41784030080c1034101c41c8a054030310301103407030600b0000b07035940f0310111440d0100d80804038201d00c1c0209015103400c3c4082e4030300103103100d00e0b944c404916045c0650303201d0062000b82c46400401d1008140c80e071080c0211103030500c0b10710121400b5140c0c40b241e03c0085400402c24000703480303842500400d4074002d00130a041d07540900310105080c109401840c4000c1216449020f100c0888102200003c07000e10540c2c1c110b81d000c0c2800182e007040b50a0060191080b590049101000c01c40040c2a409402014107010f28081e01c2c4050040c4454090124070304c41507039183d80c00701514490340c0a0b8004c5600a06945e4071460010612142e40d0b591080700c08070940081e00480c09480c002c5224260350700c501c000402c030f42c0c6821403440c10100702440b031519405440c07604020030722000185d003901a1304208070f629806003c8a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 210517904 1250 210516654 210516659
    0x100e0f0f03030a1206050604030f030c020f040e0309011d0109060c050c0901170606030a02060f0d09060203010b0c0d020106030f02090903120c04090b190e13240501230405070e0a 78
    0x412009419a4804c002898103201041905010013a10140c0380e20401c03c5080307000e940ca05a42ea035030403e0381280c0c0031446a044884a032a1409031100940d0220700854890310f8a00014007100340b4404512500740b01656003000503a404900c910840f10603050142080895040450400c056004040d411410080c0000703401d14043e10440581080e05080c3c910356200d220815840b007aa19002943c40503003030040018038129800149803410904400107110002130f580c0a090342c201346d1189880f29008114035100e00c4061001c900b2a03000d601c02006401e0a594070034409052614011380506d02c6480040e80b5400100202d4140001700d0440c14150302e04942003c1c5079030703c140a03c0242608240032840c080c02d0604c02034040c05412030b15007920317030305004128800c01d1005082200700b020200002d0045081440f05030305c4501681e000401220002c00107030b080c0c50b03040e84521040351074122040d07440701da0781501d40c090083c1110f01080b103481b00e00d4120380140810305401e503c0800220300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 210519154 1250 210517904 210517907
    0x3050102030403200a03020601030809010e03010f0506280e0403050903010213210317040602041205030301030204150b12040302030903010618050a05070f030c091d090c100e0f0f03030a 81
    0x72114803c2400148071106144924100c0c0c0b5170801401c0200560b0003100107100080f012001340888880625001d0070310b500d05000a0709403440171046000c501c0c1e4031814040c07541040d4034041c1030f031480070100d60b003180010460200d10b410b003842415600701002c07010804041c85801120414200240203545486a04802e44010501c80c8a4800c4111305442c401d040710b0b640e002c0014120340c245d00c0300c0b096074031445095103c00000400444189070b08210104290481d0650100b0990080c0b00031601c0e0f6065105000031905060a60030058128500c01c200b10400c0c0402c46240408a040c00c5d0400c1e2911b10f02a40b5500840558540c154240a40442c444802c82c000074002c07208120280415200d103040801114401d4800e60700050340c0340301e1030000c00e0283d0001d09840919180008030720342e6410025030b106c404804400c1c0740c0a46c000921101d03050070040e02e0f00d0300ba8201e9081e1011000b114000d02984e2001d0030305400b40b500d00103591203030340d0f0307400d4201c40119014043e42d5031070984410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 210520404 1250 210519154 210519167
    0x503040f080301031a060919050402060d0204230118031b18020d110703080408071a15010e01110303060f0303040b0406020309010909050103020f12010e011a03010605010311070b060a03050102030403 87
    0x3170000c0d100301000024a68075003442c0c1540100380a070040c0ca044003450750098041d040040042c1e0304072404200e00410502607200600007172030b602d01441100020a04002d04180d10b171900a410400088180d421340c94280480d6030899a21514501091214400030b01110400d0342c0304089c0000011110344140035107030010041b5040884080014682e070b074034100340324024031002070001203d0b140083c0c0015202070003801010700500c01c5144a8081e10a80041c0c032078211485808003501054074013495804c44102000042c09007808c0b144420708002e115541e002c02440e5910907100710f485500e41e40c40038021100a0326800e403400c3d40d599280c08003e55607074030006880d8000303075040b040000c90b50350038400c00341629801000da050f07280e0301c081049501d07101ea002154095581d044c103609100c8c1d09200d01911520f100521607000c10032501010b00710b035403640c07055052609210803204480a030b041202c6401c1d40c41844011991122400700d80442055080181990301c00000c1c0300030702d42c105071b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 210521654 1250 210520404 210520433
    0x6020106060905090f0f04051207051c05070b06010e01030209130b091821091903050d020d050906251a0604020c0c1216090504060506030a02010f0503040f08030103 72
    0xb00e440c84840d5841c0d0600c801002c0c110741c42074106070703100b000c2140c900445040a030030a0213071003100c2000c104200c2480d140d9002d030800312865841b4284076603030142404041001c1540d03500701a400e04c2080c3d200c00154800062060303041046c414128015607000f41d0503151100005008249420603030340e6070500418807c81020301c1031144200058102c42907084c980203415405024000201c940c07c840710220007003c21604044809210390012500c82a50b0701c250410384800b554040d84c17642c02d0145c2094030034044c8004541000700841c1915411004072050100d082c0d80d84e0f03646440c00303e518050340c121403400d0140e120048007184180070f4122050702e5100898403150545031204000c21003284144c1805903a607130406058085c280c03030720043d00e0030140f40e0b0f40140e03964100c0d80090014050081d4108400040d41d660a00007030000a1146540c03010065000b0122801642c0028003004070f4200c4400402c9000030001e410000303007401c0115100d901814041d100d503103070315044482c400d032007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 210522904 1250 210521654 210521657
    0xc100804030c081e120c0c030f0904020f0a05030f150f09040c170303070f02070f0509040219120309080a0314070c05040216050607080c030a0902030c031605192403090c0602010606 79
    0x71700840d071b0403400c01080307410740079103880118a40fa80141a42c441a00984560382d8460f40c03d0152014015900c0d0007891132488550f111030b52807038601c9a462101c2e2003d046840102e08000f4102c9003a150382e901708080140860320f0b105159a585003183d50200a50000d0344030032000c6071001401c4000101450007586c0c203484aa196900c01802247c3e250020b1080d05444440d40340304200768108807050f141c1041c00600100710f044904d070300892600d621580b0050402400310034038400d059100c1e8015003d810503902800da820020b46009207905018840d8564424000440a0400103030000040041030081c01c19074803881c140d8080c50b10600e040f02c0c103a03007a004000004812501c1403201a103d000e10707030001030a640321070740104000c182802040760984104107480c0351a641c1000902c05c00d0380e0038080180540d013001d0601ca8407070440780102070342440350401446003014482c075014001c51001d050480c008151801100a0138102c607018050766120380011500c1581900400c0a4690b81e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 210524154 1250 210522904 210522937
    0x20328021018050409020d051507090909021011030c0d05190810090b0111070f0503010b01020f06070e042a03050105060a171b0f09030c100804030c081e 67
    0x4400094a040c2e0072009070002c15001401c00b8041c902d0a40e102a0050740040c01541d14a4000e5641c107240c00759100547c0b408502d40c030204050945c1c0300400c4001391070603039414010348400703034081020701220740305860501c980481d00340f4040b07c04101342c9140000184c01c8400401c40c07540007510603400900c0c2e08110340380c51066408000d00648a06008d02400c120352034010780751000c0b6a0040c542501400d04008011115138010f070070030440c9a000d440300300780050080e454070040608450107103036038038103541220502e0292480040b905035480211801c00030b41c040d0301940002c00804007001c020251520304201c4035078040f403504414504480c0d5440800c0166255000c0220501607100814000f4000c44030514a044e0039260302900101310340460200022005680b061036000061820602200071030741280c146410401e10715a00c00c25103e1048115402c94000e1583e08010700241c00e11400c0202c01d001c104200303007240c03004a06801403a02a41c140302498800d80c0c0701c83c1030400c25440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 210525404 1250 210524154 210524179
    0xb010507050a02010e030102040b04090e0705040e060403080405100c030e0d02010e0a0201050f0c0a03120c03110f0310171e060c03070f0219030f021e100902032802 72
    0x90012158800e41190040400c00d9999004488118a042141d9015502400005242603040c0e020384044c0c680410301090010400b0249803910010340d0080d0320903800d00085100e0004003152690f04250103103000601651103091151034170b02c00d190808903d902d0101c01003c1d0981c1903100e4098143e0030003e40700301c1050107108900744e0b18652540c0d802900030030000001580644010241001001049818120b03403403245070505803a68001e40100d1344606002e0b0740b500c030600ca085020044c50034100b00c0c03d00c0014014481b80170750f100010000000001240d07400358100118001448040c0200700003e100300130448e00c42c006000b5012402201c500c2e81d041e001c0010446511a0321604891800c42c0d0b2403040c1150518210300c0c80d0030a500409070310300d9446048292544d54280030351200041e1119103a0020b00d400c1e90b00c050b20f000c0071310b081000900044041021070080f180e1403408242c0c0c0c01c01d400064101031068500c00303003c000111041c920413010044107000e50f40200c802d840c0703014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 210526654 1250 210525404 210525407
    0x90a060302010e01050901111905070f270902034612170a0516020d020709110f22060804081e0f03040308180c030a0602070602090307030f060b01 64
    0x9065010003808101c0d02e482c0350304a544550003815178500149000000030341600e94a40c00c051102d8150340d03468003004000e100b807080801002c4001c0203000e01c00045603280200c00c540c4400c40320856030b24503050481c0050f01c840141c0016204a400405859840e40c40c02d40350200f9030b404440c80400c40c0311030101444018003210503021400b02c45c2401e028070020940c3c821102150074082e0b20140040443d003e420000605103540c42211849070000b46818000005081004a0301211046502250080c81c6940e404517922048a4140001103804120b01082080718000c4000d4440c00700000b0643c40c0210580012050b000303d1504617111032603807220400c0702e420f941103c02405420080049040e03490b002c0c020b0302a0b40122030203080c14000707000000a010b500c1a00c0a038001040001404042490744542e5031601003000001c100c54a6400086515100c8058025080340d502082e02c4062049507012240003202c000d0503510510b44134901840481d440c03400989007540b81090944030355 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 210527904 1250 210526654 210526661
    0x1418070b070510020d02160809011d030a0204050405010b0d081b0a0c0b091c03050d0606230309030c0114040302010b0415033c03020f01020703081605041a040302090a 73
    0x54222028080c41440483e00c1c40195004140c4001c0c2d26600b0002001d00c070707484050040350b0038410a002c035a0b580039000010601790231030201c40041040854003100300d0798000340056660745d050b2404102d40d503d90501b50300500c0126070b42ca4110803103007050820014503100900b14440041610303403044a0141d140d541e6184021030080039101049400d000c80030801d4060144900c0c010072502c03500782c041411602e0500c001c1c0c802c07004110081410110201c6901032503015001d1880e00398a00c4080f0038002c0d5240d0050907444402d41c40000c081007444005004540c420a144c1001744003c3e0030107078940d62000002c40707050b00194039000e40f120244c603042c004e4444107031040c10098405400c50701da05d41081020500c414503c100322100c054010409074401c40000c5070714204144c45500c034200030303043c4480c2c0c014812440c1d10402c02840001e4102080d241c02041001222608003a13000302521a88070b580c01800c00e03114100b0607200c5030b001c541d0041c0305503407003580c601081d42c503280303c1e0000f40e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 210529154 1250 210527904 210527917
    0x1e0e360d020625140409141501030903050315010c0b070804050d0201020412030807032c10022712010e01060f0b090a1e0b0c010c110f060402090403031418070b 70
    0x10007951141c60fa21051180c444207041003407009a90b45840ea680c0b03001c00448024110a9800c1c031200300400003440030300c450111081c1c40a080502c415000742e90010114480240526205134051401c81d540d42d100785100a015544071341880c00ca07081045010702542d0b4200c030100c80d18030882414206031841802560b0445900c500d102e40c500243d50f406846051009001504040d503070940c050410b6059814003001c010a40050300038091000c62440c06d00089800c4092000d004000301c0702002002d9403241e0b81c47c40c0c1c20641d0007a020101e80003500441103031250814940c01d0a2801c00c3c00ca1040d442002155100c414202c0329664510000a0302e0003202900c0707a10100020301040f040756204048003181004035000701c0800d413100c03503009041e044082c1601d0305030340d9010984040b42d0803515038212054843c0003071204041d8035460307603511034004100074011f100003c08a01098000e03005580078091000c48100103241250003140d52007040b0000d001a44540180003901c0e190b40c108840d01c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 210530404 1250 210529154 210529201
    0x180b010e090f1b090705190c0b0601090b041205031905041d010302281806080105010902030c030711010906020c010525050d02130e010e011e0e360d0206 67
    0x91030f003112000c0201060008201109000041040005400c01a520880108200e490381d1980d21601d06010200e054001c0405040c003030500d4060101ca20030400303480854004005036003a4103403614085095024800100c002c4c0425801c0041c80150407e0180084c0c941291440f04514a020152100c103d000e00c8003a41140c80c000003080062542c034000c0c24010700c1c010054002c1a628501001118002130805140039074409080c401001c0a0040d1801000200025421070031b00490182252201406000c2886010400c2c0031101e902900f162080503080740d0215250541001d1883c0601811a4407001041183c0e08040d40d41c4403000706010710f01c6003030ba1010b042440d40c1c0300b40f40c02580502c0310390900c4400c810780000e1030101000c40d14080c0c2410350011600754036040320350060580c030a00740260850360400c00d0143d410714206450348030002c00c8142c10030502d8502c050540c6443c3c84c400c07003810a80300301080c01c0d40000084032001620607508841c4143d03580d81c0c200c90b2400c8910750124 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 210531654 1250 210530404 210530443
    0xa0b0d0b0606030403211e0903090e04030212040b1213050d1b050703060204061202091509010e100509010e04020711060708130608010611160603180b010e090f 70
    0x4440e41400405036a0045c460b05214941c0700194211b00e0390580840f405014081e280c0b901d14400d2024903581402c8001075410a0002420079a005010f10071140113503005c5000340303000070b010315108100d40c2e075414080c0d010150b5183c0d1284140f402d40d501c295a01c0280315a224045480d040b400c1c07030103203189a0000050101e9160b02d0b001155400304202500080800f451b80c1c1c1d1010a000380728800041d40b05001c01aa680d18010010b0036009c12415802e1019206000c00900c80c0c071035403082c9480c0c50090000e0396941405800507101842c2041501d90401e0100400c10b03051a00900249008a82602c9080f103240e00f240400081e40301d82c0c98010b140044400001c00c003030801c0400391029900c03c01081d400d001900f04041d13120720301a44040005070203500100001c2e50003403181e604141658028003600801044181100030980c030455003050703654a50020f015101c03032441c000507640441e0000055959000b1090603610943d016403e5000f00800e41803000d000040303440c02070708404950b1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 210532904 1250 210531654 210531661
    0x50304030c120b0c030a0e010e0c040b060307020a1e140c0108060a0b070807030c120f090e09030909070210020706060906090209031b030703020904050d08010f0b160501230a0b0d0b 79
    0x600d0b41d40000c0d02c0041040d844050a40340c0b640c7c28003480401d075001c44000d000b00800c00e010801035544a05110340074034000c10600071402d0303020801080440c1c1268000341a2042034018a00002007514007031b02c0c6800d0841050407a50021910026417407090361004d0485d19000104440b139400d03442900c040520030000c5000203000180507120003030080c14905420034064441d041c0108607401a40c0020f10240c203184c00319a00031110b80d001d4400c4070b000c0b41240c41c10301c070042c0c2d4a11a4a005c1881102c4000028003614400c120701c1c9520401c0f00740c03d4ad2585d2061901601404480c012070460341e0400601040c0c07003206201b514203030007009006181a03070b0012440890024242071864041c0900740300400941c0341c810a40d0300480c460802044015003558008106030410380221910304200e0b542003103011000340546617415103800c103d42200c2030603d0058010246070a605814404000c0740e110400074901100e4810b21020360280034001403103081040b0b85024105c01006c6141e0600030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 210534154 1250 210532904 210532921
    0x2030c13020a170c270901030c03050f01090c0311030a0c1401020709090503040509040314031009050709080607050d0e0706090f09020c03070807060b040608010507030b04050c030a2007050304030c120b 88
    0x743c688031910b900c3c100a0180404011446000023600300380e0304190800810001c11200b040f00c4030001440c44d00070003441c040365443d41c03c1521036100152a000203140507810b155000e0141d1f02a4507403110440301c0559444c0c1860f04155913009000d80580282c0e10005220350030381c05110f1250307901c403010f10300d41824442008001200a0002d90401120500c81e000018000c0000c43c0112424940098070a1820300c0c1d0030b0030f890005011204000072020100f01c0520700040e00e9400c110607091041c0ca40107800700d240000c00d00c0e80c820703000703e2103002000a0000e402c03001001c29581d500c201000c540d501e56480c1401c1c2d1040031503051982d4001c01c00c01022071280c4c0c0250a41078464080400d002810a0000d4251421504240d0f0141d5503102400300e107a40500c0bc901c0d4099099071b040c0001d140031030440e03505000040c407035504580c0381c00c61103c0b4450100508400c0c459400c02898079012036080440d41ca42040c001121000c00c2040e000c203107401c00e403244141c999030255501540d40e030b070282c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 210535404 1250 210534154 210534187
    0x3060a110408031201091a03100b1201050f0106080c03011a09130203190605030d0806061602090f01030b0a18060c02070f1413021c020702030c13020a170c 68
    0x26812000005001c041040d0070140020945640e81c503da001065052240a100300c07545c0b90003078800103e6001c1400c00684010803400c061039400c078000145400600c0101300030704100398000780c00b5480c080c03c1104020241143c84d041e503c03143d56142059a94080001d03917448280201e031181c10b030700414102c40c40e008c480108124034000d0322007503038584062608800d98100380c402244000741c941705803d21020303900c950401024201c000b041c1e0020b412102421181d0081c0040d07028040015105040042c400410300310954050407a0320b21340f4008140500055080c00222000301a0f207006ca90721810a004030b0482040310305460301d0b141c5655959034001e04400007400c0541c0a01c4400060184503400d62000070240800c80d002610300c0c0c40b0401c800d0701600224000440e1040c00940c0180708050b8208116002c3e8150060f6641c801e400041d241483c03a49541d43d01400c0b03010f10020381401da8001d07184178991920f4880380003030a180600010b5004891009000f00e00340001d00f8404604039 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 210536654 1250 210535404 210535421
    0x6140106021222150f020d050a0e1309050d020d110d08070c02040608030f09010e0301060f120606080d030c031b0f0315120c06171003060209030f0d020d0906090503060a 74
    0x4500d010321940d13101450350940918400d1008120001c07841c9244c2034041c000100001100d1600528003105481d014004094200415018090348000c0740003400c1a80d022410312600300c412650001c01a840081d5078400301d0841500107665910310941601c0d001416810042c030703c0e00c420021b95280401190790b0119120280d91050f2504000607802c18148001e00c00101841201d60390b807000100090300c10510100b6080c020b0389842010090b00005c04882c000707941600c18810250045420a1009014103410440160103940c900030600f54055010402d5050b050b00c052029000610100d402ea412250840c8042042c204640444030b1095100c0710202c200e051100114545816007a90f102e142c05a04803120440d440061002d21740040401c020072032850002030a52800c2d0781641102c100d00d1100400a980200f003001842c1d600b803142801c8401b6580480700117100b401e02c0203590700306140c0f40c54045000b04402207412889070b27903110152140070b00105900d89421204000404002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 210537904 1250 210536654 210536707
    0x30403020603130c06030c020c0d080406140d02030a0204060311070201080106030c022109033a03060308030a1b0e010507020d1b09060f0b07110904020102070f03061401060212 77
    0x341c020500166080400078081c2c03081b9a000645072804483c0649440000c15425100e110b00304c4690740003030088411102a40c13594079100c0241e01d221400c207000c60082002d1199080e0000c410881c111080340c1c082d00895003207540a000c84928000380007042e00c03840310003a000460b000014020180690042c02c0000c100384116541d1501a404d040449059014022006ca00001d510983d0b840e080205001a0780c404800c0050f100c200101c0d02000c08481c1e103002084038061010107030440c000c0c0d210324011500038101a90301c0ca02000907a0003881442480071810441070740610056105000490710100181c540a28090785a001c1020b0600141c42c11940310358503800e0190701038541c82e030040080c01c2031200420024248003d420109525400c9003910940138085180410f10480140b000508165444401034665000403801c0c54096000020210706080d03001081100b1a0f00046507400002000c4000c0d0745c8410041780c460007464650102c69000f440741d5100b405540007500b0146184 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 210539154 1250 210537904 210537931
    0x110405090f071107060c020325030f03030212010e091203060a0b030c0405040c0507051c0c060504060b120c010e061810050903060a0518060415020c07080328090305030403020603 78
    0xb0b07603034001d284c040c842c2c00c10000a29518944000c50800304103060383d100b4446084105140d10180c1307941c01010300d20014100d91117401020052501907412136400c2c202038000031059607119104407286c5103041e24445817034450000c02052990086050340d009c2c0c00020880e4283c94600760311107131a40c202030030380508a001080b00103a80c0c1c1d220700c6030403a80c164940303910f611101c80382041414859042c11020f900300704046c42284003940001c5003920a540500300260300c0d100d0341031440c000c1c411221183d400c0f80440350160110907000501002c00d41d4240d0759410032064503020f2240900900c803802d040200c29034035900c09464814288540c1d40ea0380c1c45c2c8030381440c00547c0080c0c1303481003d81c1d90fa41360a50740c00c01d1111880b801d100701601990340c0002000d0504003640c684c031405910b80340031058140c0c00b150402c100082440404001d0865404070390f143e01c01c0f100c810400e19044003403074150310701c8034400e6150940601c8a803001c40340c1180280d4201403841d001c0c062281e100805034900e4105 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 210540404 1250 210539154 210539177
    0x80c2b03031b02162309040f230307020904150903082a04051012180c06030c020c100212041d070216120201030906141009021606150302090f0a110405090f07 69
    0x1500b054142c840c0d030140205492303116480c1030442c00244006903104042200840b0b03a144240000304481200d40c1c10b446400032680e9504203910503a800312940c1d0089070801721008140f65000401c10b01910002600400b220701841208510806044c0c1000c406c001c18081041185480400c41d030300c09a441c10940084883c0c20043d00442c0e1144061480f1701c510f202e015402d000214444902400042c10208003501c9000006940d4066403104d440c40391070310060b45000b185c0700f80202c4803081d14000b10f69403582c0c2c0b0380140503032520400c41089131b003000c078030300080c03034148002545070104400d55500b40721141813031221030900c584034400342c0c1490f480b0900d510005445202d100001802d1860407034150420180c03072801040c1c0b40d4020b0860b1401808421000302d401b0080540b802d610540016824543e2180c0c43c201e0f44207070780b0195100c42c8150401c0003402d0940005441580341050070040092100a4914140501e00506812502d6074001905030406400b00f9600308640382460aa0500e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 210541654 1250 210540404 210540409
    0x20705070806040312020c0604171b1f060f06320a02100605061c06091b0e010801150509030709020c01020405030c0901080c2b03031b021623 62
    0x4035141d0056601d039100303200700014958490b915406011045070705600c0d040102c4607141e40c0300000b903c058400403048403076070100310010084803c1310b540314642e150102c0b9901070f0140c640c805c50900206ca140d8150384608402341034032488090780c04044005120380d04007842211900209401c1c09005030348980c07280110f1380759030005000080d03401140ca5580f41c002000a040ca401e8004043c009400d04609110f195508400c0d0780142c94101940c4526201c1604680040d01140c0d00010900b86840c5070000c016070508039459488189d9110320b44600140801140d849000340b10325114580a1703104a420b8900c188010301e00d03180c004007100c030340e10b46407484c08003240d0100c4603c0d94183e6001a040056003014089a100c501044800c00c013158500701c1c83c16202d22086278082d101e84081803e80c40e001c0803071588414240b00000400340300818620700a0020b021170391036140b0640201e01d180782528400240c02038000b05070500e042c140e80ca8690500d01240a002040340401c91003c6010410f4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 210542904 1250 210541654 210541663
    0x303072001020c12040510140301060309060b04050705210c0a030e1e0f010b01020a020307090e0327010305060904030c060b121b011803032c0909010c1412040f06020705 74
    0x41c4e003c0d059955594503180c1048500103140c601102030000c01d80c501c00d41140d45005a070304440c640c1c140031594000505d0940c00500c128000c403a4130078500340a01042540c0320010f0429024aa0412482d00b402c00e14060012002240d204030480d10400444100c14842d0b0010580005000d089611450340c000c0c4889000650b803980d500c041e440030000c2100c60009024031084c00b107080c006801d881c040390700800d80380d03030207070055400040e1182041007485c10100101e5032040680c1c2c51690b4040740800702040c0d000e40e0301880500003030030311010600c11f00d4000304050180d0b516848588601c5c0407070f038800c0003400c03001a22031360145074104c50014126091040c59114045014061745c81a40d100c0007400d421119485194200710751882840043d4020100d181404004d01124400d03140b029030010280920703580d92604404140144101c01c02c054203c040028515120001c1022025045e22a640982e00d00e18110480590124020030200300340c60032098002d190140c5491010303101d29190 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 210544154 1250 210542904 210542923
    0xb3c04170705030c010507030f0e251a070b0708010e040b04080c010903080402041104081e0a060603080309010606230702040209180411010903150e07050301110d0e0303072001020c 79
    0x4ca035114001c21888035410711600b0800642c02c04100100c110800e4501c8d039415005003015440403005214181018081d0b070b00800070191501c0010b00c141800300700218a4022035030071202061010041812103001da2000c41c10384402c2c58145086940310b446400750b1010190050301c003410700300700c503241c041420b00075000355038040d841740b5989040c00e206102c1103d0303054608845038101404140710031080480c941c0c5146040d66401c00466114011103070820041100003010a03103800000810032039140c1c003451280030008000c106403907440070107035412002514031703c82d401c14400201640350262805040c07418000781c001400c0c40c0340400829102c41d902821000181164400c0100f08000c81d00b003101c801d40c081c640303201424a5651489140c07041c0c40701c003400464454601110b61102000041e000b081d00070000d0040c5401c2c01c504060b075500050f08181a5170500350008000c0e003000013264000d002c10b944d03000b080c040d41c85191900c0b019401403541255002c2040803100c0700c00308550480c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 210545404 1250 210544154 210544177
    0xd0b13020403150203042102010b031009060513031b0c05090c280903020904021f1808071a0a0c05010c030b09060103050717060109030b3c0417070503 66
    0x81c0c0e182541030080c9452585030090403114010410040041d44400c1161042d41c0c018018100340080200c09901512415580541521580000041d030103400e03001410454040c020401541e2602040c40361464549440500032a981c1c04640030800101c0d4500b110030b0340512100041c0701d444d00c0010b84030724015140040400700214044044501803101c0022403d0188a60701d0041150304026108008620002e0b215020010003e000d540301c101c0b180345004a084810020f10030f5021000c0c010020005024049000c00e04001ca00c25200141400907101c1c01a5040002008040021800c1d4882202d0100b004203100781403000550900815441401a803004110400d000e014400c4203840104114100f42c140010310140b560080703030450036098801c00d141d01c943e59110041c4c0310344c000c41e0b0000300781505100400406402200e0410009402210641c21801400002840c0d5042001c094883c0b4120f48011500262032505c0c0aea1800c0038000e8090705000b400d0f2950750443d00050b02c00103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 210546654 1250 210545404 210545407
    0xa02040303021501030317060a0b03090703030807020a15020309070f06110c090f0a0c03020c1e0606010203030415050402040b1005070224041a120916061b080d0b1302 73
    0x205501403102d0f8107038072241e0098594561450301d0091a011400c503215401590380d5001c9091902d0740b618006c050100460317840e9507802d0036440e460340c841c1c95110540018400c030780422030349440440c00a400c2900701d60700c40300c42e040c0414180025072020b44249094070031a000010452a1042c0000060145407142c0d5079101000c1c09160511850b000d0550bc03a00c84d680c10007100340741001100740c01404000d80000e508040c944180d009203c1c42c3c504145038442c40d803000400103413019010801d00008070550b8602d8030b80307070010fa03920b0005440040800c90301844104141565904c52540140018008503160712203602055003c00c01a0000c40024070010390350041d41480c05040940f01490615074200b00e11569072040513004502848003c00400526142c0264101090341d00700c004403489202c8504081d803a542d500c0f0880c5000c03101005140c600011114080c0d00c400304244d41241c41c40c4076001845e40c52550325802030b80c1e0a00c00300d954105020705a00c441015400c04d01d50082c006 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 210547904 1250 210546654 210546659
    0x7030b0408180f060f0706090b10050102070b0a0206040b040c090218030610180f0608060f04030f03020301080616050c070609050102010b06040b0f072f010306120309031b0902030a0204 81
    0xd500e1502c24160aa001e04060f1010080300d8554804490b440005258141c1d1200d40c1441c012026101814000d42500c3c02c1809001e030320559600c0807421908240c003143c40703441d80c1d8030400b101f90182c08088009038200000080100390f11046240c0e0080c400d0383c8801040b61038803800070498000d1000c0d041d4110b42000e10b0806c81c182000a1908280c1d205040410b143c07409540b808512590300618100030303110345501d00b44a40c10741024029014540503110b0510f0900b07101084001c04031400d4000070760181000010b1806482120306903110030f000740c041d50381c0c3c1c1c0031028901a000d240c8001049000c00000208441c20310400c80580855656085005e150a000a00b520352003000c031403003a0b0041004100303220b10f08040303d144140e0102d4035602d0311480c0c2008000b0300504444d4500702080115103603120203042e0511070231540240c90030020640c4400030020014102e41c0001c0100d803802600b840801d03200d05e040210b2210109090099030f45400fa00d005980003030b0f900c1c42c241600404c0c01d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 210549154 1250 210547904 210547927
    0x307030c030b01021f0e0a1a04020301060b1e1e1605060901020a09150207050d0f1e0201050a0e0a120f140f100f02250c0e06010e06090307030b0408 65
    0x102c00c9103070400d2004210b40799415000b06503040100010b0300942e07554100301d02c001c580600c0000c0302c5035000b400c007504c0d410550101c400c0c10041290201d120b075103000d40119450300d80c0c20654608201884c020003080c01e005501c005a0340c03004426034200c50b1440c0804600505480003002c1c0d0745d0228000010b640000e08d4068640603011f0200d202a90050210000c600d9025600e641224070444031007120f4801d2600503402c181450304200d400400f0340c440b500c203002000f000341003202c0c420f03461801e00100303000b0801150740a5100c02030000300c04000c3c2886c031910584076010342c0300004080161080e41e402d041c80540d8a01f040803115820b01580242c00d1001c0c0c0440c4048241d6150040d0012464100030f0f240c42d5003180c464071220707950301c1155811700035060b03040d43c010300310b0032002086280c8440703280550940b80030401c0714030710300b15070f000b00792104020036850280a040c0c45034803042600d03c080020301d410141055070075100d5500b000000ca0340c2c2061603030040380140081039075a0800082c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 210550404 1250 210549154 210549161
    0xf07061a03010c1d0f030f1501051f0c150203090a0213020316080c0c030406030608010c11031b01021c0507110a0308010b031509010306060503070503010b061b0709020307030c03 78
    0x1a0395200381d14100c608880d080d0020403000182c0700f09580d20f4a00d921550014011a60301407466400d8440c403000d043d01203078001262801396407a80c0361000982e9030751040090314000c0b262068407a01e0310a19000503d030145104d0310450380300d034000c90100781c3c8250202049030030849000f5040d41c8000b41200550505000c01954000200001d51462821082100e10060301e004488100710a6500140a0501075010f0328035a064a50a480e80c0395038070640207001c4c3c11140a4550f565203416400c09000d8002c100c1d04602e50f101101641c1405200c1e110380c1c400da41c0001c0282e1b9555000c12036400b000e181200020310400075604005442e0902d90750007000740740445915201e50744410000808a5041940c0d5411284100c0450345e50703a588081d07190a8120060402c0d030030608404c0048100f00d00c541140c2c0560700240c044400040e5a4010182a43c03454184c071034118404000301c0351103241041c8200342d1000340074100c800d59a502c21948040303a2003250154002551001101c20b00c5a1600 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 210551654 1250 210550404 210550451
    0x2030c0114011806030f0b1305030408070510210518060a140906040c030b1003020d030e1512060d0201030e030301030303060810050601121512080d0606030903020d080c0f0706 77
    0x210100301150075584c074504980300810f40544010924000123a40c10a1145a0703200349512205503a22680e40d00040c0d5601c4506001c0d0070311a044102c04d2094451113851501c180c42e070401c2c941c801c5074061000310b10050001401e000a0f0040d000c01011425404004003401000b8030740340010408424981c1d4001c200c400341218105820180c10f00001c50120581003003078a0300074003145080d480740c42141e01d98840b0780c1d00003500318680a440d8401c0c580c100b0341c0302e01d0699060741ca8980c90310170945008440d00ca00c0000d44401c0c000003010034854145181481c003a0303441810006145503506044610319002684100d001070340303032081071020440910103d0341107403004005011600342640040c101c5c2240902440a0950360641c400020250703c5001000b4805ca45210100c0181410002c20701d500032144800c8c0c80d4240540058841d10134801e000055070568007615a10144181c101d0340f442c80504221042030090099441861281000b03140c0188120702c0000d0f04241c282e00b8261501b0302e81d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 210552904 1250 210551654 210551699
    0x509010909050319030b1507050606010801061d12010519140417031005150a090f03080a0804080d18060f1a04020d110c0706140a0c06050702030c011401 67
    0x15540c507000403030000995402c61040c0213420b9040c1c1024000301e0080001e00c11581e4006120003100710660300010041042074050410b0b1182170341d90320b0041d5507149003841780400196080540d04911408022000e810200c01401c12800700031a42c0350600751102650201402030642c030f0f442100c68814440c0f4400e2540410720700c4d086261070385480501942c00c070040904141c0000016202c1c074544504840600340050258188204000b105c03a21a00405010b078040b48072010301085026101d9250005c036a40a00074500d043d0404800321030503c030150040340c00300ba046c8810b42400d00c00e8000c4020210803541100d40003a184e00380101601c0010708422003080c9045031429244038002c8500e408000103071400742e0388a040484650043c540005810800300000c284080d041c100400c000045070010359600044444242242c1820311910045002081d80f4007941c40000d24250032044d4802030b6030060f6030070b040c0e56880c11800d41d1844801840c00300751100051192034070080d891030201e2a01c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 210554154 1250 210552904 210552911
    0x30d0201060b0315030a1a011409041101050903100c02030a03050a0c090302150c1b0a0b040b030402130b10090603051005060f0f0f0c1b0409120c02240405090109 71
    0x30010302d015544005000d020618081c2c00c181c02076910100324482199a0000200c0e40090401070045d4002c031080c000c20002e4001070360200d00e00e10308404640c3c06290000410303000c1e06a02401520700394084142c682d014040e0800d083c4c0c26804c240b10740a400700280c1c010315038500b410b00005048a400402c11055245883d40104000742c0c01000d500680e87d06a9407a103a4004110241096004006140c0702c24454907941e20441d1140130002c41c4880f17810740350315a0740f50316104800410301540c02203404030f400c00d00028000d80743c84407190021000510001903907644e914089403000300a6164100032036048002004995414070616038010003034103509803000e080030006070982c800d4800802d450303400443d03e03010f004403080031242c1c6440442d01c540d6032405030841c2561529440b006440ca01001c10f50640e180e400d140c002c22081c0d541c02208042321020f80306054404144605007aa000006850b1070804480070000441e0607511070012140c0740c3e0718241c104082d40308160400c07400c4504 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 210555404 1250 210554154 210554159
    0x9020c060a020c151009020412020f0108010302060f0f0409020304030203070b060a0b070201110c0a170d08071b032001020909150a0e150316032f01140d0e0606030d020106 75
    0x83c0854076403115011044100000d46a020780b03d0701c010059001498450310004002800000054500c8a4180302340d400c4440e65001800542d415142444040e4010004101d00b000120500d0002c000c01000c0f8146141015203d4590108980003140c084000d40c0c400141c2105002902610650004080b01c3c0c00e00484e040080c0115140607040009040c0031070204109107000081c4200200c50b0005020740501c00e5a492914684500411420000d80a440420201e00b842040b2480c4075038010340741c02003905000b50180c502000074090503010080b2600289844540408087c511560050300240e01ca4500c5002c2045008001d8200f400e0b0044ca800100d1081d20303a244039408541d0142e203804000d681f100c034882c0c4080c074010b044a13414098818101c00303c2012103088429a030040c4402400b528151800074060004140b141c44104414203c545696125004014a90014100e42810035140c400707083c081ea082407004d00c409400990803c011400c0401101885525600c001d00034940b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 210556654 1250 210555404 210555427
    0xc05040605090612070c030f0201050106021b0f090406060914090616021504080d0b221e1401090c0507031205100321020607050c070509060d080409020c060a02 70
    0x219a1264006000c07010a080e4495514030041c0ca038074081c0302411086504c1c006900a00c0380f1509081280428000b40700c0b008014414030629040e03991a40040c001034002610360400c03080481c1c032103a40001103104c190a0740d21001c9280e40078520410002c602c0c0c9041244075810798911514000703240c1d414404010901900003261600040300e101c0100c0c10304c01d0440224200003060303500150030400c9109100070040060004c00e00128031440800c040300d0500c042041c00c02d0095480d05248402240c80d4200c0b050b2135000e1040381503583ca030502d0501905203e90152109040001c000743e00c4100104100a49400707049901500d07860001c0c41c0540c0c07594003820700040c0031803007085907136110005000c035030580050768003460f00100403c0030207103403410901c4d100402d0400100140141404244000e00520983d00d100d50060b000d080021b0500083c000059001007245a0101d280091803003c20002c030300030070103459034140144e551b0f01c0c40c1d45001d180c160007a124003025407040003050400c2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 210557904 1250 210556654 210556657
    0x1103030a140c0705030601120204050f010b03070f02011d03070204050c040303140703141b011121090109060e030d06060804080307032c0a03090506030106090b1e070c090b040c05 78
    0x42007100140d8559400040e810b190034480c2e00301c0c0d070309841a03800104070280c007a9424001c0358800c640c01e001a6503030f0203081c4100942881031480080f000e00114119600034680780300e002c5450710001400580f400f500021003042050700010640000030110294286070058580c01546c01148030724003131841d0380041c09103041102001030410003094040400d4480c1d410040c401c03201180e02c40c2c0310a103500d0100860084180e0440c601d42c40d01082e00503a100b4401501d0f424030030341c1c5042403a101004900700040c0c5c00280341c041655662000c001c000780c410705c0758040d49a1800c1c000c58694841542143c126299600030310280501c000820000600001c102c079030020240c43c0100b44480700c0120404881801c2100340c11410b1b0400e42400380240005800211900965450b40d800c0d43d45e405009040c8428000d000007d90540818060381090703030018101c402680c6101e40501d901850349510305d401c078100840d54181d810004010f0520140540c1260100881e07003081281c420340005042c0c0d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 210559154 1250 210557904 210557927
    0xf01020c030f070804030f060f0b040605010819150803040f21030f03020d1a030d0804050a02040c2705011202090f1905040e01020702031606080f190c0c1103030a 71
    0x1114000a0f40350400031007100f038034019070344105013541166483c900301c0040c0c8111641c240c2840d00c0c10000541d186424019101281c2d0107031100c00707180c0c0700c1402115100d5510b80e650314130180c0320017000402011429604008010301005141c039203040c00102c101d42103040e481507400c150380d100350b500140130707410f060166140e2505000400203450b0f8000d40182c06054000c285051416000200c980781c010124420007004034151000e0380032103081136500d6041034a014180350300608000c0d006003409d9101c0c4c40b1001c0c00d0709051115841c1d00b2060440448000450754080494840030821541c020b00504165510340e5010340c204018000465070b030a0740c0034a4948914107144240c40c0c0c842e440007048000d000050000d1065503460310455010b5841244101c0c040d100301080c01d4821030f110764a200a80e9a00c0da80c805840e110a80d600f080154050076000c1c235030003a40070342003044074107104a200c41c03030194840c5038007108981000c0407020782c0040c555000e80c0003000001d0000ba40024000720 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 210560404 1250 210559154 210559177
    0x20a062c0a2f0319020f030f070b0d0e0307150506010c030e09040302011b050702030c093304020a0305010503190c0e0603030d0903020619050705041205011b17090a1101080601181401020f01020c03 86
    0x2118200300000748054033380084103c10f10300000401e241806068110b903405034440365000d01243d01d415004440151b602c03000580080e03481d1001c41c40d40d00d0502d55098101e8000e01c00801c02e200240b5184178030048040c850404200001082421400c081c401c107200303044120b83d529018600107075a200d0b00c01c003920740158647c2601180800d207082d064010041c40c0009001151600c80c00400a00203103000c0c054580300b03101301341c08003070b003604050380002e121540f00107031a80315403501c2401c079290b11000d8030183e4180802d0001c25800e4031980708503640304d802a4020502800d11076942e0240c2003560070007440c0c981c00c1004000f4007a410204407030444140b00d04c03500d0702000504005005080264030740382c00b40c220328286011180d018600324030405908600e4400c5844803418a42d603030303501880081c484481007c403c0e01c40d6003d000b01c00ea00c5041810601c1150440b007050300302c800210380002807400c80c00c0846201c0d13964104203c840b5107100c40c0003140741a11031701e4016901c3c01180b10b00d82 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 210561654 1250 210560404 210560407
    0x712060803070305120414070902070309050306060f0d290103120c0803180f030409021201060908100f0221011d040f020d03020a062c0a2f0319020f030f070b 69
    0x604100389500031f035029140b80700660f510903494030141d001a50000c541540014a150750200702864085086030145500800003002c100c04c1c0d00c00c1c031007651a000b0701078034107071502081c0070585c01495125400b07071802c000c40e0001e69811407038950038400f10301e2401e50402a6900e042c40018031080c0450f43c209030b0422307801d84402c1803603a0483c030700082c40c0ca501d00203000100300003a00708120f0f00613040c10303903c03201c0180303481e0b03200d1500712240007162195090079031082c0b02e80000d2003120740c45070700e46600c0f0300f40241c9081540e50202c42a50a020001c581503084003004024081c041003c0e5003c80368882d2542c01281030a403a41119200744d444007034480d810021880e0304040c000c00094500540c40780f402e00056104d514082d2055116800a49003031120203540c20342128003040170038a0652111034101d40852440c110012407024906c80c00300c0100e205e680c0005650304000c407092007140a1030780d05031006544184a001e6200c5060340e40254008030301d50300d00c00c80104681c81561404016135 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 210562904 1250 210561654 210561661
    0x31215030304090f0c03051308040b03060d022206060908031207020f071e060906170c21060a0504050103020a03080a0903060c0807110d0c0f02030c09071206080307030512 75
    0x742148950703445038040034500a1690400381958100020042e0b280c1c40421403035a4203103240350301c010078070300061510704100300511201009402954001d28050040d01e04580390707a0110351440c2c242d02d030300450380311050301d0144040c0c100c3c01448090081444d01c0b282c032034545986155030f07001c0e0440d491303c4a03080030700080c03c0383e200308600b045205034a8121880140d0310340303c501d00031030b5202d03256515010010001c6541402100a0070441c1c1003070391404c08840c5070a07943d00090502a2611050f000100700c0482401d1182c07505403401c5d2611a002e11850070301e902044502e1400381d000a002c1d40c01c050040002d40c1c0c1c0c4070722520840e0f40000213203607502c40710041118648919000100490300d0000c04000c81c0794030200d010f11841c601e496507000f100d26280d0a950320605680d0800006000c2148000010340049114041d1440507084a5420a010340040d891131421146500000d1207102c1c1540421101d01a0310004c10748680958648a01c6440060492082d032460130b840b0718103070021 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 210564154 1250 210562904 210562909
    0xb0f0f070f0206300c0313050a0503130e0a14010e130b010f08010c0e0f0f0103021c02250c03240609050603240a110d020409020a0908031215 62
    0x48a441c0c03039008000e9692010b003070745411900460100306244d084520aa800031600e000c0391654021801d0b00507642c00d45d0b4511620b1404400c070124119494003c3c0c042c00400907074100003411401c0e19401c11f80d04000c0c20100b050307000749001804081040d04140760414250401e6110034103540310b08100e84515500d284000d8138178080044000e020018080c000581100c17100000400d480401c00240221030326484126a0712000c036803000e41c0103000c41c2500540d4541b650a1139150441810b001d03060070380c2c0c1c41f041505100190b021030f0a9640001e10701b2001300015204400ea0103002441010950321521282c280a007039020007801200104c0d01d429402441084c02c118001002c02c0900201e500d90300500050842a25014060310500010032580d8140300a000091058900d220425596140002000e00298100c144001c101040f52025074000c40c0001c0003d8210004050ba9402d40306e00001c00c04c2c4d05550040c90766400a110210010a6854030283c000c800c0707070800311854206900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 210565404 1250 210564154 210564173
    0xb0406052202060f1e04150f0819050a0f0204240206010303051e0f03070917011118010309020a0815010902031311010201020f1201090e01020a0f0828050406060b0f0f07 74
    0x104e0310700c60350000c00d001034018200d000841488440303035282c004a0308e1580c425940d0b5101910786070075500c180103000000c1013035540b04c0c2d41d1100c51500c0100701040c1c40038280c0c0407a44150000c0b100303944020650300c1710001420f049184070150744000c10307071503145490041541c0209002103001c9454509241514814201683c90b28030b10f080c1d280e0395a0a100002922000d954880d9600a0112091140c4050010700c161079100340011801841d001e1107030081101402c0d800c0143c1e06161307076410110301589400d001c4101034400d010050503001d400c202d544082270416803201d02014010410000078094055004905541c008041440381340c207180180d029001c4c4d6071040400d41c10120b00f084811040300155030481d00300301c40401c01c91011142c613500382d01c1603280020114542c801c144403518841c1650030750002200b60707042e08420001e09206110781851654054240c0c849003840144615131181d44010078402080f145400d100d005000818065241260784504c0049040400d2100d07000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 210566654 1250 210565404 210565447
    0x705090a1509090606230c01090b19200d061a1b030a0f050c01060305030a03020a020c0906101808060403020a05060a0902011b02010c0b0406052202060f 67
    0x60001a000303441c0c40d21150000c0d0840c080200052944200203250b910038414441554040c1ea50458500b00401d07078014010082d1021540e544810049040104400c6c0308503044ca030f200d59080c4070141400c52100071160900c0100150b220301c3e00961180558000c1d103040d00032150b400d0005d0b15080c005490030000c2c0391541c004c0c800404004203440500540d1001049250300114171554035031000c50704181d61b0302840b1401d0001c161a420040030b100d00400190120b000d40f030700040f034003544940d25a42140c10181425000c80e8012840c000a40d0b014081a20011400c0d82c0d00c05131480d1520001d00c101c16003004650500510b9a04840261000700c844000b5210342800c8079124241481c1c02955450103200c1520280075032004a0002c5520307020707640c48244c05954844003042e900107046083e1548680490500201e030a000c0300180c003690040c2d00c40e40c00741c90001340c03d280100040c420010b22002d581e28803205002c0507001070780d4580c166816407200c81c801740d0b1103407034605206803e40e2581 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 210567904 1250 210566654 210566659
    0xd0506040b0405040b07020d03020c0309060310120c030201030b060903251d0108060906130602090a09090b04050601050f011d12060a06091109030d0c02040f09050f010e12030f070509 80
    0x3c020001481020903441c0c0c0103c686501701c42d43d0261304c2d20114200d00031803101750000d400402c4a101d50346050030195070400b810b5000036401e107a60314006001844c401c44210f50880038920100151340c4c01d4811200348210580361507140c005c13903900013a00c0b03202c11560b80812100c4802c0402241e00c0d480c00160107481220f021541c06440c0005000c2d500134244074035041803062000280c09aa00800c00d01d00030b00203102841140241581c807407000c0d401c551640c58005002410004011030107028510302e00b401403182c0301450900f81055820020305801c40e80c010b21210780c02c2011a40d115014010301c40081500000303208010380003911643d0780c01174842d814419082031100446040d404081110280c40301041201c1c1c1d40017220043d402110105c0740c0c907030041015042c045014804801c000c2d4401440060348066070102d4200b1918021000e4a040d84400e0111003900002d1180201d141000001042200f6880014005500c0010010020480d0b070382c0220b401113000b48140e46040c07100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 210569154 1250 210567904 210567911
    0x2105040c05210609070e1302030a0b012904080a150905010509030c1902300f07090f05041e080706020d0207110109030c061809020c0609150603030d0506040b04 70
    0x103034000c085400300480d02a10640a840007141300080b0014000342100c101d140215015503d40710a80402a24050180e0300350082103007400001e80d140400901a00c0e01d0b10b041c02ca054508010802c05c10b41044012640c648104003d019031080000c6044515502c01c10f42c049102c060b07c1c0c0003002e003540768001000c660a14080c4510700b0804405031400f5007151080b01c0c41e0f414401c1c0000c030306030ba0106019410a550145007001d80805900445000380c000c00c4640c10420280c03070390303441c01c00c820a040e01c40390081c103401c0c00201424001c840906110703042c00e01140c105a10307030401442848081c019007507060300504081100034030980d1401a040301c011074035503e07602e0002000e58800141110000035241070410380b5802a034241040e41c1c0c002c0514000c0c141441020345000c1e5030921840301c0d00f04030b01c400041d004803d00040124800e100c014000c44d080003031a0624141100921400d103117010002c08c00261000401d40d000040201e2007c60b03140c5444020030002e1180600c81c0d40c21505 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 210570404 1250 210569154 210569179
    0x1b0c0a080f0417030915030403030e070b030603160e07050a020a05070308030f0f1302062a03041403071508060607060f060501090503123403090f05012105040c05 71
    0x102000d441164031110f40c038804032042034245600c07072240000296020168a410390340310160300707015583c000d10034140051095504580540303031200d141d20103480350b000003080200c142428000c200c045d42c64050900000d50a0103001440171a004200030f0812402054001055100300302080015400105449010351241003480c00340c3e0003200c42004134080302c00071031081c1c0c0480c440c2d01d1103880014114030615040d9800c11103998400400014928491140d403c14036084100d40440800071f08000c4d95158078011020000c080d4101c20b2034880e421481c802c1203d0318018007240e80c5403100d0310300405035030746030f00001d6003034000e075031002d00558500072501c0e00c400400c0d40544d0642d503013600c1b030b4541c50307950b5010503546180341c0c4210f10500b88140608142203030403010100c028010704644002ea819985200b1a41403c81c150581c0040c80c0000d0400c40d0046185180c0094002031030410b2101d8085e1021030000000040c03640300280e51040080d06203c0d070302554401400b4000c0c60f03e50f0704d04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 210571654 1250 210570404 210570427
    0x70f0b0703170103110f040f0e030306030601090b090403030510150c020103060806010b120c042c0105031207081b0106090903121a060d180b0117061b0c0a08 69
    0x41298404601190b001510340654042e10031a4a040b41da111010405000030641401440e04014846c01d4200751500b04004c2041000d02420800c1070801d8011626481c00d40200343c5032900680c4403e4405103001d009500c0c0d900c50b449a5507000f82c060030301241a032108103c48451910a50110f265400c0c1528290807640d03020a13201c1905000366824801a030b10742402035203641080c403a0245280301000007a0b00500352150301540003914809150600317665062410034100c0d60502c84c180840300b00e406041101002c0e040314003400094006040325045004008110b20900e000034040c1e01c0040740d00c2c1e8454a0341405910102c84101c000e01c0800da480450001914040e1401c0340499644071924160300c42c03030711070152224038a0b914283d10440a9040c082d091344803545004a040c0c92396007403850903450310001e1110030310400803042c081d89015a003106503200d4014501490700070006007c0980021415071101d5014030b45219074565011001c1e52030512080001003040d00082814500358 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 210572904 1250 210571654 210571657
    0x50d0308061003111b031306050319090807140c1002012003150d15020f030109061203020706030c17090f0c0111060f040c0b0c0a021309031e02070f0b 66
    0x112002d50754800240e6051105034140d820405100407070101c14801c50f032900e030014490500d0002c1d110162441d1a11011a8002c020100e801c07000200b54000240b080c001075000343d103c40c0030b50980c0c2c10030030b100d2142d0710110320b84100c19000e051841d03500101c046d41c8500f40030404141400030040b1848101400d40607000c1c04400020500d8007140380590855848540b003107034070031004c0100c99914101800b040000d001c8500d50140c40100d030801854580940c9840200755113401021102d8a03989002e00c824240c0d405500000c40821040d58a400001e400244002c1600c14505002c6820125a20b088440c0343c201d040360365064008000f40f00b0300600100707400340c84026500503030701800c0c42c0ba40151180c038040d101c1c05171541e020324001141e000361400b0040d00148100b0803108441d030b8484070743d034654101d00900320180d000242040114500511100004c400d14201484515a240c40142a20b07070003001a1440c0b0111070315044800f403080c0300d001d0140c440721020003003c5032510042a1301c0d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 210574154 1250 210572904 210572911
    0x1e051503010e0d080a0507021216021905010c0b0c0915071a1312021c03020a08100b0f0708070b0708090706092403140a0b13050915090304050d0308 65
    0x41d5280c030004211910010802058140c40c03078403003090780d0b110601484001d080080155085000c0c1c401d6046140002c2d0303009000385615030b00302d0a4000e101c1d0040102c001c0d4900c01442c40515040ca0821840c0d800001042c101c40e0803200c4c03800c1036656126202c41c3c511030380071801d9200020502c503081040700a0060040d850003004014070b19080703001c100b02c0d0380c042071b94a20704e040d61510f8080f00143ca051503035400101c83d481901c840c442640d8680c19501140140d0304042600404c11035071103640030fa4100d074001101c83c0d6040c1c5607071403e80c4546161080380046501140001503103400c3c40540d0003100c10440d07000322240120314100c00020408041524030454034080c100b4001440c5205125070b000b0344205119468070300110002c0781c0c130851203282312001855161080c806044200380800f902c9003400c03075808101240c42804120700703c0c0c1c58a0120b00e80b90703e058140b10b0140c0b4006030a00110050818a01540d116500540e1450040781c0c0501d40c080440d848090030113612104c1c0702d00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 210575404 1250 210574154 210574159
    0x71d040e0a02041e110307080402102a140a0309061d1305010e0c0702060414030c030607020c040b0616110d0506010305010903030c020f0a02060a030204030c091a010c050c01031e0515 80
    0x10010f003580308851a06c800d85203040010500c40100d00503203480f01c1300c02e07805101418003255100384c0c0034490300c001a5030b100b0500c25105804805040c0184000c44034503200d94007003d44004d891039900a00740d44007a00811040200000d482d031150010074116180d0580008c0940c01040070f103c407280d018200034001c580c80c500720700c0040b601e4580240243c850f1154014800c4d030509040c108101c00c01d40c92a0300c070795810b1007482d81a41c055107050042c5409000d141d8054003002942c00c043c40f00392445040c541d40664410030084299049900d82c0d8240b00c0c0d8171a030f0754000b40c803000c00040c0380182c10f40e001404a00498000004000301580202d244921a841c180301d94840324070b050382c07600c90000450b40140c12044144005283c114018004074000d41001800c16899498109004ca030f00d8101c1421203641d2042e02d0440c40f820380c0c000364558802d1900b2610b074a520358806854202c1b41c070030181410b8560714000c0d140245002240c1c2c0c07a20507414100400d00d000581020003901c1549201e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 210576654 1250 210575404 210575411
    0x6030e1c03022703160b0702090604063201090e010312030b060d0e0d11060402090414030705301215040509100f060b0f1606060303050a08071d040e0a02041e 69
    0x1070700156045c00b20300407100c6120450b81051096000e101003201d00518182d482503885401154481d00b41940040042910301011903000e0031070150040d8003c240b81c094103000009000f0045054140327840c50640e46e1000c203024551121714001c0c0c01070030052000ca80d20170300220345003075140d44a600200010b82c1800448802d0724460800f40d5030602c1944161215400100000b0701500746020a550003a100b201110074059141c0203907400c0d44c221401c2200c480e0400105002c02d00098203044404080c8200354156031480c495440358184180c03600184402c0c00740000031a410400e408914007554041d02c14800d45c900300c00500d0b12542e1054128190a10300918180d0510948c800c0b1010303103014120700740ca4159110124101034000040c0100f01c0703020b0f0790a0388001001c0740221801144280c603440d032200304084002d005000020040b4007003086c00000d4100954100038a066030340010395001455000341140e40e81403c0f42003501070341081c00e06480700c07042a10800308040c01c8903420400c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 210577904 1250 210576654 210576673
    0x207050405040201320429090d1202030c0102040603020409180201081b192016050d0f06060602030a020c011b030e1c0809090106030e1c03022703 64
    0x11007115000c0d82c0182c0051640e008021407880c1024103d610709502c0c2107542e00d034003141e81c1100d00d254040d0700850007001906007400d52a41407440300c0c08040607440d64a42c281540000403c3c81da112108025140b04032114984254a00038000c0f00c21b0100c6600c000d65031107480b0407025010798068416240528948510050402020980c00d100c9c1641651900179507100c6c80852110b0071091910005864020090700500d81e40142408041c0701440d140e0002c0002207041d41c0303c50702c00070342d5803104503004812265021110030039a801603030340840e03240b4680422414100f1207050440d50041040e49040b0000c111260000040d113121186982181d030801095001110342941001c251b2010002c220702550020380160302554210801401466058030450740e0325403800352407041640c00110004d6140d1840c20072040d00c60142a0b40c1c1001c9c032200c1c10030540290344848819080d0b1090b8443e080e10303081284a41c044940c00c218040440a4403404441000086c04401012510070312400d82403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 210579154 1250 210577904 210577909
    0x30209090c1008060109080304151b080409090311060a14010503030c0c04050a180303021312020303090f0604081609060911031605040e0a0905010501060816051b030304030c03020705 80
    0x200c550751000d0048511080d242200780c03560180984041d042c08880032002c02d00800800c0940020041c0310344541d411141e02401030038210591750b03c41d0130790f041d001c800c0340820107850485048583c20a00096141240d04027125815102029a2402d0040780f00340200556550004000c020301c5048148080c0d1341c0b44105950b0744100e00c11a80c0980220803a8070b4549420362000d40e00038288000450601001e40c400003800c181140100d011035404942c1802800c1070041582c0506a0044810613804041c0c000a9482c024014000c1c80703003100e00b000c4007041d1138000c16500103001a800300e944460100d25601001c4044c0c2c0038420140b450488005896640d50085590f0f0285002d25945551a0020080d14140301582103005200040100068101d070034607509228000701d64002440b200607241407801d448040e03014134100803004007031002c011a605c480d0103800b140c0341031080d580c4000e000401000940d172426105640004003c00c0103260b00442c1c1000c4140c400d6095500c0180c8a404 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 210580404 1250 210579154 210579163
    0x130f0b030f0c01030e030d021308190b012106020406050904111602010c170d02030a0c0801030206031503100212061002060906040204050a0f0603080913021e13081603020909 76
    0x860000364002500d800283d4040e5202c0300540c45940c00b501d01d07220f51351814000360703406050702d0105228201803c01c010766007880b80f030110140c0b941441c010600d6544445444c80010301070b40c580c0074041d801030710000005503440d21407140d02160039500c0741d40e141d80c050603a40002e2451400f982c10241c0070f2180b1303900c0700c00b25001440b00c2d80d40c69082d61116001112607c03602c51044580d00e80081c0680342c0c2c3e1940c0c070042d0454070943c01c0050fa69240460100054030202c04004050000a20041c40141e460030196548204140220034070700c0a03460019117007460b260381b5013030f1462000030601d0700e80750302401181c03140c4030075035140480340403c650881e916201211502c0a80c0c201e90007140040c901500182d400c00742e110f8000c240c100610f590304080b1000e40d40300f1120840e00241150f0300782003094100c00c401e40548030460400b200d40340e00c1c180082c1c40f14000c0090540002c0c2c5070700306030303000f51814000d05401400c50701044ca402e40c1c54115034a060106a104d0300603640041d601010019 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 210581654 1250 210580404 210580423
    0xe010f0c0b01060807020f2b0f0f051e03010e040209012111012709050108070b0702061608070803091501080a02011d0d0f061505100e03010605130f0b03 67
    0x2805081c0681c60490200c070700c4c103005070014086014840f9a080c02c504104070030621186121100407001d40500603101545562428650611900308030381c014031a013044081d480d10290b400c01b941d071003022261070351185003110140500c1300c0000c030011544040380c806980c4550700c00c5d40d1030140399803600d440803a5030224404500c81c2680420039140054809404031001d204103040090010310860003480100900220010200b401400d0800002d101c601450340100a0000a044960701b032251002542c8504803000e0300074080000c1d0a019100045480300042c0e80120304c5a4883c030321460310410035401980c2c86600d5114601d03a40f664541c00543c0f40381200e40303800003082d500781c0326401515094003426001e0f484140d80003101d031a0b919000302605c0403911803840001e2a1845103000310845100c0e41042118050f6440180029101d80f881c2c02070740c1880e42000300050610600180c05824160041030f00011506007040388503100c0d821039050341401c0d4000740a801c10040c14582c5d6540c11a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 210582904 1250 210581654 210581663
    0x12050601120303060b070f0203060a0b0130060e0106030e03031603180506011206060f150c060b031f0e0a0803060607020303070506070c020114120a0b0418030e010f0c 73
    0x180010400d84195881c100c424510a050102d1031540e00c06044146400c1403200303403017a4500448010840c6014868103034408032134a0100440030f14800000d218403051204120005c04100c002d09150381c454640404030f000d011414050395440302c02401002800784035a00110781821000f9900c10804020faa100e40d4511803892110500300504030b014080081800c140781001000c1240403403418403807680078100e01c0c45c440b180c190003840c0002c203d8000364000011342caa001014800102c081188514001c26413501d106012102d0405000520f240034043e41d242c030614050803410640e02809022140005400704140300003481125158149070000030a030f02c4007000080d007146803040181c02058005002c59081405075601c040c0f07040c5055520002040c80040f4a004640c0c2c80000381d03942880184a19091003203044c0150007449014140300d01503600c440c8200d506854a6100710090110780650801d1000b1600303003d00300c00008440c407030020740d1120b000707020b840c0548800031005620 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 210584154 1250 210582904 210582913
    0x3020a1b05071e0305210702090103051f0b030c01051b0105072c03070603021c09080919031a13331a090a060308040b0a0f080c070609031107031b1205 66
    0xe41c0030106c082081300041d0300b0240a02040300980c4854a095001e9881a002000806d0b402820080200c1080144030344060170b01008640d59140842c1c051000705081c02d0180d20341c03c60540d00b855000c48107110000961904040042d8140c1c0100b10880c200c68203050255980c6006004031062401c0301481c0e81c0580c810f0b4000c11060388294003c00f007801240208000d801e5540f0130a8080d030384850301c140c030003c0000c0f8111405207031000c58028009281e9000c50f1005265640324071010b88602e10900c0c0085042d0b0000c3e400b14941c1c500540c0ea60b03480344040202d1045001c1c040c1000700c04101c44010020b407001c00110070991486074034000074041000f84000d5080c90100304a06200622092225899400000020f0240c2c0701800242603108100341e01c40d030034800014020101840d01c0c1d0300300032841050103400481c21044800c001c1d00301001090403107180c01c040d04e03000400f45a000892080240002c18841d1800101624605d0804c80c0d50b00c09950f0f81d16890202048080500941c02 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 210585404 1250 210584154 210584173
    0xf0f01020a0308041b080105010302040b01110709050604060e010e160f021002030a06050a03050307140604030c2015070b0108030702062512080f1b090103020a1b05071e0305 76
    0x50f8000030b5116104040c42d00442200c0300500d596001940d1180b45560344072001441145028000c0c008948001e10741105060171300c070551550b0311028460540f80c03503991230202e405a10b0301d80000d40030b00061840542c955030b58078041c002244040362005c0d96071000302d503001720f954440c445074a28481e032940141030b290a0b402440c4020f5002601c26262103640d024001050f403140d04070743c00210b01440c061034032503a6a0800c2d28a5210f8011020a9600041d0030400004d07004000c01c104580c10202c01407409001e280082d000c0c001c1d212503168840440e18582c1c1600c60943d0080414a120304030340d1410341da07201e880a44e24015200d00a61201e0140025816541e40c54070205c10103800301c40094140c0102d803a10001d0703100085603100000c101d81b00b001041340d5500303001a0014200400761040b9250300500d005580141d544460405030000703043d0405512618800e444d48944a00482c42c10b401450309690f00c0380c0301d21502c9810480006504420400210444122074108024020002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 210586654 1250 210585404 210585407
    0x9040c05062107050703120203060a1206091b080c010207030206160309180906180f080d0204030b090a03020606060c15100e1008070801020f0909130b04110f0f01020a03 74
    0x300540030036030000031400401c586094200e0742d0140600750a840320b550720440c1d803c009040c80d0404680d111818010828422680c0310012410102c5800e134001c01c20380b02840c0b50600c040d14614401621102d018500460301c0c0d40728044c1c51040394190305c203c80313202d400c2400580c0c46007414800a54044014481d90b44030700070845510f1107183c42440c080c80000c1d00c0e46040070f102440800c1d280f0016940d1102a42082050f20460b0741140c1c03900a0281c5040c250354803040e580f03004281c01852007030301241c0a480780800c0c0d015240036585c0030205810a25042500c0c48d503d07549510160018404c03030340440c10a080020448141840c80005006400401400b0801548001e010114080c1c540e40000440c2c000317018510b8060702d007d000070301c50140f40811480c43c168840d0040c1c48a64070400c55007404003442400c40c0e2140f4002c4c4c072504059039441070103003120740303e00030044e00c8010300b0020881004242861a94a4901103d01c12101c030413500601c03000c440d03010b5540d80542c3c402c1580c0000300f03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 210587904 1250 210586654 210586657
    0x2041d06011211270d1208150609190f061d0a03021e01050f070302011a100c0b09030c030f1c02040e040f02030a050d03061703030c03180115060e0f09040c0506 70
    0x10540050000b441910131001c903d003072040356000d40c2d2805805c082d80441c140c0c000e40f060f40081228022881d145920000034440d40300307030440144030f18140c440c140c90070b10224070080d00420004004068080c3d840034040c00c8010070701e42d010384550400c40c0784400c600d4001034610a40390050181181e018100a103408030300d81ca0b4103418140710090140e441203030b050030024001035110381d001103280191003c1840d030340c101c1201d510384144181d01d44000203d40c00080011031301e802c0f04420441e9140e040d00745080d40701e441c50707251181c0000a140902800e800c4010210150b02d080c0c906103001c0c165485108034081c1d8021407020b0200b40d4003007004030b040d408038102030701d0000b010f8880800040d40c43d00c0c900318030f460310b4801090b1036030001c000750105069030018284010011714070350302c0c0500c000000c074031009141c8420070103900b548034900007095001e031410702c0e43c940b49042c680c4c0d1070b480060710b841c0b00403d82c90b2140d00925a5001a0700303000d00e020b80038541c00345580300000d00740010000709 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 210589154 1250 210587904 210587947
    0x30308010f0b03160c060501090b0301050906060102190c0b120f0702030f07080d0213030c080c09060303040302040c09120c0509090c010801140409060203040f0506090703111302041d06011211 84
    0x801c2174500300c1c28082405407080a0003448401400071f4146680c00606003903a00082110100750400c0c420805030b66000f1603803502c003075030292038007034443d071503181100c20f0301d0454100c40e1700c1d400301003403500e440c80240c41050700520480e643c040e61070b038a1090499480c469002e6100d511002400b0500c0001c1490000e01034100c808903000d030a107480e1001c58004980340741c0c4150b4440741010002c011246051050301c00c0c0240980d01e44040b442c2440c003003542d81c491440001c0c003866642c0210395905e40714a61034000b40104812049805180e81070081c0020403500600384200fa5800200320720010005114030562010307164450203a2904403c0a00d064003050070581168491600e40000750041c4003c510580c4194124a518800b60410380d1400100600341501540194801e202045d0300480406a1040850b80b8581810001c001d4202a00647c1e002c0041c0903415007058242201d2111110300c00c420030780c0c40c4904440102d0442c001e40700c80c100344042621082003550018180c10008003807 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 210590404 1250 210589154 210589157
    0x306042712090503030315040b04060609300803090d0e13050705040b0c1506090c070b0a15090c0e01020106061d060c0706090e0907030312091a090304030308010f0b0316 74
    0x68a0340c2e03c41c007007030456004665a010106100035170402c2880c144c4180300a1a2058404025050501d040544004040d0291040d040e16207010742e070030320071440c400309104048a0000090600c2c01d00e030542a039001034410200a0141c0d4041c0640141301e20301c000c1800d80010704c245120039501c0807541c0245000350038003003040700801010812a005100030240700701d07500b0080501054000d11200001d9014040900c2907003070b0401e00040d41c3c8400c081d11445500003411007802d03141d65040100901c2200e40d003410801c1008400105174005510013505d4020a441d840da00b00811001242214941c1c0144800f0406588900d0306128001107000d42525010b89250324182e41094054070b466000d03407141d0001124582c1c24000b034030810b40225007152640004041090840d0360140a400503510700c903440b10342c0d404201d002c0c0043c0c00d8003802451400c2145e4011400c21242c040d0303c03540240000d4010444120000810a0340c401c0741d4000c07038980c9d62581c2d05544540f1051a4514603e40380ca40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 210591654 1250 210590404 210590417
    0xd06140d060c180620030c0a020603101d22120309080904021210090b0102030703030b0607121d030a050c01051308030a050306040609050402010914060c070b0306042712 74
    0x810800040c0440004e0f00703280d1101d0074041d055003010080d080c0c2d041c2039105c4c40e0b0000d2012482c801c03800a0111a02a411640750b80c03281c0d01c54403000d08082070743d40a000d10a0070f8903200580c03a1141200180208800410112050400d0120245030440090b00805c1140c4040e0185186403103a8040c5400510840c1e109240c03061100000e0309a8110b40c00204411042c4400d00600040d001c50080c002d24030700b00d01f03201c61181c0e11300207034a0740100e950280034903456441c41055a59247d00b2918030581c00000b00324140280c3e03000070005145c0c0c560042e0912a807400c0c8103e1803800280030800558400c0c020880858030300e00440d225080b0a5503443c56002034a8085420141800641200481a5581074a900e0108100411f8484591022096615220a01c000f60340e00c14031b1001612400e11940c1d0b000210800440d80364840e8042d04040c0340200000821044502c0c2c0046000b240121000e0114016048810311650b203446110850310031009048000620f100e12020a900500d081a0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 210592904 1250 210591654 210591677
    0x40b04061d09010c020a0512030a061e051516140c0d051507030e0312090f07091d0705060406030b0102030d050411030106061b02041e110d06140d060c 66
    0x4401e5004000030030070790000200320102e0300c24440e283d100303811840140a4089503882d01ca44910080c58140e04801b00000051982c41c11070300110010440d804900b40745280c0520746064100703542c01200d10950180c00b0092212160f00d043d2008520020240032410410360b90b01c100356040c00d407041c90b2034010600c01c82c8103a6202042d6408150060307000d4012514043c443c0820120010001e0f0185031402c2070325840488000281c0c0e15a54160b560f551550b11800f01852812600342488002d510034440d0105442c035554010b1041e03112104500410281066a02601d96105018603504070000b84001c00083c3d111340c0040f080a041801078031b00d0103548603860025220104c90607180c2001106019000d410300340b150310001d01e5a440c048503428620000118848074240010381b01d82c0d11440d41080003801c44803034981d2030705284800c10070554805080b0945800560004601c2880d0200c00186502040d80418140100412030008202d07280c0d12000148484c5c4852001c11118680c81d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 210594154 1250 210592904 210592919
    0x13050405090a0b0c0a0201060608040b0708040302120309011508010902010e0919050103030509030d020105010e2802032703040305031c0b0a030506160903051c11030a030213080109030e040b0406 85
    0x441c01282c8204000f581d0b41c45e1804081d003920380729840142000000010007010900d408205900301040b89403400058507282022072500b4000704417060320400000600c2034a190540c46000b44442409094840303c2c0c4c1c030080c0c11300321004400003070701092940b840115103203071416155611a070123a0408500030007032180d070011200c00340c00490100d000003400d1803891908210080e2000f11610003030100798100000505041c201400344124003001c14824400f60b86010414100014003490454407440d10b00c180c0d403c01d11155008403006000c00e402e00c9000c9102108a4040d660403000035840e04600f02d80d44444074010040c101d1200b03995807810a00d590700c1700881c00056019500400c00f03070920010300ca50f00c100c0d02e070140003804002002040010300c045202c840c180ca07081c500e0700900d551101c040d29140543c2400342402e0100040544596804d58013900b007006003196480d03041c0d91148882c5080ba4402440030b0f0108850802400c480d1515420810340e10741c01920100e806684d0f07000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 210595404 1250 210594154 210594173
    0xf032d080a051206041505060f07020d060912050a08011a12070e01031104050d0f0c0518040605010902090102030d1e020406091e03170a02070308030103061401050613050405090a 78
    0x5040051000184043c43c40b00c1026840c0c2c21090440d0104000700b0440d4040341200118459180500c0011596001100f54902901d81e00c0e9000b5120401c03849151802500520380c0610880c3c200b4a000314442006201c0d00035944030f03080c1c51300c0d030042507400d080240c6010106000101c40c1c0d0902044050680c0d056110041c1c010402c0340c8a1564100b0301f000058144c1d80001e1981c80d00c0d84051004020594481181640558100801d12010a200d0820b0b031144202508803c2d00008421014040300c4680c0d81e0580c130a5024030303c01c0204d030340c807144944168851480b400c3e005038414001c6000300101544030000c1d4010140c500030f00c100c41d04500d0b106a8000790b0017900407880701403041117088403090300c94034600a501a09020f140c01c6603555080311011b10380074003005c10b0108010400c94000c00641000c4d40d089a80c2644075a5240741c4030018220031b500480f0b0b2081da41000003a2030908605962034001c9880c4d120000c60300b00400e200c000c00e0020074486442c42400401c00c0442c06058 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 210596654 1250 210595404 210595417
    0x40621060602100b010e0109090f020d0c020d031503020f100c0b01080708011512030503040809030601180b09070807030c2a0203072306090301020d1506090f032d08 72
    0x40260011003034100f2a002180e5840c0303190760501000c45d150000c81d0b80c0c421344440c02c4d211082000a510120884144024025202030b00c2c0100d00e042d00d00000c1c190006612050604c00e0f542c14021145e4220301010703000c100380300094011094075907080c420f181500a0b00310040301840d01d40d00407122611641884102130340020500e42240000303000301c2c5028051612842200e6401d694960319191207121440c0b1180c1014040180120106040103a00d40498104e280010122226940c5036000c06d0000c0d075090304c1d010312484c42d0520810384ca040c01051a07100d0a030030340314000d0311398401c03509170045c0003079030b511708100408400d5050a52940d9448502d0710401e4000003880e464503803042c1841c20742182c00005d001c91041446a03445840603110b18041e600660700e080c1c0f58811040801e01a014500b41d2805150800c007008e82480c81000b01c0c0f00403034102c0e6540201d0f6981d55004038854060398000505100c180c01d0040548891640303424581c0c000340340351085d0340d61003600c41841a40040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 210597904 1250 210596654 210596657
    0x703110604140705040603051b0d05010603080a090918020112090b010305030714120403080a030207121806170c03100506030108030301030b100b0909090111130512120406210606 78
    0x44400c03404002c1000b410014142c117640400c80c0906503100c059540100c0e2000b0078100c40304000142d0700d51030322441c0300f541562010080c407103542c6a240c405401c0d0400504100010070034000080d00c031919002d4240005136130205c414400340780c0d400449124050710404900c05449656050000d544824003500940c010005103131111502d240904071003d02d868004c0640d0704c074102c07000b500e041810071182204d83c030550103a515600e5041c154047c0c015080c0c042c103050003c1c2150300b00e80d50800c203141c2c002003500c29040c690986460040c0c841c49c42a280c5010b590b900c01c00042d0b0f61180c203100650b0080c01c02c0440d0400030359148002800c580c82600102e14980001c4010000c00440950b0150030040408120612608051601c5441d000e06042c1c948621200c20120310404004e50002c0742401c0420700e019912003a804850380001343c60b2103403602070840d104601d841241e001c00d01540301114400d04501d0249842000c90750308035000c0680c1c804c03203640303c1914442c3c2c10b28428000206245d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 210599154 1250 210597904 210597923
    0x1b0e0f040e030f0301053309150301090b03120a0504120203030d090311010507021c031a040c09050102060a050403050313110d0b04050d020703051e0a050106060206041203060e010603020703110604 86
    0x4046c00e100d403100030145402070035003549030b1096000d00c58800e4104107a4281d03c030709846619120004d41e100500c81d00e400303107143c0000004501c40c6116000807020150640032540403c42c94511340c41507210300b176a8000004e406003c144042609142e0141c2130a00040481307051600c00e034a490100c40d0000310232000b0070f00080250404482c01c2c00f891350302961070700162403881d1481c01095214a03172001603100300b41e5a060002048a0060b8075160b0001002d80700b0404103110700000f402c012514020741780544540c40025001d15068000d20b88a6981039480904607292843c41850769403464408980e180084000c645072074031825880e2100a02848408006042600345a404c041c1410510b6046410014050000c1100010040400443c1c5114000c01c03c084e0a12203080403010b50005011754204480020b4860303001407464010350081c5032003680b85072800030950480b0164030411545656071401007001501036405011420302908040c00f00030815040305041c0641180e0454a0418 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 210600404 1250 210599154 210599159
    0x10602121b1506130203010311040c030e060108210f0403060e0f0604060218030102030609070f09030f05030705060117070b0d14090706021c02060406090804180509011b0e0f040e030f0301 82
    0x10400f0301c111940024850841c03547d411a02c3e90038021544841d064021510f41700743d80039040c8244d02c107403c45404d81064409c0c650b15400c020ba15111120441a005070820940b0401d03078403031204442440f50b11480340b03480c142c0f81da55044040c0800c605000070a000c1c0001544045509000380380c0f0440c4a00e50040e611798405049084042506102a002e0381c814010020702c1d8540190017038200d1160309011441c011050402c03902040f042e0070013042c001d4502002c40800c000040540182c620032400c1e502e00c0da80703503030401458817800603002c111540b19410410118000d0b030003c01c00c40346412804500c1088102c0c60b030642400a540001e2150305c007100410115505100c09888000c0c007449070882041000e1000390749034000b074409040c040e2b5500400c1c007004081c1c4210341c000d08240010500741c880184198000340001c0700c3c440c8040d42402542c144110201c1460411000e403a141c0c081003800d40c8060124004040d211a508240e95030013503106004200033900c911a507086042c3e66030f60 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 210601654 1250 210600404 210600409
    0x111b1503130c060903020f090c0d0603061b080402011407050313080c090a02030112020910081903090608060d11010e130b01030f022a160f150206010602121b1506 71
    0x242c154400b074208000c984007400140e44806040443c40e004403030620322512030325403000c01d034406c60070306409681c98154008100b281a40105150100141200803483e600e090300740c030701c1401140e000740040e14900c00d00c01c0107164980030b400f029015030100c0b030030100e608482070089981d98200380d42c2c41d0b11410241103289400c44400381d000440c00415070865141c11941c0726140c410080080c45203801900154040d042589004002e00d841000c403032404d1704101007072600b235071001c030140d000680c1c80c0000700700140920000d40c00740401908001210a07192980d070045000d2480d0681000700200000d02282da602501340c02c18500c0c0c260002c0c1501c080b00001d0100c440c1003599180c4280180018120600c880410000d1400144000c4055000020f4002d0410301c03100443c5440f405009002b056030300414904074141c0d50030180f5503041c0301d144c1000784c0c0e03a00300900c11100103a00070304c2c80059490700b80010f0500030704850b45250880403161003403400c1130030750b0a130301c0e9005070701404210161 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 210602904 1250 210601654 210601673
    0x50408030105032b030c021006030606050312250f0b180709060312050f21012c06010f020313030b0702010b100807080606040506030a0e0d111b150313 66
    0x130b419102142919100c1c4400403088500c0e9408039020f05035180300300da0101e03000340030844854003c1d4408000590710380c17038450018240d50066030b019101d52528110b07240b85900131540c40214100c1c250b035000510405041c0c20100243c800c4624000018400000803490051680200f107132001250708040c20311155403801001e0b60050704550f081103000c0010469920b403403003840c0400c0c58429a505180a40c3c840d0501c151580e10890f00440c02e01841d240e183d070380a45050310a158807a403601d101c40c520101e80e40070f0415684100c0c9000201180701c541c01401c3d04580440207006503803d00d01000a00c0c9002010303548281c5950b59041d04010b84168280b040d8224610304440080c00d010074403500800114005100b0010321480d0700c04101a541c807002070303030002d00005001c0d03542ca10b0302c1f60703101c0040c09000d00c00c080948190000104101c0c020b80f10f850a00500c8001081d90008a43d00d605545056401d116007000d803801402f078680c20000c0081d4420300418060400d18001440d003400b21 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 210604154 1250 210602904 210602923
    0x2606180c010e0d08031b030a06050a05010e010518120d020a0c06050a05030115031d0d080705160213021b1b090f070503060411160201031805061305070905040803010503 74
    0x4115082031140c000f5030361540210a40e642220805440b1358426100031009085544003010205002c000c10803201c109030440016504140d0746007214981d50b000546a603007501c00710901003074086c00494414892100140302c1207100500b001c1103040210308181c2003803070003501c240041e0000d400010074007880103080e00c0280610324107a440c0204c048002000750106000780305800c0c00d024485500c40780b09801040d03001e11a003420000b01032248441d6984c40c0c991095000101b80311100040c1810701440696001c14403031080400c868546500b001354041c03c003024100700560074400d60b00485400305442401644940041072503607002c1001d0102c103082040703002c0c402c01d124000c0211040f1040c0c42c46410501c541003041d03c0b13841e00c500080103000e0503104203a0b03103200410b075581e03002e49054016403031900030788080000b6111803041006d402080c810260050f8000d00c00300e80d5400c40c3c1400ca1115a010b0400d440d8041c0e29805000d05454003910141d992000200061000340b4091003841c01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 210605404 1250 210604154 210604157
    0x614060406080606031003051204060e01030e0705040209060d02031302030615010e0f130905060601031d030901180803070501020702040e0a020d0b0705040306061203020c0114042606180c01 83
    0x34645460300042071820024140c41c00740c1004400318040000c07900090001d1540320003a6102189030210035141900244506000562499600e0702c10754001d110300d41c80585842c002c3c205007800d101c1884065403240c16407680040d020003101074080024800346004401d10701041d1039030115030040502c0d049002e4082c0390000c2031030f048100c1980c2c04c1440100200030a40d00405504981130000380f0107003d1400c1e45480500b0301c2800d5007001300c08205144250002d88003001085a0402031040040c00d12209485552082108080790340c00343e00111002c541040222810301e446142c81820b503000110200d8541c0e4000c69584114a894000d100d0b034840070800070041404550001054a05e240801130010082000440c01c03041c8501c08450246400c40f40c14000c081d6507441c003203032150b0010019401800703000c4071640d0a61041f205010002c01c4528001e007042e05081c0d502000ca08004801100090340d2107071101c0a090078032484c0d200e00001d82c11304100340c055210040c240380728221000d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 210606654 1250 210605404 210605407
    0x30c060f02030f030a0b0a030812040b0c040b040b090a170f120712030504030e030a11030609010203010303081b040909050d0e0a0f0317090307083003041104090b0703061406 76
    0x482100c0c141040d130f42d0086540001048507072103840410720040098002a100d06400a0001c600040415041d0f010718482d0303054040a55504070240c40e0384c06203004034031214004000400c18000340101820082d0b40003451584016651107043ea0700d101c03100d49a03020780d0041c0380070458008041c0a601221090ba03c02c8525283c0303039a2703d10314006400b03080001419584e07004601030510500304040c266002a08403040f4501c0390034620700c01c003c08040390b846849030380002400d9170418000daa0499906841d429001e407580803403400721120451200b58928800d10000405040b60b01071240c0181c00f420141441c046160402040c07007102c00c003c64000c028042007000410142d070210380031203400c40400d406000b401c1041c50382d148a0b440103607900d0320820a000ca11050085550542d078116401c0d8104149407500441ea06525a104807094003942030001070045061005506030200c030041001585e007815a80d4041c2c54003064480c0c0300002c0c2d89100c207000d034080c014001803a10a00301c40e0075 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 210607904 1250 210606654 210606667
    0x106080d05090103050405010b150705120a08040209040503070b0c0405011d1c020f060d020c10050105090f0711060a020903070603140a0902030a05030a0203090a2103051b030301030c060f0203 84
    0x307080c0303100d050507a42c101540c400000381441802e602c04203a5500080030840d02100031000344400d500050815141c0f4042e800c0d108030307003400c20ba003151000c448940f110495a5100e800b00260820014025505070000b00408400200c481101903c45c00034840240d4585042030001481140c54403424000d40343e14066136034483da07032108545012440086803603403404140c80819070100e01740d030700503411000c00b10b004165031003550044d1046c0007000003101c0e010100441d0540640d00c0a03c0740301d03001000d13540401d0001881f5041154003040c14200000507010341c8031070501c0c001080b1035007034400341d02158003011407500b4007685004000d2850b0a204284d01481502500b90010309070440c0760307030303140580011900d0034011500b05641080980e03440c0e14143c0c0c40692603030301801103d0310540382090041885200304004a15031100942c0d001d221080a5600781c81c0c41d1f1200f07401100001820900820785641000154040d41c424400806001d15101c805458110881300c10402d40d0424802e8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 210609154 1250 210607904 210607907
    0x32006182d0a0206040906150c24020708030403080403091203021b030a02060f03040c23040b040b040e071d011a13090203010e041a060d0206130e0f01080106080d 71
    0x41000c0e941d000e05020042001a040701c034500000004000d402c03c20200300000d11806c2584404111528020003005822803401e0440d08000114001000d041c071210b164100d0b00f5580c00d8500d10f59907403000051a0074074a446004107a001110b00310005100c40b410481019808041d6800906a04500e20708240032079a02075101d08000c0800c4001a5524001041590701001100041500601400c5d50340c0c0440800c24569841168203552845500d4030002d98105180c0002c0100e01c5151310080103660b034001000042c1400d010030550142d16512852441d945900c101d040f4152998014400340d494132500343c0c607090301903003074040440c0c00c00c00422104401d644043ca888d104c10718403940d03030190760032a000c0c804c0e2503401140d40c2d140b0110010414a008a00c2180102e0003804d640c40c0142c04000304880c540380440c2c465800c8045454024018200440a00b40219449640d000280d4551040100f50071040b5001424107640d08010442d0703550a206082c060001d0784040c01d556018030301c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 210610404 1250 210609154 210609193
    0xf0c030d030e0309120609061b0306090414010c030f0b030604030e0d05010f0c09080f0c010f1b020d08070201110a120809010e070602160e0114060703200618 69
    0x480c4018507440301d0310990510750600464100c15030081401c071820002501c1ca0740e0f500411a0000106d02c00c04000c54504101100f03044c82201890300100c0c59555900e05001c4905806401215074090655007082a40750a000310b006002140e41c0014041c88075840c808144d8220380c1450f400f94104e1410f00c030110398092401d140b0568203458616a0070098606a40140221841d040c000d45c42e01400410f560b60003400c0d401242c80c00b0003112151280a02c0c126156208507161a0204441c482c2d40880325008840401c800c103030640c1c04200b140000c0e000b05a031104408021501501700180120841d81c204100c5041800503074001e0486558642d103548012007101004014032201d0000540601c209400a4002c0b04d6401c00ba100d04c141d5600029581e003854811152030040c80702e4000c0341c0901c9002d180c0b03040700d9456038072082c407102c14410301c00954000082030b81003201e5500598003401186040109065100700240f0351440d021103030045040326440e00c040b9a8004a054001e00a040d04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 210611510 1106 210610404 210610423
    0x61a010906030c121104170c0a1508070509040f2a03110423101d06160210020f0a0804081005160c150603050a0201020f0c03 55
    0xc010b8042e41c00c10100304001031003500301e6000b4220a6008045241031a5400c54907258851520702284503080740410301c20360100010180506045058000500b10301000316205406020000c20f036141c0070b00688200303c0c011440d94582e036102c0e4480f1b40a403514480801042c48042c902500e0402800d4005951500c0c50082c404628064043c0f105014007081724070f4034081c01c04403811000e201c125640007041000220030001a00c601c07018188043c543d0710b490251482a801540121030361442d2a800341d0003d100e02d0b0b040c0810440104080e40e41126042e0b80040403000482c50280d8401956046100b043e00306e90a21040000420035195108166001e2a00f54172014054460517141c40b40602d2082e40300000b032a1007600e24135001c43c864041480202e96001e00749064501c0c51b001540c16401c4412071404543e0100210710756100903501911902c1b1600f40002e403139000f9030 = true := by decide +kernel

theorem cover : BRFrame.Cov 210431654 210611510 := by
  have h0 := BRFrame.cov_init 210431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 210431654 ≤ n) (h2 : n < 210611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
