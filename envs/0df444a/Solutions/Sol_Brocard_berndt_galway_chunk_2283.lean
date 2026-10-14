-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2283
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:14:20.039194+00:00
-- url     : https://prove2.me/submissions/4795dbe6-3ae9-47da-b064-1d0f0706ee2a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 410431654 ≤ n < 410611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 410432904 1250 410431654 410431657
    0x7061d0613030c030818040905030318160306360b070c0c0e04031d1e06040e0903070c05010e01080c09150c010c0215011a0c070806010b22030305040515 67
    0x1103074003c07010702c0d420303441e400c151505d42c1141e900c550f8000174281c03051040342003901645001da80d21400a6007503840b240302c242c00400700c95500c8109842100c03022b400446141c507640c0001c0d401640006500092240000a018210400c20501181407a07041e40c0b4042e01200214410760032421102050312040c2048403624000302c4040c003143c26406012034030640074915640a20721a8a0318001c452000300649900030503043c62552101034150b504c40007916144080c0106a4010040c1c1d142c541c6401c0d407010010030a8428126a0707202003000c0003003118a95000c2c0281030242044640c404d401c200003001a00f0080c1401c9548401081000d6607407280f2600c0903941c08480a46910f40d0903042025008101c0c6c4102200103100e05c14000207404511070100e03050300c182e0001c1055041d0707016408060341d444090301c2c02480c41682000105a07805101c81e90181c282109860b641e101c00b9942e66454800c0f411540b8120f2100036010400650408212030440d038096501000d0f50000c00b032203100a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 410434154 1250 410432904 410432909
    0x503030a140c1e101509020a1b060c080705070803010506070f050105041b090603020d080f040f03080a08010b0a02062d01030803040c15080c0d0e030c0d0207061d0613 73
    0x100d1240c8a081482400f020402d074003120b04020844e140201c11a0164040d10804ca040303144240880743d050000c0001c0e60020a107403602070030f2951302c3d82d805400702106501050001e03203c29644d011849441d80d0701c0001107800014503d40349003001c03a25101c0504510040c8102c1e4810500043c041c002c11000ba0306280030190000002c0110789480c3c1001c8041d4462580c01032a114070b01180420001024441d40e4152a0060207036440c1088035507a101ca00d5020350194640c1240c1030000083c14801c065507100a144240062612408800c1e0054244513041c0c108412500061090035005c641c0060a0742e40061201c069600d0242020310b42d104141075400b03080c8810000345e00200501035140c0003140101e104070001c0c8003265940b0800c09600d03c040b9004000240b40001080c410806100503001280c00d00000080d1440011120380ca564070050b10342d0550f030032540500142c07640520074040244103506100f41c000d0640c1143d0070301c001c4d00b603c24a1060700f020900032818266004034402 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 410435404 1250 410434154 410434177
    0x40501210504120201050c07110409020a0308041205151e18010c08090c06040b0a050f0f03090c0103050f071215050301020a1806020115030b040614070f11070503030a14 74
    0x300c2c107007820b0820401040f0000f0030055070800c4045034070311100d070040340c1d0055042541814600109400c1002030008140c0903603008a40c0440400403404000081008212100c894080c0200034030303149003400300e8442140c0300240039604224103e041040741c810301c45001c00303414003030740d40c0d000000021401c0c6924011a0703600c0c00c01d1003800e680d04880c049000d500e03d00100e40b50075040c5002c0000d1b074807443c007074241d40e90f805010ba90110f6003c2c3d00646001718064400c58103010300c89100711655001241c240d45d0790790041c1402036855070036220b1150002200d031840303100da103489480a0a10380401d03140c0f2403032583e5031645a00c0302c8051080b20000d040020300940d51403011103030082c500d040000b50001c0e6003072040f100207070040c01445400070390300103200d983d00070314a592117254200b800100160750058a502c0d044014586503400f040c815101901c402c441200e4403103004040300100311980780c02e44d100031000e10069a0002c10f4503000302440c80c060b010360400708800040c5008006981a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 410436654 1250 410435404 410435411
    0x30f0612070602010b0918070b070c05031902010e0d020303030106051303020a08070e070e03120a030f0525080c0909090f0d170a1506050903010612060b2404050121 72
    0x150700c039410f40012445c0c1d24200c0e00040f090304d4504d03501540d9101c850f0700c14450751124000700548504003002d02807160091034103490f2203032f458000c24100101c02e100280c416014007143c404540e0410589005d04030b042e603400b00b080b452076011a036039110600929082c0a07010810201034a0460540b0000d10750141c4424503a40d61245d10b65620107090040501c486c0c1c4000020742018443c41d0170813a4000024010a01001d14040f04180c4d80d1102c0c1c4140e08150312100504401101400340710b0003400720900040c1107501d0710041c0784518023808603c2003041580320034402040840c5e0241e034801c04d011106c1309083c0c0c48045026190240d0100d01070045d0007108229480b0b00d40001c1a080e4910394446143c0c1d50f60340d489000000c03504240e00011660742c8051061013614461400f4020180000d000020320319218810160442103610044034217640703a0201544504203120042c1c3d1070200c2c0050440e0017404d4840d000518083c0740520743c104080300c0d0b4580c101c1d010070748040044011040040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 410437904 1250 410436654 410436659
    0x105041a060c0303150117070c020409080c0703050120040b03060d1a0f1501080f0a02090a030f02151c0902041e020712020303100311060915040603060515030f061207 73
    0x2c0d4680d00304803440a070000c0c80500290880d4000c0042c001203803000c40303404c0032603501c055007564890210a001c1c0e130495902c491030350010f13045500428075401d03404000d00da82882c5282440c2919400c0c0300e41c010001d0542150402000303894152420346044c02d031026240e0b96020003003130031514050005040450190054041c5050529585014840c0e000b59018a80c0e60b180088465035441c3e4074007400100c45000042d0001700451025401800c802005860300c1c04242c006405481d00e604150745024000810108604e403200508001030031844c01035003007448104071100d0001380701d415103c03030303d848540d00811036689a005d00245110076038000c0b0014a0042244029084100e0440b0281800151000320030300010a40c2d206064880ea0a404141585d484480d03018081002c2a001102030007000c2c802e90301c0b005001c41d4a51755000c0e1603121850650002c0580700b10341d00071400350700c4c03c2c0c0d9030084800101c021203900180d800200044d985501c004a500411400c003441030f54064014017 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 410439154 1250 410437904 410437927
    0xf03011104090e07150f11120909010e010b070f031209030c1104050c0d0f1515090b0301120807020616060c0f051612020708010e0d030f0c02060105041a06 68
    0x780c400d95000d180b04100148500e2803031540c5013002c0c0907038a240c034041201186403500c0b90101103482182c6280240b00168001d411500d081c4444283c90f0303d00790080307118400d0f400c1100025004140c600000344141d450409000514414010050291392000c000f14051500800d002584440100300c204611240750034018040d5a411a00312103265041d410355400d498103000300c03401418200800c61030311514901c140000c0243c1d40c1441c8021351208242e002e1900900b19a00080070f0301c20000c11032403134000000b004029a41c0000d8902c1c8020300060080060704c3c200c1480a41e071001ca1181c0e284ea0038000161306006000c80381000e55089000d20b810020032741c0104c07184104c541c642c2901400303c002c040d101030080340d40070a070310b00c0079400250102d039285c1d1019811400301e00540300c03042d88500c056403e5801c06070600c0031550203c00420005a4144584038200031801820000b0b180d040500a464030410322826200320f0316200ca083c40c411900315100d05419008084541c0e889003005c6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 410440404 1250 410439154 410439157
    0x2280512030c03071106060f19080f0307020316030335040c050306160804080706090803070e100507050a060c120c0206040516030203100e16030f0c0501050408030d02090f030111 78
    0x1303420000030b441c5018007910110014100e400381c00020504101c404818050080d019040d90148400060904000404500510026680741c2100014507602e10581c0141440c120b02583d40c046a082c0c4d50800700080b90b03200c01c03a2003c1900d0602604e0381004810780c5061640f444807140345d425000d00301448104104002010f080b40c00903800d8451a9556201661100500c02c6511001c50616070014000880490003405600c0c450038001813300b00714ec40320056500206c2d884800701d0f0380310012942903d006002000c4200c1c0c5441c20700d20f0700074a60b4801d40c032110000001059103845134440c11400d0700500c070a5200700b46070281005450700b000802565001c1c2a241503c460050524040301c8402c0c6038001c200b52031700900100100000400c56100509040d03862041c503002e58040d200e112815407480100441c051100e8a01c0c9100600700f0a00d02c01d000d900c0581400400c020811a1040201c01d07500070480710340e0300603100c000301400300c0c0b07503030ae0300c403880d1541075180c5010740501480180 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 410441654 1250 410440404 410440411
    0x1905030f0106020304050609040902030316080d050112150506030703021507060509070b040b0f040e010e0118050f0601141c20070f06050a020d0614010e0102280512030c03 75
    0x40400d01140d03a2484182d8503446507004030b03030304840208640640741c00c0541092032034901c090100d0386483c14417101d1a440703450f508004c81d03804900144140320a4981c0c01005d01628a10100011455840e0703210100520355440c82e0054949070b40019840b586c042c000c6400450300600383c280c00c0c00e034030f0684102e02e034040d000440c3c070945004007048240400080001c2035810040000c1d1405040604030041a088030748000c0d81c1c510100b2010070903407018030042e07000300002c158034407195041c8500041c1c04440340c81c0d1150181c1c13030142000f0b2641c412206643d0090310130b080144038503001401c84611440780400c1180d01c2000102110404a41c0780e00203540502000d40c041e2411248002c01c0f4414031582202038410a03448107880d001c20394952049400056001d0014a40000c1480070000d071a000e0340224030700090241003180d0395801403080c40520700d091001c0d02c0c400f9243c01500075074051448840c0c2540c5500346500040140400c100341c3c450306420036080d01c0c1d15041d000c40750523a01c06ca = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 410442904 1250 410441654 410441671
    0x20c01061205210d061514180f0a030f111f02060a0506010909090b0105010909020403230a08130f0902032203032004090e0307080706090305190503 65
    0x3050004010400d080307044105036020700039004003e00340d9203101561036540b200c000d9112040194207900b05061080f40010003100c10120f00d080c15181003c1c0081000c40031021201600b00540902c1e201650940d81e1a210304480b105035071200c54002c94207042c051381000300080400c2c0e201e003050041e140304030703c542c0400722442c0d400481100b011145030020100200301680c80030020034a204002e401090380036206262903031a441c1d450500d6400e541c01603805035580c004080040c4510b5a00c40e0408003e071801800552505207103648121461400903020040c103000c070b2442d80c8480b101440300d54400c9400ca0300741911507410480a180000d41341c402c10250b04405800051001e200d402600d2080500c6820f281d4480c03808020501d0b440e012003801c40815996000c4e0740c00d60254080802000f43342025020349540c10034001340111405482070005a81c0300740003200016901204940344036902ca071000c5031080a5150a8070a4002c96101d01540c02c1b082ca100c403815603016000e5403042d8804c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 410444154 1250 410442904 410442911
    0x121804090c08010c1d030c0904060e12030a09060b030318090408071403033c0601020a050d0201141012080f123103090b09060417250f061209050d0201020c01 69
    0x41040503640c4c0e02074410b03142c01a00490002d0044ac0055004180c401100025110300220074040700c0c07035a81c411900030100c0c5550301d08000034000300c0d200305c040305c242c10390083d8580007107030104074840c00c0000c032068407030502c100002e001c000024042d5141c4550003810003000342407000c4e40325201d410484402003104e40342c103e44081401c41240d40c142610b1605840c2c4112000103410450001d4001d100905620400e41c0c6100003900801c4186c01524590340000781e000040c0800220b80d10000c2c000f41c940c00e020007001d0150158804032100c2842d48010307400d96400d4120801c0000d405601a406070030070340070041041c0d54145545412001407a481410700f6040204801111100c1d020ba0140014411210a00c248641a802403c000308010221070070990b0f40d9415070313404141c040c0d40d035081d074004034032200f8140e1580c05040e2829105041e044d07260780c00c168007244017407605c1c442c0d44208107440103840ca000c40e9641c0725141c0310743c0210035610003280004019011750b22032601e407c140c0d0718 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 410445404 1250 410444154 410444207
    0xc09010b0a1d060906090628022103220611070c060305040b01210204020301080a030905010512070804020f1804020913030503010302040507090e04110102121804090c08010c 76
    0x10002442c200100030100d41c2400030410510005070029010190400410407460154041c203864403210312020000019040071900d000130708110110720000c0007018048101d010840315041500d07400403210084151f404410302e9a011200b2038402c2c0a81510f28080102e84070a070640018a2644d00848800c2c03482c036680c10b000c5040f9103044a014001030500001803040341403242d1a10f03014804450841051801030700054100c1e030003a84080d03415440300c0c0000e010513800c65481b000408003400c0850400343d10740c040030280e8000034803003400c01c08658009000c658442100f00000c000240016004071145210750408400c03d480685c42400e00300005440c4080d16480c411145601da9030319425a440d41c1d09000241002400c1c020a0111030400070818546a00700a0f10450142c00c2c040c8448282c9000a820114501510103403080c08120b0303c031110001c0c458400030000203031000a5250b8480c142420016800c1e0028180c035400d1141d035184081e8455401810f8035400d1032454000740 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 410446654 1250 410445404 410445437
    0xf0a0f080114100e130203011412070306180c03241134030c060e030307210608030a020703110910050904060b04020304030c0515010501020c120c09010b0a 68
    0x1001d1084203100004102c680019040003580305000c00c01070b0510b080e01490f4040052545074a02c055400000da000c401040009c09510040100c01001da41b440190182400e020351a15254040909002d4440c049004150350300128016001e4100e42d00c612029107a14140c40d10f460b482d0090600c14511461400ca8030b0042d1140c05c814944000703400b450f015011039074071a0484442001c40c19241c850007403050b144890420f0316082c610079a100c038801581440c0150071210041d040601d80d510500800403d40d8100040e4010b00e03860031610b84900d041d0f00a810007415190b085104540030110b43d922443e44c0000364142a13902c240340144503072240000380103801d142141d0881406c0700c80c200400031814600646500300d8040c01000c560300800c440490240d1b40705403000c0b0000b03045008403a00b8000140551112800c0d003601d0074400303524040000b55250b00c3c50a407240710304060441850907a804205007424560050080c00c0590794a01c94543d00b82c00c4604040045000703010044541d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 410447904 1250 410446654 410446667
    0x41502120a0e0a050301060303020c03190c050402160606081b090f0114060f2709040309090b0604030f08030603120c03040308180d0b0105040b1002031b120f0a0f 71
    0x10100010290801001d40d00448101002100715604482140400f00d01901c0a0140307a0142d030198000340444840b01c001d143c64903006280324501d0720214660480018018a180000c6550841c2e01585030000b110000340865001600204034529081c1d00241050010503203045d8404080d0b05903003042c0e0b90030280603090800b1030b80c44c0000c1d1890b02c0144604d856050b03c1000c0c180014100c5410403002c0710309080300d13522952900c0c0d440011084644a40031082c1040d240c140c2d01601c00501c070303060a4de0b006e00803000c14000d000d83e03aa00c2d418005100d40711801030710002c607082203460440c030310182450313501a0300c2680c406000f8020302304000300d00c450743c800b224205810b034001149440c0c03441d151007580b40c01c0311565021410b84541001020b98607030f000303265080d0041003102055450700d01040100c9000380c107418015590368200300081500801540d501441d040c80c0889140000b8070458107101448005203405000824402c00258120000d403200729901d0303c4561505101d1042035400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 410449154 1250 410447904 410447923
    0x3090503010c1e1103030916091b0c1103030f18100c110619051306080c0d0207080408060916140616230a02040501140f150d0c0302041502 61
    0x10400b0003243d42d00d800011052040090700c0d03454504550300554415a0542e8800d548100c006d40c8048071440d20761012a12a000421030081c040194070b5181000004900007000560107024042c9101c006115051110785010000117043ea55070b8003840c88000416080030b8561102c4405001104282d810074510382125840c9039220303007804541a544502d80400320044007074010900707006600300070340490850301b00761310f494884907112620300c1040c0401c50f40d82e500201c01c000c10f02e030601001c07081d0320301101c1642c040722401599034001403d2001e45c620695000120302c0c03059108105d4490400b10308c100241000d0607094582c0e9a5071a00c5a00304842103045a40c0b000303007080391500900524602031111072246904019a81d80d80c44001100135846446a0f01604001400011882d10740300e610302410007002c02030358551190780841c40c41c0c50b007a50f400d80500020400148080d0700d2205031400e480ca01c0b0401c0c00701b030a18660080c0a9003191182071100c0b0b05403c885c111507070012441189 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 410450404 1250 410449154 410449157
    0x20406030c081518070513060e03240a0c0903020a0603060e0c070209060d030e0409150608061323070b07060e191104140a02040f0b040b0406080403030f0e0a03090503010c 75
    0x101c1c5440b00d058502013aa01922103000c3c0300040000c3e14003407c0c8400140000d000c19145c0000d100c000200349410648075036504110003800c0d040d2400700b00d001030849a005810400001b4080b12110030075252001e00390400b9520900b101d100040060f8560081c200303450b10703040d6070041c1c1d850f02021181203010b080307002944500c5510018840f03007072442059060234000d1522001a20041c2d001c1000c0311f4000e001603484540807015a110744405014950040071060020119481c102d44542031415103460b00803d0b0410324112503010040624001415154078419140700c3d0760b44039031054441d4400b81080301d46074103008245807104404210342481d8116070080c1c40c4880d0317040e03940c00a12240d000c3d60030381c41340e5180300304110310125031002881140101c0c00142e44500340460780000c15006e82c8003803000780080000380003990494054404650180c1400400e44e11030386130a501a1003550081502549400100410390300b00090300212140251540e003c41900ca9040c07500780d460307003c0b0210 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 410451654 1250 410450404 410450419
    0x60f0c0305030c071b060e060a02070e0603011e050a06050607030f0c0213180c0509060a12060609020a0f0e040204060c08090d05121b151503010b04020406030c0815 72
    0x40400d00a400a560000c070f8408258076042c166034590742d000c40380311102c60808080030024003000340c21000d040d194103412103000341024681d01f0300075900c013228004c00d03d0303941c0c00703002080080c0c80941048008482292404001100c2c6d40c010000914080f40c6010300c82c1d0034550700007141c0c10890200c81c2038540550b94020320080101e42030310388062151049800404c800340c031465449440c80782c2c160074401e00400c3d0380c09a03503606040c0c60700c04258200c0c0c3d228030141402d004c216914000c880040314003204180704860001c3c2052001072000e9840810494000520602829030020181200d14010b803240181b901d4503d05100480c0107038012000881c1c60580d0107400b2a08910241540050080c110001c001c00c0c0d0740c0b00c5040031480c00c041d902030000880c080601c00780307102c1200e901400100041041c0300c20320620120b06000a8882c00110f01e10a1052020b80c50a422100c20741c41c005c1c000f503541c0e0b540d440c80140203007841e81c001d40014900401043d420301e08007494000d1010000d0808 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 410452904 1250 410451654 410451677
    0x20d0219080a03020c27190e03040e011d061003150b0403060e060114040e0102091009150507241b0504090b0306160f021e0703030801050603090714030a08070b10060f 73
    0x252a020083c2c030f0081f840070fa90018155443c0309000c0d03e03200503480700196403140d00d04107000404207410b03008980ea1480c0d00e4514402d0410b074902d202d41c440002c803045404807040c11420740c020b0480b004041c9a1860481c4c021840040c0c4200030400c4074855001088820a40100c8a807203060a0080c0300004010608a071094549504004501c030001d000061604c420140024047c541490b5503c022880d40c200402802c01803c3c0441c1c0c400c9041d05000345031800325a100c060031085190740b04003410303a840c0020068182940440c0950007060f0101c00fa215003050007500301d030000e2141d1104142090040c2c20541004182640039110b074900c0039a032140c500c0b109031540035241003010118410364a0a21074074402c660400c488400c250050700e1018214100145120b90503000719018040400502ca14442c00007a010226101c82c03c060700800e240d00c0000c0d00700070721443d000d40071503008207404051000101503140294a0110403208640e42e0305410750341c89446203909004290340c051203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 410454154 1250 410452904 410452969
    0x10f0e0307171f150f0b03010501120e03072001020111121812040306150506120405030c01020f0c010c0c05030415030621031205060a03020d0219080a03020c 69
    0x8081d00c0240c008165501500100c0c21030300440c201500c40001c06864a1007a070941020701c4c00400608044031043c0180c81c10b0441007003103880180b203014104040720f40682d20380c41d415480a00c0c105410f0060701e40e9400a401c01f000da111071607600c0380d0049016000b0380342030340c014460000070340c1740030303500c00d040903c2808a921442ca0042c41c0340d41a84030702003906000314040c40038a00281c180618035881d03909504003c0b0071914034452040395409140010700117665a802176907003001d200050164981d5071460001c0c03e50082e00451480e540c00070501d41000c00005014202c0710700110003c01c85d40d44401800c903514201a000600540c1080205028100c0c400e1140e540c8800c035810003061083e0303241460043c0f4040c4592040f10b41c001c001244c0200341e4014003203404003084a80c10300580c180030b00014200941c03440000d10650318040e6640464946c60f10101400303012000b0b0031600e903943c54445403100d013816011001401882000601d91902c0c2c9142c120b40b000381401100003c240d5041d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 410455404 1250 410454154 410454179
    0x20d0503060a0e010e04030201060e07081603110d020405030f030901270803070c08010537090b10030c082b050d060816050d1a1e0403050405010f0e0307 67
    0x1d900a00350200115031803562000ea24000c045030f403840c41c50703460141030003821500c81790080d8405880d01428442903d6000071000e070000807040021040009c0001e040c3c0087c07410402c114a0310001140040000c14168064070444c0c0080e02640d601d0342c5040351164680c840e004045000c19990302022074008402c800e14200c08071800c166488140e219503c042c81c580041400f2a0020780385401403081003401c0c00340720307000200002e0062010f140ea0002966040d1140d488a03518a1100d0041100d111641c001da00d0191704081c07914a42d0401c02d40f11000c103001c07030005448114402c1d40000781d100d000280c0c507154810a54050740b0800b511440c9044903116003240000b00507081c8912642204c003403007900f0003090b518000704108099030380c40d62003021385a40500c0c07180c0c120315a1100801c0003040c050300901403034020014280c0d1800d0551200141d16039441c1c40310025082080105074104008200b41d60090f29091800b9411300b07006c664841c1810750b055019089010100240303034000c036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 410456654 1250 410455404 410455411
    0x6040623040b040c0801140703111e091203040311041a06032e12081e0a0801090b0d1208071416020901080303040c0b03090a061b0e03030901020d0503 66
    0x121195125a04010300e034445440a4030159803a004160a2004000d1001810b00c01030071214028401c07403c40601074100aa001001c24080c0364841ca06542c00d5040d03941160780141410181400c10344500d000301c0c0080e0007480815000c0d0328030713400c6000084400819170f412039900c032691404100d00d1006200c05440e001d0031041103080e0201404404d035071414069407140601c8a60000d518404440c29124544403402c40710069403080403c1c171110130210510940c0b00e4000e83c84980c2d43e09040c2c000c101076941000d0f40c2c1613080c40031404498940d80f045c0c62504881030b244060107070620141c1040a007031035141008005094a00c08140842d01491b000c61303104029041c40602d2207900c080208203a481a0606140c81b841c0c94418011417030201c0c40140500030f404011811482d01e59601d9000714000e00031030321084004000038100e420100840c0c0c1c9407503030090b414840358803042040160510484044404030741000d40d803c8440c14004107480641c0703416401007286c28094041900c8642c07018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 410457904 1250 410456654 410456681
    0x71710020f09040c0816030c0c030e0a35011a0910030c0f2405121f0902030f3103030219050a080a060f140d0b01170d020303040203060406 61
    0xb800001c074035585510400383c41840c652955000e6103050085110a90010042c6a06240ca0165500006036100030a2603100e40c1c54108441c114002d6400103481d6106640300c407000c0b010722051004600c0680070b401d5007a00000c45000b070010f95540505099680c80b11005000c13a8104d040c03100b0600c0c0c07001c1700380d80144410070300b000140d46135141e5945085d80b6401c0350f800c04007802e4040211580b103410802e18907001705e61100030400740c08002400c900c940981d5051041c2c4001c00300e141c05048240071180c410300d030804500000d650f0114032000c2e4008460040b01a190040011200072160707c41c401e881d4a03480d009000c04d84440440c492a1512003425010907600380403510075040e0003031030820f400c1e4084c0c40300c9440d40f041507070003064032034000c00c4816407508003102042500550f041c200242c5580c004094071035480500880e00b80101d4000c0900b002850784000500348a207a01c1d04034030075a030001981d0304056016000d07a500c0c802030710001d4142d4001800540825000e610844410200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 410459154 1250 410457904 410457907
    0xc060304030c140706091d060a140102120a030603120e0907050a030213030b01050f120a06050a022101050f060403050606100302090d060c030b090601120c052703071710020f 76
    0x1c2e0580c500c2d11095170851004a4143c0c04144805800844d01101841038a4031085031850650b000c01c58440c524410301c1c800c01804c01000b415030b03000b800702c00c0c0c00304181c044e0191030350796680300140030304040d100030b07280450100c3c442c42109201d40700b01615644040c11582e2181c480140031152a0b1050095400f0140d09001100c102c2c0882c0100d01d00071401500065042d5040004100b402c01d255000148036030746401c09040c0e82400030445140c800c0d04510300140b55560705040601a12030320403200400400d00007603002440c91800d205050350340541d800212400600d0600000e840703203002c060143e0b0321040c0001c603549004100220210a589009803d100a01c0301203008040e00d0b0038105d03100d0f41c07540380c040c1c41e41e40c0c94452a11540030841d06c090090030708600190403107009011350705980d03440700d030640456402a4115120324010203a50640942009068a254424031702101d210740646c0400041001041e02006002a88034016000ca981c2014980c0001d500442604104050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 410460404 1250 410459154 410459183
    0x607031e08040f1202190302100e011509091704080105092e0e0703020901080f0f03040b03060d170d020417010603170c07181a0a210819030c0f020c060304030c 70
    0x400c07203150b803006c6100380c008041980516240c0c1341624812000c00490780e26000c540700940c608a000a4112424031000180f61181c60400d08036049120013800c000780d81c0060005010a015440240300c1c1003c44280c44444c0d20000d04525002c1c05000800c01101008400e9a40e0041c02d85c0020340e650702002c100c4620903034036400f02d030900302c09a2010302070b90410690700c07521100602022411001000c0070314909410801003468038000a000940505113280d24001041a140c0000103c0e00400c10f80750745a0f02c1035102403005e507125001c0d05080441c7c2002400a0070414000c03401901d50100496071070025011131888150400b03000c4800a10580c0000203100000354079124142d091204042152341c04800c108200350040302c0003034000d5805507810007881c190f28400d50085001280040d48000c1c903824020214000d41315441c60000e01140303000035054040e03101d040e5010290b1034900380c030050003409913110b0601c449201e8228000b000050700181c4250460321145100d002444050b10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 410461654 1250 410460404 410460433
    0x40b0d020c0f0a12050408070e070c020a0e07020c01032906120f061c0c0e06060f040b040f05090c030103021302040e04031206090b010507021c020607031e08040f1202 73
    0xd0080016040754000045000c10701000d0704404c0600740050424900d0986002c02c0c0b180d0b034513030303038410311402e121080041900305200700702e0110b055800401c014010340d15688485034804055400780058416400300051650088c01407000350000c2c0301001c916071a00d60710b900c00d9100b03071000e0182d1040c0200800c00800355510f500798015080d0f41030500b110b11b00078050202c4100030f4900200200300046040001410500480069400d807084002041d1a0a0086020350140d4905040204170129022600030320281c0600100c400000714482541e503680107020b0b003ca4240e8010f03001407810001030000d81450083c8103100481100014905669148506180e04080c0c4086000078a80504003140c400180200c0d8064440f908c001c001c2c01c141e07400040c0c40b41c07181c900f0082c000c042c01940d0208a0160006500105401030826503407400a49001400700700c481c4000c0710080e030307070300d04514115106410b401e11995001d465440808480d8544270400803102e010340b0118440c84061503401c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 410462904 1250 410461654 410461663
    0x1a01020c060d090c031a19020c0d0c0c08030f0c060a1e0504021909050717060d021201110a0503180703020a170705030304170105090604030f11030d0507050903010f050606040b0d020c 80
    0x40c8284244c1b4402c0c0e007008000c060410031509100307522640103201c1001500c0011940038411840e80c14040c0c030f2000d10b86070400903c407280e84003030503601000c2650391008424030010134110803078506856003555148012001ca41e0541103807441c92911000c0c492680e90158486a0403c1c0020302d9881c603d4042400301050207015017101848589800c01d010860740c00416084611100c00c10900081c0350440100340c0035000c84001a01ca500501d606204c108802c2d4403801420304200c0b143c3c2d54552135050050107581c01a01d04052821010241022031600030540320309483c1d00500d2210180c1c54101c3c0f8014407030400c00c07030b01414000e80b64002015601000184010000b04100c0315140080c040140c0c215a801042e065454100c50100400030394482e8480d2a668154240024100c03841404c180c5107004e9240840c030410319100c1409a69074121001e0541200118000d01084400e110804140c1c0d5003a00c50581040041c8414010710101c04040c080c401100c100042c1808280010907141 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 410464154 1250 410462904 410462933
    0xc0318160f051e030c0105090d020d0b040521031b090301061e0902030c0d051e07020c0909150a0b0105070b100e0f0f04061805030a02011a01020c060d090c03 69
    0x500c8041003080040b4100115001542c10700501c400d02044850703004a03032074952851040e03042040014064105a40b09a85100d2702034011700911501640d62801007010380d03059505aa0a00c41e0019050760102000010110303007248005260131a200c5046807171041d041203820f030300121014490300c241c40e2001d208620040c40007201c0b00c00100c2c0c501d4000c901d0031100ea0400000d490040003048100c0091600316640d0641d1800006902d41d070b81290702c992000140e01242d0418500424042c180e540050030020209084450309079035242c1030180340c0d0790707003800400c20f94031340c2260b0000b4008491070b07201c0e400c044010706200d0700c0c05000ea07403541c2c0300c00001c90b20008103040303018061003403807078500c412a84040c80241502e010f051042c84030100d003800070401040742d0349458100d03988100c2c607041001d0b402d85c0001100d840303921401002e4041c10710607808030503100040b0341002c2690b1001419085815020303044900d02000300041c800540303554141030b6040c04660381c0001c0095040f00300c1008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 410465404 1250 410464154 410464169
    0xc06050412080c04050f09070c0507030b0601140315150d0e07150306080a0b04050a02090403020102090f0a0b0a200607020a1505010f2913030203060606030c031816 72
    0x8880c0d180c000381040d1000f9003402c0b0701d404140028440e80c1c0350321089500c120f100b01c494007095612108100d486032480c400c014001c2c00352800000c01c0104641e80240a000241c0b100980f1000703592030300c0380300e000031a00f0382c001180450655282b0300f020145a82d91060b1000458501a29003650206a0f002640c0c0100d1950140c2030030484480c0360141920342444514041c01640d10f04400300360307500340205029160440c0900420200b11042081030806079002c1e081030704d03515090602900075040307110303ca40a0701d009104003c9518107280f02009481e1a20764550500c0242c41080b141c1484140030f60136151000040b2003410740c02008080d100320340075802008009618a800402240040110340c0030f1403e100c011b00c000010300c55a081940c2100d018000e5000b440842e042200c40f01c1d404400d5600c50000f400001089601c5401003547d009404440340354030380c00c0601c9050322046400c50b1103020180046002c4210466000b070a42d00000216582202e981545406484a0381e020a0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 410466654 1250 410465404 410465423
    0x907030b0d06180515040803190609090b0a0506030708071a0c16030c080106080607110a2307080339070f030b0a0e070308130f0905040204050c0c100b010c060504 71
    0x1001010080e40a00d02100a02011641003581d1f0380ca802d03001c041c103800d245500170074480040691940c03240008115284040c400028942428280c00c00c05541d042c82103800c11000400c14100024190202d070200c50040a07030a1915800001d4121004440c00030454200001044e42000b000101000420008940310b09440c52070200e8040300313964401d00b81c59051410400005170b0116820f64009503038200700000e6051156103d007070217213901e00105039200010003203080100c0140407000c00c1810a04a030110754072029860390702c0c0a00043c003100240e00320442d2040098003000d40d1109019000080481d0032001c580038201a01c40d00b00c4070401003502e80410901605807005900000088801c0020400190304136454100314000138100010020368298074800400030640100003031031030b14460546030704400002d48001e8406070f01c00c1e410306010948003114401143c41d04441ca10040c4400c010424158003d4400c3c2456681030000074035440c004200c80b070061510031446040c110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 410467904 1250 410466654 410466701
    0x5091e07051e180f0108040f030c02010c08180301110405031e01090b07030903020606040603050c10050405060403050a050f150a0e1e16060f02030703080a0b040e100b06090907030b0d06 81
    0x2c0f160704e21014400e810020381c4400d00c008150400c590f40001605850840d601c0101400182c80910301d0150050000500003501000c001c45500d000702503a40c12802840f010b020313000c02c0d000300c0c080c50080960581103a088044221303401c29608031a40f50201c00855021942c1c2c60360700700c094003107802c0c001181c0c6401702d407002c15034140802d0b540a0f00860b01088080d0031601e819980e420300d03d020310f0181c02010075103141140501c007514014003004000c6950f41d138030ba140448d1240513444080b55a403240340e000b60109200454400c1a001e50f464111f14540e07a9808200b0141c5500f03440c40f101400303240005d44d5506409140d4001c00e0208000801e0002150081040460440c0e0312140c200602044c035610080d901008941840d600362410031040e45900e1800c0e4001c100f0110b090782e001c4e1030803010354407500e00800d8261500c80e00040400c02d40c010503041c85140c2c490340c0f41c00c5e41c0c040f002500003407200e03019a010603120300e0041d26071400842c0c4d682c0d03458200ca030103a22a41c026201d21445 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 410469154 1250 410467904 410467909
    0x40507180b0a09050607020409170a18050904080d0204080d050418050405030d0902211f0b01050412110d0501051006020a0807030e03160b0405091e07051e18 69
    0xc503401060720308041032401e941c11400800c03081160256511800000400e17805543e07450700004989a000060480014914a2042c0c0300381d200d40701e500c000c0340c120344020b00c21200b01d03070348071007182c9020304072007002d80d29a6283c4e1070740e41c80400401038103a402d00000c952a00b082105210f0010701d070305c51580d42d5040c031004c0c400d41110f9034525003501e4281000c00001800210a6440018907000c0225580010344002094076100702101840c140201c020303950f11100019842d8010a101c000c015070301c100100e055000d0342d41c80c0100601040c001c000070481241c0d0040c41c4c06015004403568002c0704001c00005100c0d080c0c6040640c5c1980d140c83c00d100b95441100300520013000540000c0540d4060340c1d840703080034000c8140107800d0103001407801d440d6480074405007034031001010b09000c1c1c490b201c21003100303217030041d0040c940100e80090020341820a084c01c079414150001044e20204d0703546003011940f55204160041c010f0600016118081a64402600006100b000607030040b1155509 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 410470404 1250 410469154 410469197
    0x717010213051c03030b1201050c0d0507020706020a120509060310030506010b12180102120c0a0e1804120e06130302040f090b04111c0b040b01092c010605040507 71
    0x302510505905000003003242e0b03e00d6154012a52600300482d0040b19440000c101d01c2d038049000d80554200403c101210034240d00030f00881040500812054031111070481e50755005018110241e23002c1c84c416800714120130500c1c80c1140320341c0f0f0180c0c5071030360340408107040740c00030f0341d107509161100d079001d10800030706220050140100342c09071402c01495400034181c00c0c001400000000321682c500101d85030080d0101c4003000c41c5c03803205041906051582105c180d100365420800581c4078070a14284c3d10384480950312030070942140c141c640e00c4944031000060381001001050000313280d2400890f8481001130700c1304155044d04d400e0698036600600095038070003900301401c0707071801c6003074000641240400340d00990070400700310506240360042402040c1c0b0007224528249040c7d502c40800201c4d150007803050f4460794005003141d03610f8507180b00f942c002d0a0f03501444007490407080c2c80d045038540611060000c0f04004120555140c01080850b10103480000001b080b13100710002d5040d0000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 410471654 1250 410470404 410470409
    0x3050c06011a1804060801090b0f070801050d060507020a02030d11120f0a11070914070e010f05031f050d05031306140f0f1218010e0703110f01020717010213 69
    0x4441d100401d201050350b100c203100c2e0b07001246820840030042201c64450f940818060a401c0d002004003c401d03092214414608644411800300752400240c42140308054040c1240c0019040000c100c15507910700014040044c503c204502c21961508050780c0d040009010401281d204c1c1c00078021036005071410710341c1c414a100504c4c40100a03095654071510b0403661441014a040d410718004124007506042d2668032840380076041980c01001480c2841443d405a1542d445000d903000601e0010340b00d803c920440080498424000201410461074683d20b41c1c00c200591b01400720740310310000d400c1101d6410251090b50000c20b00c0c5030703115000300405000c3d1a05040c0000c0c05055100b0150840c030940c0ca000c52091400b184d00d2a046d10404296100d00020400c0b0601900d407031002c0b445482c0610b65881501c0d0b081241102c0000b002040c4401900c2c1c1114903020500308040c00c0c0a110344920047c1030462280c91030020f600c1c3c03648007039110481c45040015a86190507200070311082c4803078 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 410472904 1250 410471654 410471669
    0x905012a02070f121505041101030c0e010929030a050402121609020f0913050402030d210e0f06091b0a0b090409081c020d1508071a1603050c0601 64
    0xe00c0b00740103d01982003550120f52001400c215042654a4403459400455900c0c8442c1c0341010240010442d1801c0c00c50428030b4284d034200502684078108980e04164448214081280c203101801044414901d2020141c0c40c001c0030a0390480388a0a500903501c11204500ca450780c4000740000c40c908158100040c8295400a09440000d040702c80e403013122502c6010701440c3e0000d481e48120280200350303041008000c15500c01d000c0c940c81c4200140c0000c9508038400e0107032904c600320017401130010300601000c52400713000c400801300406004000c0c14844402138800c203002d54001c1c0404120031403040d03030381398050300180884005c404280e0340174408203842408401c41c1445104000820b699541d241107901140c111450301740b030000d611410704040c80501080800d0790007280c0c103400900106c000450100500c0c8031066a403201c400341400317210348a403c00502003040304c41ca80d0ba0018842d0640f41c44504c0c02c40d03801d510411075202c43c10218045540070644212200080c0080c50052030300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 410474154 1250 410472904 410472913
    0x30216230619230c030307080109050106231e040e090307081206120615010908070e07050703030204090f0e010b031c050705031b06180a11130905012a02 67
    0x281c181803a0000106030b038410803200c00c4100d0082e07006202e11520440345031240030361300c0760022200d0f40c030b0f640201c03065000303d010130000140104c903c0c81140c0c104c0d01d0a40e00d500c1103401111104405020090401710884014441c1d80b890f02c4d42901c0c4894500b240c070500070741c0d541c504104180749900041c80d0240540003880f14002240440c800c6420190302a07034000042d07034501000641c01c580c0e002d810061441400104801e6001888041302a00000d0f01c410800304c0d03880405d03035034078a4140601005003807084041540240100041c3c8a4a4802d00b409070419480b41c01c04002c03240301013000c840083e100c1145800c8000c00b8824440320b8802039002d0003100c01c03140841ca0783d011301c1862403010014000b8106040c400141b09031410b0f001c40203250541210021126541d610b82035801e68400d00049104501c110000102d140700164410306194100055104110342d0b40000400078180d1612150240001142803052084130a95200f18940c084040e02080707441c0319003142c5803c1994030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 410475404 1250 410474154 410474167
    0x70e090c10090b0910020307060903030c110c0a06050a02100915140f0601080a0b04020309070602070b0a0f050703140705100513020607060b012003090315010e130302162306 76
    0x1c982003110200341d015648040170040112049165110b080c80c0030f0601860b200c940000c065041d0400c54603407000369604250f040741d40c4506916062042a01075001905d180200940d90288010b0640b4041a006551075407070345140d6801505d01003c2c0071600650901032280c1c031601d56115590036814400200f911520b82605081c1c103c03200500010305002440d00001e22036009504035040c07036900600299100d0400d41c0d4035558581c0740c0e0140101500410602180444195060b02d01747d1071070380c0e51f260200c4514042511140d11000c01a4104880d00603941ca03e0f0440e180100325140c8210010720092500681e04011505c0103405400018480c41c0d000016a071042c2c161044140c0060300090511441c100581d680d41245150300ba50342d01e068219000c0c2c001c08009404040d4050b000c1e100d50004180c2c0040d0001c3d02400b03818241c410480228940d100035900450140c2e10a0046484141c030800540800600070b03841019250003028000d0308011410501211590060392020b05102 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 410476654 1250 410475404 410475419
    0x5120d0e0d11150a020d090602031b03040c090c0e09010b0901020606120a151b02030301081018151d0708010609020408070e090705040c080612120912070e090c1009 72
    0x7008100321804255840c1d0221380e0507000c940c100c5182442d810703820404802d451a0841c069002214424084128601115514018070003102e100782e034081041c80700c50303040a900100604554030340e101002262442c1034140d48030101d506001e00746030387c240d81d11456004002413070900000d00b035a00888400301d07100720750b040000d0464007280e841070903201402c040c0b84c650b000404680c3c2040d00c01d6008241e495820030340110003141a0340d2401c081c0c0e030b00300d0140b9600c1c000343c98a00003031420000d14851401c0106124078501050607110f0040803c0c03440b610b010403000c0e41c078074801541007030304495000c200c5401c091003100300805240606505180c5043c0040ba212009032282c0d401d01e841101c0001d01a21040c0a150094140240b00304000b510081d030041c49400c04440181c013a01a41550240002c40041c058100d14428035100e8039015511061020301c00110702c060701c5a10070024041030584a0814851260201c1c900a00c052402c4408101e40c007131680e840c69041c400c04003421b20800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 410477904 1250 410476654 410476663
    0x60512070302130c020c04090803060108070516020d06020c15100602010e06070f090f0801021e07020a060e01171306060f0f09090305040806040303060f0f050102060f0405120d0e0d11 80
    0x2149401000204c045070000c05038202000300c9082c80d0702920300741041003080b031020051400b808080e0380c2d8600799038031444103444502c1004039030401c10a008503408010b18288040d04400744c4129400360600250f104103605c1c0420440803620102041c2081006507030301814000c000700a01d10091012101d03003040941c59580180860040005440002682e5401600000c0041031135025040d18581d540b41224001c1d0005224500911040c91011007548141408c0c2c40d01ea46c1c005260701106858004280d4200d84440a03840c1030290301e00740027030841800c9000d980700f60112100c0300760105081c9450b60413205650481801044c44490a1045480c041e48d64419100300203000a48801c260400395040d01890f408040c0c188030792420230007010703459082241202c0c0e01b428404441a00e5021081e6450102d0051900592041001a00581c507150000350000d0081054a15040c41d0780206d1199034458a2081052074403036482c10759021003000070611000072458010000100100800d884 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 410479154 1250 410477904 410477929
    0x702030f12090a08030a0b01020c010509010e130e0a0b0402130e0706080604022a01060f27060f0e100806010e01030201110f0106121106210c0702090703060512070302 73
    0x441c0a040001d0401030300708241000305400c24200c03920703440d01140c0c0e4030182107036400d803074014081d813046114554003c40a541000744141c65240102038903500740701a9402d9201ea0103502c503110b80142295500901628a041c4d02550700300100f480c15005010780940340241809081d4601250340301000000300d03d80060761203030700e4200040d03254180020f0103809100721000781c90248079010a11920354a4091303106a070420024070a003982c4202a0040d040075101e9070b66003402c490749042545800350413085a003204080b0008007a61a03424140c1502c030300e034100c01d03c0d204070181030000e01304010880c50000c001c13100003041c583d0f040080e5981c100a040c40000c0c14052008119500c48009100240d44400340310700800103d0b40d2189010340400c2e0000d425079110610130680301041c24128111507040840c448a0b4000c401052110809580c1c014541d1361103007402d210000059840000450207109030366070100340c10b0304003410080c0c000035500c0905500d40c07000500700010f8850740c003070a81 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 410480404 1250 410479154 410479177
    0x3010503030304032d080105180c09120a0b0f0601110d050a0c0201050d090c0518010f03170715050402120c011e1103070c0911160803070c150e01050702030f 69
    0xf51611550030700030000d46904105d1910450343d01092000742e840002c3c18103e500c05c40b88082c0c0b55441404580b00040c0559254100344010007001c0300d40c2c206484000c604200c0e020454030403038966110008030f4003007a1002c210105001c801d100c56507a110a85080c41c20b010b402600c10384458420107007042c4500f0b000070042c0041c0c4801901507a0081d01a14032440314807c0a1006e0b11aa15040c40d40c1c00311070003054821540194a10300d4900e4108449060324240410082c82c4ca0540d1581d0358405440c4803010360048081201400145150801102580401c000400d0314101441040301c0d10041202d44a00e41d07200d080000040da0f4800d0380e903c104030102074401c64502030740a045072221400c1507a00f00520001445404000302850340c9000c448881500304660a1507003558641c138030a01c000400d080e01c00300201c0c0081900c540045821190a04000521040310303503d668110039074410703403c03000343c1d10380c9010b0120000b0300823a54031043c5c500c080c514000d0381e2000b24815001c0c2d04212030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 410481654 1250 410480404 410480417
    0x40509120d0c0905030f0c03100b0102060f0406060f08061b0f09040504050708070305150f010b1e04150203070b010f0b120603011113060f0c1520130603110301050303030403 76
    0xb5146030003010850041c18000e130950350307841048020a0b0f503402000c55440e0092280c00074004a600c09846444c6440c5016805852a500c5030390003203503042c8c80900103517070150f681e15000880c00c9640228000802d0048041c062500d400804484060f0141d481c81680c508200654402c40904400320341404c8412600042da46c0c949003440761408007070384c1100015100f240f2010091040003d41c010281e1a00301041d03010b65100780800014020030700c1402d0018905200700024403506240244a1102c15401642800d075030340f400030710943d4a2104107002d0f800c0040c2030820f03c07000b0350f480781c05440745100103103130b49160a0500c0418401d01000d202015401c101203480356400390050f459159800f94055180c134841c181d0030300e90703000902c01c80001c980860840c400c124020352020748080d8014249044000624a044000c1c2440380c030800c08016240158418007581000a0509440110011486142010b5016049411600551a01326020320041000d580d00000b02ca5005501d4a00340 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 410482904 1250 410481654 410481671
    0x1116260f0c100e071e08060c07061b17090c010e0f0a18060e15100327081e0310060509030703060f0c03050c07020a03030e0f06040e06040509120d 64
    0x102e04064000709044480740c18062641d14020340000c4d0007042e42d01e001d181d0b500381031404515040825441c8111441a000307000000c00c00c1003524090b10400f8010b210100391401d20300a440c0c200b40114003441e000c19198008030580385100314110344d100045a0050620b606104001307007810510420a40c45403a03c40c1d4105210384400b01c00c08000d044500d0f8000c44504100d00380e001a029074011340550307070384250000d180000d680d21110f00c3c1501c050441090381c54401d030114090303c403607800d020040541d40307036190058841c2d1110315a4180900d601c60745a00802e016010104c54083d152a40841c0601c20722807070149101c1800112003840c18900c2e80c0d40070b00400b0a041103100e5001410703031482c19820350703000145601b1442108820360b5007040242da40c9440580e440c00340e13207000307500301066040030320020f8050b0a5980200400515100048800c50000f0301d5a84c080d4006010b5543d04809210513801c043c02070135041030300300000c1d005005004d03207050614000c00c10700003201511030100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 410484154 1250 410482904 410482927
    0x71704081b011b02010b1008150f0d0b10050114030c0309160306090b060406060c060510080a060f0c02030a140d020f070f05060f060607151116260f 65
    0x1419420207820001d0010030740c40c101e0041c51401d202a0354025508100d500c070000e142a04100145448945074100d4640311000550f074410701c0030414030b4100f02100c006580d59610710700d94140a0b48030701555400ca19003840c2c50702102c0c07995400355041c450550030400a100c100c038142c031343c400081e07116136480e5910501200c2c5000b1403600400201d200c000c4020090082c03d4025114081c0251140c08068903480184402c907461441604001038413648208001191074002d140c100d040d0000443c940c41c1c03950200b5061410760b600450b40c455503105411660346c458014607101407003c2c0040c40c2400800400507000c950001d0000910400c00280c0950a60240d4191000c1e0080d00e0015a04e4a0080ca4200005c40042e00284c3e1140705c1c060000742d407440c0c84a10310b44144409402d4505228207039903030001c041c6100461400c01500c400c4081443c46d454405019100610001c50341d0126003810104a404104103618118031507504040c0c10312240354040302c06004004542903940c034000a030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 410485404 1250 410484154 410484187
    0x910050c101b0801080312010b1321060e0109080307080a1119080a1a13090611090109140603060d030c0b07090f0b04030c0509100305030c0a060507170408 68
    0x442490701450008a9140850003071110b550441c1c054a8070426a40c072800015507a0040c8450341a40c020448018010100000d001d0305e40c001d14029240d0b440354079150043d110743c860700e41050560742440d04141c2404941c1c0505c00360000e07088000c104440c215201c3e00130354400205100b050004e000c3c0450004207545d409200c85001800c0c43d01e484559040d809041a034000440c01c00064040002c229902a41c4c8204a4100d4810b11811065400345050048400100c0407562240781c0d105029000f2907400e000f0700c011141c0340d019036503540c0c245900142a2003001d8000510021000d59042d83c00d445100403039410850031643c000c0741001c6441c2c2101c0c404843c90b8014000c000c02028046525000b0342501d041e2410090345010660700c41241441900036480041c0075119112000c1002c1d08140e0041a04959115021064952a911000d00e168850400490740358450141c0170b0500006100b21a000845072402e40644c00c0d2440c00e155500d0b00c080c102402c2098001112031031403070082c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 410486654 1250 410485404 410485423
    0x6140603090709020403030804060b0111060402090c0417100c080403170c0d1401050f1c1101020a1b0609050d0210030f0e0109110306011208030c180a18060b0910050c 73
    0x4159585c40d1245001410100c0070307602140c13502d04002c0356404941c0581c083c6101415448002e000d90b135500d400308000c0748009420401e08003030810001c03c0810382c0d40705190919096038020002101c00344590402c076a00120001e00704400c500600c03000942c0440102c50513034441140c6c1c0495101c00d1042001f6204080450700320340d2610750000003140f030600b081030403a0012103100c2290000c103802d000d52000400c1c51a12a080002d09210000c0d5a24005281225061044601000c241d03511600000700c80c0b5445105022000c00402c056a40255400701030002030300c0078490304855070701180340c1204001801050680303442e14088111b120b6480051003c192000a0100304840d04019045000100e10746000340240740002c9007007072141c6232054a680c3e000c2c842c0380c950766841e140340d419a00048119440e55104403500010b50380e030040114080e00f0b083c100e04000c20140b01da0041100d040b9449485440c4048c4152900d030765410b010010014000d04005640311801080c1e80c0c101125036 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 410487904 1250 410486654 410486669
    0xf0e01140d1b08090a0b09071205030c0115060507031d0a1203110a020d23060109020a080709060f0c060b1507140601050a1502010e1b01020709061406030907 69
    0x400d2030040c40c42550000c00405503480303840510b5050b0484111040e903001c699030303004c50780145410b070000382d5582111076025144005880c1b0150302d0340c1546210310512181503416900200e0403003d844400c3c4200781c110000030312022003081c80c058001d00507004020f006420301161100c210300c05c41c500c404505221500030902c034220f039180c51141c04500c00e4488103900180740c0f0064145040c200007215852141c00a00c40c0e0088605542c8202000c00d1402c25065049440c10b0304a04104041011501900305c81601617140e6024000c01441c3c0c4c2001000d0100f0040d40400801849810960141070100345291142c801246420920007030605501c400d600300c032a46010141510307880000d0807489215044085046a0507800d080e40c5510038055154007008205007080750100a148200d241340f080e000200345552810900e9090448a5111540585404280482d03a44c0c0c18000c00000d0034035200c0030050141004220700c046825025014051103002000c141c468200308040c00091541 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 410489154 1250 410487904 410487907
    0x10807020c09420f030708010e0a03270b03060a050303040305010c17281103100302130204060219060e03030103050a0b0109020301081b060903010c0c20010f0e0114 72
    0x1c3c0000920780359600300301401c64190382010100030542085048a0750307a50008455a03584040402103c0307945002e40d1640341c42070002c00116910203004140c40c2c0c1060030098000381e49641000780002c2d00f600c6103442c40c05c405035540400409030040c00720a40d41c41c0c031165526652250045022103150303401070755051001050000421405401c0032100180b0350b0346510301d002c0c4c4a400c050b4407090640c0c02030030b00d070910303600545c110425202105440c62000d10104500400c1990b442c0d040e4001d8072940d0a00b4803296051040d07042c080f582144081d04148114542413829070b0007511802c8211f1100304a0440c0b2a0b1036081c049940c0203111055210f0041c0c03952540d4034500603a1f41c200c42c1c4021216078a03003400000b03c0d024144207503030484191801602c01e000d82e00c0c091040724010b0254003640500280400840d80d182445004411031a40e19810f09240e050309101005048030078103010750302c0c1c0115142226986c03100300c440307003c0d40c0c170f05100901420810041c0d42981c0d580707012040340c600 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 410490404 1250 410489154 410489161
    0x12051312060506094b0a0e03130603020307120f05091c0203040905041401060b030108190305030a090c17070602121305090c07060f0903120b0a06050c03120411090a0c0e010807020c09 80
    0x107461440c135001d10702d080010801861f0f40500c650312801509503040d507035602d448007001514003a4000b0b6901c80c2281c0b40c180008910201a801224490318801d0143c4d51b0310410010240402c00c00399081600c1c9010204e03032940ca45500a580e0b22440c0149280c107912203020404100700d440140e004145040028400e9a40b01c00d83d04115820034440c2440520a0034019810350300e01201c0341000c55090342d80d403891940e800b07a104014150303108c011659800800b40000305041d081c0c10380c02c0d480380c0d0700d0041c00c0c0840ca81b103002440d001078940c00b2500c021041001803145095a04c03142d04407001511744400643d0ad4000b010141e0084c186d015104505100040c00c042070076030700001c0c59a100b034480703002550030076492504840d0100107440c0c0100c071840d420700c0800e002e4006464800036900840380b601035a449444401c0105440482c4d64005240b00406180340c800308050740300240490404c240400654000c241992303082c1102d060081c104040f8201520034083d6550100025054443e1400c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 410491654 1250 410490404 410490541
    0xd06150c0b101521090b01081005090c0f1c06091202060f0c0c0304050d050a03030b090f0103110406030609030c05010510050307031205131206050609 66
    0x10050225200014000010194800307894840700b91038550390381c519240e1078568142c131442100341c07180407500315140c0e1410f4400e00e2405085141440790140310315a51424005501e80000388481ca12a5070401d01044264100011240d40d0321208850400401f0f44040100e40745010300440c40034000e1560398000c00b80315442c1c01c1409110f100741e10f900f0340c900341138204989854095500e24030040b03200c07000c101c8454010b0058101d519413001501e1a003aa950001000c08040041c1121190440d0280c8010306805210701b203041074003650706203402d140c0039181e100c041c0344c1408014a4802100000562516590700c07840c055a070040d4100021b1070036040180004c0318030360f0300301d81c03941c2004000341000030b80c000500102c03000900140718013800d5035640f0880d0715030381e050141003040900c8984060348102c404003000745100f006440786c1030410b05102c000d80708010403050080b560303541403014200c014201c0414040b9485882e104c0d08000d4040d001e010203182c0d502c2840044251030200c03000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 410492904 1250 410491654 410491667
    0x18060f0a03141e0a02190801090303062907030c031205091b2403130b01230906061b0f030408030903070e091f0204210303050a060308040b0d0615 64
    0x28402c42180c050030307401542070900d0980260244481e07001000d280e00107050115082c00141001c07440d1507906a201c130700741400c46000e01c000b03030002506c0b41d00c1004680540220402907104040b210045a0300700b0030710136002d2007091002010400d0325099241418425501c80703481071300c5504140180c0c01c100c0c101594501c01e0f514060241d1003c010762403114507080d040101800c0505c01da0f000e2196030b8000040d1542c10050588c0d21b101241254000068480d1401034042c0082c0c1014507924640040d810303070601c8131440d04500801d4502c0500009981d0602583c5034040307082c07401041040c0c126401820036200c009000b80601c00841c02241100c804009071100100650880f0402995001c003508003c40617164205030787c2148100720021503040d48501160096070002516003a03503150040c8130000d44403800e5a0444030800c150302015854040d0300c1d00900074050602280d030a41e10b600c062845284942000c000000030945681011500300d1802000380c80741100520038844005401d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 410494154 1250 410492904 410492933
    0x10081002030f130b0106031d01051806010803070305090f27070e150702040c0513030803011502010b0a051216090501030210090b030a0b041404030c1103010b18060f0a03 74
    0x1402c00e1800083d0b40780301c03071007036040340e094000e000d8600c01c0c5d01c0d1182c250020001040380d00f420751401600040001024040c860080313000f14655101d007002107403101e017025410b80026049400c208019030100b9807000a0b128a007108485149114186d80c001031849808210400e540207804070320101e0308250001c50503c9911591154001414580d0420001c01c152582e0740520000610000e000350503e0781c03110b000404a8180f00d490144010b031000c040440582c03048800d1040000144202185814010500102d0b03000a004444000c80010354031002405498000c1c9025258070715036a03810050342c03001d1107015800d8140e280d01c030801d44001d00024041a801032400868501c03005205800ca40100e4a01955240c00c5032904000440a0191280c0d050350040d210002c040a4003000c10400d405640310352601d0000045e28505a0b40d2809030680441c441d03458040c00c0321407a11060140e0030854017418070440340f075980d140001c009410040384290449480d4a0100400a41542c01c686 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 410495404 1250 410494154 410494171
    0x1020a0f02041e0911100201090309030f110303030a06090c09060e0d060204150201090204110c03030c07050a021011010525031d030310090e01150302040504020102070812040501080609010609030b1008100203 91
    0x403500b0f80e1040523800d071010740c000103001540270308041000c50706956102c0c0040344102660b4080c00400c000091441c0c00580d81e03000b4a41c1c1e200303010002610715118000341052a8107007040365a2070048054029106060076030702412340001e500040019644c100c0f405003408600506001000d210300034000c00c41b03444c040b4000c03031030b1900f034810012406e002c1c0e43d90850500700440c13469031740401101013500078080484461041c501c0010040c0e440d51b04400043c0b03429a20200c03c40c2442603101c0c00e4036800707002d6001181c5402c2110480e013403846d4103d040c005560501244000c041d4007081180045240e42001c41d0002000b400410498540204101c0796000c40038458008520303862401c9582025401250380c0a1140401c01400c0030b070480c0b41c0c8640140160355405a4456503181005884220080c100c2c000107428452980c0215060b5080503054801007019030510034040c294140c00e010251003150b40c0000903404030a14194800944400b400f52000304d0b0400d41d401c1c02940081c0da4110 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 410496654 1250 410495404 410495419
    0x13050303090c1207080c010c051234030509010507030c0c08030307120b09011710050f06040e0601080a020405040c0308041509081b130609060f031101020a0f02041e0911 74
    0x650802001448130180d0f0301ca1406000e01301b403090700555404805650403aa280100450030400070500009003840043c44d2008000c1d0846010088a00007115000c1c2480810616101000700c1d521006651500e1820300300306a0303869907424152180d080407030005064600c3d5000c04600d540c070120107036018142c20349800b0240985c1d00750311002e90348801141600544a01d0041007204510303902023030f00a81100c10740304020384000b05101611801c42e5515920040e09060040500302442280c14120761800541419418080d0507519002c0481e000b80c455500d400200d13081c8003500050310011580005051307036031130f940d00b00003000340d031051440742c00b1580000c40010740c0c01d004981038261088110b40e140013041120100030300d900c1c9031901a40050360f905d1020800751824030401001e06444030720300c101c3c5c40ca50b18103480c000d4003850010341150004201c10000504c800a840d401c1641104c01260324458002c1c0c00d071444500c4080e0103032242c2410090800c1c000c48800504c1c02c03a005681c00d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 410497904 1250 410496654 410496679
    0xd1506060215090c06090604080610080712020307030602181003050702101802010309080904020f0d0f02040e24041a0102121e030a090f1b060e06070b13050303090c 72
    0x150b00400100d6003603103150440181c0c0b5a49241c04001084000b81c000c041500302a03c40c0419490044100d69807000e07800740e80d0007030012400411943c0004c026032264030f40341116030f901280c1c0b00c3c1040c0c80000d01145c4c02080081403184804c490980c0e8840250950361000001d2800501500c000d68403000036001381e44581c64954000d02030160410407000c0d1440382404254011030081c01c550b401070b103c400081c400d02c29142d0f40c9000420704850064591071b201d20004d0143c40c1115035020150803820300c100b1003000304001407035015030722007000740783d005940d101c4a4500240e5640c5c4800c4540c050301e0306840e003500008103465204c00110030f03402c0710380100454000034024458521000090f90080100020380b00f0241c0003190702c41040e04000c9030307061150355072091000101e10b044500140c3c08425195801d81051404000c03c0741d49400e4042e0b101e050003040461249090242c0040c1400c000101509494540280420f81c0241203a6580c076000341c43c2d903120300d80d20344464804e11110008 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 410499154 1250 410497904 410497933
    0xe0309030a050d1d1005070c0f08070f080d020606010c0f02090a0f0c0905130b01350a05150d0221010f0f020c0613051603120e03010c1d0d15060602 65
    0x182090044068440100507511a20070755aa8007d00c008946a1850304008103020150810361001029007100808400d07082c00d50021407010180c01a0140303600004088a09650014607103030000c0080c01c01e08150b101c28100f07502c112846050103500882680103100120600b940440c284c0d02049904210704100c4100840707148180d48a03580d4000d1442c05082d00f150519404050083c005060014040074040001e089400d503540300b6641101011400c0945c040e54500030943c04040302004002c2440c00b240800002048004030030302400036840170404646425185400100e40030f002e010010307818082280c003806081c4c403d8bc0201d4205800b82a41c8a032600030f48070b1440c00341d005400303155250001000e1050103450141c40030b202d035007421460070565013a80340146010355410401d41500f100080c0c52802d0321138002c0c1c002d0385004000707010160b0107000c001d20900702194560388401206c0000c2c4000100e01c00141c804001e864600310411103961050b4106c07169902507640011002c0e06 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 410500404 1250 410499154 410499197
    0x303031a0a05090a02070f0602031512030a03020a050c062401030c0e060f04050603070201140708131103010b03011112070504120b0606070606030f1b0609090e0309030a050d 76
    0x121942140c4074081c2840640f0303024642030340c02484800300604000e40c0307455401068404940a5a001d0307800014045510200708103408507280540b06082000c4516200b196070b44500f01d8244101540031483c11303956403080f02111146095682240c41c14100314040e408500112842c011004c030520079802900e5000e40251190844581c460300b403200c802030244051a8010702c030240400004200118155a40c0e4024600412040d40005040500d01c909030008035000f4180000b486002001c2040034106108032025090340308c90880c00c10f540c4980460b0152522080065055003810100008050148041c021641904960900036100d900c03054601d03128034050750800d020104451008210400c13166078001b01c010340414503065083d2141c104550090308101d52119500307441e54240996564040d000812507000c40d9041450f04602030841c0a041c0706501070141c41c4d40c45802c03d144140305a40503140b02605850b00d814a0346132041c1c4541c0c1d00350f042d401291103013980040c2c0c841041c0c2d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 410501654 1250 410500404 410500451
    0xd0c2102100c030509030403150219090906060e0f120c0916180f0e0c0d110a02010e1203010501030e070305030a03050108070b070809010c1529030c030d0c17030c04030303 75
    0x46c600d00740c11500c030341c90301c404035002c9850181c3d001c0040c0710502d030300203500e010060120f80e58a61404d082c03603008002c0d144943c0c480d03400c000c078800e131400c160356400340b0341c40c16004c0880301c02e01441e058400090400c01012501548503003040c08100c010351010070083d545c100c40341d0f0390400c2d92011480042d113984203070190201c418036140050000b0b04554900680202c030b030190301401c0450024412007915403003244520042804034072514803d8090080820420303100c000342500c86508410440a0b010502c580b07410503454070b55070105c80700300f80881005550401c0c150f941e41c900c404800f601511080c4541d40c1c1c14031aa220009040000c032007034601495001c140107182004100044401c1040c0080c144c44030000c4c400d070091200000d201e0386c0c5082d04090f600c8090281400d00c10040d0b04025003110b8003d0300030001c200c0207503901054480c220442c07030603d4001c04400e42071807981b4030810101d4080c40500001401022200740000d0f00813030b031003564140003d02c40394122218810441c3c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 410502904 1250 410501654 410501671
    0x60a0e010b1603020708030a020307031d090c030709120b04030806220b04020d15082a0405130803040c05030606060c0616050c1f1a030d0c2102100c0305 67
    0x140b0200441ca04a5150062200c1c02441220303601034640d0b07407050039a40300c0308804c1d026034400070f030007010507400202c00d81c03c0c0079032079650768041d8452901240304400028203450504200000040e84036016007112000b9021039000403255148074a429112b010b4282d030142e02151900000075150700d040343c0c0c40d03a6583c01812450840d151221100c0c0d015050503040241d0154080c40b40941e1140c0a104804070170b08803002c65680245401c0c0001c2c1880010850219140c00ba404024042d00f003014945503000825a07001425940342c840101240400300c034000c001074000020300040c025018044000c1d00c2045054541580b1004200030f814841c0300c1c50320805411400c0040c815034407108018070140e040d41861858800340c1d200e003500b8603c4c122100c41202e002e03003904940b40b000a215003081d1b04164803402e040c610144001907591800b5a03d48800c11803030550700c0e008c1014a000c20b00104584441100c001040300d04040d48450a0418044202d45441000008180300380075250045450 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 410504154 1250 410502904 410502907
    0x52b0b0904080703030b04061a07060605101d2b0c1e060806010c1202150604060302150a0302070506040303050105010f02062203090e0a0c020708060103020a27050106020303060a0e010b 81
    0x10b130b8003540a00b40d030503c5140e0040c0d0b980c000103064140210000001c0400245080c1e440e003651505c4021110701d44c00039402404d40711060480d294024590080034904088904442e0310120b00140c3c42d02c2c14030405400d040300c0000880c000790a4420382c0700c1c2d500d01c41c84000c4080d81e100d50000340c0500c510b40d5900030340c801c401400c0002030701440c0134030340080d010301d8207014040043c0c5402c00000015411680160300c641121300d07600307943c1c00b0120f42000d4101d8090201616640010302034405640c1009001540000d40d10100c9000742d04503654140d0040a64610b45400c1c01d015000344024410940426241e0b035070301e00294800305c0c42c01e10070710b03821616003900600d0030306103020503801c107800b1010b0180308180894000e000e481c3c40c912603007940e04c02003083d520312a4001e00f04603582c0e20040d4141d009100500059541022550130340d400441c44011540d02281c07a440700c50819041014403510b80000811090f6001c002184149829600d0300c6081da50fa0105c03002c041c03c01d100e054801030b030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 410505404 1250 410504154 410504167
    0x310060806092b0e09042006071205130f0e0703060902070c060e0112050f011505071e0602190e0405060a0e06090c0c071203080106090806070c03052b0b090408 70
    0x120f107400501400c946084808a00d9200103d02844000d541c16940f885070310314541c14015034646044001c800c02e41b4224100030349640d480103640038014042c010f000e004200c81a404003507413144402840e210780780480c51503071606401c01d00b020980c0d03814006030518101081c00062802180c8200307031300010300740320f062410340110380814400042904003e80305407981c3c052072890250324000e9070a80c07001007855140043c0780c043d0081e8a948034060240a01c1248003040b00703031003408605d00015404030328004461804a00034402c0940100d4444007109440e8607043c1d01030000c282010302036a0411050722803000b000010082c034032030308080308206c00006120b81400031741c03903401c142001c400030b0905d01808007944c188030383e07600148649c42c6c50703028000c2030691003842c513401803c0e2070501410705030800080702c0d2150381c01040c040611000b010403204043c031460803942204403102d10300c140700440b00c061a0005198041c800205e50514021000034940b8082083c0240c1d88554860b15151 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 410506654 1250 410505404 410505463
    0x3020c040f110708090a0504050f011a0403020d03080f070e15180a0312030507030b012a050601060306080c12030412050c040911011101110d0f020405031006080609 72
    0x101150414140703688550345404a404160301800080344036241440e1214054800e0103c1c0c480507902880c40b03242010107002c0c5500c0c9034803045044d40c01f4400c9070b920f8080d01c05030700c0c061446207500c004e42059040e40c15001380350340300701c2407402523117550000d400396160f07003004503040702c207482c02581d20428040000000001d50030041003050360a82070f0815101c81c1600088030003c0541c410b07186180c41c0514004055410b1207241c1d4401c0c41400d01300316404603030000070005440e00d00380303001014080103840c1900c0281d0f0a5503242c0d0750301a084410540c0c503203000038068109481800014440d0a61101e40c519003207206240096200e0015803c00740f0f407403002112202d510318241d800b8020b20b0281c0003240c4513802b5044020f8018500070140ca2100000185502489623100065034984007010107051000d0088610104503410045407810010110f000240b249902c40707a414401d007288a828101c054000c1411104500c0c1581c5071580c41c0c402071600c441691101c2d0318004502441800d0b030a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 410507904 1250 410506654 410506661
    0x2040e1803031f0312080912160308040809040608160501140a030209060708190806040c140903010f0603050a05070b0c1207060608060708091b010e0f01021915050a050403020c04 78
    0x2120f44004980740f8694035160701011000c08600c00380007aa50302c4c1000f0030540f0030000e038405240c0c5034151a14002180c113248542402c440c1000f020800d4120204c2d040c407030710105442e24400010420808259031b451010b03a03440014504071011000660001000c1d0700540d8441074015244140d18600580c00130220300a40c800b82510760b0140040c40312001040108001e840001c0288000a0050140100241052000501d407500c1a4140500491744551201e0703100303d03105219003050f860b0002c80d0700080c050600c440002002c00d03d000c100001380440060184035442c051000ea4183c15104c1810341f0040c03007a5881d11080b5441248501440d80d031500c000c003190b0b809040c0004400c0e80360800103050200a40304600000e18003010f0040d518810300c001c207001401500c51504040340040041c00103900b1245491080c80404110b03201e6900038044841c07028200c048045411903c0d180601e00c0407041d4800c3c0e110186860005402d5150920840b40a26090780090490303004030b40420014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 410509154 1250 410507904 410507941
    0x90f0904051e0c04060b16061109060a08060f01110d1b06020a03020a03060503010e19060b0d1505280531031101020f0301171c0302040e180303 63
    0x52180701c200791160859080e05610080c442c03000303401d400b16404208401e640d200c0c0c004841e07804d01005404101c02c0c01000c5030030540da020202141d40d11035030703203441c525028209210350007c400058604d081c6070b100d01510b04c10103080342c185550850410045680c280c0e000003041c4d080c0e10503407076140310f5800b48120340ca00000081e002c1c903454821307030385101c00e0346c204280c100046500072840d680c01d190036000d01009090198002c03c464005400780541d03441c5180441000c0000342020403080c0b00da1908030040101c005000512100c0040c640110405020700d541114a458480800c03510300160f0200036103102e2500340a6801e1301018001d00040c200070740065081d125804122071810352100c10320142132086020714840355100d0170080d0203c054284030240d03030b920400843d0701140130407060301e041d00c2c000000901003001c000000c2d4902031030000f00e0010030081e00091800076500d41c008105035144000c0544494440c241d8882e960000e01c0803a0300c0b1074200780009418114400ca506a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 410510404 1250 410509154 410509163
    0x19060902041a210606040f02040e0c030601090e070503010902031314030904060b090607030507020a0f090516020118080d0908030a0504050d0f0e01080c0d0e01090c05030102090f0904 80
    0x15429155800241110b004185081500160703020a82c00e40c81d0092101110000300d04011445018640e590350322080c00038101d0780b00701e0356030051480384500d646c10750700a07013245907105030b013410111905082d5410031120140025410303a404602ca261400d01a409516607443c2c850559090292207400317900024003108050121040c0440411240000e91071039901120165698584003004d21050711913642001424400800c00c5480d140c840200b101c0c0555014500551215805c0c400511200410b90010202c114440ca0100d20a0410380c0107600032203c0018952101e013450b24140d082c0d030841000350341d20169100140f0007155844006108200b8803900c0010051382958604200c0c1d081036034995542580c4004010410a0403c50006480a18106940c0c03071240d809004040600310f15610f0704118012010990a243d07a409a410340008a102884918102c10103203000b46403221061b034407c90207000c00509070406200b215510803000d400c482d5000140c9040c40319810024104a5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 410511654 1250 410510404 410510411
    0x1005030a030c1709060d052205070506030c04080d020106050319030f030f0f061e050a08060117100203040f1a01051804140303040309030c050108070f12090c06050a09171906 76
    0x10300c1541c1c1c079070041111440c21b0b580007405050001e901c92000b81289410004400d12900c22404110b0010700b500803183c3c21900e0903600e607544010094079010702d038000316080c401c0d8403914070025019009001a6902602101c0e00a40768440c07a5800c0b03591f640c00600032074080705e0740300b100c1482500410f0642403c050086182c2860000c440200c800541c00808180c01210500741c0a00310900d81e0002840102d40803043c071f6080900e1781d40c42e100103200e00d090146070f0080302d569512051003035015087c0040003c544911340380c2014980199000301c1203501030b40130710007844414000031580d03050359400b4001c940c0c0186207401c807085180e4090b10a8501c00c01d600340c00301585408000a51040e07100c3d59030901e00714070f185480c0c85414542c1c3c00c4a41800906001c01046540c00a009540000945420b880c486c900c61a108000c2c91070400280410050403c04160242c0000013407130b204c4d82e15a00c2024085ea5894070040700c0c03920300041d50154200790301e4054a20a4041d06181180c081c40001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 410512904 1250 410511654 410511667
    0x7151805100b12010203060a120501061a071505090715030e0303041b080607020c01080a181212052203020717070501080f04050c1c020a0803031005030a030c17 70
    0x5a00d014903007804049115111004a420342c10301c010f42180300d8066500950460030402c000618101050050100c0d0388080e072112310602c00300350031400007800c0034642c0016107122110000101e500241080e130315154150045840d010036403241d14800c006940c042c01005050100d031140c000300c8041880c0406848885c2c0014031031041c00150300461083e5054a56100012903032102c02c0700c00d0b8882c54003a0005000c101c0341507004901c1000d8120b00b460088103a80c0c490b03900b000204454514501d00300c507201b03c1c0d001003151500d02000c2d003000c20b4071980c24101602e4100000d4403000ca450300d074002c00302c02818110400c10700c088020244a40182c80c442515121a0b4101c101c007481040342992100c0010401540c0240e8a036401a1107120340c100d043c9082d4550035a038040303041c20240038007000c0103010021009042b5100441c0c0e801411900c210799100e881d035036617400c2543d22852040c0202c500003511311700054082080355042d00c0745010301c002c3d602d90600340c0980c0240d1000d000c03401c0101 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 410514154 1250 410512904 410512913
    0x1b0c050f180c0c070b0d0b1f020303011e03060f0902010e030106180c2106140d030509190503030a081e060d140a021c1b0807050d060f0509060417071518 67
    0xc2d004903242c07086c00091440007541009040d0350040100201c50703807075440d4000c602c1e60203c1141d066035406072500449602120288103080781c036a1000d02454a003d100c090403020603006256410f000740d840000410315201094200c900d03500c60005106010240d800c40d010aa4200d10101d09017410018a0741c4030010180740071080c140481c61055503030390024400080704603080311028600342c80d0103518800e280c0e0003074850700c1012041442540c803070f843c031606141c0307009401c00a03185c040c0559842744107404010b441018152802034242c403907991800c038070111441d030701c41c49520002c1c48103040b00190b44400c0c80079282414040b40c1808dea80d911400b503141e0800300844414003140d03844221189092048112402c00c1552007070000d540c2d400c012a4000092400a80703508a848802040d0646088402030a9246060b0f040e1400c0078200040c182c00421050320441c054080404d040d000007613141c0c0742c0e108611000b444407800d04282e14900000b0391001f90842d03c40168608c0307105154a4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 410515404 1250 410514154 410514157
    0x10e0616050601030b0f010b0307052809080105061c020105070f02030a0f0302010c02060c0a1d090c03060a1d01030b061206090601050f0d02060403121b0c050f180c0c070b 75
    0x10507503007a030140c801003007000b41d529103041d030140703040d03001000c20350401030452518400601481e0030043c0100d10076410460985200c01c4081d4071510029515066075405012100c84e48600922941790200141450400200ca24507840c203850b01810a43c60950040d2042d0704019001c0c6d801003581c0300700c140140c50810103044114010b10440511504a00d0003d0039900500e95050440d0401004d10000f20010070a48821f00414140142000e05007030f107000004100a0b040c03070b800490602840148401c000c000d5005220596210310740d16159000c010045000c2d2040c41c0d070107035071500104045504100b5007604141d00900141c204441d0030491860810180c0700c40c41d40c1d802150041045242002071704104820a0b604402c080402d60005803c40c0501d10028180010a805c80b01281e4030504000c4130700043c010307403913050215505000010400c00d015150142840b02001515840d202c004044096541000c1500d15076444040c07032401c2c0c010404170300b411302c960900441c82036039510 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 410516654 1250 410515404 410515447
    0x408041e090501090207110d02010804150b03100f050717010504021308060403020c01021e15100302060c010c02101119030f2406030509032205060a020102071b050f010e06 75
    0x150151b103942c1d650502280c4849407406292040c000509043e0061341c002c0e10240e80541c101402442501d8820341c0e16000e0000c2d008a42c0e40760080c02d040e00c207a400181c2c85820305c40140c400410072961008410b9950303d41d840201840e240e1020010000c41c07038682c000b0000c00400c0300742c0b181d080780d9a681d11450000d040d102103000d6003080f400300340103581c1003280c0c0c021603030710162404408104080c83c07a2a2035600700c0b0001c8407a030400002c0c2d04a030507003220f103004540c00340c4400d5070303150440c11940c020400307400090b00601030920552407a8903270f0b0180c04216040f030b0380c80c60320380701d9040c00003034030304030150419424940c407403510744603203400b03440f8410490224081c007640354042e9401e08081c0c450250070180515141c001800340d40f030000015030350500e0f1241d0354100600c0c0d10541c3c1c045100402d5000319400140040c07031000e940d5041d000703081018410741c80001c00050041c0424071401a40c010190040000c0c1c4e5100342c00c4d0711504140300100c002402c0c0c686030031b44109101c1c41c0d180700c88 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 410517904 1250 410516654 410516669
    0xb030c06030c03041704050d0f0204060f080609010606031a090a0617010207050f03121b0708132105030a12090b01060203090306070c20030f070e1506030408041e090501 74
    0x700c00c020a00900c5210717082e80846840107989000d00b0301c80090419000c40317002030034000001d00744d5400c640356a440074014110260070303840314950394441141d40e6a41160625015400e01100080c2c0e41c1c043d010754002294210700c40740940010340300348111410f005200445003501c0705c500040000074240503401e43c080c0c850000da07072201d0728144246000801e41501c0c4c416442080303c8003460700d0604a05c0e4005210030302202d0080701100144401e40a0f4800c0030b8181800050014481c25000030ac0340119081041c071f40b018001984800984900350701c4003d0301c5c640040115440340f42c0b00d40941800e455811600007842c840a0b02c8400702150260400c80159000145000d214a000c011041d803003983e6240900402105a03203065400c00c101050f034840c0c0800110a01c1159002c1c00700d01a90500c0c24202c03200c45a40360000c030720991080d1602401c05010300300c042040d040444c12680320b95009800c0500d070a00c0c5c09030900409920304841001f1a0801740702003481c1e00c032800340d6070003400f04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 410519154 1250 410517904 410517907
    0x9111002010c0306120c0302040b0d120e12031204141009110f0d0f0609031101050403020607080a021e0d02070807050102030105040b061603030b04061e08070e190b030c06030c 77
    0x1060000f80440e030036034001010408a130340740c0c0030016034083d0f5405c00b92941601c0c042503802c1000040b03503c01d80032443c01001035071507045101c80305501000100940c03000300c07040d0305000c00741004030f41c485c441d41011020690103000043c0101c1c1d190001e00041d11491011a482072240a081c503088540c1c482c000c880c0b41003401c6003420540350000da020f0408500701d07881070011240c1d40c0c0b240084032001a0040c001911034000c6c81c01c0c03500500c000071142107500f009004030f00c0c0900c0d00a4072294112044804285050007142c000701c0c6501c2030740e16100c4034420385025000d5121103003d040e004400507285d541e4003005903400041d006405040058881d00015840c1c6d410801003106450b411043d4600580050280503d803080b651150801281c00d401c6c00207c000403140410041d001e143c001e01c440c0c0450818081000e51001802c0d401c0b030300340e1400d40b8400c035207031415008a174400355034a10030700421404201c2c125055911400f50b000340203003108d02d649042ca01182903900212180c59030f44a0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 410520404 1250 410519154 410519171
    0x4060902121002180901061e020102070804091d030313020f060f0a02060702101107060f060314070311040c0c080f0712120b0d081b12030a051f180911100201 69
    0x169200340c803d013410120b41006296060036002401e28206000031a44142c1600c00072565500030750480f0100781d0003903202640d0b26241c3d1300d51030240c4129021003104442c8100080d8203c50044150382c012030580c9826030041da000d40822170f030040380b0500607a001008200d81c0581042c0c85c0018090020704ac1c01074580c91500c40c81c042d0402041c5003903030070803505000040c0d2540402a0481d03100035448440000c4202110314901c008020940004100d9014000320405030349000407101d040700d200701030300e641d17400307004040c00161980c4460341c5003c00c40c070b07443e09000603440c1009024118450b20302c070360901c1c2c03c3d40c8829189002407040d031008030b02034102e00b4240c1c000602031011030b92001c1d119030a4510896960160903c6800180780304401070180d441803502040c06001282c1d4081500142c6030b0819030740b25401000203a68420b440462641d40341e5031141c114081c0b004560a064401120320064600c200242601c000115225001198040c01ca51f03120240d071882543c080d400041c1495 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 410521654 1250 410520404 410520427
    0x7090e0c0a120305030103170705010f050a060611071401140706060612020717130302090405010209010905091308090625260f07050c1c1505060904060902121002 71
    0x54580100d0b400e455426a0500442c0c0c200e82142d0460f684001c080901c04a00c56070881c8900071050000c159500340702661841c15030139003285005982e0b00104102103a600c9800b40e0b01c5c3c1100c1d03c0c04c440701e0340003080c040024080440c4504090001130400d0b11121030440e0301080c0c140d010000c1140d595980b8401800060b5120a0b10240100c80030001c5143c034100c0c0e01c03038030b8001d08944a1024607403000203906450302d840b050304600540c0c1c042c20782c0d134250525180c80d1b0702075000b440c02240002d062040004051038034803d024000c10035080c0c01358551940d516010203c0c3e000f10195070b0032440401034002d00d030600d6588075249044284801000003854a03248100c520841000c2002c007800080c003c80c00034184007200c0021210301c44640c0c1e11601881c0050410300c5030b40c402c0b1791040001110040c9030341d1940346280010310074954980c05080103141d50040301d41c251002c81e041404000000d0001303a0b190300c00c100c0c03980000c2a02050200321849540742040d40c405030080960089481044030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 410522904 1250 410521654 410521669
    0x209010f0f05060a0e040504050c040c0207050306131502031e04141c1d030708010608071a040f0b090a0f1502012304082511120c0f1207090e0c 63
    0x500341154440d1501d041c91100805c2144400710b4103120b40d03500d80c00300741005010030001810003c090000c0c0071003201504080c1d01c400341d901c03429000c0d02a600c001101400c1d07410143c03d0440c1c8c000c43c40c02501c11804803400007900300404510f607000e01d25801607421030348514860b1180e403081c03800003c0450440280307400c185502020004803003840032000d604982150411402408a0a400144c881c2c2d80d80001c1ca014020b90100c40c840d440c14001142c4030300e0200794132060380d040b101a0000d0840b8280200c2503840b880c4105000511010020b01080c120100117105a002c010118400243c403408884ea0b2a110740d8481c90000881ca10a051010380a02982450b40715545c1490003044a104074010607103c001c00c001d00c00e075800500300140440460000754581102c4110035120303500c5140c80003a44070034142842c442c0380c6890030b129544d600014020403075980a400d4002c11204401445a616600046980a0300500b500820281c0785841100402442c04000f0501c00c00207100b0300288 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 410524154 1250 410522904 410522909
    0x70c0807080924160203030d02191b0b0c071a0c03011d0c0702010c0302071a030109110c100b0103060306021c050903040b160c0312080405011d101104030209010f0f 72
    0x55804400700c80504501903030004c84a5807058200c0c084e05100190862003141280305080c0d00c0840d49445440e540320310944034a90646070003800c2d289070300368000010010031004041c8131400000444494204024085c103601c9190524510f01250303101d50184030040340c40c0303071100030040010800919101a1740380014151849000030b400e210249a103a8810800c020327044c003008203181010980f00300001401084042c04850100941e2071018200c1d500a114610300542085000e0b1204055101101c480741c10301c0004002c5403c6a00ea82009000303811120b03414103680301c0001011a030240000c220044e2044002d450940410035001e045800180c040d0300355610a100a001c085180da085442d00d2001e280103603903210036450a104109010341000b841200850b180c00402500224941e001b548500c00a000400c02400c2c818050b04a08409012503030086907004192060b03540984403100c1400384040c5230a490f50046204a0030a030f00003001a541c0060800c844510040d44801 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 410525404 1250 410524154 410524189
    0x50d141204030e04050a110301090b220b010f031a0d06020c07060302090310020301062102072306011e0b03150d030c060e06040308010306050601030b041104031403120708070c08070809 81
    0x42d000c82000314100b88d000501070585010382d24002c0c148195a4114170030781c5204005054407101a110340e04401424032408880d01151b04182c100910a010340102d100d00c1c500424807000070310b04a020040344a1322044161015a0b00300280c16418005106040152105490140c2c1e05e14800c3c0c1814901601503030107545c0584144018031103213911001e081501c00b03030800d04918038441c4c85250305c024814124010000074000e10640180c00040c0031074560070b40a00103865003685d8485000e000705244010900c81e8103200c402c14001f240e000b002442c5c03c0200540c074000c0c00a440008100d0445d19072030190041032359071041008005582c0140b06c0c03050940c00252040b800c0c03659000c0c2420f00c042c00020909512200083c003a84d120703a211800314403004100788100c840e84501580258803500003602c0d9003000303210b15138100a0000032129410391100c480022599010011136111b440586600100700303000c1c40303a0010411040103030a8047c0165030a80e43d84001e04204448100058001c28 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 410526654 1250 410525404 410525411
    0xe120f0c090109020f04060f050c010501030c060314010605041a210f090d021b01030f060905060f03030f07080912030c06071205190b01170109021b0a050d141204030e04050a 76
    0x41c0c005c28084c159400c6600c2400c15910002208100f41c6042c000c121640019610f404000000c0c08180c03182c81e402c41c1d0f502e8504000010448000200e110402d02904022070810801000320034102c14450002000b01585242840540085400c103000d00c2001c50401c402c00c0400d204104202c000600c3d00201039034000c001c0382e140c0100103512071240a00c1810307442d01c9400c0c904941c1c2d010717401c08180801c074081d0400c03010b80c07988100c4c401000107544841c0100c1b1100308070022401c00004850b07031403a180c1005030a001e4217640b5680258070150080341c00910a41c4a5444442d0410252000c10f0300080501400d00d0050f138000c111250a003801ca2202c3d0800040c4018900010401950f1107100107020804c00c1a400050b00c800c41c0255042041007401030001070107800d907a01034801d81100044441c4110703259059540d0b9800d100c84083c1058004190b0f06601038090003007046546a20f1040c2402c141c2d01031035544884c64225016030202e076111400081500e02480341a503c141c0d82036042 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 410527904 1250 410526654 410526667
    0x216060806090709090518070603020703170402030f030412110906060912032217070e1311040203041401050f0c0403031b080f0c0d1704030e120f0c09010902 69
    0x2010400080c00a40c060300302c080104500c103100340480c202400008201384843c0c108950740072072840c1c401ea441d010701e00070314001007980c5100340200da582607056640c507800c00403d680c400034203060160089070305106a4803400c80010301030001c1c000402142d8148800030030141482c06000f0100861a4850140c2c0c8c0d0401401341d546809a400d030ba2015102d03003100a5107413001520b184510040c5074407440e12000c0109030300103003003041c5c803d885041c01c0f54041c40ea0039190181d59008140560b401059080000480044041d9510b06200340a000c2e9008001281c41c0810102d038401e690950311103005a00d0f01c01e500c4802d00941c1e070000c01c0001807028a2170f2003d00c50010340500d01000307080010038401102c0d100d02c007080750b0b081603400145207135076400f40b20841c5c0c920354003011050310f81d8040c103d80208842d0003500e01d25040e80c014100c485456a45075021500381882040c074503407045401800c85810078041202e51380d030b514a5002403280180d200f04020303201c541684580c0c2981c0c01040b80 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 410529154 1250 410527904 410527907
    0x30305060a0b1c06050406270204152d08040209060f0303030a200408010e060f0c0a030902040f0f05010f0e06030a0f0c030f060b040608030c060103170c0319021606 72
    0x22100041003da140400f5000b2641008000c0c000540c059135000d410481301040c031603042c0c00f480c0403032603241c1c1551a4420050f0111420fa029600c10700200452840500d10030602901900c0e141940c2404444140302c94100360070072054030420001c00240d1218108011410001c02403600030070201c031940f00c08492000040e0b501c1c0b0009258812180c5c4400d03002102d07001c2c9a8804003c54200401c440d01e85845840c624024000003540540c01c3c42100c02140f05000342041041c060344102c0b4549103885008d6100350041c102c5200300702e801c556554130090110106105019003030301c0b40400451254074180b42c142410086801030742e2000d00c5082444820780d400525030300040c0d4003904040002c54141018a031140c6d1303a0f072018044400c14040481000019441020b40e008101c074100304a940300c000c00d540c0ca001e540d05d020300941c458001440803403803000030a840803032401c03103a900c0d01c2c070040d080504540244680b40140c2c2d503003484450b00603406000f14910310208038500041d50389043c40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 410530404 1250 410529154 410529157
    0x20102032422050702060105010804120c14010c031401050423060109210302061303020a0330020304020a050904080304060b01120e0c12010c0504090218030613030305060a0b 76
    0x8038948911600c41425806403a5840c90b11000c08044040c409840d82030a108000703000c0460f0010018018003001040960082490b140a550023003070304d40a91800480969071220800d900341c1d03010000190368802c1010900501840070150b0b903000c05d80a00da894940090501a0041e61049040004450002c1d000300b20f03e2a2400c1e002020030740c0c036150000113075581c3c031494001c0003070302c1856035461416280709422101140d100341d08554140d9200c00740103512044503200140160081b05104010900c0b03507203000d141030b10204130201a10924094000200f480c00c4d40416590340120421040d031a05212541c000d090680b08102e6501c0d007030703803040d415210040c03004001940d80d035040c190036442480e013520880464181040403503a51044955128100040c05200d1344c071065660001ca0018001c40428100302d0701e6483c00c0c035080074940c1001e0341092811204541018a0743c4007945d40410085000324101e003d031504100c02400c0c0101a10001001240144400b0300c04002141c0480c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 410531654 1250 410530404 410530441
    0x30910080c090f0a150503010f0e070f03050901060b0c0d120c140711090406020304060c0e03071512020f040f06180311130f0204080d0306030c05061605030c1b0102010203 75
    0x701c50058003140f440010f00010056000780d850048134070100074249030080c00550503260080e52032801d50b0795404074602100022540720740001c0c410403100507034602a810550f006403440002140c0d02d40c49079840c1c101ca0b0442990111070b50f20400280700515003008ac840c00c46180c003d01440030300c0b0041000f41c101c04050050115640000800c0c0c3d0510807113140c48613451800a00010590400e42015806900155425907960703103880d0704960450301171610000c0594000d4081c15509141855144103103075040fa100b014401302c50005841030b01c2520082508503000044261201d0800e00d58102c00340c0c280d0810301c28800ea0070000401c0f0394003000c0c3e80c0d040301d0b4803610000748035240d01c0108150721a490b0701811283d0034001900881c98581e00904103a5100c14101e4045800800c0110700fa10124403010700308841429040c4020308050000b40002c504480b185c444540503075a50758138640c800c1c2c0e56280d2642000001640c000c208604056040c80240300075421405d20b00014114101d008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 410532904 1250 410531654 410531659
    0x305030a0c0c21170c07110103020a0e04110d020f0c010c0c03120f020d090501330e0c0702090f010e100b090f01090b04062006040b0c0705070f0602030910080c09 71
    0xf00c42c0d040c01e4415407240704600380c401140c0400b41030501d0035607400d400144003100c000c1048000c451155100f84291400803440d6614440d05103070f2981400020554100080c404901c100900b954100b0343c0d0004080b04410914140d0341d5600801d00035003180c0015061004225642c0b0014000c26440074502c2c4d00f498141c00e000402e5901d006400009102c2c1d405200821428541c0c0807051003410750080c82c44400480442d564804125440c0c500e0030072004049820f02c0c1502418040d002100c0d81c5190720050a8110514003505500020150241158407508401500340107001c05003450f494a80c1055503418007200076800c1540e09000380c0a4429003602454440c507030b26110768030591070b0310010104030341e56039540c80c0c0707034040145007001611204400340d40c01ca00034510340b540020304910960700007114070078a03243c07a002501e4580c007058064802e03118090010030022144a50400281110b800440d5240e6404040c4102301d800481c90308103100c0706408100c0b810103950300f05c0346011802c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 410534154 1250 410532904 410532953
    0xa0e0a0518040308061c12020106060810140f061903060509130609020a230f060a0903120302040509151206010806071223010f15090501030f0906090305030a0c0c 71
    0x40c4004501c0340b00c1001131b251024400300d4011801d00000c00010031141480d54020b011941d00e4440aa4074072009503411140c80c5582c00040001d01c1154410740d04101c401891444000d0400d400582c10740c2003941e5100c040484c41001d903003d0303a014400d078002010161503091030343c0b809104010710311400d031501a10840d2500034940441d03980d1780c0481c01403c01e03d4800307803404000760360140100401c00151402900c01402084042c607012007516442000741c0d0351024054110b07580d180034180302d40b002c6e00c180340d0280f001091340d90710071403101d10075011400c0c00e070002c1c03104004000380d141d860000520035401000c01444582c00110b55598080020700b0440c19950075040203800800488511100349004c0001210240d542e003000076040700d0740091460017080e141d5101c80f41e00100c10b03c4c000d01141c014601002154007030f400402016001c544009818416921650243c4805240c100e0000d4000002c10260580134402c4c2a50443d00745004900400d041c1d481811502c19034014007250000d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 410535404 1250 410534154 410534161
    0xf1d0f06010b181809014712010906020310120c090203090a0204021303122c010309080c2a031002090604031a07020d0806012705060a0e0a0518040308 66
    0xc1d440c0044d802a40e60070584402890508012802032110500c40c842064103074038504100303100b90055801c00041e9000707480f4030424180c00640103080d801001608400c0ca0550400490405e2140301c802e50b00030600503a070392605086c8017100380700c15000034400151a11883d00070845448000013500c05428005a880e101c0c020510300d8404d0300700e8000e41c0140001905c00d40e4100d05565142168850000c00038504000c880c2a100b41f40441004481e88a0b000c0381000e0040c1441c80306c001005042c14001103203109034655400c182d0100021444550120207a061040f240782107111151a80008103103200a62400190300c1c2d0f01d01c19400900260085044c2da62541d401003280c00642e480f00440b50403052014100c210b0000440703105000d40034030788079583c0d644c2c044c581491140744144d54000c981d0604c0000b100302100c0c46080c03400c0d810003202021440f6155040102071442d200c2e16011424101d1804000607100c0c260803040c0140304000f21014000b0700b981c0340315009941824108040e60b03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 410536654 1250 410535404 410535409
    0x4150b0a09050d080732070e06040509030a030506010e0907030b120102040605040e0406021908091b0a1e0b04090603260906030c090a06030f0b040525030f1d0f06010b18 74
    0x84007001c00c0320b211540c901b40c51000c400b000400340b0450301c9001258840307a8886c010441110703403c07248681c0c16001008003c01451003603014a50102050501000c40341c017070004100410011035440001c25510b0202c900c10f8544500300803400b6101c4030083d4502801c000d00180180943d10030300344003400000100d01004140d8065402102a080481d00618060040205020010f45800f403080c0904074100240450180600312a081d000d40152000d41c40c00c0c0c040c2c01c1108440710490380442070080301180034404040240300174a010310b400b01d4040c1c110700345001c00030540351241c819000480005440c854a40c010303502c150320100c8605840707a4a021218510b8854403501c0350313100e0001d810100d400d5400d0b61002020300c1c01d9441c20050714102e101803008a078001d990101d25190103242c03080d031000c908101c16008101c1854080307a400c44a07104c02d0141d54180d01d581405802e969444409180e080160303050004428005103165450464148014804c01e411021540e865420401d13498 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 410537904 1250 410536654 410536703
    0x40309090e030c0a060203041505010308030105060c0f070306060815090d0305100b030403020703061a030a060b03010f1103010503010510060906030906140403082d06060904150b0a09050d0807 84
    0x100f003800f040d01c201320201c3c40c0850003540110342c100c9004041852081d1070000c0b9100d4a4142d9502108081c516400c0204200d0180c0204544034103a106843c44040803080501c81080114843d50010801c5030a180c2d03150b0401422804000034100d2400400580c0d09000070b0798040c0f144c0718107000545841d80344410701030721941e401440000c1000014002015400076601c42168082c40e010080c60b10500b1080c40300c040d07a001407551503408041c000c1c021540c1503015801e81071004000060560801d041c3c001076805250701d0038aa00e401100400c4282403c2c010030794410f03070088282d0662810060081c0c06141c2c0c2d070050f401003554076140c4000b0403031954015030b114428480041402c1c82c081c60003d00e00c03001110708504442007080e540240086149003900120329a62202c0b200b607a501040c003403e9002451305607803050725080b510001c100301c6c002c402c1c007034a00712444035550a03600e1005070078078616502030340c0542e01c2010000041404c500c140d41c7c1c07050b400307020003801c0c02c07800c404e11050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 410539154 1250 410537904 410537917
    0xe07020313080d1d0916090f0801020d0f14130201120f0b041409031c1503050a0516060c151d01020d0b0303250819051b06040309090e03 60
    0x64601c44402281c00b000002d240707001d424883e80c5180c0d8a940054850000310082010789800240034004940740101d5400120707910780031841e01c541c8469480700c1d01e506000342a401010607940c00101001240f88a01895003a2105054140304190149014641404008180300b20b0b542c40301c520001160320078109040409850003080c0b0190880300303140310003450f2000d8018030440c0751994104201280407120752081c043d00010350b0524080111107442248440482403809540341b00300140010800c60b42c0e0090b5001e1030052210546500d0300d40e04e4005648043d034100c0551103020401c107640b042c07011624035440202d94a1810450b98907a01a003051301e140701c0760040c5c90b0300b2480c0030380d01540a01683c000d00d0030103020761107020080c076031a482800100310303810100d074a40407145400c0c1c1e411184440d00c20613601d03190000407004a09990307648540f40c07000a0000030500030310200c0120400d000468200901501d04007507901034400042e41c4a041d1101e80c44a07511050a041803003940c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 410540404 1250 410539154 410539177
    0x50105010b032215141e04080d09030504151701091b0302090303070b18010c080f0a0e070902070f020916080718030803180f0604151a0d0b09010c0e0a0e070203 70
    0x3101140f586050505c0045810240b00c0c0468003035032055030302028030340340590341001040380790050b4601c1d0b040c0a040548400e500f4400d0800000a420400001d42d45c00700101c1d540d122610506820705d0408001c044c1c0c0a2081ca40c10329035003451034442084440318070544d6003401a911007070304000c281940245007002c0c4c40d0384c0040d4100540c50102c03e00e900c91541c2036030300030840b6440c1090246c540450513518044a840d0a500190360300001d9405400d07110020021144140d694200744c0c010381e406100d0803160500c9071a2030804504103110060740090307041c5004807600c0d0740720708018146c4100621701810812101010b003044080a0081006190003110455a03841d010364103000386d0400280c991151f101c0e4880208400001107003050107141d03c03a101071204101d0079241c2c0040c020841150207460070035901003807242d5486404402192043d000c007203403840c00c0e81249007158080304d480d2041c0054039007010519030340c02c042c0500740d4a0010740310741d442e1102c240032032a60041001d82031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 410541654 1250 410540404 410540411
    0x90a0503010f052719060603120507021e063a0b090a0e060112060204051e0103050f06010c081b0a2a0609090e101107050105010b032215 60
    0x81e0b401c2c664000520880d200045400c0d0412400c08880b4460740500c40c00d41590444d4001300135060b00b603404000d41d00c4c052240070807081d4680d00c803001036400c1c0c4403405003c904000785e07140071030030210b8070003000403d4041003180740e41001c40411070512448800c070340b15203a05070442a407161900c625201103064407200c581b00c8640002060000e110140059100761040c800280141c60039000d064884141380340600308030307403801a070581d920140800445072550207010118160305c51100c2c240824804018000b26603481c4c600240464030f0191020300840c058804012291740c124602c078a1550b448501d03650b9504003510300007500d5000d4002a145801485803c00901804c90300d480503000a8001000002c8807040c03041d180d01840380b0801004c50303c05482003140c3caa151744441e003c0020f03281a155008241c1d0900412599020101724201002051013424888240705d010702502220345500e183d802c4c0346600d50a42e040d84030140c0314401c40740200804020311008660382144100b802030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 410542904 1250 410541654 410541671
    0x3060103050a090605012909030322030b280506010f0e040f0c0c12020714041a2d030c0f1002073308040b04032312071404060f0302090a050301 63
    0x74565101c01c1c3d60601040f09000649041074587c43d045070413134031008005514199610a070800c044024000b101c21a510601000011405520400c0d2003940e00340765440043c03054804500c500003880325034070b0542e0301c3e0904018169801c2000400550010300f0030342c000f41d00c0100050050b01c0c1010401e0b00041c00d0107448540c1c0c5400441c42c81da800e11441c404039146068410403030350790080b1301c03c51200700b034092090006420168024404030003203901120f5201c0010380860020265a0000303032005040c00c03040088014000c001d4041700c1021030181070000d00000014a01650010b0224445c0d2101c0b1103100111f4000c00500b00102400010700170054000030f000c103900b00c4842d0012017007021102c034070000c4500c2170601e50300c01c40d030000740180030f602d071078034101c0e46d9805085951001520b40300c840012640480041e100004217140f0440340c41c503100c200201611807102c016100000d0030300c401d20040e500320344110700102c0985001601c400c1000006190340786036900040e01540780280c1c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 410544154 1250 410542904 410542919
    0xf08060105040b1f0c0f12020c0a05030a02090a0203220503040602010c26070908100f240b1303120c051605130216050601060801031b0b03060103050a09060501 70
    0x40a04a4104542c2003060702c07000c400340010028040d141c100c042c0c1086850703080442c05000914406400b45801d10300040c4990b13140c00e681220f0014640260b44608912242c520b8141d604030b02404041d0040d00001d046540400e840003c0946422619500400060b03602101e148046045048905120302000700b14140aa100d500a000e0f04006500340404008a24010740d0200c010010658040d0f080801c0000283c0c4001000b0302054100710044800040319481003010000b130b44140400002c880549800f040119007070700202c0c00b400c1c6214580c900105500456031401c0f6007a0b00c0b04143d071040071480303102440300103800c010100b0802e11038624000703901518034200c061080003116110040c030f41100400f03201d20300c5a668451a031640c0311001202940180a00351400346501c440b01c00b4940d2680d0408009800c5040015150801042403010550391000440c04400d04c0c00409814500d103c0030741e1000030009418152600c0124001c0364490344150540c507000401041156114041d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 410545404 1250 410544154 410544163
    0x61e2d090c0403060e01050f01030f050c04110d0f0c0e010c0f23010b0a140402070302030405150c12030906042907030e010606020309030a06111c020a0f020a0c0b030a02040f08 77
    0x2058034075915200c0c20503805c900512925000d1054001082ca45a18654407021040c00401040b1561b00411111454980f01d03400748404165080d010300392a00b2100f2804000c0300c5030740e507034121840d0800b0101c41e040c54222550003a2001300386040789038904207062200040c00107180040040b004491125041d04000c010143c40240c02c1c002840518500001c110401c0e000740610302c1ca00b50740b00e045101c44d140c5603008000703e51183c01038904141c0d23500e0000381e1440e2110060640900c0000701d00c04032150034041803254030312006400d800c40c02d203d0082ca0340c82400800042032000100c059010311200300c00700f10442d40100c88039200b40e152111000340904407540da1100d0660a111002c90389034004016a20048005401001c13081c196403242c0000c0c002110029659650801150680302984400c1a911184405000d079035542c48120081000c10480680400c5400c071682250004050144d014116880c80c041e9076180e49a01028030024420f90344840aa0003007984005699000440c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 410546654 1250 410545404 410545409
    0x7020a020906010e0a05060a14070c0801140705031b0412061b02030403032106030203030a05090102100905030304120e0402040303020a02210706050c0321061e2d090c04 74
    0x803507864407919601c005403200380150380c050750720080380c00c01404503042042c05001a48070b949000440ca040411584959600400042d118100016000c0c400300109000c4c1d00c04005d031408209000d4680301400600d540000361085e0740030306102007a24843c200410595003d0301070307000c40310252078213460120b00a180301c052032020b042c03000326210056030020043e9005c580d00b6031600a107014100020280c00c03024012001c0905590303c40220141e00c081004c1c104103005501c80c0c80e039844e6840000380c42e010310307540b204000d00d08200003840080d20120039030303400070b41c00380ca1110014155201503e0451701e11114542191001c203000090560008252510038029a55001d8860320040714030400036004841d0106580520020004580f0400c001c00000460006881c00c0a1000025600300441c1604920305202c00000740b0016141001c0001c400c1210324484040c03c22001021401003447c040900f20780502c40342032071907610307802401121521070082021000303140c00580e4400f03c0d0043d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 410547904 1250 410546654 410546659
    0x7120528110406140405100f030b040303060b07170a020a0b0a0603020f0603040819020c0a230307030b061c1202070602162603070b09010b010225090209030a050607020a02 75
    0x507040c241042c10a441502e09403252890344005071104034050002605028000381500f21b0540740008089005044140240d0f214650196035400c080c2001030a0b01d00318ac00200784420108403010004040b40c1021110a8144030007075107410819000ba0300340501d54402600c007070001d508015034010a58810320a50f032089412802c0c00600e0414000da5002c03c50f002031581004003c0003040901c4102108075400c803e10407900745869010220340202303800d91201700440d000030025000c009000c00310b425041f400350001d100c194503544500300c40c108040d1059025540046501c0e0341c02070b131f068106c05e2242d0440f08204001c1c4400d03500035681e000c130f0320503800140a4021482d040110f0030584404640069090701c24100c2804582c50300003403142100a8244410461980000e500400302440341111600000300c40c200c0d00e00280c141800d8500c902e01c022001c0c0b8205980c10510319120081e150344075001a10b0f04600c1000ca441c1200348040501580310700020404141d50008200d00e11074400d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 410549154 1250 410547904 410547923
    0xf110a020d0504030206120402030a05100504110105070c1502070305010608030403050c12100f09050a061e2f070215040f1d0403030c0233010b0c07120528 68
    0xc0308007142c03a80158000258403000401c0b4005040500140541e046030008043d40d010100c940d644503d05000c0200781e41200b0b440c3c0f02080248031400002680da51009c0c01d2003841c0c04029998410304115900030001009031182c0c1101049108103c03403009940c0c040020800d40380c0702c448055480d00544030880c0d0754800c03142d2454030750601084000c0705c051924000c00c0baa0006503620400b07010001443c0b000c3d6640c6240c0d82c1c010030420000c60954501900000034842c5a122207007105d501044200052141407401040c6010b090290000301f1500049103803a0090640c05028030070b12800d04060740c00320f0701c0036213040d44040342d02c002d00071101041c203030440f090b030340e0142c03114942413100304026611030880004022034007039000030b0741e41034217071040d20b00444240340304207460310582ca80900342c0000c0065a407114881c25528501500d140106241410101112265600b05900820b01030030340041c801d20401008124210681c002005060500f410301254586c445486031000c3e038100c02d6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 410550404 1250 410549154 410549173
    0x204240e01090e03070302120f1606020a0e0906030c120703050303010b0d0c0c02091f0302060a0509190e070c1b0902030618060a14120304080109020109060201050105030d0804060f110a02 82
    0x3c0002101c00c000d501d42c01621403402c040c0003030702c05a00116140d0603640e00800c4035a09640103143c0030030803240309190040c2c0b2941440801044202d15545807070047c8010382c28007076644d5001a23980080707039080f200804440c2201c01d00d2414951b04d54401482480080b00128101c09118098844e80111003810840031100315001c88080000381d01c00380d004100000451a291801e220032811642840c50300e651051f81c0b94045245d0740e02c641c2c0100001100403070700e41c5040c54110442805103003c94a100c40803802c2107a003c21140c00a001c1c04140301c0c1c2845440204000c1441400d240c5c9501c42403801c4090781d800d01e01c00654022903040b48035406036003400e5040d80844e114580559000352000d4403450902c1304118207543c0c42903595a01c810040d0110f00c4240b03041004001400c072140c00414800c0a078800074140030b440e5000a0150390424005000d16100062100d0401d480781c035001115441d1804c00342c0042c0780f4490a41890ba05107106280d55000758402403403204160350840c0d08080703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 410551654 1250 410550404 410550431
    0x1020c181b1303080a110718062304050601120f050612030a0906050306040207061b03060803030408070f032d090602212503090815130204240e0109 65
    0x1080b8120b503614034403a01c0b41880440d42440181c40002c1030790130849a102c11140c00180f4110595201070000704c3c804805184c00712450154000038510f802030460130117849a268520107201306e0b01e0178000c40c0e4510019900c0da1250b6000ca445a551030820007001d80000031540c0079042c02c540480c000d0445102c080c010f840d00004440a5035a1941c03002501410581c085649a00203080b05500030f809020500102d076183c402c81c5150a01b40081604d032a04060003e02600c0140d40902c100e44c10500821000c42c07802000c545000390f00002d211600360322460181c5040d4002451840803841c400c9010001c400344486090743c009803602d8404e40d01d03946123003c80ea104448003080e2070110309140c140382040c04450182c8110719100031101d10102d8048081da40d400940c6800350700148002204210740354080c081040054807841140b003492034042d442800b001c00d003000081c025079441101d00504d070103410320791008580140c151102c066a803c90386400d20b00038010b41c00c042c0d01e440c00c60020031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 410552904 1250 410551654 410551657
    0x1e050a1707030e121029010201060305030f16080304050a0318150c02040e010203090d030e06041e050a0213240302030d1103040902030a06080d0f050f0901020c181b 72
    0x39415911802400018800c0c44002c4814519154082c440c03844403030100d2500380511800003003410481c131014002250210007416201b03404074156450030b403003030010580100496054128400a0030b540d040c040800f40840410010054240c8070040103000070010041070041c129402540c2c1c2c1034a131840c8526801c903c3d1000c1c0f01d0742030030b240400b07426000d05d4001c0048c064018002003000a20ba03c08003001c5003a40d00441d0011041e41000843d0180c1b5500341c42948120304030b440050855140c15030b100e58041150955001440180700b141108102c01005042890741c1d000c0c2c20418000007400c146070107080f40d0310004000d01900d8851429905105040004494004004000500095600359601182c1c9410030840e070004100c0421425060300003180100c0041800103032049c81d1150003414102038080c0f071010060035011083d5550740c003005075100300ea003408440b903030381c134444005030714042c082c041c0c1c10381080385842c6083d01c800007a04264801c1942c100c01c90203403a04641140c0340da = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 410554154 1250 410552904 410552917
    0x3010e070903230d03140a0b03030d020d0b0102120408060703110c0d0305060a050915060c07090501060c060615080106050a0e0315010e090f1f0b0619030b030d0504050d1e050a17 78
    0xc90704806c00074841c50002d800004100c3c1c00642074a10742007075a4111401d81c0d01054a40c401103403038508405507940d0401440c01110300d00000b4a06050034094102c4d00c4900c040c25140401d62a0300011222840400c102ea4180850504950011a156102070042c0c00110b070064452a000e8100083c10b0914007603030b61081191080d9503198000d080c0c10084640c224072207000042c880c050001c924650345e4800d5901038141c0740c90b0100f81005a2408600f41c440030b4000588000c0643c201103131503a000320744141036849508007036484019000044804151110500c0e906100d5070b009002d800200c10007d034180c0e0b031280b060b400d0356912844000d550352401c42d8081900e610440b02005859031040c00906812440c1a000c0703807518024002a0396a0003285141c1c650350040c0d40001c28080d01449001041002030307001d4a9101c180d900044e04a0180d032040e58000c08440d4030400821038402c0c900340b00e400c01102d854040d106142851542ca030300c100400c07105111501501c1d0710308014142035511 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 410555404 1250 410554154 410554181
    0x10e07050f0a03061104080303040c090506010e0108040f03050f0d150609030210030509070b0301031b061e050304050111030705071a0c030105120709180203120301060503010e070903230d03 83
    0x40141c59036a07084d00404490600c1200f110301030001090110303003030004502407401051403117151810701e840d035812202c0103001d1134184000182e03440903698100751190361003500008030405070710b4582002e8400344a0312800310011b031400100f03e0315001d925805007501c00342c0794440d40c6115886d4041170b02c01210038003001e58450f1825159400d00e40c030036003015034442a03004c1921040384e500c540c2201c0315002a007084039603220102031130501d014005c101000400c018608242c0203098642103101400c8072503103002c01c00a00000240c240182500039510048203401031640e203140c1810014010303000f1643c1290744d130f09a51002e1507440f4540030350720f00071440f0850030b52441e4600020007550701c03480251092103000340c5400144540c904c2c441c20b001e1842d090384540003141d10384101030a0424030120141052014030042c0311280c0d110054030706482400c9808655a01d400c0425501c50050b544005d28000320800c230071040b02001120a040001c0120880305541540038040d0181d900030100d40c407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 410556654 1250 410555404 410555419
    0x80f0903040e0a090f031d040501050a05040c030902030a03050304030810051c0302013e0f0304031b050f01140114130b040204170312060607050304060e0609090405010e07050f 77
    0x70501c1c0400035125000300314038400113400344c490303034400b41090031290044c0c0c082100d00f0050f64585c28402d0243ca0705042c1110104950741c10540091500142800340714000c0307a44040312558a40030354842144540c000b0101c600103101490010040d900441d402c80003e5800310101d602c0025002d02e4205840d40103002c01000310751080c41c0c510b030103040c2c0001d81c2159200d07a082454000c0908014441003101503c070103034100014804c250340d030101c2d00d9140b0791070020440100c1103415401501d400903814500003100c0020900304510421208c04007420b54006c082c2c80c41025081503221009030106160f036204940c2e60b4240740c1110f20440325403140c100c3d40091461440c00c0499004401c000c81c0140014203198440c0e2600d60083c11825807004594000600d040400003840501d07940142c0482e403203440c1003625070b141501ca01551081c00140003000d5115109a03030381c0403d5509410019055051a140c10704180d0f0280c1198440044c0f030703004840d808a40303801c0c0b48c1070142c0d4000020f4000f0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 410557904 1250 410556654 410556659
    0x10305060114220902012a0206070c0f090e19020108070f2003120108011503060507032310050a061413090c08070201061d0402090403020a05030c0a03080f090304 71
    0x50880c81c0300341e882d5a520602c400704a896840c0400d280e00c0c41c0002003840010440564400501a69070001c4180007601085241400d82c0296410045520b941039651503281c910f60310f010600750b08141c02c0808141c40003000031401400c554010508000c08404407440c061042a0f4200341c451071120290001c1d058500141000703001d610401c081c11030701e00d000b0003c02c821482010020f954410950141d80000440240302c1407224501400b401001c8003c0140c00f900c1c1c461250303009a60310000340741a4440b00000c038041e003e5407245414440709468040540d00205844201d141c013181c040c40341d0300c00c4090100c0c00d810142644003d642c40794541002d1301e15014003099007600841c1181c0d10309030700050080740c0c0d461a07004201d503140260b03c2e91003145c01e000c0d5010b402d68260ba0810380502040b0109142102102d040894000e60196801d18054680e410204c3c140824541c0140c02c030301c400118072140e46030010b038840815000799201200b80d1996150203a20f00801d07206040640c6c8240410b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 410559154 1250 410557904 410557919
    0xf0301030201030b180718080606030d110a020904030804061d0c1e0d0f03120b0102030a0e040f060b0c07080f101107061410080a02010807140c070905011d0103050601 73
    0x402e050000040c448949400301780142c20044404444900000d01100300241041e030a814001028180140c090000c0b4904900403030743d03e901d96808002001204000b601400380b00744040d00c3c22580280c440310301c1e0b242a04000d480808140c42c120b0b0014a003e4608041c0d0b13180030101a42081c83c60007a014918500c42000b00d42b88000c40310040d80075003410030184039902c901945041c1c900c00c114040045000307090150442044a40c0c880b00541040004c40d56aa0f003c4200c55004074103091104a007045080407400401030306c0c17030302405146000b40200380605928043c02003044400f0440d240d5070340302d00032107482d1101420794074501e0740031100800d8180311a03006208200031410129007000090703182c200555040c450401440001c400030b02070f251444030a000007074111032000703000c03040941c0e0000300301480c005d001c1c1c02005104020070381c26482c1d120860b062900710302c04581c0000d44030f0700c0d5800101428030031a102980c04440324400c45c50b0703109102d81213941001c0604016172902c2d0302c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 410560404 1250 410559154 410559161
    0x30c03130815280501030b101a03010306050411060310050a0504200a031b0c030206010f080307121223061804030f0309060e1e0601141207030816170f030103020103 72
    0x500e030070120742e00c00491001560a1140d45e00031800343c440030111b410a2082007010f00203c1c1c112080c010418444100d51403501c10440341103030750241001801d03594905121442d080f0101505900010001c140100721441b00700081c15680f040313a038240f403140e80354100400c40b110414100030032059a00311049683d000d80c00340c16034030350b14100800d485004039004112815034905400110788814558020305030b0421002d03002d8681c0c0030320751000904040c3c2da60f03502d000740c41009101842582c1107035104d07407040d05509443c06060805220010700110003008040440e400524680300490004405140c80783c4c60380704946101148001a440e2502e00f2074036107919465601c14140c030340036050009006440380400c4950018003824102c0d0710174952440b450313a8060103001c540c3c0007500510951210b8111201e14200840e0005280403801d41e0081c1403908941c0b0281c0450404952140b9503c00c103072115050b2407049181e100620f045040a00d824000c100c2c001160701810f200500055000b40d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 410561654 1250 410560404 410560441
    0x303020c0708010c05030103060f021611010c120906120507090308031b0318100c080a1512060c0f020703030c02010804061e0605130902030c0d080705030c03130815 72
    0x10140d074503941d12006181e00703480310001d1400c0015000070042090000611441c84017103c220303003e61401d0105606806d00008901000d450ba42d031941c80b00403e40c0c0518640c0d10f40f0380d40700302403079078500c1004005014204180b04807008600031b08802d0a00301c400340300e010301c07440060300c40c00113441c00c5031110001ca403c0100440c12004140501031018400b0a000d9886002404144100b40b01d104a089041000c3c8000380040c40b414192441c58854208141c10b90240381c6000005000021805503080c0d41e034503500104070340003090103040512270b60750408019075100c0e80b241c986c00311040d80e08a80c0c41c1520f10015000507000380074480190b101d500859080350041c04e0116441e5000c00161540c00c2012156000c02ca40e511130810141c00c3c0360104c0945901200e0080013504d076550003080d111101008085d20400082c06e0360340c20800e01105481c1c04680003c01c698648802d040c1541c0e50b40d100c8039208900503221040080c1d2000b0009681c1018003184690344455120b042d03210b080d008600 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 410562904 1250 410561654 410561677
    0x609040f0c091e0c020610030803070201062103030b10050a0509122b03090213020a0203071b21030f1d0607080403061107021f0c02090405060906090c0d030302 70
    0x1c0040c190700030f4010030340c940b07031000748003000743d000e05242208943c00c540c3e000042d908010b003041a40c1c500b00c80302c14100c81d0001c2c0800d40c1c03030741d071580d04074010320090300b10f0300c8003401341500801c14004440d0f080700d00921944003048890307903990070052100c0071203510100282c1c04100e0081074622401c0a4104850003a00724280c002580c1e01c041d0078000c00392120603a4001e10b50300010707510b07840d4070b00401007203107400c0803c5034441940100b4410103800c03031010646900011000304180c4200115001c440c0c10100d443c541410b0101c1152074241d8a20400c41028111070b00001c03e5000840b81e504400d40c1034841e09030740002c0e42c100346c80b040070f04401101001190500d034000c589800c401400c0c490b2141140595441c2076113418421910016000341080c0414411311006880b059400300040c82c04021001c4407030000802100d01c2640348500a4102c0b140e4814002000702c0040d040e40503514650541d4000e94035044030ba56503180d0f05005603400a0800b03000e00110340039900800320504034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 410564154 1250 410562904 410562923
    0x30507030903020d0302010e010609020310060c1505010b1b01140406050720070503010f140601080c09031e010b040b2101090b0114011103070809040209130f150e0609040f 75
    0x200d40021312200481141540940d4403a0390801984500b031081002401c9200b03000c604500f002103070000d40040900a15080c0013441e00c40310241306a0315a0b11142d124850703000e01c565a16903001c540380d130f00440da00840f81c03814412040380600c010b014010b040c040e40c000405150382c1b141c440d4000383c103001d0078140030701481c4194101c0d905c1c1024954403d03445078100a0542c03503e80024542140c80d1100040b000c180350000c5400c2d544220018582c028000740707840540358944603070442d100d01c03400c19000d616229692a805022410400811107202d005000708051506101071100380c40300e001c200313070b880041082e080404000d001c904420150464000141340e10b06507072100f007032031002c1c0c00100c4103d8009900500307075a0b00c43e46210f0701d0750040f4041c2d81032941e5550f03000b0190250488140c41140c01180f030801540b038003454455040b0840d03409100460b52540c003900140407050040c00440d5028602180d0300360f034000c40d02d006e2600942a01c00ba95510381783ca20003429207070001c481300c0e001c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 410565404 1250 410564154 410564159
    0x111e21040221060912090a0e0603100216030305012705191a0907090608190b04090f0b01050a030b01031b15020c01080a06080307020d0204230114040b0303070305070309 74
    0x61124100b254403075950007020141400b140351494211551a14020301c1000c1013607003480d40701c0180d4081140d182161104054840344000790500601840c03150383c0d980b02080c0d50714451600002444514081d860412650340c1382d1200030440d40d1940c0c900d5140c48200d6280317007000c1c6429070000f5841a12034005001070350042d5038034007c0d40e1080300d580100816080040c10107241c0500001c0e0013900741e00344910001d00d0000054254140148072020301000d179141003110842903080a00c0402000b441004103e440741350400d55000204070540e02083c04c103001003041d051000580301500d40040300b040f200da107156a6449404d0034500800003c03c091140021848003810304039102001c01c0d00500042c032107003000101312140041aa000443c2082410068a40040100c800300344e0151815401c411181c0046005000c1742440e22140101310200c00c140c50b0401403006040c2e49c643c0d484129402c005904001c01c4d58488010168150030810040c0006400346000300102c500c80d0070590300301035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 410566654 1250 410565404 410565439
    0x120c010e0324040b161b0503040b03090616021f02070c09020c1c0825021204091e02090117040c0b0d050f0f090304090c0909111e210402 60
    0xe1035955580460403240d00f0300041003202803c05512107900084400340380918000102420301c0316000784404c40b15034840c0c1040c07000910450300a0811100c1f5155a800d2401d50b0355640d2104450f05840700104050080b0030301e1001c610284102c107005031141d11400000c92802c000c0d4800780085540d445d40350000107124001340050404451400c1c050003403131544a196183c41010030841e1401c001b4070004226528100d03211032500c45400c0c21000d80c144111050036484d1003044407000f08040da0124000961040941010002426250742d0030030302c4500e2000c50080c0d00509071900d01107400c6407480310422800c50305c82640203000e800c0e4a65040d64035240074416030f020800744e054140d2610f042001000180c0c04268010003c0034850b1405e1400325405a03c0c0d004900401e84100e4940481d0f41c0c00503c105208005003e078440c00300400c00c0c0041e40c20581d0390200184580c01c0f45c8260252895500520955040107810002c0b00240303c00600c0c07044411000810403030b03103c012903901e1b000c01c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 410567904 1250 410566654 410566693
    0xc060315040906060f1d0c03160c0c090b010909090b070c0c090e0c090c030910020d09020301060f0303180602060a1104030503120a1104080c040207050f0a06060f05120c010e03 77
    0x2042c201080e0b00e5070508110545010b11b0a6289015858171104140034850311b205040320f620481200320260800c006030411200000b00c180060300080c04100d003c1040c2141d50702401103800262a2820b1095480c18900e050741e5490340c4c003411880c1e001c000121240e000e501111456031081180495450310703a0391400855410350742c00c192982c0507062900c0c0b0341c00c2128031030740c01c801203840060a500c1c000350017540e141c3c250301890f64140e8011500c042e190710b254000011050380100284036103a141c24405140c001184419000602000c8100d05008882c0c450072065400940c0640a5a60b0740c238141000341c92040c0169003181020000000800c82c1880a44084501142e82e9180c0b401c080c4501800e4034064591070480e004104010012079800049501c80c141c010382e00940c4030302c00d5081c1a41050302d5013076000712500444004104104c0143d100d00d06550700c0000c0549850344600601403803850000c44140240c1c032044400450f903000701c00c1c104040100400f02c0b801c2144400c20350f81388 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 410569154 1250 410567904 410567909
    0xb0612060c090a30031e030b272a1206030c0103020309031602060c0a030c03020d03060509010501031a0a0b0a030e0109033207030804050f0c06031504090606 69
    0x1101203016191440c0100341d60006003240c040a008121480c00c0d640d0039200d801481040207402c2c4040c404c2014004c00282d911030300f00d5061030305078004a42c4003030060a01030070914800e816400c00074141d0b11624109502c014806d207504042640e030b408280111a0240d8011500700c0100c4002040c4220355200500b11081c2c01068004a41000800e00d40b42c00030002d40b80d410300d8010f00070403003800740000a031078001c0b1501041039180541400401e032140315802d400010350040008401c18140c0181e01d030746000b0321036030071101c841301a21001c0b422901180a443e60050305080100003640c401d400601140c008005005480c140143c00241840d030141d0102d9400170011803550711090b0140300c1c1310301c0300c40e5140080c840040c503640c4c010482e030000c0d0740748200aa171002500e000b4400711401050450850f0800c02e82d984442d0030b0151215004031011a22031040c030748110154400402c1c0541c02c9440600307554215211210200b600d444050030403908159292810804a81607000c1e0303400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 410570404 1250 410569154 410569171
    0x9030f1306180605030c0703090f270204030209071d0d0b06030d0e0604031704031e02040b0f01140a0311030406090c0602030f0703033c050912070b061206 68
    0x140d0074605880a00031610940081c1e40022080400b00800e030740000c00c90358803c03035001a4554541c00c174901507500750207a130090091006000ea011030605003d0b2110742c41071000c80700c601260707000c001900090b84601d00009405c207012b03c011031340c020b0107541e501d00d50741c01411071144a04a400c01003070000710811001d44481d00c944c014030a590a003813008000c61841c03854030650482100021417414492031000900b44060702c131480078050003800a940103076902603407244405c80b410104148055890200b03a100b0b9140c411280f04c285012110305010407010b84802e5038051540e41481f14640080c1100700900d0b884001c040c03481140e0300c004511032885150000f408000031b060240c1121010f401c1582594400c1080113003c84506060f80c7d4443d42c5850040394418502c2c5c41900e1f1680342c106c0c1025000d111030400d407200e030b0245444111502442c42c0c10480b96540f00200e41c3e17108840750400c41c4d412802c104220104020101e41684080040c0041407d02039031403112b4a0400304444060 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 410571654 1250 410570404 410570437
    0x30606070f0c0312110604020f01020a12020601180e0c090c0c240a0c0507080705012a020f0d050d020d0603021903170f0301170c1905090604060b0f0309030f 69
    0x200000d60401d810802c02038a40000482140440d10346d64600103800a80b0410254401030300350b0380308120413091180d202c2e44143d05840e040070b010350f6401081c05130780b800300311103035840302c40c43c61a02c98000a440400c0003001c01e0003030b4806100c905a00034048010402c002c20144071501c0d410000c40084070f0f0501c0303d46a045294000903081c03000083d041c0d49602c2d0501c4006019103038000107854100e90803845007503881c90715141450043c4690010041c91480340421544034205000c140b001c1d065141d02500c10980099040985074000c0380500408a14244055140d0040b1175000d808448a16032000a002e42c883c3c000400007a00a8010025105144014010003200000c4502d400b00c05002d103074100740398030113421a280014004d07074401030855400400903400400c00714214540152035211000014215415035a445010f014000c2c03038110041032040c10584202c10444041109203400d1181505040301070380d002825140c207a10081c01160b01c1c554520300202912803441c1890f0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 410572904 1250 410571654 410571659
    0x1061409010b0702010e1002010b040614030d08070917010e030d060f0e01031a09011d030414150a0c0f0c080607120203090a02010819050c030f10060c08030606070f0c 73
    0x4600054141c2040b03000b003100b40301d1400141d810503104842514102d0705483c030305a820310200c4c0188455102554087c3c00c03e0000103e100c0102840003211801b03031709488030300190a1050324a5030301034403208005008680204104801d0007010300851100c1400407488480c00702031189560080d4445100c5c259035000c0070010104007a06a100520100b04941429032642d241d90403003480b02030010b414035105800140b0100340079405284401c03a030040404008000e0020255650020702031803524042022450150f4940114035800d8000c01c10300c0d00740341140c003030400c0301c03000c007685006c5480c0c0c0c40311444400011030342c0300c40c1c40140850500030b180030304d000a0028000e84501711000341c0310340704005221242c100824062111038080c02d0103400d03600c0da01c480c03004400b101310b0f680308114901f1060000070066280110b01900c1101d13510302450b11880a442e03036031100c511900380483e14400c10704c00010028005113901c07800017000c0070b0400c411901c0c0c01614074800c1004848404182809 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 410574154 1250 410572904 410572909
    0x305070e1815070305060a030602071209060c080f0c0c060a02030a08100608130c0504020a052a0709050a0612140106091b0e060f12040b060d1e03020a0203010614 71
    0x210445a01c400c4014002d018a02e00825850000681940c00b0151180002005c5071204280300c0b005641c0324100b15580da074542044401c1104482c3c030040054441480050401c1c45045030320070554100162071315040c58040c0c5040d0b0b0750b000c0401d002050183c1d005140e410f542d9074001d003c1840c00354029503a0742c07600748002014000b0061604002c844012400d010300c9901c01c0e40345074003220092000c074001000d410018820308241d44440e07071041c00010b00c0284181d11201402c4035201014111b007a00c90100c091404031400d4130105c00c0158048141000440da5a4000f55003114107075500280720303030300c618043d1882c0f0300400068941c03988440c1400700700740d024801c0704000c020703124042142505100e0780058507a810040e000400c580084061205ea941034201d401741540003018030360b1090b00c503070014040174089805485c4c48141d840094800c0c140050502c510562080c001c3c9030505103018000150042c902003601144940c901280041c0c501740300c3c43d40a8143d0051b20101b0070000000c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 410575404 1250 410574154 410574181
    0x80c13061d0f0c0a050910090b030a0b030f07120b0403110a0c1d060f0d030509090a05010510030c0219110405190b180408030403110a030509182802040305070e 70
    0x10006030503c00300040039940350b00006451041108441e4000303611959030048030005069040120400000018400158019400206103190a42c00c1d6450703142c0c090792050302c40c030147c4241082408000d520300700060740140c48680c01842401c2c0100b0f0030007a654440e1400841007001c8800d0130140200f07002054070003050802000ca046e16a81542c030b00500031030544420101c4c164020201504004101070164080da40c3c1e6400c0540400564582241000003400d02031007550700a414501d030046180e0720901402e450941180c00901d03019802000d400004402c0c104141c0c2c608111403240b0140390f1707a03401540d018481c0303400342d407085008030040b42e0704a55407054980e11074620105108200e00d1020074041c0e01c990840000d5840399110309050340d45128103400070307095004d080840c4c82016044000741412403c02c1d16003e008003410308064a084a0a4030101902902c01403c8240508100e0f12240b5180e0200d40240c10590b495948902d490115000160001c0410007040444c001300702 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 410576654 1250 410575404 410575411
    0x3030e130506010210020f0405060f0703030c260402010e03010509070302090603070608010b0c0a020a0306060305010b1503060409060b03031206031c170403020c10030222080c13061d0f 81
    0x303200300311600302140041e6840782100f0900d40c62940108440b40807201400c207030303230003031002404069440c0b82800035001036600a803412000700f40b8090003504614403641c1002100d10340808032003000300c080e407e900070329140100103d04000b01110300c004152800c6c01058004e104017401401c01c0d038118410410f02d00c2008080c40d011394003c400c2080801e61111426045940701c09030582c0d2400070410150900e03400640181d00325000c0340c400000c004088c2e000c0c03c1201d006100070014904107204008400c000a0700701d5403101d0702840880c007203240c954001c14610b4800d810010781d01e408070010a055030011074a034900300301c4d42e070704002507810284110848440000190700800d000c098018002072158002025240c05e0701c8001010103008210144610b00000c0800307100d8040f40100502a6000c54100310954200c43d20400b0071070f954850020507110040f02a1a1b05820401030140010308105060171042e00c8000001e0b102240c0c504141ea041d0b40d1a64000f06441c04d0b00d606040410084e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 410577904 1250 410576654 410576689
    0x708070204110a141e040605210c0a0e010e0406080703020f06090d0f15060902040618030503032202090c0901020f0307050d0f030213080c040f0b090c030402031603030e 74
    0x421000305141d50100e02e07813582c4100100354540341c00501451841c005405685001003500002d4085095608480035101030036101a41102c04101010559a81c001c1520412203a8809001000140e4000c1c900c111004c2c0341850501c100c00e62a41c001b409a403419401505140c0201c6014025814100b84c100082081941c2e01841c1070900700116010b05c1446074003400700011100420200540c1e00308900ca42030041c41d0038450b5a071034440f440b0007035005118003400f1074408850030215410a88101c01100d404c07070003960559583d880c0c40010844406031b680743c0310720130207080c40040c3d65405400340642c03048141d458071010705038006441c1c003101c1007807c0000c1d4014484900002c10001d8400000c0030f036031a08140414000c0800d801034094900c0070078620384600008100d20300f000a101d120a1401c89040c40b050f1840d4841c281200c00510501d600003440c071001884031601c0b20000d60304680702070105c40540200d0f000b01c084c03c21003600214000b605e0580110f42515101c49a1502030a0b031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 410579154 1250 410577904 410577907
    0x1c0903031b0507080306090c0409090b0a06080a020a0e07050c010603050f2401090f09021e09070f0806040509191124120405011506080a060602030306090c0d0908070807020411 77
    0x107443e111102d01008280c21f109000b510f001807040002e50080d0b600a080c0b046051200c08098030300030185040c00c035902a03007240f8010000640050020f4440f10154000d441240c1d9036091015580c111100100242d05200d420041d02c503454000b480b03050025402003018020000000e940700341045940300d01078100980d8980c0d0740e0104100c068683c0d04480f0840000038141c00c2011142c0003600181c1d5002e5030140304003020040704d01c0c82122513200d20030100c400e0201c0c0e81d1111000d8a980140d4500035001840301000150b8034203040c0d1000da04241003000b158514101d1740f400c1540c1210114045802681d00c803001c41c12030a003880c2c072031290340e0300030401c0d0030380a484c00003c4054060080d144004140d003e0115044c440c0a5110f02d4641e041c82d8000e204181c1c503040040d03d50407090302d00440503441c110000a601c2e03c0031056900a40004089071019180c1c81e0f0300401642020643c42c55140e950b860356070000760860010b00000b032054541d161103442c0e500410046520305010107448400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 410580404 1250 410579154 410579167
    0xc0504020408150406110d0b01090602030a020c040e03070b07051c1b0c030905061305120601060c0308190203070809010b100e01230417301c0903031b05 67
    0x7400710340e103c040014502050700e40e82e6103081c100040c017205840e0901d50000062000101c92094110080c80102030b203444482e0795030341034101c2c0c0c0c920a22581a0050f00f004000c40000d01c0c5c503410943c030652500c4100ca0521680d501c810500300702c00d484403404150000f8220080805081c00b141c4200d80c45502003004003a0055018840c00c0300c00c614100b000715040305202014060340030400500fa0160400d5210001034844119405050264900c43d10b0744a0000748111000518541a205196604448040a59015581110003521040394220b031400001c0b4944102e2002d03610602c000d5680c600c0c0303400c0c518540b2b4212603219030701500030b800300d0000041c40c5800080141e4814001e02e08020840c4601041142a80c85141d2031000064001000200c070300f04130b0f500350011141c08040d9898915481802008100c4e008200151707007040f401c0c8140d184282202a01035040a20074407080550307206d01841c05c6940c800300c2240070035903401054642c60321041d03003c01000c0c0d29050451801e02c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 410581654 1250 410580404 410580419
    0x2405090406020a030e070801020d0f11040b030c0d090b070834090b0c010b01091d06190e090604150b0109030609141209090f01271104080a0c05040204 66
    0x10000c00c0a0300c4aa0001021501544a640034000205240c01950480c0e9143d09034113010b90b0000a007460007600f00302c00b075130315076401d0300c0f4201489030303c0800301d032420b4a0202c001d0500d07000100340c101009802d12541401c541140507920340c140c03081c11512482d00e403521001d0402000903191240944e450070100c586220090f08400e01030900c800240c1180d80c48142c1112225070907006180d55010204000c070b080f0805402010950074262202d12255441b04d21074002e14100d07c40c18000310207040d010a041e0301b481b00c800300711404e40310001d061440d102d840e00c80400d171060700d4490b02d03540840100000d0080b105c403aa2030460b00c00e44148810268407000a207840984d00010f400241d445608000300901b070a8000302803807114003980c001d80352000031008030b500503003c0640030314a02c200152400320150102c07810303100c0e510bc1e00c85107a144440c82d01c84141601103441c00d01681c46000445c41500e250181005200c100c0c0208221186858103c0d0a40c03880e5000c24001d0b07006000034403040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 410582904 1250 410581654 410581669
    0x30206040b090f010c1d2407020a051f0e040213030209090307120801030c0f05010c08031522060509010302090402060a02100203010306021215090c0a11010c02012405 73
    0x390300100540700c2a201e8000e5203062040c1d520104403990b1030b001d03949132036035040502011013542d1100026038191800c810710201020a100c0319511036000712414606140e070001034507855002405000c006511500854030030b10810b0049000c625841504d1140c036a40100c3e41c2c803091070305490950501d140c00040360264100d42c01300034820780c42d5000069818031b0800545400c0c940218075120f5401d010b0002810108080c00b0655441d015541d001c030700209544260000c484040c1d6603042c0c100e84079250b1002a0300041c18001914042c42011801940d038910446403030020070302072042d401104101b0004464180d40031500503410ba000400160782c0c0c074100140c3c4143c042e40c1403540c07078210b080100c0c1882c40180c46419114401b000100a000d0f45501038908101c080d1480b10f207e455000704000308950f5600038a500ca04100005885c0c51002400740240b0516410b0103440007561429950030340308914400b4006030340d61100c03110f45c0d00311410b0703050000541d200c48520003400c1001083c0d08 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 410584154 1250 410582904 410582911
    0x2b06050907120902060a030e0d0503010f0b07050307021e12010e030708070507091b080901152c0c180109181a09090a14010c0c0609080f0c030d18030206 67
    0x5120050b0101564203096410500c803080e03004100603610314044c000503000349503d441204062040d80300b46c481450040080368107880d2881e541d807d00074034009500e00d40d54403d04d0103c2d42c0d03000500000300180ca035001c400c042000e6100c4c2944800d0076050612130314404a5203440c0c91030381003544400300808040111924140c01010990741ca021900b4061300e48002c640c4400d01c004c0c51304400c8810812291448903264086644181d4140c4401c1085800d03101c1b0f400740403403003491a04003001440c803200c20003208030b2030322810034075039021400044282c06403c0390500401c0300c00180c01c40308822a800d1500400307500f424220030080c1000401c2440c0d8002c0d03001c68599640e2100c000c0c1c200d480800b8440e0040c100103180b0909494124001d81e119100c0c3c41003100c00101e034802c103000752841070040a00c00340c07203036658800c45496911050007400060205540011042120030310401200c0020603447c103480c00250341e52042c280d00d080c1111680c0b62901c0e0008a058011000240c0c00300d0407540 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 410585404 1250 410584154 410584157
    0x4020609040603050307050a05010c0f1b14010204260f031b03090d1202060105030105010b07200411191803140c06130306060b03060a180b03032b06050907 68
    0x11610300100105004150540001d4190320001c13800c40e0800c50000b5004551034402c000034440902005010b58480c0b00501908000c40c0031b0030081101082e0085001c41241e00520380143c1242c0030005003402ca0340160098010000c8102030220451101e18040101c2c0304824000c018440c0c00d880c0040e02c902440055038080d103000a001d0302041000c10a840c040d54008018000740c6400349800d08000a00c5072640700940100800094280340c1849500c1c104c55181c020b030341c80e2442a68445180c01c0c034211522811100f141c01d0f003421516548a481e401050681c0074a6482c08071010245003814010760450400195118004051480b034441d14212580403100d182c1c040030315a01c2d02e052a111014032900a6804180e201501491a001504417805164200310301c0d0b8851310b26050620080303c0d42c07500440c5241c410007554409003c1420040500b820006915141d4400030341540d100c481d5041000c80003031f00c2d041601020320701c440d80d0040301e602e0411550f13140c038020626a0400a01400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 410586654 1250 410585404 410585407
    0x705090f16020f10091e030e0402090303041e0e16090b0c01020d0903030605040f020c0a111c0305040f0503010e120901020304030c170606060a08012c0a1d01090b040206 74
    0x2585000300a10304a82d0070600580705000b4013240400010071a4050682e440e842c1c080004d0b1260800592615101d0307010b9179124041c0c64600c0512000e50710400c0e0094161000b080002040d4103200c49500641c8159031056900f640703490711840d121000609641e0150600c3c0398500401900b008080d0116201d442925841d021800207031402401100000c040960810b041e60301010742c03540c001010ba4000320b600b08144254480c00a08a00a000e0207a081c0d610090060020482c4820200c00b1051300030500c020f1041c0500c0b141c6001e003c1000100c8c041000800d060044900045914001c2d2206900030040703a0b802d5003050340d40b21001c0d80029054900010204203130f074800e008846c0a940c00040c007081c015034418840102d50318180b000111805071074080303991442d0203801c03219580081d81c0e50030040c1e401c5c0a00300c820300321400290720b0218886d009078040c24540781d20651180c882c0e500001000509480084a04003c0e002c2618081e403400480b040050070010542d80c0180c0c041e0b4196 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 410587904 1250 410586654 410586691
    0xa0e062104080d02180406060903050303041707021507020a0501260c1303031106010b03060105040e0702031c050405120c1213122d11010f17090a0201020705090f 71
    0x80d400f88903c05415480f84c1c000105d800041c28403081220b000441035400704201c4e9550402100c2d07165032408020800c1d0000c00c00f2501144059050400d170380980002d183c03600c2c030150b002443c00300b52405460072205004c51200306502e0000c0c031400c001c0c2020b00b401b44c90a01180040107108030b40c4010400c0500244010500500e4400c06407170303100e10b0301400d00e462181c803801c000d4641d80664a030300484d4403840f4000b00d01c803042c80080d02c5c01035206865160410741411140c040d400d40003801c020841c802441000102415603140385121950018001400c5c20942401420001401c1b51065403031010030a400030090000740c11440220503144c040d480b900d40d03502c44901d00095034001034003e4100c0510a00b404405001705d21091200e00d00140744d403c0808002030034040c41c8001600d0301f0003030022082d07194007940b90100401e0162514403202240325003c07158908040d07074803da080c0d002841c040b0442d60100300142c0a0300044401080a1900d40c0c0700300081400107016030200c25003010320 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 410589154 1250 410587904 410587913
    0x1205061b0717160b1008070801060e2404050a0203060f010e011209020d05060906070f020c0a0b072f03100203090d0f02030d0e06070f1701031709060d020a0e062104 72
    0x10324124a41c0511329600d6030170300c000d00c205400301900030707401580070348000002d21a10500c0b5030740440c1d545140da1111031307403480c11002014041d0b4440d0208000000640c0b8400e6613540304092054104c0c0314010307200d06040c810320042045c295180d50512a548540161a0b80c0144030740c00c08020000000c00c0ca5420307880402e40d90188110010998801c000034880380e0f58010501c5441408156160703000400001006c980e03404c0701505154010110200034452030f08014000c1456900602c0710326072218032100c2000380c26205500103100b000c00042103080c90301d01845110b05418035180154203508044002584402004c40344205010140c460564242e0003030060301e101c44070142c400c01041c07031104c142d00e42f500801c60700480005c1c0e103402d42030301450083c2c80813092401036002002160b03003180c0d80c1034110413507150a54003a00c0e09110f1504180c0d500e20042c201002c0341100546c41b014009009007110070981c54543c8503005c00e02824800140310031a0070b04108004900c0c0d0a20340f00c0382003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 410590404 1250 410589154 410589187
    0x1209030f01020f0702030c37080a03020f010e031201152606041d0a14070f0902130b040305100b010311070f03020c040e03040905101205061b0717 64
    0x10384240d400401c0110300b0350301d2031000c0c141d100e000750306468580e01524104161a413104d89980744401d070901c00c0f500442030007142183d9210260055a081a449000301071901c4040305007140164400418007000c44428000c06001465441c01941452482502244d60351014014082c0c0031355181e102030242d0344070380007507401c840010115800d420000590580051000c0303030300502807814440d1019100e0900b13f6000b0078000c2c020054038000795284c0e80c41540c0000d9110f014403901c100b82000c16402d22498400c4020505c1e03400040c1d49041007203094900e10b506900400040609200800c081507021480b030070f45256021001411400071801a4014038496500c10400c541c00f03d032640421284e08203000c501802030302196800c000d40c904000940b0030150a0b898150001e00c010044c6034400e402c06030b0070105404109803842e8980004689102c280c1c5402d640580c00402403201c82102000c002103c10745d000659490301c612a16055500314441020907064100050000f41c04444100d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 410591654 1250 410590404 410590423
    0x30b030d051602210c06030c30070302070507090501080a03081b07122007091505090406060f1505071707021e040c031a122407030b0d020102120903 65
    0xf030141035640c4c0c06498083c444021580c603001140300d0205481828580081607901c01c03041003001030b00e00718080c0c021002040380e100101104241182c01034210b0040031980d188103545681c0d0040c5c440000d400e100c0d00e85551a40010300d07942c94140140001c4501003540400c2c030740c040c00c0c44142a221903d1520322600c02d001402c04202001c6041410403c104a07403046800042d5904111266900c04805c0b5022800d0171313810300c1d603000aa080010034602c3c0c1100134030a62020b1000c5081e56074202050072000d04460449031550b48150600807403070a05981409003540755450080064031002c080c00506c100d081c00361183d4020505090a60204030885600daa800380103044490a40c3c1c1a540701104e41112080c80b990400000103402803182c8209a0100e0400c60031441c01c03052041448850140170740300d80980e0042ca525400340c080e0b200b04104840000185514461a18800040407940e001d40c42900c038580e12114400580c2c0e0010b04c40e070005150b07120340d13565101850002032402100301d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 410592904 1250 410591654 410591659
    0x30c0a0b09100210061d070f080a0e030f0c0102040e011205060103030503060f030a12020607030e10090201030216030e011418130216050c0906030a0f060507200307020a06030b030d051602 82
    0x251010442c001840c00d00100000c40f400720b80c07015120f07e2819101003401c0d0381e403800040d4000000a07030181c419004441340d6801141580d19109495010343d1032648a440c0e014090780d0001010450062456595401841d03030000ca03007460100c541e140b80d00d481040c0300240403c41d0100104e02c0e01c0e0360307103840385100780001070884d06216040d00c1c064140c40045005800903004602c00038020b035000f40030303840401c240f0b800035007201d0300451a5103008040318003003a81016828888100d02c5802c14002c0c0e620a80242c407110141c0407480300041c0700c2c640f060081154058103000c00520004488010707001300c0412a803407120300c03a40c05002d00090041121005d0f4007c1d0500007401441004a118561200c050b61602c10a0307aa0f803050559503a0700c1180108031a82c0c0c0d078500070100310a6803240750050180d00d40100040071070304040c668651004020300c265000040d01004514003115a5401000d01d814240802a04600001d131140c0254065005000c4001400f50180548500001850703500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 410594154 1250 410592904 410592911
    0xc26010b0f18060409150e060d0201050d0b0a030f1514070305090a0501020a050406090b0c070501300e100902010207050d1b080607090b12010302061c0e010b030c0a0b09100210 77
    0x1c680c11030001d00400b09206c4540180d00c800815a0100c0d070711000d101d01006010004524116801100c10383e200105405156a032103403120159550201ca80d4011801003a112540d80741c03a05142034031034a54410401d80514200042031020000352120341c3c0414503041c0040d40b60b80781401682010b0074410018442d510000d00000e1480c0c114003d8401d881283e0b42e4904920340f81c0c0800c015621a6102122481d84502d10410140d88500c1c00b440030514109000143c00c1e81140110780c91070804c0e54540b203055120304411030031900800c10304103030401a4506000c14020782d00043d4031001540202402051301071810070900070020941c1d0804000741103410820303903960350341c03a45601341921741070300003401c6403000141c440c894000d0b20310245280004400d141d195500700180c6c0e42c40781e20340314249480c254400304840ca4620400101c5000c2030004121104007000700347c10080304227044c0e4030035407200505000109149065400000041c0c5507505040b480e00c5050f46407a50307442804804c10308 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 410595404 1250 410594154 410594159
    0x40209040501021233240c19110409020915010c081b0d081902090d0803130c1e18091b030501110f07020d0c090c26010b0f180604 57
    0x15116013650b1010040c400d103105030100c104c2d00d030205d40500c0700d0f00d079120308441c1064a1015080300402e20750036a0300c0000c0d00c3c0045000c0a20300f029000c0300c100f44c00c840c800ca01d02c02840400c42c1100e0a040b802c503800c00c5140e016500183d80c464000e004201c40480c507100712071982c0d003d03401285c0c009800c140c056485514032855951841c09a10490348107000e41f0320002e003594041d0301c555000d44019881441d000250802407030094000c1e4003400c1c0c2c4108102a998040340021000314090410340f00b490a985003182070200e24820b4540c40f40490700c1680c01c0c9180488840342880f4203540a04003004003924091404001528200390050601016491000c561208107088442140e100300003d0008850400c00c50b942070040d01212039950a04000c0000149040f800728116207201d41c22015015454000c51000c6410619200020411190b641e90f400320000303521004441700687c40501641c180240401140030307405030302c605010041145408450340200344035480c2e501905e99602c866 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 410596654 1250 410595404 410595421
    0xc04090e070f05010e03100905100f020c010c0e010e091305030c031905090a06080709030c0605071421130b030a050402040c080402030606010f030b060a0207030b010e0f0402090405010212 82
    0x1041c40340c2600380c00c00b00e80000e0b10354000c150861300882c0040280c946190b0800005002d44420201203c4a00072201d1503080310545102c1d820354145440001070700c54031260700f110308659440208005000401d0300f98012030307a000205203600942a164000e003030315030080300f4200c1c401c120300c018414080410b10000d0300c48000043e040700344604840b965070001c4040150b45601c0b483c0c0c000380c4c2210340e040052100d14051a400707034221585213040701caa03e07581e440341c520040d00b640014000403800140d101c2884505107500d2041c2e110760000c1d148008100d00b00300319a9030010513610b6091000b0032043c0307030340b0518803114004114214910f9070764500403007020010a001c0307404901c2a4602180c00d400940324000c243c2c420340c1c1c090001d1032951100310054900c44080101c0300105520791031202a103072580e4001d4815048290024202a070840c50084c0c4007540580080482c030364484108014095402106604140c0668800c80320f80c50341d04115029106030103003103860111001c00e126122 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 410597904 1250 410596654 410596663
    0x200103020c240711072303010606021e070e2701090b041403070f1b0f03050304061724060c060f0103150902010518040b150a2d03050c04090e 62
    0x74401800702c0107643d40d60301401c2e100201d41e00400708040e0310100090001081920349540071220100780141a20b000000180c02d4601d141c000d0401038007c0d1658282405400720030300c190520030006060017a041ca000707100aa03100034034240f404502e15803c10007080300d010035000700c444528001d204039500d90908106081003640d00b1501c12051034112818500048281d8a50710341c8000f80300c5820b05030b074658264501500110100c2148030500c0020403000c0030704020011849070000c1c50700c540c548035003c0c14a09900350003c0403244880704110100d5001c20203040b5504106400303401403d07407000820128041c0d43c000c00514452041401400218081640c2c102ca120b8204c4588843703a60301c1c82015a211804002c1c0815418000000075401a4a02c00d40e06a805440082c0c006101d0002407038011801c114811a03240c000340f04510315a0040b12111403008030481462045c0c590300e010700c204e11281d01e5600402d41c0da100810100c01288007120004c00b0081c00522034004100709440c4c58 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 410599154 1250 410597904 410597953
    0x4050d030207080606010e0303070323041d090601081c0201060f0909111504030f020f06030705031e0c03070804030216080312011a03040f030c051b040506030a200103020c 75
    0x904c502400100658030400d1207008441001e0051810100c0d076540c00d481d0f80c0d6410805002c440388a01c80301e050f4210500140c0001c0c4040b1b100e49101c4030f8400707480300b080340014042d01c00c0c540000006010f50240011958241a0408003c410f1a00d0400040f0b00500498001254031201c5003000100c20915810a90885000f000c2e11302d8115010130800c0101e07007441d1040d1018040910040000c100c1403c00c00410600107050300b0500d038080ca002880729030040b0380010120b03002000f40011502e086040214544c1e03001001c90302070412009c03803801800000d05040410101c0d030000740406100340a00c0904055850340898501d03150b40506c3e859800c1301c8060307210002d8400c000500c8802c52000c040800e600800c8461454441d600c2d01006501844030030f500f03003c4444e1140d400100200070110002030395012415404c2e82f0682040196980a0310240c0300768004500c41d00031540d02501c2041180d2a011072900130703010500141c0203400342c203807211824001c9441e1501c7c9650a140041341 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 410600404 1250 410599154 410599169
    0x40603031d01110c150d0e0102030708011205100906140403271503020a09080601182a0f02071208030a15080703023a1202030a121104050d030207 64
    0x40076807800c0046030400040c0039211029442034040070f5550520085424200c2c1110a009240180b1910700702d085c4c510600001280c0da40c0001000900e590140c02d0a003d4205100d900420820540700c507691000003502a02007150380320b83c031300b0420006511100c2e21007400c0e08280101d24150038003a059640b04150020050400500b0201010800c0e12020548107207081c3e040d190440c500080b4000d4000c00301e0b070801e0103030849020a1540301001801e009041d00000005c0d80d03290017a098007552801c049405078200045a40c62000096804483c280b014a02e0105003034000300e44124580411a0b010030220316801c030040c401e02802000951080d10710f070106001c800502046002100c51a2040e00300940114809000504e085082c596002210602da0315410032880e15942895540007407117440c0000716a2044e04104c204460645000054005142017240e456000791509020307200216256644c0c464a01d02e40110400340d80180c000507041c1c101c0200309107406980c4030041d014601 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 410601654 1250 410600404 410600447
    0xd1211010e0c0913031107092a0c0201120609060e040506010807050a06270b09010809030a20100903020a050106050913030302030601020c1c15020705030a0c0f0204060303 75
    0x1618650006800c01045101900c0156250385400241c0c100340c0d856070b1304804000d0140803100b04460f081000802030100d00c10001141444040b19200f4100b10723006003942a00340c520f040b044203130040d1110650903020300706510300d2920000190024642a0444085c0130324014002c2621401829400d03c601d104030100d8400380d0303d0700b805036952070040c86041c2d40700c3c10341d40090210705e200740718105140541a5000c48254005000b1809500083d0400c211100d004129550b4540c0c1c445840741e002101200514031b0104015170081829218400403000805402c41c5211740907001c118289030251a00c10403c0000340c0c86c90000d488a0380303102d09903500e41c20a50003241504d01000550702a207200c0e10401085102980d041d0080d41006060b80c0c194000e6140c21090f54175035031800c40c00803603030100b4030744000250301d070042404001602006900384180a00310000c0e1340041140d4409219003001d556002070361400407407010248d0390080d0030904094001042540001c40300c08020700ca0070452 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 410602904 1250 410601654 410601671
    0x115031107020306070f09080717010c03051605070f0503070807020a0f060530090303070f020703050c150f0f0d1404050c01140d0213060807022a0d121101 68
    0x184039806801c8019505403c80404269030034003c40c404440403042d400d00704c12031a5a552081d0a041d0b0a83c0190b84030590001f90044080c02032180b50008900c2d030800f0482400c0420254503400340740c1c04448144031000480d40e00b80328a10038594041e40d171140449550742010f1600720181d40101c00200e010349920240410703a2500c2d072284e007080d0b0310580d982c40c0c03d111003921a154001900a12200404849541d00009810014a40d4419910140156075900301400c00410914004c1007940440d0030040051002460218441021040c12200d0070426400071058101611a040c0504210300000541d08244400207014104803800700e0410001c05000c40c5401070040b0045400810380e8002130220030b0a5809100c25110b01c601c040d21950511802d901c078101213038045001542c034000b0502040141030307448181720394003230134520240030307860321003140c180c00604001c0740049a0308901003980415101d2540d4100880c2d0404105822102c1951000e05101c404d06441c225035401d00369403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 410604154 1250 410602904 410602931
    0x50a060312090e0402150f0c1c0e060906130f080d080a05040201080a0c022a240307120f0617060a0b030a0b1302060a0f02060702070e0606030a0f05011503 68
    0xa142c100c40810840704015900c0e0350030802c207160300503d4010026000e01074034032480c1c0010040c0c000c3c40c0c59440180b070740d01b283c01140d8443c0d6090642000410004400c035104984440094841d481d8055604580f039048040007210080d030103800220510360540c10004000c02c0006031800d483d005a2603c1e1000e468070110302043d100111400390114541c039003c244000c0940d8444040c921091050b180138440c0c00c180044425405050072107003a005406110017403408400710b03184021496002980d401380041000c0c003902004001c201841158101c400c0713264001e0700002503020f0312a0b42000410b464095243d026407042000e0019481144009099005148201101c00c0402001440c011416548042031414010030000451078000144801600c804002c2e10300d0f620756449020510005410007841c1403002000e5004562040d00100501c1d0080e80560780c20800643d9403655903035a80040001038024131400031b031001d01d8500001800e104142440900104558080c040280801c95 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 410605404 1250 410604154 410604167
    0x60507080f0411012106030b0a090f0201050c010905030313050d11030d020702010512010e0f13152a08070908120a03150b040f09050c07050a140f01050a060312 70
    0x22180d681caa214000305011410702c4803010b042960515140034040310200c0c0c140174012195a45000c1d242c0c407058140108820300b207050b40d0103c030301102042900384503200d4080e911403c9401a042c06000a10b40304030150079040b8141c0e090700700c0c04581e640d042003100d000e80701800d4201078a2502624041c0d1115501c00d22141c8205e0361004021030030b19907403c6044000317500c410320403030602108010724603c40081240032802420704032150b4400f8604203140701d035020700c01052090304d50110740f082c4001442c440408040102500780024050b6201000c80c5425a40c0001a80e2081c5402c41072180c0c0b2507010305a076220b00b00c5540c0e00920f19644a103450764400c0051030f4155240000e0241281c0c0c107100b580080c0e10226403880b00980181d8445a070507031030b88544c01659040080342824007d1081300d004294008105203101c2c0e15241858039219103c40c0b03100001050410b03805408400d4a10800150340e001081c40007c20481c1005043c00b0000d0100c0c2c841200c1c104081c44008000358000da1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 410606654 1250 410605404 410605411
    0x9100507020d2c13060509040c080d05030c0d15030f11190303080c0d090f060c03110702030d030e0f1e0d050f251212050a05010506041205010e0a0f06050708 69
    0x404040d07400c02c40000f001000d5036044d0045005a65940c1d0008455698400181c015401080300e112541e00f480403041c145204100c03000140041003050140c45040002181e076808401200000e81282251101c40c00a02960020b0300c1c00b0180c141000c00d1010200803141d82140c2120b4140024103085840040c8100900c409008581c614002414610301e02005105604012900040460180e80e81003e0700502d040182c03040e541d2180244a41c50b01032181240d40b11a140c206420401c0301d60000740c0c6d0301d0310120b51504040d00d5480c642e40515041222404280740d036030a68010b070107001d10008080d07444503403000e818420549204030060013001100c4002039600581842d1840c00340d1003128a603110070304010300f09071055100c40404c1c2d91048071103a1454580c0e8400b04c0300004d1665106403400946240c120905d0100104080da4402d800c840c01c68004900e070340300c00c40c100e041c11801083c480503103011a002d00c6000c1d1003001800703040c450b0359034401d9004125580b1034481c200c03517800045 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 410607904 1250 410606654 410606717
    0xc0301050915041a01060f0e01020604020d110f09011d010b07080301060f12110c0609070b1806090303040e01081605010806010503090f010f05011508090604080309100507020d 77
    0x3070720481001d4841d0b0034010780c458040c0704420711040c00700140c0003848030300b40c2c000030000305800301304810a44c3c000f00d4a0421182440107250500342038000900c4901c1c0000002c1c80c0510b200b01c1c003e055100c1c402c2442800c00024050240c541c4e4500c50481030b04681c5100202c00d40090b8001306054004034242e0f00040d0f0050041c1d07003940e003002d00584048205000c40024408010401d00809180b03001d00f8502071080c00d0103e441d80e2008a0031803a101002d400d542858001c1c8000b400b40c008148142c0e2900c2080007280f0324038a07070f1000030440d18414602e0072509400001808914000940b0b9134604031421102202c0c05c503903000da03840700c8041d094003e080c0003855010201d145580304038051508100b207d415031740c0b160058642142154402c8030a100c10700d03190001080b402010103022a2040c0031405c104d1054a40b0050164075000e0007040140f50860200205151039000c104000000d102004104041d003403046001e0350710500c2c07000b072b0000503c00c050074221190b00c024100340042c481 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 410609154 1250 410607904 410607913
    0x90f0d091d06030a0501020316090602030c0607050306040b1206040203060106080c0f09010e0415030302070504021309051506070c09110a0c0605090c030111030406060b0f1b031c0b030c03010509 85
    0x1c28141e050802005008540c0c0b40c031820a50401003402032004501810a140c02c4c214622082580913203240c0309940f008003075420600c019050a0004181e5540c02842d6240483d03070f0781d640c0800900245804905580c02c000340e8100c3c0760321f41900160b0780703024500841c1241d91680ea203001c112008401156500082038092100010020030070f03010304403a00050402001040780344000c1421140040404140001c90580420038580c05000031005403034140e6082d4a801d003020300b510008982072007800740709581d950028094031140303440d402d07034600c00401c4103a85c0c00700c60a00d58040403441c0514086603141001440d00741001004654100242d0780716400103801c60f840e003e00a0500404d040c81500400744070b41600d5800b8442d094021045902850b00e905081c00d080c01200c0141e04406041c0604200710285409901c0969240442400c0400e01242c5124811825400f84017000300f01215440e4020107403648580007401c1c0c9840940446503101d03965406c0600740c1e02c096a100030326812 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 410610404 1250 410609154 410609189
    0x121e07030c14070306050f0403030506090601091406160b010816051003020d151211030d1403100305030d0b01032d0e16090e07120c0603091a090f0d09 66
    0x80200c81452942000c019070352401c2e501d803503010942e1407c48000d40c1910700b070380c10402050740621560b43c000d03905440c2003105181c40000640300c0c001034000c10080249042c0014190703959401201c41540740c880403601540d140d0b140c120040c410a00468641b03010b115001c46c54070414800321811030f40300900144412814890a40080d8082d0091000c2039441b19030201c030b038940041c2e11500821010428610007151400e02040f41007950746464802c4d0010004c0125103a403020000c020641502585075403900c5000c030001480c0c0b0305501c010076078000490b0703110a091040d4042c0580c250207032000d101c0905a04c03145484d9a2490050300f108861980c99101300d00003542c00403030410360310000c403800d9400640c800c02a500141d8810703c900d680311362800780100c9080c05440010902c0c044076204250032981d8240c0c02030380314000c00042555603209101803080d030301120101034018480005c1c131828401000fa4644143c192008001c1c8071b441c000c2905607104000d43d004030780e4000619600400e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 410611510 1106 410610404 410610413
    0x130f05030717031b0a062c030703021515120a060b030a050c0108060402220312021908070812070c060f1b031d121e07030c 54
    0x11054078403444002c1000040d00c0c0150541188108100041c0100b0b07407414000090140002c0d050603400340700c000c2886280e000304540d03000782500c050170b001c8684d5500c0c45910b50080050f4070100804546240505141d500400302403050907000700340c880010000c8080000c10070303c0e42c103c0510b000c1080124819284800c2c410390240484200f607440d2152105410f201503410301020a002a2480d41e5a604480b144c840d01e0798141076001082402d150014a80d0008031605030207400d803000c0ca2800003690103178891001083e642000740c25641c8075041e400440c000c4507548400d2181d00c40d00b4403407003020380c0305d40140d6403001c01c030307580900707044007694035143c030324950585840c1040d0102030601194030400b603030301d0901080c21a541042c0c01026a807880804450b8044d581c0d007403010f154544001d16100708001c100b44030081c0040140049886130b1100100491003000081d0b0005 = true := by decide +kernel

theorem cover : BRFrame.Cov 410431654 410611510 := by
  have h0 := BRFrame.cov_init 410431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 410431654 ≤ n) (h2 : n < 410611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
